module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrKernelFactors
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup
open scoped Pointwise

variable {F : Type*} [Group F]

theorem mem_normalizer_sup_of_mem_of_mem {A B : Subgroup F} {g : F}
    (hA : g ∈ normalizer (A : Set F)) (hB : g ∈ normalizer (B : Set F)) :
    g ∈ normalizer ((A ⊔ B : Subgroup F) : Set F) := by
  have hle : ∀ {h : F}, h ∈ normalizer (A : Set F) → h ∈ normalizer (B : Set F) →
      (A ⊔ B).map (MulAut.conj h).toMonoidHom ≤ A ⊔ B := by
    intro h hA hB
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.mp hA x).mp hx
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.mp hB x).mp hx
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hle hA hB ⟨x, hx, rfl⟩
  · intro hx
    have h1 := hle (inv_mem hA) (inv_mem hB) ⟨_, hx, rfl⟩
    rwa [show (MulAut.conj g⁻¹).toMonoidHom (g * x * g⁻¹) = x by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group] at h1

theorem exists_mulEquiv_prod_of_commute {K₁ K₂ W : Subgroup F} (hW : K₁ ⊔ K₂ = W)
    (hdisj : K₁ ⊓ K₂ = ⊥) (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) :
    ∃ μ : ↥K₁ × ↥K₂ ≃* ↥W, ∀ (k : ↥K₁) (l : ↥K₂), (μ (k, l) : F) = k * l := by
  have hcm : ∀ (k : ↥K₁) (l : ↥K₂), Commute (K₁.subtype k) (K₂.subtype l) :=
    fun k l => hc k k.2 l l.2
  let f := MonoidHom.noncommCoprod K₁.subtype K₂.subtype hcm
  have hf : ∀ x, f x ∈ W := fun x => hW ▸ mul_mem (mem_sup_left x.1.2) (mem_sup_right x.2.2)
  let f' := f.codRestrict W hf
  have hbij : Function.Bijective f' := by
    refine ⟨fun x y hxy => ?_, fun ⟨z, hz⟩ => ?_⟩
    · have h1 : (x.1 : F) * x.2 = y.1 * y.2 := congrArg Subtype.val hxy
      have hmem : (y.1 : F)⁻¹ * x.1 ∈ K₁ ⊓ K₂ := by
        refine ⟨K₁.mul_mem (K₁.inv_mem y.1.2) x.1.2, ?_⟩
        have : (y.1 : F)⁻¹ * x.1 = y.2 * (x.2 : F)⁻¹ := by
          calc (y.1 : F)⁻¹ * x.1 = (y.1 : F)⁻¹ * (x.1 * x.2) * (x.2 : F)⁻¹ := by group
            _ = (y.1 : F)⁻¹ * (y.1 * y.2) * (x.2 : F)⁻¹ := by rw [h1]
            _ = y.2 * (x.2 : F)⁻¹ := by group
        rw [this]
        exact K₂.mul_mem y.2.2 (K₂.inv_mem x.2.2)
      rw [hdisj, mem_bot, inv_mul_eq_one] at hmem
      have h2 : (x.2 : F) = y.2 := by
        rw [← hmem] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext h2)
    · have hK : K₁ ≤ normalizer (K₂ : Set F) := fun x hx =>
        centralizer_le_normalizer K₂ (mem_centralizer_iff.mpr fun y hy => (hc x hx y hy).symm)
      rw [← hW, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right K₁ K₂ hK] at hz
      obtain ⟨k, hk, l, hl, rfl⟩ := Set.mem_mul.mp hz
      exact ⟨(⟨k, hk⟩, ⟨l, hl⟩), rfl⟩
  exact ⟨MulEquiv.ofBijective f' hbij, fun k l => rfl⟩

theorem not_isSimpleGroup_of_prod {K₁ K₂ W : Subgroup F} (hW : K₁ ⊔ K₂ = W)
    (hdisj : K₁ ⊓ K₂ = ⊥) (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (h₁ : K₁ ≠ ⊥)
    (h₂ : K₂ ≠ ⊥) : ¬ IsSimpleGroup ↥W := by
  intro hs
  have hK₁W : K₁ ≤ W := hW ▸ le_sup_left
  have hK₂W : K₂ ≤ W := hW ▸ le_sup_right
  have hn : (K₁.subgroupOf W).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hK₁W, ← hW]
    exact sup_le le_normalizer fun y hy =>
      centralizer_le_normalizer K₁ (mem_centralizer_iff.mpr fun x hx => hc x hx y hy)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K₁.subgroupOf W) with h | h
  · exact h₁ ((subgroupOf_eq_bot.mp h).eq_bot_of_le hK₁W)
  · have hWK : W ≤ K₁ := subgroupOf_eq_top.mp h
    exact h₂ (le_bot_iff.mp (hdisj ▸ le_inf (hK₂W.trans hWK) le_rfl))

variable [Finite F]

theorem simple_layer_facts {F : Type} [Group F] (hKF : SectionRank.IsKGroupCat F)
    {W L : Subgroup F} (hW : IsSimpleGroup ↥W) {t : F} (hWt : ⁅W, zpowers t⁆ = W)
    (hLW : L ≤ W) (htL : L ≤ centralizer ({t} : Set F)) :
    Blueprint.Catalog ↥W ∧ L < W ∧ ∃ w ∈ W, t * w * t⁻¹ ≠ w := by
  have hW1 : W ≠ ⊥ := by
    intro h
    have : Nontrivial ↥W := IsSimpleGroup.toNontrivial
    exact (nontrivial_iff_ne_bot W).mp this h
  have hcat : Blueprint.Catalog ↥W :=
    SectionRank.catalog_of_isKGroupCat_of_surjective hKF W (MonoidHom.id ↥W) fun w => ⟨w, rfl⟩
  have hbot : ∀ X : Subgroup F, X ≤ centralizer ({t} : Set F) → ⁅X, zpowers t⁆ = ⊥ := by
    intro X hX
    rw [commutator_eq_bot_iff_le_centralizer, UnbalancedLayer.centralizer_zpowers_eq]
    exact hX
  refine ⟨hcat, lt_of_le_of_ne hLW fun h => hW1 ?_, ?_⟩
  · rw [← hWt, ← h]
    exact hbot L htL
  · by_contra hall
    push Not at hall
    apply hW1
    rw [← hWt]
    apply hbot
    intro w hw
    rw [mem_centralizer_singleton_iff]
    have := hall w hw
    calc w * t = t * w * t⁻¹ * t := by rw [this]
      _ = t * w := by group

theorem swapped_layer_facts {W L S₁ S₂ : Subgroup F} {t : F} (ht : orderOf t = 2)
    (hlayer : layer F = W) (hZ : W ⊓ centralizer (W : Set F) = ⊥) (hS : S₁ ⊔ S₂ = W)
    (hSd : S₁ ⊓ S₂ = ⊥) (hSc : ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x) (hS₁ : S₁ ≠ ⊥)
    (hS₂ : S₂ ≠ ⊥) (hLW : L ≤ W) (htL : L ≤ centralizer ({t} : Set F))
    (hLt : IsComponent (L.subgroupOf (centralizer ({t} : Set F))))
    (hLcl : (⨆ e ∈ layer F, conjugate L e) = W) :
    ∃ K₁ : Subgroup F, IsComponent K₁ ∧ conjugate K₁ t ≠ K₁ ∧ K₁ ⊔ conjugate K₁ t = W ∧
      K₁ ⊓ conjugate K₁ t = ⊥ ∧ (∀ u ∈ K₁, ∀ w ∈ conjugate K₁ t, u * w = w * u) ∧
      (L : Set F) = {g | ∃ k ∈ K₁, k * (t⁻¹ * k * t) = g} ∧
      L = W ⊓ centralizer ({t} : Set F) ∧
      ∃ δ : ↥K₁ ≃* ↥L, (∀ k : ↥K₁, (δ k : F) = k * (t⁻¹ * k * t)) ∧
      ∃ ψ : ↥W ≃* ↥L × ↥L,
        (∀ (k l : ↥K₁) (hw : (k : F) * (t⁻¹ * l * t) ∈ W), ψ ⟨_, hw⟩ = (δ k, δ l)) ∧
        (∀ (j : ↥L) (hj : (j : F) ∈ W), ψ ⟨j, hj⟩ = (j, j)) ∧
        (∀ (w : ↥W) (hw : t⁻¹ * (w : F) * t ∈ W), ψ ⟨_, hw⟩ = (ψ w).swap) ∧
        IsSimpleGroup ↥L := by
  classical
  have hWns : ¬ IsSimpleGroup ↥W := not_isSimpleGroup_of_prod hS hSd hSc hS₁ hS₂
  have ht' : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two ht
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hJ : Assembly.IsComponentOf L (centralizer ({t} : Set F)) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf htL).mpr hLt
  have hJE : L ≤ layer F := hlayer ▸ hLW
  obtain ⟨K₁, hK₁, hcase⟩ :=
    LocalAnalysis.ComponentInitial.involution_layer_component_orbit_location ht hJ hJE
  have hK₁W : K₁ ≤ W := hlayer ▸ LocalCores.component_le_layer hK₁
  have hWK₁ : W ≤ normalizer (K₁ : Set F) := hlayer ▸ LocalCores.layer_le_normalizer hK₁
  have hZW : (center ↥W).map W.subtype = ⊥ := by
    rw [eq_bot_iff, ← hZ]
    intro z hz
    exact mem_inf.mpr ((LocalCores.mem_map_center_iff W).mp hz)
  have hZK : ∀ {K : Subgroup F}, IsComponent K → center ↥K = ⊥ := by
    intro K hK
    have h1 := LocalCores.center_component_le_center_layer hK
    rw [hlayer, hZW, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at h1
    exact h1
  have hK₁s : IsSimpleGroup ↥K₁ :=
    isSimpleGroup_of_isQuasisimple_of_center_eq_bot hK₁.1 (hZK hK₁)
  have hconj : ∀ {X : Subgroup F} {e : F}, L ≤ X → e ∈ normalizer (X : Set F) →
      conjugate L e ≤ X := by
    intro X e hLX he y hy
    rw [UnbalancedLayer.mem_conjugate_iff] at hy
    have h1 := (mem_normalizer_iff.mp (inv_mem he) _).mp (hLX hy)
    rwa [show e⁻¹ * (e * y * e⁻¹) * e⁻¹⁻¹ = y by group] at h1
  rcases hcase with ⟨-, hLK⟩ | ⟨hsw, hLset, ⟨δ₀, hδ₀, hδs, hδk⟩, -, ⟨Z, hZle, hZset⟩, -⟩
  ·
    exfalso
    have hLK₁ : L ≤ K₁ := hLK.1.trans inf_le_left
    have hWle : W ≤ K₁ := by
      rw [← hLcl]
      exact iSup₂_le fun e he => hconj hLK₁ (hWK₁ (hlayer ▸ he))
    have hKW : K₁ = W := le_antisymm hK₁W hWle
    subst hKW
    exact hWns hK₁s
  · set K₂ := conjugate K₁ t with hK₂def
    have hsw' : K₂ ≠ K₁ := hsw
    have hK₂ : IsComponent K₂ := LocalCores.isComponent_map_mulEquiv (MulAut.conj t⁻¹) hK₁
    have hK₂W : K₂ ≤ W := hlayer ▸ LocalCores.component_le_layer hK₂
    have hWK₂ : W ≤ normalizer (K₂ : Set F) := hlayer ▸ LocalCores.layer_le_normalizer hK₂
    have hc12 : ⁅K₁, K₂⁆ = ⊥ :=
      (LocalCores.distinct_components_commute hK₁ hK₂).resolve_left fun h => hsw' h.symm
    have hcomm : ∀ u ∈ K₁, ∀ w ∈ K₂, u * w = w * u := by
      intro u hu w hw
      have h1 := commutator_mem_commutator hu hw
      rw [hc12, mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    have hLsup : L ≤ K₁ ⊔ K₂ := by
      intro g hg
      have hg' : g ∈ (L : Set F) := hg
      rw [hLset] at hg'
      obtain ⟨x, hx, rfl⟩ := hg'
      have hxt : t⁻¹ * x * t ∈ K₂ := by
        rw [hK₂def, UnbalancedLayer.mem_conjugate_iff]
        rw [show t * (t⁻¹ * x * t) * t⁻¹ = x by group]
        exact hx
      exact mul_mem (mem_sup_left hx) (mem_sup_right hxt)
    have hsup : K₁ ⊔ K₂ = W := by
      refine le_antisymm (sup_le hK₁W hK₂W) ?_
      rw [← hLcl]
      exact iSup₂_le fun e he => hconj hLsup
        (mem_normalizer_sup_of_mem_of_mem (hWK₁ (hlayer ▸ he)) (hWK₂ (hlayer ▸ he)))
    have hdisj : K₁ ⊓ K₂ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hx₁, hx₂⟩ := mem_inf.mp hx
      have hxc : (⟨x, hx₁⟩ : K₁) ∈ center ↥K₁ := mem_center_iff.mpr fun y =>
        Subtype.ext (hcomm y y.2 x hx₂)
      rw [hZK hK₁, mem_bot] at hxc
      exact mem_bot.mpr (congrArg Subtype.val hxc)
    have hδinj : Function.Injective δ₀ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZK hK₁]
      exact hδk
    set δ : ↥K₁ ≃* ↥L := MulEquiv.ofBijective δ₀ ⟨hδinj, hδs⟩ with hδdef
    have hδ : ∀ k : ↥K₁, (δ k : F) = k * (t⁻¹ * k * t) := fun k => hδ₀ k
    have hsup' : K₁ ⊔ LocalAnalysis.ComponentInitial.conjSub t⁻¹ K₁ = W := hsup
    rw [hsup'] at hZle hZset
    have hZbot : Z = ⊥ := le_bot_iff.mp (hZle.trans hZW.le)
    rw [hZbot, coe_bot, Set.mul_singleton] at hZset
    have hLC : L = W ⊓ centralizer ({t} : Set F) := by
      apply SetLike.coe_injective
      rw [hZset]
      ext y
      simp
    obtain ⟨μ, hμ⟩ := exists_mulEquiv_prod_of_commute hsup hdisj hcomm
    let e₀ : ↥K₁ ≃* ↥K₂ :=
      K₁.equivMapOfInjective (MulAut.conj t⁻¹).toMonoidHom (MulAut.conj t⁻¹).injective
    have he₀ : ∀ l : ↥K₁, (e₀ l : F) = t⁻¹ * l * t := fun l => by
      show (MulAut.conj t⁻¹) (l : F) = _
      rw [MulAut.conj_apply, inv_inv]
    let ψ : ↥W ≃* ↥L × ↥L := μ.symm.trans (MulEquiv.prodCongr δ (e₀.symm.trans δ))
    have hψa : ∀ (k l : ↥K₁) (hw : (k : F) * (t⁻¹ * l * t) ∈ W), ψ ⟨_, hw⟩ = (δ k, δ l) := by
      intro k l hw
      have h1 : (⟨_, hw⟩ : ↥W) = μ (k, e₀ l) := Subtype.ext (by rw [hμ, he₀])
      show (MulEquiv.prodCongr δ (e₀.symm.trans δ)) (μ.symm ⟨_, hw⟩) = _
      rw [h1, MulEquiv.symm_apply_apply]
      show (δ k, δ (e₀.symm (e₀ l))) = (δ k, δ l)
      rw [MulEquiv.symm_apply_apply]
    have hψb : ∀ (j : ↥L) (hj : (j : F) ∈ W), ψ ⟨j, hj⟩ = (j, j) := by
      intro j hj
      obtain ⟨k, rfl⟩ := δ.surjective j
      have hw : (k : F) * (t⁻¹ * k * t) ∈ W := by rw [← hδ k]; exact hj
      have h1 : (⟨(δ k : F), hj⟩ : ↥W) = ⟨_, hw⟩ := Subtype.ext (hδ k)
      rw [h1, hψa]
    have hψc : ∀ (w : ↥W) (hw : t⁻¹ * (w : F) * t ∈ W), ψ ⟨_, hw⟩ = (ψ w).swap := by
      intro w hw
      obtain ⟨⟨k, y⟩, rfl⟩ := μ.surjective w
      obtain ⟨l, rfl⟩ := e₀.surjective y
      have hw1 : (k : F) * (t⁻¹ * l * t) ∈ W := by
        rw [← he₀, ← hμ]
        exact (μ (k, e₀ l)).2
      have hw2 : (l : F) * (t⁻¹ * k * t) ∈ W :=
        hsup ▸ mul_mem (mem_sup_left l.2) (mem_sup_right (by
          rw [hK₂def, UnbalancedLayer.mem_conjugate_iff,
            show t * (t⁻¹ * (k : F) * t) * t⁻¹ = k by group]
          exact k.2))
      have hkt : t⁻¹ * (k : F) * t ∈ K₂ := by
        rw [hK₂def, UnbalancedLayer.mem_conjugate_iff,
          show t * (t⁻¹ * (k : F) * t) * t⁻¹ = k by group]
        exact k.2
      have htt' : t⁻¹ * t⁻¹ = 1 := by rw [ht', htt]
      have h1 : (⟨_, hw⟩ : ↥W) = ⟨_, hw2⟩ := Subtype.ext (by
        show t⁻¹ * ((μ (k, e₀ l) : ↥W) : F) * t = (l : F) * (t⁻¹ * k * t)
        rw [hμ, he₀]
        calc t⁻¹ * ((k : F) * (t⁻¹ * l * t)) * t
            = (t⁻¹ * k * t) * ((t⁻¹ * t⁻¹) * l * (t * t)) := by group
          _ = (t⁻¹ * k * t) * l := by rw [htt, htt', one_mul, mul_one]
          _ = l * (t⁻¹ * k * t) := (hcomm l l.2 _ hkt).symm)
      have h2 : (μ (k, e₀ l) : ↥W) = ⟨_, hw1⟩ := Subtype.ext (by rw [hμ, he₀])
      rw [h1, hψa, h2, hψa]
      rfl
    exact ⟨K₁, hK₁, hsw', hsup, hdisj, hcomm, hLset, hLC, δ, hδ, ψ, hψa, hψb, hψc,
      δ.symm.isSimpleGroup⟩

end CFSG.ComponentClassification.UnbalancedCorr
