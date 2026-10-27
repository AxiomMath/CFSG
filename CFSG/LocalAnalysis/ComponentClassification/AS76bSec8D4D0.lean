module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4LeviZ
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcD0Gen
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.D4

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement Matrix Pointwise

section RankOneComplement

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem orbitRankOneGroup_le_normalizer_d4
    (a : Fin TwistTag.D4.foldedTag.rank) :
    orbitRankOneGroup TwistTag.D4 K σ.toRingHom a ≤
      normalizer (graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom a :
        Set (ModGL TwistTag.D4.tag K)) := by
  obtain ⟨hle, hnorm, -, -, -, -, -, hn, -,
      himg⟩ := fixed_simple_positive_complement TwistTag.D4 K σ a
  have hX : ∀ c, (orbitX TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K) ∈
      normalizer (graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom a :
        Set (ModGL TwistTag.D4.tag K)) := fun c =>
    Exc.le_normalizer_of_normal_subgroupOf hnorm hle
      (zpowers_le.2 (orbitX_mem_graphFixedPosUnipotent TwistTag.D4 σ.toRingHom a c))
      (mem_zpowers _)
  refine (closure_le _).2 ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact hX c
  · have h : (orbitY TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K) ∈
        (fun g => canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) *
          g * (canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a))⁻¹) ''
          Set.range (fun c : orbitField TwistTag.D4 K σ.toRingHom a =>
            (orbitX TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K)) := by
      rw [himg]; exact ⟨c, rfl⟩
    obtain ⟨_, ⟨c', rfl⟩, hc'⟩ := h
    change (orbitY TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K) ∈ _
    rw [← hc']
    exact mul_mem (mul_mem hn (hX c')) (inv_mem hn)

theorem eq_orbitX_of_mem_d4
    (a : Fin TwistTag.D4.foldedTag.rank)
    {x : ModGL TwistTag.D4.tag K} (hx : x ∈ orbitRankOneGroup TwistTag.D4 K σ.toRingHom a)
    (hxU : x ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) :
    ∃ c, x = orbitX TwistTag.D4 K σ.toRingHom a c := by
  obtain ⟨-, -, -, -, -, hN, -⟩ :=
    exceptional_fixed_rank_one_central_image TwistTag.D4 K σ.toRingHom a
  rw [orbitRankOneGroup, ← orbitRankOneHom_range] at hx
  obtain ⟨g, rfl⟩ := hx
  have hXU : ∀ c, (orbitX TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K) ∈
      graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
    orbitX_mem_graphFixedPosUnipotent TwistTag.D4 σ.toRingHom a
  have hHT : ∀ u, (orbitH TwistTag.D4 K σ.toRingHom a u : ModGL TwistTag.D4.tag K) ∈
      graphFixedRootTorus TwistTag.D4 K σ.toRingHom := fun u => by
    have h1 := orbitH_mem_graphFixedRootGroup (t := TwistTag.D4) (σ := σ.toRingHom) a u
    exact mem_inf.2 ⟨mem_inf.2 ⟨orbitH_mem_torusGroup a u,
      graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom h1⟩, h1⟩
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) (orbitField TwistTag.D4 K σ.toRingHom a)) 1 0 = 0
  · obtain ⟨t, s, rfl⟩ : ∃ t s, g = HSL t * uSL s := ⟨_, _, eq_HSL_mul_uSL hc⟩
    rw [map_mul, orbitRankOneHom_HSL, orbitRankOneHom_uSL] at hxU ⊢
    have hhU : (orbitH TwistTag.D4 K σ.toRingHom a t : ModGL TwistTag.D4.tag K) ∈
        graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
      have := mul_mem hxU (inv_mem (hXU s))
      rwa [mul_inv_cancel_right] at this
    have h1 : (orbitH TwistTag.D4 K σ.toRingHom a t : ModGL TwistTag.D4.tag K) = 1 :=
      (graphFixedRoot_mul_unique (hHT t) (one_mem _) (one_mem _) hhU
        (by rw [mul_one, one_mul])).1
    exact ⟨s, by rw [h1, one_mul]⟩
  · exfalso
    obtain ⟨s, t, s', rfl⟩ : ∃ s t s', g = uSL s * HSL t * WSL * uSL s' :=
      ⟨_, _, _, eq_uSL_mul_HSL_mul_WSL_mul_uSL hc⟩
    rw [map_mul, map_mul, map_mul, orbitRankOneHom_uSL, orbitRankOneHom_HSL, orbitRankOneHom_WSL,
      orbitRankOneHom_uSL, hN] at hxU
    refine canonicalRep_orbitReflection_not_mem_borelGroup (K := K) a ?_
    have hB : ∀ y ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom,
        y ∈ borelGroup TwistTag.D4.tag K := fun y hy => mem_sup_right (mem_inf.1 hy).1
    have hHB : (orbitH TwistTag.D4 K σ.toRingHom a t : ModGL TwistTag.D4.tag K) ∈
        borelGroup TwistTag.D4.tag K := mem_sup_left (mem_inf.1 (mem_inf.1 (hHT t)).1).1
    have e : canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) =
        (orbitH TwistTag.D4 K σ.toRingHom a t : ModGL TwistTag.D4.tag K)⁻¹ *
          (orbitX TwistTag.D4 K σ.toRingHom a s : ModGL TwistTag.D4.tag K)⁻¹ *
          ((orbitX TwistTag.D4 K σ.toRingHom a s : ModGL TwistTag.D4.tag K) *
            (orbitH TwistTag.D4 K σ.toRingHom a t : ModGL TwistTag.D4.tag K) *
            canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) *
            (orbitX TwistTag.D4 K σ.toRingHom a s' : ModGL TwistTag.D4.tag K)) *
          (orbitX TwistTag.D4 K σ.toRingHom a s' : ModGL TwistTag.D4.tag K)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (mul_mem (inv_mem hHB) (inv_mem (hB _ (hXU s)))) (hB _ hxU))
      (inv_mem (hB _ (hXU s')))

theorem complement_inf_orbitRankOneGroup_d4
    (a : Fin TwistTag.D4.foldedTag.rank) :
    graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom a ⊓
      orbitRankOneGroup TwistTag.D4 K σ.toRingHom a = ⊥ := by
  obtain ⟨hle, -, -, -, hinter, -⟩ := fixed_simple_positive_complement TwistTag.D4 K σ a
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxV, hxM⟩ := mem_inf.1 hx
  obtain ⟨c, rfl⟩ := eq_orbitX_of_mem_d4 σ a hxM (hle hxV)
  have : (orbitX TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K) ∈
      ({1} : Set (ModGL TwistTag.D4.tag K)) := by
    rw [← hinter]
    exact ⟨hxV, ⟨c, rfl⟩⟩
  exact this

end RankOneComplement

section CentDecomp

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

omit [Finite K] [CharP K 2] in
theorem torus_conj_mem_complement_d4
    (a : Fin TwistTag.D4.foldedTag.rank)
    {h v : ModGL TwistTag.D4.tag K} (hh : h ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom)
    (hv : v ∈ graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom a) :
    h * v * h⁻¹ ∈ graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom a := by
  have hT : h ∈ torusGroup TwistTag.D4.tag K := (mem_inf.1 (mem_inf.1 hh).1).1
  have hΓ : h ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom := (mem_inf.1 (mem_inf.1 hh).1).2
  exact mem_inf.2 ⟨(mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSpan
    (fun _ hα => hα.1.1) hT) v).1 (mem_inf.1 hv).1,
      mul_mem (mul_mem hΓ (mem_inf.1 hv).2) (inv_mem hΓ)⟩

omit [Finite K] [CharP K 2] in
theorem d4x₁_mem_d4Mr
    (hσ3 : σ.toRingHom ^ 3 = 1) (c : K) : d4x₁ K σ c ∈ d4Mr K σ := by
  rw [← coe_d4OuterIncl σ hσ3 c, ← coe_orbitX_zero_d4]
  exact subset_closure (Or.inl ⟨_, rfl⟩)

omit [Finite K] [CharP K 2] in
theorem d4y₁_mem_d4Mr
    (hσ3 : σ.toRingHom ^ 3 = 1) (c : K) : d4y₁ K σ c ∈ d4Mr K σ := by
  rw [← coe_d4OuterIncl σ hσ3 c, ← coe_orbitY_zero_d4]
  exact subset_closure (Or.inr ⟨_, rfl⟩)

omit [Finite K] [CharP K 2] in
theorem d4x₂_mem_d4Ma
    {c : K} (hc : σ c = c) : d4x₂ K c ∈ d4Ma K σ := by
  have hc' : c ∈ orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ :=
    (mem_orbitField_D4_one σ).2 hc
  rw [show c = ((⟨c, hc'⟩ : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) : K) from rfl,
    ← coe_orbitX_one_d4]
  exact subset_closure (Or.inl ⟨_, rfl⟩)

omit [Finite K] [CharP K 2] in
theorem d4y₂_mem_d4Ma
    {c : K} (hc : σ c = c) : d4y₂ K c ∈ d4Ma K σ := by
  have hc' : c ∈ orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ :=
    (mem_orbitField_D4_one σ).2 hc
  rw [show c = ((⟨c, hc'⟩ : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) : K) from rfl,
    ← coe_orbitY_one_d4]
  exact subset_closure (Or.inr ⟨_, rfl⟩)

omit [Finite K] [CharP K 2] in
theorem hm_mul_d4
    (b b' : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityMiddleTorus K σ (b * b') = trialityMiddleTorus K σ b * trialityMiddleTorus K σ b' := by
  rw [hm_eq_d4, hm_eq_d4, hm_eq_d4, ← map_mul, Prod.mk_mul_mk, one_mul]

omit [Finite K] [CharP K 2] in
theorem ho_mul_d4 (a a' : Kˣ) :
    trialityOuterTorus K σ (a * a') = trialityOuterTorus K σ a * trialityOuterTorus K σ a' := by
  rw [ho_eq_d4, ho_eq_d4, ho_eq_d4, ← map_mul, Prod.mk_mul_mk, mul_one]

omit [Finite K] [CharP K 2] in
theorem ho_inv_d4 (a : Kˣ) :
    trialityOuterTorus K σ a⁻¹ = (trialityOuterTorus K σ a)⁻¹ := by
  rw [ho_eq_d4, ho_eq_d4, ← map_inv]
  congr 1

omit [Finite K] [CharP K 2] in
theorem hm_inv_d4
    (b : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityMiddleTorus K σ b⁻¹ = (trialityMiddleTorus K σ b)⁻¹ := by
  rw [hm_eq_d4, hm_eq_d4, ← map_inv]
  congr 1

omit [Finite K] [CharP K 2] in
theorem ho_hm_comm_d4 (a : Kˣ)
    (b : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityOuterTorus K σ a * trialityMiddleTorus K σ b =
      trialityMiddleTorus K σ b * trialityOuterTorus K σ a := by
  rw [ho_eq_d4, hm_eq_d4, ← map_mul, ← map_mul, mul_comm]

omit [Finite K] [CharP K 2] in
theorem hm_conj_mem_d4Mr
    (hσ3 : σ.toRingHom ^ 3 = 1)
    (b : (trialityFixedField K σ.toRingHom)ˣ) {x : ModGL TwistTag.D4.tag K}
    (hx : x ∈ d4Mr K σ) :
    trialityMiddleTorus K σ b * x * (trialityMiddleTorus K σ b)⁻¹ ∈ d4Mr K σ := by
  have hle : d4Mr K σ ≤ (d4Mr K σ).comap (MulAut.conj (trialityMiddleTorus K σ b)).toMonoidHom := by
    refine (closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) <;>
      simp only [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    · rw [coe_orbitX_zero_d4, hm_conj_d4x₁]
      exact d4x₁_mem_d4Mr σ hσ3 _
    · rw [coe_orbitY_zero_d4, hm_conj_d4y₁]
      exact d4y₁_mem_d4Mr σ hσ3 _
  exact hle hx

omit [Finite K] [CharP K 2] in
theorem ho_conj_mem_d4Ma
    (hσ : σ ^ 3 = 1) (a : Kˣ) {x : ModGL TwistTag.D4.tag K}
    (hx : x ∈ d4Ma K σ) :
    trialityOuterTorus K σ a * x * (trialityOuterTorus K σ a)⁻¹ ∈ d4Ma K σ := by
  have hN : σ ((a : K) * σ a * σ (σ a)) = (a : K) * σ a * σ (σ a) :=
    (mem_trialityFixedField).1 (norm_mem_trialityFixedField hσ (a : K))
  have hle : d4Ma K σ ≤ (d4Ma K σ).comap (MulAut.conj (trialityOuterTorus K σ a)).toMonoidHom := by
    refine (closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) <;>
      simp only [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    · rw [coe_orbitX_one_d4, ho_conj_d4x₂]
      refine d4x₂_mem_d4Ma σ ?_
      rw [map_mul, map_inv₀, hN, (mem_orbitField_D4_one σ).1 c.2]
    · rw [coe_orbitY_one_d4, ho_conj_d4y₂]
      refine d4y₂_mem_d4Ma σ ?_
      rw [map_mul, map_inv₀, map_inv₀, hN, (mem_orbitField_D4_one σ).1 c.2]
  exact hle hx

omit [Finite K] [CharP K 2] in
theorem canonicalRep_orbitReflection_mem_d4
    (a : Fin TwistTag.D4.foldedTag.rank) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) ∈
      orbitRankOneGroup TwistTag.D4 K σ.toRingHom a := by
  obtain ⟨-, -, -, -, -, hN, -⟩ :=
    exceptional_fixed_rank_one_central_image TwistTag.D4 K σ.toRingHom a
  rw [← hN]
  exact orbitN_one_mem_orbitRankOneGroup a

theorem d4Vr_sup_d4Mr_le_centralizer
    (hσ : ∀ c, σ (σ (σ c)) = c) :
    d4Vr K σ ⊔ d4Mr K σ ≤ centralizer {d4z K} := sup_le
  (fun v hv => by
    obtain ⟨b₀, c₀, d₀, e₀, f₀, -, -, -, rfl⟩ := exists_d4v σ (toRingHom_pow_three_d4 σ hσ) hv
    rw [mem_centralizer_singleton_iff, d4z]
    exact d4v_commute_d4x₆ σ hσ b₀ c₀ d₀ e₀ f₀ 1)
  (fun x hx => mem_centralizer_singleton_iff.2
    (d4Mr_commute_d4Zz σ x hx _ (subset_closure ⟨1, rfl⟩)).symm)

theorem centralizer_d4z_eq
    (hσ : ∀ c, σ (σ (σ c)) = c) :
    d4C K σ ⊓ centralizer {d4z K} = d4Vr K σ ⊔ d4Mr K σ := by
  have hσ3 := toRingHom_pow_three_d4 σ hσ
  have hσ' := ringEquiv_cube_d4 σ hσ
  have hVrC : d4Vr K σ ≤ d4C K σ := (graphFixedSimpleComplement_le _).trans
    (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _)
  apply le_antisymm
  · intro g hgz'
    obtain ⟨hg, hgz⟩ := mem_inf.1 hgz'
    have hz : g * d4z K * g⁻¹ = d4z K := by
      rw [mem_centralizer_singleton_iff] at hgz; rw [hgz, mul_inv_cancel_right]
    obtain ⟨w, hw, b, hb, b', hb', rfl⟩ := exists_cell_d4 σ hg
    have hnM : canonicalRep (coxeterSystem TwistTag.D4.tag) K w ∈ d4Mr K σ := by
      rcases relWeyl_stab_theta hw (weyl_theta_of_commute σ hσ hb hb' hz).1 with rfl | rfl
      · rw [canonicalRep_one]; exact one_mem _
      · exact canonicalRep_orbitReflection_mem_d4 σ _
    set P := d4Vr K σ ⊔ d4Mr K σ with hP
    have hPn : ∀ β : (trialityFixedField K σ.toRingHom)ˣ, ∀ p ∈ P,
        trialityMiddleTorus K σ β * p * (trialityMiddleTorus K σ β)⁻¹ ∈ P := by
      intro β p hp
      have hH : trialityMiddleTorus K σ β ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
        rw [hm_eq_d4]; exact trialityTorusHom_mem_d4H σ hσ' _
      have hle : P ≤ P.comap (MulAut.conj (trialityMiddleTorus K σ β)).toMonoidHom := by
        refine sup_le (fun v hv => ?_) (fun x hx => ?_) <;>
          simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        · exact mem_sup_left (torus_conj_mem_complement_d4 σ _ hH hv)
        · exact mem_sup_right (hm_conj_mem_d4Mr σ hσ3 β hx)
      exact hle hp
    have hborel : ∀ b ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom,
        ∃ β : (trialityFixedField K σ.toRingHom)ˣ, ∃ p ∈ P, b = trialityMiddleTorus K σ β * p := by
      intro b hb
      obtain ⟨a, β, a₁, b₁, c₁, d₁, e₁, f₁, hb₁, he₁, hf₁, -, -, rfl⟩ :=
        exists_borel_coords σ hσ hb
      refine ⟨β, trialityOuterTorus K σ a * (d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁),
        mul_mem (mem_sup_right (ho_mem_d4Mr σ hσ' a)) (mul_mem (mem_sup_right
          (d4x₁_mem_d4Mr σ hσ3 a₁)) (mem_sup_left (d4v_mem_d4Vr σ hσ3 hb₁ he₁ hf₁))), ?_⟩
      rw [ho_hm_comm_d4, mul_assoc]
    obtain ⟨β, p, hp, rfl⟩ := hborel b hb
    obtain ⟨β', p', hp', rfl⟩ := hborel b' hb'
    set n := canonicalRep (coxeterSystem TwistTag.D4.tag) K w
    have hq : (trialityMiddleTorus K σ β')⁻¹ * (p * n) * trialityMiddleTorus K σ β' ∈ P := by
      have := hPn β'⁻¹ (p * n) (mul_mem hp (mem_sup_right hnM))
      rwa [hm_inv_d4, inv_inv] at this
    set p'' := (trialityMiddleTorus K σ β')⁻¹ * (p * n) * trialityMiddleTorus K σ β' * p'
    have hp'' : p'' ∈ P := mul_mem hq hp'
    have hg' : trialityMiddleTorus K σ β * p * n * (trialityMiddleTorus K σ β' * p') =
        trialityMiddleTorus K σ (β * β') * p'' := by
      rw [hm_mul_d4]
      simp only [p'']
      group
    rw [hg'] at hz ⊢
    have hPz : p'' * d4z K * p''⁻¹ = d4z K := by
      rw [mem_centralizer_singleton_iff.1 (d4Vr_sup_d4Mr_le_centralizer σ hσ hp''),
        mul_inv_cancel_right]
    have hβz : trialityMiddleTorus K σ (β * β') * d4z K * (trialityMiddleTorus K σ (β * β'))⁻¹ =
        d4z K := by
      calc trialityMiddleTorus K σ (β * β') * d4z K * (trialityMiddleTorus K σ (β * β'))⁻¹ =
            trialityMiddleTorus K σ (β * β') * (p'' * d4z K * p''⁻¹) *
              (trialityMiddleTorus K σ (β * β'))⁻¹ := by rw [hPz]
        _ = trialityMiddleTorus K σ (β * β') * p'' * d4z K *
              (trialityMiddleTorus K σ (β * β') * p'')⁻¹ := by group
        _ = d4z K := hz
    rw [d4z, hm_conj_d4x₆, mul_one] at hβz
    have h1 : β * β' = 1 :=
      Units.ext (Subtype.ext (pinnedX_injective _ _ _ hβz))
    rw [h1, hm_one_d4, one_mul]
    exact hp''
  · exact le_inf (sup_le hVrC (d4Mr_le σ hσ')) (d4Vr_sup_d4Mr_le_centralizer σ hσ)

end CentDecomp

section CentT

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

omit [Finite K] [CharP K 2] in
theorem d4Ma_le
    (hσ : σ ^ 3 = 1) : d4Ma K σ ≤ d4C K σ := by
  rw [d4Ma, orbitRankOneGroup, ← orbitRankOneHom_range]
  exact ((triality_all_characteristic_faithful_torus_coordinates K σ hσ).2.2.2.2.1
    ⟨1, by decide⟩).1

omit [Finite K] in
theorem d4Ma_commute_d4x₄ :
    ∀ x ∈ d4Ma K σ, ∀ c : K, d4x₄ K σ c * x = x * d4x₄ K σ c := by
  have hgen : ∀ x ∈ (Set.range (fun c : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ =>
      (orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ c : ModGL TwistTag.D4.tag K)) ∪
      Set.range (fun c : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ =>
        (orbitY TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ c : ModGL TwistTag.D4.tag K))),
      ∀ c : K, d4x₄ K σ c * x = x * d4x₄ K σ c := by
    rintro _ (⟨b, rfl⟩ | ⟨b, rfl⟩) c <;> dsimp only
    · rw [coe_orbitX_one_d4]
      exact commute_d4x₄_d4x₂ σ c (b : K)
    · rw [coe_orbitY_one_d4]
      have h := commute_d4x₄_d4x₂ σ c (b : K)
      rw [← trialityMiddleRep_conj_d4x₂, ← trialityMiddleRep_conj_d4x₄ σ c]
      calc trialityMiddleRep K * d4x₄ K σ c * (trialityMiddleRep K)⁻¹ *
            (trialityMiddleRep K * d4x₂ K (b : K) * (trialityMiddleRep K)⁻¹) =
          trialityMiddleRep K * (d4x₄ K σ c * d4x₂ K (b : K)) * (trialityMiddleRep K)⁻¹ := by
            group
        _ = trialityMiddleRep K * (d4x₂ K (b : K) * d4x₄ K σ c) * (trialityMiddleRep K)⁻¹ := by
            rw [h.eq]
        _ = _ := by group
  intro x hx c
  have hle : d4Ma K σ ≤ centralizer {d4x₄ K σ c} := (closure_le _).2 fun x hx => by
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact (hgen x hx c).symm
  exact (mem_centralizer_singleton_iff.1 (hle hx)).symm

omit [Finite K] in
theorem eq_one_of_char_d4 (hσ : ∀ c, σ (σ (σ c)) = c) {u : K} (hu : u ≠ 0)
    (h : 1 = σ u ^ 2 * σ (σ u) ^ 2 * (u * σ u * σ (σ u))⁻¹ * 1) : u = 1 := by
  have hy0 : σ u ≠ 0 := (map_ne_zero σ).2 hu
  have hz0 : σ (σ u) ≠ 0 := (map_ne_zero σ).2 hy0
  have h0 : u * (σ u * σ (σ u)) = (σ u * σ (σ u)) * (σ u * σ (σ u)) := by
    have hN0 : u * σ u * σ (σ u) ≠ 0 := mul_ne_zero (mul_ne_zero hu hy0) hz0
    rw [mul_one, eq_comm, mul_inv_eq_one₀ hN0] at h
    linear_combination -h
  have h1 : u = σ u * σ (σ u) := mul_right_cancel₀ (mul_ne_zero hy0 hz0) h0
  have h2 : σ u = σ (σ u) * u := by
    have := congrArg σ h1
    rwa [map_mul, hσ] at this
  have h3 : u * σ (σ u) ^ 2 = u * 1 := by
    calc u * σ (σ u) ^ 2 = (σ (σ u) * u) * σ (σ u) := by ring
      _ = u := by rw [← h2, ← h1]
      _ = u * 1 := (mul_one _).symm
  have h4 : σ (σ u) = 1 := CharTwo.sq_injective
    (show σ (σ u) ^ 2 = 1 ^ 2 by rw [mul_left_cancel₀ hu h3, one_pow])
  have := congrArg σ h4
  rwa [hσ, map_one] at this

theorem centralizer_d4t_eq
    (hσ : ∀ c, σ (σ (σ c)) = c) :
    d4C K σ ⊓ centralizer {d4t K σ} = d4U0t K σ ⊔ d4Ma K σ := by
  have hσ3 := toRingHom_pow_three_d4 σ hσ
  have hσ' := ringEquiv_cube_d4 σ hσ
  obtain ⟨hVle, -, hUVX, -⟩ := fixed_simple_positive_complement TwistTag.D4 K σ d4o1
  have hVaC : graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom d4o1 ≤ d4C K σ :=
    (graphFixedSimpleComplement_le _).trans (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _)
  have hMat : d4Ma K σ ≤ centralizer {d4t K σ} := fun x hx =>
    mem_centralizer_singleton_iff.2 (d4Ma_commute_d4x₄ σ x hx 1).symm
  apply le_antisymm
  · intro g hgt'
    obtain ⟨hg, hgt⟩ := mem_inf.1 hgt'
    have ht : g * d4t K σ * g⁻¹ = d4t K σ := by
      rw [mem_centralizer_singleton_iff] at hgt; rw [hgt, mul_inv_cancel_right]
    obtain ⟨w, hw, b, hb, b', hb', rfl⟩ := exists_cell_d4 σ hg
    have hnM : canonicalRep (coxeterSystem TwistTag.D4.tag) K w ∈ d4Ma K σ := by
      rcases weyl_t_of_commute σ hσ hw hb hb' ht with rfl | rfl
      · rw [canonicalRep_one]; exact one_mem _
      · exact canonicalRep_orbitReflection_mem_d4 σ _
    set P := d4Ma K σ ⊔ graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom d4o1 with hP
    have hPn : ∀ a : Kˣ, ∀ p ∈ P,
        trialityOuterTorus K σ a * p * (trialityOuterTorus K σ a)⁻¹ ∈ P := by
      intro a p hp
      have hH : trialityOuterTorus K σ a ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
        rw [ho_eq_d4]; exact trialityTorusHom_mem_d4H σ hσ' _
      have hle : P ≤ P.comap (MulAut.conj (trialityOuterTorus K σ a)).toMonoidHom := by
        refine sup_le (fun x hx => ?_) (fun v hv => ?_) <;>
          simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        · exact mem_sup_left (ho_conj_mem_d4Ma σ hσ' a hx)
        · exact mem_sup_right (torus_conj_mem_complement_d4 σ _ hH hv)
      exact hle hp
    have hUP : ∀ u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom, u ∈ P := by
      intro u hu
      have hu' : u ∈ (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :
        Set (ModGL TwistTag.D4.tag K)) := hu
      rw [hUVX] at hu'
      obtain ⟨v, hv, _, ⟨c, rfl⟩, rfl⟩ := hu'
      exact mul_mem (mem_sup_right hv) (mem_sup_left (subset_closure (Or.inl ⟨c, rfl⟩)))
    have hborel : ∀ b ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom,
        ∃ a : Kˣ, ∃ p ∈ P, b = trialityOuterTorus K σ a * p := by
      intro b hb
      obtain ⟨a, β, a₁, b₁, c₁, d₁, e₁, f₁, -, -, -, -, hu, rfl⟩ := exists_borel_coords σ hσ hb
      refine ⟨a, trialityMiddleTorus K σ β * (d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁),
        mul_mem (mem_sup_left ?_) (hUP _ hu), by rw [mul_assoc]⟩
      rw [hm_eq_d4]
      exact d4Qt_le_d4Ma σ hσ' ⟨β, rfl⟩
    obtain ⟨a, p, hp, rfl⟩ := hborel b hb
    obtain ⟨a', p', hp', rfl⟩ := hborel b' hb'
    set n := canonicalRep (coxeterSystem TwistTag.D4.tag) K w
    have hq : (trialityOuterTorus K σ a')⁻¹ * (p * n) * trialityOuterTorus K σ a' ∈ P := by
      have := hPn a'⁻¹ (p * n) (mul_mem hp (mem_sup_left hnM))
      rwa [ho_inv_d4, inv_inv] at this
    set p'' := (trialityOuterTorus K σ a')⁻¹ * (p * n) * trialityOuterTorus K σ a' * p'
    have hp'' : p'' ∈ P := mul_mem hq hp'
    have hg' : trialityOuterTorus K σ a * p * n * (trialityOuterTorus K σ a' * p') =
        trialityOuterTorus K σ (a * a') * p'' := by
      rw [ho_mul_d4]
      simp only [p'']
      group
    rw [hg'] at ht ⊢
    have hP' : (P : Set (ModGL TwistTag.D4.tag K)) = (d4Ma K σ : Set (ModGL TwistTag.D4.tag K)) *
        (graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom d4o1 :
          Set (ModGL TwistTag.D4.tag K)) :=
      coe_mul_of_left_le_normalizer_right _ _ (orbitRankOneGroup_le_normalizer_d4 σ d4o1)
    have hp''' : p'' ∈ (P : Set (ModGL TwistTag.D4.tag K)) := hp''
    rw [hP'] at hp'''
    obtain ⟨m, hm, v, hv, hmv⟩ := Set.mem_mul.1 hp'''
    rw [← hmv] at ht ⊢
    generalize a * a' = a₀ at ht ⊢
    obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, -, -, -, rfl⟩ := exists_d4coord σ hσ3 (hVle hv)
    have hmt : ∀ c : K, m⁻¹ * d4x₄ K σ c * m = d4x₄ K σ c := fun c => by
      rw [← d4Ma_commute_d4x₄ σ m⁻¹ (inv_mem hm) c, inv_mul_cancel_right]
    have hot : (trialityOuterTorus K σ a₀)⁻¹ * d4t K σ * trialityOuterTorus K σ a₀ =
        d4x₄ K σ (σ (a₀⁻¹ : Kˣ) ^ 2 * σ (σ (a₀⁻¹ : Kˣ)) ^ 2 *
          (((a₀⁻¹ : Kˣ) : K) * σ (a₀⁻¹ : Kˣ) * σ (σ (a₀⁻¹ : Kˣ)))⁻¹ * 1) := by
      rw [← ho_conj_d4x₄ σ hσ, ho_inv_d4, inv_inv, d4t]
    have hvt : d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁ * d4x₄ K σ 1 *
        (d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁)⁻¹ =
          d4x₄ K σ (σ (a₀⁻¹ : Kˣ) ^ 2 * σ (σ (a₀⁻¹ : Kˣ)) ^ 2 *
            (((a₀⁻¹ : Kˣ) : K) * σ (a₀⁻¹ : Kˣ) * σ (σ (a₀⁻¹ : Kˣ)))⁻¹ * 1) := by
      calc d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁ * d4x₄ K σ 1 *
            (d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁)⁻¹ =
          m⁻¹ * ((trialityOuterTorus K σ a₀)⁻¹ * (trialityOuterTorus K σ a₀ *
            (m * (d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁)) * d4t K σ * (trialityOuterTorus K σ a₀ *
              (m * (d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁)))⁻¹) *
                trialityOuterTorus K σ a₀) * m := by rw [d4t]; group
        _ = m⁻¹ * ((trialityOuterTorus K σ a₀)⁻¹ * d4t K σ * trialityOuterTorus K σ a₀) * m := by
          rw [ht]
        _ = _ := by rw [hot, hmt]
    rw [coord_conj_d4x₄ σ hσ, d4x₄_eq_d4v σ] at hvt
    obtain ⟨-, -, hχ, hT₁, hT₂⟩ := d4v_injective σ hvt
    have hvC : d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁ ∈ centralizer {d4t K σ} := by
      rw [mem_centralizer_singleton_iff]
      have h1 : d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁ * d4t K σ *
          (d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁)⁻¹ = d4t K σ := by
        rw [d4t, coord_conj_d4x₄ σ hσ, hT₁, hT₂, d4x₄_eq_d4v σ]
      calc d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁ * d4t K σ =
            d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁ * d4t K σ *
              (d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁)⁻¹ *
                (d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁) := by group
        _ = _ := by rw [h1]
    have ha₀ : a₀ = 1 :=
      inv_eq_one.1 (Units.ext (eq_one_of_char_d4 σ hσ (a₀⁻¹ : Kˣ).ne_zero hχ))
    rw [ha₀, ho_one_d4, one_mul]
    exact mul_mem (mem_sup_right hm) (mem_sup_left (mem_inf.2 ⟨hv, hvC⟩))
  · rw [d4U0t]
    exact sup_le (le_inf (inf_le_left.trans hVaC) inf_le_right) (le_inf (d4Ma_le σ hσ') hMat)

end CentT

section WeylCommute

theorem conj_commute_d4 {G : Type*} [Group G] {g a b a' b' : G} (ha : g * a * g⁻¹ = a')
    (hb : g * b * g⁻¹ = b') (h : a * b = b * a) : a' * b' = b' * a' := by
  subst ha hb
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [h]
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

theorem exists_mul_ne_mul_d4 {G : Type*} [Group G] [Nontrivial G] (h : commutator G = ⊤) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra hc'
  have hc : ∀ a b : G, a * b = b * a := fun a b => by_contra fun h => hc' ⟨a, b, h⟩
  have hbot : commutator G = ⊥ := by
    rw [commutator_def, commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [mem_centralizer_iff]
    intro y _
    exact hc y x
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  have hx' : x ∈ commutator G := h ▸ mem_top x
  rw [hbot, mem_bot] at hx'
  exact hx hx'

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)

theorem d4Nm_conj_d4x₂
    (c : K) :
    trialityMiddleRep K * trialityOuterRep K * trialityMiddleRep K * d4x₂ K c *
      (trialityMiddleRep K * trialityOuterRep K * trialityMiddleRep K)⁻¹ = d4y₆ K c := by
  rw [show trialityMiddleRep K * trialityOuterRep K * trialityMiddleRep K * d4x₂ K c *
      (trialityMiddleRep K * trialityOuterRep K * trialityMiddleRep K)⁻¹ =
        trialityMiddleRep K * (trialityOuterRep K * (trialityMiddleRep K * d4x₂ K c *
          (trialityMiddleRep K)⁻¹) * (trialityOuterRep K)⁻¹) * (trialityMiddleRep K)⁻¹ by group,
    trialityMiddleRep_conj_d4x₂, trialityOuterRep_conj_d4y₂, trialityMiddleRep_conj_d4y₅]

theorem d4Nm_conj_d4x₄
    (c : K) :
    trialityMiddleRep K * trialityOuterRep K * trialityMiddleRep K * d4x₄ K σ c *
      (trialityMiddleRep K * trialityOuterRep K * trialityMiddleRep K)⁻¹ = d4x₁ K σ c := by
  rw [show trialityMiddleRep K * trialityOuterRep K * trialityMiddleRep K * d4x₄ K σ c *
      (trialityMiddleRep K * trialityOuterRep K * trialityMiddleRep K)⁻¹ =
        trialityMiddleRep K * (trialityOuterRep K * (trialityMiddleRep K * d4x₄ K σ c *
          (trialityMiddleRep K)⁻¹) * (trialityOuterRep K)⁻¹) * (trialityMiddleRep K)⁻¹ by group,
    trialityMiddleRep_conj_d4x₄, trialityOuterRep_conj_d4x₄, trialityMiddleRep_conj_d4x₃]

theorem d4Nm_conj_d4y₁
    (c : K) :
    trialityMiddleRep K * trialityOuterRep K * trialityMiddleRep K * d4y₁ K σ c *
      (trialityMiddleRep K * trialityOuterRep K * trialityMiddleRep K)⁻¹ = d4y₄ K σ c := by
  rw [show trialityMiddleRep K * trialityOuterRep K * trialityMiddleRep K * d4y₁ K σ c *
      (trialityMiddleRep K * trialityOuterRep K * trialityMiddleRep K)⁻¹ =
        trialityMiddleRep K * (trialityOuterRep K * (trialityMiddleRep K * d4y₁ K σ c *
          (trialityMiddleRep K)⁻¹) * (trialityOuterRep K)⁻¹) * (trialityMiddleRep K)⁻¹ by group,
    trialityMiddleRep_conj_d4y₁, trialityOuterRep_conj_d4y₃, trialityMiddleRep_conj_d4y₄]

theorem d4Nm_conj_d4y₆
    (c : K) :
    trialityMiddleRep K * trialityOuterRep K * trialityMiddleRep K * d4y₆ K c *
      (trialityMiddleRep K * trialityOuterRep K * trialityMiddleRep K)⁻¹ = d4x₂ K c := by
  rw [show trialityMiddleRep K * trialityOuterRep K * trialityMiddleRep K * d4y₆ K c *
      (trialityMiddleRep K * trialityOuterRep K * trialityMiddleRep K)⁻¹ =
        trialityMiddleRep K * (trialityOuterRep K * (trialityMiddleRep K * d4y₆ K c *
          (trialityMiddleRep K)⁻¹) * (trialityOuterRep K)⁻¹) * (trialityMiddleRep K)⁻¹ by group,
    trialityMiddleRep_conj_d4y₆, trialityOuterRep_conj_d4y₅, trialityMiddleRep_conj_d4y₂]

theorem commute_d4x₆_d4y₁
    (c d : K) : d4x₆ K c * d4y₁ K σ d = d4y₁ K σ d * d4x₆ K c :=
  conj_commute_d4 (trialityOuterRep_conj_d4x₆ (K := K) c) (trialityOuterRep_conj_d4x₁ σ d)
    (commute_d4x₁_d4x₆ σ d c).symm.eq

theorem commute_d4y₆_d4x₁
    (c d : K) : d4y₆ K c * d4x₁ K σ d = d4x₁ K σ d * d4y₆ K c :=
  conj_commute_d4 (d4Nm_conj_d4x₂ (K := K) c) (d4Nm_conj_d4x₄ σ d)
    (commute_d4x₄_d4x₂ σ d c).symm.eq

theorem commute_d4y₆_d4y₁
    (c d : K) : d4y₆ K c * d4y₁ K σ d = d4y₁ K σ d * d4y₆ K c :=
  conj_commute_d4 (trialityOuterRep_conj_d4y₆ (K := K) c) (trialityOuterRep_conj_d4x₁ σ d)
    (commute_d4y₆_d4x₁ σ c d)

theorem commute_d4x₄_d4y₂
    (c d : K) : d4x₄ K σ c * d4y₂ K d = d4y₂ K d * d4x₄ K σ c :=
  conj_commute_d4 (trialityMiddleRep_conj_d4x₄ σ c) (trialityMiddleRep_conj_d4x₂ (K := K) d)
    (commute_d4x₄_d4x₂ σ c d).eq

theorem commute_d4y₄_d4x₂
    (c d : K) : d4y₄ K σ c * d4x₂ K d = d4x₂ K d * d4y₄ K σ c :=
  conj_commute_d4 (d4Nm_conj_d4y₁ σ c) (d4Nm_conj_d4y₆ (K := K) d) (commute_d4y₆_d4y₁ σ d c).symm

theorem commute_d4y₄_d4y₂
    (c d : K) : d4y₄ K σ c * d4y₂ K d = d4y₂ K d * d4y₄ K σ c :=
  conj_commute_d4 (trialityMiddleRep_conj_d4y₄ σ c) (trialityMiddleRep_conj_d4x₂ (K := K) d)
    (commute_d4y₄_d4x₂ σ c d)

end WeylCommute

section D0Groups

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)

theorem d4N6_conj_d4x₂
    (c : K) :
    trialityMiddleRep K * trialityOuterRep K * d4x₂ K c *
      (trialityMiddleRep K * trialityOuterRep K)⁻¹ = d4x₆ K c := by
  rw [show trialityMiddleRep K * trialityOuterRep K * d4x₂ K c *
      (trialityMiddleRep K * trialityOuterRep K)⁻¹ = trialityMiddleRep K *
        (trialityOuterRep K * d4x₂ K c * (trialityOuterRep K)⁻¹) * (trialityMiddleRep K)⁻¹ by
      group, trialityOuterRep_conj_d4x₂, trialityMiddleRep_conj_d4x₅]

theorem d4N6_conj_d4y₂
    (c : K) :
    trialityMiddleRep K * trialityOuterRep K * d4y₂ K c *
      (trialityMiddleRep K * trialityOuterRep K)⁻¹ = d4y₆ K c := by
  rw [show trialityMiddleRep K * trialityOuterRep K * d4y₂ K c *
      (trialityMiddleRep K * trialityOuterRep K)⁻¹ = trialityMiddleRep K *
        (trialityOuterRep K * d4y₂ K c * (trialityOuterRep K)⁻¹) * (trialityMiddleRep K)⁻¹ by
      group, trialityOuterRep_conj_d4y₂, trialityMiddleRep_conj_d4y₅]

theorem d4D0z_eq_map :
    d4D0z K σ = (d4Ma K σ).map
    (MulAut.conj (trialityMiddleRep K * trialityOuterRep K)).toMonoidHom := by
  rw [d4Ma, orbitRankOneGroup, MonoidHom.map_closure, d4D0z]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_union, Set.mem_range, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨_, Or.inl ⟨⟨(c : K), (mem_orbitField_D4_one σ).2 c.2⟩, rfl⟩, by
        rw [coe_orbitX_one_d4, d4N6_conj_d4x₂]⟩
    · exact ⟨_, Or.inr ⟨⟨(c : K), (mem_orbitField_D4_one σ).2 c.2⟩, rfl⟩, by
        rw [coe_orbitY_one_d4, d4N6_conj_d4y₂]⟩
  · rintro ⟨_, ⟨c, rfl⟩ | ⟨c, rfl⟩, rfl⟩
    · exact Or.inl ⟨⟨(c : K), (mem_orbitField_D4_one σ).1 c.2⟩, by
        rw [coe_orbitX_one_d4, d4N6_conj_d4x₂]⟩
    · exact Or.inr ⟨⟨(c : K), (mem_orbitField_D4_one σ).1 c.2⟩, by
        rw [coe_orbitY_one_d4, d4N6_conj_d4y₂]⟩

@[expose] noncomputable def d4MaEquiv
    (hσ : σ ^ 3 = 1) :
    ↥(d4Ma K σ) ≃* SL2 (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) :=
  (MulEquiv.subgroupCongr (orbitRankOneHom_range (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom) ⟨1, by decide⟩)).symm.trans
      (MonoidHom.ofInjective (orbitRankOneHom_injective_D4 hσ ⟨1, by decide⟩)).symm

@[expose] noncomputable def d4D0zEquiv
    (hσ : σ ^ 3 = 1) :
    ↥(d4D0z K σ) ≃* SL2 (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) :=
  (MulEquiv.subgroupCongr (d4D0z_eq_map σ)).trans
    (((d4Ma K σ).equivMapOfInjective
      (MulAut.conj (trialityMiddleRep K * trialityOuterRep K)).toMonoidHom
        (MulAut.conj _).injective).symm.trans (d4MaEquiv σ hσ))

@[expose] noncomputable def d4LtEquiv
    (hσ3 : σ.toRingHom ^ 3 = 1) (hσ : σ ^ 3 = 1) :
    ↥(d4Lt K σ) ≃* SL2 K :=
  (MulEquiv.subgroupCongr (range_d4LtHom σ hσ3)).symm.trans
    (MonoidHom.ofInjective (d4LtHom_injective σ hσ3 hσ)).symm

theorem d4D0z_le :
    d4D0z K σ ≤ d4C K σ :=
  (closure_le _).2 (by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact (d4x_long_mem σ c.2).2.2
    · exact (d4y_long_mem σ c.2).2.2)

omit [CharP K 2] in
theorem d4Zz_le_d4D0z :
    d4Zz K σ ≤ d4D0z K σ :=
  closure_mono Set.subset_union_left

theorem d4D0z_commute_d4Mr :
    ∀ d ∈ d4D0z K σ, ∀ r ∈ d4Mr K σ, d * r = r * d := by
  have hgen : ∀ r ∈ (Set.range (fun c : orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ =>
      (orbitX TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ c : ModGL TwistTag.D4.tag K)) ∪
      Set.range (fun c : orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ =>
        (orbitY TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ c : ModGL TwistTag.D4.tag K))),
      ∀ d ∈ (Set.range (fun c : d4k K σ => d4x₆ K c) ∪ Set.range (fun c : d4k K σ => d4y₆ K c)),
        d * r = r * d := by
    rintro _ (⟨b, rfl⟩ | ⟨b, rfl⟩) _ (⟨c, rfl⟩ | ⟨c, rfl⟩) <;> dsimp only
    · rw [coe_orbitX_zero_d4]; exact (commute_d4x₁_d4x₆ σ (b : K) (c : K)).symm.eq
    · rw [coe_orbitX_zero_d4]; exact commute_d4y₆_d4x₁ σ (c : K) (b : K)
    · rw [coe_orbitY_zero_d4]; exact commute_d4x₆_d4y₁ σ (c : K) (b : K)
    · rw [coe_orbitY_zero_d4]; exact commute_d4y₆_d4y₁ σ (c : K) (b : K)
  have hle : d4D0z K σ ≤ centralizer (d4Mr K σ : Set (ModGL TwistTag.D4.tag K)) := by
    rw [d4Mr, orbitRankOneGroup, centralizer_closure]
    refine (closure_le _).2 fun d hd => ?_
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro r hr
    exact (hgen r hr d hd).symm
  intro d hd r hr
  exact (mem_centralizer_iff.1 (hle hd) r hr).symm

theorem d4Lt_commute_d4Ma :
    ∀ d ∈ d4Lt K σ, ∀ r ∈ d4Ma K σ, d * r = r * d := by
  have hgen : ∀ r ∈ (Set.range (fun c : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ =>
      (orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ c : ModGL TwistTag.D4.tag K)) ∪
      Set.range (fun c : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ =>
        (orbitY TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ c : ModGL TwistTag.D4.tag K))),
      ∀ d ∈ (Set.range (d4x₄ K σ) ∪ Set.range (d4y₄ K σ)), d * r = r * d := by
    rintro _ (⟨b, rfl⟩ | ⟨b, rfl⟩) _ (⟨c, rfl⟩ | ⟨c, rfl⟩) <;> dsimp only
    · rw [coe_orbitX_one_d4]; exact commute_d4x₄_d4x₂ σ c (b : K)
    · rw [coe_orbitX_one_d4]; exact commute_d4y₄_d4x₂ σ c (b : K)
    · rw [coe_orbitY_one_d4]; exact commute_d4x₄_d4y₂ σ c (b : K)
    · rw [coe_orbitY_one_d4]; exact commute_d4y₄_d4y₂ σ c (b : K)
  have hle : d4Lt K σ ≤ centralizer (d4Ma K σ : Set (ModGL TwistTag.D4.tag K)) := by
    rw [d4Ma, orbitRankOneGroup, centralizer_closure]
    refine (closure_le _).2 fun d hd => ?_
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro r hr
    exact (hgen r hr d hd).symm
  intro d hd r hr
  exact (mem_centralizer_iff.1 (hle hd) r hr).symm

end D0Groups

section D0DataSec

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem d4_d0Data_z
    (m : ℕ) (hm : 2 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 3)
    (hσq : ∀ c, σ c = c ^ 2 ^ m) {z : ↥(d4C K σ)} (hz : (z : ModGL TwistTag.D4.tag K) = d4z K) :
    Exc.D0Data z ((d4Zz K σ).subgroupOf (d4C K σ)) := by
  obtain ⟨z, hzC⟩ := z
  change z = d4z K at hz
  subst hz
  have : CharP K 2 := charP_two_of_card_d4 hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ3' := sigma_cube_of_card_d4 σ hK hσq
  have hσ3 := toRingHom_pow_three_d4 σ hσ3'
  have hσ := ringEquiv_cube_d4 σ hσ3'
  have hk : Nat.card (d4k K σ) = 2 ^ m := card_d4k_of_card σ (by omega) hK hσq
  obtain ⟨-, -, -, hL2, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ
  have h4 : 4 ≤ Nat.card (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) := by
    rw [hL2, hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have : Finite (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) := Subtype.finite
  obtain ⟨hperf, hsimp, -⟩ := sl2_facts_d4 (d4D0zEquiv σ hσ) h4
  have hVrC : d4Vr K σ ≤ d4C K σ := (graphFixedSimpleComplement_le _).trans
    (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _)
  have hV2 : IsPGroup 2 (d4Vr K σ) := (isPGroup_posUnipotent 2 TwistTag.D4.tag).to_le
    ((graphFixedSimpleComplement_le _).trans inf_le_left)
  have hnt : Nontrivial (d4D0z K σ) := hsimp.toNontrivial
  refine Exc.d0Data_of_semidirect hzC (centralizer_d4z_eq σ hσ3')
    (orbitRankOneGroup_le_normalizer_d4 σ _) (complement_inf_orbitRankOneGroup_d4 σ _) hV2
    (d4D0z_commute_d4Mr σ) (d4D0z_le σ) hVrC (exists_mul_ne_mul_d4 hperf) (d4Zz_le_d4D0z σ)
    ?_ ?_
  · intro a ha b hb
    obtain ⟨c, -, rfl⟩ := (mem_d4Zz σ).1 ha
    obtain ⟨d, -, rfl⟩ := (mem_d4Zz σ).1 hb
    rw [← d4x₆_add, ← d4x₆_add, add_comm]
  · intro v hv y hy
    obtain ⟨b₀, c₀, d₀, e₀, f₀, -, -, -, rfl⟩ := exists_d4v σ hσ3 hv
    obtain ⟨c, -, rfl⟩ := (mem_d4Zz σ).1 hy
    exact d4v_commute_d4x₆ σ hσ3' b₀ c₀ d₀ e₀ f₀ c

theorem d4_d0Data_t
    (m : ℕ) (hm : 2 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 3)
    (hσq : ∀ c, σ c = c ^ 2 ^ m) {t : ↥(d4C K σ)} (ht : (t : ModGL TwistTag.D4.tag K) = d4t K σ) :
    Exc.D0Data t ((d4Zt K σ).subgroupOf (d4C K σ)) := by
  obtain ⟨t, htC⟩ := t
  change t = d4t K σ at ht
  subst ht
  have : CharP K 2 := charP_two_of_card_d4 hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ3' := sigma_cube_of_card_d4 σ hK hσq
  have hσ3 := toRingHom_pow_three_d4 σ hσ3'
  have hσ := ringEquiv_cube_d4 σ hσ3'
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      _ ≤ (2 ^ m) ^ 3 := Nat.le_self_pow (by norm_num) _
  obtain ⟨hperf, hsimp, -⟩ := sl2_facts_d4 (d4LtEquiv σ hσ3 hσ) hK4
  have hVa := graphFixedSimpleComplement_le (t := TwistTag.D4) (K := K) (σ := σ.toRingHom) d4o1
  have hUC : d4U0t K σ ≤ d4C K σ := inf_le_left.trans
    (hVa.trans (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _))
  have hV2 : IsPGroup 2 (d4U0t K σ) := (isPGroup_posUnipotent 2 TwistTag.D4.tag).to_le
    (inf_le_left.trans (hVa.trans inf_le_left))
  have hnt : Nontrivial (d4Lt K σ) := hsimp.toNontrivial
  have hRV : d4Ma K σ ≤ normalizer (d4U0t K σ : Set (ModGL TwistTag.D4.tag K)) := by
    intro x hx
    have hxN := mem_normalizer_iff.1 (orbitRankOneGroup_le_normalizer_d4 σ d4o1 hx)
    have hxt : x ∈ centralizer {d4t K σ} :=
      mem_centralizer_singleton_iff.2 (d4Ma_commute_d4x₄ σ x hx 1).symm
    refine mem_normalizer_iff.2 fun y => ?_
    show y ∈ d4U0t K σ ↔ x * y * x⁻¹ ∈ d4U0t K σ
    rw [d4U0t, mem_inf, mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hxN y).1 h1, mul_mem (mul_mem hxt h2) (inv_mem hxt)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(hxN y).2 h1, ?_⟩
      have := mul_mem (mul_mem (inv_mem hxt) h2) hxt
      rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this
  refine Exc.d0Data_of_semidirect htC (centralizer_d4t_eq σ hσ3') hRV ?_ hV2
    (d4Lt_commute_d4Ma σ) (d4Lt_le σ hσ3) hUC (exists_mul_ne_mul_d4 hperf) (d4Zt_le_d4Lt σ)
    ?_ ?_
  · exact eq_bot_iff.2 fun x hx => (complement_inf_orbitRankOneGroup_d4 σ d4o1).le
      (mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hx).1).1, (mem_inf.1 hx).2⟩)
  · intro a ha b hb
    obtain ⟨c, -, rfl⟩ := (mem_d4Zt σ).1 ha
    obtain ⟨d, -, rfl⟩ := (mem_d4Zt σ).1 hb
    rw [← d4x₄_add, ← d4x₄_add, add_comm]
  · intro v hv y hy
    obtain ⟨c, hc, rfl⟩ := (mem_d4Zt σ).1 hy
    have hvt : v * d4t K σ * v⁻¹ = d4t K σ := by
      have := mem_centralizer_singleton_iff.1 (mem_inf.1 hv).2
      rw [this, mul_inv_cancel_right]
    have := conj_d4x₄_of_commute σ hσ3' (hUC hv) hvt hc
    calc v * d4x₄ K σ c = v * d4x₄ K σ c * v⁻¹ * v := by group
      _ = d4x₄ K σ c * v := by rw [this]

end D0DataSec

end CFSG.ComponentClassification.RankTwoExceptional.D4
