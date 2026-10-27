module

public import CFSG.HardMathSupport.GuralnickMalle.SL6Exterior3_2F
public import CFSG.LieType.SpecialLinear.ExteriorModel.Reversal.Basic
public import CFSG.HardMathSupport.GuralnickMalle.BasicGeneral
public import CFSG.LieType.Chevalley.C2E6ExteriorCube

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Module
open CFSG.Open
open CFSG.LieType.SpecialLinear.ExteriorModel (permImage)

variable {K : Type} [Field K]

@[expose] noncomputable def glExterior3Rep (K : Type) [Field K] :
    Representation K (GL (Fin 6) K) (⋀[K]^3 (Fin 6 → K)) where
  toFun g := exteriorPower.map 3 ((glNaturalRep 6 K) g)
  map_one' := by
    change exteriorPower.map 3 ((glNaturalRep 6 K) 1) = 1
    rw [map_one]
    change exteriorPower.map 3 (LinearMap.id : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) =
      LinearMap.id
    rw [exteriorPower.map_id]
  map_mul' g h := by
    change exteriorPower.map 3 ((glNaturalRep 6 K) (g * h)) =
      exteriorPower.map 3 ((glNaturalRep 6 K) g) *
        exteriorPower.map 3 ((glNaturalRep 6 K) h)
    rw [map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      exteriorPower.map_comp]

theorem glExterior3Rep_apply (g : GL (Fin 6) K) :
    (glExterior3Rep K) g = exteriorPower.map 3 ((glNaturalRep 6 K) g) := rfl

theorem glNaturalRep_eq_toLin (g : GL (Fin 6) K) :
    (glNaturalRep 6 K) g =
      Matrix.toLin' ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
  apply LinearMap.ext
  intro v
  change ((Matrix.GeneralLinearGroup.toLin g) : Module.End K (Fin 6 → K)) v = _
  rw [Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]
  rfl

theorem slNaturalRep_eq_toLin (g : StatedSL 6 K) :
    (slNaturalRep 6 K) g =
      Matrix.toLin' ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
  change (glNaturalRep 6 K) ((g : GL (Fin 6) K)) = _
  rw [glNaturalRep_eq_toLin]

theorem sl6Exterior3Rep_eq_glExterior3Rep (g : StatedSL 6 K) :
    (sl6Exterior3Rep K) g = (glExterior3Rep K) ((g : GL (Fin 6) K)) := by
  rw [sl6Exterior3Rep_apply, glExterior3Rep_apply, slNaturalRep_eq_toLin,
    glNaturalRep_eq_toLin]

theorem sl6Exterior3Rep_apply_eq (g : StatedSL 6 K) (v : ⋀[K]^3 (Fin 6 → K)) :
    (sl6Exterior3Rep K) g v = (glExterior3Rep K) ((g : GL (Fin 6) K)) v := by
  rw [sl6Exterior3Rep_eq_glExterior3Rep]

theorem fixSubGen_sl6Exterior3Rep_eq_map (A : Subgroup (StatedSL 6 K)) :
    fixSubGen (sl6Exterior3Rep K) A =
      fixSubGen (glExterior3Rep K) (A.map (StatedSL 6 K).subtype) := by
  ext v
  constructor
  · intro hv b hb
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
    show (glExterior3Rep K) (Subtype.val a) v = v
    rw [← sl6Exterior3Rep_apply_eq]
    exact hv a ha
  · intro hv a ha
    rw [sl6Exterior3Rep_apply_eq]
    exact hv _ (Subgroup.mem_map_of_mem _ ha)

theorem weight1Gen_sl6Exterior3Rep_eq_map (A : Subgroup (StatedSL 6 K)) :
    weight1Gen (sl6Exterior3Rep K) A =
      weight1Gen (glExterior3Rep K) (A.map (StatedSL 6 K).subtype) := by
  rw [weight1Gen, weight1Gen, fixSubGen_sl6Exterior3Rep_eq_map,
    Subgroup.card_map_of_injective (StatedSL 6 K).subtype_injective]

variable {V : Type*} [AddCommGroup V] [Module K V] {n k : ℕ}

theorem powersetCard_card {I : Set.powersetCard (Fin n) k} : I.val.card = k := I.2

theorem basis_exteriorPower_apply (b : Basis (Fin n) K V) (I : Set.powersetCard (Fin n) k) :
    b.exteriorPower k I =
      exteriorPower.ιMulti K k (b ∘ (I.val.orderEmbOfFin (powersetCard_card (n := n)))) := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    Set.powersetCard.ofFinEmbEquiv_symm_apply]

theorem neg_eq_self_of_charP_two [CharP K 2] {W : Type*} [AddCommGroup W] [Module K W]
    (x : W) : -x = x := by
  have h' : ((-1 : K) • x) = x := by rw [CharTwo.neg_eq (1 : K), one_smul]
  rwa [neg_one_smul K x] at h'

theorem exteriorPower_ιMulti_comp_perm [CharP K 2] (v : Fin k → V)
    (σ : Equiv.Perm (Fin k)) :
    exteriorPower.ιMulti K k (v ∘ σ) = exteriorPower.ιMulti K k v := by
  rw [AlternatingMap.map_perm]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h]; simp
  · rw [h]
    show ((-1 : ℤ) • (exteriorPower.ιMulti K k v : ⋀[K]^k V)) = _
    rw [← Int.cast_smul_eq_zsmul (R := K) (M := ⋀[K]^k V) (-1 : ℤ)
      (exteriorPower.ιMulti K k v),
      show ((-1 : ℤ) : K) = 1 by
        rw [Int.cast_neg, Int.cast_one, CharTwo.neg_eq],
      one_smul]

theorem exists_perm_comp_of_forall_mem_range {ι : Type*} {f g : Fin k → ι}
    (hf : Function.Injective f) (_hg : Function.Injective g)
    (h : ∀ t, f t ∈ Set.range g) : ∃ σ : Equiv.Perm (Fin k), f = g ∘ σ := by
  classical
  choose σ hσ using h
  have hσinj : Function.Injective σ := by
    intro s t hst
    apply hf
    rw [← hσ s, ← hσ t, hst]
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hσinj
  refine ⟨Equiv.ofBijective σ hbij, ?_⟩
  funext t
  show f t = g (σ t)
  rw [hσ t]

theorem exteriorPower_map_basis_perm [CharP K 2] {b : Basis (Fin n) K V} (T : V →ₗ[K] V)
    (τ : Equiv.Perm (Fin n)) (hT : ∀ i, T (b i) = b (τ i)) (I : Set.powersetCard (Fin n) k) :
    exteriorPower.map k T (b.exteriorPower k I) = b.exteriorPower k (permImage τ I) := by
  rw [basis_exteriorPower_apply b I, basis_exteriorPower_apply b (permImage τ I),
    exteriorPower.map_apply_ιMulti]
  have hT' : (T ∘ ⇑b) = ⇑b ∘ ⇑τ := by funext i; exact hT i
  rw [← Function.comp_assoc, hT', Function.comp_assoc]
  have hrange : ∀ t, (τ ∘ (I.val.orderEmbOfFin (powersetCard_card (n := n)))) t ∈
      Set.range ((permImage τ I).val.orderEmbOfFin (powersetCard_card (n := n))) := by
    intro t
    rw [Finset.range_orderEmbOfFin]
    exact Finset.mem_image_of_mem τ
      (Finset.orderEmbOfFin_mem I.val (powersetCard_card (n := n)) t)
  obtain ⟨σ, hσ⟩ := exists_perm_comp_of_forall_mem_range
    (f := τ ∘ (I.val.orderEmbOfFin (powersetCard_card (n := n))))
    (g := (permImage τ I).val.orderEmbOfFin (powersetCard_card (n := n)))
    (fun s t hst => (I.val.orderEmbOfFin (powersetCard_card (n := n))).injective (τ.injective hst))
    (fun s t hst => ((permImage τ I).val.orderEmbOfFin (powersetCard_card (n := n))).injective hst)
    hrange
  rw [hσ, ← Function.comp_assoc]
  exact exteriorPower_ιMulti_comp_perm (K := K) (V := V) (k := k) _ σ

theorem exists_orderEmbOfFin_eq {I : Set.powersetCard (Fin n) k} {c : Fin n}
    (hc : c ∈ I.val) : ∃ t, I.val.orderEmbOfFin (powersetCard_card (n := n)) t = c := by
  have h : c ∈ Set.range (I.val.orderEmbOfFin (powersetCard_card (n := n))) := by
    rw [Finset.range_orderEmbOfFin]; exact hc
  exact h

theorem update_comp_basis {b : Basis (Fin n) K V} (a : Fin n) (f : Fin k → Fin n) (t₀ : Fin k) :
    Function.update (⇑b ∘ f) t₀ (b a) = ⇑b ∘ Function.update f t₀ a := by
  funext s
  by_cases hs : s = t₀
  · subst hs; simp
  · simp [Function.update_of_ne hs]

theorem exteriorPower_map_basis_transvection [CharP K 2] {b : Basis (Fin n) K V} {a c : Fin n}
    (hac : a ≠ c) (t : K) (T : V →ₗ[K] V)
    (hT : ∀ i, T (b i) = b i + (if i = c then t • b a else 0))
    (I : Set.powersetCard (Fin n) k) :
    exteriorPower.map k T (b.exteriorPower k I) =
      if h : c ∈ I.val ∧ a ∉ I.val then
        b.exteriorPower k I + t • b.exteriorPower k
          (CFSG.LieType.Chevalley.ExteriorCube.replace I h.1 h.2)
      else b.exteriorPower k I := by
  rw [basis_exteriorPower_apply b I, exteriorPower.map_apply_ιMulti]
  set f : Fin k ↪o Fin n := I.val.orderEmbOfFin (powersetCard_card (n := n)) with hf
  have hfun : (⇑T ∘ ⇑b ∘ ⇑f) =
      (fun s => b (f s) + (if f s = c then t • b a else 0)) := by
    funext s
    exact hT (f s)
  rw [hfun]
  by_cases hc : c ∈ I.val
  · obtain ⟨t₀, ht₀⟩ := exists_orderEmbOfFin_eq hc
    have hft₀ : f t₀ = c := by rw [hf]; exact ht₀
    have hupd : (fun s => b (f s) + (if f s = c then t • b a else 0)) =
        Function.update (⇑b ∘ f) t₀ (b c + t • b a) := by
      funext s
      by_cases hs : s = t₀
      · subst hs
        simp [hft₀]
      · have hne : f s ≠ c := fun hh => hs (f.injective (hh.trans hft₀.symm))
        simp [Function.update_of_ne hs, hne]
    rw [hupd, AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
      show Function.update (⇑b ∘ ⇑f) t₀ (b c) = ⇑b ∘ ⇑f from by
        rw [show b c = (⇑b ∘ ⇑f) t₀ by simp [hft₀]]
        exact Function.update_eq_self t₀ _]
    by_cases ha : a ∈ I.val
    · rw [dif_neg (by tauto)]
      obtain ⟨t₁, ht₁⟩ := exists_orderEmbOfFin_eq (I := I) (c := a) ha
      have hft₁ : f t₁ = a := by rw [hf]; exact ht₁
      have hne : t₀ ≠ t₁ := fun h => hac (by rw [← hft₁, ← hft₀, h])
      have hzero : exteriorPower.ιMulti K k
          (Function.update (⇑b ∘ ⇑f) t₀ (b a)) = 0 := by
        refine AlternatingMap.map_eq_zero_of_eq _ _ (i := t₀) (j := t₁) ?_ hne
        rw [Function.update_self, Function.update_of_ne hne.symm]
        simp [hft₁]
      rw [hzero, smul_zero, add_zero]
    · rw [dif_pos (⟨hc, ha⟩ : c ∈ I.val ∧ a ∉ I.val)]
      have hinner : exteriorPower.ιMulti K k (Function.update (⇑b ∘ ⇑f) t₀ (b a)) =
          b.exteriorPower k (CFSG.LieType.Chevalley.ExteriorCube.replace I hc ha) := by
        rw [show Function.update (⇑b ∘ ⇑f) t₀ (b a) = ⇑b ∘ Function.update f t₀ a from
          update_comp_basis a f t₀]
        rw [basis_exteriorPower_apply b (CFSG.LieType.Chevalley.ExteriorCube.replace I hc ha)]
        have hrange : ∀ s, (Function.update f t₀ a) s ∈
            Set.range ((CFSG.LieType.Chevalley.ExteriorCube.replace I hc ha).val.orderEmbOfFin
              (powersetCard_card (n := n))) := by
          intro s
          rw [Finset.range_orderEmbOfFin]
          by_cases hs : s = t₀
          · subst hs
            rw [Function.update_self]
            exact Finset.mem_insert_self a _
          · rw [Function.update_of_ne hs]
            refine Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨?_, Finset.orderEmbOfFin_mem _ _ s⟩)
            intro hh
            exact hs (f.injective (hh.trans hft₀.symm))
        obtain ⟨σ, hσ⟩ := exists_perm_comp_of_forall_mem_range
          (f := Function.update f t₀ a)
          (g := (CFSG.LieType.Chevalley.ExteriorCube.replace I hc ha).val.orderEmbOfFin
            (powersetCard_card (n := n)))
          (by
            intro s t hst
            by_cases hs : s = t₀ <;> by_cases ht : t = t₀
            · rw [hs, ht]
            · subst hs
              rw [Function.update_self, Function.update_of_ne ht] at hst
              exact absurd hst (fun hh => ha (hh ▸ Finset.orderEmbOfFin_mem _ _ t))
            · subst ht
              rw [Function.update_self, Function.update_of_ne hs] at hst
              exact absurd hst.symm (fun hh => ha (hh ▸ Finset.orderEmbOfFin_mem _ _ s))
            · rw [Function.update_of_ne hs, Function.update_of_ne ht] at hst
              exact f.injective hst)
          (fun s t hst => ((CFSG.LieType.Chevalley.ExteriorCube.replace I hc ha).val.orderEmbOfFin
            (powersetCard_card (n := n))).injective hst)
          hrange
        rw [hσ, ← Function.comp_assoc]
        exact exteriorPower_ιMulti_comp_perm (K := K) (V := V) (k := k) _ σ
      rw [hinner]
  · rw [dif_neg (by tauto)]
    have hfun' : (fun s => b (f s) + (if f s = c then t • b a else 0)) = ⇑b ∘ f := by
      funext s
      have hne : f s ≠ c := fun hh => hc (hh ▸ Finset.orderEmbOfFin_mem _ _ s)
      simp [hne]
    rw [hfun']

theorem mem_span_basis_image_iff {ι : Type*} {W : Type*} [AddCommGroup W] [Module K W]
    {b : Basis ι K W} {S : Set ι} {w : W} :
    w ∈ Submodule.span K (b '' S) ↔ ∀ i ∉ S, b.repr w i = 0 := by
  constructor
  · intro hw i hi
    have h := b.repr_support_subset_of_mem_span S hw
    by_contra hc
    exact hi (h (Finsupp.mem_support_iff.mpr hc))
  · intro h
    refine (Submodule.span_mono ?_) (b.mem_span_repr_support w)
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨i, ?_, rfl⟩
    by_contra hS
    exact (Finsupp.mem_support_iff.mp hi) (h i hS)

theorem inf_span_basis_image {ι : Type*} {W : Type*} [AddCommGroup W] [Module K W]
    {b : Basis ι K W} {S T : Set ι} :
    Submodule.span K (b '' S) ⊓ Submodule.span K (b '' T) =
      Submodule.span K (b '' (S ∩ T)) := by
  refine le_antisymm ?_ ?_
  · intro w hw
    rw [mem_span_basis_image_iff]
    intro i hi
    rw [Set.mem_inter_iff, not_and_or] at hi
    rcases hi with hi | hi
    · exact (mem_span_basis_image_iff.mp hw.1) i hi
    · exact (mem_span_basis_image_iff.mp hw.2) i hi
  · refine le_inf ?_ ?_
    · exact Submodule.span_mono (Set.image_mono Set.inter_subset_left)
    · exact Submodule.span_mono (Set.image_mono Set.inter_subset_right)

theorem finrank_span_basis_finset_le {ι : Type*} [DecidableEq ι] {W : Type*} [AddCommGroup W]
    [Module K W] (b : Basis ι K W) (s : Finset ι) :
    finrank K (Submodule.span K (b '' (↑s : Set ι))) ≤ s.card := by
  have hbij : Function.Bijective
      (fun i : (↑s : Set ι) =>
        (⟨b i, Set.mem_image_of_mem b i.2⟩ : b '' (↑s : Set ι))) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      exact Subtype.ext (b.injective (congrArg Subtype.val hxy))
    · rintro ⟨_, ⟨i, hi, rfl⟩⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have : Fintype ↥(b '' (↑s : Set ι)) := (s.finite_toSet.image b).fintype
  have hcard : Fintype.card ↥(b '' (↑s : Set ι)) = s.card := by
    rw [← Fintype.card_coe s]
    exact Fintype.card_congr (Equiv.ofBijective _ hbij).symm
  have h := finrank_span_le_card (R := K) (M := W) (b '' (↑s : Set ι))
  rwa [Set.toFinset_card, hcard] at h

theorem add_self_eq_zero_of_charP_two [CharP K 2] {W : Type*} [AddCommGroup W] [Module K W]
    (x : W) : x + x = 0 := by
  have h : (2 : K) • x = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  rwa [two_smul] at h

theorem fixSubGen_closure_singleton {G : Type*} [Group G] (ρ : Representation K G V) (g : G) :
    fixSubGen ρ (Subgroup.closure {g}) = LinearMap.ker (ρ g - 1) := by
  ext w
  rw [mem_fixSubGen, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  constructor
  · intro h
    exact h g (Subgroup.subset_closure (Set.mem_singleton g))
  · intro h x hx
    let S : Subgroup G :=
      { carrier := {y | ρ y w = w}
        mul_mem' := fun {y z} hy hz => by
          change ρ (y * z) w = w
          rw [map_mul, Module.End.mul_apply, hz, hy]
        one_mem' := by change ρ 1 w = w; rw [map_one, Module.End.one_apply]
        inv_mem' := fun {y} hy => by
          change ρ y⁻¹ w = w
          conv_lhs => rw [← hy]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply] }
    exact (Subgroup.mem_closure.mp hx) S (fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h)

end CFSG.HardMathSupport.GuralnickMalle
