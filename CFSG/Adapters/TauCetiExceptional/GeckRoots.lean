module

public import CFSG.Blueprint.ChevalleyInfinitesimals
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Basic

public noncomputable section

namespace CFSG.TauCetiBridge.GeckRoots

open TauCeti CFSG.Blueprint.Chevalley

structure RootData (τ : Tag) (t : DynkinType) (ht : t.Valid) where
  node : Fin t.rank ≃ Fin τ.rank
  coord : Fin t.numRoots → Fin τ.rank → ℤ
  root_eq : ∀ j l, (t.simplyConnectedRootDatum ht).root j l =
    ∑ k, coord j (node k) * t.cartanMatrix k l
  isRoot : ∀ j, IsRoot τ (coord j)
  card : t.numRoots = τ.rootCount
  cartan : ∀ i j, τ.cartan (node j) (node i) = t.cartanMatrix i j

namespace RootData

variable {τ : Tag} {t : DynkinType} {ht : t.Valid} (D : RootData τ t ht)

@[expose] def comb : (Fin τ.rank → ℤ) →+ (Fin t.rank → ℚ) where
  toFun v := ∑ k, (v (D.node k) : ℚ) • (t.rationalRootSystem ht).root (t.simpleSupportEquiv ht k)
  map_zero' := by simp
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]

theorem comb_apply (v : Fin τ.rank → ℤ) :
    D.comb v =
      ∑ k, (v (D.node k) : ℚ) • (t.rationalRootSystem ht).root (t.simpleSupportEquiv ht k) :=
  rfl

theorem comb_injective : Function.Injective D.comb := by
  have hli : LinearIndependent ℚ fun k =>
      (t.rationalRootSystem ht).root (t.simpleSupportEquiv ht k) :=
    (t.rationalBase ht).linearIndepOn_root.comp (t.simpleSupportEquiv ht)
      (t.simpleSupportEquiv ht).injective
  rw [injective_iff_map_eq_zero]
  intro v hv
  have h := Fintype.linearIndependent_iff.mp hli (fun k => (v (D.node k) : ℚ)) hv
  funext a
  obtain ⟨k, rfl⟩ := D.node.surjective a
  exact_mod_cast h k

theorem root_eq_comb (j : Fin t.numRoots) :
    (t.rationalRootSystem ht).root j = D.comb (D.coord j) := by
  funext l
  rw [comb_apply, Finset.sum_apply, DynkinType.root_rationalRootSystem, D.root_eq]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, DynkinType.root_rationalRootSystem,
    DynkinType.coe_simpleSupportEquiv, DynkinType.root_simpleIndex]

theorem comb_single (i : Fin t.rank) :
    D.comb (Pi.single (D.node i) 1) =
      (t.rationalRootSystem ht).root (t.simpleSupportEquiv ht i) := by
  rw [comb_apply, Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [D.node.injective.ne hk]
  · simp

theorem coord_injective : Function.Injective D.coord := fun a b h =>
  (t.rationalRootSystem ht).root.injective (by rw [D.root_eq_comb, D.root_eq_comb, h])

theorem coord_simple (i : Fin t.rank) :
    D.coord (t.simpleSupportEquiv ht i) = Pi.single (D.node i) 1 :=
  D.comb_injective (by rw [← D.root_eq_comb, D.comb_single])

theorem coord_neg_simple (i : Fin t.rank) :
    D.coord ((t.rationalRootSystem ht).reflectionPerm (t.simpleSupportEquiv ht i)
      (t.simpleSupportEquiv ht i)) = -Pi.single (D.node i) 1 :=
  D.comb_injective (by
    rw [← D.root_eq_comb, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self,
      map_neg, D.comb_single])

theorem coord_eq_simple_iff (k : Fin t.numRoots) (i : Fin t.rank) :
    D.coord k = Pi.single (D.node i) 1 ↔ k = t.simpleSupportEquiv ht i := by
  rw [← D.coord_simple]
  exact D.coord_injective.eq_iff

theorem coord_eq_neg_simple_iff (k : Fin t.numRoots) (i : Fin t.rank) :
    D.coord k = -Pi.single (D.node i) 1 ↔
      k = (t.rationalRootSystem ht).reflectionPerm (t.simpleSupportEquiv ht i)
        (t.simpleSupportEquiv ht i) := by
  rw [← D.coord_neg_simple]
  exact D.coord_injective.eq_iff

theorem root_eq_add_iff (γ β α : Fin t.numRoots) :
    (t.rationalRootSystem ht).root γ =
        (t.rationalRootSystem ht).root β + (t.rationalRootSystem ht).root α ↔
      D.coord γ = D.coord β + D.coord α := by
  rw [D.root_eq_comb, D.root_eq_comb, D.root_eq_comb, ← map_add]
  exact D.comb_injective.eq_iff

theorem root_eq_sub_iff (γ β α : Fin t.numRoots) :
    (t.rationalRootSystem ht).root γ =
        (t.rationalRootSystem ht).root β - (t.rationalRootSystem ht).root α ↔
      D.coord γ = D.coord β - D.coord α := by
  rw [D.root_eq_comb, D.root_eq_comb, D.root_eq_comb, ← map_sub]
  exact D.comb_injective.eq_iff

@[expose] def rootEquiv :
    Fin t.numRoots ≃ {v : Fin τ.rank → ℤ // IsRoot τ v} :=
  Equiv.ofBijective (fun j => ⟨D.coord j, D.isRoot j⟩) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b h => D.coord_injective (congrArg Subtype.val h), ?_⟩
    rw [Fintype.card_fin, card_isRoot, D.card])

theorem rootEquiv_apply
    (j : Fin t.numRoots) : D.rootEquiv j = ⟨D.coord j, D.isRoot j⟩ :=
  rfl

theorem exists_coord_eq
    {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) : ∃ j, D.coord j = v := by
  obtain ⟨j, hj⟩ := D.rootEquiv.surjective ⟨v, hv⟩
  exact ⟨j, congrArg Subtype.val hj⟩

theorem comb_mem_range_root_iff (v : Fin τ.rank → ℤ) :
    D.comb v ∈ Set.range (t.rationalRootSystem ht).root ↔ IsRoot τ v := by
  constructor
  · rintro ⟨γ, hγ⟩
    rw [D.root_eq_comb] at hγ
    exact D.comb_injective hγ ▸ D.isRoot γ
  · intro hv
    obtain ⟨γ, hγ⟩ := D.exists_coord_eq hv
    exact ⟨γ, by rw [D.root_eq_comb, hγ]⟩

@[expose] def labelEquiv : t.GeckIndex ht ≃ Label τ :=
  Equiv.sumCongr ((t.simpleSupportEquiv ht).symm.trans D.node) D.rootEquiv

theorem labelEquiv_inl (k : Fin t.rank) :
    D.labelEquiv (.inl (t.simpleSupportEquiv ht k)) = .inl (D.node k) := by
  simp [labelEquiv]

theorem labelEquiv_inr (j : Fin t.numRoots) :
    D.labelEquiv (.inr j) = .inr ⟨D.coord j, D.isRoot j⟩ :=
  rfl

theorem linearIndependent_pair (i : Fin t.rank) (j : Fin t.numRoots)
    (h₁ : D.coord j ≠ Pi.single (D.node i) 1) (h₂ : D.coord j ≠ -Pi.single (D.node i) 1) :
    LinearIndependent ℚ ![(t.rationalRootSystem ht).root (t.simpleSupportEquiv ht i),
      (t.rationalRootSystem ht).root j] := by
  by_contra hli
  rcases RootPairing.IsReduced.eq_or_eq_neg _ _ hli with h | h
  · rw [D.root_eq_comb, D.root_eq_comb, D.coord_simple] at h
    exact h₁ (D.comb_injective h).symm
  · rw [D.root_eq_comb, D.root_eq_comb, D.coord_simple, ← map_neg] at h
    exact h₂ (by rw [D.comb_injective h, neg_neg])

theorem chainBotCoeff_eq
    (i : Fin t.rank) (j : Fin t.numRoots)
    (h₁ : D.coord j ≠ Pi.single (D.node i) 1) (h₂ : D.coord j ≠ -Pi.single (D.node i) 1) :
    (t.rationalRootSystem ht).chainBotCoeff (t.simpleSupportEquiv ht i) j =
      stringDown τ (D.node i) (D.coord j) := by
  have hli := D.linearIndependent_pair i j h₁ h₂
  have key : ∀ n : ℕ, n ≤ (t.rationalRootSystem ht).chainBotCoeff (t.simpleSupportEquiv ht i) j ↔
      n ≤ stringDown τ (D.node i) (D.coord j) := by
    intro n
    rw [← (t.rationalRootSystem ht).root_sub_nsmul_mem_range_iff_le_chainBotCoeff hli]
    have hc : (t.rationalRootSystem ht).root j -
        n • (t.rationalRootSystem ht).root (t.simpleSupportEquiv ht i) =
          D.comb (D.coord j + (-(n : ℤ)) • Pi.single (D.node i) 1) := by
      rw [map_add, map_zsmul, D.comb_single, ← D.root_eq_comb, neg_smul, natCast_zsmul,
        sub_eq_add_neg]
    rw [hc, D.comb_mem_range_root_iff,
      (isRoot_add_smul_single_iff (D.isRoot j) (D.node i) h₁ h₂).2]
    omega
  exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)

theorem chainTopCoeff_eq
    (i : Fin t.rank) (j : Fin t.numRoots)
    (h₁ : D.coord j ≠ Pi.single (D.node i) 1) (h₂ : D.coord j ≠ -Pi.single (D.node i) 1) :
    (t.rationalRootSystem ht).chainTopCoeff (t.simpleSupportEquiv ht i) j =
      stringUp τ (D.node i) (D.coord j) := by
  have hli := D.linearIndependent_pair i j h₁ h₂
  have key : ∀ n : ℕ, n ≤ (t.rationalRootSystem ht).chainTopCoeff (t.simpleSupportEquiv ht i) j ↔
      n ≤ stringUp τ (D.node i) (D.coord j) := by
    intro n
    rw [← (t.rationalRootSystem ht).root_add_nsmul_mem_range_iff_le_chainTopCoeff hli]
    have hc : (t.rationalRootSystem ht).root j +
        n • (t.rationalRootSystem ht).root (t.simpleSupportEquiv ht i) =
          D.comb (D.coord j + (n : ℤ) • Pi.single (D.node i) 1) := by
      rw [map_add, map_zsmul, D.comb_single, ← D.root_eq_comb, natCast_zsmul]
    rw [hc, D.comb_mem_range_root_iff,
      (isRoot_add_smul_single_iff (D.isRoot j) (D.node i) h₁ h₂).2]
    omega
  exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)

theorem coord_ne_smul_single
    (k : Fin t.numRoots) (i : Fin t.rank) (m : ℤ) (hm : m ≠ 1)
    (hm' : m ≠ -1) : D.coord k ≠ m • Pi.single (D.node i) 1 := fun h =>
  ((isRoot_smul_single_iff (D.node i) m).1 (h ▸ D.isRoot k)).elim hm hm'

end RootData

@[expose] def coordCheck {τ : Tag} {n : ℕ} (C : RootCertificate τ) (idx : List ℕ)
    (coord : Fin n → Fin τ.rank → ℤ) : Bool :=
  (List.finRange n).all fun j => decide (idx.getD j 0 < C.roots.length) &&
    List.ofFn (C.root (idx.getD j 0)) == List.ofFn (coord j)

theorem isRoot_of_coordCheck {τ : Tag} {n : ℕ} {C : RootCertificate τ} (hC : C.check = true)
    {idx : List ℕ} {coord : Fin n → Fin τ.rank → ℤ} (h : coordCheck C idx coord = true)
    (j : Fin n) : IsRoot τ (coord j) := by
  simp only [coordCheck, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨h₁, h₂⟩ := h j
  rw [← RootCertificate.eq_of_ofFn_beq h₂]
  exact RootCertificate.isRoot_root hC _ h₁

theorem rootVec_eq_single {τ : Tag} {R : Type*} [CommRing R] {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) : rootVec τ R β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 := by
  rw [rootVec, dite_eq_left_of_eq_true (eq_true hβ)]

theorem rootVec_apply_inl {τ : Tag} {R : Type*} [CommRing R] (β : Fin τ.rank → ℤ)
    (a : Fin τ.rank) : rootVec τ R β (.inl a) = 0 := by
  unfold rootVec
  split <;> simp

theorem rootVec_apply_inr {τ : Tag} {R : Type*} [CommRing R] (β : Fin τ.rank → ℤ)
    (γ : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    rootVec τ R β (.inr γ) = if γ.1 = β then 1 else 0 := by
  unfold rootVec
  by_cases h : IsRoot τ β
  · rw [dite_eq_left_of_eq_true (eq_true h)]
    simp [Finsupp.single_apply, Subtype.ext_iff, eq_comm]
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    have hγ : γ.1 ≠ β := fun h' => h (h' ▸ γ.2)
    simp [hγ]

theorem rootVec_apply_inr_mk {τ : Tag} {R : Type*} [CommRing R] (β γ : Fin τ.rank → ℤ)
    (hγ : IsRoot τ γ) : rootVec τ R β (.inr ⟨γ, hγ⟩) = if γ = β then 1 else 0 :=
  rootVec_apply_inr β ⟨γ, hγ⟩

theorem natAbs_cast (n : ℤ) : ((n.natAbs : ℕ) : ℚ) = ((|n| : ℤ) : ℚ) := by
  rw [← Int.natCast_natAbs, Int.cast_natCast]

theorem hVec_apply {τ : Tag} {R : Type*} [CommRing R] (i : Fin τ.rank) (a : Label τ) :
    hVec τ R i a = if a = .inl i then 1 else 0 := by
  simp [hVec, Finsupp.single_apply, eq_comm]

namespace RootData

variable {τ : Tag} {t : DynkinType} {ht : t.Valid} (D : RootData τ t ht)

section Entries

open RootPairing.GeckConstruction

variable (i : Fin t.rank)

theorem e_inl_inl (a b : (t.rationalBase ht).support) :
    (e (t.simpleSupportEquiv ht i) : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)
      (.inl a) (.inl b) = 0 := by
  simp [e]

theorem e_inl_inr (a : (t.rationalBase ht).support) (j : Fin t.numRoots) :
    (e (t.simpleSupportEquiv ht i) : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)
      (.inl a) (.inr j) =
      if a = t.simpleSupportEquiv ht i ∧ j = (t.rationalRootSystem ht).reflectionPerm
        (t.simpleSupportEquiv ht i) (t.simpleSupportEquiv ht i) then 1 else 0 := by
  simp [e, RootPairing.indexNeg_neg]

theorem e_inr_inl (k : Fin t.numRoots) (b : (t.rationalBase ht).support) :
    (e (t.simpleSupportEquiv ht i) : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)
      (.inr k) (.inl b) =
      if k = t.simpleSupportEquiv ht i then
        ((|(t.rationalBase ht).cartanMatrix (t.simpleSupportEquiv ht i) b| : ℤ) : ℚ) else 0 := by
  simp [e]

theorem e_inr_inr (k j : Fin t.numRoots) :
    (e (t.simpleSupportEquiv ht i) : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)
      (.inr k) (.inr j) =
      if (t.rationalRootSystem ht).root k = (t.rationalRootSystem ht).root
          (t.simpleSupportEquiv ht i) + (t.rationalRootSystem ht).root j then
        ((t.rationalRootSystem ht).chainBotCoeff (t.simpleSupportEquiv ht i) j + 1 : ℚ)
      else 0 := by
  simp [e]

theorem f_inl_inl (a b : (t.rationalBase ht).support) :
    (f (t.simpleSupportEquiv ht i) : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)
      (.inl a) (.inl b) = 0 := by
  simp [f]

theorem f_inl_inr (a : (t.rationalBase ht).support) (j : Fin t.numRoots) :
    (f (t.simpleSupportEquiv ht i) : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)
      (.inl a) (.inr j) =
      if a = t.simpleSupportEquiv ht i ∧ j = t.simpleSupportEquiv ht i then 1 else 0 := by
  simp [f]

theorem f_inr_inl (k : Fin t.numRoots) (b : (t.rationalBase ht).support) :
    (f (t.simpleSupportEquiv ht i) : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)
      (.inr k) (.inl b) =
      if k = (t.rationalRootSystem ht).reflectionPerm (t.simpleSupportEquiv ht i)
          (t.simpleSupportEquiv ht i) then
        ((|(t.rationalBase ht).cartanMatrix (t.simpleSupportEquiv ht i) b| : ℤ) : ℚ) else 0 := by
  simp [f, RootPairing.indexNeg_neg]

theorem f_inr_inr (k j : Fin t.numRoots) :
    (f (t.simpleSupportEquiv ht i) : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)
      (.inr k) (.inr j) =
      if (t.rationalRootSystem ht).root k = (t.rationalRootSystem ht).root j -
          (t.rationalRootSystem ht).root (t.simpleSupportEquiv ht i) then
        ((t.rationalRootSystem ht).chainTopCoeff (t.simpleSupportEquiv ht i) j + 1 : ℚ)
      else 0 := by
  simp [f]

end Entries

include D in
theorem simple_ne_neg (i : Fin t.rank) :
    ((t.simpleSupportEquiv ht i : Fin t.numRoots)) ≠
      (t.rationalRootSystem ht).reflectionPerm (t.simpleSupportEquiv ht i)
        (t.simpleSupportEquiv ht i) := fun h =>
  single_ne_neg_single (D.node i)
    ((D.coord_simple i).symm.trans ((congrArg D.coord h).trans (D.coord_neg_simple i)))

theorem e_apply
    (i : Fin t.rank) (x y : t.GeckIndex ht) :
    (RootPairing.GeckConstruction.e (t.simpleSupportEquiv ht i) :
      Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) x y =
        infE τ ℚ (D.node i) (Finsupp.single (D.labelEquiv y) 1) (D.labelEquiv x) := by
  rcases y with b | j
  · obtain ⟨j', rfl⟩ := (t.simpleSupportEquiv ht).surjective b
    rw [D.labelEquiv_inl, show Finsupp.single (Sum.inl (D.node j')) (1 : ℚ) =
      hVec τ ℚ (D.node j') from rfl, infE_hVec, Finsupp.smul_apply, smul_eq_mul]
    rcases x with a | k
    · obtain ⟨a', rfl⟩ := (t.simpleSupportEquiv ht).surjective a
      rw [D.labelEquiv_inl, e_inl_inl, rootVec_apply_inl, mul_zero]
    · rw [D.labelEquiv_inr, e_inr_inl, rootVec_apply_inr_mk,
        DynkinType.cartanMatrix_rationalBase, ← D.cartan, natAbs_cast]
      by_cases hk : k = t.simpleSupportEquiv ht i
      · rw [ite_eq_left hk, ite_eq_left ((D.coord_eq_simple_iff k i).2 hk), mul_one]
      · rw [ite_eq_right hk, ite_eq_right fun h => hk ((D.coord_eq_simple_iff k i).1 h),
          mul_zero]
  · rw [D.labelEquiv_inr, ← rootVec_eq_single (D.isRoot j)]
    by_cases h₁ : D.coord j = Pi.single (D.node i) 1
    · have hj := (D.coord_eq_simple_iff j i).1 h₁
      rw [h₁, infE_rootVec_single, Finsupp.zero_apply]
      subst hj
      rcases x with a | k
      · rw [e_inl_inr, ite_eq_right fun h => D.simple_ne_neg i h.2]
      · have hk : ¬ (t.rationalRootSystem ht).root k =
            (t.rationalRootSystem ht).root (t.simpleSupportEquiv ht i) +
              (t.rationalRootSystem ht).root (t.simpleSupportEquiv ht i) := by
          rw [D.root_eq_add_iff, D.coord_simple, ← two_smul ℤ]
          exact D.coord_ne_smul_single k i 2 (by decide) (by decide)
        rw [e_inr_inr, ite_eq_right hk]
    by_cases h₂ : D.coord j = -Pi.single (D.node i) 1
    · have hj := (D.coord_eq_neg_simple_iff j i).1 h₂
      rw [h₂, infE_rootVec_neg_single, hVec_apply]
      rcases x with a | k
      · obtain ⟨a', rfl⟩ := (t.simpleSupportEquiv ht).surjective a
        rw [D.labelEquiv_inl, e_inl_inr]
        by_cases ha : a' = i
        · subst ha
          rw [ite_eq_left ⟨rfl, hj⟩, ite_eq_left rfl]
        · rw [ite_eq_right fun h => ha ((t.simpleSupportEquiv ht).injective h.1),
            ite_eq_right fun h => ha (D.node.injective (Sum.inl_injective h))]
      · have hk : ¬ (t.rationalRootSystem ht).root k =
            (t.rationalRootSystem ht).root (t.simpleSupportEquiv ht i) +
              (t.rationalRootSystem ht).root j := by
          rw [D.root_eq_add_iff, D.coord_simple, h₂, add_neg_cancel,
            ← zero_smul ℤ (Pi.single (D.node i) (1 : ℤ))]
          exact D.coord_ne_smul_single k i 0 (by decide) (by decide)
        rw [D.labelEquiv_inr, e_inr_inr, ite_eq_right hk, ite_eq_right Sum.inr_ne_inl]
    rw [infE_rootVec_of_ne _ (D.isRoot j) h₁ h₂, Finsupp.smul_apply, smul_eq_mul]
    rcases x with a | k
    · obtain ⟨a', rfl⟩ := (t.simpleSupportEquiv ht).surjective a
      rw [D.labelEquiv_inl, e_inl_inr, rootVec_apply_inl, mul_zero,
        ite_eq_right fun h => h₂ ((D.coord_eq_neg_simple_iff j i).2 h.2)]
    · rw [D.labelEquiv_inr, e_inr_inr, rootVec_apply_inr_mk, D.chainBotCoeff_eq i j h₁ h₂]
      by_cases hk : D.coord k = D.coord j + Pi.single (D.node i) 1
      · have hk' : (t.rationalRootSystem ht).root k =
            (t.rationalRootSystem ht).root (t.simpleSupportEquiv ht i) +
              (t.rationalRootSystem ht).root j := by
          rw [D.root_eq_add_iff, D.coord_simple, hk, add_comm]
        rw [ite_eq_left hk', ite_eq_left hk]
        push_cast
        ring
      · have hk' : ¬ (t.rationalRootSystem ht).root k =
            (t.rationalRootSystem ht).root (t.simpleSupportEquiv ht i) +
              (t.rationalRootSystem ht).root j := by
          rw [D.root_eq_add_iff, D.coord_simple, add_comm]
          exact hk
        rw [ite_eq_right hk', ite_eq_right hk, mul_zero]

theorem f_apply
    (i : Fin t.rank) (x y : t.GeckIndex ht) :
    (RootPairing.GeckConstruction.f (t.simpleSupportEquiv ht i) :
      Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) x y =
        infF τ ℚ (D.node i) (Finsupp.single (D.labelEquiv y) 1) (D.labelEquiv x) := by
  rcases y with b | j
  · obtain ⟨j', rfl⟩ := (t.simpleSupportEquiv ht).surjective b
    rw [D.labelEquiv_inl, show Finsupp.single (Sum.inl (D.node j')) (1 : ℚ) =
      hVec τ ℚ (D.node j') from rfl, infF_hVec, Finsupp.smul_apply, smul_eq_mul]
    rcases x with a | k
    · obtain ⟨a', rfl⟩ := (t.simpleSupportEquiv ht).surjective a
      rw [D.labelEquiv_inl, f_inl_inl, rootVec_apply_inl, mul_zero]
    · rw [D.labelEquiv_inr, f_inr_inl, rootVec_apply_inr_mk,
        DynkinType.cartanMatrix_rationalBase, ← D.cartan, natAbs_cast]
      by_cases hk : k = (t.rationalRootSystem ht).reflectionPerm (t.simpleSupportEquiv ht i)
          (t.simpleSupportEquiv ht i)
      · rw [ite_eq_left hk, ite_eq_left ((D.coord_eq_neg_simple_iff k i).2 hk), mul_one]
      · rw [ite_eq_right hk, ite_eq_right fun h => hk ((D.coord_eq_neg_simple_iff k i).1 h),
          mul_zero]
  · rw [D.labelEquiv_inr, ← rootVec_eq_single (D.isRoot j)]
    by_cases h₂ : D.coord j = -Pi.single (D.node i) 1
    · have hj := (D.coord_eq_neg_simple_iff j i).1 h₂
      rw [h₂, infF_rootVec_neg_single, Finsupp.zero_apply]
      rcases x with a | k
      · have hne : ¬ (a = t.simpleSupportEquiv ht i ∧ j = t.simpleSupportEquiv ht i) :=
          fun h => D.simple_ne_neg i (h.2.symm.trans hj)
        rw [f_inl_inr, ite_eq_right hne]
      · have hk : ¬ (t.rationalRootSystem ht).root k =
            (t.rationalRootSystem ht).root j -
              (t.rationalRootSystem ht).root (t.simpleSupportEquiv ht i) := by
          rw [D.root_eq_sub_iff, D.coord_simple, h₂, ← neg_add', ← two_smul ℤ, ← neg_smul]
          exact D.coord_ne_smul_single k i (-2) (by decide) (by decide)
        rw [f_inr_inr, ite_eq_right hk]
    by_cases h₁ : D.coord j = Pi.single (D.node i) 1
    · have hj := (D.coord_eq_simple_iff j i).1 h₁
      rw [h₁, infF_rootVec_single, hVec_apply]
      rcases x with a | k
      · obtain ⟨a', rfl⟩ := (t.simpleSupportEquiv ht).surjective a
        rw [D.labelEquiv_inl, f_inl_inr]
        by_cases ha : a' = i
        · subst ha
          rw [ite_eq_left ⟨rfl, hj⟩, ite_eq_left rfl]
        · rw [ite_eq_right fun h => ha ((t.simpleSupportEquiv ht).injective h.1),
            ite_eq_right fun h => ha (D.node.injective (Sum.inl_injective h))]
      · have hk : ¬ (t.rationalRootSystem ht).root k =
            (t.rationalRootSystem ht).root j -
              (t.rationalRootSystem ht).root (t.simpleSupportEquiv ht i) := by
          rw [D.root_eq_sub_iff, D.coord_simple, h₁, sub_self,
            ← zero_smul ℤ (Pi.single (D.node i) (1 : ℤ))]
          exact D.coord_ne_smul_single k i 0 (by decide) (by decide)
        rw [D.labelEquiv_inr, f_inr_inr, ite_eq_right hk, ite_eq_right Sum.inr_ne_inl]
    rw [infF_rootVec_of_ne _ (D.isRoot j) h₁ h₂, Finsupp.smul_apply, smul_eq_mul]
    rcases x with a | k
    · obtain ⟨a', rfl⟩ := (t.simpleSupportEquiv ht).surjective a
      rw [D.labelEquiv_inl, f_inl_inr, rootVec_apply_inl, mul_zero,
        ite_eq_right fun h => h₁ ((D.coord_eq_simple_iff j i).2 h.2)]
    · rw [D.labelEquiv_inr, f_inr_inr, rootVec_apply_inr_mk, D.chainTopCoeff_eq i j h₁ h₂]
      by_cases hk : D.coord k = D.coord j - Pi.single (D.node i) 1
      · have hk' : (t.rationalRootSystem ht).root k =
            (t.rationalRootSystem ht).root j -
              (t.rationalRootSystem ht).root (t.simpleSupportEquiv ht i) := by
          rw [D.root_eq_sub_iff, D.coord_simple, hk]
        rw [ite_eq_left hk', ite_eq_left hk]
        push_cast
        ring
      · have hk' : ¬ (t.rationalRootSystem ht).root k =
            (t.rationalRootSystem ht).root j -
              (t.rationalRootSystem ht).root (t.simpleSupportEquiv ht i) := by
          rw [D.root_eq_sub_iff, D.coord_simple]
          exact hk
        rw [ite_eq_right hk', ite_eq_right hk, mul_zero]

end RootData

end CFSG.TauCetiBridge.GeckRoots
