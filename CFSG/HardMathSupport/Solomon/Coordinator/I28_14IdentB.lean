module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14IdentBBlocks
import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypes

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Module CFSG.ComponentClassification.OutcomeLocal

section Ident

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem i28_14_identB_numeric {a k : ℕ} (ha : a = 6 ∨ a = 72) (hk : 2 ≤ k)
    (h : a ^ k = 6 ∨ a ^ k = 72) : False := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rcases ha with rfl | rfl
  · rcases m with _ | m
    · norm_num at h
    · have : 6 ^ 3 ≤ 6 ^ (m + 1 + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  · have : 72 ^ 2 ≤ 72 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem i285_not_two_blocks
    (hcard : ∀ (W : Type) [Group W], UniquenessMaximal.IsMcLaughlinGroup W →
      Group.IsSolvable W → Nat.card W = 6 ∨ Nat.card W = 72)
    (S : i285_Setup M) {r : ℕ}
    {W : Fin (r + 1) → Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) M)}
    (hW : i285_Decomp S.X S.τ r W)
    (hgen : ∀ j, W j = Subgroup.closure (S.D ∩ (W j : Set (LinearMap.GeneralLinearGroup (ZMod 2) M))))
    (hfac : ∀ R : Submodule (ZMod 2) M, S.IsMin R →
      ∃ j, S.T R ⊆ (W j : Set (LinearMap.GeneralLinearGroup (ZMod 2) M)))
    {R R' : Submodule (ZMod 2) M} (hR : S.IsMin R) (hR' : S.IsMin R') (hne : R ≠ R')
    (j : Fin (r + 1)) (h1 : S.T R ⊆ (W j : Set (LinearMap.GeneralLinearGroup (ZMod 2) M)))
    (h2 : S.T R' ⊆ (W j : Set (LinearMap.GeneralLinearGroup (ZMod 2) M))) : False := by
  classical
  have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) M) := i28_14_identB_finite_gl
  have : Finite (Submodule (ZMod 2) M) := i28_14_identB_finite_submodule
  have hIcl : ∀ R'', S.IsMin R'' → UniquenessMaximal.IsMcLaughlinGroup ↥(S.H R'') := fun R'' h =>
    S.isMcLaughlinGroup_H mcLaughlinTypes_holds h
  have hWmc : UniquenessMaximal.IsMcLaughlinGroup ↥(W j) := hW.2.2.2.2.2.2.2 j
  have hRI : R ∈ S.identBI W j := ⟨hR, h1⟩
  have hR'I : R' ∈ S.identBI W j := ⟨hR', h2⟩
  have hnormal := S.identB_normal hW hgen hfac j
  have hiSup := S.identB_iSup hW hgen hfac j
  have hindep := S.identB_indep W j
  have hRR' : S.H R ⊓ S.H R' = ⊥ := by
    refine disjoint_iff.1 ((hindep ⟨R, hRI⟩).mono_right ?_)
    exact le_iSup₂_of_le (⟨R', hR'I⟩ : S.identBI W j) (fun h => hne (congrArg Subtype.val h).symm)
      le_rfl
  have hle : ∀ R'' : S.identBI W j, S.H R''.1 ≤ W j := fun R'' => by
    rw [hiSup]
    exact le_iSup (fun R : S.identBI W j => S.H R.1) R''
  by_cases hsol : Group.IsSolvable ↥(S.H R)
  · obtain ⟨n, hn⟩ := hsol.solvable
    have : Finite (S.identBI W j) := Finite.of_injective Subtype.val Subtype.val_injective
    have : Fintype (S.identBI W j) := Fintype.ofFinite _
    have hcomm : Pairwise fun a b : S.identBI W j =>
        ∀ x y : LinearMap.GeneralLinearGroup (ZMod 2) M, x ∈ S.H a.1 → y ∈ S.H b.1 →
          Commute x y := fun a b hab x y hx hy => S.identB_commute hab hx hy
    set φ := Subgroup.noncommPiCoprod (H := fun R'' : S.identBI W j => S.H R''.1) hcomm with hφ
    have hinj : Function.Injective φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hindep
    have hrange : φ.range = W j := Subgroup.noncommPiCoprod_range.trans hiSup.symm
    have hequiv : ∀ R'' : S.identBI W j, Nonempty (↥(S.H R) ≃* ↥(S.H R''.1)) := fun R'' =>
      S.identB_equiv hR R''.2.1
    have hds : ∀ R'' : S.identBI W j, derivedSeries ↥(S.H R''.1) n = ⊥ := fun R'' => by
      obtain ⟨e⟩ := hequiv R''
      exact i28_14_identB_derivedSeries_equiv e n hn
    have hpi : Group.IsSolvable (∀ R'' : S.identBI W j, ↥(S.H R''.1)) :=
      ⟨⟨n, i28_14_identB_derivedSeries_pi n hds⟩⟩
    have hsolW : Group.IsSolvable ↥(W j) := by
      have := Group.isSolvable_of_surjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
      rwa [hrange] at this
    have hcardR := hcard _ (hIcl R hR) hsol
    have hcardW := hcard _ hWmc hsolW
    have hc : Nat.card ↥(W j) =
        Nat.card ↥(S.H R) ^ Fintype.card (S.identBI W j) := by
      have e1 : Nat.card ↥φ.range = Nat.card (∀ R'' : S.identBI W j, ↥(S.H R''.1)) :=
        Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
      rw [hrange] at e1
      rw [e1, Nat.card_pi]
      have : ∀ R'' : S.identBI W j, Nat.card ↥(S.H R''.1) = Nat.card ↥(S.H R) := fun R'' => by
        obtain ⟨e⟩ := hequiv R''
        exact (Nat.card_congr e.toEquiv).symm
      simp [this]
    have hk : 2 ≤ Fintype.card (S.identBI W j) :=
      Fintype.one_lt_card_iff.2 ⟨⟨R, hRI⟩, ⟨R', hR'I⟩, fun h => hne (congrArg Subtype.val h)⟩
    exact i28_14_identB_numeric hcardR hk (by rw [← hc]; exact hcardW)
  · obtain ⟨eR⟩ := S.identB_equiv hR hR'
    have hsol' : ¬ Group.IsSolvable ↥(S.H R') := fun h =>
      hsol (Group.isSolvable_of_isSolvable_injective (f := eR.toMonoidHom) eR.injective)
    have k1 := i28_14_identB_inf_le hWmc (hIcl R hR) (hle ⟨R, hRI⟩) (hnormal ⟨R, hRI⟩) hsol
    have k2 := i28_14_identB_inf_le hWmc (hIcl R' hR') (hle ⟨R', hR'I⟩) (hnormal ⟨R', hR'I⟩) hsol'
    apply k1.2
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ S.H R ⊓ S.H R' := ⟨k1.1 hx, k2.1 hx⟩
    rw [hRR'] at this
    exact this

end Ident

end CFSG.HardMathSupport.Solomon.Coordinator
