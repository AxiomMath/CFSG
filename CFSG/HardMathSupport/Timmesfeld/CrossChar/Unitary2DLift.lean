module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalNonsplit

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.Balance

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

@[expose] noncomputable def liftGroup (h : UnitaryFieldData ℓ f K) (n : ℕ)
    (D : Subgroup (MulAut (primeFormP h (idGram K n)))) :
    Subgroup (primeFormUnitary h (idGram K n)) :=
  D.comap (primeFormConjHom h (idGram K n))

theorem mem_liftGroup {D : Subgroup (MulAut (primeFormP h (idGram K n)))}
    {A : primeFormUnitary h (idGram K n)} :
    A ∈ liftGroup h n D ↔ primeFormConjHom h (idGram K n) A ∈ D := Iff.rfl

theorem card_units_eq_three (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) : Nat.card Kˣ = 3 := by
  have := h.finite
  rw [Nat.card_units, h.card, pow_mul', hq]
  norm_num

section Hom

variable (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))

include hn hne in
theorem exists_comm_hom {D : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (A : primeFormUnitary h (idGram K n))
    (hA : primeFormConjHom h (idGram K n) A ∈ D) :
    ∃ κ : liftGroup h n D →* Kˣ, ∀ Y : liftGroup h n D,
      (A : GL (Fin n) K) * ((Y : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
        ((Y : primeFormUnitary h (idGram K n)) : GL (Fin n) K) * (A : GL (Fin n) K) *
          GeneralLinearGroup.scalar (Fin n) (κ Y) := by
  classical
  have hn0 : 0 < n := by omega
  have hex : ∀ Y : liftGroup h n D, ∃ d : Kˣ,
      (A : GL (Fin n) K) * ((Y : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
        ((Y : primeFormUnitary h (idGram K n)) : GL (Fin n) K) * (A : GL (Fin n) K) *
          GeneralLinearGroup.scalar (Fin n) d := fun Y =>
    exists_scalar_of_conj_commute hn hne (hcomm _ hA _ Y.2)
  choose κ hκ using hex
  have hcentral : ∀ (u : Kˣ) (N : GL (Fin n) K),
      GeneralLinearGroup.scalar (Fin n) u * N = N * GeneralLinearGroup.scalar (Fin n) u :=
    fun u N => GeneralLinearGroup.scalar_commute u N
  refine ⟨{ toFun := κ, map_one' := ?_, map_mul' := ?_ }, hκ⟩
  · apply glScalar_injective hn0
    have h1 := hκ 1
    simp only [Subgroup.coe_one, mul_one, one_mul] at h1
    rw [map_one]
    exact (mul_eq_left.mp h1.symm)
  · intro Y Y'
    apply glScalar_injective hn0
    have e1 := hκ Y
    have e2 := hκ Y'
    have e3 := hκ (Y * Y')
    simp only [Subgroup.coe_mul] at e3
    rw [map_mul]
    set a : GL (Fin n) K := (A : GL (Fin n) K)
    set y : GL (Fin n) K := ((Y : primeFormUnitary h (idGram K n)) : GL (Fin n) K)
    set y' : GL (Fin n) K := ((Y' : primeFormUnitary h (idGram K n)) : GL (Fin n) K)
    have e4 : a * (y * y') = y * y' * a * (GeneralLinearGroup.scalar (Fin n) (κ Y') *
        GeneralLinearGroup.scalar (Fin n) (κ Y)) := by
      calc a * (y * y') = (a * y) * y' := by rw [mul_assoc]
        _ = y * a * GeneralLinearGroup.scalar (Fin n) (κ Y) * y' := by rw [e1]
        _ = y * a * (y' * GeneralLinearGroup.scalar (Fin n) (κ Y)) := by
          rw [mul_assoc (y * a), hcentral]
        _ = y * (a * y') * GeneralLinearGroup.scalar (Fin n) (κ Y) := by
          simp only [mul_assoc]
        _ = y * (y' * a * GeneralLinearGroup.scalar (Fin n) (κ Y')) *
            GeneralLinearGroup.scalar (Fin n) (κ Y) := by rw [e2]
        _ = y * y' * a * (GeneralLinearGroup.scalar (Fin n) (κ Y') *
            GeneralLinearGroup.scalar (Fin n) (κ Y)) := by simp only [mul_assoc]
    have e5 := e3.symm.trans e4
    have e6 := mul_left_cancel (a := y * y' * a) e5.symm
    rw [← e6]
    exact GeneralLinearGroup.scalar_commute _ _

include hn in
theorem comm_hom_ker_iff {D : Subgroup (MulAut (primeFormP h (idGram K n)))}
    {A : primeFormUnitary h (idGram K n)} {κ : liftGroup h n D →* Kˣ}
    (hκ : ∀ Y : liftGroup h n D,
      (A : GL (Fin n) K) * ((Y : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
        ((Y : primeFormUnitary h (idGram K n)) : GL (Fin n) K) * (A : GL (Fin n) K) *
          GeneralLinearGroup.scalar (Fin n) (κ Y)) (Y : liftGroup h n D) :
    Y ∈ κ.ker ↔
      A * (Y : primeFormUnitary h (idGram K n)) = (Y : primeFormUnitary h (idGram K n)) * A := by
  have hn0 : 0 < n := by omega
  rw [MonoidHom.mem_ker]
  constructor
  · intro h1
    apply Subtype.ext
    have := hκ Y
    rw [h1, map_one, mul_one] at this
    exact this
  · intro h1
    have h2 : (A : GL (Fin n) K) * ((Y : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
        ((Y : primeFormUnitary h (idGram K n)) : GL (Fin n) K) * (A : GL (Fin n) K) :=
      congrArg Subtype.val h1
    have := hκ Y
    rw [h2] at this
    have h3 : GeneralLinearGroup.scalar (Fin n) (κ Y) = 1 := (mul_eq_left.mp this.symm)
    exact glScalar_injective hn0 (by rw [h3, map_one])

theorem index_ker_comm_hom_le (hq : ℓ ^ f = 2)
    {D : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (κ : liftGroup h n D →* Kˣ) : κ.ker.index ≤ 3 := by
  have := h.finite
  rw [Subgroup.index_ker]
  have := Subgroup.card_le_card_group κ.range
  rw [card_units_eq_three h hq] at this
  exact this

end Hom

section Lift

@[expose] noncomputable def liftMap (h : UnitaryFieldData ℓ f K) (n : ℕ)
    (D : Subgroup (MulAut (primeFormP h (idGram K n)))) : liftGroup h n D →* D :=
  ((primeFormConjHom h (idGram K n)).comp (liftGroup h n D).subtype).codRestrict D
    (fun Y => Y.2)

theorem liftMap_surjective {D : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hDl : D ≤ primeFormD h (idGram K n)) : Function.Surjective (liftMap h n D) := by
  intro d
  obtain ⟨A, hA⟩ := hDl d.2
  exact ⟨⟨A, by rw [mem_liftGroup, hA]; exact d.2⟩, Subtype.ext hA⟩

variable (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hq : ℓ ^ f = 2)

theorem commute_of_isElemAbelian {p : ℕ} {D : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hD : IsElemAbelian p D) : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

include hn hne hq in
theorem exists_commuting_lift {D : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 27) (hDl : D ≤ primeFormD h (idGram K n))
    (A : primeFormUnitary h (idGram K n))
    (hA : primeFormConjHom h (idGram K n) A ∈ D) :
    ∃ B : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) B ∈ D ∧
      primeFormConjHom h (idGram K n) B ∉ Subgroup.zpowers (primeFormConjHom h (idGram K n) A) ∧
      A * B = B * A := by
  classical
  have := h.finite
  obtain ⟨κ, hκ⟩ := exists_comm_hom hn hne (commute_of_isElemAbelian hD) A hA
  set T : Subgroup D := κ.ker.map (liftMap h n D) with hT
  have hidx : T.index ≤ 3 := by
    have h1 := Subgroup.index_map_dvd (H := κ.ker) (liftMap_surjective hDl)
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1).trans
      (index_ker_comm_hom_le hq κ)
  have hTcard : 9 ≤ Nat.card T := by
    have e := Subgroup.card_mul_index T
    rw [hcard] at e
    have hpos : 0 < T.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    interval_cases hi : T.index <;> omega
  set Z' : Subgroup D := Subgroup.zpowers (⟨primeFormConjHom h (idGram K n) A, hA⟩ : D) with hZ'
  have hZcard : Nat.card Z' ≤ 3 := by
    rw [hZ', Nat.card_zpowers]
    refine orderOf_le_of_pow_eq_one (by norm_num) ?_
    exact Subtype.ext (hD.2 _ hA)
  have hnle : ¬ T ≤ Z' := by
    intro hle
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨t, htT, htZ⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  obtain ⟨Y, hYκ, rfl⟩ := Subgroup.mem_map.mp htT
  refine ⟨(Y : primeFormUnitary h (idGram K n)), Y.2, ?_,
    (comm_hom_ker_iff hn hκ Y).mp hYκ⟩
  intro hmem
  apply htZ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [hZ']
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_zpow]
  exact hk

include hn hne hq in
theorem exists_commuting_lift_two {D : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 27) (hDl : D ≤ primeFormD h (idGram K n))
    (A B : primeFormUnitary h (idGram K n))
    (hA : primeFormConjHom h (idGram K n) A ∈ D) (hB : primeFormConjHom h (idGram K n) B ∈ D) :
    ∃ Z : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) Z ∈ D ∧
      primeFormConjHom h (idGram K n) Z ≠ 1 ∧ A * Z = Z * A ∧ B * Z = Z * B := by
  classical
  have := h.finite
  obtain ⟨κA, hκA⟩ := exists_comm_hom hn hne (commute_of_isElemAbelian hD) A hA
  obtain ⟨κB, hκB⟩ := exists_comm_hom hn hne (commute_of_isElemAbelian hD) B hB
  set Kc : Subgroup (liftGroup h n D) := κA.ker ⊓ κB.ker with hKc
  have hKidx : Kc.index ≤ 9 := by
    have h1 : Kc.index ≤ κA.ker.index * κB.ker.index := Subgroup.index_inf_le
    have h3 := Nat.mul_le_mul (index_ker_comm_hom_le hq κA) (index_ker_comm_hom_le hq κB)
    omega
  set T : Subgroup D := Kc.map (liftMap h n D) with hT
  have hidx : T.index ≤ 9 := by
    have h1 := Subgroup.index_map_dvd (H := Kc) (liftMap_surjective hDl)
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1).trans hKidx
  have hTcard : 3 ≤ Nat.card T := by
    have e := Subgroup.card_mul_index T
    rw [hcard] at e
    have hpos : 0 < T.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    interval_cases hi : T.index <;> omega
  have hnle : ¬ T ≤ ⊥ := by
    intro hle
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_bot] at this
    omega
  obtain ⟨t, htT, htZ⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  obtain ⟨Y, hYκ, rfl⟩ := Subgroup.mem_map.mp htT
  have hYA : Y ∈ κA.ker := (Subgroup.mem_inf.mp hYκ).1
  have hYB : Y ∈ κB.ker := (Subgroup.mem_inf.mp hYκ).2
  refine ⟨(Y : primeFormUnitary h (idGram K n)), Y.2, ?_,
    (comm_hom_ker_iff hn hκA Y).mp hYA, (comm_hom_ker_iff hn hκB Y).mp hYB⟩
  intro h1
  apply htZ
  rw [Subgroup.mem_bot]
  exact Subtype.ext h1

end Lift

end CFSG.HardMathSupport.Timmesfeld.CrossChar
