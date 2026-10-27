module

public import CFSG.GH74.KGroups.Cover
public import CFSG.GH74.KGroups.Sz8Tables
public import CFSG.GH74.E2.FrattiniRank

public section

namespace CFSG.GH74.KGroups.TwoSz8

open CFSG.Blueprint

variable {K : Type} [Group K]

theorem autRank_ge5
    (hperf : Group.IsPerfect K)
    (hK : LieModel (K ⧸ Subgroup.center K) .twistedB2 0 2 3) (p : ℕ) (hp : p.Prime)
    (h5 : 5 ≤ p) (B : Subgroup (MulAut K)) (hB : ElemAb p B) : Nat.card B ≤ p := by
  obtain ⟨e⟩ := Sz8.equiv_of_lieModel hK
  exact cover_elemAb_card_le hperf p p (fun B' hB' => Sz8.autRank_ge5 e p hp h5 B' hB') B hB

theorem autRank3_le_two
    (hperf : Group.IsPerfect K)
    (hK : LieModel (K ⧸ Subgroup.center K) .twistedB2 0 2 3) (R : Subgroup (MulAut K))
    (hR : ElemAb 3 R) : Nat.card R ≤ 9 := by
  obtain ⟨e⟩ := Sz8.equiv_of_lieModel hK
  exact cover_elemAb_card_le hperf 3 9 (fun B' hB' => Sz8.autRank3_le_two e B' hB') R hR

theorem autRank3_le_one
    (hperf : Group.IsPerfect K)
    (hK : LieModel (K ⧸ Subgroup.center K) .twistedB2 0 2 3) (R : Subgroup (MulAut K))
    (hR : ElemAb 3 R) : Nat.card R ≤ 3 := by
  obtain ⟨e⟩ := Sz8.equiv_of_lieModel hK
  exact cover_elemAb_card_le hperf 3 3 (fun B' hB' => Sz8.autRank3_le_one e B' hB') R hR

theorem fixed_false
    [Finite K] (hperf : Group.IsPerfect K)
    (hK : LieModel (K ⧸ Subgroup.center K) .twistedB2 0 2 3) (α : MulAut K) (hα2 : α ^ 2 = 1)
    (hα1 : α ≠ 1) (L : Subgroup K) (hL : ∀ x ∈ L, α x = x) (hLp : Group.IsPerfect L)
    (hLn : ¬ ∀ a b : L, a * b = b * a) : False := by
  obtain ⟨e⟩ := Sz8.equiv_of_lieModel hK
  exact cover_pumpup_solvable hperf
    (fun β hβ2 hβ1 Lb hLb => Sz8.fixed_solvable e β hβ2 hβ1 Lb hLb) α hα2 hα1 L hL hLp hLn

theorem rank_ge4
    [Finite K] (hZ : Nat.card (Subgroup.center K) = 2)
    (hK : LieModel (K ⧸ Subgroup.center K) .twistedB2 0 2 3) :
    ∃ U : Subgroup K, IsPGroup 2 U ∧ 4 ≤ Group.rank U := by
  classical
  set Z : Subgroup K := Subgroup.center K with hZdef
  let π : K →* K ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  obtain ⟨T⟩ : Nonempty (Sylow 2 (K ⧸ Z)) := inferInstance
  obtain ⟨hT1, hT2, hT3, x, hxN, hxtrans⟩ :=
    Sz8.bender hK (T : Subgroup (K ⧸ Z)) T.isPGroup' T.not_dvd_index
  have hcard := Sz8.bender_card hK (T : Subgroup (K ⧸ Z)) T.isPGroup' T.not_dvd_index
  set Abar : Subgroup (K ⧸ Z) := (T : Subgroup (K ⧸ Z)) ⊓
    Subgroup.centralizer ((T : Subgroup (K ⧸ Z)) : Set (K ⧸ Z)) with hAbar
  set A : Subgroup K := Abar.comap π with hAdef
  have hmemA : ∀ a : K, a ∈ A ↔ π a ∈ Abar := fun a => Iff.rfl
  have hmemZ : ∀ a : K, a ∈ Z ↔ π a = 1 := fun a => by
    rw [← MonoidHom.mem_ker, hker]
  have hZA : Z ≤ A := fun z hz => by
    rw [hmemA, (hmemZ z).1 hz]
    exact Abar.one_mem
  have hAcard : Nat.card A = 16 := by
    rw [hAdef, card_comap_of_surjective π hπ Abar, hcard, hker, hZ]
  have hZc : ∀ z ∈ Z, ∀ g : K, g * z = z * g := fun z hz g => Subgroup.mem_center_iff.1 hz g
  have hsq : ∀ a ∈ A, a ^ 2 ∈ Z := by
    intro a ha
    rw [hmemZ, map_pow]
    exact hT2 _ ((hmemA a).1 ha)
  obtain ⟨s, hs⟩ := hπ x
  have htrans : ∀ x' ∈ A, x' ∉ Z → ∀ y ∈ A, y ∉ Z →
      ∃ k : ℕ, ∃ z ∈ Z, s ^ k * x' * (s ^ k)⁻¹ = y * z := by
    intro x' hx' hx'Z y hy hyZ
    obtain ⟨k, hk⟩ := hxtrans (π x') ((hmemA x').1 hx') (π y) ((hmemA y).1 hy)
      (fun h => hx'Z ((hmemZ x').2 h)) (fun h => hyZ ((hmemZ y).2 h))
    have hπk : π (s ^ k * x' * (s ^ k)⁻¹) = π y := by
      simpa [map_mul, map_inv, map_pow, hs] using hk
    refine ⟨k, y⁻¹ * (s ^ k * x' * (s ^ k)⁻¹), ?_, by group⟩
    rw [hmemZ, map_mul, map_inv, hπk, inv_mul_cancel]
  have hall := elementary_of_transitive A Z hZc hZ (by rw [hAcard]; norm_num) hsq s htrans
  have hp : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [hAcard]; norm_num)
  have hcomm : IsMulCommutative A := by
    constructor
    constructor
    intro a b
    exact Subtype.ext ((hall a a.2).2 b b.2)
  have h2 : ∀ y : A, y ^ 2 = 1 := fun y => Subtype.ext (by simpa using (hall y y.2).1)
  have h16 := CFSG.GH74.E2.two_pow_rank_eq_card_of_exponent_two (Y := A) h2
  rw [hAcard] at h16
  refine ⟨A, hp, ?_⟩
  have h4 : 2 ^ Group.rank A = 2 ^ 4 := by rw [h16]; norm_num
  exact (Nat.pow_right_injective le_rfl h4).ge

end CFSG.GH74.KGroups.TwoSz8
