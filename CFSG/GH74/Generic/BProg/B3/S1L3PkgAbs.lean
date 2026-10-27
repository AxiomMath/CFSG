module

public import CFSG.StronglyEmbedded.SteinbergBURankTwoOddCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1L3PkgAbs

open CFSG Subgroup

theorem exists_invol_comm_of_even {L : Type} [Group L] [Finite L] {N : Subgroup L}
    (hN2 : 2 ∣ Nat.card ↥N) {β : L} (hβ : β * β = 1)
    (hnorm : ∀ n ∈ N, β * n * β⁻¹ ∈ N) :
    ∃ δ ∈ N, δ ≠ 1 ∧ δ * δ = 1 ∧ δ * β = β * δ := by
  classical
  have : Fintype ↥N := Fintype.ofFinite _
  have hβi : β⁻¹ = β := inv_eq_of_mul_eq_one_right hβ
  let inv : Function.End ↥N := fun x => x⁻¹
  have hinv : inv ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext x
    exact inv_inv x
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) hinv
  have hY : Fintype.card {x : ↥N // x * x = 1} = Fintype.card (Function.fixedPoints inv) := by
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    simp [Function.mem_fixedPoints, Function.IsFixedPt, inv, mul_eq_one_iff_inv_eq]
  have hcard : 2 ∣ Fintype.card {x : ↥N // x * x = 1} := by
    rw [hY]
    have h2 : 2 ∣ Fintype.card ↥N := by rwa [← Nat.card_eq_fintype_card]
    exact (Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 h2)))
  have hconj : ∀ y : {x : ↥N // x * x = 1}, (β * (y.1 : L) * β⁻¹) * (β * (y.1 : L) * β⁻¹) = 1 := by
    intro y
    have h1 : (y.1 : L) * y.1 = 1 := congrArg Subtype.val y.2
    calc β * (y.1 : L) * β⁻¹ * (β * (y.1 : L) * β⁻¹) = β * ((y.1 : L) * y.1) * β⁻¹ := by group
      _ = 1 := by rw [h1]; simp
  have hsq : ∀ n : L, β * (β * n * β⁻¹) * β⁻¹ = n := by
    intro n
    rw [hβi]
    calc β * (β * n * β) * β = (β * β) * n * (β * β) := by group
      _ = n := by rw [hβ]; simp
  let σ : Equiv.Perm {x : ↥N // x * x = 1} :=
    { toFun := fun y => ⟨⟨β * y.1 * β⁻¹, hnorm _ y.1.2⟩, Subtype.ext (hconj y)⟩
      invFun := fun y => ⟨⟨β * y.1 * β⁻¹, hnorm _ y.1.2⟩, Subtype.ext (hconj y)⟩
      left_inv := fun y => Subtype.ext (Subtype.ext (hsq _))
      right_inv := fun y => Subtype.ext (Subtype.ext (hsq _)) }
  have hσ : σ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    exact Equiv.ext fun y => Subtype.ext (Subtype.ext (hsq _))
  obtain ⟨b, hb, hb1⟩ := Equiv.Perm.exists_fixed_point_of_prime' (p := 2) (n := 1) hcard hσ
    (a := ⟨1, mul_one 1⟩) (Subtype.ext (Subtype.ext (by simp [σ])))
  refine ⟨b.1, b.1.2, fun h => hb1 (Subtype.ext (Subtype.ext h)), congrArg Subtype.val b.2, ?_⟩
  have h2 : β * (b.1 : L) * β⁻¹ = b.1 :=
    congrArg (fun z : {x : ↥N // x * x = 1} => ((z.1 : ↥N) : L)) hb
  calc (b.1 : L) * β = (β * (b.1 : L) * β⁻¹) * β := by rw [h2]
    _ = β * b.1 := by group

theorem exists_invol_comm_of_conj {N : Type} [Group N]
    (hconj : ∀ a b : N, a ≠ 1 → a * a = 1 → b ≠ 1 → b * b = 1 → ∃ g : N, g * a * g⁻¹ = b)
    {v w : N} (hv : v ≠ 1) (hv2 : v * v = 1) (hw : w ≠ 1) (hw2 : w * w = 1) (hvw : v ≠ w)
    (hcomm : v * w = w * v) {b : N} (hb : b ≠ 1) (hb2 : b * b = 1) :
    ∃ d : N, d ≠ 1 ∧ d * d = 1 ∧ d ≠ b ∧ d * b = b * d := by
  obtain ⟨g, hg⟩ := hconj v b hv hv2 hb hb2
  refine ⟨g * w * g⁻¹, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hw
    have := congrArg (fun z => g⁻¹ * z * g) h
    simpa [mul_assoc] using this
  · calc g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
      _ = 1 := by rw [hw2]; simp
  · intro h
    apply hvw
    have h1 : g * w * g⁻¹ = g * v * g⁻¹ := h.trans hg.symm
    have := congrArg (fun z => g⁻¹ * z * g) h1
    simpa [mul_assoc] using this.symm
  · rw [← hg]
    calc g * w * g⁻¹ * (g * v * g⁻¹) = g * (w * v) * g⁻¹ := by group
      _ = g * (v * w) * g⁻¹ := by rw [hcomm]
      _ = g * v * g⁻¹ * (g * w * g⁻¹) := by group

theorem exists_two_commuting_involutions {N : Type} [Group N] [Finite N] (h : 2 ≤ pRank 2 N) :
    ∃ v w : N, v ≠ 1 ∧ v * v = 1 ∧ w ≠ 1 ∧ w * w = 1 ∧ v ≠ w ∧ v * w = w * v := by
  classical
  obtain ⟨A, hA, hcard⟩ := CFSG.StronglyEmbedded.SteinbergBU.exists_four_group_of_two_le_pRank h
  have : Fintype ↥A := Fintype.ofFinite _
  have hc4 : Fintype.card ↥A = 4 := by
    rw [← Nat.card_eq_fintype_card, hcard]
    norm_num
  have hcomm : ∀ x y : ↥A, x * y = y * x := fun x y =>
    hA.toIsMulCommutative.is_comm.comm x y
  have hsq : ∀ x : ↥A, x * x = 1 := fun x => by
    have : IsElementaryAbelian 2 ↥A := hA
    have hx2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) (x : N) x.2
    rw [pow_two] at hx2
    exact Subtype.ext hx2
  have hnt : Nontrivial ↥A := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨v, hv⟩ := exists_ne (1 : ↥A)
  have hex : ∃ w : ↥A, w ≠ 1 ∧ w ≠ v := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset ↥A) ⊆ {1, v} := fun x _ => by
      by_cases h1 : x = 1
      · simp [h1]
      · simp [hcon x h1]
    have := Finset.card_le_card hsub
    have h2 : ({1, v} : Finset ↥A).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ] at this
    omega
  obtain ⟨w, hw1, hwv⟩ := hex
  refine ⟨(v : N), (w : N), fun h => hv (Subtype.ext h), congrArg Subtype.val (hsq v),
    fun h => hw1 (Subtype.ext h), congrArg Subtype.val (hsq w), fun h => hwv (Subtype.ext h.symm),
    congrArg Subtype.val (hcomm v w)⟩

end S1L3PkgAbs

end CFSG.GH74.Generic.BProg.B3
