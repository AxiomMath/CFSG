module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
import CFSG.GH74.GLS.Stage1.Thm4.Pure
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2OuterInvolutionFusion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod.L145

open Subgroup CFSG CFSG.GorensteinWalter

section LcSec

variable {H : Type} [Group H] [Finite H] (L : Subgroup H) [L.Normal]

@[expose] noncomputable def Lc : Subgroup H := (commutator ↥L).map L.subtype

variable {L}

omit [Finite H] in
theorem Lc_normal : (Lc L).Normal := by
  unfold Lc
  exact ConjAct.normal_of_characteristic_of_normal

omit [Finite H] [L.Normal] in
theorem Lc_le : Lc L ≤ L := Subgroup.map_subtype_le _

omit [Finite H] [L.Normal] in
theorem mem_Lc_iff (a : ↥L) : (a : H) ∈ Lc L ↔ a ∈ commutator ↥L := by
  unfold Lc
  constructor
  · rintro ⟨b, hb, hba⟩
    have : b = a := Subtype.ext hba
    rw [← this]; exact hb
  · intro h; exact ⟨a, h, rfl⟩

variable {K : Type} [Field K] [Finite K]

omit [Finite H] [L.Normal] [Finite K] in
theorem map_commutator_equiv (e : ↥L ≃* PGL2 K) :
    (commutator ↥L).map e.toMonoidHom = commutator (PGL2 K) := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  rfl

omit [L.Normal] in
theorem Lc_equiv (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) (e : ↥L ≃* PGL2 K) :
    Nonempty (↥(Lc L) ≃* PSL2 K) := by
  obtain ⟨e1⟩ := commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three K hK hcard e
  exact ⟨(Subgroup.equivMapOfInjective (commutator ↥L) L.subtype L.subtype_injective).symm.trans e1⟩

theorem odd_of_isOddPrimePower {q : ℕ} (hK : IsOddPrimePower q) : Odd q := by
  obtain ⟨p, n, -, hp, -, rfl⟩ := hK
  exact hp.pow

omit [L.Normal] in
theorem card_L (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) (e : ↥L ≃* PGL2 K) :
    Nat.card L = 2 * Nat.card (Lc L) := by
  obtain ⟨e1⟩ := Lc_equiv hK hcard e
  rw [Nat.card_congr e.toEquiv, Nat.card_congr e1.toEquiv, pgl2_card_formula, psl2_card_formula K hK]
  obtain ⟨j, hj⟩ := odd_of_isOddPrimePower hK
  rw [hj]
  have h1 : (2 * j + 1) ^ 2 - 1 = 2 * (2 * j * (j + 1)) := by
    have : (2 * j + 1) ^ 2 = 2 * (2 * j * (j + 1)) + 1 := by ring
    omega
  rw [h1]
  have : (2 * j + 1) * (2 * (2 * j * (j + 1))) = 2 * ((2 * j + 1) * (2 * j * (j + 1))) := by ring
  rw [this, Nat.mul_div_cancel_left _ (by norm_num)]

omit [Finite K] in
theorem isInvolution_iff {G : Type*} [Group G] (g : G) :
    CFSG.BenderSuzuki.PFAppendixIII.IsInvolution g ↔ orderOf g = 2 := by
  unfold CFSG.BenderSuzuki.PFAppendixIII.IsInvolution
  rw [orderOf_eq_prime_iff]
  exact and_comm

omit [Finite H] [L.Normal] [Finite K] in
theorem Lc_simple (hcard : 3 < Nat.card K) (e1 : ↥(Lc L) ≃* PSL2 K) : IsSimpleGroup ↥(Lc L) :=
  (MulEquiv.isSimpleGroup_congr e1).2 (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega))

omit [Finite H] [L.Normal] in
theorem Lc_perfect (hcard : 3 < Nat.card K) (e1 : ↥(Lc L) ≃* PSL2 K) : Group.IsPerfect ↥(Lc L) := by
  have := psl2_isPerfect_of_card_gt_three K hcard
  exact Group.IsPerfect.ofSurjective (f := e1.symm.toMonoidHom) e1.symm.surjective

omit [Finite H] [L.Normal] in
theorem outer_conj (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) (e : ↥L ≃* PGL2 K)
    {u v : H} (hu : u ∈ L) (hv : v ∈ L) (hu2 : orderOf u = 2) (hv2 : orderOf v = 2)
    (hu' : u ∉ Lc L) (hv' : v ∉ Lc L) : ∃ l ∈ L, l * u * l⁻¹ = v := by
  have hI : ∀ {w : H} (hw : w ∈ L), orderOf w = 2 → w ∉ Lc L →
      CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (e ⟨w, hw⟩) ∧ e ⟨w, hw⟩ ∉ commutator (PGL2 K) := by
    intro w hw h2 hw'
    refine ⟨(isInvolution_iff _).2 ?_, ?_⟩
    · have := orderOf_injective e.toMonoidHom e.injective ⟨w, hw⟩
      rw [Subgroup.orderOf_mk, h2] at this
      exact this
    · intro hc
      rw [← map_commutator_equiv e] at hc
      obtain ⟨c, hc1, hc2⟩ := hc
      have hcw : c = ⟨w, hw⟩ := e.injective hc2
      rw [hcw] at hc1
      exact hw' ((mem_Lc_iff _).2 hc1)
  obtain ⟨hIu, hnu⟩ := hI hu hu2 hu'
  obtain ⟨hIv, hnv⟩ := hI hv hv2 hv'
  have h := pgl2_outer_involutions_conjugate K hK hcard hIu hIv hnu hnv
  rw [isConj_iff] at h
  obtain ⟨g, hg⟩ := h
  refine ⟨((e.symm g : ↥L) : H), (e.symm g).2, ?_⟩
  have : (e.symm g) * ⟨u, hu⟩ * (e.symm g)⁻¹ = ⟨v, hv⟩ := by
    apply e.injective
    simpa using hg
  exact congrArg Subtype.val this

omit [Finite H] [L.Normal] in
theorem inner_conj (hK : IsOddPrimePower (Nat.card K)) (e1 : ↥(Lc L) ≃* PSL2 K)
    {u v : H} (hu : u ∈ Lc L) (hv : v ∈ Lc L) (hu2 : orderOf u = 2) (hv2 : orderOf v = 2) :
    ∃ l ∈ Lc L, l * u * l⁻¹ = v := by
  have hI : ∀ {w : H} (hw : w ∈ Lc L), orderOf w = 2 →
      CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (e1 ⟨w, hw⟩) := by
    intro w hw h2
    refine (isInvolution_iff _).2 ?_
    have := orderOf_injective e1.toMonoidHom e1.injective ⟨w, hw⟩
    rw [Subgroup.orderOf_mk, h2] at this
    exact this
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power K hK _ _ (hI hu hu2) (hI hv hv2)
  refine ⟨((e1.symm g : ↥(Lc L)) : H), (e1.symm g).2, ?_⟩
  have : (e1.symm g) * ⟨u, hu⟩ * (e1.symm g)⁻¹ = ⟨v, hv⟩ := by
    apply e1.injective
    simpa using hg
  exact congrArg Subtype.val this

omit [Finite K] in
theorem two_elt_mem_L (hL : Odd L.index) {g : H} {m : ℕ} (hg : g ^ (2 ^ m) = 1) : g ∈ L := by
  have h1 : (QuotientGroup.mk g : H ⧸ L) ^ (2 ^ m) = 1 := by
    rw [← QuotientGroup.mk_pow, hg]; rfl
  have hodd : Odd (Nat.card (H ⧸ L)) := hL
  have := Stage1.Thm4.eq_one_of_pow_two_pow_of_odd hodd h1
  exact (QuotientGroup.eq_one_iff g).1 this

end LcSec

theorem mod8_of_not_dvd_sixteen {q : ℕ} (hq : Odd q) (h : ¬ 16 ∣ q * (q ^ 2 - 1)) :
    q % 8 = 3 ∨ q % 8 = 5 := by
  obtain ⟨j, rfl⟩ := hq
  by_contra hcon
  push Not at hcon
  have h1 : (2 * j + 1) % 8 = 1 ∨ (2 * j + 1) % 8 = 7 := by omega
  apply h
  rcases h1 with h1 | h1
  · obtain ⟨k, hk⟩ : ∃ k, 2 * j + 1 = 8 * k + 1 := ⟨(2 * j + 1) / 8, by omega⟩
    rw [hk]
    have : (8 * k + 1) ^ 2 - 1 = 16 * (4 * k ^ 2 + k) := by
      have : (8 * k + 1) ^ 2 = 16 * (4 * k ^ 2 + k) + 1 := by ring
      omega
    rw [this]
    exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
  · obtain ⟨k, hk⟩ : ∃ k, 2 * j + 1 = 8 * k + 7 := ⟨(2 * j + 1) / 8, by omega⟩
    rw [hk]
    have : (8 * k + 7) ^ 2 - 1 = 16 * (4 * k ^ 2 + 7 * k + 3) := by
      have : (8 * k + 7) ^ 2 = 16 * (4 * k ^ 2 + 7 * k + 3) + 1 := by ring
      omega
    rw [this]
    exact Dvd.dvd.mul_left (dvd_mul_right _ _) _

theorem card_eight_mul {n idx m : ℕ} (hidx : Odd idx) (hm : Odd m) (h : n * idx = 8 * m) :
    ∃ m', Odd m' ∧ n = 8 * m' := by
  have h8 : 8 ∣ n := by
    have : 8 ∣ n * idx := ⟨m, h⟩
    have hc : Nat.Coprime 8 idx := by
      have : Nat.Coprime 2 idx := (Nat.coprime_two_left).2 hidx
      simpa using Nat.Coprime.pow_left 3 this
    exact hc.dvd_of_dvd_mul_right this
  obtain ⟨m', rfl⟩ := h8
  refine ⟨m', ?_, rfl⟩
  have : m' * idx = m := by nlinarith
  rw [← this] at hm
  exact (Nat.odd_mul.1 hm).1

end CFSG.GH74.GLS.Stage1.Thm6.Prod.L145
