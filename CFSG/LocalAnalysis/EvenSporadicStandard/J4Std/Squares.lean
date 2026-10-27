module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Layer0J4
public import Certificates.Certificate25120

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.J4
  CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

theorem wordProd_sq_eq_eta (hM : MatFacts) {w : List ℤ} {c : ℕ}
    (h : chkSqRoot (locMats ()) (locInvs ()) w c = true) :
    wordProd xJ w * wordProd xJ w = eta uJ 11 c := by
  apply Mx_injective
  have := congrArg rowsMatrix (eqRows_iff.1 h)
  rw [rowsMatrix_mulRows, ← Mx_wordProd hM, ← Mx_eta hM 11 le_rfl] at this
  rwa [map_mul]

theorem chkSqRoot_parts :
    chkSqRoot (locMats ()) (locInvs ()) sqWordB 1 = true ∧
      chkSqRoot (locMats ()) (locInvs ()) sqWordA 3 = true :=
  Bool.and_eq_true_iff.1 Certificates.certificate25120

theorem exists_sq_eta_one (hM : MatFacts) :
    ∃ g : J, g * g = eta uJ 11 1 :=
  ⟨wordProd xJ sqWordB, wordProd_sq_eq_eta hM chkSqRoot_parts.1⟩

theorem exists_sq_eta_three (hM : MatFacts) :
    ∃ g : J, g * g = eta uJ 11 3 :=
  ⟨wordProd xJ sqWordA, wordProd_sq_eq_eta hM chkSqRoot_parts.2⟩

theorem exists_sq_of_mul_self_eq_one
    {r : J} (hr : r * r = 1) : ∃ c : J, c * c = r := by
  by_cases hne : r = 1
  · exact ⟨1, by rw [hne, mul_one]⟩
  rcases inv_conj_root j4Facts hr hne with h | h
  · obtain ⟨k, hk⟩ := isConj_iff.1 h
    obtain ⟨g, hg⟩ := exists_sq_eta_one j4Facts.mat
    exact ⟨k * g * k⁻¹, by rw [← hk, ← hg]; group⟩
  · obtain ⟨k, hk⟩ := isConj_iff.1 h
    obtain ⟨g, hg⟩ := exists_sq_eta_three j4Facts.mat
    exact ⟨k * g * k⁻¹, by rw [← hk, ← hg]; group⟩

theorem isSq_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .J4) {u : Y} (hu : u * u = 1) : ∃ c : Y, c * c = u := by
  obtain ⟨f⟩ := nonempty_mulEquiv_J h
  obtain ⟨c, hc⟩ := exists_sq_of_mul_self_eq_one (r := f u) (by rw [← map_mul, hu, map_one])
  exact ⟨f.symm c, f.injective (by rw [map_mul, MulEquiv.apply_symm_apply, hc])⟩

theorem isSq_subgroup_of_isSporadic
    {G : Type} [Group G] {L : Subgroup G} (h : IsSporadic L .J4) :
    ∀ u ∈ L, u * u = 1 → ∃ c ∈ L, c * c = u := by
  intro u hu hu2
  obtain ⟨c, hc⟩ := isSq_of_isSporadic h (u := ⟨u, hu⟩) (Subtype.ext hu2)
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.setting_j4'
    (h : StdHyp G L) (hL : IsSporadic L .J4) {z : G}
    (hz : z ∈ centralizer (L : Set G)) (hz2 : orderOf z = 2) : Setting L z :=
  h.setting_j4 hL (isSq_subgroup_of_isSporadic hL) hz hz2

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.exists_setting_j4
    (h : StdHyp G L) (hL : IsSporadic L .J4) :
    ∃ z : G, z ∈ centralizer (L : Set G) ∧ orderOf z = 2 ∧ Setting L z := by
  obtain ⟨S, -⟩ := h.cyclicSylow
  have h2 : Nat.card S = 2 := h.card_sylow_eq_two_j4 hL S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := (S : Subgroup (centralizer (L : Set G))))
    2 (by rw [h2])
  have hz2 : orderOf (((s : centralizer (L : Set G)) : G)) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hs]
  have hz : ((s : centralizer (L : Set G)) : G) ∈ centralizer (L : Set G) :=
    (s : centralizer (L : Set G)).2
  exact ⟨_, hz, hz2, h.setting_j4' hL hz hz2⟩

end CFSG.EvenSporadicStandard.J4Std
