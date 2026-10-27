module

public import CFSG.GH74.GLS.SP.Local.SPLOrdG1
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open CFSG.ShultStronglyClosedTI.InvolutionCounting
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

section G2

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

@[expose] def Utset : Set G :=
  {a | (∃ g ∈ D.K₁, a = g * D.t * g⁻¹) ∨ (a ∈ D.K₁ ⊔ D.K₂ ∧ a * a = 1 ∧ a ≠ 1 ∧ a ≠ D.z)}

@[expose] def Uzset : Set G := {b | b = D.z ∨ ∃ g ∈ D.K₁, b = g * (D.t * D.z) * g⁻¹}

omit [Finite G] in
theorem not_isConj_t_z (hs : SPLSetup D.toSPLNot0) : ¬ IsConj D.t D.z :=
  fun h => hs.syl.t_nconj h.symm

theorem Kt_cases (hs : SPLSetup D.toSPLNot0) {a : G} (ha : a ∈ D.Kt) :
    a ∈ D.K ∨ a * D.t ∈ D.K := by
  have htt := t_mul_t D hs
  obtain ⟨κ, hκ, τ, hτ, rfl⟩ := mem_sup_of_le_normalizer (t_le_normalizer_K D hs) ha
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hτ
  have h2 : ∀ m : ℤ, D.t ^ (2 * m) = 1 := fun m => by rw [zpow_mul, zpow_two, htt, one_zpow]
  rcases Int.even_or_odd' i with ⟨m, rfl | rfl⟩
  · left; rw [h2, mul_one]; exact hκ
  · right
    have h1 : D.t ^ (2 * m + 1) = D.t := by rw [zpow_add_one, h2, one_mul]
    rw [h1]
    have e : κ * D.t * D.t = κ := by
      calc κ * D.t * D.t = κ * (D.t * D.t) := by group
        _ = κ := by rw [htt, mul_one]
    rw [e]; exact hκ

omit [Finite G] in
theorem orderOf_eq_two_of_sq (a : G) (h : a * a = 1) (h1 : a ≠ 1) : orderOf a = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h) h1

omit [Finite G] in
theorem mul_self_of_orderOf_two {a : G} (h : orderOf a = 2) : a * a = 1 := by
  have := pow_orderOf_eq_one a
  rwa [h, pow_two] at this

theorem Ut_iff (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) {a : G} (haC : a ∈ D.C)
    (ha2 : orderOf a = 2) : IsConj D.t a ↔ a ∈ Utset D := by
  have htt := t_mul_t D hs
  constructor
  · intro hta
    have haa := mul_self_of_orderOf_two ha2
    have haKt := inv_C_le_Kt D hs hc haC haa
    rcases Kt_cases D hs haKt with hK | hK
    · right
      refine ⟨hK, haa, ?_, ?_⟩
      · intro h1; rw [h1, orderOf_one] at ha2; exact absurd ha2 (by norm_num)
      · intro hz; rw [hz] at hta; exact not_isConj_t_z D hs hta
    · left
      have hinv : (a * D.t) * D.t * ((a * D.t) * D.t) = 1 := by
        have e : a * D.t * D.t = a := by
          calc a * D.t * D.t = a * (D.t * D.t) := by group
            _ = a := by rw [htt, mul_one]
        rw [e]; exact haa
      obtain ⟨g, hg, hg'⟩ := kt_involution D hs hK hinv
      have e : a * D.t * D.t = a := by
        calc a * D.t * D.t = a * (D.t * D.t) := by group
          _ = a := by rw [htt, mul_one]
      rw [e] at hg'
      rcases hg' with h1 | h1
      · exact ⟨g, hg, h1⟩
      · exfalso
        have h3 : IsConj (D.t * D.z) a := isConj_iff.mpr ⟨g, h1.symm⟩
        have h4 : IsConj D.z a := hs.syl.tz_conj.trans h3
        exact hs.syl.t_nconj (h4.trans hta.symm)
  · rintro (⟨g, -, h1⟩ | ⟨hK, haa, h1, hz⟩)
    · exact isConj_iff.mpr ⟨g, h1.symm⟩
    · exact hs.syl.inv_K hK (orderOf_eq_two_of_sq a haa h1) hz

theorem Uz_iff (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) {b : G} (hbC : b ∈ D.C)
    (hb2 : orderOf b = 2) : IsConj D.z b ↔ b ∈ Uzset D := by
  have htt := t_mul_t D hs
  constructor
  · intro hzb
    have hbb := mul_self_of_orderOf_two hb2
    have hbKt := inv_C_le_Kt D hs hc hbC hbb
    rcases Kt_cases D hs hbKt with hK | hK
    · by_cases hz : b = D.z
      · left; exact hz
      · exfalso
        have htb : IsConj D.t b := hs.syl.inv_K hK hb2 hz
        exact hs.syl.t_nconj (hzb.trans htb.symm)
    · right
      have e : b * D.t * D.t = b := by
        calc b * D.t * D.t = b * (D.t * D.t) := by group
          _ = b := by rw [htt, mul_one]
      have hinv : (b * D.t) * D.t * ((b * D.t) * D.t) = 1 := by rw [e]; exact hbb
      obtain ⟨g, hg, hg'⟩ := kt_involution D hs hK hinv
      rw [e] at hg'
      rcases hg' with h1 | h1
      · exfalso
        have htb : IsConj D.t b := isConj_iff.mpr ⟨g, h1.symm⟩
        exact hs.syl.t_nconj (hzb.trans htb.symm)
      · exact ⟨g, hg, h1⟩
  · rintro (h | ⟨g, -, h1⟩)
    · rw [h]
    · have h3 : IsConj (D.t * D.z) b := isConj_iff.mpr ⟨g, h1.symm⟩
      exact hs.syl.tz_conj.trans h3

theorem Utset_le_C (hs : SPLSetup D.toSPLNot0) : Utset D ⊆ (D.C : Set G) := by
  rintro a (⟨g, hg, rfl⟩ | ⟨hK, -⟩)
  · have hgC : g ∈ D.C := K_le_C D hs (Subgroup.mem_sup_left hg)
    have htC : D.t ∈ D.C := t_mem_Cz hs
    exact D.C.mul_mem (D.C.mul_mem hgC htC) (D.C.inv_mem hgC)
  · exact K_le_C D hs hK

theorem thompsonPairs_z_eq (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    thompsonPairs D.t D.z D.z =
      {p : G × G | p.1 ∈ Utset D ∧ p.2 ∈ Uzset D ∧ D.z ∈ zpowers (p.1 * p.2)} := by
  have htt := t_mul_t D hs
  have hzz := z_mul_z D hs
  ext p
  constructor
  · intro hp
    have hcen := mem_centralizer_of_mem_thompsonPairs htt hzz hzz hp
    obtain ⟨h1, h2, h3⟩ := hp
    have ha2 : orderOf p.1 = 2 := by
      rw [← CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj h1]; exact hs.syl.t_ord
    have hb2 : orderOf p.2 = 2 := by
      rw [← CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj h2]; exact hs.syl.z_inv
    exact ⟨(Ut_iff D hs hc hcen.1 ha2).mp h1, (Uz_iff D hs hc hcen.2 hb2).mp h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    have hpt : IsConj D.t p.1 := by
      rcases h1 with ⟨g, -, hg⟩ | ⟨hK, haa, ha1, haz⟩
      · exact isConj_iff.mpr ⟨g, hg.symm⟩
      · exact hs.syl.inv_K hK (orderOf_eq_two_of_sq _ haa ha1) haz
    have hpz : IsConj D.z p.2 := by
      rcases h2 with h | ⟨g, -, hg⟩
      · rw [h]
      · exact hs.syl.tz_conj.trans (isConj_iff.mpr ⟨g, hg.symm⟩)
    exact ⟨hpt, hpz, h3⟩

end G2

end CFSG.GH74.GLS.SP.Local
