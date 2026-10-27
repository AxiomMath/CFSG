module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511K
public import CFSG.GH74.GLS.C3.Layer1.Thm1GlueJ
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511H

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ABGLocalTools
  CFSG.GH74.GLS.IVK.Lifted GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem exists_commutator_test {D : Subgroup G} (hD : IsPGroup 2 D) (h16 : 16 ≤ Nat.card D)
    {r z : G} (hrD : r ∈ D) (hr2 : r * r = 1) (hr1 : r ≠ 1) (hzD : z ∈ D) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hzc : ∀ g ∈ D, g * z = z * g) (hrz : r ≠ z)
    (hC : ∀ g ∈ D, g * r = r * g → g = 1 ∨ g = r ∨ g = z ∨ g = r * z)
    (hnab : ∃ g ∈ D, g * r ≠ r * g) :
    ∃ v ∈ D, ∀ a ∈ D, a * a = 1 → (v * a * v⁻¹ * a⁻¹) * (v * a * v⁻¹ * a⁻¹) = 1 →
      a = 1 ∨ a = z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set b : D := ⟨r, hrD⟩ with hbdef
  set c : D := ⟨z, hzD⟩ with hcdef
  have hb2 : b * b = 1 := Subtype.ext hr2
  have hc2 : c * c = 1 := Subtype.ext hz2
  have hbc : Commute b c := Subtype.ext (hzc r hrD)
  have hb1 : b ≠ 1 := fun h1 => hr1 (congrArg Subtype.val h1)
  have hc1 : c ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
  have hbcne : b ≠ c := fun h1 => hrz (congrArg Subtype.val h1)
  set V := kleinFourOfCommutingInvolutions b c hb2 hc2 hbc with hVdef
  have hV4 : Nat.card V = 4 :=
    (isKleinFour_kleinFourOfCommutingInvolutions b c hb2 hc2 hb1 hc1 hbcne hbc).card_four
  have hVsq : ∀ x ∈ V, x * x = 1 := fun x hx => by
    rcases (mem_kleinFour_iff hb2 hc2 hbc).mp hx with h1 | h1 | h1 | h1 <;> rw [h1]
    · rw [show b * c * (b * c) = b * (c * b) * c by group, ← hbc.eq,
        show b * (b * c) * c = (b * b) * (c * c) by group, hb2, hc2, one_mul]
    · exact hb2
    · exact hc2
    · exact one_mul 1
  have hCV : centralizer ({b} : Set D) = V := by
    ext g
    rw [mem_centralizer_singleton_iff, mem_kleinFour_iff hb2 hc2 hbc]
    constructor
    · intro hg
      rcases hC g g.2 (congrArg Subtype.val hg) with h1 | h1 | h1 | h1
      · exact Or.inr (Or.inr (Or.inr (Subtype.ext h1)))
      · exact Or.inr (Or.inl (Subtype.ext h1))
      · exact Or.inr (Or.inr (Or.inl (Subtype.ext h1)))
      · exact Or.inl (Subtype.ext h1)
    · rintro (h1 | h1 | h1 | h1)
      · rw [h1, mul_assoc, ← hbc.eq, ← mul_assoc]
      · rw [h1]
      · rw [h1]
        exact hbc.eq.symm
      · rw [h1, one_mul, mul_one]
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb2) hb1
  have hmax := GH74.GLS.C3.Layer1.Thm1.isMaximalClassTwoGroup_of_card_centralizer hD hbo
    (by rw [hCV, hV4])
  have hnc : ¬ IsMulCommutative D := by
    intro hcomm
    obtain ⟨g, hg, hgr⟩ := hnab
    exact hgr (congrArg Subtype.val (hcomm.is_comm.comm ⟨g, hg⟩ b))
  have hNMC : GH74.GLS.IsNonabelianMaximalClassTwoGroup D := by
    refine ⟨hD, hnc, ?_⟩
    obtain ⟨hn, heq⟩ := hmax.2
    exact ⟨hn, heq.symm⟩
  obtain ⟨A, u, hA, hu, hu4, hout, hinv⟩ := dsdData_of_maxClass hNMC ⟨V, hVsq, hV4⟩
  obtain ⟨v, hv⟩ := dsd_exists_test hD hA hu hu4 hout hinv hc2 hc1
    (fun g => Subtype.ext (hzc g g.2)) h16
  refine ⟨v, v.2, fun a ha ha2 hca => ?_⟩
  rcases hv ⟨a, ha⟩ (Subtype.ext ha2) (Subtype.ext (by simpa using hca)) with h1 | h1
  · exact Or.inl (congrArg Subtype.val h1)
  · exact Or.inr (congrArg Subtype.val h1)

omit [Finite G] in
theorem mem_or_mul_mem_of_mem_sup {Q : Subgroup G} {r : G} (hr2 : r * r = 1)
    (hrQ : r ∈ normalizer (Q : Set G)) {x : G} (hx : x ∈ Q ⊔ zpowers r) : x ∈ Q ∨ x * r ∈ Q := by
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hconj : ∀ q ∈ Q, r * q * r⁻¹ ∈ Q := fun q hq => (mem_normalizer_iff.mp hrQ q).mp hq
  let H : Subgroup G :=
    { carrier := {x | x ∈ Q ∨ x * r ∈ Q}
      one_mem' := Or.inl (one_mem Q)
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (mul_mem hx hy)
        · exact Or.inr (by rw [mul_assoc]; exact mul_mem hx hy)
        · right
          have h1 := hconj y hy
          rw [hri] at h1
          rw [show x * y * r = (x * r) * (r * y * r) by
            rw [show (x * r) * (r * y * r) = x * (r * r) * y * r by group, hr2, mul_one]]
          exact mul_mem hx h1
        · left
          have h1 := hconj _ hy
          rw [hri, show r * (y * r) * r = r * y * (r * r) by group, hr2, mul_one] at h1
          rw [show x * y = (x * r) * (r * y) by
            rw [show (x * r) * (r * y) = x * (r * r) * y by group, hr2, mul_one]]
          exact mul_mem hx h1
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (inv_mem hx)
        · right
          have h1 := hconj _ (inv_mem hx)
          rwa [hri, show r * (x * r)⁻¹ * r = x⁻¹ * r by
            rw [mul_inv_rev, hri]
            calc r * (r * x⁻¹) * r = (r * r) * x⁻¹ * r := by group
              _ = x⁻¹ * r := by rw [hr2, one_mul]] at h1 }
  have hle : Q ⊔ zpowers r ≤ H :=
    sup_le (fun q hq => Or.inl hq) (zpowers_le.mpr (Or.inr (by rw [hr2]; exact one_mem Q)))
  exact hle hx

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem exists_test_Q_sup (hQ : 4 < Nat.card Q) {r : G} (hrS : r ∈ S) (hr2 : r * r = 1)
    (hrQ : r ∉ Q) (hrz : r * z = z * r)
    (hcard : Nat.card ↥(Q ⊓ centralizer ({r} : Set G)) ≤ 2) :
    ∃ v ∈ Q ⊔ zpowers r, ∀ a ∈ Q ⊔ zpowers r, a * a = 1 →
      (v * a * v⁻¹ * a⁻¹) * (v * a * v⁻¹ * a⁻¹) = 1 → a = 1 ∨ a = z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 := h.z_mul_self
  have hz1 : z ≠ 1 := fun h1 => by
    have := h.z2
    rw [h1, orderOf_one] at this
    omega
  have hrN := h.S_le_normalizer_Q hrS
  set D := Q ⊔ zpowers r with hDdef
  have hDS : D ≤ S := sup_le h.QS (zpowers_le.mpr hrS)
  have hdisj : Q ⊓ zpowers r = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases eq_one_or_eq_of_mem_zpowers_sq hr2 (mem_inf.mp hx).2 with h1 | h1
    · rw [h1]; exact one_mem _
    · exact absurd (h1 ▸ (mem_inf.mp hx).1) hrQ
  have hr1 : r ≠ 1 := fun h1 => hrQ (h1 ▸ one_mem Q)
  have hro : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hr2) hr1
  have hDcard : Nat.card D = Nat.card Q * 2 := by
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer Q (zpowers r)
      (zpowers_le.mpr hrN) (disjoint_iff.mpr hdisj), Nat.card_zpowers, hro]
  have hQ8 : 8 ≤ Nat.card Q := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_Q
    rw [hk] at hQ ⊢
    have hk3 : 3 ≤ k := by
      by_contra h2
      push Not at h2
      have h3 : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h3
      omega
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
  have hzc : ∀ g ∈ D, g * z = z * g := fun g hg => h.zS g (hDS hg)
  have hzCr : z ∈ Q ⊓ centralizer ({r} : Set G) :=
    mem_inf.mpr ⟨h.zQ, mem_centralizer_singleton_iff.mpr hrz.symm⟩
  have hCQ : ∀ q ∈ Q, q * r = r * q → q = 1 ∨ q = z := fun q hq hqr =>
    eq_one_or_eq_of_card_le_two hcard hzCr hz1
      (mem_inf.mpr ⟨hq, mem_centralizer_singleton_iff.mpr hqr⟩)
  have hC : ∀ g ∈ D, g * r = r * g → g = 1 ∨ g = r ∨ g = z ∨ g = r * z := by
    intro g hg hgr
    rcases mem_or_mul_mem_of_mem_sup hr2 hrN hg with hgQ | hgQ
    · rcases hCQ g hgQ hgr with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr (Or.inl h1))
    · have hq : (g * r) * r = r * (g * r) := by
        rw [mul_assoc, hr2, mul_one, hgr, ← mul_assoc, hr2, one_mul]
      rcases hCQ _ hgQ hq with h1 | h1
      · right; left
        calc g = g * r * r := by rw [mul_assoc, hr2, mul_one]
          _ = r := by rw [h1, one_mul]
      · right; right; right
        calc g = g * r * r := by rw [mul_assoc, hr2, mul_one]
          _ = r * z := by rw [h1, hrz]
  have hnab : ∃ g ∈ D, g * r ≠ r * g := by
    by_contra hall
    push Not at hall
    have hsub : Q ≤ Q ⊓ centralizer ({r} : Set G) := fun q hq =>
      mem_inf.mpr ⟨hq, mem_centralizer_singleton_iff.mpr (hall q (mem_sup_left hq))⟩
    have := card_le_of_le hsub
    omega
  have hrz' : r ≠ z := fun h1 => hrQ (h1 ▸ h.zQ)
  exact exists_commutator_test (h.isPGroup_S.to_le hDS) (by rw [hDcard]; omega)
    (mem_sup_right (mem_zpowers r)) hr2 hr1 (mem_sup_left h.zQ) hz2 hz1 hzc hrz' hC hnab

end Sec5

end CFSG.ComponentClassification.Foote5
