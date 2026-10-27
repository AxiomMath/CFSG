module

public import CFSG.ClassicalInvolution.Q3.TL4LinkB2b4
public import CFSG.ClassicalInvolution.Q3.TL4ConnDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem pair_cases (hΩ : TypeRFam r Ω) (hr : 3 ≤ r) {A B : Subgroup G} (hA : A ∈ Ω) (hB : B ∈ Ω)
    {a b : G} (ha : IsUniqueInvolution A a) (hb : IsUniqueInvolution B b) (hne : a ≠ b)
    {V : Subgroup G} (hV : IsSylow2In V (B ⊓ Subgroup.centralizer ({a} : Set G))) (hbV : b ∈ V) :
    B ∈ omegaNbr Ω A ∨
      (V = Subgroup.zpowers b ∧ ∀ R : Subgroup G, IsSylow2In R A →
        b ∈ Subgroup.normalizer (R : Set G) → Outer R b) ∨
      V ∈ USet Ω := by
  have hP : Sec6Gen.Pair Ω A B a b := ⟨hA, hB, ha, hb, hne⟩
  have hnt : B ∉ twinSet Ω A := by
    rintro ⟨-, z, hz, hz'⟩
    exact hne ((ha.eq hz).trans (hb.eq hz').symm)
  have hVN : V ≤ Subgroup.normalizer (A : Set G) := fun v hv =>
    hΩ.tight A hA a ha (Subgroup.mem_inf.mp (hV.1 hv)).2
  rcases Sec6Gen.l6_2Gen G Ω hΩ.hyp A hA a ha B hB hnt b hb V hV hbV with
    ⟨-, hbA⟩ | ⟨hVb, -⟩ | ⟨hVU, -⟩ | ⟨hVR, -⟩
  · exact absurd (mem_normalizer_iff_conjSub_eq.mp (hVN hbV)) hbA
  · refine Or.inr (Or.inl ⟨hVb, fun R hR _ => ?_⟩)
    intro w hw hwb
    by_contra hww
    have hwA : w ∈ A := hR.1 hw
    have hw2 : IsPGroup 2 (Subgroup.zpowers w) := hR.2.1.to_le (Subgroup.zpowers_le.mpr hw)
    obtain ⟨i, hi⟩ := hw2.exists_card_eq
    rw [Nat.card_zpowers] at hi
    have hw1 : w ≠ 1 := by
      rintro rfl
      exact hww (mul_one 1)
    obtain ⟨u, hu, hu2, hu1⟩ := AscL62.exists_involution_pow hw1 hi
    have hua : u = a :=
      (ha.unique u (Subgroup.zpowers_le.mpr hwA hu) hu2).resolve_left hu1
    have haW : a ∈ Subgroup.zpowers w := hua ▸ hu
    have hWc : Subgroup.zpowers w ≤ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hwb)
    have hi2 : 2 ≤ i := by
      by_contra hlt
      apply hww
      rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, hi]
      exact (pow_dvd_pow 2 (show i ≤ 1 by omega)).trans (by norm_num)
    have hW4 : 4 ≤ Nat.card (Subgroup.zpowers w) := by
      rw [Nat.card_zpowers, hi]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi2
    obtain ⟨-, RB, hRB, -, hRB4, -⟩ :=
      hP.bootstrap hΩ.hyp (Subgroup.zpowers_le.mpr hwA) hw2 haW hWc hW4
    have hle := hV.natCard_le hRB.2.1.to_inf_left (inf_le_inf_right _ hRB.1)
    have hV2 : Nat.card V = 2 := by
      rw [hVb, Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact hb.sq) hb.ne_one
    omega
  · exact Or.inr (Or.inr hVU)
  · exact Or.inl ⟨hB, fun h => hne (ha.eq (h ▸ hb)), V, hVR, hV.1.trans inf_le_left, hVN⟩

end CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b
