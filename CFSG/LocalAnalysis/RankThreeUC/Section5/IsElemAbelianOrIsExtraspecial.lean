module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.Foundations.Basic

public section

open scoped commutatorElement

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_or_isExtraspecial {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h51 : OddPrimeClassTwoAction G p P T B e) (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ) :
    CFSG.Open.IsElemAbelian p P ∨ CFSG.IsExtraspecialPGroup p ↥P := by
  classical
  have hset := h51.setting
  have hp : p.Prime := hset.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hexp : ∀ x ∈ P, x ^ p = 1 := by
    intro x hx
    have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : ↥P)
    rw [hset.exponent] at h
    exact congrArg Subtype.val h
  by_cases hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a
  · left
    exact ⟨⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩, hexp⟩
  · right
    push Not at hab
    obtain ⟨a, ha, b, hb, hab'⟩ := hab
    have hwP : ⁅a, b⁆ ∈ P := by
      rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
    have hwne : ⁅a, b⁆ ≠ 1 := fun h => hab' (commutatorElement_eq_one_iff_mul_comm.mp h)
    have hcomm2 : ∀ x ∈ P, ∀ y ∈ P, ∀ g ∈ P, ⁅x, y⁆ * g = g * ⁅x, y⁆ := by
      intro x hx y hy g hg
      have h1 : ⁅⁅x, y⁆, g⁆ = 1 := by
        have hmem : ⁅⁅x, y⁆, g⁆ ∈ ⁅⁅P, P⁆, P⁆ :=
          Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator hx hy) hg
        rw [hset.class_le_two] at hmem
        simpa using hmem
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    set Q : Subgroup G := P ⊓ Subgroup.centralizer (P : Set G) with hQ_def
    have hQP : Q ≤ P := inf_le_left
    have hQc : ∀ q ∈ Q, ∀ h ∈ P, h * q = q * h := fun q hq h hh =>
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hq).2) h hh
    have hwQ : ⁅a, b⁆ ∈ Q := Subgroup.mem_inf.mpr ⟨hwP, fun h hh => (hcomm2 a ha b hb h hh).symm⟩
    have hQn : Q.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hn' := Subgroup.mem_inf.mp hn
      refine Subgroup.mem_inf.mpr ⟨h53.normal.conj_mem n hn'.1 g, fun h hh => ?_⟩
      have hk := hn'.2 (g⁻¹ * h * g⁻¹⁻¹) (h53.normal.conj_mem h hh g⁻¹)
      rw [inv_inv] at hk
      calc h * (g * n * g⁻¹) = g * ((g⁻¹ * h * g) * n) * g⁻¹ := by group
        _ = g * (n * (g⁻¹ * h * g)) * g⁻¹ := by rw [hk]
        _ = (g * n * g⁻¹) * h := by group
    have hQcard : CFSG.Open.pRank p Q ≤ 1 := by
      by_contra hc
      push Not at hc
      have hQeq : Q = P := h53.minimal Q hQn hc hQP
      apply hab'
      have haQ : a ∈ Q := by rw [hQeq]; exact ha
      exact (hQc a haQ b hb).symm
    have hQab : IsMulCommutative Q :=
      ⟨⟨fun x y => Subtype.ext (hQc x.1 x.2 y.1 (hQP y.2)).symm⟩⟩
    have hQpg : IsPGroup p Q := hset.pGroup.to_le hQP
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hQpg
    have hbdd : BddAbove {k | ∃ E : Subgroup G, E ≤ Q ∧ CFSG.Open.IsElemAbelian p E ∧
        Nat.card E = p ^ k} := by
      refine ⟨Nat.card G, fun k hk => ?_⟩
      obtain ⟨E, _, _, hE⟩ := hk
      have h1 : k < p ^ k := Nat.lt_pow_self hp.one_lt
      have h2 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
      omega
    have hwmemQ : Nat.card (Subgroup.zpowers (⁅a, b⁆)) = p := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hexp _ hwP) hwne
    have hpQ : p ≤ Nat.card Q := by
      have h := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hwQ)
      rw [hwmemQ] at h
      exact h
    have hnle : n ≤ 1 := by
      by_contra hc
      push Not at hc
      have : n ≤ CFSG.Open.pRank p Q := le_csSup hbdd ⟨Q, le_rfl, ⟨hQab, fun x hx => hexp x (hQP hx)⟩, hn⟩
      omega
    have hQeq : Nat.card Q = p := by
      interval_cases n
      · rw [pow_zero] at hn
        have := hp.two_le
        omega
      · rw [pow_one] at hn
        exact hn
    have hcenter_iff : ∀ z : ↥P, z ∈ Subgroup.center ↥P ↔ z.1 ∈ Q := by
      intro z
      rw [Subgroup.mem_center_iff]
      constructor
      · intro hz
        refine Subgroup.mem_inf.mpr ⟨z.2, fun h hh => ?_⟩
        have h2 := congrArg Subtype.val (hz ⟨h, hh⟩)
        simpa using h2
      · intro hz g
        apply Subtype.ext
        exact (hQc z.1 hz g.1 g.2)
    have hcardC : Nat.card (Subgroup.center ↥P) = p := by
      have hmap : (Subgroup.center ↥P).map P.subtype = Q := by
        ext x
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact (hcenter_iff z).mp hz
        · intro hx
          exact ⟨⟨x, hQP hx⟩, (hcenter_iff _).mpr hx, rfl⟩
      have h := Subgroup.card_map_of_injective (K := Subgroup.center ↥P) P.subtype_injective
      rw [hmap, hQeq] at h
      exact h.symm
    set wP : ↥P := ⟨⁅a, b⁆, hwP⟩ with hwP_def
    have hwPp : wP ^ p = 1 := Subtype.ext (by simp only [Subgroup.coe_pow, Subgroup.coe_one]; exact hexp _ hwP)
    have hwPne : wP ≠ 1 := fun h => hwne (congrArg Subtype.val h)
    have hzpc : Subgroup.zpowers wP = Subgroup.center ↥P := by
      apply Subgroup.eq_of_le_of_card_ge
      · rw [Subgroup.zpowers_le]; exact (hcenter_iff wP).mpr hwQ
      · rw [hcardC, Nat.card_zpowers, orderOf_eq_prime hwPp hwPne]
    have hwPcomm : wP ∈ commutator ↥P := by
      have hw' : wP = ⁅(⟨a, ha⟩ : ↥P), ⟨b, hb⟩⁆ := Subtype.ext rfl
      rw [hw']
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have hcomm : commutator ↥P = Subgroup.center ↥P := by
      apply le_antisymm
      · show ⁅(⊤ : Subgroup ↥P), ⊤⁆ ≤ _
        rw [Subgroup.commutator_le]
        intro g₁ _ g₂ _
        rw [hcenter_iff]
        have hc : (⁅g₁, g₂⁆ : ↥P).1 = ⁅g₁.1, g₂.1⁆ := by simp [commutatorElement_def]
        rw [hc]
        exact Subgroup.mem_inf.mpr ⟨P.mul_mem (P.mul_mem (P.mul_mem g₁.2 g₂.2) (P.inv_mem g₁.2)) (P.inv_mem g₂.2),
          fun h hh => (hcomm2 g₁.1 g₁.2 g₂.1 g₂.2 h hh).symm⟩
      · rw [← hzpc, Subgroup.zpowers_le]; exact hwPcomm
    have hfr : frattini ↥P = Subgroup.center ↥P := by
      haveI : Fact (IsPGroup p ↥P) := ⟨hset.pGroup⟩
      rw [← hcomm, CFSG.frattini_eq_closure_commutator_union_powers (p := p)]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro y (hy | ⟨x, rfl⟩)
        · exact hy
        · have hx : x ^ p = 1 := Subtype.ext (by simpa using hexp x.1 x.2)
          simp only [hx]
          exact one_mem _
      · intro y hy
        exact Subgroup.subset_closure (Or.inl hy)
    exact ⟨hset.pGroup, hcomm, hfr, hcardC⟩

end Section5

end CFSG.LocalAnalysis.RankThreeUC
