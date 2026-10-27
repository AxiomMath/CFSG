module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DPhase2

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_coreOf_iff {p : ℕ} {X : Subgroup G} (y : ↥X) :
    (y : G) ∈ GLAPPrimeCoreOf p X ↔ y ∈ GLAPPrimeCore p ↥X :=
  Subgroup.mem_map_iff_mem X.subtype_injective

theorem mem_coreOf_iff' {p : ℕ} {X : Subgroup G} {y : G} :
    y ∈ GLAPPrimeCoreOf p X ↔ ∃ h : y ∈ X, (⟨y, h⟩ : ↥X) ∈ GLAPPrimeCore p ↥X := by
  constructor
  · intro hy
    obtain ⟨⟨z, hz⟩, hzc, rfl⟩ := hy
    exact ⟨hz, hzc⟩
  · rintro ⟨h, hc⟩
    exact (mem_coreOf_iff ⟨y, h⟩).2 hc

theorem mk_eq_iff_of_pgroup {X R : Subgroup G} (hR : IsPGroup 3 ↥R) (hRX : R ≤ X) {r s : G}
    (hr : r ∈ R) (hs : s ∈ R)
    (h : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨r, hRX hr⟩ =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨s, hRX hs⟩) : r = s := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := QuotientGroup.eq.1 h
  have h2 : r⁻¹ * s ∈ GLAPPrimeCoreOf 3 X :=
    mem_coreOf_iff'.2 ⟨X.mul_mem (X.inv_mem (hRX hr)) (hRX hs), h1⟩
  have h3 : r⁻¹ * s ∈ R := R.mul_mem (R.inv_mem hr) hs
  have h4 : r⁻¹ * s ∈ R ⊓ GLAPPrimeCoreOf 3 X := ⟨h3, h2⟩
  rw [pgroup_inf_core_eq_bot X hR, Subgroup.mem_bot] at h4
  exact (inv_mul_eq_one.1 h4)

theorem card_barX_mul_card_inf {X K : Subgroup G} (hKX : K ≤ X) :
    Nat.card ↥(barX 3 X K) * Nat.card ↥(K ⊓ GLAPPrimeCoreOf 3 X) = Nat.card ↥K := by
  set f : ↥(K.subgroupOf X) →* ↥X ⧸ GLAPPrimeCore 3 ↥X :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).comp (K.subgroupOf X).subtype with hf
  have hrange : f.range = barX 3 X K := by
    ext z
    rw [MonoidHom.mem_range]
    unfold barX
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w.1, w.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
  have hker : Nat.card f.ker = Nat.card ↥(K ⊓ GLAPPrimeCoreOf 3 X) := by
    set φ : ↥(K.subgroupOf X) →* G := X.subtype.comp (K.subgroupOf X).subtype with hφ
    have hφi : Function.Injective φ := X.subtype_injective.comp (K.subgroupOf X).subtype_injective
    have hmap : f.ker.map φ = K ⊓ GLAPPrimeCoreOf 3 X := by
      ext z
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hw1 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) w.1 = 1 := hw
        have hw2 : w.1 ∈ GLAPPrimeCore 3 ↥X := (QuotientGroup.eq_one_iff _).1 hw1
        refine ⟨(Subgroup.mem_subgroupOf).1 w.2, ?_⟩
        exact mem_coreOf_iff'.2 ⟨w.1.2, hw2⟩
      · rintro ⟨hzK, hzO⟩
        obtain ⟨hzX, hz⟩ := mem_coreOf_iff'.1 hzO
        refine ⟨⟨⟨z, hzX⟩, (Subgroup.mem_subgroupOf).2 hzK⟩, ?_, rfl⟩
        exact (QuotientGroup.eq_one_iff _).2 hz
    rw [← hmap]
    exact (Subgroup.card_map_of_injective hφi).symm
  have hdom : Nat.card ↥(K.subgroupOf X) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv
  have := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange, hdom] at this
  rw [mul_comm]
  exact this

theorem barCenterX_eq_barX_Zc {X S : Subgroup G} (hS : IsPGroup 3 ↥S) (hSX : S ≤ X) :
    barCenterX 3 X S = barX 3 X (Zc S) := by
  apply le_antisymm
  · intro ζ hζ
    rw [mem_barCenterX_iff] at hζ
    obtain ⟨⟨z, hzX⟩, hzS, rfl⟩ := mem_barX_iff.1 hζ.1
    refine mem_barX_iff.2 ⟨⟨z, hzX⟩, mem_Zc.2 ⟨hzS, fun r hr => ?_⟩, rfl⟩
    have h := hζ.2 (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨r, hSX hr⟩)
      (mem_barX_iff.2 ⟨⟨r, hSX hr⟩, hr, rfl⟩)
    rw [← map_mul, ← map_mul] at h
    exact mk_eq_iff_of_pgroup hS hSX (S.mul_mem hzS hr) (S.mul_mem hr hzS) h
  · exact barX_Zc_le_barCenterX hSX

theorem card_barCenterX_of_heis {X S : Subgroup G} (hS : IsThreeOnePlusTwo S) (hSX : S ≤ X) :
    Nat.card ↥(barCenterX 3 X S) = 3 := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSp : IsPGroup 3 ↥S := by
    apply IsPGroup.of_card (n := 3)
    rw [hS.2.1]; norm_num
  rw [barCenterX_eq_barX_Zc hSp hSX]
  have hZp : IsPGroup 3 ↥(Zc S) := hSp.to_le (Zc_le S)
  rw [card_barX_of_isPGroup Nat.prime_three ((Zc_le S).trans hSX) hZp]
  exact hS.card_Zc

omit [Finite G] in
theorem center_quot_center_eq_bot {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    Subgroup.center (Q ⧸ Subgroup.center Q) = ⊥ := by
  obtain ⟨hperf, hsimple⟩ := h
  have := hsimple
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center (Q ⧸ Subgroup.center Q)) with h0 | h0
  · exact h0
  · exfalso
    have hab : ∀ a b : Q ⧸ Subgroup.center Q, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top b : b ∈ Subgroup.center _) a)
    have hcomm : commutator Q ≤ Subgroup.center Q := by
      rw [commutator_eq_closure]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨a, b, rfl⟩
      rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff]
      have h1 := map_commutatorElement (QuotientGroup.mk' (Subgroup.center Q)) a b
      have h2 : (QuotientGroup.mk' (Subgroup.center Q)) ⁅a, b⁆ = 1 := by
        rw [h1]; exact commutatorElement_eq_one_iff_mul_comm.2 (hab _ _)
      exact h2
    rw [hperf] at hcomm
    obtain ⟨a, ha⟩ := exists_ne (1 : Q ⧸ Subgroup.center Q)
    induction a using QuotientGroup.induction_on with | H q => ?_
    apply ha
    exact (QuotientGroup.eq_one_iff q).2 (hcomm (Subgroup.mem_top q))

omit [Finite G] in
theorem pow_three_eq_one_of_sylow {Q : Type*} [Group Q] [Finite Q] (P : Subgroup Q)
    (hP : Nat.card P = 3 ^ (Nat.card Q).factorization 3) (hexp : ∀ r ∈ P, r ^ 3 = 1)
    {q : Q} (hq : ∃ k : ℕ, q ^ (3 ^ k) = 1) : q ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Sylow 3 Q := Sylow.ofCard P hP
  obtain ⟨k, hk⟩ := hq
  have hpg : IsPGroup 3 ↥(Subgroup.zpowers q) := by
    intro x
    obtain ⟨x, m, rfl⟩ := x
    refine ⟨k, Subtype.ext ?_⟩
    show (q ^ m) ^ (3 ^ k) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨T, hT⟩ := IsPGroup.exists_le_sylow hpg
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q S T
  have hqT : q ∈ (T : Subgroup Q) := hT (Subgroup.mem_zpowers q)
  rw [← hg, Sylow.coe_subgroup_smul] at hqT
  obtain ⟨r, hr, hrq⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hqT
  have hrP : r ∈ P := hr
  rw [← hrq]
  simp only [MulAut.smul_def, MulAut.conj_apply]
  have h3 : (g * r * g⁻¹) ^ 3 = g * r ^ 3 * g⁻¹ := conj_pow
  rw [h3, hexp r hrP]
  simp

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
