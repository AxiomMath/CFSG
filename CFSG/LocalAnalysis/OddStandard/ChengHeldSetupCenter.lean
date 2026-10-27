module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSetup
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCenter
public import CFSG.LocalAnalysis.OddStandard.GlueL34

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem fusionZStar_eq_center_of_perfect {J : Type*} [Group J] (hperf : commutator J = ⊤)
    (hO : CFSG.pPrimeCore 2 J ≤ center J) : Open.fusionZStar J = center J := by
  apply le_antisymm
  · intro z hz
    have hc : ∀ m : J, ⁅z, m⁆ ∈ center J := fun m =>
      hO ((ComponentClassification.GSThmB.OddQuot.mem_fusionZStar_iff.mp hz) m)
    let φ : J →* J :=
      { toFun := fun m => ⁅z, m⁆
        map_one' := by simp
        map_mul' := fun m₁ m₂ => by
          have h2 : m₁ * ⁅z, m₂⁆ * m₁⁻¹ = ⁅z, m₂⁆ := by
            rw [(mem_center_iff.mp (hc m₂) m₁), mul_inv_cancel_right]
          show ⁅z, m₁ * m₂⁆ = ⁅z, m₁⁆ * ⁅z, m₂⁆
          rw [← h2]
          simp only [commutatorElement_def]
          group }
    have hrange : φ.range ≤ center J := by
      rintro _ ⟨m, rfl⟩
      exact hc m
    have h1 : (commutator J).map φ = ⊥ := by
      rw [map_commutator_eq, commutator_eq_bot_iff_le_centralizer]
      exact hrange.trans (center_le_centralizer _)
    rw [hperf, ← MonoidHom.range_eq_map] at h1
    rw [mem_center_iff]
    intro m
    have hm : φ m = 1 := by
      have : φ m ∈ φ.range := ⟨m, rfl⟩
      rw [h1] at this
      exact this
    have hm' : ⁅z, m⁆ = 1 := hm
    rw [commutatorElement_eq_one_iff_mul_comm] at hm'
    exact hm'.symm
  · intro z hz
    refine ComponentClassification.GSThmB.OddQuot.mem_fusionZStar_iff.mpr fun m => ?_
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hz m).symm]
    exact one_mem _

theorem Hyp.commutator_eq_top (h : Hyp G A) : commutator ↥A = ⊤ := h.setting.standard.1.1

theorem Hyp.isSimpleGroup_quotient (h : Hyp G A) : IsSimpleGroup (↥A ⧸ center ↥A) :=
  h.setting.standard.1.2

theorem Hyp.card_quotient (h : Hyp G A) : Nat.card (↥A ⧸ center ↥A) = 20160 :=
  GlueL34.card_eq_of_lieModel_psl34 h.model

theorem Hyp.pPrimeCore_le_center (h : Hyp G A) : CFSG.pPrimeCore 2 ↥A ≤ center ↥A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.isSimpleGroup_quotient
  set N := CFSG.pPrimeCore 2 ↥A
  have hN : (N.map (QuotientGroup.mk' (center ↥A))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases hN.eq_bot_or_eq_top with h1 | h1
  · intro x hx
    have h2 : QuotientGroup.mk' (center ↥A) x = 1 := by
      rw [← mem_bot, ← h1]
      exact mem_map_of_mem _ hx
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  · exfalso
    have hdvd := Subgroup.card_map_dvd N (QuotientGroup.mk' (center ↥A))
    rw [h1, Subgroup.card_top, h.card_quotient] at hdvd
    have hcop := CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥A)
    exact absurd (Nat.Coprime.coprime_dvd_right hdvd hcop) (by norm_num)

theorem Hyp.fusionZStar_eq_center (h : Hyp G A) : Open.fusionZStar ↥A = center ↥A :=
  fusionZStar_eq_center_of_perfect h.commutator_eq_top h.pPrimeCore_le_center

theorem Hyp.isL34Type (h : Hyp G A) :
    ComponentClassification.GrSLit.IsL34Type (↥A ⧸ Open.fusionZStar ↥A) :=
  LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq h.fusionZStar_eq_center.symm) h.model

omit [Finite G] in
theorem isSylowTwoIn_of_isSylowOf {P K : Subgroup G} (h : IsSylowOf 2 P K) :
    ComponentClassification.GrSLit.IsSylowTwoIn P K := by
  obtain ⟨Q, hQ⟩ := h.exists_sylow_eq_subgroupOf
  exact ⟨h.le, Q, hQ⟩

theorem mem_zStarIn_of_mem_center (h : Hyp G A) {z : G} (hzA : z ∈ A)
    (hz : z ∈ centralizer (A : Set G)) : z ∈ ComponentClassification.GrSLit.zStarIn A := by
  have hmem : (⟨z, hzA⟩ : A) ∈ Open.fusionZStar ↥A := by
    rw [h.fusionZStar_eq_center, mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.mp hz g g.2)
  exact ⟨⟨z, hzA⟩, hmem, rfl⟩

namespace Datum

variable (d : Datum A)

theorem S_sylow : IsSylowOf 2 d.S A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact d.X_sylow.inf_of_le_normalizer le_normalizer le_rfl

theorem Q_isCyclic (h : Hyp G A) : IsCyclic d.Q :=
  h.isCyclic_of_isPGroup inf_le_right d.X_sylow.isPGroup.to_inf_left

theorem Q_inf_S : d.Q ⊓ d.S = d.X ⊓ A ⊓ centralizer (A : Set G) := by
  ext x
  simp only [Datum.Q, Datum.S, mem_inf]
  tauto

theorem center_two_part
    (h : Hyp G A) :
    (Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 2 ∨
      Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) ∧
    IsCyclic ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z₂ : Subgroup G := d.X ⊓ A ⊓ centralizer (A : Set G) with hZ₂
  have hp : IsPGroup 2 Z₂ := d.X_sylow.isPGroup.to_le (inf_le_left.trans inf_le_left)
  have hcyc : IsCyclic Z₂ := h.isCyclic_of_isPGroup inf_le_right hp
  refine ⟨?_, hcyc⟩
  have hexp : ∀ z ∈ Z₂, z ^ 4 = 1 := by
    intro z hz
    exact ComponentClassification.GrSLit.L34Facts.l34CenterExponentFact G A (d.X ⊓ A)
      (Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr h.commutator_eq_top))
      h.isL34Type (isSylowTwoIn_of_isSylowOf d.S_sylow) z
      ⟨⟨hz.1.1, hz.1.2⟩, mem_zStarIn_of_mem_center h hz.1.2 hz.2⟩
  have hq : d.q ∈ Z₂ := ⟨⟨(d.q_mem_X h).1, d.q_mem⟩, d.q_cent⟩
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card Z₂ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hg4 : g ^ 4 = 1 := Subtype.ext (by simpa using hexp g g.2)
  have hdvd : Nat.card Z₂ ∣ 4 := hord ▸ orderOf_dvd_of_pow_eq_one hg4
  have hne : Nat.card Z₂ ≠ 1 := by
    intro h1
    have : Z₂ = ⊥ := Subgroup.eq_bot_of_card_eq Z₂ h1
    rw [this, mem_bot] at hq
    have := d.q_ord
    rw [hq, orderOf_one] at this
    exact absurd this (by norm_num)
  have h4 : Nat.card Z₂ ∣ 2 ^ 2 := by simpa using hdvd
  rw [Nat.dvd_prime_pow Nat.prime_two] at h4
  obtain ⟨k, hk, hk'⟩ := h4
  interval_cases k
  · exact absurd (by simpa using hk') hne
  · left; simpa using hk'
  · right; simpa using hk'

theorem S_le_A : d.S ≤ A := inf_le_right

theorem S_le_X : d.S ≤ d.X := inf_le_left

theorem Q_le_centralizer : d.Q ≤ centralizer (A : Set G) := inf_le_right

theorem Q_le_X : d.Q ≤ d.X := inf_le_left

theorem QS_le_X : d.QS ≤ d.X := sup_le d.Q_le_X d.S_le_X

theorem Q_le_centralizer_S : d.Q ≤ centralizer (d.S : Set G) := fun c hc => by
  rw [mem_centralizer_iff]
  intro s hs
  exact mem_centralizer_iff.mp (d.Q_le_centralizer hc) s (d.S_le_A hs)

theorem conj_mem_S {x s : G} (hx : x ∈ d.X) (hs : s ∈ d.S) : x * s * x⁻¹ ∈ d.S :=
  ⟨d.X.mul_mem (d.X.mul_mem hx hs.1) (d.X.inv_mem hx),
    (mem_normalizer_iff.mp (d.X_sylow.le hx) s).mp hs.2⟩

theorem conj_mem_Q {x c : G} (hx : x ∈ d.X) (hc : c ∈ d.Q) : x * c * x⁻¹ ∈ d.Q :=
  ⟨d.X.mul_mem (d.X.mul_mem hx hc.1) (d.X.inv_mem hx),
    mul_mul_inv_mem_centralizer (d.X_sylow.le hx) hc.2⟩

theorem mem_QS_iff {x : G} : x ∈ d.QS ↔ ∃ u ∈ d.Q, ∃ s ∈ d.S, x = u * s := by
  refine ⟨fun hx => exists_mul_of_mem_sup_of_le_centralizer d.Q_le_centralizer_S hx, ?_⟩
  rintro ⟨u, hu, s, hs, rfl⟩
  exact mul_mem (mem_sup_left hu) (mem_sup_right hs)

end Datum

end CFSG.OddStandard.ChengHeld
