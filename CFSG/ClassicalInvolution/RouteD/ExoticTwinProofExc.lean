module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProof

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped commutatorElement

section Abstract

variable {L : Type*} [Group L]

theorem exists_conj_not_commutes (hL : CFSG.Open.IsQuasisimple L) {R : Subgroup L}
    (hRc : ¬ R ≤ Subgroup.center L) (hRtop : R ≠ ⊤) :
    ∃ g : L, conjSub g R ≠ R ∧ ¬ Commutes (conjSub g R) R := by
  by_contra hcon
  push Not at hcon
  have hperfL : (⊤ : Subgroup L) ≤ ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ := by
    have := hL.1
    rw [commutator_def] at this
    exact this.ge
  have hnorm : Subgroup.normalClosure (R : Set L) ≤ Subgroup.normalizer (R : Set L) := by
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    obtain ⟨b, hb, hbc⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨c, hc⟩ := isConj_iff.mp hbc
    have hyS : y ∈ R.map (MulAut.conj c).toMonoidHom := ⟨b, hb, by simpa using hc⟩
    by_cases hSR : R.map (MulAut.conj c).toMonoidHom = R
    · rw [hSR] at hyS
      exact Subgroup.le_normalizer hyS
    · have hc1 : ∀ r ∈ R, y * r = r * y := (hcon c hSR) y hyS
      have hc' : ∀ r ∈ R, y⁻¹ * r = r * y⁻¹ :=
        (hcon c hSR) y⁻¹ (Subgroup.inv_mem _ hyS)
      rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
      intro r
      constructor
      · intro hr
        have : y * r * y⁻¹ = r := by rw [mul_inv_eq_iff_eq_mul]; exact hc1 r hr
        rw [this]
        exact hr
      · intro hr
        have h1 : y⁻¹ * (y * r * y⁻¹) * y = r := by group
        have h2 : y⁻¹ * (y * r * y⁻¹) * y = y * r * y⁻¹ := by
          rw [mul_assoc, ← mul_assoc y⁻¹, hc' _ hr]
          group
        rw [← h1, h2]
        exact hr
  have : (Subgroup.normalClosure (R : Set L)).Normal := Subgroup.normalClosure_normal
  rcases normal_le_center_or_sup_eq_top hL (Subgroup.normalClosure (R : Set L)) with h | h
  · exact hRc ((Subgroup.subset_normalClosure).trans h)
  · have htop : (⊤ : Subgroup L) ≤ Subgroup.normalClosure (R : Set L) :=
      CFSG.ClassicalInvolution.RouteD.le_of_perfect_of_le_sup_center
        (Z := Subgroup.center L) le_rfl hperfL h.ge
    have : R.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (htop.trans hnorm))
    rcases normal_le_center_or_sup_eq_top hL R with h' | h'
    · exact hRc h'
    · exact hRtop (top_le_iff.mp
        (CFSG.ClassicalInvolution.RouteD.le_of_perfect_of_le_sup_center
          (Z := Subgroup.center L) le_rfl hperfL h'.ge))

variable {K : Type*} [Group K]

theorem exists_conj_not_commutes_of_le {L R : Subgroup K} (hL : CFSG.Open.IsQuasisimple ↥L)
    (hRL : R ≤ L) (hRc : ¬ ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) (hRtop : ¬ L ≤ R) :
    ∃ g ∈ L, conjSub g R ≠ R ∧ ¬ Commutes (conjSub g R) R := by
  have hc : ¬ R.subgroupOf L ≤ Subgroup.center ↥L := by
    intro h
    apply hRc
    intro x hx y hy
    have := Subgroup.mem_center_iff.mp (h (show (⟨x, hRL hx⟩ : ↥L) ∈ R.subgroupOf L from hx))
      ⟨y, hRL hy⟩
    exact congrArg Subtype.val this.symm
  have htop : R.subgroupOf L ≠ ⊤ := fun h => hRtop (Subgroup.subgroupOf_eq_top.mp h)
  obtain ⟨g, hg1, hg2⟩ := exists_conj_not_commutes hL hc htop
  refine ⟨g, g.2, fun heq => hg1 ?_, fun hcomm => hg2 ?_⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : (g : K) * y * (g : K)⁻¹ ∈ conjSub (g : K) R := ⟨y, hy, rfl⟩
      rw [heq] at this
      exact this
    · intro hx
      have hx' : (x : K) ∈ conjSub (g : K) R := by rw [heq]; exact hx
      obtain ⟨r, hr, hrx⟩ := hx'
      refine ⟨(g⁻¹ * x * g : ↥L), ?_, ?_⟩
      · show ((g⁻¹ * x * g : ↥L) : K) ∈ R
        have : ((g⁻¹ * x * g : ↥L) : K) = r := by
          have h1 : (g : K) * r * (g : K)⁻¹ = x := hrx
          simp only [Subgroup.coe_mul, InvMemClass.coe_inv, ← h1]
          group
        rw [this]
        exact hr
      · show g * (g⁻¹ * x * g) * g⁻¹ = x
        group
  · rintro _ ⟨y, hy, rfl⟩ z hz
    have h1 : (g : K) * (y : K) * (g : K)⁻¹ ∈ conjSub (g : K) R := ⟨y, hy, rfl⟩
    exact Subtype.ext (hcomm _ h1 z hz)

end Abstract

section Layer

variable {p f : ℕ} [Fact p.Prime]

@[expose] def HasQuasisimpleLayer (p : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  ∀ R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
    ∃ L : Subgroup (modelUniv t n p e Fact.out).K, CFSG.Open.IsQuasisimple ↥L ∧
      L ≤ Subgroup.centralizer (R₀ : Set (modelUniv t n p e Fact.out).K) ∧
      (∀ P : Subgroup (modelUniv t n p e Fact.out).K,
        P ≤ Subgroup.centralizer (R₀ : Set (modelUniv t n p e Fact.out).K) → P ≤ ⁅P, P⁆ →
          P ≤ L) ∧
      L ∉ fundamentalSubgroups t (modelUniv t n p e Fact.out).D

theorem noTwinClass_of_layer (hp2 : p ≠ 2) {t : StatedLieTag} {n e a : ℕ} (hq : 4 ≤ p ^ e)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hlayer : HasQuasisimpleLayer p t n e) (ha : 2 ≤ a) : ¬ ModelTwinClass p t n e a := by
  intro h
  obtain ⟨R₀, R₁, hR₀, hR₁, hne, hc, htw⟩ :=
    ((modelTwinClass_iff t n e a).mp h).exists_two ha
  have hperf : Gaps.FundPerfect t (modelUniv t n p e Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 hfund hadm hq
  obtain ⟨L, hLqs, hLC, hLperf, hLfund⟩ := hlayer R₀ hR₀
  have hR₁C : R₁ ≤ Subgroup.centralizer (R₀ : Set (modelUniv t n p e Fact.out).K) :=
    fun y hy => Subgroup.mem_centralizer_iff.mpr fun x hx => hc x hx y hy
  have hR₁L : R₁ ≤ L := hLperf R₁ hR₁C (hperf R₁ hR₁)
  have hnab : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
      ¬ ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    intro R hR hab
    apply fundamentalSubgroups_ne_bot hfund hadm hR
    refine eq_bot_iff.mpr ((hperf R hR).trans (Subgroup.commutator_le.mpr fun x hx y hy => ?_))
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hab x hx y hy
  obtain ⟨g, hgL, hg1, hg2⟩ := exists_conj_not_commutes_of_le hLqs hR₁L (hnab R₁ hR₁)
    (fun hLR => hLfund (le_antisymm hLR hR₁L ▸ hR₁))
  have hS : conjSub g R₁ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D :=
    CFSG.ClassicalInvolution.RouteD.conjSub_mem_fundamentalSubgroups hR₁ g
  have hSL : conjSub g R₁ ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    exact L.mul_mem (L.mul_mem hgL (hR₁L hy)) (L.inv_mem hgL)
  have hSR₀ : conjSub g R₁ ≠ R₀ := by
    intro heq
    apply hnab R₀ hR₀
    intro x hx y hy
    have hxS : x ∈ conjSub g R₁ := heq ▸ hx
    exact (Subgroup.mem_centralizer_iff.mp (hLC (hSL hxS)) y hy).symm
  have hcS : Commutes (conjSub g R₁) R₀ := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hLC (hSL hx)) y hy).symm
  exact hg2 ((htw _ hS hSR₀ hg1).mp hcS)

@[expose] def ExcLayer (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ (t : StatedLieTag) (n : ℕ),
    (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) →
    StatedLieAdmissible t n p f → HasQuasisimpleLayer p t n f

theorem mfTwinExc_of_layer (h : ExcLayer p f) : MFTwinExc p f := by
  intro hp2 hq t n a hexc hadm ha
  have hfund : IsFundTag t := by
    rcases hexc with rfl | rfl | rfl | rfl | rfl <;> trivial
  exact noTwinClass_of_layer hp2 (by omega) hfund hadm (h hp2 hq t n hexc hadm) ha

theorem mfTwin_of_layer (h : ExcLayer p f) : MFTwin p f :=
  mfTwin_of_parts (mfTwinClassical p f) (mfTwinExc_of_layer h)

end Layer

end CFSG.ClassicalInvolution.RouteD.Exotic
