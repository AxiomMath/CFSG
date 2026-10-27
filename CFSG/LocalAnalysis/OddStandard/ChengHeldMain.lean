module

public import CFSG.LocalAnalysis.OddStandard.L34EvenSylowBal
public import CFSG.LocalAnalysis.OddStandard.ChengHeldUnitMain
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec1Final
public import CFSG.LocalAnalysis.OddStandard.ChengHeldONCert

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools
open CFSG.OddStandard.ChengHeldData

theorem l34EvenSylowStepBal_of_exclusions
    (hQS : ∀ {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ} {g : G}, α ≤ 1 →
        ∀ (c : Chart4 d α), HypBal G A → Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4 → g ∈ A →
        (∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) → GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g → c.kinds = ∅
        → False) (hgraph : ∀ {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α :
        ℕ} {g : G}, α ≤ 1 → ∀ (c : Chart4 d α), HypBal G A → Nat.card ↥(d.X ⊓ A ⊓ centralizer (A :
        Set G)) = 4 → g ∈ A → (∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) → GAct α c.t c.pi c.tau c.mu c.lam c.ze
        c.xi g → c.kinds = {Kind.graph} → False) (hfield : ∀ {G : Type} [Group G] [Finite G] {A : Subgroup G}
        {d : Datum A} {α : ℕ} {g : G}, α ≤ 1 → ∀ (c : Chart4 d α), HypBal G A → Nat.card ↥(d.X ⊓ A ⊓
        centralizer (A : Set G)) = 4 → g ∈ A → (∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) → GAct α c.t c.pi
        c.tau c.mu c.lam c.ze c.xi g → c.kinds = {Kind.field} → False) (hboth0 : ∀ {G : Type} [Group G]
        [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ} {g : G}, α ≤ 1 → ∀ (c : Chart4 d α),
        HypBal G A → Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4 → g ∈ A → (∀ s ∈ d.S, g⁻¹ * s
        * g ∈ d.S) → GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g → α = 0 → c.kinds = Set.univ →
        False)
    (hboth1 : ∀ {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ} {g : G}, α ≤
        1 → ∀ (c : Chart4 d α), HypBal G A → Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4 → g ∈
        A → (∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) → GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g → α = 1 →
        c.kinds = Set.univ → False) : CFSG.OddStandard.L34EvenSylowStepBal := by
  intro G _ _ A hS hbal h34 hev R hcyc
  have hb : HypBal G A := ⟨Hyp.of_one_cyclic hS h34 hev R hcyc, hbal⟩
  obtain ⟨d⟩ := hb.toHyp.exists_datum
  obtain ⟨hcard, -⟩ := d.center_two_part hb.toHyp
  rcases hcard with h2 | h4
  · exact (sec1_false hb h2).elim
  · obtain ⟨α, hα, c, g, hgA, hg, hgact⟩ := d.exists_chart4_g_cert hb.toHyp h4
    have hP : chPresOK = true := Certificates.certificate6137
    have hQ : chPropsOK = true := Certificates.certificate6138
    rcases c.shape hb.toHyp with hk | hk | hk | hk | hk
    · exact (hQS hα c hb h4 hgA hg hgact hk).elim
    · exact (hfield hα c hb h4 hgA hg hgact hk).elim
    · exact (hgraph hα c hb h4 hgA hg hgact hk).elim
    · obtain ⟨hα0, z, hz, hz2, hza, hX, hcardX⟩ :=
        c.unitary_structure_cert hα hb.toHyp h4 hg hgact hk
      obtain ⟨S, hSX⟩ := exists_sylow_of_isSylowOf_top (c.X_sylow_G_of_facts hα hb.toHyp hP hQ)
      subst hα0
      obtain ⟨T, ⟨e⟩⟩ := exists_mulEquiv_onSylow_cert c.frame hz2 hza hX hcardX
      exact ⟨S, T, ⟨(MulEquiv.subgroupCongr hSX).trans e⟩⟩
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hα with hα0 | hα1
      · exact (hboth0 hα c hb h4 hgA hg hgact hα0 hk).elim
      · exact (hboth1 hα c hb h4 hgA hg hgact hα1 hk).elim

end CFSG.OddStandard.ChengHeld
