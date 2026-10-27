module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodInner
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutExcBurnside

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open scoped commutatorElement
open CFSG.RankThree.PartOne.OutStructure CFSG.ComponentClassification.OuterAutomorphisms

theorem mem_inner_of_mem_innAutDerived_of_outPNice {p : ℕ} [Fact p.Prime] {X : Type} [Group X]
    [Finite X] (h : OutPNice p X) {a : MulAut X} (ha : a ∈ innAutDerived X) (hap : a ^ p = 1) :
    a ∈ inner X := by
  classical
  obtain ⟨D, E, hID, hD2, hpE, hD4, -⟩ := h
  have hDE : D ≤ E := fun δ hδ => hpE δ ⟨0, by simpa using hδ⟩
  have hDn : D.Normal := ⟨fun δ hδ γ => by
    have h1 : ⁅γ, δ⁆ ∈ D := hD4 γ δ (hDE hδ)
    have : γ * δ * γ⁻¹ = ⁅γ, δ⁆ * δ := by rw [commutatorElement_def]; group
    rw [this]
    exact mul_mem h1 hδ⟩
  let π : MulAut X →* MulAut X ⧸ D := QuotientGroup.mk' D
  have hcen : ∀ y : MulAut X ⧸ D, (∃ k : ℕ, y ^ (p ^ k) = 1) →
      y ∈ Subgroup.center (MulAut X ⧸ D) := by
    rintro y ⟨k, hk⟩
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective D y
    have hαD : α ^ (p ^ k) ∈ D := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hk
    have hαE : α ∈ E := hpE α ⟨k, hαD⟩
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk'_surjective D z
    have h1 : π ⁅γ, α⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (hD4 γ α hαE)
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hamem : π a ∈ commutator (MulAut X ⧸ D) := by
    have ha' : a ∈ inner X ⊔ commutator (MulAut X) := ha
    obtain ⟨i, hi, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 ha'
    have hπi : π i = 1 := (QuotientGroup.eq_one_iff i).2 (hID hi)
    rw [map_mul, hπi, one_mul]
    have hc' : π c ∈ (commutator (MulAut X)).map π := Subgroup.mem_map_of_mem π hc
    refine (?_ : (commutator (MulAut X)).map π ≤ commutator (MulAut X ⧸ D)) hc'
    rw [commutator_def, commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hπ1 : π a = 1 := eq_one_of_mem_commutator_of_central_pElements (p := p) hcen hamem
    ⟨1, by rw [pow_one, ← map_pow, hap, map_one]⟩
  have haD : a ∈ D := (QuotientGroup.eq_one_iff a).1 hπ1
  exact hD2 a haD 1 (by rw [pow_one, hap]; exact (Inn X).one_mem)

theorem innGoodAt_of_outPNice {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    (hZ : Subgroup.center S = ⊥) (hout : OutPNice p S) (h : PerfectCentralizerPlanes p S)
    (d : TauCeti.LieTypeIndex) : InnGoodAt p d S := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact innGoodAt_of_inner_planes hZ
    (fun β hβ hβp => mem_inner_of_mem_innAutDerived_of_outPNice hout hβ hβp) h d

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
