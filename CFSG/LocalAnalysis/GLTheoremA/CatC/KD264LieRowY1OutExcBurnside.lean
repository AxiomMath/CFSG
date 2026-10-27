module

public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open scoped commutatorElement
open CFSG.RankThree.PartOne.OutStructure CFSG.ComponentClassification.OuterAutomorphisms

theorem eq_one_of_mem_commutator_of_central_pElements {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (hcen : ∀ x : Q, (∃ k : ℕ, x ^ (p ^ k) = 1) → x ∈ Subgroup.center Q)
    {x : Q} (hx : x ∈ commutator Q) (hxp : ∃ k : ℕ, x ^ (p ^ k) = 1) : x = 1 := by
  classical
  obtain ⟨P⟩ : Nonempty (Sylow p Q) := inferInstance
  have hPc : (P : Subgroup Q) ≤ Subgroup.center Q := fun y hy => hcen y (by
    obtain ⟨k, hk⟩ := P.2 ⟨y, hy⟩
    exact ⟨k, congrArg Subtype.val hk⟩)
  have hP : Subgroup.normalizer (P : Subgroup Q) ≤ Subgroup.centralizer (P : Set Q) := by
    intro n _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_center_iff.1 (hPc hy) n |>.symm
  have hcomm : ∀ u v : (P : Subgroup Q), u * v = v * u := fun u v =>
    Subtype.ext (Subgroup.mem_center_iff.1 (hPc v.2) u)
  have hker : commutator Q ≤ (MonoidHom.transferSylow P hP).ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro u _ v _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
  obtain ⟨k, hk⟩ := hxp
  have hpg : IsPGroup p (Subgroup.zpowers x) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨k, Subtype.ext ?_⟩
    show (g : Q) ^ (p ^ k) = 1
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  have hdis := MonoidHom.ker_transferSylow_disjoint P hP (Subgroup.zpowers x) hpg
  exact (Subgroup.disjoint_def.1 hdis) (hker hx) (Subgroup.mem_zpowers x)

theorem mem_inner_of_mem_innAutDerived_of_outPNice_three {X : Type} [Group X] [Finite X]
    (h : OutPNice 3 X) {a : MulAut X} (ha : a ∈ innAutDerived X) (ha3 : a ^ 3 = 1) :
    a ∈ inner X := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D, E, hID, hD2, hpE, hD4, -⟩ := h
  have hDE : D ≤ E := fun δ hδ => hpE δ ⟨0, by simpa using hδ⟩
  have hDn : D.Normal := ⟨fun δ hδ γ => by
    have h1 : ⁅γ, δ⁆ ∈ D := hD4 γ δ (hDE hδ)
    have : γ * δ * γ⁻¹ = ⁅γ, δ⁆ * δ := by rw [commutatorElement_def]; group
    rw [this]
    exact mul_mem h1 hδ⟩
  let π : MulAut X →* MulAut X ⧸ D := QuotientGroup.mk' D
  have hcen : ∀ y : MulAut X ⧸ D, (∃ k : ℕ, y ^ (3 ^ k) = 1) → y ∈ Subgroup.center (MulAut X ⧸ D) := by
    rintro y ⟨k, hk⟩
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective D y
    have hαD : α ^ (3 ^ k) ∈ D := by
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
  have hπ1 : π a = 1 := eq_one_of_mem_commutator_of_central_pElements (p := 3) hcen hamem
    ⟨1, by rw [pow_one, ← map_pow, ha3, map_one]⟩
  have haD : a ∈ D := (QuotientGroup.eq_one_iff a).1 hπ1
  exact hD2 a haD 1 (by rw [pow_one, ha3]; exact (Inn X).one_mem)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie
