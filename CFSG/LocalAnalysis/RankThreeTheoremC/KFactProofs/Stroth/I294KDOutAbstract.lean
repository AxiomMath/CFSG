module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.AGLEmbedding.TwoGenInner (PGoodOut)
open scoped commutatorElement

section Burnside

variable {G : Type*} [Group G] [Finite G]

theorem eq_one_of_pElement_mem_commutator {p : ℕ} (hp : p.Prime)
    (hcent : ∀ g : G, (∃ k : ℕ, g ^ p ^ k = 1) → g ∈ Subgroup.center G) {x : G}
    (hx : x ∈ commutator G) (hxp : ∃ k : ℕ, x ^ p ^ k = 1) : x = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hxp
  have hord : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hord
  have hpg : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨P, -⟩ := hpg.exists_le_sylow
  have hPc : ∀ g ∈ (P : Subgroup G), g ∈ Subgroup.center G := by
    intro g hg
    obtain ⟨m, hm⟩ := P.isPGroup' ⟨g, hg⟩
    exact hcent g ⟨m, congrArg Subtype.val hm⟩
  have hN : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) :=
    fun n _ g hg => ((Subgroup.mem_center_iff.1 (hPc g hg)) n).symm
  set φ : G →* P := MonoidHom.transferSylow P hN with hφ
  have hPcomm : ∀ a b : P, a * b = b * a := fun a b =>
    Subtype.ext ((Subgroup.mem_center_iff.1 (hPc b b.2)) a)
  have hker : commutator G ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hPcomm _ _)
  have hdisj := MonoidHom.ker_transferSylow_disjoint P hN (Subgroup.zpowers x) hpg
  exact (Subgroup.disjoint_def.1 hdisj) (hker hx) (Subgroup.mem_zpowers x)

end Burnside

theorem pElement_mem_inner_of_pGoodOut {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    (h : PGoodOut p X) {α : MulAut X} (hα : ∃ k : ℕ, α ^ p ^ k = 1)
    (hmem : α ∈ commutator (MulAut X) ⊔ (MulAut.conj : X →* MulAut X).range) :
    α ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨D, hDn, hID, hD2, hD3⟩ := h
  obtain ⟨k, hk⟩ := hα
  haveI : Finite (MulAut X) := CFSG.RankThree.PartOne.OutStructure.instFiniteMulAut' X
  let π : MulAut X →* MulAut X ⧸ D := QuotientGroup.mk' D
  have hcent : ∀ g : MulAut X ⧸ D, (∃ k : ℕ, g ^ p ^ k = 1) → g ∈ Subgroup.center _ := by
    intro g ⟨m, hm⟩
    obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective g
    have hβD : β ^ (p ^ m) ∈ D := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hm
    rw [Subgroup.mem_center_iff]
    intro g'
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g'
    have h1 : ⁅γ, β⁆ ∈ D := hD3 β γ ⟨m, hβD⟩
    have h2 : π ⁅γ, β⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  have hπα : π α ∈ commutator (MulAut X ⧸ D) := by
    have hle : commutator (MulAut X) ⊔ (MulAut.conj : X →* MulAut X).range ≤
        (commutator (MulAut X ⧸ D)).comap π := by
      refine sup_le ?_ ?_
      · intro a ha
        rw [Subgroup.mem_comap]
        have hmap : (commutator (MulAut X)).map π ≤ commutator (MulAut X ⧸ D) := by
          rw [commutator_def, commutator_def, Subgroup.map_commutator]
          exact Subgroup.commutator_mono le_top le_top
        exact hmap (Subgroup.mem_map_of_mem π ha)
      · intro a ha
        rw [Subgroup.mem_comap]
        have : π a = 1 := (QuotientGroup.eq_one_iff a).2 (hID ha)
        rw [this]
        exact Subgroup.one_mem _
    exact hle hmem
  have hπ1 : π α = 1 :=
    eq_one_of_pElement_mem_commutator hp hcent hπα ⟨k, by rw [← map_pow, hk, map_one]⟩
  exact hD2 α ((QuotientGroup.eq_one_iff α).1 hπ1) k (by rw [hk]; exact Subgroup.one_mem _)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
