module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.RankThree.PartOne.OutStructure (Inn)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.AGLEmbedding.TwoGenInner (PGoodOut)
open scoped commutatorElement

theorem exists_normal_pComplement_of_pGoodOut {p : ℕ} (hp : p.Prime) {X : Type*} [Group X]
    [Finite X] (h : PGoodOut p X) :
    ∃ N : Subgroup (Outer X), N.Normal ∧ ¬ p ∣ Nat.card N ∧ ∃ k : ℕ, N.index = p ^ k := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨D, hDn, hID, hD2, hD3⟩ := h
  let π : MulAut X →* MulAut X ⧸ D := QuotientGroup.mk' D
  have hπ : ∀ a : MulAut X, π a = (a : MulAut X ⧸ D) := fun a => rfl
  have hcent : ∀ g : MulAut X ⧸ D, (∃ k : ℕ, g ^ p ^ k = 1) → g ∈ Subgroup.center _ := by
    intro g ⟨m, hm⟩
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective g
    have hαD : α ^ (p ^ m) ∈ D := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hm
    rw [Subgroup.mem_center_iff]
    intro g'
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g'
    have h1 : ⁅γ, α⁆ ∈ D := hD3 α γ ⟨m, hαD⟩
    have h2 : π ⁅γ, α⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  obtain ⟨P⟩ : Nonempty (Sylow p (MulAut X ⧸ D)) := inferInstance
  haveI : Finite (Sylow p (MulAut X ⧸ D)) := Sylow.finite_of_finiteIndex P
  have hPc : ∀ g ∈ (P : Subgroup (MulAut X ⧸ D)), g ∈ Subgroup.center _ := by
    intro g hg
    obtain ⟨m, hm⟩ := P.isPGroup' ⟨g, hg⟩
    exact hcent g ⟨m, congrArg Subtype.val hm⟩
  have hN : Subgroup.normalizer (P : Set (MulAut X ⧸ D)) ≤
      Subgroup.centralizer (P : Set (MulAut X ⧸ D)) :=
    fun n _ g hg => ((Subgroup.mem_center_iff.1 (hPc g hg)) n).symm
  let φ : MulAut X ⧸ D →* P := MonoidHom.transferSylow P hN
  let θ0 : MulAut X →* P := φ.comp π
  have hθ0 : Inn X ≤ θ0.ker := by
    intro a ha
    rw [MonoidHom.mem_ker]
    show φ (π a) = 1
    rw [hπ, (QuotientGroup.eq_one_iff a).2 (hID ha), map_one]
  let θ : Outer X →* P := QuotientGroup.lift (Inn X) θ0 hθ0
  have hθmk : ∀ b : MulAut X, θ (QuotientGroup.mk b) = φ (π b) := fun b => rfl
  refine ⟨θ.ker, inferInstance, ?_, ?_⟩
  ·
    intro hdiv
    obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' p hdiv
    have hnord : orderOf (n : Outer X) = p := (Subgroup.orderOf_coe n).trans hn
    have hpow : (n : Outer X) ^ p = 1 := by
      have := pow_orderOf_eq_one (n : Outer X)
      rwa [hnord] at this
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (n : Outer X)
    have hmem : (QuotientGroup.mk a : Outer X) ∈ θ.ker := by
      rw [ha]
      exact n.2
    have hφa : φ (π a) = 1 := by
      rw [← hθmk]
      exact MonoidHom.mem_ker.1 hmem
    have hπa : π a ∈ φ.ker := MonoidHom.mem_ker.2 hφa
    have hpa : a ^ p ∈ Inn X := by
      have h1 : (QuotientGroup.mk a : Outer X) ^ p = 1 := by
        rw [ha]
        exact hpow
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hpπ : (π a) ^ p = 1 := by
      rw [← map_pow, hπ]
      exact (QuotientGroup.eq_one_iff _).2 (hID hpa)
    have hord : orderOf (π a) ∣ p ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one hpπ
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hord
    have hQ : IsPGroup p (Subgroup.zpowers (π a)) :=
      IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    have hdisj := MonoidHom.ker_transferSylow_disjoint P hN (Subgroup.zpowers (π a)) hQ
    have hπa1 : π a = 1 := (Subgroup.disjoint_def.1 hdisj) hπa (Subgroup.mem_zpowers _)
    have haD : a ∈ D := (QuotientGroup.eq_one_iff a).1 (by rw [← hπ]; exact hπa1)
    have hainn : a ∈ Inn X := hD2 a haD 1 (by rw [pow_one]; exact hpa)
    have hn1 : (n : Outer X) = 1 := by
      rw [← ha]
      exact (QuotientGroup.eq_one_iff a).2 hainn
    rw [hn1, orderOf_one] at hnord
    exact hp.one_lt.ne hnord
  ·
    have hidx : θ.ker.index = Nat.card θ.range := Subgroup.index_ker θ
    obtain ⟨m, hm⟩ := IsPGroup.exists_card_eq P.isPGroup'
    have hdvd : Nat.card θ.range ∣ p ^ m := by
      rw [← hm]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    exact ⟨j, hidx.trans hj⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
