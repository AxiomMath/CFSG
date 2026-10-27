module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerDefs

public section

namespace CFSG.AGLEmbedding.TwoGenInner

open CFSG.RankThree.PartOne.OutStructure (Inn OutPNice)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

section Burnside

variable {G : Type*} [Group G] [Finite G]

theorem eq_one_of_pElement_mem_closure_twoElements {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcent : ∀ g : G, (∃ k : ℕ, g ^ p ^ k = 1) → g ∈ Subgroup.center G) {x : G}
    (hx : x ∈ Subgroup.closure {a : G | ∃ k : ℕ, a ^ 2 ^ k = 1})
    (hxp : ∃ k : ℕ, x ^ p ^ k = 1) : x = 1 := by
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
  have hker : Subgroup.closure {a : G | ∃ k : ℕ, a ^ 2 ^ k = 1} ≤ φ.ker := by
    rw [Subgroup.closure_le]
    rintro a ⟨j, hj⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have h1 : (φ a) ^ 2 ^ j = 1 := by rw [← map_pow, hj, map_one]
    obtain ⟨m, hm⟩ := P.isPGroup' (φ a)
    have hcop : Nat.Coprime (p ^ m) (2 ^ j) :=
      Nat.Coprime.pow m j ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have h2 : orderOf (φ a) ∣ p ^ m := orderOf_dvd_of_pow_eq_one hm
    have h3 : orderOf (φ a) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one h1
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h3)
  have hdisj := MonoidHom.ker_transferSylow_disjoint P hN (Subgroup.zpowers x) hpg
  exact (Subgroup.disjoint_def.1 hdisj) (hker hx) (Subgroup.mem_zpowers x)

end Burnside

section Reduction

variable {X : Type*} [Group X] {p : ℕ}

theorem pGoodOut_of_outPNice (h : OutPNice p X) : PGoodOut p X := by
  obtain ⟨D, E, hID, hD2, hpE, hDE, -⟩ := h
  refine ⟨D, ⟨fun δ hδ γ => ?_⟩, hID, hD2, fun α γ hα => hDE γ α (hpE α hα)⟩
  have hδE : δ ∈ E := hpE δ ⟨0, by simpa using hδ⟩
  have h1 : ⁅γ, δ⁆ ∈ D := hDE γ δ hδE
  have e : γ * δ * γ⁻¹ = ⁅γ, δ⁆ * δ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact D.mul_mem h1 hδ

theorem pGoodOut_of_not_dvd_outer [Finite X] (hp : p.Prime) (h : ¬ p ∣ Nat.card (Outer X)) :
    PGoodOut p X := by
  refine ⟨⊤, inferInstance, le_top, ?_, fun _ _ _ => trivial⟩
  intro δ _ k hk
  have h1 : (QuotientGroup.mk δ : Outer X) ^ (p ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have hd1 : orderOf (QuotientGroup.mk δ : Outer X) ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
  have hd2 : orderOf (QuotientGroup.mk δ : Outer X) ∣ Nat.card (Outer X) := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (p ^ k) (Nat.card (Outer X)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr h)
  have h2 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  exact (QuotientGroup.eq_one_iff δ).mp (orderOf_eq_one_iff.mp h2)

theorem PGoodOut.of_mulEquiv {Y : Type*} [Group Y] (e : X ≃* Y) (h : PGoodOut p Y) :
    PGoodOut p X := by
  obtain ⟨D, hDn, hID, hD2, hD3⟩ := h
  let φ : MulAut X ≃* MulAut Y := MulAut.congr e
  have hinner : (Inn X).map φ.toMonoidHom = Inn Y :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e
  have hmem : ∀ α : MulAut X, α ∈ Inn X ↔ φ α ∈ Inn Y := by
    intro α
    rw [← hinner]
    constructor
    · exact fun h => ⟨α, h, rfl⟩
    · rintro ⟨β, hβ, hβα⟩
      have : β = α := φ.injective hβα
      exact this ▸ hβ
  refine ⟨D.comap φ.toMonoidHom, hDn.comap _, fun α hα => hID ((hmem α).mp hα), ?_, ?_⟩
  · intro δ hδ k hk
    rw [hmem]
    refine hD2 (φ δ) hδ k ?_
    rw [← map_pow]
    exact (hmem _).mp hk
  · intro α γ ⟨k, hk⟩
    have hk' : (φ α) ^ (p ^ k) ∈ D := by rw [← map_pow]; exact hk
    show φ ⁅γ, α⁆ ∈ D
    rw [map_commutatorElement]
    exact hD3 (φ α) (φ γ) ⟨k, hk'⟩

theorem twoGenPInner_of_pGoodOut [Finite X] (hp : p.Prime) (hp2 : p ≠ 2) (h : PGoodOut p X) :
    ∀ x ∈ Subgroup.closure {a : MulAut X | ∃ k : ℕ, a ^ 2 ^ k = 1},
      (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ Inn X := by
  obtain ⟨D, hDn, hID, hD2, hD3⟩ := h
  intro x hx hxp
  obtain ⟨k, hk⟩ := hxp
  let π : MulAut X →* MulAut X ⧸ D := QuotientGroup.mk' D
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
  have hxc : π x ∈ Subgroup.closure {a : MulAut X ⧸ D | ∃ k : ℕ, a ^ 2 ^ k = 1} := by
    have hle : Subgroup.closure {a : MulAut X | ∃ k : ℕ, a ^ 2 ^ k = 1} ≤
        (Subgroup.closure {a : MulAut X ⧸ D | ∃ k : ℕ, a ^ 2 ^ k = 1}).comap π := by
      rw [Subgroup.closure_le]
      rintro a ⟨j, hj⟩
      refine Subgroup.subset_closure ⟨j, ?_⟩
      rw [← map_pow, hj, map_one]
    exact hle hx
  have hx1 : π x = 1 :=
    eq_one_of_pElement_mem_closure_twoElements hp hp2 hcent hxc ⟨k, by rw [← map_pow, hk, map_one]⟩
  exact hD2 x ((QuotientGroup.eq_one_iff x).1 hx1) k (by rw [hk]; exact (Inn X).one_mem)

end Reduction

end CFSG.AGLEmbedding.TwoGenInner
