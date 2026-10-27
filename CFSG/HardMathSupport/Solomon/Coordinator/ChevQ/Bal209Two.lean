module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Defs
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Dickson.I271.Support.EngineBasic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.I271

@[expose] def Bal209TwoParabolic : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), CFSG.Open.IsQuasisimple ↥K →
    IsLieQuot ↥K Bal209TwoIndex →
      3 ∣ Nat.card K ∧ ∃ U Q : Subgroup X, U ≤ K ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ Q ≤ K ∧
        CFSG.Open.IsElemAbelian 3 Q ∧ Nat.card Q = 3 ^ 4 ∧
        Q ≤ Subgroup.normalizer (U : Set X) ∧ Q ⊓ Subgroup.centralizer (K : Set X) = ⊥

namespace Bal209TwoAux

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_card (p : ℕ) [Fact p.Prime] (H : Subgroup G) :
    CFSG.Open.pRank p H ≤ Nat.card G := by
  unfold CFSG.Open.pRank
  apply csSup_le'
  rintro k ⟨F, -, -, hF⟩
  have h1 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
  have h2 : k < p ^ k := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
  calc k ≤ p ^ k := h2.le
    _ = Nat.card F := hF.symm
    _ ≤ Nat.card G := h1

theorem card_eq_pow_pRank {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) : Nat.card E = p ^ CFSG.Open.pRank p E := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.Open.IsElemAbelian.isPGroup hE)
  have hbound : ∀ k ∈ {k | ∃ F : Subgroup G, F ≤ E ∧ CFSG.Open.IsElemAbelian p F ∧
      Nat.card F = p ^ k}, k ≤ n := by
    rintro k ⟨F, hFE, -, hF⟩
    have h1 : Nat.card F ≤ Nat.card E := Subgroup.card_le_of_le hFE
    rw [hF, hn] at h1
    exact (pow_le_pow_iff_right₀ hp.one_lt).1 h1
  have hpR : CFSG.Open.pRank p E = n := by
    apply le_antisymm
    · unfold CFSG.Open.pRank
      exact csSup_le' hbound
    · unfold CFSG.Open.pRank
      exact le_csSup ⟨n, hbound⟩ ⟨E, le_rfl, hE, hn⟩
  rw [hpR, hn]

theorem le_glaTwoLocalRank_of_elemAb {p : ℕ} (hp : p.Prime) {U E : Subgroup G} (hU : U ≠ ⊥)
    (hUp : IsPGroup 2 U) (hEN : E ≤ Subgroup.normalizer (U : Set G))
    (hE : CFSG.Open.IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ GLATwoLocalRank p G := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hbdd1 : BddAbove {j | ∃ F : Subgroup G, F ≤ Subgroup.normalizer (U : Set G) ∧
      CFSG.Open.IsElemAbelian p F ∧ Nat.card F = p ^ j} := by
    refine ⟨Nat.card G, ?_⟩
    rintro j ⟨F, -, -, hF⟩
    have h1 : j < p ^ j := Nat.lt_pow_self hp.one_lt
    have h2 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
    omega
  have hbdd2 : BddAbove {j | ∃ H : Subgroup G, IsTwoLocal H ∧ CFSG.Open.pRank p H = j} := by
    refine ⟨Nat.card G, ?_⟩
    rintro j ⟨H, -, rfl⟩
    exact pRank_le_card p H
  have h1 : k ≤ CFSG.Open.pRank p (Subgroup.normalizer (U : Set G)) :=
    le_csSup hbdd1 ⟨E, hEN, hE, hk⟩
  have h2 : CFSG.Open.pRank p (Subgroup.normalizer (U : Set G)) ≤
      CFSG.Open.twoLocalPrimeRank p G := by
    unfold CFSG.Open.twoLocalPrimeRank
    exact le_csSup hbdd2 ⟨Subgroup.normalizer (U : Set G), ⟨U, hU, hUp, rfl⟩, rfl⟩
  exact h1.trans h2

theorem mem_normalizer_of_mem_centralizer {K U : Subgroup G} (hUK : U ≤ K) {g : G}
    (hg : g ∈ Subgroup.centralizer (K : Set G)) : g ∈ Subgroup.normalizer (U : Set G) := by
  have hcomm : ∀ x ∈ K, x * g = g * x := fun x hx => Subgroup.mem_centralizer_iff.1 hg x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : g * h * g⁻¹ = h := by
      rw [← hcomm h (hUK hh), mul_inv_cancel_right]
    rw [e]
    exact hh
  · intro hh
    have hu : (g * h * g⁻¹) * g = g * (g * h * g⁻¹) := hcomm _ (hUK hh)
    have h1 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    have h2 : g⁻¹ * (g * h * g⁻¹) * g = g * h * g⁻¹ := by
      calc g⁻¹ * (g * h * g⁻¹) * g = g⁻¹ * ((g * h * g⁻¹) * g) := mul_assoc _ _ _
        _ = g⁻¹ * (g * (g * h * g⁻¹)) := by rw [hu]
        _ = (g⁻¹ * g) * (g * h * g⁻¹) := (mul_assoc _ _ _).symm
        _ = g * h * g⁻¹ := by rw [inv_mul_cancel, one_mul]
    rw [← h1, h2]
    exact hh

def pairHom (C Q : Subgroup G) (hcomm : ∀ c ∈ C, ∀ q ∈ Q, c * q = q * c) :
    (↥C × ↥Q) →* G where
  toFun x := (x.1 : G) * (x.2 : G)
  map_one' := by simp
  map_mul' x y := by
    have h := hcomm (y.1 : G) y.1.2 (x.2 : G) x.2.2
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    rw [mul_assoc (x.1 : G), ← mul_assoc (y.1 : G), h]
    simp only [mul_assoc]

theorem exists_elemAb_normalizer {p : ℕ} [Fact p.Prime] {C Q U : Subgroup G}
    (hC : CFSG.Open.IsElemAbelian p C) (hQ : CFSG.Open.IsElemAbelian p Q)
    (hcomm : ∀ c ∈ C, ∀ q ∈ Q, c * q = q * c) (hdisj : C ⊓ Q = ⊥)
    (hCN : C ≤ Subgroup.normalizer (U : Set G)) (hQN : Q ≤ Subgroup.normalizer (U : Set G)) :
    ∃ E : Subgroup G, E ≤ Subgroup.normalizer (U : Set G) ∧ CFSG.Open.IsElemAbelian p E ∧
      Nat.card E = Nat.card C * Nat.card Q := by
  have hinj : Function.Injective (pairHom C Q hcomm) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x.1 : G) * (x.2 : G) = 1 := hx
    have hmem : (x.1 : G) ∈ C ⊓ Q := by
      refine ⟨x.1.2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hx']
      exact Q.inv_mem x.2.2
    have h1 : (x.1 : G) = 1 := by
      have : (x.1 : G) ∈ (⊥ : Subgroup G) := by
        rw [← hdisj]
        exact hmem
      exact Subgroup.mem_bot.1 this
    have h2 : (x.2 : G) = 1 := by
      rw [h1, one_mul] at hx'
      exact hx'
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hCc : ∀ x y : ↥C, x * y = y * x := fun x y => hC.1.is_comm.comm x y
  have hQc : ∀ x y : ↥Q, x * y = y * x := fun x y => hQ.1.is_comm.comm x y
  have hprod : ∀ x y : ↥C × ↥Q, x * y = y * x := fun x y =>
    Prod.ext (hCc x.1 y.1) (hQc x.2 y.2)
  refine ⟨(pairHom C Q hcomm).range, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact mul_mem (hCN x.1.2) (hQN x.2.2)
  · have hab : ∀ a b : (pairHom C Q hcomm).range, a * b = b * a := by
      rintro ⟨a, x, rfl⟩ ⟨b, y, rfl⟩
      apply Subtype.ext
      show (pairHom C Q hcomm) x * (pairHom C Q hcomm) y =
        (pairHom C Q hcomm) y * (pairHom C Q hcomm) x
      rw [← map_mul, ← map_mul, hprod x y]
    refine ⟨⟨⟨hab⟩⟩, ?_⟩
    rintro _ ⟨z, rfl⟩
    rw [← map_pow]
    have hz1 : (z.1 : ↥C) ^ p = 1 := Subtype.ext (by simpa using hC.2 (z.1 : G) z.1.2)
    have hz2 : (z.2 : ↥Q) ^ p = 1 := Subtype.ext (by simpa using hQ.2 (z.2 : G) z.2.2)
    have hz : z ^ p = 1 := Prod.ext (by simpa using hz1) (by simpa using hz2)
    rw [hz, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

theorem not_isCyclic_of_card {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian p A) (hcard : p ^ 2 ≤ Nat.card A) : ¬ IsCyclic ↥A := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card A := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hA.2 (g : G) g.2)
  have hle : orderOf g ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hgp)
  have h2 := hp.two_le
  rw [hord] at hle
  nlinarith

end Bal209TwoAux

open Bal209TwoAux

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
