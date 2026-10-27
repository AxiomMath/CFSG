module

public import CFSG.LieType.SeitzGeneration.ExcTorusRank
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6One
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Two
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Six
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Ten
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Eight
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Eighteen
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Twelve
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Adapters.TauCetiExceptional.TwistedBlock
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.TauCetiBridge TauCeti

@[expose] def ennola (e : ℕ) : ℕ :=
  if e % 2 = 1 then 2 * e else if e % 4 = 2 then e / 2 else e

theorem orderOf_neg_natCast_zmod {p q e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ q)
    (he : orderOf (q : ZMod p) = e) : orderOf (((-(q : ℤ) : ℤ)) : ZMod p) = ennola e := by
  have : Fact p.Prime := ⟨hp⟩
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  have h1 : (-1 : ZMod p) ≠ 1 := neg_one_ne_one_zmod hp hp2
  push_cast
  unfold ennola
  split_ifs with h h'
  · exact orderOf_neg_of_odd h1 he (Nat.odd_iff.2 h) he0
  · exact orderOf_neg_of_two_mod_four he h'
  · exact orderOf_neg_of_four_dvd he (by omega) he0

@[expose] def degCountTw (e : ℕ) : ℕ := degCount Tag.E6 (ennola e)

theorem le_two_mul_ennola (e : ℕ) : e ≤ 2 * ennola e := by
  unfold ennola
  split_ifs <;> omega

theorem le_sixty_of_degCountTw_pos {e : ℕ} (h : 0 < degCountTw e) : e ≤ 60 := by
  have := le_thirty_of_degCount_pos (τ := Tag.E6) (by simp) h
  have := le_two_mul_ennola e
  omega

section Adjoint


theorem elemAbelian_card_eq_one_of_degCountTw_zero {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ ℓ ^ f)
    {e : ℕ} (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e) (h0 : degCountTw e = 0)
    {F : Subgroup (twistedE6RootGroup K σ)} (hF : IsElemAbelian p F) : Nat.card F = 1 := by
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set Q : ℤ := -((ℓ ^ f : ℕ) : ℤ) with hQdef
  have hQ2 : 2 ≤ Q.natAbs := by simpa [hQdef] using hq2
  have hpQ : ¬ (p : ℤ) ∣ Q := fun h => hpq (Int.natCast_dvd_natCast.1 (by simpa [hQdef] using h))
  have he' : orderOf (Q : ZMod p) = ennola e :=
    orderOf_neg_natCast_zmod hp (by omega) hpq he
  have hnil : ((degreesE Tag.E6).filter fun d => ennola e ∣ d).length = 0 := by
    simpa [degCountTw, degCount, degreesW] using h0
  have hD : ∀ d ∈ degreesE Tag.E6, ennola e ∣ d → d ≠ 0 ∧ ¬ p ∣ d / ennola e := by
    intro d hd hed
    exfalso
    have hmem : d ∈ (degreesE Tag.E6).filter (fun d => ennola e ∣ d) :=
      List.mem_filter.2 ⟨hd, by simpa using hed⟩
    have := List.length_pos_of_mem hmem
    omega
  refine elemAbelian_card_eq_one_of_ordProj hp ?_ hF
  rw [ordProj_card_twistedE6 hℓ hf K hK σ hσ hp hp3 hpq,
    prod_ordProj_int_pow_sub_one hp (by omega) hQ2 hpQ he' (degreesE Tag.E6) hD, hnil, pow_zero]

theorem rankLE1_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hpq : ¬ p ∣ ℓ ^ f)
    (hcnt : degCountTw (orderOf (((ℓ ^ f : ℕ)) : ZMod p)) ≤ 1) :
    RankLE1 p (twistedE6RootGroup K σ) := by
  have he0 := orderOf_natCast_ne_zero hp hpq
  have hlt := orderOf_lt_prime hp hpq (rfl : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = _)
  obtain ⟨e, he⟩ : ∃ e, orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt he0 hlt
  have he3 : 3 ≤ e := by
    by_contra h
    have h1 : 1 ≤ e := Nat.pos_of_ne_zero he0
    interval_cases e <;> revert hcnt <;> decide
  have hp3 : 3 < p := by omega
  by_cases h0 : degCountTw e = 0
  · intro F hF
    rw [elemAbelian_card_eq_one_of_degCountTw_zero hℓ hf K hK σ hσ hp hp3 hpq he h0 hF]
    exact hp.one_lt.le
  · have h60 := le_sixty_of_degCountTw_pos (Nat.pos_of_ne_zero h0)
    interval_cases e <;> first | exact absurd hcnt (by decide) | exact absurd h0 (by decide) | skip
    · exact (sylowTorus_twistedE6_eight hℓ hf K hK σ hσ hp he).rankLE1 hp
    · exact (sylowTorus_twistedE6_ten hℓ hf K hK σ hσ hp he).rankLE1 hp
    · exact (sylowTorus_twistedE6_twelve hℓ hf K hK σ hσ hp he).rankLE1 hp
    · exact (sylowTorus_twistedE6_eighteen hℓ hf K hK σ hσ hp he).rankLE1 hp

theorem not_rankLE2_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ ℓ ^ f)
    (hcnt : 3 ≤ degCountTw (orderOf (((ℓ ^ f : ℕ)) : ZMod p))) :
    ¬ RankLE2 p (twistedE6RootGroup K σ) := by
  obtain ⟨e, he⟩ : ∃ e, orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  have h60 := le_sixty_of_degCountTw_pos (by omega : 0 < degCountTw e)
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  have h1 : 1 ≤ e := Nat.pos_of_ne_zero he0
  interval_cases e <;> first | exact absurd hcnt (by decide) | skip
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_twistedE6_one hℓ hf K hK σ hσ hp hp3 he
    exact not_rankLE2_of_elemAbelian hp (by norm_num) hE hc
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_twistedE6_two hℓ hf K hK σ hσ hp hp3 he
    exact not_rankLE2_of_elemAbelian hp (by norm_num) hE hc
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_twistedE6_six hℓ hf K hK σ hσ hp he
    exact not_rankLE2_of_elemAbelian hp (by norm_num) hE hc

end Adjoint

end CFSG.LieType.SeitzGeneration
