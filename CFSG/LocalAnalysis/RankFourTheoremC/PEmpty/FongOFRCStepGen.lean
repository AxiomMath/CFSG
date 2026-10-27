module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCExcRed
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCArith
public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint.Chevalley
open CFSG.RankThree.Chevalley (exhaustionPhi exhaustionMinusFactors
  pow_sub_one_eq_prod_exhaustionPhi exists_dvd_exhaustionPhi_of_dvd_prod)
open Polynomial

theorem dvd_eval_iff_of_natCast_eq {p : ℕ} (P : ℤ[X]) {q q₀ : ℕ}
    (h : (q : ZMod p) = (q₀ : ZMod p)) :
    (p : ℤ) ∣ P.eval (q : ℤ) ↔ (p : ℤ) ∣ P.eval (q₀ : ℤ) := by
  have hq : (p : ℤ) ∣ (q : ℤ) - (q₀ : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h, sub_self]
  have h1 : (p : ℤ) ∣ P.eval (q : ℤ) - P.eval (q₀ : ℤ) :=
    hq.trans (Polynomial.sub_dvd_eval_sub _ _ P)
  constructor
  · intro h2
    have := dvd_sub h2 h1
    simpa using this
  · intro h2
    have := dvd_add h2 h1
    simpa using this

theorem exists_dvd_exhaustionPhi_of_dvd_ord {p q N : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q)
    {D : List ℕ} (hD : ∀ d ∈ D, d ∈ ([2, 5, 6, 8, 9, 10, 12, 14, 18, 20, 24, 30] : List ℕ))
    (h : p ∣ q ^ N * (D.map fun d => q ^ d - 1).prod) :
    ∃ m ∈ D.flatMap exhaustionMinusFactors, (p : ℤ) ∣ (exhaustionPhi m).eval (q : ℤ) := by
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0
      exact absurd (dvd_zero p) hpq
    · exact h0
  have hprod : p ∣ (D.map fun d => q ^ d - 1).prod :=
    ((Nat.Prime.dvd_mul hp).1 h).resolve_left fun h' => hpq (hp.dvd_of_dvd_pow h')
  have hprodZ : (p : ℤ) ∣ (D.map fun d => (q : ℤ) ^ d - 1).prod := by
    have := Int.natCast_dvd_natCast.2 hprod
    have hc : (((D.map fun d => q ^ d - 1).prod : ℕ) : ℤ) = (D.map fun d => (q : ℤ) ^ d - 1).prod := by
      rw [Nat.cast_list_prod, List.map_map]
      congr 1
      refine List.map_congr_left fun d _ => ?_
      simp only [Function.comp_apply]
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hq1)]
      push_cast
      rfl
    rwa [hc] at this
  obtain ⟨a, ha, hpa⟩ := (Prime.dvd_prod_iff (Nat.prime_iff_prime_int.mp hp)).mp hprodZ
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
  have hfac := pow_sub_one_eq_prod_exhaustionPhi (q : ℤ) (hD d hd)
  rw [hfac] at hpa
  obtain ⟨m, hm, hpm⟩ := exists_dvd_exhaustionPhi_of_dvd_prod hp hpa
  exact ⟨m, List.mem_flatMap.2 ⟨d, hd, hm⟩, hpm⟩

theorem natCast_card_eq_of_pow {ℓ f₀ p : ℕ} [Fact p.Prime] {K k : Type} (hK : Nat.card K = ℓ ^ (p * f₀))
    (hk : Nat.card k = ℓ ^ f₀) : ((Nat.card K : ℕ) : ZMod p) = ((Nat.card k : ℕ) : ZMod p) := by
  rw [hK, hk, pow_mul']
  exact OFRC.natCast_pow_prime _

theorem pRank_le_one_of_cyclic_p_subgroups {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : ∀ Q : Subgroup G, IsPGroup p Q → IsCyclic Q) :
    CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 1 := by
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup G)
  have hpg : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨g, hg⟩ := (h E hpg).exists_generator
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hE.2 g g.2)
  have h1 : Nat.card E = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have h2 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  have h3 : p ^ CFSG.Open.pRank p (⊤ : Subgroup G) ≤ p := by
    rw [← hcard, h1]
    exact Nat.le_of_dvd hp.pos h2
  by_contra hcon
  have : p ^ 2 ≤ p ^ CFSG.Open.pRank p (⊤ : Subgroup G) :=
    Nat.pow_le_pow_right hp.pos (by omega)
  nlinarith [hp.two_le]

section


@[expose] def CyclicSylowGap (τ : Tag) (m : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] {p : ℕ}, p.Prime → 7 < p →
    (p : ℤ) ∣ (exhaustionPhi m).eval (Nat.card K : ℤ) →
      CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ K)) ≤ 1

theorem untwCrossRankStep_of_row {τ : Tag} {D : List ℕ} {N : ℕ}
    (hD : ∀ d ∈ D, d ∈ ([2, 5, 6, 8, 9, 10, 12, 14, 18, 20, 24, 30] : List ℕ))
    (hcard : ∀ (K : Type) [Field K] [Finite K], Nat.card (adjointGroup τ K) ∣
      Nat.card K ^ N * (D.map fun d => Nat.card K ^ d - 1).prod)
    (hrow : ∀ {ℓ f₀ p : ℕ}, ℓ.Prime → 1 ≤ f₀ → p.Prime → 5 ≤ p → ℓ ≠ p →
      ∀ (K k : Type) [Field K] [Finite K] [Field k] [Finite k],
        Nat.card K = ℓ ^ (p * f₀) → Nat.card k = ℓ ^ f₀ →
        ∀ m ∈ D.flatMap exhaustionMinusFactors,
          (p : ℤ) ∣ (exhaustionPhi m).eval (Nat.card K : ℤ) →
          2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ K)) →
            2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ k))) :
    UntwCrossRankStep τ := by
  intro ℓ f₀ p hℓ hf₀ hp hp5 hne K k _ _ _ _ hK hk hrkK
  have hpq : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact OFRC.not_dvd_pow_of_ne hp hℓ hne
  have hdvd : p ∣ Nat.card (adjointGroup τ K) := by
    obtain ⟨E, -, -, hcardE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
      (⊤ : Subgroup (adjointGroup τ K))
    have h0 : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ K)) ≠ 0 := by omega
    exact (hcardE ▸ dvd_pow_self p h0).trans (Subgroup.card_subgroup_dvd_card E)
  obtain ⟨m, hm, hpm⟩ := exists_dvd_exhaustionPhi_of_dvd_ord hp hpq hD (hdvd.trans (hcard K))
  exact hrow hℓ hf₀ hp hp5 hne K k hK hk m hm hpm hrkK

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
