module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevWreath
public import CFSG.GroupTheory.WeirSylow.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace RankChevProof

open CFSG.Open CFSG.SectionRank CFSG.GroupTheory.WeirSylow

theorem pRank_wreath_cyclic {p : ℕ} (hp : p.Prime) [NeZero p] {P : Type*} [Group P] [Finite P]
    (hm : 1 ≤ pRank p (⊤ : Subgroup P)) :
    pRank p (⊤ : Subgroup (P ≀ᵣ Multiplicative (ZMod p))) = p * pRank p (⊤ : Subgroup P) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact pRank_wreath (by rw [Fintype.card_multiplicative, ZMod.card]) hm

theorem pRank_wreathTower {p : ℕ} [hp : Fact p.Prime] {a : ℕ} (ha : 1 ≤ a) :
    ∀ i : ℕ, pRank p (⊤ : Subgroup (wreathTower p (Multiplicative (ZMod (p ^ a))) i)) = p ^ i
  | 0 => pRank_multiplicative_zmod ha
  | i + 1 => by
    have ih := pRank_wreathTower (p := p) ha i
    have hm : 1 ≤ pRank p (⊤ : Subgroup (wreathTower p (Multiplicative (ZMod (p ^ a))) i)) := by
      rw [ih]
      exact Nat.one_le_pow _ _ hp.out.pos
    have h := pRank_wreath_cyclic hp.out hm
    rw [ih] at h
    exact h.trans (by rw [pow_succ, mul_comm])

theorem sum_getElem_mul_pow (p : ℕ) :
    ∀ L : List ℕ, ∑ i : Fin L.length, L[i] * p ^ (i : ℕ) = Nat.ofDigits p L
  | [] => by simp
  | d :: L => by
    have h := Fin.sum_univ_succ (n := L.length)
      (fun i : Fin (L.length + 1) => (d :: L)[i] * p ^ (i : ℕ))
    refine h.trans ?_
    rw [Nat.ofDigits_cons, ← sum_getElem_mul_pow p L, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, List.getElem_cons_zero, Fin.val_succ,
      List.getElem_cons_succ, pow_succ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (d :: L)[i.succ] = L[i] := rfl
    rw [e]
    ring

theorem pRank_sigmaModel (p : ℕ) [hp : Fact p.Prime] (e a N : ℕ) (ha : 1 ≤ a) :
    pRank p (⊤ : Subgroup (sigmaModel p e a N)) = N / e := by
  have h1 : pRank p (⊤ : Subgroup (sigmaModel p e a N)) =
      ∑ i : Fin (Nat.digits p (N / e)).length, (Nat.digits p (N / e))[i] * p ^ (i : ℕ) := by
    change pRank p (⊤ : Subgroup ((i : Fin (Nat.digits p (N / e)).length) →
      Fin (Nat.digits p (N / e))[i] →
        wreathTower p (Multiplicative (ZMod (p ^ a))) i)) = _
    rw [pRank_pi]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pRank_pi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      pRank_wreathTower ha]
  rw [h1, sum_getElem_mul_pow, Nat.ofDigits_digits]

theorem pRank_eq_of_sylow_sigmaModel (p : ℕ) [hp : Fact p.Prime] {G : Type} [Group G] [Finite G]
    {e a N : ℕ} (ha : 1 ≤ a) (h : ∀ P : Sylow p G, Nonempty (P ≃* sigmaModel p e a N)) :
    pRank p (⊤ : Subgroup G) = N / e := by
  have hp1 : 1 < p := hp.out.one_lt
  apply le_antisymm
  · refine pRank_le hp1 (fun E _ hE => ?_)
    have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
    obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
    obtain ⟨φ⟩ := h Q
    let ι : E →* sigmaModel p e a N := φ.toMonoidHom.comp (Subgroup.inclusion hEQ)
    have hι : Function.Injective ι := φ.injective.comp (Subgroup.inclusion_injective hEQ)
    have hle := card_le_pow_pRank_of_injective (p := p)
      (fun a b => hE.1.is_comm.comm a b)
      (fun a => Subtype.ext (by simpa using hE.2 a a.2)) ι hι
    rwa [pRank_sigmaModel p e a N ha] at hle
  · obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p G))
    obtain ⟨φ⟩ := h S
    rw [← pRank_sigmaModel p e a N ha, ← pRank_top_eq_of_mulEquiv hp1 φ]
    exact pRank_top_le_of_injective hp1 (S : Subgroup G).subtype Subtype.val_injective

end RankChevProof

end CFSG.LocalAnalysis.RankThreeUC.S15
