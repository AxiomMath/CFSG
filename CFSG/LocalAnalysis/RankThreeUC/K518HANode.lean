module

public import CFSG.LocalAnalysis.RankThreeUC.K518HAAut
public import CFSG.LocalAnalysis.RankThreeUC.K518HRkDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviQuasi

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open CFSG.AGLEmbeddingD2.Tits.GN516

@[expose] def NodeGood (Λ : Type) [Group Λ] [Finite Λ] (p : ℕ) : Prop :=
  ((∀ N : Subgroup Λ, N.Normal → IsPGroup 2 N → N = ⊥) ∧ RKGood Λ p ∧
      p ∣ Nat.card (MulAut.conj : Λ →* MulAut Λ).range) ∨
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Λ)

theorem normal_two_eq_bot_of_quasisimple {Λ : Type} [Group Λ] [Finite Λ]
    (hq : CFSG.Open.IsQuasisimple Λ) (hZ : ∀ z ∈ Subgroup.center Λ, ∃ m : ℕ, Odd m ∧ z ^ m = 1)
    (N : Subgroup Λ) [N.Normal] (hN2 : IsPGroup 2 N) : N = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial (Λ ⧸ Subgroup.center Λ) := hq.2.toNontrivial
  haveI : Nontrivial Λ :=
    Function.Surjective.nontrivial (f := QuotientGroup.mk' (Subgroup.center Λ))
      (QuotientGroup.mk'_surjective _)
  rcases normal_le_center_or_eq_top hq N with hc | ht
  · refine eq_bot_iff.2 fun x hx => ?_
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).1 hN2 ⟨x, hx⟩
    have h1 : orderOf x = 2 ^ k := by rw [← Subgroup.orderOf_mk x hx, hk]
    obtain ⟨m, hm, hxm⟩ := hZ x (hc hx)
    have h2 : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one hxm
    have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (h1 ▸ dvd_rfl) h2)
  · exfalso
    have h2 : IsPGroup 2 Λ := by
      refine (IsPGroup.iff_orderOf).2 fun g => ?_
      have hg : g ∈ N := by rw [ht]; exact Subgroup.mem_top g
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).1 hN2 ⟨g, hg⟩
      exact ⟨k, by rw [← Subgroup.orderOf_mk g hg, hk]⟩
    exact false_of_isPGroup_of_perfect h2 hq.1

theorem conj_injective_of_center_eq_bot {G : Type*} [Group G] (h : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  refine eq_bot_iff.2 fun x hx => ?_
  have : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : (MulAut.conj x : MulAut G) g = g := by
      rw [MonoidHom.mem_ker.1 hx]
      rfl
    rw [MulAut.conj_apply] at h1
    calc g * x = (x * g * x⁻¹) * x := by rw [h1]
      _ = x * g := by group
  rw [h] at this
  exact this

section SL2

open CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.ParabHub

variable {k : Type} [Field k] [Finite k] [CharP k 2]

private theorem normal_two_eq_bot_sl2 (N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k)) [N.Normal]
    (hN2 : IsPGroup 2 N) : N = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm1, hm⟩ := exists_card_eq_two_pow k
  by_cases h1 : m = 1
  · have h2 : Nat.card k = 2 := by rw [hm, h1, pow_one]
    have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) = 6 := by
      rw [card_sl2, h2]
      norm_num
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hN2
    have hdvd : Nat.card N ∣ 6 := hcard ▸ Subgroup.card_subgroup_dvd_card N
    have hj2 : j < 2 := by
      by_contra hge
      have h4 : 2 ^ 2 ∣ Nat.card N := by
        rw [hj]
        exact pow_dvd_pow 2 (not_lt.1 hge)
      have := h4.trans hdvd
      omega
    interval_cases j
    · exact Subgroup.eq_bot_of_card_eq N (by simpa using hj)
    · exfalso
      obtain ⟨x, hx1, hxu⟩ := (Nat.card_eq_two_iff' (1 : ↥N)).1 (by rw [hj]; norm_num)
      have hcen : (x : Matrix.SpecialLinearGroup (Fin 2) k) ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hmem : g * (x : Matrix.SpecialLinearGroup (Fin 2) k) * g⁻¹ ∈ N :=
          Subgroup.Normal.conj_mem ‹N.Normal› _ x.2 g
        have hne : (⟨g * (x : Matrix.SpecialLinearGroup (Fin 2) k) * g⁻¹, hmem⟩ : ↥N) ≠ 1 := by
          intro h
          apply hx1
          have h' := congrArg Subtype.val h
          have : (x : Matrix.SpecialLinearGroup (Fin 2) k) = 1 := by
            have h'' : g * (x : Matrix.SpecialLinearGroup (Fin 2) k) * g⁻¹ = 1 := h'
            calc (x : Matrix.SpecialLinearGroup (Fin 2) k)
                = g⁻¹ * (g * (x : Matrix.SpecialLinearGroup (Fin 2) k) * g⁻¹) * g := by group
              _ = 1 := by rw [h'']; group
          exact Subtype.ext this
        have heq := hxu _ hne
        have h2 := congrArg Subtype.val heq
        calc g * (x : Matrix.SpecialLinearGroup (Fin 2) k)
            = (g * (x : Matrix.SpecialLinearGroup (Fin 2) k) * g⁻¹) * g := by group
          _ = (x : Matrix.SpecialLinearGroup (Fin 2) k) * g := by
            have h3 : g * (x : Matrix.SpecialLinearGroup (Fin 2) k) * g⁻¹ =
              (x : Matrix.SpecialLinearGroup (Fin 2) k) := h2
            rw [h3]
      rw [sl2_center_eq_bot, Subgroup.mem_bot] at hcen
      exact hx1 (Subtype.ext hcen)
  · have h4 : 4 ≤ Nat.card k := by
      rw [hm]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) k) := sl2_isSimpleGroup h4
    have hq : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) k) :=
      ⟨(sl2_isPerfect h4).commutator_eq_top,
        ((QuotientGroup.quotientMulEquivOfEq sl2_center_eq_bot).trans
          QuotientGroup.quotientBot).isSimpleGroup⟩
    exact normal_two_eq_bot_of_quasisimple hq (fun z hz => by
      rw [sl2_center_eq_bot, Subgroup.mem_bot] at hz
      exact ⟨1, odd_one, by rw [hz, one_pow]⟩) N hN2

theorem nodeGood_sl2 (h1 : K518RkSL2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpk : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) k)) :
    NodeGood (Matrix.SpecialLinearGroup (Fin 2) k) p := by
  left
  refine ⟨fun N _ hN2 => normal_two_eq_bot_sl2 N hN2, ?_, ?_⟩
  · intro ψ hψ hnot
    exact h1 k (ringChar.eq k 2) p hp hp2 hpk ψ hψ hnot
  · rw [← Nat.card_congr
      (MonoidHom.ofInjective (conj_injective_of_center_eq_bot sl2_center_eq_bot)).toEquiv]
    exact hpk

end SL2

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end
