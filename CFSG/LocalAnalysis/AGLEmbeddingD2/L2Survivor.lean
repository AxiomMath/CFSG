module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinTwo
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorel
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorelAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoReduced
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorus
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoUnipotentCentralizer

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding CFSG.ComponentClassification.OuterAutomorphisms

variable {X : Type} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ K : Subgroup X}

namespace D2AlmostSimple

theorem not_dvd_card_outer_of_psl2 [Fact p.Prime] (h : D2AlmostSimple p X R A X₀ K)
    (e : K ≃* PSL2GF p 2) : ¬ p ∣ Nat.card (Outer K) := by
  have hp3 : 3 ≤ p := by have := h.prime.two_le; have := h.ne_two; omega
  exact not_dvd_card_outer_of_linTwo h.ne_two (by norm_num) le_rfl
    (le_trans (by norm_num) (Nat.pow_le_pow_left hp3 2)) e

theorem sylow_inf_eq_of_psl2 [Fact p.Prime] (h : D2AlmostSimple p X R A X₀ K)
    (e : K ≃* PSL2GF p 2) : (R : Subgroup X) ⊓ K = A ∧ (R : Subgroup X) = A := by
  have hRK : (R : Subgroup X) ≤ K :=
    h.sylow_le_of_not_dvd_card_outer (h.not_dvd_card_outer_of_psl2 e)
  have := h.normal
  obtain ⟨-, hcard⟩ := isElemAbelian_sylow_inf_of_psl2GF (by norm_num) e R
  rw [inf_eq_left.mpr hRK] at hcard ⊢
  have hAR : A = R := Subgroup.eq_of_le_of_card_ge h.A_le (le_of_eq (by rw [hcard, h.card_A]))
  exact ⟨hAR.symm, hAR.symm⟩

theorem A_le_of_psl2 [Fact p.Prime] (h : D2AlmostSimple p X R A X₀ K) (e : K ≃* PSL2GF p 2) :
    A ≤ K :=
  (h.sylow_inf_eq_of_psl2 e).1 ▸ inf_le_right

theorem centralizer_A_le_of_psl2 [Fact p.Prime] (h : D2AlmostSimple p X R A X₀ K)
    (e : K ≃* PSL2GF p 2) : Subgroup.centralizer (A : Set X) ≤ A := by
  have hC := centralizer_sylow_inf_le_of_psl2GF kFactL2UnipotentCentralizer h.ne_two
    (by norm_num) h.normal ⟨e⟩ h.centralizer_eq_bot R
  rwa [(h.sylow_inf_eq_of_psl2 e).1] at hC

theorem A_ne_bot (h : D2AlmostSimple p X R A X₀ K) : A ≠ ⊥ := by
  intro hbot
  have hc := h.card_A
  rw [hbot, Subgroup.card_bot] at hc
  have := Nat.one_lt_pow two_ne_zero h.prime.one_lt
  omega

theorem normalizer_A_eq_of_psl2 [Fact p.Prime] (h : D2AlmostSimple p X R A X₀ K)
    (e : K ≃* PSL2GF p 2) : Subgroup.normalizer (A : Set X) = X₀ := by
  have := h.normal
  obtain ⟨hU, -⟩ := h.sylow_inf_eq_of_psl2 e
  have hN : Subgroup.normalizer (A : Set X) ≤ X₀ := h.normalizer_le_of_le_A A le_rfl h.A_ne_bot
  have hN' : Subgroup.normalizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) ≤ X₀ := by
    rw [hU]
    exact hN
  have hY₀K := inf_le_normalizer_of_psl2GF h.ne_two (by norm_num) e R hN' h.not_le
  have hUY₀ : (R : Subgroup X) ⊓ K ≤ X₀ := Subgroup.le_normalizer.trans hN'
  have hle := le_normalizer_sylow_inf K R hUY₀ hY₀K
  rw [hU] at hle
  exact le_antisymm hN hle

theorem dichotomy_of_psl2 [Fact p.Prime] (h : D2AlmostSimple p X R A X₀ K)
    (e : K ≃* PSL2GF p 2) {W : Subgroup X} (hWY₀ : W ≤ X₀)
    (hY₀W : X₀ ≤ Subgroup.normalizer (W : Set X)) : W = ⊥ ∨ A ≤ W := by
  have hp2 := h.ne_two
  have h2 : (2 : GaloisField p 2) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p 2) p]; exact hp2)
  have hCU := h.centralizer_A_le_of_psl2 e
  have hNA := h.normalizer_A_eq_of_psl2 e
  have hY₀U : X₀ ≤ Subgroup.normalizer (A : Set X) := hNA.ge
  have hUY₀ : A ≤ X₀ := Subgroup.le_normalizer.trans hNA.le
  obtain ⟨ψ, -, hψU, hψc⟩ :=
    exists_torus_param_of_mulEquiv_psl2GF hp2 (by norm_num) e A (h.A_le_of_psl2 e) h.card_A
  rcases (W ⊓ A).bot_or_exists_ne_one with hWU | ⟨g, ⟨hgW, hgU⟩, hg1⟩
  ·
    left
    rw [eq_bot_iff]
    intro w hw
    have hwC : w ∈ Subgroup.centralizer (A : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hcW : w * u * w⁻¹ * u⁻¹ ∈ W := by
        have h' := (Subgroup.mem_normalizer_iff.mp (hY₀W (hUY₀ hu)) w⁻¹).mp (W.inv_mem hw)
        simpa only [mul_assoc] using W.mul_mem hw h'
      have hcomm : w * u * w⁻¹ * u⁻¹ ∈ W ⊓ A := ⟨hcW,
        A.mul_mem ((Subgroup.mem_normalizer_iff.mp (hY₀U (hWY₀ hw)) u).mp hu) (A.inv_mem hu)⟩
      rw [hWU, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hcomm
      exact hcomm.symm
    have hwWU : w ∈ W ⊓ A := ⟨hw, hCU hwC⟩
    rwa [hWU] at hwWU
  ·
    right
    rw [← hψU] at hgU ⊢
    obtain ⟨a, rfl⟩ := hgU
    refine range_le_of_torus h2 ψ (fun μ => ?_) hgW hg1
    obtain ⟨c, -, hc⟩ := hψc μ
    have hcN : c ∈ Subgroup.normalizer (A : Set X) :=
      hψU ▸ mem_normalizer_range_of_torus ψ μ.ne_zero hc
    exact ⟨c, hY₀W (hNA.le hcN), hc⟩

theorem primeComplementCore_eq_bot_of_psl2 [Fact p.Prime] (h : D2AlmostSimple p X R A X₀ K)
    (e : K ≃* PSL2GF p 2) : primeComplementCore (G := X₀) p = ⊥ := by
  have hp : p.Prime := h.prime
  set W := (primeComplementCore (G := X₀) p).map X₀.subtype
  have hWsub : W.subgroupOf X₀ = primeComplementCore (G := X₀) p :=
    Subgroup.comap_map_eq_self_of_injective X₀.subtype_injective _
  have hWX₀ : W ≤ X₀ := Subgroup.map_subtype_le _
  have hY₀W : X₀ ≤ Subgroup.normalizer (W : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWX₀).mp (by rw [hWsub]; infer_instance)
  have hcop : p.Coprime (Nat.card W) := by
    rw [Subgroup.card_map_of_injective X₀.subtype_injective]
    exact primeComplementCore_coprime p
  have hW : W = ⊥ := by
    rcases h.dichotomy_of_psl2 e hWX₀ hY₀W with hW | hAW
    · exact hW
    · exfalso
      have hdvd : Nat.card A ∣ Nat.card W := Subgroup.card_dvd_of_le hAW
      rw [h.card_A] at hdvd
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
        ((dvd_pow_self p two_ne_zero).trans hdvd)
  exact (Subgroup.map_eq_bot_iff_of_injective _ X₀.subtype_injective).mp hW

end D2AlmostSimple

end CFSG.AGLEmbeddingD2
