module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieTransfer
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSL
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.RankThree.PartOne.FOC.PSLTwoOuter
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSL)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinearSubfield
open CFSG.HardMathSupport.Lang.UnitaryAutomorphisms CFSG.HardMathSupport.Lang.Coordinator

theorem psl_three_pRank_fixed {K : Type} [Group K] [Finite K] {n ℓ f : ℕ} (hn : 3 ≤ n)
    (hcl : StatedClassicalModel K .PSL n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : ¬ p ∣ Nat.gcd n (ℓ ^ f - 1)) (α : MulAut K) (hαp : α ^ p = 1) (hαin : α ∉ inner K) :
    p ∣ f ∧ ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = ℓ ^ (f / p) ∧
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL n F₀))) ≤
        CFSG.Open.pRank p (fixedSubgroup α) := by
  classical
  obtain ⟨⟨hℓ, hf, hn2, -, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have : Fintype F := Fintype.ofFinite F
  have hFcard' : Fintype.card F = ℓ ^ f := by rw [← Nat.card_eq_fintype_card]; exact hFcard
  have : CharP F ℓ := charP_of_card_eq_prime_pow hFcard'
  have hdiv' : ¬ p ∣ Nat.gcd n (Nat.card F - 1) := by rw [hFcard]; exact hdiv
  let θ : K ≃* projectiveSL n F := e.trans (statedProjSLEquiv n F)
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL n F) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 =>
    hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hβE : β ∈ semilinearAutGroup n F :=
    CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.mem_semilinearAutGroup_of_pow hn
      (hp.odd_of_ne_two hp2) hβp
  by_cases hD : β ∈ linearAutGroup n F
  · exfalso
    exact hβout (CFSG.RankThree.PartOne.OutStructure.linear_D2 hp hn hdiv' β hD 1
      (by
        rw [pow_one, hβp]
        exact (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem))
  obtain ⟨hpf, σ, hσord, ⟨h, hh, hβh⟩, hcardk⟩ :=
    higher_linear_prime_semilinear_field_descent' hℓ hf hn hFcard hp β hβE hD hβord
  obtain ⟨H, rfl⟩ := mem_linearAutGroup_iff.mp hh
  refine ⟨hpf, semilinearFixedSubfield σ, inferInstance, Subtype.finite, hcardk, ?_⟩
  have hfix : fixedSubgroup (fieldAut n F σ) =
      (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range :=
    SetLike.coe_injective (fixedSubgroup_fieldAut_eq_range hp hn hdiv' σ hσord)
  have hinj := linearSubfieldInclusion_injective (K := F) (n := n) (by omega)
    (semilinearFixedSubfield σ)
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL n (semilinearFixedSubfield σ))) ≤
      CFSG.Open.pRank p (fixedSubgroup (fieldAut n F σ)) :=
    pRank_top_le_pRank_fixed_of_embedding hp1
      (linearSubfieldInclusion n (semilinearFixedSubfield σ)) hinj (fieldAut n F σ) fun a => by
        have : linearSubfieldInclusion n (semilinearFixedSubfield σ) a ∈
            fixedSubgroup (fieldAut n F σ) := by
          rw [hfix]; exact ⟨a, rfl⟩
        exact this
  have h2 : CFSG.Open.pRank p (fixedSubgroup (fieldAut n F σ)) ≤
      CFSG.Open.pRank p (fixedSubgroup β) :=
    pRank_fixed_le_of_intertwine hp1 (conjAut n F H : MulAut _).symm β (fieldAut n F σ) fun x => by
      rw [hβh]
      simp [MulAut.mul_apply]
  have h3 : CFSG.Open.pRank p (fixedSubgroup β) ≤ CFSG.Open.pRank p (fixedSubgroup α) :=
    pRank_fixed_le_of_intertwine hp1 θ α β fun x => by
      rw [hβdef]
      simp [MulAut.congr_apply]
  have h4 : CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL n (semilinearFixedSubfield σ)))) =
      CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL n (semilinearFixedSubfield σ))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 (statedProjSLEquiv n (semilinearFixedSubfield σ))
  omega

theorem psl_two_pRank_fixed {K : Type} [Group K] [Finite K] {ℓ f : ℕ}
    (hcl : StatedClassicalModel K .PSL 2 ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut K) (hαp : α ^ p = 1) (hαin : α ∉ inner K) :
    p ∣ f ∧ ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = ℓ ^ (f / p) ∧
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL 2 F₀))) ≤
        CFSG.Open.pRank p (fixedSubgroup α) := by
  classical
  obtain ⟨⟨hℓ, hf, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  let ψ : K ≃* CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateG F :=
    (e.trans (statedProjSLEquiv 2 F)).trans
      ((LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 F).symm.trans
        (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pslEquivCoordinateG F))
  have hαord : orderOf α = p := by
    refine orderOf_eq_prime hαp ?_
    intro h1
    exact hαin (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner K).one_mem)
  obtain ⟨hpf, k, hkcard, ⟨eX⟩⟩ := CFSG.RankThree.PartOne.FOC.psl_two_fixSub_equiv_gen hℓ hp hp2
    hf hFcard ψ hαord hαin
  refine ⟨hpf, k, inferInstance, Subtype.finite, hkcard, ?_⟩
  have h1 : CFSG.Open.pRank p (fixedSubgroup α) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥(fixedSubgroup α)) :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_eq_pRank_top _
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup ↥(fixedSubgroup α)) =
      CFSG.Open.pRank p (⊤ : Subgroup
        (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateG ↥k)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 eX
  have h3 : CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL 2 ↥k))) =
      CFSG.Open.pRank p (⊤ : Subgroup
        (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateG ↥k)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 ↥k).symm.trans
        (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pslEquivCoordinateG ↥k))
  omega

theorem two_le_pRank_statedProj_PSL {p n f₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 2 ≤ n)
    (hf₀ : 1 ≤ f₀) (hcase : 3 ≤ n ∨ 2 ≤ f₀) {F₀ : Type} [Field F₀] [Finite F₀]
    (hF₀ : Nat.card F₀ = p ^ f₀) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL n F₀))) := by
  have hq5 : 5 ≤ p ^ f₀ := le_trans hp5 (Nat.le_self_pow (by omega) p)
  have hm : StatedClassicalModel (StatedProj (StatedSL n F₀)) .PSL n p f₀ := by
    refine ⟨⟨hp, hf₀, hn, fun h => ?_, fun h => ?_⟩, F₀, inferInstance, inferInstance, hF₀,
      ⟨MulEquiv.refl _⟩⟩
    · exact absurd ((Prod.mk.inj h).2 ▸ hq5) (by norm_num)
    · exact absurd ((Prod.mk.inj h).2 ▸ hq5) (by norm_num)
  obtain ⟨-, -, hcases⟩ := CFSG.SectionRank.classical_model_rank (by omega) hm
  rcases hcases with ⟨-, h1 | h1 | h1⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h1
  · omega
  · omega
  · omega
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · omega

theorem outerFixedRankDefAt_PSL : OuterFixedRankDefAt .PSL := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ α hαp hαin
  subst hℓ
  have hcl : StatedClassicalModel K .PSL n ℓ f :=
    hmodel.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨-, hf, hn2, -, -⟩ := hadm
  have hdiv : ¬ ℓ ∣ Nat.gcd n (ℓ ^ f - 1) := by
    intro h
    have h1 : ℓ ∣ ℓ ^ f - 1 := h.trans (Nat.gcd_dvd_right _ _)
    have h2 : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ (by omega)
    have h3 : ℓ ∣ ℓ ^ f - (ℓ ^ f - 1) := Nat.dvd_sub h2 h1
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h3
    exact hp.one_lt.ne' (Nat.dvd_one.1 h3)
  by_cases hn3 : 3 ≤ n
  · obtain ⟨hpf, F₀, _, _, hcard, hrank⟩ := psl_three_pRank_fixed hn3 hcl hp (by omega) hdiv α
      hαp hαin
    have hf0 : 1 ≤ f / ℓ := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
    have := two_le_pRank_statedProj_PSL hp hp5 hn2 hf0 (Or.inl hn3) hcard
    exact Or.inl (by omega)
  · obtain rfl : n = 2 := by omega
    obtain ⟨hpf, F₀, _, _, hcard, hrank⟩ := psl_two_pRank_fixed hcl hp (by omega) α hαp hαin
    have hf0 : 1 ≤ f / ℓ := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
    by_cases h2 : 2 ≤ f / ℓ
    · have := two_le_pRank_statedProj_PSL hp hp5 hn2 hf0 (Or.inr h2) hcard
      exact Or.inl (by omega)
    · refine Or.inr ⟨rfl, rfl, ?_⟩
      obtain ⟨c, hc⟩ := hpf
      have hc1 : f / ℓ = c := by rw [hc, Nat.mul_div_cancel_left _ hp.pos]
      have : c = 1 := by omega
      rw [hc, this, mul_one]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
