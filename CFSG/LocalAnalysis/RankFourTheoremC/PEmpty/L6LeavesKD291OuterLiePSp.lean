module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieTransfer
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSp
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSp)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.RankThree.CASymplecticSubfield
open CFSG.RankThree.Classical.SteinbergBY (symplectic_prime_semilinear_field_descent)
open CFSG.HardMathSupport.Lang.UnitaryAutomorphisms CFSG.HardMathSupport.Lang.Coordinator
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)

theorem psp_pRank_fixed {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hcl : StatedClassicalModel K .PSp n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut K) (hαp : α ^ p = 1) (hαin : α ∉ inner K) :
    p ∣ f ∧ ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = ℓ ^ (f / p) ∧
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSp n F₀))) ≤
        CFSG.Open.pRank p (fixedSubgroup α) := by
  classical
  obtain ⟨⟨hℓ, hf, hn, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨-, -, -, -, -, -, -, hidx, hDH, hdesc⟩ :=
    symplectic_prime_semilinear_field_descent hℓ hf hn hFcard
  set β := MulAut.congr e α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp n F)) :=
    fun hin => hαin ((congr_mem_inner_iff e α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 =>
    hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hβE : β ∈ spSemilinearAutGroup n F := mem_of_pow_eq_one_of_index_dvd_two hidx hp hp2 hβp
  by_cases hD : β ∈ spLinearAutGroup n F
  · exfalso
    haveI := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal
      (StatedProj (StatedSp n F))
    exact hβout (mem_of_pow_eq_one_of_relIndex_dvd_two
      (H := CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp n F)))
      (D := spLinearAutGroup n F) (hDH.trans (Nat.gcd_dvd_left 2 _)) hp hp2 hD hβp)
  obtain ⟨hpf, σ, hσord, hcardk, h, hh, hβh⟩ := hdesc p hp β hβE hD hβord
  refine ⟨hpf, descentField σ, inferInstance, Subtype.finite, hcardk, ?_⟩
  have hfix : fixedSubgroup (fieldAut n F σ) = (subfieldSpProj n (descentField σ)).range :=
    Subgroup.ext fun x => fieldAut_apply_eq_self_iff (by omega)
      (by rw [hσord]; exact hp.odd_of_ne_two hp2) x
  have hinj := subfieldSpProj_injective (K := F) (r := n) (by omega) (descentField σ)
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSp n (descentField σ)))) ≤
      CFSG.Open.pRank p (fixedSubgroup (fieldAut n F σ)) :=
    pRank_top_le_pRank_fixed_of_embedding hp1 (subfieldSpProj n (descentField σ)) hinj
      (fieldAut n F σ) fun a => by
        have : subfieldSpProj n (descentField σ) a ∈ fixedSubgroup (fieldAut n F σ) := by
          rw [hfix]; exact ⟨a, rfl⟩
        exact this
  have h2 : CFSG.Open.pRank p (fixedSubgroup (fieldAut n F σ)) ≤
      CFSG.Open.pRank p (fixedSubgroup β) :=
    pRank_fixed_le_of_intertwine hp1 (h : MulAut _).symm β (fieldAut n F σ) fun x => by
      rw [hβh]
      simp [MulAut.mul_apply]
  have h3 : CFSG.Open.pRank p (fixedSubgroup β) ≤ CFSG.Open.pRank p (fixedSubgroup α) :=
    pRank_fixed_le_of_intertwine hp1 e α β fun x => by
      rw [hβdef]
      simp [MulAut.congr_apply]
  omega

theorem two_le_pRank_statedProj_PSp {p n f₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 2 ≤ n)
    (hf₀ : 1 ≤ f₀) {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Nat.card F₀ = p ^ f₀) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSp n F₀))) := by
  have hq5 : 5 ≤ p ^ f₀ := le_trans hp5 (Nat.le_self_pow (by omega) p)
  have hm : StatedClassicalModel (StatedProj (StatedSp n F₀)) .PSp n p f₀ := by
    refine ⟨⟨hp, hf₀, hn, fun h => ?_⟩, F₀, inferInstance, inferInstance, hF₀,
      ⟨MulEquiv.refl _⟩⟩
    exact absurd ((Prod.mk.inj h).2 ▸ hq5) (by norm_num)
  obtain ⟨-, -, hcases⟩ := CFSG.SectionRank.classical_model_rank (by omega) hm
  rcases hcases with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨-, h1 | h1⟩ | h1
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · omega
  · omega
  · omega

theorem outerFixedRankDefAt_PSp : OuterFixedRankDefAt .PSp := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ α hαp hαin
  subst hℓ
  have hcl : StatedClassicalModel K .PSp n ℓ f :=
    hmodel.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨-, hf, hn2, -⟩ := hadm
  obtain ⟨hpf, F₀, _, _, hcard, hrank⟩ := psp_pRank_fixed hcl hp (by omega) α hαp hαin
  have hf0 : 1 ≤ f / ℓ := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have := two_le_pRank_statedProj_PSp hp hp5 hn2 hf0 hcard
  exact Or.inl (by omega)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
