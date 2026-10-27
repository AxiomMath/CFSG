module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.AlphaU43.Sound
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Cover423.Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.RigidOuter
public import CFSG.RankThree.PartTwo.Sec4.Item423Res3ProofMcL
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inputs
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofU43

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.AlphaU43

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.ComponentClassification.OuterAutomorphisms

theorem alphaNine_of_rigid_inputs {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (hOut : ∀ σ : MulAut X, ∃ k : ℕ, σ ^ (2 ^ k) ∈ (MulAut.conj : X →* MulAut X).range)
    (hchar : ∀ b : X, orderOf b = 3 →
      IsCharacteristicP 3 ↥(Subgroup.centralizer ({b} : Set X)))
    (hfix : ∀ b : X, orderOf b = 3 → ∀ τ : MulAut X, τ ^ 2 = 1 →
      τ ∉ (MulAut.conj : X →* MulAut X).range →
      ¬ ∀ c ∈ Subgroup.centralizer ({b} : Set X), τ c = c) :
    Census.Karpilovsky.Coordinator.Cover423.AlphaNine X := by
  intro D hD hD9
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD1 : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hD9
    omega
  have hord : ∀ b ∈ D, b ≠ 1 → orderOf b = 3 := fun b hb hb1 =>
    orderOf_eq_prime (hD.2 b hb) hb1
  refine Res423Three.alphaVanishes_of_rigid hZ hD1
    (fun b hb hb1 =>
      Res423Three.core_eq_bot_of_isCharacteristicP (hchar b (hord b hb hb1)))
    (fun b hb hb1 σ hσ hfixσ => ?_)
  have hb3 := hord b hb hb1
  have hbC : b ∈ Subgroup.centralizer ({b} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine Census.Karpilovsky.Proving.eq_one_of_fix_of_outer hZ hOut
    (Subgroup.centralizer ({b} : Set X)) ?_ ?_ σ hσ hfixσ
  · intro g hg
    have hgC : g ∈ Subgroup.centralizer ({b} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hg b hbC)
    have hcen : (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({b} : Set X))) ∈
        Subgroup.center ↥(Subgroup.centralizer ({b} : Set X)) := by
      rw [Subgroup.mem_center_iff]
      intro h
      exact Subtype.ext (hg h h.2).symm
    obtain ⟨k, hk⟩ := Res423Three.exists_pow_eq_one_of_mem_center (hchar b hb3) hcen
    exact ⟨k, congrArg Subtype.val hk⟩
  · intro τ hτ2 hτo hall
    exact hfix b hb3 τ hτ2 hτo hall

section U43

open CFSG.LieType.Multipliers.U43 CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut


theorem pow_eight_mem_range (σ : MulAut X₀) :
    σ ^ 8 ∈ (MulAut.conj : X₀ →* MulAut X₀).range := by
  obtain ⟨e, -⟩ := autModel
  have hinj : Function.Injective (MulAut.conj : X₀ →* MulAut X₀) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hcen : g ∈ Subgroup.center X₀ := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h2 : g * h * g⁻¹ = h := by
        have := DFunLike.congr_fun hg h
        simpa only [MulAut.conj_apply, MulAut.one_apply] using this
      calc h * g = g * h * g⁻¹ * g := by rw [h2]
        _ = g * h := by group
    rw [u43_center_eq_bot] at hcen
    exact Subgroup.mem_bot.1 hcen
  have hcardAut : Nat.card (MulAut X₀) = 26127360 := by
    rw [← card_Nrm]
    exact (Nat.card_congr e.toEquiv).symm
  have hcardInn : Nat.card (inner X₀) = 3265920 := by
    rw [← card_X₀]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hidx : (inner X₀).index = 8 := by
    have := (inner X₀).card_mul_index
    rw [hcardInn, hcardAut] at this
    omega
  have hmem := Subgroup.pow_index_mem (inner X₀) σ
  rw [hidx] at hmem
  exact hmem


theorem alphaNine_U43 :
    Census.Karpilovsky.Coordinator.Cover423.AlphaNine (CFSG.Assembly.RankThreeEven.projSU 4 3 1) := by
  have e : CFSG.Assembly.RankThreeEven.projSU 4 3 1 ≃* X₀ := Item434RemU43.projSUEquivUX
  have : Finite (CFSG.Assembly.RankThreeEven.projSU 4 3 1) := Finite.of_equiv _ e.symm.toEquiv
  refine alphaNine_of_rigid_inputs ?_ ?_ ?_ ?_
  ·
    rw [eq_bot_iff]
    intro g hg
    have : e g ∈ Subgroup.center X₀ := by
      rw [Subgroup.mem_center_iff] at hg ⊢
      intro h
      have := congrArg e (hg (e.symm h))
      simpa using this
    rw [u43_center_eq_bot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (e.injective (this.trans (map_one e).symm))
  ·
    intro σ
    refine ⟨3, ?_⟩
    obtain ⟨x, hx⟩ := pow_eight_mem_range (MulAut.congr e σ)
    refine ⟨e.symm x, ?_⟩
    apply (MulAut.congr e).injective
    rw [map_pow, congr_conj, e.apply_symm_apply]
    exact hx
  · exact CFSG.RankThree.PartTwo.Sec6.kCentCharThreeU43_holds
  ·
    intro b hb τ hτ2 hτo hall
    have hb' : orderOf (e b) = 3 := by rw [MulEquiv.orderOf_eq]; exact hb
    refine outer_not_fix hb' (MulAut.congr e τ) ?_ ?_ ?_
    · rw [← map_pow, hτ2, map_one]
    · rintro ⟨x, hx⟩
      apply hτo
      refine ⟨e.symm x, ?_⟩
      apply (MulAut.congr e).injective
      rw [congr_conj, e.apply_symm_apply]
      exact hx
    · intro c hc
      have hc' : e.symm c ∈ Subgroup.centralizer ({b} : Set (CFSG.Assembly.RankThreeEven.projSU 4 3 1)) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
        apply e.injective
        simpa using hc
      have := hall _ hc'
      show e (τ (e.symm c)) = c
      rw [this]
      simp

end U43

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.AlphaU43
