module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AGap
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AModel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.Open
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns

theorem hasOrderThreeLift_of_mulEquiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X') {x : X}
    (h : HasOrderThreeLift X x) : HasOrderThreeLift X' (e x) := by
  rcases h with ⟨K, hK, hf, θ, hc, yh, hyh, hθ⟩ | ⟨K, hK, hf, q, θ, hc, hq, yh, hyh, hθ⟩
  · exact Or.inl ⟨K, hK, hf, e.symm.trans θ, hc, yh, hyh, by simpa using hθ⟩
  · exact Or.inr ⟨K, hK, hf, q, e.symm.trans θ, hc, hq, yh, hyh, by simpa using hθ⟩

theorem hasOrderThreeLift_of_model {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {X : Type*} [Group X]
    (g : X ≃* (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K))) {x : X}
    {t : ↥(slPi π 3 (p ^ f) K)} (ht : orderOf t = 3) (hx : g x = QuotientGroup.mk t) :
    HasOrderThreeLift X x := by
  have hfin := hK.finite
  let e := QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hq)
  cases π
  · refine Or.inr ⟨K, inferInstance, hfin, p ^ f, g.trans e, ?_, hq, t, ht, ?_⟩
    · rw [hK.card, piCard, Bool.cond_false]
    · show e (g x) = _
      rw [hx]
      rfl
  · refine Or.inl ⟨K, inferInstance, hfin, g.trans e, ?_, t, ht, ?_⟩
    · rw [hK.card, piCard, Bool.cond_true]
      exact hq
    · show e (g x) = _
      rw [hx]
      rfl

theorem exists_model_of_hasOrderThreeLift {Y : Type} [Group Y] (hY : CFSG.Open.IsQuasisimple Y)
    {y : Y} (h : HasOrderThreeLift Y y) :
    ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), PiField π p f K ∧ ModThree π (p ^ f) ∧
      2 < p ^ f ∧
      ∃ (e : Y ≃* (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)))
        (yh : ↥(slPi π 3 (p ^ f) K)), orderOf yh = 3 ∧ e y = QuotientGroup.mk yh := by
  rcases h with ⟨K, hKf, hFin, θ, hc, yh, hyh, hθ⟩ | ⟨K, hKf, hFin, q, θ, hcard, hq3, yh, hyh, hθ⟩
  · obtain ⟨p, f, hK, hmod, h2⟩ := exists_true_data K hc
    let e₀ : StatedProj (StatedSL 3 K) ≃*
        (↥(slPi true 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi true 3 (p ^ f) K)) :=
      (QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hmod)).symm
    refine ⟨true, p, f, K, hKf, hK, hmod, h2, θ.trans e₀, yh, hyh, ?_⟩
    show e₀ (θ y) = _
    rw [hθ]
    rfl
  · obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hcard
    have hK : PiField false p f K :=
      ⟨hF.prime, hF.one_le, by rw [piCard, Bool.cond_false]; exact hcard⟩
    have hmod : ModThree false (p ^ f) := hq3
    have h2 : 2 < p ^ f := by
      by_contra hle
      have hs := isSolvable_statedProj_of_pow_eq_two hF (pow_eq_two_of_not_two_lt hF hle)
      exact false_of_quasisimple_of_solvable hY
        (Group.isSolvable_of_isSolvable_injective (f := θ.toMonoidHom) θ.injective)
    let e₀ : StatedProj (StatedSU 3 (p ^ f) K) ≃*
        (↥(slPi false 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi false 3 (p ^ f) K)) :=
      (QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hmod)).symm
    refine ⟨false, p, f, K, hKf, hK, hmod, h2, θ.trans e₀, yh, hyh, ?_⟩
    show e₀ (θ y) = _
    rw [hθ]
    rfl

theorem l3gj_exists_frobModel {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K) (hq2 : 2 < p ^ f)
    (e : Y ≃* (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)))
    {α : MulAut Y} (h3 : α ^ 3 = 1) (hf : IsFieldAutThree α) (hα : α ≠ 1) :
    ∃ (σ : K ≃+* K) (_ : orderOf σ = 3) (x : GL (Fin 3) K) (_ : x ∈ glPi π 3 (p ^ f) K)
      (e₂ : Y ≃* (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K))),
      MulAut.congr e₂ α = centerDescend _ (frobSL hK σ) ∧
      ∀ (y : Y) (yh t : ↥(slPi π 3 (p ^ f) K)), e y = QuotientGroup.mk yh →
        (t : GL (Fin 3) K) = x * yh * x⁻¹ → e₂ y = QuotientGroup.mk t := by
  obtain ⟨pkg⟩ := exists_etaPkg hK hq2
  have hGq : CFSG.Open.IsQuasisimple ↥(slPi π 3 (p ^ f) K) :=
    isQuasisimple_slPi hK (fun _ h => by omega)
  have hGp : Group.IsPerfect ↥(slPi π 3 (p ^ f) K) := (Group.isPerfect_def).2 hGq.1
  have hcQ : Subgroup.center (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot _
  have hZ : Subgroup.center Y = ⊥ := center_eq_bot_of_mulEquiv_of_center_eq_bot e hcQ
  set ε : Y ≃* pkg.M := e.trans pkg.η with hε
  have hβ3 : MulAut.congr ε α ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  rcases pkg.dich _ hβ3 with hin | ⟨σ, hσ, κ, hκ, hβ⟩
  · exfalso
    apply hα
    refine eq_one_of_inndiag_model hY pkg.good ((barEquivBot hZ).trans ε) ?_ hf
    rw [congr_trans', congr_barEquivBot]
    exact hin
  · let e2 : Y ≃* (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) :=
      (ε.trans κ⁻¹).trans pkg.η.symm
    have hc : MulAut.congr e2 α = centerDescend _ (frobSL hK σ) := by
      have h1 : MulAut.congr e2 α =
          MulAut.congr pkg.η.symm (MulAut.congr κ⁻¹ (MulAut.congr ε α)) := by
        rw [congr_trans', congr_trans']
      rw [h1, hβ, congr_self, inv_inv]
      have h2 : κ⁻¹ * (κ * MulAut.congr pkg.η (centerDescend _ (frobSL hK σ)) * κ⁻¹) * κ =
          MulAut.congr pkg.η (centerDescend _ (frobSL hK σ)) := by group
      rw [h2]
      ext x
      simp [MulAut.congr_apply]
    obtain ⟨x, hx, hxc⟩ := pkg.conj_of_inndiag κ⁻¹ (pkg.P.inndiag.inv_mem hκ)
    refine ⟨σ, hσ, x, hx, e2, hc, fun y yh t hy ht => ?_⟩
    have h1 := hxc yh t ht
    rw [← h1]
    simp only [e2, hε, MulEquiv.trans_apply, MulAut.congr_apply, hy, MulEquiv.symm_symm]

end CFSG.HardMathSupport.Solomon.Coordinator
