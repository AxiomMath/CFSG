module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightSiegMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightOmBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightTorRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightOmClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)
open CFSG.RankThree.OrthogonalInvolutions (commSpace)
open CFSG.RankThree.PartOne.AUTSL (mem_matrixDerived_iff_even)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem ne_of_bClassAt_two_derived {n : ℕ}
    (htor : ∀ j : ℕ, 1 ≤ j → 2 * j < n + 1 → SpTwoAToralAt (n + 1) j) (hset : SeitzSetting G L)
    (hK : Nat.card K = 2) (hn : 3 ≤ n) (e : L ≃* StatedSp (n + 1) K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {κ : Sp2mKind} (hκ : κ = .omegaPlus ∨ κ = .omegaMinus)
    (hglob : NsRowGlobal e t (q2GlobalKind κ))
    (h1 : ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)),
      (nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ ∉
        (MulAut.conj : nsGlobal e →* MulAut (nsGlobal e)).range)
    (hclos : ∀ j : ℕ, 2 * j = n + 1 → SpTwoLagDerivedClosureAt (n + 1) j)
    {g : G} (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G))
    {K' : Type} [Field K'] [Finite K'] {Q : QuadraticForm K' (Fin (2 * (n + 1 + 1)) → K')}
    (hK' : Nat.card K' = 2 ^ 1) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * (n + 1 + 1)) → K'), Module.finrank K' T = 3 ∧
      ∀ x ∈ T, Q x = 0)
    (ε : nsGlobal e ≃* matrixProjectiveDerived Q) (β : MulAut (matrixProjectiveDerived Q))
    {s : matrixIsometries Q} (hs : s * s = 1)
    (h3 : 3 ≤ (((s : GL (Fin (2 * (n + 1 + 1))) K') :
      Matrix (Fin (2 * (n + 1 + 1))) (Fin (2 * (n + 1 + 1))) K') - 1).rank) :
    β⁻¹ * MulAut.congr ε ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) * β ≠
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) := by
  intro hβeq
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN : t ∈ normalizer (nsGlobal e : Set G) := mem_normalizer_nsGlobal e htC
  have hout := (hglob.2 htN).1
  obtain ⟨hZ, hoddC⟩ := nsGlobal_inf_centralizer_eq_bot_and_odd_two hK (by omega) e ht hKt hκ
    hglob
  have hLG : L ≤ nsGlobal e := le_nsGlobal hK (by omega) e
  set θt := (nsGlobal e).normalizerMonoidHom ⟨t, htN⟩ with hθt
  set θw := (nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ with hθw
  have houtw : θw ∉ (MulAut.conj : nsGlobal e →* MulAut (nsGlobal e)).range := h1 g hg
  have hnotZ : ¬ ∀ y : nsGlobal e, θw y = y → (∀ z : nsGlobal e, θw z = z → z * y = y * z) →
      y = 1 := by
    intro hZw
    have hθ' : MulAut.congr (ε.trans (β⁻¹ : MulAut (matrixProjectiveDerived Q))) θw =
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) := by
      rw [congr_trans_inv_eq, hβeq]
    have h1' := bCoord_finrank_eq_one_of_outer hQ hT _ houtw hZw hs hθ'
    rw [← lagRank_sub_one_eq_finrank_commSpace] at h1'
    omega
  obtain ⟨Kc, _, _, Qc, hKc, hQc, hTc, hEc, hImgc, ⟨εc⟩⟩ :=
    exists_coordModel_two_of_three_le hn e hκ hglob
  have : CharP Kc 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hconj : ∀ α : MulAut (matrixProjectiveDerived Qc), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Qc :=
    fun α _ => ⟨1, by rw [hImgc]; exact Subgroup.mem_top _⟩
  have hlin : ∀ (g' : G) (hg' : g'⁻¹ * t * g' ∈ normalizer (nsGlobal e : Set G)),
      ∃ s' : matrixIsometries Qc, s' * s' = 1 ∧
        MulAut.congr εc ((nsGlobal e).normalizerMonoidHom ⟨g'⁻¹ * t * g', hg'⟩) =
          matrixProjectiveConjugationHom Qc (matrixIsometryInclusion Qc s') := by
    intro g' hg'
    obtain ⟨β', s₁, hs₁, hβ'⟩ := exists_conj_linear_of_conj_nsGlobal hset (by omega) e hK ht hKt
      hKc hQc hTc hEc hconj εc hg'
    obtain ⟨s', hs', -, hθ⟩ := bCoord_exists_kappa_of_conj hImgc hs₁ hβ'
    exact ⟨s', hs', hθ⟩
  have hg1 : (1 : G)⁻¹ * t * 1 ∈ normalizer (nsGlobal e : Set G) := by simpa using htN
  obtain ⟨s₀, hs₀, hθ₀⟩ := hlin 1 hg1
  rw [normalizerMonoidHom_one_conj_eq htN hg1] at hθ₀
  have hZt := fixed_centreless_of_le ht hKt hLG htN hout
  have hr₀ : finrank Kc (commSpace (matrixLinearIso s₀.val)) = 1 :=
    bCoord_finrank_eq_one_of_outer hQc hTc εc hout hZt hs₀ hθ₀
  obtain ⟨sw, hsw, hθsw⟩ := hlin g hg
  have hswodd : Odd (finrank Kc (commSpace (matrixLinearIso sw.val))) := by
    rw [← Nat.not_even_iff_odd]
    intro hev
    have hΩ : sw.val ∈ matrixDerived Qc := (mem_matrixDerived_iff_even hQc hTc sw.2).2 hev
    exact houtw (bCoord_mem_range_conj_of_congr εc (hθsw.trans (bCoord_kappa_of_mem sw hΩ)))
  obtain ⟨j', hj'⟩ := hswodd
  have hj'1 : 1 ≤ j' := by
    by_contra h0
    have hr1 : finrank Kc (commSpace (matrixLinearIso sw.val)) = 1 := by omega
    obtain ⟨γ, hγ⟩ := exists_conj_of_rank_eq_one hQc hTc hsw hs₀
      (by rw [lagRank_sub_one_eq_finrank_commSpace]; exact hr1)
      (by rw [lagRank_sub_one_eq_finrank_commSpace]; exact hr₀)
    obtain ⟨β', hβ'⟩ := exists_conj_of_linearClass_conj εc (β := 1) (β₀ := 1) (θ := θw)
      (θ₀ := θt) (by rw [inv_one, one_mul, mul_one]; exact hθsw)
      (by rw [inv_one, one_mul, mul_one]; exact hθ₀) hγ
    apply hnotZ
    intro y hy hcomm
    have hθtw : θt = β'⁻¹ * θw * β' := by rw [mul_assoc, ← hβ']; group
    have hy1 : θt (β'⁻¹ y) = β'⁻¹ y := by
      rw [hθtw]
      simp only [MulAut.mul_apply, MulAut.apply_inv_self, hy]
    have hy2 : ∀ z : nsGlobal e, θt z = z → z * β'⁻¹ y = β'⁻¹ y * z := by
      intro z hz
      have hz' : θw (β' z) = β' z := by
        have h2 := congrArg (fun α : MulAut (nsGlobal e) => α z) hβ'
        simp only [MulAut.mul_apply, hz] at h2
        exact h2.symm
      have h3 := hcomm (β' z) hz'
      apply β'.injective
      rw [map_mul, map_mul, MulAut.apply_inv_self]
      exact h3
    have h4 := hZt (β'⁻¹ y) hy1 hy2
    have h5 := congrArg β' h4
    rwa [MulAut.apply_inv_self, map_one] at h5
  obtain ⟨σ⟩ : Nonempty (K ≃+* Kc) := by
    have := Fintype.ofFinite K
    have := Fintype.ofFinite Kc
    exact ⟨FiniteField.ringEquivOfCardEq (K := K) (K' := Kc) (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hKc, pow_one])⟩
  have hnb : centralizerPerfectCore
      (modelToG e (nsTorusSp K (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)))) ≤ nsGlobal e := by
    rw [nsGlobal_def]
    exact le_iSup (fun k : Fin (n + 1) => centralizerPerfectCore (modelToG e (nsTorusSp K k)))
      ⟨n + 1 - 1, by omega⟩
  have hnotL : ∀ y : G, y * t * y⁻¹ ∉ L := by
    intro y hyL
    have hy' : y⁻¹⁻¹ * t * y⁻¹ ∈ nsGlobal e := by rw [inv_inv]; exact hLG hyL
    have hyN : y⁻¹⁻¹ * t * y⁻¹ ∈ normalizer (nsGlobal e : Set G) := le_normalizer hy'
    apply h1 y⁻¹ hyN
    rw [normalizerMonoidHom_eq_conj_of_mem hy' hyN]
    exact ⟨_, rfl⟩
  exact false_of_q2OmegaBType_derived (N := n + 1) hset hK (by omega) e ht hKt hLG htN hout hZ
    hoddC
    (fun g' hg' β' hβ' => mem_normalizer_nsGlobal_of_conj_mulAut hset hK (by omega) e ht hKt htN
      hg' β' hβ') hnotL
    (fun j hj hjN t' c' hc'L Φ₂ hΦ₂ hΦ₂t hxa hodd₁ hodd₂ hfin =>
      false_of_planeTorus_of_at (htor j hj hjN) hK (by omega) e hLG hnb hjN hc'L Φ₂ hΦ₂ hΦ₂t hxa
        hodd₁ hodd₂ hfin) hclos (SpOmegaModelBType εc)
    (fun g' hg' j hj hB => omegaBShapeOn_of_model σ hQc hTc hEc hImgc εc hs₀ hr₀ hθ₀ hj hB)
    (fun y hy => omegaBCoset_of_model hQc hTc hEc εc hs₀ hr₀ hθ₀ y hy) j' hj'1 g hg
    ⟨1, sw, hsw, by rw [lagRank_sub_one_eq_finrank_commSpace, hj'], by
      rw [inv_one, one_mul, mul_one]; exact hθsw⟩

end Main

theorem spTwoOmegaBClassAtInput_of_derived {κ : Sp2mKind} (hκ : κ = .omegaPlus ∨ κ = .omegaMinus)
    {n : ℕ} (hn : 3 ≤ n) (htor : ∀ j : ℕ, 1 ≤ j → 2 * j < n + 1 → SpTwoAToralAt (n + 1) j)
    (hclos : ∀ j : ℕ, 2 * j = n + 1 → SpTwoLagDerivedClosureAt (n + 1) j) :
    SpTwoOmegaBClassAtInput κ n := by
  intro G _ _ L hset K _ _ _ hK e t ht hKt hroot hglob g hg K' _ _ Q hK' hQ hT _ ε β s hs _ h3
  exact ne_of_bClassAt_two_derived htor hset hK hn e ht hKt hκ hglob
    (fun g' hg' => not_mem_range_conj_omega_two_of_three_le hset hK hn e ht hKt hκ hroot hglob hg')
    hclos hg hK' hQ hT ε β hs h3

theorem spTwoOmegaBClassAtInput_three_of_derived {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (hclos : SpTwoLagDerivedClosureAt 4 2) :
    SpTwoOmegaBClassAtInput κ 3 :=
  spTwoOmegaBClassAtInput_of_derived hκ le_rfl
    (fun j hj hjN => spTwoAToralAt_holds_of_four_le 4 j le_rfl hj hjN) (fun j hj => by
      obtain rfl : j = 2 := by omega
      exact hclos)

theorem spTwoOmegaBClassInput_of_lagClosure {κ : Sp2mKind} (hκ : κ = .omegaPlus ∨ κ = .omegaMinus)
    (hMC : SpTwoLagClosureInput) : SpTwoOmegaBClassInput κ := by
  intro G _ _ L hset n K _ _ _ hK hn
  exact spTwoOmegaBClassAtInput_of_derived hκ (by omega)
    (fun j hj hjN => spTwoAToralAt_holds_of_four_le (n + 1) j (by omega) hj hjN)
    (fun j hj => spTwoLagDerivedClosureAt_of_closure hMC (by omega) hj) G L hset K hK

end CFSG.SeitzReduction.SymplecticPilot
