module

public import CFSG.ClassicalInvolution.Q3.Q3TY34

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (toralNormal_plus_of_normalized_subgroups)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

section Frame

set_option maxHeartbeats 400000 in
theorem toralNormal_of_frame_chain3 {s : ℕ} (hs : 1 ≤ s) {X : Type}
    [Group X] (θ : spinGroup (quadPlus (s + 4) (GaloisField 3 1)) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus (s + 4) (GaloisField 3 1))))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    (x : spinGroup (quadPlus (s + 4) (GaloisField 3 1))) (t : Bool)
    {R : ℕ → Subgroup (spinGroup (quadPlus (s + 4) (GaloisField 3 1)))}
    {Rtw RM : Subgroup (spinGroup (quadPlus (s + 4) (GaloisField 3 1)))}
    (hR : ∀ a (ha : a ≤ s), R a = ((rootSL2 (plusFrame (s + 4) (GaloisField 3 1) (by omega)) a
      (a + 1) (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom))
    (hRtw : Rtw = ((rootSL2 (plusFrame (s + 4) (GaloisField 3 1) (by omega)) s (s + 1) (by omega)
      (by omega) (by omega) true true).map (MulAut.conj x).toMonoidHom))
    (hRM : RM = ((rootSL2 (plusFrame (s + 4) (GaloisField 3 1) (by omega)) (s + 2) (s + 3)
      (by omega) (by omega) (by omega) true t).map (MulAut.conj x).toMonoidHom))
    (hfix : ∀ a, 1 ≤ a → a ≤ s → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ∃ (k₀ : spinGroup (quadPlus (s + 4) (GaloisField 3 1))) (v : Fin (s + 4) → ZMod 2),
      ∀ γ : Fin (s + 4) → ℤ, γ ∈ (plusDatum (s + 4) (GaloisField 3 1) (by omega)).roots →
        ((((plusDatum (s + 4) (GaloisField 3 1) (by omega)).rootGroup γ ⊔
              (plusDatum (s + 4) (GaloisField 3 1) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((plusDatum (s + 4) (GaloisField 3 1) (by omega)).rootGroup γ ⊔
              (plusDatum (s + 4) (GaloisField 3 1) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((plusDatum (s + 4) (GaloisField 3 1) (by omega)).rootGroup γ ⊔
              (plusDatum (s + 4) (GaloisField 3 1) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔
          ∑ i, (γ i : ZMod 2) * v i = 0) := by
  classical
  have hm3 : 3 ≤ s + 4 := by omega
  have hK : Nat.card (GaloisField 3 1) = 3 ^ 1 := by
    rw [card_gf3]
    norm_num
  set F₀ := plusFrame (s + 4) (GaloisField 3 1) hm3 with hF₀
  let i₀ : Fin (s + 4) := ⟨s + 2, by omega⟩
  let i₁ : Fin (s + 4) := ⟨s + 3, by omega⟩
  let c₀ : Fin (s + 4) := ⟨0, by omega⟩
  let jj : Fin (s + 4) := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := fun h => by have := congrArg Fin.val h; simp [i₀, i₁] at this
  have hc0 : c₀ ≠ i₀ := fun h => by have := congrArg Fin.val h; simp [i₀, c₀] at this
  have hc1 : c₀ ≠ i₁ := fun h => by have := congrArg Fin.val h; simp [i₁, c₀] at this
  have hj0 : jj ≠ i₀ := fun h => by have := congrArg Fin.val h; simp [i₀, jj] at this
  have hj1 : jj ≠ i₁ := fun h => by have := congrArg Fin.val h; simp [i₁, jj] at this
  have hjc : c₀ ≠ jj := fun h => by have := congrArg Fin.val h; simp [c₀, jj] at this
  obtain ⟨γ₀, -, hγ₀⟩ := exists_mem_rootsD_toStdD_eq (s + 4) h01
    (boolSign_eq_one_or_eq_neg_one true) (boolSign_eq_one_or_eq_neg_one t)
  obtain ⟨γ₁, -, hγ₁⟩ := exists_mem_rootsD_toStdD_eq (s + 4) hjc.symm.symm
    (boolSign_eq_one_or_eq_neg_one false) (boolSign_eq_one_or_eq_neg_one true)
  let Fix : Subgroup (spinGroup (quadPlus (s + 4) (GaloisField 3 1))) :=
    MonoidHom.eqLocus (σ.toMonoidHom.comp (θ.comp (MulAut.conj x).toMonoidHom))
      (θ.comp (MulAut.conj x).toMonoidHom)
  have hFix : ∀ g, g ∈ Fix ↔ σ (θ (x * g * x⁻¹)) = θ (x * g * x⁻¹) := fun g => Iff.rfl
  have H1 : ∀ y ∈ (((plusDatum (s + 4) (GaloisField 3 1) hm3).rootGroup γ₀ ⊔
      (plusDatum (s + 4) (GaloisField 3 1) hm3).rootGroup (-γ₀)).map
        (MulAut.conj x).toMonoidHom), σ (θ y) = θ y := by
    rw [rootGroup_sup_eq_longSL2_range hm3 h01 true t hγ₀]
    intro y hy
    exact hfixM y (by rw [hRM]; exact hy)
  have hFixR : ∀ a (ha1 : 1 ≤ a) (ha2 : a ≤ s) (g : spinGroup (quadPlus (s + 4) (GaloisField 3 1))),
      g ∈ rootSL2 F₀ a (a + 1) (by omega) (by omega) (by omega) true false → g ∈ Fix := by
    intro a ha1 ha2 g hg
    rw [hFix]
    exact hfix a ha1 ha2 _ (by rw [hR a ha2]; exact ⟨g, hg, rfl⟩)
  have hFixT : ∀ g : spinGroup (quadPlus (s + 4) (GaloisField 3 1)),
      g ∈ rootSL2 F₀ s (s + 1) (by omega) (by omega) (by omega) true true → g ∈ Fix := by
    intro g hg
    rw [hFix]
    exact hfixtw _ (by rw [hRtw]; exact ⟨g, hg, rfl⟩)
  have hA : ∀ a, 1 ≤ a → a < s + 1 →
      RootInN F₀ Fix a (a + 1) true false ∧ RootInN F₀ Fix (a + 1) a true false := by
    intro a ha1 ha2
    constructor
    · refine ⟨by omega, by omega, by omega, fun c => ?_⟩
      apply hFixR a ha1 (by omega)
      exact ⟨upperSL2 c, HypFrame.longSL2_upperSL2 F₀ _ true false c⟩
    · refine ⟨by omega, by omega, by omega, fun c => ?_⟩
      apply hFixR a ha1 (by omega)
      exact ⟨lowerSL2 c, HypFrame.longSL2_lowerSL2 F₀ _ true false c⟩
  have hT : RootInN F₀ Fix (s + 1 - 1) (s + 1) true true ∧
      RootInN F₀ Fix (s + 1) (s + 1 - 1) false false := by
    have e : s + 1 - 1 = s := by omega
    rw [e]
    constructor
    · refine ⟨by omega, by omega, by omega, fun c => ?_⟩
      apply hFixT
      exact ⟨upperSL2 c, HypFrame.longSL2_upperSL2 F₀ _ true true c⟩
    · refine ⟨by omega, by omega, by omega, fun c => ?_⟩
      apply hFixT
      exact ⟨lowerSL2 c, HypFrame.longSL2_lowerSL2 F₀ _ true true c⟩
  have hall := rootInN_of_chain (F := F₀) (Fix := Fix) (n := s + 1) (by omega) hA hT
  have H2 : ∀ (a b : Fin (s + 4)), a ≠ b → a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → b ≠ i₀ → b ≠ i₁ →
      b ≠ c₀ → ∀ (s' t' : Bool) {γ : Fin (s + 4) → ℤ},
        toStdD (s + 4) γ = Pi.single a (boolSign s') + Pi.single b (boolSign t') →
          ∀ y ∈ ((plusDatum (s + 4) (GaloisField 3 1) hm3).rootGroup γ).map
            (MulAut.conj x).toMonoidHom, σ (θ y) = θ y := by
    intro a b hab ha0 ha1 hac hb0 hb1 hbc s' t' γ hγ y hy
    have hav : 1 ≤ a.val ∧ a.val ≤ s + 1 := by
      have h1 : a.val ≠ s + 2 := fun h => ha0 (Fin.ext h)
      have h2' : a.val ≠ s + 3 := fun h => ha1 (Fin.ext h)
      have h3 : a.val ≠ 0 := fun h => hac (Fin.ext h)
      have := a.isLt
      omega
    have hbv : 1 ≤ b.val ∧ b.val ≤ s + 1 := by
      have h1 : b.val ≠ s + 2 := fun h => hb0 (Fin.ext h)
      have h2' : b.val ≠ s + 3 := fun h => hb1 (Fin.ext h)
      have h3 : b.val ≠ 0 := fun h => hbc (Fin.ext h)
      have := b.isLt
      omega
    have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    obtain ⟨_, _, _, hroot⟩ := hall a.val b.val s' t' hav.1 hav.2 hbv.1 hbv.2 hab'
    have hXγ : (plusDatum (s + 4) (GaloisField 3 1) hm3).rootGroup γ =
        (F₀.longRoot hab s' t').range := plusRootGroup_eq hm3 hab s' t' hγ
    rw [hXγ] at hy
    obtain ⟨g, ⟨c, rfl⟩, rfl⟩ := hy
    exact (hFix _).mp (hroot (Multiplicative.toAdd c))
  have hscal : ∀ z ∈ Subgroup.center (spinGroup (quadPlus (s + 4) (GaloisField 3 1))),
      ∃ η : GaloisField 3 1, ∀ v, spinAction (quadPlus (s + 4) (GaloisField 3 1)) z v = η • v := by
    intro z hz
    obtain ⟨c, hc⟩ := mem_scalars.mp (spinAction_center_mem_scalars hm3 hz)
    exact ⟨c, hc⟩
  let k2 : Fin (s + 4) := ⟨2, by omega⟩
  have hjk : jj ≠ k2 := fun h => by have := congrArg Fin.val h; simp [jj, k2] at this
  have hik : c₀ ≠ k2 := fun h => by have := congrArg Fin.val h; simp [c₀, k2] at this
  have H3 : ∀ y ∈ ((plusDatum (s + 4) (GaloisField 3 1) hm3).rootGroup γ₁).map
      (MulAut.conj x).toMonoidHom, σ (θ y) ∈ (((plusDatum (s + 4) (GaloisField 3 1) hm3).rootGroup
        γ₁).map (MulAut.conj x).toMonoidHom).map θ := by
    have hXγ₁ : (plusDatum (s + 4) (GaloisField 3 1) hm3).rootGroup γ₁ =
        (F₀.longRoot hjc false true).range := plusRootGroup_eq hm3 hjc false true hγ₁
    rw [hXγ₁]
    rintro y ⟨u, ⟨c, rfl⟩, rfl⟩
    set c0 : GaloisField 3 1 := Multiplicative.toAdd c with hc0
    have hcc : c = Multiplicative.ofAdd c0 := rfl
    rw [hcc]
    have hswap := HypFrame.longRoot_swap F₀ hjc false true c0
    have hu : F₀.longRoot hjc false true (.ofAdd c0) ∈ rootSL2 F₀ 0 1 (by omega) (by omega)
        (by omega) true false := by
      refine ⟨lowerSL2 (-c0), ?_⟩
      rw [HypFrame.longSL2_lowerSL2]
      exact hswap.symm
    have hy0 : (MulAut.conj x).toMonoidHom (F₀.longRoot hjc false true (.ofAdd c0)) ∈ R 0 := by
      rw [hR 0 (by omega)]
      exact ⟨_, hu, rfl⟩
    obtain ⟨y', hy'R, hy'θ⟩ := hnorm0 _ hy0
    rw [hR 0 (by omega)] at hy'R
    obtain ⟨g, hg, rfl⟩ := hy'R
    have hc : ∀ c' : GaloisField 3 1, ⁅g, F₀.longRoot hjk true false (.ofAdd c')⁆ ∈
        Subgroup.center (spinGroup (quadPlus (s + 4) (GaloisField 3 1))) := by
      intro c'
      set w := F₀.longRoot hjk true false (.ofAdd c') with hw
      have hwR : (MulAut.conj x).toMonoidHom w ∈ R 1 := by
        rw [hR 1 hs]
        refine ⟨w, ⟨upperSL2 c', ?_⟩, rfl⟩
        exact HypFrame.longSL2_upperSL2 F₀ _ true false c'
      have hfw := hfix 1 le_rfl hs _ hwR
      have hcomm : Commute (F₀.longRoot hjc false true (.ofAdd c0)) w := by
        rw [hswap]
        exact HypFrame.commute_longRoot_longRoot_left F₀ (i := jj) (j := c₀) (l := k2) hjc.symm
          hjk true false false (-c0) c'
      have hcomm' := hcomm.map (MulAut.conj x).toMonoidHom
      exact commutator_central_of_conj x g w
        (commutator_central_of_stable θ hker σ hy'θ hfw hcomm'.eq)
    obtain ⟨c', hgc⟩ := mem_lowerRoot_of_comm_central F₀ hscal hjc hjk hik hg hc
    have hgU : g ∈ (F₀.longRoot hjc false true).range :=
      ⟨Multiplicative.ofAdd (-c'), (HypFrame.longRoot_swap F₀ hjc false true (-c')).trans
        (by rw [neg_neg]; exact hgc.symm)⟩
    rw [← hy'θ]
    exact ⟨_, ⟨g, hgU, rfl⟩, rfl⟩
  exact toralNormal_plus_of_normalized_subgroups (p := 3) (f := 1) (by norm_num) le_rfl hK
    (m := s + 4) (by omega) hm3 θ hker σ hσ2 hσr h01 hc0 hc1 hj0 hj1 hjc hγ₀ hγ₁ x H1 H2 H3

end Frame


section Long

theorem toralNormal_of_chain_long3 {u : ℕ} {X : Type} [Group X]
    (θ : spinGroup (quadPlus (u + 3 + 4) (GaloisField 3 1)) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus (u + 3 + 4) (GaloisField 3 1))))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {R : ℕ → Subgroup (spinGroup (quadPlus (u + 3 + 4) (GaloisField 3 1)))}
    {Rtw RM : Subgroup (spinGroup (quadPlus (u + 3 + 4) (GaloisField 3 1)))}
    (hRf : ∀ a ≤ u + 3, R a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (u + 3 + 4) (GaloisField 3 1) (by omega)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (u + 3 + 4) (GaloisField 3 1) (by omega)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (u + 3 + 4) (GaloisField 3 1) (by omega)))
    (hadj : ∀ a < u + 3, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < u + 3, ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ u + 3 → Commutes (R a) (R b))
    (hM : ∀ a ≤ u + 3, Commutes RM (R a))
    (hadjtw : ModelAdj (Subgroup.center _) (R (u + 2)) Rtw)
    (hcommtw : ∀ a, a ≤ u + 1 → Commutes (R a) Rtw) (hcommtw' : Commutes (R (u + 3)) Rtw)
    (hne : Rtw ≠ R (u + 3))
    (hfix : ∀ a, 1 ≤ a → a ≤ u + 3 → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ∃ (k₀ : spinGroup (quadPlus (u + 3 + 4) (GaloisField 3 1))) (v : Fin (u + 3 + 4) → ZMod 2),
      ∀ γ : Fin (u + 3 + 4) → ℤ,
        γ ∈ (plusDatum (u + 3 + 4) (GaloisField 3 1) (by omega)).roots →
        ((((plusDatum (u + 3 + 4) (GaloisField 3 1) (by omega)).rootGroup γ ⊔
              (plusDatum (u + 3 + 4) (GaloisField 3 1) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((plusDatum (u + 3 + 4) (GaloisField 3 1) (by omega)).rootGroup γ ⊔
              (plusDatum (u + 3 + 4) (GaloisField 3 1) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((plusDatum (u + 3 + 4) (GaloisField 3 1) (by omega)).rootGroup γ ⊔
              (plusDatum (u + 3 + 4) (GaloisField 3 1) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔
          ∑ i, (γ i : ZMod 2) * v i = 0) := by
  have hm3 : 3 ≤ u + 3 + 4 := by omega
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero two_ne_zero_gf3
  have hQ : (quadPlus (u + 3 + 4) (GaloisField 3 1)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadPlus (u + 3 + 4) (GaloisField 3 1))
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1)
      (Fin (u + 3 + 4) ⊕ Fin (u + 3 + 4) → GaloisField 3 1) := by
    rw [finrank_plus]
    omega
  have cq := centralQuot3_plus (m := u + 3 + 4) (by omega)
  obtain ⟨hdist, htwin⟩ := chain_distinct_twin_gen3 (u := u) hdim cq hRf hRtwf hadj hcomm hadjtw
    hcommtw hcommtw'
  obtain ⟨x, hxR, hxtw, t, hxM⟩ := spin_chain_recognition_gen3 hQ (s := u + 3) (by omega)
    (plusFrame (u + 3 + 4) (GaloisField 3 1) hm3) hdim cq hRf hRtwf hRMf hadj hlin hcomm hM hdist
    hne htwin
  exact toralNormal_of_frame_chain3 (s := u + 3) (by omega) θ hker σ hσ2 hσr x t hxR hxtw hxM
    hfix hfixtw hfixM hnorm0

end Long

end CFSG.ClassicalInvolution.Q3.Q3TD
