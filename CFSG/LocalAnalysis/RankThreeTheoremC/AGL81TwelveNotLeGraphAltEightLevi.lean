module

import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.SymplecticTwo
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinCuts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.AltEight

open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Subgroup

theorem linBlockSL_eq_top_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2) {n : ℕ}
    (I : Set ℕ) (a : Fin n) : linBlockSL K n I a = ⊤ := by
  have hunit : ∀ c : Kˣ, c = 1 := by
    have h1 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
    have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp h1).1
    exact fun c => Subsingleton.elim c 1
  rw [linBlockSL, Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
  exact (Subgroup.eq_top_iff' _).mpr fun g => MonoidHom.mem_ker.mpr (hunit _)

theorem range_linLeviHom_eq_top_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2) {n : ℕ}
    (I : Set ℕ) : (linLeviHom K n I).range = ⊤ := by
  refine top_le_iff.mp ?_
  have h : Subgroup.pi Set.univ (linBlockSL K n I) = ⊤ := by
    rw [show linBlockSL K n I = fun _ => ⊤ from funext (linBlockSL_eq_top_of_card_two hK I),
      Subgroup.pi_top]
  rw [← h]
  exact pi_le_range_linLeviHom

theorem sum_linBlockLen_le (n : ℕ) (I : Set ℕ) : ∑ a : Fin n, linBlockLen n I a ≤ n := by
  classical
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin n)), ∀ b ∈ (Finset.univ : Finset (Fin n)),
      a ≠ b → Disjoint (Finset.Ico (a : ℕ) (a + linBlockLen n I a))
        (Finset.Ico (b : ℕ) (b + linBlockLen n I b)) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro r hra hrb
    rw [Finset.mem_Ico] at hra hrb
    exact linBlock_disjoint hab hra.1 hra.2 hrb.1 hrb.2
  calc ∑ a : Fin n, linBlockLen n I a
      = ∑ a : Fin n, (Finset.Ico (a : ℕ) (a + linBlockLen n I a)).card := by simp
    _ = (Finset.univ.biUnion fun a : Fin n =>
          Finset.Ico (a : ℕ) (a + linBlockLen n I a)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.range n).card := by
        refine Finset.card_le_card fun r hr => ?_
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_Ico] at hr
        obtain ⟨a, -, h2⟩ := hr
        have := linBlockLen_le (I := I) a
        simp only [Finset.mem_range]
        omega
    _ = n := Finset.card_range n

theorem pCore_gl_eq_bot_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (m : ℕ) : CFSG.pCore 2 (GL (Fin m) K) = ⊥ :=
  ParabCensus.pCore_two_eq_bot_of_mulEquiv (CFSG.GH74.Exceptional.glEquivZModTwoOfCardTwo hK m)
    (ParabCensus.pCore_two_gl_zmod_two_eq_bot m)

theorem pCore_flagStabilizer_eq_ker_linLeviHom {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {n : ℕ} (hn : 1 ≤ n) (I : Set ℕ) :
    CFSG.pCore 2 ↥(flagStabilizer n K I) = (linLeviHom K n I).ker := by
  refine le_antisymm ?_ (le_sSup ⟨inferInstance, isPGroup_ker_linLeviHom hn⟩)
  intro z hz
  rw [MonoidHom.mem_ker]
  funext j
  let ψ : ↥(flagStabilizer n K I) →* GL (Fin (linBlockLen n I j)) K :=
    (Pi.evalMonoidHom (fun a : Fin n => GL (Fin (linBlockLen n I a)) K) j).comp
      (linLeviHom K n I)
  have hψs : Function.Surjective ψ := by
    intro y
    have hy : Pi.mulSingle j y ∈ (linLeviHom K n I).range := by
      rw [range_linLeviHom_eq_top_of_card_two hK I]
      exact Subgroup.mem_top _
    obtain ⟨q, hq⟩ := hy
    exact ⟨q, by simp [ψ, hq]⟩
  have hnorm : ((CFSG.pCore 2 ↥(flagStabilizer n K I)).map ψ).Normal :=
    (inferInstance : (CFSG.pCore 2 ↥(flagStabilizer n K I)).Normal).map ψ hψs
  have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥(flagStabilizer n K I)).map ψ) :=
    IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥(flagStabilizer n K I))) ψ
  have hle : (CFSG.pCore 2 ↥(flagStabilizer n K I)).map ψ ≤
      CFSG.pCore 2 (GL (Fin (linBlockLen n I j)) K) := le_sSup ⟨hnorm, h2⟩
  rw [pCore_gl_eq_bot_of_card_two hK] at hle
  have hz' : ψ z ∈ (CFSG.pCore 2 ↥(flagStabilizer n K I)).map ψ := ⟨z, hz, rfl⟩
  rw [le_bot_iff.mp hle, Subgroup.mem_bot] at hz'
  exact hz'

theorem nonempty_quotient_pCore_flagStabilizer_linLevi {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2) {n : ℕ} (hn : 1 ≤ n) (I : Set ℕ) :
    Nonempty (↥(flagStabilizer n K I) ⧸ CFSG.pCore 2 ↥(flagStabilizer n K I) ≃*
      ∀ a : Fin n, GL (Fin (linBlockLen n I a)) K) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (pCore_flagStabilizer_eq_ker_linLeviHom hK hn I)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (MonoidHom.range_eq_top.mp (range_linLeviHom_eq_top_of_card_two hK I)))⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.AltEight
