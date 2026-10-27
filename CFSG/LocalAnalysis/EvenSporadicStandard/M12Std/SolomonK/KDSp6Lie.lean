module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.BasicSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.KDSp6Expo
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrder
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.CatLeaf

variable {K : Type} [Group K] [Finite K]

theorem no_order_eight (hP : P12Facts) (hK : SolomonA12HypK K) {m : ℕ} {F : Type}
    [Field F] [Finite F] [CharP F 2] (hm : m ≤ 4) {H : Subgroup (GL (Fin m) F)}
    (e : K ≃* StatedProj H) : False := by
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := K)
  obtain ⟨-, ⟨g, -, hg⟩, -⟩ := elemFactsIn_sylow hP hK S
  have horder : orderOf (e g) = 8 := by rw [MulEquiv.orderOf_eq, hg]
  exact orderOf_ne_eight_proj (by simpa using hm) H (e g) horder

theorem no_order_eight_PSL (hP : P12Facts) (hK : SolomonA12HypK K) {n f : ℕ}
    (h : StatedClassicalModel K .PSL n 2 f) (hf : 1 ≤ f) (hn : n ≤ 4) : False := by
  obtain ⟨-, F, hField, hFinite, hcard, ⟨e⟩⟩ := h
  letI := hField
  letI := hFinite
  haveI : CharP F 2 := charP_two_of_card hf hcard
  exact no_order_eight hP hK hn e

theorem no_order_eight_PSU (hP : P12Facts) (hK : SolomonA12HypK K) {n f : ℕ}
    (h : StatedClassicalModel K .PSU n 2 f) (hf : 1 ≤ f) (hn : n ≤ 4) : False := by
  obtain ⟨-, F, hField, hFinite, hcard, ⟨e⟩⟩ := h
  letI := hField
  letI := hFinite
  have hcard' : Nat.card F = 2 ^ (2 * f) := by
    rw [hcard, ← pow_mul]
    congr 1
    omega
  haveI : CharP F 2 := charP_two_of_card (by omega : 1 ≤ 2 * f) hcard'
  exact no_order_eight hP hK hn e

theorem lieModel_psp_of_even (hO : LieOrderFormulasInput) (hP : P12Facts)
    (hK : SolomonA12HypK K) {t : StatedLieTag} {n f : ℕ} (hL : LieModel K t n 2 f) :
    LieModel K .PSp 3 2 1 := by
  have hadm : StatedLieAdmissible t n 2 f := hL.admissible
  obtain ⟨-, -, hfac⟩ := hO K t n 2 f hadm hL
  have hN : lieSylowExponent t n * f = 9 := by
    rw [two_part_card hP hK] at hfac
    exact hfac.symm
  have hb : lieSylowExponent t n * f ≤ 10 := by omega
  rcases lie_casework hadm hb with
    ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn0, hf1, hf2⟩
  · rcases ht with rfl | rfl
    ·
      simp only [lieSylowExponent] at hN
      interval_cases n <;> norm_num at hN
      all_goals
        exfalso
        have hS := hL.statedClassicalModel (by decide : .PSL ∈ classicalTags)
        first
          | exact no_order_eight_PSL hP hK hS hf1 (by omega)
          | omega
    ·
      simp only [lieSylowExponent] at hN
      interval_cases n <;> norm_num at hN
      all_goals
        exfalso
        have hS := hL.statedClassicalModel (by decide : .PSU ∈ classicalTags)
        first
          | exact no_order_eight_PSU hP hK hS hf1 (by omega)
          | omega
  · rcases ht with rfl | rfl
    ·
      simp only [lieSylowExponent] at hN
      interval_cases n <;> norm_num at hN
      · exfalso
        omega
      · have hf : f = 1 := by omega
        subst f
        exact hL
    ·
      exfalso
      exact hadm.2.2.2 rfl
  ·
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
    cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6
    all_goals
      exfalso
      simp only [lieSylowExponent] at hN
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact absurd hadm.2.2.2.1 (by decide)
    · omega
    · omega

end CFSG.EvenSporadicStandard.M12Std.SolomonK
