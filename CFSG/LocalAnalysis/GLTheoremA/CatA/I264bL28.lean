module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bArith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bLoc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bSL2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bFacts
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.GH74.KGroups.L28
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Adapters.LinearCatalogStated
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped MatrixGroups


theorem statedClassicalModel_of_fL28 {S : Type} [Group S] (h : catalogIs S fL28) :
    StatedClassicalModel S .PSL 2 2 3 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | A r q =>
      rcases r with _ | _ | r
      · exact hi.elim
      · have hq : q.card = 8 := hi
        obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 3) (by norm_num)
          (hq.trans (by norm_num))
        have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
        rw [h1, h2] at hm
        exact hm
      · exact hi.elim
    | _ => exact hi.elim

theorem rankBound_l28_three {S : Type} [Group S] [Finite S] (h : catalogIs S fL28) :
    ∀ E T : Subgroup S, IsElemAbelian 3 E → IsPGroup 2 T → T ≠ ⊥ →
      E ≤ Subgroup.normalizer (T : Set S) → Nat.card E ≤ 1 := by
  intro E T hE hT2 hT hET
  have hm := statedClassicalModel_of_fL28 h
  obtain ⟨⟨-, hf1, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf1 hK
  let φ : SL(2, K) ≃* S := (e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
    ((LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K).trans
      (LinearCover.projectiveSLTwoEquivSL K)))).symm
  have h7 : ¬ 3 ∣ Nat.card K - 1 := by
    rw [hK]
    norm_num
  have hall : ∀ g ∈ E, g = 1 := by
    intro g hg
    have hg3 : (φ.symm g) ^ 3 = 1 := by rw [← map_pow, hE.2 g hg, map_one]
    have hN : φ.symm g ∈ Subgroup.normalizer ((T.map φ.symm.toMonoidHom : Subgroup SL(2, K)) : Set SL(2, K)) :=
      Subgroup.le_normalizer_map φ.symm.toMonoidHom ⟨g, hET hg, rfl⟩
    have := eq_one_of_order_three_normalizes_two (F := K) h7 (hT2.map φ.symm.toMonoidHom)
      (fun hbot => hT ((Subgroup.map_eq_bot_iff_of_injective T φ.symm.injective).1 hbot)) hg3 hN
    simpa using this
  have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hall
  rw [this, Subgroup.card_bot]

theorem card_mulAut_fL28 {S : Type} [Group S] (h : catalogIs S fL28) : Nat.card (MulAut S) = 1512 :=
  CFSG.GH74.KGroups.L28.card_mulAut (Or.inl ⟨by decide, statedClassicalModel_of_fL28 h⟩)

theorem kDescFam_l28 (p : ℕ) : KDescFam p fL28 := by
  intro hp hp2 Y _ _ K B h hc hcB
  have hm := statedClassicalModel_of_fL28 hc
  have hcard : Nat.card (↥K ⧸ Subgroup.center ↥K) = 504 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_eight hm
  have hAut := card_mulAut_fL28 hc
  by_cases hp3 : p = 3
  · subst hp3
    haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := h.qs.2
    have hZ : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ :=
      center_eq_bot_of_simple_nonprime hcard (by norm_num)
    have hOutc : Nat.card (Outer (↥K ⧸ Subgroup.center ↥K)) = 3 := by
      have := card_mulAut_eq_mul_outer hcard (by norm_num)
      rw [hAut] at this
      omega
    refine (false_of_rank_bound' (m := 3) (r := 1) hp hp2 h hcB (MulEquiv.refl _) hZ
      (fun P _ => ?_) (rankBound_l28_three hc) (by norm_num)).elim
    have := card_le_mul_card_inf_inner P
    rwa [hOutc] at this
  · refine (false_of_not_sq_dvd hp h hcB (MulEquiv.refl _) fun hdvd => ?_).elim
    rw [hAut] at hdvd
    exact not_sq_dvd_of_dvd_smooth_mul (a := 3) (b := 3) (M := 7) hp hp2 hp3
      (by norm_num : Nat.Prime 7).squarefree (by norm_num) hdvd

end CFSG.LocalAnalysis.GLTheoremA
