module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderInputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderBridge
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderSp4Trans
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderCommQuasi
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2OneFactor
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2Offender
public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.RankThree.FFModules Matrix
open scoped IsMulCommutative

theorem k54NatQuotSp4_proof : K54NatQuotSp4 := by
  classical
  intro G _ _ V _ _ _ ρ hfaith L F _ _ n hn hF he A hAN hbest hnot
  obtain ⟨e⟩ := he
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  have : CharP F 2 := hchar
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hqS : CFSG.IsQuasisimple ↥(StatedSp 2 F) :=
    CFSG.RankThree.GF2n.Stroth80.statedSp_quasisimple_of_card 2 F (by norm_num) h4
  have hqL : CFSG.IsQuasisimple ↥L := CFSG.IsQuasisimple.of_mulEquiv e hqS
  have hq : CFSG.Open.IsQuasisimple ↥L := ⟨hqL.1.commutator_eq_top, hqL.2.1⟩
  have hntL : Nontrivial ↥L := by
    have : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hq.2.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥L ⧸ Subgroup.center ↥L)
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) x
    exact ⟨y, 1, fun h => hx (by rw [← hy, h, map_one])⟩
  have hLA : ⁅L, A⁆ = L := commutator_eq_of_isQuasisimple_of_not_le hq hAN hnot
  have hKnt : ¬ L ≤ cenOn ρ L ⊤ := by
    intro h
    have hbot : L = ⊥ := by
      rw [eq_bot_iff]
      intro l hl
      rw [Subgroup.mem_bot]
      apply hfaith
      ext v
      rw [map_one, Module.End.one_apply]
      exact (h hl).2 v Submodule.mem_top
    exact (Subgroup.nontrivial_iff_ne_bot L).mp hntL hbot
  have hA2 : CFSG.IsElementaryAbelian 2 A := by
    refine (isElemAbelianOn_top_iff (ρ := ρ) (A := A) ?_).mpr hbest.1
    intro a ha hfix
    apply hfaith
    ext v
    rw [map_one, Module.End.one_apply]
    exact hfix v
  obtain ⟨B, hBA, hUinv, hLU, hBU, hbestB, hquad, hmove, -⟩ :=
    exists_strictMin_moving (ρ := ρ) L A hA2 hAN hLA hKnt hbest
  have hBNsub : B ≤ Subgroup.normalizer (L : Set G) := hBA.trans hAN
  have hBNmem : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L := fun b hb l hl =>
    (Subgroup.mem_normalizer_iff.mp (hBNsub hb) l).mp hl
  have hB2 : ∀ b ∈ B, b * b = 1 := by
    intro b hb
    have h : b ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := A) b (hBA hb)
    simpa [pow_two] using h
  have hAc : ∀ a ∈ A, ∀ c ∈ A, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥A) ⟨c, hc⟩)
  have hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b := fun a ha c hc => hAc a (hBA ha) c (hBA hc)
  have hinner : ∀ b ∈ B, ∃ l ∈ L, ConjAgree L b l :=
    strictMin_inner_sp4 ρ L B hn hF e hq hBNmem hB2 hBc hUinv hLU hbestB hquad hmove
  obtain ⟨r, Vs, i₀, α, φ, hVs, htriv, hnat⟩ :=
    exists_series_natural_factor_sp4 ρ L B hn hF e hq.1 hq.2 hB2 hBc hinner
      (U := commOn ρ L ⊤) le_rfl hUinv hbestB hmove hBU
  obtain ⟨Mat, P, hMatinj, hrange, hP⟩ := exists_mat_antiSp_of_natural (G := G) (L := L) e α
  let φ' : ((Vs i₀.succ).toSubmodule ⧸ factorSub (Vs i₀.castSucc) (Vs i₀.succ)) ≃+ (Fin 4 → F) :=
    φ.trans P
  have hφ' : ∀ (l : ↥L)
      (x : (Vs i₀.succ).toSubmodule ⧸ factorSub (Vs i₀.castSucc) (Vs i₀.succ)),
      φ' (factorRep (Vs i₀.castSucc) (Vs i₀.succ) l x) =
        (Mat l : Matrix (Fin 4) (Fin 4) F) *ᵥ φ' x := by
    intro l x
    have h1 := hnat (e l) x
    rw [MulEquiv.symm_apply_apply] at h1
    change P (φ (factorRep (Vs i₀.castSucc) (Vs i₀.succ) l x)) =
      (Mat l : Matrix (Fin 4) (Fin 4) F) *ᵥ P (φ x)
    rw [h1, hP l (φ x)]
  obtain ⟨N, hNMat, hNI, hNIcomm⟩ :=
    NatQuot.exists_of_series_natural_factor ρ L hq.1 Mat hMatinj Vs hVs i₀ htriv φ' hφ'
  refine ⟨N, ?_, hNIcomm, ?_⟩
  · rw [hNMat, hrange]
  · intro a ha v hv
    rw [hNI] at hv ⊢
    exact isInvariant_commOn_top (ρ := ρ) hAN a ha v hv

end CFSG.LocalAnalysis.RankThreeUC.S15

end
