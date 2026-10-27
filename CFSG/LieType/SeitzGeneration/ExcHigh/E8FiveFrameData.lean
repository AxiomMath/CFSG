module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveFrameElt
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSplitFrame
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveTwistedFrame
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.LangLeviAux

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.SeitzReduction CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcHighThree

set_option linter.unusedSectionVars false

section LangClosure


theorem exists_langLevi_algebraicClosure (τ : Tag) (K : Type) [Field K] [Finite K]
    (w : WeylGroup τ) (hw : w • highRoot τ = highRoot τ) :
    ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
      ∃ g : ModGL τ (AlgebraicClosure K), g ∈ Lθ τ (AlgebraicClosure K) ∧
        Units.map (entrywiseHom Fr) g =
          g * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w := by
  classical
  obtain ⟨p, hpK⟩ := CharP.exists K
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpp, hcard⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hcard' : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hZ := LangLeviAux.isConnectedAlgebraicSubgroup_parabolicLevi (τ := τ)
    (k := AlgebraicClosure K) (Jθ τ)
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction p hZ (e := (n : ℕ)) n.pos 1
    (fun g hg => LangLeviAux.frobTwistGL_one_mem_parabolicLevi p (n : ℕ) (Jθ τ) hg)
  have hn : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∈ Lθ τ (AlgebraicClosure K) :=
    canonicalRep_mem_parabolicLevi (mem_parabolicWeylGroup_of_smul_highRoot τ hw)
  obtain ⟨z, hz, hzn⟩ := hlang _ hn
  refine ⟨iterateFrobenius (AlgebraicClosure K) p n, fun c => ?_, z, hz, ?_⟩
  · rw [iterateFrobenius_def, hcard']
  · have h1 : frobTwistGL τ (AlgebraicClosure K) p n 1 z =
        Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) p n)) z := by
      rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
    rw [← hzn, mul_inv_cancel_left]
    exact h1.symm

end LangClosure

section FrameData


theorem nonempty_e8FiveFrameElt_split (K : Type) [Field K] [Finite K]
    (hK : 5 ∣ Nat.card K - 1) : Nonempty (E8FiveFrameElt K) := by
  obtain ⟨ζ, hζ⟩ := e8SplitFrame K hK
  obtain ⟨-, -, X, hX⟩ := e8SplitFrame_of K hK ζ hζ
  set ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hω : orderOf (Units.map ι.toMonoidHom ζ) = 5 :=
    (orderOf_injective (Units.map ι.toMonoidHom) (Units.map_injective ι.injective) ζ).trans hζ
  refine ⟨⟨Units.map ι.toMonoidHom ζ, hω, zSplitE8 K ζ, 1, 1, 1, one_mem _, one_mem _,
    by norm_num, fun Fr _ => by simp, by simp, ?_, ⟨X, hX⟩⟩⟩
  change baseChangeGL ι (rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) ζ)) =
    1 * rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) (Units.map ι.toMonoidHom ζ)) * 1⁻¹
  rw [baseChangeGL_rootDiagUnit, inv_one, mul_one, one_mul]
  congr 1
  funext i
  by_cases hi : i = 4
  · subst hi
    simp
  · simp [Pi.mulSingle_eq_of_ne hi]

theorem e8Ten_w_theta :
    TwClass.e8Ten.w • highRoot TwClass.e8Ten.tag = highRoot TwClass.e8Ten.tag := by
  change (coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten • highRoot Tag.E8 = highRoot Tag.E8
  rw [wordProd_smul_eq_wordMat_mulVec]
  decide +kernel

theorem e8Ten_conj_rootDiagUnit {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 5) :
    canonicalRep (coxeterSystem TwClass.e8Ten.tag) L TwClass.e8Ten.w *
        rootDiagUnit TwClass.e8Ten.tag
          (Pi.mulSingle (⟨4, by decide⟩ : Fin TwClass.e8Ten.tag.rank) ζ) *
        (canonicalRep (coxeterSystem TwClass.e8Ten.tag) L TwClass.e8Ten.w)⁻¹ =
      rootDiagUnit TwClass.e8Ten.tag
          (Pi.mulSingle (⟨4, by decide⟩ : Fin TwClass.e8Ten.tag.rank) ζ) ^ 4 := by
  set i₁ : Fin TwClass.e8Ten.tag.rank := ⟨4, by decide⟩
  set a : Fin TwClass.e8Ten.tag.rank → Lˣ := Pi.mulSingle i₁ ζ with ha
  have hchar : ∀ α : Fin TwClass.e8Ten.tag.rank → ℤ, rootChar a α = ζ ^ (α i₁) := by
    intro α
    unfold rootChar
    rw [Finset.prod_eq_single i₁]
    · simp [ha]
    · intro j _ hj
      simp [ha, Pi.mulSingle_eq_of_ne hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hweyl : CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct TwClass.e8Ten.w a = a ^ 4 := by
    funext i
    unfold CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct
    rw [hchar]
    have hm := e8Ten_row i
    set m : ℤ := ((TwClass.e8Ten.w)⁻¹ • (Pi.single i 1 : Fin TwClass.e8Ten.tag.rank → ℤ)) i₁
    by_cases hi : i = i₁
    · have h2 : m % 5 = 4 := by
        rw [if_pos (show i = ⟨4, by decide⟩ from hi)] at hm
        exact hm
      rw [zpow_eq_of_emod_five hζ (show m % 5 = (4 : ℤ) % 5 by rw [h2]; norm_num)]
      simp [ha, hi]
    · have h0 : m % 5 = 0 := by
        rw [if_neg (show ¬ i = ⟨4, by decide⟩ from hi)] at hm
        exact hm
      rw [zpow_eq_of_emod_five hζ (show m % 5 = (0 : ℤ) % 5 by rw [h0]; norm_num)]
      simp [ha, Pi.mulSingle_eq_of_ne hi]
  rw [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit, hweyl]
  change rootDiagUnitHom TwClass.e8Ten.tag L (a ^ 4) = (rootDiagUnitHom TwClass.e8Ten.tag L a) ^ 4
  exact map_pow _ _ _

theorem nonempty_e8FiveFrameElt_twisted (K : Type) [Field K] [Finite K]
    (hK : 5 ∣ Nat.card K + 1) : Nonempty (E8FiveFrameElt K) := by
  have hnd : ¬ 5 ∣ Nat.card K := by omega
  obtain ⟨Fr, hFr, g, hg, hlang⟩ := exists_langLevi_algebraicClosure TwClass.e8Ten.tag K
    TwClass.e8Ten.w e8Ten_w_theta
  let D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w :=
    ⟨AlgebraicClosure K, Fr, hFr, g, hg, hlang⟩
  obtain ⟨ω, hω⟩ := exists_fifth_root_langLevi K hnd D
  obtain ⟨z, hzbc, -, -, X, hX⟩ := e8TwistedFrame_of K hK D ω hω
  refine ⟨⟨ω, hω, z, g,
    canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) TwClass.e8Ten.w, 4,
    parabolicLevi_le_adjointGroup (K := AlgebraicClosure K) (τ := TwClass.e8Ten.tag) _ hg,
    canonicalRep_mem_adjointGroup _ _ _, by norm_num,
    ?_, e8Ten_conj_rootDiagUnit hω, hzbc, ⟨X, hX⟩⟩⟩
  intro Fr' hFr'
  have hFr'' : Fr' = Fr := RingHom.ext fun c => (hFr' c).trans (hFr c).symm
  subst hFr''
  exact hlang

end FrameData

end CFSG.LieType.SeitzGeneration.ExcHigh
