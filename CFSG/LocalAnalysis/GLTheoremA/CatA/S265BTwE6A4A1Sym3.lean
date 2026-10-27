module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Plumb
import CFSG.LocalAnalysis.StandardType.GGTwE6EltSmallFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoreDefs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreKac
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqA1
import CFSG.LocalAnalysis.StandardType.GGLangRootSym3
import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147cMat
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddBSL2
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.TE6

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Seitz CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs (kac_facts
  orbit_ne_of_rank_one_quasisimple)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (exists_pair_of_rank_one)
open CFSG.StandardType.LangRat (rootSL2_WSL_mem_Γ_of_rho exists_rootSL2_sym3_mem_Γ)
open CFSG.RankThree.Chevalley (rootSL2_injective_of_field)

theorem exists_sym3_centralizing_of_dim28
    {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} (hK : Nat.card K = 4) (hσ : ∀ c, σ c = c ^ 2) {h : twistedE6InndiagGL K σ}
    (hh3 : h ^ 3 = 1) (hh1 : h ≠ 1) (hdim : twE6MatFixDim K σ h = 28)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : IsComponentOf J (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)))) :
    ∃ t ∈ fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)),
      ∃ m ∈ fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)),
        t ∈ Subgroup.centralizer (J : Set (twistedE6RootGroup K σ)) ∧
        m ∈ Subgroup.centralizer (J : Set (twistedE6RootGroup K σ)) ∧
        m ^ 3 = 1 ∧ m ≠ 1 ∧ t * m * t⁻¹ = m⁻¹ ∧
        ∃ β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β ∧
          ∃ ζ : (AlgebraicClosure K)ˣ, ζ ^ 3 = 1 ∧ ζ ≠ 1 ∧
            ∃ g ∈ adjointGroup Tag.E6 (AlgebraicClosure K),
              g⁻¹ * (baseChangeGL (algebraMap K (AlgebraicClosure K))
                (m : ModGL TwistTag.E6.tag K) : ModGL Tag.E6 (AlgebraicClosure K)) * g =
              rootDiagUnit Tag.E6 (CFSG.StandardType.TwE6RootAs.corootTuple β ζ) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hK3 : ringChar K ≠ 3 := by rw [ringChar.eq K 2]; decide
  obtain ⟨DI⟩ := d4t2pl_nonempty_lineLangIota K σ 2 hK3 hσ (by rw [hK]; norm_num)
    le_rfl h hh1 hh3
  let D : TwE6LineLang K σ 2 h := DI.toTwE6LineLang
  have hq2 : D.S.D.q = 2 := D.hSq.trans D.hqe.symm
  have h22 : (kernelRoots (rootCharHom D.a)).ncard = 22 := by
    have := D.hker
    omega
  have hfin : (kernelRoots (rootCharHom D.a)).Finite :=
    (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1
  have F := kac_facts D.hL3 D.hap
  have hsize : ∀ k : KernelComponent (rootCharHom D.a),
      (componentRoots (rootCharHom D.a) k).ncard = 2 ∨
        (componentRoots (rootCharHom D.a) k).ncard = 20 := by
    intro k
    obtain ⟨m, hm, v, ψ₀, σ₀, hψ₀, hn₀, hΨ₀, -, hS1⟩ :=
      KSConn.conn_class_data D.hL3 D.hap (Or.inl h22) k
    have hnorm : ∀ x y, x ≠ y → iform (v • σ₀ x y) (v • σ₀ x y) = 2 * 1 := fun x y hxy => by
      rw [CFSG.LieType.Chevalley.iform_smul, hn₀ x y hxy, mul_one]
    have hΨ : componentRoots (rootCharHom D.a) k = frameRoots (fun x y => v • σ₀ x y) := by
      rw [hΨ₀, IsSLFrame.frameRoots_smul]
    have hc := kd147c_frameRoots_ncard (hψ₀.transport v) one_ne_zero hnorm
    rw [← hΨ] at hc
    have hle := Set.ncard_le_ncard (fun γ hγ => hγ.1 : componentRoots (rootCharHom D.a) k ⊆
      kernelRoots (rootCharHom D.a)) hfin
    rcases hm with rfl | rfl | rfl
    · exact Or.inl (hS1 rfl).2.1
    · exact Or.inr (by omega)
    · omega
  obtain ⟨i, hqi, hJi⟩ := D.exists_rationalComponent hJ
  have hstab : ∀ k : KernelComponent (rootCharHom D.a),
      ((componentRoots (rootCharHom D.a) k).ncard = 2 ∨
        12 ≤ (componentRoots (rootCharHom D.a) k).ncard) →
      (D.S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' componentRoots (rootCharHom D.a) k =
        componentRoots (rootCharHom D.a) k := by
    intro k hk
    obtain ⟨k', hk'⟩ := outer_exists_image_component D.S D.hT k
    have hn : (componentRoots (rootCharHom D.a) k').ncard =
        (componentRoots (rootCharHom D.a) k).ncard := by
      rw [← hk', Set.ncard_image_of_injective _ D.S.ρ.injective]
    rw [hk']
    rcases hk with hk | hk
    · rw [F.one k' k (hn.trans hk) hk]
    · by_contra hne
      exact F.big k k' (fun e => hne (by rw [e])) hk (by omega)
  have hi20 : (componentRoots (rootCharHom D.a) i).ncard = 20 := by
    rcases hsize i with h2 | h20
    · exact absurd (hstab i (Or.inl h2))
        (orbit_ne_of_rank_one_quasisimple D.S hq2 D.hT i (F.rank_one i h2) h2 hqi)
    · exact h20
  obtain ⟨β, hβ, hβi⟩ : ∃ β ∈ kernelRoots (rootCharHom D.a),
      β ∉ componentRoots (rootCharHom D.a) i := by
    by_contra hall
    have hsub : kernelRoots (rootCharHom D.a) ⊆ componentRoots (rootCharHom D.a) i :=
      fun γ hγ => Classical.byContradiction fun hγi => hall ⟨γ, hγ, hγi⟩
    have := Set.ncard_le_ncard hsub (hfin.subset fun γ hγ => hγ.1)
    omega
  obtain ⟨j, hβj⟩ : ∃ j, β ∈ componentRoots (rootCharHom D.a) j := ⟨_, hβ, rfl⟩
  have hij : i ≠ j := by
    rintro rfl
    exact hβi hβj
  have hj2 : (componentRoots (rootCharHom D.a) j).ncard = 2 := by
    rcases hsize j with h2 | h20
    · exact h2
    · exact (F.big i j hij (by omega) (by omega)).elim
  have hρβ : D.S.ρ β = β ∨ D.S.ρ β = -β := by
    obtain ⟨β₀, -, hΨj⟩ := exists_pair_of_rank_one j hj2
    have hmem : D.S.ρ β ∈ componentRoots (rootCharHom D.a) j := by
      rw [← hstab j (Or.inl hj2)]
      exact Set.mem_image_of_mem _ hβj
    have h1 : β ∈ componentRoots (rootCharHom D.a) j := hβj
    rw [hΨj] at hmem h1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem h1
    rcases h1 with h1 | h1 <;> rcases hmem with h2 | h2
    · exact Or.inl (h2.trans h1.symm)
    · exact Or.inr (h2.trans (by rw [h1]))
    · exact Or.inr (h2.trans (by rw [h1, neg_neg]))
    · exact Or.inl (h2.trans h1.symm)
  have hβr : IsRoot Tag.E6 β := hβ.1
  have hAlg : D.S.IsAlgebraic := D.S.isAlgebraic_of_algebraic K 2 (by rw [hK, hq2]; norm_num)
  have hwΓ : rootSL2 Tag.E6 (AlgebraicClosure K) β WSL ∈ D.S.Γ :=
    rootSL2_WSL_mem_Γ_of_rho D.S (Or.inr (Or.inl rfl)) (hq2.trans (pow_one 2).symm) hAlg hβr hρβ
  obtain ⟨A, hAΓ, hA2, hA3, hA1⟩ :=
    exists_rootSL2_sym3_mem_Γ D.S (Or.inr (Or.inl rfl)) hq2 hAlg hβr hρβ
  have hle : rootRankOneGroup Tag.E6 (AlgebraicClosure K) β ≤
      componentRootSpan (AlgebraicClosure K) (rootCharHom D.a) j := by
    rw [(exceptional_Lang_root_rank_one_torus_transport Tag.E6 (AlgebraicClosure K) hβr).1]
    exact sup_le (le_iSup₂_of_le β hβj le_rfl)
      (le_iSup₂_of_le (-β) ((isRootComponent_componentRoots j).neg_mem β hβj) le_rfl)
  have hj : ∀ X, rootSL2 Tag.E6 (AlgebraicClosure K) β X ∈
      componentRootSpan (AlgebraicClosure K) (rootCharHom D.a) j :=
    fun X => hle (MonoidHom.mem_range.2 ⟨X, rfl⟩)
  have hρi := hstab i (Or.inr (by omega))
  have hsubi : rationalRoots D.S.ρ (rootCharHom D.a) i ⊆ componentRoots (rootCharHom D.a) i := by
    rintro _ ⟨k, δ, hδ, rfl⟩
    induction k with
    | zero => exact hδ
    | succ k ih =>
      rw [Function.iterate_succ_apply', ← hρi]
      exact Set.mem_image_of_mem _ ih
  have hRi : rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i ≤
      componentRootSpan (AlgebraicClosure K) (rootCharHom D.a) i :=
    (Subgroup.commutator_le_self (rationalSpan D.S.ρ D.S.Γ (rootCharHom D.a) i)).trans
      (inf_le_left.trans (iSup₂_le fun α hα => le_iSup₂_of_le α (hsubi hα) le_rfl))
  have hpull : ∀ X, rootSL2 Tag.E6 (AlgebraicClosure K) β X ∈ D.S.Γ →
      ∃ x ∈ fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)),
        x ∈ Subgroup.centralizer (J : Set (twistedE6RootGroup K σ)) ∧
        D.ι x = rootSL2 Tag.E6 (AlgebraicClosure K) β X := by
    intro X hX
    obtain ⟨x, hx, hxX⟩ : rootSL2 Tag.E6 (AlgebraicClosure K) β X ∈
        (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))).map D.ι := by
      rw [D.map_fixedPoints]
      exact Subgroup.mem_inf.2 ⟨hX, CFSG.LieType.Chevalley.rootSpan_le_centralizer D.a
        (fun γ hγ => hγ.1) (hj X)⟩
    refine ⟨x, hx, ?_, hxX⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply D.hinj
    have hyR : D.ι y ∈ rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i := by
      rw [← hJi]
      exact Subgroup.mem_map_of_mem D.ι hy
    rw [map_mul, map_mul, hxX]
    exact (Subgroup.mem_centralizer_iff.1
      (componentRootSpan_le_centralizer (AlgebraicClosure K) hij (hRi hyR)) _ (hj X)).symm
  obtain ⟨t, ht, htJ, htw⟩ := hpull WSL hwΓ
  obtain ⟨m, hm, hmJ, hmw⟩ := hpull (WSL * A) (by rw [map_mul]; exact mul_mem hwΓ hAΓ)
  have hW2 : (WSL : SL2 (AlgebraicClosure K)) * WSL = 1 := by
    ext a b
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_WSL, Matrix.SpecialLinearGroup.coe_one]
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]
  have hconj : (WSL : SL2 (AlgebraicClosure K)) * (WSL * A) * WSL⁻¹ = (WSL * A)⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right hW2, ← mul_assoc, hW2, one_mul, mul_inv_rev,
      inv_eq_of_mul_eq_one_right hW2, inv_eq_of_mul_eq_one_right hA2]
  refine ⟨t, ht, m, hm, htJ, hmJ, D.hinj ?_, fun h1 => hA1 (rootSL2_injective_of_field β ?_),
    D.hinj ?_, ?_⟩
  · rw [map_pow, hmw, map_one, ← map_pow (rootSL2 Tag.E6 (AlgebraicClosure K) β), hA3, map_one]
  · rw [← hmw, h1, map_one, map_one]
  · have e := congrArg (rootSL2 Tag.E6 (AlgebraicClosure K) β) hconj
    rw [map_mul, map_mul, map_inv, map_inv] at e
    rw [map_mul, map_mul, map_inv, map_inv, htw, hmw, e]
  ·
    have hζ : ∃ ζ : (AlgebraicClosure K)ˣ, ζ ^ 3 = 1 ∧ ζ ≠ 1 := by
      have : NeZero (3 : AlgebraicClosure K) := ⟨D.hL3⟩
      obtain ⟨r, hr⟩ := HasEnoughRootsOfUnity.prim (M := AlgebraicClosure K) (n := 3)
      have hr0 : r ≠ 0 := hr.ne_zero (by decide : (3 : ℕ) ≠ 0)
      let ζ : (AlgebraicClosure K)ˣ := Units.mk0 r hr0
      have hζ3 : ζ ^ 3 = 1 := by
        ext
        simpa [ζ] using hr.pow_eq_one
      have hζ1 : ζ ≠ 1 := by
        intro h1
        have hval : r = 1 := by
          simpa [ζ] using congrArg (fun u : (AlgebraicClosure K)ˣ => (u : AlgebraicClosure K)) h1
        exact hr.ne_one (by decide : 1 < 3) hval
      exact ⟨ζ, hζ3, hζ1⟩
    obtain ⟨ζ, hζ3, hζ1⟩ := hζ
    obtain ⟨P, hP⟩ := CFSG.LieType.SeitzGeneration.ExcWideThree.triOdd_sl2_conj_hsl ζ hζ3 hζ1
      ((WSL : SL2 (AlgebraicClosure K)) * A) hA3 hA1
    let R : ModGL Tag.E6 (AlgebraicClosure K) :=
      rootSL2 Tag.E6 (AlgebraicClosure K) β P
    let g : ModGL Tag.E6 (AlgebraicClosure K) := D.S.D.g0 * R⁻¹
    have hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := by
      dsimp [g]
      exact mul_mem D.S.D.g0_mem (inv_mem (rootSL2_mem_adjointGroup β P))
    have hιm : D.ι m = D.S.D.g0⁻¹ *
        (baseChangeGL (algebraMap K (AlgebraicClosure K))
          (m : ModGL TwistTag.E6.tag K) : ModGL Tag.E6 (AlgebraicClosure K)) *
        D.S.D.g0 := by
      simpa [D] using DI.hι m
    have hcalc : g⁻¹ *
        (baseChangeGL (algebraMap K (AlgebraicClosure K))
          (m : ModGL TwistTag.E6.tag K) : ModGL Tag.E6 (AlgebraicClosure K)) * g =
        rootDiagUnit Tag.E6 (CFSG.StandardType.TwE6RootAs.corootTuple β ζ) := by
      calc
        g⁻¹ * (baseChangeGL (algebraMap K (AlgebraicClosure K))
            (m : ModGL TwistTag.E6.tag K) : ModGL Tag.E6 (AlgebraicClosure K)) * g
            = R * (D.ι m) * R⁻¹ := by
              rw [hιm]
              dsimp [g]
              group
        _ = rootSL2 Tag.E6 (AlgebraicClosure K) β
              (P * ((WSL : SL2 (AlgebraicClosure K)) * A) * P⁻¹) := by
              dsimp [R]
              rw [hmw]
              simp only [map_mul, map_inv]
        _ = rootSL2 Tag.E6 (AlgebraicClosure K) β (HSL ζ) := by rw [hP]
        _ = rootDiagUnit Tag.E6 (CFSG.StandardType.TwE6RootAs.corootTuple β ζ) := by
              change rootSL2 TwistTag.E6.tag (AlgebraicClosure K) β (HSL ζ) =
                rootDiagUnit TwistTag.E6.tag
                  (CFSG.StandardType.TwE6RootAs.corootTuple β ζ)
              exact CFSG.StandardType.TwE6EltSmall.rootSL2_HSL_eq_rootDiagUnit_corootTuple
                (show IsRoot TwistTag.E6.tag β from hβr) ζ
    exact ⟨β, hβr, ζ, hζ3, hζ1, g, hg, hcalc⟩

end CFSG.LocalAnalysis.GLTheoremA.S265.TE6

end
