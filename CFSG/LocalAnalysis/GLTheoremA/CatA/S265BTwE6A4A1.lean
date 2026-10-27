module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24LineLang
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreKac
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqA1
import CFSG.LocalAnalysis.StandardType.GGLangWSLGamma
import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147cMat
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.Monster.B.Fischer.Fi22Order

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
open CFSG.StandardType.LangRat (rootSL2_WSL_mem_Γ_of_rho rootSL2_WSL_mul_self)
open CFSG.RankThree.Chevalley (rootSL2_injective_of_field)


theorem exists_involution_centralizing_of_dim28 {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} (hK : Nat.card K = 4) (hσ : ∀ c, σ c = c ^ 2) {h : twistedE6InndiagGL K σ}
    (hh3 : h ^ 3 = 1) (hh1 : h ≠ 1) (hdim : twE6MatFixDim K σ h = 28)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : IsComponentOf J (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)))) :
    ∃ t ∈ fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)),
      t ∈ Subgroup.centralizer (J : Set (twistedE6RootGroup K σ)) ∧ t * t = 1 ∧ t ≠ 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hK3 : ringChar K ≠ 3 := by rw [ringChar.eq K 2]; decide
  obtain ⟨D⟩ := nonempty_twE6LineLang K σ 2 hK3 hσ (by rw [hK]; norm_num) le_rfl h hh1 hh3
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
  have hle : rootRankOneGroup Tag.E6 (AlgebraicClosure K) β ≤
      componentRootSpan (AlgebraicClosure K) (rootCharHom D.a) j := by
    rw [(exceptional_Lang_root_rank_one_torus_transport Tag.E6 (AlgebraicClosure K) hβr).1]
    exact sup_le (le_iSup₂_of_le β hβj le_rfl)
      (le_iSup₂_of_le (-β) ((isRootComponent_componentRoots j).neg_mem β hβj) le_rfl)
  have hwj : rootSL2 Tag.E6 (AlgebraicClosure K) β WSL ∈
      componentRootSpan (AlgebraicClosure K) (rootCharHom D.a) j :=
    hle (MonoidHom.mem_range.2 ⟨WSL, rfl⟩)
  have hwd : rootSL2 Tag.E6 (AlgebraicClosure K) β WSL ∈
      Subgroup.centralizer {rootDiagUnit Tag.E6 D.a} :=
    CFSG.LieType.Chevalley.rootSpan_le_centralizer D.a (fun γ hγ => hγ.1) hwj
  have hw2 : rootSL2 Tag.E6 (AlgebraicClosure K) β WSL *
      rootSL2 Tag.E6 (AlgebraicClosure K) β WSL = 1 := rootSL2_WSL_mul_self β
  have hw1 : rootSL2 Tag.E6 (AlgebraicClosure K) β WSL ≠ 1 := fun h1 => by
    have h2 := rootSL2_injective_of_field β (h1.trans (map_one _).symm)
    have h3 := congrArg (fun A : SL2 (AlgebraicClosure K) =>
      (A : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) 0 0) h2
    simp [coe_WSL] at h3
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
  obtain ⟨t, ht, htw⟩ : rootSL2 Tag.E6 (AlgebraicClosure K) β WSL ∈
      (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))).map D.ι := by
    rw [D.map_fixedPoints]
    exact Subgroup.mem_inf.2 ⟨hwΓ, hwd⟩
  refine ⟨t, ht, ?_, D.hinj (by rw [map_mul, htw, hw2, map_one]),
    fun ht1 => hw1 (by rw [← htw, ht1, map_one])⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  apply D.hinj
  have hyR : D.ι y ∈ rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i := by
    rw [← hJi]
    exact Subgroup.mem_map_of_mem D.ι hy
  rw [map_mul, map_mul, htw]
  exact (Subgroup.mem_centralizer_iff.1
    (componentRootSpan_le_centralizer (AlgebraicClosure K) hij (hRi hyR)) _ hwj).symm

end CFSG.LocalAnalysis.GLTheoremA.S265.TE6

end
