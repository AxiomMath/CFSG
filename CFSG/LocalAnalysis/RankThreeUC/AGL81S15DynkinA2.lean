module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerStrict
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15DynkinA2Matrix
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15DynkinA2Series

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Module Polynomial
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 CFSG.Semidihedral.Principal
open CFSG.ComponentClassification
open scoped MatrixGroups

private theorem finrank_ker_factorRep_eq_zero_of_factorRep_eq_one {K V : Type*} [Group K]
    [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) K V}
    {U U' : Subrepresentation ρ} {k : K} (h : factorRep U U' k = 1) :
    finrank (ZMod 2) ↥(LinearMap.ker (aeval (factorRep U U' k) fL)) = 0 := by
  rw [h]
  have h2 : LinearMap.ker (aeval (1 : Module.End (ZMod 2)
      (U'.toSubmodule ⧸ factorSub U U')) fL) = ⊥ := DynkinA2.ker_aeval_fL_one
  rw [h2, finrank_bot]

private theorem finrank_ker_factorRep_pos_of_natural {K V : Type*} [Group K]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) K V}
    {F : Type*} [Field F] {ψ : K ⧸ CFSG.pCore 2 K ≃* SL(3, F)}
    {U U' : Subrepresentation ρ} {k : K} (h : IsNaturalFactor ψ U U')
    (hk : DynkinA2.fMat ((ψ (k : K ⧸ CFSG.pCore 2 K) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 0) :
    0 < finrank (ZMod 2) ↥(LinearMap.ker (aeval (factorRep U U' k) fL)) := by
  rw [DynkinA2.ker_aeval_fL_eq_top_of_natural h hk, finrank_top]
  exact DynkinA2.finrank_pos_of_natural h

private theorem finrank_ker_factorRep_eq_zero_of_natural {K V : Type*} [Group K]
    [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) K V}
    {F : Type*} [Field F] {ψ : K ⧸ CFSG.pCore 2 K ≃* SL(3, F)}
    {U U' : Subrepresentation ρ} {k : K} (h : IsNaturalFactor ψ U U')
    (hk : ∃ N : Matrix (Fin 3) (Fin 3) F,
      N * DynkinA2.fMat ((ψ (k : K ⧸ CFSG.pCore 2 K) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1) :
    finrank (ZMod 2) ↥(LinearMap.ker (aeval (factorRep U U' k) fL)) = 0 := by
  obtain ⟨N, hN⟩ := hk
  rw [DynkinA2.ker_aeval_fL_eq_bot_of_natural h hN, finrank_bot]

private theorem finrank_ker_factorRep_eq_zero_of_dual {K V : Type*} [Group K]
    [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) K V}
    {F : Type*} [Field F] {ψ : K ⧸ CFSG.pCore 2 K ≃* SL(3, F)}
    {U U' : Subrepresentation ρ} {k : K} (h : IsDualNaturalFactor ψ U U')
    (hk : ∃ N : Matrix (Fin 3) (Fin 3) F,
      N * DynkinA2.fMat (dualMat (ψ (k : K ⧸ CFSG.pCore 2 K))) = 1) :
    finrank (ZMod 2) ↥(LinearMap.ker (aeval (factorRep U U' k) fL)) = 0 := by
  obtain ⟨N, hN⟩ := hk
  rw [DynkinA2.ker_aeval_fL_eq_bot_of_dual h hN, finrank_bot]

private theorem finrank_ker_factorRep_pos_of_dual {K V : Type*} [Group K]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) K V}
    {F : Type*} [Field F] {ψ : K ⧸ CFSG.pCore 2 K ≃* SL(3, F)}
    {U U' : Subrepresentation ρ} {k : K} (h : IsDualNaturalFactor ψ U U')
    (hk : DynkinA2.fMat (dualMat (ψ (k : K ⧸ CFSG.pCore 2 K))) = 0) :
    0 < finrank (ZMod 2) ↥(LinearMap.ker (aeval (factorRep U U' k) fL)) := by
  rw [DynkinA2.ker_aeval_fL_eq_top_of_dual h hk, finrank_top]
  exact DynkinA2.finrank_pos_of_dual h

private theorem sum_finrank_ker_factorRep_eq_zero_of_natural {K V : Type*} [Group K]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) K V}
    {F : Type*} [Field F] {ψ : K ⧸ CFSG.pCore 2 K ≃* SL(3, F)} {r : ℕ}
    {Vs : Fin (r + 1) → Subrepresentation ρ}
    (hnat : ∀ i ∈ nontrivialFactors Vs, IsNaturalFactor ψ (Vs i.castSucc) (Vs i.succ))
    {k : K} (hk : ∃ N : Matrix (Fin 3) (Fin 3) F,
      N * DynkinA2.fMat ((ψ (k : K ⧸ CFSG.pCore 2 K) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1) :
    ∑ i : Fin r, finrank (ZMod 2)
      ↥(LinearMap.ker (aeval (factorRep (Vs i.castSucc) (Vs i.succ) k) fL)) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i ∈ nontrivialFactors Vs
  · exact finrank_ker_factorRep_eq_zero_of_natural (hnat i hi) hk
  · exact finrank_ker_factorRep_eq_zero_of_factorRep_eq_one (by
      by_contra h
      exact hi (mem_nontrivialFactors.mpr ⟨k, h⟩))

private theorem sum_finrank_ker_factorRep_eq_zero_of_dual {K V : Type*} [Group K]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) K V}
    {F : Type*} [Field F] {ψ : K ⧸ CFSG.pCore 2 K ≃* SL(3, F)} {r : ℕ}
    {Vs : Fin (r + 1) → Subrepresentation ρ}
    (hdual : ∀ i ∈ nontrivialFactors Vs, IsDualNaturalFactor ψ (Vs i.castSucc) (Vs i.succ))
    {k : K} (hk : ∃ N : Matrix (Fin 3) (Fin 3) F,
      N * DynkinA2.fMat (dualMat (ψ (k : K ⧸ CFSG.pCore 2 K))) = 1) :
    ∑ i : Fin r, finrank (ZMod 2)
      ↥(LinearMap.ker (aeval (factorRep (Vs i.castSucc) (Vs i.succ) k) fL)) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i ∈ nontrivialFactors Vs
  · exact finrank_ker_factorRep_eq_zero_of_dual (hdual i hi) hk
  · exact finrank_ker_factorRep_eq_zero_of_factorRep_eq_one (by
      by_contra h
      exact hi (mem_nontrivialFactors.mpr ⟨k, h⟩))

private theorem false_of_all_natural {K V : Type*} [Group K] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) K V} {F : Type*} [Field F]
    {ψ : K ⧸ CFSG.pCore 2 K ≃* SL(3, F)} {r : ℕ} {Vs : Fin (r + 1) → Subrepresentation ρ}
    (hmono : ∀ i : Fin r, Vs i.castSucc ≤ Vs i.succ) (h0 : Vs 0 = ⊥)
    (hlast : Vs (Fin.last r) = ⊤) (hSne : (nontrivialFactors Vs).Nonempty)
    (hnat : ∀ i ∈ nontrivialFactors Vs, IsNaturalFactor ψ (Vs i.castSucc) (Vs i.succ))
    {k₀ k₁ : K} (hk₀ : k₀ ^ 7 = 1) (hk₁ : k₁ ^ 7 = 1)
    (hf₀ : DynkinA2.fMat ((ψ (k₀ : K ⧸ CFSG.pCore 2 K) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 0)
    (hf₁ : ∃ N : Matrix (Fin 3) (Fin 3) F,
      N * DynkinA2.fMat ((ψ (k₁ : K ⧸ CFSG.pCore 2 K) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1)
    (hF : finrank (ZMod 2) ↥(LinearMap.ker (aeval (ρ k₀) fL)) =
      finrank (ZMod 2) ↥(LinearMap.ker (aeval (ρ k₁) fL))) : False := by
  obtain ⟨a, ha⟩ : ∃ a : Fin r → ℕ, a = fun i => finrank (ZMod 2)
      ↥(LinearMap.ker (aeval (factorRep (Vs i.castSucc) (Vs i.succ) k₀) fL)) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin r → ℕ, b = fun i => finrank (ZMod 2)
      ↥(LinearMap.ker (aeval (factorRep (Vs i.castSucc) (Vs i.succ) k₁) fL)) := ⟨_, rfl⟩
  have h0' : finrank (ZMod 2) ↥(LinearMap.ker (aeval (ρ k₀) fL)) = ∑ i : Fin r, a i := by
    rw [DynkinA2.finrank_ker_aeval_fL_eq_sum hmono h0 hlast hk₀, ha]
  have h1' : finrank (ZMod 2) ↥(LinearMap.ker (aeval (ρ k₁) fL)) = ∑ i : Fin r, b i := by
    rw [DynkinA2.finrank_ker_aeval_fL_eq_sum hmono h0 hlast hk₁, hb]
  have hb0 : (∑ i : Fin r, b i) = 0 := by
    rw [hb]
    exact sum_finrank_ker_factorRep_eq_zero_of_natural hnat hf₁
  obtain ⟨i₀, hi₀⟩ := hSne
  have hpos : 0 < a i₀ := by
    rw [ha]
    exact finrank_ker_factorRep_pos_of_natural (hnat i₀ hi₀) hf₀
  have hle : a i₀ ≤ ∑ i : Fin r, a i :=
    Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀)
  rw [h0', h1', hb0] at hF
  exact absurd hF (ne_of_gt (lt_of_lt_of_le hpos hle))

private theorem false_of_all_dual {K V : Type*} [Group K] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) K V} {F : Type*} [Field F]
    {ψ : K ⧸ CFSG.pCore 2 K ≃* SL(3, F)} {r : ℕ} {Vs : Fin (r + 1) → Subrepresentation ρ}
    (hmono : ∀ i : Fin r, Vs i.castSucc ≤ Vs i.succ) (h0 : Vs 0 = ⊥)
    (hlast : Vs (Fin.last r) = ⊤) (hSne : (nontrivialFactors Vs).Nonempty)
    (hdual : ∀ i ∈ nontrivialFactors Vs, IsDualNaturalFactor ψ (Vs i.castSucc) (Vs i.succ))
    {k₀ k₁ : K} (hk₀ : k₀ ^ 7 = 1) (hk₁ : k₁ ^ 7 = 1)
    (hf₀ : ∃ N : Matrix (Fin 3) (Fin 3) F,
      N * DynkinA2.fMat (dualMat (ψ (k₀ : K ⧸ CFSG.pCore 2 K))) = 1)
    (hf₁ : DynkinA2.fMat (dualMat (ψ (k₁ : K ⧸ CFSG.pCore 2 K))) = 0)
    (hF : finrank (ZMod 2) ↥(LinearMap.ker (aeval (ρ k₀) fL)) =
      finrank (ZMod 2) ↥(LinearMap.ker (aeval (ρ k₁) fL))) : False := by
  obtain ⟨a, ha⟩ : ∃ a : Fin r → ℕ, a = fun i => finrank (ZMod 2)
      ↥(LinearMap.ker (aeval (factorRep (Vs i.castSucc) (Vs i.succ) k₀) fL)) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin r → ℕ, b = fun i => finrank (ZMod 2)
      ↥(LinearMap.ker (aeval (factorRep (Vs i.castSucc) (Vs i.succ) k₁) fL)) := ⟨_, rfl⟩
  have h0' : finrank (ZMod 2) ↥(LinearMap.ker (aeval (ρ k₀) fL)) = ∑ i : Fin r, a i := by
    rw [DynkinA2.finrank_ker_aeval_fL_eq_sum hmono h0 hlast hk₀, ha]
  have h1' : finrank (ZMod 2) ↥(LinearMap.ker (aeval (ρ k₁) fL)) = ∑ i : Fin r, b i := by
    rw [DynkinA2.finrank_ker_aeval_fL_eq_sum hmono h0 hlast hk₁, hb]
  have ha0 : (∑ i : Fin r, a i) = 0 := by
    rw [ha]
    exact sum_finrank_ker_factorRep_eq_zero_of_dual hdual hf₀
  obtain ⟨i₀, hi₀⟩ := hSne
  have hpos : 0 < b i₀ := by
    rw [hb]
    exact finrank_ker_factorRep_pos_of_dual (hdual i₀ hi₀) hf₁
  have hle : b i₀ ≤ ∑ i : Fin r, b i :=
    Finset.single_le_sum (f := b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀)
  rw [h0', h1', ha0] at hF
  exact absurd hF (ne_of_lt (lt_of_lt_of_le hpos hle))

theorem not_isGraphType_of_strictMin {G : Type} [Group G] [Finite G] {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) G W)
    (L B : Subgroup G) {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (e : ↥L ≃* SL(3, F)) (hperf : commutator ↥L = ⊤)
    (hsimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L))
    (hB2 : ∀ b ∈ B, b * b = 1) (hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b)
    (hinner : ∀ b ∈ B, ∃ l ∈ L, ConjAgree L b l) {U : Submodule (ZMod 2) W}
    (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) U) (hbest : IsBestOffenderOn ρ B U)
    (hmove : ∀ b ∈ B, b ∉ cenOn ρ B U → ∃ k ∈ L, ∃ u ∈ U, ρ b (ρ k u) ≠ ρ k (ρ b u))
    (hnt : ¬ B ≤ cenOn ρ B U) (hLnt : ¬ L ≤ cenOn ρ L U)
    {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) (hgU : ∀ u ∈ U, ρ g u ∈ U)
    (hgU' : ∀ u ∈ U, ρ g⁻¹ u ∈ U) :
    ¬ CFSG.Quasithin.L34Out.IsGraphType (MulAut.congr e (L.normalizerMonoidHom ⟨g, hg⟩)) := by
  classical
  intro hα
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hZ' : ∀ z ∈ Subgroup.center ↥L, z ^ 3 = 1 := center_pow_three e
  have hZ : ∀ z ∈ L, (∀ k ∈ L, k * z = z * k) → z ^ 3 = 1 := by
    intro z hz hzc
    have hmem : (⟨z, hz⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hzc g g.2)
    simpa using congrArg Subtype.val (hZ' _ hmem)
  obtain ⟨lB, hlB⟩ := exists_lift_hom hB2 hBc hZ hinner
  obtain ⟨π, hπ⟩ := exists_split_hom lB hlB
  have hLsub : ∀ l : ↥L, π (l, 1) = (l : G) := fun l => by rw [hπ]; simp
  have hgr : ∀ b : ↥B, π (lB b, b) = (b : G) := fun b => by rw [hπ]; simp
  have hπmem : ∀ k : ↥L × ↥B, π k ∈ L ⊔ B := by
    rintro ⟨l, b⟩
    rw [hπ]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left l.2)
      (Subgroup.inv_mem _ (Subgroup.mem_sup_left (lB b).2))) (Subgroup.mem_sup_right b.2)
  have hBp : IsPGroup 2 ↥B := fun b => ⟨1, by
    apply Subtype.ext
    show (b : G) ^ 2 ^ 1 = 1
    rw [pow_one, pow_two]
    exact hB2 b b.2⟩
  have hLp : CFSG.pCore 2 ↥L = ⊥ := pCore_two_eq_bot_of_quasisimple hperf hsimple hZ'
  obtain ⟨e1, he1⟩ := exists_quotientEquiv_fst hBp hLp
  let ψ : (↥L × ↥B) ⧸ CFSG.pCore 2 (↥L × ↥B) ≃* Matrix.SpecialLinearGroup (Fin 3) F := e1.trans e
  have hAea : CFSG.IsElementaryAbelian 2 (graphSub lB) := graphSub_isElementaryAbelian lB
    (fun b c => Subtype.ext (hBc b b.2 c c.2)) (fun b => Subtype.ext (hB2 b b.2))
  have hex : ∃ b : ↥B, lB b ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hnt fun b hb => mem_cenOn_of_lift_eq_one lB hlB hmove ⟨b, hb⟩ (hall ⟨b, hb⟩)
  have hnotle : ¬ graphSub lB ≤ CFSG.pCore 2 (↥L × ↥B) := not_graphSub_le_pCore hBp hLp lB hex
  let SU : Subrepresentation (ρ.comp π) := ⟨U, fun g w hw => hinv (π g) (hπmem g) w hw⟩
  have : Finite ↥SU.toSubmodule := inferInstanceAs (Finite ↥U)
  obtain ⟨r, Vs, hVs⟩ := exists_isCompositionSeries SU.toRepresentation
  let φ : ↥B →* (↥L × ↥B) ⧸ CFSG.pCore 2 (↥L × ↥B) :=
    (QuotientGroup.mk' (CFSG.pCore 2 (↥L × ↥B))).comp (lB.prod (MonoidHom.id ↥B))
  have hrange : φ.range = (graphSub lB).map (QuotientGroup.mk' (CFSG.pCore 2 (↥L × ↥B))) :=
    (MonoidHom.map_range _ _).symm
  have hφ : ∀ b : ↥B, φ b = 1 → (b : G) ∈ cenOn ρ B U := by
    intro b hb
    have h1 : (lB b, b) ∈ CFSG.pCore 2 (↥L × ↥B) := (QuotientGroup.eq_one_iff _).mp hb
    rw [pCore_prod_eq_ker_fst hBp hLp] at h1
    exact mem_cenOn_of_lift_eq_one lB hlB hmove b (MonoidHom.mem_ker.mp h1)
  have hlog := finrank_sub_le_log_card_range hbest φ hφ
  rw [hrange] at hlog
  have hsum : ∑ i ∈ nontrivialFactors Vs, factorCodim Vs (graphSub lB) i ≤
      Nat.log 2 (Nat.card ((graphSub lB).map
        (QuotientGroup.mk' (CFSG.pCore 2 (↥L × ↥B))))) := by
    calc ∑ i ∈ nontrivialFactors Vs, factorCodim Vs (graphSub lB) i
        ≤ ∑ i, factorCodim Vs (graphSub lB) i :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ ≤ finrank (ZMod 2) ↥SU.toSubmodule -
            finrank (ZMod 2) ↥(fixSub SU.toRepresentation (graphSub lB)) :=
          sum_factorCodim_le Vs (fun i => (hVs.covBy i).le) hVs.zero hVs.last _
      _ = finrank (ZMod 2) ↥U - finrank (ZMod 2) ↥(fixOn ρ B U) := by
          rw [finrank_fixSub_graph lB π hgr SU]
      _ ≤ _ := hlog
  obtain ⟨hpc, hnat, hcard, hiso⟩ := chief_factors_of_FFClassification ψ (by omega) hFc
    (ffClassificationSL3_of_card hn hFc) hVs (graphSub lB) hnotle hsum
  have hker : ∀ b : ↥B, ((1 : ↥L), b) ∈ CFSG.pCore 2 (↥L × ↥B) := fun b => by
    rw [pCore_prod_eq_ker_fst hBp hLp]
    exact MonoidHom.mem_ker.mpr rfl
  have hsurj : ∀ (i : Fin r) (k : ↥L × ↥B), ∃ l : ↥L,
      factorRep (Vs i.castSucc) (Vs i.succ) k =
        factorRep (Vs i.castSucc) (Vs i.succ) (MonoidHom.inl ↥L ↥B l) := by
    rintro i ⟨l, b⟩
    refine ⟨l, ?_⟩
    have hk : ((l, b) : ↥L × ↥B) = MonoidHom.inl ↥L ↥B l * ((1 : ↥L), b) := by simp
    have h1 : factorRep (Vs i.castSucc) (Vs i.succ) ((1 : ↥L), b) = 1 :=
      LinearMap.ext (hpc i _ (hker b))
    rw [hk, map_mul, h1, mul_one]
  have hle := nontrivCount_comp_le_card (MonoidHom.inl ↥L ↥B) hVs hsurj
  have hSne : (nontrivialFactors Vs).Nonempty := by
    by_contra hS
    rw [Finset.not_nonempty_iff_eq_empty] at hS
    have h0 : nontrivCount ((SU.toRepresentation).comp (MonoidHom.inl ↥L ↥B)) = 0 := by
      have h := hle
      rw [hS] at h
      simpa using h
    have : Module.Finite (ZMod 2) ↥SU.toSubmodule := Module.Finite.of_finite
    have htriv := trivial_of_nontrivCount_eq_zero (k := ZMod 2) (G := ↥L) hperf
      ((SU.toRepresentation).comp (MonoidHom.inl ↥L ↥B)) h0
    exact hLnt fun l hl => mem_cenOn.mpr ⟨hl, fun u hu => by
      have h1 := htriv ⟨l, hl⟩
      have h2 : SU.toRepresentation (MonoidHom.inl ↥L ↥B ⟨l, hl⟩) ⟨u, hu⟩ = ⟨u, hu⟩ := by
        have h2 := LinearMap.congr_fun h1 ⟨u, hu⟩
        rwa [Module.End.one_apply] at h2
      have h3 : (ρ.comp π) (MonoidHom.inl ↥L ↥B ⟨l, hl⟩) u = u :=
        (Subrepresentation.toRepresentation_apply_mk).mp h2
      rw [show MonoidHom.inl ↥L ↥B ⟨l, hl⟩ = ((⟨l, hl⟩, 1) : ↥L × ↥B) from rfl] at h3
      rw [show (ρ.comp π) ((⟨l, hl⟩, 1) : ↥L × ↥B) =
        ρ (π ((⟨l, hl⟩, 1) : ↥L × ↥B)) from rfl, hLsub] at h3
      exact h3⟩
  have hpat : (∀ i ∈ nontrivialFactors Vs, IsNaturalFactor ψ (Vs i.castSucc) (Vs i.succ)) ∨
      (∀ i ∈ nontrivialFactors Vs, IsDualNaturalFactor ψ (Vs i.castSucc) (Vs i.succ)) := by
    have hcpos : 0 < (nontrivialFactors Vs).card := Finset.card_pos.mpr hSne
    rcases Nat.eq_or_lt_of_le hcard with h2 | h1
    ·
      obtain ⟨i, j, hi, hj, hij, ⟨φij, hφij⟩, -⟩ := hiso h2
      have hsub : ({i, j} : Finset (Fin r)) ⊆ nontrivialFactors Vs := by
        intro m hm
        rw [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl
        · exact hi
        · exact hj
      have hcard2 : ({i, j} : Finset (Fin r)).card = 2 :=
        Finset.card_pair (by rintro rfl; exact lt_irrefl _ hij)
      have hSij : nontrivialFactors Vs = {i, j} :=
        (Finset.eq_of_subset_of_card_le hsub (by rw [hcard2, h2])).symm
      have hmem : ∀ m ∈ nontrivialFactors Vs, m = i ∨ m = j := by
        intro m hm
        rw [hSij] at hm
        simpa using hm
      rcases (hnat i hi).1 with hN | hD
      · left
        intro m hm
        rcases hmem m hm with rfl | rfl
        · exact hN
        · exact DynkinA2.isNaturalFactor_of_equiv hN φij hφij
      · right
        intro m hm
        rcases hmem m hm with rfl | rfl
        · exact hD
        · exact DynkinA2.isDualNaturalFactor_of_equiv hD φij hφij
    ·
      have h1' : (nontrivialFactors Vs).card = 1 := by omega
      obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp h1'
      have hi₀mem : i₀ ∈ nontrivialFactors Vs := by
        rw [hi₀]; exact Finset.mem_singleton_self i₀
      have hall : ∀ i ∈ nontrivialFactors Vs, i = i₀ := by
        intro i hi
        rw [hi₀] at hi
        simpa using hi
      rcases (hnat i₀ hi₀mem).1 with hN | hD
      · left; intro i hi; rw [hall i hi]; exact hN
      · right; intro i hi; rw [hall i hi]; exact hD
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut (SL(3, F)),
      α = MulAut.congr e (L.normalizerMonoidHom ⟨g, hg⟩) := ⟨_, rfl⟩
  rw [← hαdef] at hα
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ↥L, x₀ = e.symm (DynkinA2.cSL F) := ⟨_, rfl⟩
  have hx₀e : e x₀ = DynkinA2.cSL F := by
    rw [hx₀, MulEquiv.apply_symm_apply]
  have hyL : g * (x₀ : G) * g⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hg (x₀ : G)).1 x₀.2
  obtain ⟨y, hy⟩ : ∃ y : ↥L, (y : G) = g * (x₀ : G) * g⁻¹ := ⟨⟨_, hyL⟩, rfl⟩
  have hey : e y = α (DynkinA2.cSL F) := by
    have h1 : y = (L.normalizerMonoidHom ⟨g, hg⟩) x₀ := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hy]
    rw [h1, hαdef, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, ← hx₀]
  obtain ⟨k₀, hk₀def⟩ : ∃ k₀ : ↥L × ↥B, k₀ = (x₀, 1) := ⟨_, rfl⟩
  obtain ⟨k₁, hk₁def⟩ : ∃ k₁ : ↥L × ↥B, k₁ = (y, 1) := ⟨_, rfl⟩
  have hψ₀ : ψ (k₀ : (↥L × ↥B) ⧸ CFSG.pCore 2 (↥L × ↥B)) = DynkinA2.cSL F := by
    rw [hk₀def]
    change e (e1 (QuotientGroup.mk ((x₀, 1) : ↥L × ↥B))) = DynkinA2.cSL F
    rw [he1]
    exact hx₀e
  have hψ₁ : ψ (k₁ : (↥L × ↥B) ⧸ CFSG.pCore 2 (↥L × ↥B)) = α (DynkinA2.cSL F) := by
    rw [hk₁def]
    change e (e1 (QuotientGroup.mk ((y, 1) : ↥L × ↥B))) = α (DynkinA2.cSL F)
    rw [he1]
    exact hey
  have hx₀pow : x₀ ^ 7 = 1 := by
    apply e.injective
    rw [map_pow, hx₀e, DynkinA2.cSL_pow_seven, map_one]
  have hypow : y ^ 7 = 1 := by
    apply e.injective
    rw [map_pow, hey, ← map_pow, DynkinA2.cSL_pow_seven, map_one, map_one]
  have hk₀ : k₀ ^ 7 = 1 := by
    rw [hk₀def, Prod.pow_mk, hx₀pow, one_pow, Prod.mk_one_one]
  have hk₁ : k₁ ^ 7 = 1 := by
    rw [hk₁def, Prod.pow_mk, hypow, one_pow, Prod.mk_one_one]
  have hs₀ := DynkinA2.finrank_ker_aeval_fL_eq_sum (fun i => (hVs.covBy i).le) hVs.zero
    hVs.last hk₀
  have hs₁ := DynkinA2.finrank_ker_aeval_fL_eq_sum (fun i => (hVs.covBy i).le) hVs.zero
    hVs.last hk₁
  have hκ₀ : kerDim ρ fL (x₀ : G) U =
      finrank (ZMod 2) ↥(LinearMap.ker (aeval (SU.toRepresentation k₀) fL)) := by
    have h := DynkinA2.kerDim_eq_finrank_ker ρ π SU k₀ fL
    rw [hk₀def, hLsub] at h
    rw [hk₀def]
    exact h
  have hκ₁ : kerDim ρ fL (y : G) U =
      finrank (ZMod 2) ↥(LinearMap.ker (aeval (SU.toRepresentation k₁) fL)) := by
    have h := DynkinA2.kerDim_eq_finrank_ker ρ π SU k₁ fL
    rw [hk₁def, hLsub] at h
    rw [hk₁def]
    exact h
  have hconj : kerDim ρ fL (y : G) U = kerDim ρ fL (x₀ : G) U := by
    rw [hy]
    exact kerDim_conj ρ fL (x₀ : G) g U hgU hgU'
  have hF : finrank (ZMod 2) ↥(LinearMap.ker (aeval (SU.toRepresentation k₀) fL)) =
      finrank (ZMod 2) ↥(LinearMap.ker (aeval (SU.toRepresentation k₁) fL)) := by
    rw [← hκ₀, ← hκ₁, hconj]
  rcases hpat with hpat | hpat
  · refine false_of_all_natural (ρ := SU.toRepresentation) (Vs := Vs)
      (fun i => (hVs.covBy i).le) hVs.zero hVs.last hSne hpat hk₀ hk₁ ?_ ?_ hF
    · rw [hψ₀]
      exact DynkinA2.fMat_cSL F
    · rw [hψ₁]
      exact (DynkinA2.fMat_isGraphType_cSL F hα).1
  · refine false_of_all_dual (ρ := SU.toRepresentation) (Vs := Vs)
      (fun i => (hVs.covBy i).le) hVs.zero hVs.last hSne hpat hk₀ hk₁ ?_ ?_ hF
    · rw [hψ₀]
      exact DynkinA2.exists_mul_fMat_dualMat_cSL F
    · rw [hψ₁]
      exact (DynkinA2.fMat_isGraphType_cSL F hα).2

theorem exists_eq_slConjugation_mul_slFieldAut_of_offender {G : Type} [Group G] [Finite G]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) G W) (hρ : Function.Injective ρ) {L : Subgroup G} {F : Type}
    [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (e : ↥L ≃* SL(3, F))
    (hquasi : CFSG.Open.IsQuasisimple ↥L) {A : Subgroup G} (hA2 : CFSG.IsElementaryAbelian 2 ↥A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hLA : ⁅L, A⁆ = L)
    (hb : IsBestOffenderOn ρ A ⊤) (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    ∃ (P : GL (Fin 3) F) (σ : F ≃+* F),
      MulAut.congr e (L.normalizerMonoidHom ⟨g, hg⟩) =
        CatalogueBHigherLinearAction.slConjugation 3 F P *
          CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ := by
  classical
  have : CFSG.IsElementaryAbelian 2 ↥A := hA2
  have hKnt : ¬ L ≤ cenOn ρ L ⊤ := by
    intro h
    have h1 : ∀ k : ↥L, k = 1 := fun k => by
      apply Subtype.ext
      apply hρ
      ext v
      rw [Subgroup.coe_one, map_one, Module.End.one_apply]
      exact (mem_cenOn.mp (h k.2)).2 v Submodule.mem_top
    obtain ⟨a, b, hab⟩ := hquasi.2.exists_pair_ne
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [h1 x, h1 y])
  obtain ⟨B, hBA, hUinv, hLU, hBU, hbest, hquad, hmove, -⟩ :=
    exists_strictMin_moving (ρ := ρ) L A hA2 hAN hLA hKnt hb
  have hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b := fun b hb c hc =>
    congrArg Subtype.val (hA2.toIsMulCommutative.is_comm.comm ⟨b, hBA hb⟩ ⟨c, hBA hc⟩)
  have hB2 : ∀ b ∈ B, b * b = 1 := fun b hb => by
    rw [← pow_two]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := A) b (hBA hb)
  have hBN : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L := fun b hb l hl =>
    (Subgroup.mem_normalizer_iff.mp (hAN (hBA hb)) l).mp hl
  have hinner := strictMin_inner ρ L B hn hF e hquasi hBN hB2 hBc hUinv hLU hbest hquad hmove
  have hUN := isInvariant_commOn_top (ρ := ρ) (K := L)
    (H := Subgroup.normalizer (L : Set G)) le_rfl
  have hgU : ∀ u ∈ commOn ρ L ⊤, ρ g u ∈ commOn ρ L ⊤ := fun u hu => hUN g hg u hu
  have hgU' : ∀ u ∈ commOn ρ L ⊤, ρ g⁻¹ u ∈ commOn ρ L ⊤ :=
    fun u hu => hUN g⁻¹ (Subgroup.inv_mem _ hg) u hu
  obtain ⟨P, σ, ε, hε, hβ⟩ := CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl
    (n := 3) (K := F) (by norm_num) (MulAut.congr e (L.normalizerMonoidHom ⟨g, hg⟩))
  interval_cases ε
  · exact ⟨P, σ, by rw [hβ, pow_zero, mul_one]⟩
  · exfalso
    exact not_isGraphType_of_strictMin ρ L B hn hF e hquasi.1 hquasi.2 hB2 hBc hinner hUinv
      hbest hmove hBU hLU hg hgU hgU' ⟨P, σ, by rw [hβ, pow_one]⟩

end CFSG.LocalAnalysis.RankThreeUC.S15

end
