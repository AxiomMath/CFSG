module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RepChain
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15OffenderLift
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15OffenderSplit
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15OffenderBudget
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SeriesCodim
public import CFSG.RankThree.FFModules.ClassificationSL3

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Module
open CFSG.Semidihedral.Principal

section CompSeries

theorem exists_isCompositionSeries {K V : Type} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (ρ : Representation (ZMod 2) K V) :
    ∃ (r : ℕ) (Vs : Fin (r + 1) → Subrepresentation ρ), IsCompositionSeries r Vs := by
  have n1 := isNoetherian_of_finiteDimensional (ZMod 2) (A := MonoidAlgebra (ZMod 2) K)
    (M := ρ.asModule)
  have a1 := isArtinian_of_finiteDimensional (ZMod 2) (A := MonoidAlgebra (ZMod 2) K)
    (M := ρ.asModule)
  obtain ⟨s, h₁, h₂⟩ := exists_compositionSeries_of_isNoetherian_isArtinian
    (MonoidAlgebra (ZMod 2) K) ρ.asModule
  let e : Subrepresentation ρ ≃o Submodule (MonoidAlgebra (ZMod 2) K) ρ.asModule :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  refine ⟨s.length, fun i => e.symm (s i), ⟨?_, ?_, ?_⟩⟩
  · show e.symm (s 0) = ⊥
    rw [show s 0 = ⊥ from h₁]
    exact map_bot e.symm
  · show e.symm (s (Fin.last s.length)) = ⊤
    rw [show s (Fin.last s.length) = ⊤ from h₂]
    exact map_top e.symm
  · intro i
    exact (apply_covBy_apply_iff e.symm).mpr (s.step i)

end CompSeries

section Offender

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G W} {L B : Subgroup G}

theorem mem_cenOn_of_lift_eq_one {U : Submodule (ZMod 2) W} (lB : ↥B →* ↥L)
    (hlB : ∀ b : ↥B, ConjAgree L (b : G) (lB b : G))
    (hmove : ∀ b ∈ B, b ∉ cenOn ρ B U → ∃ k ∈ L, ∃ u ∈ U, ρ b (ρ k u) ≠ ρ k (ρ b u))
    (b : ↥B) (hb : lB b = 1) : (b : G) ∈ cenOn ρ B U := by
  by_contra hc
  obtain ⟨k, hk, u, hu, hne⟩ := hmove b b.2 hc
  apply hne
  have hconj := hlB b k hk
  rw [hb] at hconj
  have hconj' : (b : G) * k * (b : G)⁻¹ = k := by simpa using hconj
  have hcomm : (b : G) * k = k * b := by
    calc (b : G) * k = ((b : G) * k * (b : G)⁻¹) * b := by group
      _ = k * b := by rw [hconj']
  calc ρ b (ρ k u) = ρ (b * k) u := by rw [map_mul]; rfl
    _ = ρ (k * b) u := by rw [hcomm]
    _ = ρ k (ρ b u) := by rw [map_mul]; rfl


theorem map_subtype_fixSub_graph (lB : ↥B →* ↥L) (π : ↥L × ↥B →* G)
    (hgr : ∀ b : ↥B, π (lB b, b) = (b : G)) (SU : Subrepresentation (ρ.comp π)) :
    (fixSub SU.toRepresentation (graphSub lB)).map SU.toSubmodule.subtype =
      fixOn ρ B SU.toSubmodule := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_fixOn.mpr ⟨x.2, fun b hb => ?_⟩
    have h1 : SU.toRepresentation (lB ⟨b, hb⟩, ⟨b, hb⟩) x = x :=
      (mem_fixSub.mp hx) _ (mem_graphSub.mpr ⟨⟨b, hb⟩, rfl⟩)
    have h2 : ρ (π (lB ⟨b, hb⟩, ⟨b, hb⟩)) (x : W) = x := congrArg Subtype.val h1
    rwa [hgr] at h2
  · intro hw
    obtain ⟨hw, hfix⟩ := mem_fixOn.mp hw
    refine ⟨⟨w, hw⟩, mem_fixSub.mpr fun a ha => ?_, rfl⟩
    obtain ⟨b, rfl⟩ := mem_graphSub.mp ha
    apply Subtype.ext
    show ρ (π (lB b, b)) w = w
    rw [hgr]
    exact hfix b b.2

theorem finrank_fixSub_graph (lB : ↥B →* ↥L) (π : ↥L × ↥B →* G)
    (hgr : ∀ b : ↥B, π (lB b, b) = (b : G)) (SU : Subrepresentation (ρ.comp π)) :
    finrank (ZMod 2) ↥(fixSub SU.toRepresentation (graphSub lB)) =
      finrank (ZMod 2) ↥(fixOn ρ B SU.toSubmodule) := by
  rw [← map_subtype_fixSub_graph lB π hgr SU]
  exact (Submodule.finrank_map_subtype_eq _ _).symm


end Offender

section Main

theorem nontrivCount_le_two {G : Type} [Group G] [Finite G] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) G W) (L B : Subgroup G)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) F) (hperf : commutator ↥L = ⊤)
    (hsimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L))
    (hB2 : ∀ b ∈ B, b * b = 1) (hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b)
    (hinner : ∀ b ∈ B, ∃ l ∈ L, ConjAgree L b l) {U : Submodule (ZMod 2) W}
    (hUL : commOn ρ L ⊤ ≤ U) (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) U) (hbest : IsBestOffenderOn ρ B U)
    (hmove : ∀ b ∈ B, b ∉ cenOn ρ B U → ∃ k ∈ L, ∃ u ∈ U, ρ b (ρ k u) ≠ ρ k (ρ b u))
    (hnt : ¬ B ≤ cenOn ρ B U) : nontrivCount (ρ.comp L.subtype) ≤ 2 := by
  classical
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  haveI : Fintype F := Fintype.ofFinite F
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
  obtain ⟨e1, -⟩ := exists_quotientEquiv_fst hBp hLp
  let ψ : (↥L × ↥B) ⧸ CFSG.pCore 2 (↥L × ↥B) ≃* Matrix.SpecialLinearGroup (Fin 3) F := e1.trans e
  haveI hAea : CFSG.IsElementaryAbelian 2 (graphSub lB) := graphSub_isElementaryAbelian lB
    (fun b c => Subtype.ext (hBc b b.2 c c.2)) (fun b => Subtype.ext (hB2 b b.2))
  have hex : ∃ b : ↥B, lB b ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hnt fun b hb => mem_cenOn_of_lift_eq_one lB hlB hmove ⟨b, hb⟩ (hall ⟨b, hb⟩)
  have hnotle : ¬ graphSub lB ≤ CFSG.pCore 2 (↥L × ↥B) := not_graphSub_le_pCore hBp hLp lB hex
  let SU : Subrepresentation (ρ.comp π) := ⟨U, fun g w hw => hinv (π g) (hπmem g) w hw⟩
  haveI : Finite ↥SU.toSubmodule := inferInstanceAs (Finite ↥U)
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
  obtain ⟨hpc, -, hcard, -⟩ := chief_factors_of_FFClassification ψ (by omega) hFc
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
  have hsq := nontrivCount_comp_sub_quot (MonoidHom.inl ↥L ↥B) (ρ.comp π) SU
  haveI : Finite (W ⧸ SU.toSubmodule) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have hq : nontrivCount (SU.quotient.comp (MonoidHom.inl ↥L ↥B)) = 0 := by
    refine nontrivCount_eq_zero_of_trivial _ fun l => ?_
    refine LinearMap.ext fun q => ?_
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show Submodule.Quotient.mk (ρ (π (l, 1)) w) = Submodule.Quotient.mk w
    rw [hLsub, Submodule.Quotient.eq]
    exact hUL (Submodule.subset_span ⟨(l : G), l.2, w, Submodule.mem_top, rfl⟩)
  have hcomp : (ρ.comp π).comp (MonoidHom.inl ↥L ↥B) = ρ.comp L.subtype :=
    MonoidHom.ext fun l => by
      show ρ (π (l, 1)) = ρ l
      rw [hLsub]
  rw [← hcomp]
  omega

end Main


end CFSG.LocalAnalysis.RankThreeUC.S15
