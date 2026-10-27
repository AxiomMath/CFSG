module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6RootSL2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevToral
public import CFSG.RankThree.OddKernel.CentralCoverComponentModels
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4RestLevi
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.CGT.Timmesfeld75.JLemmaSub
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.SubsystemRank
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.E6.NativeTwoA2
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Suz.Simple

public section

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.GLTheoremA

theorem card_le_pow_two_subsystemGroup_e6pair
    {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {i j : Fin TwistTag.E6.tag.rank} (hij : i ≠ j)
    (hcij : Tag.cartan .E6 i j = -1) (hcji : Tag.cartan .E6 j i = -1)
    (hk : ∃ k : Fin TwistTag.E6.tag.rank,
      ¬ (3 : ℤ) ∣ Tag.cartan .E6 i k + 2 * Tag.cartan .E6 j k)
    {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ subsystemGroup TwistTag.E6.tag F ({i, j} : Set (Fin TwistTag.E6.tag.rank)))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  have hpK : (p : F) ≠ 0 := CFSG.StandardType.F4Rest.natCast_ne_zero_of_charTwo hp hp2
  obtain ⟨O, C, hEx⟩ :=
    CFSG.ComponentClassification.CatLeafProof.exists_e6_chevalleyExtras F
  let D := CFSG.LieType.Steinberg.Adjoint.adjDatum
    (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6) F
  let i' : Fin D.rank := i
  let j' : Fin D.rank := j
  have hcij' : D.cartan i' j' = -1 := hcij
  have hcji' : D.cartan j' i' = -1 := hcji
  obtain ⟨k, hk⟩ := hk
  let k' : Fin D.rank := k
  have hk' : ¬ (3 : ℤ) ∣ D.cartan i' k' + 2 * D.cartan j' k' := hk
  obtain ⟨emb, hinj, hpair, -⟩ :=
    CFSG.ClassicalInvolution.WeakCT.exists_sl3Levi
      (D := D) (x := CFSG.LieType.Steinberg.Adjoint.xPar
        (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6))
      hEx rfl (show i' ≠ j' from hij) hcij' hcji' hk'
  let emb' : SL(3, F) →* ModGL TwistTag.E6.tag F :=
    (adjointGroup TwistTag.E6.tag F).subtype.comp emb
  have hinj' : Function.Injective emb' :=
    (adjointGroup TwistTag.E6.tag F).subtype_injective.comp hinj
  have hrootmem : ∀ (γ : Fin D.rank → ℤ), γ ∈ CFSG.Timmesfeld.pairRoots D i' j' →
      ∀ c : F, (adjointGroup TwistTag.E6.tag F).subtype
        (CFSG.LieType.Steinberg.Adjoint.xPar
          (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6) γ c) ∈ emb'.range := by
    intro γ hγ c
    have hγroot : γ ∈ D.roots := hγ.1
    have hxroot : CFSG.LieType.Steinberg.Adjoint.xPar
        (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6) γ c ∈ D.rootGroup γ :=
      ((hEx.param γ hγroot).1 _).2 ⟨c, rfl⟩
    obtain ⟨A, hA⟩ := hpair γ hγ hxroot
    refine ⟨A, ?_⟩
    change (adjointGroup TwistTag.E6.tag F).subtype (emb A) =
      (adjointGroup TwistTag.E6.tag F).subtype
        (CFSG.LieType.Steinberg.Adjoint.xPar
          (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6) γ c)
    rw [hA]
  have hsingle : (CFSG.Timmesfeld.sroot i' : Fin D.rank → ℤ) ∈
      CFSG.Timmesfeld.pairRoots D i' j' := by
    refine ⟨CFSG.Timmesfeld.LevisExtras.single_mem_roots (D := D) i', ?_⟩
    intro k hki hkj
    exact CFSG.Timmesfeld.sroot_of_ne hki
  have hsingle' : (-CFSG.Timmesfeld.sroot i' : Fin D.rank → ℤ) ∈
      CFSG.Timmesfeld.pairRoots D i' j' := by
    refine ⟨CFSG.Timmesfeld.LevisExtras.neg_mem_roots
      (CFSG.Timmesfeld.LevisExtras.single_mem_roots (D := D) i'), ?_⟩
    intro k hki hkj
    simp [CFSG.Timmesfeld.sroot_of_ne hki]
  have hsinglej : (CFSG.Timmesfeld.sroot j' : Fin D.rank → ℤ) ∈
      CFSG.Timmesfeld.pairRoots D i' j' := by
    refine ⟨CFSG.Timmesfeld.LevisExtras.single_mem_roots (D := D) j', ?_⟩
    intro k hki hkj
    exact CFSG.Timmesfeld.sroot_of_ne hkj
  have hsinglej' : (-CFSG.Timmesfeld.sroot j' : Fin D.rank → ℤ) ∈
      CFSG.Timmesfeld.pairRoots D i' j' := by
    refine ⟨CFSG.Timmesfeld.LevisExtras.neg_mem_roots
      (CFSG.Timmesfeld.LevisExtras.single_mem_roots (D := D) j'), ?_⟩
    intro k hki hkj
    simp [CFSG.Timmesfeld.sroot_of_ne hkj]
  have hxUnit : ∀ c : F, xUnit TwistTag.E6.tag F i c ∈ emb'.range := by
    intro c
    have hthis := hrootmem (CFSG.Timmesfeld.sroot i') hsingle c
    have hxeq : (adjointGroup TwistTag.E6.tag F).subtype
        (CFSG.LieType.Steinberg.Adjoint.xPar
          (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6)
          (CFSG.Timmesfeld.sroot i') c) = xUnit TwistTag.E6.tag F i c := by
      change (adjointGroup TwistTag.E6.tag F).subtype
        (CFSG.LieType.Steinberg.Adjoint.xPar
          (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6) (Pi.single i 1) c) = _
      exact (CFSG.ComponentClassification.CatLeafProof.coe_xPar_e6 F i c).1
    rwa [hxeq] at hthis
  have hyUnit : ∀ c : F, yUnit TwistTag.E6.tag F i c ∈ emb'.range := by
    intro c
    have hthis := hrootmem (-CFSG.Timmesfeld.sroot i') hsingle' c
    have hxeq : (adjointGroup TwistTag.E6.tag F).subtype
        (CFSG.LieType.Steinberg.Adjoint.xPar
          (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6)
          (-CFSG.Timmesfeld.sroot i') c) = yUnit TwistTag.E6.tag F i c := by
      change (adjointGroup TwistTag.E6.tag F).subtype
        (CFSG.LieType.Steinberg.Adjoint.xPar
          (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6) (-Pi.single i 1) c) = _
      exact (CFSG.ComponentClassification.CatLeafProof.coe_xPar_e6 F i c).2
    rwa [hxeq] at hthis
  have hxUnitj : ∀ c : F, xUnit TwistTag.E6.tag F j c ∈ emb'.range := by
    intro c
    have hthis := hrootmem (CFSG.Timmesfeld.sroot j') hsinglej c
    have hxeq : (adjointGroup TwistTag.E6.tag F).subtype
        (CFSG.LieType.Steinberg.Adjoint.xPar
          (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6)
          (CFSG.Timmesfeld.sroot j') c) = xUnit TwistTag.E6.tag F j c := by
      change (adjointGroup TwistTag.E6.tag F).subtype
        (CFSG.LieType.Steinberg.Adjoint.xPar
          (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6) (Pi.single j 1) c) = _
      exact (CFSG.ComponentClassification.CatLeafProof.coe_xPar_e6 F j c).1
    rwa [hxeq] at hthis
  have hyUnitj : ∀ c : F, yUnit TwistTag.E6.tag F j c ∈ emb'.range := by
    intro c
    have hthis := hrootmem (-CFSG.Timmesfeld.sroot j') hsinglej' c
    have hxeq : (adjointGroup TwistTag.E6.tag F).subtype
        (CFSG.LieType.Steinberg.Adjoint.xPar
          (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6)
          (-CFSG.Timmesfeld.sroot j') c) = yUnit TwistTag.E6.tag F j c := by
      change (adjointGroup TwistTag.E6.tag F).subtype
        (CFSG.LieType.Steinberg.Adjoint.xPar
          (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6) (-Pi.single j 1) c) = _
      exact (CFSG.ComponentClassification.CatLeafProof.coe_xPar_e6 F j c).2
    rwa [hxeq] at hthis
  have hSle : subsystemGroup TwistTag.E6.tag F
      ({i, j} : Set (Fin TwistTag.E6.tag.rank)) ≤ emb'.range := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨k, hkij, c, rfl | rfl⟩
    · rcases (by simpa using hkij : k = i ∨ k = j) with rfl | rfl
      · exact hxUnit c
      · exact hxUnitj c
    · rcases (by simpa using hkij : k = i ∨ k = j) with rfl | rfl
      · exact hyUnit c
      · exact hyUnitj c
  have hRankSL3 : CFSG.Open.pRank p (⊤ : Subgroup (SL(3, F))) ≤ 2 := by
    haveI : Fact p.Prime := ⟨hp⟩
    have hpF : (p : F) ≠ 0 := CFSG.StandardType.F4Rest.natCast_ne_zero_of_charTwo hp hp2
    have hstated : CFSG.Open.pRank p (StatedSL 3 F) ≤ 2 :=
      CFSG.LocalAnalysis.RankThreeUC.S15.pRank_statedSL_le (F := F) (r := p) (m := 3)
        (by norm_num) hpF
    calc CFSG.Open.pRank p (⊤ : Subgroup (SL(3, F)))
        ≤ CFSG.Open.pRank p ((⊤ : Subgroup (SL(3, F))).map Matrix.SpecialLinearGroup.toGL) :=
          CFSG.SectionRank.pRank_le_map hp.one_lt Matrix.SpecialLinearGroup.toGL
            Matrix.SpecialLinearGroup.toGL_injective ⊤
      _ = CFSG.Open.pRank p (StatedSL 3 F) := by
          rw [CFSG.Open.StatedAPI.statedSL_eq_range_toGL, ← MonoidHom.range_eq_map]
      _ ≤ 2 := hstated
  let eRange : SL(3, F) ≃* ↥emb'.range := MonoidHom.ofInjective hinj'
  have hRankEmb : CFSG.Open.pRank p emb'.range = CFSG.Open.pRank p (⊤ : Subgroup (SL(3, F))) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (emb'.range)]
    exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eRange).symm
  have hRank : CFSG.Open.pRank p (⊤ : Subgroup ↥(subsystemGroup TwistTag.E6.tag F
      ({i, j} : Set (Fin TwistTag.E6.tag.rank)))) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup
      (subsystemGroup TwistTag.E6.tag F ({i, j} : Set (Fin TwistTag.E6.tag.rank)))]
    calc CFSG.Open.pRank p (subsystemGroup TwistTag.E6.tag F ({i, j} : Set _))
        ≤ CFSG.Open.pRank p emb'.range := CFSG.SectionRank.pRank_mono hp.one_lt hSle
      _ = CFSG.Open.pRank p (⊤ : Subgroup (SL(3, F))) := hRankEmb
      _ ≤ 2 := hRankSL3
  have hcard := CFSG.RankThree.OddKernel.card_le_pow_pRank_of_le (p := p) hp hEel hE
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup
    (subsystemGroup TwistTag.E6.tag F ({i, j} : Set (Fin TwistTag.E6.tag.rank)))] at hcard
  exact hcard.trans (Nat.pow_le_pow_right hp.pos hRank)

private theorem card_scalar_subtype_le_one {F : Type} [Field F] [CharP F 2]
    {R : Subgroup ((Fin 2 → F) ≃ₗ[F] (Fin 2 → F))}
    (hR : R ≤ (Matrix.SpecialLinearGroup.toLin' (n := Fin 2) (R := F)).range) :
    Nat.card {x : R // ∃ a : F, ∀ v, (x : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) v = a • v} ≤ 1 := by
  classical
  have scalar_eq_one : ∀ (x : R) (a : F),
      (∀ v, (x : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) v = a • v) → x = 1 := by
    intro x a ha
    let A : Matrix.SpecialLinearGroup (Fin 2) F := Classical.choose (hR x.2)
    have hAx : Matrix.SpecialLinearGroup.toLin' A = x.1 := Classical.choose_spec (hR x.2)
    have hAfun : ∀ v, (Matrix.SpecialLinearGroup.toLin' A : (Fin 2 → F) →ₗ[F] (Fin 2 → F)) v =
        a • v := by
      intro v
      calc (Matrix.SpecialLinearGroup.toLin' A : (Fin 2 → F) →ₗ[F] (Fin 2 → F)) v =
          (x.1 : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) v :=
            congrArg (fun e : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) => e v) hAx
        _ = a • v := ha v
    have hAeq : (Matrix.SpecialLinearGroup.toLin' A : (Fin 2 → F) →ₗ[F] (Fin 2 → F)) =
        a • (1 : (Fin 2 → F) →ₗ[F] (Fin 2 → F)) :=
      LinearMap.ext fun v => by rw [hAfun v]; simp
    let M : Matrix (Fin 2) (Fin 2) F := A
    have hmat : M = Matrix.scalar (Fin 2) a := by
      calc M = LinearMap.toMatrix' (Matrix.toLin' M) := by
            rw [← Matrix.toLin'_symm]
            exact (LinearEquiv.symm_apply_apply _ _).symm
        _ = LinearMap.toMatrix' (a • (1 : (Fin 2 → F) →ₗ[F] (Fin 2 → F))) := by
            exact congrArg LinearMap.toMatrix' hAeq
        _ = Matrix.scalar (Fin 2) a := by
            ext i j
            by_cases hij : i = j
            · subst hij
              simp [Matrix.scalar_apply]
            · simp [Matrix.scalar_apply, hij, Pi.single_eq_of_ne]
    have hdet : a ^ 2 = 1 := by
      have hA := A.2
      change M.det = 1 at hA
      rw [hmat, Matrix.scalar_apply, Matrix.det_diagonal] at hA
      simpa using hA
    have ha1 : a = 1 := by
      have h : (a - 1) ^ 2 = 0 := by
        have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
        rw [sub_sq, hdet, h2]
        ring_nf
        exact h2
      exact sub_eq_zero.1 (sq_eq_zero_iff.1 h)
    refine Subtype.ext ?_
    apply LinearEquiv.ext
    intro v
    calc (x.1 : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) v =
        (Matrix.SpecialLinearGroup.toLin' A : (Fin 2 → F) →ₗ[F] (Fin 2 → F)) v :=
          (congrArg (fun e : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) => e v) hAx).symm
      _ = a • v := hAfun v
      _ = v := by rw [ha1]; simp
  have hsub : Subsingleton {x : R // ∃ a : F, ∀ v,
      (x : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) v = a • v} :=
    ⟨fun x y => Subtype.ext (by rw [scalar_eq_one x.1 x.2.choose x.2.choose_spec,
      scalar_eq_one y.1 y.2.choose y.2.choose_spec])⟩
  have hcard : Nat.card {x : R // ∃ a : F, ∀ v,
      (x : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) v = a • v} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨hsub, ⟨⟨1, ⟨1, by simp⟩⟩⟩⟩
  exact hcard.le

theorem card_le_pow_one_subsystemGroup_e6node
    {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = (2 ^ n) ^ 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hPRL : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (R : Subgroup (V ≃ₗ[F] V)), IsPGroup p R →
      (∀ x ∈ R, ∀ y ∈ R, ∃ a : F, ∀ v, (x * y * x⁻¹ * y⁻¹) v = a • v) →
      (∀ x ∈ R, ∃ a : F, ∀ v, (x ^ p) v = a • v) →
      Nat.card R ≤ p ^ (Module.finrank F V - 1) *
        Nat.card {x : R // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v})
    (i : Fin TwistTag.E6.tag.rank) {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ subsystemGroup TwistTag.E6.tag F {i}) (hEel : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 1 := by
  have hn : 1 ≤ n * 2 := by
    have h2F : 2 ≤ Nat.card F := by
      haveI : Fintype F := Fintype.ofFinite F
      rw [Nat.card_eq_fintype_card]
      have h := Fintype.one_lt_card (α := F)
      omega
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp at hF
      omega
    · omega
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (k := n * 2) hn (by rw [hF, pow_mul])
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  let V := Fin 2 → F
  let e : SL2 F →* ModGL TwistTag.E6.tag F := simpleRootSL2 TwistTag.E6.tag F i
  have hinj : Function.Injective e :=
    CFSG.LieType.Chevalley.E6GraphRadical.simpleRootSL2_injective_of_two h2 i
  have hrange : e.range = subsystemGroup TwistTag.E6.tag F {i} := by
    rw [range_simpleRootSL2, subsystemGroup]
    congr 1
    ext g
    constructor
    · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact ⟨i, by simp, c, Or.inl rfl⟩
      · exact ⟨i, by simp, c, Or.inr rfl⟩
    · rintro ⟨j, hj, c, rfl | rfl⟩
      · rw [Set.mem_singleton_iff] at hj
        subst hj
        exact Or.inl ⟨c, rfl⟩
      · rw [Set.mem_singleton_iff] at hj
        subst hj
        exact Or.inr ⟨c, rfl⟩
  let Et : Subgroup (SL2 F) := E.comap e
  have hEtrange : E ≤ e.range := hrange ▸ hE
  have hEtcard : Nat.card Et = Nat.card E := by
    calc Nat.card Et = Nat.card (Et.map e) := (Subgroup.card_map_of_injective hinj).symm
      _ = Nat.card E := by rw [Subgroup.map_comap_eq_self hEtrange]
  have hEtel : IsElemAbelian p Et := hEel.comap hinj
  let R : Subgroup (V ≃ₗ[F] V) := Et.map (Matrix.SpecialLinearGroup.toLin' (n := Fin 2) (R := F))
  have hRcard : Nat.card R = Nat.card Et :=
    Subgroup.card_map_of_injective Matrix.SpecialLinearGroup.toLin'_injective
  have hRel : IsElemAbelian p R := hEtel.map _
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, ∃ a : F, ∀ v,
      (x * y * x⁻¹ * y⁻¹) v = a • v := by
    intro x hx y hy
    refine ⟨1, fun v => ?_⟩
    have hxy : x * y = y * x :=
      congrArg Subtype.val (hRel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hx1 : x * y * x⁻¹ * y⁻¹ = 1 := by
      rw [hxy]
      group
    rw [hx1]
    simp
  have hRpow : ∀ x ∈ R, ∃ a : F, ∀ v, (x ^ p) v = a • v := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    refine ⟨1, fun v => ?_⟩
    rw [← map_pow, hEtel.2 y hy, map_one]
    simp
  have hbound := hPRL V R hRel.isPGroup hRcomm hRpow
  have hscalar : Nat.card {x : R // ∃ a : F, ∀ v,
      (x : V ≃ₗ[F] V) v = a • v} ≤ 1 :=
    card_scalar_subtype_le_one (Subgroup.map_le_range _ _)
  have hfin : Module.finrank F V = 2 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  calc Nat.card E = Nat.card Et := hEtcard.symm
    _ = Nat.card R := hRcard.symm
    _ ≤ p ^ (Module.finrank F V - 1) * Nat.card {x : R // ∃ a : F, ∀ v,
          (x : V ≃ₗ[F] V) v = a • v} := hbound
    _ ≤ p ^ 1 * 1 := by
        rw [hfin]
        exact Nat.mul_le_mul_left _ hscalar
    _ = p ^ 1 := by rw [mul_one]

theorem eq_one_of_mem_subsystemGroup_singleton_of_centralizes
    {F : Type} [Field F] [Finite F] [CharP F 2] (i : Fin TwistTag.E6.tag.rank)
    {x : ModGL TwistTag.E6.tag F} (hx : x ∈ subsystemGroup TwistTag.E6.tag F {i})
    (hc : ∀ y ∈ subsystemGroup TwistTag.E6.tag F {i}, Commute x y) : x = 1 := by
  have hneg : (-1 : F) = 1 := neg_one_eq_one_iff.2 (ringChar.eq F 2)
  have hcenter : Subgroup.center (SL2 F) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _
      (CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one hneg)
  have hinj : Function.Injective (simpleRootSL2 TwistTag.E6.tag F i) :=
    CFSG.LieType.Chevalley.E6GraphRadical.simpleRootSL2_injective_of_two
      (CharP.cast_eq_zero F 2) i
  have hrange : (simpleRootSL2 TwistTag.E6.tag F i).range =
      subsystemGroup TwistTag.E6.tag F {i} := by
    rw [range_simpleRootSL2, subsystemGroup]
    congr 1
    ext g
    constructor
    · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact ⟨i, by simp, c, Or.inl rfl⟩
      · exact ⟨i, by simp, c, Or.inr rfl⟩
    · rintro ⟨j, hj, c, rfl | rfl⟩
      · rw [Set.mem_singleton_iff] at hj
        subst hj
        exact Or.inl ⟨c, rfl⟩
      · rw [Set.mem_singleton_iff] at hj
        subst hj
        exact Or.inr ⟨c, rfl⟩
  have hxrange : x ∈ (simpleRootSL2 TwistTag.E6.tag F i).range := hrange ▸ hx
  obtain ⟨y, rfl⟩ := hxrange
  have hycenter : y ∈ Subgroup.center (SL2 F) := by
    rw [Subgroup.mem_center_iff]
    intro A
    have h := (hc (simpleRootSL2 TwistTag.E6.tag F i A) (hrange ▸ ⟨A, rfl⟩)).symm.eq
    exact hinj (by simpa [map_mul] using h)
  rw [hcenter, Subgroup.mem_bot] at hycenter
  rw [hycenter, map_one]

variable {F : Type} [Field F]

private theorem transfer_bound {τ : Tag} {K : Type} [Field K] {p k : ℕ}
    {J : Set (Fin τ.rank)}
    (h : ∀ E : Subgroup (ModGL τ K), E ≤ subsystemGroup τ K J → IsElemAbelian p E →
      Nat.card E ≤ p ^ k) :
    ∀ F : Subgroup (subsystemGroup τ K J), IsElemAbelian p F → Nat.card F ≤ p ^ k := by
  intro F hF
  have hF' : IsElemAbelian p (F.map (subsystemGroup τ K J).subtype) := hF.map _
  have hcard : Nat.card (F.map (subsystemGroup τ K J).subtype) = Nat.card F :=
    Subgroup.card_map_of_injective (subsystemGroup τ K J).subtype_injective
  have hle : F.map (subsystemGroup τ K J).subtype ≤ subsystemGroup τ K J := by
    simpa [Subgroup.range_subtype] using Subgroup.map_le_range (subsystemGroup τ K J).subtype F
  rw [← hcard]
  exact h _ hle hF'

private theorem memA (k : Fin 6) (h2 : k ≠ 2) (h4 : k ≠ 4) :
    e6Index k ∈ ({i : Fin Tag.E6.rank | i.val ≠ 2 ∧ i.val ≠ 4} : Set (Fin Tag.E6.rank)) := by
  simp only [e6Index, Set.mem_setOf_eq]
  constructor <;> intro h
  · exact h2 (Fin.ext h)
  · exact h4 (Fin.ext h)

private theorem memA0 : e6Index 0 ∈ ({i : Fin Tag.E6.rank | i.val ≠ 2 ∧ i.val ≠ 4} : Set _) := memA 0 (by decide) (by decide)
private theorem memA1 : e6Index 1 ∈ ({i : Fin Tag.E6.rank | i.val ≠ 2 ∧ i.val ≠ 4} : Set _) := memA 1 (by decide) (by decide)
private theorem memA3 : e6Index 3 ∈ ({i : Fin Tag.E6.rank | i.val ≠ 2 ∧ i.val ≠ 4} : Set _) := memA 3 (by decide) (by decide)
private theorem memA5 : e6Index 5 ∈ ({i : Fin Tag.E6.rank | i.val ≠ 2 ∧ i.val ≠ 4} : Set _) := memA 5 (by decide) (by decide)

private theorem support_0_1 : ∀ γ ∈ rootFinset (Tag.E6),
    (∀ k, k ≠ e6Index 0 → k ≠ e6Index 1 → γ k = 0) →
      γ (e6Index 0) = 0 ∨ γ (e6Index 1) = 0 := by decide +kernel
private theorem support_0_3 : ∀ γ ∈ rootFinset (Tag.E6),
    (∀ k, k ≠ e6Index 0 → k ≠ e6Index 3 → γ k = 0) →
      γ (e6Index 0) = 0 ∨ γ (e6Index 3) = 0 := by decide +kernel
private theorem support_0_5 : ∀ γ ∈ rootFinset (Tag.E6),
    (∀ k, k ≠ e6Index 0 → k ≠ e6Index 5 → γ k = 0) →
      γ (e6Index 0) = 0 ∨ γ (e6Index 5) = 0 := by decide +kernel
private theorem support_1_5 : ∀ γ ∈ rootFinset (Tag.E6),
    (∀ k, k ≠ e6Index 1 → k ≠ e6Index 5 → γ k = 0) →
      γ (e6Index 1) = 0 ∨ γ (e6Index 5) = 0 := by decide +kernel
private theorem support_3_5 : ∀ γ ∈ rootFinset (Tag.E6),
    (∀ k, k ≠ e6Index 3 → k ≠ e6Index 5 → γ k = 0) →
      γ (e6Index 3) = 0 ∨ γ (e6Index 5) = 0 := by decide +kernel

theorem e6_pair_support (a b : Fin 6) (hab : a ≠ b)
    (h : ∀ γ ∈ rootFinset (Tag.E6),
      (∀ k, k ≠ e6Index a → k ≠ e6Index b → γ k = 0) →
        γ (e6Index a) = 0 ∨ γ (e6Index b) = 0) :
    e6Index a ≠ e6Index b ∧ ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot (Tag.E6) γ →
      (∀ k, k ≠ e6Index a → k ≠ e6Index b → γ k = 0) →
        γ (e6Index a) = 0 ∨ γ (e6Index b) = 0 :=
  ⟨fun hh => hab (Fin.ext (by simpa [e6Index] using congrArg Fin.val hh)),
    fun γ hγ hk => h γ (mem_rootFinset.2 hγ) hk⟩

theorem card_le_pow_four_subsystemGroup_e6A1A2
    {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = (2 ^ n) ^ 2)
    (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    (hPRL : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (R : Subgroup (V ≃ₗ[F] V)), IsPGroup p R →
      (∀ x ∈ R, ∀ y ∈ R, ∃ a : F, ∀ v, (x * y * x⁻¹ * y⁻¹) v = a • v) →
      (∀ x ∈ R, ∃ a : F, ∀ v, (x ^ p) v = a • v) →
      Nat.card R ≤ p ^ (Module.finrank F V - 1) *
        Nat.card {x : R // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v})
    {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hEel : IsElemAbelian p E)
    (hE : E ≤ subsystemGroup TwistTag.E6.tag F {i | i.val ≠ 2 ∧ i.val ≠ 4} ⊓
      twistedFixedGroup TwistTag.E6 F σ.toRingHom) :
    Nat.card E ≤ p ^ 4 := by
  let L0 := subsystemGroup Tag.E6 F ({e6Index 0} : Set (Fin Tag.E6.rank))
  let L13 := subsystemGroup Tag.E6 F ({e6Index 1, e6Index 3} : Set (Fin Tag.E6.rank))
  let L5 := subsystemGroup Tag.E6 F ({e6Index 5} : Set (Fin Tag.E6.rank))
  let B := subsystemGroup Tag.E6 F
    (({e6Index 1, e6Index 3} : Set (Fin Tag.E6.rank)) ∪ {e6Index 5})
  let LA := subsystemGroup Tag.E6 F
    ({i : Fin Tag.E6.rank | i.val ≠ 2 ∧ i.val ≠ 4} : Set (Fin Tag.E6.rank))
  have hB : B = L13 ⊔ L5 := by
    rw [show B = subsystemGroup Tag.E6 F
      (({e6Index 1, e6Index 3} : Set _) ∪ {e6Index 5}) from rfl, CFSG.StandardType.F4Rest.subsystemGroup_union]
  have hcomm0B : ∀ x ∈ L0, ∀ y ∈ B, Commute x y := by
    refine commute_subsystemGroup ?_
    intro a ha b hb
    simp only [Set.mem_singleton_iff] at ha
    subst ha
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with (rfl | rfl) | rfl
    · exact e6_pair_support 0 1 (by decide) support_0_1
    · exact e6_pair_support 0 3 (by decide) support_0_3
    · exact e6_pair_support 0 5 (by decide) support_0_5
  have hcomm13_5 : ∀ x ∈ L13, ∀ y ∈ L5, Commute x y := by
    refine commute_subsystemGroup ?_
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    subst hb
    rcases ha with rfl | rfl
    · exact e6_pair_support 1 5 (by decide) support_1_5
    · exact e6_pair_support 3 5 (by decide) support_3_5
  haveI : CharP F 2 := by
    have hn : 1 ≤ n * 2 := by
      have h2F : 2 ≤ Nat.card F := by
        haveI : Fintype F := Fintype.ofFinite F
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card (α := F)
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at hF; omega
      · omega
    exact CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (k := n * 2) hn (by rw [hF, pow_mul])
  have hinf0B : L0 ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact eq_one_of_mem_subsystemGroup_singleton_of_centralizes (F := F) (i := e6Index 0)
      hx.1 (fun y hy => (hcomm0B y hy x hx.2).symm)
  have hinf13_5 : L13 ⊓ L5 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact eq_one_of_mem_subsystemGroup_singleton_of_centralizes (F := F) (i := e6Index 5)
      hx.2 (fun y hy => hcomm13_5 x hx.1 y hy)
  have hp_one : ¬ p ∣ Nat.card ↥(L0 ⊓ B) := by
    rw [hinf0B]
    simp [hp.ne_one]
  have hp_thirteen_five : ¬ p ∣ Nat.card ↥(L13 ⊓ L5) := by
    rw [hinf13_5]
    simp [hp.ne_one]
  have hL0_bound : ∀ G : Subgroup L0, IsElemAbelian p G → Nat.card G ≤ p ^ 1 := by
    refine transfer_bound (J := ({e6Index 0} : Set (Fin Tag.E6.rank))) ?_
    intro G hG hGel
    exact card_le_pow_one_subsystemGroup_e6node (F := F) (n := n) hF hp hp2 hPRL
      (e6Index 0) hG hGel
  have hL5_bound : ∀ G : Subgroup L5, IsElemAbelian p G → Nat.card G ≤ p ^ 1 := by
    refine transfer_bound (J := ({e6Index 5} : Set (Fin Tag.E6.rank))) ?_
    intro G hG hGel
    exact card_le_pow_one_subsystemGroup_e6node (F := F) (n := n) hF hp hp2 hPRL
      (e6Index 5) hG hGel
  have hL13_bound : ∀ G : Subgroup L13, IsElemAbelian p G → Nat.card G ≤ p ^ 2 := by
    refine transfer_bound (J := ({e6Index 1, e6Index 3} : Set (Fin Tag.E6.rank))) ?_
    intro G hG hGel
    exact card_le_pow_two_subsystemGroup_e6pair (F := F) hp hp2
      (i := e6Index 1) (j := e6Index 3)
      (by intro h; have := congrArg Fin.val h; simp [e6Index] at this)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hG hGel
  have hB_bound : ∀ G : Subgroup B, IsElemAbelian p G → Nat.card G ≤ p ^ 3 := by
    refine transfer_bound (J := (({e6Index 1, e6Index 3} : Set (Fin Tag.E6.rank)) ∪ {e6Index 5})) ?_
    intro G hG hGel
    show Nat.card G ≤ p ^ 3
    rw [show subsystemGroup Tag.E6 F (({e6Index 1, e6Index 3} : Set (Fin Tag.E6.rank)) ∪ {e6Index 5}) = L13 ⊔ L5 from hB] at hG
    exact card_le_pow_add_of_le_sup_of_not_dvd_inf hp hcomm13_5 hp_thirteen_five
      hL13_bound hL5_bound hG hGel
  let E' : Subgroup (ModGL Tag.E6 F) := E
  have hE' : E' ≤ L0 ⊔ B := by
    have hLAeq : LA = L0 ⊔ B := by
      refine le_antisymm ?_ ?_
      · rw [show LA = subsystemGroup Tag.E6 F
          ({i : Fin Tag.E6.rank | i.val ≠ 2 ∧ i.val ≠ 4} : Set _) from rfl, subsystemGroup]
        refine (Subgroup.closure_le _).2 ?_
        rintro g ⟨i, hi, c, rfl | rfl⟩
        · have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 3 ∨ i.val = 5 := by
            have h2 : i.val ≠ 2 := hi.1
            have h4 : i.val ≠ 4 := hi.2
            have hlt : i.val < 6 := i.isLt
            omega
          rcases hv with h | h | h | h
          · rw [show i = e6Index 0 from Fin.ext h]
            exact Subgroup.mem_sup_left (xUnit_mem_subsystemGroup (by simp [support13, support56]) c)
          · rw [show i = e6Index 1 from Fin.ext h]
            exact Subgroup.mem_sup_right (xUnit_mem_subsystemGroup (by simp [support13, support56]) c)
          · rw [show i = e6Index 3 from Fin.ext h]
            exact Subgroup.mem_sup_right (xUnit_mem_subsystemGroup (by simp [support13, support56]) c)
          · rw [show i = e6Index 5 from Fin.ext h]
            exact Subgroup.mem_sup_right (xUnit_mem_subsystemGroup (by simp [support13, support56]) c)
        · have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 3 ∨ i.val = 5 := by
            have h2 : i.val ≠ 2 := hi.1
            have h4 : i.val ≠ 4 := hi.2
            have hlt : i.val < 6 := i.isLt
            omega
          rcases hv with h | h | h | h
          · rw [show i = e6Index 0 from Fin.ext h]
            exact Subgroup.mem_sup_left (yUnit_mem_subsystemGroup (by simp [support13, support56]) c)
          · rw [show i = e6Index 1 from Fin.ext h]
            exact Subgroup.mem_sup_right (yUnit_mem_subsystemGroup (by simp [support13, support56]) c)
          · rw [show i = e6Index 3 from Fin.ext h]
            exact Subgroup.mem_sup_right (yUnit_mem_subsystemGroup (by simp [support13, support56]) c)
          · rw [show i = e6Index 5 from Fin.ext h]
            exact Subgroup.mem_sup_right (yUnit_mem_subsystemGroup (by simp [support13, support56]) c)
      · refine sup_le ?_ ?_
        · refine CFSG.StandardType.F4Rest.subsystemGroup_mono ?_
          intro i hi
          simp only [Set.mem_singleton_iff] at hi
          subst hi
          exact memA0
        · refine CFSG.StandardType.F4Rest.subsystemGroup_mono ?_
          intro i hi
          simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
          rcases hi with (rfl | rfl) | rfl
          · exact memA1
          · exact memA3
          · exact memA5
    have hE_LA : E' ≤ LA := hE.trans inf_le_left
    rw [hLAeq] at hE_LA
    exact hE_LA
  have hEel' : IsElemAbelian p E' := hEel
  calc Nat.card E = Nat.card E' := rfl
    _ ≤ p ^ (1 + 3) := card_le_pow_add_of_le_sup_of_not_dvd_inf hp hcomm0B hp_one
        hL0_bound hB_bound hE' hEel'
    _ = p ^ 4 := by norm_num

variable {F : Type} [Field F] [Finite F] [CharP F 2]

private lemma toLin'_eq_scalar {A : Matrix.SpecialLinearGroup (Fin 3) F} {l : F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) l) (v : Fin 3 → F) :
    (Matrix.SpecialLinearGroup.toLin' A : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) v = l • v := by
  change (Matrix.toLin' (A : Matrix (Fin 3) (Fin 3) F)) v = l • v
  rw [Matrix.toLin'_apply, hA]
  simp [Matrix.scalar_apply]

private theorem center_N1_le_Z0 :
    Subgroup.center (subsystemGroup Tag.E6 F support13) ≤
    (subsystemGroup Tag.E6 F support13 ⊓ subsystemGroup Tag.E6 F support56).subgroupOf
      (subsystemGroup Tag.E6 F support13) := by
  classical
  intro g hg
  rw [mem_center_Q₁_iff] at hg
  obtain ⟨u, hu, hgu⟩ := hg
  let g2 : subsystemGroup Tag.E6 F support56 :=
    ⟨e6TorusPair (e6Index 4) (e6Index 5) u (u ^ 2),
      e6TorusPair_mem_subsystemGroup _ _ _ _⟩
  have hg2center : g2 ∈ Subgroup.center (subsystemGroup Tag.E6 F support56) :=
    (mem_center_Q₂_iff (K := F) g2).2 ⟨u, hu, rfl⟩
  have hg2mem : (g2 : ModGL Tag.E6 F) ∈ subsystemGroup Tag.E6 F support56 := g2.2
  refine Subgroup.mem_subgroupOf.2 ⟨g.2, ?_⟩
  have hcomm := (commute_Q₁_Q₂ (K := F) g.2 g2.2).eq
  have hprod : (g2 : ModGL Tag.E6 F) * (g : ModGL Tag.E6 F) = 1 := by
    rw [← hcomm, hgu]
    exact e6TorusPair_center_mul hu
  have hprod' : (g : ModGL Tag.E6 F) * (g2 : ModGL Tag.E6 F) = 1 := by
    rw [hcomm]; exact hprod
  have hg_eq : (g : ModGL Tag.E6 F) = (g2 : ModGL Tag.E6 F)⁻¹ :=
    eq_inv_of_mul_eq_one_left hprod'
  rw [hg_eq]
  exact Subgroup.inv_mem _ hg2mem

private theorem a2Equiv_center_scalar (z : subsystemGroup Tag.E6 F support13)
    (hz : z ∈ Subgroup.center (subsystemGroup Tag.E6 F support13)) :
    ∃ l : F, l ^ 3 = 1 ∧
      (((a2Equiv₁ F) z : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        Matrix.scalar (Fin 3) l := by
  let A : Matrix.SpecialLinearGroup (Fin 3) F := (a2Equiv₁ F) z
  have hAc : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
    rw [Subgroup.mem_center_iff]
    intro X
    obtain ⟨y, rfl⟩ := (a2Equiv₁ F).surjective X
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
  obtain ⟨l, hl, hlA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hAc
  exact ⟨l, by simpa using hl, hlA.symm⟩

theorem card_inf_A2_A2_dvd_three :
    Nat.card ↥(subsystemGroup Tag.E6 F support13 ⊓
      subsystemGroup Tag.E6 F support56) ∣ 3 := by
  let N1 := subsystemGroup Tag.E6 F support13
  let N2 := subsystemGroup Tag.E6 F support56
  let Z0 := N1 ⊓ N2
  let Z1 : Subgroup ↥N1 := Z0.subgroupOf N1
  have hZ0centerN1 : Z1 ≤ Subgroup.center ↥N1 := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hzZ0 : ((z : ↥N1) : ModGL Tag.E6 F) ∈ Z0 := Subgroup.mem_subgroupOf.1 hz
    have hzN2 : ((z : ↥N1) : ModGL Tag.E6 F) ∈ N2 := (Subgroup.mem_inf.1 hzZ0).2
    exact Subtype.ext (by
      show (g : ↥N1).1 * (z : ↥N1).1 = (z : ↥N1).1 * (g : ↥N1).1
      exact (commute_Q₁_Q₂ (K := F) g.2 hzN2).eq)
  have hZ0centerSL3 : Z1.map (a2Equiv₁ F).toMonoidHom ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro X
    obtain ⟨g, rfl⟩ := (a2Equiv₁ F).surjective X
    show (a2Equiv₁ F) g * (a2Equiv₁ F) z = (a2Equiv₁ F) z * (a2Equiv₁ F) g
    rw [← map_mul, ← map_mul]
    rw [Subgroup.mem_center_iff.1 (hZ0centerN1 hz) g]
  have hcardmap : Nat.card ↥(Z1.map (a2Equiv₁ F).toMonoidHom) = Nat.card ↥Z1 :=
    Subgroup.card_map_of_injective (a2Equiv₁ F).injective
  have hdvd : Nat.card ↥Z1 ∣ Nat.card ↥(Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) :=
    hcardmap ▸ Subgroup.card_dvd_of_le hZ0centerSL3
  have hcenter : Nat.card ↥(Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) ∣ 3 :=
    (CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (n := 3) (by norm_num) F).trans
      (Nat.gcd_dvd_left 3 (Nat.card F - 1))
  have hZ1 : Nat.card ↥Z1 = Nat.card ↥Z0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Z0 ≤ N1)).toEquiv
  rw [hZ1] at hdvd
  exact hdvd.trans hcenter

private theorem Z0_le_center_N1 :
    (subsystemGroup Tag.E6 F support13 ⊓ subsystemGroup Tag.E6 F support56).subgroupOf
      (subsystemGroup Tag.E6 F support13) ≤
    Subgroup.center (subsystemGroup Tag.E6 F support13) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hzZ0 : ((z : ↥(subsystemGroup Tag.E6 F support13)) : ModGL Tag.E6 F) ∈
      subsystemGroup Tag.E6 F support13 ⊓ subsystemGroup Tag.E6 F support56 :=
    Subgroup.mem_subgroupOf.1 hz
  have hzN2 : ((z : ↥(subsystemGroup Tag.E6 F support13)) : ModGL Tag.E6 F) ∈
      subsystemGroup Tag.E6 F support56 := (Subgroup.mem_inf.1 hzZ0).2
  exact Subtype.ext (by
    show (g : ↥(subsystemGroup Tag.E6 F support13)).1 *
        (z : ↥(subsystemGroup Tag.E6 F support13)).1 =
      (z : ↥(subsystemGroup Tag.E6 F support13)).1 *
        (g : ↥(subsystemGroup Tag.E6 F support13)).1
    exact (commute_Q₁_Q₂ (K := F) g.2 hzN2).eq)

private theorem card_le_pow_four_E0_p3 {E0 : Subgroup (ModGL Tag.E6 F)}
    (hPRL : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (R : Subgroup (V ≃ₗ[F] V)), IsPGroup 3 R →
      (∀ x ∈ R, ∀ y ∈ R, ∃ a : F, ∀ v, (x * y * x⁻¹ * y⁻¹) v = a • v) →
      (∀ x ∈ R, ∃ a : F, ∀ v, (x ^ 3) v = a • v) →
      Nat.card R ≤ 3 ^ (Module.finrank F V - 1) *
        Nat.card {x : R // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v})
    (hE0 : E0 ≤ subsystemGroup Tag.E6 F support13 ⊔ subsystemGroup Tag.E6 F support56)
    (hE0el : IsElemAbelian 3 E0) :
    Nat.card E0 ≤ 3 ^ 4 := by
  classical
  let N1 := subsystemGroup Tag.E6 F support13
  let N2 := subsystemGroup Tag.E6 F support56
  let N := N1 ⊔ N2
  let Z0 := N1 ⊓ N2
  let N2' : Subgroup ↥N := N2.subgroupOf N
  have hN2'normal : N2'.Normal := by
    have hNle : N ≤ Subgroup.normalizer (N2 : Set (ModGL Tag.E6 F)) := by
      refine sup_le ?_ Subgroup.le_normalizer
      refine Subgroup.le_normalizer_iff.2 ?_
      intro a ha b hb
      have hab : a * b * a⁻¹ = b := by
        rw [(commute_Q₁_Q₂ (K := F) ha hb).eq]
        group
      rw [hab]
      exact hb
    refine Subgroup.Normal.mk ?_
    intro n hn m
    have hm : ((m : ↥N) : ModGL Tag.E6 F) ∈
        Subgroup.normalizer (N2 : Set (ModGL Tag.E6 F)) := hNle m.2
    exact (Subgroup.mem_normalizer_iff.1 hm ((n : ↥N) : ModGL Tag.E6 F)).mp
      (Subgroup.mem_subgroupOf.1 hn)
  letI : N2'.Normal := hN2'normal
  let π : ↥N →* (↥N ⧸ N2') := QuotientGroup.mk' N2'
  let S : Subgroup ↥N := E0.subgroupOf N
  let P : Subgroup (↥N ⧸ N2') := S.map π
  let φ : ↥N1 →* (↥N ⧸ N2') :=
    π.comp (Subgroup.inclusion (le_sup_left : N1 ≤ N1 ⊔ N2))
  have hφker : φ.ker = Z0.subgroupOf N1 := by
    ext x
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk' N2') ((Subgroup.inclusion (le_sup_left : N1 ≤ N1 ⊔ N2) x : ↥N)) = 1 ↔
      (x : ↥N1) ∈ Z0.subgroupOf N1
    constructor
    · intro hx
      have hxN : (Subgroup.inclusion (le_sup_left : N1 ≤ N1 ⊔ N2) x : ↥N) ∈ N2' :=
        (QuotientGroup.eq_one_iff _).1 hx
      exact Subgroup.mem_subgroupOf.2 ⟨x.2, Subgroup.mem_subgroupOf.1 hxN⟩
    · intro hx
      apply (QuotientGroup.eq_one_iff _).2
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hx).2
  have hPle : P ≤ φ.range := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    have hxN : ((x : ↥N) : ModGL Tag.E6 F) ∈ N1 ⊔ N2 := hE0 (Subgroup.mem_subgroupOf.1 hx)
    obtain ⟨a, ha, b, hb, hab⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
        (fun a ha b hb => (commute_Q₁_Q₂ (K := F) ha hb).eq) hxN
    refine ⟨⟨a, ha⟩, ?_⟩
    simp only [φ, MonoidHom.comp_apply, Subgroup.coe_inclusion]
    change π ⟨a, (le_sup_left : N1 ≤ N1 ⊔ N2) ha⟩ = π (x : ↥N)
    have hxeq : (x : ↥N) = ⟨a * b,
        N.mul_mem ((le_sup_left : N1 ≤ N1 ⊔ N2) ha)
          ((le_sup_right : N2 ≤ N1 ⊔ N2) hb)⟩ := Subtype.ext hab.symm
    have hbker : π ⟨b, (le_sup_right : N2 ≤ N1 ⊔ N2) hb⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hb)
    rw [hxeq, show (⟨a * b,
        N.mul_mem ((le_sup_left : N1 ≤ N1 ⊔ N2) ha)
          ((le_sup_right : N2 ≤ N1 ⊔ N2) hb)⟩ : ↥N) =
        ⟨a, (le_sup_left : N1 ≤ N1 ⊔ N2) ha⟩ *
          ⟨b, (le_sup_right : N2 ≤ N1 ⊔ N2) hb⟩ from rfl,
      map_mul, hbker, mul_one]
  let R : Subgroup ↥N1 := P.comap φ
  have hRsurj : Function.Surjective (fun r : R => (⟨φ (r : ↥N1), r.2⟩ : P)) := by
    intro p
    obtain ⟨a, ha⟩ := hPle p.2
    refine ⟨⟨a, ?_⟩, ?_⟩
    · show φ a ∈ P
      rw [ha]
      exact p.2
    · exact Subtype.ext ha
  let ψ : R →* P :=
    { toFun := fun r => ⟨φ (r : ↥N1), r.2⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun x y => Subtype.ext (map_mul φ (x : ↥N1) (y : ↥N1)) }
  have hψsurj : Function.Surjective ψ := hRsurj
  have hψker : ψ.ker = (Z0.subgroupOf N1).subgroupOf R := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : φ (r : ↥N1) = 1 := congrArg Subtype.val h
      have h2 : (r : ↥N1) ∈ φ.ker := MonoidHom.mem_ker.2 h1
      rwa [hφker] at h2
    · intro h
      have h2 : (r : ↥N1) ∈ φ.ker := by rwa [hφker]
      exact Subtype.ext (MonoidHom.mem_ker.1 h2)
  have hRcard : Nat.card ↥R = Nat.card ↥P * Nat.card ↥Z0 := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hψker, MonoidHom.range_eq_top.2 hψsurj, Subgroup.card_top] at h
    have hZ0R : (Z0.subgroupOf N1) ≤ R := by
      intro z hz
      show φ (z : ↥N1) ∈ P
      have hz1 : φ (z : ↥N1) = 1 := by
        rw [← MonoidHom.mem_ker, hφker]
        exact hz
      rw [hz1]
      exact P.one_mem
    have hZ2 : Nat.card ↥((Z0.subgroupOf N1).subgroupOf R) = Nat.card ↥(Z0.subgroupOf N1) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ0R).toEquiv
    have hZ : Nat.card ↥(Z0.subgroupOf N1) = Nat.card ↥Z0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Z0 ≤ N1)).toEquiv
    rw [hZ2, hZ] at h
    rw [mul_comm] at h
    exact h.symm
  have hP_el : IsElemAbelian 3 P := (hE0el.subgroupOf N).map π
  obtain ⟨k, hk⟩ := hP_el.isPGroup.exists_card_eq
  have hZ0dvd : Nat.card ↥Z0 ∣ 3 := card_inf_A2_A2_dvd_three (F := F)
  obtain ⟨z, hz⟩ : ∃ z, Nat.card ↥Z0 = 3 ^ z := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hZ0dvd with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  have hR_pgroup : IsPGroup 3 ↥R := by
    refine IsPGroup.of_card (n := k + z) ?_
    rw [hRcard, hk, hz, ← pow_add]
  let V := Fin 3 → F
  let e : ↥N1 →* (V ≃ₗ[F] V) :=
    (Matrix.SpecialLinearGroup.toLin' (n := Fin 3) (R := F)).comp (a2Equiv₁ F).toMonoidHom
  have he_inj : Function.Injective e :=
    Matrix.SpecialLinearGroup.toLin'_injective.comp (a2Equiv₁ F).injective
  let Slin : Subgroup (V ≃ₗ[F] V) := R.map e
  have hS_pgroup : IsPGroup 3 ↥Slin := hR_pgroup.map e
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R,
      (x * y * x⁻¹ * y⁻¹) ∈ Z0.subgroupOf N1 := by
    intro x hx y hy
    have hφ : φ (x * y * x⁻¹ * y⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      have hcommP : Commute (⟨φ x, hx⟩ : P) (⟨φ y, hy⟩ : P) :=
        hP_el.1.is_comm.comm _ _
      have hEq : φ x * φ y = φ y * φ x := congrArg Subtype.val hcommP.eq
      rw [hEq, mul_inv_cancel_right, mul_inv_cancel]
    rw [← MonoidHom.mem_ker, hφker] at hφ
    exact hφ
  have hRpow : ∀ x ∈ R, (x ^ 3) ∈ Z0.subgroupOf N1 := by
    intro x hx
    have hφ : φ (x ^ 3) = 1 := by
      rw [map_pow]
      have hx3 : (φ x) ^ 3 = 1 := hP_el.2 (φ x) hx
      exact hx3
    rw [← MonoidHom.mem_ker, hφker] at hφ
    exact hφ
  have hcomm_scalar : ∀ x ∈ Slin, ∀ y ∈ Slin, ∃ a : F, ∀ v,
      (x * y * x⁻¹ * y⁻¹) v = a • v := by
    intro x hx y hy
    obtain ⟨rx, hrx, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨ry, hry, rfl⟩ := Subgroup.mem_map.1 hy
    let z1 : ↥N1 := rx * ry * rx⁻¹ * ry⁻¹
    have hz : z1 ∈ Z0.subgroupOf N1 := hRcomm rx hrx ry hry
    have hzcenter : z1 ∈ Subgroup.center ↥N1 := Z0_le_center_N1 hz
    obtain ⟨l, hl, hlA⟩ := a2Equiv_center_scalar z1 hzcenter
    refine ⟨l, fun v => ?_⟩
    have hmul : e rx * e ry * (e rx)⁻¹ * (e ry)⁻¹ = e z1 := by
      change e rx * e ry * (e rx)⁻¹ * (e ry)⁻¹ = e (rx * ry * rx⁻¹ * ry⁻¹)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [hmul]
    change (Matrix.SpecialLinearGroup.toLin' ((a2Equiv₁ F) z1)) v = l • v
    exact toLin'_eq_scalar hlA v
  have hpow_scalar : ∀ x ∈ Slin, ∃ a : F, ∀ v, (x ^ 3) v = a • v := by
    intro x hx
    obtain ⟨rx, hrx, rfl⟩ := Subgroup.mem_map.1 hx
    let z1 : ↥N1 := rx ^ 3
    have hz : z1 ∈ Z0.subgroupOf N1 := hRpow rx hrx
    have hzcenter : z1 ∈ Subgroup.center ↥N1 := Z0_le_center_N1 hz
    obtain ⟨l, hl, hlA⟩ := a2Equiv_center_scalar z1 hzcenter
    refine ⟨l, fun v => ?_⟩
    have hmul : e rx ^ 3 = e z1 := by
      change e rx ^ 3 = e (rx ^ 3)
      rw [map_pow]
    rw [hmul]
    change (Matrix.SpecialLinearGroup.toLin' ((a2Equiv₁ F) z1)) v = l • v
    exact toLin'_eq_scalar hlA v
  have hscalar_le : Nat.card {x : Slin // ∃ a : F, ∀ v,
      (x : V ≃ₗ[F] V) v = a • v} ≤ Nat.card ↥Z0 := by
    classical
    let f : {x : Slin // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v} → ↥Z0 :=
      fun x => by
        let r : ↥N1 := Classical.choose (Subgroup.mem_map.1 x.1.2)
        have hr : r ∈ R := (Classical.choose_spec (Subgroup.mem_map.1 x.1.2)).1
        have hxr : e r = x.1 := (Classical.choose_spec (Subgroup.mem_map.1 x.1.2)).2
        have hcent : r ∈ Subgroup.center (subsystemGroup Tag.E6 F support13) := by
          rw [Subgroup.mem_center_iff]
          intro g
          have hscalar : ∃ a : F, ∀ v, (e r : V ≃ₗ[F] V) v = a • v := by
            simpa [hxr] using x.2
          obtain ⟨a, ha⟩ := hscalar
          have hlin : (Matrix.SpecialLinearGroup.toLin' ((a2Equiv₁ F) r) :
              (V →ₗ[F] V)) = a • (1 : V →ₗ[F] V) := by
            apply LinearMap.ext
            intro v
            change (Matrix.SpecialLinearGroup.toLin' ((a2Equiv₁ F) r)) v = a • v
            exact ha v
          have hAcomm : (a2Equiv₁ F) r * (a2Equiv₁ F) g = (a2Equiv₁ F) g * (a2Equiv₁ F) r := by
            apply Matrix.SpecialLinearGroup.toLin'_injective
            apply LinearEquiv.ext
            intro v
            rw [map_mul, map_mul]
            change (Matrix.SpecialLinearGroup.toLin' ((a2Equiv₁ F) r) :
              (V ≃ₗ[F] V)) ((Matrix.SpecialLinearGroup.toLin' ((a2Equiv₁ F) g) :
                (V ≃ₗ[F] V)) v) =
              (Matrix.SpecialLinearGroup.toLin' ((a2Equiv₁ F) g) :
                (V ≃ₗ[F] V)) ((Matrix.SpecialLinearGroup.toLin' ((a2Equiv₁ F) r) :
                  (V ≃ₗ[F] V)) v)
            have hAr : (Matrix.SpecialLinearGroup.toLin' ((a2Equiv₁ F) r) :
                V →ₗ[F] V) = a • (1 : V →ₗ[F] V) := hlin
            have hAv : ∀ w : V, (Matrix.SpecialLinearGroup.toLin' ((a2Equiv₁ F) r) :
                (V ≃ₗ[F] V)) w = a • w := by
              intro w
              change (Matrix.SpecialLinearGroup.toLin' ((a2Equiv₁ F) r) :
                V →ₗ[F] V) w = a • w
              rw [hAr]; simp
            rw [hAv, hAv, map_smul]
          have hg : (a2Equiv₁ F) (g * r) = (a2Equiv₁ F) (r * g) := by
            rw [map_mul, map_mul]
            exact hAcomm.symm
          exact (a2Equiv₁ F).injective hg
        exact ⟨r, Subgroup.mem_subgroupOf.1 (center_N1_le_Z0 hcent)⟩
    refine Nat.card_le_card_of_injective f ?_
    intro x y hxy
    have hxr : e (Classical.choose (Subgroup.mem_map.1 x.1.2)) = x.1 :=
      (Classical.choose_spec (Subgroup.mem_map.1 x.1.2)).2
    have hyr : e (Classical.choose (Subgroup.mem_map.1 y.1.2)) = y.1 :=
      (Classical.choose_spec (Subgroup.mem_map.1 y.1.2)).2
    have hval : (f x : ↥Z0).1 = (f y : ↥Z0).1 := congrArg Subtype.val hxy
    have hxval : (f x : ↥Z0).1 =
        ((Classical.choose (Subgroup.mem_map.1 x.1.2) : ↥N1) : ModGL Tag.E6 F) := by
      dsimp only [f]
    have hyval : (f y : ↥Z0).1 =
        ((Classical.choose (Subgroup.mem_map.1 y.1.2) : ↥N1) : ModGL Tag.E6 F) := by
      dsimp only [f]
    rw [hxval, hyval] at hval
    have hN1 : (Classical.choose (Subgroup.mem_map.1 x.1.2) : ↥N1) =
        (Classical.choose (Subgroup.mem_map.1 y.1.2) : ↥N1) := Subtype.ext hval
    refine Subtype.ext (Subtype.ext ?_)
    calc x.1 = e (Classical.choose (Subgroup.mem_map.1 x.1.2)) := hxr.symm
      _ = e (Classical.choose (Subgroup.mem_map.1 y.1.2)) := by rw [hN1]
      _ = y.1 := hyr
  have hbound := hPRL V Slin hS_pgroup hcomm_scalar hpow_scalar
  have hfin : Module.finrank F V = 3 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hScalar3 : Nat.card {x : Slin // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v} ≤
      Nat.card ↥Z0 := hscalar_le
  have hZ0le3 : Nat.card ↥Z0 ≤ 3 := Nat.le_of_dvd (by norm_num) hZ0dvd
  have hSboundZ : Nat.card Slin ≤ 3 ^ 2 * Nat.card ↥Z0 := by
    calc Nat.card Slin ≤ 3 ^ (Module.finrank F V - 1) *
        Nat.card {x : Slin // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v} := hbound
      _ ≤ 3 ^ 2 * Nat.card ↥Z0 := by
          rw [hfin]
          exact Nat.mul_le_mul_left _ hscalar_le
  have hScard : Nat.card Slin = Nat.card ↥R := Subgroup.card_map_of_injective he_inj
  have hP9 : Nat.card ↥P ≤ 9 := by
    have hRle : Nat.card ↥R ≤ 3 ^ 2 * Nat.card ↥Z0 := hScard ▸ hSboundZ
    have hZ0pos : 0 < Nat.card ↥Z0 := Nat.card_pos
    have hmul : Nat.card ↥P * Nat.card ↥Z0 ≤ 3 ^ 2 * Nat.card ↥Z0 := by
      rw [← hRcard]
      exact hRle
    have := Nat.le_of_mul_le_mul_right hmul hZ0pos
    simpa [pow_two] using this
  have hSinf_eq_sub : S ⊓ N2' = (E0 ⊓ N2).subgroupOf N := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    tauto
  have hSinf_eq : Nat.card ↥(S ⊓ N2') = Nat.card ↥(E0 ⊓ N2) := by
    rw [hSinf_eq_sub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((inf_le_left : E0 ⊓ N2 ≤ E0).trans hE0)).toEquiv
  have hScardE : Nat.card S = Nat.card E0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE0).toEquiv
  have hE0card : Nat.card E0 = Nat.card ↥P * Nat.card ↥(E0 ⊓ N2) := by
    have hc := CFSG.CGT.Timmesfeld75.card_map_mk'_mul_card_inf S N2'
    change Nat.card ↥P * Nat.card ↥(S ⊓ N2') = Nat.card ↥S at hc
    calc Nat.card E0 = Nat.card S := hScardE.symm
      _ = Nat.card ↥P * Nat.card ↥(S ⊓ N2') := hc.symm
      _ = Nat.card ↥P * Nat.card ↥(E0 ⊓ N2) := by rw [hSinf_eq]
  have hInfN2 : Nat.card ↥(E0 ⊓ N2) ≤ 9 := by
    have hE0N2el : IsElemAbelian 3 (E0 ⊓ N2) := hE0el.mono inf_le_left
    have hle : E0 ⊓ N2 ≤ subsystemGroup Tag.E6 F ({e6Index 4, e6Index 5} : Set (Fin Tag.E6.rank)) := by
      intro x hx
      have hxN2 : (x : ModGL Tag.E6 F) ∈ N2 := (Subgroup.mem_inf.1 hx).2
      have hxN2' : (x : ModGL Tag.E6 F) ∈ subsystemGroup Tag.E6 F support56 := hxN2
      simpa [support56] using hxN2'
    have h := card_le_pow_two_subsystemGroup_e6pair (F := F) (p := 3) Nat.prime_three
      (by norm_num) (i := e6Index 4) (j := e6Index 5)
      (by intro h; have := congrArg Fin.val h; simp [e6Index] at this)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hle hE0N2el
    exact h
  calc Nat.card E0 = Nat.card ↥P * Nat.card ↥(E0 ⊓ N2) := hE0card
    _ ≤ 9 * 9 := Nat.mul_le_mul hP9 hInfN2
    _ = 3 ^ 4 := by norm_num

variable {G : Type*} [Group G] [Finite G]

private theorem card_le_pow_mul_card_inf_of_le_sup {p k : ℕ} {A B : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, Commute x y) (hinf : A ⊓ B = ⊥)
    (hA : ∀ F : Subgroup A, IsElemAbelian p F → Nat.card F ≤ p ^ k)
    {E : Subgroup G} (hE : E ≤ A ⊔ B) (hEel : IsElemAbelian p E) :
    Nat.card E ≤ p ^ k * Nat.card ↥(E ⊓ B : Subgroup G) := by
  classical
  let M : Subgroup G := A ⊔ B
  let A' : Subgroup ↥M := A.subgroupOf M
  let B' : Subgroup ↥M := B.subgroupOf M
  have hAnorm : A ≤ Subgroup.normalizer (B : Set G) := by
    refine Subgroup.le_normalizer_iff.2 ?_
    intro a ha b hb
    have hab : a * b * a⁻¹ = b := by
      rw [(hcomm a ha b hb).eq]
      group
    rw [hab]
    exact hb
  have hBnormG : M ≤ Subgroup.normalizer (B : Set G) :=
    sup_le hAnorm Subgroup.le_normalizer
  have hB'normal : B'.Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn m
    have hm : ((m : ↥M) : G) ∈ Subgroup.normalizer (B : Set G) := hBnormG m.2
    exact (Subgroup.mem_normalizer_iff.1 hm ((n : ↥M) : G)).mp (Subgroup.mem_subgroupOf.1 hn)
  letI : B'.Normal := hB'normal
  have htop : A' ⊔ B' = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hmap : Subgroup.map M.subtype (A' ⊔ B') = M := by
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype A M,
        Subgroup.subgroupOf_map_subtype B M,
        inf_of_le_left (le_sup_left : A ≤ A ⊔ B),
        inf_of_le_left (le_sup_right : B ≤ A ⊔ B)]
    have hx : (x : G) ∈ Subgroup.map M.subtype (A' ⊔ B') := by
      rw [hmap]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [show y = x from Subtype.ext hyx] at hy
  let π : ↥M →* (↥M ⧸ B') := QuotientGroup.mk' B'
  let S : Subgroup ↥M := E.subgroupOf M
  have hEcard : Nat.card S = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
  have hSmap : Subgroup.map π S ≤ Subgroup.map π A' := by
    have h1 : S ≤ A' ⊔ B' := by rw [htop]; exact le_top
    have h2 : Subgroup.map π S ≤ Subgroup.map π (A' ⊔ B') := Subgroup.map_mono h1
    rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff B').2 (QuotientGroup.ker_mk' B').ge,
      sup_bot_eq] at h2
  have hinj : Function.Injective (π.comp A'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxO : (x : ↥M) ∈ B' := (QuotientGroup.eq_one_iff _).1 hx
    have hxAB : ((x : ↥M) : G) ∈ A ⊓ B := ⟨x.2, hxO⟩
    rw [hinf, Subgroup.mem_bot] at hxAB
    exact Subtype.ext (Subtype.ext hxAB)
  let P : Subgroup (↥M ⧸ B') := Subgroup.map π S
  let Q : Subgroup ↥A' := P.comap (π.comp A'.subtype)
  have hPle : P ≤ (π.comp A'.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hSmap
  have hPQ : Nat.card Q = Nat.card P := by
    calc Nat.card Q = Nat.card (Q.map (π.comp A'.subtype)) :=
          (Subgroup.card_map_of_injective hinj).symm
      _ = Nat.card P := by rw [Subgroup.map_comap_eq_self hPle]
  have hQel : IsElemAbelian p Q :=
    ((hEel.subgroupOf M).map π).comap hinj
  let eA : ↥A' ≃* ↥A := Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ B)
  let Q' : Subgroup A := Q.map eA.toMonoidHom
  have hQ'el : IsElemAbelian p Q' := hQel.map eA.toMonoidHom
  have hQ'card : Nat.card Q' = Nat.card Q :=
    Subgroup.card_map_of_injective eA.injective
  have hPbound : Nat.card P ≤ p ^ k := by
    calc Nat.card P = Nat.card Q := hPQ.symm
      _ = Nat.card Q' := hQ'card.symm
      _ ≤ p ^ k := hA Q' hQ'el
  have hInf : Nat.card ↥(S ⊓ B' : Subgroup ↥M) ≤ Nat.card ↥(E ⊓ B : Subgroup G) := by
    refine Nat.card_le_card_of_injective
      (fun x : ↥(S ⊓ B' : Subgroup ↥M) => (⟨(x.1 : G), ?_, ?_⟩ : ↥(E ⊓ B : Subgroup G))) ?_
    · exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 x.2).1
    · exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 x.2).2
    · intro x y hxy
      have h1 : (x.1 : G) = (y.1 : G) :=
        congrArg (fun z : (E ⊓ B : Subgroup G) => (z : G)) hxy
      exact Subtype.ext (Subtype.ext h1)
  calc Nat.card E = Nat.card S := hEcard.symm
    _ = Nat.card P * Nat.card ↥(S ⊓ B' : Subgroup ↥M) := by
        change Nat.card ↥S = Nat.card ↥(Subgroup.map (QuotientGroup.mk' B') S) *
          Nat.card ↥(S ⊓ B' : Subgroup ↥M)
        rw [CFSG.CGT.Timmesfeld75.card_map_mk'_mul_card_inf S B']
    _ ≤ p ^ k * Nat.card ↥(E ⊓ B : Subgroup G) := Nat.mul_le_mul hPbound hInf

private theorem support_1_0 : ∀ γ ∈ rootFinset (Tag.E6),
    (∀ k, k ≠ e6Index 1 → k ≠ e6Index 0 → γ k = 0) →
      γ (e6Index 1) = 0 ∨ γ (e6Index 0) = 0 := by decide +kernel
private theorem support_1_2 : ∀ γ ∈ rootFinset (Tag.E6),
    (∀ k, k ≠ e6Index 1 → k ≠ e6Index 2 → γ k = 0) →
      γ (e6Index 1) = 0 ∨ γ (e6Index 2) = 0 := by decide +kernel
private theorem support_1_4 : ∀ γ ∈ rootFinset (Tag.E6),
    (∀ k, k ≠ e6Index 1 → k ≠ e6Index 4 → γ k = 0) →
      γ (e6Index 1) = 0 ∨ γ (e6Index 4) = 0 := by decide +kernel

private theorem memB (k : Fin 6) (h3 : k ≠ 3) :
    e6Index k ∈ ({i : Fin Tag.E6.rank | i.val ≠ 3} : Set (Fin Tag.E6.rank)) := by
  simp only [e6Index, Set.mem_setOf_eq]
  intro h
  exact h3 (Fin.ext h)
private theorem memB0 : e6Index 0 ∈ ({i : Fin Tag.E6.rank | i.val ≠ 3} : Set _) := memB 0 (by decide)
private theorem memB1 : e6Index 1 ∈ ({i : Fin Tag.E6.rank | i.val ≠ 3} : Set _) := memB 1 (by decide)
private theorem memB2 : e6Index 2 ∈ ({i : Fin Tag.E6.rank | i.val ≠ 3} : Set _) := memB 2 (by decide)
private theorem memB4 : e6Index 4 ∈ ({i : Fin Tag.E6.rank | i.val ≠ 3} : Set _) := memB 4 (by decide)
private theorem memB5 : e6Index 5 ∈ ({i : Fin Tag.E6.rank | i.val ≠ 3} : Set _) := memB 5 (by decide)
theorem card_le_pow_five_subsystemGroup_e6A2A1
    {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = (2 ^ n) ^ 2)
    (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    (hPRL : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (R : Subgroup (V ≃ₗ[F] V)), IsPGroup p R →
      (∀ x ∈ R, ∀ y ∈ R, ∃ a : F, ∀ v, (x * y * x⁻¹ * y⁻¹) v = a • v) →
      (∀ x ∈ R, ∃ a : F, ∀ v, (x ^ p) v = a • v) →
      Nat.card R ≤ p ^ (Module.finrank F V - 1) *
        Nat.card {x : R // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v})
    {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hEel : IsElemAbelian p E)
    (hE : E ≤ subsystemGroup TwistTag.E6.tag F {i | i.val ≠ 3} ⊓
      twistedFixedGroup TwistTag.E6 F σ.toRingHom) :
    Nat.card E ≤ p ^ 5 := by
  haveI : CharP F 2 := by
    have hn : 1 ≤ n * 2 := by
      have h2F : 2 ≤ Nat.card F := by
        haveI : Fintype F := Fintype.ofFinite F
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card (α := F)
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at hF; omega
      · omega
    exact CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (k := n * 2) hn (by rw [hF, pow_mul])
  let L1 := subsystemGroup Tag.E6 F ({e6Index 1} : Set (Fin Tag.E6.rank))
  let N1 := subsystemGroup Tag.E6 F support13
  let N2 := subsystemGroup Tag.E6 F support56
  let N := N1 ⊔ N2
  let LA := subsystemGroup Tag.E6 F
    ({i : Fin Tag.E6.rank | i.val ≠ 3} : Set (Fin Tag.E6.rank))
  have hcomm12 : ∀ x ∈ N1, ∀ y ∈ N2, Commute x y :=
    fun x hx y hy => commute_Q₁_Q₂ (K := F) hx hy
  have hcomm1N1 : ∀ x ∈ L1, ∀ y ∈ N1, Commute x y := by
    refine commute_subsystemGroup ?_
    intro a ha b hb
    simp only [Set.mem_singleton_iff] at ha
    subst ha
    rw [show support13 = ({e6Index 0, e6Index 2} : Set (Fin Tag.E6.rank)) from rfl] at hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · exact e6_pair_support 1 0 (by decide) support_1_0
    · exact e6_pair_support 1 2 (by decide) support_1_2
  have hcomm1N2 : ∀ x ∈ L1, ∀ y ∈ N2, Commute x y := by
    refine commute_subsystemGroup ?_
    intro a ha b hb
    simp only [Set.mem_singleton_iff] at ha
    subst ha
    rw [show support56 = ({e6Index 4, e6Index 5} : Set (Fin Tag.E6.rank)) from rfl] at hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · exact e6_pair_support 1 4 (by decide) support_1_4
    · exact e6_pair_support 1 5 (by decide) support_1_5
  have hcomm1N : ∀ x ∈ L1, ∀ y ∈ N, Commute x y := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
        (fun a ha b hb => (hcomm12 a ha b hb).eq) hy
    exact (hcomm1N1 x hx a ha).mul_right (hcomm1N2 x hx b hb)
  have hinf1N : L1 ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact eq_one_of_mem_subsystemGroup_singleton_of_centralizes (F := F) (i := e6Index 1)
      hx.1 (fun y hy => (hcomm1N y hy x hx.2).symm)
  have hp_one : ¬ p ∣ Nat.card ↥(L1 ⊓ N) := by
    rw [hinf1N]; simp [hp.ne_one]
  have hL1_bound : ∀ G : Subgroup L1, IsElemAbelian p G → Nat.card G ≤ p ^ 1 := by
    refine transfer_bound (J := ({e6Index 1} : Set (Fin Tag.E6.rank))) ?_
    intro G hG hGel
    exact card_le_pow_one_subsystemGroup_e6node (F := F) (n := n) hF hp hp2 hPRL
      (e6Index 1) hG hGel
  let E' : Subgroup (ModGL Tag.E6 F) := E
  have hEel' : IsElemAbelian p E' := hEel
  have hLAeq : LA = L1 ⊔ N := by
    refine le_antisymm ?_ ?_
    · rw [show LA = subsystemGroup Tag.E6 F
          ({i : Fin Tag.E6.rank | i.val ≠ 3} : Set _) from rfl, subsystemGroup]
      refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨i, hi, c, rfl | rfl⟩
      · have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 4 ∨ i.val = 5 := by
          have h3 : i.val ≠ 3 := hi
          have hlt : i.val < 6 := i.isLt
          omega
        rcases hv with h | h | h | h | h
        · rw [show i = e6Index 0 from Fin.ext h]
          exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (xUnit_mem_subsystemGroup (by simp [support13, support56]) c))
        · rw [show i = e6Index 1 from Fin.ext h]
          exact Subgroup.mem_sup_left (xUnit_mem_subsystemGroup (by simp [support13, support56]) c)
        · rw [show i = e6Index 2 from Fin.ext h]
          exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (xUnit_mem_subsystemGroup (by simp [support13, support56]) c))
        · rw [show i = e6Index 4 from Fin.ext h]
          exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (xUnit_mem_subsystemGroup (by simp [support13, support56]) c))
        · rw [show i = e6Index 5 from Fin.ext h]
          exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (xUnit_mem_subsystemGroup (by simp [support13, support56]) c))
      · have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 4 ∨ i.val = 5 := by
          have h3 : i.val ≠ 3 := hi
          have hlt : i.val < 6 := i.isLt
          omega
        rcases hv with h | h | h | h | h
        · rw [show i = e6Index 0 from Fin.ext h]
          exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (yUnit_mem_subsystemGroup (by simp [support13, support56]) c))
        · rw [show i = e6Index 1 from Fin.ext h]
          exact Subgroup.mem_sup_left (yUnit_mem_subsystemGroup (by simp [support13, support56]) c)
        · rw [show i = e6Index 2 from Fin.ext h]
          exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (yUnit_mem_subsystemGroup (by simp [support13, support56]) c))
        · rw [show i = e6Index 4 from Fin.ext h]
          exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (yUnit_mem_subsystemGroup (by simp [support13, support56]) c))
        · rw [show i = e6Index 5 from Fin.ext h]
          exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (yUnit_mem_subsystemGroup (by simp [support13, support56]) c))
    · refine sup_le ?_ ?_
      · refine CFSG.StandardType.F4Rest.subsystemGroup_mono ?_
        intro i hi
        simp only [Set.mem_singleton_iff] at hi
        subst hi
        exact memB1
      · refine sup_le ?_ ?_
        · refine CFSG.StandardType.F4Rest.subsystemGroup_mono ?_
          intro i hi
          rw [show support13 = ({e6Index 0, e6Index 2} : Set (Fin Tag.E6.rank)) from rfl] at hi
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
          rcases hi with rfl | rfl
          · exact memB0
          · exact memB2
        · refine CFSG.StandardType.F4Rest.subsystemGroup_mono ?_
          intro i hi
          rw [show support56 = ({e6Index 4, e6Index 5} : Set (Fin Tag.E6.rank)) from rfl] at hi
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
          rcases hi with rfl | rfl
          · exact memB4
          · exact memB5
  have hE1 : E' ≤ L1 ⊔ N := by
    have h : E ≤ LA := hE.trans inf_le_left
    rw [← hLAeq]
    change E ≤ LA
    exact h
  have hproj := card_le_pow_mul_card_inf_of_le_sup (p := p) (k := 1)
    hcomm1N hinf1N hL1_bound hE1 hEel'
  have hE0el : IsElemAbelian p (E' ⊓ N) := hEel'.mono inf_le_left
  have hE0le : E' ⊓ N ≤ N1 ⊔ N2 := by
    rw [show N = N1 ⊔ N2 from rfl]
    exact inf_le_right
  have hN1_bound : ∀ G : Subgroup N1, IsElemAbelian p G → Nat.card G ≤ p ^ 2 := by
    refine transfer_bound (J := support13) ?_
    intro G hG hGel
    exact card_le_pow_two_subsystemGroup_e6pair (F := F) hp hp2
      (i := e6Index 0) (j := e6Index 2)
      (by intro h; have := congrArg Fin.val h; simp [e6Index] at this)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hG hGel
  have hN2_bound : ∀ G : Subgroup N2, IsElemAbelian p G → Nat.card G ≤ p ^ 2 := by
    refine transfer_bound (J := support56) ?_
    intro G hG hGel
    exact card_le_pow_two_subsystemGroup_e6pair (F := F) hp hp2
      (i := e6Index 4) (j := e6Index 5)
      (by intro h; have := congrArg Fin.val h; simp [e6Index] at this)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hG hGel
  have hE0_bound : Nat.card ↥(E' ⊓ N) ≤ p ^ 4 := by
    by_cases hp3 : p = 3
    · subst p
      exact card_le_pow_four_E0_p3 (F := F) hPRL (by rw [show N = N1 ⊔ N2 from rfl]; exact hE0le) hE0el
    · have hpZ0 : ¬ p ∣ Nat.card ↥(N1 ⊓ N2) := by
        have hdvd : Nat.card ↥(N1 ⊓ N2) ∣ 3 := card_inf_A2_A2_dvd_three (F := F)
        intro hd
        rcases (Nat.dvd_prime Nat.prime_three).1 (hd.trans hdvd) with h | h
        · exact hp.ne_one h
        · exact hp3 h
      exact (card_le_pow_add_of_le_sup_of_not_dvd_inf hp
        (fun x hx y hy => hcomm12 x hx y hy) hpZ0 hN1_bound hN2_bound hE0le hE0el)
  by_cases hp3 : p = 3
  · subst p
    calc Nat.card E = Nat.card E' := rfl
      _ ≤ 3 ^ 1 * Nat.card ↥(E' ⊓ N) := hproj
      _ ≤ 3 ^ 1 * 3 ^ 4 := Nat.mul_le_mul_left _ hE0_bound
      _ = 3 ^ 5 := by norm_num
  · have hE0b : Nat.card ↥(E' ⊓ N) ≤ p ^ 4 := by
      have hpZ0 : ¬ p ∣ Nat.card ↥(N1 ⊓ N2) := by
        have hdvd : Nat.card ↥(N1 ⊓ N2) ∣ 3 := card_inf_A2_A2_dvd_three (F := F)
        intro hd
        rcases (Nat.dvd_prime Nat.prime_three).1 (hd.trans hdvd) with h | h
        · exact hp.ne_one h
        · exact hp3 h
      exact (card_le_pow_add_of_le_sup_of_not_dvd_inf hp
        (fun x hx y hy => hcomm12 x hx y hy) hpZ0 hN1_bound hN2_bound hE0le hE0el)
    calc Nat.card E = Nat.card E' := rfl
      _ ≤ p ^ 1 * Nat.card ↥(E' ⊓ N) := hproj
      _ ≤ p ^ 1 * p ^ 4 := Nat.mul_le_mul_left _ hE0b
      _ = p ^ 5 := by ring

end CFSG.LocalAnalysis.GLTheoremA
