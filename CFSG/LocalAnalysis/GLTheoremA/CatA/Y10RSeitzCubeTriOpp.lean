module

public import CFSG.LieType.ChevTwo.OppositeFixedExcTri
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.LieType.Chevalley.FixedRootCentralizerGeneration
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.GroupTheory.WielandtProductLocal
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcTwOpp
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.ChevTwo CFSG.LieType.ChevTwo.Semi
  CFSG.LieType.Chevalley CFSG.LieType.Chevalley.EvenOddRadical CFSG.StandardType
  CFSG.StandardType.GGOppRadExc

section Certs


variable {K : Type} [Field K] [Finite K]

theorem length_le_d4NegOne (w : WeylGroup TwistTag.D4.tag) :
    (coxeterSystem TwistTag.D4.tag).length w ≤
      (coxeterSystem TwistTag.D4.tag).length CFSG.RankThree.PartOne.Q1327T.d4NegOne := by
  obtain ⟨w₀, hmax, -⟩ := weyl_longest_element TwistTag.D4.tag
  have heq : w₀ = CFSG.RankThree.PartOne.Q1327T.d4NegOne :=
    ReversesSigns.eq (reversesSigns_of_forall_length_le hmax) reversesSigns_d4NegOne
  rw [← heq]
  exact hmax w

theorem canonicalRep_d4NegOne_mem (σ : K ≃+* K) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K CFSG.RankThree.PartOne.Q1327T.d4NegOne ∈
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  canonicalRep_mem_graphFixedRootGroup (mem_relWeylTwist_of_forall_length_le length_le_d4NegOne)

noncomputable def n0Tri (σ : K ≃+* K) :
    ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  ⟨canonicalRep (coxeterSystem TwistTag.D4.tag) K CFSG.RankThree.PartOne.Q1327T.d4NegOne,
    canonicalRep_d4NegOne_mem σ⟩

@[expose] noncomputable def oppTri (σ : K ≃+* K) (J : Set (Fin TwistTag.D4.foldedTag.rank)) :
    Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  (oppRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) ⊓
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subgroupOf _

theorem oppRadical_inf_graphFixedRootGroup_eq_map_conj (σ : K ≃+* K)
    (J : Set (Fin TwistTag.D4.foldedTag.rank)) :
    oppRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) ⊓
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom =
      (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J).map
        (MulAut.conj (canonicalRep (coxeterSystem TwistTag.D4.tag) K
          CFSG.RankThree.PartOne.Q1327T.d4NegOne)).toMonoidHom := by
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) K
    CFSG.RankThree.PartOne.Q1327T.d4NegOne with hn
  have hopp : oppRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) =
      (parabolicRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J)).map
        (MulAut.conj n).toMonoidHom := by
    have h := oppRadical_eq_map_conj' (τ := TwistTag.D4.tag) (K := K)
      (w₀ := CFSG.RankThree.PartOne.Q1327T.d4NegOne) (δ := id) Function.injective_id
      (fun i => CFSG.RankThree.PartOne.Q1327T.d4NegOne_smul_single i)
      d4NegOne_mul_self reversesSigns_d4NegOne (TwistTag.D4.orbitUnion J)
    simpa [hn] using h
  have hnC : n ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    canonicalRep_d4NegOne_mem σ
  have hnΓ : n ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedRootGroup_le _ _ _ hnC
  have hΓmap : (twistedFixedGroup TwistTag.D4 K σ.toRingHom).map
      (MulAut.conj n).toMonoidHom = twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
    GGTwoSig.map_conj_eq (Subgroup.le_normalizer hnΓ)
  have hmapinf : (parabolicRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) ⊓
        twistedFixedGroup TwistTag.D4 K σ.toRingHom).map (MulAut.conj n).toMonoidHom =
      (parabolicRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J)).map
        (MulAut.conj n).toMonoidHom ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj n).injective, hΓmap]
  have hCΓ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≤
      twistedFixedGroup TwistTag.D4 K σ.toRingHom := graphFixedRootGroup_le _ _ _
  have hinfC : oppRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) ⊓
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom = oppRadical TwistTag.D4.tag K
        (TwistTag.D4.orbitUnion J) ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom := by
    refine le_antisymm (fun x hx => Subgroup.mem_inf.2
      ⟨(Subgroup.mem_inf.1 hx).1, hCΓ (Subgroup.mem_inf.1 hx).2⟩) ?_
    intro x hx
    obtain ⟨hxO, hxΓ⟩ := Subgroup.mem_inf.1 hx
    have hxneg : x ∈ negUnipotent TwistTag.D4.tag K := oppRadical_le_negUnipotent _ hxO
    exact Subgroup.mem_inf.2 ⟨hxO, graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
      (Subgroup.mem_inf.2 ⟨hxneg, hxΓ⟩)⟩
  rw [hinfC]
  show oppRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) ⊓
      twistedFixedGroup TwistTag.D4 K σ.toRingHom =
    (parabolicRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) ⊓
      twistedFixedGroup TwistTag.D4 K σ.toRingHom).map (MulAut.conj n).toMonoidHom
  rw [hmapinf, ← hopp]

theorem oppTri_eq_map_conj (σ : K ≃+* K) (J : Set (Fin TwistTag.D4.foldedTag.rank)) :
    oppTri σ J = (radTri K σ J).map (MulAut.conj (n0Tri σ)).toMonoidHom := by
  have hle := graphFixedParabolicRadical_le_graphFixedRootGroup (t := TwistTag.D4) K
    σ.toRingHom J
  rw [oppTri, radTri, map_conj_subgroupOf hle (n0Tri σ)]
  exact congrArg (fun H => H.subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (oppRadical_inf_graphFixedRootGroup_eq_map_conj σ J)

theorem isPGroup_radTri [CharP K 2] (σ : K ≃+* K) (J : Set (Fin TwistTag.D4.foldedTag.rank)) :
    IsPGroup 2 (radTri K σ J) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J) :=
    (isPGroup_posUnipotent 2 TwistTag.D4.tag).to_le
      ((inf_le_left : graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J ≤
        parabolicRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J)).trans
        (parabolicRadical_le_posUnipotent _))
  exact h2.of_equiv
    (Subgroup.subgroupOfEquivOfLe
      (graphFixedParabolicRadical_le_graphFixedRootGroup (t := TwistTag.D4) K σ.toRingHom J)).symm

theorem isPGroup_oppTri [CharP K 2] (σ : K ≃+* K) (J : Set (Fin TwistTag.D4.foldedTag.rank)) :
    IsPGroup 2 (oppTri σ J) := by
  rw [oppTri_eq_map_conj σ J]
  exact (isPGroup_radTri σ J).map _

theorem radTri_sup_oppTri (σ : K ≃+* K) (J : Set (Fin TwistTag.D4.foldedTag.rank))
    (hJ : J ≠ Set.univ)
    [IsSimpleGroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)] :
    radTri K σ J ⊔ oppTri σ J = ⊤ := by
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  set Q := graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J with hQ
  set L := graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J with hL
  set Q' := oppRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) ⊓ C with hQ'
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) K
    CFSG.RankThree.PartOne.Q1327T.d4NegOne with hn
  have hQ'eq : Q' = Q.map (MulAut.conj n).toMonoidHom :=
    oppRadical_inf_graphFixedRootGroup_eq_map_conj σ J
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hQnorm, hLP, -, -, -, -, -, hfin, hne⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors (t := TwistTag.D4) K σ J
  have hQ1 : Q ≠ ⊥ := hne hJ
  have hQC : Q ≤ C := graphFixedParabolicRadical_le_graphFixedRootGroup _ _ _ J
  have hQ'C : Q' ≤ C := inf_le_right
  have hPQ : graphFixedParabolic TwistTag.D4 K σ.toRingHom J ≤
      Subgroup.normalizer (Q : Set (ModGL TwistTag.D4.tag K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).1 hQnorm
  have hLQ : L ≤ Subgroup.normalizer (Q : Set (ModGL TwistTag.D4.tag K)) := hLP.trans hPQ
  have hLQ' : L ≤ Subgroup.normalizer (Q' : Set (ModGL TwistTag.D4.tag K)) := by
    intro m hm
    have hmM : m ∈ parabolicLevi TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) :=
      (Subgroup.mem_inf.1 hm).1
    have hmC : m ∈ C := graphFixedParabolicLevi_le _ _ _ J hm
    refine Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
    · exact parabolicLevi_le_normalizer_oppRadical
        (w₀ := CFSG.RankThree.PartOne.Q1327T.d4NegOne) (δ := id) Function.injective_id
        (fun i => CFSG.RankThree.PartOne.Q1327T.d4NegOne_smul_single i) d4NegOne_mul_self
        reversesSigns_d4NegOne (TwistTag.D4.orbitUnion J) hmM
    · exact Subgroup.le_normalizer hmC
  have hLn : L.map (MulAut.conj n).toMonoidHom ≤ L := by
    refine map_conj_graphFixedParabolicLevi_le (σ := σ.toRingHom) (canonicalRep_d4NegOne_mem σ) ?_
    have h := map_conj_parabolicLevi_le (k := K) (w₀ := CFSG.RankThree.PartOne.Q1327T.d4NegOne)
      (δ := id) (fun i => CFSG.RankThree.PartOne.Q1327T.d4NegOne_smul_single i)
      (TwistTag.D4.orbitUnion J)
    simpa [hn] using h
  have hgen : C ≤ Q ⊔ Q' ⊔ L := by
    rw [hC]
    change graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊔
      graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom ≤ Q ⊔ Q' ⊔ L
    refine sup_le ?_ ?_
    · exact (graphFixedPosUnipotent_le_sup (t := TwistTag.D4) σ J).trans
        (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    · rw [← map_conj_graphFixedPosUnipotent (t := TwistTag.D4) (σ := σ.toRingHom) (K := K)
        length_le_d4NegOne]
      refine (Subgroup.map_mono (graphFixedPosUnipotent_le_sup (t := TwistTag.D4) σ J)).trans ?_
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [← hQ'eq]
        exact le_trans le_sup_right le_sup_left
      · exact hLn.trans le_sup_right
  have hXnorm : C ≤ Subgroup.normalizer ((Q ⊔ Q' : Subgroup (ModGL TwistTag.D4.tag K)) :
      Set (ModGL TwistTag.D4.tag K)) :=
    hgen.trans (sup_le Subgroup.le_normalizer fun m hm =>
      Subgroup.inf_normalizer_le_normalizer_sup Q Q'
        (Subgroup.mem_inf.2 ⟨hLQ hm, hLQ' hm⟩))
  have hXC : Q ⊔ Q' ≤ C := sup_le hQC hQ'C
  have hnormal : ((Q ⊔ Q').subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXC).2 hXnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Q ⊔ Q').subgroupOf C) with h | h
  · exfalso
    apply hQ1
    have hdis := Subgroup.subgroupOf_eq_bot.1 h
    exact eq_bot_iff.2 fun q hq => (Subgroup.disjoint_def.1 hdis)
      (Subgroup.mem_sup_left hq) (hQC hq) ▸ Subgroup.mem_bot.2 rfl
  · have hXeq : Q ⊔ Q' = C :=
      le_antisymm hXC ((Subgroup.subgroupOf_eq_top (H := Q ⊔ Q') (K := C)).1 h)
    have htop : (Q ⊔ Q').subgroupOf C = (⊤ : Subgroup ↥C) := by
      rw [hXeq, Subgroup.subgroupOf_self]
    rw [Subgroup.subgroupOf_sup hQC hQ'C] at htop
    exact htop

theorem oppTri_map_conj_inv_invariant (σ : K ≃+* K) (J : Set (Fin TwistTag.D4.foldedTag.rank))
    (hNF : UniqueNormalFormOn (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    {R : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    {y : ModGL TwistTag.D4.tag K} (hyC : y ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hyM : ∀ α ∈ R, (SemidirectProduct.inl y * liftAutOn hNF α *
      (SemidirectProduct.inl y)⁻¹).left ∈ graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J) :
    ∀ α ∈ R, ((oppTri σ J).map
        (MulAut.conj (⟨y, hyC⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁻¹)).map
          α.toMonoidHom =
      (oppTri σ J).map
        (MulAut.conj (⟨y, hyC⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁻¹) := by
  classical
  intro α hα
  have hstep : ∀ w : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom), w ∈ oppTri σ J →
      α ((MulAut.conj (⟨y, hyC⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁻¹) w) ∈
        (oppTri σ J).map
          (MulAut.conj (⟨y, hyC⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁻¹).toMonoidHom := by
    intro w hw
    obtain ⟨hwO, hwC⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hw)
    set s : GamL TwistTag.D4.tag K := liftAutOn hNF α with hs
    have hmL' : (SemidirectProduct.inl y * s * (SemidirectProduct.inl y)⁻¹).left ∈
        graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J := by
      simpa [hs] using hyM α hα
    set m : ModGL TwistTag.D4.tag K :=
      (SemidirectProduct.inl y * s * (SemidirectProduct.inl y)⁻¹).left with hm
    have hmL : m ∈ graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J := by
      rw [hm]; exact hmL'
    have hmM : m ∈ parabolicLevi TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) :=
      (Subgroup.mem_inf.1 hmL).1
    have hmC : m ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
      graphFixedParabolicLevi_le _ _ _ J hmL
    have hsw : fieldAutHom TwistTag.D4.tag K s.right (w : ModGL TwistTag.D4.tag K) ∈
        oppRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) :=
      entrywise_mem_rootSpan hwO
    have hswC : fieldAutHom TwistTag.D4.tag K s.right (w : ModGL TwistTag.D4.tag K) ∈
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
      fieldAut_mem_graphFixedRootGroupTri σ s.right hwC
    set u : ModGL TwistTag.D4.tag K :=
      m * fieldAutHom TwistTag.D4.tag K s.right (w : ModGL TwistTag.D4.tag K) * m⁻¹ with hu
    have huO : u ∈ oppRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) := by
      rw [hu]
      exact (Subgroup.mem_normalizer_iff.1
        (parabolicLevi_le_normalizer_oppRadical (w₀ := CFSG.RankThree.PartOne.Q1327T.d4NegOne)
          (δ := id) Function.injective_id
          (fun i => CFSG.RankThree.PartOne.Q1327T.d4NegOne_smul_single i) d4NegOne_mul_self
          reversesSigns_d4NegOne (TwistTag.D4.orbitUnion J) hmM) _).1 hsw
    have huC : u ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
      rw [hu]
      exact mul_mem (mul_mem hmC hswC) (inv_mem hmC)
    refine Subgroup.mem_map.2 ⟨⟨u, huC⟩, Subgroup.mem_subgroupOf.2
      (Subgroup.mem_inf.2 ⟨huO, huC⟩), ?_⟩
    refine Subtype.ext ?_
    change (↑((MulAut.conj (⟨y, hyC⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁻¹)
        (⟨u, huC⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :
        ModGL TwistTag.D4.tag K) = _
    have h1 : (↑((MulAut.conj (⟨y, hyC⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁻¹)
        (⟨u, huC⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :
        ModGL TwistTag.D4.tag K) = y⁻¹ * u * y := by
      rw [MulAut.conj_apply]
      rfl
    have h2 : (↑(α ((MulAut.conj (⟨y, hyC⟩ : ↥(graphFixedRootGroup TwistTag.D4 K
        σ.toRingHom))⁻¹) w)) : ModGL TwistTag.D4.tag K) =
        s.left * fieldAutHom TwistTag.D4.tag K s.right
          (y⁻¹ * (w : ModGL TwistTag.D4.tag K) * y) * s.left⁻¹ := by
      rw [liftAutOn_spec hNF α, conjAct_apply, MulAut.conj_apply, ← fieldAutHom_apply]
      rfl
    rw [h1, h2]
    have hmval : m = y * s.left * (fieldAutHom TwistTag.D4.tag K s.right y)⁻¹ := by
      rw [hm]
      simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
        SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, MulAut.one_apply,
        map_inv, one_mul]
      rw [show (SemidirectProduct.inl y)⁻¹ = SemidirectProduct.inl y⁻¹ by simp,
        SemidirectProduct.left_inl, map_inv]
    rw [hu, hmval]
    simp only [map_mul, map_inv, MulEquiv.map_mul, MulEquiv.map_inv]
    group
  have hle : ((oppTri σ J).map (MulAut.conj (⟨y, hyC⟩ :
        ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁻¹).toMonoidHom).map α.toMonoidHom ≤
      (oppTri σ J).map (MulAut.conj (⟨y, hyC⟩ :
        ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁻¹).toMonoidHom := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := hz
    obtain ⟨w, hw, rfl⟩ := hv
    exact hstep w hw
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  exact (Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective).ge

theorem seitzCubeTri_hcore (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (J : Set (Fin TwistTag.D4.foldedTag.rank)) (hJ : J ≠ Set.univ)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    (hR : IsPGroup p R)
    (hQR : ∀ α ∈ R, (radTri K σ J).map α.toMonoidHom = radTri K σ J)
    (hNQ : Subgroup.normalizer ((radTri K σ J : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom)) : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = parTri K σ J) :
    ∃ V : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup 2 V ∧
      (∀ α ∈ R, V.map α.toMonoidHom = V) ∧ radTri K σ J ⊔ V = ⊤ := by
  classical
  let C : Subgroup (ModGL TwistTag.D4.tag K) := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI hK2 : CharP K 2 := charP_two_of_card_two_pow hK3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfinM : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hNF : UniqueNormalFormOn C := uniqueNormalFormOn_D4 σ hf hK hσ
  have hH : ∀ δ : RingAut K, ∀ h ∈ C, fieldAutHom TwistTag.D4.tag K δ h ∈ C :=
    fun δ _ hh => fieldAut_mem_graphFixedRootGroupTri σ δ hh
  set T := R.map (liftHomOn hNF hH) with hT
  have hTcard : Nat.card T = Nat.card R :=
    Subgroup.card_map_of_injective (liftHomOn_injective hNF hH)
  haveI : Fact p.Prime := ⟨hp⟩
  have hRodd : Nat.card R % 2 = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hR
    rw [hk]
    exact Nat.odd_iff.1 ((hp.eq_two_or_odd'.resolve_left hp2).pow)
  have hTodd : ¬ 2 ∣ Nat.card T := by
    rw [hTcard]
    exact Nat.two_dvd_ne_zero.2 hRodd
  have hTP : ∀ s ∈ T, s.left ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom J := by
    rintro _ ⟨α, hα, rfl⟩
    exact liftAutOn_left_mem_graphFixedParabolic σ hNF J (hQR α hα) hNQ
  obtain ⟨y, hyQ, hyM⟩ := exists_conj_into_graphFixedLevi σ J hTP hTodd
  have hyC : y ∈ C := graphFixedParabolicRadical_le_graphFixedRootGroup _ _ _ J hyQ
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    have h2 : 2 ≤ (2 : ℕ) ^ f := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hf
    have h1 : 4 ≤ (2 ^ f) ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left h2 2
    exact h1.trans (Nat.pow_le_pow_right (by positivity) (by norm_num))
  have hperf : ⁅C, C⁆ = C :=
    commutator_graphFixedRootGroup_triality_char_two (ringChar.eq K 2) σ
      (fun c => ringEquiv_cube_apply_eq hK hσ c) h4
  haveI hsimple : IsSimpleGroup ↥C :=
    (isSimpleGroup_graphFixedRootGroup_of_perfect (t := TwistTag.D4) (K := K) (σ := σ) hperf).1
  have hsup : radTri K σ J ⊔ oppTri σ J = ⊤ := radTri_sup_oppTri σ J hJ
  refine ⟨(oppTri σ J).map (MulAut.conj (⟨y, hyC⟩ : ↥C)⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · exact (isPGroup_oppTri σ J).map _
  · exact oppTri_map_conj_inv_invariant σ J hNF hyC
      (fun α hα => hyM (liftAutOn hNF α) (Subgroup.mem_map_of_mem _ hα))
  · have hyQrad : (⟨y, hyC⟩ : ↥C) ∈ radTri K σ J := Subgroup.mem_subgroupOf.2 hyQ
    have hQconj : (radTri K σ J).map (MulAut.conj (⟨y, hyC⟩ : ↥C)).toMonoidHom =
        radTri K σ J :=
      GGTwoSig.map_conj_eq (Subgroup.le_normalizer hyQrad)
    have hVconj : ((oppTri σ J).map (MulAut.conj (⟨y, hyC⟩ : ↥C)⁻¹).toMonoidHom).map
        (MulAut.conj (⟨y, hyC⟩ : ↥C)).toMonoidHom = oppTri σ J := by
      rw [Subgroup.map_map]
      have hcomp : ((MulAut.conj (⟨y, hyC⟩ : ↥C)).toMonoidHom.comp
          (MulAut.conj (⟨y, hyC⟩ : ↥C)⁻¹).toMonoidHom) = MonoidHom.id ↥C := by
        refine MonoidHom.ext fun x => ?_
        show (MulAut.conj (⟨y, hyC⟩ : ↥C)) ((MulAut.conj (⟨y, hyC⟩ : ↥C)⁻¹) x) = x
        have h : (MulAut.conj (⟨y, hyC⟩ : ↥C)) * (MulAut.conj (⟨y, hyC⟩ : ↥C)⁻¹) = 1 := by
          rw [← map_mul, mul_inv_cancel, map_one]
        rw [← MulAut.mul_apply, h, MulAut.one_apply]
      rw [hcomp, Subgroup.map_id]
    have hmap : ((radTri K σ J ⊔ (oppTri σ J).map
        (MulAut.conj (⟨y, hyC⟩ : ↥C)⁻¹).toMonoidHom)).map
          (MulAut.conj (⟨y, hyC⟩ : ↥C)).toMonoidHom = ⊤ := by
      rw [Subgroup.map_sup, hQconj, hVconj, hsup]
    have htop : (⊤ : Subgroup ↥C).map (MulAut.conj (⟨y, hyC⟩ : ↥C)).toMonoidHom = ⊤ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top]
      exact (MulAut.conj (⟨y, hyC⟩ : ↥C)).surjective
    exact Subgroup.map_injective (MulAut.conj (⟨y, hyC⟩ : ↥C)).injective (hmap.trans htop.symm)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
