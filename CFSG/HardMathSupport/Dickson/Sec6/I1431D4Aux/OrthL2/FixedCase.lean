module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Pairs
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Final
public import CFSG.RankThree.PartOne.KC.OrthogonalSplitFourClause
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.LeviComm
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.Reduction
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocksComp

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2 QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Coordinator.D4Bridge (Coord)

section Basic

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem rhoImg_mono {L L' : Subgroup (V ≃ₗ[K] V)} (h : L ≤ L') : rhoImg Q L ≤ rhoImg Q L' :=
  Subgroup.map_mono (fun _ hz => h hz)

theorem sup_le_normalizer_of_commute {G : Type*} [Group G] {L M : Subgroup G}
    (h : ∀ u ∈ L, ∀ v ∈ M, u * v = v * u) : L ⊔ M ≤ Subgroup.normalizer (L : Set G) := by
  have hM : M ≤ Subgroup.centralizer (L : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.2 fun u hu => h u hu v hv
  exact sup_le Subgroup.le_normalizer (hM.trans (Subgroup.centralizer_le_normalizer (L : Set G)))

theorem rhoImg_sup {L L' : Subgroup (V ≃ₗ[K] V)} (hL : L ≤ orthDerived Q)
    (hL' : L' ≤ orthDerived Q) : rhoImg Q (L ⊔ L') = rhoImg Q L ⊔ rhoImg Q L' := by
  unfold rhoImg
  rw [Subgroup.subgroupOf_sup hL hL', Subgroup.map_sup]

theorem isComponentOf_rhoImg_of_normal {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) {G : Subgroup (V ≃ₗ[K] V)}
    (hGle : G ≤ supportedFixedDerived Q x)
    (hGn : ∀ h ∈ G, ∀ k ∈ supportedFixedDerived Q x, k * h * k⁻¹ ∈ G)
    (hq : CFSG.IsQuasisimple ↥(rhoImg Q G)) :
    CFSG.Open.IsComponentOf (rhoImg Q G) (centralizerImage Q x) := by
  have hGΩ : G ≤ orthDerived Q := hGle.trans hx.supportedFixedDerived_le_orthDerived
  have hle1 : rhoImg Q G ≤ fixedComponentImage Q x := rhoImg_mono hGle
  have hle : rhoImg Q G ≤ centralizerImage Q x := hle1.trans fixedComponentImage_le_centralizerImage
  have hconj := map_conj_mem (rho Q) (F := G.subgroupOf (orthDerived Q))
    (F' := (supportedFixedDerived Q x).subgroupOf (orthDerived Q)) (fun h k hh hk => by
      exact Subgroup.mem_subgroupOf.mpr (hGn (h : V ≃ₗ[K] V) (Subgroup.mem_subgroupOf.mp hh)
        (k : V ≃ₗ[K] V) (Subgroup.mem_subgroupOf.mp hk)))
  have hsub : ((rhoImg Q G).subgroupOf (centralizerImage Q x)).IsSubnormal := by
    refine Subgroup.IsSubnormal.step _ ((fixedComponentImage Q x).subgroupOf (centralizerImage Q x))
      (fun g hg => Subgroup.mem_subgroupOf.mpr (hle1 (Subgroup.mem_subgroupOf.mp hg)))
      (hx.normal_fixedComponentImage.isSubnormal) ?_
    rw [Subgroup.normal_subgroupOf_iff (fun g hg =>
      Subgroup.mem_subgroupOf.mpr (hle1 (Subgroup.mem_subgroupOf.mp hg)))]
    intro h k hh hk
    exact Subgroup.mem_subgroupOf.mpr (hconj _ _ (Subgroup.mem_subgroupOf.mp hh)
      (Subgroup.mem_subgroupOf.mp hk))
  exact CFSG.Assembly.isComponentOf_iff_open.1
    ((CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hle).2
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm hq,
        hsub⟩)

theorem card_ne_two_of_listed {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hlist : FixedLayerListed Q x) (hw : finrank K (fixedSpace x) = 4) {A B : HypPair Q}
    (hAB : A.Orth B) (hspan : Submodule.span K {A.e, A.f, B.e, B.f} = fixedSpace x) :
    Nat.card K ≠ 2 := by
  intro h2
  apply hlist.2
  refine Or.inr ⟨⟨hw, ?_⟩, Or.inl h2⟩
  set S₀ : Submodule K V := Submodule.span K {A.e, B.e} with hS₀
  have hS₀le : S₀ ≤ fixedSpace x := by
    rw [hS₀, ← hspan]
    exact Submodule.span_mono (by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto)
  refine ⟨S₀.comap (fixedSpace x).subtype, ?_, ?_⟩
  · rw [(Submodule.comapSubtypeEquivOfLe hS₀le).finrank_eq]
    have hli : LinearIndependent K ![A.e, B.e] := by
      have := (linearIndependent_pairs hAB).comp ![0, 2] (by decide)
      convert this using 1
      ext i
      fin_cases i <;> rfl
    have h1 := finrank_span_eq_card hli
    have hr : Set.range ![A.e, B.e] = {A.e, B.e} := by
      ext z
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl)
        exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
    rw [hr] at h1
    simpa using h1
  · intro s hs
    have hs' : (s : V) ∈ S₀ := Submodule.mem_comap.1 hs
    have := map_eq_zero_of_mem_span (K := K) (Q := Q) (S := {A.e, B.e})
      (fun u hu => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with rfl | rfl
        exacts [A.Q_e, B.Q_e])
      (fun u hu w hw => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hw
        rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
        · exact A.polar_ee
        · exact hAB.ee
        · rw [polar_comm]; exact hAB.ee
        · exact B.polar_ee) hs'
    simpa using this

end Basic

section Finite

variable (K : Type) [Field K] [Finite K]

instance finite_coordLinearEquiv : Finite ((Coord → K) ≃ₗ[K] (Coord → K)) :=
  haveI : Finite (Coord → K) := inferInstance
  Finite.of_injective (fun e : (Coord → K) ≃ₗ[K] (Coord → K) => (e : (Coord → K) → (Coord → K)))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)

instance finite_projOrthDerived_quadPlus : Finite (ProjOrthDerived (quadPlus 4 K)) :=
  inferInstance

end Finite

section Quasisimple


variable (K : Type) [Field K] [Finite K]

theorem isQuasisimple_rootSL2 (hK : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple ↥(simplePosSubgroup Tag.D4 K node0 ⊔ simpleNegSubgroup Tag.D4 K node0) := by
  rw [← rankOneRep_range_eq node0]
  refine CFSG.GH74.Generic.S1.isQuasisimple_range_of_ker
    (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := K) le_rfl hK)
    (rankOneRep Tag.D4 K node0) ?_
  intro g hg
  obtain ⟨l, hl, hgl⟩ := rankOneRep_ker node0 g (MonoidHom.mem_ker.1 hg)
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨(l : K), ?_, ?_⟩
  · simpa [Units.val_pow_eq_pow_val] using congrArg (fun u : Kˣ => (u : K)) hl
  · rw [hgl]
    simp [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem isQuasisimple_rhoImg_levi (hK : 4 ≤ Nat.card K) {A B : HypPair (quadPlus 4 K)}
    (h : A.Orth B) : CFSG.IsQuasisimple ↥(rhoImg (quadPlus 4 K) (levi (quadPlus 4 K) A B)) := by
  obtain ⟨c, hc⟩ := exists_Pimg_levi_eq_root K h
  have h1 : CFSG.IsQuasisimple ↥(Pimg K (levi (quadPlus 4 K) A B)) := by
    rw [hc]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective _ (MulAut.conj c).toMonoidHom (MulAut.conj c).injective)
      (isQuasisimple_rootSL2 K hK)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.equivMapOfInjective _ (eTheta K).toMonoidHom (eTheta K).injective).symm h1

theorem ringChar_eq_three_of_card_eq_three (h : Nat.card K = 3) : ringChar K = 3 := by
  haveI := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hdvd : ringChar K ∣ 3 := by
    rw [← h, Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self _ n.pos.ne'
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd

end Quasisimple

section Four


variable (K : Type) [Field K] [Finite K]

theorem rootSL2_of_fixed_four (hK3 : ringChar K ≠ 3) (T2 : LeviSelfDual K) (T3 : LeviFixed K)
    {y : (Coord → K) ≃ₗ[K] (Coord → K)} (hy : OddOrderIsometry (quadPlus 4 K) 3 y)
    (hlist : FixedLayerListed (quadPlus 4 K) y) (hw : finrank K (fixedSpace y) = 4)
    {I : Subgroup (ProjOrthDerived (quadPlus 4 K))}
    (hI : CFSG.Open.IsComponentOf I (centralizerImage (quadPlus 4 K) y))
    (hIle : I ≤ fixedComponentImage (quadPlus 4 K) y) :
    ∃ c : adjointGroup Tag.D4 K, I.map (eTheta K).toMonoidHom =
      (simplePosSubgroup Tag.D4 K node0 ⊔ simpleNegSubgroup Tag.D4 K node0).map
        (MulAut.conj c).toMonoidHom := by
  classical
  obtain ⟨A, B, hAB, hspan⟩ := exists_fixed_pairs K T2 hy hw
  have hK2 : Nat.card K ≠ 2 := card_ne_two_of_listed hlist hw hAB hspan
  have hK3' : Nat.card K ≠ 3 := fun h => hK3 (ringChar_eq_three_of_card_eq_three K h)
  have hK4 : 4 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have hsfd := T3 y hy hK2 A B hAB hspan
  have hAB' : A.Orth (swapPair B) := orth_swapPair_right hAB
  have hΩ : supportedFixedDerived (quadPlus 4 K) y ≤ orthDerived (quadPlus 4 K) :=
    hy.supportedFixedDerived_le_orthDerived
  have hL₁le : levi (quadPlus 4 K) A B ≤ supportedFixedDerived (quadPlus 4 K) y := by
    rw [hsfd]; exact le_sup_left
  have hL₂le : levi (quadPlus 4 K) A (swapPair B) ≤ supportedFixedDerived (quadPlus 4 K) y := by
    rw [hsfd]; exact le_sup_right
  have hcomm := leviV_comm_swap hAB
  have hn₁ : ∀ h ∈ levi (quadPlus 4 K) A B, ∀ k ∈ supportedFixedDerived (quadPlus 4 K) y,
      k * h * k⁻¹ ∈ levi (quadPlus 4 K) A B := by
    intro h hh k hk
    rw [hsfd] at hk
    exact (Subgroup.mem_normalizer_iff.1
      (sup_le_normalizer_of_commute (L := levi (quadPlus 4 K) A B)
        (M := levi (quadPlus 4 K) A (swapPair B)) hcomm hk) h).1 hh
  have hn₂ : ∀ h ∈ levi (quadPlus 4 K) A (swapPair B), ∀ k ∈ supportedFixedDerived (quadPlus 4 K) y,
      k * h * k⁻¹ ∈ levi (quadPlus 4 K) A (swapPair B) := by
    intro h hh k hk
    rw [hsfd, sup_comm] at hk
    exact (Subgroup.mem_normalizer_iff.1
      (sup_le_normalizer_of_commute (L := levi (quadPlus 4 K) A (swapPair B))
        (M := levi (quadPlus 4 K) A B) (fun u hu v hv => (hcomm v hv u hu).symm) hk) h).1 hh
  have hG₁ := isComponentOf_rhoImg_of_normal hy hL₁le hn₁ (isQuasisimple_rhoImg_levi K hK4 hAB)
  have hG₂ := isComponentOf_rhoImg_of_normal hy hL₂le hn₂
    (isQuasisimple_rhoImg_levi K hK4 hAB')
  have hIsup : I ≤ rhoImg (quadPlus 4 K) (levi (quadPlus 4 K) A B) ⊔
      rhoImg (quadPlus 4 K) (levi (quadPlus 4 K) A (swapPair B)) := by
    refine hIle.trans ?_
    rw [fixedComponentImage_eq_rhoImg, hsfd]
    exact (rhoImg_sup (hL₁le.trans hΩ) (hL₂le.trans hΩ)).le
  have hI' : I ≤ ⨆ j : Fin 2, (![rhoImg (quadPlus 4 K) (levi (quadPlus 4 K) A B),
      rhoImg (quadPlus 4 K) (levi (quadPlus 4 K) A (swapPair B))] j) :=
    hIsup.trans (sup_le (le_iSup (fun j : Fin 2 => ![rhoImg (quadPlus 4 K) (levi (quadPlus 4 K) A B),
      rhoImg (quadPlus 4 K) (levi (quadPlus 4 K) A (swapPair B))] j) 0)
      (le_iSup (fun j : Fin 2 => ![rhoImg (quadPlus 4 K) (levi (quadPlus 4 K) A B),
      rhoImg (quadPlus 4 K) (levi (quadPlus 4 K) A (swapPair B))] j) 1))
  obtain ⟨j, hj⟩ := CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.exists_eq_of_isComponentOf_le_iSup
    (![rhoImg (quadPlus 4 K) (levi (quadPlus 4 K) A B),
      rhoImg (quadPlus 4 K) (levi (quadPlus 4 K) A (swapPair B))])
    (fun j => by fin_cases j <;> assumption) hI hI'
  fin_cases j
  · obtain ⟨c, hc⟩ := exists_Pimg_levi_eq_root K hAB
    exact ⟨c, by rw [← hj]; exact hc⟩
  · obtain ⟨c, hc⟩ := exists_Pimg_levi_eq_root K hAB'
    exact ⟨c, by rw [← hj]; exact hc⟩

end Four

section Six


@[expose] noncomputable def commEquivOrthDerived {W : Type} [AddCommGroup W] {K : Type} [Field K] [Module K W]
    (R : QuadraticForm K W) :
    ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) ≃* ↥(orthDerived R) :=
  (Subgroup.equivMapOfInjective _ (TauCeti.QuadraticMap.orthogonalGroup R).subtype
    (TauCeti.QuadraticMap.orthogonalGroup R).subtype_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator _))

variable (K : Type) [Field K] [Finite K]

theorem false_of_fixed_six (hK3 : ringChar K ≠ 3) (T4 : SixNotL2 K)
    {y : (Coord → K) ≃ₗ[K] (Coord → K)} (hy : OddOrderIsometry (quadPlus 4 K) 3 y)
    (hlist : FixedLayerListed (quadPlus 4 K) y) (hw : finrank K (fixedSpace y) = 6)
    {I : Subgroup (ProjOrthDerived (quadPlus 4 K))}
    (hI : CFSG.Open.IsComponentOf I (centralizerImage (quadPlus 4 K) y))
    (hIle : I ≤ fixedComponentImage (quadPlus 4 K) y) {q : ℕ} (hq : 64 ≤ q)
    (hT : IsTypeL2 q ↥I) : False := by
  classical
  set R := (quadPlus 4 K).comp (fixedSpace y).subtype with hR
  have hRnd := hy.polarBilin_fixed_nondegenerate
  have hns : ¬ (finrank K ↥(fixedSpace y) = 4 ∧ ∃ S : Submodule K ↥(fixedSpace y),
      finrank K S = 2 ∧ ∀ s ∈ S, R s = 0) := fun h => by
    have := h.1
    omega
  have hqs : CFSG.IsQuasisimple ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) :=
    orthogonal_regular_space_derived_quasisimple R hRnd hlist.1 hlist.2 hns
  obtain ⟨-, hFq, -, hFN, hFsub⟩ := hy.fixedLayer_unsplit hqs
  have hFc : CFSG.Open.IsComponentOf (fixedComponentImage (quadPlus 4 K) y)
      (centralizerImage (quadPlus 4 K) y) :=
    CFSG.Assembly.isComponentOf_iff_open.1
      ((CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hFN).2
        ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFN).symm hFq,
          hFsub⟩)
  obtain ⟨j, hj⟩ := CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.exists_eq_of_isComponentOf_le_iSup
    (fun _ : Fin 1 => fixedComponentImage (quadPlus 4 K) y) (fun _ => hFc) hI
    (by simpa using hIle)
  have hTF : IsTypeL2 q ↥(fixedComponentImage (quadPlus 4 K) y) := by
    rw [hj]; exact hT
  have hΩ : supportedFixedDerived (quadPlus 4 K) y ≤ orthDerived (quadPlus 4 K) :=
    hy.supportedFixedDerived_le_orthDerived
  have hqO : CFSG.IsQuasisimple ↥(orthDerived R) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (commEquivOrthDerived R) hqs
  have hperf : Group.IsPerfect ↥(supportedFixedDerived (quadPlus 4 K) y) :=
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (supportedFixedDerivedEquiv hy).symm hqO).1
  have hT' : IsTypeL2 q ↥(supportedFixedDerived (quadPlus 4 K) y) :=
    (isTypeL2_rhoImg_iff hΩ hperf).1 hTF
  have hT'' : IsTypeL2 q ↥(orthDerived R) := p6_isTypeL2_of_equiv (supportedFixedDerivedEquiv hy) hT'
  exact T4 R hRnd hw hK3 hq hT''

end Six

end CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2
