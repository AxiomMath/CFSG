module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158InnHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9LabHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgD4Graph
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8D4Adj
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4Orders
public import CFSG.LocalAnalysis.ComponentClassification.BFailureSolvableQuotient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158Core

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived inner mem_innAutDerived_congr
  inner_le_innAutDerived congr_mem_inner_iff)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open CFSG.Blueprint.Chevalley (adjointGroup Tag TwistTag)

section Basic

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem t158Core_chevAut_mem_stab {K J : Subgroup Γ} {b : Γ} (hJK : J ≤ K)
    (hbK : b ∈ Subgroup.normalizer (K : Set Γ)) (hbJ : b ∈ Subgroup.normalizer (J : Set Γ)) :
    chevAut 3 K ⟨b, hbK⟩ ∈ CFSG.GroupActions.subgroupStabAut (chevTransfer 3 K J) := by
  have key : ∀ (c : Γ) (hcN : c ∈ Subgroup.normalizer (K : Set Γ))
      (_ : c ∈ Subgroup.normalizer (J : Set Γ)),
      (chevTransfer 3 K J).map (chevAut 3 K ⟨c, hcN⟩).toMonoidHom ≤ chevTransfer 3 K J := by
    intro c hcN hcJ
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    have hkJ : (k : Γ) ∈ J := Subgroup.mem_subgroupOf.1 hk
    have hck : c * k * c⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hcJ k).1 hkJ
    refine ⟨K.normalizerMonoidHom ⟨c, hcN⟩ k, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · rw [chev_coe_normalizerMonoidHom]
      exact hck
    · exact (chevAut_chevQuotHom 3 K ⟨c, hcN⟩ k).symm
  have h1 := key b hbK hbJ
  have h2 := key b⁻¹ (Subgroup.inv_mem _ hbK) (Subgroup.inv_mem _ hbJ)
  change (chevTransfer 3 K J).map (chevAut 3 K ⟨b, hbK⟩).toMonoidHom = chevTransfer 3 K J
  refine le_antisymm h1 ?_
  intro s hs
  refine ⟨chevAut 3 K ⟨b⁻¹, Subgroup.inv_mem _ hbK⟩ s, h2 ⟨s, hs, rfl⟩, ?_⟩
  change chevAut 3 K ⟨b, hbK⟩ (chevAut 3 K ⟨b⁻¹, Subgroup.inv_mem _ hbK⟩ s) = s
  rw [← MulAut.mul_apply, ← map_mul]
  have : (⟨b, hbK⟩ : ↥(Subgroup.normalizer (K : Set Γ))) * ⟨b⁻¹, Subgroup.inv_mem _ hbK⟩ = 1 :=
    Subtype.ext (mul_inv_cancel b)
  rw [this, map_one, MulAut.one_apply]

theorem t158Core_card_pSimple_dvd (J : Subgroup Γ) : Nat.card (PSimple 3 J) ∣ Nat.card J :=
  (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)

theorem t158Core_indAut_eq_inv {K : Subgroup Γ} {x : Γ} (hx : x ∈ Subgroup.normalizer (K : Set Γ)) :
    MI.indAut 3 K x hx = (chevAut 3 K ⟨x, hx⟩)⁻¹ := by
  rw [← map_inv]
  rfl

theorem t158Core_pow_of_cyclic {A : Type*} [Group A] [Finite A] [IsCyclic A] {a b : A}
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hb3 : b ^ 3 = 1) : ∃ j : ℕ, j < 3 ∧ b = a ^ j := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hmem : b ∈ Subgroup.zpowers a := by
    by_cases hb1 : b = 1
    · rw [hb1]
      exact Subgroup.one_mem _
    · have hob : orderOf b = 3 := orderOf_eq_prime hb3 hb1
      have h : Subgroup.zpowers b = Subgroup.zpowers a :=
        IsCyclic.subgroup_eq_iff_card_eq.2 (by rw [Nat.card_zpowers, Nat.card_zpowers, hoa, hob])
      rw [← h]
      exact Subgroup.mem_zpowers b
  have hfin : IsOfFinOrder a := isOfFinOrder_of_finite a
  obtain ⟨j, hj, hj'⟩ := Finset.mem_image.1 ((hfin.mem_zpowers_iff_mem_range_orderOf).1 hmem)
  rw [Finset.mem_range, hoa] at hj
  exact ⟨j, hj, hj'.symm⟩

theorem t158Core_d4Eight_index {i : TauCeti.CFSGIndex} (hi : T158Inn.isD4Eight i) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid),
      i = TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩ ∧ q.p = 2 ∧ q.exponent = 3 := by
  rcases i with ⟨n, hn⟩ | ⟨p, hp⟩ | ⟨d, hv⟩ | s
  all_goals try (simp [T158Inn.isD4Eight, onLie] at hi; done)
  cases d with
  | D r q =>
    rcases r with _ | _ | _ | _ | _ | r
    all_goals try (simp [T158Inn.isD4Eight, onLie] at hi; done)
    exact ⟨q, hv, rfl, by simpa [T158Inn.isD4Eight, onLie] using hi⟩
  | _ => simp [T158Inn.isD4Eight, onLie] at hi

theorem t158Core_td4Eight_index {i : TauCeti.CFSGIndex} (hi : T158Inn.isTD4Eight i) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      i = TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩ ∧ q.p = 2 ∧ q.exponent = 3 := by
  rcases i with ⟨n, hn⟩ | ⟨p, hp⟩ | ⟨d, hv⟩ | s
  all_goals try (simp [T158Inn.isTD4Eight, onLie] at hi; done)
  cases d with
  | trialityD4 q => exact ⟨q, hv, rfl, by simpa [T158Inn.isTD4Eight, onLie] using hi⟩
  | _ => simp [T158Inn.isTD4Eight, onLie] at hi

private theorem t158Core_nineteen_not_dvd_two_pow_sub_one (j : ℕ) (hj0 : 0 < j) (hj : j < 12) :
    ¬ 19 ∣ 2 ^ j - 1 := by
  interval_cases j <;> decide

end Basic

section NineteenD4


theorem t158Core_nineteen_not_dvd_card_d4_two {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    ¬ 19 ∣ Nat.card (adjointGroup Tag.D4 k) := by
  refine CFSG.LieType.SeitzGeneration.ExcWideThree.not_dvd_card_adjointGroup_D4 (by norm_num) ?_ ?_
  · rw [hk]; decide
  · intro j hj0 hj
    rw [hk]
    exact t158Core_nineteen_not_dvd_two_pow_sub_one j hj0 hj

end NineteenD4

section D4Eight

open CFSG.Blueprint CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent


theorem t158Core_d4Eight_mem_innAutDerived {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3)
    {α : MulAut (adjointGroup Tag.D4 K)} (hα3 : α ^ 3 = 1) {P : Subgroup (adjointGroup Tag.D4 K)}
    (hP : P ≤ fixSubgroup α) (hperf : ⁅P, P⁆ = P) (h19 : 19 ∣ Nat.card P) :
    α ∈ innAutDerived (adjointGroup Tag.D4 K) := by
  classical
  by_contra hαout
  have hK3 : ringChar K ≠ 3 := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow Nat.prime_two
      (by norm_num) hK]
    norm_num
  have h19α : 19 ∣ Nat.card (fixSubgroup α) := h19.trans (Subgroup.card_dvd_of_le hP)
  have hgf : ∀ (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K), σ ≠ 1 →
      σ ^ 3 = 1 → ∀ {ε : ℕ}, (ε = 1 ∨ ε = 2) →
      α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) → False := by
    intro g a σ hσ1 hσ3 ε hε hαeq
    have hm := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om.d4_graphField_model hK hα3 g a σ hσ1 hσ3 hε hαeq
    rcases hm with ⟨hcl, -⟩ | ⟨-, -, hexc⟩ | ⟨-, hree, -⟩ | ⟨-, h, -⟩
    · exact absurd hcl (by decide)
    · have hcard : Nat.card ↥(fixSubgroup α) = ordTrialityD4 (2 ^ 1) :=
        CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hexc
      rw [hcard] at h19α
      exact absurd h19α (by decide)
    · exact absurd hree (by decide)
    · exact absurd h (by decide)
  obtain ⟨g, a, σ, ε, hε3, hσ3, hαeq⟩ := exists_cube_normal_form_sigma α hα3
  interval_cases ε
  · have hα0 : α = MulAut.conj g * exactNormalAut Tag.D4 K a σ 0 := by
      rw [hαeq, d4Graph_zero, mul_one]
    by_cases hσ1 : σ = 1
    · subst hσ1
      rw [hα0] at hα3 hαout
      obtain ⟨h, hh⟩ := d4_inner_of_diag hK3 g a hα3
      exact hαout (hh ▸ (inner_le_innAutDerived _ ⟨h, rfl⟩))
    ·
      have hα3' : (MulAut.conj g * exactNormalAut Tag.D4 K a σ 0) ^ 3 = 1 := by
        rw [← hα0]
        exact hα3
      obtain ⟨ψ, hψ⟩ :=
        ExcCopy.exists_conj_eq_entrywiseAdjointAut .D4 Nat.prime_three g a σ hσ1 hσ3 hα3'
      rw [← hα0] at hψ
      have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
      have hk : Nat.card (fixSubfield σ) = 2 := by
        obtain ⟨-, hc⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two (f := 3) (by norm_num)
          hK σ
        rw [hord] at hc
        simpa using hc
      haveI : Finite (fixSubfield σ) := Subtype.finite
      obtain ⟨ι, hιinj, hιfix, hnorm, hsolv⟩ := ExcCopy.exists_fixed_structure Tag.D4 σ
      set F := fixSubgroup (entrywiseAdjointAut Tag.D4 σ) with hFdef
      set P' : Subgroup (adjointGroup Tag.D4 K) := P.map (ψ : MulAut (adjointGroup Tag.D4 K)).toMonoidHom
        with hP'def
      have hP'F : P' ≤ F := by
        rintro _ ⟨y, hy, rfl⟩
        have hy' : α y = y := mem_fixSubgroup.1 (hP hy)
        rw [hFdef, mem_fixSubgroup, ← hψ]
        show ψ (α (ψ⁻¹ (ψ y))) = ψ y
        rw [MulAut.inv_apply_self, hy']
      have hP'perf : ⁅P', P'⁆ = P' := by
        rw [hP'def, ← Subgroup.map_commutator, hperf]
      have hcardP' : Nat.card P' = Nat.card P :=
        Subgroup.card_map_of_injective (ψ : MulAut (adjointGroup Tag.D4 K)).injective
      haveI := hnorm
      haveI : Group.IsPerfect ↥P' := Subgroup.isPerfect_iff.mpr hP'perf
      haveI : Group.IsPerfect ↥(P'.subgroupOf F) :=
        Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hP'F).symm.toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hP'F).symm.surjective
      have hle := CFSG.ComponentClassification.CatalogueBPrimeJoin.le_of_isPerfect_of_isSolvable_quotient
        (L := P'.subgroupOf F) (N := ι.range.subgroupOf F) hsolv
      have hP'ι : P' ≤ ι.range := by
        intro y hy
        have h1 : (⟨y, hP'F hy⟩ : ↥F) ∈ P'.subgroupOf F := Subgroup.mem_subgroupOf.2 hy
        exact Subgroup.mem_subgroupOf.1 (hle h1)
      have hdvd : Nat.card P' ∣ Nat.card (adjointGroup Tag.D4 (fixSubfield σ)) := by
        rw [Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv]
        exact Subgroup.card_dvd_of_le hP'ι
      rw [hcardP'] at hdvd
      exact t158Core_nineteen_not_dvd_card_d4_two hk (h19.trans hdvd)
  · by_cases hσ1 : σ = 1
    · subst hσ1
      exact hαout (hαeq ▸ KD264Lie.mem_innAutDerived_of_graphType g a (Or.inl rfl)
        (by rw [← hαeq]; exact hα3))
    · exact hgf g a σ hσ1 hσ3 (Or.inl rfl) hαeq
  · by_cases hσ1 : σ = 1
    · subst hσ1
      exact hαout (hαeq ▸ KD264Lie.mem_innAutDerived_of_graphType g a (Or.inr rfl)
        (by rw [← hαeq]; exact hα3))
    · exact hgf g a σ hσ1 hσ3 (Or.inr rfl) hαeq

end D4Eight

section G2Eight


theorem t158Core_false_of_component_G2_eight {Y : Type} [Group Y] {β : MulAut Y} {F' : Type}
    [Field F'] [Finite F'] (hF' : Nat.card F' = 2 ^ 3)
    (eG : ↥(fixSubgroup β) ≃* ↥(adjointGroup Tag.G2 F')) {J : Subgroup Y}
    (hJ : IsComponentOf J (fixSubgroup β)) (hcard : Nat.card (↥J ⧸ Subgroup.center ↥J) = 5515776) :
    False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF'3 : 3 ≤ Nat.card F' := by rw [hF']; norm_num
  have hG2simple : IsSimpleGroup ↥(adjointGroup Tag.G2 F') :=
    CFSG.LieType.SeitzGeneration.isSimpleGroup_adjointGroup_of_isQuasisimple
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card F' hF'3)
  have hsH : IsSimpleGroup ↥(fixSubgroup β) := (MulEquiv.isSimpleGroup_congr eG).2 hG2simple
  haveI := hJ.2.2.2
  haveI : Nontrivial ↥J := (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).nontrivial
  have hJne : J ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot J).1 inferInstance
  have hJH : J = fixSubgroup β :=
    CFSG.StandardType.ggEq_of_isSubnormal_of_isSimpleGroup
      (CFSG.Assembly.isSubnormal_iff_open.2 hJ.2.1) hsH hJne
  let eJ' : ↥J ≃* ↥(adjointGroup Tag.G2 F') := (MulEquiv.subgroupCongr hJH).trans eG
  have hZ : Subgroup.center ↥J = ⊥ := by
    have hmap : (Subgroup.center ↥J).map eJ' = (⊥ : Subgroup ↥(adjointGroup Tag.G2 F')) := by
      rw [Subgroup.map_center_eq eJ', CFSG.LieType.Chevalley.center_adjointGroup_eq_bot]
    exact (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center ↥J) eJ'.injective).1 hmap
  have hcardJ : Nat.card ↥J = CFSG.Open.ordG2 8 := by
    rw [Nat.card_congr eJ'.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hF']
    norm_num
  have hQcard : Nat.card (↥J ⧸ Subgroup.center ↥J) = CFSG.Open.ordG2 8 := by
    rw [← hcardJ]
    exact Nat.card_congr
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv
  rw [hQcard] at hcard
  norm_num [CFSG.Open.ordG2] at hcard

end G2Eight

section PGUThree

open CFSG.RankThree.PartTwo

theorem t158Core_component_eq_commutator_of_isoPGU {Y : Type} [Group Y] {β : MulAut Y} {K : Type}
    [Field K] [Finite K] (hKcard : Nat.card K = (2 ^ 3) ^ 2)
    (φ : ↥(fixSubgroup β) ≃* CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K))
    {J : Subgroup Y} (hJ : IsComponentOf J (fixSubgroup β)) :
    J = ⁅fixSubgroup β, fixSubgroup β⁆ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Sec4.PiField false 2 3 K :=
    ⟨Nat.prime_two, by norm_num, by simpa [Sec4.piCard] using hKcard⟩
  have hq2 : 2 < (2 : ℕ) ^ 3 := by norm_num
  have hSP : CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K) ≤
      CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi (fun _ => hK.unitary))
  have hsimple : IsSimpleGroup ↥(CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K)) :=
    Sec8.Item8KFacts2Proof.isSimpleGroup_projImage_slPi hK hq2
  have hcomm := Sec13.commutator_projImage_glPi hK hq2
  have eComm : ↥(⁅fixSubgroup β, fixSubgroup β⁆ : Subgroup Y) ≃*
      ↥(CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K)) :=
    ((CFSG.StandardType.ggCommutatorEquiv (fixSubgroup β)).trans
      ((CFSG.StandardType.ggCommutatorCongr φ).trans
        ((MulEquiv.subgroupCongr hcomm).trans (Subgroup.subgroupOfEquivOfLe hSP))))
  have hsComm : IsSimpleGroup ↥(⁅fixSubgroup β, fixSubgroup β⁆ : Subgroup Y) :=
    (MulEquiv.isSimpleGroup_congr eComm).2 hsimple
  exact CFSG.StandardType.ggComponent_eq_commutator (CFSG.Assembly.isComponentOf_iff_open.2 hJ) hsComm

theorem t158Core_exists_mulEquiv_projImage_slPi {Y : Type} [Group Y] {β : MulAut Y} {K : Type}
    [Field K] [Finite K] (hKcard : Nat.card K = (2 ^ 3) ^ 2)
    (φ : ↥(fixSubgroup β) ≃* CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K))
    {J : Subgroup Y} (hJ : IsComponentOf J (fixSubgroup β)) (hJH : J = ⁅fixSubgroup β, fixSubgroup β⁆) :
    ∃ eJ : ↥J ≃* ↥(CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K)),
      ∀ y : ↥J, ((eJ y : ↥(CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K))) :
          Matrix.ProjGenLinGroup (Fin 3) K) =
        (φ ⟨(y : Y), hJ.1 y.2⟩ : Matrix.ProjGenLinGroup (Fin 3) K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Sec4.PiField false 2 3 K :=
    ⟨Nat.prime_two, by norm_num, by simpa [Sec4.piCard] using hKcard⟩
  have hq2 : 2 < (2 : ℕ) ^ 3 := by norm_num
  have hSP : CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K) ≤
      CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi (fun _ => hK.unitary))
  have hcomm := Sec13.commutator_projImage_glPi hK hq2
  let g : ↥J →* ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K)) :=
    φ.toMonoidHom.comp (Subgroup.inclusion hJ.1)
  have hmem : ∀ y : ↥J, g y ∈
      (CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K)).subgroupOf
        (CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K)) := by
    intro y
    have hycomm : Subgroup.inclusion hJ.1 y ∈ commutator ↥(fixSubgroup β) := by
      rw [← CFSG.StandardType.ggCommutator_subgroupOf (fixSubgroup β)]
      exact hJH ▸ y.2
    have himg : g y ∈ (commutator ↥(fixSubgroup β)).map φ.toMonoidHom :=
      Subgroup.mem_map_of_mem _ hycomm
    rw [CFSG.StandardType.ggMap_commutator_of_surjective φ.toMonoidHom φ.surjective,
      hcomm] at himg
    exact himg
  let f : ↥J →* ↥((CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K)).subgroupOf
      (CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K))) := g.codRestrict _ hmem
  have hf_inj : Function.Injective f := by
    intro a b hab
    have h1 : g a = g b := congrArg Subtype.val hab
    have h2 : (Subgroup.inclusion hJ.1 a : ↥(fixSubgroup β)) = Subgroup.inclusion hJ.1 b :=
      φ.injective h1
    exact Subtype.ext (congrArg (fun z : ↥(fixSubgroup β) => (z : Y)) h2)
  have hf_surj : Function.Surjective f := by
    intro w
    have hw : (w : ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K))) ∈
        (commutator ↥(fixSubgroup β)).map φ.toMonoidHom := by
      rw [CFSG.StandardType.ggMap_commutator_of_surjective φ.toMonoidHom φ.surjective, hcomm]
      exact w.2
    obtain ⟨z, hz, hwz⟩ := hw
    have hzJ : (z : Y) ∈ J := by
      rw [hJH]
      exact ((CFSG.StandardType.ggCommutatorEquiv (fixSubgroup β)).symm ⟨z, hz⟩).2
    refine ⟨⟨(z : Y), hzJ⟩, ?_⟩
    apply Subtype.ext
    show g ⟨(z : Y), hzJ⟩ = (w : ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K)))
    have h1 : (Subgroup.inclusion hJ.1 ⟨(z : Y), hzJ⟩ : ↥(fixSubgroup β)) = z := Subtype.ext rfl
    rw [show g ⟨(z : Y), hzJ⟩ = φ (Subgroup.inclusion hJ.1 ⟨(z : Y), hzJ⟩) from rfl, h1]
    exact hwz
  refine ⟨(MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩).trans (Subgroup.subgroupOfEquivOfLe hSP), ?_⟩
  intro y
  rfl

end PGUThree

section PGUThreeAct

open CFSG.RankThree.PartTwo


theorem t158Core_mem_innAutDerived_of_isoPGU {Y : Type} [Group Y] {β : MulAut Y} {K : Type} [Field K]
    [Finite K] (hKcard : Nat.card K = (2 ^ 3) ^ 2)
    (φ : ↥(fixSubgroup β) ≃* CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K))
    {J : Subgroup Y} (hJ : IsComponentOf J (fixSubgroup β))
    {x : MulAut Y} (hxstab : x ∈ CFSG.GroupActions.subgroupStabAut J)
    {s : Y} (hs : s ∈ fixSubgroup β) {j : ℕ} (hxeq : x = MulAut.conj s * β ^ j) :
    centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J ⟨x, hxstab⟩) ∈
      innAutDerived (↥J ⧸ Subgroup.center ↥J) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Sec4.PiField false 2 3 K :=
    ⟨Nat.prime_two, by norm_num, by simpa [Sec4.piCard] using hKcard⟩
  have hq2 : 2 < (2 : ℕ) ^ 3 := by norm_num
  have hJH := t158Core_component_eq_commutator_of_isoPGU hKcard φ hJ
  obtain ⟨eJ, eJ_apply⟩ := t158Core_exists_mulEquiv_projImage_slPi hKcard φ hJ hJH
  let α : MulAut ↥J := CFSG.GroupActions.subgroupStabRestrict J ⟨x, hxstab⟩
  have hαy : ∀ y : ↥J, ((α y : ↥J) : Y) = s * (y : Y) * s⁻¹ := by
    intro y
    have hpow : ∀ n : ℕ, (β ^ n) (y : Y) = y := by
      intro n
      have hy : β (y : Y) = y := (mem_fixSubgroup).1 (hJ.1 y.2)
      induction n with
      | zero => rw [pow_zero, MulAut.one_apply]
      | succ n ih => rw [pow_succ, MulAut.mul_apply, hy, ih]
    show ((CFSG.GroupActions.subgroupStabRestrict J ⟨x, hxstab⟩ y : ↥J) : Y) = _
    rw [CFSG.GroupActions.subgroupStabRestrict_apply]
    change x (y : Y) = _
    rw [hxeq, MulAut.mul_apply, hpow j, MulAut.conj_apply]
  have hαeq : ∀ y : ↥J, (⟨(α y : ↥J), hJ.1 (α y).2⟩ : ↥(fixSubgroup β)) =
      ⟨s, hs⟩ * ⟨(y : Y), hJ.1 y.2⟩ * ⟨s, hs⟩⁻¹ := by
    intro y
    apply Subtype.ext
    exact hαy y
  let sH : ↥(fixSubgroup β) := ⟨s, hs⟩
  obtain ⟨A, hA, hAeq⟩ := (φ sH).2
  have hconjJ : ∀ y : ↥J,
      ((eJ (α y) : ↥(CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K))) :
          Matrix.ProjGenLinGroup (Fin 3) K) =
        Matrix.ProjGenLinGroup.mk A * ((eJ y : ↥(CFSG.PGLModel.projImage
          (Sec4.slPi false 3 (2 ^ 3) K))) : Matrix.ProjGenLinGroup (Fin 3) K) *
          (Matrix.ProjGenLinGroup.mk A)⁻¹ := by
    intro y
    rw [eJ_apply, eJ_apply]
    calc (φ ⟨(α y : ↥J), hJ.1 (α y).2⟩ : Matrix.ProjGenLinGroup (Fin 3) K)
        = φ (sH * ⟨(y : Y), hJ.1 y.2⟩ * sH⁻¹) := by rw [hαeq y]
      _ = φ sH * φ ⟨(y : Y), hJ.1 y.2⟩ * (φ sH)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
          rfl
      _ = Matrix.ProjGenLinGroup.mk A * φ ⟨(y : Y), hJ.1 y.2⟩ *
            (Matrix.ProjGenLinGroup.mk A)⁻¹ := by
          rw [hAeq]
          rfl
  have hαmem : α ∈ innAutDerived ↥J :=
    KD264Lie.mem_innAutDerived_of_conj_projImage_slPi (p := 2) (f := 3) hK hq2 eJ hA hconjJ
  exact CFSG.ComponentClassification.PerfectCentralQuotient.centerQuotientHom_mem_innAutDerived hαmem

end PGUThreeAct

section Transfer


theorem t158Core_transfer {Ω : Type} [Group Ω] [Finite Ω] {S L : Subgroup Ω} {x : Ω}
    (hxN : x ∈ Subgroup.normalizer (S : Set Ω)) (hx3 : x ^ 3 = 1)
    (hL : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x} : Set Ω)) L)
    (hU : catalogIs (PSimple 3 L) S9.isU3eight) :
    GLAPComponent 3 (fixSubgroup (chevAut 3 S ⟨x, hxN⟩)) (chevTransfer 3 S L) ∧
      Nonempty (PSimple 3 L ≃* PSimple 3 (chevTransfer 3 S L)) ∧
      Nat.card (PSimple 3 (chevTransfer 3 S L)) = 5515776 := by
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hx3
  obtain ⟨eJ⟩ := nonempty_pSimple_equiv_chevTransfer Nat.prime_three hxN hxp hL
  refine ⟨glaPComponent_chevTransfer Nat.prime_three hxN hxp hL, ⟨eJ⟩, ?_⟩
  rw [← Nat.card_congr eJ.toEquiv]
  exact CatSingle.card_isU3eight CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hU

end Transfer

section Restrict


theorem t158Core_false_of_restrict {Ω : Type} [Group Ω] [Finite Ω] {S L₁ : Subgroup Ω} {x₁ x₂ : Ω}
    (hN1 : x₁ ∈ Subgroup.normalizer (S : Set Ω)) (hN2 : x₂ ∈ Subgroup.normalizer (S : Set Ω))
    (hx1 : x₁ ^ 3 = 1) (hL1 : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x₁} : Set Ω)) L₁)
    (hU1 : catalogIs (PSimple 3 L₁) S9.isU3eight) (hF21 : FieldOn 3 x₂ L₁)
    (hTq : CFSG.Open.IsQuasisimple ↥(chevTransfer 3 S L₁))
    (hmem : ∀ hstab : MI.indAut 3 S x₂ hN2 ∈ CFSG.GroupActions.subgroupStabAut (chevTransfer 3 S L₁),
      centerQuotientHom ↥(chevTransfer 3 S L₁)
          (CFSG.GroupActions.subgroupStabRestrict (chevTransfer 3 S L₁) ⟨_, hstab⟩) ∈
        innAutDerived (↥(chevTransfer 3 S L₁) ⧸ Subgroup.center ↥(chevTransfer 3 S L₁))) : False := by
  have hJK : L₁ ≤ S := hL1.1.trans inf_le_left
  have hgS : x₂⁻¹ ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.inv_mem _ hN2
  have hgJ : x₂⁻¹ ∈ Subgroup.normalizer (L₁ : Set Ω) := Subgroup.inv_mem _ hF21.1
  have hstab : MI.indAut 3 S x₂ hN2 ∈ CFSG.GroupActions.subgroupStabAut (chevTransfer 3 S L₁) :=
    t158Core_chevAut_mem_stab hJK hgS hgJ
  obtain ⟨hT1, -, -⟩ := t158Core_transfer hN1 hx1 hL1 hU1
  let π : ↥L₁ →* ↥(chevTransfer 3 S L₁) :=
    ((chevQuotHom 3 S).comp (Subgroup.inclusion hJK)).codRestrict (chevTransfer 3 S L₁)
      (fun j => ⟨Subgroup.inclusion hJK j, Subgroup.mem_subgroupOf.2 j.2, rfl⟩)
  have hπval : ∀ j : ↥L₁, ((π j : ↥(chevTransfer 3 S L₁)) : PSimple 3 S) =
      chevQuotHom 3 S (Subgroup.inclusion hJK j) := fun j => rfl
  have hπ : Function.Surjective π := by
    rintro ⟨t, k, hk, rfl⟩
    exact ⟨⟨k, Subgroup.mem_subgroupOf.1 hk⟩, rfl⟩
  obtain ⟨ι, hι⟩ := CFSG.LocalAnalysis.GLTheoremA.I141F.u9_exists_pSimple_equiv_centerQuot
    Nat.prime_three (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL1) hTq
    (isQuasisimple_nontrivial (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hT1)) π hπ
  have hν : MulAut.congr ι.symm (centerQuotientHom ↥(chevTransfer 3 S L₁)
      (CFSG.GroupActions.subgroupStabRestrict (chevTransfer 3 S L₁) ⟨_, hstab⟩)) =
      MI.indAut 3 L₁ x₂ hF21.1 := by
    ext s
    obtain ⟨j, rfl⟩ := chevQuotHom_surjective 3 L₁ s
    set j' : ↥L₁ := L₁.normalizerMonoidHom ⟨x₂⁻¹, hgJ⟩ j with hj'
    have h1 : ι (chevQuotHom 3 L₁ j) = QuotientGroup.mk (π j) := hι j
    have h5 : ι (chevQuotHom 3 L₁ j') = QuotientGroup.mk (π j') := hι j'
    have h2 : CFSG.GroupActions.subgroupStabRestrict (chevTransfer 3 S L₁) ⟨_, hstab⟩ (π j) = π j' := by
      apply Subtype.ext
      rw [CFSG.GroupActions.subgroupStabRestrict_apply, hπval j, hπval j']
      change chevAut 3 S ⟨x₂⁻¹, hgS⟩ (chevQuotHom 3 S (Subgroup.inclusion hJK j)) = _
      rw [chevAut_chevQuotHom]
      congr 1
    have h3 : MI.indAut 3 L₁ x₂ hF21.1 (chevQuotHom 3 L₁ j) = chevQuotHom 3 L₁ j' :=
      chevAut_chevQuotHom 3 L₁ ⟨x₂⁻¹, hgJ⟩ j
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_symm, h1,
      h3, MulEquiv.symm_apply_eq, h5, ← h2]
    exact CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk _ (π j)
  have hmem' : MI.indAut 3 L₁ x₂ hF21.1 ∈ innAutDerived (PSimple 3 L₁) := by
    rw [← hν]
    exact (mem_innAutDerived_congr ι.symm).2 (hmem hstab)
  exact (MI.field_nonInnDiag_holds Nat.prime_three (by norm_num) hF21).2
    (CFSG.LocalAnalysis.GLTheoremA.I141F.u9_innDiagOn_of_indAut_mem_innAutDerived hF21.1
      (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL1) hU1 hmem')

theorem t158Core_not_inner {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {x : Ω}
    (hSc : GLAPComponent 3 S S) (hchev : IsChevSimple 2 (PSimple 3 S)) (hnon : NonInnDiag 3 x S) :
    chevAut 3 S ⟨x, hnon.1⟩ ∉ inner (PSimple 3 S) := by
  intro h
  have hq := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hSc
  have h' : MI.indAut 3 S x hnon.1 ∈ inner (PSimple 3 S) := by
    rw [t158Core_indAut_eq_inv hnon.1]
    exact Subgroup.inv_mem _ h
  exact hnon.2 (MI.inner_innDiag_any hSc hchev hnon.1 ((MI.indAut_mem_inner_iff_any hq hnon.1).1 h'))

end Restrict

section TriCore


theorem t158Core_tri_d4 {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {x₁ x₂ : Ω}
    {L₁ L₂ : Subgroup Ω} (hSn : S.Normal) (hq : CFSG.Open.IsQuasisimple ↥S)
    (hcore : GLAPPrimeCore 3 ↥S = ⊥) (hD : catalogIs (PSimple 3 S) T158Inn.isD4Eight)
    (hx1 : x₁ ^ 3 = 1) (hx2 : x₂ ^ 3 = 1) (hc : x₁ * x₂ = x₂ * x₁) (hnon : NonInnDiag 3 x₁ S)
    (hL1 : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x₁} : Set Ω)) L₁)
    (hU1 : catalogIs (PSimple 3 L₁) S9.isU3eight)
    (hL2 : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x₂} : Set Ω)) L₂)
    (hU2 : catalogIs (PSimple 3 L₂) S9.isU3eight) (hF21 : FieldOn 3 x₂ L₁) : False := by
  classical
  have hSc : GLAPComponent 3 S S :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_self_of_quasisimple hq hcore
  obtain ⟨hsimple, hna⟩ := chev_pSimple_simple_nonabelian Nat.prime_three hSc
  haveI := hsimple
  have hN : ∀ y : Ω, y ∈ Subgroup.normalizer (S : Set Ω) := fun y => by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact Subgroup.mem_top y
  set β := chevAut 3 S ⟨x₁, hN x₁⟩ with hβdef
  set γ := chevAut 3 S ⟨x₂, hN x₂⟩ with hγdef
  have hβ3 : β ^ 3 = 1 := chevAut_pow_eq_one 3 S (hN x₁) hx1
  have hγ3 : γ ^ 3 = 1 := chevAut_pow_eq_one 3 S (hN x₂) hx2
  have hβγ : β * γ = γ * β := by
    rw [hβdef, hγdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc
  obtain ⟨hT1, ⟨eT1⟩, hcT1⟩ := t158Core_transfer (hN x₁) hx1 hL1 hU1
  obtain ⟨hT2, -, hcT2⟩ := t158Core_transfer (hN x₂) hx2 hL2 hU2
  have h19T1 : 19 ∣ Nat.card ↥(chevTransfer 3 S L₁) := by
    have h : 19 ∣ Nat.card (PSimple 3 (chevTransfer 3 S L₁)) := by rw [hcT1]; norm_num
    exact h.trans (t158Core_card_pSimple_dvd _)
  have h19T2 : 19 ∣ Nat.card ↥(chevTransfer 3 S L₂) := by
    have h : 19 ∣ Nat.card (PSimple 3 (chevTransfer 3 S L₂)) := by rw [hcT2]; norm_num
    exact h.trans (t158Core_card_pSimple_dvd _)
  obtain ⟨i, hi, ⟨eS⟩⟩ := hD
  obtain ⟨q, hv, rfl, hq2, hq3⟩ := t158Core_d4Eight_index hi
  have hchar : (⟨.D 4 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic = 2 := by
    rw [TauCeti.LieTypeIndex.characteristic_D]
    exact hq2
  have hchev : IsChevSimple 2 (PSimple 3 S) :=
    Or.inl ⟨TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩, hchar, ⟨eS⟩⟩
  let F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩)
  haveI : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hFcard : Nat.card F = 2 ^ 3 := by
    change Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) = 2 ^ 3
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent,
      TauCeti.LieTypeIndex.characteristic_D, TauCeti.LieTypeIndex.fieldExponent_D, hq2, hq3]
  let e : PSimple 3 S ≃* adjointGroup Tag.D4 F :=
    eS.trans ((CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q hv).trans
      (CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup F).some)
  have hmem : ∀ {α : MulAut (PSimple 3 S)}, α ^ 3 = 1 → ∀ {P : Subgroup (PSimple 3 S)},
      P ≤ fixSubgroup α → ⁅P, P⁆ = P → 19 ∣ Nat.card P → α ∈ innAutDerived (PSimple 3 S) := by
    intro α hα3 P hP hperf h19
    refine (mem_innAutDerived_congr e).1 (t158Core_d4Eight_mem_innAutDerived hFcard
      (α := MulAut.congr e α) (by rw [← map_pow, hα3, map_one])
      (P := P.map (e : PSimple 3 S →* adjointGroup Tag.D4 F)) ?_ ?_ ?_)
    · rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr]
      exact Subgroup.map_mono hP
    · rw [← Subgroup.map_commutator, hperf]
    · rw [Subgroup.card_map_of_injective e.injective]
      exact h19
  have hβmem := hmem hβ3 hT1.1 (glaPComponent_perfect hT1) h19T1
  have hγmem := hmem hγ3 hT2.1 (glaPComponent_perfect hT2) h19T2
  have hβout : β ∉ inner (PSimple 3 S) := t158Core_not_inner hSc hchev hnon
  have hβ1 : β ≠ 1 := fun h => hβout (h ▸ Subgroup.one_mem _)
  have hpil := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent (PSimple 3 S)
    hsimple hna ⟨.D 4 q, hv⟩ ⟨eS⟩ 3 Nat.prime_three (by decide) (by rw [hchar]; decide) β hβ3 hβ1
  have hTle := hpil _ hT1.1 (glaPComponent_perfect hT1)
  have hTc := (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hT1 hTle).1
  obtain ⟨q8, hv8, hq8, ⟨e8⟩⟩ := CatB.lieIndex_isU3eight hU1
  obtain ⟨eTZ⟩ := I141F.centerQuot_equiv_pSimple Nat.prime_three hT1 hTc.2.2
  have hCA : KD264Lie.CompAlgAtWith (PSimple 3 S) (fun β _ => β ∉ inner (PSimple 3 S)) :=
    KD264Lie.compAlgAtWith_of_mulEquiv e.symm
      (fun β _ h hβ => h ((congr_mem_inner_iff e.symm β).2 hβ))
      (KD264Lie.compAlgAtWith_d4Eight_graph hFcard)
  refine t158Core_false_of_restrict (hN x₁) (hN x₂) hx1 hL1 hU1 hF21 hTc.2.2 (fun hstab => ?_)
  have hγinv : MI.indAut 3 S x₂ (hN x₂) = γ⁻¹ := t158Core_indAut_eq_inv (hN x₂)
  have hxmem : MI.indAut 3 S x₂ (hN x₂) ∈ innAutDerived (PSimple 3 S) := by
    rw [hγinv]
    exact Subgroup.inv_mem _ hγmem
  have hx3 : (MI.indAut 3 S x₂ (hN x₂)) ^ 3 = 1 := by rw [hγinv, inv_pow, hγ3, inv_one]
  have hβx : β * MI.indAut 3 S x₂ (hN x₂) = MI.indAut 3 S x₂ (hN x₂) * β := by
    rw [hγinv]
    exact (Commute.inv_right hβγ).eq
  exact hCA β hβmem hβ3 hβ1 _ hTc ⟨.twistedA 2 q8, hv8⟩ ⟨q8, Or.inr rfl, hq8⟩
    ⟨eTZ.trans (eT1.symm.trans e8)⟩ _ hxmem hx3 hβx hβout hstab

theorem t158Core_tri_td4 {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {x₁ x₂ : Ω}
    {L₁ : Subgroup Ω} (hSn : S.Normal) (hq : CFSG.Open.IsQuasisimple ↥S)
    (hcore : GLAPPrimeCore 3 ↥S = ⊥) (hD : catalogIs (PSimple 3 S) T158Inn.isTD4Eight)
    (hx1 : x₁ ^ 3 = 1) (hx2 : x₂ ^ 3 = 1) (hc : x₁ * x₂ = x₂ * x₁) (hnon : NonInnDiag 3 x₁ S)
    (hL1 : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x₁} : Set Ω)) L₁)
    (hU1 : catalogIs (PSimple 3 L₁) S9.isU3eight) (hF21 : FieldOn 3 x₂ L₁) : False := by
  classical
  have hSc : GLAPComponent 3 S S :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_self_of_quasisimple hq hcore
  obtain ⟨hsimple, hna⟩ := chev_pSimple_simple_nonabelian Nat.prime_three hSc
  haveI := hsimple
  have hN : ∀ y : Ω, y ∈ Subgroup.normalizer (S : Set Ω) := fun y => by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact Subgroup.mem_top y
  set β := chevAut 3 S ⟨x₁, hN x₁⟩ with hβdef
  set γ := chevAut 3 S ⟨x₂, hN x₂⟩ with hγdef
  have hβ3 : β ^ 3 = 1 := chevAut_pow_eq_one 3 S (hN x₁) hx1
  have hγ3 : γ ^ 3 = 1 := chevAut_pow_eq_one 3 S (hN x₂) hx2
  have hβγ : β * γ = γ * β := by
    rw [hβdef, hγdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc
  obtain ⟨hT1, ⟨eT1⟩, hcT1⟩ := t158Core_transfer (hN x₁) hx1 hL1 hU1
  obtain ⟨i, hi, ⟨eS⟩⟩ := hD
  obtain ⟨q, hv, rfl, hq2, hq3⟩ := t158Core_td4Eight_index hi
  have hchar : (⟨.trialityD4 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic = 2 := by
    rw [TauCeti.LieTypeIndex.characteristic_trialityD4]
    exact hq2
  have hchev : IsChevSimple 2 (PSimple 3 S) :=
    Or.inl ⟨TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩, hchar, ⟨eS⟩⟩
  have hβout : β ∉ inner (PSimple 3 S) := t158Core_not_inner hSc hchev hnon
  have hβ1 : β ≠ 1 := fun h => hβout (h ▸ Subgroup.one_mem _)
  have hpil := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent (PSimple 3 S)
    hsimple hna ⟨.trialityD4 q, hv⟩ ⟨eS⟩ 3 Nat.prime_three (by decide) (by rw [hchar]; decide) β hβ3
    hβ1
  have hTle := hpil _ hT1.1 (glaPComponent_perfect hT1)
  have hTc := (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hT1 hTle).1
  obtain ⟨eTZ⟩ := I141F.centerQuot_equiv_pSimple Nat.prime_three hT1 hTc.2.2
  have hJcard : Nat.card (↥(chevTransfer 3 S L₁) ⧸ Subgroup.center ↥(chevTransfer 3 S L₁)) = 5515776 := by
    rw [Nat.card_congr eTZ.toEquiv]
    exact hcT1
  obtain ⟨K, hKf, hKfin, σ, hK, hσ, ⟨Θ, hker⟩, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  letI := hKf
  letI := hKfin
  rw [hq2, hq3] at hK hσ
  let e : PSimple 3 S ≃* ↥(CFSG.LieType.Chevalley.graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    eS.trans eC
  let Θ' : MulAut (PSimple 3 S) →* (K ≃+* K) := Θ.comp (MulAut.congr e).toMonoidHom
  have hker' : ∀ α : MulAut (PSimple 3 S), Θ' α = 1 ↔ α ∈ inner (PSimple 3 S) := by
    intro α
    rw [← congr_mem_inner_iff e α]
    change Θ (MulAut.congr e α) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hker]
    rfl
  set x := MI.indAut 3 S x₂ (hN x₂) with hxdef
  have hγinv : x = γ⁻¹ := t158Core_indAut_eq_inv (hN x₂)
  have hx3 : x ^ 3 = 1 := by rw [hγinv, inv_pow, hγ3, inv_one]
  have hβx : β * x = x * β := by
    rw [hγinv]
    exact (Commute.inv_right hβγ).eq
  haveI : IsCyclic (K ≃+* K) := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  haveI : Finite (K ≃+* K) :=
    Finite.of_injective (fun f : K ≃+* K => (f : K → K)) (fun f g h => RingEquiv.ext (congrFun h))
  have hΘβ1 : Θ' β ≠ 1 := fun h => hβout ((hker' β).1 h)
  obtain ⟨j, -, hj⟩ := t158Core_pow_of_cyclic (a := Θ' β) (b := Θ' x)
    (by rw [← map_pow, hβ3, map_one]) hΘβ1 (by rw [← map_pow, hx3, map_one])
  obtain ⟨s, hs⟩ : x * (β ^ j)⁻¹ ∈ inner (PSimple 3 S) :=
    (hker' _).1 (by rw [map_mul, map_inv, map_pow, ← hj, mul_inv_cancel])
  have hxeq : x = MulAut.conj s * β ^ j := by
    rw [hs]
    group
  have hcen : Subgroup.center (PSimple 3 S) = ⊥ :=
    Y10F.center_centerQuot_eq_bot (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hSc)
  have hsfix : s ∈ fixSubgroup β := by
    rw [mem_fixSubgroup]
    have h1 : β * x = x * β := hβx
    rw [hxeq] at h1
    have h2 : MulAut.conj (β s) * β ^ (j + 1) = MulAut.conj s * β ^ (j + 1) := by
      calc MulAut.conj (β s) * β ^ (j + 1) = (β * MulAut.conj s) * β ^ j := by
            rw [CFSG.HardMathSupport.Lang.D4Three.mul_conj_eq (β := β) (g := s)]
            group
        _ = β * (MulAut.conj s * β ^ j) := by group
        _ = (MulAut.conj s * β ^ j) * β := h1
        _ = MulAut.conj s * β ^ (j + 1) := by group
    exact CFSG.mulAutConj_injective_of_center_eq_bot hcen (mul_right_cancel h2)
  have hβ'3 : (MulAut.congr e β) ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hβ'out : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut (MulAut.congr e β) :=
    fun h => hβout ((congr_mem_inner_iff e β).1 h)
  let eF : ↥(fixSubgroup β) ≃* ↥(fixSubgroup (MulAut.congr e β)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupCongrEquiv e β
  refine t158Core_false_of_restrict (hN x₁) (hN x₂) hx1 hL1 hU1 hF21 hTc.2.2 (fun hstab => ?_)
  have hk : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = 2 ^ 3 :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom (by norm_num) hK hσ
  haveI : Finite (CFSG.LieType.Chevalley.fixSubfield σ) := Subtype.finite
  rcases CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv
      (f := 3) (by norm_num) hK hσ hβ'3 hβ'out with ⟨ψ, hψ | hψ⟩ | he₂
  ·
    exfalso
    obtain ⟨eG⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_fixSubgroup_fieldActor_equiv_G2
      (ℓ := 2) (by norm_num) (by norm_num : 1 ≤ 3) (Or.inl rfl) hK σ hσ
    let eβ : ↥(fixSubgroup β) ≃* ↥(adjointGroup Tag.G2 (CFSG.LieType.Chevalley.fixSubfield σ)) :=
      eF.trans ((MulEquiv.subgroupCongr (by rw [hψ])).trans
        ((CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupConjEquiv ψ _).symm.trans eG))
    exact t158Core_false_of_component_G2_eight hk eβ hTc hJcard
  ·
    exfalso
    obtain ⟨eG⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_fixSubgroup_fieldActor_equiv_G2
      (ℓ := 2) (by norm_num) (by norm_num : 1 ≤ 3) (Or.inl rfl) hK σ hσ
    let eβ : ↥(fixSubgroup β) ≃* ↥(adjointGroup Tag.G2 (CFSG.LieType.Chevalley.fixSubfield σ)) :=
      eF.trans ((MulEquiv.subgroupCongr (by rw [hψ])).trans
        ((CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupConjEquiv ψ _).symm.trans
          ((MulEquiv.subgroupCongr
            (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq _)).trans eG)))
    exact t158Core_false_of_component_G2_eight hk eβ hTc hJcard
  ·
    obtain ⟨e₂⟩ := he₂
    obtain ⟨F, _, _, hF', ⟨e₃⟩⟩ :=
      CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0_holds 3 (by decide) K σ hK hσ
    have hfixφ : fixSubgroup (MulAut.congr e β) = CFSG.RankThree.PartTwo.Sec4.autFix (MulAut.congr e β) :=
      Subgroup.ext fun _ => Iff.rfl
    let φ : ↥(fixSubgroup β) ≃* CFSG.PGLModel.projImage (CFSG.RankThree.PartTwo.Sec4.glPi false 3 (2 ^ 3) F) :=
      eF.trans ((MulEquiv.subgroupCongr hfixφ).trans (e₂.trans e₃))
    exact t158Core_mem_innAutDerived_of_isoPGU hF' φ hTc hstab hsfix hxeq

theorem t158TriCore_holds : T158Inn.T158TriCore := by
  intro Ω _ _ S x₁ x₂ L₁ L₂ hSn hq hcore hD hx1 hx2 hc hnon _ hL1 hU1 hL2 hU2 _ hF21
  rcases hD with hD | hD
  · exact t158Core_tri_d4 hSn hq hcore hD hx1 hx2 hc hnon hL1 hU1 hL2 hU2 hF21
  · exact t158Core_tri_td4 hSn hq hcore hD hx1 hx2 hc hnon hL1 hU1 hF21

end TriCore

end CFSG.LocalAnalysis.GLTheoremA.T158Core

end
