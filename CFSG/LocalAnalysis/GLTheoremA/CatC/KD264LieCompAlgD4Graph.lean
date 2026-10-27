module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgClassical
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedD4
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4GraphFieldNF
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgExcCore
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzBal2
import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcComp
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofCent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.HardMathSupport.Lang.D4Three
open CFSG.LieType.SeitzGeneration.ExcWideThree


theorem exists_conj_of_hasNF_zero {F : Type} [Field F] [Finite F] (h2 : ringChar F = 2)
    {α : MulAut (adjointGroup Tag.D4 F)} (h : HasNF α 0 1) :
    ∃ s : adjointGroup Tag.D4 F, α = MulAut.conj s := by
  obtain ⟨g, a, rfl⟩ := h
  obtain ⟨d, hd⟩ :=
    CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.exactNormalAut_eq_conj_of_charTwo
      h2 a
  refine ⟨g * d, ?_⟩
  rw [CFSG.HardMathSupport.Lang.E6Descent.d4Graph_zero, mul_one, hd, ← map_mul]

theorem exists_conj_or_exists_conj_mul_d4Graph {F : Type} [Field F] [Finite F]
    (h2 : ringChar F = 2) {x : MulAut (adjointGroup Tag.D4 F)}
    (hx : x ∈ innAutDerived (adjointGroup Tag.D4 F)) (hx3 : x ^ 3 = 1) :
    (∃ s : adjointGroup Tag.D4 F, x = MulAut.conj s) ∨
      ∃ (ε : ℕ) (s : adjointGroup Tag.D4 F), (ε = 1 ∨ ε = 2) ∧
        x = MulAut.conj s * d4Graph F ε := by
  rcases CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived_D4_three_cases hx hx3 with
    ⟨h, rfl⟩ | ⟨g, a, ε, hε, rfl⟩
  · exact Or.inl ⟨h, rfl⟩
  · obtain ⟨d, hd⟩ :=
      CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.exactNormalAut_eq_conj_of_charTwo
        h2 a
    exact Or.inr ⟨ε, g * d, hε, by rw [hd, ← mul_assoc, ← map_mul]⟩

theorem exists_conj_mul_pow_of_mem_innAutDerived_D4 {F : Type} [Field F] [Finite F]
    (h2 : ringChar F = 2) {β x : MulAut (adjointGroup Tag.D4 F)}
    (hβ : β ∈ innAutDerived (adjointGroup Tag.D4 F)) (hβ3 : β ^ 3 = 1)
    (hβout : β ∉ inner (adjointGroup Tag.D4 F)) (hx : x ∈ innAutDerived (adjointGroup Tag.D4 F))
    (hx3 : x ^ 3 = 1) :
    ∃ (j : ℕ) (s : adjointGroup Tag.D4 F), j < 3 ∧ x = MulAut.conj s * β ^ j := by
  obtain ⟨g, a, ε, hε, hβeq⟩ :=
    (CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived_D4_three_cases hβ hβ3
      ).resolve_left (fun h => hβout ⟨h.choose, h.choose_spec.symm⟩)
  have hβNF : HasNF β ε 1 := ⟨g, a, hβeq⟩
  rcases exists_conj_or_exists_conj_mul_d4Graph h2 hx hx3 with ⟨s, rfl⟩ | ⟨ε', t, hε', hxeq⟩
  · exact ⟨0, s, by omega, by rw [pow_zero, mul_one]⟩
  · have hxNF : HasNF x ε' 1 := by
      refine ⟨t, 1, ?_⟩
      have hone : exactNormalAut Tag.D4 F (1 : Fin Tag.D4.rank → Fˣ) 1 0 = 1 := by
        rw [← CFSG.LieType.SeitzGeneration.ExcWideThree.rootDiagAut_eq_normalAut]
        exact (rootDiagAutHom Tag.D4 F).map_one
      rw [hxeq, hone, one_mul]
    rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl
    ·
      have hNF : HasNF (x * β ^ 2) (1 + 2) 1 := by
        rw [pow_two]
        simpa using HasNF.mul hxNF (HasNF.mul hβNF hβNF)
      obtain ⟨s, hs⟩ := exists_conj_of_hasNF_zero h2 (by simpa using hNF.mod_three)
      refine ⟨1, s, by omega, ?_⟩
      calc x = x * β ^ 3 := by rw [hβ3, mul_one]
        _ = x * β ^ 2 * β := by group
        _ = MulAut.conj s * β := by rw [hs]
    ·
      have hNF : HasNF (x * β) (2 + 1) 1 := by
        simpa using HasNF.mul hxNF hβNF
      obtain ⟨s, hs⟩ := exists_conj_of_hasNF_zero h2 (by simpa using hNF.mod_three)
      refine ⟨2, s, by omega, ?_⟩
      calc x = x * β ^ 3 := by rw [hβ3, mul_one]
        _ = x * β * β ^ 2 := by group
        _ = MulAut.conj s * β ^ 2 := by rw [hs]
    ·
      have hNF : HasNF (x * β) (1 + 2) 1 := by
        simpa using HasNF.mul hxNF hβNF
      obtain ⟨s, hs⟩ := exists_conj_of_hasNF_zero h2 (by simpa using hNF.mod_three)
      refine ⟨2, s, by omega, ?_⟩
      calc x = x * β ^ 3 := by rw [hβ3, mul_one]
        _ = x * β * β ^ 2 := by group
        _ = MulAut.conj s * β ^ 2 := by rw [hs]
    ·
      have hNF : HasNF (x * β ^ 2) (2 + (2 + 2)) 1 := by
        rw [pow_two]
        simpa using HasNF.mul hxNF (HasNF.mul hβNF hβNF)
      obtain ⟨s, hs⟩ := exists_conj_of_hasNF_zero h2 (by simpa using hNF.mod_three)
      refine ⟨1, s, by omega, ?_⟩
      calc x = x * β ^ 3 := by rw [hβ3, mul_one]
        _ = x * β ^ 2 * β := by group
        _ = MulAut.conj s * β := by rw [hs]

theorem mem_innAutDerived_of_conj_projImage_slPi {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hK : Sec4.PiField false p f K) (hq : 2 < p ^ f) {Y : Type} [Group Y]
    (e : Y ≃* CFSG.PGLModel.projImage (Sec4.slPi false 3 (p ^ f) K))
    {A : GL (Fin 3) K} (hA : A ∈ Sec4.glPi false 3 (p ^ f) K) {α : MulAut Y}
    (hconj : ∀ y : Y,
      ((e (α y) : CFSG.PGLModel.projImage (Sec4.slPi false 3 (p ^ f) K)) :
          Matrix.ProjGenLinGroup (Fin 3) K) =
        Matrix.ProjGenLinGroup.mk A * (e y : Matrix.ProjGenLinGroup (Fin 3) K) *
          (Matrix.ProjGenLinGroup.mk A)⁻¹) :
    α ∈ innAutDerived Y := by
  classical
  haveI := hK.finite
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact p.Prime := ⟨hK.prime⟩
  set β : MulAut (CFSG.PGLModel.projImage (Sec4.slPi false 3 (p ^ f) K)) :=
    MulAut.congr e α with hβ
  have hβeq : ∀ m : CFSG.PGLModel.projImage (Sec4.slPi false 3 (p ^ f) K),
      (β m : Matrix.ProjGenLinGroup (Fin 3) K) =
        Matrix.ProjGenLinGroup.mk A * (m : Matrix.ProjGenLinGroup (Fin 3) K) *
          (Matrix.ProjGenLinGroup.mk A)⁻¹ := by
    intro m
    obtain ⟨y, rfl⟩ := e.surjective m
    simpa [hβ, MulAut.congr_apply] using hconj y
  have hpsu := CFSG.RankThree.PartTwo.Sec11.KS11LieProof.congr_eq_psuConj hK hA hβeq
  have hmem : MulAut.congr (CFSG.RankThree.PartTwo.Sec4.psuEquivUnitary hK.unitary) β ∈
      innAutDerived (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hK.unitary 3) := by
    rw [hpsu]
    exact commutator_le_innAutDerived _
      (CFSG.HardMathSupport.Solomon.Coordinator.psuConj_mem_commutator
        (hF := hK.unitary) (p := p) (f := f) (K := K) hq
        ⟨A, CFSG.RankThree.PartTwo.KFacts.mem_unitaryIsom3.mpr
          ((Sec4.mem_glPi_false hK.unitary).mp hA)⟩)
  have hβmem : β ∈ innAutDerived
      (CFSG.PGLModel.projImage (Sec4.slPi false 3 (p ^ f) K)) :=
    (mem_innAutDerived_congr (CFSG.RankThree.PartTwo.Sec4.psuEquivUnitary hK.unitary)).1 hmem
  exact (mem_innAutDerived_congr e).1 (by rwa [hβ] at hβmem)

theorem false_of_component_adjointGroup_G2_eight {F F' : Type} [Field F] [Finite F]
    [Field F'] [Finite F'] (hF' : Nat.card F' = 2 ^ 3)
    {β : MulAut (adjointGroup Tag.D4 F)}
    (eG : ↥(fixSubgroup β) ≃* ↥(adjointGroup Tag.G2 F'))
    {J : Subgroup (adjointGroup Tag.D4 F)} (hJ : IsComponentOf J (fixSubgroup β))
    {e : TauCeti.ValidLieTypeIndex}
    (he : ∃ q : TauCeti.PrimePower, (e.1 = .A 1 q ∨ e.1 = .twistedA 2 q) ∧ q.card = 8)
    (hiso : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* (TauCeti.CFSGIndex.lie e).Group)) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF'3 : 3 ≤ Nat.card F' := by rw [hF']; norm_num
  have hG2simple : IsSimpleGroup ↥(adjointGroup Tag.G2 F') :=
    CFSG.LieType.SeitzGeneration.isSimpleGroup_adjointGroup_of_isQuasisimple
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card F' hF'3)
  have hsH : IsSimpleGroup ↥(fixSubgroup β) :=
    (MulEquiv.isSimpleGroup_congr eG).2 hG2simple
  haveI := hJ.2.2.2
  haveI : Nontrivial ↥J := (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).nontrivial
  have hJne : J ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot J).1 inferInstance
  have hJH : J = fixSubgroup β :=
    CFSG.StandardType.ggEq_of_isSubnormal_of_isSimpleGroup
      (CFSG.Assembly.isSubnormal_iff_open.2 hJ.2.1) hsH hJne
  let eJ' : ↥J ≃* ↥(adjointGroup Tag.G2 F') := (MulEquiv.subgroupCongr hJH).trans eG
  have hZ : Subgroup.center ↥J = ⊥ := by
    have hmap : (Subgroup.center ↥J).map eJ' =
        (⊥ : Subgroup ↥(adjointGroup Tag.G2 F')) := by
      rw [Subgroup.map_center_eq eJ', center_adjointGroup_eq_bot]
    exact (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center ↥J) eJ'.injective).1 hmap
  have hcardJ : Nat.card ↥J = ordG2 8 := by
    rw [Nat.card_congr eJ'.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2,
      hF']
    norm_num
  have hQcard : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordG2 8 := by
    rw [← hcardJ]
    exact Nat.card_congr
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv
  rcases card_eq_of_compAlgEight_kd264alg e he hiso with h | h
  · rw [hQcard] at h
    norm_num [ordG2] at h
  · rw [hQcard] at h
    norm_num [ordG2] at h

theorem component_eq_commutator_of_isoPGUThree {F K : Type} [Field F] [Finite F]
    [Field K] [Finite K] (hKcard : Nat.card K = (2 ^ 3) ^ 2)
    {β : MulAut (adjointGroup Tag.D4 F)}
    (φ : ↥(fixSubgroup β) ≃* CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K))
    {J : Subgroup (adjointGroup Tag.D4 F)} (hJ : IsComponentOf J (fixSubgroup β)) :
    J = ⁅fixSubgroup β, fixSubgroup β⁆ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Sec4.PiField false 2 3 K :=
    ⟨Nat.prime_two, by norm_num, by simpa [Sec4.piCard] using hKcard⟩
  have hq2 : 2 < (2 : ℕ) ^ 3 := by norm_num
  have hSP : CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K) ≤
      CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi (fun _ => hK.unitary))
  have hsimple : IsSimpleGroup
      ↥(CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K)) :=
    CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.isSimpleGroup_projImage_slPi hK hq2
  have hcomm := CFSG.RankThree.PartTwo.Sec13.commutator_projImage_glPi hK hq2
  have eComm : ↥(⁅fixSubgroup β, fixSubgroup β⁆ : Subgroup (adjointGroup Tag.D4 F)) ≃*
      ↥(CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K)) :=
    ((CFSG.StandardType.ggCommutatorEquiv (fixSubgroup β)).trans
      ((CFSG.StandardType.ggCommutatorCongr φ).trans
        ((MulEquiv.subgroupCongr hcomm).trans (Subgroup.subgroupOfEquivOfLe hSP))))
  have hsComm : IsSimpleGroup
      ↥(⁅fixSubgroup β, fixSubgroup β⁆ : Subgroup (adjointGroup Tag.D4 F)) :=
    (MulEquiv.isSimpleGroup_congr eComm).2 hsimple
  exact CFSG.StandardType.ggComponent_eq_commutator
    (CFSG.Assembly.isComponentOf_iff_open.2 hJ) hsComm

theorem exists_mulEquiv_projImage_slPi_of_eq_commutator {F K : Type} [Field F] [Finite F]
    [Field K] [Finite K] (hKcard : Nat.card K = (2 ^ 3) ^ 2)
    {β : MulAut (adjointGroup Tag.D4 F)}
    (φ : ↥(fixSubgroup β) ≃* CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K))
    {J : Subgroup (adjointGroup Tag.D4 F)} (hJ : IsComponentOf J (fixSubgroup β))
    (hJH : J = ⁅fixSubgroup β, fixSubgroup β⁆) :
    ∃ eJ : ↥J ≃* ↥(CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K)),
      ∀ y : ↥J, ((eJ y : ↥(CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K))) :
          Matrix.ProjGenLinGroup (Fin 3) K) =
        (φ ⟨(y : adjointGroup Tag.D4 F), hJ.1 y.2⟩ :
          Matrix.ProjGenLinGroup (Fin 3) K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Sec4.PiField false 2 3 K :=
    ⟨Nat.prime_two, by norm_num, by simpa [Sec4.piCard] using hKcard⟩
  have hq2 : 2 < (2 : ℕ) ^ 3 := by norm_num
  have hSP : CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K) ≤
      CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi (fun _ => hK.unitary))
  have hcomm := CFSG.RankThree.PartTwo.Sec13.commutator_projImage_glPi hK hq2
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
    exact Subtype.ext (congrArg (fun z : ↥(fixSubgroup β) =>
      (z : adjointGroup Tag.D4 F)) h2)
  have hf_surj : Function.Surjective f := by
    intro w
    have hw : (w : ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K))) ∈
        (commutator ↥(fixSubgroup β)).map φ.toMonoidHom := by
      rw [CFSG.StandardType.ggMap_commutator_of_surjective φ.toMonoidHom φ.surjective, hcomm]
      exact w.2
    obtain ⟨z, hz, hwz⟩ := hw
    have hzJ : (z : adjointGroup Tag.D4 F) ∈ J := by
      rw [hJH]
      exact ((CFSG.StandardType.ggCommutatorEquiv (fixSubgroup β)).symm ⟨z, hz⟩).2
    refine ⟨⟨(z : adjointGroup Tag.D4 F), hzJ⟩, ?_⟩
    apply Subtype.ext
    show g ⟨(z : adjointGroup Tag.D4 F), hzJ⟩ =
      (w : ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K)))
    have h1 : (Subgroup.inclusion hJ.1 ⟨(z : adjointGroup Tag.D4 F), hzJ⟩ :
        ↥(fixSubgroup β)) = z := Subtype.ext rfl
    rw [show g ⟨(z : adjointGroup Tag.D4 F), hzJ⟩ =
      φ (Subgroup.inclusion hJ.1 ⟨(z : adjointGroup Tag.D4 F), hzJ⟩) from rfl, h1]
    exact hwz
  refine ⟨(MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩).trans
    (Subgroup.subgroupOfEquivOfLe hSP), ?_⟩
  intro y
  rfl

theorem centerQuotientHom_mem_innAutDerived_of_isoPGUThree
    {F : Type} [Field F] [Finite F] {β : MulAut (adjointGroup Tag.D4 F)}
    {K : Type} [Field K] [Finite K] (hKcard : Nat.card K = (2 ^ 3) ^ 2)
    (φ : ↥(fixSubgroup β) ≃* CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K))
    {J : Subgroup (adjointGroup Tag.D4 F)} (hJ : IsComponentOf J (fixSubgroup β))
    {x : MulAut (adjointGroup Tag.D4 F)} (hxstab : x ∈ CFSG.GroupActions.subgroupStabAut J)
    {s : adjointGroup Tag.D4 F} (hs : s ∈ fixSubgroup β)
    {j : ℕ} (hxeq : x = MulAut.conj s * β ^ j) :
    centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J ⟨x, hxstab⟩) ∈
      innAutDerived (↥J ⧸ Subgroup.center ↥J) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Sec4.PiField false 2 3 K :=
    ⟨Nat.prime_two, by norm_num, by simpa [Sec4.piCard] using hKcard⟩
  have hq2 : 2 < (2 : ℕ) ^ 3 := by norm_num
  have hJH := component_eq_commutator_of_isoPGUThree hKcard φ hJ
  obtain ⟨eJ, eJ_apply⟩ :=
    exists_mulEquiv_projImage_slPi_of_eq_commutator hKcard φ hJ hJH
  let α : MulAut ↥J := CFSG.GroupActions.subgroupStabRestrict J ⟨x, hxstab⟩
  have hαy : ∀ y : ↥J, ((α y : ↥J) : adjointGroup Tag.D4 F) =
      s * (y : adjointGroup Tag.D4 F) * s⁻¹ := by
    intro y
    have hpow : ∀ n : ℕ, (β ^ n) (y : adjointGroup Tag.D4 F) = y := by
      intro n
      have hy : β (y : adjointGroup Tag.D4 F) = y := (mem_fixSubgroup).1 (hJ.1 y.2)
      induction n with
      | zero => rw [pow_zero, MulAut.one_apply]
      | succ n ih => rw [pow_succ, MulAut.mul_apply, hy, ih]
    show ((CFSG.GroupActions.subgroupStabRestrict J ⟨x, hxstab⟩ y : ↥J) :
        adjointGroup Tag.D4 F) = _
    rw [CFSG.GroupActions.subgroupStabRestrict_apply]
    change x (y : adjointGroup Tag.D4 F) = _
    rw [hxeq, MulAut.mul_apply, hpow j, MulAut.conj_apply]
  have hαeq : ∀ y : ↥J,
      (⟨(α y : ↥J), hJ.1 (α y).2⟩ : ↥(fixSubgroup β)) =
        ⟨s, hs⟩ * ⟨(y : adjointGroup Tag.D4 F), hJ.1 y.2⟩ * ⟨s, hs⟩⁻¹ := by
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
        = φ (sH * ⟨(y : adjointGroup Tag.D4 F), hJ.1 y.2⟩ * sH⁻¹) := by rw [hαeq y]
      _ = φ sH * φ ⟨(y : adjointGroup Tag.D4 F), hJ.1 y.2⟩ * (φ sH)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
          rfl
      _ = Matrix.ProjGenLinGroup.mk A * φ ⟨(y : adjointGroup Tag.D4 F), hJ.1 y.2⟩ *
            (Matrix.ProjGenLinGroup.mk A)⁻¹ := by
          rw [hAeq]
          rfl
  have hαmem : α ∈ innAutDerived ↥J :=
    mem_innAutDerived_of_conj_projImage_slPi (p := 2) (f := 3) hK hq2 eJ hA hconjJ
  exact CFSG.ComponentClassification.PerfectCentralQuotient.centerQuotientHom_mem_innAutDerived
    hαmem

theorem compAlgAtWith_d4Eight_graph {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 3) :
    CompAlgAtWith (adjointGroup Tag.D4 F)
      (fun β _ => β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (adjointGroup Tag.D4 F)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : ringChar F = 2 := by
    haveI : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (k := 3) (by norm_num) hF
    exact ringChar.eq F 2
  intro β hβmem hβ3 hβ1 J hJ e he hiso x hxmem hx3 hβx hβout hxstab
  obtain ⟨g, a, ε, hε, hβeq⟩ :=
    (CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived_D4_three_cases hβmem hβ3
      ).resolve_left (fun h => hβout ⟨h.choose, h.choose_spec.symm⟩)
  have hA : D4ElemType β (fun ε σ => ε ≠ 0 ∧ σ = 1) :=
    ⟨g, a, 1, ε, by omega, by simp, ⟨by omega, rfl⟩, hβeq⟩
  have hfix : CFSG.RankThree.PartOne.CTP.fixedSubgroup β = fixSubgroup β :=
    Subgroup.ext fun _ => Iff.rfl
  obtain ⟨j, s, -, hxeq⟩ :=
    exists_conj_mul_pow_of_mem_innAutDerived_D4 h2 hβmem hβ3 hβout hxmem hx3
  have hs : s ∈ fixSubgroup β := by
    have h1 : β * x = x * β := hβx
    rw [hxeq] at h1
    have h2 : MulAut.conj (β s) * β ^ (j + 1) = MulAut.conj s * β ^ (j + 1) := by
      calc MulAut.conj (β s) * β ^ (j + 1) = (β * MulAut.conj s) * β ^ j := by
            rw [CFSG.HardMathSupport.Lang.D4Three.mul_conj_eq (β := β) (g := s)]
            group
        _ = β * (MulAut.conj s * β ^ j) := by group
        _ = (MulAut.conj s * β ^ j) * β := h1
        _ = MulAut.conj s * β ^ (j + 1) := by group
    exact CFSG.mulAutConj_injective_of_center_eq_bot center_adjointGroup_eq_bot
      (mul_right_cancel h2)
  rcases CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz2.graphFix_cases hF hβ3 hA
    with ⟨F', hF'f, hF'fin, hF'card, ⟨eG⟩⟩ | ⟨K, hKf, hKfin, hKcard, ⟨ePGU⟩⟩
  · letI := hF'f
    letI := hF'fin
    have eG' : ↥(fixSubgroup β) ≃* ↥(adjointGroup Tag.G2 F') :=
      (MulEquiv.subgroupCongr hfix).symm.trans eG
    exact (false_of_component_adjointGroup_G2_eight hF'card eG' hJ he hiso).elim
  · letI := hKf
    letI := hKfin
    have φ : ↥(fixSubgroup β) ≃*
        CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K) :=
      (MulEquiv.subgroupCongr hfix).symm.trans ePGU
    exact centerQuotientHom_mem_innAutDerived_of_isoPGUThree hKcard φ hJ hxstab hs hxeq

@[expose] def D4EightTrialityInnerPairs : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ 3 →
    CompAlgAtWith (adjointGroup Tag.D4 F) (fun β x =>
      β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.D4 F) ∧
        x ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.D4 F))

theorem d4EightCompAlgOuter_of_trialityInnerPairs (hB : D4EightTrialityInnerPairs) :
    D4EightCompAlgOuter := by
  rintro ⟨d, hv⟩ ⟨q, rfl⟩ hfield
  classical
  let F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩)
  haveI : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hfieldD : fieldSize (.D 4 q) = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hq8 : q.p ^ q.exponent = 8 := hfieldD ▸ hfield
  have hFcard' : Nat.card F = q.p ^ q.exponent := by
    change Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) = q.p ^ q.exponent
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent,
      TauCeti.LieTypeIndex.characteristic_D, TauCeti.LieTypeIndex.fieldExponent_D]
  have hFcard : Nat.card F = 2 ^ 3 := by
    rw [hFcard', hq8]
    norm_num
  have e₁ := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid
    4 q hv
  have e₂ := (CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup
    F).some
  refine compAlgOuterAt_of_mulEquiv (e₁.trans e₂).symm ?_
  intro β hβmem hβ3 hβ1 J hJ e he hiso x hxmem hx3 hβx hR hxstab
  by_cases hβin : β ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.D4 F)
  · exact hB F hFcard β hβmem hβ3 hβ1 J hJ e he hiso x hxmem hx3 hβx
      ⟨hβin, fun hx => hR ⟨hβin, hx⟩⟩ hxstab
  · exact compAlgAtWith_d4Eight_graph hFcard β hβmem hβ3 hβ1 J hJ e he hiso x hxmem hx3 hβx
      hβin hxstab

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
