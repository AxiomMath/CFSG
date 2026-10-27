module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256o
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzRest
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.G2EvenOuterTypeDet
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MITD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I161a2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256o

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple PSimple)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256m (IsGF4Type)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover (EvenScope)

theorem isChevIndexTwo_of_characteristic {d : TauCeti.LieTypeIndex} (h : d.characteristic = 2) :
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevIndexTwo d := by
  cases d <;> simp_all [CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevIndexTwo]

section SeitzCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.StandardType.ChevTwo (blueprintLieModel_of_modelsLieModel untwistedChevalleyModel_of_bridge
  twistedChevalleyModel_of_bridge)


theorem not_iso_evenScope_of_gf4Rest {S : Type} [Group S] {d : TauCeti.ValidLieTypeIndex}
    (hd : d.1.characteristic = 2 ∧ Inputs256c.defField d.1 = 4 ∧ ¬ EvenScope d.1 ∧
      ¬ ∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ¬ ∃ d' : TauCeti.ValidLieTypeIndex, EvenScope d'.1 ∧
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d').Group) := by
  rintro ⟨d', hs', ⟨e'⟩⟩
  obtain ⟨t', n', f', ht', hadm', -, -, hM'⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.exists_blueprintLieModel_of_scope d' hs'
  have hc' := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder (CFSG.Blueprint.LieModel.of_mulEquiv e'.symm hM')
  obtain ⟨hd2, hd4, hns, hnu⟩ := hd
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
  obtain ⟨d, hv⟩ := d
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hdup := ((TauCeti.LieTypeIndex.valid_iff _).mp hv).2
  cases d with
  | A r q =>
    have hp : q.p = 2 := by simpa using hd2
    have hq4 : q.card = 4 := hd4
    have hr1 : r = 1 := by
      have h1 : ¬ (q.p = 2 ∧ 2 ≤ r) := hns
      have := hr.1
      by_contra h
      exact h1 ⟨hp, by omega⟩
    apply hdup
    rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact Or.inl ⟨hr1, Or.inl hq4⟩
  | twistedA r q =>
    have hp : q.p = 2 := by simpa using hd2
    have hr2 : r = 2 := by
      have h1 : ¬ (q.p = 2 ∧ 3 ≤ r) := hns
      have := hr.1
      by_contra h
      exact h1 ⟨hp, by omega⟩
    subst hr2
    exact hnu ⟨q, rfl⟩
  | B r q => exact hns (show q.p = 2 by simpa using hd2)
  | C r q => exact hr.2 (by simpa using hd2)
  | D r q => exact hns (show q.p = 2 by simpa using hd2)
  | E6 q => exact hns (show q.p = 2 by simpa using hd2)
  | E7 q => exact hns (show q.p = 2 by simpa using hd2)
  | E8 q => exact hns (show q.p = 2 by simpa using hd2)
  | F4 q => exact hns (show q.p = 2 by simpa using hd2)
  | twistedE6 q => exact hns (show q.p = 2 by simpa using hd2)
  | twistedD r q =>
    have hp : q.p = 2 := by simpa using hd2
    have hq4 : q.card = 4 := hd4
    obtain ⟨-, he2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 2)
      Nat.prime_two (by norm_num) (hq4.trans (by norm_num))
    have h := CFSG.Models.lieModel_twistedD r q hv e
    rw [hp, he2] at h
    have hM := blueprintLieModel_of_modelsLieModel (by simp [classicalTags]) h
    rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM] at hc'
    obtain ⟨rfl, -, -⟩ := CFSG.SeitzReduction.OmegaPilot.evenLieOrder_eq_ordTwistedD hadm' hr (by norm_num)
      hc'.symm
    exact ht'
  | G2 q =>
    have hp : q.p = 2 := by simpa using hd2
    have hq4 : q.card = 4 := hd4
    obtain ⟨-, he2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 2)
      Nat.prime_two (by norm_num) (hq4.trans (by norm_num))
    have h3 : 3 ≤ 2 ^ q.exponent := by
      have h3 : 3 ≤ q.card := hr
      rwa [TauCeti.PrimePower.card_def, hp] at h3
    have hM : CFSG.Blueprint.LieModel S .G2 0 2 q.exponent :=
      .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags], ⟨Nat.prime_two, q.exponent_pos, rfl, h3⟩,
        untwistedChevalleyModel_of_bridge hB.g2 q hv hp e⟩)
    rw [he2] at hM
    rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM] at hc'
    obtain ⟨rfl, -⟩ := CFSG.EvenSporadicStandard.Induction.evenLieOrder_eq_ordG2 hadm' (le_refl 2) hc'.symm
    exact ht'
  | trialityD4 q =>
    have hp : q.p = 2 := by simpa using hd2
    have hM : CFSG.Blueprint.LieModel S .trialityD4 0 2 q.exponent :=
      .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags], ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
        twistedChevalleyModel_of_bridge hB.trialityD4 q hv hp e⟩)
    rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM] at hc'
    have := CFSG.LocalAnalysis.GLTheoremA.MI.evenLieOrder_eq_ordTrialityD4 hadm' q.exponent_pos hc'.symm
    subst this
    exact ht'
  | suzuki m => exact (Inputs256m.two_pow_odd_ne_four_pow (m := m) (k := 1) (by rw [pow_one]; exact hd4)).elim
  | reeF4 m => exact (Inputs256m.two_pow_odd_ne_four_pow (m := m) (k := 1) (by rw [pow_one]; exact hd4)).elim
  | reeG2 m => exact absurd hd2 (by simp)
  | tits => exact absurd hd4 (by simp [Inputs256c.defField])

theorem gen2313On_gf4_of_seitzCubeRest (h : CFSG.LocalAnalysis.GLTheoremA.Y10F.SeitzCubeRest) :
    Inputs256m.Gen2313On (fun d => d.1.characteristic = 2 ∧ Inputs256c.defField d.1 = 4 ∧ ¬ EvenScope d.1 ∧
      ¬ ∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q) := by
  intro S _ _ d hd he E hE hE9 hU
  obtain ⟨e⟩ := he
  have hS : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevTwo S :=
    Or.inl ⟨d, isChevIndexTwo_of_characteristic hd.1, ⟨e⟩⟩
  have hE0 : E ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hE9
    norm_num at hE9
  exact h S hS (not_iso_evenScope_of_gf4Rest hd e) 3 Nat.prime_three (by norm_num) E hE hE0
    (by rw [hE9]; norm_num) hU

end SeitzCube

section Core


theorem sporGF4_of_b3BNoGF4 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable) (hB : B3BNoGF4) :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSporType s S → ∀ α : MulAut S, α ^ 3 = 1 →
      ∀ I : Subgroup S, GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) I →
        ¬ IsGF4Type (PSimple 3 I) := by
  intro S _ _ hS hnc s hs α hα I hI
  by_cases hα1 : α = 1
  · subst hα1
    rw [Claims1116b.fixSubgroup_one_eq_top] at hI
    haveI := hS
    obtain ⟨f⟩ := CFSG.LocalAnalysis.GLTheoremA.chevQ_pSimple_top_equiv Nat.prime_three hnc hI
    intro hG
    exact not_isGF4Type_of_sporadic hs.some (hG.of_mulEquiv f.symm)
  by_cases hsB : s = .B
  · subst hsB
    exact not_isGF4Type_of_gf4FreeAtThree hOut hS hnc hs
      (gf4FreeAtThree_of_carrier hbr (gf4FreeAtThree_B hB) hs) hα hα1 hI
  by_cases hsM : s = .M
  · subst hsM
    exact not_isGF4Type_of_gf4FreeAtThree hOut hS hnc hs
      (gf4FreeAtThree_of_carrier hbr gf4FreeAtThree_M hs) hα hα1 hI
  by_cases hsJ : s = .J1
  · subst hsJ
    have hcard : Nat.card S = CFSG.HardMathSupport.Solomon.Coordinator.sporOrd .J1 :=
      (Nat.card_congr hs.some.toEquiv).trans (hOrd .J1)
    exact not_isGF4Type_of_gf4FreeAtThree hOut hS hnc hs
      (gf4FreeAtThree_of_not_sq_dvd (by rw [hcard]; decide)) hα hα1 hI
  exact not_isGF4Type_of_rows (crow_three_of_ne hOut hbr hb s hsB hsM hsJ)
    (typeRow_three_of_ne hOut hbr hb s hsB hsM hsJ) hs hα hα1 hI

end Core

section PCentralFree

theorem dvd_card_center_of_isComponent_of_pCentral {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {z : X} (hzo : orderOf z = p) (hzc : z ∈ Subgroup.center X) {P : Subgroup X}
    (hP : Nat.card P = p ^ (Nat.card X).factorization p)
    (hZ : ∀ c ∈ P, (∀ g ∈ P, c * g = g * c) → c ∈ Subgroup.zpowers z)
    (hO : CFSG.pPrimeCore p X = ⊥) {K : Subgroup X} (hK : CFSG.IsComponent K) :
    p ∣ Nat.card (Subgroup.center K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hK3
  let S : Set (Subgroup X) := {L | CFSG.IsComponent L ∧ ¬ p ∣ Nat.card (Subgroup.center L)}
  let E : Subgroup X := sSup S
  have hS : ∀ (g : X), ∀ L ∈ S, L.map (MulAut.conj g).toMonoidHom ∈ S := by
    intro g L hL
    refine ⟨CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hL.1, ?_⟩
    rw [← Nat.card_congr (Subgroup.centerCongr
      (L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)).toEquiv]
    exact hL.2
  haveI hEn : E.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hle : E ≤ E.comap (MulAut.conj g).toMonoidHom :=
      sSup_le fun L hL => Subgroup.map_le_iff_le_comap.1 (le_sSup (hS g L hL))
    have h := hle hn
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  have hKE : K ≤ E := le_sSup ⟨hK, hK3⟩
  haveI : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  have hEne : E ≠ ⊥ := fun h =>
    (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance (le_bot_iff.1 (h ▸ hKE))
  have hpE : p ∣ Nat.card E := by
    by_contra h
    have hcop : Nat.Coprime p (Nat.card E) := (Nat.Prime.coprime_iff_not_dvd hp).2 h
    have hle : E ≤ CFSG.pPrimeCore p X := le_sSup ⟨hEn, hcop⟩
    rw [hO] at hle
    exact hEne (le_bot_iff.1 hle)
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := E) p hpE
  have hy : orderOf (e : X) = p := by rw [Subgroup.orderOf_coe]; exact he
  let Sy : Sylow p X := Sylow.ofCard P hP
  obtain ⟨c, hc⟩ :=
    CFSG.HardMathSupport.Dickson.I271.PCentralLayer.exists_conj_mem_sylow_of_orderOf Sy hy
  have hcP : c * (e : X) * c⁻¹ ∈ P := hc
  have hcE : c * (e : X) * c⁻¹ ∈ E := hEn.conj_mem _ e.2 c
  have hco : orderOf (c * (e : X) * c⁻¹) = p := by
    rw [← MulAut.conj_apply]
    exact (orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective _).trans hy
  have hcne : c * (e : X) * c⁻¹ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hco
    exact hp.one_lt.ne hco
  have hPp : IsPGroup p P := IsPGroup.of_card hP
  haveI : Group.IsNilpotent ↥P := IsPGroup.isNilpotent hPp
  have hHne : E.subgroupOf P ≠ ⊥ := by
    intro h
    have : (⟨c * (e : X) * c⁻¹, hcP⟩ : P) ∈ E.subgroupOf P := hcE
    rw [h, Subgroup.mem_bot] at this
    exact hcne (congrArg Subtype.val this)
  have hmeet := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := P) hHne
  obtain ⟨⟨w, hwE, hwZ⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hmeet
  have hwcomm : ∀ g ∈ P, (w : X) * g = g * w := fun g hg =>
    (congrArg Subtype.val ((Subgroup.mem_center_iff.1 hwZ) ⟨g, hg⟩)).symm
  have hwz : (w : X) ∈ Subgroup.zpowers z := hZ w w.2 hwcomm
  have hwne : (w : X) ≠ 1 := fun h => hw1 (Subtype.ext (Subtype.ext h))
  have hzcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hzo]
  have hwo : orderOf (w : X) = p := by
    have hd : orderOf (w : X) ∣ p := hzcard ▸ Subgroup.orderOf_dvd_natCard _ hwz
    rcases (Nat.dvd_prime hp).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hwne
    · exact h
  have hzw : Subgroup.zpowers (w : X) = Subgroup.zpowers z := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hwz) ?_
    rw [hzcard, Nat.card_zpowers, hwo]
  have hzE : z ∈ E := by
    have : z ∈ Subgroup.zpowers (w : X) := hzw ▸ Subgroup.mem_zpowers z
    have hwE' : (w : X) ∈ E := hwE
    exact (Subgroup.zpowers_le.2 hwE') this
  let F : Subgroup (∀ L : CFSG.LocalCores.ComponentIndex X, L.1) :=
    Subgroup.pi {L | p ∣ Nat.card (Subgroup.center L.1)} fun _ => ⊥
  have hEF : E ≤ F.map (CFSG.LocalCores.layerMul X) := by
    refine sSup_le fun L hL l hl => ?_
    refine ⟨Pi.mulSingle ⟨L, hL.1⟩ ⟨l, hl⟩, (Subgroup.mem_pi _).2 fun M hM => ?_,
      CFSG.LocalCores.layerMul_mulSingle _ _⟩
    by_cases h : M = ⟨L, hL.1⟩
    · subst h
      exact absurd hM hL.2
    · rw [Pi.mulSingle_eq_of_ne h]
      exact one_mem _
  obtain ⟨x, hxF, hxz⟩ := hEF hzE
  have hxc : ∀ L, x L ∈ Subgroup.center L.1 := fun L =>
    Subgroup.mem_center_iff.2 fun k => Subtype.ext
      ((CFSG.LocalCores.commute_layerMul_iff x L k.2).1 (by
        rw [hxz]
        exact Subgroup.mem_center_iff.1 hzc (k : X))).eq
  obtain ⟨N, hN⟩ : ∃ N, N = Nat.card X / p ^ (Nat.card X).factorization p := ⟨_, rfl⟩
  have hxN : x ^ N = 1 := by
    funext L
    rw [Pi.pow_apply, Pi.one_apply]
    by_cases hL : p ∣ Nat.card (Subgroup.center L.1)
    · have h1 : x L ∈ (⊥ : Subgroup L.1) := (Subgroup.mem_pi _).1 hxF L hL
      rw [Subgroup.mem_bot] at h1
      rw [h1, one_pow]
    · have hdvd : orderOf (x L) ∣ Nat.card (Subgroup.center L.1) :=
        Subgroup.orderOf_dvd_natCard (Subgroup.center L.1) (hxc L)
      have hdX : Nat.card (Subgroup.center L.1) ∣ Nat.card X :=
        (Subgroup.card_subgroup_dvd_card (Subgroup.center L.1)).trans
          (Subgroup.card_subgroup_dvd_card L.1)
      have hcop : Nat.Coprime (Nat.card (Subgroup.center L.1)) (p ^ (Nat.card X).factorization p) :=
        Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hL).symm
      have hdN : Nat.card (Subgroup.center L.1) ∣ N := by
        have hmul := Nat.ordProj_mul_ordCompl_eq_self (Nat.card X) p
        rw [← hmul] at hdX
        rw [hN]
        exact hcop.dvd_of_dvd_mul_left hdX
      exact orderOf_dvd_iff_pow_eq_one.1 (hdvd.trans hdN)
  have hzN : z ^ N = 1 := by rw [← hxz, ← map_pow, hxN, map_one]
  have hpN : p ∣ N := hzo ▸ orderOf_dvd_of_pow_eq_one hzN
  rw [hN] at hpN
  exact Nat.not_dvd_ordCompl hp Nat.card_pos.ne' hpN

theorem dvd_card_center_of_isComponentOf_of_pCentral {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {C : Subgroup G} {z : G} (hzC : z ∈ C) (hcent : ∀ g ∈ C, g * z = z * g)
    (hzo : orderOf z = p) {P : Subgroup G} (hPC : P ≤ C)
    (hP : Nat.card P = p ^ (Nat.card C).factorization p)
    (hZ : ∀ c ∈ P, (∀ g ∈ P, c * g = g * c) → c ∈ Subgroup.zpowers z)
    (hO : GLAPPrimeCoreOf p C = ⊥) {J : Subgroup G} (hJ : CFSG.Open.IsComponentOf J C) :
    p ∣ Nat.card (Subgroup.center ↥J) := by
  have hJC : J ≤ C := hJ.1
  have hcomp : CFSG.Assembly.IsComponentOf J C := CFSG.Assembly.isComponentOf_iff_open.2 hJ
  have hK : CFSG.IsComponent (J.subgroupOf C) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJC).1 hcomp
  have hzo' : orderOf (⟨z, hzC⟩ : C) = p := (Subgroup.orderOf_mk z hzC).trans hzo
  have hzc : (⟨z, hzC⟩ : C) ∈ Subgroup.center C :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcent g g.2)
  have hP' : Nat.card (P.subgroupOf C) = p ^ (Nat.card C).factorization p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv).trans hP
  have hZ' : ∀ c ∈ P.subgroupOf C, (∀ g ∈ P.subgroupOf C, c * g = g * c) →
      c ∈ Subgroup.zpowers (⟨z, hzC⟩ : C) := by
    intro c hc hcomm
    have hcP : (c : G) ∈ P := hc
    have h1 := hZ (c : G) hcP fun g hg =>
      congrArg Subtype.val (hcomm ⟨g, hPC hg⟩ (show (⟨g, hPC hg⟩ : C) ∈ P.subgroupOf C from hg))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩
  have h := dvd_card_center_of_isComponent_of_pCentral hp hzo' hzc hP' hZ'
    (CFSG.HardMathSupport.Dickson.I271.PCentralLayer.pPrimeCore_eq_bot_of_glaPPrimeCoreOf hO) hK
  rwa [Nat.card_congr (Subgroup.centerCongr (Subgroup.subgroupOfEquivOfLe hJC)).toEquiv] at h

theorem card_center_map_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (J : Subgroup G) :
    Nat.card (Subgroup.center ↥(J.map φ.toMonoidHom)) = Nat.card (Subgroup.center ↥J) :=
  (Nat.card_congr (Subgroup.centerCongr (φ.subgroupMap J)).toEquiv).symm

theorem seven_dvd_four_pow_cube_sub_one (m : ℕ) : 7 ∣ (4 ^ m) ^ 3 - 1 := by
  have h1 : (4 ^ m) ^ 3 = 64 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h1]
  exact (by norm_num : 7 ∣ 64 - 1).trans (Nat.sub_one_dvd_pow_sub_one 64 m)

theorem seven_dvd_ordA_four_pow {r : ℕ} (hr : 2 ≤ r) (m : ℕ) : 7 ∣ CFSG.Open.ordA r (4 ^ m) := by
  unfold CFSG.Open.ordA
  apply Nat.dvd_div_of_mul_dvd
  refine Dvd.dvd.mul_left ?_ _
  have h23 : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 (r + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_Icc]
    omega
  have hprod := Finset.prod_dvd_prod_of_subset _ _ (fun i => (4 ^ m) ^ i - 1) h23
  rw [Finset.prod_pair (by norm_num)] at hprod
  refine (?_ : Nat.gcd (r + 1) (4 ^ m - 1) * 7 ∣ ((4 ^ m) ^ 2 - 1) * ((4 ^ m) ^ 3 - 1)).trans hprod
  exact mul_dvd_mul ((Nat.gcd_dvd_right _ _).trans (Nat.sub_one_dvd_pow_sub_one _ 2))
    (seven_dvd_four_pow_cube_sub_one m)

theorem seven_dvd_orderE6_four_pow (m : ℕ) : 7 ∣ CFSG.Open.orderE6 (4 ^ m) := by
  have h7 : 7 ∣ (4 ^ m) ^ 6 - 1 := by
    refine (seven_dvd_four_pow_cube_sub_one m).trans ?_
    rw [show (4 ^ m) ^ 6 = ((4 ^ m) ^ 3) ^ 2 by ring]
    exact Nat.sub_one_dvd_pow_sub_one _ 2
  unfold CFSG.Open.orderE6
  apply Nat.dvd_div_of_mul_dvd
  have h : Nat.gcd 3 (4 ^ m - 1) * 7 ∣ ((4 ^ m) ^ 6 - 1) * ((4 ^ m) ^ 2 - 1) := by
    rw [mul_comm (Nat.gcd 3 (4 ^ m - 1)) 7]
    exact mul_dvd_mul h7 ((Nat.gcd_dvd_right _ _).trans (Nat.sub_one_dvd_pow_sub_one _ 2))
  exact h.trans (mul_dvd_mul (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) dvd_rfl)

end PCentralFree

section SevenGF4


theorem seven_dvd_of_isGF4Type_of_three_dvd_center (hGA : CFSG.Open.GriessAllModelsStatement)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {K : Type} [Group K] [Finite K] (hq : CFSG.IsQuasisimple K)
    (h3 : 3 ∣ Nat.card (Subgroup.center K)) (hG : IsGF4Type (K ⧸ Subgroup.center K)) :
    7 ∣ Nat.card (K ⧸ Subgroup.center K) := by
  obtain ⟨d, hd2, hk, ⟨e⟩⟩ := hG
  obtain ⟨t, n, f, hM, ⟨m, rfl⟩, -⟩ := Inputs256m.exists_lieModel_two_even_of_gf4 d hd2 hk e
  have hm := CFSG.LocalAnalysis.GLTheoremA.I161aNames.lieModel_models_of_blueprint hM
  have htab := h3.trans (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.center_dvd_table hGA hq
    (MulEquiv.refl _) hm)
  have h4 : (2 : ℕ) ^ (m + m) = 4 ^ m := by rw [← two_mul, pow_mul]; norm_num
  have h3m : 3 ∣ 4 ^ m - 1 := by simpa using Nat.sub_one_dvd_pow_sub_one 4 m
  have h4pos : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
  rcases CFSG.HardMathSupport.Dickson.I271.ThreeCentralTable.three_dvd_table_cases htab with
    ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
    ⟨-, -, h, -⟩
  ·
    obtain ⟨-, -, hn2, -⟩ := hm.1
    have hn3 : 3 ∣ n := (Nat.dvd_gcd_iff.1 h).1
    have hn : 3 ≤ n := by omega
    rw [CFSG.GH74.card_of_lieModel_PSL (by omega) hM, h4]
    exact seven_dvd_ordA_four_pow (by omega) m
  ·
    have h' := (Nat.dvd_gcd_iff.1 h).2
    rw [h4] at h'
    generalize 4 ^ m = a at h' h3m h4pos
    omega
  ·
    obtain ⟨-, hc | ⟨-, ⟨idx, hv⟩, hnames, ⟨e'⟩⟩⟩ := hm
    · exact hc.2.elim
    · cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i q
      obtain ⟨hqp, hqe⟩ := hnames
      have hord := hb ⟨.E6 q, hv⟩ (K ⧸ Subgroup.center K) ⟨e'⟩
      simp only [CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula,
        TauCeti.PrimePower.card_def] at hord
      rw [hord, hqp, hqe, h4]
      exact seven_dvd_orderE6_four_pow m
  ·
    rw [h4] at h
    generalize 4 ^ m = a at h h3m h4pos
    omega
  all_goals exact absurd h (by norm_num)

end SevenGF4

section BabyThreeB


theorem b3BNoGF4_holds
    : B3BNoGF4 := by
  intro s hs hunv J hJ hG
  haveI : Finite CFSG.Blueprint.NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨z, hz3, hzrk, ⟨P, hPC, hPcard, hPZ⟩, -⟩ := CFSG.HardMathSupport.Dickson.I271.exists_z_sylow_aut
  have hzc : IsConj z (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.phiB
      (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.t3 1)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.B3B.isConj_phiB_t3_one_of_rk hz3 hzrk
  have hsc : IsConj s (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.phiB
      (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.t3 1)) :=
    CFSG.HardMathSupport.Dickson.I271.uninverted_isConj_phiB_t3_one hs hunv
  obtain ⟨c, hc⟩ := isConj_iff.1 (hsc.trans hzc.symm)
  have hOs : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set CFSG.Blueprint.NativeSporadic.B)) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.oPrimeCoreTrivialAt_B_three s hs
  have hJc : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({s} : Set CFSG.Blueprint.NativeSporadic.B)) :=
    CFSG.HardMathSupport.Dickson.I271.isComponentOf_of_glaPComponent_of_core hOs hJ
  have hcoreJ : GLAPPrimeCore 3 ↥J = ⊥ := by
    have h1 : GLAPPrimeCoreOf 3 J = ⊥ := le_bot_iff.1
      ((CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal 3 hJc.2.1).trans hOs.le)
    exact (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).1 h1
  have hGJ : IsGF4Type (↥J ⧸ Subgroup.center ↥J) := by
    obtain ⟨d, hd2, hk, ⟨e⟩⟩ := hG
    exact ⟨d, hd2, hk, ⟨(CFSG.HardMathSupport.Dickson.I271.pSimpleEquivCenterQuot J hcoreJ).symm.trans e⟩⟩
  have hJz : CFSG.Open.IsComponentOf (J.map (MulAut.conj c).toMonoidHom)
      (Subgroup.centralizer ({z} : Set CFSG.Blueprint.NativeSporadic.B)) := by
    have h := CFSG.HardMathSupport.Solomon.Coordinator.bmInv_isComponentOf_map (MulAut.conj c) hJc
    rwa [MulAut.conj_apply, hc] at h
  have h3z := dvd_card_center_of_isComponentOf_of_pCentral Nat.prime_three
    (Subgroup.mem_centralizer_singleton_iff.2 rfl)
    (fun g hg => Subgroup.mem_centralizer_singleton_iff.1 hg) hz3 hPC hPcard hPZ
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.oPrimeCoreTrivialAt_B_three z hz3) hJz
  have h3 : 3 ∣ Nat.card (Subgroup.center ↥J) := by
    rw [← card_center_map_mulEquiv (MulAut.conj c) J]
    exact h3z
  have hq := hJc.2.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥J hq
  have hq' : CFSG.IsQuasisimple ↥J := ⟨⟨hq.1⟩, hq.2, hnab⟩
  have h7 := seven_dvd_of_isGF4Type_of_three_dvd_center
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hq' h3 hGJ
  have hC : ¬ 7 ∣ Nat.card (Subgroup.centralizer ({s} : Set CFSG.Blueprint.NativeSporadic.B)) := by
    rw [CFSG.Monster.Existence.natCard_centralizer_eq_of_isConj hsc]
    exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal.bThreeB_seven_free
  refine hC ((h7.trans ?_).trans (Subgroup.card_dvd_of_le hJc.1))
  exact Dvd.intro _ (Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)).symm

end BabyThreeB

@[expose] def GF4CompsRest : Prop :=
  Inputs256m.GF4CompsOn (fun d => d.1.characteristic = 2 ∧ Inputs256c.defField d.1 = 4 ∧
    (¬ ∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q) ∧ ¬ ∃ (r : ℕ) (q : TauCeti.PrimePower), d.1 = .A r q)

@[expose] def Chev2GF4Rest2 : Prop :=
  CFSG.LocalAnalysis.GLTheoremA.Y10F.SeitzCubeRest ∧ GF4CompsRest

section Final


theorem sporGF4Three_of_b3BNoGF4 (hB : B3BNoGF4) :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSporType s S → ∀ α : MulAut S, α ^ 3 = 1 →
      ∀ I : Subgroup S, GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) I →
        ¬ IsGF4Type (PSimple 3 I) :=
  sporGF4_of_b3BNoGF4 CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds hB

end Final

section FinalBaby


theorem sporGF4Three_holds
    :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSporType s S → ∀ α : MulAut S, α ^ 3 = 1 →
      ∀ I : Subgroup S, GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) I →
        ¬ IsGF4Type (PSimple 3 I) :=
  sporGF4Three_of_b3BNoGF4 b3BNoGF4_holds

theorem chev2GF4Rest_of_rest2
    (h : Chev2GF4Rest2) : Inputs256m.Chev2GF4Rest :=
  ⟨gen2313On_gf4_of_seitzCubeRest h.1, h.2, sporGF4Three_holds⟩

end FinalBaby

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256o

end
