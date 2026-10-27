module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Chev2Split
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.InnOrthSB
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.InnOrthFix
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.InnOrthModel
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnOrth
public import CFSG.LocalAnalysis.OddStandard.AltNoHeQuasisimple
public import CFSG.GroupTheory.IsComponentOfMap

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.GLTheoremB

theorem exists_component_of_isD42_two {S : Type} [Group S] [Finite S] {β : MulAut S}
    (hβ : PerfectInLayer β) {I : Subgroup S} (hI : GLAPComponent 3 (fixSubgroup β) I)
    (hD : IsCatalogLieIso (↥I ⧸ GLAPPrimeCore 3 ↥I) IsD42Index) :
    IsComponentOf I (fixSubgroup β) ∧
      IsCatalogLieIso (↥I ⧸ Subgroup.center ↥I) IsD42Index := by
  have hle : I ≤ GLALayer (fixSubgroup β) := hβ I hI.1 (glaPComponent_perfect hI)
  obtain ⟨hcomp, -⟩ := glaPComponent_isComponent_of_le_layer hI hle
  haveI : IsSimpleGroup (↥I ⧸ Subgroup.center ↥I) := hcomp.2.2.2
  have hmodel := CFSG.GH74.statedClassicalModel_of_lieModel (by decide) (lieModel_of_isD42 hD)
  haveI : IsSimpleGroup (↥I ⧸ GLAPPrimeCore 3 ↥I) :=
    (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_orthogonal_two
      _ .POmegaPlus (Or.inl rfl) 4 1 hmodel).2
  obtain ⟨e⟩ := CFSG.OddStandard.AltNoHe.mulEquiv_of_surjective hcomp.2.2.1
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥I)) (QuotientGroup.mk'_surjective _)
  obtain ⟨d, hd, ⟨eD⟩⟩ := hD
  exact ⟨hcomp, d, hd, ⟨e.trans eD⟩⟩

theorem exists_component_of_upD42Pumpup_conj_orthogonal {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) {n f : ℕ}
    (hG : StatedClassicalModel S t n 2 f) {x : S} (hx : UpD42Pumpup S (MulAut.conj x)) :
    x ^ 3 = 1 ∧ x ≠ 1 ∧ ∃ I : Subgroup S,
      IsComponentOf I (Subgroup.centralizer ({x} : Set S)) ∧
        IsCatalogLieIso (↥I ⧸ Subgroup.center ↥I) IsD42Index := by
  haveI := hs
  obtain ⟨hx3, hx1, I, hI, hD⟩ := hx
  have hZ : Subgroup.center S = ⊥ := up34_center_eq_bot_of_simple hnab
  have hxcube : x ^ 3 = 1 := by
    have h1 : MulAut.conj (x ^ 3) = 1 := by rw [map_pow]; exact hx3
    have h2 : x ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun φ : MulAut S => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    simpa only [hZ, Subgroup.mem_bot] using h2
  have hPIL : PerfectInLayer (MulAut.conj x) :=
    perfectInLayer_conj_omega (ht.elim (fun h => Or.inr (Or.inl h))
      (fun h => Or.inr (Or.inr h))) hG Nat.prime_three (by decide) (by decide) x hxcube
  obtain ⟨hcomp, hDI⟩ := exists_component_of_isD42_two hPIL hI hD
  rw [OrthBlocks.fixSubgroup_conj_eq_centralizer'] at hcomp
  exact ⟨hxcube, fun h => hx1 (by rw [h, map_one]), I, hcomp, hDI⟩

theorem exists_projOrth_component_of_upD42Pumpup {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) {n f : ℕ}
    (hG : StatedClassicalModel S t n 2 f) {x : S} (hx : UpD42Pumpup S (MulAut.conj x)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
      (_ : FiniteDimensional K V) (Q : QuadraticForm K V)
      (e : S ≃* CFSG.RankThree.Classical2.ProjOrthDerived Q),
      (QuadraticMap.polarBilin Q).Nondegenerate ∧
        (∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) ∧
        Module.finrank K V = 2 * n ∧ Nat.card K = 2 ^ f ∧
        (e x) ^ 3 = 1 ∧ e x ≠ 1 ∧
        ∃ I : Subgroup (CFSG.RankThree.Classical2.ProjOrthDerived Q),
          IsComponentOf I (Subgroup.centralizer ({e x} : Set _)) ∧
            IsCatalogLieIso (↥I ⧸ Subgroup.center ↥I) IsD42Index := by
  obtain ⟨hx3, hx1, I, hI, hD⟩ :=
    exists_component_of_upD42Pumpup_conj_orthogonal ht hs hnab hG hx
  obtain ⟨K, _, _, V, _, _, _, Q, hQ, hT, hdim, hK, ⟨e⟩⟩ :=
    Up34Chev2.exists_projOrth_model_two ht hG
  let J := I.map e.toMonoidHom
  have hJ : IsComponentOf J (Subgroup.centralizer ({e x} : Set _)) := by
    have h := CFSG.isComponentOf_map_mulEquiv e hI
    simpa only [CFSG.Walter.map_centralizer_mulEquiv, Set.image_singleton] using h
  let eI : ↥I ≃* ↥J := I.equivMapOfInjective e.toMonoidHom e.injective
  let eQ := QuotientGroup.congr _ _ eI (Subgroup.map_center_eq eI)
  obtain ⟨d, hd, ⟨eD⟩⟩ := hD
  refine ⟨K, inferInstance, inferInstance, V, inferInstance, inferInstance, inferInstance,
    Q, e, hQ, hT, hdim, hK, ?_, ?_, J, hJ, d, hd, ⟨eQ.symm.trans eD⟩⟩
  · rw [← map_pow, hx3, map_one]
  · exact fun h => hx1 (e.injective (h.trans (map_one e).symm))

open Polynomial Module CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial OrthBlocks

theorem rank_and_field_of_component_projOrth_two
    {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {n f : ℕ} (hdim : finrank K V = 2 * n) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {b : ProjOrthDerived Q} (hb : b ^ 3 = 1) (hb1 : b ≠ 1)
    {I : Subgroup (ProjOrthDerived Q)}
    (hI : CFSG.Open.IsComponentOf I (Subgroup.centralizer ({b} : Set _)))
    (hD : IsCatalogLieIso (↥I ⧸ Subgroup.center ↥I) IsD42Index) : 5 ≤ n ∧ f = 1 := by
  classical
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Nontrivial V := by
    obtain ⟨U, hU, -⟩ := hT
    exact Module.nontrivial_of_finrank_pos (R := K) (by
      have := Submodule.finrank_le U
      omega)
  have hpl : (3 : ℕ) ≠ ringChar K := by rw [ringChar.eq K 2]; decide
  obtain ⟨x, Rep, -, hxp, hx, hRep, hNeq, hcases⟩ :=
    exists_lift_isComponentOf_centralizer_cases hQ hT Nat.prime_three (by decide) hpl
      (orderOf_eq_prime hb hb1)
  let xe : V ≃ₗ[K] V := x
  rcases hcases I hI with ⟨h, hh, hne1, hq, hIeq⟩ |
      ⟨-, m, C, hsup, -, -, i, hIeq⟩
  · have hhp : h ∈ primaryFactors xe.toLinearMap := hRep.1 hh
    haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hhp⟩
    have hFΩ : specialBlock Q xe h ≤ orthDerived Q :=
      specialBlock_le_orthDerived_of_perfect hq.1
        ((specialBlock_le_isometryCentralizer h).trans
          (fun _ hg => (Subgroup.mem_inf.mp hg).1))
    have hinj := CFSG.RankThree.PartOne.S15K.mk_injective_orth hQ
    let eF : ↥(specialBlock Q xe h) ≃* ↥I :=
      (((Subgroup.subgroupOfEquivOfLe hFΩ).symm.trans
        (((specialBlock Q xe h).subgroupOf (orthDerived Q)).equivMapOfInjective _ hinj)).trans
        (MulEquiv.subgroupCongr hIeq.symm))
    let eQ := QuotientGroup.congr _ _ eF.symm (Subgroup.map_center_eq eF.symm)
    have hDF : IsCatalogLieIso
        (↥(specialBlock Q xe h) ⧸ Subgroup.center ↥(specialBlock Q xe h)) IsD42Index := by
      obtain ⟨d, hd, ⟨eD⟩⟩ := hD
      exact ⟨d, hd, ⟨eQ.symm.trans eD⟩⟩
    exact (false_of_specialBlock_isD42 hf hK hx hhp hne1 hq hDF).elim
  · have hIle : I ≤ fixedComponentImage Q xe := by
      rw [← hsup, hIeq]
      exact le_iSup C i
    rw [hNeq] at hI
    have hLN : fixedComponentImage Q xe ≤ centralizerImage Q xe :=
      fixedComponentImage_le_centralizerImage
    have hIc : CFSG.Assembly.IsComponentOf I (fixedComponentImage Q xe) :=
      (CFSG.Assembly.isComponentOf_iff_open.2 hI).of_le_of_le hIle hLN
    have hIc' : CFSG.IsComponent (I.subgroupOf (fixedComponentImage Q xe)) :=
      (isComponentOf_iff_isComponent_subgroupOf hIle).1 hIc
    let φ := CFSG.RankThree.PartOne.fixedComponentImageEquiv hQ hx
    have hM : CFSG.IsComponent ((I.subgroupOf (fixedComponentImage Q xe)).map φ.toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv φ hIc'
    let eI : ↥I ≃* ↥(I.subgroupOf (fixedComponentImage Q xe)) :=
      (Subgroup.subgroupOfEquivOfLe hIle).symm
    let eM := (I.subgroupOf (fixedComponentImage Q xe)).equivMapOfInjective
      φ.toMonoidHom φ.injective
    let e := eI.trans eM
    let eQ := QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
    have hDM : IsCatalogLieIso
        (↥((I.subgroupOf (fixedComponentImage Q xe)).map φ.toMonoidHom) ⧸
          Subgroup.center ↥((I.subgroupOf (fixedComponentImage Q xe)).map φ.toMonoidHom))
        IsD42Index := by
      obtain ⟨d, hd, ⟨eD⟩⟩ := hD
      exact ⟨d, hd, ⟨eQ.symm.trans eD⟩⟩
    obtain ⟨hf1, hfix⟩ := d42_orthogonal_layer hK _ hx.polarBilin_fixed_nondegenerate hM hDM
    have hxne : xe ≠ 1 := by
      intro h
      have hx1 : x = 1 := Subtype.ext h
      rw [hx1, orderOf_one] at hxp
      omega
    exact ⟨five_le_of_finrank_fixedSpace_eq_eight hdim hfix hxne, hf1⟩

theorem rank_and_field_of_upD42Pumpup_conj_orthogonal {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) {n f : ℕ}
    (hG : StatedClassicalModel S t n 2 f) {x : S} (hx : UpD42Pumpup S (MulAut.conj x)) :
    5 ≤ n ∧ f = 1 := by
  obtain ⟨K, _, _, V, _, _, _, Q, e, hQ, hT, hdim, hK, hb, hb1, I, hI, hD⟩ :=
    exists_projOrth_component_of_upD42Pumpup ht hs hnab hG hx
  exact rank_and_field_of_component_projOrth_two hQ hT hdim hG.1.2.1 hK hb hb1 hI hD

theorem upD42Chev2Inn_orthogonal_holds : UpD42Chev2Inn
    (fun d => match d with | .D _ _ | .twistedD _ _ => True | _ => False) := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ x hx
  cases d with
  | D r q =>
    have hq2 : q.p = 2 := hc
    have hm := blueprintLieModel_D r q hv e
    have hr : 4 ≤ r := (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hm).2.2
    have hC := CFSG.GH74.statedClassicalModel_of_lieModel (by omega) hm
    rw [hq2] at hC
    obtain ⟨hn, hf⟩ := rank_and_field_of_upD42Pumpup_conj_orthogonal (Or.inl rfl) hs hnab hC hx
    exact Or.inl ⟨⟨.D r q, hv⟩, ⟨hn, hq2, hf⟩, ⟨e⟩⟩
  | twistedD r q =>
    have hq2 : q.p = 2 := hc
    have hm := blueprintLieModel_twistedD r q hv e
    have hr : 4 ≤ r := (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hm).2.2
    have hC := CFSG.GH74.statedClassicalModel_of_lieModel (by omega) hm
    rw [hq2] at hC
    obtain ⟨hn, hf⟩ := rank_and_field_of_upD42Pumpup_conj_orthogonal (Or.inr rfl) hs hnab hC hx
    exact Or.inl ⟨⟨.twistedD r q, hv⟩, ⟨hn, hq2, hf⟩, ⟨e⟩⟩
  | _ => exact hF.elim

end CFSG.HardMathSupport.Dickson.Sec6

end
