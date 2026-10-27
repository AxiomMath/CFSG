module

public import CFSG.CGT.PushingUpLit.CGT6.EmbK

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit CFSG.Quasithin
open CFSG.CGT.PushingUpLit.CGT6
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.SixThree
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def OmegaFourOutcomeSharp (V Y X : Subgroup G) : Prop :=
  oResidualTwo ↥X = ⊤ ∧ ⁅X, X⁆ = X ∧ CFSG.IsQuasisimple (↥Y ⧸ pCore 2 ↥Y) ∧ ⁅Y, Y⁆ = Y ∧
    ∃ n : ℕ, 2 ≤ n ∧
      (IsNatBy (omegaPlusAct n) X ⁅X, V⁆ ∨ IsNatBy (omegaMinusAct n) X ⁅X, V⁆) ∧
      (⁅X, V⁆ : Subgroup G) ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
      X ⊓ Subgroup.centralizer ((⁅X, V⁆ : Subgroup G) : Set G) ≤
        Subgroup.centralizer (V : Set G) ∧
      ¬ (Y.subgroupOf X).IsSubnormal ∧
      (∀ hV : IsElemAbelian 2 V, NatOmega hV n (autOn X V)) ∧
      autOn Y V ≤ autOn X V ∧ autOn Y V ≠ autOn X V ∧
      Nonempty (↥(autOn Y V) ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n)) ∧
      Nat.card ↥⁅Y, V⁆ = 2 ^ (3 * n)

theorem OmegaFourOutcomeSharp.toOmegaFourOutcome {V Y X : Subgroup G}
    (h : OmegaFourOutcomeSharp V Y X) : OmegaFourOutcome V Y X := by
  obtain ⟨h1, h2, -, -, n, hn, h3, h4, h5, h6, -⟩ := h
  exact ⟨h1, h2, n, hn, h3, h4, h5, h6⟩

@[expose] def AschbacherEmbeddingAmbK' : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.IsKGroup G → IsCharacteristicP 2 G →
    ∀ (Y V : Subgroup G), InClassX ↥Y → V.Normal → IsElementaryAbelian 2 V →
      ¬ Y ≤ Subgroup.centralizer (V : Set G) →
      (∃ P : Subgroup G, IsPGroup 2 P ∧ ¬ P ≤ Subgroup.centralizer (V : Set G) ∧
        Y ≤ Subgroup.normalizer ((P ⊔ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ∧
        (Y.subgroupOf (Subgroup.normalizer
          ((P ⊔ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))).IsSubnormal) →
      ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧
        Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (X : Set G) ∧
        IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G)) ∧
        ((InClassX ↥X ∧ ⁅oTwoIn X, X⁆ ≤ V ∧ ArrowNat Y X) ∨ OmegaFourOutcomeSharp V Y X)

section Concl

variable [Finite G]

theorem emb_concl_sharp (hMinus : EmbDictMinus) (hArrow : EmbDictArrow) (hOmega : EmbOmega)
    (hchar : IsCharacteristicP 2 G) {Y V : Subgroup G} [V.Normal] (hV : IsElemAbelian 2 V)
    (hY : InClassX ↥Y) (hVY : V ≤ Subgroup.normalizer (Y : Set G)) (hU : ⁅V, Y⁆ = ⁅oTwoIn Y, Y⁆)
    (hQU : ⁅pCore 2 G ⊓ Subgroup.centralizer (V : Set G), Y⁆ = ⁅oTwoIn Y, Y⁆)
    (hCY : Subgroup.centralizer (V : Set G) ≤ centralizerModCore Y)
    (Xh : Subgroup (MulAut ↥V)) (hYX : autOn Y V ≤ Xh) (hXG : Xh ≤ autOn (⊤ : Subgroup G) V)
    (hXs : (Xh.subgroupOf (autOn (⊤ : Subgroup G) V)).IsSubnormal)
    (hout : (InClassX ↥(yuHolOf hV Xh) ∧ ArrowNat (yuHolOf hV (autOn Y V)) (yuHolOf hV Xh)) ∨
      (CFSG.IsQuasisimple (↥Y ⧸ pCore 2 ↥Y) ∧ ⁅Y, Y⁆ = Y ∧ ∃ n : ℕ, 2 ≤ n ∧ NatOmega hV n Xh ∧
        (autOn Y V = Xh ∨ (Nonempty (↥(autOn Y V) ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n)) ∧
          Nat.card ↥(@commV ↥V (commGroupOfElemAbelian hV) (autOn Y V)) = 2 ^ (3 * n))))) :
    ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧
      Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (X : Set G) ∧
      IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G)) ∧
      ((InClassX ↥X ∧ ⁅oTwoIn X, X⁆ ≤ V ∧ ArrowNat Y X) ∨ OmegaFourOutcomeSharp V Y X) := by
  classical
  have hNo : SubTwo.NoTwoQuotient Y := SubTwo.noTwoQuotient_of_oResidualTwo hY.1.residual_eq
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV.2 v v.2)
  have hYhat : (Y.map (ambRho V)) = autOn Y V := map_ambRho V Y
  have hYXt : Y ≤ Xh.comap (ambRho V) := fun y hy => by
    apply hYX
    rw [← hYhat]
    exact ⟨y, hy, rfl⟩
  have hCXt : Subgroup.centralizer (V : Set G) ≤ Xh.comap (ambRho V) :=
    centralizer_le_comap_ambRho V Xh
  have hXtsub : (Xh.comap (ambRho V)).IsSubnormal := isSubnormal_comap_ambRho hXs
  have hXle : CGT6.conjClosure Y (Xh.comap (ambRho V)) ≤ Xh.comap (ambRho V) :=
    CGT6.conjClosure_le hYXt
  have hXsub : (CGT6.conjClosure Y (Xh.comap (ambRho V))).IsSubnormal :=
    CGT6.isSubnormal_conjClosure hYXt hXtsub
  have hCX : Subgroup.centralizer (V : Set G) ≤
      Subgroup.normalizer (CGT6.conjClosure Y (Xh.comap (ambRho V)) : Set G) :=
    hCXt.trans CGT6.le_normalizer_conjClosure
  obtain ⟨hQXV, hXCQ, hXCX⟩ := emb_conj_facts (Xt := Xh.comap (ambRho V)) hchar (hQU.trans hU.symm)
  have hX2 : IsPGroup 2
      ↥(CGT6.conjClosure Y (Xh.comap (ambRho V)) ⊓ Subgroup.centralizer (V : Set G)) :=
    (pCore_isPGroup (p := 2) (G := G)).to_le hXCQ
  have hres : oResidualTwo ↥(CGT6.conjClosure Y (Xh.comap (ambRho V))) = ⊤ :=
    CGT6.oResidualTwo_conjClosure hNo
  have hfit : generalizedFitting ↥(CGT6.conjClosure Y (Xh.comap (ambRho V))) =
      pCore 2 ↥(CGT6.conjClosure Y (Xh.comap (ambRho V))) :=
    generalizedFitting_eq_pCore_of_isSubnormal hchar hXsub
  have hρX : (CGT6.conjClosure Y (Xh.comap (ambRho V))).map (ambRho V) ≤ Xh :=
    Subgroup.map_le_iff_le_comap.mpr hXle
  have hρY : Y.map (ambRho V) ≤ (CGT6.conjClosure Y (Xh.comap (ambRho V))).map (ambRho V) :=
    Subgroup.map_mono CGT6.le_conjClosure
  have hρXn :
      (((CGT6.conjClosure Y (Xh.comap (ambRho V))).map (ambRho V)).subgroupOf Xh).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hρX]
    intro xh hxh
    have h1 : xh ∈ autOn (⊤ : Subgroup G) V := hXG hxh
    rw [← map_ambRho V ⊤] at h1
    obtain ⟨g, -, rfl⟩ := h1
    exact CGT6.map_mem_normalizer_map (ambRho V)
      (CGT6.le_normalizer_conjClosure (show g ∈ Xh.comap (ambRho V) from hxh))
  have hVC : V ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.1
  have hVX : V ≤ Subgroup.normalizer (CGT6.conjClosure Y (Xh.comap (ambRho V)) : Set G) :=
    hVC.trans hCX
  have hkerN : (ambRho V).ker ≤ Subgroup.normalizer (Y : Set G) := by
    rw [ker_ambRho V]
    exact fun c hc => (hCY hc).1
  have hXYimp : autOn Y V = Xh → CGT6.conjClosure Y (Xh.comap (ambRho V)) ≤ Y := by
    intro hEq
    refine CGT6.conjClosure_le_of_map_eq (ambRho V) hkerN (fun g hg => ?_)
    have h1 : ambRho V g ∈ Xh := hg
    rw [← hEq, ← hYhat] at h1
    exact h1
  have hperfX : ⁅Y, Y⁆ = Y → ⁅CGT6.conjClosure Y (Xh.comap (ambRho V)),
      CGT6.conjClosure Y (Xh.comap (ambRho V))⁆ = CGT6.conjClosure Y (Xh.comap (ambRho V)) :=
    CGT6.commutator_conjClosure_eq_self
  have hYXc : Y ≤ CGT6.conjClosure Y (Xh.comap (ambRho V)) := CGT6.le_conjClosure
  refine ⟨CGT6.conjClosure Y (Xh.comap (ambRho V)), CGT6.le_conjClosure, hXsub, hCX, hX2, ?_⟩
  generalize CGT6.conjClosure Y (Xh.comap (ambRho V)) = X at *
  rcases hout with ⟨hXhat, harr⟩ | ⟨hq, hYperf, n, hn, hnat, hYX2⟩
  ·
    left
    have hnot : ¬ IsPGroup 2 ↥(X.map (ambRho V)) := fun h => by
      have := h.to_le hρY
      rw [hYhat] at this
      exact not_isPGroup_autOn hY hU this
    have hXeq : X.map (ambRho V) = Xh :=
      @eq_of_inClassX_yuHol ↥V (commGroupOfElemAbelian hV) _ _ _ hρX hρXn hXhat hnot
    have hXhat' : autOn X V = Xh := (map_ambRho V X).symm.trans hXeq
    have hXcl : InClassX ↥(yuHolOf hV (autOn X V)) := by
      rw [hXhat']
      exact hXhat
    obtain ⟨hXc, hUX⟩ := hMinus G V X hV hVX hX2 hres hfit hXCX hXcl
    refine ⟨hXc, hUX.le.trans (Subgroup.commutator_le_left V X), ?_⟩
    by_cases hyu : yuHolOf hV (autOn Y V) = yuHolOf hV (autOn X V)
    · have hEq : autOn Y V = autOn X V := @yuHol_inj ↥V (commGroupOfElemAbelian hV) _ _ hyu
      exact Or.inl (le_antisymm hYXc (hXYimp (hEq.trans hXhat')))
    · refine hArrow G V Y X hV hYXc hY hXc hVY hU hVX hUX.symm hX2 hyu ?_
      rw [hXhat']
      exact harr
  · by_cases hEq : autOn Y V = Xh
    ·
      have hXeqY : X = Y := le_antisymm (hXYimp hEq) hYXc
      rw [hXeqY]
      left
      exact ⟨hY, by rw [← hU]; exact Subgroup.commutator_le_left V Y, Or.inl rfl⟩
    ·
      right
      obtain ⟨hSL, hcard⟩ := hYX2.resolve_left hEq
      have hΩ := @hOmega ↥V (commGroupOfElemAbelian hV) _ hV2 Xh (autOn Y V) n hn hnat hYX hEq
        hSL hcard
      have hXeq : X.map (ambRho V) = Xh := hΩ.1 _ (by rw [← hYhat]; exact hρY) hρX hρXn
      have hXhat' : autOn X V = Xh := (map_ambRho V X).symm.trans hXeq
      have hnat' : NatOmega hV n (autOn X V) := by
        rw [hXhat']
        exact hnat
      have : NeZero n := ⟨by omega⟩
      have key : (IsNatBy (omegaPlusAct n) X ⁅X, V⁆ ∨ IsNatBy (omegaMinusAct n) X ⁅X, V⁆) ∧
          (⁅X, V⁆ : Subgroup G) ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
          X ⊓ Subgroup.centralizer ((⁅X, V⁆ : Subgroup G) : Set G) ≤
            Subgroup.centralizer (V : Set G) := by
        rcases hnat' with h | h
        · obtain ⟨h1, h2, h3⟩ := isNatBy_of_isNatSectionBy hV
            (fun s hs => omegaPlusAct_faithful hs) (fun m hm => omegaPlusAct_fixed hm) h
          exact ⟨Or.inl h1, h2, h3⟩
        · obtain ⟨h1, h2, h3⟩ := isNatBy_of_isNatSectionBy hV
            (fun s hs => omegaMinusAct_faithful hs) (fun m hm => omegaMinusAct_fixed hm) h
          exact ⟨Or.inr h1, h2, h3⟩
      have hYN : Y ≤ Subgroup.normalizer (V : Set G) := by
        rw [Subgroup.normalizer_eq_top V]
        exact le_top
      have hcard' : Nat.card ↥⁅Y, V⁆ = 2 ^ (3 * n) := by
        rw [← BHS6.map_commOn hV hYN, Subgroup.card_map_of_injective V.subtype_injective]
        exact hcard
      refine ⟨hres, hperfX hYperf, hq, hYperf, n, hn, key.1, key.2.1, key.2.2, ?_, fun _ => hnat',
        by rw [hXhat']; exact hYX, by rw [hXhat']; exact hEq, hSL, hcard'⟩
      intro hsn
      apply hΩ.2
      have h1 : ((Y.map (ambRho V)).subgroupOf (X.map (ambRho V))).IsSubnormal := by
        let f : ↥X →* ↥(X.map (ambRho V)) :=
          ((ambRho V).comp X.subtype).codRestrict (X.map (ambRho V)) fun x => ⟨x, x.2, rfl⟩
        have hf : Function.Surjective f := by
          rintro ⟨_, ⟨x, hx, rfl⟩⟩
          exact ⟨⟨x, hx⟩, rfl⟩
        have hmap : (Y.subgroupOf X).map f = (Y.map (ambRho V)).subgroupOf (X.map (ambRho V)) := by
          ext z
          constructor
          · rintro ⟨x, hx, rfl⟩
            exact ⟨x, hx, rfl⟩
          · intro hz
            obtain ⟨y, hy, hyz⟩ := hz
            exact ⟨⟨y, hYXc hy⟩, hy, Subtype.ext hyz⟩
        rw [← hmap]
        exact Subgroup.IsSubnormal.map hf hsn
      rw [hXeq, hYhat] at h1
      exact h1

end Concl

theorem aschbacherEmbeddingAmbK'_of_embedding (hE : AschbacherEmbeddingK) (hPlus : EmbDictPlus)
    (hMinus : EmbDictMinus) (hArrow : EmbDictArrow) (hOmega : EmbOmega) :
    AschbacherEmbeddingAmbK' := by
  intro G _ _ hK hchar Y V hY hVn hVe hYV hP
  have := hVn
  obtain ⟨P, hP2, hPC, hYN, hs⟩ := hP
  have hV : IsElemAbelian 2 V :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).mp hVe
  obtain ⟨hVY, hU, hQU, hCY⟩ := emb_stage_one hchar hVe hY hYV hYN hs
  obtain ⟨-, hTG, hTne, hT2, hYc, hYs, -⟩ :=
    emb_hyp_data (kProper_of_isKGroup' hK) hV hY hP2 hPC hYN hs hU
  have hKp : CFSG.IsKGroup ↥(autOn (⊤ : Subgroup G) V) :=
    isKGroup_of_surjective hK (ambRhoHat V) (ambRhoHat_surjective V)
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV.2 v v.2)
  have hYU : InClassX ↥(yuHolOf hV (autOn Y V)) := hPlus G V Y hV hY hVY hU
  rcases hY.1.quotient_type with hq | hp
  ·
    have hperf : ⁅Y, Y⁆ = Y := commutator_self_eq_of_isShortGroup hY.1 hq
    have hperf' : ⁅autOn Y V, autOn Y V⁆ = autOn Y V := by
      rw [← map_ambRho V Y, ← Subgroup.map_commutator, hperf]
    obtain ⟨Xh, hYX, hXG, hXs, hout⟩ := @hE.1 ↥V (commGroupOfElemAbelian hV) _ hV2
      (autOn (⊤ : Subgroup G) V) hKp (autOn P V) (autOn Y V) hTG hTne hT2 hYc hYs hperf' hYU
    refine emb_concl_sharp hMinus hArrow hOmega hchar hV hY hVY hU hQU hCY Xh hYX hXG hXs ?_
    rcases hout with h | ⟨n, hn, hnat, hh⟩
    · exact Or.inl h
    · exact Or.inr ⟨hq, hperf, n, hn, hnat, hh.imp id (fun h => ⟨h.2.1, h.2.2⟩)⟩
  ·
    have h3 := card_autOn_eq_three hV hY hp hU
    have h4 := card_commOn_eq_four hV hY hp hU
    obtain ⟨Xh, hYX, hXG, hXs, hXhat, harr⟩ := @hE.2 ↥V (commGroupOfElemAbelian hV) _ hV2
      (autOn (⊤ : Subgroup G) V) hKp (autOn P V) (autOn Y V) hTG hTne hT2 hYc hYs h3 h4
    exact emb_concl_sharp hMinus hArrow hOmega hchar hV hY hVY hU hQU hCY Xh hYX hXG hXs
      (Or.inl ⟨hXhat, harr⟩)

theorem aschbacherEmbeddingAmbK'_holds (hE : AschbacherEmbeddingK) : AschbacherEmbeddingAmbK' :=
  aschbacherEmbeddingAmbK'_of_embedding hE embDictPlus_holds embDictMinus_holds
    embDictArrow_holds embOmega_holds

end CFSG.CGT.PushingUpLit.ThmOne
