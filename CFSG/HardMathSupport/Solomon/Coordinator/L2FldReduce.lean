module

public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldBasic
import CFSG.Quasithin.Background.GoldschmidtListedSolv
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.L2Order
public import CFSG.HardMathSupport.Solomon.Coordinator.L3G515CovBasic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open (GLAPComponent GLAPPrimeCore GLAPLayer StatedProj StatedSL)
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.LocalAnalysis.GLTheoremB

theorem l2fld_not_cube_nine (n : ℕ) : n ^ 3 ≠ 9 := by
  intro h
  have hn : n < 3 := by
    by_contra hc
    push Not at hc
    have := Nat.pow_le_pow_left hc 3
    omega
  interval_cases n <;> omega

theorem l2fld_core (hU : L2OrderUnique) (h1 : L2Aut3Classification) (h2 : L2FieldFixed)
    (h0 : L2CentreThree) {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q)
    (hO : GLAPPrimeCore 3 Q = ⊥) {s r0 : ℕ} (hs : IsTypeL2 s Q) {a : MulAut Q} (ha3 : a ^ 3 = 1)
    {S : Subgroup Q} (hS : GLAPComponent 3 (fixSub a) S) (hr : IsTypeL2 r0 (barOf 3 S)) :
    (a = 1 ∧ (s = r0 ∨ ((s = 4 ∨ s = 5) ∧ (r0 = 4 ∨ r0 = 5)))) ∨
      (a ≠ 1 ∧ IsFieldAutPSLn 2 a ∧ (s = r0 ^ 3 ∨ ((r0 = 4 ∨ r0 = 5) ∧ (s = 64 ∨ s = 125)))) := by
  have hZp : IsPGroup 3 (Subgroup.center Q) := isPGroup_center_of_core_eq_bot hO
  have hSsolv : Group.IsSolvable ↥S → False := fun hsv => by
    have hb : Group.IsSolvable (barOf 3 S) := inferInstanceAs (Group.IsSolvable (↥S ⧸ _))
    exact false_of_quasisimple_of_solvable (isQuasisimple_quotient_of_glaPComponent hS) hb
  by_cases hg1 : a = 1
  · left
    refine ⟨hg1, ?_⟩
    subst hg1
    rw [fixSub_one] at hS
    have hOt := glaPPrimeCore_top_eq_bot hO
    have hq : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup Q) :=
      isQuasisimple_open_of_mulEquiv Subgroup.topEquiv hQ
    obtain ⟨-, comp, -⟩ := layer_of_normal_quasisimple (F := (⊤ : Subgroup Q))
      (S := (⊤ : Subgroup Q)) le_rfl (commutator_le_self _) (fun x _ => ⟨0, by simp⟩) hq hOt
    have hST : S = ⊤ := (comp S).1 hS
    subst hST
    let e : barOf 3 (⊤ : Subgroup Q) ≃* Q :=
      (barEquivOfCore hOt).symm.trans Subgroup.topEquiv
    have hr' := l2fld_isTypeL2_of_mulEquiv e hr
    rcases hU Q s r0 hs hr' with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨Or.inl rfl, Or.inr rfl⟩
    · exact Or.inr ⟨Or.inr rfl, Or.inl rfl⟩
  · right
    refine ⟨hg1, ?_⟩
    obtain ⟨F, hFf, hFfin, hcF, ⟨e⟩⟩ := hs
    set α := centerDescend Q a with hα
    set β : MulAut (StatedProj (StatedSL 2 F)) := MulAut.congr e α with hβdef
    have hβ3 : β ^ 3 = 1 := by rw [hβdef, ← map_pow, hα, ← map_pow, ha3, map_one, map_one]
    have hβ1 : β ≠ 1 := by
      intro h
      apply hg1
      apply eq_one_of_centerDescend_eq_one hQ
      apply (MulAut.congr e).injective
      rw [← hα, ← hβdef, h, map_one]
    have hkey : ∀ z : Q ⧸ Subgroup.center Q, β (e z) = e (α z) := by
      intro z
      simp [hβdef, MulAut.congr_apply]
    rcases h1 F β hβ3 with h | hsol | ⟨σ, φ, γ, hφ, hβ⟩
    · exact absurd h hβ1
    · exfalso
      refine hSsolv ?_
      let f : ↥S →* ↥(fixSub β) :=
        { toFun := fun x => ⟨e (QuotientGroup.mk (x : Q)), by
            rw [mem_fixSub, hkey, hα, centerDescend_mk, mem_fixSub.1 (hS.1 x.2)]⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun x y => Subtype.ext (by simp) }
      refine CFSG.Quasithin.isSolvable_of_ker_le_center f ?_
      intro y hy
      have h1' : e (QuotientGroup.mk (y : Q)) = 1 := congrArg Subtype.val hy
      have h2' : (QuotientGroup.mk (y : Q) : Q ⧸ Subgroup.center Q) = 1 := e.map_eq_one_iff.1 h1'
      have h3' : (y : Q) ∈ Subgroup.center Q := (QuotientGroup.eq_one_iff _).1 h2'
      rw [Subgroup.mem_center_iff] at h3' ⊢
      intro w
      exact Subtype.ext (h3' (w : Q))
    · have hF : IsFieldAutPSLn 2 a := by
        refine ⟨F, hFf, hFfin, e, σ, φ, γ, hφ, fun y => ?_⟩
        rw [← hβ, hkey, hα, centerDescend_mk]
      refine ⟨hF, ?_⟩
      obtain ⟨F₀, hF₀f, hF₀fin, hcard, ⟨ψ0⟩⟩ := h2 F β hβ3 hβ1 σ φ γ hφ hβ
      have hZ : Subgroup.center Q = ⊥ := by
        by_contra hZ
        have h9 := h0 Q hQ hZp hZ F ⟨e⟩
        exact l2fld_not_cube_nine (Nat.card F₀) (by omega)
      let E : Q ≃* StatedProj (StatedSL 2 F) := (barEquivBot hZ).symm.trans e
      have hcongr : MulAut.congr E a = β := by
        apply MulEquiv.ext
        intro y
        obtain ⟨x, rfl⟩ := E.surjective y
        have h3 : (barEquivBot hZ).symm x = (x : Q ⧸ Subgroup.center Q) := by
          rw [MulEquiv.symm_apply_eq]; rfl
        have h4 : (barEquivBot hZ).symm (a x) = (a x : Q ⧸ Subgroup.center Q) := by
          rw [MulEquiv.symm_apply_eq]; rfl
        change E (a (E.symm (E x))) = β (E x)
        rw [MulEquiv.symm_apply_apply]
        show e ((barEquivBot hZ).symm (a x)) = β (e ((barEquivBot hZ).symm x))
        rw [h3, h4, hkey, hα, centerDescend_mk]
      have hfix : fixSub β = (fixSub a).map E.toMonoidHom := by
        rw [← hcongr]; exact fixSub_congr E a
      let ψ : ↥(fixSub a) ≃* ↥(fixSub β) :=
        ((fixSub a).equivMapOfInjective E.toMonoidHom E.injective).trans
          (MulEquiv.subgroupCongr hfix.symm)
      let Ψ : ↥(fixSub a) ≃* StatedProj (StatedSL 2 F₀) := ψ.trans ψ0
      by_cases h4 : 4 ≤ Nat.card F₀
      · obtain ⟨hQ₀, hZ₀⟩ := l2fld_isQuasisimple_psl2 h4
        have hXq : CFSG.Open.IsQuasisimple ↥(fixSub a) := isQuasisimple_open_of_mulEquiv Ψ hQ₀
        have hSX : S = fixSub a :=
          eq_of_isSubnormal_of_quasisimple hXq hS.2.1 (glaPComponent_perfect hS)
            (glaPComponent_ne_bot hS)
        subst hSX
        have hZX : Subgroup.center ↥(fixSub a) = ⊥ := center_eq_bot_of_mulEquiv' Ψ hZ₀
        have hOX : GLAPPrimeCore 3 ↥(fixSub a) = ⊥ :=
          glaPPrimeCore_eq_bot_of_quasisimple hXq
            (fun z hz => by rw [hZX, Subgroup.mem_bot] at hz; rw [hz, one_pow])
            (by rw [Nat.card_congr Ψ.toEquiv]; exact l2fld_three_dvd_card_psl2)
        let Eb : barOf 3 (fixSub a) ≃* StatedProj (StatedSL 2 F₀) := (barEquivOfCore hOX).symm.trans Ψ
        have hZb : Subgroup.center (barOf 3 (fixSub a)) = ⊥ := center_eq_bot_of_mulEquiv' Eb hZ₀
        have hty0 : IsTypeL2 (Nat.card F₀) (barOf 3 (fixSub a)) :=
          ⟨F₀, hF₀f, hF₀fin, rfl, ⟨(barEquivBot hZb).trans Eb⟩⟩
        rcases hU _ r0 (Nat.card F₀) hr hty0 with h | ⟨rfl, h5⟩ | ⟨rfl, h4'⟩
        · left; rw [← hcF, hcard, h]
        · right; refine ⟨Or.inl rfl, Or.inr ?_⟩
          rw [← hcF, hcard, h5]; norm_num
        · right; refine ⟨Or.inr rfl, Or.inl ?_⟩
          rw [← hcF, hcard, h4']; norm_num
      · exfalso
        push Not at h4
        have hsolP := l2fld_isSolvable_psl2_of_card_le_three (F := F₀) (by omega)
        have hX : Group.IsSolvable ↥(fixSub a) :=
          Group.isSolvable_of_isSolvable_injective (f := Ψ.toMonoidHom) Ψ.injective
        exact hSsolv (Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion hS.1) (Subgroup.inclusion_injective hS.1))

theorem inputL2fld_of_facts (hU : L2OrderUnique) (h1 : L2Aut3Classification)
    (h2 : L2FieldFixed) (h0 : L2CentreThree) : InputL2fld := by
  intro G _ _ K g s r0 hQ hs hgN hg3 J hJ hr
  have hO : GLAPPrimeCore 3 (barOf 3 K) = ⊥ := glaPPrimeCore_quotient_eq_bot Nat.prime_three
  obtain ⟨J₁, hJ₁, hJ₁J⟩ := exists_comp_subgroupOf (inf_le_left : K ⊓ Cs g ≤ K) hJ
  have hcomp := comp_map_fixSub hgN hg3 hJ₁
  subst hJ₁J
  have hr' := l2fld_isTypeL2_of_mulEquiv (liftEquiv J₁) hr
  rcases l2fld_core hU h1 h2 h0 hQ hO hs (barAut_pow_three hgN hg3) hcomp hr' with
    ⟨h, hc⟩ | ⟨h, hf, hc⟩
  · exact Or.inl ⟨⟨hgN, h⟩, hc⟩
  · exact Or.inr ⟨fun ⟨_, hh⟩ => h hh, ⟨hgN, hf⟩, hc⟩

end CFSG.HardMathSupport.Solomon.Coordinator
