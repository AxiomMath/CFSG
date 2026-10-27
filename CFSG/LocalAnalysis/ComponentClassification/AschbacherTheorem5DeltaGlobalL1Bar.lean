module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalAFrame
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalEndBar
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalFiveFrame

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.SignalizerFunctor.Helpers

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix SectionSix.BarTools DeltaLocal.Five

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem frame_bar_U (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a) :
    AschbacherTheorem3.Frame (bar D (aschbacherThm5Preimage D (Abar a)))
      (bar D (AschbacherTheorem3.omegaOne d.T)) :=
  ⟨bar_le_normalizer EndHyp.U_le_normalizer_A EndHyp.A_le_H, by
    rw [← bar_inf_of_core_le (core_le_preimage D _), EndHyp.U_inf_A hC, bar,
      Subgroup.bot_subgroupOf, Subgroup.map_bot],
    isPGroup_bar (d.sylowT.isPGroup.to_le EndHyp.U_le_T)⟩

theorem sylowFrame_bar_U (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    (hUZ : AschbacherTheorem3.omegaOne d.T ≤ rightConjugate (zStar D Abar) d.g)
    (hU1 : AschbacherTheorem3.omegaOne d.T ≠ ⊥) :
    AschbacherTheorem3.SylowFrame (bar D (aschbacherThm5Preimage D (Abar a)))
      (bar D (AschbacherTheorem3.omegaOne d.T))
      (bar D (d.S ⊔ AschbacherTheorem3.omegaOne d.T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  have hF := sylowFrame_U hC d hUZ hU1
  have hAH : A ≤ Subgroup.normalizer (D : Set G) := EndHyp.A_le_H
  have hUH : U ≤ Subgroup.normalizer (D : Set G) := EndHyp.U_le_H hC
  have hU2 : IsPGroup 2 U := d.sylowT.isPGroup.to_le EndHyp.U_le_T
  have hKH : A ⊔ U ≤ Subgroup.normalizer (D : Set G) := sup_le hAH hUH
  have hOK : aschbacherThm5Core D ≤ A ⊔ U := (core_le_preimage D _).trans le_sup_left
  have hsup : bar D A ⊔ bar D U = bar D (A ⊔ U) := (bar_sup hAH hUH).symm
  obtain ⟨-, hSN⟩ := bar_inf_normalizer hKH hOK hU2 hUH hF.sylow.le hF.sylow.isPGroup
    hF.sylow_normalizer
  refine { toFrame := frame_bar_U hC d, sylow := ?_, sylow_normalizer := ?_ }
  · rw [hsup]
    exact isSylowOf_bar hF.sylow hKH
  · rw [hsup]
    exact hSN

theorem hyp43_bar_U (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    (hUZ : AschbacherTheorem3.omegaOne d.T ≤ rightConjugate (zStar D Abar) d.g) :
    AschbacherTheorem3.Hyp43 (bar D (aschbacherThm5Preimage D (Abar a)))
      (bar D (AschbacherTheorem3.omegaOne d.T))
      (bar D ((rightConjugate (zStar D Abar) d.g ⊓ aschbacherThm5Preimage D (Abar a)) ⊔
        AschbacherTheorem3.omegaOne d.T))
      (bar D ((aschbacherThm5Preimage D (Abar a) ⊓
        rightConjugate (Subgroup.normalizer (D : Set G)) d.g) ⊔
          AschbacherTheorem3.omegaOne d.T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set E := AschbacherTheorem3.omegaOne d.T with hEdef
  set Hg := rightConjugate (Subgroup.normalizer (D : Set G)) d.g with hHgdef
  set P := rightConjugate (zStar D Abar) d.g ⊓ A with hPdef
  have hE2 : IsPGroup 2 E := d.sylowT.isPGroup.to_le EndHyp.U_le_T
  have hEH : E ≤ Subgroup.normalizer (D : Set G) := EndHyp.U_le_H hC
  have hEA : E ≤ Subgroup.normalizer (A : Set G) := EndHyp.U_le_normalizer_A
  have hodd : Odd (Nat.card P) := by
    rw [hPdef]
    exact odd_card_zStar_conj_inf hC (datum_g_not_mem d)
  have hAH : A ≤ Subgroup.normalizer (D : Set G) := EndHyp.A_le_H
  have hPH : P ≤ Subgroup.normalizer (D : Set G) := inf_le_right.trans hAH
  have hZg : rightConjugate (zStar D Abar) d.g ≤ Hg :=
    AschbacherTheorem3.rightConjugate_le_rightConjugate zStar_le_normalizer d.g
  have hHgN : Hg ≤ Subgroup.normalizer (rightConjugate (zStar D Abar) d.g : Set G) :=
    AschbacherTheorem3.rightConjugate_le_normalizer (normalizer_le_normalizer_zStar hC.hyp) d.g
  have hPE : P ⊓ E = ⊥ :=
    two_subgroup_of_odd_eq_bot _ P (hE2.to_le inf_le_right) hodd inf_le_left
  have hEP : E ≤ Subgroup.normalizer (P : Set G) := fun e he =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hUZ he), hEA he⟩
  have hQH : P ⊔ E ≤ (A ⊓ Hg) ⊔ E :=
    sup_le_sup_right (le_inf inf_le_right (inf_le_left.trans hZg)) E
  have hnorm : (A ⊓ Hg) ⊔ E ≤ Subgroup.normalizer ((P ⊔ E : Subgroup G) : Set G) := by
    refine sup_le (fun x hx => ?_) (le_sup_right.trans Subgroup.le_normalizer)
    have hxA : x ∈ A := hx.1
    have hxHg : x ∈ Hg := hx.2
    apply AschbacherToolkit.mem_normalizer_of_conj_le
    have hle : P ⊔ E ≤ (P ⊔ E).comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun p hp => ?_) (fun e he => ?_)
      · rw [Subgroup.mem_comap]
        show x * p * x⁻¹ ∈ P ⊔ E
        exact Subgroup.mem_sup_left ⟨(Subgroup.mem_normalizer_iff.mp (hHgN hxHg) p).mp hp.1,
          (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hxA) p).mp hp.2⟩
      · rw [Subgroup.mem_comap]
        show x * e * x⁻¹ ∈ P ⊔ E
        have h1 : x * e * x⁻¹ * e⁻¹ ∈ P := by
          refine ⟨Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hHgN hxHg) e).mp
            (hUZ he)) (Subgroup.inv_mem _ (hUZ he)), ?_⟩
          have h2 := (Subgroup.mem_normalizer_iff.mp (hEA he) x⁻¹).mp (Subgroup.inv_mem _ hxA)
          have h3 := Subgroup.mul_mem _ hxA h2
          rwa [show x * (e * x⁻¹ * e⁻¹) = x * e * x⁻¹ * e⁻¹ by group] at h3
        have := Subgroup.mul_mem_sup h1 he
        simpa using this
    exact fun y hy => hle hy
  exact
    { le := bar_mono D hQH
      le_normalizer := bar_le_normalizer hnorm (sup_le hPH hEH)
      le_sup := by
        rw [← bar_sup hAH hEH]
        exact bar_mono D (sup_le_sup_right inf_le_left E)
      sylow := isSylowOf_bar (isSylowOf_sup_of_odd hEP hodd hE2 hPE) (sup_le hPH hEH)
      inf_eq_bot := fun _ hx hxH => ti_bar hC hUZ hEH hE2 hx hxH }

theorem weakClosure_bar_U (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    {b : G} (hbS : b ∈ d.S)
    (hwcl : ∀ c ∈ aschbacherThm5Preimage D (Abar a),
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        d.S ⊔ AschbacherTheorem3.omegaOne d.T →
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        AschbacherTheorem3.omegaOne d.T ⊔ rightConjugate (AschbacherTheorem3.omegaOne d.T) b) :
    relativeWeakClosure (bar D (aschbacherThm5Preimage D (Abar a)))
        (bar D (AschbacherTheorem3.omegaOne d.T))
        (bar D (d.S ⊔ AschbacherTheorem3.omegaOne d.T)) =
      bar D (AschbacherTheorem3.omegaOne d.T) ⊔
        rightConjugate (bar D (AschbacherTheorem3.omegaOne d.T))
          (toBar D ⟨b, EndHyp.A_le_H (d.sylowS.le hbS)⟩) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  have hAH : A ≤ H := EndHyp.A_le_H
  have hUH : U ≤ H := EndHyp.U_le_H hC
  have hU2 : IsPGroup 2 U := d.sylowT.isPGroup.to_le EndHyp.U_le_T
  have hSUH : d.S ⊔ U ≤ H := sup_le (d.sylowS.le.trans hAH) hUH
  set b' : H := ⟨b, hAH (d.sylowS.le hbS)⟩ with hb'def
  have hUb : rightConjugate U b ≤ d.S ⊔ U := by
    rw [← AschbacherTheorem3.rightConjugate_eq_of_mem (Subgroup.mem_sup_left hbS : b ∈ d.S ⊔ U)]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate le_sup_right b
  have hUbH : rightConjugate U b ≤ H := hUb.trans hSUH
  apply le_antisymm
  · apply iSup_le
    rintro ⟨c, hc⟩
    apply iSup_le
    intro hle
    have hV : conjugateSubgroup c (bar D U) = rightConjugate (bar D U) c⁻¹ := by
      unfold rightConjugate
      rw [inv_inv]
    rw [hV] at hle ⊢
    obtain ⟨x, hxA, rfl⟩ := (mem_bar_iff D A c).mp hc
    have e1 : rightConjugate (bar D U) (toBar D x)⁻¹ = bar D (rightConjugate U (x⁻¹ : H)) := by
      rw [bar_rightConjugate, map_inv]
    rw [e1] at hle ⊢
    have hxH : rightConjugate U (x⁻¹ : H) ≤ H :=
      (AschbacherTheorem3.rightConjugate_le_rightConjugate hUH _).trans (le_of_eq
        ((rightConjugate_eq_self_iff H _).mpr (Subgroup.le_normalizer (x⁻¹ : H).2)))
    obtain ⟨o, ho, hRo⟩ := le_rightConjugate_of_le_sup_core hSUH
      (AschbacherTheorem3.isPGroup_rightConjugate hU2 _) (le_sup_core_of_bar_le hxH hle)
    set o' : H := ⟨o, core_le_normalizer D ho⟩ with ho'def
    have h2 : rightConjugate U ((x⁻¹ * o'⁻¹ : H) : G) ≤ d.S ⊔ U := by
      have h3 := AschbacherTheorem3.rightConjugate_le_rightConjugate hRo o⁻¹
      rwa [rightConjugate_mul, rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h3
    have hcA : ((x⁻¹ * o'⁻¹ : H) : G) ∈ A :=
      A.mul_mem (A.inv_mem hxA) (A.inv_mem (core_le_preimage D _ ho))
    have h4 := hwcl _ hcA h2
    have hto : toBar D o' = 1 := (toBar_eq_one_iff D o').mpr ho
    have e2 : bar D (rightConjugate U (x⁻¹ : H)) = bar D (rightConjugate U (x⁻¹ * o'⁻¹ : H)) := by
      rw [bar_rightConjugate, bar_rightConjugate, map_mul, map_inv (toBar D) o', hto, inv_one,
        mul_one]
    rw [e2]
    refine (bar_mono D h4).trans (le_of_eq ?_)
    rw [bar_sup hUH hUbH]
    congr 1
    exact bar_rightConjugate U b'
  · refine sup_le (subgroup_le_relative_weak_closure _ _ _ (bar_mono D le_sup_right)) ?_
    refine AschbacherTheorem3.rightConjugate_le_relativeWeakClosure
      (toBar_mem_bar D (d.sylowS.le hbS)) ?_
    rw [← bar_rightConjugate U b']
    exact bar_mono D hUb

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
