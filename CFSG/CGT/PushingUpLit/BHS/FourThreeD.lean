module

public import CFSG.CGT.PushingUpLit.BHS.FourTwoB
public import CFSG.CGT.PushingUpLit.BHS.Prelim

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

namespace Hyp41

variable {V : Type} [CommGroup V] {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}

theorem mem_setNormalizer_dInter_of_conjSub_eq (h : Hyp41 P D) {U : Subgroup (MulAut V)}
    {g : MulAut V} (hgP : g ∈ P) (hg : conjSub g U = U) :
    g ∈ setNormalizer P (dInter D U) := by
  have h1 : ∀ A ∈ dInter D U, conjSub g A ∈ dInter D U := fun A hA =>
    ⟨h.conj_mem A hA.1 g hgP, by
      have := conjSub_mono g hA.2
      rwa [hg] at this⟩
  have hg' : conjSub g⁻¹ U = U := by
    have := congrArg (conjSub g⁻¹) hg
    rw [FourTwoTools.conjSub_inv_conjSub] at this
    exact this.symm
  refine ⟨hgP, fun A => ⟨h1 A, fun hA => ?_⟩⟩
  have h2 : conjSub g⁻¹ (conjSub g A) ∈ dInter D U :=
    ⟨h.conj_mem _ hA.1 g⁻¹ (P.inv_mem hgP), by
      have := conjSub_mono g⁻¹ hA.2
      rwa [hg'] at this⟩
  rwa [FourTwoTools.conjSub_inv_conjSub] at h2

end Hyp41

namespace Hyp42

variable {V : Type} [CommGroup V] [Finite V] {P : Subgroup (MulAut V)}
  {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)}

theorem le_setNormalizer (h : Hyp42 P D T M) {U : Set (Subgroup (MulAut V))}
    (hU : U ⊆ dInter D T) {A : Subgroup (MulAut V)} (hA : A ∈ dInter D T) :
    A ≤ setNormalizer P U := fun a ha =>
  FourTwoTools.mem_setNormalizer_of_comm (h.le A hA.1 ha) fun B hB b hb =>
    h.toHyp41.four_seven_pairs h.syl A hA B (hU hB) a ha b hb

theorem exists_mem_dInter_not_le (h : Hyp42 P D T M) {U : Set (Subgroup (MulAut V))}
    (hU : U ⊆ dInter D T) (hN : ¬ setNormalizer P U ≤ M) :
    ∃ B ∈ D, B ≤ setNormalizer P U ∧ ¬ B ≤ M := by
  by_contra hno
  push Not at hno
  set N : Subgroup (MulAut V) := setNormalizer P U with hNdef
  set E : Subgroup (MulAut V) := ⨆ A ∈ dInter D T, A with hE
  have hNP : N ≤ P := fun g hg => hg.1
  have hAN : ∀ A ∈ dInter D T, A ≤ N := fun A hA => h.le_setNormalizer hU hA
  have hAE : ∀ A ∈ dInter D T, A ≤ E := fun A hA =>
    le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V)) (_ : B ∈ dInter D T) => B) A hA le_rfl
  have hEN : E ≤ N := iSup₂_le hAN
  have hE2 : IsPGroup 2 E := h.syl.2.1.to_le (iSup₂_le fun A hA => hA.2)
  set Q : Subgroup (MulAut V) := Glauberman.coreIn N M ⊓ N with hQ
  have hQM : Q ≤ M := inf_le_left.trans Glauberman.coreIn_le
  have hQN : N ≤ Subgroup.normalizer (Q : Set (MulAut V)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.1 (Glauberman.le_normalizer_coreIn N M hg) y
    have h2 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hg) y
    simp only [hQ, Subgroup.mem_inf]
    rw [h1, h2]
  have hEQ : E ≤ Q := by
    refine le_inf (iSup₂_le fun A hA a ha => Glauberman.mem_coreIn.2 fun n hn => ?_) hEN
    have hAD : conjSub n⁻¹ A ∈ D := h.conj_mem A hA.1 n⁻¹ (N.inv_mem hn |> fun hh => hNP hh)
    have hAN' : conjSub n⁻¹ A ≤ N := by
      have := conjSub_mono n⁻¹ (hAN A hA)
      rwa [conjSub_self_of_mem (N.inv_mem hn)] at this
    have := hno _ hAD hAN'
    exact this (mem_conjSub_of_mem (g := n⁻¹) ha |> fun hh => by simpa using hh)
  obtain ⟨T_N, hTN, hET⟩ := Glauberman.exists_isSylowOf_ge hE2 hEN
  have hS : IsSylowOf 2 (T_N ⊓ Q) Q := by
    rw [inf_comm]
    exact FourTwoTools.isSylowOf_inf_of_le_normalizer hTN inf_le_right hQN
  have hES : ∀ A ∈ dInter D T, A ≤ T_N ⊓ Q := fun A hA =>
    le_inf ((hAE A hA).trans hET) ((hAE A hA).trans hEQ)
  have hdS : dInter D (T_N ⊓ Q) = dInter D T :=
    h.dInter_eq_of_le (inf_le_right.trans (hQM.trans h.M_le)) hS.2.1 hES
  refine hN fun g hg => ?_
  obtain ⟨x, hx, hxN, y, hy, hgxy⟩ := Glauberman.exists_mem_normalizer_mul hQN hTN.1 hTN.2.1
    hTN.2.2 hg
  have hxP : x ∈ P := hNP hxN
  have hx' : x ∈ setNormalizer P (dInter D T) := by
    have := h.toHyp41.mem_setNormalizer_dInter_of_conjSub_eq hxP
      (conjSub_eq_of_mem_normalizer hx)
    rwa [hdS] at this
  rw [hgxy]
  exact M.mul_mem (h.normSet_le hx') (hQM hy)

end Hyp42

end CFSG.CGT.PushingUpLit.BHS
