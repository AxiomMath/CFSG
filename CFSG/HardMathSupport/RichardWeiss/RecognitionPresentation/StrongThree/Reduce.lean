module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Core
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Rank
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Rows
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblySections
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open CFSG.ComponentClassification Subgroup
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem perfect_le_of_outer {X : Type*} [Group X] {K : Subgroup X} [K.Normal]
    (hC : Subgroup.centralizer (K : Set X) = ⊥)
    (hout : Group.IsSolvable (OuterAutomorphisms.Outer ↥K)) {Y : Subgroup X}
    (hY : ⁅Y, Y⁆ = Y) : Y ≤ K := by
  let τ : X →* OuterAutomorphisms.Outer ↥K :=
    (QuotientGroup.mk' (OuterAutomorphisms.inner ↥K)).comp MulAut.conjNormal
  have hker : ∀ x, τ x = 1 → x ∈ K := by
    intro x hx
    have hx' : (MulAut.conjNormal x : MulAut ↥K) ∈ OuterAutomorphisms.inner ↥K :=
      (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨k, hk⟩ := hx'
    have hcomm : ∀ y : X, y ∈ K → x * y * x⁻¹ = k * y * (k : X)⁻¹ := by
      intro y hy
      have := congrArg (fun φ : MulAut ↥K => ((φ ⟨y, hy⟩ : ↥K) : X)) hk
      simpa [MulAut.conjNormal_apply] using this.symm
    have hz : (k : X)⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := hcomm y hy
      calc y * ((k : X)⁻¹ * x) = (k : X)⁻¹ * (k * y * (k : X)⁻¹) * x := by group
        _ = (k : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
        _ = (k : X)⁻¹ * x * y := by group
    rw [hC, Subgroup.mem_bot] at hz
    have : x = k := by
      have := congrArg (fun z => (k : X) * z) hz
      simpa using this
    exact this ▸ k.2
  have : Group.IsSolvable (OuterAutomorphisms.Outer ↥K) := hout
  have hperf : ⁅Y.map τ, Y.map τ⁆ = Y.map τ := by rw [← Subgroup.map_commutator, hY]
  have hbot : Y.map τ = ⊥ := by
    by_contra hne
    exact (ne_of_lt (Group.IsSolvable.commutator_lt_of_ne_bot hne)) hperf
  intro y hy
  refine hker y ?_
  have hmem : τ y ∈ Y.map τ := ⟨y, hy, rfl⟩
  rw [hbot] at hmem
  simpa using hmem

theorem eq_bot_of_perfect_of_le {X : Type*} [Group X] {G : Subgroup X} [Group.IsSolvable ↥G]
    {Y : Subgroup X} (hYG : Y ≤ G) (hY : ⁅Y, Y⁆ = Y) : Y = ⊥ := by
  have hperf : ⁅Y.subgroupOf G, Y.subgroupOf G⁆ = Y.subgroupOf G := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hYG, hY]
  by_contra hne
  have hne' : Y.subgroupOf G ≠ ⊥ := fun h => hne (by
    rw [← Subgroup.map_subgroupOf_eq_of_le hYG, h, Subgroup.map_bot])
  exact (ne_of_lt (Group.IsSolvable.commutator_lt_of_ne_bot hne')) hperf

theorem perfect_eq_bot_of_coreFree {X : Type} [Group X] [Finite X]
    (hSch : SchreierFor CFSG.Assembly.InCatalog) (hG : Gls3StronglyThreeEmbedded)
    (hX : CFSG.Open.IsKGroup X) {M E : Subgroup X} (D : CoreFree M E) {Y : Subgroup X} (hYM : Y ≤ M)
    (hY : ⁅Y, Y⁆ = Y) : Y = ⊥ := by
  obtain ⟨K, hKn, hKs, hKnc, hKc⟩ := D.exists_simple_normal
  have hK0 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).mp inferInstance
  have hE3 : IsPGroup 3 ↥E := fun x => ⟨1, Subtype.ext (by simpa using D.elem.2 x x.2)⟩
  obtain ⟨P, hEP, hPM⟩ := exists_sylow_le_of_le D.strong D.le hE3
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE3
  have hk2 : 2 ≤ k := by
    have h9 : 3 ^ 2 ≤ 3 ^ k := by rw [← hk]; simpa using D.card
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h9
  have hrank : 2 ≤ CFSG.Open.pRank 3 (P : Subgroup X) :=
    hk2.trans (le_pRank Nat.prime_three hEP D.elem hk)
  have hγ : ∀ A Q : Subgroup X, Q ≤ P → gammaCore 3 1 A Q ≤ M ⊓ A := by
    intro A Q hQP
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxA, R, hRQ, hR, hxR⟩
    exact ⟨normalizer_le_of_stronglyEmbedded D.strong ((hRQ.trans hQP).trans hPM)
      (three_dvd_card_of_one_le_pRank hR) hxR, hxA⟩
  have hΓX : gammaCore 3 1 ⊤ (P : Subgroup X) < ⊤ :=
    lt_of_le_of_lt ((hγ ⊤ P le_rfl).trans inf_le_left) (lt_top_iff_ne_top.mpr D.strong.1)
  have hconc := hG X hX K hKn hKs hKnc hKc P hrank hΓX
  have hΓ := hγ K ((P : Subgroup X) ⊓ K) inf_le_left
  have heq : M ⊓ K = gammaCore 3 1 K ((P : Subgroup X) ⊓ K) := by
    by_contra hne
    have hlt : gammaCore 3 1 K ((P : Subgroup X) ⊓ K) < M ⊓ K := lt_of_le_of_ne hΓ (Ne.symm hne)
    have hMK : M ⊓ K = K := hconc.2.1 (M ⊓ K) hlt inf_le_right
    exact D.not_le_of_normal hK0 (hMK ▸ inf_le_left)
  have hSec : LBalance.SchreierSections X :=
    LBalance.SchreierSections.of_isKGroup (fun S _ _ _ hnc hcat => hSch S hnc hcat) hX
  have hout := hSec.outer_solvable K hKnc (MonoidHom.id ↥K) Function.surjective_id
  have hYK : Y ≤ K := perfect_le_of_outer hKc hout hY
  have hsolv := gamma_isSolvable (P.isPGroup'.to_inf_left) hconc
  have hYΓ : Y ≤ gammaCore 3 1 K ((P : Subgroup X) ⊓ K) := heq ▸ le_inf hYM hYK
  exact eq_bot_of_perfect_of_le hYΓ hY

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
