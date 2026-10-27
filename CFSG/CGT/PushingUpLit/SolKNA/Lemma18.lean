module

public import CFSG.CGT.PushingUpLit.SolKNA.Prop18Struct
public import CFSG.CGT.PushingUpLit.SolKNA.Lemma17
public import CFSG.CGT.PushingUpLit.SolKNA.NCPairModels

public section

open scoped IsMulCommutative

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n
open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne Matrix
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

namespace Prop18Setup

variable {R Rb L Lb N : Subgroup X} (S : Prop18Setup R Rb L Lb N)
include S

theorem exists_models
    (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) [N.Normal] :
    (∀ K : Subgroup (X ⧸ N), K.Normal → IsPGroup 2 K → K = ⊥) ∧
      ((∃ f : ℕ, 2 ≤ f ∧ L.relIndex R = 2 ^ f ∧
          Nonempty (X ⧸ N ≃* PSL(2, GaloisField 2 f))) ∨
        (∃ a : ℕ, 1 ≤ a ∧ L.relIndex R = 2 ^ (2 * a + 1) ∧ Nonempty (X ⧸ N ≃* Sz a)) ∨
        (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ L.relIndex R = 2 ∧
          Nonempty (X ⧸ N ≃* DihedralGroup m))) := by
  obtain ⟨hO2, hmod⟩ := S.ncPair.models hCen hU
  rw [S.relIndex_eq_card_image]
  exact ⟨hO2, hmod⟩

theorem lemma17Psl [N.Normal] {F : Type} [Field F] [Finite F] [CharP F 2]
    {ψ : X →* SL(2, F)} (hψs : Function.Surjective ψ) (hker : ψ.ker = N)
    (himg : R.map ψ = upperUnipotent F) {s : Finset (Subgroup X)} (hs : s.SupIndep id)
    (hsN : s.sup id = N)
    (hW : ∀ W ∈ s, W.Normal ∧ ∃ θ : (Fin 2 → F) → X, (∀ v v', θ (v + v') = θ v * θ v') ∧
      Function.Injective θ ∧ Set.range θ = W ∧ ∀ (x : X) (v : Fin 2 → F),
        θ ((ψ x : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = x * θ v * x⁻¹) :
    Lemma17Psl ψ N R where
  normal := inferInstance
  surj := hψs
  ker := hker
  img := himg
  sq_N := S.sq_N
  cent := fun n => by
    refine ⟨fun hn => ⟨(Subgroup.mem_inf.mp hn).2, fun r hr => ?_⟩, fun ⟨hnN, hnc⟩ => ?_⟩
    · exact (S.L_cent n (S.inf_N ▸ hn) r hr).symm
    · obtain ⟨t, ht, htN⟩ := S.exists_mem_R_notMem_N
      exact Subgroup.mem_inf.mpr ⟨S.cent_R ht htN hnN (hnc t ht), hnN⟩
  norm := fun x hx => by
    have hL : R ⊓ N = L := S.inf_N
    rw [hL] at hx
    have hxL : conjSubgroup x L = L := conjSubgroup_eq_self_iff.mpr hx
    have hne : R ⊓ conjSubgroup x R ≠ ⊥ := by
      intro hbot
      apply S.ne_bot
      rw [eq_bot_iff, ← hbot]
      refine le_inf S.L_le ?_
      calc L = conjSubgroup x L := hxL.symm
        _ ≤ conjSubgroup x R := Subgroup.map_mono S.L_le
    exact conjSubgroup_eq_self_iff.mp (conjSubgroup_eq_of_isTI S.ti hne)
  dec := ⟨s, hs, hsN, hW⟩

theorem abelian_of_index_two (hAL : L.relIndex R = 2) : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  intro a ha b hb
  by_cases haL : a ∈ L
  · exact S.L_cent a haL b hb
  by_cases hbL : b ∈ L
  · exact (S.L_cent b hbL a ha).symm
  have hl := inv_mul_mem_L_of_index_two hAL ha haL hb hbL
  have hc := S.L_cent _ hl a ha
  calc a * b = a * (a * (a⁻¹ * b)) := by group
    _ = a * ((a⁻¹ * b) * a) := by rw [← hc]
    _ = b * a := by group

theorem abelian_of_models
    (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) [N.Normal]
    (hSz : (∃ a : ℕ, 1 ≤ a ∧ L.relIndex R = 2 ^ (2 * a + 1) ∧ Nonempty (X ⧸ N ≃* Sz a)) →
      ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) :
    ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  obtain ⟨-, hmod⟩ := S.exists_models hCen hU
  rcases hmod with ⟨f, hf, hrel, ⟨e⟩⟩ | hsz | ⟨m, hm, h3, hrel, ⟨e⟩⟩
  · obtain ⟨F, hF, hFin, hchar, ψ, hcard, hψs, hψk, hψR, s, hs, hsN, hW⟩ := S.struct_psl hf e
    exact (S.lemma17Psl hψs hψk hψR hs hsN fun W hW' =>
      ⟨(hW W hW').2.1, (hW W hW').2.2.2.2⟩).abelian
  · exact hSz hsz
  · exact S.abelian_of_index_two hrel

end Prop18Setup

end CFSG.CGT.PushingUpLit.SolKNA
