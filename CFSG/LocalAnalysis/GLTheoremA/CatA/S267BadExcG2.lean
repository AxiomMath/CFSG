module

import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Omega268
import CFSG.LocalAnalysis.RankFourTheoremC.PPointAutRank
import CFSG.GH74.Uniqueness.SU.SU7Gen3
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenA
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.KFacts.AutG2
public import CFSG.RankThree.PartTwo.KFacts.K73L27

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley
open CFSG.RankThree.PartTwo.KFacts (g2FieldHom g2_automorphism_normal_form)

theorem exists_outer_of_card_le_pow {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    {p n : ℕ} (hp : p.Prime) (hX : ∀ F : Subgroup X, IsElemAbelian p F → Nat.card F ≤ p ^ n)
    {E : Subgroup (MulAut X)} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ (n + 1)) :
    ∃ β ∈ E, β ∉ (MulAut.conj : X →* MulAut X).range := by
  by_contra h
  push Not at h
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    CFSG.LocalAnalysis.RankFourTheoremC.conj_injective_of_center_eq_bot hZ
  set F := E.comap (MulAut.conj : X →* MulAut X) with hF
  have hFE : F.map (MulAut.conj : X →* MulAut X) = E := Subgroup.map_comap_eq_self fun x hx => h x hx
  have hFc : Nat.card F = p ^ (n + 1) := by
    rw [← hEc, ← hFE, Subgroup.card_map_of_injective hinj]
  have hFel : IsElemAbelian p F := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · have := congrArg Subtype.val (hE.1.is_comm.comm (⟨MulAut.conj (a : X), a.2⟩ : E)
        ⟨MulAut.conj (b : X), b.2⟩)
      simpa only [Subgroup.coe_mul, map_mul] using this
    · rw [map_pow, hE.2 _ hx, map_one]
  have h1 := hX F hFel
  rw [hFc] at h1
  have := Nat.pow_lt_pow_right hp.one_lt (by omega : n < n + 1)
  omega

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem exists_outer_mem_of_card {p n : ℕ} (hp : p.Prime) (hS : S.Normal)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ (n + 2))
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {X : Type} [Group X] [Finite X]
    (φ : X →* Ω) (hφ : Function.Injective φ) (hφS : φ.range = S) (hZX : Subgroup.center X = ⊥)
    (hX : ∀ F : Subgroup X, IsElemAbelian p F → Nat.card F ≤ p ^ n) :
    ∃ b ∈ B, ∃ β : MulAut X, β ∉ (MulAut.conj : X →* MulAut X).range ∧
      ∀ x, φ (β x) = b * φ x * b⁻¹ := by
  haveI : S.Normal := hS
  set ι : X ≃* ↥S := (MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hφS) with hι
  have hιφ : ∀ x, (ι x : Ω) = φ x := fun x => rfl
  set Γ : Ω →* MulAut X := (MulAut.congr ι.symm).toMonoidHom.comp MulAut.conjNormal with hΓ
  have hΓφ : ∀ b x, φ (Γ b x) = b * φ x * b⁻¹ := by
    intro b x
    have h1 : Γ b x = ι.symm (MulAut.conjNormal b (ι x)) := rfl
    rw [h1, ← hιφ, MulEquiv.apply_symm_apply, MulAut.conjNormal_apply, hιφ]
  have hφmem : ∀ s ∈ S, ∃ x, φ x = s := fun s hs => by
    rw [← hφS] at hs
    exact hs
  have hker : ∀ b, Γ b = 1 ↔ ∀ s ∈ S, b * s = s * b := by
    intro b
    constructor
    · intro h s hs
      obtain ⟨x, rfl⟩ := hφmem s hs
      have h1 := hΓφ b x
      rw [h, MulAut.one_apply] at h1
      calc b * φ x = b * φ x * b⁻¹ * b := by group
        _ = φ x * b := by rw [← h1]
    · intro h
      ext x
      apply hφ
      rw [hΓφ, MulAut.one_apply, h _ (hφS ▸ ⟨x, rfl⟩), mul_inv_cancel_right]
  have hBker : B ⊓ Γ.ker = B ⊓ centModSubgroup p S := by
    ext b
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker]
    constructor
    · rintro ⟨hb, h1⟩
      refine ⟨hb, CFSG.LocalAnalysis.GLTheoremA.S267.mem_centModSubgroup_of_commute ?_
        fun l hl => ((hker b).1 h1 l hl).symm⟩
      rw [Subgroup.mem_normalizer_iff]
      intro s
      constructor
      · intro hs
        exact hS.conj_mem s hs b
      · intro hs
        have := hS.conj_mem _ hs b⁻¹
        simpa [mul_assoc] using this
    · rintro ⟨hb, hc⟩
      exact ⟨hb, (hker b).2 fun s hs =>
        CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.comm_of_mem_centMod hS hcore hc hs⟩
  have hcard : Nat.card (B.map Γ) = p ^ (n + 1) := by
    have h := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker Γ B
    rw [hBker, hBC, hBc] at h
    have h' : Nat.card (B.map Γ) * p = p ^ (n + 1) * p := by rw [h, pow_succ]
    exact Nat.eq_of_mul_eq_mul_right hp.pos h'
  obtain ⟨β, ⟨b, hb, rfl⟩, hβ⟩ := exists_outer_of_card_le_pow hZX hp hX (hB.map Γ) hcard
  exact ⟨b, hb, Γ b, hβ, hΓφ b⟩

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
