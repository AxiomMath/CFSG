module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ModelA
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Omega268
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GH74.Uniqueness.SU.SU7Gen3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

theorem exists_outer_of_card_le_nine {X : Type} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) (hX : ∀ F : Subgroup X, IsElemAbelian 3 F → Nat.card F ≤ 3 ^ 2)
    {E : Subgroup (MulAut X)} (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3) :
    ∃ β ∈ E, β ∉ (MulAut.conj : X →* MulAut X).range := by
  by_contra h
  push Not at h
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center X := Subgroup.mem_center_iff.2 fun x => by
      have h1 : g * x * g⁻¹ = x := by
        have := congrArg (fun f : MulAut X => f x) hg
        simpa only [MulAut.conj_apply, MulAut.one_apply] using this
      calc x * g = g * x * g⁻¹ * g := by rw [h1]
        _ = g * x := by group
    rw [hZ] at hgc
    exact hgc
  set F := E.comap (MulAut.conj : X →* MulAut X) with hF
  have hFE : F.map (MulAut.conj : X →* MulAut X) = E := Subgroup.map_comap_eq_self fun x hx => h x hx
  have hFc : Nat.card F = 3 ^ 3 := by
    rw [← hEc, ← hFE, Subgroup.card_map_of_injective hinj]
  have hFel : IsElemAbelian 3 F := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · have := congrArg Subtype.val (hE.1.is_comm.comm (⟨MulAut.conj (a : X), a.2⟩ : E)
        ⟨MulAut.conj (b : X), b.2⟩)
      simpa only [Subgroup.coe_mul, map_mul] using this
    · rw [map_pow, hE.2 _ hx, map_one]
  have := hX F hFel
  rw [hFc] at this
  norm_num at this

variable {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem P3Hyp.exists_outer_mem (H : P3Hyp q S B) {X : Type} [Group X] [Finite X] (φ : X →* Ω)
    (hφ : Function.Injective φ) (hφS : φ.range = S) (hZX : Subgroup.center X = ⊥)
    (hX : ∀ F : Subgroup X, IsElemAbelian 3 F → Nat.card F ≤ 3 ^ 2) :
    ∃ b ∈ B, ∃ β : MulAut X, β ∉ (MulAut.conj : X →* MulAut X).range ∧
      ∀ x, φ (β x) = b * φ x * b⁻¹ := by
  haveI : S.Normal := H.normal
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
  have hBker : B ⊓ Γ.ker = B ⊓ centModSubgroup 3 S := by
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
        exact H.normal.conj_mem s hs b
      · intro hs
        have := H.normal.conj_mem _ hs b⁻¹
        simpa [mul_assoc] using this
    · rintro ⟨hb, hc⟩
      exact ⟨hb, (hker b).2 fun s hs => H.comm_of_mem_centMod hc hs⟩
  have hcard : Nat.card (B.map Γ) = 3 ^ 3 := by
    have h := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker Γ B
    rw [hBker, H.cent, H.card] at h
    have h' : Nat.card (B.map Γ) * 3 = 3 ^ 3 * 3 := by rw [h]; norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'
  obtain ⟨β, ⟨b, hb, rfl⟩, hβ⟩ := exists_outer_of_card_le_nine hZX hX (H.elem.map Γ) hcard
  exact ⟨b, hb, Γ b, hβ, hΓφ b⟩

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
