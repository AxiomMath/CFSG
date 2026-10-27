module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma31g
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section Generic

variable {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {F₁ F₂ : Type} [Field F₁] [Field F₂]

omit [Finite H] in
theorem orderOf_conj_two {w : H} (hw : orderOf w = 2) (c : H) : orderOf (c * w * c⁻¹) = 2 := by
  have h1 := MulEquiv.orderOf_eq (MulAut.conj c) w
  rw [MulAut.conj_apply] at h1
  rw [h1]; exact hw

theorem frattini_generic (hPr : IVK.ProdSL2 H K₁ K₂ F₁ F₂) (hF₁ : 3 < Nat.card F₁) (hF₂ : 3 < Nat.card F₂)
    (h31a : IVK.IVK_3_1a) (h31c : IVK.IVK_3_1c) (h31g : IVK.Proofs2.IVK_3_1g_fixed)
    (T : Sylow 2 H) (hN : (normalizer (K₁ : Set H)).Normal)
    (hNT : normalizer (K₁ : Set H) ⊔ (T : Subgroup H) = ⊤)
    {ζ : H} (hζK : ζ ∈ K₁ ⊓ K₂) (hζ1 : ζ ≠ 1) (hζc : ∀ c : H, c * ζ = ζ * c)
    {w : H} (hwT : w ∈ (T : Subgroup H)) (hw2 : orderOf w = 2)
    (hcase : (w ∈ K₁ ⊔ K₂ ∧ w ≠ ζ) ∨ IVK.IsDiagInv K₁ K₂ F₁ F₂ w) :
    ∀ c : H, ∃ l ∈ K₁ ⊔ K₂, ∃ d ∈ centralizer ({w} : Set H), ∃ σ ∈ (T : Subgroup H),
      c = l * d * σ := by
  have hwsq : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw2, pow_two] at this
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hwsq
  intro c
  rcases hcase with ⟨hwK, hwζ⟩ | hD
  ·
    have hy : c * w * c⁻¹ ∈ K₁ ⊔ K₂ := hPr.fstar_normal.conj_mem w hwK c
    have hyζ : c * w * c⁻¹ ≠ ζ := by
      intro h
      apply hwζ
      have : w = c⁻¹ * ζ * c := by rw [← h]; group
      rw [this, hζc c⁻¹]; group
    obtain ⟨l, hl, hlw⟩ := h31a F₁ F₂ H K₁ K₂ hPr ζ hζK hζ1 w (c * w * c⁻¹) hwK hy hw2
      (orderOf_conj_two hw2 c) hwζ hyζ
    refine ⟨l, hl, l⁻¹ * c, ?_, 1, (T : Subgroup H).one_mem, by group⟩
    rw [mem_centralizer_singleton_iff]
    have : l * w * l⁻¹ = c * w * c⁻¹ := hlw
    calc l⁻¹ * c * w = l⁻¹ * (c * w * c⁻¹) * c := by group
      _ = l⁻¹ * (l * w * l⁻¹) * c := by rw [this]
      _ = w * (l⁻¹ * c) := by
        have : l⁻¹ * (l * w * l⁻¹) * c = w * l⁻¹ * c := by group
        rw [this]; group
  ·
    have hwN : w ∈ normalizer (K₁ : Set H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => hD.1 x hx, fun hx => ?_⟩
      have := hD.1 _ hx
      have e : w * (w * x * w⁻¹) * w⁻¹ = x := by
        rw [hwinv, ← mul_assoc, ← mul_assoc, hwsq, one_mul, mul_assoc, hwsq, mul_one]
      rwa [e] at this
    obtain ⟨n, hn, σ, hσ, rfl⟩ := Subgroup.mem_sup_of_normal_left.1
      (show c ∈ normalizer (K₁ : Set H) ⊔ (T : Subgroup H) by rw [hNT]; exact Subgroup.mem_top c)
    have hcomm := (h31g F₁ F₂ H K₁ K₂ hPr hF₁ hF₂).2 n hn w hwN
    obtain ⟨hconj, -⟩ := h31c F₁ F₂ H K₁ K₂ hPr T w hwT hw2 hD
    have hy2 : orderOf (n * w * n⁻¹) = 2 := orderOf_conj_two hw2 n
    obtain ⟨l, hl, hlw⟩ := hconj w (n * w * n⁻¹) ⟨1, (K₁ ⊔ K₂).one_mem, by rw [one_mul]⟩
      ⟨⁅n, w⁆, hcomm, by simp [commutatorElement_def]⟩ hw2 hy2
    refine ⟨l, hl, l⁻¹ * n, ?_, σ, hσ, by group⟩
    rw [mem_centralizer_singleton_iff]
    have : l * w * l⁻¹ = n * w * n⁻¹ := hlw
    calc l⁻¹ * n * w = l⁻¹ * (n * w * n⁻¹) * n := by group
      _ = l⁻¹ * (l * w * l⁻¹) * n := by rw [this]
      _ = w * (l⁻¹ * n) := by
        have : l⁻¹ * (l * w * l⁻¹) * n = w * l⁻¹ * n := by group
        rw [this]; group

omit [Finite H] in
theorem center_map_eq_inf (h : IVK.ProdSL2 H K₁ K₂ F₁ F₂) {ζ : H} (hζ : ζ ∈ K₁ ⊓ K₂) (hζ1 : ζ ≠ 1) :
    (Subgroup.center ↥K₂).map K₂.subtype = K₁ ⊓ K₂ := by
  have hζ' : ζ ∈ K₂ ⊓ K₁ := by rwa [inf_comm] at hζ
  obtain ⟨-, hφζ⟩ := h.symm.z_data₁ hζ' hζ1
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    change b ∈ Subgroup.center ↥K₂ at hb
    have hcen : h.symm.slEquiv₁ b ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F₂) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨k, rfl⟩ := h.symm.slEquiv₁.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hb k]
    rcases (CFSG.Semidihedral.ProjectiveSL2Cover.mem_center_iff_eq_one_or_minusIdentity F₂ _).1 hcen with h1 | h1
    · have : b = 1 := h.symm.slEquiv₁.injective (by rw [h1, map_one])
      rw [this]
      simp
    · have hm : h.symm.slEquiv₁ b = h.symm.slEquiv₁ ⟨ζ, hζ'.1⟩ := by
        rw [hφζ, h1, CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_eq_neg_one]
        rfl
      have : b = ⟨ζ, hζ'.1⟩ := h.symm.slEquiv₁.injective hm
      have hbζ : (b : H) = ζ := congrArg Subtype.val this
      change (b : H) ∈ K₁ ⊓ K₂
      rw [hbζ]
      exact hζ
  · intro hx
    refine ⟨⟨x, hx.2⟩, ?_, rfl⟩
    change (⟨x, hx.2⟩ : ↥K₂) ∈ Subgroup.center ↥K₂
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (h.comm x hx.1 c c.2).symm

end Generic

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
