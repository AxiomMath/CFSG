module

public import CFSG.FeitThompson.Representations.CoherentImageAntirealBlockSelection
public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.PowerOperationsPreserveVirtualChars

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace DisjointCoherentBlocks

open CoherentAntirealBlock

theorem mem_span_Irr_of_mem_virtualCharSpan {G : Type*} [Group G] [Finite G] {f : G → ℂ}
    (hf : f ∈ virtualCharSpan G) : f ∈ Submodule.span ℤ (Irr G) :=
  virtualCharSpan_le (fun V _ => FDRep.character_mem_span_Irr V) hf

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
  {S T T₁ T₂ : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}
  {τT : charSpanZero (T : Set (L → ℂ)) →+ virtualChars G}
  {ν : Submodule.span ℤ (T : Set (L → ℂ)) →+ virtualChars G}
  {τ₁ : charSpanZero (T₁ : Set (L → ℂ)) →+ virtualChars G}
  {ν₁ : Submodule.span ℤ (T₁ : Set (L → ℂ)) →+ virtualChars G}
  {τ₂ : charSpanZero (T₂ : Set (L → ℂ)) →+ virtualChars G}
  {ν₂ : Submodule.span ℤ (T₂ : Set (L → ℂ)) →+ virtualChars G}

theorem cfInner_apply_mem_eq_zero (hc : IsSubcoherent S tau R) (hTS : T ⊆ S)
    (hTstar : ∀ ψ ∈ T, star ψ ∈ T) (hν : IsCoherentWith (T : Set (L → ℂ)) τT ν)
    (hτT : ∀ f : charSpanZero (T : Set (L → ℂ)), (τT f : G → ℂ) = tau (f : L → ℂ))
    {χ ψ : L → ℂ} (hχS : χ ∈ S) (hχT : χ ∉ T) (hψ : ψ ∈ T) {r : G → ℂ} (hr : r ∈ R χ) :
    cfInner (ν ⟨ψ, mem_span_of_mem hψ⟩ : G → ℂ) r = 0 := by
  obtain ⟨n, -, -, -, E, hER, -, hEsum, -⟩ :=
    exists_pos_nat_card_R_and_subset hc hTS hTstar hν hτT
      (fun s hs => mem_span_Irr_of_mem_virtualCharSpan (hc.R_subset ψ (hTS hψ) s hs))
      (fun f => coe_mem_span_Irr (ν f)) hψ
  have hψχ : ψ ≠ χ := fun h => hχT (h ▸ hψ)
  have hψstar : ψ ≠ star χ := fun h => hχT (by simpa [h] using hTstar ψ hψ)
  rw [hEsum, cfInner_sum_left]
  refine Finset.sum_eq_zero fun s hs => ?_
  have h := hc.charInner_R_R χ hχS ψ (hTS hψ) hψχ hψstar r hr s (hER hs)
  rw [charInner_eq_cfInner] at h
  rw [← conj_cfInner, h, map_zero]

theorem cfInner_eq_zero_of_notMem (hc : IsSubcoherent S tau R) (hTS : T ⊆ S)
    (hTstar : ∀ ψ ∈ T, star ψ ∈ T) (hν : IsCoherentWith (T : Set (L → ℂ)) τT ν)
    (hτT : ∀ f : charSpanZero (T : Set (L → ℂ)), (τT f : G → ℂ) = tau (f : L → ℂ))
    {χ : L → ℂ} (hχS : χ ∈ S) (hχT : χ ∉ T)
    (f : Submodule.span ℤ (T : Set (L → ℂ))) {r : G → ℂ} (hr : r ∈ R χ) :
    cfInner (ν f : G → ℂ) r = 0 := by
  obtain ⟨g, hg⟩ := f
  induction hg using Submodule.span_induction with
  | mem x hx =>
      exact cfInner_apply_mem_eq_zero hc hTS hTstar hν hτT hχS hχT (Finset.mem_coe.1 hx) hr
  | zero =>
      have he : (⟨0, Submodule.zero_mem _⟩ : Submodule.span ℤ (T : Set (L → ℂ))) = 0 := rfl
      rw [he, map_zero, ZeroMemClass.coe_zero, cfInner_zero_left]
  | add x y hx hy ihx ihy =>
      have he : (⟨x + y, Submodule.add_mem _ hx hy⟩ : Submodule.span ℤ (T : Set (L → ℂ)))
          = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [he, map_add, Submodule.coe_add, cfInner_add_left, ihx, ihy, add_zero]
  | smul a x hx ih =>
      have he : (⟨a • x, Submodule.smul_mem _ a hx⟩ : Submodule.span ℤ (T : Set (L → ℂ)))
          = a • ⟨x, hx⟩ := rfl
      rw [he, map_zsmul, SetLike.val_smul, cfInner_zsmul_left, ih, mul_zero]

theorem isOrthogonal_of_notMem (hc : IsSubcoherent S tau R) (hTS : T ⊆ S)
    (hTstar : ∀ ψ ∈ T, star ψ ∈ T) (hν : IsCoherentWith (T : Set (L → ℂ)) τT ν)
    (hτT : ∀ f : charSpanZero (T : Set (L → ℂ)), (τT f : G → ℂ) = tau (f : L → ℂ))
    {χ : L → ℂ} (hχS : χ ∈ S) (hχT : χ ∉ T)
    (f : Submodule.span ℤ (T : Set (L → ℂ))) {r : G → ℂ} (hr : r ∈ R χ) :
    IsOrthogonal (ν f : G → ℂ) r :=
  isOrthogonal_iff.2 (cfInner_eq_zero_of_notMem hc hTS hTstar hν hτT hχS hχT f hr)

theorem cfInner_eq_zero_of_disjoint (hc : IsSubcoherent S tau R)
    (hT₁S : T₁ ⊆ S) (hT₁star : ∀ ψ ∈ T₁, star ψ ∈ T₁)
    (hν₁ : IsCoherentWith (T₁ : Set (L → ℂ)) τ₁ ν₁)
    (hτ₁ : ∀ f : charSpanZero (T₁ : Set (L → ℂ)), (τ₁ f : G → ℂ) = tau (f : L → ℂ))
    (hT₂S : T₂ ⊆ S) (hT₂star : ∀ ψ ∈ T₂, star ψ ∈ T₂)
    (hν₂ : IsCoherentWith (T₂ : Set (L → ℂ)) τ₂ ν₂)
    (hτ₂ : ∀ f : charSpanZero (T₂ : Set (L → ℂ)), (τ₂ f : G → ℂ) = tau (f : L → ℂ))
    (hdisj : Disjoint T₁ T₂)
    (f₁ : Submodule.span ℤ (T₁ : Set (L → ℂ))) (f₂ : Submodule.span ℤ (T₂ : Set (L → ℂ))) :
    cfInner (ν₁ f₁ : G → ℂ) (ν₂ f₂ : G → ℂ) = 0 := by
  suffices h : cfInner (ν₂ f₂ : G → ℂ) (ν₁ f₁ : G → ℂ) = 0 by
    rw [← conj_cfInner, h, map_zero]
  obtain ⟨g, hg⟩ := f₂
  induction hg using Submodule.span_induction with
  | mem x hx =>
      have hxT₂ : x ∈ T₂ := Finset.mem_coe.1 hx
      have hxT₁ : x ∉ T₁ := Finset.disjoint_right.1 hdisj hxT₂
      obtain ⟨n, -, -, -, E, hER, -, hEsum, -⟩ :=
        exists_pos_nat_card_R_and_subset hc hT₂S hT₂star hν₂ hτ₂
          (fun s hs => mem_span_Irr_of_mem_virtualCharSpan (hc.R_subset x (hT₂S hxT₂) s hs))
          (fun f => coe_mem_span_Irr (ν₂ f)) hxT₂
      rw [hEsum, cfInner_sum_left]
      refine Finset.sum_eq_zero fun s hs => ?_
      rw [← conj_cfInner,
        cfInner_eq_zero_of_notMem hc hT₁S hT₁star hν₁ hτ₁ (hT₂S hxT₂) hxT₁ f₁ (hER hs), map_zero]
  | zero =>
      have he : (⟨0, Submodule.zero_mem _⟩ : Submodule.span ℤ (T₂ : Set (L → ℂ))) = 0 := rfl
      rw [he, map_zero, ZeroMemClass.coe_zero, cfInner_zero_left]
  | add x y hx hy ihx ihy =>
      have he : (⟨x + y, Submodule.add_mem _ hx hy⟩ : Submodule.span ℤ (T₂ : Set (L → ℂ)))
          = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [he, map_add, Submodule.coe_add, cfInner_add_left, ihx, ihy, add_zero]
  | smul a x hx ih =>
      have he : (⟨a • x, Submodule.smul_mem _ a hx⟩ : Submodule.span ℤ (T₂ : Set (L → ℂ)))
          = a • ⟨x, hx⟩ := rfl
      rw [he, map_zsmul, SetLike.val_smul, cfInner_zsmul_left, ih, mul_zero]

theorem isOrthogonal_of_disjoint (hc : IsSubcoherent S tau R)
    (hT₁S : T₁ ⊆ S) (hT₁star : ∀ ψ ∈ T₁, star ψ ∈ T₁)
    (hν₁ : IsCoherentWith (T₁ : Set (L → ℂ)) τ₁ ν₁)
    (hτ₁ : ∀ f : charSpanZero (T₁ : Set (L → ℂ)), (τ₁ f : G → ℂ) = tau (f : L → ℂ))
    (hT₂S : T₂ ⊆ S) (hT₂star : ∀ ψ ∈ T₂, star ψ ∈ T₂)
    (hν₂ : IsCoherentWith (T₂ : Set (L → ℂ)) τ₂ ν₂)
    (hτ₂ : ∀ f : charSpanZero (T₂ : Set (L → ℂ)), (τ₂ f : G → ℂ) = tau (f : L → ℂ))
    (hdisj : Disjoint T₁ T₂)
    (f₁ : Submodule.span ℤ (T₁ : Set (L → ℂ))) (f₂ : Submodule.span ℤ (T₂ : Set (L → ℂ))) :
    IsOrthogonal (ν₁ f₁ : G → ℂ) (ν₂ f₂ : G → ℂ) :=
  isOrthogonal_iff.2
    (cfInner_eq_zero_of_disjoint hc hT₁S hT₁star hν₁ hτ₁ hT₂S hT₂star hν₂ hτ₂ hdisj f₁ f₂)

end DisjointCoherentBlocks

end CFSG.FeitThompson
