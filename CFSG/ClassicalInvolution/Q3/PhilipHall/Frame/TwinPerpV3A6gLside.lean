module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gNorm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gGen
public import CFSG.ClassicalInvolution.Q3.TL3T13
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6S
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eIdent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h1ParWr

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g

open CFSG CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Asc77 (IsElemAbelian2)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S (ae6ConjIn)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6h1
  (ae6Img mem_ae6Img ae6Img_mono ae6Img_le_iff ae6Img_inj card_ae6Img ae6Img_le_range)

section LSide

variable {Y : Type} [Group Y] [Finite Y] {L K : Subgroup Y}
  (B : AEIdentOn (ae6ConjIn L K) 8 e29Sets e29Sub) (hspan : pSpan (ae6ConjIn L K) = L)

@[expose] noncomputable def lhom : ↥L →* AEQ 8 := B.φ.comp (Subgroup.inclusion hspan.symm.le)

theorem lhom_apply (g : Y) (hg : g ∈ L) :
    lhom B hspan ⟨g, hg⟩ = B.φ ⟨g, hspan.symm.le hg⟩ := rfl

theorem lhom_injective (hker : B.φ.ker = ⊥) : Function.Injective (lhom B hspan) :=
  ((MonoidHom.ker_eq_bot_iff _).mp hker).comp (Subgroup.inclusion_injective _)

theorem lhom_range : (lhom B hspan).range = e29Sub := by
  rw [← B.range_eq]
  ext e
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Subgroup.inclusion hspan.symm.le y, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨⟨z.1, hspan.le z.2⟩, rfl⟩

variable {B hspan}

theorem zBar_mem_limg {E₃ Q : Subgroup Y} {t : Y} (h8 : ∀ J ∈ ae6ConjIn L K, Nat.card J = 8)
    (hKt : IsUniqueInvolution K t) (hnorm : ∀ l ∈ L, ∀ e ∈ E₃, l * e * l⁻¹ ∈ E₃) (htE : t ∈ E₃)
    (hEQ : E₃ ≤ Q) :
    ∀ δ ∈ affinePlanes, ∀ h : δ.card = 4, zBar δ h ∈ ae6Img (lhom B hspan) Q := by
  intro δ hδ h
  obtain ⟨J, hJP, hlab⟩ := B.label_surj δ hδ h true
  have hJP' := hJP
  obtain ⟨l, hl, rfl⟩ := hJP'
  have hu := hKt.conj l
  have hK1 : K ∈ ae6ConjIn L K := ⟨1, L.one_mem, conjSub_one K⟩
  have htL : t ∈ L := hspan.le (le_pSpan hK1 hKt.mem)
  have huL : l * t * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl htL) (L.inv_mem hl)
  have hphi := phi_map_eq_zBar B.φ (by norm_num : 5 ≤ 8) hJP (h8 _ hJP) hlab hu
  refine mem_ae6Img.mpr ⟨l * t * l⁻¹, huL, hEQ (hnorm l hl t htE), ?_⟩
  rw [lhom_apply]
  exact hphi

theorem limg_facts (hker : B.φ.ker = ⊥) {E₃ Q : Subgroup Y} {t : Y}
    (h8 : ∀ J ∈ ae6ConjIn L K, Nat.card J = 8) (hKt : IsUniqueInvolution K t)
    (hnorm : ∀ l ∈ L, ∀ e ∈ E₃, l * e * l⁻¹ ∈ E₃) (htE : t ∈ E₃) (hEQ : E₃ ≤ Q) (hQL : Q ≤ L)
    (hQ : IsElemAbelian2 Q 6) :
    ae6Img (lhom B hspan) Q ≤ e29Sub ∧ (∀ a ∈ ae6Img (lhom B hspan) Q, a * a = 1) ∧
      Nat.card (ae6Img (lhom B hspan) Q) = 64 ∧
      ∀ δ ∈ affinePlanes, ∀ h : δ.card = 4, zBar δ h ∈ ae6Img (lhom B hspan) Q := by
  have hinj := lhom_injective B hspan hker
  refine ⟨(lhom_range B hspan) ▸ ae6Img_le_range Q, ?_, ?_, zBar_mem_limg h8 hKt hnorm htE hEQ⟩
  · intro a ha
    obtain ⟨g, hg, hgQ, rfl⟩ := mem_ae6Img.mp ha
    rw [← map_mul]
    have : (⟨g, hg⟩ : ↥L) * ⟨g, hg⟩ = 1 := Subtype.ext (hQ.2 g hgQ)
    rw [this, map_one]
  · rw [card_ae6Img hinj hQL, hQ.1]
    norm_num

include hspan in
theorem lside_normal (hker : B.φ.ker = ⊥) {E₃ Q : Subgroup Y} {t : Y}
    (h8 : ∀ J ∈ ae6ConjIn L K, Nat.card J = 8) (hKt : IsUniqueInvolution K t)
    (hnorm : ∀ l ∈ L, ∀ e ∈ E₃, l * e * l⁻¹ ∈ E₃) (htE : t ∈ E₃) (hEQ : E₃ ≤ Q) (hQL : Q ≤ L)
    (hQ : IsElemAbelian2 Q 6) : ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q := by
  have hinj := lhom_injective B hspan hker
  have hrange := lhom_range B hspan
  obtain ⟨hA, hsq, hcard, hz⟩ := limg_facts hker h8 hKt hnorm htE hEQ hQL hQ
  intro l hl q hq
  have hnormQ := classify_normal hA hsq hcard hz
  have hlq : lhom B hspan ⟨l, hl⟩ ∈ e29Sub := hrange ▸ ⟨_, rfl⟩
  have haQ : lhom B hspan ⟨q, hQL hq⟩ ∈ ae6Img (lhom B hspan) Q :=
    mem_ae6Img.mpr ⟨q, hQL hq, hq, rfl⟩
  have h1 := hnormQ _ hlq _ haQ
  obtain ⟨g', hg', hg'Q, hg'e⟩ := mem_ae6Img.mp h1
  have hmem : l * q * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl (hQL hq)) (L.inv_mem hl)
  have hconj : lhom B hspan ⟨l * q * l⁻¹, hmem⟩ =
      lhom B hspan ⟨l, hl⟩ * lhom B hspan ⟨q, hQL hq⟩ * (lhom B hspan ⟨l, hl⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have : (⟨g', hg'⟩ : ↥L) = ⟨l * q * l⁻¹, hmem⟩ := hinj (by rw [hg'e, hconj])
  have e : g' = l * q * l⁻¹ := congrArg Subtype.val this
  rw [← e]
  exact hg'Q

include hspan in
theorem lside_ncard_le_three (hker : B.φ.ker = ⊥) {E₃ : Subgroup Y} {t : Y}
    (h8 : ∀ J ∈ ae6ConjIn L K, Nat.card J = 8) (hKt : IsUniqueInvolution K t)
    (hnorm : ∀ l ∈ L, ∀ e ∈ E₃, l * e * l⁻¹ ∈ E₃) (htE : t ∈ E₃) :
    Set.ncard {Q : Subgroup Y | Q ≤ L ∧ IsElemAbelian2 Q 6 ∧ E₃ ≤ Q} ≤ 3 := by
  have hinj := lhom_injective B hspan hker
  refine le_trans (Set.ncard_le_ncard_of_injOn (fun Q => ae6Img (lhom B hspan) Q) ?_ ?_
    (Set.toFinite _)) ncard_E64_le_three
  · rintro Q ⟨hQL, hQ, hEQ⟩
    exact limg_facts hker h8 hKt hnorm htE hEQ hQL hQ
  · intro Q hQ Q' hQ' h
    exact ae6Img_inj hinj hQ.1 hQ'.1 h

end LSide

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g
