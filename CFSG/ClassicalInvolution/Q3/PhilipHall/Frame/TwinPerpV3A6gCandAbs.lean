module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gPos
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gPre
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g

open CFSG CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S (ae6ConjIn)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
  (aeBar8 vq vq_mul vq_eq_iff conj_vq vq_inv vq_empty E8Pkg zBar_eq_vq)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6h1
  (ae6M₀ AE6Vertex ae6Img mem_ae6Img ae6Img_mono ae6Img_le_iff ae6Img_inj card_ae6Img)
open CFSG.ClassicalInvolution.Asc77 (IsElemAbelian2)

section SData

variable {Y : Type} [Group Y] [Finite Y]

structure SData (I D : Subgroup Y) (P : Set (Subgroup Y)) (t τ x : Y) where
  A : AEIdent P 8
  hspan : pSpan P = I
  hker : A.φ.ker = ⊥
  hcore : pCoreOf 2 I = D
  hxI : x ∈ I
  ph_t : (pkgOf A hspan hker hcore).ph t = vq α₀
  ph_τ : (pkgOf A hspan hker hcore).ph τ = vq β₀
  perm_x : permQ 8 ((pkgOf A hspan hker hcore).ph x) = σ₀

@[expose, reducible] noncomputable def SData.pkg {I D : Subgroup Y} {P : Set (Subgroup Y)} {t τ x : Y}
    (S : SData I D P t τ x) : E8Pkg I D := pkgOf S.A S.hspan S.hker S.hcore

theorem ae6Img_pkgOf {P : Set (Subgroup Y)} (A : AEIdent P 8) {I D : Subgroup Y}
    (hpI : pSpan P = I) (hker : A.φ.ker = ⊥) (hD : pCoreOf 2 I = D) (J : Subgroup Y) :
    ae6Img (pkgOf A hpI hker hD).φ J = (J.subgroupOf (pSpan P)).map A.φ := by
  subst hpI
  ext e
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem ph_eq_vq_of_involution {I D : Subgroup Y} (P : E8Pkg I D) {J : Subgroup Y} {z : Y}
    (hz : IsUniqueInvolution J z) (hzI : z ∈ I) {δ : Finset (Fin 8)} {h : δ.card = 4} {c : Bool}
    (himg : ae6Img P.φ J = memBar δ h c) : P.ph z = vq δ := by
  have h1 : P.φ ⟨z, hzI⟩ ∈ memBar δ h c := himg ▸ mem_ae6Img.mpr ⟨z, hzI, hz.mem, rfl⟩
  have h2 : P.φ ⟨z, hzI⟩ * P.φ ⟨z, hzI⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, hzI⟩ : ↥I) * ⟨z, hzI⟩ = 1 := Subtype.ext hz.sq
    rw [this, map_one]
  rcases eq_of_mem_memBar_mul_self (by norm_num) h1 h2 with h3 | h3
  · exfalso
    apply hz.ne_one
    have : (⟨z, hzI⟩ : ↥I) = 1 := P.inj (by rw [h3, map_one])
    exact congrArg Subtype.val this
  · rw [P.ph_of_mem hzI, h3, zBar_eq_vq]

end SData

theorem inf_E3_D {Y : Type} [Group Y] [Finite Y] {E₃ D : Subgroup Y} {t τ x : Y}
    (hE3 : IsElemAbelian2 E₃ 3) (hxE : x ∈ E₃) (htD : t ∈ D) (hτD : τ ∈ D) (htE : t ∈ E₃)
    (hτE : τ ∈ E₃) (hxD : x ∉ D) (hne : τ ≠ t) (ht1 : t ≠ 1) (hτ1 : τ ≠ 1) (htt : t * t = 1) :
    ∀ z ∈ E₃ ⊓ D, z = 1 ∨ z = t ∨ z = τ ∨ z = t * τ := by
  have h8 : Nat.card E₃ = 8 := by rw [hE3.1]; norm_num
  have hdvd : Nat.card (E₃ ⊓ D : Subgroup Y) ∣ Nat.card E₃ := Subgroup.card_dvd_of_le inf_le_left
  have hne8 : Nat.card (E₃ ⊓ D : Subgroup Y) ≠ 8 := by
    intro h
    apply hxD
    have heq : E₃ ⊓ D = E₃ := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, h])
    have hxF : x ∈ E₃ ⊓ D := by rw [heq]; exact hxE
    exact hxF.2
  have hle4 : Nat.card (E₃ ⊓ D : Subgroup Y) ≤ 4 := by
    rw [h8] at hdvd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card (E₃ ⊓ D : Subgroup Y) ∣ 2 ^ 3 from hdvd)
    interval_cases k <;> simp_all
  have hc1 : t * τ ≠ 1 := fun h => hne (by
    have h1 : τ = t⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1]; exact inv_eq_of_mul_eq_one_right htt)
  refine eq_of_four (a := 1) (b := t) (c := τ) (d := t * τ) ht1.symm hτ1.symm hc1.symm hne.symm
    (fun h => hτ1 (by simpa using h.symm)) (fun h => ht1 (by simpa using h)) (one_mem _)
    ⟨htE, htD⟩ ⟨hτE, hτD⟩ ⟨E₃.mul_mem htE hτE, D.mul_mem htD hτD⟩ hle4

section Abstract

variable {Y : Type} [Group Y] [Finite Y]

theorem ae6M₀_le_preim {I D : Subgroup Y} {P : Set (Subgroup Y)} {t τ x : Y}
    (SD : SData I D P t τ x) (htI : t ∈ I) (hτI : τ ∈ I) {X : Subgroup (AEQ 8)} (hX : X ≤ aeBar8)
    (hsix : ∀ δ ∈ six, ∀ h : δ.card = 4, ∀ c, memBar δ h c ≤ X) :
    ae6M₀ P t τ ≤ preim SD.pkg X := by
  refine iSup₂_le fun J hJ => ?_
  obtain ⟨hJP, hJt⟩ := hJ
  obtain ⟨δ, hδ, c, hlab⟩ := SD.A.label J hJP
  have himg : ae6Img SD.pkg.φ J = memBar δ hδ c :=
    (ae6Img_pkgOf SD.A SD.hspan SD.hker SD.hcore J).trans hlab
  have htτI : t * τ ∈ I := I.mul_mem htI hτI
  have hvq : vq δ = vq α₀ ∨ vq δ = vq β₀ ∨ vq δ = vq α₀ * vq β₀ := by
    rcases hJt with hz | hz | hz
    · exact Or.inl ((ph_eq_vq_of_involution SD.pkg hz htI himg).symm.trans SD.ph_t)
    · exact Or.inr (Or.inl ((ph_eq_vq_of_involution SD.pkg hz hτI himg).symm.trans SD.ph_τ))
    · refine Or.inr (Or.inr ?_)
      have e1 : SD.pkg.ph t = vq α₀ := SD.ph_t
      have e2 : SD.pkg.ph τ = vq β₀ := SD.ph_τ
      have e3 := SD.pkg.ph_mul htI hτI
      rw [← e1, ← e2, ← e3]
      exact (ph_eq_vq_of_involution SD.pkg hz htτI himg).symm
  have hδ6 : δ ∈ six := mem_six_of_vq hvq
  intro g hg
  have hgI : g ∈ I := (le_pSpan hJP).trans SD.hspan.le hg
  refine mem_preim_of_mem SD.pkg hgI ?_
  have : SD.pkg.φ ⟨g, hgI⟩ ∈ ae6Img SD.pkg.φ J := mem_ae6Img.mpr ⟨g, hgI, hg, rfl⟩
  rw [himg] at this
  exact hsix δ hδ6 hδ c this

theorem gen_preim {I D : Subgroup Y} {P : Set (Subgroup Y)} {t τ x : Y} (SD : SData I D P t τ x)
    {M₀ K : Subgroup Y} (v : AE6Vertex I M₀ P) {X : Subgroup (AEQ 8)} (hX : X ≤ aeBar8)
    (hcard : Nat.card X = 86016) (hgen : X ≤ memSpan X) (hMX : M₀ ≤ preim SD.pkg X) (hKP : K ∈ P)
    (hKM : K ≤ M₀) : preim SD.pkg X ≤ pSpan (ae6ConjIn (preim SD.pkg X) K) := by
  have hcardX : Nat.card (preim SD.pkg X) = 86016 := (card_preim SD.pkg hX).trans hcard
  have hmem : ∀ (δ : Finset (Fin 8)) (h : δ.card = 4) (c : Bool), memBar δ h c ≤ X →
      memBar δ h c ≤ ae6Img SD.pkg.φ (pSpan (ae6ConjIn (preim SD.pkg X) K)) := by
    intro δ h c hc
    obtain ⟨J, hJP, hlab⟩ := SD.A.label_surj δ h c
    have himg : ae6Img SD.pkg.φ J = memBar δ h c :=
      (ae6Img_pkgOf SD.A SD.hspan SD.hker SD.hcore J).trans hlab
    have hJle : J ≤ preim SD.pkg X := by
      intro g hg
      have hgI : g ∈ I := (le_pSpan hJP).trans SD.hspan.le hg
      refine mem_preim_of_mem SD.pkg hgI ?_
      have : SD.pkg.φ ⟨g, hgI⟩ ∈ ae6Img SD.pkg.φ J := mem_ae6Img.mpr ⟨g, hgI, hg, rfl⟩
      rw [himg] at this
      exact hc this
    obtain ⟨g, hg, hgJ⟩ := v.orbit (preim SD.pkg X) hMX (preim_le_I SD.pkg X) hcardX K hKP J hJP
      (hKM.trans hMX) hJle
    have hJspan : J ≤ pSpan (ae6ConjIn (preim SD.pkg X) K) := le_pSpan ⟨g, hg, hgJ⟩
    rw [← himg]
    exact ae6Img_mono hJspan
  have hXs : X ≤ ae6Img SD.pkg.φ (pSpan (ae6ConjIn (preim SD.pkg X) K)) :=
    hgen.trans (iSup_le fun δ => iSup_le fun h => iSup_le fun c => iSup_le fun hc => hmem δ h c hc)
  rw [← ae6Img_le_iff SD.pkg.inj (preim_le_I SD.pkg X), ae6Img_preim SD.pkg hX]
  exact hXs

end Abstract

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g
