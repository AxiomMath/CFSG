module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23Models
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.FzBU

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzBU CFSG.GH74.GLS.Bg.TwoGroups

@[expose] def fzbF4Code (x : L23.F4c) : ℕ := x.a.val + 2 * x.b.val

@[expose] def fzbEnc (x : UT3 L23.F4c) : ℕ :=
  16 * fzbF4Code x.a + 4 * fzbF4Code x.b + fzbF4Code x.c

private theorem fzbF4Code_lt (x : L23.F4c) : fzbF4Code x < 4 := by
  have ha : x.a.val < 2 := ZMod.val_lt x.a
  have hb : x.b.val < 2 := ZMod.val_lt x.b
  unfold fzbF4Code
  omega

theorem fzbEnc_lt (x : UT3 L23.F4c) : fzbEnc x < 64 := by
  have ha := fzbF4Code_lt x.a
  have hb := fzbF4Code_lt x.b
  have hc := fzbF4Code_lt x.c
  unfold fzbEnc
  omega

theorem fzbEnc_inj {x y : UT3 L23.F4c} (h : fzbEnc x = fzbEnc y) : x = y := by
  revert x y
  decide +kernel

private theorem fzbEnc_surj_fin : ∀ n : Fin 64, ∃ x : UT3 L23.F4c, fzbEnc x = (n : ℕ) := by
  decide +kernel

theorem fzbEnc_surj {n : ℕ} (hn : n < 64) : ∃ x : UT3 L23.F4c, fzbEnc x = n := by
  obtain ⟨x, hx⟩ := fzbEnc_surj_fin ⟨n, hn⟩
  exact ⟨x, hx⟩

theorem fzbEnc_one : fzbEnc (1 : UT3 L23.F4c) = 0 := by
  decide +kernel

theorem fzbEnc_mul (x y : UT3 L23.F4c) : fzbEnc (x * y) = uMul (fzbEnc x) (fzbEnc y) := by
  revert x y
  decide +kernel

structure FzbCoding {G : Type} [Group G] (P : Subgroup G) where
  enc : G → ℕ
  dec : ℕ → G
  enc_lt : ∀ p ∈ P, enc p < 64
  dec_mem : ∀ x < 64, dec x ∈ P
  enc_dec : ∀ x < 64, enc (dec x) = x
  dec_enc : ∀ p ∈ P, dec (enc p) = p
  enc_one : enc 1 = 0
  enc_mul : ∀ p ∈ P, ∀ p' ∈ P, enc (p * p') = uMul (enc p) (enc p')

theorem fzb_exists_coding {G : Type} [Group G] {P : Subgroup G}
    (h : Nonempty (↥P ≃* SylSL3_4)) : Nonempty (FzbCoding P) := by
  classical
  obtain ⟨φ⟩ := h
  let ψ : ↥P ≃* UT3 L23.F4c := φ.trans L23.sylLCongr
  let enc : G → ℕ := fun p => if hp : p ∈ P then fzbEnc (ψ ⟨p, hp⟩) else 0
  let dec : ℕ → G := fun x =>
    if hx : x < 64 then ((ψ.symm (Classical.choose (fzbEnc_surj hx)) : ↥P) : G) else 1
  refine ⟨⟨enc, dec, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro p hp
    show enc p < 64
    simp only [enc]
    rw [dif_pos hp]
    exact fzbEnc_lt _
  · intro x hx
    show dec x ∈ P
    simp only [dec]
    rw [dif_pos hx]
    exact (ψ.symm _).2
  · intro x hx
    have hdx : dec x = ((ψ.symm (Classical.choose (fzbEnc_surj hx)) : ↥P) : G) := by
      simp only [dec]
      rw [dif_pos hx]
    rw [hdx]
    simp only [enc]
    rw [dif_pos (ψ.symm (Classical.choose (fzbEnc_surj hx))).2]
    have hsub : (⟨((ψ.symm (Classical.choose (fzbEnc_surj hx)) : ↥P) : G),
        (ψ.symm (Classical.choose (fzbEnc_surj hx))).2⟩ : ↥P)
        = ψ.symm (Classical.choose (fzbEnc_surj hx)) := Subtype.ext rfl
    rw [hsub, MulEquiv.apply_symm_apply]
    exact Classical.choose_spec (fzbEnc_surj hx)
  · intro p hp
    have henc : enc p = fzbEnc (ψ ⟨p, hp⟩) := by
      simp only [enc]
      rw [dif_pos hp]
    rw [henc]
    have hx : fzbEnc (ψ ⟨p, hp⟩) < 64 := fzbEnc_lt _
    have hdx : dec (fzbEnc (ψ ⟨p, hp⟩)) =
        ((ψ.symm (Classical.choose (fzbEnc_surj hx)) : ↥P) : G) := by
      simp only [dec]
      rw [dif_pos hx]
    rw [hdx]
    have hchoose : Classical.choose (fzbEnc_surj hx) = ψ ⟨p, hp⟩ :=
      fzbEnc_inj (Classical.choose_spec (fzbEnc_surj hx))
    rw [hchoose, MulEquiv.symm_apply_apply]
  · have h1 : (1 : G) ∈ P := P.one_mem
    have henc : enc 1 = fzbEnc (ψ ⟨1, h1⟩) := by
      simp only [enc]
      rw [dif_pos h1]
    rw [henc]
    have hsub : (⟨(1 : G), h1⟩ : ↥P) = 1 := Subtype.ext rfl
    rw [hsub, map_one, fzbEnc_one]
  · intro p hp p' hp'
    have hmem : p * p' ∈ P := P.mul_mem hp hp'
    have henc : enc (p * p') = fzbEnc (ψ ⟨p * p', hmem⟩) := by
      simp only [enc]
      rw [dif_pos hmem]
    have hencp : enc p = fzbEnc (ψ ⟨p, hp⟩) := by
      simp only [enc]
      rw [dif_pos hp]
    have hencp' : enc p' = fzbEnc (ψ ⟨p', hp'⟩) := by
      simp only [enc]
      rw [dif_pos hp']
    have hsub : (⟨p * p', hmem⟩ : ↥P) = (⟨p, hp⟩ : ↥P) * ⟨p', hp'⟩ := Subtype.ext rfl
    calc enc (p * p') = fzbEnc (ψ ⟨p * p', hmem⟩) := henc
      _ = fzbEnc (ψ ((⟨p, hp⟩ : ↥P) * ⟨p', hp'⟩)) := by rw [← hsub]
      _ = fzbEnc (ψ ⟨p, hp⟩ * ψ ⟨p', hp'⟩) := by rw [map_mul]
      _ = uMul (fzbEnc (ψ ⟨p, hp⟩)) (fzbEnc (ψ ⟨p', hp'⟩)) := fzbEnc_mul _ _
      _ = uMul (enc p) (enc p') := by rw [← hencp, ← hencp']

namespace FzbCoding

variable {G : Type} [Group G] {P : Subgroup G} (C : FzbCoding P)

theorem dec_zero : C.dec 0 = 1 := by
  rw [← C.enc_one]
  exact C.dec_enc 1 P.one_mem

theorem enc_inj {p p' : G} (hp : p ∈ P) (hp' : p' ∈ P) (h : C.enc p = C.enc p') : p = p' := by
  rw [← C.dec_enc p hp, h, C.dec_enc p' hp']

theorem dec_mul {x y : ℕ} (hx : x < 64) (hy : y < 64) :
    C.dec (uMul x y) = C.dec x * C.dec y := by
  have hmem : C.dec x * C.dec y ∈ P := P.mul_mem (C.dec_mem x hx) (C.dec_mem y hy)
  have henc : C.enc (C.dec x * C.dec y) = uMul x y := by
    rw [C.enc_mul (C.dec x) (C.dec_mem x hx) (C.dec y) (C.dec_mem y hy),
      C.enc_dec x hx, C.enc_dec y hy]
  rw [← henc, C.dec_enc _ hmem]

theorem exists_dec {p : G} (hp : p ∈ P) : ∃ x < 64, C.dec x = p :=
  ⟨C.enc p, C.enc_lt p hp, C.dec_enc p hp⟩

end FzbCoding

end CFSG.OddStandard.SmallF3.FritzII
