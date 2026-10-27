module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenElems
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocalCore
public import Certificates.Certificate17450

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal

open CFSG.Monster.B CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

local notation "sm" => CFSG.KC.BM.stripMat

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

section Elements


@[expose] noncomputable def sThree : NativeSporadic.B :=
  (eSeven ^ 2 * ySeven * eSeven * ySeven ^ 4 * tauTwo * ySeven ^ 4 * eSeven ^ 2 * tauOne * ySeven *
    tauOne * ySeven) ^ 7

@[expose] noncomputable def sFour : NativeSporadic.B :=
  (eSeven ^ 2 * ySeven ^ 4 * eSeven ^ 2 * tauTwo * ySeven * eSeven) ^ 7

@[expose] noncomputable def fSeven : NativeSporadic.B :=
  ySeven * tauOne * ySeven * eSeven ^ 2 * tauTwo * ySeven * eSeven ^ 2 * ySeven * ySeven * eSeven

@[expose] noncomputable def uOne : NativeSporadic.B :=
  (ySeven ^ 4 * eSeven * ySeven ^ 4 * eSeven * ySeven * eSeven * ySeven * eSeven) ^ 7

@[expose] noncomputable def uTwo : NativeSporadic.B :=
  (ySeven * eSeven * ySeven ^ 4 * tauTwo * ySeven * ySeven * eSeven ^ 2 * tauOne * ySeven) ^ 7

end Elements

structure LocalParts (α x τ₁ s₃ s₄ f u₁ u₂ : NativeSporadic.B) : Prop where
  rk_ax : rk (α * x) = 3996
  rk_at : rk (α * τ₁) = 2158
  rk_tx : rk (τ₁ * x) = 4008
  s3_sq : s₃ * s₃ = 1
  s3_rk : rk s₃ = 1860
  s3_x : s₃ * x = x * s₃
  w3_cube : (τ₁ * s₃) ^ 3 = 1
  w3_ne : τ₁ * s₃ ≠ 1
  s4_sq : s₄ * s₄ = 1
  s4_rk : rk s₄ = 1860
  s4_x : s₄ * x = x * s₄
  w4_pow : (τ₁ * s₄) ^ 4 = 1
  w4_sq_ne : (τ₁ * s₄) * (τ₁ * s₄) ≠ 1
  w4_rk : rk ((τ₁ * s₄) * (τ₁ * s₄)) = 2048
  f_pow : f ^ 7 = 1
  f_ne : f ≠ 1
  f_x : f * x = x * f
  f_a : f * α = α * f
  f_t : f * τ₁ = τ₁ * f
  f_ne_pow : ∀ i < 7, f ≠ x ^ i
  rk_line : rk (α * f) = 4008 ∧ rk (τ₁ * (x * f)) = 4008 ∧ rk (τ₁ * (x * f ^ 2)) = 4008 ∧
    rk (α * (x * f ^ 3)) = 4008 ∧ rk (τ₁ * (x * f ^ 4)) = 4008 ∧ rk (α * (x * f ^ 5)) = 4008 ∧
    rk (α * (x * f ^ 6)) = 4008
  u1_pow : u₁ ^ 3 = 1
  u1_ne : u₁ ≠ 1
  u2_pow : u₂ ^ 3 = 1
  u2_ne : u₂ ≠ 1
  u1_x : u₁ * x = x * u₁
  u2_x : u₂ * x = x * u₂
  u1_u2 : u₁ * u₂ = u₂ * u₁
  u2_ne_pow : ∀ i < 3, u₂ ≠ u₁ ^ i
  rk_q : rk u₁ = 2862 ∧ rk u₂ = 2862 ∧ rk (u₁ * u₂) = 2862 ∧ rk (u₁ * u₂ ^ 2) = 2862

theorem rk_of_bMat {g : NativeSporadic.B} {G : MatB} (hg : bMat g = G) :
    rk g = Matrix.rank (G - 1) := by
  change Matrix.rank (bMat g - 1) = _
  rw [hg]

theorem localParts_of {a x t s₃ s₄ f u₁ u₂ : NativeSporadic.B} {Al X T1 S3 S4 F U1 U2 : MatB}
    (ha : bMat a = Al) (hx : bMat x = X) (ht : bMat t = T1) (hs₃ : bMat s₃ = S3)
    (hs₄ : bMat s₄ = S4) (hf : bMat f = F) (hu₁ : bMat u₁ = U1) (hu₂ : bMat u₂ = U2)
    (P : CFSG.KC.BM.SevenFacts.Fact17450Of Al X T1 S3 S4 F U1 U2) :
    LocalParts a x t s₃ s₄ f u₁ u₂ := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
    f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38,
    f39⟩ := P
  have inj : ∀ {g h : NativeSporadic.B}, bMat g = bMat h → g = h := fun h => bMat_injective h
  refine ⟨(rk_of_bMat ?_).trans f1, (rk_of_bMat ?_).trans f2, (rk_of_bMat ?_).trans f3, inj ?_,
    (rk_of_bMat hs₃).trans f5, inj ?_, inj ?_, fun h => f8 ?_, inj ?_, (rk_of_bMat hs₄).trans f10,
    inj ?_, inj ?_, fun h => f13 ?_, (rk_of_bMat ?_).trans f14, inj ?_, fun h => f16 ?_, inj ?_,
    inj ?_, inj ?_, fun i hi h => f20 i hi ?_,
    ⟨(rk_of_bMat ?_).trans f21, (rk_of_bMat ?_).trans f22, (rk_of_bMat ?_).trans f23,
      (rk_of_bMat ?_).trans f24, (rk_of_bMat ?_).trans f25, (rk_of_bMat ?_).trans f26,
      (rk_of_bMat ?_).trans f27⟩,
    inj ?_, fun h => f29 ?_, inj ?_, fun h => f31 ?_, inj ?_, inj ?_, inj ?_,
    fun i hi h => f35 i hi ?_,
    ⟨(rk_of_bMat hu₁).trans f36, (rk_of_bMat hu₂).trans f37, (rk_of_bMat ?_).trans f38,
      (rk_of_bMat ?_).trans f39⟩⟩
  · rw [map_mul, ha, hx]
  · rw [map_mul, ha, ht]
  · rw [map_mul, ht, hx]
  · rw [map_mul, map_one, hs₃]
    exact f4
  · rw [map_mul, map_mul, hs₃, hx]
    exact f6
  · rw [map_pow, map_mul, map_one, ht, hs₃]
    exact f7
  · have h' := congrArg bMat h
    rw [map_mul, map_one, ht, hs₃] at h'
    exact h'
  · rw [map_mul, map_one, hs₄]
    exact f9
  · rw [map_mul, map_mul, hs₄, hx]
    exact f11
  · rw [map_pow, map_mul, map_one, ht, hs₄]
    exact f12
  · have h' := congrArg bMat h
    rw [map_mul, map_mul, map_one, ht, hs₄] at h'
    rw [sq]
    exact h'
  · rw [map_mul, map_mul, ht, hs₄, sq]
  · rw [map_pow, map_one, hf]
    exact f15
  · rw [← hf, h, map_one]
  · rw [map_mul, map_mul, hf, hx]
    exact f17
  · rw [map_mul, map_mul, hf, ha]
    exact f18
  · rw [map_mul, map_mul, hf, ht]
    exact f19
  · rw [← hf, ← hx, h, map_pow]
  · rw [map_mul, ha, hf]
  · rw [map_mul, map_mul, ht, hx, hf]
  · rw [map_mul, map_mul, map_pow, ht, hx, hf]
  · rw [map_mul, map_mul, map_pow, ha, hx, hf]
  · rw [map_mul, map_mul, map_pow, ht, hx, hf]
  · rw [map_mul, map_mul, map_pow, ha, hx, hf]
  · rw [map_mul, map_mul, map_pow, ha, hx, hf]
  · rw [map_pow, map_one, hu₁]
    exact f28
  · rw [← hu₁, h, map_one]
  · rw [map_pow, map_one, hu₂]
    exact f30
  · rw [← hu₂, h, map_one]
  · rw [map_mul, map_mul, hu₁, hx]
    exact f32
  · rw [map_mul, map_mul, hu₂, hx]
    exact f33
  · rw [map_mul, map_mul, hu₁, hu₂]
    exact f34
  · rw [← hu₂, ← hu₁, h, map_pow]
  · rw [map_mul, hu₁, hu₂]
  · rw [map_mul, map_pow, hu₁, hu₂, sq]

theorem bMat_locals :
    bMat sThree = sm CFSG.KC.BM.SevenLocal.s3 ∧ bMat sFour = sm CFSG.KC.BM.SevenLocal.s4 ∧
      bMat fSeven = sm CFSG.KC.BM.SevenLocal.f ∧ bMat uOne = sm CFSG.KC.BM.SevenLocal.u1 ∧
      bMat uTwo = sm CFSG.KC.BM.SevenLocal.u2 := by
  obtain ⟨-, h3, h4, hf, h1, h2, -⟩ := Certificates.certificate17450
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h3, sThree, CFSG.KC.BM.SevenFacts.w3W]
    simp only [map_mul, map_pow, bMat_ySeven, bMat_tauOne, bMat_tauTwo, bMat_eSeven]
  · rw [h4, sFour, CFSG.KC.BM.SevenFacts.w4W]
    simp only [map_mul, map_pow, bMat_ySeven, bMat_tauTwo, bMat_eSeven]
  · rw [hf, fSeven, CFSG.KC.BM.SevenFacts.fW]
    simp only [map_mul, map_pow, bMat_ySeven, bMat_tauOne, bMat_tauTwo, bMat_eSeven]
  · rw [h1, uOne, CFSG.KC.BM.SevenFacts.v1W]
    simp only [map_mul, map_pow, bMat_ySeven, bMat_eSeven]
  · rw [h2, uTwo, CFSG.KC.BM.SevenFacts.v2W]
    simp only [map_mul, map_pow, bMat_ySeven, bMat_tauOne, bMat_tauTwo, bMat_eSeven]

theorem localParts_of_certificate :
    LocalParts alphaB xSeven tauOne sThree sFour fSeven uOne uTwo := by
  obtain ⟨h3, h4, hf, h1, h2⟩ := bMat_locals
  exact localParts_of bMat_alphaB bMat_xSeven bMat_tauOne h3 h4 hf h1 h2
    Certificates.certificate17450.2.2.2.2.2.2

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
