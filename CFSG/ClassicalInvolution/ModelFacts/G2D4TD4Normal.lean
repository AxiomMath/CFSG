module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Class

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
open scoped MatrixGroups

section Basic

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

theorem TK_mul_comm {x y : twistedGroup σ} (hx : x ∈ TK σ) (hy : y ∈ TK σ) : x * y = y * x := by
  obtain ⟨b, hb⟩ := hx
  obtain ⟨c, hc⟩ := hy
  apply twistedIncl_injective σ
  rw [map_mul, map_mul, hb, hc, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

include hσ in
theorem slLong_neg_one_mem_TK : slLong σ hσ (-1) ∈ TK σ :=
  ⟨aLongTD4 K, twistedIncl_slLong_neg_one hσ⟩

include hσ in
theorem slShort_neg_one_mem_TK : slShort σ hσ (-1) ∈ TK σ :=
  ⟨aShortTD4 K, twistedIncl_slShort_neg_one hσ⟩

theorem neg_one_mul_comm_SL2 {F : Type} [Field F] (A : SL(2, F)) : (-1 : SL(2, F)) * A =
    A * (-1) := by
  apply Subtype.ext
  simp

theorem neg_one_mul_neg_one_SL2 {F : Type} [Field F] : (-1 : SL(2, F)) * (-1) = 1 := by
  apply Subtype.ext
  simp

include hσ in
theorem SProd_le_centralizer {z : twistedGroup σ} (hz : z ∈ SProd σ hσ) :
    z * slLong σ hσ (-1) = slLong σ hσ (-1) * z := by
  obtain ⟨t, ht, A, B, rfl⟩ := hz
  have h1 : Commute t (slLong σ hσ (-1)) := TK_mul_comm ht (slLong_neg_one_mem_TK hσ)
  have h2 : Commute (slLong σ hσ A) (slLong σ hσ (-1)) := by
    show slLong σ hσ A * slLong σ hσ (-1) = slLong σ hσ (-1) * slLong σ hσ A
    rw [← map_mul, ← map_mul, ← neg_one_mul_comm_SL2]
  have h3 : Commute (slB σ hσ B) (slLong σ hσ (-1)) := by
    show slB σ hσ B * slLong σ hσ (-1) = slLong σ hσ (-1) * slB σ hσ B
    rw [← slB_neg_one hσ, ← map_mul, ← map_mul, ← neg_one_mul_comm_SL2]
  exact (h1.mul_left h2 |>.mul_left h3)

end Basic

section Inversion

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem slLong_WSL : slLong σ hσ WSL = nHat σ (ng 0) := by
  apply Subtype.ext
  rw [WSL_eq_td4]
  simp only [map_mul, Subgroup.coe_mul]
  rw [uSL_eq_sl2Upper, vSL_eq_sl2Lower, slLong_val, slLong_val, slLongE_upper, slLongE_lower,
    nHat_val, nHatE_zero_eq]
  simp

@[expose] def m0 (hσ : ∀ c, σ (σ (σ c)) = c) : twistedGroup σ :=
  slLong σ hσ WSL * slB σ hσ WSL

theorem weylElt_conj_rootDiagUnit_td4 (i : Fin d4.rank) (b : Fin d4.rank → Kˣ) :
    weylElt d4 K i 1 * rootDiagUnit d4 b * (weylElt d4 K i 1)⁻¹ =
      rootDiagUnit d4 (weylTuple (simple d4 i) b) := by
  have h := canonicalRep_conj_rootDiagUnit (K := K) (simple d4 i) b
  rwa [show canonicalRep (coxeterSystem d4) K (simple d4 i) = weylElt d4 K i 1 from
    canonicalRep_simple _ _ i] at h

theorem canonicalRep_inv_conj_rootDiagUnit (w : WeylGroup d4) (b : Fin d4.rank → Kˣ) :
    (canonicalRep (coxeterSystem d4) K w)⁻¹ * rootDiagUnit d4 b *
        canonicalRep (coxeterSystem d4) K w = rootDiagUnit d4 (weylTuple w⁻¹ b) := by
  have h := canonicalRep_conj_rootDiagUnit (K := K) w (weylTuple w⁻¹ b)
  rw [weylTuple_weylTuple, mul_inv_cancel, weylTuple_one] at h
  rw [← h]
  group

theorem weylTuple_tdW0 (b : Fin d4.rank → Kˣ) : weylTuple (tdWA * tdWB) b = b⁻¹ := by
  funext i
  show rootChar b ((tdWA * tdWB)⁻¹ • (Pi.single i 1 : Fin d4.rank → ℤ)) = (b i)⁻¹
  have h : (tdWA * tdWB)⁻¹ • (Pi.single i 1 : Fin d4.rank → ℤ) = -Pi.single i 1 := by
    have := tdW0_smul ((tdWA * tdWB)⁻¹ • (Pi.single i 1 : Fin d4.rank → ℤ))
    rw [smul_smul, mul_inv_cancel, one_smul] at this
    exact neg_eq_iff_eq_neg.mp this.symm
  rw [h, rootChar_neg_inv, rootChar_single_td4]

include hσ in
theorem m0_conj_rootDiagUnit (b : Fin d4.rank → Kˣ) :
    twistedIncl σ (m0 hσ) * rootDiagUnit d4 b * (twistedIncl σ (m0 hσ))⁻¹ =
      rootDiagUnit d4 (weylTuple (tdWA * tdWB) b) := by
  have e1 : twistedIncl σ (m0 hσ) = weylElt d4 K (nd 2) 1 *
      (canonicalRep (coxeterSystem d4) K tdNhat * (weylElt d4 K (nd 0) 1 * weylElt d4 K (nd 1) 1 *
        weylElt d4 K (nd 3) 1) * (canonicalRep (coxeterSystem d4) K tdNhat)⁻¹) := by
    rw [m0, map_mul, twistedIncl_slB_WSL hσ, slLong_WSL hσ]
    rfl
  set N := canonicalRep (coxeterSystem d4) K tdNhat with hN
  set d := rootDiagUnit d4 b with hd
  have e2 : weylElt d4 K (nd 2) 1 * (N * (weylElt d4 K (nd 0) 1 * weylElt d4 K (nd 1) 1 *
      weylElt d4 K (nd 3) 1) * N⁻¹) * d * (weylElt d4 K (nd 2) 1 *
        (N * (weylElt d4 K (nd 0) 1 * weylElt d4 K (nd 1) 1 * weylElt d4 K (nd 3) 1) * N⁻¹))⁻¹ =
      weylElt d4 K (nd 2) 1 * (N * (weylElt d4 K (nd 0) 1 * (weylElt d4 K (nd 1) 1 *
        (weylElt d4 K (nd 3) 1 * (N⁻¹ * d * N) * (weylElt d4 K (nd 3) 1)⁻¹) *
          (weylElt d4 K (nd 1) 1)⁻¹) * (weylElt d4 K (nd 0) 1)⁻¹) * N⁻¹) *
            (weylElt d4 K (nd 2) 1)⁻¹ := by
    group
  rw [e1, e2, hN, canonicalRep_inv_conj_rootDiagUnit, weylElt_conj_rootDiagUnit_td4,
    weylElt_conj_rootDiagUnit_td4, weylElt_conj_rootDiagUnit_td4, canonicalRep_conj_rootDiagUnit,
    weylElt_conj_rootDiagUnit_td4]
  congr 1
  simp only [weylTuple_weylTuple]
  congr 1

include hσ in
theorem m0_inverts_td4 {x : twistedGroup σ} (hx : x ∈ TK σ) : m0 hσ * x * (m0 hσ)⁻¹ = x⁻¹ := by
  obtain ⟨b, hb⟩ := hx
  apply twistedIncl_injective σ
  rw [map_mul, map_mul, map_inv, map_inv, hb, m0_conj_rootDiagUnit hσ, weylTuple_tdW0,
    rootDiagUnit_inv]

end Inversion

section Normal

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem exists_conj_to_torus_mul_td4 (hK : (-1 : Kˣ) ≠ 1) [Finite K] {z : twistedGroup σ}
    (hz : z ∈ SProd σ hσ) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzτ : z ≠ slLong σ hσ (-1)) :
    ∃ x ∈ SProd σ hσ, ∃ t ∈ TK σ, x * z * x⁻¹ = t * m0 hσ := by
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_neg_one_ne_one hK
  have h2F : (2 : fixedField σ) ≠ 0 := fun h => h2K (by
    have := congrArg (fixedField σ).subtype h
    rwa [map_ofNat, map_zero] at this)
  obtain ⟨x, hx, t, ht, h⟩ := exists_conj_to_torus_mul_abs (Φ₁ := slLong σ hσ) (Φ₂ := slB σ hσ)
    h2F h2K (slLong_injective hσ) (slB_injective hσ) (slLong_comm_slB hσ) (T := TK σ)
    (SP := SProd σ hσ)
    (fun t ht => by
      obtain ⟨b, hb⟩ := ht
      obtain ⟨s, -, hs⟩ := torus_conj_slLong hσ hb
      exact ⟨s, hs⟩)
    (fun t ht => by
      obtain ⟨b, hb⟩ := ht
      obtain ⟨s, -, hs⟩ := torus_conj_slB hσ hb
      exact ⟨s, hs⟩)
    (fun u => ⟨_, twistedIncl_slLong_HSL hσ u⟩) (fun u => ⟨_, twistedIncl_slB_HSL hσ u⟩)
    (fun g hg => by
      obtain ⟨t, ht, A, B, rfl⟩ := hg
      exact ⟨t, ht, A, B, rfl⟩)
    (fun R S => mul_mem (slLong_mem_SProd hσ R) (slB_mem_SProd hσ S))
    (fun z hz hz2 hc => involution_centralizing_slLong hσ hK hz hz2 hc)
    (fun z hz hz2 hc => involution_centralizing_slB hσ hK hz hz2 hc) hz hz2 hz1 hzτ
  exact ⟨x, hx, t, ht, h⟩

end Normal



end CFSG.ClassicalInvolution.G2D4Models
