module

public import CFSG.LieType.Ree.SuzukiOvoidAction
public import Certificates.Certificate9530

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sz32

open CFSG.Blueprint CFSG.LieType.Ree Matrix
open scoped LinearAlgebra.Projectivization

theorem onOmegaGen_of_mem {a : ℕ} {K : Type} [Field K] {y : Fin 4 → K} (hy : y ≠ 0)
    (h : Projectivization.mk K y hy ∈ suzukiOmega a K) : OnOmegaGen a y := by
  rcases mem_suzukiOmega_iff.1 h with h | ⟨u, v, h⟩
  · rw [suzukiInfty, Projectivization.mk_eq_mk_iff] at h
    obtain ⟨c, hc⟩ := h
    have h0 : y 0 = 0 := by simpa using (congrFun hc 0).symm
    have h1 : y 1 = 0 := by simpa using (congrFun hc 1).symm
    have h2 : y 2 = 0 := by simpa using (congrFun hc 2).symm
    have h3 : (c : K) = y 3 := by simpa [Units.smul_def] using congrFun hc 3
    left
    exact ⟨h0, h1, h2, by rw [← h3]; exact c.ne_zero⟩
  · rw [suzukiLine, Projectivization.mk_eq_mk_iff] at h
    obtain ⟨c, hc⟩ := h
    have h0 : (c : K) * y 0 = 1 := by simpa [Units.smul_def] using congrFun hc 0
    have h1 : (c : K) * y 1 = u := by simpa [Units.smul_def] using congrFun hc 1
    have h2 : (c : K) * y 2 = v := by simpa [Units.smul_def] using congrFun hc 2
    have h3 : (c : K) * y 3 = suzukiN a u v := by simpa [Units.smul_def] using congrFun hc 3
    right
    have hc0 : (c : K) ≠ 0 := c.ne_zero
    refine ⟨fun h => ?_, ?_⟩
    · rw [h, mul_zero] at h0
      exact zero_ne_one h0
    · have hL : (c : K) ^ (2 ^ (a + 1) + 2) * (y 3 * y 0 ^ (2 ^ (a + 1) + 1)) =
          ((c : K) * y 3) * ((c : K) * y 0) ^ (2 ^ (a + 1) + 1) := by ring
      have hR : (c : K) ^ (2 ^ (a + 1) + 2) * (y 1 ^ (2 ^ (a + 1) + 2) +
          y 1 * y 2 * y 0 ^ 2 ^ (a + 1) + y 2 ^ 2 ^ (a + 1) * y 0 ^ 2) =
          ((c : K) * y 1) ^ (2 ^ (a + 1) + 2) +
          ((c : K) * y 1) * ((c : K) * y 2) * ((c : K) * y 0) ^ 2 ^ (a + 1) +
          ((c : K) * y 2) ^ 2 ^ (a + 1) * ((c : K) * y 0) ^ 2 := by ring
      refine mul_left_cancel₀ (pow_ne_zero (2 ^ (a + 1) + 2) hc0) ?_
      rw [hL, hR, h0, h1, h2, h3]
      simp [suzukiN]

theorem mulVec_ne_zero {K : Type} [Field K] (g : GL (Fin 4) K) {x : Fin 4 → K} (hx : x ≠ 0) :
    (g : Matrix (Fin 4) (Fin 4) K) *ᵥ x ≠ 0 := by
  intro h
  apply hx
  have := congrArg (fun z => ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ z) h
  simpa [Matrix.mulVec_mulVec] using this

theorem onOmegaGen_mulVec_line {a : ℕ} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (g : suzukiGroup a K) (u v : K) :
    OnOmegaGen a
      (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ ![1, u, v, suzukiN a u v]) := by
  have hx : (![1, u, v, suzukiN a u v] : Fin 4 → K) ≠ 0 := fun h => by simpa using congrFun h 0
  have hy := mulVec_ne_zero (g : GL (Fin 4) K) hx
  have hmk : g • suzukiLine a K u v = Projectivization.mk K _ hy :=
    suzuki_smul_mk_eq a g hx hy 1 (by simp)
  have hmem := suzuki_smul_mem_suzukiOmega hK g (suzukiLine_mem_suzukiOmega a K u v)
  rw [hmk] at hmem
  exact onOmegaGen_of_mem hy hmem

theorem onOmegaGen_mulVec_infty {a : ℕ} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (g : suzukiGroup a K) :
    OnOmegaGen a (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ ![0, 0, 0, 1]) := by
  have hx : (![0, 0, 0, 1] : Fin 4 → K) ≠ 0 := fun h => by simpa using congrFun h 3
  have hy := mulVec_ne_zero (g : GL (Fin 4) K) hx
  have hmk : g • suzukiInfty K = Projectivization.mk K _ hy :=
    suzuki_smul_mk_eq a g hx hy 1 (by simp)
  have hmem := suzuki_smul_mem_suzukiOmega hK g (suzukiInfty_mem_suzukiOmega a K)
  rw [hmk] at hmem
  exact onOmegaGen_of_mem hy hmem

@[expose] def gm (h : suzukiGroup 2 F32) : Mat :=
  ((h : GL (Fin 4) F32) : Matrix (Fin 4) (Fin 4) F32)

theorem gm_mul (g h : suzukiGroup 2 F32) : gm (g * h) = gm g * gm h := rfl

theorem gm_one : gm (1 : suzukiGroup 2 F32) = 1 := rfl

theorem gm_pow (g : suzukiGroup 2 F32) (n : ℕ) : gm (g ^ n) = gm g ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, gm_mul, ih, pow_succ]

theorem gm_injective : Function.Injective gm := fun _ _ h => Subtype.ext (Units.ext h)

section Group


noncomputable def g0 : suzukiGroup 2 F32 := suzukiWElt 2 F32 * suzukiSElt 2 F32 0 omega

theorem gm_g0 : gm g0 = g0Mat := by
  show (((suzukiWElt 2 F32 : GL (Fin 4) F32) * (suzukiSElt 2 F32 0 omega : GL (Fin 4) F32) :
    GL (Fin 4) F32) : Matrix (Fin 4) (Fin 4) F32) = _
  rw [Units.val_mul]
  exact congrArg₂ (· * ·) (coe_suzukiWElt 2 F32) (coe_suzukiSElt 2 F32 0 omega)

theorem g0_pow_25 : g0 ^ 25 = 1 :=
  gm_injective (by rw [gm_pow, gm_g0, g0Mat_pow_25]; rfl)

theorem g0_pow_5_ne : g0 ^ 5 ≠ 1 := fun h =>
  g0Mat_pow_5_ne (by simpa [gm_pow, gm_g0, gm_one] using congrArg gm h)

theorem orderOf_g0 : orderOf g0 = 25 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  simpa using orderOf_eq_prime_pow (p := 5) (n := 1) (x := g0) (by simpa using g0_pow_5_ne)
    (by simpa using g0_pow_25)

theorem sz32_centralizer_t0 (h : suzukiGroup 2 F32)
    (hc : h * g0 ^ 5 = g0 ^ 5 * h) : ∃ k < 25, h = g0 ^ k := by
  have hK := F32.natCard_eq
  have hcomm : Commute (gm h) (g0Mat ^ 5) := by
    have := congrArg gm hc
    rw [gm_mul, gm_mul, gm_pow, gm_g0] at this
    exact this
  obtain ⟨k, hk, hkh⟩ := Certificates.certificate9530 (gm h) hcomm (det_suzukiGroup h)
    (fun u v => onOmegaGen_mulVec_line hK h u v) (onOmegaGen_mulVec_infty hK h)
  exact ⟨k, hk, gm_injective (by rw [gm_pow, gm_g0, hkh])⟩

theorem sz32_centralizer_le {t : suzukiGroup 2 F32}
    (ht : t ∈ Subgroup.zpowers g0) (ht1 : t ≠ 1) {h : suzukiGroup 2 F32}
    (hc : h * t = t * h) : h ∈ Subgroup.zpowers g0 := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  set k : ℕ := (m % 25).toNat with hk
  have hmk : g0 ^ m = g0 ^ k := by
    have h1 := zpow_mod_orderOf g0 m
    rw [orderOf_g0] at h1
    rw [← h1, ← zpow_natCast]
    congr 1
    rw [hk]
    have : 0 ≤ m % 25 := Int.emod_nonneg _ (by norm_num)
    omega
  have hk25 : k < 25 := by omega
  have hk0 : k ≠ 0 := by
    intro h0
    apply ht1
    rw [hmk, h0, pow_zero]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k * n % 25 = 5 := by
    have key : ∀ k : Fin 25, k ≠ 0 → ∃ n : Fin 25, k.val * n.val % 25 = 5 := by decide
    obtain ⟨n, hn⟩ := key ⟨k, hk25⟩ (fun h => hk0 (by simpa using congrArg Fin.val h))
    exact ⟨n.val, hn⟩
  have h5 : (g0 ^ m) ^ n = g0 ^ 5 := by
    rw [hmk, ← pow_mul, ← pow_mod_orderOf, orderOf_g0, hn]
  have hc' : h * g0 ^ 5 = g0 ^ 5 * h := by
    rw [← h5]
    exact ((Commute.pow_right (show Commute h (g0 ^ m) from hc) n)).eq
  obtain ⟨j, -, rfl⟩ := sz32_centralizer_t0 h hc'
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers g0) j

end Group

end CFSG.AGLEmbedding.KFactProofs.Sz32
