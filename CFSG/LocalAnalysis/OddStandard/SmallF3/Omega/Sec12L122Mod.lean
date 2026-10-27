module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Compl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

structure Sec122Mod (t : G) (V B Y W : Subgroup G) (φ s : (Fin 5 → ZMod 2) → G) : Prop where
  comm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v
  sq : ∀ v ∈ V, v * v = 1
  BV : B ≤ V
  perm : IsPermModuleVia IsEvenVec φ B Y (alternatingGroup (Fin 5))
  fB : ∀ v ∈ V, sec12f t v ∈ B
  fmul : ∀ v ∈ V, ∀ w ∈ V, sec12f t (v * w) = sec12f t v * sec12f t w
  fker : ∀ v ∈ V, sec12f t v = 1 ↔ v ∈ B
  sV : ∀ n, IsEvenVec n → s n ∈ V
  sadd : ∀ n m, IsEvenVec n → IsEvenVec m → s (n + m) = s n * s m
  sf : ∀ n, IsEvenVec n → sec12f t (s n) = φ n
  sY : ∀ y ∈ Y, ∀ σ : Equiv.Perm (Fin 5),
    (∀ v, IsEvenVec v → y * φ v * y⁻¹ = φ (permVec σ v)) →
      ∀ n, IsEvenVec n → y * s n * y⁻¹ = s (permVec σ n)
  hW : ∀ x, x ∈ W ↔ ∃ n, IsEvenVec n ∧ x = s n

variable {t : G} {V B Y W : Subgroup G} {φ s : (Fin 5 → ZMod 2) → G}

private theorem sec122_phi_zero (hM : Sec122Mod t V B Y W φ s) : φ 0 = 1 := by
  have hzero : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
  have h := hM.perm.1 0 0 hzero hzero
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

private theorem sec122_s_zero (hM : Sec122Mod t V B Y W φ s) : s 0 = 1 := by
  have hzero : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
  have h := hM.sadd 0 0 hzero hzero
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

private theorem sec122_phi_mem_B (hM : Sec122Mod t V B Y W φ s) {n : Fin 5 → ZMod 2}
    (hn : IsEvenVec n) : φ n ∈ B :=
  (hM.perm.2.2.1 (φ n)).mpr ⟨n, hn, rfl⟩

theorem sec122_t_conj (t v : G) : t * v * t⁻¹ = (sec12f t v)⁻¹ * v := by
  unfold sec12f
  group

theorem Sec122Mod.W_le_V (hM : Sec122Mod t V B Y W φ s) : W ≤ V := by
  intro x hx
  obtain ⟨n, hn, rfl⟩ := (hM.hW x).mp hx
  exact hM.sV n hn

theorem Sec122Mod.W_inf_B (hM : Sec122Mod t V B Y W φ s) : W ⊓ B = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hw, hb⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨n, hn, rfl⟩ := (hM.hW x).mp hw
  have hfx : sec12f t (s n) = 1 := (hM.fker (s n) (hM.sV n hn)).2 hb
  have hphin : φ n = 1 := by rw [← hM.sf n hn, hfx]
  have hn0 : n = 0 :=
    hM.perm.2.1 n 0 hn (by simp [IsEvenVec])
      (by rw [hphin, sec122_phi_zero hM])
  rw [hn0]
  exact sec122_s_zero hM

theorem Sec122Mod.V_eq_mul (hM : Sec122Mod t V B Y W φ s) :
    ∀ v ∈ V, ∃ w ∈ W, ∃ b ∈ B, v = w * b := by
  intro v hv
  obtain ⟨m, hm, hφm⟩ := (hM.perm.2.2.1 (sec12f t v)).mp (hM.fB v hv)
  have hsmV : s m ∈ V := hM.sV m hm
  have hbV : s m * v ∈ V := V.mul_mem hsmV hv
  have hfb : sec12f t (s m * v) = 1 := by
    rw [hM.fmul (s m) hsmV v hv, hM.sf m hm, hφm]
    exact hM.sq (sec12f t v) (hM.BV (hM.fB v hv))
  have hbB : s m * v ∈ B := (hM.fker (s m * v) hbV).mp hfb
  refine ⟨(s m)⁻¹, W.inv_mem ((hM.hW (s m)).mpr ⟨m, hm, rfl⟩), s m * v, hbB, ?_⟩
  group

theorem Sec122Mod.W_inv (hM : Sec122Mod t V B Y W φ s) :
    ∀ y ∈ Y, ∀ w ∈ W, y * w * y⁻¹ ∈ W :=
  sec122_W_inv hM.perm hM.sY hM.hW

theorem Sec122Mod.tb_conj (hM : Sec122Mod t V B Y W φ s) {b₀ : G} (hb₀ : b₀ ∈ B)
    {n : Fin 5 → ZMod 2} (hn : IsEvenVec n) :
    (t * b₀) * s n * (t * b₀)⁻¹ = s n * φ n := by
  have hbV : b₀ ∈ V := hM.BV hb₀
  have hsnV : s n ∈ V := hM.sV n hn
  have hφnV : φ n ∈ V := hM.BV (sec122_phi_mem_B hM hn)
  have hcomm : b₀ * s n * b₀⁻¹ = s n := by
    calc b₀ * s n * b₀⁻¹ = s n * b₀ * b₀⁻¹ := by rw [hM.comm b₀ hbV (s n) hsnV]
      _ = s n * (b₀ * b₀⁻¹) := by rw [mul_assoc]
      _ = s n := by rw [mul_inv_cancel, mul_one]
  calc (t * b₀) * s n * (t * b₀)⁻¹
      = t * (b₀ * s n * b₀⁻¹) * t⁻¹ := by group
    _ = t * s n * t⁻¹ := by rw [hcomm]
    _ = (sec12f t (s n))⁻¹ * s n := sec122_t_conj t (s n)
    _ = (φ n)⁻¹ * s n := by rw [hM.sf n hn]
    _ = φ n * s n := by rw [inv_eq_of_mul_eq_one_right (hM.sq (φ n) hφnV)]
    _ = s n * φ n := hM.comm (φ n) hφnV (s n) hsnV

theorem Sec122Mod.tb_not_mem_normalizer (hM : Sec122Mod t V B Y W φ s) {b₀ : G} (hb₀ : b₀ ∈ B) :
    t * b₀ ∉ normalizer (W : Set G) := by
  intro hmem
  have hg : ∀ h, h ∈ (W : Set G) ↔ (t * b₀) * h * (t * b₀)⁻¹ ∈ (W : Set G) :=
    Subgroup.mem_set_normalizer_iff.mp hmem
  have hn : IsEvenVec (wvec 0) := wvec_even 0
  have hsnW : s (wvec 0) ∈ W := (hM.hW (s (wvec 0))).mpr ⟨wvec 0, hn, rfl⟩
  have hconjW : (t * b₀) * s (wvec 0) * (t * b₀)⁻¹ ∈ W := (hg (s (wvec 0))).mp hsnW
  rw [Sec122Mod.tb_conj hM hb₀ hn] at hconjW
  have hφW : φ (wvec 0) ∈ W := by
    have h2 : (s (wvec 0))⁻¹ * (s (wvec 0) * φ (wvec 0)) ∈ W :=
      W.mul_mem (W.inv_mem hsnW) hconjW
    rwa [inv_mul_cancel_left] at h2
  have hφbot : φ (wvec 0) ∈ (⊥ : Subgroup G) := by
    rw [← Sec122Mod.W_inf_B hM]
    exact ⟨hφW, sec122_phi_mem_B hM hn⟩
  have hφ1 : φ (wvec 0) = 1 := by simpa using hφbot
  have hw0 : wvec 0 = 0 :=
    hM.perm.2.1 (wvec 0) 0 hn (by simp [IsEvenVec])
      (by rw [hφ1, sec122_phi_zero hM])
  have hne : wvec 0 (1 : Fin 5) ≠ 0 := by simp [wvec]
  exact hne (congrFun hw0 1)

end CFSG.OddStandard.SmallF3.Omega
