module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JG

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open

private lemma sec12J_delta_map_mul {W : Type*} [Group W] (hcomm : ∀ a b : W, a * b = b * a)
    (f : W →* W) (a b : W) :
    f (a * b) * (a * b)⁻¹ = f a * a⁻¹ * (f b * b⁻¹) := by
  rw [map_mul, mul_inv_rev]
  simp only [mul_assoc]
  rw [← mul_assoc (f b) b⁻¹ a⁻¹, hcomm (f b * b⁻¹) a⁻¹]

private lemma sec12J_delta_conj {W : Type*} [Group W] (f g : W →* W)
    (hfg : ∀ w, f (g w) = g (f w)) (w : W) :
    g (f w) * (f w)⁻¹ = f (g w * w⁻¹) := by
  rw [map_mul, map_inv, hfg w]

private lemma sec12J_fixed_ne_top {W Γ : Type*} [Group W] [Group Γ] {ψ : Γ →* MulAut W}
    {y : Γ} (hψ : Function.Injective ψ) (hy1 : y ≠ 1) {C : Subgroup W}
    (hCmem : ∀ w, w ∈ C ↔ ψ y w = w) : C ≠ ⊤ := by
  intro htop
  apply hy1
  apply hψ
  have h1 : ψ y = 1 := by
    apply MulEquiv.ext
    intro w
    have hw : w ∈ C := by simp [htop]
    simpa using (hCmem w).mp hw
  rw [h1, map_one]

private lemma sec12J_comm_of_index_two {W Γ : Type} [Group W] [Finite W] [Group Γ]
    {ψ : Γ →* MulAut W} {φ : Sec12SL × Sec12SL →* Γ} (hS : Sec12Act ψ φ)
    (hE : (MonoidHom.range φ).Normal) {y : Γ} (hy2 : y * y = 1)
    {C : Subgroup W} (hCmem : ∀ w, w ∈ C ↔ ψ y w = w) (hCidx : C.index = 2)
    {x : Γ} (hx : x ∈ MonoidHom.range φ) : x * y = y * x := by
  have hC'idx : (C.map ((ψ x).toMonoidHom)).index = 2 := by
    rw [Subgroup.index_map_of_bijective (ψ x).bijective C, hCidx]
  have hindex : (C ⊓ C.map ((ψ x).toMonoidHom)).index ≤ 4 := by
    calc (C ⊓ C.map ((ψ x).toMonoidHom)).index
        ≤ C.index * (C.map ((ψ x).toMonoidHom)).index := Subgroup.index_inf_le
      _ = 4 := by rw [hCidx, hC'idx]
  have hcard64 : 64 ≤ Nat.card (C ⊓ C.map ((ψ x).toMonoidHom) : Subgroup W) := by
    have h1 : 256 ≤ Nat.card (C ⊓ C.map ((ψ x).toMonoidHom) : Subgroup W) * 4 := by
      calc 256 = Nat.card W := hS.card.symm
        _ = Nat.card (C ⊓ C.map ((ψ x).toMonoidHom) : Subgroup W) *
              (C ⊓ C.map ((ψ x).toMonoidHom)).index := (Subgroup.card_mul_index _).symm
        _ ≤ Nat.card (C ⊓ C.map ((ψ x).toMonoidHom) : Subgroup W) * 4 :=
              Nat.mul_le_mul_left _ hindex
    have h2 : 4 * 64 ≤ 4 * Nat.card (C ⊓ C.map ((ψ x).toMonoidHom) : Subgroup W) := by
      calc 4 * 64 = 256 := by norm_num
        _ ≤ Nat.card (C ⊓ C.map ((ψ x).toMonoidHom) : Subgroup W) * 4 := h1
        _ = 4 * Nat.card (C ⊓ C.map ((ψ x).toMonoidHom) : Subgroup W) := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  let C' : Subgroup W := C.map ((ψ x).toMonoidHom)
  have hzmem : x * y * x⁻¹ * y⁻¹ ∈ MonoidHom.range φ := by
    have hxinv : x⁻¹ ∈ MonoidHom.range φ := Subgroup.inv_mem _ hx
    have hconj : y * x⁻¹ * y⁻¹ ∈ MonoidHom.range φ := hE.conj_mem (x⁻¹) hxinv y
    have hprod : x * (y * x⁻¹ * y⁻¹) ∈ MonoidHom.range φ :=
      Subgroup.mul_mem _ hx hconj
    simpa [mul_assoc] using hprod
  obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp hzmem
  have hfixed : ∀ w, w ∈ C ⊓ C' → ψ (x * y * x⁻¹ * y⁻¹) w = w := by
    intro w hw
    have hwC : ψ y w = w := (hCmem w).mp hw.1
    obtain ⟨c, hcC, hcx⟩ := Subgroup.mem_map.mp hw.2
    have hc : ψ y c = c := (hCmem c).mp hcC
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    have hxinvw : ψ x⁻¹ w = c := by
      rw [← hcx]
      calc ψ x⁻¹ (ψ x c) = (ψ x⁻¹ * ψ x) c := rfl
        _ = (ψ (x⁻¹ * x)) c := by rw [← map_mul]
        _ = (ψ 1) c := by rw [inv_mul_cancel]
        _ = c := by rw [map_one, MulAut.one_apply]
    have h1 : ψ (x * y * x⁻¹ * y⁻¹) w = ψ x (ψ y (ψ x⁻¹ (ψ y⁻¹ w))) := by
      simp only [map_mul, MulAut.mul_apply]
    calc ψ (x * y * x⁻¹ * y⁻¹) w
        = ψ x (ψ y (ψ x⁻¹ (ψ y⁻¹ w))) := h1
      _ = ψ x (ψ y (ψ x⁻¹ (ψ y w))) := by rw [hyinv]
      _ = ψ x (ψ y (ψ x⁻¹ w)) := by rw [hwC]
      _ = ψ x (ψ y c) := by rw [hxinvw]
      _ = ψ x c := by rw [hc]
      _ = w := hcx
  have hle : Nat.card (C ⊓ C' : Subgroup W) ≤
      Nat.card {w : W // ψ (x * y * x⁻¹ * y⁻¹) w = w} :=
    sec12J_card_subtype_le (P := fun w => w ∈ C ⊓ C')
      (Q := fun w => ψ (x * y * x⁻¹ * y⁻¹) w = w) hfixed
  have h64fixed : 64 ≤ Nat.card {w : W // ψ (x * y * x⁻¹ * y⁻¹) w = w} :=
    hcard64.trans hle
  by_cases hq1 : q = 1
  · have hz1 : x * y * x⁻¹ * y⁻¹ = 1 := by
      rw [← hq, hq1, map_one]
    have h1 : x * y * x⁻¹ = y := mul_inv_eq_one.mp hz1
    exact mul_inv_eq_iff_eq_mul.mp h1
  · exfalso
    have h16 : Nat.card {w : W // ψ (x * y * x⁻¹ * y⁻¹) w = w} ≤ 16 := by
      have h := hS.fix1 q hq1
      rwa [hq] at h
    omega

theorem sec12J_transvection {W Γ : Type} [Group W] [Finite W] [Group Γ] {ψ : Γ →* MulAut W}
    {φ : Sec12SL × Sec12SL →* Γ} (hS : Sec12Act ψ φ) (hψ : Function.Injective ψ)
    (hE : (MonoidHom.range φ).Normal) {y : Γ} (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    Nat.card {w : W // ψ y w = w} ≤ 64 := by
  classical
  let C : Subgroup W :=
    { carrier := {w | ψ y w = w}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      one_mem' := by
        simp only [Set.mem_setOf_eq, map_one, MulAut.one_apply]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv, ha] }
  have hCmem : ∀ w, w ∈ C ↔ ψ y w = w := fun w => Iff.rfl
  by_contra hle0
  push Not at hle0
  have hleC : 64 < Nat.card C := hle0
  have hCne : C ≠ ⊤ := sec12J_fixed_ne_top hψ hy1 hCmem
  obtain ⟨w0, hw0⟩ : ∃ w : W, w ∉ C := by
    by_contra h
    push Not at h
    exact hCne (Subgroup.ext fun w => ⟨fun _ => by simp, fun _ => h w⟩)
  have hdvd : Nat.card C ∣ 256 := by
    rw [← hS.card]
    exact ⟨C.index, (Subgroup.card_mul_index C).symm⟩
  have hdvd' : Nat.card C ∣ 2 ^ 8 := by
    norm_num
    exact hdvd
  obtain ⟨k, hk8, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
  have hk6 : 6 < k := by
    by_contra h
    push Not at h
    have h1 : 2 ^ k ≤ 2 ^ 6 := pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) h
    rw [hk] at hleC
    norm_num at h1 hleC
    omega
  interval_cases k
  · have hk7 : Nat.card C = 128 := by
      norm_num at hk ⊢
      exact hk
    have hCidx : C.index = 2 := by
      have h := Subgroup.card_mul_index C
      rw [hk7, hS.card] at h
      omega
    have hcomm_range : ∀ x ∈ MonoidHom.range φ, x * y = y * x :=
      fun x hx => sec12J_comm_of_index_two hS hE hy2 hCmem hCidx hx
    let δ : W →* W := MonoidHom.mk' (fun w => ψ y w * w⁻¹)
      (sec12J_delta_map_mul hS.comm (ψ y).toMonoidHom)
    have hδ : ∀ w, δ w = ψ y w * w⁻¹ := fun w => rfl
    have hδone : ∀ w, δ w = 1 ↔ w ∈ C := by
      intro w
      rw [hδ, hCmem w]
      exact mul_inv_eq_one
    have hδconj : ∀ (x : Γ), x * y = y * x → ∀ w, δ (ψ x w) = ψ x (δ w) := by
      intro x hxy w
      have hfg : ∀ v, ψ x (ψ y v) = ψ y (ψ x v) := by
        intro v
        have := congrArg (fun f : MulAut W => f v)
          (show ψ x * ψ y = ψ y * ψ x by rw [← map_mul, hxy, map_mul])
        simpa using this
      rw [hδ, hδ]
      exact sec12J_delta_conj (ψ x).toMonoidHom (ψ y).toMonoidHom hfg w
    have hv0ne : δ w0 ≠ 1 := fun h => hw0 ((hδone w0).mp h)
    have hfixv : ∀ x ∈ MonoidHom.range φ, ψ x (δ w0) = δ w0 := by
      intro x hx
      have hxy := hcomm_range x hx
      have hnot : ψ x w0 ∉ C := by
        intro hin
        have h1 : δ (ψ x w0) = 1 := (hδone _).mpr hin
        have h2 : ψ x (δ w0) = 1 := by
          rw [← hδconj x hxy w0]
          exact h1
        have h3 : δ w0 = 1 := by
          have := congrArg (fun v => ψ x⁻¹ v) h2
          simpa using this
        exact hv0ne h3
      have hprod : w0⁻¹ * ψ x w0 ∈ C := by
        rw [mul_mem_iff_of_index_two hCidx]
        have hw0inv : w0⁻¹ ∉ C := fun h => hw0 (by simpa using C.inv_mem h)
        exact ⟨fun h => (hw0inv h).elim, fun h => (hnot h).elim⟩
      have h1 : δ (w0⁻¹ * ψ x w0) = 1 := (hδone _).mpr hprod
      have h2 : (δ w0)⁻¹ * δ (ψ x w0) = 1 := by
        simpa using h1
      rw [hδconj x hxy w0] at h2
      exact (inv_mul_eq_one.mp h2).symm
    have hU : ψ (φ (sec12U, 1)) (δ w0) = δ w0 :=
      hfixv (φ (sec12U, 1)) (MonoidHom.mem_range.mpr ⟨(sec12U, 1), rfl⟩)
    have hL : ψ (φ (sec12Lo, 1)) (δ w0) = δ w0 :=
      hfixv (φ (sec12Lo, 1)) (MonoidHom.mem_range.mpr ⟨(sec12Lo, 1), rfl⟩)
    exact hv0ne (hS.gen (δ w0) hU hL)
  · exfalso
    have hk8' : Nat.card C = 256 := by
      norm_num at hk ⊢
      exact hk
    have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C (by rw [hk8', hS.card])
    exact hCne htop

end CFSG.OddStandard.SmallF3.Omega
