module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1ElemA
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Tau

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B K : Subgroup G}

theorem sec8t84a1_E_sq_const (h8B : Asc82Lemma8B) (hK : Sec8T84A1Pre G t L S z g B K)
    (hH : ∀ b ∈ B, b ≠ 1 → ∀ b' ∈ B, b' ≠ 1 → ∃ h ∈ Hsub8 t B K, h * b * h⁻¹ = b')
    {x₀ : G} (hx₀ : x₀ ∈ K) (hx₀B : x₀ * x₀ ∉ B) {x : G} (hx : x ∈ K)
    (hxA : x ∉ Asub8 t B) : ∃ b ∈ B, x * x = t * b := by
  have hx₀A : x₀ ∉ Asub8 t B := by
    intro h
    exact hx₀B (by rw [sec8t84a1_A_sq hK.ctx h]; exact B.one_mem)
  obtain hmem | ⟨b₀, hb₀B, hb₀eq⟩ :=
    sec8t84a1_mem_A hK.ctx (sec8t84a1_E_sq_A h8B hK hx₀)
  · exact absurd hmem hx₀B
  have hv₀B : x₀ * t * x₀⁻¹ * t⁻¹ ∈ B := sec8t84a1_E_comm_t h8B hK hx₀
  have hv₀ne : x₀ * t * x₀⁻¹ * t⁻¹ ≠ 1 := by
    intro h
    exact hx₀A ((sec8t84a1_E_mem_A_iff hK hx₀).mpr h)
  have hvB : x * t * x⁻¹ * t⁻¹ ∈ B := sec8t84a1_E_comm_t h8B hK hx
  have hvne : x * t * x⁻¹ * t⁻¹ ≠ 1 := by
    intro h
    exact hxA ((sec8t84a1_E_mem_A_iff hK hx).mpr h)
  obtain ⟨h, hhH, hconj⟩ :=
    hH (x₀ * t * x₀⁻¹ * t⁻¹) hv₀B hv₀ne (x * t * x⁻¹ * t⁻¹) hvB hvne
  obtain ⟨hhN, hhK, hht⟩ :=
    (sec8t84a1_mem_H (t := t) (B := B) (K := K)).mp hhH
  have hhNnorm : h ∈ normalizer (B : Set G) := sec8t84a1_N_le_normalizer h8B hK.ctx hhN
  set y : G := h * x₀ * h⁻¹ with hydef
  have hyK : y ∈ K := (hhK x₀).mp hx₀
  have hb₂B : h * b₀ * h⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hhNnorm b₀).mp hb₀B
  have hyy : y * y = t * (h * b₀ * h⁻¹) := by
    have h1 : y * y = h * (x₀ * x₀) * h⁻¹ := by rw [hydef]; group
    rw [h1, hb₀eq]
    have hht' : h * t * h⁻¹ = t := by rw [hht]; group
    calc h * (t * b₀) * h⁻¹ = (h * t * h⁻¹) * (h * b₀ * h⁻¹) := by group
      _ = t * (h * b₀ * h⁻¹) := by rw [hht']
  have hyt : y * t * y⁻¹ * t⁻¹ = x * t * x⁻¹ * t⁻¹ := by
    have h2 := sec8t84a1_tau_conj (h := h) (c := x₀) hht
    rw [hydef]
    rw [h2, hconj]
  set a : G := x⁻¹ * y with hadef
  have haK : a ∈ K := K.mul_mem (K.inv_mem hx) hyK
  have hxinv_t : x⁻¹ * t * (x⁻¹)⁻¹ * t⁻¹ = (x * t * x⁻¹ * t⁻¹)⁻¹ := by
    have h := sec8t84a1_E_tau_mul h8B hK hx (K.inv_mem hx)
    have h1 : (x * x⁻¹) * t * (x * x⁻¹)⁻¹ * t⁻¹ = 1 := by group
    rw [h1] at h
    calc x⁻¹ * t * (x⁻¹)⁻¹ * t⁻¹
        = ((x * t * x⁻¹ * t⁻¹)⁻¹ * (x * t * x⁻¹ * t⁻¹)) *
            (x⁻¹ * t * (x⁻¹)⁻¹ * t⁻¹) := by group
      _ = (x * t * x⁻¹ * t⁻¹)⁻¹ *
            ((x * t * x⁻¹ * t⁻¹) * (x⁻¹ * t * (x⁻¹)⁻¹ * t⁻¹)) := by group
      _ = (x * t * x⁻¹ * t⁻¹)⁻¹ := by rw [← h]; group
  have hat : a * t * a⁻¹ * t⁻¹ = 1 := by
    have h := sec8t84a1_E_tau_mul h8B hK (K.inv_mem hx) hyK
    rw [hadef]
    rw [h, hxinv_t, hyt]
    group
  have haA : a ∈ Asub8 t B := (sec8t84a1_E_mem_A_iff hK haK).mpr hat
  have hb₁B : x⁻¹ * a * x * a⁻¹ ∈ B := by
    simpa using sec8t84a1_E_comm_A h8B hK (K.inv_mem hx) haA
  have hya : y = x * a := by rw [hadef]; group
  have hyy2 : y * y = (x * x) * (x⁻¹ * a * x * a⁻¹) := by
    rw [hya]
    calc (x * a) * (x * a) = x * (a * x) * a := by group
      _ = x * (x * (x⁻¹ * a * x * a⁻¹) * a) * a := by
            rw [show a * x = x * (x⁻¹ * a * x * a⁻¹) * a from by group]
      _ = (x * x) * (x⁻¹ * a * x * a⁻¹) * (a * a) := by group
      _ = (x * x) * (x⁻¹ * a * x * a⁻¹) := by
            rw [sec8t84a1_A_sq hK.ctx haA, mul_one]
  refine ⟨(h * b₀ * h⁻¹) * (x⁻¹ * a * x * a⁻¹)⁻¹,
    B.mul_mem hb₂B (B.inv_mem hb₁B), ?_⟩
  have hxx : x * x = (y * y) * (x⁻¹ * a * x * a⁻¹)⁻¹ := by
    rw [hyy2]; group
  rw [hxx, hyy]
  group

theorem sec8t84a1_E_pair (h8B : Asc82Lemma8B) (hK : Sec8T84A1Pre G t L S z g B K)
    (hsq : ∀ x ∈ K, x ∉ Asub8 t B → ∃ b ∈ B, x * x = t * b) {x y : G} (hx : x ∈ K)
    (hy : y ∈ K) (hxA : x ∉ Asub8 t B) (hyA : y ∉ Asub8 t B) (hxyA : x * y ∉ Asub8 t B) :
    ∃ b ∈ B, x * y * x⁻¹ * y⁻¹ = t * b := by
  have hcK : x * y * x⁻¹ * y⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (K.inv_mem hy)
  have hc_invK : (x * y * x⁻¹ * y⁻¹)⁻¹ ∈ K := K.inv_mem hcK
  obtain ⟨b₂, hb₂B, hxy2⟩ := hsq (x * y) (K.mul_mem hx hy) hxyA
  obtain ⟨b₃, hb₃B, hx2⟩ := hsq x hx hxA
  obtain ⟨b₄, hb₄B, hy2⟩ := hsq y hy hyA
  obtain ⟨b₁, hb₁B, hsqmul⟩ := sec8t84a1_E_sq_mul h8B hK hx hy
  have hxy_sq : (t * b₃) * (t * b₄) = b₃ * b₄ := by
    calc (t * b₃) * (t * b₄) = b₃ * (t * t) * b₄ := by
          rw [sec8t84a1_t_comm hK.ctx hb₃B]; group
      _ = b₃ * b₄ := by rw [sec8t84a1_t_sq hK.ctx]; group
  have heq : t * b₂ = b₁ * (x * y * x⁻¹ * y⁻¹)⁻¹ * ((t * b₃) * (t * b₄)) := by
    rw [← hxy2, hsqmul, hx2, hy2]
    group
  have heq2 : t * b₂ = b₁ * (x * y * x⁻¹ * y⁻¹)⁻¹ * (b₃ * b₄) := by
    rw [heq, hxy_sq]
  have hcent_b₁ : b₁ * (x * y * x⁻¹ * y⁻¹)⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ * b₁ :=
    Subgroup.mem_centralizer_iff.mp (hK.le_C hc_invK).2 b₁ hb₁B
  have hcf : t * b₂ = (x * y * x⁻¹ * y⁻¹)⁻¹ * (b₁ * (b₃ * b₄)) := by
    rw [heq2]
    calc b₁ * (x * y * x⁻¹ * y⁻¹)⁻¹ * (b₃ * b₄)
        = (b₁ * (x * y * x⁻¹ * y⁻¹)⁻¹) * (b₃ * b₄) := by group
      _ = ((x * y * x⁻¹ * y⁻¹)⁻¹ * b₁) * (b₃ * b₄) := by rw [hcent_b₁]
      _ = (x * y * x⁻¹ * y⁻¹)⁻¹ * (b₁ * (b₃ * b₄)) := by group
  set f : G := b₁ * (b₃ * b₄) with hfdef
  have hfB : f ∈ B := B.mul_mem hb₁B (B.mul_mem hb₃B hb₄B)
  have hc_inv_eq : (x * y * x⁻¹ * y⁻¹)⁻¹ = (t * b₂) * f⁻¹ := by
    rw [hcf]
    group
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (sec8t84a1_t_sq hK.ctx)
  have hc_inv2 : (x * y * x⁻¹ * y⁻¹)⁻¹ = (b₂ * f⁻¹) * t := by
    calc (x * y * x⁻¹ * y⁻¹)⁻¹ = (t * b₂) * f⁻¹ := hc_inv_eq
      _ = (b₂ * t) * f⁻¹ := by rw [sec8t84a1_t_comm hK.ctx hb₂B]
      _ = b₂ * (t * f⁻¹) := by group
      _ = b₂ * (f⁻¹ * t) := by rw [sec8t84a1_t_comm hK.ctx (B.inv_mem hfB)]
      _ = (b₂ * f⁻¹) * t := by group
  have hc_eq : x * y * x⁻¹ * y⁻¹ = t * (b₂ * f⁻¹)⁻¹ := by
    calc x * y * x⁻¹ * y⁻¹ = ((x * y * x⁻¹ * y⁻¹)⁻¹)⁻¹ := by group
      _ = ((b₂ * f⁻¹) * t)⁻¹ := by rw [hc_inv2]
      _ = t⁻¹ * (b₂ * f⁻¹)⁻¹ := by rw [mul_inv_rev]
      _ = t * (b₂ * f⁻¹)⁻¹ := by rw [htinv]
  exact ⟨(b₂ * f⁻¹)⁻¹, B.inv_mem (B.mul_mem hb₂B (B.inv_mem hfB)), hc_eq⟩

theorem sec8t84a1_elem (h8B : Asc82Lemma8B) (hK : Sec8T84A1Pre G t L S z g B K)
    (hH : ∀ b ∈ B, b ≠ 1 → ∀ b' ∈ B, b' ≠ 1 → ∃ h ∈ Hsub8 t B K, h * b * h⁻¹ = b') :
    (∀ k ∈ K, ∀ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∈ B) ∧ ∀ k ∈ K, k * k ∈ B := by
  have hsq_mem : ∀ k ∈ K, k * k ∈ B := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x₀, hx₀K, hx₀B⟩ := hcon
    have hsq : ∀ x ∈ K, x ∉ Asub8 t B → ∃ b ∈ B, x * x = t * b :=
      fun x hx hxA => sec8t84a1_E_sq_const (x := x) h8B hK hH hx₀K hx₀B hx hxA
    obtain ⟨v₁, hv₁B, v₂, hv₂B, v₃, hv₃B, hv₁, hv₂, hv₃, hv₁₂, hv₁₃, hv₂₃, hv₁₂₃⟩ :=
      sec8t84a1_E_indep hK.ctx
    obtain ⟨x₁, hx₁K, hx₁t⟩ := hK.tau v₁ hv₁B
    obtain ⟨x₂, hx₂K, hx₂t⟩ := hK.tau v₂ hv₂B
    obtain ⟨x₃, hx₃K, hx₃t⟩ := hK.tau v₃ hv₃B
    have hnotA : ∀ {z : G}, z ∈ K → z * t * z⁻¹ * t⁻¹ ≠ 1 → z ∉ Asub8 t B :=
      fun hz hne hzA => hne ((sec8t84a1_E_mem_A_iff hK hz).mp hzA)
    have hx₁A : x₁ ∉ Asub8 t B := hnotA hx₁K (by rw [hx₁t]; exact hv₁)
    have hx₂A : x₂ ∉ Asub8 t B := hnotA hx₂K (by rw [hx₂t]; exact hv₂)
    have hx₃A : x₃ ∉ Asub8 t B := hnotA hx₃K (by rw [hx₃t]; exact hv₃)
    have hv₁₂ne : v₁ * v₂ ≠ 1 := by
      intro h
      apply hv₁₂
      have hv₂inv : v₂⁻¹ = v₂ := inv_eq_of_mul_eq_one_right (sec8t84a1_B_sq hK.ctx hv₂B)
      calc v₁ = (v₁ * v₂) * v₂⁻¹ := by group
        _ = 1 * v₂⁻¹ := by rw [h]
        _ = v₂ := by rw [one_mul, hv₂inv]
    have hv₁₃ne : v₁ * v₃ ≠ 1 := by
      intro h
      apply hv₁₃
      have hv₃inv : v₃⁻¹ = v₃ := inv_eq_of_mul_eq_one_right (sec8t84a1_B_sq hK.ctx hv₃B)
      calc v₁ = (v₁ * v₃) * v₃⁻¹ := by group
        _ = 1 * v₃⁻¹ := by rw [h]
        _ = v₃ := by rw [one_mul, hv₃inv]
    have hv₂₃ne : v₂ * v₃ ≠ 1 := by
      intro h
      apply hv₂₃
      have hv₃inv : v₃⁻¹ = v₃ := inv_eq_of_mul_eq_one_right (sec8t84a1_B_sq hK.ctx hv₃B)
      calc v₂ = (v₂ * v₃) * v₃⁻¹ := by group
        _ = 1 * v₃⁻¹ := by rw [h]
        _ = v₃ := by rw [one_mul, hv₃inv]
    have hv₁₂₃ne : v₁ * v₂ * v₃ ≠ 1 := by
      intro h
      apply hv₁₂₃
      have hsqv : (v₁ * v₂) * (v₁ * v₂) = 1 :=
        sec8t84a1_B_sq hK.ctx (B.mul_mem hv₁B hv₂B)
      have hinv : (v₁ * v₂)⁻¹ = v₁ * v₂ := inv_eq_of_mul_eq_one_right hsqv
      calc v₃ = (v₁ * v₂)⁻¹ * ((v₁ * v₂) * v₃) := by group
        _ = (v₁ * v₂)⁻¹ * 1 := by rw [h]
        _ = v₁ * v₂ := by rw [mul_one, hinv]
    have hx₁₂t : (x₁ * x₂) * t * (x₁ * x₂)⁻¹ * t⁻¹ = v₁ * v₂ := by
      rw [sec8t84a1_E_tau_mul h8B hK hx₁K hx₂K, hx₁t, hx₂t]
    have hx₁₃t : (x₁ * x₃) * t * (x₁ * x₃)⁻¹ * t⁻¹ = v₁ * v₃ := by
      rw [sec8t84a1_E_tau_mul h8B hK hx₁K hx₃K, hx₁t, hx₃t]
    have hx₂₃t : (x₂ * x₃) * t * (x₂ * x₃)⁻¹ * t⁻¹ = v₂ * v₃ := by
      rw [sec8t84a1_E_tau_mul h8B hK hx₂K hx₃K, hx₂t, hx₃t]
    have hx₁₂₃t : (x₁ * (x₂ * x₃)) * t * (x₁ * (x₂ * x₃))⁻¹ * t⁻¹ = v₁ * v₂ * v₃ := by
      rw [sec8t84a1_E_tau_mul h8B hK hx₁K (K.mul_mem hx₂K hx₃K), hx₁t, hx₂₃t]
      group
    have hx₁₂A : x₁ * x₂ ∉ Asub8 t B :=
      hnotA (K.mul_mem hx₁K hx₂K) (by rw [hx₁₂t]; exact hv₁₂ne)
    have hx₁₃A : x₁ * x₃ ∉ Asub8 t B :=
      hnotA (K.mul_mem hx₁K hx₃K) (by rw [hx₁₃t]; exact hv₁₃ne)
    have hx₂₃A : x₂ * x₃ ∉ Asub8 t B :=
      hnotA (K.mul_mem hx₂K hx₃K) (by rw [hx₂₃t]; exact hv₂₃ne)
    have hx₁₂₃A : x₁ * (x₂ * x₃) ∉ Asub8 t B :=
      hnotA (K.mul_mem hx₁K (K.mul_mem hx₂K hx₃K)) (by rw [hx₁₂₃t]; exact hv₁₂₃ne)
    obtain ⟨b, hbB, hb⟩ := sec8t84a1_E_pair h8B hK hsq hx₁K hx₂K hx₁A hx₂A hx₁₂A
    obtain ⟨b', hb'B, hb'⟩ := sec8t84a1_E_pair h8B hK hsq hx₁K hx₃K hx₁A hx₃A hx₁₃A
    obtain ⟨b'', hb''B, hb''⟩ := sec8t84a1_E_pair h8B hK hsq hx₁K (K.mul_mem hx₂K hx₃K)
      hx₁A hx₂₃A hx₁₂₃A
    have hx₂conj_t : x₂ * t * x₂⁻¹ = v₂ * t := by
      calc x₂ * t * x₂⁻¹ = (x₂ * t * x₂⁻¹ * t⁻¹) * t := by group
        _ = v₂ * t := by rw [hx₂t]
    have hcomm_x₂_b' : x₂ * b' = b' * x₂ :=
      (Subgroup.mem_centralizer_iff.mp (hK.le_C hx₂K).2 b' hb'B).symm
    have hx₂conj : x₂ * (t * b') * x₂⁻¹ = t * (v₂ * b') := by
      calc x₂ * (t * b') * x₂⁻¹ = (x₂ * t * x₂⁻¹) * (x₂ * b' * x₂⁻¹) := by group
        _ = (v₂ * t) * b' := by rw [hx₂conj_t, hcomm_x₂_b']; group
        _ = t * (v₂ * b') := by rw [← sec8t84a1_t_comm hK.ctx hv₂B]; group
    have hcomm_identity :
        x₁ * (x₂ * x₃) * x₁⁻¹ * (x₂ * x₃)⁻¹ =
          (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) * (x₂ * (x₁ * x₃ * x₁⁻¹ * x₃⁻¹) * x₂⁻¹) := by
      group
    have hkey : t * b'' = (t * b) * (x₂ * (t * b') * x₂⁻¹) := by
      rw [← hb'', ← hb, ← hb', hcomm_identity]
    have hkey2 : t * b'' = (t * b) * (t * (v₂ * b')) := by
      rw [hkey, hx₂conj]
    have hc'B : v₂ * b' ∈ B := B.mul_mem hv₂B hb'B
    have hfinal : t * b'' ∈ B := by
      have hsimp : (t * b) * (t * (v₂ * b')) = b * (v₂ * b') := by
        calc (t * b) * (t * (v₂ * b')) = (b * t) * (t * (v₂ * b')) := by
              rw [sec8t84a1_t_comm hK.ctx hbB]
          _ = b * (t * t) * (v₂ * b') := by group
          _ = b * (v₂ * b') := by rw [sec8t84a1_t_sq hK.ctx]; group
      rw [hkey2, hsimp]
      exact B.mul_mem hbB hc'B
    exact (sec8t84a1_t_mul_not_mem_B hK.ctx hb''B) hfinal
  constructor
  · intro k hk k' hk'
    obtain ⟨b, hbB, heq⟩ := sec8t84a1_E_sq_mul h8B hK hk hk'
    have hkksq : (k * k') * (k * k') ∈ B := hsq_mem (k * k') (K.mul_mem hk hk')
    have hkksq_k : k * k ∈ B := hsq_mem k hk
    have hkksq_k' : k' * k' ∈ B := hsq_mem k' hk'
    have hcK : k * k' * k⁻¹ * k'⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)) (K.inv_mem hk')
    have hc_invK : (k * k' * k⁻¹ * k'⁻¹)⁻¹ ∈ K := K.inv_mem hcK
    have hcent : b * (k * k' * k⁻¹ * k'⁻¹)⁻¹ = (k * k' * k⁻¹ * k'⁻¹)⁻¹ * b :=
      Subgroup.mem_centralizer_iff.mp (hK.le_C hc_invK).2 b hbB
    have heq2 : (k * k') * (k * k') =
        (k * k' * k⁻¹ * k'⁻¹)⁻¹ * (b * (k * k) * (k' * k')) := by
      rw [heq]
      calc b * (k * k' * k⁻¹ * k'⁻¹)⁻¹ * (k * k) * (k' * k')
          = (b * (k * k' * k⁻¹ * k'⁻¹)⁻¹) * ((k * k) * (k' * k')) := by group
        _ = ((k * k' * k⁻¹ * k'⁻¹)⁻¹ * b) * ((k * k) * (k' * k')) := by rw [hcent]
        _ = (k * k' * k⁻¹ * k'⁻¹)⁻¹ * (b * (k * k) * (k' * k')) := by group
    have heB : b * (k * k) * (k' * k') ∈ B := B.mul_mem (B.mul_mem hbB hkksq_k) hkksq_k'
    have hc_inv_mem : (k * k' * k⁻¹ * k'⁻¹)⁻¹ ∈ B := by
      have h2 : (k * k' * k⁻¹ * k'⁻¹)⁻¹ =
          ((k * k') * (k * k')) * (b * (k * k) * (k' * k'))⁻¹ := by
        rw [heq2]; group
      rw [h2]
      exact B.mul_mem hkksq (B.inv_mem heB)
    simpa using B.inv_mem hc_inv_mem
  · exact hsq_mem

end CFSG.OddStandard.SmallF3.Omega
