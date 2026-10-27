module

public import CFSG.LargeExtraspecial.AS35QIxNine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup

variable {G : Type} [Group G]

@[expose] def PropP (w : G) : Prop :=
  ∀ e x b : G, e * w = w * e → x * w = w * x → b * w = w * b → e * e = 1 → x ^ 3 = 1 →
    e * (x * e * x⁻¹) = (x * e * x⁻¹) * e →
    ∃ n : ℕ, ((e * x * e⁻¹ * x⁻¹) * b * (e * x * e⁻¹ * x⁻¹)⁻¹ * b⁻¹) ^ (2 ^ n) = 1

theorem PropP.conj {w : G} (h : PropP w) (k : G) : PropP (k * w * k⁻¹) := by
  intro e x b he hx hb hee hx3 hc
  set φ : G ≃* G := MulAut.conj k⁻¹ with hφ
  have hφw : φ (k * w * k⁻¹) = w := by rw [hφ, MulAut.conj_apply]; group
  have hcomm : ∀ y : G, y * (k * w * k⁻¹) = k * w * k⁻¹ * y → φ y * w = w * φ y := by
    intro y hy
    rw [← hφw, ← map_mul, ← map_mul, hy]
  obtain ⟨n, hn⟩ := h (φ e) (φ x) (φ b) (hcomm e he) (hcomm x hx) (hcomm b hb)
    (by rw [← map_mul, hee, map_one]) (by rw [← map_pow, hx3, map_one])
    (by simp only [← map_mul, ← map_inv, hc])
  refine ⟨n, φ.injective ?_⟩
  rw [map_one, ← hn]
  simp only [map_pow, map_mul, map_inv]

variable [Finite G] {S : Setting G}

namespace IxSetup

variable (T : IxSetup S)

theorem conj_mul_self_of {H : Type*} [Group H] (x y : H) (hy : y * y = 1) :
    (x * y * x⁻¹) * (x * y * x⁻¹) = 1 := by
  rw [show x * y * x⁻¹ * (x * y * x⁻¹) = x * (y * y) * x⁻¹ by group, hy, mul_one,
    mul_inv_cancel]

theorem conj_comm_of {H : Type*} [Group H] (x y y' : H) (h : y * y' = y' * y) :
    (x * y * x⁻¹) * (x * y' * x⁻¹) = (x * y' * x⁻¹) * (x * y * x⁻¹) := by
  calc (x * y * x⁻¹) * (x * y' * x⁻¹) = x * (y * y') * x⁻¹ := by group
    _ = x * (y' * y) * x⁻¹ := by rw [h]
    _ = (x * y' * x⁻¹) * (x * y * x⁻¹) := by group

theorem mul_mul_self_of_comm {H : Type*} [Group H] {a b : H} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) : (a * b) * (a * b) = 1 := by
  calc (a * b) * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hab]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha, hb, one_mul]

include T in
theorem conj_eq_of_bar {e x : S.O} (he : e ∈ S.Mbar) (hx : x ∈ S.Mbar) (hee : e * e = 1)
    (hx3 : x ^ 3 = 1) (hc : e * (x * e * x⁻¹) = (x * e * x⁻¹) * e) : x * e * x⁻¹ = e := by
  have hxζ : Commute x T.ζ := T.comm_zeta_of_pow_three hx hx3
  have hx3' : x * (x * x) = 1 := by rw [← pow_three]; exact hx3
  obtain ⟨e₂, he₂⟩ : ∃ e₂, e₂ = x * e * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨e₃, he₃⟩ : ∃ e₃, e₃ = x * e₂ * x⁻¹ := ⟨_, rfl⟩
  rw [← he₂] at hc ⊢
  have he₂e₂ : e₂ * e₂ = 1 := he₂ ▸ conj_mul_self_of x e hee
  have he₃e₃ : e₃ * e₃ = 1 := he₃ ▸ conj_mul_self_of x e₂ he₂e₂
  have hc₂₃ : e₂ * e₃ = e₃ * e₂ := by
    have h := conj_comm_of x e e₂ hc
    rwa [← he₂, ← he₃] at h
  have he₄ : x * e₃ * x⁻¹ = e := by
    rw [he₃, he₂, show x * (x * (x * e * x⁻¹) * x⁻¹) * x⁻¹ =
      (x * (x * x)) * e * (x * (x * x))⁻¹ by group, hx3', one_mul, inv_one, mul_one]
  have hc₃₁ : e₃ * e = e * e₃ := by
    have h := conj_comm_of x e₂ e₃ hc₂₃
    rwa [← he₃, he₄] at h
  have hconjc : ∀ y : S.O, Commute y T.ζ → Commute (x * y * x⁻¹) T.ζ := fun y hy =>
    ((hxζ.mul_left hy).mul_left hxζ.inv_left)
  have hconjinv : ∀ y : S.O, y * T.ζ * y⁻¹ = T.ζ⁻¹ →
      (x * y * x⁻¹) * T.ζ * (x * y * x⁻¹)⁻¹ = T.ζ⁻¹ := by
    intro y hy
    have h1 : x⁻¹ * T.ζ * x = T.ζ := by
      rw [mul_assoc, ← hxζ.eq, ← mul_assoc, inv_mul_cancel, one_mul]
    have h2 : x * T.ζ⁻¹ * x⁻¹ = T.ζ⁻¹ := by
      rw [hxζ.inv_right.eq, mul_assoc, mul_inv_cancel, mul_one]
    calc (x * y * x⁻¹) * T.ζ * (x * y * x⁻¹)⁻¹ = x * (y * (x⁻¹ * T.ζ * x) * y⁻¹) * x⁻¹ := by
          group
      _ = x * T.ζ⁻¹ * x⁻¹ := by rw [h1, hy]
      _ = T.ζ⁻¹ := h2
  by_cases heζ : e * T.ζ = T.ζ * e
  · have he₂ζ : e₂ * T.ζ = T.ζ * e₂ := he₂ ▸ (hconjc e heζ).eq
    rcases T.eq_or_of_commute_O heζ he₂ζ hee he₂e₂ hc with h | h | h
    · exact h.symm
    · rw [he₂, h]
      group
    · have h1 : e = 1 := by
        calc e = x⁻¹ * (x * e * x⁻¹) * x := by group
          _ = 1 := by rw [← he₂, h]; group
      rw [h, h1]
  · have hinv₁ := T.conj_inv_of_not_comm he heζ
    have hinv₂ : e₂ * T.ζ * e₂⁻¹ = T.ζ⁻¹ := he₂ ▸ hconjinv e hinv₁
    have hinv₃ : e₃ * T.ζ * e₃⁻¹ = T.ζ⁻¹ := he₃ ▸ hconjinv e₂ hinv₂
    have hf₁ := T.comm_of_inv_of_inv hinv₁ hinv₂
    have hf₂ := T.comm_of_inv_of_inv hinv₂ hinv₃
    have hf₁f₁ := mul_mul_self_of_comm hee he₂e₂ hc
    have hf₂f₂ := mul_mul_self_of_comm he₂e₂ he₃e₃ hc₂₃
    have hff : (e * e₂) * (e₂ * e₃) = (e₂ * e₃) * (e * e₂) := by
      calc (e * e₂) * (e₂ * e₃) = e * (e₂ * e₂) * e₃ := by group
        _ = e * e₃ := by rw [he₂e₂, mul_one]
        _ = e * (e₂ * e₂) * e₃ := by rw [he₂e₂, mul_one]
        _ = (e * e₂) * (e₂ * e₃) := by group
        _ = (e₂ * e) * (e₂ * e₃) := by rw [hc]
        _ = e₂ * (e * e₂) * e₃ := by group
        _ = e₂ * (e₂ * e) * e₃ := by rw [hc]
        _ = e₂ * e₂ * (e * e₃) := by group
        _ = e₂ * e₂ * (e₃ * e) := by rw [hc₃₁]
        _ = e₂ * (e₂ * e₃) * e := by group
        _ = e₂ * (e₃ * e₂) * e := by rw [hc₂₃]
        _ = (e₂ * e₃) * (e₂ * e) := by group
        _ = (e₂ * e₃) * (e * e₂) := by rw [← hc]
    rcases T.eq_or_of_commute_O hf₁ hf₂ hf₁f₁ hf₂f₂ hff with h | h | h
    · have h13 : e = e₃ := by
        calc e = e * (e₂ * e₂) := by rw [he₂e₂, mul_one]
          _ = (e * e₂) * e₂ := by group
          _ = (e₂ * e₃) * e₂ := by rw [h]
          _ = e₂ * (e₃ * e₂) := by group
          _ = e₂ * (e₂ * e₃) := by rw [hc₂₃]
          _ = e₃ := by rw [← mul_assoc, he₂e₂, one_mul]
      calc e₂ = x * e * x⁻¹ := he₂
        _ = x * e₃ * x⁻¹ := by rw [← h13]
        _ = e := he₄
    · exact (eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hee)
    · have h23 : e₃ = e₂ := (eq_inv_of_mul_eq_one_right h).trans
        (inv_eq_of_mul_eq_one_right he₂e₂)
      calc e₂ = x⁻¹ * (x * e₂ * x⁻¹) * x := by group
        _ = x⁻¹ * e₂ * x := by rw [← he₃, h23]
        _ = e := by rw [he₂]; group

include T in
theorem comm_mem_QG {e x : G} (heM : e ∈ S.M) (hxM : x ∈ S.M) (hee : e * e = 1)
    (hx3 : x ^ 3 = 1) (hc : e * (x * e * x⁻¹) = (x * e * x⁻¹) * e) :
    e * x * e⁻¹ * x⁻¹ ∈ S.QG := by
  have hmem : e * x * e⁻¹ * x⁻¹ ∈ S.M :=
    S.M.mul_mem (S.M.mul_mem (S.M.mul_mem heM hxM) (S.M.inv_mem heM)) (S.M.inv_mem hxM)
  have hxe : x * e * x⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hxM heM) (S.M.inv_mem hxM)
  refine (S.ρ_eq_one_iff ⟨_, hmem⟩).mp ?_
  have e1 : (⟨_, hmem⟩ : S.M) = ⟨e, heM⟩ * ⟨x, hxM⟩ * (⟨e, heM⟩ : S.M)⁻¹ * (⟨x, hxM⟩ : S.M)⁻¹ :=
    rfl
  have hρee : S.ρ ⟨e, heM⟩ * S.ρ ⟨e, heM⟩ = 1 := by
    rw [← map_mul]
    rw [show (⟨e, heM⟩ : S.M) * ⟨e, heM⟩ = 1 from Subtype.ext hee, map_one]
  have hρx3 : S.ρ ⟨x, hxM⟩ ^ 3 = 1 := by
    rw [← map_pow]
    rw [show (⟨x, hxM⟩ : S.M) ^ 3 = 1 from Subtype.ext (by simpa using hx3), map_one]
  have hρc : S.ρ ⟨e, heM⟩ * (S.ρ ⟨x, hxM⟩ * S.ρ ⟨e, heM⟩ * (S.ρ ⟨x, hxM⟩)⁻¹) =
      (S.ρ ⟨x, hxM⟩ * S.ρ ⟨e, heM⟩ * (S.ρ ⟨x, hxM⟩)⁻¹) * S.ρ ⟨e, heM⟩ := by
    simp only [← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext hc
  have key := T.conj_eq_of_bar ⟨_, rfl⟩ ⟨_, rfl⟩ hρee hρx3 hρc
  rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv]
  calc S.ρ ⟨e, heM⟩ * S.ρ ⟨x, hxM⟩ * (S.ρ ⟨e, heM⟩)⁻¹ * (S.ρ ⟨x, hxM⟩)⁻¹ =
      S.ρ ⟨e, heM⟩ * (S.ρ ⟨x, hxM⟩ * S.ρ ⟨e, heM⟩ * (S.ρ ⟨x, hxM⟩)⁻¹)⁻¹ := by group
    _ = 1 := by rw [key, mul_inv_cancel]

omit [Finite G] in
theorem pow_two_pow_of_mem_QG {y : G} (hy : y ∈ S.QG) : ∃ n : ℕ, y ^ (2 ^ n) = 1 := by
  obtain ⟨k, hk⟩ := S.isPGroup_QG ⟨y, hy⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

include T in
theorem propP_z : PropP S.z := by
  intro e x b he hx hb hee hx3 hc
  have heM : e ∈ S.M := S.mem_M_iff.mpr he
  have hxM : x ∈ S.M := S.mem_M_iff.mpr hx
  have hbM : b ∈ S.M := S.mem_M_iff.mpr hb
  have hf := T.comm_mem_QG heM hxM hee hx3 hc
  set f := e * x * e⁻¹ * x⁻¹
  have hbf : f * b * f⁻¹ * b⁻¹ ∈ S.QG := by
    rw [show f * b * f⁻¹ * b⁻¹ = f * (b * f⁻¹ * b⁻¹) by group]
    exact S.QG.mul_mem hf (S.conj_mem_QG hbM (S.QG.inv_mem hf))
  exact pow_two_pow_of_mem_QG hbf

theorem conj_t_of_conj_z {c : G} (hc : c * (S.z * T.t) = S.z * T.t * c)
    (h : c * S.z * c⁻¹ = S.z) : c * T.t * c⁻¹ = T.t := by
  have h1 : c * (S.z * T.t) * c⁻¹ = S.z * T.t := by rw [hc]; group
  rw [show c * (S.z * T.t) * c⁻¹ = (c * S.z * c⁻¹) * (c * T.t * c⁻¹) by group, h] at h1
  exact mul_left_cancel h1

theorem conj_t_of_conj_z_eq_t {c : G} (hc : c * (S.z * T.t) = S.z * T.t * c)
    (h : c * S.z * c⁻¹ = T.t) : c * T.t * c⁻¹ = S.z := by
  have h1 : c * (S.z * T.t) * c⁻¹ = S.z * T.t := by rw [hc]; group
  rw [show c * (S.z * T.t) * c⁻¹ = (c * S.z * c⁻¹) * (c * T.t * c⁻¹) by group, h,
    ← T.t_comm_z] at h1
  exact mul_left_cancel h1

theorem mem_QG_inf_or_Qa_of_mem {f b : G} (hfQ : f ∈ S.QG) (hft : f * T.t = T.t * f)
    (hb : b * S.z * b⁻¹ = T.t) (hbt : b * T.t * b⁻¹ = S.z) :
    ∃ n : ℕ, (f * b * f⁻¹ * b⁻¹) ^ (2 ^ n) = 1 := by
  set H : Subgroup G := S.QG ⊓ centralizer ({T.t} : Set G) with hH
  set K : Subgroup G := S.Qa T.g ⊓ S.M with hK
  have hHp : IsPGroup 2 H := S.isPGroup_QG.to_le inf_le_left
  have hKp : IsPGroup 2 K := (Setting.AS35T.isPGroup_Qa S T.g).to_le inf_le_left
  have hKt : ∀ k ∈ K, k * T.t = T.t * k := fun k hk =>
    Setting.AS35T.commute_of_mem_Qa S (mem_inf.mp hk).1
  have hKN : K ≤ normalizer (H : Set G) := by
    intro k hk
    have hkM := (mem_inf.mp hk).2
    have hkt := hKt k hk
    have hkt' : k⁻¹ * T.t = T.t * k⁻¹ := (Commute.inv_left hkt).eq
    rw [mem_normalizer_iff]
    intro y
    simp only [hH, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hyQ, hyt⟩
      refine ⟨S.conj_mem_QG hkM hyQ, ?_⟩
      calc k * y * k⁻¹ * T.t = k * y * (k⁻¹ * T.t) := by group
        _ = k * y * (T.t * k⁻¹) := by rw [hkt']
        _ = k * (y * T.t) * k⁻¹ := by group
        _ = k * (T.t * y) * k⁻¹ := by rw [hyt]
        _ = T.t * (k * y * k⁻¹) := by rw [← mul_assoc k T.t, hkt]; group
    · rintro ⟨hyQ, hyt⟩
      have h1 := S.conj_mem_QG (S.M.inv_mem hkM) hyQ
      rw [show k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ = y by group] at h1
      refine ⟨h1, ?_⟩
      calc y * T.t = k⁻¹ * (k * y * k⁻¹) * k * T.t := by group
        _ = k⁻¹ * (k * y * k⁻¹) * (T.t * k) := by rw [mul_assoc _ k, hkt]
        _ = k⁻¹ * ((k * y * k⁻¹) * T.t) * k := by group
        _ = k⁻¹ * (T.t * (k * y * k⁻¹)) * k := by rw [hyt]
        _ = T.t * y := by rw [← mul_assoc k⁻¹ T.t, hkt']; group
  have hR : IsPGroup 2 (H ⊔ K : Subgroup G) := hHp.to_sup_of_normal_left' hKp hKN
  have hfH : f ∈ H := mem_inf.mpr ⟨hfQ, mem_centralizer_singleton_iff.mpr hft⟩
  have hbf : b * f⁻¹ * b⁻¹ ∈ K := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [← S.Qa_eq_of_conj_eq (g := b) (h := T.g) hb, S.mem_Qa_iff_inv_conj_mem]
      rw [show b⁻¹ * (b * f⁻¹ * b⁻¹) * b = f⁻¹ by group]
      exact S.QG.inv_mem hfQ
    · rw [S.mem_M_iff]
      have hft' : f⁻¹ * T.t = T.t * f⁻¹ := (Commute.inv_left hft).eq
      calc b * f⁻¹ * b⁻¹ * S.z = b * f⁻¹ * (b⁻¹ * S.z * b) * b⁻¹ := by group
        _ = b * f⁻¹ * T.t * b⁻¹ := by
          rw [show b⁻¹ * S.z * b = T.t by
            calc b⁻¹ * S.z * b = b⁻¹ * (b * T.t * b⁻¹) * b := by rw [hbt]
              _ = T.t := by group]
        _ = b * (T.t * f⁻¹) * b⁻¹ := by rw [mul_assoc b, hft']
        _ = (b * T.t * b⁻¹) * (b * f⁻¹ * b⁻¹) := by group
        _ = S.z * (b * f⁻¹ * b⁻¹) := by rw [hbt]
  have hmem : f * b * f⁻¹ * b⁻¹ ∈ (H ⊔ K : Subgroup G) := by
    rw [show f * b * f⁻¹ * b⁻¹ = f * (b * f⁻¹ * b⁻¹) by group]
    exact mul_mem (mem_sup_left hfH) (mem_sup_right hbf)
  obtain ⟨k, hk⟩ := hR ⟨_, hmem⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem propP_zt (hS : S.SixHyp) : PropP (S.z * T.t) := by
  intro e x b he hx hb hee hx3 hc
  have hx3' : x * (x * x) = 1 := by rw [← pow_three]; exact hx3
  have hxz : x * S.z * x⁻¹ = S.z := by
    rcases T.fiveNineTwo hS hx with h | h
    · exact h
    · exfalso
      have h2 := T.conj_t_of_conj_z_eq_t hx h
      have h3 : (x * (x * x)) * S.z * (x * (x * x))⁻¹ = T.t := by
        calc (x * (x * x)) * S.z * (x * (x * x))⁻¹ =
            x * (x * (x * S.z * x⁻¹) * x⁻¹) * x⁻¹ := by group
          _ = T.t := by rw [h, h2, h]
      rw [hx3', one_mul, inv_one, mul_one] at h3
      exact T.t_ne_z h3.symm
  have hxt := T.conj_t_of_conj_z hx hxz
  have hxM : x ∈ S.M := S.mem_M_of_conj_eq_z hxz
  obtain ⟨e₂, he₂⟩ : ∃ e₂, e₂ = x * e * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨e₃, he₃⟩ : ∃ e₃, e₃ = x * e₂ * x⁻¹ := ⟨_, rfl⟩
  rw [← he₂] at hc
  have he₂e₂ : e₂ * e₂ = 1 := he₂ ▸ conj_mul_self_of x e hee
  have he₃e₃ : e₃ * e₃ = 1 := he₃ ▸ conj_mul_self_of x e₂ he₂e₂
  have hc₂₃ : e₂ * e₃ = e₃ * e₂ := by
    have h := conj_comm_of x e e₂ hc
    rwa [← he₂, ← he₃] at h
  have he₄ : x * e₃ * x⁻¹ = e := by
    rw [he₃, he₂, show x * (x * (x * e * x⁻¹) * x⁻¹) * x⁻¹ =
      (x * (x * x)) * e * (x * (x * x))⁻¹ by group, hx3', one_mul, inv_one, mul_one]
  have hc₃₁ : e₃ * e = e * e₃ := by
    have h := conj_comm_of x e₂ e₃ hc₂₃
    rwa [← he₃, he₄] at h
  have hez := T.fiveNineTwo hS he
  have he₂z : e₂ * S.z * e₂⁻¹ = e * S.z * e⁻¹ := by
    have hxz' : x⁻¹ * S.z * x = S.z := by
      calc x⁻¹ * S.z * x = x⁻¹ * (x * S.z * x⁻¹) * x := by rw [hxz]
        _ = S.z := by group
    calc e₂ * S.z * e₂⁻¹ = x * (e * (x⁻¹ * S.z * x) * e⁻¹) * x⁻¹ := by rw [he₂]; group
      _ = x * (e * S.z * e⁻¹) * x⁻¹ := by rw [hxz']
      _ = e * S.z * e⁻¹ := by rcases hez with h | h <;> rw [h] <;> [exact hxz; exact hxt]
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have hf : e * x * e⁻¹ * x⁻¹ = e * e₂ := by rw [he₂, heinv]; group
  have hfz : (e * e₂) * S.z * (e * e₂)⁻¹ = S.z := by
    calc (e * e₂) * S.z * (e * e₂)⁻¹ = e * (e₂ * S.z * e₂⁻¹) * e⁻¹ := by group
      _ = (e * e) * S.z * (e * e)⁻¹ := by rw [he₂z]; group
      _ = S.z := by rw [hee]; group
  have hfM : e * e₂ ∈ S.M := S.mem_M_of_conj_eq_z hfz
  have he₂C : e₂ * (S.z * T.t) = S.z * T.t * e₂ := by
    rw [he₂]
    have h1 : x * (S.z * T.t) * x⁻¹ = S.z * T.t := by
      rw [show x * (S.z * T.t) * x⁻¹ = (x * S.z * x⁻¹) * (x * T.t * x⁻¹) by group, hxz, hxt]
    calc x * e * x⁻¹ * (S.z * T.t) = x * e * (x⁻¹ * (S.z * T.t) * x) * x⁻¹ := by group
      _ = x * e * (S.z * T.t) * x⁻¹ := by
        rw [show x⁻¹ * (S.z * T.t) * x = S.z * T.t by
          calc x⁻¹ * (S.z * T.t) * x = x⁻¹ * (x * (S.z * T.t) * x⁻¹) * x := by rw [h1]
            _ = S.z * T.t := by group]
      _ = x * (S.z * T.t * e) * x⁻¹ := by rw [mul_assoc x e, he]
      _ = x * (S.z * T.t) * x⁻¹ * (x * e * x⁻¹) := by group
      _ = S.z * T.t * (x * e * x⁻¹) := by rw [h1]
  have hft : (e * e₂) * T.t = T.t * (e * e₂) := by
    obtain ⟨f, hfdef⟩ : ∃ f, f = e * e₂ := ⟨_, rfl⟩
    rw [← hfdef] at hfM ⊢
    have hzt : f * (S.z * T.t) = S.z * T.t * f := by
      rw [hfdef]
      calc (e * e₂) * (S.z * T.t) = e * (e₂ * (S.z * T.t)) := by group
        _ = e * (S.z * T.t * e₂) := by rw [he₂C]
        _ = (e * (S.z * T.t)) * e₂ := by group
        _ = S.z * T.t * (e * e₂) := by rw [he]; group
    have hfz' : f * S.z = S.z * f := S.mem_M_iff.mp hfM
    have hfz'' : f * S.z⁻¹ = S.z⁻¹ * f := (Commute.inv_right hfz').eq
    calc f * T.t = (f * S.z⁻¹) * (S.z * T.t) := by group
      _ = (S.z⁻¹ * f) * (S.z * T.t) := by rw [hfz'']
      _ = S.z⁻¹ * (f * (S.z * T.t)) := by group
      _ = S.z⁻¹ * (S.z * T.t * f) := by rw [hzt]
      _ = T.t * f := by group
  have hff : (e * e₂) * (e * e₂) = 1 := mul_mul_self_of_comm hee he₂e₂ hc
  have hfx : (e * e₂) * (x * (e * e₂) * x⁻¹) = (x * (e * e₂) * x⁻¹) * (e * e₂) := by
    rw [show x * (e * e₂) * x⁻¹ = (x * e * x⁻¹) * (x * e₂ * x⁻¹) by group, ← he₂, ← he₃]
    calc e * e₂ * (e₂ * e₃) = e * e₃ := by rw [mul_assoc e, ← mul_assoc e₂, he₂e₂, one_mul]
      _ = e₃ * e := hc₃₁.symm
      _ = e₂ * e₂ * e₃ * e := by rw [he₂e₂, one_mul]
      _ = e₂ * (e₂ * e₃) * e := by group
      _ = e₂ * (e₃ * e₂) * e := by rw [hc₂₃]
      _ = e₂ * e₃ * (e₂ * e) := by group
      _ = e₂ * e₃ * (e * e₂) := by rw [← hc]
  have hcomm := T.comm_mem_QG hfM hxM hff hx3 hfx
  have hf3 : (e * e₂) * (x * (e * e₂) * x⁻¹) = x * (x * (e * e₂) * x⁻¹) * x⁻¹ := by
    rw [show x * (e * e₂) * x⁻¹ = (x * e * x⁻¹) * (x * e₂ * x⁻¹) by group, ← he₂, ← he₃,
      show x * (e₂ * e₃) * x⁻¹ = (x * e₂ * x⁻¹) * (x * e₃ * x⁻¹) by group, ← he₃, he₄]
    calc e * e₂ * (e₂ * e₃) = e * e₃ := by rw [mul_assoc e, ← mul_assoc e₂, he₂e₂, one_mul]
      _ = e₃ * e := hc₃₁.symm
  have hfQ : e * e₂ ∈ S.QG := by
    set a := e * e₂ with ha
    have hxa : x * a * x⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hxM hfM) (S.M.inv_mem hxM)
    have h1 : a * (x * a * x⁻¹)⁻¹ ∈ S.QG := by
      rw [show a * (x * a * x⁻¹)⁻¹ = a * x * a⁻¹ * x⁻¹ by group]
      exact hcomm
    have hρ1 : S.ρ ⟨a, hfM⟩ = S.ρ ⟨x * a * x⁻¹, hxa⟩ := by
      have h1M : a * (x * a * x⁻¹)⁻¹ ∈ S.M := S.M.mul_mem hfM (S.M.inv_mem hxa)
      have e1 := (S.ρ_eq_one_iff ⟨_, h1M⟩).mpr h1
      have e2 : (⟨_, h1M⟩ : S.M) = ⟨a, hfM⟩ * (⟨x * a * x⁻¹, hxa⟩ : S.M)⁻¹ := rfl
      rw [e2, map_mul, map_inv, mul_inv_eq_one] at e1
      exact e1
    have hx2a : x * (x * a * x⁻¹) * x⁻¹ ∈ S.M :=
      S.M.mul_mem (S.M.mul_mem hxM hxa) (S.M.inv_mem hxM)
    have hc1 : S.ρ ⟨x * a * x⁻¹, hxa⟩ = S.ρ ⟨x, hxM⟩ * S.ρ ⟨a, hfM⟩ * (S.ρ ⟨x, hxM⟩)⁻¹ := by
      rw [show (⟨x * a * x⁻¹, hxa⟩ : S.M) = ⟨x, hxM⟩ * ⟨a, hfM⟩ * (⟨x, hxM⟩ : S.M)⁻¹ from rfl,
        map_mul, map_mul, map_inv]
    have hc2 : S.ρ ⟨x * (x * a * x⁻¹) * x⁻¹, hx2a⟩ =
        S.ρ ⟨x, hxM⟩ * S.ρ ⟨x * a * x⁻¹, hxa⟩ * (S.ρ ⟨x, hxM⟩)⁻¹ := by
      rw [show (⟨x * (x * a * x⁻¹) * x⁻¹, hx2a⟩ : S.M) =
          ⟨x, hxM⟩ * ⟨x * a * x⁻¹, hxa⟩ * (⟨x, hxM⟩ : S.M)⁻¹ from rfl,
        map_mul, map_mul, map_inv]
    have hρ2 : S.ρ ⟨x * a * x⁻¹, hxa⟩ = S.ρ ⟨x * (x * a * x⁻¹) * x⁻¹, hx2a⟩ := by
      rw [hc2, ← hρ1, ← hc1]
      exact hρ1
    have hρ3 : S.ρ ⟨a, hfM⟩ * S.ρ ⟨x * a * x⁻¹, hxa⟩ =
        S.ρ ⟨x * (x * a * x⁻¹) * x⁻¹, hx2a⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hf3
    rw [← hρ2, ← hρ1, mul_eq_right] at hρ3
    exact (S.ρ_eq_one_iff ⟨a, hfM⟩).mp hρ3
  rw [hf]
  rcases T.fiveNineTwo hS hb with hbz | hbz
  · have hbM : b ∈ S.M := S.mem_M_of_conj_eq_z hbz
    have hbf : (e * e₂) * b * (e * e₂)⁻¹ * b⁻¹ ∈ S.QG := by
      rw [show (e * e₂) * b * (e * e₂)⁻¹ * b⁻¹ = (e * e₂) * (b * (e * e₂)⁻¹ * b⁻¹) by group]
      exact S.QG.mul_mem hfQ (S.conj_mem_QG hbM (S.QG.inv_mem hfQ))
    exact pow_two_pow_of_mem_QG hbf
  · exact T.mem_QG_inf_or_Qa_of_mem hfQ hft hbz (T.conj_t_of_conj_z_eq_t hb hbz)

end IxSetup

end CFSG.LargeExtraspecial.AS35QIx
