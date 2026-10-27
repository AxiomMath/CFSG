module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageBranch
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1BranchNu

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

section Basic

variable (h : U3C1Stage G L f t T d V U U₁ k)
include h

theorem V_le_V₁ : V ≤ U₁ ⊓ centralizer (szT₁ L T : Set G) :=
  le_inf h.V_le_U₁ h.le_centralizer

theorem mem_V_of_mem_V₁_of_mem_sup {w : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hws : w ∈ szT₁ L T ⊔ V) : w ∈ V := by
  obtain ⟨y, hy, r, hr, rfl⟩ := h.exists_mul_of_mem_sup hws
  have hyC : y ∈ centralizer (szT₁ L T : Set G) := by
    have := mul_mem (mem_inf.mp hw).2 (h.le_centralizer (inv_mem hr))
    simpa using this
  exact mul_mem (h.le (mem_szA₁.mpr ⟨hy, hyC⟩)) hr

theorem conj_d_mem_V₁ {w : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    d⁻¹ * w * d ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) := by
  obtain ⟨hwU₁, hwC⟩ := mem_inf.mp hw
  refine mem_inf.mpr ⟨h.conj_d_mem_U₁ hwU₁, mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hdy : d * y * d⁻¹ ∈ szT₁ L T := by
    simpa using (mem_normalizer_iff.mp h.d_norm.1.2 y).mp hy
  have e := mem_centralizer_iff.mp hwC _ hdy
  calc y * (d⁻¹ * w * d) = d⁻¹ * ((d * y * d⁻¹) * w) * d := by group
    _ = d⁻¹ * (w * (d * y * d⁻¹)) * d := by rw [e]
    _ = d⁻¹ * w * d * y := by group

theorem sq_mul_t (x : G) : (x * t) ^ 2 = x * (t * x * t⁻¹) := by
  rw [sq, h.t_inv]
  group

theorem t_conj_mem_V₁ {w : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    t * w * t⁻¹ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) := by
  obtain ⟨hwU₁, hwC⟩ := mem_inf.mp hw
  refine mem_inf.mpr ⟨h.conj_mem_U₁ h.t_mem_U hwU₁, mem_centralizer_iff.mpr fun y hy => ?_⟩
  have e := mem_centralizer_iff.mp hwC y hy
  have e1 : y * t = t * y := h.t_comm hy
  have e2 : y * t⁻¹ = t⁻¹ * y := by rw [h.t_inv]; exact e1
  calc y * (t * w * t⁻¹) = (y * t) * w * t⁻¹ := by group
    _ = t * (y * w) * t⁻¹ := by rw [e1]; group
    _ = t * (w * y) * t⁻¹ := by rw [e]
    _ = t * w * (y * t⁻¹) := by group
    _ = t * w * (t⁻¹ * y) := by rw [e2]
    _ = t * w * t⁻¹ * y := by group

theorem szR_V₁_eq (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) :
    szR (szT₁ L T) (U₁ ⊓ centralizer (szT₁ L T : Set G)) t = U := by
  rw [szR, ← hlam, h.sup_eq]

theorem U_le_normalizer_sup : U ≤ normalizer ((szT₁ L T ⊔ V : Subgroup G) : Set G) :=
  fun x hx => mem_normalizer_of_forall_inv_mul_mul_mem fun z hz => by
    obtain ⟨y, hy, r, hr, rfl⟩ := h.exists_mul_of_mem_sup hz
    rw [show x⁻¹ * (y * r) * x = (x⁻¹ * y * x⁻¹⁻¹) * (x⁻¹ * r * x⁻¹⁻¹) by group]
    exact mul_mem (mem_sup_left (h.conj_T₁_mem (inv_mem hx) hy))
      (mem_sup_right (h.conj_V_of_mem_U (inv_mem hx) hr))

end Basic

section Coords

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {v : G → K}
  {μ : K} (h : U3C1Stage G L f t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
  (hc : U3A₁Coords (szA₁ (szT₁ L T)) d v μ)
include h hK hc

theorem S_surj_V₁ (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w)
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) (s : K) :
    ∃ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), v ((w * t * w⁻¹ * t⁻¹) ^ 2 ^ k) = s := by
  obtain ⟨x, hx, hxs⟩ := h.S_surj hK hc hμ s
  have hTN : szT₁ L T ≤ normalizer ((U₁ ⊓ centralizer (szT₁ L T : Set G) : Subgroup G) : Set G) :=
    fun y hy => mem_normalizer_of_forall_inv_mul_mul_mem fun w hw => by
      rw [mem_centralizer_iff.mp (mem_inf.mp hw).2 _ (inv_mem hy), inv_mul_cancel_right]
      exact hw
  have hx' : x ∈ ((szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) : Subgroup G) : Set G) := by
    rw [← hlam]
    exact hx
  rw [coe_mul_of_left_le_normalizer_right _ _ hTN] at hx'
  obtain ⟨y, hy, w, hw, rfl⟩ := hx'
  refine ⟨w, hw, ?_⟩
  rw [← hxs, h.S_mul hK hc (h.T₁_le_U₁ hy) (mem_inf.mp hw).1,
    h.S_eq_zero_of_mem_sup hK hc (mem_sup_left hy), zero_add]

theorem V₁_comm' (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w)
    (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) :
    ∀ x ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), ∀ y ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      x * y = y * x := by
  set V₁ := U₁ ⊓ centralizer (szT₁ L T : Set G) with hV₁
  have hcA : ∀ x ∈ V₁, ∀ y ∈ V₁, x * y * x⁻¹ * y⁻¹ ∈ szA₁ (szT₁ L T) := fun x hx y hy =>
    h.comm_mem_szA₁ x (mem_inf.mp hx).1 y (mem_inf.mp hy).1
  have hcen : ∀ x ∈ V₁, ∀ b ∈ szA₁ (szT₁ L T), x * b * x⁻¹ = b := fun x hx b hb =>
    h.conj_szA₁ x (h.U₁_le (mem_inf.mp hx).1) b hb
  have hVc : ∀ x ∈ V₁, x ∈ V → ∀ y ∈ V₁, x * y * x⁻¹ * y⁻¹ = 1 := by
    intro x _ hxV y hy
    rw [mem_centralizer_iff.mp (hμV (mem_inf.mp hy).1) x hxV]
    group
  obtain ⟨D, hD⟩ := SzC1.exists_addMonoidHom₂_of_hom₂ (M := V₁)
    (S := fun x => v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k)) (B := fun x y => v (x * y * x⁻¹ * y⁻¹))
    (fun x hx y hy => h.S_mul hK hc (mem_inf.mp hx).1 (mem_inf.mp hy).1)
    (h.S_surj_V₁ hK hc hμ hlam)
    (fun x hx x' hx' y hy => by
      show v (x * x' * y * (x * x')⁻¹ * y⁻¹) = v (x * y * x⁻¹ * y⁻¹) + v (x' * y * x'⁻¹ * y⁻¹)
      rw [show x * x' * y * (x * x')⁻¹ * y⁻¹ = x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹ *
          (x * y * x⁻¹ * y⁻¹) by group, hcen x hx _ (hcA x' hx' y hy),
        hc.mul _ (hcA x' hx' y hy) _ (hcA x hx y hy), add_comm])
    (fun x hx y hy y' hy' => by
      show v (x * (y * y') * x⁻¹ * (y * y')⁻¹) = v (x * y * x⁻¹ * y⁻¹) + v (x * y' * x⁻¹ * y'⁻¹)
      rw [show x * (y * y') * x⁻¹ * (y * y')⁻¹ = x * y * x⁻¹ * y⁻¹ *
          (y * (x * y' * x⁻¹ * y'⁻¹) * y⁻¹) by group, hcen y hy _ (hcA x hx y' hy'),
        hc.mul _ (hcA x hx y hy) _ (hcA x hx y' hy')])
    (fun x hx h0 y hy => by
      show v (x * y * x⁻¹ * y⁻¹) = 0
      rw [hVc x hx (h.mem_V_of_mem_V₁_of_mem_sup hx (h.mem_sup_of_S_eq_zero hK hc
        (mem_inf.mp hx).1 h0)) y hy, hc.v_one])
    (fun y hy h0 x hx => by
      show v (x * y * x⁻¹ * y⁻¹) = 0
      have hyV := h.mem_V_of_mem_V₁_of_mem_sup hy (h.mem_sup_of_S_eq_zero hK hc
        (mem_inf.mp hy).1 h0)
      rw [show x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ by group, hVc y hy hyV x hx, inv_one,
        hc.v_one])
  obtain ⟨c, hc'⟩ := bilinear_eq_mul_sqrt_of_equivariant hK (by have := h.start.two_le; omega) D
    hμ fun s s' => by
      obtain ⟨x, hx, rfl⟩ := h.S_surj_V₁ hK hc hμ hlam s
      obtain ⟨y, hy, rfl⟩ := h.S_surj_V₁ hK hc hμ hlam s'
      rw [← h.S_conj_d hK hc (mem_inf.mp hx).1, ← h.S_conj_d hK hc (mem_inf.mp hy).1,
        ← hD _ (h.conj_d_mem_V₁ hx) _ (h.conj_d_mem_V₁ hy), ← hD x hx y hy]
      rw [show d⁻¹ * x * d * (d⁻¹ * y * d) * (d⁻¹ * x * d)⁻¹ * (d⁻¹ * y * d)⁻¹ =
        d⁻¹ * (x * y * x⁻¹ * y⁻¹) * d by group, hc.conj _ (hcA x hx y hy)]
  obtain ⟨x₁, hx₁, hS₁⟩ := h.S_surj_V₁ hK hc hμ hlam 1
  have hc0 : c = 0 := by
    have e := (hD x₁ hx₁ x₁ hx₁).trans (hc' _ _)
    rw [show x₁ * x₁ * x₁⁻¹ * x₁⁻¹ = (1 : G) by group, hc.v_one, hS₁, one_mul, one_pow,
      mul_one] at e
    exact e.symm
  intro x hx y hy
  have e := (hD x hx y hy).trans (hc' _ _)
  rw [hc0, zero_mul] at e
  have e1 := hc.eq_one_of_v_eq_zero (hcA x hx y hy) e
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [e1, one_mul]

theorem sq_mul_t_mem_szA₁ (hμV : U₁ ≤ centralizer (V : Set G)) {w : G} (hw : w ∈ U₁) :
    (w * t) ^ 2 ∈ szA₁ (szT₁ L T) := by
  have hσV := h.comm_t_mem (h.U₁_le hw)
  have hw2 := h.sq_mem_V hw
  have hcw : ∀ r ∈ V, r * w = w * r := fun r hr => mem_centralizer_iff.mp (hμV hw) r hr
  have e1 : (w * t) ^ 2 = w ^ 2 * (w * t * w⁻¹ * t⁻¹)⁻¹ := by
    rw [h.sq_mul_t]
    calc w * (t * w * t⁻¹) = w * ((w * t * w⁻¹ * t⁻¹)⁻¹ * w) := by group
      _ = w * (w * (w * t * w⁻¹ * t⁻¹)⁻¹) := by rw [hcw _ (inv_mem hσV)]
      _ = w ^ 2 * (w * t * w⁻¹ * t⁻¹)⁻¹ := by rw [sq]; group
  have e2 : (w ^ 2) ^ 2 = (w * t * w⁻¹ * t⁻¹) ^ 2 := by
    rw [← h.comm_t_of_mem_V hw2, sq w, SzC1.comm_t_mul, ← hcw _ hσV, mul_inv_cancel_right, sq]
  refine h.omega _ (e1 ▸ mul_mem hw2 (inv_mem hσV)) ?_
  rw [e1, (Commute.mul_pow (h.comm _ hw2 _ (inv_mem hσV)) 2), e2, inv_pow, mul_inv_cancel]

theorem exists_nu (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w)
    (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) :
    ∃ ν : K, ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      v ((w * t) ^ 2) = ν * v ((w * t * w⁻¹ * t⁻¹) ^ 2 ^ k) := by
  have hcomm := h.V₁_comm' hK hc hμ hμV hlam
  have hdt : d * t = t * d := (mem_centralizer_singleton_iff.mp h.d_norm.2)
  exact exists_mul_of_hom hμ (M := U₁ ⊓ centralizer (szT₁ L T : Set G))
    (S := fun w => v ((w * t * w⁻¹ * t⁻¹) ^ 2 ^ k)) (φ := fun w => v ((w * t) ^ 2))
    (fun x hx y hy => h.S_mul hK hc (mem_inf.mp hx).1 (mem_inf.mp hy).1)
    (h.S_surj_V₁ hK hc hμ hlam)
    (fun x hx y hy => by
      show v ((x * y * t) ^ 2) = v ((x * t) ^ 2) + v ((y * t) ^ 2)
      have e : (x * y * t) ^ 2 = (x * t) ^ 2 * (y * t) ^ 2 := by
        rw [h.sq_mul_t, h.sq_mul_t, h.sq_mul_t]
        rw [show t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) by group]
        rw [show x * y * ((t * x * t⁻¹) * (t * y * t⁻¹)) =
          x * (y * (t * x * t⁻¹)) * (t * y * t⁻¹) by group,
          hcomm y hy _ (h.t_conj_mem_V₁ hx)]
        group
      rw [e, hc.mul _ (h.sq_mul_t_mem_szA₁ hK hc hμV (mem_inf.mp hx).1)
        _ (h.sq_mul_t_mem_szA₁ hK hc hμV (mem_inf.mp hy).1)])
    (fun w hw h0 => by
      show v ((w * t) ^ 2) = 0
      have hwV := h.mem_V_of_mem_V₁_of_mem_sup hw
        (h.mem_sup_of_S_eq_zero hK hc (mem_inf.mp hw).1 h0)
      rw [h.sq_mul_t, h.inv w hwV, mul_inv_cancel, hc.v_one])
    (fun w hw => ⟨d⁻¹ * w * d, h.conj_d_mem_V₁ hw, h.S_conj_d hK hc (mem_inf.mp hw).1, by
      show v ((d⁻¹ * w * d * t) ^ 2) = _
      have e : (d⁻¹ * w * d * t) ^ 2 = d⁻¹ * (w * t) ^ 2 * d := by
        have e1 : d⁻¹ * w * d * t = d⁻¹ * (w * t) * d := by
          rw [show d⁻¹ * (w * t) * d = d⁻¹ * w * (t * d) by group, ← hdt]; group
        rw [e1, show d⁻¹ * (w * t) * d = d⁻¹ * (w * t) * d⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv]
      rw [e, hc.conj _ (h.sq_mul_t_mem_szA₁ hK hc hμV (mem_inf.mp hw).1)]⟩)

theorem mem_V_of_sq_eq_one (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w)
    (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∃ w₀ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w₀ * t) ^ 2 ≠ 1) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) (h1 : (w * t) ^ 2 = 1) : w ∈ V := by
  obtain ⟨ν, hν'⟩ := h.exists_nu hK hc hμ hμV hlam
  obtain ⟨w₀, hw₀, hw₀1⟩ := hν
  have hν0 : ν ≠ 0 := by
    rintro rfl
    have e := hν' w₀ hw₀
    rw [zero_mul] at e
    exact hw₀1 (hc.eq_one_of_v_eq_zero (h.sq_mul_t_mem_szA₁ hK hc hμV (mem_inf.mp hw₀).1) e)
  have e := hν' w hw
  rw [h1, hc.v_one] at e
  have hS : v ((w * t * w⁻¹ * t⁻¹) ^ 2 ^ k) = 0 :=
    (mul_eq_zero.mp e.symm).resolve_left hν0
  exact h.mem_V_of_mem_V₁_of_mem_sup hw (h.mem_sup_of_S_eq_zero hK hc (mem_inf.mp hw).1 hS)

end Coords

theorem V₁_comm (h : U3C1Stage G L f t T d V U U₁ k)
    (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) :
    ∀ x ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), ∀ y ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      x * y = y * x := by
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := h.coords
  exact h.V₁_comm' hK hc hμ hμV hlam

theorem eq_of_le_normalizer_T₁ (h : U3C1Stage G L f t T d V U U₁ k)
    (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∃ w₀ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w₀ * t) ^ 2 ≠ 1) {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hUP : U ≤ P) (hPN : P ≤ normalizer (szT₁ L T : Set G)) : P = U := by
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := h.coords
  by_contra hne
  obtain ⟨z, hzP, hzN, hzU⟩ := SzC1.exists_mem_normalizer_of_lt hP2 hUP hne
  have hxU : z * t * z⁻¹ ∈ U := (mem_normalizer_iff.mp hzN t).mp h.t_mem_U
  have hwU₁ := (h.mem_or_mul_t_mem hxU).resolve_left (h.conj_not_mem_U₁ z)
  have hxC : z * t * z⁻¹ ∈ centralizer (szT₁ L T : Set G) := by
    refine mem_centralizer_iff.mpr fun y hy => ?_
    have hy' : z⁻¹ * y * z ∈ szT₁ L T := by
      simpa using (mem_normalizer_iff.mp (inv_mem (hPN hzP)) y).mp hy
    have e := h.t_comm hy'
    calc y * (z * t * z⁻¹) = z * ((z⁻¹ * y * z) * t) * z⁻¹ := by group
      _ = z * (t * (z⁻¹ * y * z)) * z⁻¹ := by rw [e]
      _ = z * t * z⁻¹ * y := by group
  have hw : z * t * z⁻¹ * t ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) :=
    mem_inf.mpr ⟨hwU₁, mul_mem hxC h.start.mem_centralizer_szT₁⟩
  have hw1 : (z * t * z⁻¹ * t * t) ^ 2 = 1 := by
    rw [mul_assoc (z * t * z⁻¹) t t, h.t_mul_self, mul_one, sq,
      show z * t * z⁻¹ * (z * t * z⁻¹) = z * (t * t) * z⁻¹ by group, h.t_mul_self, mul_one,
      mul_inv_cancel]
  have hwV := h.mem_V_of_sq_eq_one hK hc hμ hμV hlam hν hw hw1
  refine hzU (h.mem_U_of_comm_t_mem hP2 hUP hzP ?_)
  rw [h.t_inv]
  exact hwV

theorem reduction_nu (h : U3C1Stage G L f t T d V U U₁ k)
    (hfpf : U3C1TorusFpf L T d) :
    (¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U) ∧ U₁ ≤ centralizer (V : Set G) ∧
      U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) ∧
      ((∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) ∨
        ((∃ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 ≠ 1) ∧
          ∀ P : Subgroup G, IsPGroup 2 P → U ≤ P → P ≤ normalizer (szT₁ L T : Set G) →
            P = U)) := by
  obtain ⟨hU, hμV, hlam⟩ := h.reduction hfpf
  refine ⟨hU, hμV, hlam, ?_⟩
  by_cases hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1
  · exact Or.inl hν
  · push Not at hν
    exact Or.inr ⟨hν, fun P hP2 hUP hPN => h.eq_of_le_normalizer_T₁ hμV hlam hν hP2 hUP hPN⟩

theorem sq_sq_eq (h : U3C1Stage G L f t T d V U U₁ k)
    (hμV : U₁ ≤ centralizer (V : Set G)) {w : G} (hw : w ∈ U₁) :
    (w ^ 2) ^ 2 = (w * t * w⁻¹ * t⁻¹) ^ 2 := by
  have hσV := h.comm_t_mem (h.U₁_le hw)
  rw [← h.comm_t_of_mem_V (h.sq_mem_V hw), sq w, SzC1.comm_t_mul,
    ← mem_centralizer_iff.mp (hμV hw) _ hσV, mul_inv_cancel_right, sq]

theorem nextConf (h : U3C1Stage G L f t T d V U U₁ k)
    (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 = 1) :
    U₁ ⊓ centralizer (szT₁ L T : Set G) ≤ centralizer (szT₁ L T : Set G) ∧
    (∀ x ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), ∀ y ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      x * y = y * x) ∧
    Nat.card (U₁ ⊓ centralizer (szT₁ L T : Set G) : Subgroup G) = (2 ^ f) ^ (k + 1 + 1) ∧
    (∀ x ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), x ^ 2 = 1 → x ∈ szA₁ (szT₁ L T)) ∧
    (∀ x ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), x ^ 2 ^ (k + 1 + 1) = 1) ∧
    szA₁ (szT₁ L T) ≤ U₁ ⊓ centralizer (szT₁ L T : Set G) ∧
    (∀ x ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), t * x * t⁻¹ = x⁻¹) ∧
    d ∈ normalizer ((U₁ ⊓ centralizer (szT₁ L T : Set G) : Subgroup G) : Set G) ⊓
      normalizer (szT₁ L T : Set G) ⊓ centralizer ({t} : Set G) := by
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := h.coords
  have hk := h.one_le
  set V₁ := U₁ ⊓ centralizer (szT₁ L T : Set G) with hV₁
  have hcard : Nat.card V₁ = (2 ^ f) ^ (k + 1 + 1) := by
    have hrel1 : (szT₁ L T ⊔ V).relIndex U₁ = 2 ^ f := by
      have h1 := relIndex_mul_card (H := szT₁ L T ⊔ V) (K := U₁)
      rw [inf_of_le_left h.sup_le_U₁, h.card_sup, h.card_U₁] at h1
      have h2 : 2 ^ f * (2 ^ f) ^ (k + 3) = (2 ^ f) ^ (k + 4) := by ring
      exact Nat.eq_of_mul_eq_mul_right (by positivity) (h1.trans h2.symm)
    have hsup : V₁ ⊔ (szT₁ L T ⊔ V) = U₁ := le_antisymm
      (sup_le inf_le_left h.sup_le_U₁)
      (by
        conv_lhs => rw [hlam]
        exact sup_le (le_sup_left.trans le_sup_right) le_sup_left)
    have hinf : V₁ ⊓ (szT₁ L T ⊔ V) = V := le_antisymm
      (fun w hw => h.mem_V_of_mem_V₁_of_mem_sup (mem_inf.mp hw).1 (mem_inf.mp hw).2)
      (le_inf h.V_le_V₁ le_sup_right)
    have hrel2 := SzC1.relIndex_sup_eq_relIndex_inf (H := V₁) (K := szT₁ L T ⊔ V)
      ((inf_le_left.trans h.U₁_le).trans h.U_le_normalizer_sup)
    rw [hsup, hrel1, hinf] at hrel2
    have h3 := relIndex_mul_card (H := V) (K := V₁)
    rw [← hrel2, inf_of_le_left h.V_le_V₁, h.card] at h3
    rw [← h3]
    ring
  refine ⟨inf_le_right, h.V₁_comm hμV hlam, hcard, fun w hw hw2 => ?_, fun w hw => ?_,
    h.le.trans h.V_le_V₁, fun w hw => ?_, ⟨⟨mem_normalizer_of_forall_inv_mul_mul_mem
      fun w hw => h.conj_d_mem_V₁ hw, h.d_norm.1.2⟩, h.d_norm.2⟩⟩
  · have hσV := h.comm_t_mem (h.U₁_le (mem_inf.mp hw).1)
    have hσ2 : (w * t * w⁻¹ * t⁻¹) ^ 2 = 1 := by
      rw [← h.sq_sq_eq hμV (mem_inf.mp hw).1, hw2, one_pow]
    have hS : v ((w * t * w⁻¹ * t⁻¹) ^ 2 ^ k) = 0 := by
      obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [hj, pow_succ', pow_mul, hσ2, one_pow, hc.v_one]
    exact h.omega w (h.mem_V_of_mem_V₁_of_mem_sup hw
      (h.mem_sup_of_S_eq_zero hK hc (mem_inf.mp hw).1 hS)) hw2
  · rw [pow_succ', pow_mul]
    exact h.pow _ (h.sq_mem_V (mem_inf.mp hw).1)
  · have e := hν w hw
    rw [h.sq_mul_t] at e
    exact eq_inv_of_mul_eq_one_right e

end U3C1Stage

end CFSG.SeitzReduction.RankOne
