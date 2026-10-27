module

public import CFSG.GH74.Uniqueness.SU.SU13TB2Inv
public import CFSG.GH74.Uniqueness.SU.SU13Data

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB CFSG.RankThree.Asc83Table

variable {G : Type} [Group G] [Finite G]

theorem isSylowIn_of_central_involution {X T : Subgroup G} {z : G}
    (hT : IsSylowIn (X ⊓ centralizer ({z} : Set G)) T) (hzT : z ∈ T)
    (hzc : ∀ s ∈ T, s * z = z * s)
    (hcen : ∀ y ∈ T, orderOf y = 2 → (∀ s ∈ T, s * y = y * s) → y = z) (hz : orderOf z = 2) :
    IsSylowIn X T := by
  refine isSylowIn_of_normalizer_le_centralizer hT fun g _ hg => ?_
  have hgz : g * z * g⁻¹ ∈ T := (mem_normalizer_iff.mp hg z).mp hzT
  have hcomm : ∀ s ∈ T, s * (g * z * g⁻¹) = (g * z * g⁻¹) * s := by
    intro s hs
    have hs' : g⁻¹ * s * g ∈ T := by
      have := (mem_normalizer_iff.mp (inv_mem hg) s).mp hs
      simp [mul_assoc] at this ⊢
      exact this
    have h1 := hzc _ hs'
    calc s * (g * z * g⁻¹) = g * ((g⁻¹ * s * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
      _ = (g * z * g⁻¹) * s := by group
  have := hcen _ hgz (by rw [orderOf_conj_eq]; exact hz) hcomm
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

structure Lem232 (z : G) (e : Elts G z) : Prop where
  a : ∀ g : G, g * e.s₁ = e.s₁ * g → ∃ c k : G, c * e.s₁ = e.s₁ * c ∧ c * z = z * c ∧
    k ∈ oc (centralizer ({e.s₁} : Set G)) ∧ g = c * k
  d12 : ¬ GConj e.s₁ e.s₂
  d13 : ¬ GConj e.s₁ e.s₃
  d23 : ¬ GConj e.s₂ e.s₃
  k₁ : ∃ k : G, k * e.s₂ = e.s₂ * k ∧ k * z * k⁻¹ = e.t
  k₂ : ∃ k : G, k * e.s₂ = e.s₂ * k ∧ k * z * k⁻¹ = e.t * z
  R : ∃ R : Subgroup G, IsSylowIn (centralizer ({e.s₂} : Set G)) R ∧ z ∈ R ∧ ∀ r ∈ R, r * z = z * r
  one : ∀ u v : G, u * e.s₂ = e.s₂ * u → v * e.s₂ = e.s₂ * v → orderOf u = 2 → orderOf v = 2 →
    ∃ c : G, c * e.s₂ = e.s₂ * c ∧ c * u * c⁻¹ = v

omit [Finite G] in
theorem orderOf_mul_eq_two_of_commute {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a * b = b * a) (hne : a ≠ b) : orderOf (a * b) = 2 := by
  have ha2 : a * a = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two ha
  have hb2 : b * b = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hb
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two]
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, mul_one]
  · intro h
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    apply hne
    rw [this]
    exact (inv_eq_of_mul_eq_one_right hb2).symm ▸ rfl

theorem lemma232_ten [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2)
    (e : Elts G z) (f : FPart10 z e) (p3 : P3Part z e) (hm : MPart10 z e) : Lem232 z e := by
  have hq : IsSylowIn (centralizer ({e.s₁} : Set G)) f.T₁ :=
    isSylowIn_of_unique_involution f.T₁_syl f.T₁_z hz f.T₁_uniq
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  have hz2 : z * z = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hz
  have hcard1 : 2 < Nat.card f.T₁ := by
    obtain ⟨k, hk, ⟨φ⟩⟩ := f.T₁_quat
    have : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hu3 : ∀ y ∈ zpowers z, orderOf y = 2 → y = z := by
    rintro y ⟨n, rfl⟩ hy
    beta_reduce at hy ⊢
    have h1 : z ^ n = z ^ (n % (orderOf z : ℤ)) := (zpow_mod_orderOf z n).symm
    rw [hz] at h1
    have h2 : n % ((2 : ℕ) : ℤ) = 0 ∨ n % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases h2 with h2 | h2
    · rw [h1, h2, zpow_zero, orderOf_one] at hy
      exact absurd hy (by norm_num)
    · rw [h1, h2, zpow_one]
  have h3 : IsSylowIn (centralizer ({e.s₃} : Set G)) (zpowers z) :=
    isSylowIn_of_unique_involution p3.syl (mem_zpowers z) hz hu3
  have hcard3 : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hz]
  have hbs := eq_oc_mul_centralizer_of_quaternion hz hq f.T₁_z f.T₁_quat
  have hd := not_gconj_of_sylow (s₁ := e.s₁) (s₂ := e.s₂) (s₃ := e.s₃) (z := z) (t := e.t) hq f.T₁_uniq
    hcard1 h3 hu3 hcard3 e.s₂_comm.symm e.t_s₂ hz e.t_ord e.t_ne.symm e.t_comm.symm
  have hne12 : ¬ GConj e.s₂ e.s₁ := fun h => hd.1 h.symm
  have hne23 : ¬ GConj e.s₂ e.s₃ := hd.2.2
  have hk₁ : ∃ k : G, k * e.s₂ = e.s₂ * k ∧ k * z * k⁻¹ = e.t :=
    exists_centralizer_conj hz inferInstance hnab e.class3 e.class2 hne12 hne23 e.s₂_ord e.t_comm e.t_ord
      e.t_ne e.t_s₂
  have htz2 : orderOf (e.t * z) = 2 :=
    orderOf_mul_eq_two_of_commute e.t_ord hz e.t_comm e.t_ne
  have ht1 : e.t ≠ 1 := by
    intro h; have := e.t_ord; rw [h, orderOf_one] at this; exact absurd this (by norm_num)
  have hw : e.t * z * z = z * (e.t * z) := by
    calc e.t * z * z = e.t * (z * z) := by group
      _ = e.t := by rw [hz2, mul_one]
      _ = z * (e.t * z) := by rw [← mul_assoc, ← e.t_comm, mul_assoc, hz2, mul_one]
  have hws : e.t * z * e.s₂ = e.s₂ * (e.t * z) := by
    calc e.t * z * e.s₂ = e.t * (z * e.s₂) := by group
      _ = e.t * (e.s₂ * z) := by rw [← e.s₂_comm]
      _ = (e.t * e.s₂) * z := by group
      _ = (e.s₂ * e.t) * z := by rw [e.t_s₂]
      _ = e.s₂ * (e.t * z) := by group
  have hk₂ : ∃ k : G, k * e.s₂ = e.s₂ * k ∧ k * z * k⁻¹ = e.t * z :=
    exists_centralizer_conj hz inferInstance hnab e.class3 e.class2 hne12 hne23 e.s₂_ord hw htz2
      (fun h => ht1 (by simpa using h)) hws
  set C : Subgroup G := centralizer ({e.s₂} : Set G) with hC
  set M : Subgroup G := C ⊓ centralizer ({z} : Set G) with hM
  have hMC : M ≤ C := inf_le_left
  have hzC : z ∈ C := mem_centralizer_singleton_iff.mpr e.s₂_comm.symm
  have htC : e.t ∈ C := mem_centralizer_singleton_iff.mpr e.t_s₂
  have hzM : z ∈ M := mem_inf.mpr ⟨hzC, mem_centralizer_singleton_iff.mpr rfl⟩
  have htM : e.t ∈ M := mem_inf.mpr ⟨htC, mem_centralizer_singleton_iff.mpr e.t_comm⟩
  have hzc : ∀ m ∈ M, m * z = z * m := fun m hm => mem_centralizer_singleton_iff.mp (mem_inf.mp hm).2
  obtain ⟨fM⟩ := hm.gl
  obtain ⟨R, hRM, hzR⟩ := exists_isSylowIn_ge (X := M) (K := zpowers z)
    ((zpowers_le).mpr hzM) (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz]; norm_num))
  have hzR' : z ∈ R := hzR (mem_zpowers z)
  have hRz : ∀ r ∈ R, r * z = z * r := fun r hr => hzc r (hRM.1 hr)
  have hRC : IsSylowIn C R :=
    isSylowIn_of_central_involution hRM hzR' hRz
      (fun y hy hy2 hyc => eq_of_central_sylow fM hzM hz hzc hm.card hRM hy hy2 hyc) hz
  have cl : ∀ u : G, u * e.s₂ = e.s₂ * u → orderOf u = 2 →
      ∃ c : G, c * e.s₂ = e.s₂ * c ∧ c * u * c⁻¹ = z := by
    intro u hu hu2
    have huC : u ∈ C := mem_centralizer_singleton_iff.mpr hu
    have hK : zpowers u ≤ C := (zpowers_le).mpr huC
    have hKp : IsPGroup 2 (zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2]; norm_num)
    obtain ⟨c₀, hc₀C, hc₀⟩ := hRC.exists_conj_le hK hKp
    have hu'R : c₀⁻¹ * u * c₀ ∈ R :=
      hc₀ (mem_conjSub.mpr (by simp [mul_assoc]))
    have hu'M : c₀⁻¹ * u * c₀ ∈ M := hRM.1 hu'R
    have hu'2 : orderOf (c₀⁻¹ * u * c₀) = 2 := by
      have := orderOf_conj_eq (a := u) c₀⁻¹
      rw [inv_inv] at this
      rw [this]; exact hu2
    by_cases hz' : c₀⁻¹ * u * c₀ = z
    · refine ⟨c₀⁻¹, mem_centralizer_singleton_iff.mp (C.inv_mem hc₀C), ?_⟩
      simpa using hz'
    · obtain ⟨m, hmM, hmt⟩ := exists_conj_of_involutions fM hzM hz hzc hu'M htM hu'2 e.t_ord hz' e.t_ne
      obtain ⟨k, hkC, hk⟩ := hk₁
      have hkC' : k ∈ C := mem_centralizer_singleton_iff.mpr hkC
      refine ⟨k⁻¹ * m * c₀⁻¹, mem_centralizer_singleton_iff.mp
        (C.mul_mem (C.mul_mem (C.inv_mem hkC') (hMC hmM)) (C.inv_mem hc₀C)), ?_⟩
      calc k⁻¹ * m * c₀⁻¹ * u * (k⁻¹ * m * c₀⁻¹)⁻¹ = k⁻¹ * (m * (c₀⁻¹ * u * c₀) * m⁻¹) * k := by group
        _ = k⁻¹ * e.t * k := by rw [hmt]
        _ = z := by rw [← hk]; group
  have hone : ∀ u v : G, u * e.s₂ = e.s₂ * u → v * e.s₂ = e.s₂ * v → orderOf u = 2 → orderOf v = 2 →
      ∃ c : G, c * e.s₂ = e.s₂ * c ∧ c * u * c⁻¹ = v := by
    intro u v hu hv hu2 hv2
    obtain ⟨cu, hcu, hzu⟩ := cl u hu hu2
    obtain ⟨cv, hcv, hzv⟩ := cl v hv hv2
    refine ⟨cv⁻¹ * cu, ?_, ?_⟩
    · have hcvinv : cv⁻¹ * e.s₂ = e.s₂ * cv⁻¹ := (Commute.inv_left (show Commute cv e.s₂ from hcv)).eq
      calc cv⁻¹ * cu * e.s₂ = cv⁻¹ * (cu * e.s₂) := by group
        _ = cv⁻¹ * (e.s₂ * cu) := by rw [hcu]
        _ = (cv⁻¹ * e.s₂) * cu := by group
        _ = (e.s₂ * cv⁻¹) * cu := by rw [hcvinv]
        _ = e.s₂ * (cv⁻¹ * cu) := by group
    · calc cv⁻¹ * cu * u * (cv⁻¹ * cu)⁻¹ = cv⁻¹ * (cu * u * cu⁻¹) * cv := by group
        _ = cv⁻¹ * z * cv := by rw [hzu]
        _ = v := by rw [← hzv]; group
  refine ⟨?_, hd.1, hd.2.1, hd.2.2, hk₁, hk₂, ⟨R, hRC, hzR', hRz⟩, hone⟩
  intro g hg
  obtain ⟨c, hc, k, hk, hgck⟩ := hbs g (mem_centralizer_singleton_iff.mpr hg)
  obtain ⟨hcX, hcz⟩ := mem_inf.mp hc
  exact ⟨c, k, mem_centralizer_singleton_iff.mp hcX, mem_centralizer_singleton_iff.mp hcz, hk, hgck⟩

end CFSG.GH74.Uniqueness.SU.SU13
