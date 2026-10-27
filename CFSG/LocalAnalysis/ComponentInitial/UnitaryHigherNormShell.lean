module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherHermitian

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_norm_eq (h : UnitaryFieldData p f K) {c : K} (hc : h.bar c = c) :
    ∃ l : K, h.norm l = c := by
  obtain ⟨l, hl⟩ := h.normHom_surjective ⟨c, hc⟩
  exact ⟨l, by simpa using congrArg Subtype.val hl⟩

theorem exists_vector_of_norm (h : UnitaryFieldData p f K) {W : Type*} [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] {B : W →ₛₗ[h.bar] W →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (hW : 0 < Module.finrank K W) {c : K} (hc : h.bar c = c) :
    ∃ x : W, B x x = c := by
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis hB hBl
  obtain ⟨l, hl⟩ := exists_norm_eq h hc
  refine ⟨l • e ⟨0, hW⟩, ?_⟩
  simp only [map_smulₛₗ, LinearMap.smul_apply, he, ↓reduceIte, smul_eq_mul, mul_one]
  rw [← hl, UnitaryFieldData.norm, RingHom.id_apply, mul_comm]

theorem finrank_ker_of_nonisotropic [FiniteDimensional K V] {σ : K →+* K}
    {B : V →ₛₗ[σ] V →ₗ[K] K} {u : V} (hu : B u u ≠ 0) :
    Module.finrank K (LinearMap.ker (B u)) + 1 = Module.finrank K V := by
  have hsurj : Function.Surjective (B u) := fun c =>
    ⟨(c / B u u) • u, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hu]⟩
  have := LinearMap.finrank_range_add_finrank_ker (B u)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at this
  omega

theorem linearIndependent_of_orth {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K} {y z : V}
    (hy : B y y ≠ 0) (hz : z ≠ 0) (hyz : B y z = 0) : LinearIndependent K ![y, z] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (B y) hst
  rw [map_add, map_smul, map_smul, hyz, smul_zero, add_zero, map_zero, smul_eq_mul,
    mul_eq_zero] at h1
  have hs : s = 0 := h1.resolve_right hy
  subst hs
  rw [zero_smul, zero_add, smul_eq_zero] at hst
  exact ⟨rfl, hst.resolve_right hz⟩

theorem exists_common_neighbor (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hd : 4 ≤ Module.finrank K V) {a : K} (haF : h.bar a = a) (ha0 : a ≠ 0) {u v : V}
    (hli : LinearIndependent K ![u, v]) (hu : B u u = a) :
    ∃ w : V, B w w = a ∧ B u w = a ∧ B w v = a := by
  set γ := B u v with hγ
  set r := v - (γ / a) • u with hr
  set β := a - h.bar γ with hβ
  have hur : B u r = 0 := by
    rw [hr, map_sub, map_smul, smul_eq_mul, hu, div_mul_cancel₀ _ ha0, ← hγ, sub_self]
  have hru : B r u = 0 := by rw [← hB.eq u r, hur, map_zero]
  have hr0 : r ≠ 0 := fun h0 => by
    rw [LinearIndependent.pair_iff] at hli
    have := hli (-(γ / a)) 1 (by rw [neg_smul, one_smul, neg_add_eq_sub, ← hr, h0])
    exact one_ne_zero this.2
  have hrrF : h.bar (B r r) = B r r := hB.eq r r
  suffices hw : ∃ w : V, B w w = a ∧ B u w = a ∧ B r w = β by
    obtain ⟨w, hww, huw, hrw⟩ := hw
    have hvw : B v w = a := by
      have hv' : v = r + (γ / a) • u := by rw [hr, sub_add_cancel]
      rw [hv', map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, hrw, huw, hβ,
        smul_eq_mul, map_div₀, haF, div_mul_cancel₀ _ ha0, sub_add_cancel]
    exact ⟨w, hww, huw, by rw [← hB.eq v w, hvw, haF]⟩
  have hU₀ := separatingLeft_ker_of_nonisotropic h hB hBl (show B u u ≠ 0 by rw [hu]; exact ha0)
  have hdimU₀ := finrank_ker_of_nonisotropic (show B u u ≠ 0 by rw [hu]; exact ha0)
  set U₀ := LinearMap.ker (B u) with hU₀def
  have hr' : r ∈ U₀ := hur
  have hr'0 : (⟨r, hr'⟩ : U₀) ≠ 0 := fun h0 => hr0 (congrArg Subtype.val h0)
  by_cases hρ : B r r = 0
  ·
    obtain ⟨⟨s, hrs, hss⟩, -⟩ := hermitian_hyperbolic_splitting h (hB.domRestrict U₀) hU₀ hr'0 hρ
    have hus : B u s = 0 := s.2
    have hsu : B s u = 0 := by rw [← hB.eq u s, hus, map_zero]
    have hrs' : B r s = 1 := hrs
    have hss' : B s s = 0 := hss
    refine ⟨u + β • (s : V), ?_, ?_, ?_⟩
    · simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, hu, hus, hsu, hss', mul_zero, add_zero]
    · rw [map_add, map_smul, hu, hus, smul_zero, add_zero]
    · rw [map_add, map_smul, hru, hrs', smul_eq_mul, mul_one, zero_add]
  ·
    have hT := separatingLeft_ker_of_nonisotropic h (hB.domRestrict U₀) hU₀ (u := ⟨r, hr'⟩) hρ
    have hdimT := finrank_ker_of_nonisotropic (B := B.domRestrict₁₂ U₀ U₀) (u := ⟨r, hr'⟩) hρ
    set c := -(h.norm β) / B r r with hc
    have hcF : h.bar c = c := by
      rw [hc, map_div₀, map_neg, hrrF,
        (UnitaryFieldData.mem_fixedField h).mp (h.norm_mem_fixedField β)]
    obtain ⟨e, he⟩ := exists_vector_of_norm h ((hB.domRestrict U₀).domRestrict _) hT
      (by omega) hcF
    have hue : B u (e : V) = 0 := (e : U₀).2
    have hre : B r (e : V) = 0 := e.2
    have heu : B (e : V) u = 0 := by rw [← hB.eq u, hue, map_zero]
    have her : B (e : V) r = 0 := by rw [← hB.eq r, hre, map_zero]
    have hee : B (e : V) (e : V) = c := he
    refine ⟨u + (β / B r r) • r + (e : V), ?_, ?_, ?_⟩
    · have hN : (β / B r r) * (h.bar (β / B r r) * B r r) = h.norm β / B r r := by
        rw [map_div₀, hrrF, UnitaryFieldData.norm]
        field_simp
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, hu, hur, hru, hue, hre, heu, her, hee, mul_zero, add_zero, zero_add,
        RingHom.id_apply]
      rw [hN, hc]
      ring
    · rw [map_add, map_add, map_smul, hu, hur, hue, smul_zero, add_zero, add_zero]
    · rw [map_add, map_add, map_smul, hru, hre, smul_eq_mul, div_mul_cancel₀ _ hρ, zero_add,
        add_zero]

theorem norm_shell_graph_connected (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hd : 4 ≤ Module.finrank K V) {a : K} (haF : h.bar a = a) (ha0 : a ≠ 0) {u v : V}
    (hu : B u u = a) (hv : B v v = a) :
    (∃ m ≤ 4, ∃ w : Fin (m + 1) → V, w 0 = u ∧ w (Fin.last m) = v ∧
      (∀ i, B (w i) (w i) = a) ∧ ∀ i : Fin m, B (w i.castSucc) (w i.succ) = a) ∧
    (LinearIndependent K ![u, v] → ∃ m ≤ 2, ∃ w : Fin (m + 1) → V, w 0 = u ∧
      w (Fin.last m) = v ∧ (∀ i, B (w i) (w i) = a) ∧
      ∀ i : Fin m, B (w i.castSucc) (w i.succ) = a) := by
  have hind : LinearIndependent K ![u, v] → ∃ m ≤ 2, ∃ w : Fin (m + 1) → V, w 0 = u ∧
      w (Fin.last m) = v ∧ (∀ i, B (w i) (w i) = a) ∧
      ∀ i : Fin m, B (w i.castSucc) (w i.succ) = a := by
    intro hli
    obtain ⟨w, hww, huw, hwv⟩ := exists_common_neighbor h hB hBl hd haF ha0 hli hu
    refine ⟨2, le_rfl, ![u, w, v], rfl, rfl, fun i => ?_, fun i => ?_⟩
    · fin_cases i <;> simp [hu, hww, hv]
    · fin_cases i <;> simp [huw, hwv]
  refine ⟨?_, hind⟩
  by_cases hli : LinearIndependent K ![u, v]
  · obtain ⟨m, hm, w, hw⟩ := hind hli
    exact ⟨m, hm.trans (by norm_num), w, hw⟩
  by_cases huv : u = v
  · subst huv
    exact ⟨0, by norm_num, ![u], rfl, rfl, fun i => by fin_cases i; simpa using hu,
      fun i => i.elim0⟩
  have hu0 : B u u ≠ 0 := by rw [hu]; exact ha0
  obtain ⟨c, hvc⟩ : ∃ c : K, v = c • u := by
    rw [LinearIndependent.pair_iff] at hli
    push Not at hli
    obtain ⟨s, t, hst, hne⟩ := hli
    have ht : t ≠ 0 := fun ht => by
      subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      exact hne (hst.resolve_right fun h0 => hu0 (by simp [h0])) rfl
    refine ⟨-(t⁻¹ * s), ?_⟩
    rw [neg_smul, mul_smul, ← smul_neg, ← eq_neg_of_add_eq_zero_right hst, smul_smul,
      inv_mul_cancel₀ ht, one_smul]
  have hU₀ := separatingLeft_ker_of_nonisotropic h hB hBl hu0
  have hdimU₀ := finrank_ker_of_nonisotropic hu0
  obtain ⟨x, hx⟩ := exists_vector_of_norm h (hB.domRestrict _) hU₀ (by omega) haF
  have hux : B u (x : V) = 0 := x.2
  have hx' : B (x : V) (x : V) = a := hx
  have hx0 : (x : V) ≠ 0 := fun h0 => ha0 (by rw [← hx', h0]; simp)
  have hv0 : B v v ≠ 0 := by rw [hv]; exact ha0
  have hvx : B v (x : V) = 0 := by
    rw [hvc, map_smulₛₗ, LinearMap.smul_apply, hux, smul_zero]
  have hli₁ : LinearIndependent K ![u, (x : V)] := linearIndependent_of_orth hu0 hx0 hux
  have hli₂ : LinearIndependent K ![(x : V), v] := by
    have := linearIndependent_of_orth hv0 hx0 hvx
    rw [LinearIndependent.pair_iff] at this ⊢
    intro s t hst
    obtain ⟨h1, h2⟩ := this t s (by rw [add_comm]; exact hst)
    exact ⟨h2, h1⟩
  obtain ⟨w₁, hw₁, huw₁, hw₁x⟩ := exists_common_neighbor h hB hBl hd haF ha0 hli₁ hu
  obtain ⟨w₂, hw₂, hxw₂, hw₂v⟩ := exists_common_neighbor h hB hBl hd haF ha0 hli₂ hx'
  refine ⟨4, le_rfl, ![u, w₁, x, w₂, v], rfl, rfl, fun i => ?_, fun i => ?_⟩
  · fin_cases i <;> simp [hu, hw₁, hx', hw₂, hv]
  · fin_cases i <;> simp [huw₁, hw₁x, hxw₂, hw₂v]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
