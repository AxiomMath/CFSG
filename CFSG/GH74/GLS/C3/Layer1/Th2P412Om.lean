module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412Sw
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.Th2.P43f

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.Th2 Equiv Equiv.Perm
  CFSG.LieType.SteinbergBR.SmallAlt

variable {G : Type} [Group G]

@[expose] def OmegaX (x v u : G) : Prop := u * u = 1 ∧ u * x = x * u ∧ IsConj v u ∧ IsConj x (u * x)

theorem omegaX_conj {x v g u : G} (hg : g * x = x * g) (hu : OmegaX x v u) :
    OmegaX x v (g * u * g⁻¹) := by
  obtain ⟨hu2, hux, hvu, hxux⟩ := hu
  have hgx : g⁻¹ * x * g = x := by
    calc g⁻¹ * x * g = g⁻¹ * (x * g) := by group
      _ = g⁻¹ * (g * x) := by rw [hg]
      _ = x := by group
  have e : g * u * g⁻¹ * x = g * (u * x) * g⁻¹ := by
    calc g * u * g⁻¹ * x = g * u * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [hgx]; group
  refine ⟨?_, ?_, hvu.trans (isConj_iff.2 ⟨g, rfl⟩), ?_⟩
  · calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  · rw [e, hux]
    calc g * (x * u) * g⁻¹ = (g * x * g⁻¹) * (g * u * g⁻¹) := by group
      _ = x * (g * u * g⁻¹) := by
        congr 1
        rw [hg]; group
  · rw [e]
    exact hxux.trans (isConj_iff.2 ⟨g, rfl⟩)

theorem omegaX_pull {x v s t g : G} (hg : g * x * g⁻¹ = s) (ht2 : t * t = 1) (hts : t * s = s * t)
    (htv : IsConj v t) (hxst : IsConj x (s * t)) : OmegaX x v (g⁻¹ * t * g) := by
  have hx : x = g⁻¹ * s * g := by rw [← hg]; group
  refine ⟨?_, ?_, htv.trans (isConj_iff.2 ⟨g⁻¹, by group⟩), ?_⟩
  · calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht2]; group
  · rw [hx]
    calc g⁻¹ * t * g * (g⁻¹ * s * g) = g⁻¹ * (t * s) * g := by group
      _ = g⁻¹ * (s * t) * g := by rw [hts]
      _ = g⁻¹ * s * g * (g⁻¹ * t * g) := by group
  · have e : g⁻¹ * t * g * x = g⁻¹ * (s * t) * g := by
      rw [hx, ← hts]; group
    rw [e]
    exact hxst.trans (isConj_iff.2 ⟨g⁻¹, by group⟩)

namespace Frame

variable {x : G} {K T S : Subgroup G} {a z : G} {psi : G → Perm (Fin 7)}

variable (F : Frame x K T S a z psi)

include F

theorem zx_comm [Finite G] : z * x = x * z := F.core.comm_P_conj z F.z_mem x F.x_mem

theorem v_sq [Finite G] : (z * x) * (z * x) = 1 := by
  calc (z * x) * (z * x) = z * (x * z) * x := by group
    _ = z * (z * x) * x := by rw [← F.zx_comm]
    _ = (z * z) * (x * x) := by group
    _ = 1 := by rw [F.z_sq, F.x_sq, one_mul]

theorem v_ne [Finite G] : z * x ≠ 1 := by
  intro h
  have hxz : x = z := by
    have : x = z⁻¹ := by
      calc x = z⁻¹ * (z * x) := by group
        _ = z⁻¹ := by rw [h, mul_one]
    rw [this]
    exact inv_eq_of_mul_eq_one_right F.z_sq
  have : x ∈ (T ⊓ K) ⊓ conjugate (T ⊓ K) a := ⟨hxz ▸ F.z_mem, F.x_mem⟩
  rw [F.core.P_inf_conj, Subgroup.mem_bot] at this
  exact F.x_ne this

theorem exists_K_conj_z [Finite G] {u : G} (hu : u ∈ T ⊓ K) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ k ∈ K, k * z * k⁻¹ = u := by
  obtain ⟨k, hkK, hk⟩ := k_rule F.K_le F.K_norm psi F.psi_mul F.psi_K_odd F.psi_surj
    (F.P_le_C hu) (F.P_le_C F.z_mem) hu2 F.z_sq
    (K.mul_mem F.z_mem.2 (K.inv_mem hu.2))
    (by rw [F.supp_psi_P hu hu2 hu1, F.supp_psi_P F.z_mem F.z_sq F.z_ne])
  refine ⟨k⁻¹, K.inv_mem hkK, ?_⟩
  rw [← hk]
  group

theorem omega_T [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {u : G} (huT : u ∈ T) (hu : OmegaX x (z * x) u) :
    ∃ p ∈ T ⊓ K, p * p = 1 ∧ p ≠ 1 ∧ u = p * x := by
  obtain ⟨hu2, -, hvu, hxux⟩ := hu
  have hxv : ¬ IsConj x (z * x) :=
    F.not_isConj_v_of_Q hG hs e7 hP2 hQ4 ⟨F.x_mem_T, F.x_mem_CxK⟩ F.x_sq F.x_ne
  have hR := F.R_four hG hs e7 hP2 hQ4
  have hzR : z ∈ conjugate (T ⊓ CxK x K) a⁻¹ := F.z_mem_four hR
  have hu' : u ∈ (T ⊓ K) ⊔ conjugate (T ⊓ K) a := F.T_eq ▸ huT
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute F.core.comm_P_conj hu'
  have hcomm : p * q = q * p := F.core.comm_P_conj p hp q hq
  have hsq : (p * p) * (q * q) = 1 * 1 := by
    calc (p * p) * (q * q) = p * (p * q) * q := by group
      _ = p * (q * p) * q := by rw [hcomm]
      _ = (p * q) * (p * q) := by group
      _ = 1 * 1 := by rw [← hpq, hu2]; simp
  obtain ⟨hp2, hq2⟩ := eq_of_mul_eq_of_inf_eq_bot F.core.P_inf_conj
    (Subgroup.mul_mem _ hp hp) (one_mem _) (Subgroup.mul_mem _ hq hq) (one_mem _) hsq
  have hwP : a * q * a⁻¹ ∈ T ⊓ K := mem_conjugate_iff'.1 hq
  have hw2 : (a * q * a⁻¹) * (a * q * a⁻¹) = 1 := by
    calc (a * q * a⁻¹) * (a * q * a⁻¹) = a * (q * q) * a⁻¹ := by group
      _ = 1 := by rw [hq2]; group
  have hqw : q = a⁻¹ * (a * q * a⁻¹) * a := by group
  have hut : u = tt a p (a * q * a⁻¹) := by
    unfold tt
    rw [← hqw]
    exact hpq
  generalize a * q * a⁻¹ = w at hwP hw2 hut
  by_cases hp1 : p = 1
  · exfalso
    by_cases hw1 : w = 1
    · have hu1 : u = 1 := by rw [hut, hp1, hw1]; unfold tt; group
      rw [hu1] at hvu
      exact F.v_ne (isConj_one_left.1 hvu)
    · have h1 : IsConj x u := by
        have : u = a⁻¹ * w * a := by rw [hut, hp1]; unfold tt; group
        rw [this]
        exact (F.isConj_conj_x hwP hw2 hw1).symm
      exact hxv (h1.trans hvu.symm)
  by_cases hw1 : w = 1
  · exfalso
    have h1 : IsConj x u := by
      have : u = p := by rw [hut, hw1]; unfold tt; group
      rw [this]
      exact (F.isConj_P_x hp hp2 hp1).symm
    exact hxv (h1.trans hvu.symm)
  by_cases hwz : w = z
  · refine ⟨p, hp, hp2, hp1, ?_⟩
    rw [hut, hwz]
    unfold tt
    rw [F.a_z_a]
  · exfalso
    have hw₂P : w * z ∈ T ⊓ K := Subgroup.mul_mem _ hwP F.z_mem
    have hwzc : w * z = z * w := F.z_central w hwP
    have hw₂sq : (w * z) * (w * z) = 1 := by
      calc (w * z) * (w * z) = w * (z * w) * z := by group
        _ = w * (w * z) * z := by rw [← hwzc]
        _ = (w * w) * (z * z) := by group
        _ = 1 := by rw [hw2, F.z_sq, one_mul]
    have hw₂1 : w * z ≠ 1 := by
      intro h
      apply hwz
      rw [mul_eq_one_iff_eq_inv.1 h]
      exact inv_eq_of_mul_eq_one_right F.z_sq
    have hux : u * x = tt a p (w * z) := by
      rw [hut]
      unfold tt
      rw [← F.a_z_a]
      group
    by_cases hpR : p ∈ conjugate (T ⊓ CxK x K) a⁻¹
    · have h1 : IsConj (tt a p (w * z)) (z * x) :=
        F.isConj_tt_v_of_left hp hw₂P hp2 hw₂sq hp1 hw₂1 (F.psi_R hpR)
      rw [← hux] at h1
      exact hxv (hxux.trans h1)
    by_cases hwzR : w * z ∈ conjugate (T ⊓ CxK x K) a⁻¹
    · have h1 : IsConj (tt a p (w * z)) (z * x) :=
        F.isConj_tt_v_of_right hp hw₂P hp2 hw₂sq hp1 hw₂1 (F.psi_R hwzR)
      rw [← hux] at h1
      exact hxv (hxux.trans h1)
    · have hwR : w ∉ conjugate (T ⊓ CxK x K) a⁻¹ := fun hwR =>
        hwzR (Subgroup.mul_mem _ hwR hzR)
      have h1 : IsConj (tt a p w) x :=
        F.isConj_tt_x_of_not_mem_R hG hs e7 hP2 hQ4 hp hwP hp2 hw2 hpR hwR
      rw [← hut] at h1
      exact hxv (h1.symm.trans hvu.symm)

theorem omega_conj [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {u : G} (hu : OmegaX x (z * x) u) :
    ∃ m ∈ centralizer ({x} : Set G), m * (z * x) * m⁻¹ = u := by
  have huC : u ∈ centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hu.2.1
  have hup : IsPGroup 2 ↥(zpowers u) := (isElementaryAbelian_zpowers_of_sq hu.1).isPGroup 2 _
  obtain ⟨g, hgC, hgW⟩ := Th2.exists_cj_le_of_isSylowOf hs.setup.sylowT (zpowers_le.2 huC) hup
  have hmem : g * u * g⁻¹ ∈ T := by
    refine hgW ((mem_cj_iff g _ _).2 ?_)
    have e : g⁻¹ * (g * u * g⁻¹) * g = u := by group
    rw [e]
    exact mem_zpowers u
  have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 hgC
  obtain ⟨p, hp, hp2, hp1, hpu⟩ := F.omega_T hG hs e7 hP2 hQ4 hmem (omegaX_conj hgx hu)
  obtain ⟨k, hkK, hk⟩ := F.exists_K_conj_z hp hp2 hp1
  have hkx : k * x = x * k := Subgroup.mem_centralizer_singleton_iff.1 (F.K_le hkK)
  have hkxk : k * x * k⁻¹ = x := by rw [hkx]; group
  refine ⟨g⁻¹ * k, (centralizer ({x} : Set G)).mul_mem ((centralizer ({x} : Set G)).inv_mem hgC)
    (F.K_le hkK), ?_⟩
  calc g⁻¹ * k * (z * x) * (g⁻¹ * k)⁻¹ = g⁻¹ * ((k * z * k⁻¹) * (k * x * k⁻¹)) * g := by group
    _ = g⁻¹ * (p * x) * g := by rw [hk, hkxk]
    _ = g⁻¹ * (g * u * g⁻¹) * g := by rw [hpu]
    _ = u := by group

theorem omega_pair_false [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {u₁ u₂ : G} (h₁ : OmegaX x (z * x) u₁)
    (h₂ : OmegaX x (z * x) u₂) (hc : u₁ * u₂ = u₂ * u₁) (h₁₂ : OmegaX x (z * x) (u₁ * u₂)) :
    False := by
  have hW : CFSG.IsElementaryAbelian 2 ↥(zpowers u₁ ⊔ zpowers u₂) :=
    isElementaryAbelian_sup_of_commute (isElementaryAbelian_zpowers_of_sq h₁.1)
      (isElementaryAbelian_zpowers_of_sq h₂.1) (fun a' ha b hb => by
        rcases mem_zpowers_of_sq h₁.1 ha with rfl | rfl <;>
          rcases mem_zpowers_of_sq h₂.1 hb with rfl | rfl
        · simp
        · simp
        · simp
        · exact hc)
  have hWC : zpowers u₁ ⊔ zpowers u₂ ≤ centralizer ({x} : Set G) :=
    sup_le (zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 h₁.2.1))
      (zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 h₂.2.1))
  have hWp : IsPGroup 2 ↥(zpowers u₁ ⊔ zpowers u₂) := hW.isPGroup 2 _
  obtain ⟨g, hgC, hgW⟩ := Th2.exists_cj_le_of_isSylowOf hs.setup.sylowT hWC hWp
  have hmemW : ∀ w ∈ zpowers u₁ ⊔ zpowers u₂, g * w * g⁻¹ ∈ T := fun w hw =>
    hgW ((mem_cj_iff g _ _).2 (by
      have e : g⁻¹ * (g * w * g⁻¹) * g = w := by group
      rw [e]; exact hw))
  have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 hgC
  have hu₁W : u₁ ∈ zpowers u₁ ⊔ zpowers u₂ := Subgroup.mem_sup_left (mem_zpowers u₁)
  have hu₂W : u₂ ∈ zpowers u₁ ⊔ zpowers u₂ := Subgroup.mem_sup_right (mem_zpowers u₂)
  obtain ⟨p₁, hp₁, -, -, hpu₁⟩ := F.omega_T hG hs e7 hP2 hQ4 (hmemW u₁ hu₁W) (omegaX_conj hgx h₁)
  obtain ⟨p₂, hp₂, -, -, hpu₂⟩ := F.omega_T hG hs e7 hP2 hQ4 (hmemW u₂ hu₂W) (omegaX_conj hgx h₂)
  obtain ⟨p₃, hp₃, -, -, hpu₃⟩ := F.omega_T hG hs e7 hP2 hQ4
    (hmemW (u₁ * u₂) (Subgroup.mul_mem _ hu₁W hu₂W)) (omegaX_conj hgx h₁₂)
  have hxp₂ : p₂ * x = x * p₂ := F.core.comm_P_conj p₂ hp₂ x F.x_mem
  have hprod : p₃ * x = p₁ * p₂ := by
    calc p₃ * x = g * (u₁ * u₂) * g⁻¹ := hpu₃.symm
      _ = (g * u₁ * g⁻¹) * (g * u₂ * g⁻¹) := by group
      _ = (p₁ * x) * (p₂ * x) := by rw [← hpu₁, ← hpu₂]
      _ = p₁ * (x * p₂) * x := by group
      _ = p₁ * (p₂ * x) * x := by rw [hxp₂]
      _ = p₁ * p₂ * (x * x) := by group
      _ = p₁ * p₂ := by rw [F.x_sq, mul_one]
  have hxP : x ∈ T ⊓ K := by
    have : x = p₃⁻¹ * (p₁ * p₂) := by rw [← hprod]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hp₃) (Subgroup.mul_mem _ hp₁ hp₂)
  have : x ∈ (T ⊓ K) ⊓ conjugate (T ⊓ K) a := ⟨hxP, F.x_mem⟩
  rw [F.core.P_inf_conj, Subgroup.mem_bot] at this
  exact F.x_ne this

theorem exists_conj_of_Fv [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {t : G} (htv : t * (z * x) = (z * x) * t)
    (hxt : IsConj x t) (hxtv : IsConj x (t * (z * x))) :
    ∃ c : G, c * (z * x) = (z * x) * c ∧ c * x * c⁻¹ = t := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hxt
  have hu : OmegaX x (z * x) (g⁻¹ * (z * x) * g) :=
    omegaX_pull hg F.v_sq htv.symm (IsConj.refl _) hxtv
  obtain ⟨m, hmC, hm⟩ := F.omega_conj hG hs e7 hP2 hQ4 hu
  have hmx : m * x * m⁻¹ = x := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hmC
    rw [this]; group
  have hcv : g * m * (z * x) * (g * m)⁻¹ = z * x := by
    calc g * m * (z * x) * (g * m)⁻¹ = g * (m * (z * x) * m⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * (z * x) * g) * g⁻¹ := by rw [hm]
      _ = z * x := by group
  refine ⟨g * m, ?_, ?_⟩
  · calc g * m * (z * x) = (g * m * (z * x) * (g * m)⁻¹) * (g * m) := by group
      _ = (z * x) * (g * m) := by rw [hcv]
  · calc g * m * x * (g * m)⁻¹ = g * (m * x * m⁻¹) * g⁻¹ := by group
      _ = g * x * g⁻¹ := by rw [hmx]
      _ = t := hg

end Frame

end CFSG.GH74.GLS.Th2.P43f
