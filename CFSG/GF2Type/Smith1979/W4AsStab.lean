module

public import CFSG.GF2Type.Smith1979.W4AsWeightB
public import CFSG.GF2Type.Smith1979.W4O83Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.GF2Type.Smith1979.W4O83
open CFSG.RankThree.Literature.FSmith (zmod2_cases)
open CFSG.RankThree.OrthogonalInvolutions (add_self_vec neg_vec_eq polar_self_eq_zero)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

@[expose] def Full (C : Omega83Pre S) (v : S.Qt) : Prop := ∀ k, C.prL k v ≠ 0

@[expose] def Pdir (C : Omega83Pre S) (u : S.Qt) : Prop :=
  ∀ x, Full C x → Full C (x + polar S.q x u • u)

section Pdir

variable (C : Omega83Pre S)

theorem pdir_of_mem_plane {i : Fin 4} {u : S.Qt} (hu : u ∈ C.plane i) : Pdir C u := by
  intro x hx k
  rw [map_add, map_smul]
  by_cases hki : k = i
  · rw [hki, C.prL_of_mem_self hu]
    rcases zmod2_cases (polar S.q x u) with hc | hc
    · rw [hc, zero_smul, add_zero]
      exact hx i
    · rw [hc, one_smul]
      intro h0
      have hxu : C.prL i x = u := by
        rw [eq_neg_of_add_eq_zero_left h0, neg_vec_eq (ZMod 2)]
      have h1 : polar S.q x u = 0 := by
        rw [C.polar_eq_polar_prL i x hu, hxu]
        exact polar_self_eq_zero S.q u
      rw [hc] at h1
      exact one_ne_zero h1
  · rw [C.prL_of_mem_ne hki hu, smul_zero, add_zero]
    exact hx k

theorem not_pdir_of_two {u : S.Qt} {i₁ i₂ : Fin 4} (hne : i₁ ≠ i₂) (h₁ : C.prL i₁ u ≠ 0)
    (h₂ : C.prL i₂ u ≠ 0) : ¬ Pdir C u := by
  classical
  intro hP
  choose nz hnz hnz0 using exists_ne_zero_mem_plane C
  let a : Fin 4 → S.Qt := fun k =>
    if k = i₁ then C.th i₁ (C.prL i₁ u) else if C.prL k u = 0 then nz k else C.prL k u
  have ha_mem : ∀ k, a k ∈ C.plane k := by
    intro k
    by_cases hk : k = i₁
    · simp only [a, ite_eq_left hk]
      rw [hk]
      exact C.th_mem_plane (C.prL_mem_plane i₁ u)
    · simp only [a, ite_eq_right hk]
      split_ifs with h0
      · exact hnz k
      · exact C.prL_mem_plane k u
  have ha_ne : ∀ k, a k ≠ 0 := by
    intro k
    by_cases hk : k = i₁
    · simp only [a, ite_eq_left hk]
      intro h0
      exact h₁ ((C.th i₁).injective (h0.trans (map_zero _).symm))
    · simp only [a, ite_eq_right hk]
      split_ifs with h0
      · exact hnz0 k
      · exact h0
  have hpr : ∀ k, C.prL k (∑ j, a j) = a k := fun k => C.prL_decomp ha_mem k
  have hfull : Full C (∑ j, a j) := fun k => by
    rw [hpr]
    exact ha_ne k
  have hpolk : ∀ k, polar S.q (a k) u = if k = i₁ then 1 else 0 := by
    intro k
    rw [polar_comm, C.polar_eq_polar_prL k u (ha_mem k), polar_comm]
    by_cases hk : k = i₁
    · simp only [a, ite_eq_left hk]
      rw [hk, polar_comm]
      exact C.polar_th_self (C.prL_mem_plane i₁ u) h₁
    · simp only [a, ite_eq_right hk]
      split_ifs with h0
      · rw [h0, polar_zero_right]
      · exact polar_self_eq_zero S.q _
  have hpol : polar S.q (∑ j, a j) u = 1 := by
    rw [Omega83Pre.polar_sum_left]
    simp [hpolk]
  have h := hP _ hfull i₂
  rw [hpol, one_smul, map_add, hpr] at h
  apply h
  have ha2 : a i₂ = C.prL i₂ u := by
    simp only [a, ite_eq_right hne.symm, ite_eq_right h₂]
  rw [ha2]
  exact add_self_vec (ZMod 2) _

theorem mem_plane_of_pdir {u : S.Qt} (hu : Pdir C u) (hu0 : u ≠ 0) : ∃ j, u ∈ C.plane j := by
  have hex : ∃ j, C.prL j u ≠ 0 := by
    by_contra h
    push Not at h
    apply hu0
    rw [← C.sum_prL u]
    exact Finset.sum_eq_zero fun k _ => h k
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, ?_⟩
  have hzero : ∀ k, k ≠ j → C.prL k u = 0 := by
    intro k hk
    by_contra hk0
    exact not_pdir_of_two C hk.symm hj hk0 hu
  have hu' : u = C.prL j u := by
    conv_lhs => rw [← C.sum_prL u]
    exact Finset.sum_eq_single j (fun k _ hk => hzero k hk) (by simp)
  rw [hu']
  exact C.prL_mem_plane j u

theorem eq_of_mem_planes {i j : Fin 4} {u : S.Qt} (hi : u ∈ C.plane i) (hj : u ∈ C.plane j)
    (hu : u ≠ 0) : i = j := by
  by_contra hij
  apply hu
  have h1 := C.prL_of_mem_self hi
  rw [C.prL_of_mem_ne hij hj] at h1
  exact h1.symm

variable {C}

theorem pdir_apply {m : S.O} (hm : ∀ v, Full C v → Full C ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) v))
    (hm' : ∀ v, Full C v → Full C (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) {u : S.Qt}
    (hu : Pdir C u) : Pdir C ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) u) := by
  intro x hx
  have h1 := hu _ (hm' x hx)
  have h2 := hm _ h1
  have e1 : (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x) = x := by
    simp
  have e2 : polar S.q (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x) u =
      polar S.q x ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) u) := by
    have := polar_apply_O m (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x) u
    rw [e1] at this
    exact this.symm
  rw [map_add, map_smul, e1, e2] at h2
  exact h2

variable (C)

theorem exists_plane_map {m : S.O}
    (hm : ∀ v, Full C v → Full C ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) v))
    (hm' : ∀ v, Full C v → Full C (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) :
    ∃ j : Fin 4 → Fin 4, ∀ i, ∀ u ∈ C.plane i, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ C.plane (j i) := by
  have hP : ∀ i, ∀ u ∈ C.plane i, Pdir C ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) u) := fun i u hu =>
    pdir_apply hm hm' (pdir_of_mem_plane C hu)
  have hinj : ∀ u, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) u = 0 → u = 0 := fun u hu =>
    (LinearEquiv.map_eq_zero_iff _).mp hu
  choose nz hnz hnz0 using exists_ne_zero_mem_plane C
  have hex : ∀ i, ∃ j, ∀ u ∈ C.plane i, u ≠ 0 → (m : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ C.plane j := by
    intro i
    obtain ⟨j, hj⟩ := mem_plane_of_pdir C (hP i _ (hnz i)) fun h => hnz0 i (hinj _ h)
    refine ⟨j, fun u hu hu0 => ?_⟩
    obtain ⟨j', hj'⟩ := mem_plane_of_pdir C (hP i u hu) fun h => hu0 (hinj _ h)
    by_cases hjj : j = j'
    · rw [hjj]
      exact hj'
    · exfalso
      have hsum : (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (u + nz i) =
          (m : S.Qt ≃ₗ[ZMod 2] S.Qt) u + (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (nz i) := map_add _ _ _
      refine not_pdir_of_two C hjj ?_ ?_ (hP i (u + nz i) (add_mem hu (hnz i)))
      · rw [hsum, map_add, C.prL_of_mem_self hj, C.prL_of_mem_ne hjj hj', zero_add]
        exact fun h => hnz0 i (hinj _ h)
      · rw [hsum, map_add, C.prL_of_mem_ne (Ne.symm hjj) hj, C.prL_of_mem_self hj', add_zero]
        exact fun h => hu0 (hinj _ h)
  choose jm hjm using hex
  refine ⟨jm, fun i u hu => ?_⟩
  by_cases hu0 : u = 0
  · rw [hu0, map_zero]
    exact zero_mem _
  · exact hjm i u hu hu0

theorem eq_of_agree {J : Fin 4} {w₀ : S.Qt} (hw₀ : w₀ ∈ C.plane J) (hw₀0 : w₀ ≠ 0)
    {φ ψ : S.Qt ≃ₗ[ZMod 2] S.Qt} (h0 : φ w₀ = ψ w₀) (h1 : φ (C.th J w₀) = ψ (C.th J w₀))
    (hoth : ∀ k, k ≠ J → ∀ w ∈ C.plane k, φ w = ψ w) : φ = ψ := by
  refine LinearEquiv.ext fun v => ?_
  conv_lhs => rw [← C.sum_prL v]
  conv_rhs => rw [← C.sum_prL v]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = J
  · have hmem := C.prL_mem_plane k v
    rw [hk] at hmem ⊢
    rw [C.plane_eq_span_pair hw₀ hw₀0, Submodule.mem_span_pair] at hmem
    obtain ⟨a, b, hab⟩ := hmem
    rw [← hab, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h0, h1]
  · exact hoth k hk _ (C.prL_mem_plane k v)

theorem exists_conj_th (M N : S.Qt ≃ₗ[ZMod 2] S.Qt) (hMN : ∀ v, M (N v) = v)
    (hNM : ∀ v, N (M v) = v) (jm jn : Fin 4 → Fin 4)
    (hjm : ∀ l, ∀ u ∈ C.plane l, M u ∈ C.plane (jm l))
    (hjn : ∀ l, ∀ u ∈ C.plane l, N u ∈ C.plane (jn l)) (i : Fin 4) :
    ∃ J, (∀ v, M (C.th i (N v)) = C.th J v) ∨ (∀ v, M (C.th i (N v)) = C.th J (C.th J v)) := by
  have hjn_jm : ∀ l, jn (jm l) = l := by
    intro l
    obtain ⟨u, hu, hu0⟩ := exists_ne_zero_mem_plane C l
    have h2 := hjn _ _ (hjm l u hu)
    rw [hNM] at h2
    exact eq_of_mem_planes C h2 hu hu0
  have hjm_jn : ∀ l, jm (jn l) = l := by
    intro l
    obtain ⟨u, hu, hu0⟩ := exists_ne_zero_mem_plane C l
    have h2 := hjm _ _ (hjn l u hu)
    rw [hMN] at h2
    exact eq_of_mem_planes C h2 hu hu0
  let φ : S.Qt ≃ₗ[ZMod 2] S.Qt := N.trans ((C.th i).trans M)
  have hφ : ∀ v, φ v = M (C.th i (N v)) := fun v => rfl
  have hfix : ∀ k, k ≠ jm i → ∀ w ∈ C.plane k, φ w = w := by
    intro k hk w hw
    have h1 := hjn k w hw
    have hik : i ≠ jn k := by
      intro h
      apply hk
      rw [h, hjm_jn]
    rw [hφ, C.th_eq_of_ne hik h1, hMN]
  have hmem : ∀ w ∈ C.plane (jm i), φ w ∈ C.plane (jm i) := by
    intro w hw
    have h1 := hjn _ w hw
    rw [hjn_jm] at h1
    rw [hφ]
    exact hjm i _ (C.th_mem_plane h1)
  have hfree : ∀ w ∈ C.plane (jm i), φ w = w → w = 0 := by
    intro w hw hφw
    have h1 := hjn _ w hw
    rw [hjn_jm] at h1
    have h2 : C.th i (N w) = N w := by
      have h3 := congrArg N hφw
      rwa [hφ, hNM] at h3
    have h3 := C.eq_zero_of_th_eq h1 h2
    have h4 := congrArg M h3
    rwa [hMN, map_zero] at h4
  have hcube : ∀ v, φ (φ (φ v)) = v := by
    intro v
    simp only [hφ, hNM]
    rw [C.th_th_th, hMN]
  refine ⟨jm i, ?_⟩
  have hrel : ∀ w ∈ C.plane (jm i), φ (φ w) = w + φ w := by
    intro w hw
    have hu : φ (φ w) + φ w + w ∈ C.plane (jm i) :=
      add_mem (add_mem (hmem _ (hmem _ hw)) (hmem _ hw)) hw
    have hfixu : φ (φ (φ w) + φ w + w) = φ (φ w) + φ w + w := by
      simp only [map_add, hcube]
      abel
    have h := hfree _ hu hfixu
    have h2 : φ (φ w) + (w + φ w) = 0 := by
      rw [← h]
      abel
    rw [eq_neg_of_add_eq_zero_left h2, neg_vec_eq (ZMod 2)]
  obtain ⟨w₀, hw₀, hw₀0⟩ := exists_ne_zero_mem_plane C (jm i)
  have hφw₀0 : φ w₀ ≠ 0 := fun h => hw₀0 ((LinearEquiv.map_eq_zero_iff φ).mp h)
  have hφw₀ne : φ w₀ ≠ w₀ := fun h => hw₀0 (hfree w₀ hw₀ h)
  rcases C.mem_orbit hw₀ hw₀0 (hmem w₀ hw₀) with h | h | h | h
  · exact absurd h hφw₀0
  · exact absurd h hφw₀ne
  ·
    left
    have h1 : φ (C.th (jm i) w₀) = C.th (jm i) (C.th (jm i) w₀) :=
      calc φ (C.th (jm i) w₀) = φ (φ w₀) := by rw [h]
        _ = w₀ + φ w₀ := hrel w₀ hw₀
        _ = w₀ + C.th (jm i) w₀ := by rw [h]
        _ = C.th (jm i) (C.th (jm i) w₀) := (C.th_th_eq_add hw₀).symm
    have heq := eq_of_agree C hw₀ hw₀0 (φ := φ) (ψ := C.th (jm i)) h h1
      (fun k hk w hw => by rw [hfix k hk w hw, C.th_eq_of_ne (Ne.symm hk) hw])
    exact fun v => LinearEquiv.congr_fun heq v
  ·
    right
    have hθ : C.th (jm i) w₀ = φ w₀ + w₀ := by
      calc C.th (jm i) w₀ = C.th (jm i) w₀ + (w₀ + w₀) := by
            rw [add_self_vec (ZMod 2), add_zero]
        _ = (w₀ + C.th (jm i) w₀) + w₀ := by abel
        _ = φ w₀ + w₀ := by rw [h, C.th_th_eq_add hw₀]
    have h1 : φ (C.th (jm i) w₀) = (C.th (jm i) * C.th (jm i)) (C.th (jm i) w₀) :=
      calc φ (C.th (jm i) w₀) = φ (φ w₀ + w₀) := by rw [← hθ]
        _ = (w₀ + φ w₀) + φ w₀ := by rw [map_add, hrel w₀ hw₀]
        _ = w₀ + (φ w₀ + φ w₀) := by abel
        _ = w₀ := by rw [add_self_vec (ZMod 2), add_zero]
        _ = (C.th (jm i) * C.th (jm i)) (C.th (jm i) w₀) := (C.th_th_th (jm i) w₀).symm
    have heq := eq_of_agree C hw₀ hw₀0 (φ := φ) (ψ := C.th (jm i) * C.th (jm i)) h h1
      (fun k hk w hw => by
        rw [hfix k hk w hw, LinearEquiv.mul_apply, C.th_eq_of_ne (Ne.symm hk) hw,
          C.th_eq_of_ne (Ne.symm hk) hw])
    exact fun v => LinearEquiv.congr_fun heq v

theorem conj_theta_mem {m : S.O}
    (hm : ∀ v, (∀ k, C.prL k v ≠ 0) → ∀ k, C.prL k ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) v) ≠ 0)
    (hm' : ∀ v, (∀ k, C.prL k v ≠ 0) →
      ∀ k, C.prL k (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) ≠ 0) (i : Fin 4) :
    ∃ j, m * C.theta i * m⁻¹ = C.theta j ∨ m * C.theta i * m⁻¹ = C.theta j ^ 2 := by
  obtain ⟨jm, hjm⟩ := exists_plane_map C hm hm'
  obtain ⟨jn, hjn⟩ := exists_plane_map C (m := m⁻¹) hm' (by rw [inv_inv]; exact hm)
  have hMN : ∀ v, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
    intro v
    simp
  have hNM : ∀ v, ((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
    intro v
    simp
  obtain ⟨J, hJ | hJ⟩ := exists_conj_th C (m : S.Qt ≃ₗ[ZMod 2] S.Qt)
    ((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) hMN hNM jm jn hjm hjn i
  · exact ⟨J, Or.inl (Subtype.ext (LinearEquiv.ext fun v => hJ v))⟩
  · refine ⟨J, Or.inr (Subtype.ext (LinearEquiv.ext fun v => ?_))⟩
    rw [pow_two]
    exact hJ v

section Invariance

theorem exists_conj_z_of_full {E : Subgroup S.O} (hEM : E ≤ S.Mbar)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hE81 : Nat.card E ∣ 3 ^ 4) (hθ : ∀ i, C.theta i ∈ E)
    (hw : S.width = 4)
    (hbase : ∀ g' : G, g' * S.z * g'⁻¹ ∈ S.QG → g' * S.z * g'⁻¹ ≠ S.z →
      S4.Hyp4 S g' ∧ S4.Cons311 S g')
    (hex : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z)
    {v : S.Qt} (hv : ∀ k, C.prL k v ≠ 0) :
    ∃ g' : G, g' * S.z * g'⁻¹ ∈ S.QG ∧ g' * S.z * g'⁻¹ ≠ S.z ∧
      S.cl (g' * S.z * g'⁻¹) = v := by
  obtain ⟨g₀, ha₀Q, hne₀⟩ := hex
  obtain ⟨y, hyQ, rfl⟩ := S.exists_cl v
  have hg₀ : ∀ k, C.th k (S.cl (g₀ * S.z * g₀⁻¹)) ≠ S.cl (g₀ * S.z * g₀⁻¹) := fun k =>
    (C.th_ne_iff k _).mpr
      (prL_ne_zero_of_conj_z C hEM hE3 hE81 hθ hw (hbase g₀ ha₀Q hne₀).1
        (hbase g₀ ha₀Q hne₀).2 k)
  obtain ⟨k, hk⟩ := C.exists_conj_of_full (hbase g₀ ha₀Q hne₀).1 hg₀ hyQ
    fun k => (C.th_ne_iff k _).mpr (hv k)
  subst hk
  refine ⟨k, hyQ, ?_, rfl⟩
  intro h
  apply hv 0
  rw [h, S.cl_z, map_zero]

theorem full_apply_of_mem_Mbar {E : Subgroup S.O} (hEM : E ≤ S.Mbar)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hE81 : Nat.card E ∣ 3 ^ 4) (hθ : ∀ i, C.theta i ∈ E)
    (hw : S.width = 4)
    (hbase : ∀ g' : G, g' * S.z * g'⁻¹ ∈ S.QG → g' * S.z * g'⁻¹ ≠ S.z →
      S4.Hyp4 S g' ∧ S4.Cons311 S g')
    (hex : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z)
    {x : S.O} (hx : x ∈ S.Mbar) {v : S.Qt} (hv : ∀ k, C.prL k v ≠ 0) :
    ∀ k, C.prL k ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) ≠ 0 := by
  obtain ⟨g, haQ, hne, rfl⟩ := exists_conj_z_of_full C hEM hE3 hE81 hθ hw hbase hex hv
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hx
  rw [S4.ρ_cl_conj_z S m haQ]
  exact fun k => prL_ne_zero_of_conj_z C hEM hE3 hE81 hθ hw
    (hbase _ (S4.conj_mem_QG' S m.2 haQ) (S4.conj_ne_z' S m.2 hne)).1
    (hbase _ (S4.conj_mem_QG' S m.2 haQ) (S4.conj_ne_z' S m.2 hne)).2 k

end Invariance

end Pdir

end CFSG.GF2Type.Smith1979.W4As
