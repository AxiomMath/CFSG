module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AN4D

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem perm_fin4_aux : ∀ σ : Equiv.Perm (Fin 4), σ ^ 8 = 1 → σ ^ 4 = 1 := by
  decide +kernel

theorem card_perm_four {X : Type} [Finite X] (hX : Nat.card X = 4) :
    Nat.card (Equiv.Perm X) = 24 := by
  rw [Nat.card_perm, hX]
  norm_num [Nat.factorial]

theorem perm_pow_four_of_two_pow {X : Type} [Finite X] (hX : Nat.card X = 4)
    (σ : Equiv.Perm X) {k : ℕ} (h : σ ^ 2 ^ k = 1) : σ ^ 4 = 1 := by
  have h24 : orderOf σ ∣ 24 := by
    have := orderOf_dvd_natCard σ
    rwa [card_perm_four hX] at this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
  have hj3 : j ≤ 3 := by
    by_contra hcon
    have h4 : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    rw [hj] at h24
    exact absurd (h4.trans h24) (by norm_num)
  have h8 : σ ^ 8 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hj]
    exact (Nat.pow_dvd_pow 2 hj3).trans (by norm_num)
  have : Fintype X := Fintype.ofFinite X
  have hX' : Fintype.card X = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hX
  let E : Equiv.Perm X ≃* Equiv.Perm (Fin 4) := Equiv.permCongrHom (Fintype.equivFinOfCardEq hX')
  have h4 := perm_fin4_aux (E σ) (by rw [← map_pow, h8, map_one])
  exact E.injective (by rw [map_pow, h4, map_one])

theorem n4_S_le_normalizer_O2 (h : L41GPh1 t L S x₁ x₂ lam rho) :
    S ≤ normalizer ((l41O2 t x₁ x₂ : Subgroup G) : Set G) := fun s hs =>
  mem_normalizer_of_conj_mem fun q hq => pCoreOf_two_conj_mem (n4_S_le_N h hs) hq

theorem n4_V_le_N (h : L41GPh1 t L S x₁ x₂ lam rho) : l41V S t x₁ x₂ ≤ l41N t x₁ x₂ :=
  sup_le (pCoreOf_two_le _) (n4_S_le_N h)

theorem n4_V_pGroup (h : L41GPh1 t L S x₁ x₂ lam rho) : IsPGroup 2 (l41V S t x₁ x₂) :=
  (pCoreOf_two_isPGroup (l41N t x₁ x₂)).to_sup_of_normal_left' h.isPGroup
    (n4_S_le_normalizer_O2 h)

theorem n4_W_le_V (h : L41GPh1 t L S x₁ x₂ lam rho) : ctxW t x₁ x₂ ≤ l41V S t x₁ x₂ :=
  h.basic.normal_W.1.trans (le_sup_right : S ≤ l41O2 t x₁ x₂ ⊔ S)

theorem n4_lam_mem_S (h : Ctx0 t L S x₁ x₂ lam rho) : lam ∈ S := by
  have hmem : lam ∈ S ⊓ L := by
    rw [h.inf_eq]
    exact Subgroup.subset_closure (by simp)
  exact hmem.1

@[expose] def n4Phi (h : L41GPh3 t L S x₁ x₂ lam rho) :
    ↥(l41V S t x₁ x₂) →* Equiv.Perm ↥(t • (fourGrp x₁ x₂ : Set G)) :=
  (conjAct (l41N t x₁ x₂) (t • (fourGrp x₁ x₂ : Set G)) (n4_omega_inv h)).comp
    (Subgroup.inclusion (n4_V_le_N h.toL41GPh1))

theorem n4Phi_apply (h : L41GPh3 t L S x₁ x₂ lam rho) (v : ↥(l41V S t x₁ x₂))
    (x : ↥(t • (fourGrp x₁ x₂ : Set G))) :
    ((n4Phi h v x : ↥(t • (fourGrp x₁ x₂ : Set G))) : G) = (v : G) * x * (v : G)⁻¹ := rfl

theorem n4_phi_ker (h : L41GPh3 t L S x₁ x₂ lam rho) :
    (n4Phi h).ker = (ctxW t x₁ x₂).subgroupOf (l41V S t x₁ x₂) := by
  ext v
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have e : n4Phi h v = conjAct (l41N t x₁ x₂) (t • (fourGrp x₁ x₂ : Set G)) (n4_omega_inv h)
      (Subgroup.inclusion (n4_V_le_N h.toL41GPh1) v) := rfl
  rw [e, conjAct_eq_one_iff, ← h.basic.cent_A]
  exact n4_fix_iff h (v : G)

theorem n4_O2_fix (h : L41GPh3 t L S x₁ x₂ lam rho) {c : G} (hc : c ∈ l41O2 t x₁ x₂) {f : G}
    (hf : f ∈ fourGrp x₁ x₂) : c * f * c⁻¹ = f := by
  rw [n4_O2_eq h] at hc
  exact n4_conj_eq_of_comm ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2) f hf)

theorem n4_mem_O2 (h : L41GPh3 t L S x₁ x₂ lam rho) {c : G} (hc : c ∈ l41N t x₁ x₂)
    (hfix : ∀ f ∈ fourGrp x₁ x₂, c * f * c⁻¹ = f) : c ∈ l41O2 t x₁ x₂ := by
  rw [n4_O2_eq h]
  exact Subgroup.mem_inf.mpr ⟨hc, Subgroup.mem_centralizer_iff.mpr fun f hf =>
    n4_comm_of_conj_eq (hfix f hf)⟩

theorem n4_exists_c1 (h : L41GPh3 t L S x₁ x₂ lam rho) :
    ∃ c ∈ l41O2 t x₁ x₂, c * t * c⁻¹ = t * x₁ ^ 2 := by
  obtain ⟨n, hn, hnt⟩ := n4_trans h (n4_y_mem_four x₁ x₂)
  have hX : ∀ n ∈ l41N t x₁ x₂, ∀ x ∈ nonid (fourGrp x₁ x₂),
      n * x * n⁻¹ ∈ nonid (fourGrp x₁ x₂) := conj_mem_nonid (n4_normal_F2 h).2
  obtain ⟨k, hk, hnk⟩ := exists_mul_centralizes (K := closure {rho, lam}) hX
    (fun σ => n4_exists_conj_F h σ) hn
  refine ⟨n * k, n4_mem_O2 h (Subgroup.mul_mem _ hn (n4_K_le_N h.toL41GPh1 hk)) fun f hf => ?_, ?_⟩
  · by_cases hf1 : f = 1
    · rw [hf1]
      group
    · exact hnk f ⟨hf, hf1⟩
  · calc n * k * t * (n * k)⁻¹ = n * (k * t * k⁻¹) * n⁻¹ := by group
      _ = n * t * n⁻¹ := by rw [n4_K_fix_t h.toCtx0 hk]
      _ = t * x₁ ^ 2 := hnt

theorem n4_r_conj (h : L41GPh3 t L S x₁ x₂ lam rho) {c : G} (hc : c ∈ l41O2 t x₁ x₂)
    (hct : c * t * c⁻¹ = t * x₁ ^ 2) :
    (c * lam) * t * (c * lam)⁻¹ = t * x₁ ^ 2 ∧
      (c * lam) * (t * x₁ ^ 2) * (c * lam)⁻¹ = t * (x₁ * x₂) ^ 2 := by
  have hlt : lam * t * lam⁻¹ = t := n4_K_fix_t h.toCtx0 (Subgroup.subset_closure (by simp))
  have hly : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := n4_lam_y h.wreath
  have hy2 : x₁ ^ 2 * x₁ ^ 2 = 1 := (y_mul_self_ne_one h.wreath).1
  have hyz : x₁ ^ 2 * (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ :=
    Subgroup.mul_mem _ (n4_y_mem_four x₁ x₂) (n4_z_mem_four x₁ x₂)
  have hcyz := n4_O2_fix h hc hyz
  refine ⟨?_, ?_⟩
  · calc (c * lam) * t * (c * lam)⁻¹ = c * (lam * t * lam⁻¹) * c⁻¹ := by group
      _ = c * t * c⁻¹ := by rw [hlt]
      _ = t * x₁ ^ 2 := hct
  · calc (c * lam) * (t * x₁ ^ 2) * (c * lam)⁻¹
        = c * ((lam * t * lam⁻¹) * (lam * x₁ ^ 2 * lam⁻¹)) * c⁻¹ := by group
      _ = c * (t * (x₁ ^ 2 * (x₁ * x₂) ^ 2)) * c⁻¹ := by rw [hlt, hly]
      _ = (c * t * c⁻¹) * (c * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * c⁻¹) := by group
      _ = (t * x₁ ^ 2) * (x₁ ^ 2 * (x₁ * x₂) ^ 2) := by rw [hct, hcyz]
      _ = t * ((x₁ ^ 2 * x₁ ^ 2) * (x₁ * x₂) ^ 2) := by simp only [mul_assoc]
      _ = t * (x₁ * x₂) ^ 2 := by rw [hy2, one_mul]

theorem n4_sq_mem_W (h : L41GPh3 t L S x₁ x₂ lam rho) {c : G} (hc : c ∈ l41O2 t x₁ x₂)
    (hct : c * t * c⁻¹ = t * x₁ ^ 2) : c * c ∈ ctxW t x₁ x₂ := by
  rw [← h.basic.cent_A]
  refine (n4_fix_iff h (c * c)).mp fun x hx => ?_
  obtain ⟨f, hf, rfl⟩ := n4_mem_smul_iff.mp hx
  have hy2 : x₁ ^ 2 * x₁ ^ 2 = 1 := (y_mul_self_ne_one h.wreath).1
  have hyf : x₁ ^ 2 * f ∈ fourGrp x₁ x₂ := Subgroup.mul_mem _ (n4_y_mem_four x₁ x₂) hf
  have e1 : c * (t * f) * c⁻¹ = t * x₁ ^ 2 * f := by
    calc c * (t * f) * c⁻¹ = (c * t * c⁻¹) * (c * f * c⁻¹) := by group
      _ = t * x₁ ^ 2 * f := by rw [hct, n4_O2_fix h hc hf]
  have e2 : c * (t * x₁ ^ 2 * f) * c⁻¹ = t * f := by
    calc c * (t * x₁ ^ 2 * f) * c⁻¹ = c * (t * (x₁ ^ 2 * f)) * c⁻¹ := by simp only [mul_assoc]
      _ = (c * t * c⁻¹) * (c * (x₁ ^ 2 * f) * c⁻¹) := by group
      _ = (t * x₁ ^ 2) * (x₁ ^ 2 * f) := by rw [hct, n4_O2_fix h hc hyf]
      _ = t * ((x₁ ^ 2 * x₁ ^ 2) * f) := by simp only [mul_assoc]
      _ = t * f := by rw [hy2, one_mul]
  calc (c * c) * (t * f) * (c * c)⁻¹ = c * (c * (t * f) * c⁻¹) * c⁻¹ := by group
    _ = t * f := by rw [e1, e2]

theorem n4_rel_mem_W (h : L41GPh3 t L S x₁ x₂ lam rho) {c : G} (hc : c ∈ l41O2 t x₁ x₂)
    (hct : c * t * c⁻¹ = t * x₁ ^ 2) :
    lam * (c * lam) * lam⁻¹ * (c * lam) ∈ ctxW t x₁ x₂ := by
  have hlinv : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right (n4_lam_sq h.toCtx0)
  have hlN : lam ∈ l41N t x₁ x₂ :=
    n4_K_le_N h.toL41GPh1 (Subgroup.subset_closure (by simp))
  have e : lam * (c * lam) * lam⁻¹ * (c * lam) = lam * (c * c) * lam⁻¹ := by
    calc lam * (c * lam) * lam⁻¹ * (c * lam) = lam * (c * c) * lam := by group
      _ = lam * (c * c) * lam⁻¹ := by rw [hlinv]
  rw [e]
  exact n4_conj_W h.toL41GPh1 hlN (n4_sq_mem_W h hc hct)

theorem n4_phi_sq_apply (h : L41GPh3 t L S x₁ x₂ lam rho) (v : ↥(l41V S t x₁ x₂)) :
    ((((n4Phi h v) ^ 2) ⟨t, n4_t_mem_omega t x₁ x₂⟩ : ↥(t • (fourGrp x₁ x₂ : Set G))) : G) =
      (v : G) * ((v : G) * t * (v : G)⁻¹) * (v : G)⁻¹ := by
  rw [pow_two, Equiv.Perm.mul_apply, n4Phi_apply, n4Phi_apply]

theorem n4_quot_V (h : L41GPh3 t L S x₁ x₂ lam rho) :
    Sec4SectionIso (l41V S t x₁ x₂) (ctxW t x₁ x₂) (DihedralGroup 4) := by
  obtain ⟨c, hc, hct⟩ := n4_exists_c1 h
  obtain ⟨hr1, hr2⟩ := n4_r_conj h hc hct
  have hV2 := n4_V_pGroup h.toL41GPh1
  have hcard : Nat.card ↥(t • (fourGrp x₁ x₂ : Set G)) = 4 := n4_card_omega h.toCtx0
  have hcV : c ∈ l41V S t x₁ x₂ := Subgroup.mem_sup_left hc
  have hlV : lam ∈ l41V S t x₁ x₂ := Subgroup.mem_sup_right (n4_lam_mem_S h.toCtx0)
  let r : ↥(l41V S t x₁ x₂) := ⟨c * lam, Subgroup.mul_mem _ hcV hlV⟩
  let s : ↥(l41V S t x₁ x₂) := ⟨lam, hlV⟩
  have hker := n4_phi_ker h
  have hr2ne : (n4Phi h r) ^ 2 ≠ 1 := by
    intro h1
    have h2 := n4_phi_sq_apply h r
    rw [h1] at h2
    have h3 : t = c * lam * (c * lam * t * (c * lam)⁻¹) * (c * lam)⁻¹ := h2
    rw [hr1, hr2] at h3
    exact (z_mul_self_ne_one h.toCtx0).2 (mul_left_cancel (h3.symm.trans (mul_one t).symm))
  have h4 : (n4Phi h r) ^ 4 = 1 := by
    obtain ⟨k, hk⟩ := hV2 r
    exact perm_pow_four_of_two_pow hcard (n4Phi h r) (k := k) (by rw [← map_pow, hk, map_one])
  have hr : orderOf (n4Phi h r) = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := n4Phi h r) (by simpa using hr2ne)
      (by simpa using h4)
    simpa using this
  have hs : n4Phi h s * n4Phi h s = 1 := by
    rw [← map_mul]
    have : s * s = 1 := Subtype.ext (n4_lam_sq h.toCtx0)
    rw [this, map_one]
  have hrel : n4Phi h s * n4Phi h r * (n4Phi h s)⁻¹ = (n4Phi h r)⁻¹ := by
    have hg : s * r * s⁻¹ * r ∈ (n4Phi h).ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact n4_rel_mem_W h hc hct
    have h1 : n4Phi h (s * r * s⁻¹ * r) = 1 := hg
    rw [map_mul, map_mul, map_mul, map_inv] at h1
    exact mul_eq_one_iff_eq_inv.mp h1
  exact exists_dihedral_section hV2 (dvd_of_eq (card_perm_four hcard)) (n4Phi h) hker hr hs hrel

theorem card_dihedral_four : Nat.card (DihedralGroup 4) = 8 := by
  rw [DihedralGroup.nat_card]

theorem n4_card_V (h : L41GPh3 t L S x₁ x₂ lam rho) :
    Nat.card (l41V S t x₁ x₂) = 8 * Nat.card (ctxW t x₁ x₂) := by
  obtain ⟨ψ, hs, hker⟩ := n4_quot_V h
  have := card_eq_mul_of_section (n4_W_le_V h.toL41GPh1) ψ hs hker
  rw [card_dihedral_four] at this
  exact this

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
