module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARem
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0e

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private abbrev hc4of (hc : Ctx8d t L S x₁ x₂ lam rho tau) : Ctx4 t L S x₁ x₂ lam rho tau :=
  hc.toCtx8c.toCtx8b.toCtx8a.toCtx8.toCtx10.toCtx4

private abbrev hc0of (hc : Ctx8d t L S x₁ x₂ lam rho tau) : Ctx0 t L S x₁ x₂ lam rho :=
  (hc4of hc).toCtx.toCtx0

private theorem p0g_X_gen_pairwise_comm (hc : Ctx8d t L S x₁ x₂ lam rho tau) :
    ({t, tau, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G).Pairwise Commute := by
  have htt : Commute t tau := (S4A.mem_invCent_iff.mp (hc.le_invCent hc.tau_mem)).symm
  have hty : Commute t (x₁ ^ 2) :=
    (S4A.mem_invCent_iff.mp
      (S4A.L_le_invCent hc.hyp (S4A.y_z_mem_L (hc0of hc)).1)).symm
  have htz : Commute t ((x₁ * x₂) ^ 2) := S4A.t_commute_z (hc0of hc)
  have htay : Commute tau (x₁ ^ 2) := S4A.tau_commute_y (hc4of hc).toCtx
  have htaz : Commute tau ((x₁ * x₂) ^ 2) := S4A.tau_commute_z (hc4of hc).toCtx
  have hyz : Commute (x₁ ^ 2) ((x₁ * x₂) ^ 2) := S4A.y_commute_z hc.wreath
  intro a ha b hb hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hab
      | exact htt
      | exact htt.symm
      | exact hty
      | exact hty.symm
      | exact htz
      | exact htz.symm
      | exact htay
      | exact htay.symm
      | exact htaz
      | exact htaz.symm
      | exact hyz
      | exact hyz.symm

private theorem p0g_commute_mem_X (hc : Ctx8d t L S x₁ x₂ lam rho tau) {a b : G}
    (ha : a ∈ ctxX t tau x₁ x₂) (hb : b ∈ ctxX t tau x₁ x₂) : a * b = b * a := by
  haveI : IsMulCommutative ↥(ctxX t tau x₁ x₂) := by
    rw [ctxX]
    exact Subgroup.isMulCommutative_closure (p0g_X_gen_pairwise_comm hc)
  exact congrArg Subtype.val (mul_comm' ⟨a, ha⟩ ⟨b, hb⟩)

private theorem p0g_rho_t (hc : Ctx8d t L S x₁ x₂ lam rho tau) : rho * t = t * rho :=
  S4A.mem_invCent_iff.mp (S4A.L_le_invCent hc.hyp hc.rho_mem)

private theorem p0g_rho_tau (hc : Ctx8d t L S x₁ x₂ lam rho tau) : rho * tau = tau * rho :=
  hc.tau_rho.symm

private theorem p0g_V_le_X (hc : Ctx8d t L S x₁ x₂ lam rho tau) :
    fourGrp x₁ x₂ ≤ ctxX t tau x₁ x₂ :=
  le_trans (p0_V_le_N_le_X t tau x₁ x₂).1 (p0_V_le_N_le_X t tau x₁ x₂).2

private theorem p0g_pair_le_X (hc : Ctx8d t L S x₁ x₂ lam rho tau) :
    closure ({t, tau} : Set G) ≤ ctxX t tau x₁ x₂ := by
  refine (Subgroup.closure_le (K := ctxX t tau x₁ x₂)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl <;> exact Subgroup.subset_closure (by simp)

private theorem p0g_X_eq_sup (hc : Ctx8d t L S x₁ x₂ lam rho tau) :
    ctxX t tau x₁ x₂ = closure ({t, tau} : Set G) ⊔ fourGrp x₁ x₂ := by
  rw [ctxX, fourGrp, ← Subgroup.closure_union]
  congr 1
  ext a
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_empty_iff_false,
    or_false]
  tauto

private theorem p0g_eq_one_of_commute_rho (hc : Ctx8d t L S x₁ x₂ lam rho tau) {f : G}
    (hf : f ∈ fourGrp x₁ x₂) (hcomm : rho * f = f * rho) : f = 1 := by
  by_contra hf1
  have hρf : rho * f * rho⁻¹ = f := by rw [hcomm]; group
  have hρinvf : rho⁻¹ * f * rho = f := by
    calc rho⁻¹ * f * rho = rho⁻¹ * (f * rho) := by group
      _ = rho⁻¹ * (rho * f) := by rw [← hcomm]
      _ = f := by group
  have hy1 : x₁ ^ 2 ≠ 1 := (S4A.y_mul_self_ne_one hc.wreath).2
  have hz1 : (x₁ * x₂) ^ 2 ≠ 1 := hc.wreath.sq_x₁x₂_ne_one
  have hyV : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hzV : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hy_eq : x₁ ^ 2 = f := by
    rcases p0_rho_orbit_V (hc4of hc) hf hf1 hyV hy1 with h | h | h
    · exact h
    · rw [hρf] at h; exact h
    · rw [hρinvf] at h; exact h
  have hz_eq : (x₁ * x₂) ^ 2 = f := by
    rcases p0_rho_orbit_V (hc4of hc) hf hf1 hzV hz1 with h | h | h
    · exact h
    · rw [hρf] at h; exact h
    · rw [hρinvf] at h; exact h
  have hyz_ne : x₁ ^ 2 ≠ (x₁ * x₂) ^ 2 := by
    intro h
    apply (S4A.yz_mul_self_ne_one hc.wreath).2
    rw [← h, (S4A.y_mul_self_ne_one hc.wreath).1]
  exact hyz_ne (hy_eq.trans hz_eq.symm)

private theorem p0g_centralizes_V (hc : Ctx8d t L S x₁ x₂ lam rho tau) {g : G}
    (hg : g ∈ ctxR t tau x₁ x₂) {v : G} (hv : v ∈ fourGrp x₁ x₂) : g * v * g⁻¹ = v := by
  have hgO : g ∈ ctxO t tau x₁ x₂ := hc.R_le_O hg
  have hgc : g ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    have h : g ∈ ctxM t tau x₁ x₂ ⊓
        centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
      rw [← hc.O_eq_C]; exact hgO
    exact h.2
  have hv' : v * g = g * v := Subgroup.mem_centralizer_iff.mp hgc v hv
  calc g * v * g⁻¹ = (g * v) * g⁻¹ := rfl
    _ = (v * g) * g⁻¹ := by rw [← hv']
    _ = v := by group

private theorem p0g_conj_mem_smul_V (hc : Ctx8d t L S x₁ x₂ lam rho tau) {k u : G}
    (hk : k ∈ ctxR t tau x₁ x₂) (hu : u ∈ ctxX t tau x₁ x₂) :
    k * u * k⁻¹ ∈ u • (fourGrp x₁ x₂ : Set G) := by
  have hkM : k ∈ ctxM t tau x₁ x₂ := hc.normal_R.1 hk
  have hkO : k ∈ ctxO t tau x₁ x₂ := hc.R_le_O hk
  have hkcentV : ∀ v ∈ fourGrp x₁ x₂, k * v * k⁻¹ = v := fun v hv =>
    p0g_centralizes_V hc hk hv
  have hcommX : ∀ {a b : G}, a ∈ ctxX t tau x₁ x₂ → b ∈ ctxX t tau x₁ x₂ → a * b = b * a :=
    fun ha hb => p0g_commute_mem_X hc ha hb
  rw [ctxX] at hu
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h | h | h
      · rw [h]
        exact (p0_mem_R_iff hc.toCtx8c hkO).mp hk
      · rw [h]
        exact p0_tau_conj_mem hc.toCtx8c hkM
      · rw [h]
        refine Set.mem_smul_set.mpr ⟨1, (fourGrp x₁ x₂).one_mem, ?_⟩
        rw [smul_eq_mul, mul_one]
        exact (hkcentV (x₁ ^ 2) (Subgroup.subset_closure (by simp))).symm
      · rw [h]
        refine Set.mem_smul_set.mpr ⟨1, (fourGrp x₁ x₂).one_mem, ?_⟩
        rw [smul_eq_mul, mul_one]
        exact (hkcentV ((x₁ * x₂) ^ 2) (Subgroup.subset_closure (by simp))).symm
  | one =>
      exact Set.mem_smul_set.mpr ⟨1, (fourGrp x₁ x₂).one_mem, by rw [smul_eq_mul, mul_one]; group⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨vx, hvx, hvx'⟩ := Set.mem_smul_set.mp ihx
      obtain ⟨vy, hvy, hvy'⟩ := Set.mem_smul_set.mp ihy
      refine Set.mem_smul_set.mpr ⟨vx * vy, (fourGrp x₁ x₂).mul_mem hvx hvy, ?_⟩
      rw [smul_eq_mul]
      have e1 : k * x * k⁻¹ = x * vx := hvx'.symm.trans (smul_eq_mul x vx)
      have e2 : k * y * k⁻¹ = y * vy := hvy'.symm.trans (smul_eq_mul y vy)
      have hyvx : y * vx = vx * y := hcommX hy (p0g_V_le_X hc hvx)
      calc (x * y) * (vx * vy) = x * (y * (vx * vy)) := by group
        _ = x * ((y * vx) * vy) := by group
        _ = x * ((vx * y) * vy) := by rw [hyvx]
        _ = (k * x * k⁻¹) * (k * y * k⁻¹) := by rw [e1, e2]; group
        _ = k * (x * y) * k⁻¹ := by group
  | inv x hx ihx =>
      obtain ⟨vx, hvx, hvx'⟩ := Set.mem_smul_set.mp ihx
      refine Set.mem_smul_set.mpr ⟨vx⁻¹, (fourGrp x₁ x₂).inv_mem hvx, ?_⟩
      rw [smul_eq_mul]
      have e1 : k * x * k⁻¹ = x * vx := hvx'.symm.trans (smul_eq_mul x vx)
      have hcomm : x * vx = vx * x := hcommX hx (p0g_V_le_X hc hvx)
      calc x⁻¹ * vx⁻¹ = (vx * x)⁻¹ := by rw [mul_inv_rev]
        _ = (x * vx)⁻¹ := by rw [hcomm]
        _ = (k * x * k⁻¹)⁻¹ := by rw [e1]
        _ = k * x⁻¹ * k⁻¹ := by group

private theorem p0g_R_not_le_cent_t (hc : Ctx8d t L S x₁ x₂ lam rho tau) :
    ∃ r ∈ ctxR t tau x₁ x₂, r * t * r⁻¹ ≠ t := by
  by_contra h
  push Not at h
  have hle : ctxR t tau x₁ x₂ ≤ ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G) := by
    intro r hr
    refine ⟨hc.normal_R.1 hr, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc r * t = r * t * r⁻¹ * r := by group
        _ = t * r := by rw [h r hr])
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hc.card_R, p0_card_CMt (hc4of hc)] at hdvd
  norm_num at hdvd

private theorem p0g_orbit_R (hc : Ctx8d t L S x₁ x₂ lam rho tau) {u : G}
    (hu : u ∈ ctxX t tau x₁ x₂) (hρ : rho * u = u * rho)
    (hnc : ∃ r ∈ ctxR t tau x₁ x₂, r * u * r⁻¹ ≠ u) :
    conjIn (ctxR t tau x₁ x₂) u = u • (fourGrp x₁ x₂ : Set G) := by
  have hc4 := hc4of hc
  apply le_antisymm
  · rintro w ⟨k, hkR, rfl⟩
    exact p0g_conj_mem_smul_V hc hkR hu
  · rintro w hw
    obtain ⟨v, hv, hwv⟩ := Set.mem_smul_set.mp hw
    rw [← hwv, smul_eq_mul]
    obtain ⟨r₀, hr₀R, hr₀ne⟩ := hnc
    have hv₀V : u⁻¹ * (r₀ * u * r₀⁻¹) ∈ fourGrp x₁ x₂ := by
      obtain ⟨v₀, hv₀, hv₀eq⟩ := Set.mem_smul_set.mp (p0g_conj_mem_smul_V hc hr₀R hu)
      have heq : u⁻¹ * (r₀ * u * r₀⁻¹) = v₀ := by
        rw [← hv₀eq, smul_eq_mul]; group
      rwa [heq]
    have hv₀ne : u⁻¹ * (r₀ * u * r₀⁻¹) ≠ 1 := by
      intro h1
      apply hr₀ne
      calc r₀ * u * r₀⁻¹ = u * (u⁻¹ * (r₀ * u * r₀⁻¹)) := by group
        _ = u * 1 := by rw [h1]
        _ = u := by rw [mul_one]
    have hbase : u * (u⁻¹ * (r₀ * u * r₀⁻¹)) ∈ conjIn (ctxR t tau x₁ x₂) u :=
      ⟨r₀, hr₀R, by group⟩
    have hρM : rho ∈ ctxM t tau x₁ x₂ := (p0_gens_mem_M hc4).2.2.2.2.1
    have hρinv : rho⁻¹ * u = u * rho⁻¹ := by
      calc rho⁻¹ * u = rho⁻¹ * (u * rho) * rho⁻¹ := by group
        _ = rho⁻¹ * (rho * u) * rho⁻¹ := by rw [← hρ]
        _ = u * rho⁻¹ := by group
    have hρu : rho⁻¹ * u * rho = u := by
      calc rho⁻¹ * u * rho = rho⁻¹ * (u * rho) := by group
        _ = rho⁻¹ * (rho * u) := by rw [← hρ]
        _ = u := by group
    have hρu' : rho * u * rho⁻¹ = u := by
      calc rho * u * rho⁻¹ = rho * (u * rho⁻¹) := by group
        _ = rho * (rho⁻¹ * u) := by rw [← hρinv]
        _ = u := by group
    have hconj_rho : ∀ y ∈ conjIn (ctxR t tau x₁ x₂) u,
        rho * y * rho⁻¹ ∈ conjIn (ctxR t tau x₁ x₂) u := by
      rintro y ⟨k, hkR, rfl⟩
      refine ⟨rho * k * rho⁻¹, hc.normal_R.2 rho hρM k hkR, ?_⟩
      calc (rho * k * rho⁻¹) * u * (rho * k * rho⁻¹)⁻¹
          = rho * k * (rho⁻¹ * u * rho) * k⁻¹ * rho⁻¹ := by group
        _ = rho * k * u * k⁻¹ * rho⁻¹ := by rw [hρu]
        _ = rho * (k * u * k⁻¹) * rho⁻¹ := by group
    have hconj_rhoinv : ∀ y ∈ conjIn (ctxR t tau x₁ x₂) u,
        rho⁻¹ * y * rho ∈ conjIn (ctxR t tau x₁ x₂) u := by
      rintro y ⟨k, hkR, rfl⟩
      refine ⟨rho⁻¹ * k * rho, ?_, ?_⟩
      · simpa using hc.normal_R.2 rho⁻¹ (Subgroup.inv_mem _ hρM) k hkR
      · calc (rho⁻¹ * k * rho) * u * (rho⁻¹ * k * rho)⁻¹
            = rho⁻¹ * k * (rho * u * rho⁻¹) * k⁻¹ * rho := by group
          _ = rho⁻¹ * k * u * k⁻¹ * rho := by rw [hρu']
          _ = rho⁻¹ * (k * u * k⁻¹) * rho := by group
    by_cases hv1 : v = 1
    · rw [hv1, mul_one]
      exact ⟨1, (ctxR t tau x₁ x₂).one_mem, by group⟩
    · rcases p0_rho_orbit_V hc4 hv₀V hv₀ne hv hv1 with h | h | h
      · rw [h]; exact hbase
      · rw [h]
        have hu_rho : u * rho = rho * u := hρ.symm
        have heq : u * (rho * (u⁻¹ * (r₀ * u * r₀⁻¹)) * rho⁻¹) =
            rho * (u * (u⁻¹ * (r₀ * u * r₀⁻¹))) * rho⁻¹ := by
          calc u * (rho * (u⁻¹ * (r₀ * u * r₀⁻¹)) * rho⁻¹)
              = (u * rho) * (u⁻¹ * (r₀ * u * r₀⁻¹)) * rho⁻¹ := by group
            _ = (rho * u) * (u⁻¹ * (r₀ * u * r₀⁻¹)) * rho⁻¹ := by rw [hu_rho]
            _ = rho * (u * (u⁻¹ * (r₀ * u * r₀⁻¹))) * rho⁻¹ := by group
        rw [heq]
        exact hconj_rho (u * (u⁻¹ * (r₀ * u * r₀⁻¹))) hbase
      · rw [h]
        have hu_rhoinv : u * rho⁻¹ = rho⁻¹ * u := by
          calc u * rho⁻¹ = rho⁻¹ * (rho * u) * rho⁻¹ := by group
            _ = rho⁻¹ * (u * rho) * rho⁻¹ := by rw [hρ]
            _ = rho⁻¹ * u := by group
        have heq : u * (rho⁻¹ * (u⁻¹ * (r₀ * u * r₀⁻¹)) * rho) =
            rho⁻¹ * (u * (u⁻¹ * (r₀ * u * r₀⁻¹))) * rho := by
          calc u * (rho⁻¹ * (u⁻¹ * (r₀ * u * r₀⁻¹)) * rho)
              = (u * rho⁻¹) * (u⁻¹ * (r₀ * u * r₀⁻¹)) * rho := by group
            _ = (rho⁻¹ * u) * (u⁻¹ * (r₀ * u * r₀⁻¹)) * rho := by rw [hu_rhoinv]
            _ = rho⁻¹ * (u * (u⁻¹ * (r₀ * u * r₀⁻¹))) * rho := by group
        rw [heq]
        exact hconj_rhoinv (u * (u⁻¹ * (r₀ * u * r₀⁻¹))) hbase

private theorem p0g_tR_class (hc : Ctx8d t L S x₁ x₂ lam rho tau) :
    conjIn (ctxR t tau x₁ x₂) t = t • (fourGrp x₁ x₂ : Set G) :=
  p0g_orbit_R hc (Subgroup.subset_closure (by simp)) (p0g_rho_t hc) (p0g_R_not_le_cent_t hc)

private theorem p0g_x₁_conj_tau (hc : Ctx8d t L S x₁ x₂ lam rho tau) :
    x₁ * tau * x₁⁻¹ = x₁ ^ 2 * tau := by
  have h1 : tau * x₁⁻¹ * tau⁻¹ = x₁ := by
    calc tau * x₁⁻¹ * tau⁻¹ = (tau * x₁ * tau⁻¹)⁻¹ := by group
      _ = (x₁⁻¹)⁻¹ := by rw [hc.tau_x₁]
      _ = x₁ := by group
  have h2 : x₁ * tau * x₁⁻¹ * tau⁻¹ = x₁ ^ 2 := by
    calc x₁ * tau * x₁⁻¹ * tau⁻¹ = x₁ * (tau * x₁⁻¹ * tau⁻¹) := by group
      _ = x₁ * x₁ := by rw [h1]
      _ = x₁ ^ 2 := by rw [pow_two]
  calc x₁ * tau * x₁⁻¹ = x₁ * tau * x₁⁻¹ * tau⁻¹ * tau := by group
    _ = x₁ ^ 2 * tau := by rw [h2]

private theorem p0g_centralizes_X (hc : Ctx8d t L S x₁ x₂ lam rho tau) {g : G}
    (hgR : g ∈ ctxR t tau x₁ x₂) (hgt : g * t = t * g) (hgτ : g * tau = tau * g) :
    ∀ a ∈ ctxX t tau x₁ x₂, a * g = g * a := by
  intro a ha
  rw [ctxX] at ha
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hgt.symm
      · exact hgτ.symm
      · have h := p0g_centralizes_V hc hgR (v := x₁ ^ 2)
          (Subgroup.subset_closure (by simp))
        calc x₁ ^ 2 * g = (g * x₁ ^ 2 * g⁻¹) * g := by rw [h]
          _ = g * x₁ ^ 2 := by group
      · have h := p0g_centralizes_V hc hgR (v := (x₁ * x₂) ^ 2)
          (Subgroup.subset_closure (by simp))
        calc (x₁ * x₂) ^ 2 * g = (g * (x₁ * x₂) ^ 2 * g⁻¹) * g := by rw [h]
          _ = g * (x₁ * x₂) ^ 2 := by group
  | one => simp
  | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | inv x _ hx =>
      calc x⁻¹ * g = x⁻¹ * (g * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * g) * x⁻¹ := by rw [← hx]
        _ = g * x⁻¹ := by group

private theorem p0g_C_R_X (hc : Ctx8d t L S x₁ x₂ lam rho tau) :
    ctxR t tau x₁ x₂ ⊓ centralizer ((ctxX t tau x₁ x₂ : Subgroup G) : Set G) =
      ctxX t tau x₁ x₂ := by
  obtain ⟨act, hact, hker⟩ := Ctx4.exists_action_on_X (hc4of hc)
  apply le_antisymm
  · rintro g ⟨hgR, hgC⟩
    have hgM : g ∈ ctxM t tau x₁ x₂ := hc.normal_R.1 hgR
    have h1 : act ⟨g, hgM⟩ = 1 := by
      ext x
      rw [hact]
      have hv : (x : G) * g = g * (x : G) :=
        Subgroup.mem_centralizer_iff.mp hgC x x.2
      calc g * (x : G) * g⁻¹ = ((x : G) * g) * g⁻¹ := by rw [← hv]
        _ = x := by group
    exact (hker ⟨g, hgM⟩).mp h1
  · rintro g hg
    exact ⟨hc.X_le_R hg, Subgroup.mem_centralizer_iff.mpr fun x hx =>
      p0g_commute_mem_X hc hx hg⟩

theorem p0_CR_rho (hc : Ctx8d t L S x₁ x₂ lam rho tau) :
    ctxR t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) = closure {t, tau} := by
  have hVX := p0g_V_le_X hc
  have hpairX := p0g_pair_le_X hc
  have hXV := p0g_X_eq_sup hc
  have hρt : rho * t = t * rho := p0g_rho_t hc
  have hρtau : rho * tau = tau * rho := p0g_rho_tau hc
  apply le_antisymm
  · intro g hg
    obtain ⟨hgR, hgC⟩ := hg
    have hgM : g ∈ ctxM t tau x₁ x₂ := hc.normal_R.1 hgR
    have hgO : g ∈ ctxO t tau x₁ x₂ := hc.R_le_O hgR
    have hgV : ∀ v ∈ fourGrp x₁ x₂, g * v * g⁻¹ = v := fun v hv =>
      p0g_centralizes_V hc hgR hv
    have hρg : rho * g = g * rho := (Subgroup.mem_centralizer_singleton_iff.mp hgC).symm
    have haV : g * t * g⁻¹ * t⁻¹ ∈ fourGrp x₁ x₂ := by
      have hmem : g * t * g⁻¹ ∈ t • (fourGrp x₁ x₂ : Set G) :=
        (p0_mem_R_iff hc.toCtx8c hgO).mp hgR
      obtain ⟨v, hv, htv⟩ := Set.mem_smul_set.mp hmem
      have heq : g * t * g⁻¹ * t⁻¹ = v := by
        rw [← htv, smul_eq_mul]
        rw [p0g_commute_mem_X hc (Subgroup.subset_closure (by simp)) (hVX hv)]
        group
      rwa [heq]
    have hbV : g * tau * g⁻¹ * tau⁻¹ ∈ fourGrp x₁ x₂ := by
      have hmem : g * tau * g⁻¹ ∈ tau • (fourGrp x₁ x₂ : Set G) :=
        p0_tau_conj_mem hc.toCtx8c hgM
      obtain ⟨v, hv, htv⟩ := Set.mem_smul_set.mp hmem
      have heq : g * tau * g⁻¹ * tau⁻¹ = v := by
        rw [← htv, smul_eq_mul]
        rw [p0g_commute_mem_X hc (Subgroup.subset_closure (by simp)) (hVX hv)]
        group
      rwa [heq]
    have hρg' : rho * g * rho⁻¹ = g := by rw [hρg]; group
    have hρt' : rho * t * rho⁻¹ = t := by rw [hρt]; group
    have hρtau' : rho * tau * rho⁻¹ = tau := by rw [hρtau]; group
    have ha_comm : rho * (g * t * g⁻¹ * t⁻¹) = (g * t * g⁻¹ * t⁻¹) * rho := by
      have haρ : rho * (g * t * g⁻¹ * t⁻¹) * rho⁻¹ = g * t * g⁻¹ * t⁻¹ := by
        have e : rho * (g * t * g⁻¹ * t⁻¹) * rho⁻¹ =
            (rho * g * rho⁻¹) * (rho * t * rho⁻¹) * (rho * g * rho⁻¹)⁻¹ *
              (rho * t * rho⁻¹)⁻¹ := by group
        rw [e, hρg', hρt']
      calc rho * (g * t * g⁻¹ * t⁻¹)
          = rho * (g * t * g⁻¹ * t⁻¹) * rho⁻¹ * rho := by group
        _ = (g * t * g⁻¹ * t⁻¹) * rho := by rw [haρ]
    have hb_comm : rho * (g * tau * g⁻¹ * tau⁻¹) = (g * tau * g⁻¹ * tau⁻¹) * rho := by
      have hbρ : rho * (g * tau * g⁻¹ * tau⁻¹) * rho⁻¹ = g * tau * g⁻¹ * tau⁻¹ := by
        have e : rho * (g * tau * g⁻¹ * tau⁻¹) * rho⁻¹ =
            (rho * g * rho⁻¹) * (rho * tau * rho⁻¹) * (rho * g * rho⁻¹)⁻¹ *
              (rho * tau * rho⁻¹)⁻¹ := by group
        rw [e, hρg', hρtau']
      calc rho * (g * tau * g⁻¹ * tau⁻¹)
          = rho * (g * tau * g⁻¹ * tau⁻¹) * rho⁻¹ * rho := by group
        _ = (g * tau * g⁻¹ * tau⁻¹) * rho := by rw [hbρ]
    have ha1 : g * t * g⁻¹ * t⁻¹ = 1 := p0g_eq_one_of_commute_rho hc haV ha_comm
    have hb1 : g * tau * g⁻¹ * tau⁻¹ = 1 := p0g_eq_one_of_commute_rho hc hbV hb_comm
    have hgt : g * t * g⁻¹ = t := by
      calc g * t * g⁻¹ = g * t * g⁻¹ * t⁻¹ * t := by group
        _ = 1 * t := by rw [ha1]
        _ = t := by rw [one_mul]
    have hgtau : g * tau * g⁻¹ = tau := by
      calc g * tau * g⁻¹ = g * tau * g⁻¹ * tau⁻¹ * tau := by group
        _ = 1 * tau := by rw [hb1]
        _ = tau := by rw [one_mul]
    have hgt_comm : g * t = t * g := by
      calc g * t = g * t * g⁻¹ * g := by group
        _ = t * g := by rw [hgt]
    have hgtau_comm : g * tau = tau * g := by
      calc g * tau = g * tau * g⁻¹ * g := by group
        _ = tau * g := by rw [hgtau]
    have hgCent : g ∈ centralizer ((ctxX t tau x₁ x₂ : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr
        (p0g_centralizes_X hc hgR hgt_comm hgtau_comm)
    have hgXmem : g ∈ ctxX t tau x₁ x₂ := by
      have hmem : g ∈ ctxR t tau x₁ x₂ ⊓
          centralizer ((ctxX t tau x₁ x₂ : Subgroup G) : Set G) := ⟨hgR, hgCent⟩
      rwa [p0g_C_R_X hc] at hmem
    have hKnorm : ∀ k ∈ fourGrp x₁ x₂, ∀ h ∈ closure ({t, tau} : Set G),
        k * h * k⁻¹ ∈ closure ({t, tau} : Set G) := by
      intro k hk h hh
      have hkX : k ∈ ctxX t tau x₁ x₂ := hVX hk
      have hhX : h ∈ ctxX t tau x₁ x₂ := hpairX hh
      have hcomm := p0g_commute_mem_X hc hkX hhX
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact hh
    have hg_sup : g ∈ closure ({t, tau} : Set G) ⊔ fourGrp x₁ x₂ := by
      rwa [← hXV]
    obtain ⟨c, hc_mem, v, hv, hg_eq⟩ :=
      (mem_sup_iff_of_normalizes (H := closure ({t, tau} : Set G))
        (K := fourGrp x₁ x₂) hKnorm).mp hg_sup
    have hpairCent : closure ({t, tau} : Set G) ≤ centralizer ({rho} : Set G) := by
      refine (Subgroup.closure_le (K := centralizer ({rho} : Set G))).mpr ?_
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hρt.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hρtau.symm
    have hcC : c ∈ centralizer ({rho} : Set G) := hpairCent hc_mem
    have hvC : v ∈ centralizer ({rho} : Set G) := by
      have hv_eq : v = c⁻¹ * g := by rw [hg_eq]; group
      rw [hv_eq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcC) hgC
    have hv1 : v = 1 := p0g_eq_one_of_commute_rho hc hv
      (Subgroup.mem_centralizer_singleton_iff.mp hvC).symm
    rw [hg_eq, hv1, mul_one]
    exact hc_mem
  · intro g hg
    have hgR : g ∈ ctxR t tau x₁ x₂ := by
      refine (Subgroup.closure_le (K := ctxR t tau x₁ x₂)).mpr ?_ hg
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact hc.X_le_R (Subgroup.subset_closure (by simp))
      · exact hc.X_le_R (Subgroup.subset_closure (by simp))
    have hgC : g ∈ centralizer ({rho} : Set G) := by
      refine (Subgroup.closure_le (K := centralizer ({rho} : Set G))).mpr ?_ hg
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hρt.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hρtau.symm
    exact ⟨hgR, hgC⟩

theorem p0_orbit_R (hc : Ctx8d t L S x₁ x₂ lam rho tau) {u : G} (hu : u ∈ ctxX t tau x₁ x₂)
    (hρ : rho * u = u * rho) (hnc : ∃ r ∈ ctxR t tau x₁ x₂, r * u * r⁻¹ ≠ u) :
    conjIn (ctxR t tau x₁ x₂) u = u • (fourGrp x₁ x₂ : Set G) :=
  p0g_orbit_R hc hu hρ hnc

theorem p0_ttau_mem_tM (hc : Ctx8d t L S x₁ x₂ lam rho tau) :
    t * tau ∈ conjIn (ctxM t tau x₁ x₂) t := by
  rw [hc.tM]
  right
  refine Set.mem_smul_set.mpr ⟨1, (fourGrp x₁ x₂).one_mem, ?_⟩
  rw [smul_eq_mul, mul_one]

theorem p0_R_not_le_cent_ttau (hc : Ctx8d t L S x₁ x₂ lam rho tau) :
    ∃ r ∈ ctxR t tau x₁ x₂, r * (t * tau) * r⁻¹ ≠ t * tau := by
  by_contra h
  push Not at h
  have hmem : t * tau ∈ conjIn (ctxM t tau x₁ x₂) t := p0_ttau_mem_tM hc
  obtain ⟨m, hmM, hm_eq⟩ := hmem
  have hsets : conjIn (ctxM t tau x₁ x₂) (t * tau) = conjIn (ctxM t tau x₁ x₂) t := by
    apply le_antisymm
    · rintro w ⟨k, hkM, rfl⟩
      exact ⟨k * m, mul_mem hkM hmM, by rw [show (k * m) * t * (k * m)⁻¹ =
        k * (m * t * m⁻¹) * k⁻¹ by group, hm_eq]⟩
    · rintro w ⟨k, hkM, rfl⟩
      refine ⟨k * m⁻¹, mul_mem hkM (inv_mem hmM), ?_⟩
      have h1 : m⁻¹ * (t * tau) * m = t := by rw [← hm_eq]; group
      rw [show (k * m⁻¹) * (t * tau) * (k * m⁻¹)⁻¹ =
        k * (m⁻¹ * (t * tau) * m) * k⁻¹ by group, h1]
  have hncard : (conjIn (ctxM t tau x₁ x₂) (t * tau)).ncard = 8 := by
    rw [hsets]; exact p0_ncard_tM hc.toCtx8c.toCtx8b.toCtx8a.toCtx8
  have hstab := card_eq_ncard_conjIn_mul (ctxM t tau x₁ x₂) (t * tau)
  have hcardC : Nat.card ↥(ctxM t tau x₁ x₂ ⊓ centralizer ({t * tau} : Set G)) = 384 := by
    rw [hc.card_M, hncard] at hstab
    have h8 : 8 * Nat.card ↥(ctxM t tau x₁ x₂ ⊓ centralizer ({t * tau} : Set G)) =
        3 * 2 ^ 10 := hstab.symm
    norm_num at h8
    omega
  have hle : ctxR t tau x₁ x₂ ≤ ctxM t tau x₁ x₂ ⊓ centralizer ({t * tau} : Set G) := by
    intro r hr
    refine ⟨hc.normal_R.1 hr, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc r * (t * tau) = r * (t * tau) * r⁻¹ * r := by group
        _ = (t * tau) * r := by rw [h r hr])
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hc.card_R, hcardC] at hdvd
  norm_num at hdvd

theorem p0_tR (hc : Ctx8d t L S x₁ x₂ lam rho tau) :
    conjIn (ctxR t tau x₁ x₂) t = t • (fourGrp x₁ x₂ : Set G) :=
  p0g_tR_class hc

theorem p0_ttauR (hc : Ctx8d t L S x₁ x₂ lam rho tau) :
    conjIn (ctxR t tau x₁ x₂) (t * tau) = (t * tau) • (fourGrp x₁ x₂ : Set G) := by
  refine p0_orbit_R hc
    (mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))) ?_
    (p0_R_not_le_cent_ttau hc)
  calc rho * (t * tau) = (rho * t) * tau := by group
    _ = (t * rho) * tau := by rw [p0g_rho_t hc]
    _ = t * (rho * tau) := by group
    _ = t * (tau * rho) := by rw [(p0g_rho_tau hc).symm]
    _ = (t * tau) * rho := by group

theorem p0_tauR (hc : Ctx8d t L S x₁ x₂ lam rho tau) :
    conjIn (ctxR t tau x₁ x₂) tau = tau • (fourGrp x₁ x₂ : Set G) := by
  refine p0_orbit_R hc (Subgroup.subset_closure (by simp)) (p0g_rho_tau hc) ?_
  refine ⟨x₁, (p0_x₁_x₂_mem_R hc.toCtx8c).1, ?_⟩
  intro hx
  have hconj : x₁ * tau * x₁⁻¹ = x₁ ^ 2 * tau := p0g_x₁_conj_tau hc
  rw [hconj] at hx
  have hx2 : x₁ ^ 2 = 1 := by
    have : x₁ ^ 2 * tau = 1 * tau := by rw [hx, one_mul]
    exact mul_right_cancel this
  have hx1sq : x₁ ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf x₁ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hc.wreath.ord_x₁] at hdvd
    omega
  exact hx1sq hx2

theorem p0_tM_O (hc : Ctx8d t L S x₁ x₂ lam rho tau) :
    conjIn (ctxO t tau x₁ x₂) t = conjIn (ctxM t tau x₁ x₂) t := by
  apply le_antisymm
  · rintro w ⟨k, hkO, rfl⟩
    exact ⟨k, p0_O_le_M t tau x₁ x₂ hkO, rfl⟩
  · rw [hc.tM]
    have hsubV : t • (fourGrp x₁ x₂ : Set G) ⊆ conjIn (ctxO t tau x₁ x₂) t := by
      rw [← p0_tR hc]
      rintro y ⟨k, hkR, rfl⟩
      exact ⟨k, hc.R_le_O hkR, rfl⟩
    have hsubW : (t * tau) • (fourGrp x₁ x₂ : Set G) ⊆ conjIn (ctxO t tau x₁ x₂) t := by
      intro y hy
      rw [← p0_ttauR hc] at hy
      obtain ⟨r'', hr''R, rfl⟩ := hy
      have hne : ctxR t tau x₁ x₂ ≠ ctxO t tau x₁ x₂ := by
        intro heq
        have hcard : Nat.card ↥(ctxR t tau x₁ x₂) = Nat.card ↥(ctxO t tau x₁ x₂) := by
          rw [heq]
        rw [hc.card_R, hc.card_O] at hcard
        norm_num at hcard
      have hex : ∃ g ∈ ctxO t tau x₁ x₂, g ∉ ctxR t tau x₁ x₂ := by
        by_contra h
        push Not at h
        exact hne (le_antisymm hc.R_le_O (fun g hg => h g hg))
      obtain ⟨g, hgO, hgR⟩ := hex
      have hgM : g ∈ ctxM t tau x₁ x₂ := p0_O_le_M t tau x₁ x₂ hgO
      have hgnotV : g * t * g⁻¹ ∉ t • (fourGrp x₁ x₂ : Set G) := by
        intro h
        exact hgR ((p0_mem_R_iff hc.toCtx8c hgO).mpr h)
      have hgconj : g * t * g⁻¹ ∈ conjIn (ctxM t tau x₁ x₂) t := ⟨g, hgM, rfl⟩
      rw [hc.tM] at hgconj
      have hgttauV : g * t * g⁻¹ ∈ (t * tau) • (fourGrp x₁ x₂ : Set G) := by
        rcases hgconj with h | h
        · exact absurd h hgnotV
        · exact h
      rw [← p0_ttauR hc] at hgttauV
      obtain ⟨r', hr'R, hr'_eq⟩ := hgttauV
      refine ⟨r'' * r'⁻¹ * g, ?_, ?_⟩
      · exact Subgroup.mul_mem _
          (Subgroup.mul_mem _ (hc.R_le_O hr''R) (Subgroup.inv_mem _ (hc.R_le_O hr'R))) hgO
      · calc (r'' * r'⁻¹ * g) * t * (r'' * r'⁻¹ * g)⁻¹
            = r'' * (r'⁻¹ * (g * t * g⁻¹) * r') * r''⁻¹ := by group
          _ = r'' * (r'⁻¹ * (r' * (t * tau) * r'⁻¹) * r') * r''⁻¹ := by rw [← hr'_eq]
          _ = r'' * (t * tau) * r''⁻¹ := by group
    rintro w (hw | hw)
    · exact hsubV hw
    · exact hsubW hw

theorem p0_tauM (hc : Ctx8d t L S x₁ x₂ lam rho tau) :
    conjIn (ctxM t tau x₁ x₂) tau = tau • (fourGrp x₁ x₂ : Set G) := by
  apply le_antisymm
  · rintro w ⟨g, hgM, rfl⟩
    exact p0_tau_conj_mem hc.toCtx8c hgM
  · intro w hw
    rw [← p0_tauR hc] at hw
    obtain ⟨k, hkR, rfl⟩ := hw
    exact ⟨k, hc.normal_R.1 hkR, rfl⟩

theorem p0_tauO (hc : Ctx8d t L S x₁ x₂ lam rho tau) :
    conjIn (ctxO t tau x₁ x₂) tau = tau • (fourGrp x₁ x₂ : Set G) := by
  apply le_antisymm
  · rintro w ⟨g, hgO, rfl⟩
    have h : g * tau * g⁻¹ ∈ conjIn (ctxM t tau x₁ x₂) tau :=
      ⟨g, p0_O_le_M t tau x₁ x₂ hgO, rfl⟩
    rw [p0_tauM hc] at h
    exact h
  · intro w hw
    rw [← p0_tauR hc] at hw
    obtain ⟨k, hkR, rfl⟩ := hw
    exact ⟨k, hc.R_le_O hkR, rfl⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
