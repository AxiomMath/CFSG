module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

private abbrev wmodDecEq : DecidableEq WMod := WMod.equivProd.decidableEq

attribute [local instance 2000] wmodDecEq

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private def sigmaModel : WMod →* WMod where
  toFun m := ⟨-m.a, -m.b, m.i⟩
  map_one' := by decide +kernel
  map_mul' := by
    intro x y
    obtain ⟨a, b, i⟩ := x
    obtain ⟨c, d, k⟩ := y
    revert a b i c d k
    decide +kernel

private theorem conj_mem_L (h : Ctx t L S x₁ x₂ lam rho tau) {g : G} (hg : g ∈ invCent t)
    {x : G} (hx : x ∈ L) : g * x * g⁻¹ ∈ L := by
  have hxH : x ∈ invCent t := L_le_invCent h.hyp hx
  have hmem : (⟨g, hg⟩ : ↥(invCent t)) * (⟨x, hxH⟩ : ↥(invCent t)) *
      (⟨g, hg⟩ : ↥(invCent t))⁻¹ ∈ L.subgroupOf (invCent t) :=
    h.hyp.normal.conj_mem ⟨x, hxH⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hg⟩
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

theorem ncard_sq_roots_tz_le (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = t) :
    {s : G | s ∈ S ∧ s ^ 2 = t * (x₁ * x₂) ^ 2}.ncard ≤ 8 := by
  classical
  obtain ⟨φ, hφinj, hφrange, hφx₁, hφx₂, hφlam⟩ := h.wreath.exists_embedding
  have ht2 : t * t = 1 := t_mul_self h.hyp
  have htauH : tau ∈ invCent t := h.toCtx0.le_invCent h.tau_mem
  have ht_tau : t * tau = tau * t := (mem_invCent_iff.mp htauH).symm
  have htau_inv : tau⁻¹ = t * tau := by
    apply inv_eq_of_mul_eq_one_right
    calc tau * (t * tau) = tau * t * tau := by group
      _ = (t * tau) * tau := by rw [← ht_tau]
      _ = t * (tau * tau) := by group
      _ = t * t := by rw [← pow_two, h44]
      _ = 1 := ht2
  have hP_cases : ∀ p ∈ twoCore t, p = 1 ∨ p = t := by
    intro p hp
    rw [h43, mem_zpowers_iff_mem_range_orderOf, h.hyp.ord_t] at hp
    simp only [Finset.mem_image, Finset.mem_range] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    interval_cases j
    · exact Or.inl (pow_zero t)
    · exact Or.inr (pow_one t)
  have hP_sq : ∀ p ∈ twoCore t, p * p = 1 := by
    intro p hp
    rcases hP_cases p hp with rfl | rfl
    · rw [one_mul]
    · exact ht2
  have hP_comm_H : ∀ p ∈ twoCore t, ∀ g ∈ invCent t, p * g = g * p := by
    intro p hp g hg
    rcases hP_cases p hp with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (mem_invCent_iff.mp hg).symm
  have hx1L : x₁ ∈ L := (generators_mem_L h.toCtx0).1
  have hx2L : x₂ ∈ L := (generators_mem_L h.toCtx0).2.1
  have hlamL : lam ∈ L := (generators_mem_L h.toCtx0).2.2
  have hT_le_L : wreathGrp x₁ x₂ lam ≤ L := by
    rw [wreathGrp, Subgroup.closure_le]
    rintro y (hy : y ∈ ({x₁, x₂, lam} : Set G))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact hx1L
    · exact hx2L
    · exact hlamL
  have hPT_comm : ∀ a ∈ twoCore t, ∀ b ∈ wreathGrp x₁ x₂ lam, a * b = b * a :=
    fun a ha b hb => twoCore_commute h.hyp a ha b (hT_le_L hb)
  have hK_le_PL : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ twoCore t ⊔ L :=
    sup_le le_sup_left (le_trans hT_le_L le_sup_right)
  have hK_le_S : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ S := by
    rw [← h.toCtx0.inf_PL]; exact inf_le_left
  have htau_notMem_K : tau ∉ twoCore t ⊔ wreathGrp x₁ x₂ lam :=
    fun hk => h.tau_not_mem (hK_le_PL hk)
  have hzL : (x₁ * x₂) ^ 2 ∈ L := (y_z_mem_L h.toCtx0).2
  have htz_notMem_L : t * (x₁ * x₂) ^ 2 ∉ L := by
    intro hmem
    have htl : t ∈ L := by
      have h2 : (t * (x₁ * x₂) ^ 2) * ((x₁ * x₂) ^ 2)⁻¹ ∈ L :=
        Subgroup.mul_mem L hmem (Subgroup.inv_mem L hzL)
      rwa [mul_assoc, mul_inv_cancel, mul_one] at h2
    exact t_not_mem_L h.hyp htl
  have hσW : ∀ m : WMod, φ (sigmaModel m) = tau * φ m * tau⁻¹ := by
    intro m
    have hm : m ∈ Subgroup.closure ({WMod.wx₁, WMod.wx₂, WMod.wlam} : Set WMod) := by
      have h2 : Subgroup.closure ({WMod.wx₁, WMod.wx₂, WMod.wlam} : Set WMod) = ⊤ := by
        change wreathGrp WMod.wx₁ WMod.wx₂ WMod.wlam = ⊤
        exact WMod.closure_eq_top
      rw [h2]; exact Subgroup.mem_top m
    induction hm using Subgroup.closure_induction with
    | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · have hsw : sigmaModel WMod.wx₁ = WMod.wx₁⁻¹ := by decide +kernel
          rw [hsw, map_inv (f := φ), hφx₁, h.tau_x₁]
        · have hsw : sigmaModel WMod.wx₂ = WMod.wx₂⁻¹ := by decide +kernel
          rw [hsw, map_inv (f := φ), hφx₂, h.tau_x₂]
        · have hsw : sigmaModel WMod.wlam = WMod.wlam := by decide +kernel
          rw [hsw, hφlam, h.tau_lam]; group
    | one => simp
    | mul x y hx hy ihx ihy =>
        calc φ (sigmaModel (x * y))
            = φ (sigmaModel x * sigmaModel y) := by rw [map_mul (f := sigmaModel)]
          _ = φ (sigmaModel x) * φ (sigmaModel y) := by rw [map_mul (f := φ)]
          _ = (tau * φ x * tau⁻¹) * (tau * φ y * tau⁻¹) := by rw [ihx, ihy]
          _ = tau * φ (x * y) * tau⁻¹ := by rw [map_mul (f := φ)]; group
    | inv x hx ihx =>
        calc φ (sigmaModel (x⁻¹))
            = φ ((sigmaModel x)⁻¹) := by rw [map_inv (f := sigmaModel)]
          _ = (φ (sigmaModel x))⁻¹ := by rw [map_inv (f := φ)]
          _ = (tau * φ x * tau⁻¹)⁻¹ := by rw [ihx]
          _ = tau * φ (x⁻¹) * tau⁻¹ := by rw [map_inv (f := φ)]; group
  have hφwz : φ ((WMod.wx₁ * WMod.wx₂) ^ 2) = (x₁ * x₂) ^ 2 := by
    rw [map_pow, map_mul, hφx₁, hφx₂]
  let U₀ : Finset (Fin 4 × Fin 4 × Fin 2) :=
    Finset.univ.filter (fun q =>
      (⟨q.1, q.2.1, q.2.2⟩ : WMod) * sigmaModel ⟨q.1, q.2.1, q.2.2⟩ =
        (WMod.wx₁ * WMod.wx₂) ^ 2)
  have hU₀card : U₀.card = 4 := by decide +kernel
  have hAcard :
      ((U₀.image (fun q => φ (⟨q.1, q.2.1, q.2.2⟩ : WMod) * tau)) ∪
        (U₀.image (fun q => t * φ (⟨q.1, q.2.1, q.2.2⟩ : WMod) * tau))).card ≤ 8 := by
    calc ((U₀.image (fun q => φ (⟨q.1, q.2.1, q.2.2⟩ : WMod) * tau)) ∪
            (U₀.image (fun q => t * φ (⟨q.1, q.2.1, q.2.2⟩ : WMod) * tau))).card
        ≤ (U₀.image (fun q => φ (⟨q.1, q.2.1, q.2.2⟩ : WMod) * tau)).card +
          (U₀.image (fun q => t * φ (⟨q.1, q.2.1, q.2.2⟩ : WMod) * tau)).card :=
          Finset.card_union_le _ _
      _ ≤ U₀.card + U₀.card := add_le_add Finset.card_image_le Finset.card_image_le
      _ = 8 := by rw [hU₀card]
  have hsub : {s : G | s ∈ S ∧ s ^ 2 = t * (x₁ * x₂) ^ 2} ⊆
      (↑(U₀.image (fun q => φ (⟨q.1, q.2.1, q.2.2⟩ : WMod) * tau) ∪
        U₀.image (fun q => t * φ (⟨q.1, q.2.1, q.2.2⟩ : WMod) * tau)) : Set G) := by
    intro s hs
    obtain ⟨hsS, hs2⟩ := hs
    have hs_notMem_K : s ∉ twoCore t ⊔ wreathGrp x₁ x₂ lam := by
      intro hsK
      obtain ⟨p, hp, u, hu, hs_eqp⟩ := (mem_sup_iff_of_commute hPT_comm).mp hsK
      have hpu : p * u = u * p := hPT_comm p hp u hu
      have hsq : s ^ 2 = u * u := by
        rw [hs_eqp, pow_two]
        calc (p * u) * (p * u) = p * (u * p) * u := by group
          _ = p * (p * u) * u := by rw [← hpu]
          _ = (p * p) * (u * u) := by group
          _ = u * u := by rw [hP_sq p hp, one_mul]
      exact htz_notMem_L
        (by rw [← hs2, hsq]; exact Subgroup.mul_mem L (hT_le_L hu) (hT_le_L hu))
    have hstau_K : s * tau ∈ twoCore t ⊔ wreathGrp x₁ x₂ lam := by
      rcases mem_or_mem_or_mul_mem_of_relIndex_two (K := twoCore t ⊔ wreathGrp x₁ x₂ lam)
          hK_le_S h.index_PT hsS h.tau_mem with h1 | h2 | h3
      · exact absurd h1 hs_notMem_K
      · exact absurd h2 htau_notMem_K
      · exact h3
    obtain ⟨k, hk, hsk⟩ : ∃ k ∈ twoCore t ⊔ wreathGrp x₁ x₂ lam, s = k * tau := by
      refine ⟨(s * tau) * t, ?_, ?_⟩
      · exact (twoCore t ⊔ wreathGrp x₁ x₂ lam).mul_mem hstau_K
          (Subgroup.mem_sup_left h.hyp.mem_twoCore)
      · calc s = (s * tau) * tau⁻¹ := by group
          _ = (s * tau) * (t * tau) := by rw [htau_inv]
          _ = ((s * tau) * t) * tau := by group
    obtain ⟨p, hp, u, hu, hk_eq⟩ := (mem_sup_iff_of_commute hPT_comm).mp hk
    have hs_eq2 : s = p * u * tau := by rw [hsk, hk_eq]
    set su : G := tau * u * tau⁻¹ with hsu_def
    have hsuL : su ∈ L := conj_mem_L h htauH (hT_le_L hu)
    have hcommA : p * (u * tau) = (u * tau) * p :=
      hP_comm_H p hp (u * tau)
        ((invCent t).mul_mem (L_le_invCent h.hyp (hT_le_L hu)) htauH)
    have htau_u_tau : tau * u * tau = su * t := by
      rw [hsu_def, ← h44]; group
    have htu : t * u = u * t :=
      (mem_invCent_iff.mp (L_le_invCent h.hyp (hT_le_L hu))).symm
    have hts : t * su = su * t :=
      (mem_invCent_iff.mp (L_le_invCent h.hyp hsuL)).symm
    have hs_sq : s ^ 2 = t * (u * su) := by
      rw [hs_eq2, pow_two]
      calc (p * u * tau) * (p * u * tau)
          = (p * (u * tau)) * (p * (u * tau)) := by group
        _ = (p * p) * ((u * tau) * (u * tau)) := by
              calc (p * (u * tau)) * (p * (u * tau))
                  = p * ((u * tau) * p) * (u * tau) := by group
                _ = p * (p * (u * tau)) * (u * tau) := by rw [← hcommA]
                _ = (p * p) * ((u * tau) * (u * tau)) := by group
        _ = (u * tau) * (u * tau) := by rw [hP_sq p hp, one_mul]
        _ = u * (tau * u * tau) := by group
        _ = u * (su * t) := by rw [htau_u_tau]
        _ = t * (u * su) := by
              calc u * (su * t) = u * (t * su) := by rw [hts]
                _ = (u * t) * su := by group
                _ = (t * u) * su := by rw [htu]
                _ = t * (u * su) := by group
    have hu_su_eq : u * su = (x₁ * x₂) ^ 2 := by
      apply mul_left_cancel (a := t)
      rw [← hs_sq, hs2]
    have hu_range : u ∈ φ.range := by rw [hφrange]; exact hu
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hu_range
    have hsu_eq : su = φ (sigmaModel m) := by rw [hsu_def, ← hm, hσW m]
    have hu_su_model : φ (m * sigmaModel m) = (x₁ * x₂) ^ 2 := by
      rw [map_mul, hm, ← hsu_eq]
      exact hu_su_eq
    have hm_sigma : m * sigmaModel m = (WMod.wx₁ * WMod.wx₂) ^ 2 := by
      apply hφinj
      simpa only [hu_su_model, hφwz]
    have hm_triple : (m.a, m.b, m.i) ∈ U₀ := by
      simp only [U₀, Finset.mem_filter, Finset.mem_univ, true_and]
      have htri : (⟨m.a, m.b, m.i⟩ : WMod) = m := by cases m; rfl
      rw [htri]
      exact hm_sigma
    have hsA : s ∈ (U₀.image (fun q => φ (⟨q.1, q.2.1, q.2.2⟩ : WMod) * tau)) ∪
        (U₀.image (fun q => t * φ (⟨q.1, q.2.1, q.2.2⟩ : WMod) * tau)) := by
      rw [hs_eq2]
      rcases hP_cases p hp with hp1 | hpt
      · rw [hp1, one_mul]
        refine Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨(m.a, m.b, m.i), hm_triple, ?_⟩))
        show φ (⟨m.a, m.b, m.i⟩ : WMod) * tau = u * tau
        rw [show (⟨m.a, m.b, m.i⟩ : WMod) = m from by cases m; rfl, hm]
      · rw [hpt]
        refine Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨(m.a, m.b, m.i), hm_triple, ?_⟩))
        show t * φ (⟨m.a, m.b, m.i⟩ : WMod) * tau = t * u * tau
        rw [show (⟨m.a, m.b, m.i⟩ : WMod) = m from by cases m; rfl, hm]
    simpa using hsA
  calc {s : G | s ∈ S ∧ s ^ 2 = t * (x₁ * x₂) ^ 2}.ncard
      ≤ (↑(U₀.image (fun q => φ (⟨q.1, q.2.1, q.2.2⟩ : WMod) * tau) ∪
          U₀.image (fun q => t * φ (⟨q.1, q.2.1, q.2.2⟩ : WMod) * tau)) : Set G).ncard :=
        Set.ncard_le_ncard hsub
    _ = (U₀.image (fun q => φ (⟨q.1, q.2.1, q.2.2⟩ : WMod) * tau) ∪
          U₀.image (fun q => t * φ (⟨q.1, q.2.1, q.2.2⟩ : WMod) * tau)).card :=
        Set.ncard_coe_finset _
    _ ≤ 8 := hAcard

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
