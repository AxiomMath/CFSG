module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ACtxNorm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ATauC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AB1B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AE4T

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

section Centre

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem z_mem_wreath (h : Ctx0 t L S x₁ x₂ lam rho) :
    (x₁ * x₂) ^ 2 ∈ wreathGrp x₁ x₂ lam := by
  have hx₁ : x₁ ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
  have hx₂ : x₂ ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
  exact Subgroup.pow_mem _ (Subgroup.mul_mem _ hx₁ hx₂) 2

theorem z_comm_wreath (h : Ctx0 t L S x₁ x₂ lam rho) {u : G} (hu : u ∈ wreathGrp x₁ x₂ lam) :
    u * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * u := by
  have hZ := (h.wreath.center_eq).1
  have hzmem : (x₁ * x₂) ^ 2 ∈ wreathGrp x₁ x₂ lam ⊓
      centralizer (wreathGrp x₁ x₂ lam : Set G) := by
    rw [hZ]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzmem).2) u hu

theorem tau_comm_z' (h : Ctx0 t L S x₁ x₂ lam rho) (ht : CtxTauFacts t L S x₁ x₂ lam rho tau) :
    tau * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * tau := by
  have hx₁B : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂B : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have h1 : tau * (x₁ * x₂) * tau⁻¹ = (x₁ * x₂)⁻¹ :=
    tau_inv_base h ht (Subgroup.mul_mem _ hx₁B hx₂B)
  have h2 : tau * (x₁ * x₂) ^ 2 * tau⁻¹ = (x₁ * x₂)⁻¹ ^ 2 := by
    rw [← conj_pow, h1]
  have hz2 : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := (z_mul_self_ne_one h).1
  have h3 : (x₁ * x₂)⁻¹ ^ 2 = (x₁ * x₂) ^ 2 := by
    rw [inv_pow]
    exact inv_eq_of_mul_eq_one_right hz2
  calc tau * (x₁ * x₂) ^ 2 = (tau * (x₁ * x₂) ^ 2 * tau⁻¹) * tau := by group
    _ = (x₁ * x₂) ^ 2 * tau := by rw [h2, h3]

theorem ctx_z_central (h : Ctx0 t L S x₁ x₂ lam rho)
    (ht : CtxTauFacts t L S x₁ x₂ lam rho tau) :
    ∀ s ∈ S, s * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * s := by
  have hx₁T : x₁ ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
  have hx₂T : x₂ ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
  have hlamT : lam ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
  have hle : S ≤ centralizer ({(x₁ * x₂) ^ 2} : Set G) := by
    intro s hs
    rw [ht.S_eq] at hs
    refine (sup_le ?_ ?_ : twoCore t ⊔ m12Grp x₁ x₂ lam tau ≤
      centralizer ({(x₁ * x₂) ^ 2} : Set G)) hs
    · intro p hp
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact twoCore_commute h.hyp p hp _ (y_z_mem_L h).2
    · refine (Subgroup.closure_le (K := centralizer ({(x₁ * x₂) ^ 2} : Set G))).mpr ?_
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hg with hg | hg | hg | hg
      · rw [hg]
        exact z_comm_wreath h hx₁T
      · rw [hg]
        exact z_comm_wreath h hx₂T
      · rw [hg]
        exact z_comm_wreath h hlamT
      · rw [hg]
        exact tau_comm_z' h ht
  intro s hs
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hs)

theorem ctx_center_ge (h : Ctx0 t L S x₁ x₂ lam rho)
    (ht : CtxTauFacts t L S x₁ x₂ lam rho tau) :
    closure {t, (x₁ * x₂) ^ 2} ≤ S ⊓ centralizer (S : Set G) := by
  refine (Subgroup.closure_le (K := S ⊓ centralizer (S : Set G))).mpr ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with hg | hg
  · rw [hg]
    refine Subgroup.mem_inf.mpr ⟨twoCore_le_S h h.hyp.mem_twoCore, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact mem_invCent_iff.mp (h.le_invCent hs)
  · rw [hg]
    refine Subgroup.mem_inf.mpr ⟨wreathGrp_le_S h (z_mem_wreath h), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact ctx_z_central h ht s hs

theorem ctx_normal_W (h : Ctx0 t L S x₁ x₂ lam rho)
    (ht : CtxTauFacts t L S x₁ x₂ lam rho tau) : NormalIn (ctxW t x₁ x₂) S := by
  have hx₁B : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂B : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hτH : tau ∈ invCent t := h.le_invCent ht.tau_mem
  have hlamH : lam ∈ invCent t := L_le_invCent h.hyp (generators_mem_L h).2.2
  have hlamN : ∀ w ∈ baseGrp x₁ x₂, lam * w * lam⁻¹ ∈ baseGrp x₁ x₂ :=
    conj_mem_baseGrp_of_gens (by rw [h.wreath.conj_x₁]; exact hx₂B)
      (by rw [wr_lam_conj_x₂ h.wreath]; exact hx₁B)
  have hWn : ctxW t x₁ x₂ ≤ normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) :=
    Subgroup.le_normalizer
  have hlam : lam ∈ normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) :=
    mem_normalizer_of_conj_mem (conj_mem_sup (K₁ := twoCore t) (K₂ := baseGrp x₁ x₂)
      (fun p hp => twoCore_conj_mem t hlamH hp) hlamN)
  have htau : tau ∈ normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) := by
    refine mem_normalizer_of_conj_mem (conj_mem_sup (K₁ := twoCore t) (K₂ := baseGrp x₁ x₂)
      (fun p hp => twoCore_conj_mem t hτH hp) (fun b hb => ?_))
    rw [tau_inv_base h ht hb]
    exact Subgroup.inv_mem _ hb
  have hSn : S ≤ normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) := by
    intro s hs
    rw [ht.S_eq] at hs
    refine (sup_le (le_sup_left.trans hWn) ?_ : twoCore t ⊔ m12Grp x₁ x₂ lam tau ≤
      normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G)) hs
    refine (Subgroup.closure_le (K := normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G))).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg | hg
    · rw [hg]
      exact hWn (Subgroup.mem_sup_right hx₁B)
    · rw [hg]
      exact hWn (Subgroup.mem_sup_right hx₂B)
    · rw [hg]
      exact hlam
    · rw [hg]
      exact htau
  refine ⟨sup_le (twoCore_le_S h) ((pt_base_le_wreath x₁ x₂ lam).trans (wreathGrp_le_S h)),
    fun g hg k hk => ?_⟩
  exact (Subgroup.mem_normalizer_iff.mp (hSn hg) k).mp hk

theorem ctx_center_le (h : Ctx0 t L S x₁ x₂ lam rho) (hi : CtxIdxFacts t L S x₁ x₂ lam)
    (ht : CtxTauFacts t L S x₁ x₂ lam rho tau) :
    S ⊓ centralizer (S : Set G) ≤ twoCore t ⊔ zpowers ((x₁ * x₂) ^ 2) := by
  intro c hc
  obtain ⟨hcS, hcC⟩ := Subgroup.mem_inf.mp hc
  have hcC' := Subgroup.mem_centralizer_iff.mp hcC
  have hQS : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ S := sup_le (twoCore_le_S h) (wreathGrp_le_S h)
  have hτS := ht.tau_mem
  have hτH : tau ∈ invCent t := h.le_invCent hτS
  obtain ⟨hx₁L, -, -⟩ := generators_mem_L h
  have hx₁T : x₁ ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
  have hx₁B : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂B : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hxB : x₁ * x₂ ∈ baseGrp x₁ x₂ := Subgroup.mul_mem _ hx₁B hx₂B
  have hcQ : c ∈ twoCore t ⊔ wreathGrp x₁ x₂ lam := by
    by_contra hcQ
    rcases mem_or_mem_or_mul_mem_of_relIndex_two hQS hi.index_PT hcS (S.inv_mem hτS) with
      h1 | h1 | h1
    · exact hcQ h1
    · apply ht.tau_not_mem
      have h2 := (twoCore t ⊔ wreathGrp x₁ x₂ lam).inv_mem h1
      rw [inv_inv] at h2
      exact sup_le_sup_left (wreathGrp_le_L_ctx0 h) _ h2
    · obtain ⟨p, hp, u, hu, hpu⟩ := (mem_sup_iff_of_commute (pt_comm_wreath h)).mp h1
      have hc_eq : c = p * u * tau := by
        calc c = (c * tau⁻¹) * tau := by group
          _ = p * u * tau := by rw [hpu]
      have e1 : c * x₁ * c⁻¹ = x₁ := by
        have h3 := hcC' x₁ (wreathGrp_le_S h hx₁T)
        calc c * x₁ * c⁻¹ = (x₁ * c) * c⁻¹ := by rw [h3]
          _ = x₁ := by group
      have huL : u ∈ L := wreathGrp_le_L_ctx0 h hu
      have hxL : u * x₁⁻¹ * u⁻¹ ∈ L :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ huL (Subgroup.inv_mem _ hx₁L))
          (Subgroup.inv_mem _ huL)
      have hpc : p * (u * x₁⁻¹ * u⁻¹) = (u * x₁⁻¹ * u⁻¹) * p :=
        twoCore_commute h.hyp p hp _ hxL
      have e2 : c * x₁ * c⁻¹ = u * x₁⁻¹ * u⁻¹ := by
        rw [hc_eq]
        calc p * u * tau * x₁ * (p * u * tau)⁻¹
            = p * u * (tau * x₁ * tau⁻¹) * u⁻¹ * p⁻¹ := by group
          _ = p * u * x₁⁻¹ * u⁻¹ * p⁻¹ := by rw [ht.tau_x₁]
          _ = (p * (u * x₁⁻¹ * u⁻¹)) * p⁻¹ := by group
          _ = ((u * x₁⁻¹ * u⁻¹) * p) * p⁻¹ := by rw [hpc]
          _ = u * x₁⁻¹ * u⁻¹ := by group
      have e3 : u * x₁⁻¹ * u⁻¹ = x₁ := e2.symm.trans e1
      apply wreath_conj_x₁_ne_inv h.wreath hu
      calc u * x₁ * u⁻¹ = (u * x₁⁻¹ * u⁻¹)⁻¹ := by group
        _ = x₁⁻¹ := by rw [e3]
  have hcZ : c ∈ twoCore t ⊔ zpowers (x₁ * x₂) := by
    rw [← pt_center h]
    refine Subgroup.mem_inf.mpr ⟨hcQ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact hcC' s (hQS hs)
  have hZB : zpowers (x₁ * x₂) ≤ baseGrp x₁ x₂ := Subgroup.zpowers_le.mpr hxB
  have hZL : zpowers (x₁ * x₂) ≤ L := hZB.trans (pt_base_le_L h)
  have hPcomm : ∀ a ∈ twoCore t, ∀ b ∈ zpowers (x₁ * x₂), a * b = b * a :=
    fun a ha b hb => twoCore_commute h.hyp a ha b (hZL hb)
  obtain ⟨p, hp, w, hw, rfl⟩ := (mem_sup_iff_of_commute hPcomm).mp hcZ
  have hwB : w ∈ baseGrp x₁ x₂ := hZB hw
  have hwL : w ∈ L := hZL hw
  have e : tau * (p * w) * tau⁻¹ = p * w := by
    calc tau * (p * w) * tau⁻¹ = ((p * w) * tau) * tau⁻¹ := by rw [hcC' tau hτS]
      _ = p * w := by group
  have e' : tau * (p * w) * tau⁻¹ = (tau * p * tau⁻¹) * (tau * w * tau⁻¹) := by group
  rw [e', tau_inv_base h ht hwB] at e
  have hq : p⁻¹ * (tau * p * tau⁻¹) = w * w := by
    calc p⁻¹ * (tau * p * tau⁻¹) = p⁻¹ * ((tau * p * tau⁻¹) * w⁻¹) * w := by group
      _ = p⁻¹ * (p * w) * w := by rw [e]
      _ = w * w := by group
  have hqP : p⁻¹ * (tau * p * tau⁻¹) ∈ twoCore t :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hp) (twoCore_conj_mem t hτH hp)
  have hww1 : w * w = 1 := by
    have hmem : w * w ∈ twoCore t ⊓ L :=
      ⟨by rw [← hq]; exact hqP, Subgroup.mul_mem _ hwL hwL⟩
    rw [h.hyp.twoCore_inf, Subgroup.mem_bot] at hmem
    exact hmem
  have hord : orderOf (x₁ * x₂) = 4 := by
    rw [← Nat.card_zpowers]
    exact (h.wreath.center_eq).2
  have hz : (x₁ * x₂) ^ 2 ∈ zpowers ((x₁ * x₂) ^ 2) := Subgroup.mem_zpowers _
  rcases pt_eq_one_or_sq_of_mem_zpowers hord hw hww1 with hw1 | hw1
  · rw [hw1, mul_one]
    exact Subgroup.mem_sup_left hp
  · rw [hw1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right hz)

theorem ctx_center_omega (h : Ctx0 t L S x₁ x₂ lam rho) (hi : CtxIdxFacts t L S x₁ x₂ lam)
    (ht : CtxTauFacts t L S x₁ x₂ lam rho tau) :
    ∀ g ∈ S ⊓ centralizer (S : Set G), g ^ 2 = 1 → g ∈ closure {t, (x₁ * x₂) ^ 2} := by
  intro g hg hg2
  have hgle := ctx_center_le h hi ht hg
  have hQS : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ S := sup_le (twoCore_le_S h) (wreathGrp_le_S h)
  have hQ : twoCore t ⊔ zpowers ((x₁ * x₂) ^ 2) ≤ twoCore t ⊔ wreathGrp x₁ x₂ lam :=
    sup_le_sup_left (Subgroup.zpowers_le.mpr (z_mem_wreath h)) _
  refine pt_center_omega h g ?_ hg2
  refine Subgroup.mem_inf.mpr ⟨hQ hgle, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hg).2) s (hQS hs)

end Centre

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
