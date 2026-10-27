module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ATauA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AF1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AB1A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ACtxSteps

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

namespace S4A

section Generic

variable {G : Type} [Group G]

theorem conj_mem_sup {K₁ K₂ : Subgroup G} {g : G} (h1 : ∀ k ∈ K₁, g * k * g⁻¹ ∈ K₁)
    (h2 : ∀ k ∈ K₂, g * k * g⁻¹ ∈ K₂) : ∀ k ∈ K₁ ⊔ K₂, g * k * g⁻¹ ∈ K₁ ⊔ K₂ := by
  intro k hk
  have hle : K₁ ⊔ K₂ ≤ (K₁ ⊔ K₂).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun k hk => Subgroup.mem_sup_left (h1 k hk))
      (fun k hk => Subgroup.mem_sup_right (h2 k hk))
  exact Subgroup.mem_comap.mp (hle hk)

theorem conj_mem_zpowers {g a : G} (h : g * a * g⁻¹ = a) :
    ∀ k ∈ zpowers a, g * k * g⁻¹ ∈ zpowers a := by
  intro k hk
  have hle : zpowers a ≤ (zpowers a).comap (MulAut.conj g).toMonoidHom :=
    Subgroup.zpowers_le.mpr (by
      show g * a * g⁻¹ ∈ zpowers a
      rw [h]
      exact Subgroup.mem_zpowers a)
  exact Subgroup.mem_comap.mp (hle hk)

theorem comm_of_mul_comm {p l b : G} (hpb : p * b = b * p) (hb : b * (p * l) = (p * l) * b) :
    b * l = l * b := by
  calc b * l = p⁻¹ * (p * b) * l := by group
    _ = p⁻¹ * (b * p) * l := by rw [hpb]
    _ = p⁻¹ * (b * (p * l)) := by group
    _ = p⁻¹ * ((p * l) * b) := by rw [hb]
    _ = l * b := by group

end Generic

section Norm

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem mem_PL_or_mul_tau (h : Ctx0 t L S x₁ x₂ lam rho) (hi : CtxIdxFacts t L S x₁ x₂ lam)
    (ht : CtxTauFacts t L S x₁ x₂ lam rho tau) {g : G} (hg : g ∈ invCent t) :
    g ∈ twoCore t ⊔ L ∨ g * tau⁻¹ ∈ twoCore t ⊔ L := by
  have hτH : tau ∈ invCent t := h.le_invCent ht.tau_mem
  have hKH : twoCore t ⊔ L ≤ invCent t := sup_le (twoCore_le_invCent t) (L_le_invCent h.hyp)
  rcases mem_or_mem_or_mul_mem_of_relIndex_two hKH hi.relIndex_two hg
    ((invCent t).inv_mem hτH) with h1 | h1 | h1
  · exact Or.inl h1
  · exact absurd (by simpa using (twoCore t ⊔ L).inv_mem h1) ht.tau_not_mem
  · exact Or.inr h1

theorem tau_inv_base (h : Ctx0 t L S x₁ x₂ lam rho) (ht : CtxTauFacts t L S x₁ x₂ lam rho tau)
    {b : G} (hb : b ∈ baseGrp x₁ x₂) : tau * b * tau⁻¹ = b⁻¹ :=
  alpha_inv_of_mem_baseGrp (K := G) h.wreath (α := MulAut.conj tau)
    (by simpa [MulAut.conj_apply] using ht.tau_x₁) (by simpa [MulAut.conj_apply] using ht.tau_x₂)
    hb

theorem tau_norm_base (h : Ctx0 t L S x₁ x₂ lam rho) (ht : CtxTauFacts t L S x₁ x₂ lam rho tau) :
    tau ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem (fun b hb => ?_)
  rw [tau_inv_base h ht hb]
  exact Subgroup.inv_mem _ hb

theorem no_inverting_in_L (h : Ctx0 t L S x₁ x₂ lam rho) {l : G} (hl : l ∈ L)
    (hinv : ∀ b ∈ baseGrp x₁ x₂, l * b * l⁻¹ = b⁻¹) : False := by
  have hx₁B : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂B : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₁₂B : x₁ * x₂ ∈ baseGrp x₁ x₂ := Subgroup.mul_mem _ hx₁B hx₂B
  have hy2 : x₁ ^ 2 * x₁ ^ 2 = 1 := (y_mul_self_ne_one h.wreath).1
  have hy1 : x₁ ^ 2 ≠ 1 := (y_mul_self_ne_one h.wreath).2
  have hz2 : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := (z_mul_self_ne_one h).1
  have hly : l * x₁ ^ 2 = x₁ ^ 2 * l := by
    have e : l * x₁ ^ 2 * l⁻¹ = x₁ ^ 2 := by
      rw [← conj_pow, hinv x₁ hx₁B, inv_pow]
      exact inv_eq_of_mul_eq_one_right hy2
    calc l * x₁ ^ 2 = (l * x₁ ^ 2 * l⁻¹) * l := by group
      _ = x₁ ^ 2 * l := by rw [e]
  have hlz : l * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * l := by
    have e : l * (x₁ * x₂) ^ 2 * l⁻¹ = (x₁ * x₂) ^ 2 := by
      rw [← conj_pow, hinv (x₁ * x₂) hx₁₂B, inv_pow]
      exact inv_eq_of_mul_eq_one_right hz2
    calc l * (x₁ * x₂) ^ 2 = (l * (x₁ * x₂) ^ 2 * l⁻¹) * l := by group
      _ = (x₁ * x₂) ^ 2 * l := by rw [e]
  have hlB : l ∈ baseGrp x₁ x₂ := cent_fourGrp_of_ctx0 h l hl hly hlz
  have hcomm : l * x₁ = x₁ * l := baseGrp_comm h.wreath hlB hx₁B
  have hx : l * x₁ * l⁻¹ = x₁ := by
    rw [hcomm]
    group
  have hx' : x₁ = x₁⁻¹ := by
    rw [← hinv x₁ hx₁B, hx]
  apply hy1
  rw [pow_two]
  exact mul_eq_one_iff_eq_inv.mpr hx'

theorem ctx_cent_baseGrp (h : Ctx0 t L S x₁ x₂ lam rho) (hi : CtxIdxFacts t L S x₁ x₂ lam)
    (ht : CtxTauFacts t L S x₁ x₂ lam rho tau) :
    invCent t ⊓ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) = ctxW t x₁ x₂ := by
  have hBL := pt_base_le_L h
  have hBH : baseGrp x₁ x₂ ≤ invCent t := hBL.trans (L_le_invCent h.hyp)
  apply le_antisymm
  · intro g hg
    obtain ⟨hgH, hgC⟩ := Subgroup.mem_inf.mp hg
    have hgC' := Subgroup.mem_centralizer_iff.mp hgC
    rcases mem_PL_or_mul_tau h hi ht hgH with hPL | hPL
    ·
      obtain ⟨p, hp, l, hl, rfl⟩ := (mem_sup_iff_of_commute (twoCore_commute h.hyp)).mp hPL
      have hlcomm : ∀ b ∈ baseGrp x₁ x₂, l * b = b * l := fun b hb =>
        (comm_of_mul_comm (twoCore_commute h.hyp p hp b (hBL hb)) (hgC' b hb)).symm
      have hlB : l ∈ baseGrp x₁ x₂ := cent_fourGrp_of_ctx0 h l hl
        (hlcomm _ (pt_four_le_base x₁ x₂ (Subgroup.subset_closure (by simp))))
        (hlcomm _ (pt_four_le_base x₁ x₂ (Subgroup.subset_closure (by simp))))
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right hlB)
    ·
      exfalso
      obtain ⟨p, hp, l, hl, hgl⟩ := (mem_sup_iff_of_commute (twoCore_commute h.hyp)).mp hPL
      have hg_eq : g = p * l * tau := by
        calc g = (g * tau⁻¹) * tau := by group
          _ = p * l * tau := by rw [hgl]
      have key : ∀ b ∈ baseGrp x₁ x₂, l * b⁻¹ * l⁻¹ = b := by
        intro b hb
        have e1 : g * b * g⁻¹ = b := by
          calc g * b * g⁻¹ = (b * g) * g⁻¹ := by rw [hgC' b hb]
            _ = b := by group
        have hlbL : l * b⁻¹ * l⁻¹ ∈ L :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hl (Subgroup.inv_mem _ (hBL hb)))
            (Subgroup.inv_mem _ hl)
        have hpc : p * (l * b⁻¹ * l⁻¹) = (l * b⁻¹ * l⁻¹) * p :=
          twoCore_commute h.hyp p hp _ hlbL
        calc l * b⁻¹ * l⁻¹ = (p * (l * b⁻¹ * l⁻¹)) * p⁻¹ := by
              rw [hpc]
              group
          _ = p * l * (tau * b * tau⁻¹) * l⁻¹ * p⁻¹ := by
              rw [tau_inv_base h ht hb]
              group
          _ = g * b * g⁻¹ := by
              rw [hg_eq]
              group
          _ = b := e1
      refine no_inverting_in_L h hl (fun b hb => ?_)
      have := key b⁻¹ (Subgroup.inv_mem _ hb)
      rwa [inv_inv] at this
  · refine le_inf (sup_le (twoCore_le_invCent t) hBH) (sup_le ?_ ?_)
    · intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (twoCore_commute h.hyp p hp b (hBL hb)).symm
    · intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact baseGrp_comm h.wreath hb hw

theorem ctx_cent_W (h : Ctx0 t L S x₁ x₂ lam rho) (hi : CtxIdxFacts t L S x₁ x₂ lam)
    (ht : CtxTauFacts t L S x₁ x₂ lam rho tau) :
    centralizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) = ctxW t x₁ x₂ := by
  have htW : t ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_left h.hyp.mem_twoCore
  have hBW : baseGrp x₁ x₂ ≤ ctxW t x₁ x₂ := le_sup_right
  apply le_antisymm
  · intro g hg
    have hgC := Subgroup.mem_centralizer_iff.mp hg
    have hgH : g ∈ invCent t := mem_invCent_iff.mpr (hgC t htW).symm
    have hgB : g ∈ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) :=
      Subgroup.centralizer_le hBW hg
    rw [← ctx_cent_baseGrp h hi ht]
    exact Subgroup.mem_inf.mpr ⟨hgH, hgB⟩
  · intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    haveI : IsMulCommutative (ctxW t x₁ x₂) := h.abelian_W
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ctxW t x₁ x₂) ⟨w, hw⟩)

theorem W_le_norm_base (h : Ctx0 t L S x₁ x₂ lam rho) :
    ctxW t x₁ x₂ ≤ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
  have hBL := pt_base_le_L h
  refine sup_le (fun p hp => mem_normalizer_of_conj_mem (fun b hb => ?_))
    (fun w hw => mem_normalizer_of_conj_mem (fun b hb => ?_))
  · have hc : p * b = b * p := twoCore_commute h.hyp p hp b (hBL hb)
    have e : p * b * p⁻¹ = b := by
      rw [hc]
      group
    rw [e]
    exact hb
  · have hc : w * b = b * w := baseGrp_comm h.wreath hw hb
    have e : w * b * w⁻¹ = b := by
      rw [hc]
      group
    rw [e]
    exact hb

theorem rho_lam_norm_base (hm : CtxLModelFacts L x₁ x₂ lam rho) :
    rho ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) ∧
      lam ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
  have hle : closure {x₁, x₂, rho, lam} ≤ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [← hm.norm_L_B]
    exact inf_le_right
  exact ⟨hle (Subgroup.subset_closure (by simp)), hle (Subgroup.subset_closure (by simp))⟩

theorem ctx_norm_baseGrp (h : Ctx0 t L S x₁ x₂ lam rho) (hi : CtxIdxFacts t L S x₁ x₂ lam)
    (ht : CtxTauFacts t L S x₁ x₂ lam rho tau) (hm : CtxLModelFacts L x₁ x₂ lam rho) :
    invCent t ⊓ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) =
      ctxW t x₁ x₂ ⊔ closure {rho, lam, tau} := by
  obtain ⟨hρN, hlN⟩ := rho_lam_norm_base hm
  have hτH : tau ∈ invCent t := h.le_invCent ht.tau_mem
  have hτN := tau_norm_base h ht
  have hρH : rho ∈ invCent t := L_le_invCent h.hyp h.rho_mem
  have hlamH : lam ∈ invCent t := L_le_invCent h.hyp (generators_mem_L h).2.2
  have hWH : ctxW t x₁ x₂ ≤ invCent t :=
    sup_le (twoCore_le_invCent t) ((pt_base_le_L h).trans (L_le_invCent h.hyp))
  apply le_antisymm
  ·
    have hPLpart : ∀ g' ∈ twoCore t ⊔ L, g' ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) →
        g' ∈ ctxW t x₁ x₂ ⊔ closure {rho, lam, tau} := by
      intro g' hg' hgN
      obtain ⟨p, hp, l, hl, rfl⟩ := (mem_sup_iff_of_commute (twoCore_commute h.hyp)).mp hg'
      have hlN' : l ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
        refine mem_normalizer_of_conj_mem (fun b hb => ?_)
        have hlbL : l * b * l⁻¹ ∈ L :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hl (pt_base_le_L h hb)) (Subgroup.inv_mem _ hl)
        have hpc : p * (l * b * l⁻¹) = (l * b * l⁻¹) * p :=
          twoCore_commute h.hyp p hp _ hlbL
        have e : p * l * b * (p * l)⁻¹ = l * b * l⁻¹ := by
          calc p * l * b * (p * l)⁻¹ = (p * (l * b * l⁻¹)) * p⁻¹ := by group
            _ = ((l * b * l⁻¹) * p) * p⁻¹ := by rw [hpc]
            _ = l * b * l⁻¹ := by group
        rw [← e]
        exact (Subgroup.mem_normalizer_iff.mp hgN b).mp hb
      have hlmem : l ∈ closure {x₁, x₂, rho, lam} := by
        rw [← hm.norm_L_B]
        exact Subgroup.mem_inf.mpr ⟨hl, hlN'⟩
      have hle : closure {x₁, x₂, rho, lam} ≤ ctxW t x₁ x₂ ⊔ closure {rho, lam, tau} := by
        refine (Subgroup.closure_le (K := ctxW t x₁ x₂ ⊔ closure {rho, lam, tau})).mpr ?_
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with hg | hg | hg | hg
        · rw [hg]
          exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
        · rw [hg]
          exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
        · rw [hg]
          exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
        · rw [hg]
          exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left hp)) (hle hlmem)
    intro g hg
    obtain ⟨hgH, hgN⟩ := Subgroup.mem_inf.mp hg
    rcases mem_PL_or_mul_tau h hi ht hgH with hPL | hPL
    · exact hPLpart g hPL hgN
    · have hgτ : g * tau⁻¹ ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) :=
        Subgroup.mul_mem _ hgN (Subgroup.inv_mem _ hτN)
      have hmem := hPLpart _ hPL hgτ
      have hτ : tau ∈ ctxW t x₁ x₂ ⊔ closure {rho, lam, tau} :=
        Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
      have := Subgroup.mul_mem _ hmem hτ
      rwa [inv_mul_cancel_right] at this
  · refine sup_le (le_inf hWH (W_le_norm_base h)) ?_
    refine (Subgroup.closure_le
      (K := invCent t ⊓ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G))).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg
    · rw [hg]
      exact Subgroup.mem_inf.mpr ⟨hρH, hρN⟩
    · rw [hg]
      exact Subgroup.mem_inf.mpr ⟨hlamH, hlN⟩
    · rw [hg]
      exact Subgroup.mem_inf.mpr ⟨hτH, hτN⟩

theorem ctx_normal_norm (h : Ctx0 t L S x₁ x₂ lam rho) (hi : CtxIdxFacts t L S x₁ x₂ lam)
    (ht : CtxTauFacts t L S x₁ x₂ lam rho tau) (hm : CtxLModelFacts L x₁ x₂ lam rho) :
    NormalIn (ctxW t x₁ x₂ ⊔ zpowers tau)
      (invCent t ⊓ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G)) := by
  have hnorm := ctx_norm_baseGrp h hi ht hm
  obtain ⟨hρN, hlN⟩ := rho_lam_norm_base hm
  have hτH : tau ∈ invCent t := h.le_invCent ht.tau_mem
  have hτN := tau_norm_base h ht
  have hlamH : lam ∈ invCent t := L_le_invCent h.hyp (generators_mem_L h).2.2
  have hWH : ctxW t x₁ x₂ ≤ invCent t :=
    sup_le (twoCore_le_invCent t) ((pt_base_le_L h).trans (L_le_invCent h.hyp))
  have hτK : tau ∈ ctxW t x₁ x₂ ⊔ zpowers tau := Subgroup.mem_sup_right (Subgroup.mem_zpowers tau)
  have hρW : ∀ w ∈ ctxW t x₁ x₂, rho * w * rho⁻¹ ∈ ctxW t x₁ x₂ := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp h.rho_normalizes w).mp hw
  have hlamW : ∀ w ∈ ctxW t x₁ x₂, lam * w * lam⁻¹ ∈ ctxW t x₁ x₂ := by
    refine conj_mem_sup (fun p hp => twoCore_conj_mem t hlamH hp) (fun b hb => ?_)
    exact (Subgroup.mem_normalizer_iff.mp hlN b).mp hb
  refine ⟨?_, ?_⟩
  · rw [hnorm]
    exact sup_le_sup_left (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) _
  · intro g hg k hk
    rw [hnorm] at hg
    have hgn : g ∈ normalizer ((ctxW t x₁ x₂ ⊔ zpowers tau : Subgroup G) : Set G) := by
      have hle : ctxW t x₁ x₂ ⊔ closure {rho, lam, tau} ≤
          normalizer ((ctxW t x₁ x₂ ⊔ zpowers tau : Subgroup G) : Set G) := by
        refine sup_le (le_sup_left.trans Subgroup.le_normalizer) ?_
        refine (Subgroup.closure_le (K := normalizer
          ((ctxW t x₁ x₂ ⊔ zpowers tau : Subgroup G) : Set G))).mpr ?_
        intro g' hg'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg'
        rcases hg' with hg' | hg' | hg'
        · rw [hg']
          refine mem_normalizer_of_conj_mem (conj_mem_sup hρW (conj_mem_zpowers ?_))
          calc rho * tau * rho⁻¹ = (tau * rho) * rho⁻¹ := by rw [ht.tau_rho]
            _ = tau := by group
        · rw [hg']
          refine mem_normalizer_of_conj_mem (conj_mem_sup hlamW (conj_mem_zpowers ?_))
          calc lam * tau * lam⁻¹ = (tau * lam) * lam⁻¹ := by rw [ht.tau_lam]
            _ = tau := by group
        · rw [hg']
          exact Subgroup.le_normalizer hτK
      exact hle hg
    exact (Subgroup.mem_normalizer_iff.mp hgn k).mp hk

end Norm

end S4A

theorem ctxNorm_holds : CtxNormStmt :=
  fun h _ hi ht hm =>
    { cent_W := S4A.ctx_cent_W h hi ht
      cent_baseGrp := S4A.ctx_cent_baseGrp h hi ht
      norm_baseGrp := S4A.ctx_norm_baseGrp h hi ht hm
      normal_norm := S4A.ctx_normal_norm h hi ht hm }

end CFSG.OddStandard.SmallF3.HarrisU33
