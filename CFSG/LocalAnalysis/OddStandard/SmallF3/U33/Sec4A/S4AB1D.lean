module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AB1A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ALMod

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

section Generic

variable {G : Type} [Group G] [Finite G]

theorem pl_normalizer {P L Q D : Subgroup G} (hPL : ∀ a ∈ P, ∀ b ∈ L, a * b = b * a)
    (hPP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hinf : P ⊓ L = ⊥) (hQ : Q ≤ P) (hD : D ≤ L) :
    (P ⊔ L) ⊓ normalizer ((Q ⊔ D : Subgroup G) : Set G) =
      P ⊔ (L ⊓ normalizer (D : Set G)) := by
  have hQD : ∀ a ∈ Q, ∀ b ∈ D, a * b = b * a := fun a ha b hb => hPL a (hQ ha) b (hD hb)
  have hPN : ∀ p ∈ P, p ∈ normalizer ((Q ⊔ D : Subgroup G) : Set G) := by
    intro p hp
    refine mem_normalizer_of_conj_mem (fun x hx => ?_)
    obtain ⟨q, hq, d, hd, rfl⟩ := (mem_sup_iff_of_commute hQD).mp hx
    have e : p * (q * d) * p⁻¹ = q * d := by
      calc p * (q * d) * p⁻¹ = (p * q) * d * p⁻¹ := by group
        _ = (q * p) * d * p⁻¹ := by rw [hPP p hp q (hQ hq)]
        _ = q * (p * d) * p⁻¹ := by group
        _ = q * (d * p) * p⁻¹ := by rw [hPL p hp d (hD hd)]
        _ = q * d := by group
    rw [e]
    exact hx
  have hinfL : ∀ x ∈ Q ⊔ D, x ∈ L → x ∈ D := by
    intro x hx hxL
    obtain ⟨q, hq, d, hd, rfl⟩ := (mem_sup_iff_of_commute hQD).mp hx
    have hqL : q ∈ L := by
      have e : q = (q * d) * d⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ hxL (Subgroup.inv_mem _ (hD hd))
    have hq1 : q = 1 := by
      have hmem : q ∈ P ⊓ L := ⟨hQ hq, hqL⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      exact hmem
    rw [hq1, one_mul]
    exact hd
  apply le_antisymm
  · intro g hg
    obtain ⟨hgPL, hgN⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨p, hp, l, hl, rfl⟩ := (mem_sup_iff_of_commute hPL).mp hgPL
    have hlN : l ∈ normalizer ((Q ⊔ D : Subgroup G) : Set G) := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hPN p hp)) hgN
      simpa using this
    have hlD : l ∈ normalizer (D : Set G) := by
      refine mem_normalizer_of_conj_mem (fun d hd => ?_)
      have h1 : l * d * l⁻¹ ∈ Q ⊔ D :=
        (Subgroup.mem_normalizer_iff.mp hlN d).mp (Subgroup.mem_sup_right hd)
      have h2 : l * d * l⁻¹ ∈ L :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hl (hD hd)) (Subgroup.inv_mem _ hl)
      exact hinfL _ h1 h2
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp)
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hl, hlD⟩))
  · refine le_inf (sup_le_sup_left inf_le_left P) (sup_le (fun p hp => hPN p hp) (fun l hl => ?_))
    obtain ⟨hlL, hlND⟩ := Subgroup.mem_inf.mp hl
    refine mem_normalizer_of_conj_mem (fun x hx => ?_)
    obtain ⟨q, hq, d, hd, rfl⟩ := (mem_sup_iff_of_commute hQD).mp hx
    have hld : l * d * l⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hlND d).mp hd
    have e : l * (q * d) * l⁻¹ = q * (l * d * l⁻¹) := by
      calc l * (q * d) * l⁻¹ = (l * q) * d * l⁻¹ := by group
        _ = (q * l) * d * l⁻¹ := by rw [← hPL q (hQ hq) l hlL]
        _ = q * (l * d * l⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hld)

theorem conj_comm_of_mem_normalizer {F : Subgroup G} {l b : G}
    (hl : l ∈ normalizer (F : Set G)) (hb : ∀ f ∈ F, f * b = b * f) :
    ∀ f ∈ F, f * (l * b * l⁻¹) = (l * b * l⁻¹) * f := by
  intro f hf
  have hf' : l⁻¹ * f * l ∈ F := (Subgroup.mem_normalizer_iff''.mp hl f).mp hf
  have h1 := hb _ hf'
  calc f * (l * b * l⁻¹) = l * ((l⁻¹ * f * l) * b) * l⁻¹ := by group
    _ = l * (b * (l⁻¹ * f * l)) * l⁻¹ := by rw [h1]
    _ = (l * b * l⁻¹) * f := by group

end Generic

section Model

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem b1_ctxE_le_ctxW (h : Ctx0 t L S x₁ x₂ lam rho) : ctxE t x₁ x₂ ≤ ctxW t x₁ x₂ := by
  rw [pt_ctxE_eq_sup]
  exact sup_le_sup (Subgroup.zpowers_le.mpr h.hyp.mem_twoCore) (pt_four_le_base x₁ x₂)

theorem b1_sup_eq (t : G) (x₁ x₂ lam rho : G) :
    twoCore t ⊔ closure {x₁, x₂, rho, lam} = ctxW t x₁ x₂ ⊔ closure {rho, lam} := by
  have hBM : baseGrp x₁ x₂ ≤ closure {x₁, x₂, rho, lam} := by
    refine (Subgroup.closure_le (K := closure {x₁, x₂, rho, lam})).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact Subgroup.subset_closure (by simp)
    · rw [hg]
      exact Subgroup.subset_closure (by simp)
  have hRM : closure {rho, lam} ≤ closure {x₁, x₂, rho, lam} :=
    Subgroup.closure_mono (by
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
      tauto)
  apply le_antisymm
  · refine sup_le (le_sup_left.trans le_sup_left) ?_
    refine (Subgroup.closure_le (K := ctxW t x₁ x₂ ⊔ closure {rho, lam})).mpr ?_
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
  · exact sup_le (sup_le le_sup_left (hBM.trans le_sup_right)) (hRM.trans le_sup_right)

section Cert


theorem b1_norm_four (h : Ctx0 t L S x₁ x₂ lam rho) :
    L ⊓ normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) =
      L ⊓ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
  obtain ⟨hAbel, -, -⟩ := h.wreath.baseGrp_eq
  obtain ⟨hEeq, hEelem, -⟩ := h.wreath.fourGrp_eq_omega
  have hyF : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hzF : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · intro l hl
    obtain ⟨hlL, hlN⟩ := Subgroup.mem_inf.mp hl
    refine Subgroup.mem_inf.mpr ⟨hlL, mem_normalizer_of_conj_mem (fun b hb => ?_)⟩
    have hlbL : l * b * l⁻¹ ∈ L :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hlL (pt_base_le_L h hb)) (Subgroup.inv_mem _ hlL)
    have hcomm : ∀ f ∈ fourGrp x₁ x₂, f * b = b * f := by
      intro f hf
      haveI : IsMulCommutative (baseGrp x₁ x₂) := hAbel
      exact congrArg Subtype.val (mul_comm' (⟨f, pt_four_le_base x₁ x₂ hf⟩ : baseGrp x₁ x₂)
        ⟨b, hb⟩)
    have hc := conj_comm_of_mem_normalizer hlN hcomm
    exact cent_fourGrp_of_ctx0 h _ hlbL (hc _ hyF).symm (hc _ hzF).symm
  · intro l hl
    obtain ⟨hlL, hlN⟩ := Subgroup.mem_inf.mp hl
    refine Subgroup.mem_inf.mpr ⟨hlL, mem_normalizer_of_conj_mem (fun e he => ?_)⟩
    have heB : e ∈ baseGrp x₁ x₂ := pt_four_le_base x₁ x₂ he
    have hkB : l * e * l⁻¹ ∈ baseGrp x₁ x₂ := (Subgroup.mem_normalizer_iff.mp hlN e).mp heB
    have hsq : (l * e * l⁻¹) ^ 2 = 1 := by
      rw [conj_pow, hEelem.2 e he]
      group
    rw [hEeq]
    exact Subgroup.subset_closure ⟨hkB, hsq⟩

theorem b1_cent_A (h : Ctx0 t L S x₁ x₂ lam rho) (hPL : invCent t = twoCore t ⊔ L) :
    centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) = ctxW t x₁ x₂ := by
  have hAW := b1_ctxE_le_ctxW h
  have htA : t ∈ ctxE t x₁ x₂ := by
    rw [pt_ctxE_eq_sup]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hFA : fourGrp x₁ x₂ ≤ ctxE t x₁ x₂ := by
    rw [pt_ctxE_eq_sup]
    exact le_sup_right
  have hyF : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hzF : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · intro g hg
    have hgC := Subgroup.mem_centralizer_iff.mp hg
    have hgH : g ∈ invCent t := mem_invCent_iff.mpr (hgC t htA).symm
    rw [hPL] at hgH
    obtain ⟨p, hp, l, hl, rfl⟩ := (mem_sup_iff_of_commute (twoCore_commute h.hyp)).mp hgH
    have hlcomm : ∀ a ∈ fourGrp x₁ x₂, l * a = a * l := by
      intro a ha
      have h1 := hgC a (hFA ha)
      have hpa : p * a = a * p := twoCore_commute h.hyp p hp a (pt_four_le_L h ha)
      calc l * a = p⁻¹ * (p * l * a) := by group
        _ = p⁻¹ * (a * (p * l)) := by rw [h1]
        _ = p⁻¹ * ((a * p) * l) := by group
        _ = p⁻¹ * ((p * a) * l) := by rw [← hpa]
        _ = a * l := by group
    have hlB : l ∈ baseGrp x₁ x₂ :=
      cent_fourGrp_of_ctx0 h l hl (hlcomm _ hyF) (hlcomm _ hzF)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right hlB)
  · intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    haveI : IsMulCommutative (ctxW t x₁ x₂) := h.abelian_W
    exact congrArg Subtype.val (mul_comm' (⟨a, hAW ha⟩ : ctxW t x₁ x₂) ⟨w, hw⟩)

theorem b1_cent_W (h : Ctx0 t L S x₁ x₂ lam rho) (hPL : invCent t = twoCore t ⊔ L) :
    centralizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) = ctxW t x₁ x₂ := by
  apply le_antisymm
  · calc centralizer ((ctxW t x₁ x₂ : Subgroup G) : Set G)
        ≤ centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) :=
          Subgroup.centralizer_le (b1_ctxE_le_ctxW h)
      _ = ctxW t x₁ x₂ := b1_cent_A h hPL
  · intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    haveI : IsMulCommutative (ctxW t x₁ x₂) := h.abelian_W
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ctxW t x₁ x₂) ⟨w, hw⟩)

theorem b1_norm_W (h : Ctx0 t L S x₁ x₂ lam rho) (hPL : invCent t = twoCore t ⊔ L) :
    invCent t ⊓ normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) =
      ctxW t x₁ x₂ ⊔ closure {rho, lam} := by
  haveI := h.hyp.isCyclic
  have hPP : ∀ a ∈ twoCore t, ∀ b ∈ twoCore t, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : twoCore t) ⟨b, hb⟩)
  have hnorm := pl_normalizer (P := twoCore t) (L := L) (Q := twoCore t) (D := baseGrp x₁ x₂)
    (twoCore_commute h.hyp) hPP h.hyp.twoCore_inf le_rfl (pt_base_le_L h)
  rw [hPL, show ctxW t x₁ x₂ = twoCore t ⊔ baseGrp x₁ x₂ from rfl, hnorm,
    (ctx_lmodel_of h).norm_L_B]
  exact b1_sup_eq t x₁ x₂ lam rho

theorem b1_norm_A (h : Ctx0 t L S x₁ x₂ lam rho) (hPL : invCent t = twoCore t ⊔ L) :
    invCent t ⊓ normalizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) =
      ctxW t x₁ x₂ ⊔ closure {rho, lam} := by
  haveI := h.hyp.isCyclic
  have hPP : ∀ a ∈ twoCore t, ∀ b ∈ twoCore t, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : twoCore t) ⟨b, hb⟩)
  have hnorm := pl_normalizer (P := twoCore t) (L := L) (Q := zpowers t) (D := fourGrp x₁ x₂)
    (twoCore_commute h.hyp) hPP h.hyp.twoCore_inf (Subgroup.zpowers_le.mpr h.hyp.mem_twoCore)
    (pt_four_le_L h)
  rw [hPL, pt_ctxE_eq_sup, hnorm, b1_norm_four h, (ctx_lmodel_of h).norm_L_B]
  exact b1_sup_eq t x₁ x₂ lam rho

end Cert

end Model

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
