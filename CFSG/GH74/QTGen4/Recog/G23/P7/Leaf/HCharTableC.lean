module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.HCharTableB

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7.HChar

open CFSG.GH74.QTGen4.Recog.G23.HCharData

section Conversions

variable {G : Type} [Group G] (H : Subgroup G) (z : G) (hz : z ∈ H)

theorem mem_specialD_iff (y : ↥H) : (y : G) ∈ specialD z H ↔ InD (⟨z, hz⟩ : ↥H) y := by
  unfold specialD InD
  simp only [Set.mem_setOf_eq]
  have h3 : (y : G) ^ 3 = 1 ↔ y ^ 3 = 1 := by
    rw [← Subgroup.coe_pow]
    exact OneMemClass.coe_eq_one
  have h1 : (y : G) = 1 ↔ y = 1 := OneMemClass.coe_eq_one
  have hk : ∀ k : ℕ, (y : G) ^ k = z ↔ y ^ k = (⟨z, hz⟩ : ↥H) := fun k => by
    rw [← Subgroup.coe_pow]
    exact (Subtype.ext_iff (a1 := y ^ k) (a2 := (⟨z, hz⟩ : ↥H))).symm
  simp only [h3, h1, hk, Subgroup.orderOf_coe, y.2, true_and, ne_eq]

theorem psiFun_tab {z' : ↥H} {rep : Fin 20 → ↥H} (h : TabHyp ↥H z' rep) (k : Fin 15) :
    psiFun H (fun i => h.tab (fun j => (hcT i j : ℂ))) k =
      h.tab (fun j => (psiTab k j : ℂ)) := by
  funext y
  have key : ∀ (l : List (Fin 20 × ℤ)) (j : Fin 20),
      (l.map fun p => (p.2 : ℂ) * (hcT p.1 j : ℂ)).sum =
        (((l.map fun p => p.2 * hcT p.1 j).sum : ℤ) : ℂ) := by
    intro l j
    induction l with
    | nil => simp
    | cons a l ih => simp [ih]
  simp only [psiFun, TabHyp.tab, psiTab]
  exact key (psiTerms k) (h.cls y)

theorem inner_psi_row {z' : ↥H} {rep : Fin 20 → ↥H} [Fintype ↥H] (h : TabHyp ↥H z' rep)
    (k : Fin 15) (m : Fin 20) :
    CFSG.BlocksInnerProduct (psiFun H (fun i => h.tab (fun j => (hcT i j : ℂ))) k)
        (h.tab (fun j => (hcT m j : ℂ))) =
      (576 : ℂ)⁻¹ * (((∑ j, (hcSize j : ℤ) * psiTab k j * hcT m j : ℤ)) : ℂ) := by
  rw [psiFun_tab H h k, h.inner_tab]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_intCast]
  ring

end Conversions

open scoped Classical in
theorem hcharProps_of_tabHyp {G : Type} [Group G] [Fintype G] (H : Subgroup G) (z : G) (hz : z ∈ H)
    (rep : Fin 20 → ↥H) (h : TabHyp ↥H (⟨z, hz⟩ : ↥H) rep) :
    ∃ χ : Fin 20 → ↥H → ℂ, HCharProps H z χ := by
  set zH : ↥H := ⟨z, hz⟩ with hzH
  have hzG : ∀ y : ↥H, (y : G) = z ↔ y = zH := fun y => by rw [Subtype.ext_iff]
  have hD : ∀ y : ↥H, (y : G) ∈ specialD z H ↔ hcDfl (h.cls y) = true := fun y =>
    (mem_specialD_iff H z hz y).trans (h.inD_iff y)
  have hcls1 : h.cls (1 : ↥H) = 0 := by rw [← h.rep_zero, h.cls_rep]
  have hclsz : ∀ y : ↥H, (y : G) = z → h.cls y = 1 := fun y hy => (h.eq_z_iff y).1 ((hzG y).1 hy)
  have hclsF : ∀ (F : Fin 20 → ℂ) (y : ↥H), h.tab F y = F (h.cls y) := fun F y => rfl
  refine ⟨fun i => h.tab (fun j => (hcT i j : ℂ)), ?_⟩
  refine
    { irr := fun i => h.row_mem_irr i
      inj := ?_
      triv := ?_
      deg := ?_
      vanish := ?_
      span := ?_
      gram := ?_
      inner_triv := ?_
      chi9_absent := ?_
      chi9_z := ?_
      chi20_z := ?_
      chi9_order4 := ?_
      sum_chi9 := ?_
      count_invol := ?_
      count_order4 := ?_
      count_D := ?_
      sum_N := ?_ }
  ·
    intro i i' hii
    apply row_inj
    intro j
    have := congrFun hii (rep j)
    simp only [h.tab_rep] at this
    exact_mod_cast this
  ·
    intro y
    simp [TabHyp.tab, triv_row]
  ·
    intro i
    simp only [hclsF, hcls1]
    have := deg_eq i
    exact_mod_cast this
  ·
    intro k y hy
    rw [psiFun_tab H h k, hclsF]
    have hf : hcDfl (h.cls y) = false := by
      by_contra hcon
      exact hy ((hD y).2 (by simpa using hcon))
    simp [psi_vanish k _ hf]
  ·
    intro f hf hsupp
    refine ⟨fun k => (576 : ℂ)⁻¹ * ∑ l, f (rep (hcDcl l)) * (hcQ l k : ℂ), ?_⟩
    funext y
    have hfy : f y = f (rep (h.cls y)) := h.cf_val hf y
    have hpsi : ∀ k, psiFun H (fun i => h.tab (fun j => (hcT i j : ℂ))) k y =
        (psiTab k (h.cls y) : ℂ) := fun k => by rw [psiFun_tab H h k]; rfl
    simp only [hpsi]
    rw [hfy]
    generalize h.cls y = j
    by_cases hdj : hcDfl j = true
    · obtain ⟨l₀, hl₀⟩ := dcl_surj j hdj
      subst hl₀
      have hQ : ∀ l, ∑ k, (hcQ l k : ℂ) * (psiTab k (hcDcl l₀) : ℂ) =
          if l = l₀ then 576 else 0 := by
        intro l
        have hc : ((∑ k, hcQ l k * psiTab k (hcDcl l₀) : ℤ) : ℂ) =
            ((if l = l₀ then 576 else 0 : ℤ) : ℂ) := by rw [span_inv l l₀]
        push_cast at hc
        exact hc
      have hswap : ∑ k, (576 : ℂ)⁻¹ * (∑ l, f (rep (hcDcl l)) * (hcQ l k : ℂ)) *
          (psiTab k (hcDcl l₀) : ℂ) =
          (576 : ℂ)⁻¹ * ∑ l, f (rep (hcDcl l)) *
            ∑ k, (hcQ l k : ℂ) * (psiTab k (hcDcl l₀) : ℂ) := by
        calc _ = ∑ k, ∑ l, (576 : ℂ)⁻¹ * (f (rep (hcDcl l)) * ((hcQ l k : ℂ) *
              (psiTab k (hcDcl l₀) : ℂ))) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
              exact Finset.sum_congr rfl fun l _ => by ring
          _ = ∑ l, ∑ k, (576 : ℂ)⁻¹ * (f (rep (hcDcl l)) * ((hcQ l k : ℂ) *
              (psiTab k (hcDcl l₀) : ℂ))) := Finset.sum_comm
          _ = _ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun l _ => ?_
              rw [Finset.mul_sum, Finset.mul_sum]
      rw [hswap]
      simp only [hQ]
      rw [Finset.sum_eq_single l₀]
      · simp
        field_simp
      · intro l _ hl
        simp [hl]
      · intro hl
        exact absurd (Finset.mem_univ _) hl
    · have hdj' : hcDfl j = false := by simpa using hdj
      have hfj : f (rep j) = 0 := hsupp _ (fun hm =>
        hdj ((h.dflag j).1 ((mem_specialD_iff H z hz _).1 hm)))
      simp [hfj, psi_vanish _ j hdj']
  ·
    intro k l
    rw [psiFun_tab H h k, psiFun_tab H h l, h.inner_tab]
    have hc : (((∑ j, (hcSize j : ℤ) * psiTab k j * psiTab l j : ℤ)) : ℂ) =
        ((576 * psiGram k l : ℤ) : ℂ) := by rw [psi_gram]
    push_cast at hc
    have hs : ∑ j, (hcSize j : ℂ) * ((psiTab k j : ℂ) * (starRingEnd ℂ) (psiTab l j : ℂ)) =
        576 * (psiGram k l : ℂ) := by
      rw [← hc]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_intCast]
      ring
    rw [hs]
    field_simp
  ·
    intro k
    refine (inner_psi_row H h k 0).trans ?_
    rw [psi_triv k]
    split_ifs <;> simp
  ·
    intro k hk
    refine (inner_psi_row H h k 8).trans ?_
    rw [psi_chi9 k hk]
    simp
  ·
    intro y hy
    rw [hclsF, hclsz y hy]
    exact_mod_cast chi9_z
  ·
    intro y hy
    rw [hclsF, hclsz y hy]
    exact_mod_cast chi20_z
  ·
    intro y hy ho
    have hDy := (hD y).1 hy
    rw [hclsF]
    have := chi9_order4 (h.cls y) (by rw [← h.orderOf_eq_ord y]; exact ho) hDy
    exact_mod_cast this
  ·
    rw [Finset.sum_filter]
    have e : ∀ y : ↥H, (if (y : G) ∈ specialD z H then h.tab (fun j => (hcT 8 j : ℂ)) y else 0) =
        (fun j : Fin 20 => if hcDfl j = true then (hcT 8 j : ℂ) else 0) (h.cls y) := by
      intro y
      by_cases hy : hcDfl (h.cls y) = true
      · simp [(hD y).2 hy, hy, TabHyp.tab]
      · have : (y : G) ∉ specialD z H := fun hm => hy ((hD y).1 hm)
        simp [this, hy]
    rw [Finset.sum_congr rfl fun y _ => e y]
    refine (h.sum_cls (fun j : Fin 20 => if hcDfl j = true then (hcT 8 j : ℂ) else 0)).trans ?_
    have hc : ((∑ j, (if hcDfl j = true then (hcSize j : ℤ) * hcT 8 j else 0) : ℤ) : ℂ) =
        ((-171 : ℤ) : ℂ) := by rw [sum_chi9]
    push_cast at hc
    rw [← hc]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  ·
    have e : (Finset.univ.filter fun y : ↥H => orderOf y = 2 ∧ (y : G) ≠ z) =
        Finset.univ.filter fun y : ↥H => (fun j : Fin 20 => hcOrd j = 2 ∧ j ≠ 1) (h.cls y) := by
      refine Finset.filter_congr fun y _ => ?_
      rw [h.orderOf_eq_ord y]
      simp only [ne_eq, hzG, h.eq_z_iff]
    rw [e]
    exact (h.card_filter_cls (fun j : Fin 20 => hcOrd j = 2 ∧ j ≠ 1)).trans count_invol
  ·
    have e : (Finset.univ.filter fun y : ↥H => orderOf y = 4 ∧ (y : G) ∉ specialD z H) =
        Finset.univ.filter fun y : ↥H =>
          (fun j : Fin 20 => hcOrd j = 4 ∧ hcDfl j = false) (h.cls y) := by
      refine Finset.filter_congr fun y _ => ?_
      rw [h.orderOf_eq_ord y, hD y]
      simp
    rw [e]
    exact (h.card_filter_cls (fun j : Fin 20 => hcOrd j = 4 ∧ hcDfl j = false)).trans count_order4
  ·
    have e : (Finset.univ.filter fun y : ↥H => (y : G) ∈ specialD z H) =
        Finset.univ.filter fun y : ↥H => (fun j : Fin 20 => hcDfl j = true) (h.cls y) :=
      Finset.filter_congr fun y _ => hD y
    rw [e]
    exact (h.card_filter_cls (fun j : Fin 20 => hcDfl j = true)).trans count_D
  ·
    have hcount : ∀ y : ↥H, ((Finset.univ.filter fun u : ↥H => orderOf u = 2 ∧
        (if (y : G) = z then (u : G) ≠ z else (u : G) * y * (u : G)⁻¹ = (y : G)⁻¹)).card : ℂ) =
          (hcCt (h.cls y) : ℂ) := by
      intro y
      have hct := h.ct_val y
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hct
      have e : (Finset.univ.filter fun u : ↥H => orderOf u = 2 ∧
          (if (y : G) = z then (u : G) ≠ z else (u : G) * y * (u : G)⁻¹ = (y : G)⁻¹)) =
          Finset.univ.filter fun u : ↥H => orderOf u = 2 ∧
            (if y = zH then u ≠ zH else u * y * u⁻¹ = y⁻¹) := by
        refine Finset.filter_congr fun u _ => ?_
        refine and_congr_right fun _ => ?_
        by_cases hy : y = zH
        · rw [if_pos ((hzG y).2 hy), if_pos hy]
          exact (hzG u).not
        · have hyG : ¬ (y : G) = z := fun e => hy ((hzG y).1 e)
          rw [if_neg hyG, if_neg hy, Subtype.ext_iff]
          simp
      rw [e]
      exact_mod_cast hct
    rw [Finset.sum_filter]
    have e2 : ∀ y : ↥H, (if (y : G) ∈ specialD z H then
        psiFun H (fun i => h.tab (fun j => (hcT i j : ℂ))) 0 y * ((Finset.univ.filter fun u : ↥H =>
          orderOf u = 2 ∧ (if (y : G) = z then (u : G) ≠ z else
            (u : G) * y * (u : G)⁻¹ = (y : G)⁻¹)).card : ℂ) else 0) =
        (fun j : Fin 20 => if hcDfl j = true then (psiTab 0 j : ℂ) * (hcCt j : ℂ) else 0)
          (h.cls y) := by
      intro y
      by_cases hy : hcDfl (h.cls y) = true
      · rw [if_pos ((hD y).2 hy), hcount y, psiFun_tab H h 0]
        simp [hy, TabHyp.tab]
      · rw [if_neg (fun hm => hy ((hD y).1 hm))]
        simp [hy]
    rw [Finset.sum_congr rfl fun y _ => e2 y]
    refine (h.sum_cls (fun j : Fin 20 =>
      if hcDfl j = true then (psiTab 0 j : ℂ) * (hcCt j : ℂ) else 0)).trans ?_
    have hc : ((∑ j, (if hcDfl j = true then (hcSize j : ℤ) * psiTab 0 j * hcCt j else 0) : ℤ) : ℂ)
        = ((7200 : ℤ) : ℂ) := by rw [sum_N]
    push_cast at hc
    rw [← hc]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rw [nsmul_eq_mul]
      ring
    · simp


end CFSG.GH74.QTGen4.Recog.G23.P7.HChar
