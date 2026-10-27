module

public import CFSG.ClassicalInvolution.Phan.Geometry.NondegQTwoLift
public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycleMoves
import CFSG.ClassicalInvolution.Phan.Geometry.ShortCyclesDiag

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary Module CFSG.Monster.B.Recog
open CFSG.ClassicalInvolution.Phan.Geometry SimpleGraph

variable {K : Type*} [Field K] {σ : K ≃+* K} {d : ℕ}

private theorem ndq_exists_Y (hσ : IsUnitaryInvolution σ) {W : Submodule K (Fin d → K)}
    (hW : Nondeg σ W) (h5 : 5 ≤ finrank K W) {a c : Submodule K (Fin d → K)}
    (ha : a ∈ nsPts σ W) (hc : c ∈ nsPts σ W) (hac : a ≠ c) (hnc : ¬ IsCollinear σ a c) :
    ∃ Y : Submodule K (Fin d → K), Y ≤ W ∧ Nondeg σ Y ∧ 2 ≤ finrank K Y ∧
      finrank K Y + 2 ≤ finrank K W ∧ Orth σ a Y ∧ Orth σ c Y ∧
      ∀ b ∈ nsPts σ W, Orth σ a b → Orth σ c b →
        ∃ y ∈ nsPts σ Y, ∃ u ∈ nsPts σ Y, Orth σ y u ∧ Orth σ b u := by
  obtain ⟨α, hα, hαW, rfl⟩ := mem_nsPts_iff.mp ha
  obtain ⟨γ, hγ, hγW, rfl⟩ := mem_nsPts_iff.mp hc
  have hW₁ : Nondeg σ (W ⊓ perp σ (K ∙ α)) := Nondeg.inf_perp_span_singleton hσ hαW hα hW
  have hW₁dim := finrank_eq_inf_perp_add_one hσ hαW hα
  have hγα : γ ∉ K ∙ α := not_mem_span_of_ne hγ hac
  set γ' := projPerp σ α γ with hγ'
  have hγ'W₁ : γ' ∈ W ⊓ perp σ (K ∙ α) := by
    refine ⟨?_, mem_perp_span_singleton.mpr (herm_projPerp_left hσ hα γ)⟩
    rw [hγ', projPerp_apply]
    exact W.sub_mem hγW (W.smul_mem _ hαW)
  have hγ'0 : γ' ≠ 0 := fun h => hγα ((projPerp_eq_zero_iff hα).mp h)
  have hγ'γ' : herm σ γ' γ' = 0 := by
    by_contra h
    exact hnc ⟨hac, (nondeg_span_pair_iff hσ hα hγα).mpr h⟩
  have hγeq : γ = γ' + ((herm σ α α)⁻¹ * herm σ α γ) • α := by
    rw [hγ', projPerp_apply, sub_add_cancel]
  obtain ⟨z, hzW₁, hz⟩ : ∃ z ∈ W ⊓ perp σ (K ∙ α), herm σ γ' z ≠ 0 := by
    by_contra! h
    exact hγ'0 (hW₁ γ' hγ'W₁ h)
  have hzγ' : herm σ z γ' ≠ 0 := by
    rw [herm_conj σ hσ.invol γ' z]
    exact (map_ne_zero σ).mpr hz
  have hPW₁ : K ∙ γ' ⊔ K ∙ z ≤ W ⊓ perp σ (K ∙ α) :=
    sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hγ'W₁)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hzW₁)
  have hP : Nondeg σ (K ∙ γ' ⊔ K ∙ z) := by
    intro s hs hs'
    obtain ⟨u', hu', w', hw', rfl⟩ := Submodule.mem_sup.mp hs
    obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.mp hu'
    obtain ⟨w, rfl⟩ := Submodule.mem_span_singleton.mp hw'
    have h1 := hs' γ' (Submodule.mem_sup_left (Submodule.mem_span_singleton_self γ'))
    have h2 := hs' z (Submodule.mem_sup_right (Submodule.mem_span_singleton_self z))
    simp only [herm_add_left, herm_smul_left, hγ'γ', mul_zero, zero_add] at h1 h2
    have hw : w = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact (map_eq_zero_iff σ σ.injective).mp h
      · exact absurd h hzγ'
    subst hw
    simp only [map_zero, zero_mul, add_zero] at h2
    have hx : x = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact (map_eq_zero_iff σ σ.injective).mp h
      · exact absurd h hz
    subst hx
    simp
  have hPdim := finrank_eq_add_finrank_inf_perp hσ hP hPW₁
  have hP2 : finrank K ↥(K ∙ γ' ⊔ K ∙ z) ≤ 2 := by
    have h1 := Submodule.finrank_add_le_finrank_add_finrank (K ∙ γ') (K ∙ z)
    have h3 := finrank_span_singleton_le_one (K := K) γ'
    have h4 := finrank_span_singleton_le_one (K := K) z
    omega
  have hP1 : 1 ≤ finrank K ↥(K ∙ γ' ⊔ K ∙ z) := by
    rw [← finrank_span_singleton (K := K) hγ'0]
    exact Submodule.finrank_mono le_sup_left
  set Y := (W ⊓ perp σ (K ∙ α)) ⊓ perp σ (K ∙ γ' ⊔ K ∙ z) with hYdef
  have hY : Nondeg σ Y := Nondeg.inf_perp hσ hW₁ hP hPW₁
  have hYα : ∀ v ∈ Y, herm σ v α = 0 := fun v hv => mem_perp_span_singleton.mp hv.1.2
  have hYγ' : ∀ v ∈ Y, herm σ v γ' = 0 := fun v hv =>
    hv.2 γ' (Submodule.mem_sup_left (Submodule.mem_span_singleton_self γ'))
  have hYγ : ∀ v ∈ Y, herm σ v γ = 0 := fun v hv => by
    rw [hγeq, herm_add_right, herm_smul_right, hYγ' v hv, hYα v hv, mul_zero, add_zero]
  have orthY : ∀ {e : Fin d → K}, (∀ v ∈ Y, herm σ v e = 0) → Orth σ (K ∙ e) Y := by
    intro e he u hu v hv
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [herm_smul_left, (herm_eq_zero_iff hσ _ _).mp (he v hv), mul_zero]
  refine ⟨Y, inf_le_left.trans inf_le_left, hY, by omega, by omega, orthY hYα, orthY hYγ, ?_⟩
  intro b hb hab hcb
  obtain ⟨β, hβ, hβW, rfl⟩ := mem_nsPts_iff.mp hb
  have hαβ : herm σ α β = 0 := orth_span_singleton_iff.mp hab
  have hγβ : herm σ γ β = 0 := orth_span_singleton_iff.mp hcb
  have hβα : herm σ β α = 0 := (herm_eq_zero_iff hσ _ _).mp hαβ
  have hβγ' : herm σ β γ' = 0 := by
    rw [hγ', projPerp_apply, herm_sub_right, herm_smul_right, (herm_eq_zero_iff hσ _ _).mp hγβ,
      hβα, mul_zero, sub_zero]
  have hγ'β : herm σ γ' β = 0 := (herm_eq_zero_iff hσ _ _).mp hβγ'
  set t := herm σ z β * (herm σ z γ')⁻¹ with ht
  have hyb₁ : herm σ (β - t • γ') γ' = 0 := by
    rw [herm_sub_left, herm_smul_left, hβγ', hγ'γ', mul_zero, sub_zero]
  have hyb₂ : herm σ (β - t • γ') z = 0 := by
    refine (herm_eq_zero_iff hσ _ _).mp ?_
    rw [herm_sub_right, herm_smul_right, ht, mul_assoc, inv_mul_cancel₀ hzγ', mul_one, sub_self]
  have hybY : β - t • γ' ∈ Y := by
    refine ⟨(W ⊓ perp σ (K ∙ α)).sub_mem ⟨hβW, mem_perp_span_singleton.mpr hβα⟩
      ((W ⊓ perp σ (K ∙ α)).smul_mem _ hγ'W₁), fun s hs => ?_⟩
    obtain ⟨u', hu', w', hw', rfl⟩ := Submodule.mem_sup.mp hs
    obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.mp hu'
    obtain ⟨w, rfl⟩ := Submodule.mem_span_singleton.mp hw'
    rw [herm_add_right, herm_smul_right, herm_smul_right, hyb₁, hyb₂, mul_zero, mul_zero,
      add_zero]
  have hyb : herm σ (β - t • γ') (β - t • γ') ≠ 0 := by
    rw [herm_sub_left, herm_sub_right, herm_sub_right, herm_smul_left, herm_smul_left,
      herm_smul_right, herm_smul_right, hβγ', hγ'β, hγ'γ']
    simpa using hβ
  have hY₂ : Nondeg σ (Y ⊓ perp σ (K ∙ (β - t • γ'))) :=
    Nondeg.inf_perp_span_singleton hσ hybY hyb hY
  have hY₂dim := finrank_eq_inf_perp_add_one hσ hybY hyb
  have hYdim : 2 ≤ finrank K Y := by omega
  obtain ⟨u, hu, huu⟩ := exists_aniso_of_nondeg hσ hY₂ (fun h => by
    rw [h, finrank_bot] at hY₂dim
    omega)
  have hyu : herm σ (β - t • γ') u = 0 :=
    (herm_eq_zero_iff hσ _ _).mp (mem_perp_span_singleton.mp hu.2)
  refine ⟨K ∙ (β - t • γ'), span_singleton_mem_nsPts hyb hybY, K ∙ u,
    span_singleton_mem_nsPts huu hu.1, orth_span_singleton_iff.mpr hyu,
    orth_span_singleton_iff.mpr ?_⟩
  have hβeq : β = (β - t • γ') + t • γ' := (sub_add_cancel β _).symm
  rw [hβeq, herm_add_left, herm_smul_left, hyu, (herm_eq_zero_iff hσ _ _).mp (hYγ' u hu.1),
    mul_zero, add_zero]

private theorem ndq_quad_mem (hσ : IsUnitaryInvolution σ) {W : Submodule K (Fin d → K)}
    (hd : 3 ≤ finrank K W) {Y : Submodule K (Fin d → K)} (hYW : Y ≤ W) (hY : Nondeg σ Y)
    (hY2 : 2 ≤ finrank K Y) (hYW2 : finrank K Y + 2 ≤ finrank K W)
    {a c y y' : ↥(nsPts σ W)} (haY : Orth σ a.1 Y) (hcY : Orth σ c.1 Y) (hy : y.1 ≤ Y)
    (hy' : y'.1 ≤ Y) (hay : (collGraph σ W).Adj a y) (hyc : (collGraph σ W).Adj y c)
    (hcy' : (collGraph σ W).Adj c y') (hy'a : (collGraph σ W).Adj y' a) :
    quadWalk hay hyc hcy' hy'a ∈ ndNull hd a := by
  have hd2 : 2 ≤ finrank K W := by omega
  have hsum : ∀ {p : Submodule K (Fin d → K)}, p ∈ nsPts σ W → Orth σ p Y →
      finrank K ↥(p ⊔ Y) = finrank K Y + 1 := by
    intro p hp hpY
    have hdisj : Disjoint p Y := by
      rw [Submodule.disjoint_def]
      intro v hvp hvY
      exact hp.2.2 v hvp fun w hw => (herm_eq_zero_iff hσ _ _).mp (hpY w hw v hvY)
    rw [finrank_sup_of_disjoint hdisj, hp.2.1, add_comm]
  let ext : ∀ p : ↥(nsPts σ W), Orth σ p.1 Y → NdVert σ W := fun p hpY =>
    ⟨p.1 ⊔ Y, sup_le p.2.1 hYW, fun h => by
        have := hsum p.2 hpY
        rw [h, finrank_bot] at this
        omega,
      fun h => by
        have := hsum p.2 hpY
        rw [h] at this
        omega, Nondeg.sup_of_orth hσ p.2.2.2 hY hpY⟩
  let Yv : NdVert σ W := ⟨Y, hYW, fun h => by rw [h, finrank_bot] at hY2; omega,
    fun h => by rw [h] at hYW2; omega, hY⟩
  have hlt : ∀ {p : ↥(nsPts σ W)} (hpY : Orth σ p.1 Y) {S : Submodule K (Fin d → K)},
      S ≤ p.1 ⊔ Y → finrank K S < finrank K Y + 1 → S < p.1 ⊔ Y := fun hpY _ hS hf =>
    Submodule.lt_of_le_of_finrank_lt_finrank hS (by rw [hsum (Subtype.prop _) hpY]; exact hf)
  have hltY : ∀ {S : Submodule K (Fin d → K)}, S ≤ Y → finrank K S = 1 → S < Y := fun hS hf =>
    Submodule.lt_of_le_of_finrank_lt_finrank hS (by omega)
  have hline : ∀ {p q : ↥(nsPts σ W)} (h : (collGraph σ W).Adj p q),
      finrank K ↥(p.1 ⊔ q.1) = 2 := fun {p q} h => finrank_sup_of_ne_pts p.2.2.1 q.2.2.1 h.1
  have hA₁ : ∀ x ∈ (ndExpand hd hay).support, (ndGraph σ W).Adj x (ext a haY) := by
    intro x hx
    simp only [ndExpand, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inl (hlt haY (S := a.1) le_sup_left (by rw [a.2.2.1]; omega))
    · exact Or.inl (hlt haY (S := a.1 ⊔ y.1) (sup_le_sup_left hy _) (by rw [hline hay]; omega))
    · exact Or.inl (hlt haY (S := y.1) (hy.trans le_sup_right) (by rw [y.2.2.1]; omega))
  have hA₂ : ∀ x ∈ (ndExpand hd hy'a).support, (ndGraph σ W).Adj x (ext a haY) := by
    intro x hx
    simp only [ndExpand, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inl (hlt haY (S := y'.1) (hy'.trans le_sup_right) (by rw [y'.2.2.1]; omega))
    · exact Or.inl (hlt haY (S := y'.1 ⊔ a.1) (sup_le (hy'.trans le_sup_right) le_sup_left)
        (by rw [hline hy'a]; omega))
    · exact Or.inl (hlt haY (S := a.1) le_sup_left (by rw [a.2.2.1]; omega))
  have hC : ∀ x ∈ ((ndExpand hd hyc).append (ndExpand hd hcy')).support,
      (ndGraph σ W).Adj x (ext c hcY) := by
    intro x hx
    simp only [ndExpand, Walk.support_append, Walk.support_cons, Walk.support_nil,
      List.tail_cons, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (hlt hcY (S := y.1) (hy.trans le_sup_right) (by rw [y.2.2.1]; omega))
    · exact Or.inl (hlt hcY (S := y.1 ⊔ c.1) (sup_le (hy.trans le_sup_right) le_sup_left)
        (by rw [hline hyc]; omega))
    · exact Or.inl (hlt hcY (S := c.1) le_sup_left (by rw [c.2.2.1]; omega))
    · exact Or.inl (hlt hcY (S := c.1 ⊔ y'.1) (sup_le_sup_left hy' _) (by rw [hline hcy']; omega))
    · exact Or.inl (hlt hcY (S := y'.1) (hy'.trans le_sup_right) (by rw [y'.2.2.1]; omega))
  have key : ∀ (h₁ : (ndGraph σ W).Adj (ndPt hd2 a) (ext a haY))
      (h₂ : (ndGraph σ W).Adj (ext a haY) (ndPt hd2 y))
      (h₃ : (ndGraph σ W).Adj (ndPt hd2 y) (ext c hcY))
      (h₄ : (ndGraph σ W).Adj (ext c hcY) (ndPt hd2 y'))
      (h₅ : (ndGraph σ W).Adj (ndPt hd2 y') (ext a haY))
      (h₆ : (ndGraph σ W).Adj (ext a haY) (ndPt hd2 a)),
      Homotopic ((Walk.cons h₁ (.cons h₂ .nil)).append
        ((Walk.cons h₃ (.cons h₄ .nil)).append (Walk.cons h₅ (.cons h₆ .nil)))) .nil := by
    intro h₁ h₂ h₃ h₄ h₅ h₆
    have hM : Homotopic (Walk.cons h₂ (.cons h₃ (.cons h₄ (.cons h₅ .nil))) :
        (ndGraph σ W).Walk (ext a haY) (ext a haY)) .nil := by
      refine CFSG.Monster.B.GSide.homotopic_nil_of_forall_adj_or_eq (z := Yv) _ fun x hx => ?_
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (hlt haY (S := Y) le_sup_right (by omega)))
      · exact Or.inr (Or.inl (hltY (S := y.1) hy y.2.2.1))
      · exact Or.inr (Or.inr (hlt hcY (S := Y) le_sup_right (by omega)))
      · exact Or.inr (Or.inl (hltY (S := y'.1) hy' y'.2.2.1))
      · exact Or.inr (Or.inr (hlt haY (S := Y) le_sup_right (by omega)))
    have h := (hM.append_right (Walk.cons h₆ .nil)).cons h₁
    simp only [Walk.cons_append, Walk.nil_append] at h ⊢
    exact h.trans (homotopic_cons_cons_nil h₁)
  show Homotopic (substituteWalk (ndPt (by omega)) (ndExpand hd) (quadWalk hay hyc hcy' hy'a))
    .nil
  simp only [quadWalk, substituteWalk_cons, substituteWalk_nil, Walk.append_nil]
  have H := (CFSG.Monster.B.GSide.homotopic_cone _ hA₁).append
    ((CFSG.Monster.B.GSide.homotopic_cone _ hC).append
      (CFSG.Monster.B.GSide.homotopic_cone _ hA₂))
  rw [Walk.append_assoc] at H
  exact H.trans (key _ _ _ _ _ _)

theorem ndNullLen4 [Finite K] (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) {W : Submodule K (Fin d → K)}
    (hW : Nondeg σ W) (h5 : 5 ≤ Module.finrank K W)
    (h3 : NullLen (ndNull (σ := σ) (W := W) (by omega)) 3) :
    NullLen (ndNull (σ := σ) (W := W) (by omega)) 4 := by
  have hd : 3 ≤ finrank K W := by omega
  have horth : ∀ {x y : ↥(nsPts σ W)}, (collGraph σ W).Adj x y → Orth σ x.1 y.1 :=
    fun {x y} h => (isCollinear_iff_orth hσ hK ⟨le_top, x.2.2.1, x.2.2.2⟩
      ⟨le_top, y.2.2.1, y.2.2.2⟩).mp h
  have hadj : ∀ {x y : ↥(nsPts σ W)}, Orth σ x.1 y.1 → (collGraph σ W).Adj x y :=
    fun {x y} h => IsCollinear.of_orth hσ x.2 y.2 h
  have hquad : ∀ {a b c e : ↥(nsPts σ W)} (hab : (collGraph σ W).Adj a b)
      (hbc : (collGraph σ W).Adj b c) (hce : (collGraph σ W).Adj c e)
      (hea : (collGraph σ W).Adj e a),
      CycleHomotopic (ndNull hd) (quadWalk hab hbc hce hea) .nil := by
    intro a b c e hab hbc hce hea
    by_cases hdiag : a = c ∨ (collGraph σ W).Adj a c ∨ b = e ∨ (collGraph σ W).Adj b e
    · exact cycleHomotopic_quad_nil_of_diag _ h3 hab hbc hce hea hdiag
    push Not at hdiag
    obtain ⟨hac, hac', -, -⟩ := hdiag
    obtain ⟨Y, hYW, hY, hY2, hYW2, haY, hcY, hYb⟩ :=
      ndq_exists_Y hσ hW h5 a.2 c.2 (fun h => hac (Subtype.ext h)) hac'
    have hYpt : ∀ {p : Submodule K (Fin d → K)}, p ∈ nsPts σ Y → p ∈ nsPts σ W :=
      fun {p} hp => ⟨hp.1.trans hYW, hp.2.1, hp.2.2⟩
    obtain ⟨y₀, hy₀, u₀, hu₀, hyu, hbu⟩ :=
      hYb b.1 b.2 (horth hab) (Orth.symm hσ (horth hbc))
    let y : ↥(nsPts σ W) := ⟨y₀, hYpt hy₀⟩
    let u : ↥(nsPts σ W) := ⟨u₀, hYpt hu₀⟩
    have hay : (collGraph σ W).Adj a y := hadj (Orth.mono haY le_rfl hy₀.1)
    have hcy : (collGraph σ W).Adj c y := hadj (Orth.mono hcY le_rfl hy₀.1)
    have hau : (collGraph σ W).Adj a u := hadj (Orth.mono haY le_rfl hu₀.1)
    have hcu : (collGraph σ W).Adj c u := hadj (Orth.mono hcY le_rfl hu₀.1)
    have hbu' : (collGraph σ W).Adj b u := hadj hbu
    have hyu' : (collGraph σ W).Adj y u := hadj hyu
    have q₁ : CycleHomotopic (ndNull hd) (quadWalk hab hbc hcu hau.symm) .nil :=
      cycleHomotopic_quad_nil_of_diag _ h3 _ _ _ _ (Or.inr (Or.inr (Or.inr hbu')))
    have q₂ : CycleHomotopic (ndNull hd) (quadWalk hau hcu.symm hcy hay.symm) .nil :=
      cycleHomotopic_quad_nil_of_diag _ h3 _ _ _ _ (Or.inr (Or.inr (Or.inr hyu'.symm)))
    have qby : CycleHomotopic (ndNull hd) (quadWalk hab hbc hcy hay.symm) .nil :=
      cycleHomotopic_quad_trans _ hab hbc hcu hau.symm hcy hay.symm q₁ q₂
    obtain ⟨y₁, hy₁, u₁, hu₁, hyu₁, heu⟩ :=
      hYb e.1 e.2 (Orth.symm hσ (horth hea)) (horth hce)
    let y' : ↥(nsPts σ W) := ⟨y₁, hYpt hy₁⟩
    let u' : ↥(nsPts σ W) := ⟨u₁, hYpt hu₁⟩
    have hay' : (collGraph σ W).Adj a y' := hadj (Orth.mono haY le_rfl hy₁.1)
    have hcy' : (collGraph σ W).Adj c y' := hadj (Orth.mono hcY le_rfl hy₁.1)
    have hau' : (collGraph σ W).Adj a u' := hadj (Orth.mono haY le_rfl hu₁.1)
    have hcu' : (collGraph σ W).Adj c u' := hadj (Orth.mono hcY le_rfl hu₁.1)
    have heu' : (collGraph σ W).Adj e u' := hadj heu
    have hyu₁' : (collGraph σ W).Adj y' u' := hadj hyu₁
    have q₃ : CycleHomotopic (ndNull hd) (quadWalk hay' hcy'.symm hcu' hau'.symm) .nil :=
      cycleHomotopic_quad_nil_of_diag _ h3 _ _ _ _ (Or.inr (Or.inr (Or.inr hyu₁')))
    have q₄ : CycleHomotopic (ndNull hd) (quadWalk hau' hcu'.symm hce hea) .nil :=
      cycleHomotopic_quad_nil_of_diag _ h3 _ _ _ _ (Or.inr (Or.inr (Or.inr heu'.symm)))
    have qy'e : CycleHomotopic (ndNull hd) (quadWalk hay' hcy'.symm hce hea) .nil :=
      cycleHomotopic_quad_trans _ hay' hcy'.symm hcu' hau'.symm hce hea q₃ q₄
    have qyy' : CycleHomotopic (ndNull hd) (quadWalk hay hcy.symm hcy' hay'.symm) .nil :=
      cycleHomotopic_of_mem _ (ndq_quad_mem hσ hd hYW hY hY2 hYW2 haY hcY hy₀.1 hy₁.1 _ _ _ _)
    have qye : CycleHomotopic (ndNull hd) (quadWalk hay hcy.symm hce hea) .nil :=
      cycleHomotopic_quad_trans _ hay hcy.symm hcy' hay'.symm hce hea qyy' qy'e
    exact cycleHomotopic_quad_trans _ hab hbc hcy hay.symm hce hea qby qye
  intro x p hp
  match x, p, hp with
  | _, .cons hab (.cons hbc (.cons hce (.cons hea .nil))), _ => exact hquad hab hbc hce hea
  | _, .nil, hp => simp at hp
  | _, .cons _ .nil, hp => simp at hp
  | _, .cons _ (.cons _ .nil), hp => simp at hp
  | _, .cons _ (.cons _ (.cons _ .nil)), hp => simp at hp
  | _, .cons _ (.cons _ (.cons _ (.cons _ (.cons _ _)))), hp =>
    simp only [Walk.length_cons] at hp
    omega

end CFSG.ClassicalInvolution.Phan
