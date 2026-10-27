module

public import CFSG.LieType.D4Small.RootRelations
public import CFSG.LieType.D4Small.WeightClass

public section

namespace CFSG.LieType.D4Small.D4Datum

attribute [local instance] Fintype.ofFinite Classical.propDecidable

open Finset

variable {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2]
  {D : D4Datum G K} {X : Type*} [AddCommGroup X] [Module K X] {ρ : Representation K G X}
  {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))} {σ : ZMod (Nat.card Kˣ)}
  {E : (Fin 4 → ℤ) → Module.End K X} {j : ℕ}

private theorem exists_ne_zero_ne_one_of_four_le_card {K : Type*} [Field K] [Finite K]
    (hK : 4 ≤ Nat.card K) : ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1 := by
  have hlt : ({0, 1} : Finset K).card < (univ : Finset K).card := by
    rw [Finset.card_pair (zero_ne_one (α := K)), Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨μ, -, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
  exact ⟨μ, hnot.1, hnot.2⟩

private theorem exists_mem_ne_neg {N : ℕ} {σ : ZMod N} {C : Finset (Fin 4 → ZMod N)}
    (hC : IsSmallClass N σ C) : ∃ a ∈ C, a ≠ -a := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (by rw [hC.card_eq]; norm_num : 1 < C.card)
  have hzero : ∀ x : Fin 4 → ZMod N, x = -x → x = 0 := by
    intro x hx
    have h1 : x + x = 0 := by
      nth_rewrite 2 [hx]
      rw [add_neg_cancel]
    have h2 : (2 : ZMod N) • x = 0 := by rwa [two_smul]
    exact (IsUnit.smul_eq_zero hC.isUnit_two).mp h2
  by_cases h : a = -a
  · refine ⟨b, hb, fun hb' => hab ?_⟩
    rw [hzero a h, hzero b hb']
  · exact ⟨a, ha, h⟩

private theorem n_apply_eq {α : Fin 4 → ℤ} (hform : IsRootForm D ρ E j) (hα : IsD4Root α)
    {x : X} (hBx : E (-α) x = 0) (hAAx : E α (E α x) = 0) :
    ρ (D.n α) x = (x + E (-α) (E α x)) + E α (E (-α) (E α x)) := by
  have h1 : ρ (D.x α 1) = 1 + E α := by simpa using hform α hα 1
  have h2 : ρ (D.x (-α) 1) = 1 + E (-α) := by simpa using hform (-α) hα.neg 1
  have h3 : ρ (D.n α) = (1 + E α) * (1 + E (-α)) * (1 + E α) := by
    rw [D4Datum.n, map_mul, map_mul, h1, h2]
  rw [h3]
  simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, map_add,
    map_zero, hBx, hAAx, zero_add, add_zero]
  rw [show x + E α x + (E α x + (E (-α) (E α x) + E α (E (-α) (E α x)))) =
      x + E (-α) (E α x) + E α (E (-α) (E α x)) + (E α x + E α x) from by abel,
    add_self_eq_zero K (E α x), add_zero]

theorem IsRootForm.weyl (hform : IsRootForm D ρ E j)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) (hC : IsSmallClass (Nat.card Kˣ) σ C)
    (hE : ∀ α, IsD4Root α → ∀ a : Fin 4 → ZMod (Nat.card Kˣ),
      ∀ x ∈ D.wtSpace ρ a, E α x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α))
    {α : Fin 4 → ℤ} (hα : IsD4Root α) {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C)
    (haα : a + σ • castW (Nat.card Kˣ) α ∈ C) {x : X} (hx : x ∈ D.wtSpace ρ a) :
    E (-α) (E α x) = x := by
  have hBx : E (-α) x = 0 := by
    refine eq_zero_of_mem_wtSpace_of_not_mem (D := D) (ρ := ρ) (C := C) hCw ?_
      (hE (-α) hα.neg a x hx)
    have h : a + σ • castW (Nat.card Kˣ) (-α) = a - σ • castW (Nat.card Kˣ) α := by
      rw [castW_neg, smul_neg, sub_eq_add_neg]
    rw [h]
    exact hC.sub_not_mem a ha α hα haα
  have hAAx : E α (E α x) = 0 := by
    have h := congrArg (fun f : Module.End K X => f x) (IsRootForm.mul_self hform hα)
    simpa [Module.End.mul_apply] using h
  have hBAx : E (-α) (E α x) ∈ D.wtSpace ρ a := by
    have h1 : E α x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α) := hE α hα a x hx
    have h2 := hE (-α) hα.neg (a + σ • castW (Nat.card Kˣ) α) (E α x) h1
    have hw : (a + σ • castW (Nat.card Kˣ) α) + σ • castW (Nat.card Kˣ) (-α) = a := by
      rw [castW_neg, smul_neg, add_assoc, add_neg_cancel, add_zero]
    rwa [hw] at h2
  have hABAx : E α (E (-α) (E α x)) ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α) :=
    hE α hα a (E (-α) (E α x)) hBAx
  have hsum : x + E (-α) (E α x) ∈ D.wtSpace ρ a := Submodule.add_mem _ hx hBAx
  have hn : ρ (D.n α) x = (x + E (-α) (E α x)) + E α (E (-α) (E α x)) :=
    n_apply_eq hform hα hBx hAAx
  have hwt : ρ (D.n α) x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α) := by
    have hx' : ρ (D.n α) x ∈ (D.wtSpace ρ a).map (ρ (D.n α)) := ⟨x, hx, rfl⟩
    rw [map_n_wtSpace D ρ α hα a, hC.reflW_eq a ha α hα haα] at hx'
    exact hx'
  have hzero : x + E (-α) (E α x) = 0 := by
    have hmem : (x + E (-α) (E α x)) + E α (E (-α) (E α x)) ∈
        D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α) := by
      rw [← hn]
      exact hwt
    have hsub : x + E (-α) (E α x) ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α) := by
      have h := Submodule.sub_mem _ hmem hABAx
      rwa [add_sub_cancel_right] at h
    exact eq_zero_of_mem_wtSpace_of_mem_wtSpace D ρ
      (Ne.symm (hC.add_smul_castW_ne a hα)) hsum hsub
  refine add_left_cancel (a := x) (b := E (-α) (E α x)) (c := x) ?_
  rw [hzero, add_self_eq_zero K x]

private theorem exists_mem_ne_neg_ne_four {N : ℕ} {σ : ZMod N} {C : Finset (Fin 4 → ZMod N)}
    (hC : IsSmallClass N σ C) {a m : Fin 4 → ZMod N} (ha : a ∈ C) (hm : m ∈ C) :
    ∃ m₃ ∈ C, m₃ ≠ a ∧ m₃ ≠ -a ∧ m₃ ≠ m ∧ m₃ ≠ -m := by
  have h4 : ({a, -a, m, -m} : Finset (Fin 4 → ZMod N)).card ≤ 4 := by
    have h1 := Finset.card_insert_le a ({-a, m, -m} : Finset (Fin 4 → ZMod N))
    have h2 := Finset.card_insert_le (-a) ({m, -m} : Finset (Fin 4 → ZMod N))
    have h3 := Finset.card_insert_le m ({-m} : Finset (Fin 4 → ZMod N))
    have h0 : ({-m} : Finset (Fin 4 → ZMod N)).card ≤ 1 := by simp
    omega
  have hlt : ({a, -a, m, -m} : Finset (Fin 4 → ZMod N)).card < C.card := by
    rw [hC.card_eq]
    omega
  obtain ⟨m₃, hm₃, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
  exact ⟨m₃, hm₃, hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2⟩

theorem IsRootForm.triangle (hform : IsRootForm D ρ E j) (hμ : ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) (hC : IsSmallClass (Nat.card Kˣ) σ C)
    (hE : ∀ α, IsD4Root α → ∀ a : Fin 4 → ZMod (Nat.card Kˣ),
      ∀ x ∈ D.wtSpace ρ a, E α x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α))
    {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) {γ β : Fin 4 → ℤ} (hγ : IsD4Root γ)
    (hβ : IsD4Root β) (h1 : a + σ • castW (Nat.card Kˣ) γ ∈ C)
    (h2 : a + σ • castW (Nat.card Kˣ) (γ + β) ∈ C)
    (h3 : a + σ • castW (Nat.card Kˣ) (γ + β) ≠ a)
    (h4 : a + σ • castW (Nat.card Kˣ) (γ + β) ≠ -a)
    {x : X} (hx : x ∈ D.wtSpace ρ a) :
    γ ⬝ᵥ β = -1 ∧ IsD4Root (γ + β) ∧ E (γ + β) x = E β (E γ x) := by
  obtain ⟨hd, hb, -⟩ := hC.triangle a ha γ β hγ hβ h1 h2 h3 h4
  have hβx : E β x = 0 :=
    eq_zero_of_mem_wtSpace_of_not_mem (D := D) (ρ := ρ) (C := C) hCw hb (hE β hβ a x hx)
  refine ⟨hd, IsD4Root.add hγ hβ hd, ?_⟩
  rw [IsRootForm.add_eq hform hμ hγ hβ hd]
  simp only [LinearMap.add_apply, Module.End.mul_apply, hβx, map_zero, zero_add]

private theorem path_indep_ne (hform : IsRootForm D ρ E j) (hμ : ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) (hC : IsSmallClass (Nat.card Kˣ) σ C)
    (hE : ∀ α, IsD4Root α → ∀ a : Fin 4 → ZMod (Nat.card Kˣ),
      ∀ x ∈ D.wtSpace ρ a, E α x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α))
    {a₀ m m' : Fin 4 → ZMod (Nat.card Kˣ)} (ha₀ : a₀ ∈ C) (hm : m ∈ C) (hm' : m' ∈ C)
    (hmm : m' ≠ m) (hmm' : m' ≠ -m)
    {β β' γ δ' : Fin 4 → ℤ} (hβ : IsD4Root β) (hβ' : IsD4Root β') (hγ : IsD4Root γ)
    (hδ' : IsD4Root δ') (eβ : a₀ + σ • castW (Nat.card Kˣ) β = m)
    (eβ' : m + σ • castW (Nat.card Kˣ) β' = -a₀)
    (eγ : a₀ + σ • castW (Nat.card Kˣ) γ = m')
    (eδ' : m' + σ • castW (Nat.card Kˣ) δ' = -a₀) {v : X} (hv : v ∈ D.wtSpace ρ a₀) :
    E β' (E β v) = E δ' (E γ v) := by
  obtain ⟨δ, hδ, eδ⟩ := hC.adj m hm m' hm' hmm hmm'
  have eδm : m + σ • castW (Nat.card Kˣ) δ = m' := eδ.symm
  have hm_a : m ≠ a₀ := by rw [← eβ]; exact hC.add_smul_castW_ne a₀ hβ
  have hm_na : m ≠ -a₀ := by rw [← eβ]; exact hC.ne_neg a₀ ha₀ β hβ
  have hm'_a : m' ≠ a₀ := by rw [← eγ]; exact hC.add_smul_castW_ne a₀ hγ
  have hm'_na : m' ≠ -a₀ := by rw [← eγ]; exact hC.ne_neg a₀ ha₀ γ hγ
  have hbd : a₀ + σ • castW (Nat.card Kˣ) (β + δ) = m' := by
    rw [castW_add, smul_add, ← add_assoc, eβ, eδm]
  obtain ⟨hd, hroot, hEq1⟩ := hform.triangle hμ hCw hC hE ha₀ hβ hδ (by rw [eβ]; exact hm)
    (by rw [hbd]; exact hm') (by rw [hbd]; exact hm'_a) (by rw [hbd]; exact hm'_na) hv
  have hy : E β v ∈ D.wtSpace ρ m := by rw [← eβ]; exact hE β hβ a₀ v hv
  have htri2 : m + σ • castW (Nat.card Kˣ) (δ + δ') = -a₀ := by
    rw [castW_add, smul_add, ← add_assoc, eδm, eδ']
  obtain ⟨hd2, hroot2, hEq2⟩ := hform.triangle hμ hCw hC hE hm hδ hδ'
    (by rw [eδm]; exact hm') (by rw [htri2]; exact hC.neg_mem a₀ ha₀)
    (by rw [htri2]; exact hm_na.symm)
    (by rw [htri2]; intro h; exact hm_a.symm (neg_injective h)) hy
  have hbdeq : β + δ = γ := hC.smul_castW_inj hroot hγ (by
    have h : a₀ + σ • castW (Nat.card Kˣ) (β + δ) = a₀ + σ • castW (Nat.card Kˣ) γ := by
      rw [hbd, eγ]
    exact add_left_cancel h)
  have hδ'eq : δ + δ' = β' := hC.smul_castW_inj hroot2 hβ' (by
    have h : m + σ • castW (Nat.card Kˣ) (δ + δ') = m + σ • castW (Nat.card Kˣ) β' := by
      rw [htri2, eβ']
    exact add_left_cancel h)
  rw [← hδ'eq, ← hbdeq, hEq2, hEq1]

theorem IsRootForm.path_indep (hform : IsRootForm D ρ E j) (hμ : ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) (hC : IsSmallClass (Nat.card Kˣ) σ C)
    (hE : ∀ α, IsD4Root α → ∀ a : Fin 4 → ZMod (Nat.card Kˣ),
      ∀ x ∈ D.wtSpace ρ a, E α x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α))
    {a₀ m₁ m₂ : Fin 4 → ZMod (Nat.card Kˣ)} (ha₀ : a₀ ∈ C) (hm₁ : m₁ ∈ C) (hm₂ : m₂ ∈ C)
    {β₁ β₁' β₂ β₂' : Fin 4 → ℤ} (hβ₁ : IsD4Root β₁) (hβ₁' : IsD4Root β₁') (hβ₂ : IsD4Root β₂)
    (hβ₂' : IsD4Root β₂') (e₁ : a₀ + σ • castW (Nat.card Kˣ) β₁ = m₁)
    (e₁' : m₁ + σ • castW (Nat.card Kˣ) β₁' = -a₀)
    (e₂ : a₀ + σ • castW (Nat.card Kˣ) β₂ = m₂)
    (e₂' : m₂ + σ • castW (Nat.card Kˣ) β₂' = -a₀) {v : X} (hv : v ∈ D.wtSpace ρ a₀) :
    E β₁' (E β₁ v) = E β₂' (E β₂ v) := by
  by_cases h12 : m₂ = m₁
  · have hb2 : β₂ = β₁ := hC.smul_castW_inj hβ₂ hβ₁ (by
      have h : a₀ + σ • castW (Nat.card Kˣ) β₂ = a₀ + σ • castW (Nat.card Kˣ) β₁ := by
        rw [e₂, e₁]
        exact h12
      exact add_left_cancel h)
    have hb2' : β₂' = β₁' := hC.smul_castW_inj hβ₂' hβ₁' (by
      have h : m₁ + σ • castW (Nat.card Kˣ) β₂' = m₁ + σ • castW (Nat.card Kˣ) β₁' := by
        calc m₁ + σ • castW (Nat.card Kˣ) β₂'
            = m₂ + σ • castW (Nat.card Kˣ) β₂' := by rw [← h12]
          _ = -a₀ := e₂'
          _ = m₁ + σ • castW (Nat.card Kˣ) β₁' := e₁'.symm
      exact add_left_cancel h)
    rw [hb2, hb2']
  · by_cases h2 : m₂ = -m₁
    · obtain ⟨m₃, hm₃, h3a, h3na, h3m, h3nm⟩ := exists_mem_ne_neg_ne_four hC ha₀ hm₁
      have hnega : -a₀ ∈ C := hC.neg_mem a₀ ha₀
      obtain ⟨γ, hγ, eγ⟩ := hC.adj a₀ ha₀ m₃ hm₃ h3a h3na
      obtain ⟨γ', hγ', eγ'⟩ := hC.adj m₃ hm₃ (-a₀) hnega h3na.symm
        (fun h => h3a.symm (neg_injective h))
      have h1 := path_indep_ne hform hμ hCw hC hE ha₀ hm₁ hm₃ h3m h3nm hβ₁ hβ₁' hγ hγ'
        e₁ e₁' eγ.symm eγ'.symm hv
      have h2' := path_indep_ne hform hμ hCw hC hE ha₀ hm₃ hm₂
        (by rw [h2]; exact h3nm.symm) (by rw [h2]; intro h; exact h3m.symm (neg_injective h))
        hγ hγ' hβ₂ hβ₂' eγ.symm eγ'.symm e₂ e₂' hv
      rw [h1, h2']
    · exact path_indep_ne hform hμ hCw hC hE ha₀ hm₁ hm₂ h12 h2 hβ₁ hβ₁' hβ₂ hβ₂' e₁ e₁' e₂
        e₂' hv

private noncomputable def stepRoot (σ : ZMod (Nat.card Kˣ))
    (a a' : Fin 4 → ZMod (Nat.card Kˣ)) : Fin 4 → ℤ :=
  if h : ∃ γ, IsD4Root γ ∧ a' = a + σ • castW (Nat.card Kˣ) γ then h.choose else 0

private theorem stepRoot_spec {a a' : Fin 4 → ZMod (Nat.card Kˣ)}
    (h : ∃ γ, IsD4Root γ ∧ a' = a + σ • castW (Nat.card Kˣ) γ) :
    IsD4Root (stepRoot σ a a') ∧ a' = a + σ • castW (Nat.card Kˣ) (stepRoot σ a a') := by
  simp only [stepRoot, dif_pos h]
  exact h.choose_spec

private theorem stepRoot_eq (hC : IsSmallClass (Nat.card Kˣ) σ C)
    {a a' : Fin 4 → ZMod (Nat.card Kˣ)}
    {γ : Fin 4 → ℤ} (hγ : IsD4Root γ) (h : a' = a + σ • castW (Nat.card Kˣ) γ) :
    stepRoot σ a a' = γ := by
  obtain ⟨hroot, hspec⟩ := stepRoot_spec (σ := σ) ⟨γ, hγ, h⟩
  refine hC.smul_castW_inj hroot hγ ?_
  have hh : a + σ • castW (Nat.card Kˣ) (stepRoot σ a a') =
      a + σ • castW (Nat.card Kˣ) γ := by rw [← hspec, h]
  exact add_left_cancel hh

private theorem stepRoot_spec_of_mem (hC : IsSmallClass (Nat.card Kˣ) σ C)
    {a a' : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) (ha' : a' ∈ C) (hne : a' ≠ a)
    (hne' : a' ≠ -a) :
    IsD4Root (stepRoot σ a a') ∧ a + σ • castW (Nat.card Kˣ) (stepRoot σ a a') = a' := by
  obtain ⟨γ, hγ, hγ'⟩ := hC.adj a ha a' ha' hne hne'
  obtain ⟨hroot, -⟩ := stepRoot_spec (σ := σ) ⟨γ, hγ, hγ'⟩
  exact ⟨hroot, by rw [stepRoot_eq hC hγ hγ']; exact hγ'.symm⟩

private noncomputable def T (σ : ZMod (Nat.card Kˣ)) (E : (Fin 4 → ℤ) → Module.End K X)
    (a₀ m : Fin 4 → ZMod (Nat.card Kˣ)) (v : X) :
    (Fin 4 → ZMod (Nat.card Kˣ)) → X :=
  fun a =>
    if a = a₀ then v
    else if a = -a₀ then E (stepRoot σ m (-a₀)) (E (stepRoot σ a₀ m) v)
    else E (stepRoot σ a₀ a) v

private theorem T_self (σ : ZMod (Nat.card Kˣ)) (E : (Fin 4 → ℤ) → Module.End K X)
    (a₀ m : Fin 4 → ZMod (Nat.card Kˣ)) (v : X) : T σ E a₀ m v a₀ = v := by
  simp [T]

private theorem T_neg (σ : ZMod (Nat.card Kˣ)) (E : (Fin 4 → ℤ) → Module.End K X)
    (a₀ m : Fin 4 → ZMod (Nat.card Kˣ)) (v : X) (h : a₀ ≠ -a₀) :
    T σ E a₀ m v (-a₀) = E (stepRoot σ m (-a₀)) (E (stepRoot σ a₀ m) v) := by
  simp [T, Ne.symm h]

private theorem T_other (σ : ZMod (Nat.card Kˣ)) (E : (Fin 4 → ℤ) → Module.End K X)
    (a₀ m a : Fin 4 → ZMod (Nat.card Kˣ)) (v : X) (h1 : a ≠ a₀) (h2 : a ≠ -a₀) :
    T σ E a₀ m v a = E (stepRoot σ a₀ a) v := by
  simp [T, h1, h2]

private theorem T_of_root (hC : IsSmallClass (Nat.card Kˣ) σ C)
    {a₀ m a : Fin 4 → ZMod (Nat.card Kˣ)} {v : X}
    {γ : Fin 4 → ℤ} (hγ : IsD4Root γ) (ha : a ≠ a₀) (hna : a ≠ -a₀)
    (h : a = a₀ + σ • castW (Nat.card Kˣ) γ) :
    T σ E a₀ m v a = E γ v := by
  rw [T_other σ E a₀ m a v ha hna, stepRoot_eq hC hγ h]

private theorem T_weight (hC : IsSmallClass (Nat.card Kˣ) σ C)
    (hE : ∀ α, IsD4Root α → ∀ a : Fin 4 → ZMod (Nat.card Kˣ),
      ∀ x ∈ D.wtSpace ρ a, E α x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α))
    {a₀ m : Fin 4 → ZMod (Nat.card Kˣ)} (ha₀ : a₀ ∈ C) (hna : a₀ ≠ -a₀) (hm : m ∈ C)
    (hm_a : m ≠ a₀) (hm_na : m ≠ -a₀) {v : X} (hv : v ∈ D.wtSpace ρ a₀)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) :
    T σ E a₀ m v a ∈ D.wtSpace ρ a := by
  have h1 := stepRoot_spec_of_mem hC ha₀ hm hm_a hm_na
  have h2 := stepRoot_spec_of_mem hC hm (hC.neg_mem a₀ ha₀) hm_na.symm
    (fun h => hm_a.symm (neg_injective h))
  by_cases hsel : a = a₀
  · rw [hsel, T_self]
    exact hv
  · by_cases hsel' : a = -a₀
    · rw [hsel', T_neg σ E a₀ m v hna]
      have hy : E (stepRoot σ a₀ m) v ∈ D.wtSpace ρ m := by
        have h := hE (stepRoot σ a₀ m) h1.1 a₀ v hv
        rwa [h1.2] at h
      have h := hE (stepRoot σ m (-a₀)) h2.1 m (E (stepRoot σ a₀ m) v) hy
      rwa [h2.2] at h
    · rw [T_other σ E a₀ m a v hsel hsel']
      obtain ⟨hroot, hstep⟩ := stepRoot_spec_of_mem hC ha₀ ha hsel hsel'
      have h := hE (stepRoot σ a₀ a) hroot a₀ v hv
      rwa [hstep] at h

private theorem T_ne_zero (hform : IsRootForm D ρ E j)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) (hC : IsSmallClass (Nat.card Kˣ) σ C)
    (hE : ∀ α, IsD4Root α → ∀ a : Fin 4 → ZMod (Nat.card Kˣ),
      ∀ x ∈ D.wtSpace ρ a, E α x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α))
    {a₀ m : Fin 4 → ZMod (Nat.card Kˣ)} (ha₀ : a₀ ∈ C) (hna : a₀ ≠ -a₀) (hm : m ∈ C)
    (hm_a : m ≠ a₀) (hm_na : m ≠ -a₀) {v : X} (hv : v ∈ D.wtSpace ρ a₀) (hv0 : v ≠ 0)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) :
    T σ E a₀ m v a ≠ 0 := by
  have h1 := stepRoot_spec_of_mem hC ha₀ hm hm_a hm_na
  have h2 := stepRoot_spec_of_mem hC hm (hC.neg_mem a₀ ha₀) hm_na.symm
    (fun h => hm_a.symm (neg_injective h))
  by_cases hsel : a = a₀
  · rw [hsel, T_self]
    exact hv0
  · by_cases hsel' : a = -a₀
    · rw [hsel', T_neg σ E a₀ m v hna]
      have hy : E (stepRoot σ a₀ m) v ∈ D.wtSpace ρ m := by
        have h := hE (stepRoot σ a₀ m) h1.1 a₀ v hv
        rwa [h1.2] at h
      have hy0 : E (stepRoot σ a₀ m) v ≠ 0 := by
        intro hzero
        have hw := hform.weyl hCw hC hE h1.1 ha₀ (by rw [h1.2]; exact hm) hv
        rw [hzero, map_zero] at hw
        exact hv0 hw.symm
      intro hzero
      have hw := hform.weyl hCw hC hE h2.1 hm (by rw [h2.2]; exact hC.neg_mem a₀ ha₀) hy
      rw [hzero, map_zero] at hw
      exact hy0 hw.symm
    · rw [T_other σ E a₀ m a v hsel hsel']
      obtain ⟨hroot, hstep⟩ := stepRoot_spec_of_mem hC ha₀ ha hsel hsel'
      intro hzero
      have hw := hform.weyl hCw hC hE hroot ha₀ (by rw [hstep]; exact ha) hv
      rw [hzero, map_zero] at hw
      exact hv0 hw.symm

private theorem T_root_one (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) σ C)
    (hE : ∀ α, IsD4Root α → ∀ a : Fin 4 → ZMod (Nat.card Kˣ),
      ∀ x ∈ D.wtSpace ρ a, E α x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α))
    {a₀ m : Fin 4 → ZMod (Nat.card Kˣ)} (ha₀ : a₀ ∈ C) (hna : a₀ ≠ -a₀) (hm : m ∈ C)
    (hm_a : m ≠ a₀) (hm_na : m ≠ -a₀) {v : X} (hv : v ∈ D.wtSpace ρ a₀)
    {β : Fin 4 → ℤ} (hβ : IsD4Root β) :
    E β v = 0 ∨ ∃ a ∈ C, E β v = T σ E a₀ m v a := by
  by_cases hmem : a₀ + σ • castW (Nat.card Kˣ) β ∈ C
  · refine Or.inr ⟨a₀ + σ • castW (Nat.card Kˣ) β, hmem, ?_⟩
    exact (T_of_root hC hβ (hC.add_smul_castW_ne a₀ hβ) (hC.ne_neg a₀ ha₀ β hβ) rfl).symm
  · exact Or.inl (eq_zero_of_mem_wtSpace_of_not_mem (D := D) (ρ := ρ) (C := C) hCw hmem
      (hE β hβ a₀ v hv))

private theorem T_root_two (hform : IsRootForm D ρ E j) (hμ : ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) (hC : IsSmallClass (Nat.card Kˣ) σ C)
    (hE : ∀ α, IsD4Root α → ∀ a : Fin 4 → ZMod (Nat.card Kˣ),
      ∀ x ∈ D.wtSpace ρ a, E α x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α))
    {a₀ m : Fin 4 → ZMod (Nat.card Kˣ)} (ha₀ : a₀ ∈ C) (hna : a₀ ≠ -a₀) (hm : m ∈ C)
    (hm_a : m ≠ a₀) (hm_na : m ≠ -a₀) {v : X} (hv : v ∈ D.wtSpace ρ a₀)
    {β β' : Fin 4 → ℤ} (hβ : IsD4Root β) (hβ' : IsD4Root β') :
    E β' (E β v) = 0 ∨ ∃ a ∈ C, E β' (E β v) = T σ E a₀ m v a := by
  set a₁ := a₀ + σ • castW (Nat.card Kˣ) β with ha₁
  set a₂ := a₁ + σ • castW (Nat.card Kˣ) β' with ha₂
  have hroot1 := stepRoot_spec_of_mem hC ha₀ hm hm_a hm_na
  have hroot2 := stepRoot_spec_of_mem hC hm (hC.neg_mem a₀ ha₀) hm_na.symm
    (fun h => hm_a.symm (neg_injective h))
  by_cases h1 : a₁ ∈ C
  · have hβv : E β v = T σ E a₀ m v a₁ := by
      rw [T_of_root (v := v) (γ := β) hC hβ (by rw [ha₁]; exact hC.add_smul_castW_ne a₀ hβ)
        (by rw [ha₁]; exact hC.ne_neg a₀ ha₀ β hβ) ha₁]
    by_cases h2 : a₂ ∈ C
    · by_cases h3 : a₂ = a₀
      · have hb' : β' = -β := by
          refine hC.smul_castW_inj hβ' hβ.neg ?_
          have h : a₁ + σ • castW (Nat.card Kˣ) β' = a₁ + σ • castW (Nat.card Kˣ) (-β) := by
            rw [← ha₂, h3, castW_neg, smul_neg, ha₁, add_assoc, add_neg_cancel, add_zero]
          exact add_left_cancel h
        refine Or.inr ⟨a₀, ha₀, ?_⟩
        rw [hb', T_self]
        exact hform.weyl hCw hC hE hβ ha₀ h1 hv
      · by_cases h4 : a₂ = -a₀
        · refine Or.inr ⟨-a₀, hC.neg_mem a₀ ha₀, ?_⟩
          have hpi := hform.path_indep hμ hCw hC hE ha₀ h1 hm hβ hβ' hroot1.1 hroot2.1
            ha₁.symm (by rw [← ha₂]; exact h4) hroot1.2 hroot2.2 hv
          rw [T_neg σ E a₀ m v hna]
          exact hpi
        · have ha₂eq : a₀ + σ • castW (Nat.card Kˣ) (β + β') = a₂ := by
            rw [castW_add, smul_add, ← add_assoc, ← ha₁, ← ha₂]
          obtain ⟨hd, hroot, hEq⟩ := hform.triangle hμ hCw hC hE ha₀ hβ hβ' h1
            (by rw [ha₂eq]; exact h2) (by rw [ha₂eq]; exact h3) (by rw [ha₂eq]; exact h4) hv
          rcases T_root_one hCw hC hE ha₀ hna hm hm_a hm_na hv hroot with h0 | ⟨a, haC, hTa⟩
          · exact Or.inl (by rw [← hEq, h0])
          · exact Or.inr ⟨a, haC, by rw [← hEq, hTa]⟩
    · refine Or.inl ?_
      rw [hβv]
      have hmem := hE β' hβ' a₁ (T σ E a₀ m v a₁) (T_weight hC hE ha₀ hna hm hm_a hm_na hv h1)
      rw [← ha₂] at hmem
      exact eq_zero_of_mem_wtSpace_of_not_mem (D := D) (ρ := ρ) (C := C) hCw h2 hmem
  · refine Or.inl ?_
    rw [eq_zero_of_mem_wtSpace_of_not_mem (D := D) (ρ := ρ) (C := C) hCw h1 (hE β hβ a₀ v hv),
      map_zero]

private theorem T_root_three_neg (hform : IsRootForm D ρ E j) (hμ : ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) (hC : IsSmallClass (Nat.card Kˣ) σ C)
    (hE : ∀ α, IsD4Root α → ∀ a : Fin 4 → ZMod (Nat.card Kˣ),
      ∀ x ∈ D.wtSpace ρ a, E α x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α))
    {a₀ m : Fin 4 → ZMod (Nat.card Kˣ)} (ha₀ : a₀ ∈ C) (hna : a₀ ≠ -a₀) (hm : m ∈ C)
    (hm_a : m ≠ a₀) (hm_na : m ≠ -a₀) {v : X} (hv : v ∈ D.wtSpace ρ a₀)
    {β'' : Fin 4 → ℤ} (hβ'' : IsD4Root β'') :
    E β'' (T σ E a₀ m v (-a₀)) = 0 ∨
      ∃ a ∈ C, E β'' (T σ E a₀ m v (-a₀)) = T σ E a₀ m v a := by
  have hroot1 := stepRoot_spec_of_mem hC ha₀ hm hm_a hm_na
  have hroot2 := stepRoot_spec_of_mem hC hm (hC.neg_mem a₀ ha₀) hm_na.symm
    (fun h => hm_a.symm (neg_injective h))
  set a₃ := -a₀ + σ • castW (Nat.card Kˣ) β'' with ha₃
  by_cases h3 : a₃ ∈ C
  · have h3_a : a₃ ≠ a₀ := by
      rw [ha₃]
      simpa using hC.ne_neg (-a₀) (hC.neg_mem a₀ ha₀) β'' hβ''
    have h3_na : a₃ ≠ -a₀ := by
      rw [ha₃]
      exact hC.add_smul_castW_ne (-a₀) hβ''
    obtain ⟨hroot3, hstep3⟩ := stepRoot_spec_of_mem hC ha₀ h3 h3_a h3_na
    have e3 : a₃ + σ • castW (Nat.card Kˣ) (-β'') = -a₀ := by
      rw [ha₃, castW_neg, smul_neg, add_assoc, add_neg_cancel, add_zero]
    have hpi := hform.path_indep hμ hCw hC hE ha₀ hm h3 hroot1.1 hroot2.1 hroot3 hβ''.neg
      hroot1.2 hroot2.2 hstep3 e3 hv
    have hy : E (stepRoot σ a₀ a₃) v ∈ D.wtSpace ρ a₃ := by
      have h := hE (stepRoot σ a₀ a₃) hroot3 a₀ v hv
      rwa [hstep3] at h
    have hw := hform.weyl hCw hC hE hβ''.neg h3
      (by rw [e3]; exact hC.neg_mem a₀ ha₀) hy
    rw [neg_neg] at hw
    refine Or.inr ⟨a₃, h3, ?_⟩
    rw [T_neg σ E a₀ m v hna, hpi, hw, T_other σ E a₀ m a₃ v h3_a h3_na]
  · refine Or.inl ?_
    rw [T_neg σ E a₀ m v hna]
    have hy : E (stepRoot σ a₀ m) v ∈ D.wtSpace ρ m := by
      have h := hE (stepRoot σ a₀ m) hroot1.1 a₀ v hv
      rwa [hroot1.2] at h
    have hmem : E (stepRoot σ m (-a₀)) (E (stepRoot σ a₀ m) v) ∈
        D.wtSpace ρ (-a₀) := by
      have h := hE (stepRoot σ m (-a₀)) hroot2.1 m (E (stepRoot σ a₀ m) v) hy
      rwa [hroot2.2] at h
    have hmem2 := hE β'' hβ'' (-a₀) (E (stepRoot σ m (-a₀)) (E (stepRoot σ a₀ m) v)) hmem
    rw [← ha₃] at hmem2
    exact eq_zero_of_mem_wtSpace_of_not_mem (D := D) (ρ := ρ) (C := C) hCw h3 hmem2

private theorem T_root_three (hform : IsRootForm D ρ E j) (hμ : ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) (hC : IsSmallClass (Nat.card Kˣ) σ C)
    (hE : ∀ α, IsD4Root α → ∀ a : Fin 4 → ZMod (Nat.card Kˣ),
      ∀ x ∈ D.wtSpace ρ a, E α x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α))
    {a₀ m : Fin 4 → ZMod (Nat.card Kˣ)} (ha₀ : a₀ ∈ C) (hna : a₀ ≠ -a₀) (hm : m ∈ C)
    (hm_a : m ≠ a₀) (hm_na : m ≠ -a₀) {v : X} (hv : v ∈ D.wtSpace ρ a₀)
    {β β' β'' : Fin 4 → ℤ} (hβ : IsD4Root β) (hβ' : IsD4Root β') (hβ'' : IsD4Root β'') :
    E β'' (E β' (E β v)) = 0 ∨ ∃ a ∈ C, E β'' (E β' (E β v)) = T σ E a₀ m v a := by
  rcases T_root_two hform hμ hCw hC hE ha₀ hna hm hm_a hm_na hv hβ hβ' with h0 | ⟨a₂, ha₂, hTa⟩
  · exact Or.inl (by rw [h0, map_zero])
  · rw [hTa]
    by_cases hsel : a₂ = a₀
    · rw [hsel, T_self]
      exact T_root_one hCw hC hE ha₀ hna hm hm_a hm_na hv hβ''
    · by_cases hsel' : a₂ = -a₀
      · rw [hsel']
        exact T_root_three_neg hform hμ hCw hC hE ha₀ hna hm hm_a hm_na hv hβ''
      · rw [T_other σ E a₀ m a₂ v hsel hsel']
        exact T_root_two hform hμ hCw hC hE ha₀ hna hm hm_a hm_na hv
          (stepRoot_spec_of_mem hC ha₀ ha₂ hsel hsel').1 hβ''

private theorem T_root_apply_disj (hform : IsRootForm D ρ E j) (hμ : ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) (hC : IsSmallClass (Nat.card Kˣ) σ C)
    (hE : ∀ α, IsD4Root α → ∀ a : Fin 4 → ZMod (Nat.card Kˣ),
      ∀ x ∈ D.wtSpace ρ a, E α x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α))
    {a₀ m : Fin 4 → ZMod (Nat.card Kˣ)} (ha₀ : a₀ ∈ C) (hna : a₀ ≠ -a₀) (hm : m ∈ C)
    (hm_a : m ≠ a₀) (hm_na : m ≠ -a₀) {v : X} (hv : v ∈ D.wtSpace ρ a₀)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) {β : Fin 4 → ℤ} (hβ : IsD4Root β) :
    E β (T σ E a₀ m v a) = 0 ∨ ∃ a' ∈ C, E β (T σ E a₀ m v a) = T σ E a₀ m v a' := by
  have hroot1 := stepRoot_spec_of_mem hC ha₀ hm hm_a hm_na
  have hroot2 := stepRoot_spec_of_mem hC hm (hC.neg_mem a₀ ha₀) hm_na.symm
    (fun h => hm_a.symm (neg_injective h))
  by_cases h1 : a = a₀
  · rw [h1, T_self]
    exact T_root_one hCw hC hE ha₀ hna hm hm_a hm_na hv hβ
  · by_cases h2 : a = -a₀
    · rw [h2, T_neg σ E a₀ m v hna]
      exact T_root_three hform hμ hCw hC hE ha₀ hna hm hm_a hm_na hv hroot1.1 hroot2.1 hβ
    · rw [T_other σ E a₀ m a v h1 h2]
      exact T_root_two hform hμ hCw hC hE ha₀ hna hm hm_a hm_na hv
        (stepRoot_spec_of_mem hC ha₀ ha h1 h2).1 hβ

private theorem T_root_apply_mem (hform : IsRootForm D ρ E j) (hμ : ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) (hC : IsSmallClass (Nat.card Kˣ) σ C)
    (hE : ∀ α, IsD4Root α → ∀ a : Fin 4 → ZMod (Nat.card Kˣ),
      ∀ x ∈ D.wtSpace ρ a, E α x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α))
    {a₀ m : Fin 4 → ZMod (Nat.card Kˣ)} (ha₀ : a₀ ∈ C) (hna : a₀ ≠ -a₀) (hm : m ∈ C)
    (hm_a : m ≠ a₀) (hm_na : m ≠ -a₀) {v : X} (hv : v ∈ D.wtSpace ρ a₀) (hv0 : v ≠ 0)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) {β : Fin 4 → ℤ} (hβ : IsD4Root β) :
    E β (T σ E a₀ m v a) =
      if a + σ • castW (Nat.card Kˣ) β ∈ C then T σ E a₀ m v (a + σ • castW (Nat.card Kˣ) β)
      else 0 := by
  have hTa : T σ E a₀ m v a ∈ D.wtSpace ρ a :=
    T_weight hC hE ha₀ hna hm hm_a hm_na hv ha
  have hTa0 : T σ E a₀ m v a ≠ 0 :=
    T_ne_zero hform hCw hC hE ha₀ hna hm hm_a hm_na hv hv0 ha
  have hwt : E β (T σ E a₀ m v a) ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) β) :=
    hE β hβ a (T σ E a₀ m v a) hTa
  have hdisj := T_root_apply_disj hform hμ hCw hC hE ha₀ hna hm hm_a hm_na hv ha hβ
  by_cases hmem : a + σ • castW (Nat.card Kˣ) β ∈ C
  · rw [if_pos hmem]
    rcases hdisj with h0 | ⟨a', ha', hTa'⟩
    · have hne : E β (T σ E a₀ m v a) ≠ 0 := by
        intro h
        have hw := hform.weyl hCw hC hE hβ ha hmem hTa
        rw [h, map_zero] at hw
        exact hTa0 hw.symm
      exact absurd h0 hne
    · have hwt' : T σ E a₀ m v a' ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) β) := by
        rw [← hTa']
        exact hwt
      have hTa'0 : T σ E a₀ m v a' ≠ 0 :=
        T_ne_zero hform hCw hC hE ha₀ hna hm hm_a hm_na hv hv0 ha'
      have hTa'wt : T σ E a₀ m v a' ∈ D.wtSpace ρ a' :=
        T_weight hC hE ha₀ hna hm hm_a hm_na hv ha'
      have heq : a' = a + σ • castW (Nat.card Kˣ) β := by
        by_contra hne
        exact hTa'0 (eq_zero_of_mem_wtSpace_of_mem_wtSpace D ρ hne hTa'wt hwt')
      rw [hTa', heq]
  · rw [if_neg hmem]
    exact eq_zero_of_mem_wtSpace_of_not_mem (D := D) (ρ := ρ) (C := C) hCw hmem hwt

private theorem span_T_eq_top (hform : IsRootForm D ρ E j) (hμ : ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) (hC : IsSmallClass (Nat.card Kˣ) σ C)
    (hE : ∀ α, IsD4Root α → ∀ a : Fin 4 → ZMod (Nat.card Kˣ),
      ∀ x ∈ D.wtSpace ρ a, E α x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α))
    {a₀ m : Fin 4 → ZMod (Nat.card Kˣ)} (ha₀ : a₀ ∈ C) (hna : a₀ ≠ -a₀) (hm : m ∈ C)
    (hm_a : m ≠ a₀) (hm_na : m ≠ -a₀) {v : X} (hv : v ∈ D.wtSpace ρ a₀) (hv0 : v ≠ 0)
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤) :
    Submodule.span K (T σ E a₀ m v '' (C : Set (Fin 4 → ZMod (Nat.card Kˣ)))) = ⊤ := by
  set M : Submodule K X := Submodule.span K (T σ E a₀ m v '' (C : Set _)) with hMdef
  have hgen : ∀ a ∈ C, T σ E a₀ m v a ∈ M := fun a ha =>
    Submodule.subset_span (Set.mem_image_of_mem _ ha)
  have hME : ∀ α, IsD4Root α → ∀ x ∈ M, E α x ∈ M := by
    intro α hα x hx
    have hle : M ≤ Submodule.comap (E α) M := by
      rw [hMdef]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, ha, rfl⟩
      show E α (T σ E a₀ m v a) ∈ M
      rw [T_root_apply_mem hform hμ hCw hC hE ha₀ hna hm hm_a hm_na hv hv0 ha hα]
      by_cases h : a + σ • castW (Nat.card Kˣ) α ∈ C
      · rw [if_pos h]
        exact hgen _ h
      · rw [if_neg h]
        exact Submodule.zero_mem _
    exact hle hx
  have hM : ∀ g : G, ∀ x ∈ M, ρ g x ∈ M := by
    refine forall_mem_of_rootElt (D := D) (ρ := ρ) ?_
    intro α hα c x hx
    rw [hform α hα c]
    exact Submodule.add_mem _ hx (Submodule.smul_mem _ _ (hME α hα x hx))
  rcases hirr M hM with h | h
  · exfalso
    have hvM : v ∈ M := by
      rw [← T_self σ E a₀ m v]
      exact hgen a₀ ha₀
    rw [h] at hvM
    exact hv0 ((Submodule.mem_bot K).mp hvM)
  · exact h

theorem exists_normalForm [FiniteDimensional K X] (hK : 4 ≤ Nat.card K)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) (hC : IsSmallClass (Nat.card Kˣ) σ C)
    (hform : IsRootForm D ρ E j)
    (hE : ∀ α, IsD4Root α → ∀ a : Fin 4 → ZMod (Nat.card Kˣ),
      ∀ x ∈ D.wtSpace ρ a, E α x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α))
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤) :
    ∃ T : (Fin 4 → ZMod (Nat.card Kˣ)) → X,
      (∀ a ∈ C, T a ≠ 0 ∧ T a ∈ D.wtSpace ρ a) ∧
      Submodule.span K (T '' (C : Set (Fin 4 → ZMod (Nat.card Kˣ)))) = ⊤ ∧
      ∀ a ∈ C, ∀ β, IsD4Root β →
        E β (T a) = if a + σ • castW (Nat.card Kˣ) β ∈ C
          then T (a + σ • castW (Nat.card Kˣ) β) else 0 := by
  have hμ := exists_ne_zero_ne_one_of_four_le_card hK
  obtain ⟨a₀, ha₀, hna⟩ := exists_mem_ne_neg hC
  obtain ⟨m, hm, hm_a, hm_na⟩ : ∃ m ∈ C, m ≠ a₀ ∧ m ≠ -a₀ := by
    have h2 : ({a₀, -a₀} : Finset (Fin 4 → ZMod (Nat.card Kˣ))).card ≤ 2 := by
      have h := Finset.card_insert_le a₀ ({-a₀} : Finset (Fin 4 → ZMod (Nat.card Kˣ)))
      have h1 : ({-a₀} : Finset (Fin 4 → ZMod (Nat.card Kˣ))).card ≤ 1 := by simp
      omega
    have hlt : ({a₀, -a₀} : Finset (Fin 4 → ZMod (Nat.card Kˣ))).card < C.card := by
      rw [hC.card_eq]
      omega
    obtain ⟨m, hmC, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    exact ⟨m, hmC, hnot.1, hnot.2⟩
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff (D.wtSpace ρ a₀)).mp ((hCw a₀).mp ha₀)
  refine ⟨T σ E a₀ m v, ?_, ?_, ?_⟩
  · intro a ha
    exact ⟨T_ne_zero hform hCw hC hE ha₀ hna hm hm_a hm_na hv hv0 ha,
      T_weight hC hE ha₀ hna hm hm_a hm_na hv ha⟩
  · exact span_T_eq_top hform hμ hCw hC hE ha₀ hna hm hm_a hm_na hv hv0 hirr
  · exact fun a ha β hβ =>
      T_root_apply_mem hform hμ hCw hC hE ha₀ hna hm hm_a hm_na hv hv0 ha hβ

private theorem one_le_finrank_wtSpace [FiniteDimensional K X]
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) :
    1 ≤ Module.finrank K (D.wtSpace ρ a) := by
  haveI : Nontrivial (D.wtSpace ρ a) :=
    (Submodule.nontrivial_iff_ne_bot (p := D.wtSpace ρ a)).mpr ((hCw a).mp ha)
  exact Module.finrank_pos

private theorem finrank_le_eight [FiniteDimensional K X] (hC : IsSmallClass (Nat.card Kˣ) σ C)
    {T : (Fin 4 → ZMod (Nat.card Kˣ)) → X}
    (hTtop : Submodule.span K (T '' (C : Set (Fin 4 → ZMod (Nat.card Kˣ)))) = ⊤) :
    Module.finrank K X ≤ 8 := by
  have htop : Submodule.span K ↑(C.image T) = (⊤ : Submodule K X) := by
    rw [Finset.coe_image, hTtop]
  have h1 : (↑(C.image T) : Set X).finrank K ≤ (C.image T).card :=
    finrank_span_finset_le_card (R := K) (M := X) (C.image T)
  rw [Set.finrank, htop, finrank_top] at h1
  calc Module.finrank K X ≤ C.card := h1.trans Finset.card_image_le
    _ = 8 := hC.card_eq

private theorem finrank_eq_sum_wtSpace [FiniteDimensional K X]
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) (hC : IsSmallClass (Nat.card Kˣ) σ C) :
    Module.finrank K X = ∑ a ∈ C, Module.finrank K (D.wtSpace ρ a) := by
  have hf0 : ∀ a ∉ C, Module.finrank K (D.wtSpace ρ a) = 0 := by
    intro a ha
    have hbot : D.wtSpace ρ a = ⊥ := by
      by_contra h
      exact ha ((hCw a).mpr h)
    rw [hbot, finrank_bot]
  rw [finrank_eq_sum_finrank_wtSpace D ρ]
  exact (Finset.sum_subset (Finset.subset_univ C) fun b _ hb => hf0 b hb).symm

private theorem eight_le_finrank [FiniteDimensional K X]
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) (hC : IsSmallClass (Nat.card Kˣ) σ C) :
    8 ≤ Module.finrank K X := by
  rw [finrank_eq_sum_wtSpace hCw hC]
  calc 8 = C.card := hC.card_eq.symm
    _ = ∑ _a ∈ C, 1 := by simp
    _ ≤ ∑ a ∈ C, Module.finrank K (D.wtSpace ρ a) :=
      Finset.sum_le_sum fun a ha => one_le_finrank_wtSpace hCw ha

private theorem finrank_wtSpace_eq_one [FiniteDimensional K X]
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) (hC : IsSmallClass (Nat.card Kˣ) σ C)
    (hfin8 : Module.finrank K X = 8) :
    ∀ a ∈ C, Module.finrank K (D.wtSpace ρ a) = 1 := by
  have hsum := finrank_eq_sum_wtSpace hCw hC
  intro a ha
  by_contra hne
  have h2 : 2 ≤ Module.finrank K (D.wtSpace ρ a) := by
    have := one_le_finrank_wtSpace hCw ha
    omega
  have hsplit : (∑ b ∈ C, Module.finrank K (D.wtSpace ρ b)) =
      Module.finrank K (D.wtSpace ρ a) +
        ∑ b ∈ C.erase a, Module.finrank K (D.wtSpace ρ b) := by
    rw [← Finset.sum_erase_add (s := C) (f := fun b =>
      Module.finrank K (D.wtSpace ρ b)) ha, add_comm]
  have hge7 : (C.erase a).card ≤
      ∑ b ∈ C.erase a, Module.finrank K (D.wtSpace ρ b) := by
    have h1 : ∀ b ∈ C.erase a, 1 ≤ Module.finrank K (D.wtSpace ρ b) :=
      fun b hb => one_le_finrank_wtSpace hCw (Finset.mem_of_mem_erase hb)
    simpa using Finset.sum_le_sum h1
  have hcard : (C.erase a).card = 7 := by
    rw [Finset.card_erase_of_mem ha, hC.card_eq]
  omega

private theorem finrank_eq_eight [FiniteDimensional K X] (hK : 4 ≤ Nat.card K)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) (hC : IsSmallClass (Nat.card Kˣ) σ C)
    (hform : IsRootForm D ρ E j)
    (hE : ∀ α, IsD4Root α → ∀ a : Fin 4 → ZMod (Nat.card Kˣ),
      ∀ x ∈ D.wtSpace ρ a, E α x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α))
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤) :
    Module.finrank K X = 8 ∧ ∀ a ∈ C, Module.finrank K (D.wtSpace ρ a) = 1 := by
  obtain ⟨T, -, hTtop, -⟩ := exists_normalForm hK hCw hC hform hE hirr
  have hle : Module.finrank K X ≤ 8 := finrank_le_eight hC hTtop
  have hge : 8 ≤ Module.finrank K X := eight_le_finrank hCw hC
  have hfin8 : Module.finrank K X = 8 := le_antisymm hle hge
  exact ⟨hfin8, finrank_wtSpace_eq_one hCw hC hfin8⟩

private theorem range_eq_span_pair {T : (Fin 4 → ZMod (Nat.card Kˣ)) → X}
    (hTtop : Submodule.span K (T '' (C : Set (Fin 4 → ZMod (Nat.card Kˣ)))) = ⊤)
    (hTexact : ∀ a ∈ C, ∀ β, IsD4Root β →
      E β (T a) = if a + σ • castW (Nat.card Kˣ) β ∈ C
        then T (a + σ • castW (Nat.card Kˣ) β) else 0)
    {α : Fin 4 → ℤ} (hα : IsD4Root α) {a₁ a₂ : Fin 4 → ZMod (Nat.card Kˣ)}
    (ha₁ : a₁ ∈ C) (ha₂ : a₂ ∈ C)
    (hiff : ∀ a ∈ C, (a + σ • castW (Nat.card Kˣ) α ∈ C ↔ a = a₁ ∨ a = a₂)) :
    LinearMap.range (E α) = Submodule.span K
      ({T (a₁ + σ • castW (Nat.card Kˣ) α), T (a₂ + σ • castW (Nat.card Kˣ) α)} : Set X) := by
  have hb₁ : a₁ + σ • castW (Nat.card Kˣ) α ∈ C := (hiff a₁ ha₁).mpr (Or.inl rfl)
  have hb₂ : a₂ + σ • castW (Nat.card Kˣ) α ∈ C := (hiff a₂ ha₂).mpr (Or.inr rfl)
  have hu : E α (T a₁) = T (a₁ + σ • castW (Nat.card Kˣ) α) := by
    rw [hTexact a₁ ha₁ α hα, if_pos hb₁]
  have hv : E α (T a₂) = T (a₂ + σ • castW (Nat.card Kˣ) α) := by
    rw [hTexact a₂ ha₂ α hα, if_pos hb₂]
  refine le_antisymm ?_ ?_
  · rw [LinearMap.range_eq_map, ← hTtop, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    rw [hTexact a ha α hα]
    by_cases h : a + σ • castW (Nat.card Kˣ) α ∈ C
    · rw [if_pos h]
      rcases (hiff a ha).mp h with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
    · rw [if_neg h]
      exact Submodule.zero_mem _
  · refine Submodule.span_le.mpr ?_
    rintro _ (rfl | rfl)
    · exact ⟨T a₁, hu⟩
    · exact ⟨T a₂, hv⟩

private theorem finrank_range_eq_two [FiniteDimensional K X] (hK : 4 ≤ Nat.card K)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) (hC : IsSmallClass (Nat.card Kˣ) σ C)
    (hform : IsRootForm D ρ E j)
    (hE : ∀ α, IsD4Root α → ∀ a : Fin 4 → ZMod (Nat.card Kˣ),
      ∀ x ∈ D.wtSpace ρ a, E α x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α))
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤) :
    ∀ α, IsD4Root α → Module.finrank K (LinearMap.range (E α)) = 2 := by
  obtain ⟨T, hT0, hTtop, hTexact⟩ := exists_normalForm hK hCw hC hform hE hirr
  intro α hα
  obtain ⟨a₁, ha₁, a₂, ha₂, hne, hiff⟩ := hC.two_mem α hα
  have hb₁ : a₁ + σ • castW (Nat.card Kˣ) α ∈ C := (hiff a₁ ha₁).mpr (Or.inl rfl)
  have hb₂ : a₂ + σ • castW (Nat.card Kˣ) α ∈ C := (hiff a₂ ha₂).mpr (Or.inr rfl)
  rw [range_eq_span_pair (a₁ := a₁) (a₂ := a₂) hTtop hTexact hα ha₁ ha₂ hiff]
  have hbne : a₁ + σ • castW (Nat.card Kˣ) α ≠ a₂ + σ • castW (Nat.card Kˣ) α := by
    intro h
    exact hne (add_right_cancel h)
  have hLI : LinearIndependent K
      ![T (a₁ + σ • castW (Nat.card Kˣ) α), T (a₂ + σ • castW (Nat.card Kˣ) α)] := by
    have hf : Function.Injective
        ![a₁ + σ • castW (Nat.card Kˣ) α, a₂ + σ • castW (Nat.card Kˣ) α] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    refine (iSupIndep_wtSpace D ρ).comp hf |>.linearIndependent _ ?_ ?_
    · intro i
      fin_cases i
      · simpa using (hT0 _ hb₁).2
      · simpa using (hT0 _ hb₂).2
    · intro i
      fin_cases i
      · simpa using (hT0 _ hb₁).1
      · simpa using (hT0 _ hb₂).1
  have hrange2 : ({T (a₁ + σ • castW (Nat.card Kˣ) α),
      T (a₂ + σ • castW (Nat.card Kˣ) α)} : Set X) = Set.range
      ![T (a₁ + σ • castW (Nat.card Kˣ) α), T (a₂ + σ • castW (Nat.card Kˣ) α)] := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
  rw [hrange2, finrank_span_eq_card hLI]
  simp

theorem finrank_eq_eight_and_finrank_range [FiniteDimensional K X] (hK : 4 ≤ Nat.card K)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥) (hC : IsSmallClass (Nat.card Kˣ) σ C)
    (hform : IsRootForm D ρ E j)
    (hE : ∀ α, IsD4Root α → ∀ a : Fin 4 → ZMod (Nat.card Kˣ),
      ∀ x ∈ D.wtSpace ρ a, E α x ∈ D.wtSpace ρ (a + σ • castW (Nat.card Kˣ) α))
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤) :
    Module.finrank K X = 8 ∧ (∀ a ∈ C, Module.finrank K (D.wtSpace ρ a) = 1) ∧
      ∀ α, IsD4Root α → Module.finrank K (LinearMap.range (E α)) = 2 := by
  obtain ⟨h1, h2⟩ := finrank_eq_eight hK hCw hC hform hE hirr
  exact ⟨h1, h2, finrank_range_eq_two hK hCw hC hform hE hirr⟩

theorem linearIndependent_of_mem_wtSpace {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))}
    {b : (Fin 4 → ZMod (Nat.card Kˣ)) → X} (hb : ∀ a ∈ C, b a ≠ 0 ∧ b a ∈ D.wtSpace ρ a) :
    LinearIndependent K (fun a : C => b a) := by
  have hind : iSupIndep (fun a : C => D.wtSpace ρ (a : Fin 4 → ZMod (Nat.card Kˣ))) :=
    (iSupIndep_wtSpace D ρ).comp (f := fun a : C => (a : Fin 4 → ZMod (Nat.card Kˣ)))
      (fun a b h => Subtype.ext h)
  exact hind.linearIndependent _ (fun a => (hb a a.2).2) (fun a => (hb a a.2).1)

end CFSG.LieType.D4Small.D4Datum
