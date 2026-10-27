module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSmallFactsA6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltC5
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixAutCert

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Quasithin.SteinbergCB CFSG.LocalAnalysis.ComponentInitial

theorem fourEmb6_apply (i : Fin 4) : fourEmb (by decide : 4 ≤ 6) i = ⟨i, by omega⟩ := Fin.ext rfl

theorem viaEmbeddingHom_kOf_six : ∀ i : Fin 4,
    (viaEmbeddingHom (fourEmb (by decide : 4 ≤ 6)) (kOf i) : Perm (Fin 6)) =
      ![1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2] i := by
  intro i
  fin_cases i
  · exact map_one _
  · change viaEmbeddingHom _ (swap 0 1 * swap 2 3) = _
    rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
    rfl
  · change viaEmbeddingHom _ (swap 0 2 * swap 1 3) = _
    rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
    rfl
  · change viaEmbeddingHom _ (swap 0 1 * swap 2 3 * (swap 0 2 * swap 1 3)) = _
    rw [map_mul, map_mul, map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap,
      viaEmbeddingHom_swap, viaEmbeddingHom_swap]
    show swap (0 : Fin 6) 1 * swap 2 3 * (swap 0 2 * swap 1 3) = swap 0 3 * swap 1 2
    decide

theorem mem_rootVP_six_iff {x : Perm (Fin 6)} : x ∈ rootVP 6 ↔ x = 1 ∨ InV0 x := by
  rw [rootVP_eq (by decide : 4 ≤ 6)]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨i, rfl⟩ := exists_kOf_of_mem_kleinFour hk
    rw [viaEmbeddingHom_kOf_six]
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨kOf 0, kOf_mem 0, by rw [viaEmbeddingHom_kOf_six]; rfl⟩
    · exact ⟨kOf 1, kOf_mem 1, by rw [viaEmbeddingHom_kOf_six]; rfl⟩
    · exact ⟨kOf 2, kOf_mem 2, by rw [viaEmbeddingHom_kOf_six]; rfl⟩
    · exact ⟨kOf 3, kOf_mem 3, by rw [viaEmbeddingHom_kOf_six]; rfl⟩

theorem coe_a6c012 : ((a6c012 : alternatingGroup (Fin 6)) : Perm (Fin 6)) = sixC012 := rfl

theorem inV0_iff {x : Perm (Fin 6)} : InV0 x ↔ x ∈ v0List := by
  simp [InV0, v0List]

theorem inVexo_iff {x : Perm (Fin 6)} : InVexo x ↔ x ∈ vexoList := by
  simp [InVexo, vexoList]

theorem a6c013_eq : ((a6c013 : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
    swap 0 3 * swap 1 2 * ((a6c012 : Perm (Fin 6)) * (a6c012 : Perm (Fin 6))) := by
  decide

theorem commute_swap45_of_fix {x : Perm (Fin 6)} (h4 : x 4 = 4) (h5 : x 5 = 5) :
    x * swap 4 5 = swap 4 5 * x := by
  apply Equiv.ext
  intro i
  simp only [Perm.mul_apply]
  by_cases hi4 : i = 4
  · subst hi4
    rw [swap_apply_left, h5, h4, swap_apply_left]
  · by_cases hi5 : i = 5
    · subst hi5
      rw [swap_apply_right, h4, h5, swap_apply_right]
    · rw [swap_apply_of_ne_of_ne hi4 hi5, swap_apply_of_ne_of_ne]
      · intro h
        apply hi4
        exact x.injective (h.trans h4.symm)
      · intro h
        apply hi5
        exact x.injective (h.trans h5.symm)

theorem apply_four_five_of_mem_rootAlt {x : alternatingGroup (Fin 6)} (hx : x ∈ rootAlt 6) :
    (x : Perm (Fin 6)) 4 = 4 ∧ (x : Perm (Fin 6)) 5 = 5 := by
  obtain ⟨k, -, hk⟩ := (mem_rootAlt_iff (by decide) x).mp hx
  rw [← hk]
  have h4 : (4 : Fin 6) ∉ Set.range (fourEmb (by decide : 4 ≤ 6)) := by
    rintro ⟨j, hj⟩
    have := congrArg (fun y : Fin 6 => (y : ℕ)) hj
    simp only [fourEmb_apply] at this
    have := j.2
    simp at this
    omega
  have h5 : (5 : Fin 6) ∉ Set.range (fourEmb (by decide : 4 ≤ 6)) := by
    rintro ⟨j, hj⟩
    have := congrArg (fun y : Fin 6 => (y : ℕ)) hj
    simp only [fourEmb_apply] at this
    have := j.2
    simp at this
    omega
  exact ⟨viaEmbeddingHom_apply_of_notMem _ _ h4, viaEmbeddingHom_apply_of_notMem _ _ h5⟩

theorem a6c012_mem_rootAlt : a6c012 ∈ rootAlt 6 := by
  rw [mem_rootAlt_iff (by decide)]
  refine ⟨swap 0 1 * swap 1 2, mem_alternatingGroup.mpr (by decide), ?_⟩
  rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
  rfl

@[expose] def a6d1 : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 2 3, mem_alternatingGroup.mpr (by decide)⟩

@[expose] def a6d2 : alternatingGroup (Fin 6) :=
  ⟨swap 0 2 * swap 1 3, mem_alternatingGroup.mpr (by decide)⟩

theorem inV0_a6d1 : InV0 (a6d1 : Perm (Fin 6)) := Or.inl rfl

theorem inV0_a6d2 : InV0 (a6d2 : Perm (Fin 6)) := Or.inr (Or.inl rfl)

theorem a6d1_ne_a6d2 : (a6d1 : Perm (Fin 6)) ≠ a6d2 := by decide

theorem sixAut_facts :
    (∀ a : Perm (Fin 6), InvGood a) ∧
    (∀ u ∈ v0List, ∀ v ∈ v0List, u ≠ v → u * v ∈ v0List) ∧
    (∀ x₁ ∈ v0List, ∀ x₂ ∈ v0List, x₁ ≠ x₂ → ∀ e ∈ v0List, e = x₁ ∨ e = x₂ ∨ e = x₁ * x₂) ∧
    (∀ x₁ ∈ vexoList, ∀ x₂ ∈ vexoList, x₁ ≠ x₂ → ∀ e ∈ vexoList,
      e = x₁ ∨ e = x₂ ∨ e = x₁ * x₂) ∧
    (∀ x ∈ v0List, ∀ y ∈ v0List, x * y = y * x) ∧
    (∀ u ∈ v0List, u * u = 1) ∧
    (∀ u ∈ v0List, u ≠ 1) ∧
    (∀ u ∈ v0List, sign u = 1) ∧
    (∀ u ∈ vexoList, sign u = 1) ∧
    (∀ u ∈ v0List, sixC012 * u * sixC012⁻¹ ∈ v0List) ∧
    (∀ y : Perm (Fin 6), ActsAsC y) ∧
    (∀ y : Perm (Fin 6), NormThree y) ∧
    (∀ y : Perm (Fin 6), SqFour y) ∧
    (∀ u ∈ v0List, ∃ w ∈ v0RootList, w * w = u ∧ w * swap 4 5 = swap 4 5 * w ∧ sign w = 1) ∧
    (∀ b : Perm (Fin 6), CentSix b) := by
  have h := sixAut_check
  simp only [sixAutCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

theorem four6_check : ∀ a : Perm (Fin 6), InvGood a := sixAut_facts.1

theorem v0List_mul_check : ∀ u ∈ v0List, ∀ v ∈ v0List, u ≠ v → u * v ∈ v0List :=
  sixAut_facts.2.1

theorem v0List_cover_check : ∀ x₁ ∈ v0List, ∀ x₂ ∈ v0List, x₁ ≠ x₂ → ∀ e ∈ v0List,
    e = x₁ ∨ e = x₂ ∨ e = x₁ * x₂ :=
  sixAut_facts.2.2.1

theorem vexoList_cover_check : ∀ x₁ ∈ vexoList, ∀ x₂ ∈ vexoList, x₁ ≠ x₂ → ∀ e ∈ vexoList,
    e = x₁ ∨ e = x₂ ∨ e = x₁ * x₂ :=
  sixAut_facts.2.2.2.1

theorem v0List_comm : ∀ x ∈ v0List, ∀ y ∈ v0List, x * y = y * x := sixAut_facts.2.2.2.2.1

theorem v0List_mul_self_check : ∀ u ∈ v0List, u * u = 1 := sixAut_facts.2.2.2.2.2.1

theorem v0List_ne_one_check : ∀ u ∈ v0List, u ≠ 1 := sixAut_facts.2.2.2.2.2.2.1

theorem v0List_sign_check : ∀ u ∈ v0List, sign u = 1 := sixAut_facts.2.2.2.2.2.2.2.1

theorem v0List_conj_check : ∀ u ∈ v0List, sixC012 * u * sixC012⁻¹ ∈ v0List :=
  sixAut_facts.2.2.2.2.2.2.2.2.2.1

theorem actsAsC_check : ∀ y : Perm (Fin 6), ActsAsC y := sixAut_facts.2.2.2.2.2.2.2.2.2.2.1

theorem normThree_check : ∀ y : Perm (Fin 6), NormThree y :=
  sixAut_facts.2.2.2.2.2.2.2.2.2.2.2.1

theorem sqFour_check : ∀ y : Perm (Fin 6), SqFour y := sixAut_facts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem exists_sq_of_mem_v0List : ∀ u ∈ v0List, ∃ w ∈ v0RootList,
    w * w = u ∧ w * swap 4 5 = swap 4 5 * w ∧ sign w = 1 :=
  sixAut_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem inV0_mul {u v : Perm (Fin 6)} (hu : InV0 u) (hv : InV0 v) (huv : u ≠ v) : InV0 (u * v) := by
  rw [inV0_iff] at hu hv ⊢
  exact v0List_mul_check u hu v hv huv

theorem inV0_cover {x₁ x₂ : Perm (Fin 6)} (h₁ : InV0 x₁) (h₂ : InV0 x₂) (h12 : x₁ ≠ x₂)
    {e : Perm (Fin 6)} (he : InV0 e) : e = x₁ ∨ e = x₂ ∨ e = x₁ * x₂ := by
  rw [inV0_iff] at h₁ h₂ he
  exact v0List_cover_check x₁ h₁ x₂ h₂ h12 e he

theorem inVexo_cover {x₁ x₂ : Perm (Fin 6)} (h₁ : InVexo x₁) (h₂ : InVexo x₂) (h12 : x₁ ≠ x₂)
    {e : Perm (Fin 6)} (he : InVexo e) : e = x₁ ∨ e = x₂ ∨ e = x₁ * x₂ := by
  rw [inVexo_iff] at h₁ h₂ he
  exact vexoList_cover_check x₁ h₁ x₂ h₂ h12 e he

theorem inV0_mul_self {u : Perm (Fin 6)} (hu : InV0 u) : u * u = 1 :=
  v0List_mul_self_check u (inV0_iff.mp hu)

theorem inV0_ne_one {u : Perm (Fin 6)} (hu : InV0 u) : u ≠ 1 :=
  v0List_ne_one_check u (inV0_iff.mp hu)

theorem inV0_sign {u : Perm (Fin 6)} (hu : InV0 u) : sign u = 1 :=
  v0List_sign_check u (inV0_iff.mp hu)

theorem inV0_conj_c012 {u : Perm (Fin 6)} (hu : InV0 u) :
    InV0 ((a6c012 : Perm (Fin 6)) * u * (a6c012 : Perm (Fin 6))⁻¹) := by
  rw [inV0_iff] at hu ⊢
  rw [coe_a6c012]
  exact v0List_conj_check u hu

theorem forall_inV0_of_map {α : MulAut (alternatingGroup (Fin 6))}
    (h1 : InV0 (α a6d1 : Perm (Fin 6))) (h2 : InV0 (α a6d2 : Perm (Fin 6))) :
    ∀ u : alternatingGroup (Fin 6), InV0 (u : Perm (Fin 6)) →
      ∃ w : alternatingGroup (Fin 6), InV0 (w : Perm (Fin 6)) ∧ α w = u := by
  intro u hu
  have hne : (α a6d1 : Perm (Fin 6)) ≠ α a6d2 := fun h =>
    a6d1_ne_a6d2 (congrArg Subtype.val (α.injective (Subtype.ext h)))
  rcases inV0_cover h1 h2 hne hu with h | h | h
  · exact ⟨a6d1, inV0_a6d1, Subtype.ext h.symm⟩
  · exact ⟨a6d2, inV0_a6d2, Subtype.ext h.symm⟩
  · refine ⟨a6d1 * a6d2, inV0_mul inV0_a6d1 inV0_a6d2 a6d1_ne_a6d2, Subtype.ext ?_⟩
    rw [map_mul]
    exact h.symm

theorem mem_range_conj_of_normalizes_rootFour (α : MulAut (alternatingGroup (Fin 6)))
    (hα : ∀ u : alternatingGroup (Fin 6), InV0 (u : Perm (Fin 6)) → InV0 (α u : Perm (Fin 6))) :
    ∃ σ : Perm (Fin 6), ∀ x : alternatingGroup (Fin 6),
      ((α x : alternatingGroup (Fin 6)) : Perm (Fin 6)) = σ * x * σ⁻¹ := by
  have honto := forall_inV0_of_map (hα _ inV0_a6d1) (hα _ inV0_a6d2)
  set c : Perm (Fin 6) := ((α a6c012 : alternatingGroup (Fin 6)) : Perm (Fin 6)) with hcdef
  have hnorm : ∀ u ∈ v0List, c * u * c⁻¹ ∈ v0List := by
    intro u hu
    have hu' : InV0 u := inV0_iff.mpr hu
    have huA : u ∈ alternatingGroup (Fin 6) := mem_alternatingGroup.mpr (inV0_sign hu')
    obtain ⟨w, hw, hwu⟩ := honto ⟨u, huA⟩ hu'
    have hcw : InV0 ((a6c012 * w * a6c012⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6)) :=
      inV0_conj_c012 hw
    have := hα _ hcw
    rw [map_mul, map_mul, map_inv, hwu] at this
    exact inV0_iff.mp this
  have h3 : c * c * c = 1 := by
    rw [hcdef, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
      show a6c012 * a6c012 * a6c012 = 1 by decide, map_one]
    rfl
  have h1 : c ≠ 1 := fun h => by
    have : α a6c012 = α 1 := Subtype.ext (by rw [← hcdef, h, map_one]; rfl)
    exact absurd (α.injective this) (by decide)
  have hsupp := normThree_check _ hnorm h3 h1 (mem_alternatingGroup.mp (α a6c012).2)
  exact exists_perm_of_isThreeCycle α (card_support_eq_three_iff.mp hsupp)

theorem exists_mulAut_vexo : ∃ φ : MulAut (alternatingGroup (Fin 6)),
    ∀ x : alternatingGroup (Fin 6), InVexo (x : Perm (Fin 6)) → InV0 (φ x : Perm (Fin 6)) := by
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : MulAut (alternatingGroup (Fin 6)), φ₀ ∉ (conjPerm 6).range := by
    by_contra h
    push Not at h
    have htop : (conjPerm 6).range = ⊤ := eq_top_iff.mpr fun φ _ => h φ
    have h1 := Subgroup.card_range_dvd (conjPerm 6)
    rw [htop, Subgroup.card_top, CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6,
      Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    exact absurd h1 (by decide)
  set a' := φ₀.symm a6d1
  set b' := φ₀.symm a6d2
  have ha2 : (a' : Perm (Fin 6)) * a' = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, show a6d1 * a6d1 = 1 by decide, map_one]; rfl
  have hb2 : (b' : Perm (Fin 6)) * b' = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, show a6d2 * a6d2 = 1 by decide, map_one]; rfl
  have ha1 : (a' : Perm (Fin 6)) ≠ 1 := fun h => by
    have : φ₀.symm a6d1 = φ₀.symm 1 := Subtype.ext (by rw [h, map_one]; rfl)
    exact absurd (φ₀.symm.injective this) (by decide)
  have hb1 : (b' : Perm (Fin 6)) ≠ 1 := fun h => by
    have : φ₀.symm a6d2 = φ₀.symm 1 := Subtype.ext (by rw [h, map_one]; rfl)
    exact absurd (φ₀.symm.injective this) (by decide)
  have hba : (b' : Perm (Fin 6)) ≠ a' := fun h =>
    a6d1_ne_a6d2 (congrArg Subtype.val (φ₀.symm.injective (Subtype.ext h))).symm
  have hab : (a' : Perm (Fin 6)) * b' = b' * a' := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
      show a6d1 * a6d2 = a6d2 * a6d1 by decide]
  obtain ⟨σ, -, hσ⟩ := four6_check _ ha2 ha1 (mem_alternatingGroup.mp a'.2) _ hb2 hb1 hba hab
    (mem_alternatingGroup.mp b'.2)
  set ψ := φ₀.symm.trans (conjPerm 6 σ) with hψ
  have hψa : (ψ a6d1 : Perm (Fin 6)) = σ * a' * σ⁻¹ := by
    rw [hψ, MulEquiv.trans_apply, conjPerm_apply]
  have hψb : (ψ a6d2 : Perm (Fin 6)) = σ * b' * σ⁻¹ := by
    rw [hψ, MulEquiv.trans_apply, conjPerm_apply]
  rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    exfalso
    rw [← hψa] at h1
    rw [← hψb] at h2
    obtain ⟨τ, hτ⟩ := mem_range_conj_of_normalizes_rootFour ψ (fun u hu => by
      rcases inV0_cover inV0_a6d1 inV0_a6d2 a6d1_ne_a6d2 hu with h | h | h
      · rw [show u = a6d1 from Subtype.ext h]; exact h1
      · rw [show u = a6d2 from Subtype.ext h]; exact h2
      · rw [show u = a6d1 * a6d2 from Subtype.ext h, map_mul]
        have hne : (ψ a6d1 : Perm (Fin 6)) ≠ ψ a6d2 := fun he =>
          a6d1_ne_a6d2 (congrArg Subtype.val (ψ.injective (Subtype.ext he)))
        exact inV0_mul h1 h2 hne)
    apply hφ₀
    refine ⟨τ⁻¹ * σ, MulEquiv.ext fun x => Subtype.ext ?_⟩
    have hx := hτ (φ₀ x)
    rw [hψ, MulEquiv.trans_apply, conjPerm_apply, MulEquiv.symm_apply_apply] at hx
    rw [conjPerm_apply]
    calc (τ⁻¹ * σ) * (x : Perm (Fin 6)) * (τ⁻¹ * σ)⁻¹
        = τ⁻¹ * (σ * x * σ⁻¹) * τ := by group
      _ = τ⁻¹ * (τ * (φ₀ x : Perm (Fin 6)) * τ⁻¹) * τ := by rw [hx]
      _ = (φ₀ x : Perm (Fin 6)) := by group
  ·
    rw [← hψa] at h1
    rw [← hψb] at h2
    refine ⟨ψ.symm, fun x hx => ?_⟩
    have hne : (ψ a6d1 : Perm (Fin 6)) ≠ ψ a6d2 := fun he =>
      a6d1_ne_a6d2 (congrArg Subtype.val (ψ.injective (Subtype.ext he)))
    rcases inVexo_cover h1 h2 hne hx with h | h | h
    · rw [show x = ψ a6d1 from Subtype.ext h, MulEquiv.symm_apply_apply]; exact inV0_a6d1
    · rw [show x = ψ a6d2 from Subtype.ext h, MulEquiv.symm_apply_apply]; exact inV0_a6d2
    · rw [show x = ψ (a6d1 * a6d2) from Subtype.ext (by rw [map_mul]; exact h),
        MulEquiv.symm_apply_apply]
      exact inV0_mul inV0_a6d1 inV0_a6d2 a6d1_ne_a6d2

theorem exists_mulAut_pair {a b : alternatingGroup (Fin 6)} (ha2 : a * a = 1) (hb2 : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hcomm : a * b = b * a) :
    ∃ φ : MulAut (alternatingGroup (Fin 6)),
      InV0 (φ a : Perm (Fin 6)) ∧ InV0 (φ b : Perm (Fin 6)) := by
  have ha1' : (a : Perm (Fin 6)) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hb1' : (b : Perm (Fin 6)) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hba' : (b : Perm (Fin 6)) ≠ a := fun h => hab (Subtype.ext h).symm
  have ha2' : (a : Perm (Fin 6)) * a = 1 := congrArg Subtype.val ha2
  have hb2' : (b : Perm (Fin 6)) * b = 1 := congrArg Subtype.val hb2
  have hab' : (a : Perm (Fin 6)) * b = b * a := congrArg Subtype.val hcomm
  obtain ⟨σ, -, hσ⟩ := four6_check _ ha2' ha1' (mem_alternatingGroup.mp a.2) _ hb2' hb1' hba' hab'
    (mem_alternatingGroup.mp b.2)
  rcases hσ with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
  · refine ⟨conjPerm 6 σ, ?_, ?_⟩
    · rw [conjPerm_apply]; exact h1
    · rw [conjPerm_apply]; exact h2'
  · obtain ⟨φe, hφe⟩ := exists_mulAut_vexo
    refine ⟨(conjPerm 6 σ).trans φe, ?_, ?_⟩
    · rw [MulEquiv.trans_apply]
      exact hφe _ (by rw [conjPerm_apply]; exact h1)
    · rw [MulEquiv.trans_apply]
      exact hφe _ (by rw [conjPerm_apply]; exact h2')

theorem exists_conj_of_fix_rootV (α : MulAut (alternatingGroup (Fin 6)))
    (hα : ∀ u : alternatingGroup (Fin 6), InV0 (u : Perm (Fin 6)) → α u = u) :
    ∃ v ∈ (1 : Perm (Fin 6)) :: v0List, ∀ x ∈ rootAlt 6,
      ((α x : alternatingGroup (Fin 6)) : Perm (Fin 6)) = v * x * v⁻¹ := by
  have hact : ∀ u ∈ v0List, (α a6c012 : Perm (Fin 6)) * u * (α a6c012 : Perm (Fin 6))⁻¹ =
      (a6c012 : Perm (Fin 6)) * u * (a6c012 : Perm (Fin 6))⁻¹ := by
    intro u hu
    have hu' : InV0 u := inV0_iff.mpr hu
    have huA : u ∈ alternatingGroup (Fin 6) := mem_alternatingGroup.mpr (inV0_sign hu')
    have h1 := hα (a6c012 * ⟨u, huA⟩ * a6c012⁻¹) (inV0_conj_c012 hu')
    rw [map_mul, map_mul, map_inv, hα ⟨u, huA⟩ hu'] at h1
    exact congrArg Subtype.val h1
  obtain ⟨v, hv, hve⟩ := actsAsC_check _ (mem_alternatingGroup.mp (α a6c012).2) hact
  rw [← coe_a6c012] at hve
  refine ⟨v, hv, ?_⟩
  have hvA : v ∈ alternatingGroup (Fin 6) := by
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact one_mem _
    · exact mem_alternatingGroup.mpr (inV0_sign (inV0_iff.mpr hv'))
  set α' := α.trans (conjPerm 6 v⁻¹) with hα'
  have hα'v : ∀ x, ((α' x : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      v⁻¹ * (α x : Perm (Fin 6)) * v := fun x => by
    rw [hα', MulEquiv.trans_apply, conjPerm_apply, inv_inv]
  have hfixV : ∀ u : alternatingGroup (Fin 6), InV0 (u : Perm (Fin 6)) → α' u = u := by
    intro u hu
    apply Subtype.ext
    rw [hα'v, hα u hu]
    rcases List.mem_cons.mp hv with rfl | hv'
    · group
    · have hv0 : InV0 v := inV0_iff.mpr hv'
      have hc : v * u = u * v := v0List_comm v hv' u (inV0_iff.mp hu)
      calc v⁻¹ * (u : Perm (Fin 6)) * v = v⁻¹ * (v * u) := by rw [hc, mul_assoc]
        _ = u := by group
  have hc1 : α' a6c012 = a6c012 := by
    apply Subtype.ext
    rw [hα'v, hve]
    group
  have hc2 : α' a6c013 = a6c013 := by
    have hd3 : InV0 (swap 0 3 * swap 1 2 : Perm (Fin 6)) := Or.inr (Or.inr rfl)
    have hd3A : (swap 0 3 * swap 1 2 : Perm (Fin 6)) ∈ alternatingGroup (Fin 6) :=
      mem_alternatingGroup.mpr (inV0_sign hd3)
    have he : a6c013 = ⟨_, hd3A⟩ * (a6c012 * a6c012) := Subtype.ext a6c013_eq
    rw [he, map_mul, map_mul, hfixV _ hd3, hc1]
  have hfix : ∀ x ∈ rootAlt 6, α' x = x := by
    intro x hx
    rcases eq_one_or_eq_conj45 hc1 hc2 with h | h
    · rw [h]; rfl
    · rw [h]
      apply Subtype.ext
      rw [conjPerm_apply]
      obtain ⟨h4, h5⟩ := apply_four_five_of_mem_rootAlt hx
      calc (swap (4 : Fin 6) 5 : Perm (Fin 6)) * (x : Perm (Fin 6)) * (swap (4 : Fin 6) 5)⁻¹
          = ((x : Perm (Fin 6)) * swap 4 5) * (swap (4 : Fin 6) 5)⁻¹ := by
            rw [commute_swap45_of_fix h4 h5]
        _ = x := by group
  intro x hx
  have h1 := congrArg Subtype.val (hfix x hx)
  rw [hα'v] at h1
  calc ((α x : alternatingGroup (Fin 6)) : Perm (Fin 6))
        = v * (v⁻¹ * (α x : Perm (Fin 6)) * v) * v⁻¹ := by group
    _ = v * x * v⁻¹ := by rw [h1]

theorem inV0_of_commute_swap45 (α : MulAut (alternatingGroup (Fin 6)))
    (hα : ∀ x, α (conjPerm 6 (swap 4 5) x) = conjPerm 6 (swap 4 5) (α x))
    (u : alternatingGroup (Fin 6)) (hu : InV0 (u : Perm (Fin 6))) :
    InV0 (α u : Perm (Fin 6)) := by
  obtain ⟨w, -, hwu, hw45, hws⟩ := exists_sq_of_mem_v0List _ (inV0_iff.mp hu)
  set w' : alternatingGroup (Fin 6) := ⟨w, mem_alternatingGroup.mpr hws⟩ with hw'
  have hu' : u = w' * w' := Subtype.ext hwu.symm
  have hcw : conjPerm 6 (swap 4 5) w' = w' := by
    apply Subtype.ext
    rw [conjPerm_apply]
    change swap (4 : Fin 6) 5 * w * (swap (4 : Fin 6) 5)⁻¹ = w
    rw [← hw45]
    group
  set c : Perm (Fin 6) := ((α w' : alternatingGroup (Fin 6)) : Perm (Fin 6)) with hcdef
  have hcomm : c * swap 4 5 = swap 4 5 * c := by
    have h := congrArg Subtype.val (hα w')
    rw [hcw, conjPerm_apply] at h
    calc c * swap 4 5 = (swap (4 : Fin 6) 5 * c * (swap (4 : Fin 6) 5)⁻¹) * swap 4 5 := by
          rw [hcdef, ← h]
      _ = swap 4 5 * c := by group
  have hsq : ((α u : alternatingGroup (Fin 6)) : Perm (Fin 6)) = c * c := by
    rw [hu', map_mul]
    rfl
  have h1 : c * c ≠ 1 := by
    rw [← hsq]
    intro h
    apply inV0_ne_one hu
    have : α u = α 1 := Subtype.ext (by rw [h, map_one]; rfl)
    rw [α.injective this]
    rfl
  have h4 : c * c * (c * c) = 1 := by
    rw [← hsq, ← Subgroup.coe_mul, ← map_mul,
      show u * u = 1 from Subtype.ext (inV0_mul_self hu), map_one]
    rfl
  rw [hsq]
  exact sqFour_check c hcomm (mem_alternatingGroup.mp (α w').2) h1 h4

theorem exists_perm_of_commute_swap45 (α : MulAut (alternatingGroup (Fin 6)))
    (hα : ∀ x, α (conjPerm 6 (swap 4 5) x) = conjPerm 6 (swap 4 5) (α x)) :
    ∃ σ : Perm (Fin 6), σ * swap 4 5 = swap 4 5 * σ ∧ ∀ x : alternatingGroup (Fin 6),
      ((α x : alternatingGroup (Fin 6)) : Perm (Fin 6)) = σ * x * σ⁻¹ := by
  obtain ⟨σ, hσ⟩ := mem_range_conj_of_normalizes_rootFour α (inV0_of_commute_swap45 α hα)
  refine ⟨σ, ?_, hσ⟩
  have hw : ((swap (4 : Fin 6) 5 * σ)⁻¹ * (σ * swap 4 5) : Perm (Fin 6)) = 1 := by
    refine AlternatingFourGroup.eq_one_of_forall_commute_alternating (by simp)
      fun (g : Perm (Fin 6)) hg => ?_
    have h := congrArg Subtype.val (hα ⟨g, hg⟩)
    rw [conjPerm_apply, hσ, hσ, conjPerm_apply] at h
    have e : (σ * swap 4 5) * g * (σ * swap 4 5)⁻¹ = (swap 4 5 * σ) * g * (swap 4 5 * σ)⁻¹ := by
      calc (σ * swap 4 5) * g * (σ * swap 4 5)⁻¹ = σ * (swap 4 5 * g * (swap 4 5)⁻¹) * σ⁻¹ := by
            group
        _ = swap 4 5 * (σ * g * σ⁻¹) * (swap 4 5)⁻¹ := h
        _ = (swap 4 5 * σ) * g * (swap 4 5 * σ)⁻¹ := by group
    calc (swap 4 5 * σ)⁻¹ * (σ * swap 4 5) * g
        = (swap 4 5 * σ)⁻¹ * ((σ * swap 4 5) * g * (σ * swap 4 5)⁻¹) * (σ * swap 4 5) := by group
      _ = (swap 4 5 * σ)⁻¹ * ((swap 4 5 * σ) * g * (swap 4 5 * σ)⁻¹) * (σ * swap 4 5) := by
          rw [e]
      _ = g * ((swap 4 5 * σ)⁻¹ * (σ * swap 4 5)) := by group
  calc σ * swap 4 5 = (swap 4 5 * σ) * ((swap 4 5 * σ)⁻¹ * (σ * swap 4 5)) := by group
    _ = swap 4 5 * σ := by rw [hw, mul_one]

end CFSG.ComponentClassification.RankTwoAlt
