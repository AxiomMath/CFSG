module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.M12Model

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type*} [Group G] {x₁ x₂ lam tau : G}

private instance instDecEqM12Mod : DecidableEq M12Mod
  | ⟨a1, b1, i1, j1⟩, ⟨a2, b2, i2, j2⟩ =>
    if h1 : a1 = a2 then
      if h2 : b1 = b2 then
        if h3 : i1 = i2 then
          if h4 : j1 = j2 then
            isTrue (by subst h1; subst h2; subst h3; subst h4; rfl)
          else isFalse (fun h => h4 (congrArg M12Mod.j h))
        else isFalse (fun h => h3 (congrArg M12Mod.i h))
      else isFalse (fun h => h2 (congrArg M12Mod.b h))
    else isFalse (fun h => h1 (congrArg M12Mod.a h))

private theorem base_mul_closed :
    ∀ (a b : Fin 4) (i j : Fin 2) (c d : Fin 4) (k l : Fin 2),
      i = 0 → j = 0 → k = 0 → l = 0 →
        ((⟨a, b, i, j⟩ : M12Mod) * ⟨c, d, k, l⟩).i = 0 ∧
          ((⟨a, b, i, j⟩ : M12Mod) * ⟨c, d, k, l⟩).j = 0 := by
  decide +kernel

private theorem base_inv_closed :
    ∀ (a b : Fin 4) (i j : Fin 2), i = 0 → j = 0 →
      ((⟨a, b, i, j⟩ : M12Mod)⁻¹).i = 0 ∧ ((⟨a, b, i, j⟩ : M12Mod)⁻¹).j = 0 := by
  decide +kernel

private def baseSub : Subgroup M12Mod where
  carrier := {m | m.i = 0 ∧ m.j = 0}
  mul_mem' := by
    rintro ⟨a, b, i, j⟩ ⟨c, d, k, l⟩ ⟨hi, hj⟩ ⟨hk, hl⟩
    exact base_mul_closed a b i j c d k l hi hj hk hl
  one_mem' := by decide +kernel
  inv_mem' := by
    rintro ⟨a, b, i, j⟩ ⟨hi, hj⟩
    exact base_inv_closed a b i j hi hj

private theorem mx₁_mem_baseSub : M12Mod.mx₁ ∈ baseSub := by
  show M12Mod.mx₁.i = 0 ∧ M12Mod.mx₁.j = 0
  exact ⟨rfl, rfl⟩

private theorem mx₂_mem_baseSub : M12Mod.mx₂ ∈ baseSub := by
  show M12Mod.mx₂.i = 0 ∧ M12Mod.mx₂.j = 0
  exact ⟨rfl, rfl⟩

private theorem baseGrp_model_eq :
    baseGrp M12Mod.mx₁ M12Mod.mx₂ = baseSub := by
  refine le_antisymm ?_ ?_
  · rw [baseGrp, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact mx₁_mem_baseSub
    · exact mx₂_mem_baseSub
  · intro m hm
    rw [baseGrp, M12Mod.eq_pow_mul m]
    have hmlam : M12Mod.mlam ^ m.i.val = 1 := by rw [hm.1]; simp
    have hmtau : M12Mod.mtau ^ m.j.val = 1 := by rw [hm.2]; simp
    rw [hmlam, hmtau, mul_one, mul_one]
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) m.a.val)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) m.b.val)

private theorem mem_base_model (m : M12Mod) :
    m ∈ baseGrp M12Mod.mx₁ M12Mod.mx₂ ↔ m.i = 0 ∧ m.j = 0 := by
  rw [baseGrp_model_eq]
  rfl

private theorem four_mul_closed :
    ∀ (a b : Fin 4) (i j : Fin 2) (c d : Fin 4) (k l : Fin 2),
      i = 0 → j = 0 → Even a.val → Even b.val → k = 0 → l = 0 →
        Even c.val → Even d.val →
        ((⟨a, b, i, j⟩ : M12Mod) * ⟨c, d, k, l⟩).i = 0 ∧
          ((⟨a, b, i, j⟩ : M12Mod) * ⟨c, d, k, l⟩).j = 0 ∧
          Even (((⟨a, b, i, j⟩ : M12Mod) * ⟨c, d, k, l⟩).a).val ∧
          Even (((⟨a, b, i, j⟩ : M12Mod) * ⟨c, d, k, l⟩).b).val := by
  decide +kernel

private theorem four_inv_closed :
    ∀ (a b : Fin 4) (i j : Fin 2), i = 0 → j = 0 → Even a.val → Even b.val →
      ((⟨a, b, i, j⟩ : M12Mod)⁻¹).i = 0 ∧ ((⟨a, b, i, j⟩ : M12Mod)⁻¹).j = 0 ∧
        Even (((⟨a, b, i, j⟩ : M12Mod)⁻¹).a).val ∧
        Even (((⟨a, b, i, j⟩ : M12Mod)⁻¹).b).val := by
  decide +kernel

private def fourSub : Subgroup M12Mod where
  carrier := {m | m.i = 0 ∧ m.j = 0 ∧ Even m.a.val ∧ Even m.b.val}
  mul_mem' := by
    rintro ⟨a, b, i, j⟩ ⟨c, d, k, l⟩ ⟨hi, hj, ha, hb⟩ ⟨hk, hl, hc, hd⟩
    exact four_mul_closed a b i j c d k l hi hj ha hb hk hl hc hd
  one_mem' := by decide +kernel
  inv_mem' := by
    rintro ⟨a, b, i, j⟩ ⟨hi, hj, ha, hb⟩
    exact four_inv_closed a b i j hi hj ha hb

private theorem map_baseGrp (φ : M12Mod →* G) (h1 : φ M12Mod.mx₁ = x₁)
    (h2 : φ M12Mod.mx₂ = x₂) :
    (baseGrp M12Mod.mx₁ M12Mod.mx₂).map φ = baseGrp x₁ x₂ := by
  rw [baseGrp, baseGrp, MonoidHom.map_closure]
  congr 1
  rw [Set.image_pair, h1, h2]

private theorem mem_baseGrp_iff (φ : M12Mod →* G) (h1 : φ M12Mod.mx₁ = x₁)
    (h2 : φ M12Mod.mx₂ = x₂) (w : G) :
    w ∈ baseGrp x₁ x₂ ↔ ∃ a b : Fin 4, φ (⟨a, b, 0, 0⟩ : M12Mod) = w := by
  rw [← map_baseGrp φ h1 h2, Subgroup.mem_map]
  constructor
  · rintro ⟨m, hm, hmw⟩
    rw [mem_base_model] at hm
    obtain ⟨a, b, i, j⟩ := m
    have h : (⟨a, b, 0, 0⟩ : M12Mod) = ⟨a, b, i, j⟩ := by
      rw [show i = 0 from hm.1, show j = 0 from hm.2]
    exact ⟨a, b, by rw [h]; exact hmw⟩
  · rintro ⟨a, b, hab⟩
    exact ⟨⟨a, b, 0, 0⟩, (mem_base_model _).mpr ⟨rfl, rfl⟩, hab⟩

private theorem model_decomp :
    ∀ (a b : Fin 4) (i j : Fin 2),
      (⟨a, b, i, j⟩ : M12Mod) =
        (⟨a, b, 0, 0⟩ : M12Mod) * M12Mod.mlam ^ i.val * M12Mod.mtau ^ j.val := by
  decide +kernel

theorem M12Rel.coset_cases (h : M12Rel x₁ x₂ lam tau) :
    ∀ g ∈ m12Grp x₁ x₂ lam tau, ∃ w ∈ baseGrp x₁ x₂,
      g = w ∨ g = w * tau ∨ g = w * lam ∨ g = w * (lam * tau) := by
  obtain ⟨φ, hinj, hrange, h1, h2, h3, h4⟩ := h.exists_embedding
  intro g hg
  have hg' : g ∈ φ.range := by simpa [hrange] using hg
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hg'
  obtain ⟨a, b, i, j⟩ := m
  refine ⟨φ ⟨a, b, 0, 0⟩, (mem_baseGrp_iff φ h1 h2 _).mpr ⟨a, b, rfl⟩, ?_⟩
  rw [model_decomp a b i j, map_mul, map_mul, map_pow, map_pow, h3, h4]
  fin_cases i <;> fin_cases j
  · left; simp
  · right; left; simp
  · right; right; left; simp
  · right; right; right; simp [mul_assoc]

end CFSG.OddStandard.SmallF3.HarrisU33
