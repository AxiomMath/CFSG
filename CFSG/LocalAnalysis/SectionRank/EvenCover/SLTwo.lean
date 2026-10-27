module

public import CFSG.LieType.Steinberg.CentralExt.RankOne
public import CFSG.LieType.Steinberg.Adjoint.RankOne

public section

namespace CFSG.SectionRank.EvenCover

open Matrix CFSG.LieType.Steinberg CFSG.LieType.CentralExt

variable {k : Type*} [Field k]

@[expose] def sl2Rels (k : Type*) [Field k] : RankOneRels (SpecialLinearGroup (Fin 2) k) k where
  x := sl2Upper
  y := sl2Lower
  x_add a b := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Upper, coe_sl2Upper]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  y_add a b := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Lower, coe_sl2Lower, coe_sl2Lower]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  conj_x t ht a := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_sl2Upper,
      coe_sl2Lower]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two] <;> field_simp <;> ring

theorem sl2Rels_x (a : k) : (sl2Rels k).x a = sl2Upper a :=
  rfl

theorem sl2Rels_y (a : k) : (sl2Rels k).y a = sl2Lower a :=
  rfl

theorem coe_sl2Rels_w {t : k} (ht : t ≠ 0) :
    (((sl2Rels k).w t : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![0, t; -t⁻¹, 0] := by
  rw [RankOneRels.w_def]
  simp only [sl2Rels_x, sl2Rels_y, Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ht]

theorem coe_sl2Rels_h {t : k} (ht : t ≠ 0) :
    (((sl2Rels k).h t : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![t, 0; 0, t⁻¹] := by
  rw [RankOneRels.h_def, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    coe_sl2Rels_w ht, coe_sl2Rels_w one_ne_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]

theorem sl2Rels_sub
    {k : Type} [Field k] : (sl2Rels k).sub = ⊤ := by
  rw [eq_top_iff]
  intro s _
  obtain ⟨e, a, b, c, rfl⟩ := Adjoint.sl2_eq_prod s
  exact mul_mem (mul_mem (mul_mem ((sl2Rels k).y_mem_sub e) ((sl2Rels k).x_mem_sub a))
    ((sl2Rels k).y_mem_sub b)) ((sl2Rels k).x_mem_sub c)

variable {p : ℕ} [Fact p.Prime] [CharP k p]

theorem exists_orderOf_sl2Upper [Finite k] (c : k) : ∃ n : ℕ, orderOf (sl2Upper c) = p ^ n :=
  (sl2Rels k).exists_orderOf_x c

theorem exists_orderOf_sl2Lower [Finite k] (c : k) : ∃ n : ℕ, orderOf (sl2Lower c) = p ^ n :=
  (sl2Rels k).exists_orderOf_y c

theorem sl2_hom_ext
    {k : Type} [Field k] {G : Type*} [Group G]
    {f g : SpecialLinearGroup (Fin 2) k →* G} (hx : ∀ c, f (sl2Upper c) = g (sl2Upper c))
    (hy : ∀ c, f (sl2Lower c) = g (sl2Lower c)) : f = g := by
  apply MonoidHom.eq_of_eqOn_dense (s := Set.range (sl2Rels k).x ∪ Set.range (sl2Rels k).y)
  · rw [← RankOneRels.sub, sl2Rels_sub]
  · rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hx c
    · exact hy c

section Pullback

variable {H G E : Type*} [Group H] [Group G] [Group E]

@[expose] def pullback (π : E →* G) (ρ : H →* G) : Subgroup (H × E) where
  carrier := {x | ρ x.1 = π x.2}
  mul_mem' := fun {a b} ha hb => by
    change ρ (a.1 * b.1) = π (a.2 * b.2)
    rw [map_mul, map_mul, ha, hb]
  one_mem' := by
    change ρ 1 = π 1
    rw [map_one, map_one]
  inv_mem' := fun {a} ha => by
    change ρ a.1⁻¹ = π a.2⁻¹
    rw [map_inv, map_inv, ha]

theorem mem_pullback {π : E →* G} {ρ : H →* G} {x : H × E} :
    x ∈ pullback π ρ ↔ ρ x.1 = π x.2 :=
  Iff.rfl

@[expose] def pullbackFst (π : E →* G) (ρ : H →* G) : pullback π ρ →* H :=
  (MonoidHom.fst H E).comp (pullback π ρ).subtype

theorem pullbackFst_apply (π : E →* G) (ρ : H →* G) (x : pullback π ρ) :
    pullbackFst π ρ x = (x : H × E).1 :=
  rfl

theorem pullbackFst_surjective {π : E →* G} (hπ : Function.Surjective π) (ρ : H →* G) :
    Function.Surjective (pullbackFst π ρ) := fun g => by
  obtain ⟨e, he⟩ := hπ (ρ g)
  exact ⟨⟨(g, e), he.symm⟩, rfl⟩

theorem pullbackFst_ker_le_center {π : E →* G} (hcen : π.ker ≤ Subgroup.center E)
    (ρ : H →* G) : (pullbackFst π ρ).ker ≤ Subgroup.center (pullback π ρ) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : (x : H × E).1 = 1 := hx
  have h2 : (x : H × E).2 ∈ π.ker := by
    rw [MonoidHom.mem_ker, ← x.2, h1, map_one]
  have h3 := Subgroup.mem_center_iff.1 (hcen h2) (y : H × E).2
  apply Subtype.ext
  apply Prod.ext
  · change (y : H × E).1 * (x : H × E).1 = (x : H × E).1 * (y : H × E).1
    rw [h1, mul_one, one_mul]
  · exact h3

theorem card_pullbackFst_ker_dvd [Finite E] (π : E →* G) (ρ : H →* G) :
    Nat.card (pullbackFst π ρ).ker ∣ Nat.card π.ker := by
  let f : (pullbackFst π ρ).ker →* π.ker :=
    { toFun := fun x => ⟨((x : pullback π ρ) : H × E).2, by
        rw [MonoidHom.mem_ker, ← (x : pullback π ρ).2,
          show ((x : pullback π ρ) : H × E).1 = 1 from x.2, map_one]⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rw [show ((x : pullback π ρ) : H × E).1 = 1 from x.2,
        show ((y : pullback π ρ) : H × E).1 = 1 from y.2]
    · exact congrArg Subtype.val hxy
  exact Subgroup.card_dvd_of_injective f hf

theorem comp_snd_section {π : E →* G} {ρ : H →* G} (σ : H →* pullback π ρ)
    (hσ : ∀ g, pullbackFst π ρ (σ g) = g) :
    π.comp ((MonoidHom.snd H E).comp ((pullback π ρ).subtype.comp σ)) = ρ := by
  ext g
  have h1 : ((σ g : pullback π ρ) : H × E).1 = g := hσ g
  have h2 := (σ g).2
  change ρ ((σ g : pullback π ρ) : H × E).1 = _ at h2
  rw [h1] at h2
  exact h2.symm

end Pullback

variable {E : Type*} [Group E] [Finite E]

theorem sl2_existsUnique_section
    {k : Type} [Field k] [Finite k] [CharP k p]
    {π : E →* SpecialLinearGroup (Fin 2) k} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hC : ¬ p ∣ Nat.card π.ker) :
    ∃! σ : SpecialLinearGroup (Fin 2) k →* E, ∀ g, π (σ g) = g := by
  have hi : ∀ a t, t ≠ 0 → (sl2Rels k).x a * (sl2Rels k).h t = 1 → a = 0 ∧ t = 1 := by
    intro a t ht h
    have h' := congrArg (fun M : SpecialLinearGroup (Fin 2) k => (M : Matrix (Fin 2) (Fin 2) k)) h
    simp only [Matrix.SpecialLinearGroup.coe_mul, sl2Rels_x, coe_sl2Upper, coe_sl2Rels_h ht,
      Matrix.SpecialLinearGroup.coe_one] at h'
    have h00 := congrFun (congrFun h' 0) 0
    have h01 := congrFun (congrFun h' 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
    subst h00
    simpa using h01
  have hii : ∀ a b t, t ≠ 0 →
      (sl2Rels k).x a * (sl2Rels k).w 1 * (sl2Rels k).x b * (sl2Rels k).h t ≠ 1 := by
    intro a b t ht h
    have h' := congrArg (fun M : SpecialLinearGroup (Fin 2) k => (M : Matrix (Fin 2) (Fin 2) k)) h
    simp only [Matrix.SpecialLinearGroup.coe_mul, sl2Rels_x, coe_sl2Upper, coe_sl2Rels_h ht,
      coe_sl2Rels_w one_ne_zero, Matrix.SpecialLinearGroup.coe_one] at h'
    have h10 := congrFun (congrFun h' 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h10
    exact ht h10
  obtain ⟨φ, hφ⟩ := (sl2Rels k).exists_lift_of_separated hπ hcen hC hi hii
  let e : SpecialLinearGroup (Fin 2) k ≃* (sl2Rels k).sub :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr sl2Rels_sub.symm)
  refine ⟨φ.comp e.toMonoidHom, fun g => hφ (e g), fun τ hτ => ?_⟩
  apply sl2_hom_ext
  · intro c
    refine eq_of_pElement hcen hC ?_ (exists_orderOf_map_eq_pow τ (exists_orderOf_sl2Upper c))
      (exists_orderOf_map_eq_pow _ (exists_orderOf_sl2Upper c))
    rw [hτ, MonoidHom.comp_apply, hφ]
    rfl
  · intro c
    refine eq_of_pElement hcen hC ?_ (exists_orderOf_map_eq_pow τ (exists_orderOf_sl2Lower c))
      (exists_orderOf_map_eq_pow _ (exists_orderOf_sl2Lower c))
    rw [hτ, MonoidHom.comp_apply, hφ]
    rfl

theorem sl2_existsUnique_lift
    {k : Type} [Field k] [Finite k] [CharP k p] {G : Type*} [Group G]
    {π : E →* G} (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : ¬ p ∣ Nat.card π.ker) (ρ : SpecialLinearGroup (Fin 2) k →* G) :
    ∃! ρ' : SpecialLinearGroup (Fin 2) k →* E, π.comp ρ' = ρ := by
  obtain ⟨σ, hσ, -⟩ := sl2_existsUnique_section (pullbackFst_surjective hπ ρ)
    (pullbackFst_ker_le_center hcen ρ) (fun h => hC (h.trans (card_pullbackFst_ker_dvd π ρ)))
  refine ⟨_, comp_snd_section σ hσ, fun τ hτ => ?_⟩
  have hτ' := comp_snd_section σ hσ
  apply sl2_hom_ext
  · intro c
    refine eq_of_pElement hcen hC ?_
      (exists_orderOf_map_eq_pow τ (exists_orderOf_sl2Upper c))
      (exists_orderOf_map_eq_pow _ (exists_orderOf_sl2Upper c))
    have h1 := congrArg (· (sl2Upper c)) hτ
    have h2 := congrArg (· (sl2Upper c)) hτ'
    simp only [MonoidHom.comp_apply] at h1 h2 ⊢
    rw [h1, h2]
  · intro c
    refine eq_of_pElement hcen hC ?_
      (exists_orderOf_map_eq_pow τ (exists_orderOf_sl2Lower c))
      (exists_orderOf_map_eq_pow _ (exists_orderOf_sl2Lower c))
    have h1 := congrArg (· (sl2Lower c)) hτ
    have h2 := congrArg (· (sl2Lower c)) hτ'
    simp only [MonoidHom.comp_apply] at h1 h2 ⊢
    rw [h1, h2]

end CFSG.SectionRank.EvenCover
