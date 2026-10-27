module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open scoped commutatorElement

private theorem commutator_prod_eq :
    _root_.commutator (Elem2 2 × alternatingGroup (Fin 8)) =
      (⊥ : Subgroup (Elem2 2)).prod ⊤ := by
  apply le_antisymm
  · rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_prod]
    refine ⟨?_, Subgroup.mem_top _⟩
    have hxy : ⁅x, y⁆ = (⁅x.1, y.1⁆, ⁅x.2, y.2⁆) := by
      ext <;> simp [commutatorElement_def]
    rw [hxy]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all x.1 y.1)
  · have hcommB : _root_.commutator (alternatingGroup (Fin 8)) = ⊤ :=
      commutator_alternatingGroup_eq_top (by rw [Nat.card_fin]; norm_num)
    have hran : (MonoidHom.inr (Elem2 2) (alternatingGroup (Fin 8))).range =
        (⊥ : Subgroup (Elem2 2)).prod ⊤ := by
      ext p; constructor
      · rintro ⟨b, rfl⟩
        exact ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top b⟩
      · rintro ⟨hp1, -⟩
        exact ⟨p.2, by ext <;> simp [Subgroup.mem_bot.mp hp1]⟩
    rw [← hran]
    intro x hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨b, rfl⟩ := hx
    have hb : b ∈ _root_.commutator (alternatingGroup (Fin 8)) := by rw [hcommB]; trivial
    have hmapcomm : (_root_.commutator (alternatingGroup (Fin 8))).map
        (MonoidHom.inr (Elem2 2) (alternatingGroup (Fin 8))) =
        ⁅(MonoidHom.inr (Elem2 2) (alternatingGroup (Fin 8))).range,
          (MonoidHom.inr (Elem2 2) (alternatingGroup (Fin 8))).range⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top]
    have hmem : MonoidHom.inr (Elem2 2) (alternatingGroup (Fin 8)) b ∈
        (_root_.commutator (alternatingGroup (Fin 8))).map
          (MonoidHom.inr (Elem2 2) (alternatingGroup (Fin 8))) :=
      Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
    rw [hmapcomm] at hmem
    exact Subgroup.commutator_mono le_top le_top hmem

private theorem natCard_elem2_two : Nat.card (Elem2 2) = 4 := by
  rw [Elem2, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  norm_num

private theorem elem2_sq (g : Elem2 2) : g * g = 1 := by
  apply Multiplicative.ext
  rw [toAdd_mul, toAdd_one]
  funext i
  exact CharTwo.add_self_eq_zero (g.toAdd i)

private theorem mem_closure_pair_iff' {A : Type*} [Group A] {a b : A} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) {x : A} :
    x ∈ Subgroup.closure ({a, b} : Set A) ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have ha' : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have hba : ∀ y, b * (a * y) = a * (b * y) := fun y => by rw [← mul_assoc, ← hab, mul_assoc]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [mul_assoc, ha, hb, ha', hba, hab.symm, mul_one, one_mul, true_or, or_true]
    | inv x _ hx =>
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp only [inv_one, hai, hbi, mul_inv_rev, hab.symm, true_or, or_true]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · have ha : a ∈ Subgroup.closure ({a, b} : Set A) := Subgroup.subset_closure (by simp)
      have hb : b ∈ Subgroup.closure ({a, b} : Set A) := Subgroup.subset_closure (by simp)
      exact Subgroup.mul_mem (Subgroup.closure ({a, b} : Set A)) ha hb

private theorem elem2_closure_pair_eq_top {α β : Elem2 2} (hα : α ≠ 1) (hβ : β ≠ 1)
    (hαβ : α ≠ β) : Subgroup.closure ({α, β} : Set (Elem2 2)) = ⊤ := by
  have hsqa : α * α = 1 := elem2_sq α
  have hsqb : β * β = 1 := elem2_sq β
  have hcomm : α * β = β * α := mul_comm _ _
  have hset : (Subgroup.closure ({α, β} : Set (Elem2 2)) : Set (Elem2 2)) =
      ({1, α, β, α * β} : Set (Elem2 2)) := by
    ext x
    change x ∈ Subgroup.closure ({α, β} : Set (Elem2 2)) ↔ x ∈ ({1, α, β, α * β} : Set (Elem2 2))
    rw [mem_closure_pair_iff' hsqa hsqb hcomm]
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hab1 : α ≠ α * β := by
    intro h
    exact hβ (by
      calc β = 1 * β := by rw [one_mul]
        _ = (α * α) * β := by rw [hsqa]
        _ = α * (α * β) := by rw [mul_assoc]
        _ = α * α := by rw [← h]
        _ = 1 := hsqa)
  have hba1 : β ≠ α * β := by
    intro h
    exact hα (by
      calc α = 1 * α := by rw [one_mul]
        _ = (β * β) * α := by rw [hsqb]
        _ = β * (β * α) := by rw [mul_assoc]
        _ = β * (α * β) := by rw [hcomm.symm]
        _ = β * β := by rw [← h]
        _ = 1 := hsqb)
  have h1ab : (1 : Elem2 2) ≠ α * β := by
    intro h
    exact hαβ (by
      calc α = α * 1 := by rw [mul_one]
        _ = α * (α * β) := by rw [← h]
        _ = (α * α) * β := by rw [mul_assoc]
        _ = 1 * β := by rw [hsqa]
        _ = β := by rw [one_mul])
  have h1 : (1 : Elem2 2) ∉ ({α, β, α * β} : Set (Elem2 2)) := by
    simp [hα.symm, hβ.symm, h1ab]
  have h2 : α ∉ ({β, α * β} : Set (Elem2 2)) := by
    simp [hαβ, hab1]
  have h3 : β ∉ ({α * β} : Set (Elem2 2)) := by
    simpa using hba1
  apply Subgroup.eq_top_of_card_eq
  calc Nat.card ↥(Subgroup.closure ({α, β} : Set (Elem2 2)))
      = ((Subgroup.closure ({α, β} : Set (Elem2 2)) : Set (Elem2 2))).ncard :=
        Nat.card_coe_set_eq _
    _ = ({1, α, β, α * β} : Set (Elem2 2)).ncard := by rw [hset]
    _ = 4 := by
      rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
        Set.ncard_insert_of_notMem h3, Set.ncard_singleton]
    _ = Nat.card (Elem2 2) := by rw [natCard_elem2_two]

theorem exists_mul_eq_of_isShapeTwoTwoTimesA8 {G : Type} [Group G] {a b : G}
    (hX : IsShapeTwoTwoTimesA8 ↥(Gxy a b)) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    ∀ x ∈ Gxy a b, ∃ u ∈ Subgroup.closure ({a, b} : Set G), ∃ s ∈ derivedOf (Gxy a b), x = u * s := by
  classical
  obtain ⟨e⟩ := hX
  have ha_mem : a ∈ Gxy a b := mem_Gxy.mpr ⟨mem_Gx.mpr rfl, mem_Gx.mpr hab.symm⟩
  have hb_mem : b ∈ Gxy a b := mem_Gxy.mpr ⟨mem_Gx.mpr hab, mem_Gx.mpr rfl⟩
  let ea : ↥(Gxy a b) := ⟨a, ha_mem⟩
  let eb : ↥(Gxy a b) := ⟨b, hb_mem⟩
  have ha_center : ea ∈ Subgroup.center ↥(Gxy a b) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp g.2 a (by simp)).symm
  have hb_center : eb ∈ Subgroup.center ↥(Gxy a b) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp g.2 b (by simp)).symm
  have hea_center : e ea ∈ Subgroup.center (Elem2 2 × alternatingGroup (Fin 8)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp ha_center g)
  have heb_center : e eb ∈ Subgroup.center (Elem2 2 × alternatingGroup (Fin 8)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp hb_center g)
  have hA8center : Subgroup.center (alternatingGroup (Fin 8)) = ⊥ :=
    alternatingGroup.center_eq_bot (α := Fin 8) (by rw [Nat.card_fin]; norm_num)
  have hσ1 : (e ea).2 = 1 := by
    have hmem : (e ea).2 ∈ Subgroup.center (alternatingGroup (Fin 8)) := by
      rw [Subgroup.mem_center_iff]
      intro s
      exact congrArg Prod.snd (Subgroup.mem_center_iff.mp hea_center (1, s))
    exact Subgroup.mem_bot.mp (by rw [← hA8center]; exact hmem)
  have hτ1 : (e eb).2 = 1 := by
    have hmem : (e eb).2 ∈ Subgroup.center (alternatingGroup (Fin 8)) := by
      rw [Subgroup.mem_center_iff]
      intro s
      exact congrArg Prod.snd (Subgroup.mem_center_iff.mp heb_center (1, s))
    exact Subgroup.mem_bot.mp (by rw [← hA8center]; exact hmem)
  have hea : e ea = ((e ea).1, 1) := Prod.ext rfl hσ1
  have heb : e eb = ((e eb).1, 1) := Prod.ext rfl hτ1
  have hα1 : (e ea).1 ≠ 1 := by
    intro h
    have h1 : ea = 1 := e.injective (by rw [hea, h, map_one]; rfl)
    exact ha1 (congrArg Subtype.val h1)
  have hβ1 : (e eb).1 ≠ 1 := by
    intro h
    have h1 : eb = 1 := e.injective (by rw [heb, h, map_one]; rfl)
    exact hb1 (congrArg Subtype.val h1)
  have hαβ : (e ea).1 ≠ (e eb).1 := by
    intro h
    have h1 : ea = eb := e.injective (by rw [hea, heb, h])
    exact hne (congrArg Subtype.val h1)
  have hsqa : (e ea).1 * (e ea).1 = 1 := elem2_sq _
  have hsqb : (e eb).1 * (e eb).1 = 1 := elem2_sq _
  have hcomm : (e ea).1 * (e eb).1 = (e eb).1 * (e ea).1 := mul_comm _ _
  have hgen : Subgroup.closure ({(e ea).1, (e eb).1} : Set (Elem2 2)) = ⊤ :=
    elem2_closure_pair_eq_top hα1 hβ1 hαβ
  have hcover : ∀ γ : Elem2 2,
      e.symm (γ, 1) = 1 ∨ e.symm (γ, 1) = ea ∨ e.symm (γ, 1) = eb ∨
        e.symm (γ, 1) = ea * eb := by
    intro γ
    have hγ : γ ∈ Subgroup.closure ({(e ea).1, (e eb).1} : Set (Elem2 2)) := by
      rw [hgen]; trivial
    rcases (mem_closure_pair_iff' hsqa hsqb hcomm).mp hγ with h | h | h | h
    · left; rw [h]; simp
    · right; left; rw [h, ← hea, MulEquiv.symm_apply_apply]
    · right; right; left; rw [h, ← heb, MulEquiv.symm_apply_apply]
    · right; right; right
      have htuple : ((e ea).1 * (e eb).1, (1 : alternatingGroup (Fin 8))) =
          ((e ea).1, 1) * ((e eb).1, 1) := by ext <;> simp
      rw [h, htuple, ← hea, ← heb, ← map_mul, MulEquiv.symm_apply_apply]
  have hmem_closure : ∀ γ : Elem2 2,
      ((e.symm (γ, 1) : ↥(Gxy a b)) : G) ∈ Subgroup.closure ({a, b} : Set G) := by
    intro γ
    rcases hcover γ with h | h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; show a ∈ Subgroup.closure ({a, b} : Set G)
      exact Subgroup.subset_closure (by simp)
    · rw [h]; show b ∈ Subgroup.closure ({a, b} : Set G)
      exact Subgroup.subset_closure (by simp)
    · rw [h]; show a * b ∈ Subgroup.closure ({a, b} : Set G)
      have ha : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
      have hb : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
      exact Subgroup.mul_mem (Subgroup.closure ({a, b} : Set G)) ha hb
  have hderived_mem : ∀ y : alternatingGroup (Fin 8),
      ((e.symm (1, y) : ↥(Gxy a b)) : G) ∈ derivedOf (Gxy a b) := by
    intro y
    have hy : ((1 : Elem2 2), y) ∈
        _root_.commutator (Elem2 2 × alternatingGroup (Fin 8)) := by
      rw [commutator_prod_eq]
      exact ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top y⟩
    have hgmap : (_root_.commutator (Elem2 2 × alternatingGroup (Fin 8))).map
        e.symm.toMonoidHom = _root_.commutator ↥(Gxy a b) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.symm.surjective]
    have hy' : e.symm (1, y) ∈ _root_.commutator ↥(Gxy a b) := by
      rw [← hgmap]
      exact Subgroup.mem_map.mpr ⟨(1, y), hy, rfl⟩
    exact Subgroup.mem_map.mpr ⟨e.symm (1, y), hy', rfl⟩
  intro x hx
  have h_comm : (e.symm ((e ⟨x, hx⟩).1, 1) : ↥(Gxy a b)) *
      e.symm (1, (e ⟨x, hx⟩).2) = (⟨x, hx⟩ : ↥(Gxy a b)) := by
    rw [← map_mul]
    rw [show ((e ⟨x, hx⟩).1, 1) * (1, (e ⟨x, hx⟩).2) = e ⟨x, hx⟩ by ext <;> simp]
    rw [MulEquiv.symm_apply_apply]
  refine ⟨((e.symm ((e ⟨x, hx⟩).1, 1) : ↥(Gxy a b)) : G),
          hmem_closure (e ⟨x, hx⟩).1,
          ((e.symm (1, (e ⟨x, hx⟩).2) : ↥(Gxy a b)) : G),
          hderived_mem (e ⟨x, hx⟩).2, ?_⟩
  simpa using (congrArg Subtype.val h_comm).symm

theorem nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8 {G : Type} [Group G] {H : Subgroup G}
    (hX : IsShapeTwoTwoTimesA8 ↥H) : Nonempty (alternatingGroup (Fin 8) ≃* ↥(derivedOf H)) := by
  classical
  obtain ⟨e⟩ := hX
  let f : alternatingGroup (Fin 8) →* ↥H :=
    e.symm.toMonoidHom.comp (MonoidHom.inr (Elem2 2) (alternatingGroup (Fin 8)))
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : (MonoidHom.inr (Elem2 2) (alternatingGroup (Fin 8))) x =
        (MonoidHom.inr (Elem2 2) (alternatingGroup (Fin 8))) y := e.symm.injective hxy
    simpa using congrArg Prod.snd h1
  have hrange : f.range = _root_.commutator ↥H := by
    change (e.symm.toMonoidHom.comp (MonoidHom.inr (Elem2 2) (alternatingGroup (Fin 8)))).range =
      _root_.commutator ↥H
    rw [MonoidHom.range_comp]
    have hran : (MonoidHom.inr (Elem2 2) (alternatingGroup (Fin 8))).range =
        (⊥ : Subgroup (Elem2 2)).prod ⊤ := by
      ext p; constructor
      · rintro ⟨b, rfl⟩
        exact ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top b⟩
      · rintro ⟨hp1, -⟩
        exact ⟨p.2, by ext <;> simp [Subgroup.mem_bot.mp hp1]⟩
    rw [hran]
    have hgmap : (_root_.commutator (Elem2 2 × alternatingGroup (Fin 8))).map e.symm.toMonoidHom =
        _root_.commutator ↥H := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.symm.surjective]
    rw [← hgmap, commutator_prod_eq]
  refine ⟨(MonoidHom.ofInjective hf).trans
    ((MulEquiv.subgroupCongr hrange).trans
      (Subgroup.equivMapOfInjective (_root_.commutator ↥H) H.subtype H.subtype_injective))⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
