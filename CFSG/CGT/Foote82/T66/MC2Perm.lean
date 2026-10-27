module

public import CFSG.CGT.Foote82.T66.Perm310
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10Perm

public section

namespace CFSG.CGT.Foote82

namespace MC2

open Equiv Equiv.Perm

section AltOn

variable {m : ℕ}

theorem mem_altOn_iff {F : Set (Fin m)} {σ : Perm (Fin m)} :
    σ ∈ altOn F ↔ σ ∈ alternatingGroup (Fin m) ∧ ∀ x, x ∉ F → σ x = x := by
  simp only [altOn, Subgroup.mem_inf, mem_fixingSubgroup_iff, Set.mem_compl_iff, Perm.smul_def]

open Classical in
theorem altOn_eq (F : Set (Fin m)) :
    altOn F = CFSG.ComponentClassification.GSThmB.Catalog82A10.altOn F.toFinset := by
  ext σ
  rw [mem_altOn_iff, CFSG.ComponentClassification.GSThmB.Catalog82A10.mem_altOn]
  refine and_congr_right fun _ => ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · rw [Set.mem_toFinset]
    by_contra hxF
    exact (Perm.mem_support.1 hx) (h x hxF)
  · by_contra hσ
    exact hx (Set.mem_toFinset.1 (h (Perm.mem_support.2 hσ)))

theorem card_altOn {F : Set (Fin m)} (hF : 2 ≤ F.ncard) :
    Nat.card ↥(altOn F) = F.ncard.factorial / 2 := by
  classical
  rw [altOn_eq, CFSG.ComponentClassification.GSThmB.Catalog82A10.card_altOn,
    Set.ncard_eq_toFinset_card' F]
  · rwa [← Set.ncard_eq_toFinset_card' F]

theorem isSimpleGroup_altOn {F : Set (Fin m)} (hF : 5 ≤ F.ncard) : IsSimpleGroup ↥(altOn F) := by
  classical
  rw [altOn_eq]
  refine CFSG.ComponentClassification.GSThmB.Catalog82A10.isSimpleGroup_altOn _ ?_
  rwa [← Set.ncard_eq_toFinset_card' F]

theorem commute_of_fix {F : Set (Fin m)} {u σ : Perm (Fin m)} (hu : ∀ x ∈ F, u x = x)
    (hσ : σ ∈ altOn F) : u * σ = σ * u := by
  have hd : Equiv.Perm.Disjoint u σ := fun x => by
    by_cases hx : x ∈ F
    · exact Or.inl (hu x hx)
    · exact Or.inr ((mem_altOn_iff.1 hσ).2 x hx)
  exact hd.commute.eq

end AltOn

theorem four_le_card_support {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}
    (h2 : orderOf σ = 2) (hσ : σ ∈ alternatingGroup α) : 4 ≤ σ.support.card := by
  obtain ⟨-, h1, h3⟩ :=
    CFSG.ComponentClassification.GSThmB.Catalog82A10.cycleType_of_orderOf_two h2
  by_contra hlt
  have h22 : σ.support.card = 2 := by omega
  have hsw : σ.IsSwap := Perm.card_support_eq_two.1 h22
  have := hsw.sign_eq
  rw [Equiv.Perm.mem_alternatingGroup] at hσ
  rw [hσ] at this
  exact absurd this (by decide)

section ThreeCycles

variable {α : Type*} [Fintype α] [DecidableEq α]

@[expose] def c3 (a b c : α) : Perm α := swap a b * swap a c

theorem c3_apply_of_ne {a b c x : α} (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) :
    c3 a b c x = x := by
  rw [c3, Perm.mul_apply, swap_apply_of_ne_of_ne hxa hxc, swap_apply_of_ne_of_ne hxa hxb]

theorem isThreeCycle_c3 {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (c3 a b c).IsThreeCycle :=
  isThreeCycle_swap_mul_swap_same hab hac hbc

theorem c3_mem_alternatingGroup {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    c3 a b c ∈ alternatingGroup α :=
  Perm.mem_alternatingGroup.2 (isThreeCycle_c3 hab hac hbc).sign

theorem c3_pow_three {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    c3 a b c ^ 3 = 1 := by
  rw [← (isThreeCycle_c3 hab hac hbc).orderOf]
  exact pow_orderOf_eq_one _

theorem c3_mem_altOn {m : ℕ} {F : Set (Fin m)} {a b c : Fin m} (ha : a ∈ F) (hb : b ∈ F)
    (hc : c ∈ F) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : c3 a b c ∈ altOn F := by
  refine mem_altOn_iff.2 ⟨c3_mem_alternatingGroup hab hac hbc, fun x hx => ?_⟩
  exact c3_apply_of_ne (fun h => hx (h ▸ ha)) (fun h => hx (h ▸ hb)) (fun h => hx (h ▸ hc))

theorem disjoint_c3 {a b c a' b' c' : α} (h : [a, b, c, a', b', c'].Nodup) :
    Equiv.Perm.Disjoint (c3 a b c) (c3 a' b' c') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h
  obtain ⟨⟨hab, hac, haa', hab', hac'⟩, ⟨hbc, hba', hbb', hbc'⟩, ⟨hca', hcb', hcc'⟩,
    ⟨ha'b', ha'c'⟩, hb'c'⟩ := h
  intro x
  by_cases hx : x = a ∨ x = b ∨ x = c
  · right
    rcases hx with rfl | rfl | rfl
    · exact c3_apply_of_ne haa' hab' hac'
    · exact c3_apply_of_ne hba' hbb' hbc'
    · exact c3_apply_of_ne hca' hcb' hcc'
  · left
    push Not at hx
    exact c3_apply_of_ne hx.1 hx.2.1 hx.2.2

theorem c3_commute {a b c a' b' c' : α} (h : [a, b, c, a', b', c'].Nodup) :
    c3 a b c * c3 a' b' c' = c3 a' b' c' * c3 a b c :=
  (Equiv.Perm.Disjoint.commute (disjoint_c3 h)).eq

theorem cycleType_c3_mul {a b c a' b' c' : α} (h : [a, b, c, a', b', c'].Nodup) :
    (c3 a b c * c3 a' b' c').cycleType = {3, 3} := by
  have hn := h
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hn
  rw [Equiv.Perm.Disjoint.cycleType_mul (disjoint_c3 h), (isThreeCycle_c3 hn.1.1 hn.1.2.1 hn.2.1.1),
    (isThreeCycle_c3 hn.2.2.2.1.1 hn.2.2.2.1.2 hn.2.2.2.2)]
  rfl

theorem cycleType_c3_mul_sq {a b c a' b' c' : α} (h : [a, b, c, a', b', c'].Nodup) :
    (c3 a b c * c3 a' b' c' * c3 a' b' c').cycleType = {3, 3} := by
  have hn := h
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hn
  have h3 := isThreeCycle_c3 hn.2.2.2.1.1 hn.2.2.2.1.2 hn.2.2.2.2
  have hsq : c3 a' b' c' * c3 a' b' c' = (c3 a' b' c')⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_three']
    exact c3_pow_three hn.2.2.2.1.1 hn.2.2.2.1.2 hn.2.2.2.2
  rw [mul_assoc, hsq, Equiv.Perm.Disjoint.cycleType_mul (Equiv.Perm.Disjoint.inv_right (disjoint_c3 h)),
    (isThreeCycle_c3 hn.1.1 hn.1.2.1 hn.2.1.1), h3.inv]
  rfl

end ThreeCycles

theorem exists_injective_fin {α : Type*} {S : Finset α} {k : ℕ} (h : k ≤ S.card) :
    ∃ f : Fin k → α, Function.Injective f ∧ ∀ i, f i ∈ S := by
  classical
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq h
  let e : Fin k ≃ ↥T := T.equivFinOfCardEq hT |>.symm
  refine ⟨fun i => (e i : α), fun i j hij => e.injective (Subtype.ext hij), fun i => hTS (e i).2⟩

theorem tight_witness_of_points {m : ℕ} {F : Set (Fin m)} {a b c x y p q r w : Fin m}
    (ha : a ∉ F) (hb : b ∈ F) (hc : c ∈ F) (hx : x ∈ F) (hy : y ∈ F) (hp : p ∉ F) (hq : q ∉ F)
    (hr : r ∉ F) (hw : w ∉ F) (hbc : b ≠ c) (hbx : b ≠ x) (hby : b ≠ y) (hcy : c ≠ y)
    (hxy : x ≠ y) (hap : a ≠ p) (haq : a ≠ q) (har : a ≠ r) (haw : a ≠ w) (hpq : p ≠ q)
    (hpr : p ≠ r) (hpw : p ≠ w) (hqr : q ≠ r) (hqw : q ≠ w) (hrw : r ≠ w) :
    ∃ g ∈ alternatingGroup (Fin m), ∃ u ∈ alternatingGroup (Fin m),
      orderOf u = 2 ∧ (∀ z ∈ F, u z = z) ∧ g * u = u * g ∧
      ∃ σ ∈ altOn F, g * σ * g⁻¹ ∉ altOn F := by
  have hne : ∀ {z z' : Fin m}, z ∈ F → z' ∉ F → z ≠ z' := fun hz hz' h => hz' (h ▸ hz)
  have hab : a ≠ b := (hne hb ha).symm
  have hac : a ≠ c := (hne hc ha).symm
  have hufix : ∀ z, z ≠ p → z ≠ q → z ≠ r → z ≠ w → (swap p q * swap r w) z = z :=
    fun z hzp hzq hzr hzw => by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hzr hzw, swap_apply_of_ne_of_ne hzp hzq]
  have hdpq : Equiv.Perm.Disjoint (swap p q) (swap r w) := fun z => by
    by_cases hz : z = p ∨ z = q
    · right
      rcases hz with rfl | rfl
      · exact swap_apply_of_ne_of_ne hpr hpw
      · exact swap_apply_of_ne_of_ne hqr hqw
    · left
      push Not at hz
      exact swap_apply_of_ne_of_ne hz.1 hz.2
  have hu2 : (swap p q * swap r w) ^ 2 = 1 := by
    rw [(Equiv.Perm.Disjoint.commute hdpq).mul_pow, pow_two, pow_two, swap_mul_self, swap_mul_self,
      one_mul]
  have hu1 : swap p q * swap r w ≠ 1 := by
    intro h1'
    have := congrArg (fun π : Perm (Fin m) => π p) h1'
    simp only [Perm.one_apply] at this
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hpr hpw, swap_apply_left] at this
    exact hpq this.symm
  have huA : swap p q * swap r w ∈ alternatingGroup (Fin m) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, sign_swap hpq, sign_swap hrw]
    decide
  refine ⟨c3 a b c, c3_mem_alternatingGroup hab hac hbc, swap p q * swap r w, huA,
    orderOf_eq_prime hu2 hu1, ?_, ?_, ?_⟩
  · intro z hz
    exact hufix z (hne hz hp) (hne hz hq) (hne hz hr) (hne hz hw)
  ·
    have hd : Equiv.Perm.Disjoint (c3 a b c) (swap p q * swap r w) := fun z => by
      by_cases hz : z = a ∨ z = b ∨ z = c
      · right
        rcases hz with rfl | rfl | rfl
        · exact hufix _ hap haq har haw
        · exact hufix _ (hne hb hp) (hne hb hq) (hne hb hr) (hne hb hw)
        · exact hufix _ (hne hc hp) (hne hc hq) (hne hc hr) (hne hc hw)
      · left
        push Not at hz
        exact c3_apply_of_ne hz.1 hz.2.1 hz.2.2
    exact (Equiv.Perm.Disjoint.commute hd).eq
  ·
    refine ⟨c3 b x y, c3_mem_altOn hb hx hy hbx hby hxy, fun hmem => ?_⟩
    have hgb : c3 a b c b = a := by
      rw [c3, Perm.mul_apply, swap_apply_of_ne_of_ne hab.symm hbc, swap_apply_right]
    have hgia : (c3 a b c)⁻¹ a = b := by
      rw [Perm.inv_eq_iff_eq]
      exact hgb.symm
    have hgy : c3 a b c y = y := c3_apply_of_ne (hne hy ha) hby.symm hcy.symm
    have hσb : c3 b x y b = y := by
      rw [c3, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hby.symm hxy.symm]
    have hval : (c3 a b c * c3 b x y * (c3 a b c)⁻¹) a = y := by
      rw [Perm.mul_apply, Perm.mul_apply, hgia, hσb, hgy]
    have := (mem_altOn_iff.1 hmem).2 a ha
    rw [hval] at this
    exact hne hy ha this

theorem exists_tight_witness {m : ℕ} {F : Set (Fin m)} (hF : 5 ≤ F.ncard) (hF' : 5 ≤ Fᶜ.ncard) :
    ∃ g ∈ alternatingGroup (Fin m), ∃ u ∈ alternatingGroup (Fin m),
      orderOf u = 2 ∧ (∀ z ∈ F, u z = z) ∧ g * u = u * g ∧
      ∃ σ ∈ altOn F, g * σ * g⁻¹ ∉ altOn F := by
  classical
  obtain ⟨f₁, hf₁, hf₁F⟩ := exists_injective_fin (S := F.toFinset) (k := 5)
    (by rwa [← Set.ncard_eq_toFinset_card' F])
  obtain ⟨f₂, hf₂, hf₂F⟩ := exists_injective_fin (S := Fᶜ.toFinset) (k := 5)
    (by rwa [← Set.ncard_eq_toFinset_card' Fᶜ])
  have h1 : ∀ i, f₁ i ∈ F := fun i => Set.mem_toFinset.1 (hf₁F i)
  have h2 : ∀ i, f₂ i ∉ F := fun i => Set.mem_toFinset.1 (hf₂F i)
  have n₁ : ∀ i j : Fin 5, i ≠ j → f₁ i ≠ f₁ j := fun i j hij h => hij (hf₁ h)
  have n₂ : ∀ i j : Fin 5, i ≠ j → f₂ i ≠ f₂ j := fun i j hij h => hij (hf₂ h)
  exact tight_witness_of_points (h2 0) (h1 0) (h1 1) (h1 2) (h1 3) (h2 1) (h2 2) (h2 3) (h2 4)
    (n₁ 0 1 (by decide)) (n₁ 0 2 (by decide)) (n₁ 0 3 (by decide)) (n₁ 1 3 (by decide))
    (n₁ 2 3 (by decide)) (n₂ 0 1 (by decide)) (n₂ 0 2 (by decide)) (n₂ 0 3 (by decide))
    (n₂ 0 4 (by decide)) (n₂ 1 2 (by decide)) (n₂ 1 3 (by decide)) (n₂ 1 4 (by decide))
    (n₂ 2 3 (by decide)) (n₂ 2 4 (by decide)) (n₂ 3 4 (by decide))

end MC2

end CFSG.CGT.Foote82
