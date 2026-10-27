module

public import CFSG.Fischer.Classification.Basic.Local
public import CFSG.Fischer.Classification.Skeleton

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {X : Type} [Group X] {E : Set X}

section Affine

theorem Pair.commute_or_of_isSymplecticType_localImages (hP : Pair X E) {d : X}
    (hsymp : IsSymplecticType (LocalImages E d)) {a b z : X} (ha : a ∈ LocalClass E d)
    (hb : b ∈ LocalClass E d) (hz : z ∈ LocalClass E d) (hab : a * b ≠ b * a) :
    z * a = a * z ∨ z * b = b * z ∨ z * (a * b * a) = a * b * a * z := by
  have hmem : ∀ f : LocalClass E d, starImage E d f ∈ LocalImages E d := fun f =>
    range_starImage (E := E) d ▸ ⟨f, rfl⟩
  have hcomm : ∀ f g : LocalClass E d, starImage E d f * starImage E d g =
      starImage E d g * starImage E d f ↔ (f : X) * g = g * f := fun f g =>
    Pair.starImage_commute_iff hP f g
  have haba := Pair.mul_mul_mem_localClass_of_mem hP ha hb
  rcases hsymp _ (hmem ⟨a, ha⟩) _ (hmem ⟨b, hb⟩) _ (hmem ⟨z, hz⟩)
      (fun h => hab ((hcomm ⟨a, ha⟩ ⟨b, hb⟩).1 h)) with h | h | h
  · exact Or.inl ((hcomm ⟨z, hz⟩ ⟨a, ha⟩).1 h)
  · exact Or.inr (Or.inl ((hcomm ⟨z, hz⟩ ⟨b, hb⟩).1 h))
  · refine Or.inr (Or.inr ((hcomm ⟨z, hz⟩ ⟨a * b * a, haba⟩).1 ?_))
    rw [starImage_conj ⟨a, ha⟩ ⟨b, hb⟩ haba]
    exact h

theorem Pair.commute_or_of_commute (hP : Pair X E) {d : X} (hd : d ∈ E)
    (hsymp : IsSymplecticType (LocalImages E d)) {f a b z : X} (hf : f ∈ E) (ha : a ∈ E)
    (hb : b ∈ E) (hz : z ∈ E) (hab : a * b ≠ b * a) (hfa : f * a = a * f) (hfb : f * b = b * f)
    (hfz : f * z = z * f) :
    z * a = a * z ∨ z * b = b * z ∨ z * (a * b * a) = a * b * a * z := by
  by_cases hzf : z = f
  · subst hzf
    exact Or.inl hfa
  obtain ⟨g, hg⟩ := isConj_iff.1 (Pair.isConj hP hf hd)
  have hloc : ∀ x ∈ E, x ≠ f → f * x = x * f → g * x * g⁻¹ ∈ LocalClass E d := by
    intro x hx hxf hc
    rw [← hg, Pair.conj_mem_localClass_iff hP]
    exact ⟨hx, hxf, hc.symm⟩
  have haf : a ≠ f := by
    rintro rfl
    exact hab hfb
  have hbf : b ≠ f := by
    rintro rfl
    exact hab hfa.symm
  rcases Pair.commute_or_of_isSymplecticType_localImages hP hsymp (hloc a ha haf hfa)
      (hloc b hb hbf hfb) (hloc z hz hzf hfz) (by rwa [Ne, conj_commute_iff]) with h | h | h
  · exact Or.inl ((conj_commute_iff g z a).1 h)
  · exact Or.inr (Or.inl ((conj_commute_iff g z b).1 h))
  · refine Or.inr (Or.inr ((conj_commute_iff g z (a * b * a)).1 ?_))
    rwa [show g * (a * b * a) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) * (g * a * g⁻¹) by group]

end Affine

section Plane

namespace LocalSymp

theorem commute_of_commute_mul_mul (hP : Pair X E) {f x y : X} (hx : x ∈ E) (h1 : Commute f x)
    (h2 : Commute f (x * y * x)) : Commute f y := by
  rw [← Pair.mul_mul_mul_mul hP hx y]
  exact (h1.mul_right h2).mul_right h1

theorem commute_of_commute_line (hP : Pair X E) {f x y : X} (hx : x ∈ E) (hy : y ∈ E)
    (hxy : x * y ≠ y * x) (h1 : Commute f y) (h2 : Commute f (x * y * x)) : Commute f x := by
  rw [← Pair.mul_mul_conj_eq hP hx hy hxy]
  exact (h1.mul_right h2).mul_right h1

theorem commute_conj (hP : Pair X E) {b f x : X} (hb : b ∈ E) (h : Commute f x) :
    Commute (b * f * b) (b * x * b) := by
  have := (conj_commute_iff b f x).2 h
  rwa [Pair.inv_eq hP hb] at this

end LocalSymp

open LocalSymp

theorem Pair.four_mul_ncard_muSet_le (hP : Pair X E) {d : X} (hd : d ∈ E)
    (hsymp : IsSymplecticType (LocalImages E d)) {a b z : X} (ha : a ∈ E) (hb : b ∈ E)
    (hz : z ∈ E) (hab : a * b ≠ b * a) (haz : a * z ≠ z * a) (hbz : b * z ≠ z * b)
    (hzl : z * (a * b * a) ≠ a * b * a * z) {μ : ℕ}
    (hμ : ∀ q ∈ E, a * q ≠ q * a → (muSet E a q).ncard = μ) :
    4 * μ ≤ (LocalClass E a).ncard := by
  have := Pair.finite hP
  have hfree : ∀ f ∈ E, Commute f a → Commute f b → Commute f z → False := by
    intro f hf h1 h2 h3
    rcases Pair.commute_or_of_commute hP hd hsymp hf ha hb hz hab h1 h2 h3 with h | h | h
    · exact haz h.symm
    · exact hbz h.symm
    · exact hzl h
  have hbab : b * a * b = a * b * a := (Pair.mul_mul_eq hP ha hb hab).symm
  have haza : a * z * a ∈ E := Pair.mul_mul_mem hP ha hz
  have hbaza : b * (a * z * a) ≠ a * z * a * b := by
    intro h
    apply hzl
    have h' := (conj_commute_iff a b (a * z * a)).2 h
    rw [Pair.inv_eq hP ha, Pair.mul_mul_mul_mul hP ha] at h'
    exact h'.symm
  have hq3 : a * (b * z * b) ≠ b * z * b * a := by
    intro h
    apply hzl
    have h' := commute_conj hP hb (show Commute a (b * z * b) from h)
    rw [Pair.mul_mul_mul_mul hP hb, hbab] at h'
    exact h'.eq.symm
  have hq4 : a * (b * (a * z * a) * b) ≠ b * (a * z * a) * b * a := by
    intro h
    apply hbz
    have h' := commute_conj hP hb (show Commute a (b * (a * z * a) * b) from h)
    rw [Pair.mul_mul_mul_mul hP hb, hbab] at h'
    have h'' := commute_conj hP ha h'
    rw [Pair.mul_mul_mul_mul hP ha, Pair.mul_mul_mul_mul hP ha] at h''
    exact h''.eq
  have hμ₁ := hμ b hb hab
  have hμ₂ := hμ z hz haz
  have hμ₃ := hμ _ (Pair.mul_mul_mem hP hb hz) hq3
  have hμ₄ := hμ _ (Pair.mul_mul_mem hP hb haza) hq4
  set S₁ := muSet E a b
  set S₂ := muSet E a z
  set S₃ := muSet E a (b * z * b)
  set S₄ := muSet E a (b * (a * z * a) * b)
  have hc : ∀ {f q : X}, f ∈ muSet E a q → f ∈ E ∧ Commute f a ∧ Commute f q :=
    fun hf => ⟨hf.1.1, hf.1.2.2, hf.2.2.2⟩
  have h12 : Disjoint S₁ S₂ := Set.disjoint_left.2 fun f h1 h2 => by
    obtain ⟨hf, hfa, hfb⟩ := hc h1
    exact hfree f hf hfa hfb (hc h2).2.2
  have h13 : Disjoint S₁ S₃ := Set.disjoint_left.2 fun f h1 h3 => by
    obtain ⟨hf, hfa, hfb⟩ := hc h1
    exact hfree f hf hfa hfb (commute_of_commute_mul_mul hP hb hfb (hc h3).2.2)
  have h14 : Disjoint S₁ S₄ := Set.disjoint_left.2 fun f h1 h4 => by
    obtain ⟨hf, hfa, hfb⟩ := hc h1
    have := commute_of_commute_mul_mul hP hb hfb (hc h4).2.2
    exact hfree f hf hfa hfb (commute_of_commute_mul_mul hP ha hfa this)
  have h23 : Disjoint S₂ S₃ := Set.disjoint_left.2 fun f h2 h3 => by
    obtain ⟨hf, hfa, hfz⟩ := hc h2
    exact hfree f hf hfa (commute_of_commute_line hP hb hz hbz hfz (hc h3).2.2) hfz
  have h24 : Disjoint S₂ S₄ := Set.disjoint_left.2 fun f h2 h4 => by
    obtain ⟨hf, hfa, hfz⟩ := hc h2
    have hfaza : Commute f (a * z * a) := (hfa.mul_right hfz).mul_right hfa
    exact hfree f hf hfa (commute_of_commute_line hP hb haza hbaza hfaza (hc h4).2.2) hfz
  have h34 : Disjoint S₃ S₄ := Set.disjoint_left.2 fun f h3 h4 => by
    obtain ⟨hf, hfa, hf3⟩ := hc h3
    have hf4 := (hc h4).2.2
    have hz' := commute_conj hP hb hf3
    rw [Pair.mul_mul_mul_mul hP hb] at hz'
    have haza' := commute_conj hP hb hf4
    rw [Pair.mul_mul_mul_mul hP hb] at haza'
    have ha' := commute_of_commute_line hP ha hz haz hz' haza'
    have haba' := commute_conj hP hb hfa
    rw [hbab] at haba'
    exact hfree _ (Pair.mul_mul_mem hP hb hf) ha' (commute_of_commute_mul_mul hP ha ha' haba') hz'
  have hsub : S₁ ∪ S₂ ∪ S₃ ∪ S₄ ⊆ LocalClass E a := by
    intro f hf
    rcases hf with ((hf | hf) | hf) | hf <;> exact hf.1
  have hcard : (S₁ ∪ S₂ ∪ S₃ ∪ S₄).ncard = S₁.ncard + S₂.ncard + S₃.ncard + S₄.ncard := by
    rw [Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2 ⟨h14, h24⟩, h34⟩),
      Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨h13, h23⟩), Set.ncard_union_eq h12]
  have := Set.ncard_le_ncard hsub
  omega

end Plane

section Bound

theorem Pair.ncard_muSet_localImages_add_one_le (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) {d : X} (hd : d ∈ E) (x y : LocalClass E d) :
    (muSet (LocalImages E d) (starImage E d x) (starImage E d y)).ncard + 1 ≤
      (muSet E x y).ncard := by
  have := Pair.finite hP
  set S := muSet (LocalImages E d) (starImage E d x) (starImage E d y)
  have hinj := Pair.starImage_injective_of_simple hP hZ hS hd
  set L : Set X := Subtype.val '' (starImage E d ⁻¹' S)
  have hL : L.ncard = S.ncard := by
    rw [Set.ncard_image_of_injective _ Subtype.val_injective,
      ← Set.ncard_image_of_injective _ hinj, Set.image_preimage_eq_of_subset]
    intro q hq
    rw [range_starImage]
    exact hq.1.1
  have hdL : d ∉ L := by
    rintro ⟨f, -, hf⟩
    exact f.2.2.1 hf
  have hsub : insert d L ⊆ muSet E x y := by
    rintro w (rfl | ⟨f, ⟨⟨-, hfx, hfxc⟩, ⟨-, hfy, hfyc⟩⟩, rfl⟩)
    · exact ⟨⟨hd, fun h => x.2.2.1 h.symm, x.2.2.2.symm⟩,
        ⟨hd, fun h => y.2.2.1 h.symm, y.2.2.2.symm⟩⟩
    · refine ⟨⟨f.2.1, fun h => hfx (congrArg _ (Subtype.ext h)),
        (Pair.starImage_commute_iff hP f x).1 hfxc⟩, ⟨f.2.1, fun h => hfy (congrArg _
          (Subtype.ext h)), (Pair.starImage_commute_iff hP f y).1 hfyc⟩⟩
  calc S.ncard + 1 = (insert d L).ncard := by rw [Set.ncard_insert_of_notMem hdL, hL]
    _ ≤ (muSet E x y).ncard := Set.ncard_le_ncard hsub

theorem Pair.ncard_localImages (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) {d : X} (hd : d ∈ E) :
    (LocalImages E d).ncard = (LocalClass E d).ncard := by
  rw [← range_starImage, Set.ncard_range_of_injective
    (Pair.starImage_injective_of_simple hP hZ hS hd), Nat.card_coe_set_eq]

theorem Pair.four_mul_le_ncard_localImages (hH : Hyp X E) (hna : NonabelianCommutator X)
    (hnot : ¬ IsSymplecticType E) {d : X} (hd : d ∈ E)
    (hsymp : IsSymplecticType (LocalImages E d)) {x y : LocalQuotient E d}
    (hx : x ∈ LocalImages E d) (hy : y ∈ LocalImages E d) (hxy : x * y ≠ y * x) :
    4 * (1 + (muSet (LocalImages E d) x y).ncard) ≤ (LocalImages E d).ncard := by
  obtain ⟨hP, hZ, hS⟩ := hH
  have := Pair.finite hP
  obtain ⟨a, ha, b, hb, z, hz, hab, hzl⟩ : ∃ a ∈ E, ∃ b ∈ E, ∃ z ∈ E, a * b ≠ b * a ∧
      ¬ (z * a = a * z ∨ z * b = b * z ∨ z * (a * b * a) = a * b * a * z) := by
    by_contra! h
    exact hnot fun a ha b hb z hz hab => by
      by_contra h'
      exact h' (by simpa using h a ha b hb z hz hab)
  push Not at hzl
  obtain ⟨hza, hzb, hzl⟩ := hzl
  rw [← range_starImage] at hx hy
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hy
  have hxy' : (x' : X) * y' ≠ y' * x' := fun h =>
    hxy ((Pair.starImage_commute_iff hP x' y').2 h)
  have hμ : ∀ q ∈ E, a * q ≠ q * a → (muSet E a q).ncard = (muSet E x' y').ncard := by
    intro q hq haq
    obtain ⟨g, hga, hgq⟩ := Pair.exists_conj_pair_of_not_commute hP hZ hS hna ha hq x'.2.1 y'.2.1
      haq hxy'
    rw [← hga, ← hgq, ← Pair.image_conj_muSet hP, Set.ncard_image_of_injective _ (conj_injective g)]
  have h4 := Pair.four_mul_ncard_muSet_le hP hd hsymp ha hb hz hab (fun h => hza h.symm)
    (fun h => hzb h.symm) hzl hμ
  rw [Pair.ncard_localClass_eq hP ha hd, ← Pair.ncard_localImages hP hZ hS hd] at h4
  have h1 := Pair.ncard_muSet_localImages_add_one_le hP hZ hS hd x' y'
  omega

end Bound

end CFSG.Fischer.Classification
