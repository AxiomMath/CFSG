module

public import CFSG.Fischer.Classification.PartII.Twins.Fourth

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin LocalR3

namespace O2G

theorem even_ncard_of_involution {α : Type*} {s : Set α} (hs : s.Finite) (σ : α → α)
    (hmaps : ∀ x ∈ s, σ x ∈ s) (hinv : ∀ x ∈ s, σ (σ x) = x) (hfree : ∀ x ∈ s, σ x ≠ x) :
    Even s.ncard := by
  obtain ⟨n, hn⟩ : ∃ n, s.ncard = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · rw [Set.ncard_empty]
      exact ⟨0, rfl⟩
    · have hσx := hmaps x hx
      have hne := hfree x hx
      have hsub : ({x, σ x} : Set α) ⊆ s := by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact hx
        · exact hσx
      have h2 : ({x, σ x} : Set α).ncard = 2 := Set.ncard_pair hne.symm
      have hle : 2 ≤ n := hn ▸ h2 ▸ Set.ncard_le_ncard hsub hs
      have hcard : (s \ {x, σ x}).ncard = n - 2 := by
        rw [Set.ncard_sdiff hsub, h2, hn]
      have hmaps' : ∀ y ∈ s \ {x, σ x}, σ y ∈ s \ {x, σ x} := by
        rintro y ⟨hys, hyn⟩
        have hyx : y ≠ x := fun e => hyn (by simp [e])
        have hyσ : y ≠ σ x := fun e => hyn (by simp [e])
        refine ⟨hmaps y hys, fun hm => ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
        rcases hm with e | e
        · exact hyσ (by rw [← hinv y hys, e])
        · exact hyx (by rw [← hinv y hys, e, hinv x hx])
      have hrest := ih ((s \ {x, σ x}).ncard) (by omega) (s := s \ {x, σ x})
        (hs.subset Set.sdiff_subset) hmaps' (fun y hy => hinv y hy.1) (fun y hy => hfree y hy.1)
        rfl
      rw [hcard] at hrest
      obtain ⟨m, hm⟩ := hrest
      rw [hn]
      exact ⟨m + 1, by omega⟩

variable {G : Type} [Group G] {D : Set G}

theorem conj_mul_ne_self (hP : Pair G D) {a b x : G} (ha : a ∈ D) (hb : b ∈ D) (hx : x ∈ D)
    (hne : a ≠ b) (hab : a * b = b * a) (hxa : x * a ≠ a * x) (hxb : x * b ≠ b * x) :
    a * b * x * (a * b) ≠ x := by
  intro h
  rw [mul_mul_mul_mul_eq hab] at h
  have h1 : b * x * b = a * x * a := by
    rw [← Pair.mul_mul_mul_mul hP ha (b * x * b), h]
  have h2 : x * b * x = x * a * x := by
    rw [← Pair.mul_mul_eq hP hb hx fun e => hxb e.symm,
      ← Pair.mul_mul_eq hP ha hx fun e => hxa e.symm, h1]
  exact hne (mul_left_cancel (mul_right_cancel h2)).symm

theorem conj_mul_commute (hP : Pair G D) {a b x : G} (ha : a ∈ D) (hb : b ∈ D) (hx : x ∈ D)
    (hab : a * b = b * a) (hxa : x * a ≠ a * x) (hxb : x * b ≠ b * x) :
    a * b * x * (a * b) * x = x * (a * b * x * (a * b)) := by
  have hxx := Pair.mul_self hP hx
  have hu : b * x * b * (a * x * a) = a * x * a * (b * x * b) := by
    rw [Pair.mul_mul_eq hP hb hx fun e => hxb e.symm,
      Pair.mul_mul_eq hP ha hx fun e => hxa e.symm]
    calc x * b * x * (x * a * x) = x * b * (x * x) * a * x := by simp only [mul_assoc]
      _ = x * (b * a) * x := by rw [hxx, mul_one]; simp only [mul_assoc]
      _ = x * (a * b) * x := by rw [hab]
      _ = x * a * (x * x) * b * x := by rw [hxx, mul_one]; simp only [mul_assoc]
      _ = x * a * x * (x * b * x) := by simp only [mul_assoc]
  have h := (conj_commute_iff a (b * x * b) (a * x * a)).2 hu
  rw [Pair.inv_eq hP ha, Pair.mul_mul_mul_mul hP ha x] at h
  rw [mul_mul_mul_mul_eq hab]
  exact h

theorem exists_isTwin_ne (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) (hna : NonabelianCommutator G) {d : G} (hd : d ∈ D)
    (h2 : HasNormalPSubgroup 2 (LocalQuotient D d)) :
    ∃ a b : G, IsTwin (LocalClass D d) a b ∧ a ≠ b := by
  have hPH := Pair.pair_localQuotient hP hZ hS hna hd
  have hZH := Pair.center_localQuotient hP hZ hS hd
  obtain ⟨x, y, hxy, hne⟩ := Pair.exists_isTwin_ne hPH hZH h2
  have hch := Pair.isChart_lqMap hP (Pair.starImage_injective_of_simple hP hZ hS hd)
  have hx : x ∈ lqMap D d '' LocalClass D d := by rw [hch.image_eq]; exact hxy.1
  have hy : y ∈ lqMap D d '' LocalClass D d := by rw [hch.image_eq]; exact hxy.2.1
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a, b, (isChart_isTwin_iff hch ha hb).1 hxy, fun e => hne (by rw [e])⟩

theorem conj_eq_of_mem_centralizer {d h : G} (hh : h ∈ Subgroup.centralizer ({d} : Set G)) :
    h * d * h⁻¹ = d := by
  rw [Subgroup.mem_centralizer_singleton_iff.1 hh, mul_inv_cancel_right]

theorem ncard_twinClass_le (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {d f g : G} (hd : d ∈ D) (hf : f ∈ LocalClass D d)
    (hg : g ∈ LocalClass D d) :
    (twinClass (LocalClass D d) f).ncard ≤ (twinClass (LocalClass D d) g).ncard := by
  have := Pair.finite hP
  obtain ⟨h, hh, hhg⟩ := Pair.exists_centralizer_conj_localClass hP hZ hS hd hf hg
  rw [← Set.ncard_image_of_injective _ (conj_injective h)]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro _ ⟨x, hx, rfl⟩
  have h' := LocalU.isTwin_conj hP h hx
  rwa [conj_eq_of_mem_centralizer hh, hhg] at h'

theorem ncard_twinClass_eq (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {d f g : G} (hd : d ∈ D) (hf : f ∈ LocalClass D d)
    (hg : g ∈ LocalClass D d) :
    (twinClass (LocalClass D d) f).ncard = (twinClass (LocalClass D d) g).ncard :=
  le_antisymm (ncard_twinClass_le hP hZ hS hd hf hg) (ncard_twinClass_le hP hZ hS hd hg hf)

theorem isTwin_conj_mul (hP : Pair G D) {d a a' b : G} (h : IsTwin (LocalClass D d) a a')
    (hb : b ∈ LocalClass D d) (hab : a * b ≠ b * a) :
    IsTwin (LocalClass D d) b (a * a' * b * (a * a')) := by
  have hbd : b * d * b⁻¹ = d := by
    rw [hb.2.2, mul_inv_cancel_right]
  have had : a * d * a⁻¹ = d := by
    rw [h.1.2.2, mul_inv_cancel_right]
  have hba' : b * a' ≠ a' * b := fun e => hab ((h.2.2.2 b hb).2 e).symm
  have h1 := LocalU.isTwin_conj hP b h
  rw [hbd, Pair.inv_eq hP hb.1, ← Pair.mul_mul_eq hP h.1.1 hb.1 hab,
    ← Pair.mul_mul_eq hP h.2.1.1 hb.1 fun e => hba' e.symm] at h1
  have h2 := LocalU.isTwin_conj hP a h1
  rwa [had, Pair.inv_eq hP h.1.1, Pair.mul_mul_mul_mul hP h.1.1,
    ← mul_mul_mul_mul_eq h.2.2.1] at h2

theorem even_ncard_twinClass (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {d a a' f : G} (hd : d ∈ D)
    (h : IsTwin (LocalClass D d) a a') (hne : a ≠ a') (hf : f ∈ LocalClass D d) :
    Even (twinClass (LocalClass D d) f).ncard := by
  have := Pair.finite hP
  obtain ⟨b, hb, hba⟩ := Pair.exists_not_commute_of_mem_localClass hP hZ hS hd h.1
  rw [ncard_twinClass_eq hP hZ hS hd hf hb]
  have hab : a * b ≠ b * a := fun e => hba e.symm
  have hk : a * a' * (a * a') = 1 := mul_mul_mul_self hP h.1.1 h.2.1.1 h.2.2.1
  have hkinv : (a * a')⁻¹ = a * a' := inv_eq_of_mul_eq_one_right hk
  refine even_ncard_of_involution (Set.toFinite _) (fun x => a * a' * x * (a * a'))
    (fun x hx => ?_) (fun x _ => conj_conj_of_mul_self hk x) (fun x hx => ?_)
  · have h1 := LocalU.isTwin_conj hP (a * a') hx
    have e : a * a' * d = d * (a * a') := by
      rw [mul_assoc, h.2.1.2.2, ← mul_assoc, h.1.2.2, mul_assoc]
    have hkd : a * a' * d * (a * a')⁻¹ = d := by
      rw [e, mul_inv_cancel_right]
    rw [hkd, hkinv] at h1
    exact isTwin_trans (isTwin_conj_mul hP h hb hab) h1
  · have hxa : x * a ≠ a * x := fun e => hab ((hx.2.2.2 a h.1).2 e.symm)
    have hxa' : x * a' ≠ a' * x := by
      have hba' : a' * b ≠ b * a' := fun e => hab (((h.2.2.2 b hb).2 e.symm).symm)
      exact fun e => hba' ((hx.2.2.2 a' h.2.1).2 e.symm)
    exact conj_mul_ne_self hP h.1.1 h.2.1.1 hx.2.1.1 hne h.2.2.1 hxa hxa'

end O2G

end CFSG.Fischer.Classification
