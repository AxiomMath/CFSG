module

public import CFSG.Fischer.Classification.Basic.Transitivity

public section

namespace CFSG.LargeExtraspecial.AS35J

open Subgroup CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification

section Pair

variable {X : Type} [Group X] {E : Set X}

theorem exists_commute_not_commute_of_pair (hP : Pair X E) (hZ : center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) {a b : X} (ha : a ∈ E) (hb : b ∈ E) (hne : a ≠ b) :
    ∃ c ∈ E, c * a = a * c ∧ c * b ≠ b * c := by
  have := Pair.finite hP
  by_contra! hall
  obtain ⟨g, hg⟩ := isConj_iff.mp (Pair.isConj hP ha hb)
  have hsub : {w | w ∈ E ∧ w * a = a * w} ⊆ {w | w ∈ E ∧ w * b = b * w} :=
    fun w hw => ⟨hw.1, hall w hw.1 hw.2⟩
  have himg : {w | w ∈ E ∧ w * b = b * w} ⊆
      (fun w => g * w * g⁻¹) '' {w | w ∈ E ∧ w * a = a * w} := by
    rintro w ⟨hwE, hwb⟩
    refine ⟨g⁻¹ * w * g, ⟨by simpa using Pair.conj_mem hP hwE g⁻¹, ?_⟩, by group⟩
    calc g⁻¹ * w * g * a = g⁻¹ * (w * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * w) * g := by rw [hg, hwb]
      _ = a * (g⁻¹ * w * g) := by group
  have hcard : {w | w ∈ E ∧ w * b = b * w}.ncard ≤ {w | w ∈ E ∧ w * a = a * w}.ncard :=
    (Set.ncard_le_ncard himg (Set.toFinite _)).trans Set.ncard_image_le
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  apply hne
  refine Pair.eq_of_forall_commute_iff hP hZ hS ha hb fun w hw => ⟨hall w hw, fun hwb => ?_⟩
  have h1 : w ∈ {w | w ∈ E ∧ w * b = b * w} := ⟨hw, hwb⟩
  rw [← heq] at h1
  exact h1.2

theorem exists_commute_both_of_pair (hP : Pair X E) (hS : IsSimpleGroup (commutator X))
    (hna : ∃ x y : commutator X, x * y ≠ y * x) {a b : X} (ha : a ∈ E) (hb : b ∈ E)
    (hab : b * a ≠ a * b) : ∃ c ∈ E, c * a = a * c ∧ c * b = b * c := by
  obtain ⟨c, hca, hcb⟩ := CFSG.Fischer.Pair.muSet_nonempty hP
    (Pair.connected_of_nonabelian hP hS hna) ha hb hab
  exact ⟨c, hca.1, hca.2.2, hcb.2.2⟩

end Pair

section Lift

variable {L : Type} [Group L] {D : Set L}

theorem commute_of_orderOf_mul_le_two {c a : L} (hc : c * c = 1) (ha : a * a = 1)
    (h : orderOf (c * a) = 1 ∨ orderOf (c * a) = 2) : c * a = a * c := by
  have h2 : (c * a) * (c * a) = 1 := by
    rcases h with h | h
    · rw [orderOf_eq_one_iff.mp h, one_mul]
    · rw [← pow_two, ← h]
      exact pow_orderOf_eq_one _
  calc c * a = (c * a)⁻¹ := (inv_eq_of_mul_eq_one_right h2).symm
    _ = a * c := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hc]

theorem commute_or_mk_eq_of_mk_commute (hinv : ∀ a ∈ D, a * a = 1)
    (h3 : ∀ a ∈ D, ∀ b ∈ D, orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ)) {c a : L} (hc : c ∈ D)
    (ha : a ∈ D)
    (h : (QuotientGroup.mk c : L ⧸ center L) * QuotientGroup.mk a =
      QuotientGroup.mk a * QuotientGroup.mk c) :
    c * a = a * c ∨ (QuotientGroup.mk c : L ⧸ center L) = QuotientGroup.mk a := by
  rcases h3 c hc a ha with h1 | h1 | h1
  · exact Or.inl (commute_of_orderOf_mul_le_two (hinv c hc) (hinv a ha) (Or.inl h1))
  · exact Or.inl (commute_of_orderOf_mul_le_two (hinv c hc) (hinv a ha) (Or.inr h1))
  · right
    set x : L ⧸ center L := QuotientGroup.mk c * QuotientGroup.mk a with hx
    have hcc : (QuotientGroup.mk c : L ⧸ center L) * QuotientGroup.mk c = 1 := by
      rw [← QuotientGroup.mk_mul, hinv c hc, QuotientGroup.mk_one]
    have haa : (QuotientGroup.mk a : L ⧸ center L) * QuotientGroup.mk a = 1 := by
      rw [← QuotientGroup.mk_mul, hinv a ha, QuotientGroup.mk_one]
    have hx3 : x ^ 3 = 1 := by
      rw [hx, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, ← h1, pow_orderOf_eq_one,
        QuotientGroup.mk_one]
    have hx2 : x ^ 2 = 1 := by
      rw [hx, pow_two, mul_assoc, ← mul_assoc (QuotientGroup.mk a), ← h, mul_assoc, haa,
        mul_one, hcc]
    have hx1 : x = 1 := by
      calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
        _ = 1 := by rw [hx3, hx2, inv_one, one_mul]
    calc (QuotientGroup.mk c : L ⧸ center L) =
        QuotientGroup.mk c * (QuotientGroup.mk a * QuotientGroup.mk a) := by rw [haa, mul_one]
      _ = x * QuotientGroup.mk a := by rw [hx, mul_assoc]
      _ = QuotientGroup.mk a := by rw [hx1, one_mul]

theorem transvection_props_of_quotient [Finite L] (hgen : closure D = ⊤) (hne : D.Nonempty)
    (hcls : ∀ a ∈ D, ∀ b ∈ D, ∃ g : L, g * a * g⁻¹ = b)
    (hDc : ∀ g : L, ∀ a ∈ D, g * a * g⁻¹ ∈ D) (hinv : ∀ a ∈ D, a * a = 1)
    (h3 : ∀ a ∈ D, ∀ b ∈ D, orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ))
    (hZ : center (L ⧸ center L) = ⊥) (hS : IsSimpleGroup (commutator (L ⧸ center L)))
    (hna : ∃ x y : commutator (L ⧸ center L), x * y ≠ y * x) :
    (∀ a ∈ D, ∀ b ∈ D, a * b = b * a → a ≠ b → ∃ c ∈ D, c * a = a * c ∧ c * b ≠ b * c) ∧
      (∀ a ∈ D, ∀ b ∈ D, orderOf (a * b) = 3 → ∃ c ∈ D, c * a = a * c ∧ c * b = b * c) := by
  obtain ⟨a₀, ha₀⟩ := hne
  let π : L →* L ⧸ center L := QuotientGroup.mk' (center L)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hnc : ¬ ∀ x y : L ⧸ center L, x * y = y * x := by
    intro h
    obtain ⟨x, y, hxy⟩ := hna
    exact hxy (Subtype.ext (h x y))
  have hgen' : closure (π '' D) = ⊤ := by
    rw [← MonoidHom.map_closure, hgen]
    exact map_top_of_surjective _ hπs
  have hclass' : ∃ d₀ : L ⧸ center L, π '' D = {g | IsConj d₀ g} := by
    refine ⟨π a₀, Set.ext fun x => ⟨?_, ?_⟩⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨g, hg⟩ := hcls a₀ ha₀ a ha
      exact isConj_iff.mpr ⟨π g, by rw [← hg, map_mul, map_mul, map_inv]⟩
    · intro hx
      obtain ⟨c, rfl⟩ := isConj_iff.mp hx
      obtain ⟨g, rfl⟩ := hπs c
      exact ⟨g * a₀ * g⁻¹, hDc g a₀ ha₀, by rw [map_mul, map_mul, map_inv]⟩
  have hinv' : ∀ d ∈ π '' D, orderOf d = 2 := by
    rintro _ ⟨a, ha, rfl⟩
    refine orderOf_eq_prime (by rw [pow_two, ← map_mul, hinv a ha, map_one]) fun h1 => hnc ?_
    have hle : closure (π '' D) ≤ ⊥ := by
      rw [closure_le]
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨g, hg⟩ := hcls a ha b hb
      rw [SetLike.mem_coe, mem_bot, ← hg, map_mul, map_mul, h1, mul_one, ← map_mul,
        mul_inv_cancel, map_one]
    have hone : ∀ x : L ⧸ center L, x = 1 := fun x => mem_bot.mp (hle (hgen' ▸ mem_top x))
    intro x y
    rw [hone x, hone y]
  have h3' : ∀ d ∈ π '' D, ∀ e ∈ π '' D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have hdvd : orderOf (π a * π b) ∣ orderOf (a * b) := by
      rw [← map_mul]
      exact orderOf_map_dvd π (a * b)
    rcases h3 a ha b hb with h | h | h <;> rw [h] at hdvd
    · exact Or.inl (Nat.dvd_one.mp hdvd)
    · rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h' <;> simp [h']
    · rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h' | h' <;> simp [h']
  have hP : Pair (L ⧸ center L) (π '' D) := ⟨inferInstance, hclass', hinv', h3', hgen'⟩
  have himg : ∀ a ∈ D, π a ∈ π '' D := fun a ha => ⟨a, ha, rfl⟩
  have hπc : ∀ x y : L, x * y = y * x → π x * π y = π y * π x := by
    intro x y h
    rw [← map_mul, h, map_mul]
  obtain ⟨d, hd, e, he, hde⟩ : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 3 := by
    by_contra! hall
    have hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
      intro x hx y hy
      rcases h3 x hx y hy with h | h | h
      · exact commute_of_orderOf_mul_le_two (hinv x hx) (hinv y hy) (Or.inl h)
      · exact commute_of_orderOf_mul_le_two (hinv x hx) (hinv y hy) (Or.inr h)
      · exact absurd h (hall x hx y hy)
    apply hnc
    have hc1 : closure D ≤ centralizer D := by
      rw [closure_le]
      intro x hx
      rw [SetLike.mem_coe, mem_centralizer_iff]
      intro y hy
      exact hcomm y hy x hx
    rw [← centralizer_closure, hgen] at hc1
    intro x y
    obtain ⟨x, rfl⟩ := hπs x
    obtain ⟨y, rfl⟩ := hπs y
    rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp (hc1 (mem_top x)) y (mem_top y))]
  have htwin : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a → a ≠ b → π a ≠ π b := by
    intro a ha b hb hab hne heq
    have hu : a⁻¹ * b ∈ center L := QuotientGroup.eq.mp heq
    have hu1 : a⁻¹ * b ≠ 1 := fun h => hne (inv_mul_eq_one.mp h)
    have hu2 : (a⁻¹ * b) ^ 2 = 1 := by
      rw [pow_two, inv_eq_of_mul_eq_one_right (hinv a ha)]
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab]
        _ = 1 := by rw [← mul_assoc, hinv a ha, one_mul, hinv b hb]
    obtain ⟨g, hg⟩ := hcls a ha e he
    have heu : e * (a⁻¹ * b) ∈ D := by
      have h1 := hDc g b hb
      have h2 : g * b * g⁻¹ = e * (a⁻¹ * b) := by
        calc g * b * g⁻¹ = g * a * ((a⁻¹ * b) * g⁻¹) := by group
          _ = g * a * (g⁻¹ * (a⁻¹ * b)) := by rw [mem_center_iff.mp hu g⁻¹]
          _ = (g * a * g⁻¹) * (a⁻¹ * b) := by group
          _ = e * (a⁻¹ * b) := by rw [hg]
      rwa [h2] at h1
    have hcomm : Commute (d * e) (a⁻¹ * b) := mem_center_iff.mp hu (d * e)
    have h6 : orderOf (d * (e * (a⁻¹ * b))) = 6 := by
      rw [← mul_assoc, hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by
        rw [hde, orderOf_eq_prime hu2 hu1]; norm_num), hde, orderOf_eq_prime hu2 hu1]
    have h7 := h3 d hd _ heu
    rw [h6] at h7
    simp at h7
  have hnc3 : ∀ x ∈ D, ∀ y ∈ D, orderOf (x * y) = 3 → π x ≠ π y →
      π y * π x ≠ π x * π y := by
    intro x hx y hy hxy hne h
    rcases commute_or_mk_eq_of_mk_commute hinv h3 hx hy h.symm with h' | h'
    · have h2 : orderOf (x * y) ∣ 2 := by
        apply orderOf_dvd_of_pow_eq_one
        rw [pow_two, mul_assoc, ← mul_assoc y, ← h', mul_assoc, hinv y hy, mul_one, hinv x hx]
      rw [hxy] at h2
      norm_num at h2
    · exact hne h'
  refine ⟨fun a ha b hb hab hne => ?_, fun a ha b hb hab3 => ?_⟩
  · obtain ⟨r, ⟨c, hc, rfl⟩, hra, hrb⟩ := exists_commute_not_commute_of_pair hP hZ hS
      (himg a ha) (himg b hb) (htwin a ha b hb hab hne)
    refine ⟨c, hc, ?_, fun h => hrb (hπc _ _ h)⟩
    rcases commute_or_mk_eq_of_mk_commute hinv h3 hc ha hra with h | h
    · exact h
    · exfalso
      apply hrb
      rw [show π c = π a from h]
      exact hπc _ _ hab
  · by_cases heq : π a = π b
    · refine ⟨a, ha, rfl, ?_⟩
      have hu : a⁻¹ * b ∈ center L := QuotientGroup.eq.mp heq
      calc a * b = a * (a * (a⁻¹ * b)) := by group
        _ = a * ((a⁻¹ * b) * a) := by rw [mem_center_iff.mp hu a]
        _ = b * a := by group
    · obtain ⟨r, ⟨c, hc, rfl⟩, hra, hrb⟩ := exists_commute_both_of_pair hP hS hna (himg a ha)
        (himg b hb) (hnc3 a ha b hb hab3 heq)
      refine ⟨c, hc, ?_, ?_⟩
      · rcases commute_or_mk_eq_of_mk_commute hinv h3 hc ha hra with h | h
        · exact h
        · exfalso
          apply hnc3 a ha b hb hab3 heq
          rw [← show π c = π a from h]
          exact hrb.symm
      · rcases commute_or_mk_eq_of_mk_commute hinv h3 hc hb hrb with h | h
        · exact h
        · exfalso
          apply hnc3 a ha b hb hab3 heq
          rw [← show π c = π b from h]
          exact hra

end Lift

end CFSG.LargeExtraspecial.AS35J
