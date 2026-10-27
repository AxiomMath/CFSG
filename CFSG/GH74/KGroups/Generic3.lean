module

public import CFSG.GH74.KGroups.Generic2

public section

namespace CFSG.GH74.KGroups

theorem exists_unique_ne_one_of_card_two {G : Type*} [Group G] (Z : Subgroup G)
    (h : Nat.card Z = 2) : ∃ z0 ∈ Z, z0 ≠ 1 ∧ ∀ z ∈ Z, z = 1 ∨ z = z0 := by
  obtain ⟨x, y, hxy, hs⟩ := Nat.card_eq_two_iff.1 h
  have h1 : (1 : Z) ∈ ({x, y} : Set Z) := by rw [hs]; trivial
  have hall : ∀ w : Z, w = x ∨ w = y := fun w => by
    have : w ∈ ({x, y} : Set Z) := by rw [hs]; trivial
    simpa using this
  rcases h1 with h1 | h1
  · refine ⟨(y : G), y.2, fun h => hxy ?_, fun z hz => ?_⟩
    · apply Subtype.ext
      rw [← h1, h]
      rfl
    · rcases hall ⟨z, hz⟩ with h | h
      · left; rw [← h1] at h; simpa using congrArg Subtype.val h
      · right; exact congrArg Subtype.val h
  · simp only [Set.mem_singleton_iff] at h1
    refine ⟨(x : G), x.2, fun h => hxy ?_, fun z hz => ?_⟩
    · apply Subtype.ext
      rw [← h1, h]
      rfl
    · rcases hall ⟨z, hz⟩ with h | h
      · right; exact congrArg Subtype.val h
      · left; rw [← h1] at h; simpa using congrArg Subtype.val h

theorem sq_eq_one_of_card_two {G : Type*} [Group G] (Z : Subgroup G) (h : Nat.card Z = 2)
    (z : G) (hz : z ∈ Z) : z ^ 2 = 1 := by
  have := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
  rw [h] at this
  simpa using congrArg Subtype.val this

theorem comm_eq_sq {G : Type*} [Group G] (x y z0 c : G) (hx : x ^ 2 = z0)
    (hy : y ^ 2 = z0) (hz0 : ∀ g : G, g * z0 = z0 * g) (hz0sq : z0 ^ 2 = 1)
    (hc : c = x * y * x⁻¹ * y⁻¹) : (x * y) ^ 2 = c := by
  have h1 : x * y = c * (y * x) := by rw [hc]; group
  have h2 : (x * y) ^ 2 = c * (y * x ^ 2 * y) := by
    have e1 : (x * y) ^ 2 = (x * y) * (x * y) := pow_two _
    have e2 : y * x ^ 2 * y = y * (x * x) * y := by rw [pow_two]
    rw [e1, e2]
    nth_rewrite 1 [h1]
    group
  rw [h2, hx]
  have h3 : y * z0 * y = z0 * y ^ 2 := by
    rw [hz0 y, pow_two]; group
  rw [h3, hy]
  have : z0 * z0 = 1 := by rw [← pow_two]; exact hz0sq
  rw [this, mul_one]

theorem elementary_of_transitive {K : Type*} [Group K] (A Z : Subgroup K)
    (hZc : ∀ z ∈ Z, ∀ g : K, g * z = z * g) (hZ2 : Nat.card Z = 2) (hA : 8 < Nat.card A)
    (hsq : ∀ a ∈ A, a ^ 2 ∈ Z) (s : K) (htrans : ∀ x ∈ A, x ∉ Z → ∀ y ∈ A, y ∉ Z →
      ∃ k : ℕ, ∃ z ∈ Z, s ^ k * x * (s ^ k)⁻¹ = y * z) :
    ∀ a ∈ A, a ^ 2 = 1 ∧ ∀ b ∈ A, a * b = b * a := by
  obtain ⟨z0, hz0Z, hz01, hZe⟩ := exists_unique_ne_one_of_card_two Z hZ2
  have hz0sq : z0 ^ 2 = 1 := sq_eq_one_of_card_two Z hZ2 z0 hz0Z
  have hZsq : ∀ z ∈ Z, z ^ 2 = 1 := fun z hz => sq_eq_one_of_card_two Z hZ2 z hz
  have hz0c : ∀ g : K, g * z0 = z0 * g := hZc z0 hz0Z
  have hnotZ : ∀ x : K, x ≠ 1 → x ≠ z0 → x ∉ Z := fun x h1 h2 hx => by
    rcases hZe x hx with h | h
    · exact h1 h
    · exact h2 h
  have hsame : ∀ x ∈ A, x ∉ Z → ∀ y ∈ A, y ∉ Z → x ^ 2 = y ^ 2 := by
    intro x hx hxZ y hy hyZ
    obtain ⟨k, z, hz, hk⟩ := htrans x hx hxZ y hy hyZ
    have h1 : (s ^ k * x * (s ^ k)⁻¹) ^ 2 = x ^ 2 := by
      have hc := hZc (x ^ 2) (hsq x hx) (s ^ k)
      rw [conj_pow, hc]
      group
    have h2 : (y * z) ^ 2 = y ^ 2 := by
      have hzc : z * y = y * z := (hZc z hz y).symm
      have hz2 := hZsq z hz
      calc (y * z) ^ 2 = y * (z * y) * z := by rw [pow_two]; group
        _ = y * y * (z * z) := by rw [hzc]; group
        _ = y ^ 2 := by rw [← pow_two z, hz2, mul_one, pow_two]
    rw [← h1, hk, h2]
  obtain ⟨a0, ha0A, ha0L⟩ := exists_mem_notMem_list A [1, z0] (by simp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha0L
  have ha0Z : a0 ∉ Z := hnotZ a0 ha0L.1 ha0L.2
  obtain ⟨c, hcZ, hc⟩ : ∃ c ∈ Z, ∀ x ∈ A, x ∉ Z → x ^ 2 = c :=
    ⟨a0 ^ 2, hsq a0 ha0A, fun x hx hxZ => hsame x hx hxZ a0 ha0A ha0Z⟩
  rcases hZe c hcZ with hc1 | hcz0
  ·
    have hall : ∀ a ∈ A, a ^ 2 = 1 := by
      intro a ha
      by_cases haZ : a ∈ Z
      · exact hZsq a haZ
      · rw [hc a ha haZ, hc1]
    refine fun a ha => ⟨hall a ha, fun b hb => ?_⟩
    have hinv : ∀ x ∈ A, x⁻¹ = x := fun x hx =>
      inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hall x hx)
    have h1 : (a * b)⁻¹ = a * b := hinv _ (A.mul_mem ha hb)
    rw [mul_inv_rev, hinv a ha, hinv b hb] at h1
    exact h1.symm
  · exfalso
    have hsqx : ∀ x ∈ A, x ∉ Z → x ^ 2 = z0 := fun x hx hxZ => by rw [hc x hx hxZ, hcz0]
    have hinv : ∀ x ∈ A, x ∉ Z → x⁻¹ = x * z0 := by
      intro x hx hxZ
      apply inv_eq_of_mul_eq_one_right
      calc x * (x * z0) = x ^ 2 * z0 := by rw [pow_two, mul_assoc]
        _ = 1 := by rw [hsqx x hx hxZ, ← pow_two]; exact hz0sq
    have hmul : ∀ x ∈ A, x ∉ Z → ∀ y ∈ A, y ≠ 1 → y ≠ z0 → y ≠ x → y ≠ x * z0 →
        x * y ∉ Z := by
      intro x hx hxZ y hy h1 h2 h3 h4 hxy
      rcases hZe _ hxy with h | h
      · apply h4
        have : y = x⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [this, hinv x hx hxZ]
      · apply h3
        have : y = x⁻¹ * z0 := by rw [← h]; group
        rw [this, hinv x hx hxZ, mul_assoc, ← pow_two, hz0sq, mul_one]
    obtain ⟨b, hbA, hbL⟩ := exists_mem_notMem_list A [1, z0, a0, a0 * z0] (by simp; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hbL
    obtain ⟨d, hdA, hdL⟩ := exists_mem_notMem_list A
      [1, z0, a0, a0 * z0, b, b * z0, a0 * b, a0 * b * z0] (by simp; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hdL
    have hbZ : b ∉ Z := hnotZ b hbL.1 hbL.2.1
    have hdZ : d ∉ Z := hnotZ d hdL.1 hdL.2.1
    have hab : a0 * b ∉ Z := hmul a0 ha0A ha0Z b hbA hbL.1 hbL.2.1 hbL.2.2.1 hbL.2.2.2
    have habA : a0 * b ∈ A := A.mul_mem ha0A hbA
    have had : a0 * d ∉ Z :=
      hmul a0 ha0A ha0Z d hdA hdL.1 hdL.2.1 hdL.2.2.1 hdL.2.2.2.1
    have hbd : b * d ∉ Z :=
      hmul b hbA hbZ d hdA hdL.1 hdL.2.1 hdL.2.2.2.2.1 hdL.2.2.2.2.2.1
    have habd : a0 * b * d ∉ Z :=
      hmul (a0 * b) habA hab d hdA hdL.1 hdL.2.1 hdL.2.2.2.2.2.2.1 hdL.2.2.2.2.2.2.2
    have hbdA : b * d ∈ A := A.mul_mem hbA hdA
    have hcomm_eq : ∀ y ∈ A, y ∉ Z → a0 * y ∉ Z → a0 * y * a0⁻¹ * y⁻¹ = z0 := by
      intro y hy hyZ hay
      have h := comm_eq_sq a0 y z0 (a0 * y * a0⁻¹ * y⁻¹) (hsqx a0 ha0A ha0Z) (hsqx y hy hyZ)
        hz0c hz0sq rfl
      rw [← h]
      exact hsqx _ (A.mul_mem ha0A hy) hay
    have e1 := hcomm_eq b hbA hbZ hab
    have e2 := hcomm_eq d hdA hdZ had
    have e3 := hcomm_eq (b * d) hbdA hbd (by rwa [← mul_assoc])
    have hid : a0 * (b * d) * a0⁻¹ * (b * d)⁻¹ =
        (a0 * b * a0⁻¹ * b⁻¹) * (b * (a0 * d * a0⁻¹ * d⁻¹) * b⁻¹) := by group
    rw [e1, e2, e3, hz0c b] at hid
    rw [mul_inv_cancel_right] at hid
    exact hz01 (by simpa using hid)

theorem card_comap_of_surjective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (B : Subgroup H) :
    Nat.card (B.comap f) = Nat.card B * Nat.card f.ker := by
  let g : B.comap f →* H := f.comp (B.comap f).subtype
  have hrange : g.range = B := by
    ext y
    simp only [MonoidHom.mem_range, g, MonoidHom.comp_apply, Subgroup.coe_subtype]
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hy
      obtain ⟨k, rfl⟩ := hf y
      exact ⟨⟨k, hy⟩, rfl⟩
  have hker : Nat.card g.ker = Nat.card f.ker := by
    refine Nat.card_congr ⟨fun x => ⟨x.1.1, x.2⟩, fun x => ⟨⟨x.1, ?_⟩, x.2⟩, fun x => rfl,
      fun x => rfl⟩
    rw [Subgroup.mem_comap, x.2]
    exact B.one_mem
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hrange, hker] at h
  exact h

theorem card_subtype_mem {G : Type*} [Group G] (S : Subgroup G) (q : G → Prop) :
    Nat.card {g : G // g ∈ S ∧ q g} = Nat.card {g : S // q g} :=
  Nat.card_congr ⟨fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩, fun g => ⟨g.1.1, g.1.2, g.2⟩,
    fun _ => rfl, fun _ => rfl⟩

section Sylow

variable {K G : Type*} [Group K] [Group G]

theorem card_center_of_model [Finite K] (P : Subgroup G) (e : K ≃* P) (S : Subgroup G)
    (hSP : S ≤ P) {v m : ℕ} (hS : Nat.card S = 2 ^ v) (hK : Nat.card K = 2 ^ v * m)
    (hm : Odd m) (n : ℕ)
    (hn : Nat.card {g : G // g ∈ S ∧ ∀ y ∈ S, y * g = g * y} = n) (T : Subgroup K)
    (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) :
    Nat.card ↥(T ⊓ Subgroup.centralizer (T : Set K)) = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e', he'⟩ := exists_iso_of_sylow P e S hSP hS hK hm (hT.toSylow hTi)
  have hmem : ∀ k : K, k ∈ T ↔ ((e' k : P) : G) ∈ S := fun k => he' k
  have hcent : ∀ a : K, a ∈ T ⊓ Subgroup.centralizer (T : Set K) ↔
      (a ∈ T ∧ ∀ y ∈ T, y * a = a * y) := by
    intro a
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact Iff.rfl
  rw [← hn]
  let f : ↥(T ⊓ Subgroup.centralizer (T : Set K)) →
      {g : G // g ∈ S ∧ ∀ y ∈ S, y * g = g * y} := fun a =>
    ⟨((e' a.1 : P) : G), (hmem a.1).1 ((hcent a.1).1 a.2).1,
      (iso_central e' hSP hmem).1 ((hcent a.1).1 a.2).2⟩
  refine Nat.card_eq_of_bijective f ⟨?_, ?_⟩
  · intro a b hab
    have h1 : ((e' a.1 : P) : G) = ((e' b.1 : P) : G) :=
      congrArg (fun z : {g : G // g ∈ S ∧ ∀ y ∈ S, y * g = g * y} => z.1) hab
    exact Subtype.ext (e'.injective (Subtype.ext h1))
  · rintro ⟨g, hgS, hgc⟩
    obtain ⟨k, hkT, hk⟩ := iso_symm_mem e' hSP hmem hgS
    have hkc : ∀ y ∈ T, y * k = k * y :=
      (iso_central e' hSP hmem).2 (by rw [hk]; exact hgc)
    exact ⟨⟨k, (hcent k).2 ⟨hkT, hkc⟩⟩, Subtype.ext hk⟩

end Sylow

end CFSG.GH74.KGroups
