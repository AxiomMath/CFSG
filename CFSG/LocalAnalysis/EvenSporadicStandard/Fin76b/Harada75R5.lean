module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Cfg
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75L4

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

theorem IsElemAbelian.comm_of_mem {G : Type} [Group G] {H : Subgroup G} (hH : IsElemAbelian 2 H)
    {x y : G} (hx : x ∈ H) (hy : y ∈ H) : x * y = y * x :=
  congrArg Subtype.val (hH.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem IsElemAbelian.sq_eq_one {G : Type} [Group G] {H : Subgroup G} (hH : IsElemAbelian 2 H)
    {x : G} (hx : x ∈ H) : x * x = 1 := by
  rw [← pow_two]
  exact hH.2 x hx

theorem exists_nontriv_of_card_two {S : Type} [Group S] (C : Subgroup S) (h : Nat.card C = 2) :
    ∃ ℓ : S, ℓ ∈ C ∧ ℓ ≠ 1 ∧ ∀ x ∈ C, x = 1 ∨ x = ℓ := by
  obtain ⟨p, q, hpq, hall⟩ := Nat.card_eq_two_iff.mp h
  have hmem : ∀ x : C, x = p ∨ x = q := fun x => by
    have hx : x ∈ ({p, q} : Set C) := by rw [hall]; exact Set.mem_univ x
    simpa using hx
  rcases hmem 1 with h1 | h1
  · have hp1 : p.1 = 1 := by rw [← h1]; rfl
    refine ⟨q.1, q.2, fun hq => hpq (Subtype.ext (hp1.trans hq.symm)), fun x hx => ?_⟩
    rcases hmem ⟨x, hx⟩ with h2 | h2
    · exact Or.inl ((congrArg Subtype.val h2).trans hp1)
    · exact Or.inr (congrArg Subtype.val h2)
  · have hq1 : q.1 = 1 := by rw [← h1]; rfl
    refine ⟨p.1, p.2, fun hp => hpq (Subtype.ext (hp.trans hq1.symm)), fun x hx => ?_⟩
    rcases hmem ⟨x, hx⟩ with h2 | h2
    · exact Or.inr (congrArg Subtype.val h2)
    · exact Or.inl ((congrArg Subtype.val h2).trans hq1)

theorem card_inf_ge_two {S : Type} [Group S] [Finite S] {X Y E : Subgroup S} (hXE : X ≤ E)
    (hYE : Y ≤ E) (hX : Nat.card X = 4) (hY : Nat.card Y = 4) (hE : Nat.card E = 8) :
    2 ≤ Nat.card (X ⊓ Y : Subgroup S) := by
  have hXY : X ⊓ Y ≤ E := inf_le_left.trans hXE
  have h1 : (X ⊓ Y).relIndex E * Nat.card ((X ⊓ Y) ⊓ E : Subgroup S) = Nat.card E :=
    Subgroup.relIndex_mul_card (H := X ⊓ Y) (K := E)
  rw [inf_of_le_left hXY, hE] at h1
  have h2 : X.relIndex E * Nat.card (X ⊓ E : Subgroup S) = Nat.card E :=
    Subgroup.relIndex_mul_card (H := X) (K := E)
  rw [inf_of_le_left hXE, hX, hE] at h2
  have h3 : Y.relIndex E * Nat.card (Y ⊓ E : Subgroup S) = Nat.card E :=
    Subgroup.relIndex_mul_card (H := Y) (K := E)
  rw [inf_of_le_left hYE, hY, hE] at h3
  have h4 : (X ⊓ Y).relIndex E ≤ X.relIndex E * Y.relIndex E :=
    Subgroup.relIndex_inf_le (H := X) (K := Y) (L := E)
  have hr2 : X.relIndex E = 2 := by omega
  have hr2' : Y.relIndex E = 2 := by omega
  rw [hr2, hr2'] at h4
  by_contra hcon
  have hm1 : Nat.card (X ⊓ Y : Subgroup S) ≤ 1 := by omega
  have hmul : (X ⊓ Y).relIndex E * Nat.card (X ⊓ Y : Subgroup S) ≤ (X ⊓ Y).relIndex E * 1 :=
    Nat.mul_le_mul_left _ hm1
  omega

theorem inf_le_of_cards {S : Type} [Group S] [Finite S] {A B E : Subgroup S}
    (hAB2 : Nat.card (A ⊓ B : Subgroup S) = 2) (hAE : Nat.card (A ⊓ E : Subgroup S) = 4)
    (hBE : Nat.card (B ⊓ E : Subgroup S) = 4) (hE : Nat.card E = 8) : A ⊓ B ≤ E := by
  have hXY : (A ⊓ E) ⊓ (B ⊓ E) ≤ A ⊓ B := inf_le_inf inf_le_left inf_le_left
  have hcard := card_inf_ge_two (X := A ⊓ E) (Y := B ⊓ E) (E := E) inf_le_right inf_le_right
    hAE hBE hE
  have heq : (A ⊓ E) ⊓ (B ⊓ E) = A ⊓ B :=
    Subgroup.eq_of_le_of_card_ge hXY (by omega)
  rw [← heq]
  exact inf_le_left.trans inf_le_right

theorem coords_sub {S : Type} [Group S] [Finite S] {A : Subgroup S} (hA : IsElemAbelian 2 A)
    (hA8 : Nat.card A = 8) {p q r : S} (hp : p ∈ A) (hq : q ∈ A) (hr : r ∈ A)
    (hp1 : p ≠ 1) (hq1 : q ≠ 1) (hqp : q ≠ p) (hr1 : r ≠ 1) (hrp : r ≠ p) (hrq : r ≠ q)
    (hrpq : r ≠ p * q) :
    ∀ x ∈ A, x = 1 ∨ x = p ∨ x = q ∨ x = p * q ∨ x = r ∨ x = p * r ∨ x = q * r ∨
      x = p * (q * r) := by
  intro x hx
  have hc : ∀ u v : A, u * v = v * u := fun u v =>
    Subtype.ext (IsElemAbelian.comm_of_mem hA u.2 v.2)
  have hcoords := coords_of_card hc hA8 (⟨p, hp⟩ : A) ⟨q, hq⟩ ⟨r, hr⟩
    (fun h => hp1 (congrArg Subtype.val h)) (Subtype.ext (IsElemAbelian.sq_eq_one hA hp))
    (Subtype.ext (IsElemAbelian.sq_eq_one hA hq)) (fun h => hq1 (congrArg Subtype.val h))
    (fun h => hqp (congrArg Subtype.val h)) (fun h => hr1 (congrArg Subtype.val h))
    (fun h => hrp (congrArg Subtype.val h)) (fun h => hrq (congrArg Subtype.val h))
    (fun h => hrpq (congrArg Subtype.val h))
  rcases hcoords ⟨x, hx⟩ with h | h | h | h | h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (congrArg Subtype.val h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (congrArg Subtype.val h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))))))

theorem commute_of_coords {S : Type} [Group S] {g p q r x : S} (hp : g * p = p * g)
    (hq : g * q = q * g) (hr : g * r = r * g)
    (hx : x = 1 ∨ x = p ∨ x = q ∨ x = p * q ∨ x = r ∨ x = p * r ∨ x = q * r ∨ x = p * (q * r)) :
    g * x = x * g := by
  have hp' : Commute g p := hp
  have hq' : Commute g q := hq
  have hr' : Commute g r := hr
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Commute.one_right g
  · exact hp'
  · exact hq'
  · exact hp'.mul_right hq'
  · exact hr'
  · exact hp'.mul_right hr'
  · exact hq'.mul_right hr'
  · exact hp'.mul_right (hq'.mul_right hr')

theorem exists_F_of_invol {S : Type} [Group S] {x y : S} (hxy : x * y = y * x) (hx : x * x = 1)
    (hy : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy1 : x * y ≠ 1) :
    ∃ F : Subgroup S, (∀ f : S, f ∈ F ↔ f = 1 ∨ f = x ∨ f = y ∨ f = x * y) ∧
      IsElemAbelian 2 F ∧ Nat.card F = 4 := by
  have hxy' : Commute x y := hxy
  have hsq : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx, hy, one_mul]
  have hmul : ∀ a b : S, (a = 1 ∨ a = x ∨ a = y ∨ a = x * y) →
      (b = 1 ∨ b = x ∨ b = y ∨ b = x * y) → (a * b = 1 ∨ a * b = x ∨ a * b = y ∨ a * b = x * y) := by
    rintro a b (ha | ha | ha | ha) (hb | hb | hb | hb) <;> rw [ha, hb]
    · exact Or.inl (mul_one 1)
    · exact Or.inr (Or.inl (one_mul x))
    · exact Or.inr (Or.inr (Or.inl (one_mul y)))
    · exact Or.inr (Or.inr (Or.inr (one_mul (x * y))))
    · exact Or.inr (Or.inl (mul_one x))
    · exact Or.inl hx
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, hx, one_mul])))
    · exact Or.inr (Or.inr (Or.inl (mul_one y)))
    · exact Or.inr (Or.inr (Or.inr hxy.symm))
    · exact Or.inl hy
    · exact Or.inr (Or.inl (by rw [← mul_assoc, ← hxy, mul_assoc, hy, mul_one]))
    · exact Or.inr (Or.inr (Or.inr (mul_one (x * y))))
    · exact Or.inr (Or.inr (Or.inl (by rw [mul_assoc, ← hxy, ← mul_assoc, hx, one_mul])))
    · exact Or.inr (Or.inl (by rw [mul_assoc, hy, mul_one]))
    · exact Or.inl hsq
  have hinv : ∀ a : S, (a = 1 ∨ a = x ∨ a = y ∨ a = x * y) →
      (a⁻¹ = 1 ∨ a⁻¹ = x ∨ a⁻¹ = y ∨ a⁻¹ = x * y) := by
    rintro a (ha | ha | ha | ha) <;> rw [ha]
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hx))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hy)))
    · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right hsq)))
  let F : Subgroup S :=
    { carrier := {f | f = 1 ∨ f = x ∨ f = y ∨ f = x * y}
      mul_mem' := fun {a b} ha hb => hmul a b ha hb
      one_mem' := Or.inl rfl
      inv_mem' := fun {a} ha => hinv a ha }
  have hmemF : ∀ f : S, f ∈ F ↔ f = 1 ∨ f = x ∨ f = y ∨ f = x * y := fun f => Iff.rfl
  have hcommT : ∀ a b : S, (a = 1 ∨ a = x ∨ a = y ∨ a = x * y) →
      (b = 1 ∨ b = x ∨ b = y ∨ b = x * y) → a * b = b * a := by
    rintro a b (ha | ha | ha | ha) (hb | hb | hb | hb) <;> rw [ha, hb]
    all_goals first
      | exact Commute.one_left _
      | exact Commute.one_right _
      | exact Commute.refl _
      | exact hxy'
      | exact hxy'.symm
      | exact (Commute.refl x).mul_right hxy'
      | exact hxy'.symm.mul_right (Commute.refl y)
      | exact (Commute.refl x).mul_left hxy'.symm
      | exact hxy'.mul_left (Commute.refl y)
  have hcomF : IsMulCommutative F :=
    ⟨⟨fun u v => Subtype.ext (hcommT _ _ ((hmemF _).mp u.2) ((hmemF _).mp v.2))⟩⟩
  have hset : (F : Set S) = ({1, x, y, x * y} : Set S) := by
    ext f
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hmemF f
  have e1 : (1 : S) ∉ ({x, y, x * y} : Set S) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hx1.symm, hy1.symm, hxy1.symm⟩
  have hxy_ne : x ≠ y := fun h => hxy1 (by rw [h]; exact hy)
  have e2 : x ∉ ({y, x * y} : Set S) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxy_ne, fun h => hy1 (mul_left_cancel ((mul_one x).trans h)).symm⟩
  have e3 : y ≠ x * y := fun h => hx1 (mul_right_cancel ((one_mul y).trans h)).symm
  have hcard : Nat.card F = 4 := by
    have h1 : Nat.card F = (F : Set S).ncard := Nat.card_coe_set_eq (F : Set S)
    rw [h1, hset, Set.ncard_insert_of_notMem e1, Set.ncard_insert_of_notMem e2,
      Set.ncard_pair e3]
  refine ⟨F, hmemF, ⟨hcomF, fun f hf => ?_⟩, hcard⟩
  rw [pow_two]
  rcases (hmemF f).mp hf with h | h | h | h <;> rw [h]
  · exact mul_one 1
  · exact hx
  · exact hy
  · exact hsq

theorem eq_of_comm_one {G : Type} [Group G] {x y : G} (h : x * y * x⁻¹ * y⁻¹ = 1) :
    x * y = y * x := by
  have h' := mul_inv_eq_one.mp h
  calc x * y = x * y * x⁻¹ * x := by group
    _ = y * x := by rw [h']

theorem eq_of_comm_eq {G : Type} [Group G] {x y z : G} (h : x * y * x⁻¹ * y⁻¹ = z) :
    x * y = z * (y * x) := by
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = z * (y * x) := by rw [h]

theorem exists_notMem_zpowers {S : Type} [Group S] [Finite S] (C : Subgroup S)
    (hC : 4 ≤ Nat.card C) {ℓ : S} (hℓℓ : ℓ * ℓ = 1) (hℓ1 : ℓ ≠ 1) :
    ∃ a ∈ C, a ∉ Subgroup.zpowers ℓ := by
  by_contra hcon
  push Not at hcon
  have hle : C ≤ Subgroup.zpowers ℓ := fun a ha => hcon a ha
  have h2 : Nat.card (Subgroup.zpowers ℓ) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hℓℓ) hℓ1]
  have := Subgroup.card_le_of_le hle
  omega

theorem exists_notMem_of_card {S : Type} [Group S] {A E : Subgroup S} (hA : Nat.card A = 8)
    (hAE : Nat.card (A ⊓ E : Subgroup S) = 4) : ∃ a ∈ A, a ∉ E := by
  by_contra hcon
  push Not at hcon
  have hle : A ≤ E := fun a ha => hcon a ha
  rw [inf_of_le_left hle] at hAE
  omega

theorem commute_mul_right_iff_of {G : Type} [Group G] {g x y : G} (hgx : Commute g x) :
    Commute g (x * y) ↔ Commute g y := by
  constructor
  · intro h
    have h1 : x * (g * y) = x * (y * g) := by
      calc x * (g * y) = (x * g) * y := (mul_assoc _ _ _).symm
        _ = (g * x) * y := by rw [hgx.eq]
        _ = g * (x * y) := mul_assoc _ _ _
        _ = (x * y) * g := h
        _ = x * (y * g) := mul_assoc _ _ _
    exact mul_left_cancel h1
  · intro h
    exact hgx.mul_right h

theorem cfg2_of_AB {S : Type} [Group S] [Finite S] (A B E : Subgroup S)
    (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8) (hB : IsElemAbelian 2 B) (hB8 : Nat.card B = 8)
    (hE : IsElemAbelian 2 E) (hE8 : Nat.card E = 8) (hEn : E.Normal)
    (hCA : Subgroup.centralizer (A : Set S) ≤ A) (hCB : Subgroup.centralizer (B : Set S) ≤ B)
    (hAB2 : Nat.card (A ⊓ B : Subgroup S) = 2) (hAE : Nat.card (A ⊓ E : Subgroup S) = 4)
    (hBE : Nat.card (B ⊓ E : Subgroup S) = 4)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B) :
    ∃ (F : Subgroup S) (z : S), Cfg2 S E F z := by
  obtain ⟨ℓ, hℓAB, hℓ1, hABc⟩ := exists_nontriv_of_card_two (A ⊓ B) hAB2
  have hℓA : ℓ ∈ A := (Subgroup.mem_inf.mp hℓAB).1
  have hℓB : ℓ ∈ B := (Subgroup.mem_inf.mp hℓAB).2
  have hABE : A ⊓ B ≤ E := inf_le_of_cards hAB2 hAE hBE hE8
  have hℓE : ℓ ∈ E := hABE hℓAB
  have hℓℓ : ℓ * ℓ = 1 := IsElemAbelian.sq_eq_one hA hℓA
  have hAB_of : ∀ x, x ∈ A → x ∈ B → x = 1 ∨ x = ℓ := fun x hxA hxB =>
    hABc x (Subgroup.mem_inf.mpr ⟨hxA, hxB⟩)
  obtain ⟨a, haAE, ha_nz⟩ := exists_notMem_zpowers (A ⊓ E) hAE.symm.le hℓℓ hℓ1
  have haA : a ∈ A := (Subgroup.mem_inf.mp haAE).1
  have haE : a ∈ E := (Subgroup.mem_inf.mp haAE).2
  have ha1 : a ≠ 1 := fun h => ha_nz (by rw [h]; exact Subgroup.one_mem _)
  have haℓ : a ≠ ℓ := fun h => ha_nz (by rw [h]; exact Subgroup.mem_zpowers ℓ)
  obtain ⟨b, hbBE, hb_nz⟩ := exists_notMem_zpowers (B ⊓ E) hBE.symm.le hℓℓ hℓ1
  have hbB : b ∈ B := (Subgroup.mem_inf.mp hbBE).1
  have hbE : b ∈ E := (Subgroup.mem_inf.mp hbBE).2
  have hb1 : b ≠ 1 := fun h => hb_nz (by rw [h]; exact Subgroup.one_mem _)
  have hbℓ : b ≠ ℓ := fun h => hb_nz (by rw [h]; exact Subgroup.mem_zpowers ℓ)
  have haB : a ∉ B := fun h => (hAB_of a haA h).elim ha1 haℓ
  have hbA : b ∉ A := fun h => (hAB_of b h hbB).elim hb1 hbℓ
  have hba : b ≠ a := fun h => haB (by rw [← h]; exact hbB)
  have hbℓa : b ≠ ℓ * a := fun h => haB (by
    have h' : a = ℓ * b := by rw [h, ← mul_assoc, hℓℓ, one_mul]
    rw [h']
    exact B.mul_mem hℓB hbB)
  obtain ⟨a', ha'A, ha'E⟩ := exists_notMem_of_card hA8 hAE
  obtain ⟨b', hb'B, hb'E⟩ := exists_notMem_of_card hB8 hBE
  have ha'sq : a' * a' = 1 := IsElemAbelian.sq_eq_one hA ha'A
  have ha'1 : a' ≠ 1 := fun h => ha'E (by rw [h]; exact E.one_mem)
  have ha'ℓ : a' ≠ ℓ := fun h => ha'E (by rw [h]; exact hℓE)
  have ha'a : a' ≠ a := fun h => ha'E (by rw [h]; exact haE)
  have ha'ℓa : a' ≠ ℓ * a := fun h => ha'E (by rw [h]; exact E.mul_mem hℓE haE)
  have hb'1 : b' ≠ 1 := fun h => hb'E (by rw [h]; exact E.one_mem)
  have hb'ℓ : b' ≠ ℓ := fun h => hb'E (by rw [h]; exact hℓE)
  have hb'b : b' ≠ b := fun h => hb'E (by rw [h]; exact hbE)
  have hb'ℓb : b' ≠ ℓ * b := fun h => hb'E (by rw [h]; exact E.mul_mem hℓE hbE)
  have hcoA : ∀ x ∈ A, x = 1 ∨ x = ℓ ∨ x = a ∨ x = ℓ * a ∨ x = a' ∨ x = ℓ * a' ∨ x = a * a' ∨
      x = ℓ * (a * a') :=
    coords_sub hA hA8 hℓA haA ha'A hℓ1 ha1 haℓ ha'1 ha'ℓ ha'a ha'ℓa
  have hcoB : ∀ x ∈ B, x = 1 ∨ x = ℓ ∨ x = b ∨ x = ℓ * b ∨ x = b' ∨ x = ℓ * b' ∨ x = b * b' ∨
      x = ℓ * (b * b') :=
    coords_sub hB hB8 hℓB hbB hb'B hℓ1 hb1 hbℓ hb'1 hb'ℓ hb'b hb'ℓb
  have hcoE : ∀ x ∈ E, x = 1 ∨ x = ℓ ∨ x = a ∨ x = ℓ * a ∨ x = b ∨ x = ℓ * b ∨ x = a * b ∨
      x = ℓ * (a * b) :=
    coords_sub hE hE8 hℓE haE hbE hℓ1 ha1 haℓ hb1 hbℓ hba hbℓa
  have hab : a * b = b * a := IsElemAbelian.comm_of_mem hE haE hbE
  have hℓa : ℓ * a = a * ℓ := IsElemAbelian.comm_of_mem hA hℓA haA
  have hℓb' : ℓ * b' = b' * ℓ := IsElemAbelian.comm_of_mem hB hℓB hb'B
  have hC1 : a' * b = ℓ * (b * a') := by
    rcases hABc _ (hcomm a' ha'A b hbB) with h | h
    · exfalso
      have hbC : b ∈ Subgroup.centralizer (A : Set S) :=
        Subgroup.mem_centralizer_iff.mpr (fun x hx =>
          (commute_of_coords (IsElemAbelian.comm_of_mem hE hbE hℓE) hab.symm
            (eq_of_comm_one h).symm (hcoA x hx)).symm)
      exact hbA (hCA hbC)
    · exact eq_of_comm_eq h
  have hC2 : a * b' = ℓ * (b' * a) := by
    rcases hABc _ (hcomm a haA b' hb'B) with h | h
    · exfalso
      have haC : a ∈ Subgroup.centralizer (B : Set S) :=
        Subgroup.mem_centralizer_iff.mpr (fun x hx =>
          (commute_of_coords hℓa.symm hab (eq_of_comm_one h) (hcoB x hx)).symm)
      exact haB (hCB haC)
    · exact eq_of_comm_eq h
  obtain ⟨c, hcB, hcE, hcc, ha'c, hac⟩ : ∃ c, c ∈ B ∧ c ∉ E ∧ c * c = 1 ∧ a' * c = c * a' ∧
      a * c = ℓ * (c * a) := by
    rcases hABc _ (hcomm a' ha'A b' hb'B) with hε | hε
    · exact ⟨b', hb'B, hb'E, IsElemAbelian.sq_eq_one hB hb'B, eq_of_comm_one hε, hC2⟩
    · refine ⟨b' * b, B.mul_mem hb'B hbB, ?_, IsElemAbelian.sq_eq_one hB (B.mul_mem hb'B hbB),
        ?_, ?_⟩
      · intro h
        apply hb'E
        have e : b' = b' * b * b⁻¹ := by group
        rw [e]
        exact E.mul_mem h (E.inv_mem hbE)
      · have hε' := eq_of_comm_eq hε
        calc a' * (b' * b) = (a' * b') * b := (mul_assoc _ _ _).symm
          _ = (ℓ * (b' * a')) * b := by rw [hε']
          _ = ℓ * (b' * (a' * b)) := by simp only [mul_assoc]
          _ = ℓ * (b' * (ℓ * (b * a'))) := by rw [hC1]
          _ = (ℓ * b') * ℓ * (b * a') := by simp only [mul_assoc]
          _ = (b' * ℓ) * ℓ * (b * a') := by rw [hℓb']
          _ = b' * (ℓ * ℓ) * (b * a') := by simp only [mul_assoc]
          _ = (b' * b) * a' := by rw [hℓℓ, mul_one, mul_assoc]
      · calc a * (b' * b) = (a * b') * b := (mul_assoc _ _ _).symm
          _ = (ℓ * (b' * a)) * b := by rw [hC2]
          _ = ℓ * (b' * (a * b)) := by simp only [mul_assoc]
          _ = ℓ * (b' * (b * a)) := by rw [hab]
          _ = ℓ * ((b' * b) * a) := by simp only [mul_assoc]
  have hc1 : c ≠ 1 := fun h => hcE (by rw [h]; exact E.one_mem)
  have hcℓ : c ≠ ℓ := fun h => hcE (by rw [h]; exact hℓE)
  have hcb : c ≠ b := fun h => hcE (by rw [h]; exact hbE)
  have hcℓb : c ≠ ℓ * b := fun h => hcE (by rw [h]; exact E.mul_mem hℓE hbE)
  have hcoBc : ∀ x ∈ B, x = 1 ∨ x = ℓ ∨ x = b ∨ x = ℓ * b ∨ x = c ∨ x = ℓ * c ∨ x = b * c ∨
      x = ℓ * (b * c) :=
    coords_sub hB hB8 hℓB hbB hcB hℓ1 hb1 hbℓ hc1 hcℓ hcb hcℓb
  have ha'c_ne : a' * c ≠ 1 := by
    intro h
    have hca' : c = a' := by
      calc c = a' * (a' * c) := by rw [← mul_assoc, ha'sq, one_mul]
        _ = a' * 1 := by rw [h]
        _ = a' := mul_one a'
    exact ha'E (hABE (Subgroup.mem_inf.mpr ⟨ha'A, by rw [← hca']; exact hcB⟩))
  obtain ⟨F, hmemF, hFa, hF4⟩ := exists_F_of_invol ha'c ha'sq hcc ha'1 hc1 ha'c_ne
  have ha'F : a' ∈ F := (hmemF a').mpr (Or.inr (Or.inl rfl))
  have hcF : c ∈ F := (hmemF c).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have ha'ℓcomm : Commute a' ℓ := IsElemAbelian.comm_of_mem hA ha'A hℓA
  have ha'acomm : Commute a' a := IsElemAbelian.comm_of_mem hA ha'A haA
  have hcℓcomm : Commute c ℓ := IsElemAbelian.comm_of_mem hB hcB hℓB
  have hLa' : Commute ℓ a' := (IsElemAbelian.comm_of_mem hA hℓA ha'A)
  have hLc : Commute ℓ c := (IsElemAbelian.comm_of_mem hB hℓB hcB)
  have hLF : ∀ f ∈ F, Commute ℓ f := by
    intro f hf
    rcases (hmemF f).mp hf with h | h | h | h <;> rw [h]
    · exact Commute.one_right ℓ
    · exact hLa'
    · exact hLc
    · exact hLa'.mul_right hLc
  have hzF : ∀ f ∈ F, f * ℓ = ℓ * f := fun f hf => (hLF f hf).symm
  have ha'b_ne : a' * b ≠ b * a' := fun h => by
    rw [hC1] at h
    exact hℓ1 (mul_right_cancel (h.trans (one_mul _).symm))
  have hca_ne : c * a ≠ a * c := fun h => by
    rw [hac] at h
    exact hℓ1 (mul_right_cancel (h.symm.trans (one_mul _).symm))
  have hFK : ∀ f ∈ F, (∀ e ∈ E, f * e = e * f) → f = 1 := by
    intro f hf hfE
    rcases (hmemF f).mp hf with h | h | h | h
    · exact h
    · exfalso
      rw [h] at hfE
      exact ha'b_ne (hfE b hbE)
    · exfalso
      rw [h] at hfE
      exact hca_ne (hfE a haE)
    · exfalso
      rw [h] at hfE
      have key : a' * c * b = ℓ * (b * (a' * c)) := by
        calc a' * c * b = a' * (c * b) := mul_assoc _ _ _
          _ = a' * (b * c) := by rw [IsElemAbelian.comm_of_mem hB hcB hbB]
          _ = (a' * b) * c := (mul_assoc _ _ _).symm
          _ = (ℓ * (b * a')) * c := by rw [hC1]
          _ = ℓ * (b * (a' * c)) := by simp only [mul_assoc]
      have h1 := hfE b hbE
      exact hℓ1 (mul_right_cancel ((key.symm.trans h1).trans (one_mul _).symm))
  have hCE : ∀ e ∈ E, (∀ f ∈ F, f * e = e * f) → e = 1 ∨ e = ℓ := by
    intro e he hfe
    rcases hcoE e he with h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have h1 := hfe c hcF
      rw [h] at h1
      exact hca_ne h1
    · exfalso
      have h1 := hfe c hcF
      rw [h] at h1
      have h1' : Commute c (ℓ * a) := h1
      exact hca_ne ((commute_mul_right_iff_of hcℓcomm).mp h1')
    · exfalso
      have h1 := hfe a' ha'F
      rw [h] at h1
      exact ha'b_ne h1
    · exfalso
      have h1 := hfe a' ha'F
      rw [h] at h1
      have h1' : Commute a' (ℓ * b) := h1
      exact ha'b_ne ((commute_mul_right_iff_of ha'ℓcomm).mp h1')
    · exfalso
      have h1 := hfe a' ha'F
      rw [h] at h1
      have h1' : Commute a' (a * b) := h1
      exact ha'b_ne ((commute_mul_right_iff_of ha'acomm).mp h1')
    · exfalso
      have h1 := hfe a' ha'F
      rw [h] at h1
      have h1' : Commute a' (ℓ * (a * b)) := h1
      have h2 : Commute a' (a * b) := (commute_mul_right_iff_of ha'ℓcomm).mp h1'
      exact ha'b_ne ((commute_mul_right_iff_of ha'acomm).mp h2)
  have hCK : ∀ k : S, (∀ e ∈ E, k * e = e * k) → (∀ f ∈ F, k * f = f * k) → k = 1 ∨ k = ℓ := by
    intro k hkE hkF
    have hkℓ : k * ℓ = ℓ * k := hkE ℓ hℓE
    have hka : k * a = a * k := hkE a haE
    have hkb : k * b = b * k := hkE b hbE
    have hka' : k * a' = a' * k := hkF a' ha'F
    have hkc : k * c = c * k := hkF c hcF
    have hkA : k ∈ A := hCA (Subgroup.mem_centralizer_iff.mpr (fun x hx =>
      (commute_of_coords hkℓ hka hka' (hcoA x hx)).symm))
    have hkB : k ∈ B := hCB (Subgroup.mem_centralizer_iff.mpr (fun x hx =>
      (commute_of_coords hkℓ hkb hkc (hcoBc x hx)).symm))
    exact hABc k (Subgroup.mem_inf.mpr ⟨hkA, hkB⟩)
  exact ⟨F, ℓ, ⟨hEn, hE, hE8, hFa, hF4, hℓE, hℓ1, hzF, hFK, hCE, hCK⟩⟩

end CFSG.EvenSporadicStandard.Fin76b
