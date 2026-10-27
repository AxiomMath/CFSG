module

public import CFSG.GF2Type.Smith1979W3.Cert690.Statements

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.GF2Type.Smith1979W3.Cert690

variable {G : Type*} [Group G]

theorem image_conj_conj (a b : G) (S : Set G) :
    (fun x => a * x * a⁻¹) '' ((fun x => b * x * b⁻¹) '' S) =
      (fun x => (a * b) * x * (a * b)⁻¹) '' S := by
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by group⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨b * z * b⁻¹, ⟨z, hz, rfl⟩, by group⟩

theorem image_conj_inv_conj (c : G) (S : Set G) :
    (fun x => c⁻¹ * x * (c⁻¹)⁻¹) '' ((fun x => c * x * c⁻¹) '' S) = S := by
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hxy⟩
    rw [show c⁻¹ * (c * z * c⁻¹) * (c⁻¹)⁻¹ = z by group] at hxy
    exact hxy ▸ hz
  · intro hx
    exact ⟨c * x * c⁻¹, ⟨x, hx, rfl⟩, by group⟩

theorem image_conj_mul_set (c u : G) (S : Set G) :
    (fun x => c * x * c⁻¹) '' ((fun y => y * u) '' S) =
      (fun x => x * (c * u * c⁻¹)) '' ((fun x => c * x * c⁻¹) '' S) := by
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨c * z * c⁻¹, ⟨z, hz, rfl⟩, by group⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z * u, ⟨z, hz, rfl⟩, by group⟩

theorem mem_zpowers_pair {u x : G} (hu2 : u * u = 1) :
    x ∈ Subgroup.zpowers u ↔ x = 1 ∨ x = u := by
  constructor
  · intro hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      have h2 : u ^ (2 : ℤ) = 1 := by simpa [zpow_natCast, pow_two] using hu2
      rw [hm, _root_.zpow_mul, h2, _root_.one_zpow]
    · right
      have h2 : u ^ (2 : ℤ) = 1 := by simpa [zpow_natCast, pow_two] using hu2
      have h2m : u ^ ((2 : ℤ) * m) = 1 := by
        rw [_root_.zpow_mul, h2, _root_.one_zpow]
      rw [hm, _root_.zpow_add_one, h2m]
      simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers x

theorem zpowers_eq_pair {u : G} (hu2 : u * u = 1) :
    (Subgroup.zpowers u : Set G) = {1, u} := by
  ext x
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact mem_zpowers_pair hu2

theorem mul_comm_of_sq_eq_one {y u : G} (hy2 : y * y = 1) (hu2 : u * u = 1)
    (hyu2 : (y * u) * (y * u) = 1) : y * u = u * y := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have h1 : y * u = (y * u)⁻¹ := (inv_eq_of_mul_eq_one_right hyu2).symm
  rw [mul_inv_rev, hyi, hui] at h1
  exact h1

theorem sup_zpowers_eq_union {Y' : Subgroup G} {u : G} (hu2 : u * u = 1)
    (hcomm : ∀ y ∈ Y', y * u = u * y) :
    ((Y' ⊔ Subgroup.zpowers u : Subgroup G) : Set G) =
      (Y' : Set G) ∪ (fun y => y * u) '' (Y' : Set G) := by
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  let S : Subgroup G :=
    { carrier := (Y' : Set G) ∪ (fun y => y * u) '' (Y' : Set G)
      one_mem' := Or.inl (Y'.one_mem)
      mul_mem' := by
        rintro a b (ha | ⟨a', ha', rfl⟩) (hb | ⟨b', hb', rfl⟩)
        · exact Or.inl (Y'.mul_mem ha hb)
        · exact Or.inr ⟨a * b', Y'.mul_mem ha hb', by group⟩
        · refine Or.inr ⟨a' * b, Y'.mul_mem ha' hb, ?_⟩
          calc (a' * b) * u = a' * (b * u) := by group
            _ = a' * (u * b) := by rw [hcomm b hb]
            _ = a' * u * b := by group
        · refine Or.inl ?_
          rw [show (a' * u) * (b' * u) = a' * b' by
            calc (a' * u) * (b' * u) = a' * (u * b') * u := by group
              _ = a' * (b' * u) * u := by rw [hcomm b' hb']
              _ = a' * b' * (u * u) := by group
              _ = a' * b' := by rw [hu2]; group]
          exact Y'.mul_mem ha' hb'
      inv_mem' := by
        rintro a (ha | ⟨a', ha', rfl⟩)
        · exact Or.inl (Y'.inv_mem ha)
        · refine Or.inr ⟨a'⁻¹, Y'.inv_mem ha', ?_⟩
          calc a'⁻¹ * u = u * a'⁻¹ := by rw [hcomm a'⁻¹ (Y'.inv_mem ha')]
            _ = u⁻¹ * a'⁻¹ := by rw [hu_inv]
            _ = (a' * u)⁻¹ := by group
    }
  have hSle : S ≤ Y' ⊔ Subgroup.zpowers u := by
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact (le_sup_left : Y' ≤ Y' ⊔ Subgroup.zpowers u) hx
    · exact mul_mem ((le_sup_left : Y' ≤ Y' ⊔ Subgroup.zpowers u) hy)
        ((le_sup_right : Subgroup.zpowers u ≤ Y' ⊔ Subgroup.zpowers u)
          (Subgroup.mem_zpowers u))
  have hsup_le : Y' ⊔ Subgroup.zpowers u ≤ S := by
    apply sup_le
    · intro x hx
      exact Or.inl hx
    · intro x hx
      rw [mem_zpowers_pair hu2] at hx
      rcases hx with rfl | rfl
      · exact S.one_mem
      · exact Or.inr ⟨1, Y'.one_mem, by simp⟩
  exact Set.Subset.antisymm (fun x hx => hsup_le hx) (fun x hx => hSle hx)

theorem lList_induction (C : Subgroup G) {ι : Type*} (Λ : ι → Set G) (A : Set G)
    (hL2 : ∀ t ∈ A, ∃ j, ∃ c ∈ C, (fun x => c * x * c⁻¹) '' Λ j = {1, t})
    (hL3 : ∀ j, ∀ u ∈ C, u ∉ Λ j → u * u = 1 →
      (∀ x ∈ Λ j, u * x = x * u) →
      ∃ k, ∃ c ∈ C,
        (fun x => c * x * c⁻¹) '' (Λ j ∪ (fun x => x * u) '' Λ j) = Λ k)
    {Y : Subgroup G} (hYC : Y ≤ C) (hYfin : Finite Y)
    (hinv : ∀ y ∈ Y, y * y = 1)
    {t : G} (htA : t ∈ A) (htY : t ∈ Y) :
    ∃ j, ∃ c ∈ C, (fun x => c * x * c⁻¹) '' (Y : Set G) = Λ j := by
  classical
  haveI : Finite Y := hYfin
  have ht2 : t * t = 1 := hinv t htY
  have hcommY : ∀ y ∈ Y, ∀ z ∈ Y, y * z = z * y := by
    intro y hy z hz
    exact mul_comm_of_sq_eq_one (hinv y hy) (hinv z hz) (hinv (y * z) (Y.mul_mem hy hz))
  obtain ⟨j0, c0, hc0, hstate0'⟩ := hL2 t htA
  let Y0 : Subgroup G := Subgroup.zpowers t
  have hY0Y : Y0 ≤ Y := Subgroup.zpowers_le.mpr htY
  have htY0 : t ∈ Y0 := Subgroup.mem_zpowers t
  have hY0set : (Y0 : Set G) = {1, t} := zpowers_eq_pair ht2
  have hc0inv : c0⁻¹ ∈ C := C.inv_mem hc0
  have hstate0 : (fun x => c0⁻¹ * x * (c0⁻¹)⁻¹) '' (Y0 : Set G) = Λ j0 := by
    rw [hY0set, ← hstate0']
    exact image_conj_inv_conj c0 (Λ j0)
  have main : ∀ n, ∀ (Y' : Subgroup G) (j : ι) (c : G), c ∈ C → Y' ≤ Y → t ∈ Y' →
      (fun x => c * x * c⁻¹) '' (Y' : Set G) = Λ j →
      Nat.card Y - Nat.card Y' = n →
      ∃ j, ∃ c ∈ C, (fun x => c * x * c⁻¹) '' (Y : Set G) = Λ j := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro Y' j c hc hY'Y htY' hstate hcard
      by_cases hYY : Y' = Y
      · subst hYY
        exact ⟨j, c, hc, hstate⟩
      · have hY'fin : Finite Y' :=
          Finite.of_injective (fun x : Y' => (⟨x.1, hY'Y x.2⟩ : Y))
            (by
              intro a b hab
              apply Subtype.ext
              exact congrArg (fun x : Y => (x : G)) hab)
        haveI : Finite Y' := hY'fin
        obtain ⟨u, huY, huY'⟩ : ∃ u ∈ Y, u ∉ Y' := by
          by_contra! h
          exact hYY (le_antisymm hY'Y h)
        have hu2 : u * u = 1 := hinv u huY
        have huC : u ∈ C := hYC huY
        let u' : G := c * u * c⁻¹
        have hu'C : u' ∈ C := C.mul_mem (C.mul_mem hc huC) (C.inv_mem hc)
        have hu'2 : u' * u' = 1 := by
          change c * u * c⁻¹ * (c * u * c⁻¹) = 1
          rw [show c * u * c⁻¹ * (c * u * c⁻¹) = c * (u * u) * c⁻¹ by group]
          rw [hu2]
          group
        have hu'not : u' ∉ Λ j := by
          intro hu'
          have : u ∈ Y' := by
            have hmem : u' ∈ (fun x => c * x * c⁻¹) '' (Y' : Set G) := by
              rw [hstate]
              exact hu'
            obtain ⟨y, hy, huy⟩ := hmem
            have huy' : c * y * c⁻¹ = c * u * c⁻¹ := by
              simpa [u'] using huy
            have : u = y := by
              calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
                _ = c⁻¹ * (c * y * c⁻¹) * c := by rw [huy']
                _ = y := by group
            rwa [this]
          exact huY' this
        have hu'comm : ∀ x ∈ Λ j, u' * x = x * u' := by
          intro x hx
          have hx' : x ∈ (fun x => c * x * c⁻¹) '' (Y' : Set G) := by
            rw [hstate]
            exact hx
          obtain ⟨y, hy, hxy⟩ := hx'
          subst hxy
          change c * u * c⁻¹ * (c * y * c⁻¹) = c * y * c⁻¹ * (c * u * c⁻¹)
          rw [show c * u * c⁻¹ * (c * y * c⁻¹) = c * (u * y) * c⁻¹ by group,
            show c * y * c⁻¹ * (c * u * c⁻¹) = c * (y * u) * c⁻¹ by group,
            hcommY u huY y (hY'Y hy)]
        obtain ⟨k, c₁, hc₁, hΛk⟩ := hL3 j u' hu'C hu'not hu'2 hu'comm
        have hc₁c : c₁ * c ∈ C := C.mul_mem hc₁ hc
        let Y'' : Subgroup G := Y' ⊔ Subgroup.zpowers u
        have hY''Y : Y'' ≤ Y := sup_le hY'Y (Subgroup.zpowers_le.mpr huY)
        have htY'' : t ∈ Y'' := (le_sup_left : Y' ≤ Y' ⊔ Subgroup.zpowers u) htY'
        have hY''fin : Finite Y'' :=
          Finite.of_injective (fun x : Y'' => (⟨x.1, hY''Y x.2⟩ : Y))
            (by
              intro a b hab
              apply Subtype.ext
              exact congrArg (fun x : Y => (x : G)) hab)
        haveI : Finite Y'' := hY''fin
        have hY''set : (Y'' : Set G) = (Y' : Set G) ∪ (fun y => y * u) '' (Y' : Set G) :=
          sup_zpowers_eq_union hu2 (fun y hy => hcommY y (hY'Y hy) u huY)
        have hφY'' : (fun x => c * x * c⁻¹) '' (Y'' : Set G) =
            Λ j ∪ (fun x => x * u') '' Λ j := by
          rw [hY''set, Set.image_union, hstate, image_conj_mul_set, hstate]
        have hstate'' : (fun x => (c₁ * c) * x * (c₁ * c)⁻¹) '' (Y'' : Set G) = Λ k := by
          rw [← image_conj_conj c₁ c (Y'' : Set G)]
          rw [hφY'']
          exact hΛk
        have hlt : Y' < Y'' := by
          refine lt_of_le_of_ne le_sup_left ?_
          intro hEq
          have huY'' : u ∈ Y'' :=
            (le_sup_right : Subgroup.zpowers u ≤ Y' ⊔ Subgroup.zpowers u)
              (Subgroup.mem_zpowers u)
          exact huY' (hEq.symm ▸ huY'')
        have hcardlt : Nat.card Y' < Nat.card Y'' := by
          have hsub : (Y' : Set G) ⊂ (Y'' : Set G) := by
            refine ⟨SetLike.coe_subset_coe.mpr le_sup_left, ?_⟩
            intro hss
            exact huY' (hss ((le_sup_right : Subgroup.zpowers u ≤
              Y' ⊔ Subgroup.zpowers u) (Subgroup.mem_zpowers u)))
          simpa [Nat.card_coe_set_eq] using
            (Set.Finite.card_lt_card (Set.toFinite (Y'' : Set G)) hsub)
        have hcardle : Nat.card Y'' ≤ Nat.card Y :=
          Nat.card_le_card_of_injective (fun x : Y'' => (⟨x.1, hY''Y x.2⟩ : Y))
            (by
              intro a b hab
              apply Subtype.ext
              exact congrArg (fun x : Y => (x : G)) hab)
        have hcardn : Nat.card Y - Nat.card Y'' < n := by
          rw [← hcard]
          omega
        exact ih (Nat.card Y - Nat.card Y'') hcardn Y'' k (c₁ * c) hc₁c hY''Y htY'' hstate'' rfl
  exact main (Nat.card Y - Nat.card Y0) Y0 j0 c0⁻¹ hc0inv hY0Y htY0 hstate0 rfl

end CFSG.GF2Type.Smith1979W3.Cert690

end
