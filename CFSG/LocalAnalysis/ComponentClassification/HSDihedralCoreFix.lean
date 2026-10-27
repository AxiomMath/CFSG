module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreElem

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup
open CFSG.ComponentClassification.HSFLit (ElemAbelianTwo eq_one_or_eq_of_mem_zpowers)

variable {G : Type} [Group G] [Finite G]

theorem card_le_sq_card_fix {Y : Subgroup G} (hY : ElemAbelianTwo Y) {t : G}
    (ht : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y) (ht2 : t ^ 2 = 1) :
    Nat.card Y ≤ Nat.card ↥(Y ⊓ centralizer ({t} : Set G)) ^ 2 := by
  have htt : t * t = 1 := by rw [← pow_two, ht2]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hmem : ∀ y ∈ Y, t * y * t⁻¹ * y⁻¹ ∈ Y := fun y hy => mul_mem (ht y hy) (inv_mem hy)
  let f : ↥Y →* ↥Y := MonoidHom.mk'
    (fun y => ⟨t * (y : G) * t⁻¹ * (y : G)⁻¹, hmem y y.2⟩) (by
    intro a b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc t * ((a : G) * b) * t⁻¹ * ((a : G) * b)⁻¹ =
        t * a * t⁻¹ * ((t * (b : G) * t⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
      _ = t * a * t⁻¹ * ((a : G)⁻¹ * (t * (b : G) * t⁻¹ * (b : G)⁻¹)) := by
          rw [hY.comm _ (hmem b b.2) _ (inv_mem a.2)]
      _ = t * a * t⁻¹ * (a : G)⁻¹ * (t * (b : G) * t⁻¹ * (b : G)⁻¹) := by group)
  have hker : ∀ y : ↥Y, y ∈ f.ker ↔ (y : G) ∈ centralizer ({t} : Set G) := by
    intro y
    rw [MonoidHom.mem_ker, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : t * (y : G) * t⁻¹ * (y : G)⁻¹ = 1 := congrArg Subtype.val h
      calc (y : G) * t = t * (y : G) * t⁻¹ * (y : G)⁻¹ * ((y : G) * t) := by rw [h', one_mul]
        _ = t * y := by group
    · intro h
      apply Subtype.ext
      change t * (y : G) * t⁻¹ * (y : G)⁻¹ = 1
      rw [← h]
      group
  have hrange : f.range ≤ f.ker := by
    rintro _ ⟨y, rfl⟩
    rw [hker]
    rw [mem_centralizer_singleton_iff]
    set u : G := t * y * t⁻¹ * (y : G)⁻¹
    have hu : u ∈ Y := hmem y y.2
    have h1 : t * u * t⁻¹ = u⁻¹ := by
      calc t * u * t⁻¹ = t * t * y * t⁻¹ * (y : G)⁻¹ * t⁻¹ := by simp only [u]; group
        _ = y * t * (y : G)⁻¹ * t⁻¹ := by rw [htt, one_mul, htinv]
        _ = u⁻¹ := by simp only [u]; group
    have hu2 : u * u = 1 := by rw [← pow_two]; exact hY.sq_eq_one u hu
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    change u * t = t * u
    calc u * t = t * (t * u * t⁻¹) := by
          rw [← mul_assoc, ← mul_assoc, htt, one_mul, htinv]
      _ = t * u := by rw [h1, huinv]
  have hcard : Nat.card Y = Nat.card f.ker * Nat.card f.range := by
    rw [← Subgroup.index_ker f, Subgroup.card_mul_index]
  have hle : Nat.card f.range ≤ Nat.card f.ker := Subgroup.card_le_of_le hrange
  have hker' : Nat.card f.ker = Nat.card ↥(Y ⊓ centralizer ({t} : Set G)) := by
    have : f.ker.map Y.subtype = Y ⊓ centralizer ({t} : Set G) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact mem_inf.mpr ⟨y.2, (hker y).mp hy⟩
      · intro hx
        obtain ⟨hxY, hxC⟩ := mem_inf.mp hx
        exact ⟨⟨x, hxY⟩, (hker ⟨x, hxY⟩).mpr hxC, rfl⟩
    rw [← this, card_map_of_injective Y.subtype_injective]
  rw [hcard, ← hker', pow_two]
  exact Nat.mul_le_mul_left _ hle

theorem four_le_card_fix {Y : Subgroup G} (hY : ElemAbelianTwo Y) (hY8 : Nat.card Y = 8) {t : G}
    (ht : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y) (ht2 : t ^ 2 = 1) :
    4 ≤ Nat.card ↥(Y ⊓ centralizer ({t} : Set G)) := by
  have h := card_le_sq_card_fix hY ht ht2
  have hdvd : Nat.card ↥(Y ⊓ centralizer ({t} : Set G)) ∣ 8 := by
    rw [← hY8]
    exact Subgroup.card_dvd_of_le inf_le_left
  rw [hY8] at h
  have hpos := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have h3 : 3 ≤ Nat.card ↥(Y ⊓ centralizer ({t} : Set G)) := by
    by_contra hlt
    push Not at hlt
    interval_cases (Nat.card ↥(Y ⊓ centralizer ({t} : Set G))) <;> omega
  by_contra hlt
  push Not at hlt
  have : Nat.card ↥(Y ⊓ centralizer ({t} : Set G)) = 3 := by omega
  rw [this] at hdvd
  norm_num at hdvd

omit [Finite G] in
theorem card_le_card_of_finset [Finite G] {E : Subgroup G} (s : Finset G)
    (hs : ∀ x ∈ s, x ∈ E) : s.card ≤ Nat.card E := by
  calc s.card = (s : Set G).ncard := (Set.ncard_coe_finset s).symm
    _ ≤ (E : Set G).ncard := Set.ncard_le_ncard (fun x hx => hs x hx) (Set.toFinite _)
    _ = Nat.card E := Nat.card_coe_set_eq _

theorem eq_of_card_le_four {E : Subgroup G} (hE : Nat.card E ≤ 4) {a b c d : G} (ha : a ∈ E)
    (hb : b ∈ E) (hc : c ∈ E) (hd : d ∈ E) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {x : G} (hx : x ∈ E) :
    x = a ∨ x = b ∨ x = c ∨ x = d := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨hxa, hxb, hxc, hxd⟩ := hne
  have h5 : ({x, a, b, c, d} : Finset G).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hxa, hxb, hxc, hxd]),
      Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
  have := card_le_card_of_finset (E := E) {x, a, b, c, d} (by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption)
  omega

theorem mem_E8_cases {a b c : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) {x : G}
    (hx : x ∈ zpowers a ⊔ zpowers b ⊔ zpowers c) :
    (x = 1 ∨ x = a ∨ x = b ∨ x = a * b) ∨
      (x = c ∨ x = a * c ∨ x = b * c ∨ x = a * b * c) := by
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hc])
  by_cases hcE : c ∈ zpowers a ⊔ zpowers b
  · rw [sup_eq_left.mpr (zpowers_le.mpr hcE)] at hx
    exact Or.inl (mem_E4_cases ha hb hab hx)
  · rcases ((elem_E4 ha hb hab).sup_zpowers hc hcE fun _ hy =>
        commute_of_mem_sup hac.symm hbc.symm hy).2.1 x hx with h | h
    · exact Or.inl (mem_E4_cases ha hb hab h)
    · right
      have hx' : x = x * c * c := by rw [mul_assoc, ← pow_two, hc, mul_one]
      rcases mem_E4_cases ha hb hab h with h' | h' | h' | h'
      · left; rw [hx', h', one_mul]
      · right; left; rw [hx', h']
      · right; right; left; rw [hx', h']
      · right; right; right; rw [hx', h']

theorem E8_eq {Y : Subgroup G} (hY8 : Nat.card Y = 8) {a b c : G} (ha : a ∈ Y) (hb : b ∈ Y)
    (hc : c ∈ Y) (hcard : Nat.card (zpowers a ⊔ zpowers b ⊔ zpowers c : Subgroup G) = 8) :
    zpowers a ⊔ zpowers b ⊔ zpowers c = Y :=
  Subgroup.eq_of_le_of_card_ge (E8_le ha hb hc) (by rw [hY8, hcard])

end CFSG.ComponentClassification.HSDihedral
