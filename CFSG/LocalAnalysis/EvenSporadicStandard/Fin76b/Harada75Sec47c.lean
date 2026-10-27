module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Lin
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75F3

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

section Centralizer

variable {S : Type} [Group S]

theorem sq_eq_one_of_isElemAbelian_two {E : Subgroup S} (hE : IsElemAbelian 2 E) {x : S}
    (hx : x ∈ E) : x * x = 1 := by
  have h := hE.2 x hx
  rwa [pow_two] at h

theorem comm_of_isElemAbelian_two {E : Subgroup S} (hE : IsElemAbelian 2 E) {x y : S}
    (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem index_subgroupOf_inf_le_two [Finite S] {A K : Subgroup S} (hA8 : Nat.card A = 8)
    (hAK : Nat.card (A ⊓ K : Subgroup S) = 4) : (K.subgroupOf A).index ≤ 2 := by
  have h := Subgroup.relIndex_mul_card K A
  rw [inf_comm, hAK, hA8] at h
  have h2 : K.relIndex A = 2 := by omega
  exact h2.le

theorem mem_or_mul_mem_of_subgroupOf_index_le_two [Finite S] {A K : Subgroup S}
    (hA : IsElemAbelian 2 A) (hi : (K.subgroupOf A).index ≤ 2) {a : S} (haA : a ∈ A)
    (haK : a ∉ K) {x : S} (hx : x ∈ A) : x ∈ K ∨ x * a ∈ K := by
  by_cases hxK : x ∈ K
  · exact Or.inl hxK
  · right
    have hu : (⟨x, hx⟩ : A) ∉ K.subgroupOf A := fun h => hxK (Subgroup.mem_subgroupOf.mp h)
    have hv : (⟨a, haA⟩ : A) ∉ K.subgroupOf A := fun h => haK (Subgroup.mem_subgroupOf.mp h)
    have h : x⁻¹ * a ∈ K :=
      Subgroup.mem_subgroupOf.mp (inv_mul_mem_of_not_mem_of_index_le_two hi hu hv)
    rwa [inv_eq_of_mul_eq_one_right (sq_eq_one_of_isElemAbelian_two hA hx)] at h

theorem mem_centralizer_of_comm_inf [Finite S] {A K : Subgroup S} (hA : IsElemAbelian 2 A)
    (hi : (K.subgroupOf A).index ≤ 2) {a : S} (haA : a ∈ A) (haK : a ∉ K) {g : S}
    (hga : g * a = a * g) (hgZ : ∀ z ∈ A ⊓ K, g * z = z * g) :
    g ∈ Subgroup.centralizer (A : Set S) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have ha2 : a * a = 1 := sq_eq_one_of_isElemAbelian_two hA haA
  rcases mem_or_mul_mem_of_subgroupOf_index_le_two hA hi haA haK hh with hhK | hha
  · exact (hgZ h (Subgroup.mem_inf.mpr ⟨hh, hhK⟩)).symm
  · have hgy : g * (h * a) = h * a * g := hgZ (h * a) (Subgroup.mem_inf.mpr ⟨A.mul_mem hh haA, hha⟩)
    calc h * g = h * a * (a * g) := by
          rw [mul_assoc h a (a * g), ← mul_assoc a a g, ha2, one_mul]
      _ = h * a * (g * a) := by rw [hga]
      _ = h * a * g * a := (mul_assoc _ _ _).symm
      _ = g * (h * a) * a := by rw [hgy]
      _ = g * h := by rw [mul_assoc g (h * a) a, mul_assoc h a a, ha2, mul_one]

theorem inf_centralizer_singleton_eq [Finite S] {A K : Subgroup S} (hA : IsElemAbelian 2 A)
    (hK : IsElemAbelian 2 K) (hCA : Subgroup.centralizer (A : Set S) ≤ A)
    (hi : (K.subgroupOf A).index ≤ 2) {a : S} (haA : a ∈ A) (haK : a ∉ K) :
    K ⊓ Subgroup.centralizer ({a} : Set S) = A ⊓ K := by
  ext x
  constructor
  · rintro ⟨hxK, hxa⟩
    have hxa' : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp hxa
    have hxA : x ∈ A := hCA (mem_centralizer_of_comm_inf hA hi haA haK hxa'
      (fun z hz => comm_of_isElemAbelian_two hK hxK (Subgroup.mem_inf.mp hz).2))
    exact Subgroup.mem_inf.mpr ⟨hxA, hxK⟩
  · intro hx
    obtain ⟨hxA, hxK⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hxK,
      Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_isElemAbelian_two hA hxA haA)⟩

theorem commSub_eq_inf_of_card [Finite S] {K : Subgroup S} (hK : IsElemAbelian 2 K)
    (hK16 : Nat.card K = 16) {a : S} (ha2 : a * a = 1)
    (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hKg : ∀ y ∈ K, a * y * a⁻¹ ∈ K)
    (hcard : Nat.card (K ⊓ Subgroup.centralizer ({a} : Set S) : Subgroup S) = 4) :
    commSub K hKab a hKg = K ⊓ Subgroup.centralizer ({a} : Set S) := by
  have hdecomp := card_eq_fix_mul_comm K hKab a hKg
  rw [hK16, hcard] at hdecomp
  have hc : Nat.card (commSub K hKab a hKg) = 4 := by omega
  apply Subgroup.eq_of_le_of_card_ge
  · exact commSub_le_fix K hKab (fun x hx => sq_eq_one_of_isElemAbelian_two hK hx) a hKg
      (fun y _ => by rw [ha2, one_mul, mul_one])
  · omega

theorem mem_sup_zpowers_of_conj_mem [Finite S] {K A : Subgroup S} (hKn : K.Normal)
    (hK : IsElemAbelian 2 K) (hA : IsElemAbelian 2 A)
    (hCA : Subgroup.centralizer (A : Set S) ≤ A) {a : S} (haA : a ∈ A) (haK : a ∉ K)
    (hi : (K.subgroupOf A).index ≤ 2)
    (hsurj : ∀ k ∈ K, a * k = k * a → ∃ u ∈ K, k = a * u * a⁻¹ * u⁻¹) {t : S}
    (ht : t ∈ Subgroup.centralizer ((A ⊓ K : Subgroup S) : Set S))
    (hcj : t * a * t⁻¹ ∈ K ⊔ Subgroup.zpowers a) : t ∈ K ⊔ Subgroup.zpowers a := by
  have ha2 : a * a = 1 := sq_eq_one_of_isElemAbelian_two hA haA
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  by_contra htW
  obtain ⟨k, hk, w, hw, hkw⟩ := Subgroup.mem_sup_of_normal_left.mp hcj
  have hwcases : w = 1 ∨ w = a := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hsq : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ha2]
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left
      rw [zpow_eq_zpow_emod n hsq, h, zpow_zero]
    · right
      rw [zpow_eq_zpow_emod n hsq, h, zpow_one]
  rcases hwcases with hw1 | hw1
  ·
    rw [hw1, mul_one] at hkw
    apply haK
    have h1 : t * a * t⁻¹ ∈ K := by
      rw [← hkw]
      exact hk
    have h2 := hKn.conj_mem _ h1 t⁻¹
    have h3 : t⁻¹ * (t * a * t⁻¹) * t⁻¹⁻¹ = a := by group
    rw [h3] at h2
    exact h2
  ·
    rw [hw1] at hkw
    have hsq : (t * a * t⁻¹) * (t * a * t⁻¹) = 1 := by
      calc (t * a * t⁻¹) * (t * a * t⁻¹) = t * (a * a) * t⁻¹ := by group
        _ = 1 := by rw [ha2]; group
    have hk_sq : k * a * (k * a) = 1 := by
      rw [hkw]
      exact hsq
    have hk_inv : k⁻¹ = k := inv_eq_of_mul_eq_one_right (sq_eq_one_of_isElemAbelian_two hK hk)
    have hka : a * k = k * a := by
      have h1 := inv_eq_of_mul_eq_one_right hk_sq
      rw [mul_inv_rev, ha_inv, hk_inv] at h1
      exact h1
    obtain ⟨u, hu, hku⟩ := hsurj k hk hka
    have hcomm_inv : u * a * u⁻¹ * a⁻¹ = k := by
      calc u * a * u⁻¹ * a⁻¹ = (a * u * a⁻¹ * u⁻¹)⁻¹ := by group
        _ = k⁻¹ := by rw [← hku]
        _ = k := hk_inv
    have hua : u * a * u⁻¹ = k * a := by
      calc u * a * u⁻¹ = u * a * u⁻¹ * a⁻¹ * a := by group
        _ = k * a := by rw [hcomm_inv]
    have hconj_v : u⁻¹ * t * a * (u⁻¹ * t)⁻¹ = a := by
      calc u⁻¹ * t * a * (u⁻¹ * t)⁻¹ = u⁻¹ * (t * a * t⁻¹) * u := by group
        _ = u⁻¹ * (k * a) * u := by rw [hkw]
        _ = u⁻¹ * (u * a * u⁻¹) * u := by rw [hua]
        _ = a := by group
    have hv_a : u⁻¹ * t * a = a * (u⁻¹ * t) := mul_inv_eq_iff_eq_mul.mp hconj_v
    have huX : u ∈ Subgroup.centralizer ((A ⊓ K : Subgroup S) : Set S) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz =>
        comm_of_isElemAbelian_two hK (Subgroup.mem_inf.mp hz).2 hu
    have hvX : u⁻¹ * t ∈ Subgroup.centralizer ((A ⊓ K : Subgroup S) : Set S) :=
      mul_mem (inv_mem huX) ht
    have hvA : u⁻¹ * t ∈ A :=
      hCA (mem_centralizer_of_comm_inf hA hi haA haK hv_a
        (fun z hz => (Subgroup.mem_centralizer_iff.mp hvX z hz).symm))
    rcases mem_or_mul_mem_of_subgroupOf_index_le_two hA hi haA haK hvA with hvK | hvaK
    · apply htW
      have h1 : u * (u⁻¹ * t) ∈ K ⊔ Subgroup.zpowers a :=
        mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_left hvK)
      rwa [mul_inv_cancel_left] at h1
    · apply htW
      have hv_mem : u⁻¹ * t ∈ K ⊔ Subgroup.zpowers a := by
        have h2 := Subgroup.mul_mem_sup hvaK (Subgroup.mem_zpowers a)
        rwa [mul_assoc (u⁻¹ * t) a a, ha2, mul_one] at h2
      have h1 : u * (u⁻¹ * t) ∈ K ⊔ Subgroup.zpowers a :=
        mul_mem (Subgroup.mem_sup_left hu) hv_mem
      rwa [mul_inv_cancel_left] at h1

theorem centralizer_inf_le_sup [Finite S] (hS : IsPGroup 2 S) {K A : Subgroup S}
    (hKn : K.Normal) (hK : IsElemAbelian 2 K) (hA : IsElemAbelian 2 A)
    (hCA : Subgroup.centralizer (A : Set S) ≤ A) {a : S} (haA : a ∈ A) (haK : a ∉ K)
    (hi : (K.subgroupOf A).index ≤ 2)
    (hsurj : ∀ k ∈ K, a * k = k * a → ∃ u ∈ K, k = a * u * a⁻¹ * u⁻¹) :
    Subgroup.centralizer ((A ⊓ K : Subgroup S) : Set S) ≤ K ⊔ Subgroup.zpowers a := by
  have haX : a ∈ Subgroup.centralizer ((A ⊓ K : Subgroup S) : Set S) :=
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      comm_of_isElemAbelian_two hA (Subgroup.mem_inf.mp hz).1 haA
  have : Group.IsNilpotent (Subgroup.centralizer ((A ⊓ K : Subgroup S) : Set S)) :=
    (hS.to_subgroup _).isNilpotent
  have hNC : NormalizerCondition (Subgroup.centralizer ((A ⊓ K : Subgroup S) : Set S)) :=
    Group.normalizerCondition_of_isNilpotent
  intro x hx
  by_contra hxW
  have hWX : (K ⊔ Subgroup.zpowers a).subgroupOf
      (Subgroup.centralizer ((A ⊓ K : Subgroup S) : Set S)) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hxmem : (⟨x, hx⟩ : Subgroup.centralizer ((A ⊓ K : Subgroup S) : Set S)) ∈
        (K ⊔ Subgroup.zpowers a).subgroupOf
          (Subgroup.centralizer ((A ⊓ K : Subgroup S) : Set S)) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hxW (Subgroup.mem_subgroupOf.mp hxmem)
  obtain ⟨t', ht'n, ht'W⟩ := SetLike.exists_of_lt (hNC _ hWX)
  have haW : (⟨a, haX⟩ : Subgroup.centralizer ((A ⊓ K : Subgroup S) : Set S)) ∈
      (K ⊔ Subgroup.zpowers a).subgroupOf
        (Subgroup.centralizer ((A ⊓ K : Subgroup S) : Set S)) :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
  have hconj := (Subgroup.mem_normalizer_iff.mp ht'n ⟨a, haX⟩).mp haW
  rw [Subgroup.mem_subgroupOf] at hconj
  have hconj' : (t' : S) * a * (t' : S)⁻¹ ∈ K ⊔ Subgroup.zpowers a := hconj
  exact ht'W (Subgroup.mem_subgroupOf.mpr
    (mem_sup_zpowers_of_conj_mem hKn hK hA hCA haA haK hi hsurj t'.2 hconj'))

end Centralizer

theorem centralizer_Z_le {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S) {K₀ A : Subgroup S}
    (hKn : K₀.Normal) (hK : IsElemAbelian 2 K₀) (hK16 : Nat.card K₀ = 16)
    (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8)
    (hCA : Subgroup.centralizer (A : Set S) ≤ A) {a : S} (haA : a ∈ A) (haK : a ∉ K₀)
    (hAK : Nat.card (A ⊓ K₀ : Subgroup S) = 4) :
    Nat.card (K₀ ⊓ Subgroup.centralizer ({a} : Set S) : Subgroup S) = 4 ∧
      Subgroup.centralizer ((K₀ ⊓ Subgroup.centralizer ({a} : Set S) : Subgroup S) : Set S) ≤
        K₀ ⊔ Subgroup.zpowers a := by
  have ha2 : a * a = 1 := sq_eq_one_of_isElemAbelian_two hA haA
  have hi : (K₀.subgroupOf A).index ≤ 2 := index_subgroupOf_inf_le_two hA8 hAK
  have hZ : K₀ ⊓ Subgroup.centralizer ({a} : Set S) = A ⊓ K₀ :=
    inf_centralizer_singleton_eq hA hK hCA hi haA haK
  have hZcard : Nat.card (K₀ ⊓ Subgroup.centralizer ({a} : Set S) : Subgroup S) = 4 := by
    rw [hZ]
    exact hAK
  have hKab : ∀ x ∈ K₀, ∀ y ∈ K₀, x * y = y * x :=
    fun x hx y hy => comm_of_isElemAbelian_two hK hx hy
  have hKg : ∀ y ∈ K₀, a * y * a⁻¹ ∈ K₀ := fun y hy => hKn.conj_mem y hy a
  have hcomm : commSub K₀ hKab a hKg = K₀ ⊓ Subgroup.centralizer ({a} : Set S) :=
    commSub_eq_inf_of_card hK hK16 ha2 hKab hKg hZcard
  have hsurj : ∀ k ∈ K₀, a * k = k * a → ∃ u ∈ K₀, k = a * u * a⁻¹ * u⁻¹ := by
    intro k hk hak
    have hkC : k ∈ commSub K₀ hKab a hKg := by
      rw [hcomm]
      exact Subgroup.mem_inf.mpr ⟨hk, Subgroup.mem_centralizer_singleton_iff.mpr hak.symm⟩
    obtain ⟨u, hu, hku⟩ := (mem_commSub K₀ hKab a hKg k).mp hkC
    exact ⟨u, hu, hku⟩
  refine ⟨hZcard, ?_⟩
  rw [hZ]
  exact centralizer_inf_le_sup hS hKn hK hA hCA haA haK hi hsurj

end CFSG.EvenSporadicStandard.Fin76b
