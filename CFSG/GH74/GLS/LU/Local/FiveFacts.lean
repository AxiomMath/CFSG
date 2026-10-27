module

public import CFSG.GH74.GLS.LU.Local.FiveBundles

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

variable {G : Type} [Group G]

theorem mem_cjL {g : G} {A : Subgroup G} {x : G} : x ∈ cjL g A ↔ g⁻¹ * x * g ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have : g⁻¹ * (g * a * g⁻¹) * g = a := by group
    simpa [MulAut.conj_apply, this] using ha
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply]; group⟩

theorem mem_cjL_self {g : G} {A : Subgroup G} {x : G} (hx : x ∈ A) : g * x * g⁻¹ ∈ cjL g A :=
  ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem card_cjL (g : G) (A : Subgroup G) : Nat.card ↥(cjL g A) = Nat.card ↥A :=
  (Nat.card_congr ((MulAut.conj g).subgroupMap A).toEquiv).symm

theorem cjL_cjL (g h : G) (A : Subgroup G) : cjL g (cjL h A) = cjL (g * h) A := by
  ext x
  simp only [mem_cjL]
  have : (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h := by group
  rw [this]

theorem cjL_sup (g : G) (A B : Subgroup G) : cjL g (A ⊔ B) = cjL g A ⊔ cjL g B :=
  Subgroup.map_sup _ _ _

theorem cjL_inf (g : G) (A B : Subgroup G) : cjL g (A ⊓ B) = cjL g A ⊓ cjL g B :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective

theorem cjL_one (A : Subgroup G) : cjL (1 : G) A = A := by
  ext x; simp [mem_cjL]

theorem cjL_mono (g : G) {A B : Subgroup G} (h : A ≤ B) : cjL g A ≤ cjL g B :=
  Subgroup.map_mono h

theorem cjL_le_iff (g : G) {A B : Subgroup G} : cjL g A ≤ cjL g B ↔ A ≤ B := by
  constructor
  · intro h x hx
    have : g * x * g⁻¹ ∈ cjL g B := h (mem_cjL_self hx)
    simpa [mem_cjL] using this
  · exact cjL_mono g

theorem cjL_inj (g : G) {A B : Subgroup G} : cjL g A = cjL g B ↔ A = B := by
  constructor
  · intro h; exact le_antisymm ((cjL_le_iff g).mp h.le) ((cjL_le_iff g).mp h.ge)
  · rintro rfl; rfl

theorem card_sup_mul_card_inf' {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAB
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAB
  have he := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hAB).toEquiv
  change B.relIndex A = B.relIndex (A ⊔ B) at he
  have h1 := Subgroup.relIndex_mul_card B (A ⊔ B)
  have h2 := Subgroup.relIndex_mul_card B A
  rw [inf_eq_left.mpr le_sup_right] at h1
  rw [← h1, ← he, ← h2, inf_comm]
  ring

theorem le_normalizer_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ≤ Subgroup.normalizer (B : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    have : a * b * a⁻¹ = b := by rw [h a ha b hb]; group
    rw [this]; exact hb
  · intro hb
    have hc := h a ha _ hb
    have : a⁻¹ * (a * b * a⁻¹) * a = a * b * a⁻¹ := by
      calc a⁻¹ * (a * b * a⁻¹) * a = a⁻¹ * ((a * b * a⁻¹) * a) := by group
        _ = a⁻¹ * (a * (a * b * a⁻¹)) := by rw [← hc]
        _ = a * b * a⁻¹ := by group
    have hb' : b = a⁻¹ * (a * b * a⁻¹) * a := by group
    rw [hb', this]
    exact hb

theorem card_sup_of_commute_disjoint {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hd : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have := card_sup_mul_card_inf' (le_normalizer_of_commute h)
  rw [hd, Subgroup.card_bot, mul_one] at this
  exact this

@[expose] def HInv (H A : Subgroup G) : Prop := ∀ h ∈ H, cjL h A = A

theorem HInv.sup {H A B : Subgroup G} (hA : HInv H A) (hB : HInv H B) : HInv H (A ⊔ B) :=
  fun h hh => by rw [cjL_sup, hA h hh, hB h hh]

theorem HInv.conj {H A : Subgroup G} {n : G} (hn : cjL n H = H) (hA : HInv H A) :
    HInv H (cjL n A) := by
  intro h hh
  have h' : n⁻¹ * h * n ∈ H := by
    have : h ∈ cjL n H := by rw [hn]; exact hh
    exact mem_cjL.mp this
  rw [cjL_cjL]
  have : h * n = n * (n⁻¹ * h * n) := by group
  rw [this, ← cjL_cjL, hA _ h']

theorem HInv.mem {H A : Subgroup G} (hA : HInv H A) {h x : G} (hh : h ∈ H) (hx : x ∈ A) :
    h * x * h⁻¹ ∈ A := by
  have : h * x * h⁻¹ ∈ cjL h A := mem_cjL_self hx
  rwa [hA h hh] at this

theorem centralizes_of_five_group {P X : Subgroup G} (hP : IsPGroup 5 ↥P) (hX : Nat.card ↥X = 5)
    (hn : P ≤ normalizer (X : Set G)) : ∀ r ∈ P, ∀ x ∈ X, r * x = x * r := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcyc : IsCyclic ↥X := isCyclic_of_prime_card hX
  have hfin : Finite ↥X := Nat.finite_of_card_ne_zero (by omega)
  intro r hr x hx
  let r' : ↥(normalizer (X : Set G)) := ⟨r, hn hr⟩
  obtain ⟨n, hn5⟩ := hP ⟨r, hr⟩
  have hrn : r ^ (5 ^ n) = 1 := by simpa using congrArg Subtype.val hn5
  have hr'n : r' ^ (5 ^ n) = 1 := Subtype.ext (by simpa using hrn)
  have hd1 : orderOf (X.normalizerMonoidHom r') ∣ 5 ^ n :=
    (orderOf_map_dvd _ _).trans (orderOf_dvd_of_pow_eq_one hr'n)
  have hd2 : orderOf (X.normalizerMonoidHom r') ∣ 4 := by
    have := orderOf_dvd_natCard (X.normalizerMonoidHom r')
    rwa [IsCyclic.card_mulAut, hX, Nat.totient_prime (by norm_num)] at this
  have hd : orderOf (X.normalizerMonoidHom r') = 1 := by
    have h3 : orderOf (X.normalizerMonoidHom r') ∣ Nat.gcd (5 ^ n) 4 := Nat.dvd_gcd hd1 hd2
    have h4 : Nat.gcd (5 ^ n) 4 = 1 := by
      apply Nat.Coprime.pow_left; norm_num
    rw [h4] at h3
    exact Nat.dvd_one.mp h3
  have h1 : X.normalizerMonoidHom r' = 1 := orderOf_eq_one_iff.mp hd
  have h2 : ((X.normalizerMonoidHom r' ⟨x, hx⟩ : ↥X) : G) = r * x * r⁻¹ := by simp [r']
  rw [h1] at h2
  have h3 : r * x * r⁻¹ = x := by simpa using h2.symm
  calc r * x = (r * x * r⁻¹) * r := by group
    _ = x * r := by rw [h3]

end CFSG.GH74.GLS.LU.Local.Five
