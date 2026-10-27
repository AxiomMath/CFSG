module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.AFive

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open CFSG.EvenSporadicStandard.HNRecog.Fpf
open Equiv Equiv.Perm

private def c₂ : A5 := ⟨swap 0 1 * swap 2 3, mem_alternatingGroup.2 (by decide)⟩

private instance : DecidablePred (· ∈ Subgroup.centralizer ({c₂} : Set A5)) :=
  fun x => decidable_of_iff (c₂ * x = x * c₂)
    (by simp [Subgroup.mem_centralizer_iff])

private theorem card_centralizer_c₂ :
    Nat.card (Subgroup.centralizer ({c₂} : Set A5)) = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem sq_centralizer_c₂ :
    ∀ y : A5, y ∈ Subgroup.centralizer ({c₂} : Set A5) → y ^ 2 = 1 := by
  decide +kernel

private theorem one_ne_c₂ : (1 : A5) = c₂ → False := by decide +kernel

private theorem exponent_centralizer_c₂ :
    Monoid.exponent (Subgroup.centralizer ({c₂} : Set A5)) = 2 := by
  have h : Monoid.exponent (Subgroup.centralizer ({c₂} : Set A5)) ∣ 2 := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro g
    exact Subtype.ext (by simpa using sq_centralizer_c₂ g.1 g.2)
  haveI : Nontrivial (Subgroup.centralizer ({c₂} : Set A5)) :=
    ⟨1, ⟨c₂, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, fun hcon =>
      one_ne_c₂ (congrArg Subtype.val hcon)⟩
  have hle : Monoid.exponent (Subgroup.centralizer ({c₂} : Set A5)) ≤ 2 :=
    Nat.le_of_dvd (by decide) h
  have hlt : 1 < Monoid.exponent (Subgroup.centralizer ({c₂} : Set A5)) :=
    Monoid.one_lt_exponent
  omega

private instance isKleinFour_centralizer_c₂ :
    IsKleinFour (Subgroup.centralizer ({c₂} : Set A5)) where
  card_four := card_centralizer_c₂
  exponent_two := exponent_centralizer_c₂

private instance isKleinFour_elem2 : IsKleinFour (Elem2 2) where
  card_four := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  exponent_two := by
    have hsq : ∀ g : Elem2 2, g ^ 2 = 1 := by decide +kernel
    have h : Monoid.exponent (Elem2 2) ∣ 2 := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      exact hsq
    have hle : Monoid.exponent (Elem2 2) ≤ 2 := Nat.le_of_dvd (by decide) h
    have hlt : 1 < Monoid.exponent (Elem2 2) := Monoid.one_lt_exponent
    omega

private theorem exists_conj_to_c₂ :
    ∀ a : A5, a ≠ 1 → a ^ 2 = 1 → ∃ y : A5, y * a * y⁻¹ = c₂ := by
  decide +kernel

private theorem sq_eq_one_of_two_power_A5 {g : A5} {k : ℕ} (h : g ^ (2 ^ k) = 1) :
    g ^ 2 = 1 := by
  have hd2 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have hcases : ∀ g : A5, g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 5 = 1 := by decide +kernel
  rcases hcases g with h2 | h3 | h5
  · exact h2
  · have hd1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have h1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    rw [orderOf_eq_one_iff] at h1
    rw [h1]
    simp
  · have hd1 : orderOf g ∣ 5 := orderOf_dvd_of_pow_eq_one h5
    have hcop : Nat.Coprime 5 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have h1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    rw [orderOf_eq_one_iff] at h1
    rw [h1]
    simp

theorem sq_eq_one_of_two_power (x : A5 × A5) (k : ℕ) (hx : x ^ (2 ^ k) = 1) : x ^ 2 = 1 := by
  have hx1 : x.1 ^ (2 ^ k) = 1 := by
    have := congrArg Prod.fst hx
    simpa using this
  have hx2 : x.2 ^ (2 ^ k) = 1 := by
    have := congrArg Prod.snd hx
    simpa using this
  have h1 : x.1 ^ 2 = 1 := sq_eq_one_of_two_power_A5 hx1
  have h2 : x.2 ^ 2 = 1 := sq_eq_one_of_two_power_A5 hx2
  rw [Prod.ext_iff]
  simp only [Prod.pow_fst, Prod.pow_snd, Prod.fst_one, Prod.snd_one]
  exact ⟨h1, h2⟩

private theorem centralizer_map_mulEquiv {G : Type*} [Group G] (e : G ≃* G) (g : G) :
    (Subgroup.centralizer ({g} : Set G)).map (e : G →* G) =
      Subgroup.centralizer ({e g} : Set G) := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨w, hw, rfl⟩
    change e g * e w = e w * e g
    rw [← map_mul, ← map_mul, hw]
  · intro hz
    refine ⟨e.symm z, ?_, by simp⟩
    have h := congrArg e.symm hz
    simpa using h

private noncomputable def centralizer_mulEquiv_map {G : Type*} [Group G] (e : G ≃* G) (g : G) :
    Subgroup.centralizer ({g} : Set G) ≃* Subgroup.centralizer ({e g} : Set G) :=
  (MulEquiv.subgroupMap e (Subgroup.centralizer ({g} : Set G))).trans
    (MulEquiv.subgroupCongr (centralizer_map_mulEquiv e g))

private theorem centralizer_inl_eq_prod (a : A5) :
    Subgroup.centralizer ({((a, 1) : A5 × A5)} : Set (A5 × A5)) =
      (Subgroup.centralizer ({a} : Set A5)).prod ⊤ := by
  ext p
  constructor
  · intro hp
    rw [Subgroup.mem_centralizer_iff] at hp
    simp only [Set.mem_singleton_iff, forall_eq] at hp
    rw [Subgroup.mem_prod, Subgroup.mem_centralizer_iff]
    simp only [Subgroup.mem_top, and_true, Set.mem_singleton_iff, forall_eq]
    have := congrArg Prod.fst hp
    simpa using this
  · intro hp
    rw [Subgroup.mem_prod] at hp
    rw [Subgroup.mem_centralizer_iff] at hp ⊢
    simp only [Subgroup.mem_top, and_true, Set.mem_singleton_iff, forall_eq] at hp ⊢
    rw [Prod.ext_iff]
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_one, Prod.snd_one, one_mul, mul_one]
    exact ⟨hp, trivial⟩

private noncomputable def centralizer_inl_prod (a : A5) :
    Subgroup.centralizer ({((a, 1) : A5 × A5)} : Set (A5 × A5)) ≃*
      Subgroup.centralizer ({a} : Set A5) × A5 :=
  (MulEquiv.subgroupCongr (centralizer_inl_eq_prod a)).trans <|
    (Subgroup.prodEquiv (Subgroup.centralizer ({a} : Set A5)) (⊤ : Subgroup A5)).trans <|
      (MulEquiv.prodCongr (MulEquiv.refl (Subgroup.centralizer ({a} : Set A5)))
        Subgroup.topEquiv)

theorem nonempty_mulEquiv_centralizer_inl {a : A5} (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) :
    Nonempty (Subgroup.centralizer ({((a, 1) : A5 × A5)} : Set (A5 × A5)) ≃* Elem2 2 × A5) := by
  obtain ⟨y, hy⟩ := exists_conj_to_c₂ a ha1 ha2
  have e1 : Subgroup.centralizer ({a} : Set A5) ≃*
      Subgroup.centralizer ({c₂} : Set A5) := by
    have h := centralizer_mulEquiv_map (MulAut.conj y) a
    have hy' : (MulAut.conj y) a = c₂ := by simpa [MulAut.conj_apply] using hy
    rwa [hy'] at h
  obtain ⟨e2⟩ := IsKleinFour.nonempty_mulEquiv
    (G₁ := Subgroup.centralizer ({c₂} : Set A5)) (G₂ := Elem2 2)
  exact ⟨(centralizer_inl_prod a).trans
    ((MulEquiv.prodCongr e1 (MulEquiv.refl A5)).trans
      (MulEquiv.prodCongr e2 (MulEquiv.refl A5)))⟩

theorem nonempty_mulEquiv_centralizer_inr {a : A5} (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) :
    Nonempty (Subgroup.centralizer ({((1, a) : A5 × A5)} : Set (A5 × A5)) ≃* Elem2 2 × A5) := by
  have hcomm : (MulEquiv.prodComm : A5 × A5 ≃* A5 × A5) (1, a) = (a, 1) := by
    simp [MulEquiv.coe_prodComm]
  have ec : Subgroup.centralizer ({((1, a) : A5 × A5)} : Set (A5 × A5)) ≃*
      Subgroup.centralizer ({((a, 1) : A5 × A5)} : Set (A5 × A5)) := by
    have h := centralizer_mulEquiv_map (MulEquiv.prodComm : A5 × A5 ≃* A5 × A5) (1, a)
    rwa [hcomm] at h
  obtain ⟨e⟩ := nonempty_mulEquiv_centralizer_inl ha1 ha2
  exact ⟨ec.trans e⟩

end CFSG.EvenSporadicStandard.HNRecog.ML1
