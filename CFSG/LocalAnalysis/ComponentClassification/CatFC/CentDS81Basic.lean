module

public import CFSG.Foundations.Basic
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG

@[expose] def IsCo2Shape (n : ℕ) : Prop :=
  ∃ k : ℕ, n = 2 ^ k * 42305421312000

theorem card_eq_pow_two_mul {C G : Type*} [Group C] [Finite C] [Group G]
    (e : C ⧸ pCore 2 C ≃* G) : ∃ k : ℕ, Nat.card C = 2 ^ k * Nat.card G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := C)).exists_card_eq
  refine ⟨k, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 C), hk,
    Nat.card_congr e.toEquiv, mul_comm]

theorem isCo2Shape_of_quotient {C G : Type*} [Group C] [Finite C] [Group G]
    (e : C ⧸ pCore 2 C ≃* G) (hG : Nat.card G = 42305421312000) : IsCo2Shape (Nat.card C) := by
  obtain ⟨k, hk⟩ := card_eq_pow_two_mul e
  exact ⟨k, by rw [hk, hG]⟩

namespace IsCo2Shape

variable {n : ℕ}

theorem dvd (h : IsCo2Shape n) : 42305421312000 ∣ n := by
  obtain ⟨k, rfl⟩ := h
  exact Dvd.intro_left _ rfl

theorem not_dvd_of_prime (h : IsCo2Shape n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : ¬ p ∣ 42305421312000) : ¬ p ∣ n := by
  obtain ⟨k, rfl⟩ := h
  intro hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1))
  · exact hN h1

theorem not_dvd_thirteen (h : IsCo2Shape n) : ¬ 13 ∣ n :=
  h.not_dvd_of_prime (by norm_num) (by norm_num) (by norm_num)

theorem not_dvd_seventeen (h : IsCo2Shape n) : ¬ 17 ∣ n :=
  h.not_dvd_of_prime (by norm_num) (by norm_num) (by norm_num)

theorem not_dvd_pow_five_four (h : IsCo2Shape n) : ¬ 5 ^ 4 ∣ n := by
  obtain ⟨k, rfl⟩ := h
  intro hd
  have hcop : Nat.Coprime (5 ^ 4) (2 ^ k) :=
    Nat.Coprime.pow _ _ (by norm_num)
  have h5 : 5 ^ 4 ∣ 42305421312000 := hcop.dvd_of_dvd_mul_left hd
  revert h5
  norm_num

end IsCo2Shape

section Transport

variable {G H : Type*} [Group G] [Group H]

theorem map_centralizer_singleton (φ : G ≃* H) (g : G) :
    (centralizer ({g} : Set G)).map φ.toMonoidHom = centralizer ({φ g} : Set H) := by
  ext y
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg φ h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h'
  · intro h
    apply φ.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h

@[expose] noncomputable def centEquiv (φ : G ≃* H) (g : G) :
    centralizer ({g} : Set G) ≃* centralizer ({φ g} : Set H) :=
  (φ.subgroupMap _).trans (MulEquiv.subgroupCongr (map_centralizer_singleton φ g))

theorem card_centralizer_eq (φ : G ≃* H) (g : G) :
    Nat.card (centralizer ({g} : Set G)) = Nat.card (centralizer ({φ g} : Set H)) :=
  Nat.card_congr (centEquiv φ g).toEquiv

theorem isMulCommutative_pCore_of_mulEquiv (φ : G ≃* H) (h : IsMulCommutative (pCore 2 G)) :
    IsMulCommutative (pCore 2 H) := by
  have hmap : (pCore 2 G).map φ.toMonoidHom = pCore 2 H := pCore_map_iso 2 φ
  refine ⟨⟨fun x y => ?_⟩⟩
  have hx : (x : H) ∈ (pCore 2 G).map φ.toMonoidHom := by rw [hmap]; exact x.2
  have hy : (y : H) ∈ (pCore 2 G).map φ.toMonoidHom := by rw [hmap]; exact y.2
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, hb, hby⟩ := hy
  apply Subtype.ext
  show (x : H) * y = y * x
  rw [← hax, ← hby]
  show φ a * φ b = φ b * φ a
  rw [← map_mul, ← map_mul]
  exact congrArg φ (congrArg Subtype.val (h.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))

end Transport

theorem not_isMulCommutative_of_isExtraspecialPGroup {Q : Type*} [Group Q] {p : ℕ}
    (hQ : IsExtraspecialPGroup p Q) (hcard : Nat.card Q ≠ p) : ¬ IsMulCommutative Q := by
  intro hc
  obtain ⟨-, -, -, hZ⟩ := hQ
  have h1 : center Q = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [mem_center_iff]
    intro g
    exact hc.is_comm.comm g x
  apply hcard
  rw [← hZ, h1]
  exact (Nat.card_congr (Subgroup.topEquiv).toEquiv).symm

theorem not_isMulCommutative_pCore_of_normal {C : Type*} [Group C] (Q : Subgroup C) [Q.Normal]
    (hQ : IsPGroup 2 Q) (hnc : ¬ IsMulCommutative Q) : ¬ IsMulCommutative (pCore 2 C) := by
  intro hab
  have hle : Q ≤ pCore 2 C := le_sSup ⟨inferInstance, hQ⟩
  apply hnc
  refine ⟨⟨fun x y => ?_⟩⟩
  apply Subtype.ext
  show (x : C) * y = y * x
  exact congrArg Subtype.val
    (hab.is_comm.comm ⟨x, hle x.2⟩ ⟨y, hle y.2⟩)

end CFSG.ComponentClassification.CatFC.DS81
