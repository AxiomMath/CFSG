module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Basic

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

variable {G : Type} [Group G]

theorem exists_mem_conj_mul {L1 : Subgroup G} {a : G} [Finite G]
    (hL1c : ∀ x ∈ L1, ∀ y ∈ L1, x * y = y * x) (hL1s : ∀ x ∈ L1, x * x = 1)
    (hL1card : Nat.card L1 = 256) (ha2 : a * a = 1) (haN : ∀ m, m ∈ L1 ↔ a * m * a⁻¹ ∈ L1)
    (hU : Nat.card ↥(centralizer ({a} : Set G) ⊓ L1) = 16) {l : G} (hl : l ∈ L1)
    (hal : (a * l) * (a * l) = 1) : ∃ m ∈ L1, m * a * m⁻¹ = a * l := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hN' : ∀ m ∈ L1, a * m * a ∈ L1 := fun m hm => by
    have := (haN m).1 hm
    rwa [hai] at this
  let φ : ↥L1 →* ↥L1 :=
    { toFun := fun m => ⟨a * (m : G) * a * (m : G), L1.mul_mem (hN' m m.2) m.2⟩
      map_one' := by
        apply Subtype.ext
        show a * (1 : G) * a * 1 = 1
        rw [mul_one, mul_one, ha2]
      map_mul' := by
        intro m n
        apply Subtype.ext
        show a * ((m : G) * n) * a * ((m : G) * n) =
          a * (m : G) * a * (m : G) * (a * (n : G) * a * (n : G))
        have h1 : (m : G) * (a * (n : G) * a) = a * (n : G) * a * m :=
          hL1c _ m.2 _ (hN' n n.2)
        calc a * ((m : G) * n) * a * ((m : G) * n)
            = a * m * (a * a) * n * a * (m * n) := by rw [ha2]; group
          _ = a * m * a * (a * n * a) * (m * n) := by group
          _ = a * m * a * ((a * n * a) * m) * n := by group
          _ = a * m * a * (m * (a * n * a)) * n := by rw [← h1]
          _ = a * (m : G) * a * (m : G) * (a * (n : G) * a * (n : G)) := by group }
  have hker : φ.ker = (centralizer ({a} : Set G) ⊓ L1).subgroupOf L1 := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      mem_centralizer_singleton_iff]
    have hm2 := hL1s m m.2
    constructor
    · intro h
      have h1 : a * (m : G) * a * m = 1 := congrArg Subtype.val h
      refine ⟨?_, m.2⟩
      have h2 : a * (m : G) * a = (m : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [inv_eq_of_mul_eq_one_right hm2] at h2
      calc (m : G) * a = a * a * (m * a) := by rw [ha2, one_mul]
        _ = a * (a * m * a) := by group
        _ = a * m := by rw [h2]
    · rintro ⟨h, -⟩
      apply Subtype.ext
      show a * (m : G) * a * m = 1
      calc a * (m : G) * a * m = (m * a) * a * m := by rw [← h]
        _ = m * (a * a) * m := by group
        _ = m * m := by rw [ha2, mul_one]
        _ = 1 := hm2
  have hkcard : Nat.card φ.ker = 16 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : centralizer ({a} : Set G) ⊓ L1 ≤ L1)).toEquiv, hU]
  have hrcard : Nat.card φ.range = 16 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hkcard, hL1card] at h
    omega
  have hrle : φ.range ≤ (centralizer ({a} : Set G) ⊓ L1).subgroupOf L1 := by
    rintro _ ⟨m, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_singleton_iff]
    refine ⟨?_, (φ m).2⟩
    show a * (m : G) * a * m * a = a * (a * (m : G) * a * m)
    have h1 : a * (m : G) * a * m = m * (a * (m : G) * a) := hL1c _ (hN' m m.2) _ m.2
    calc a * (m : G) * a * m * a = m * (a * m * a) * a := by rw [h1]
      _ = m * a * m * (a * a) := by group
      _ = m * a * m := by rw [ha2, mul_one]
      _ = (a * a) * m * a * m := by rw [ha2, one_mul]
      _ = a * (a * (m : G) * a * m) := by group
  have hreq : φ.range = (centralizer ({a} : Set G) ⊓ L1).subgroupOf L1 := by
    refine Subgroup.eq_of_le_of_card_ge hrle ?_
    rw [hrcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : centralizer ({a} : Set G) ⊓ L1 ≤ L1)).toEquiv, hU]
  have hlc : (⟨l, hl⟩ : ↥L1) ∈ (centralizer ({a} : Set G) ⊓ L1).subgroupOf L1 := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_singleton_iff]
    refine ⟨?_, hl⟩
    have h1 : a * l * a * l = 1 := by
      calc a * l * a * l = (a * l) * (a * l) := by group
        _ = 1 := hal
    have h2 : a * l * a = l⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [inv_eq_of_mul_eq_one_right (hL1s l hl)] at h2
    calc l * a = a * a * (l * a) := by rw [ha2, one_mul]
      _ = a * (a * l * a) := by group
      _ = a * l := by rw [h2]
  rw [← hreq] at hlc
  obtain ⟨m, hm⟩ := hlc
  have hm' : a * (m : G) * a * (m : G) = l := congrArg Subtype.val hm
  refine ⟨m, m.2, ?_⟩
  have hmi : (m : G)⁻¹ = m := inv_eq_of_mul_eq_one_right (hL1s m m.2)
  rw [hmi]
  calc (m : G) * a * m = (a * a) * m * a * m := by rw [ha2, one_mul]
    _ = a * (a * m * a * m) := by group
    _ = a * l := by rw [hm']

end CFSG.EvenSporadicStandard.M22Std
