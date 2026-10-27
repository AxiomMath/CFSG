module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RL1

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem normal_sup_subgroupOf_normalizer {G : Type} [Group G] (D E : Subgroup G) :
    (D.subgroupOf (normalizer ((D ⊔ E : Subgroup G) : Set G)) ⊔
      E.subgroupOf (normalizer ((D ⊔ E : Subgroup G) : Set G))).Normal := by
  have hDM : D ≤ normalizer ((D ⊔ E : Subgroup G) : Set G) :=
    le_trans le_sup_left (Subgroup.le_normalizer (H := D ⊔ E))
  have hEM : E ≤ normalizer ((D ⊔ E : Subgroup G) : Set G) :=
    le_trans le_sup_right (Subgroup.le_normalizer (H := D ⊔ E))
  rw [← Subgroup.subgroupOf_sup hDM hEM]
  exact inferInstance

lemma TS16RYPG_subgroupOf_map {G : Type} [Group G] (M : Subgroup G) (Q : Subgroup ↥M) :
    (Q.map M.subtype).subgroupOf M = Q :=
  Subgroup.comap_map_eq_self_of_injective M.subtype_injective Q

lemma TS16RYPG_map_inf_centralizer {G : Type} [Group G] (M : Subgroup G) (Q : Subgroup ↥M)
    (y : ↥M) :
    Q.map M.subtype ⊓ Subgroup.centralizer ({M.subtype y} : Set G) =
      (Q ⊓ Subgroup.centralizer ({y} : Set ↥M)).map M.subtype := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hxQ
    rw [Subgroup.mem_centralizer_singleton_iff] at hxC
    refine Subgroup.mem_map.mpr ⟨a, Subgroup.mem_inf.mpr ⟨ha, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hxC
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨haQ, haC⟩ := Subgroup.mem_inf.mp ha
    rw [Subgroup.mem_centralizer_singleton_iff] at haC
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨a, haQ, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val haC

theorem clauses_to_G {G : Type} [Group G] [Finite G] {M : Subgroup G} {z : G} (hzM : z ∈ M)
    (hz2 : z * z = 1)
    (hcard : ∀ (g : G) (R : Subgroup G), IsPGroup 2 R → R ≤ centralizer ({g * z * g⁻¹} : Set G) →
      Nat.card ↥R ≤ 512)
    (hP : ∃ Q' P : Subgroup ↥M, IsPGroup 2 Q' ∧ ¬ 2 ∣ Q'.index ∧ (⟨z, hzM⟩ : ↥M) ∈ Q' ∧
      P ≤ Q' ∧ P.relIndex Q' = 2 ∧ (⟨z, hzM⟩ : ↥M) ∉ P ∧
      (∃ R : Subgroup ↥M, IsPGroup 2 R ∧ R ≤ centralizer ({(⟨z, hzM⟩ : ↥M)} : Set ↥M) ∧
        Nat.card ↥R = 512) ∧
      (∀ η ∈ P, η * η = 1 → η ≠ 1 → ∃ R : Subgroup ↥M, IsPGroup 2 R ∧
        R ≤ centralizer ({η} : Set ↥M) ∧ 1024 ≤ Nat.card ↥R) ∧
      (∀ y ∈ Q', y * y = 1 → y ∉ P →
        512 ≤ Nat.card ↥(Q' ⊓ centralizer ({y} : Set ↥M)) →
          ∃ m : ↥M, y = m * (⟨z, hzM⟩ : ↥M) * m⁻¹)) :
    ∃ (Q'' P'' : Subgroup G), Q'' ≤ M ∧ IsPGroup 2 Q'' ∧ ¬ 2 ∣ (Q''.subgroupOf M).index ∧
      z ∈ Q'' ∧ P'' ≤ Q'' ∧ P''.relIndex Q'' = 2 ∧ z ∉ P'' ∧
      (∃ R : Subgroup G, IsPGroup 2 R ∧ R ≤ M ⊓ centralizer ({z} : Set G) ∧ Nat.card ↥R = 512) ∧
      (∀ y ∈ Q'', (∃ g : G, y = g * z * g⁻¹) →
        Nat.card ↥(Q'' ⊓ centralizer ({y} : Set G)) = 512 → ∃ m ∈ M, y = m * z * m⁻¹) ∧
      ∀ η ∈ P'', η * η = 1 → η ≠ 1 →
        ∃ R : Subgroup G, IsPGroup 2 R ∧ R ≤ centralizer ({η} : Set G) ∧ 512 < Nat.card ↥R := by
  obtain ⟨Q', P, hQ', hQidx, hzQ, hPQ, hrel, hzP, hR512, hPcl, hQcl⟩ := hP
  have hz1 : z ≠ 1 := by
    intro h
    apply hzP
    have h' : (⟨z, hzM⟩ : ↥M) = 1 := Subtype.ext h
    rw [h']
    exact P.one_mem
  refine ⟨Q'.map M.subtype, P.map M.subtype, Subgroup.map_subtype_le Q', hQ'.map M.subtype,
    ?_, ?_, Subgroup.map_mono hPQ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [TS16RYPG_subgroupOf_map M Q']
    exact hQidx
  · exact Subgroup.mem_map.mpr ⟨⟨z, hzM⟩, hzQ, rfl⟩
  · rw [Subgroup.relIndex_map_map_of_injective P Q' M.subtype_injective]
    exact hrel
  · intro hz
    obtain ⟨a, ha, ha'⟩ := Subgroup.mem_map.mp hz
    apply hzP
    have hae : a = ⟨z, hzM⟩ := Subtype.ext ha'
    rw [← hae]
    exact ha
  · obtain ⟨R₀, hR₀, hR₀c, hR₀card⟩ := hR512
    refine ⟨R₀.map M.subtype, hR₀.map M.subtype, ?_, ?_⟩
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_inf.mpr ⟨r.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h3 := Subgroup.mem_centralizer_singleton_iff.mp (hR₀c hr)
      exact congrArg Subtype.val h3
    · rw [Subgroup.card_map_of_injective M.subtype_injective]
      exact hR₀card
  · rintro y hy ⟨g, hg⟩ hcardy
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    have hyy : y' * y' = 1 := by
      apply M.subtype_injective
      rw [map_mul, map_one, hg]
      have h1 : g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      rw [h1, hz2]
      simp
    by_cases hyP : y' ∈ P
    · exfalso
      have hy'1 : y' ≠ 1 := by
        intro h1
        apply hz1
        have h2 : g * z * g⁻¹ = 1 := by rw [← hg, h1, map_one]
        calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
          _ = 1 := by rw [h2]; group
      obtain ⟨R, hR, hRc, hRcard⟩ := hPcl y' hyP hyy hy'1
      have hRp : IsPGroup 2 (R.map M.subtype) := hR.map M.subtype
      have hRcen : R.map M.subtype ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
        intro x hx
        obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
        rw [← hg, Subgroup.mem_centralizer_singleton_iff]
        have h3 := Subgroup.mem_centralizer_singleton_iff.mp (hRc hr)
        exact congrArg Subtype.val h3
      have hle := hcard g (R.map M.subtype) hRp hRcen
      rw [Subgroup.card_map_of_injective M.subtype_injective] at hle
      omega
    · have hle : 512 ≤ Nat.card ↥(Q' ⊓ Subgroup.centralizer ({y'} : Set ↥M)) := by
        rw [TS16RYPG_map_inf_centralizer M Q' y',
          Subgroup.card_map_of_injective M.subtype_injective] at hcardy
        exact le_of_eq hcardy.symm
      obtain ⟨m, hm⟩ := hQcl y' hy' hyy hyP hle
      exact ⟨(m : G), m.2, congrArg Subtype.val hm⟩
  · rintro η hη hηη hη1
    obtain ⟨η', hη', rfl⟩ := Subgroup.mem_map.mp hη
    have hηη' : η' * η' = 1 := by
      apply M.subtype_injective
      rw [map_mul, map_one]
      exact hηη
    have hη'1 : η' ≠ 1 := by
      intro h1
      apply hη1
      rw [h1, map_one]
    obtain ⟨R, hR, hRc, hRcard⟩ := hPcl η' hη' hηη' hη'1
    refine ⟨R.map M.subtype, hR.map M.subtype, ?_, ?_⟩
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h3 := Subgroup.mem_centralizer_singleton_iff.mp (hRc hr)
      exact congrArg Subtype.val h3
    · rw [Subgroup.card_map_of_injective M.subtype_injective]
      omega

end CFSG.EvenSporadicStandard.Fin76b
