module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.GroupTheory.PCore.CharacteristicPPrimeCore
public import CFSG.Assembly.Defs

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG

variable {G : Type*} [Group G] {p : ℕ}

theorem isCharacteristicP_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsCharacteristicP p A) : IsCharacteristicP p B := by
  unfold IsCharacteristicP at h ⊢
  intro b hb
  rw [← pCore_map_iso p e] at hb ⊢
  refine ⟨e.symm b, h ?_, by simp⟩
  rw [mem_centralizer_iff] at hb ⊢
  intro a ha
  have h1 := hb (e a) ⟨a, ha, rfl⟩
  apply e.injective
  simpa using h1

theorem map_normalizer_subgroupOf {P Q : Subgroup G} (hQP : Q ≤ P) :
    (normalizer ((Q.subgroupOf P : Subgroup P) : Set P)).map P.subtype =
      normalizer (Q : Set G) ⊓ P := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, x.2⟩
    rw [mem_normalizer_iff]
    intro q
    by_cases hq : q ∈ P
    · exact (mem_normalizer_iff.1 hx ⟨q, hq⟩)
    · have h1 : q ∉ Q := fun h => hq (hQP h)
      have h2 : (x : G) * q * (x : G)⁻¹ ∉ Q := fun h => hq (by
        have := P.mul_mem (P.mul_mem (P.inv_mem x.2) (hQP h)) x.2
        simpa [mul_assoc] using this)
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  · rintro ⟨hg, hgP⟩
    refine Subgroup.mem_map.2 ⟨⟨g, hgP⟩, ?_, rfl⟩
    rw [mem_normalizer_iff]
    intro q
    exact mem_normalizer_iff.1 hg q

theorem map_centralizer_subgroupOf {P Q : Subgroup G} (hQP : Q ≤ P) :
    (centralizer ((Q.subgroupOf P : Subgroup P) : Set P)).map P.subtype =
      centralizer (Q : Set G) ⊓ P := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, x.2⟩
    rw [mem_centralizer_iff]
    intro q hq
    exact congrArg Subtype.val (mem_centralizer_iff.1 hx ⟨q, hQP hq⟩ hq)
  · rintro ⟨hg, hgP⟩
    refine Subgroup.mem_map.2 ⟨⟨g, hgP⟩, ?_, rfl⟩
    rw [mem_centralizer_iff]
    intro q hq
    exact Subtype.ext (mem_centralizer_iff.1 hg q hq)

variable [Finite G] [Fact p.Prime]

theorem parabolic_containing_subgroup_local_characteristic_transfer {P U Q H : Subgroup G}
    (hUP : U ≤ P) (hUn : (U.subgroupOf P).Normal) (hUp : IsPGroup p U)
    (hCU : centralizer (U : Set G) ⊓ P ≤ U) (hQP : Q ≤ P) (hQp : IsPGroup p Q)
    (hH : H = normalizer (Q : Set G) ∨ H = centralizer (Q : Set G)) (hHP : H ≤ P) :
    IsCharacteristicP p P ∧ IsCharacteristicP p H ∧
      (∀ R : Subgroup H, R.Normal → ¬ p ∣ Nat.card R → R = ⊥) ∧ pPrimeCore p H = ⊥ := by
  have hp : p.Prime := Fact.out
  have hUcore : U.subgroupOf P ≤ pCore p P :=
    le_sSup ⟨hUn, hUp.comap_of_injective _ P.subtype_injective⟩
  have hPchar : IsCharacteristicP p P := by
    intro x hx
    apply hUcore
    have hxU : (x : G) ∈ centralizer (U : Set G) ⊓ P := by
      refine ⟨mem_centralizer_iff.2 fun u hu => ?_, x.2⟩
      exact congrArg Subtype.val
        (mem_centralizer_iff.1 hx ⟨u, hUP hu⟩ (hUcore (show (⟨u, hUP hu⟩ : P) ∈ U.subgroupOf P
          from hu)))
    exact hCU hxU
  have hPopen : centralizer (Open.pCore p P : Set P) ≤ Open.pCore p P := by
    exact hPchar
  have hQ'p : IsPGroup p (Q.subgroupOf P) := hQp.comap_of_injective _ P.subtype_injective
  have hHchar : IsCharacteristicP p H := by
    rcases hH with rfl | rfl
    · have hloc := RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_normalizer p hp
        hPopen (Q.subgroupOf P) hQ'p
      have hchar : IsCharacteristicP p (normalizer ((Q.subgroupOf P : Subgroup P) : Set P)) := by
        unfold IsCharacteristicP
        exact hloc
      have heq := map_normalizer_subgroupOf hQP
      rw [inf_of_le_left hHP] at heq
      exact isCharacteristicP_of_mulEquiv
        (((normalizer ((Q.subgroupOf P : Subgroup P) : Set P)).equivMapOfInjective P.subtype
          P.subtype_injective).trans (MulEquiv.subgroupCongr heq)) hchar
    · have hloc := RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_centralizer p hp
        hPopen (Q.subgroupOf P) hQ'p
      have hchar : IsCharacteristicP p (centralizer ((Q.subgroupOf P : Subgroup P) : Set P)) := by
        unfold IsCharacteristicP
        exact hloc
      have heq := map_centralizer_subgroupOf hQP
      rw [inf_of_le_left hHP] at heq
      exact isCharacteristicP_of_mulEquiv
        (((centralizer ((Q.subgroupOf P : Subgroup P) : Set P)).equivMapOfInjective P.subtype
          P.subtype_injective).trans (MulEquiv.subgroupCongr heq)) hchar
  obtain ⟨hR, hcore⟩ := characteristic_p_normal_prime_complement_trivial hHchar
  exact ⟨hPchar, hHchar, hR, hcore⟩

end CFSG.LocalAnalysis.ComponentInitial
