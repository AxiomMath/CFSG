module

public import CFSG.RankThree.OddKernel.OddLift
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {X Y : Type*} [Group X] [Group Y]

private theorem map_centralizer_eq_of_odd_ker [Finite X] (π : X →* Y)
    (hπ : Function.Surjective π) (hker : Odd (Nat.card π.ker)) {A : Subgroup X}
    (hA : IsPGroup 2 A) :
    (centralizer (A : Set X)).map π = centralizer ((A.map π : Subgroup Y) : Set Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ fun e he => ?_
  · rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff] at hc
    rw [mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, hc t ht]
  obtain ⟨y, rfl⟩ := hπ e
  rw [mem_centralizer_iff] at he
  obtain ⟨c, hc, hfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 2 hA
    (MulAut.conj.comp A.subtype) π.ker hker.not_two_dvd_nat y).2 (by
      rintro ⟨a, ha⟩ x hx
      have hxy : π x = π y := by
        have h := MonoidHom.mem_ker.1 hx
        rw [map_mul, map_inv, inv_mul_eq_one] at h
        exact h.symm
      have hcomm : π a * π y = π y * π a := he (π a) ⟨a, ha, rfl⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      change (π y)⁻¹ * π (a * x * a⁻¹) = 1
      rw [map_mul, map_mul, map_inv, hxy, hcomm]
      group)
  refine ⟨c, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_centralizer_iff]
    intro t ht
    have h := hfix ⟨t, ht⟩
    change t * c * t⁻¹ = c at h
    calc t * c = t * c * t⁻¹ * t := by group
      _ = c * t := by rw [h]
  · have h := MonoidHom.mem_ker.1 hc
    rw [map_mul, map_inv, inv_mul_eq_one] at h
    exact h.symm

theorem z4i_centralizer_map_eq [Finite X] (π : X →* Y) (hπ : Function.Surjective π)
    (hker : Odd (Nat.card π.ker)) {A : Subgroup X} (hA : IsPGroup 2 A) :
    centralizer ((A.map π : Subgroup Y) : Set Y) = (centralizer (A : Set X)).map π :=
  (map_centralizer_eq_of_odd_ker π hπ hker hA).symm

theorem z4i_lift_two_cent [Finite X] (π : X →* Y) (hπ : Function.Surjective π)
    (hker : Odd (Nat.card π.ker)) {A : Subgroup X} (hA : IsPGroup 2 A) {P : Subgroup Y}
    (hP : IsPGroup 2 P) (hPc : P ≤ centralizer ((A.map π : Subgroup Y) : Set Y)) :
    ∃ P' : Subgroup X, IsPGroup 2 P' ∧ P'.map π = P ∧ P' ≤ centralizer (A : Set X) ∧
      Function.Injective (π.comp P'.subtype) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z : Subgroup X := centralizer (A : Set X)
  let π' : Z →* Y := π.comp Z.subtype
  have hCen : centralizer ((A.map π : Subgroup Y) : Set Y) = Z.map π :=
    z4i_centralizer_map_eq π hπ hker hA
  have hPle : P ≤ Z.map π := hCen ▸ hPc
  have hrange : π'.range = Z.map π := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, z.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hPle' : P ≤ π'.range := by rw [hrange]; exact hPle
  have hker' : Odd (Nat.card π'.rangeRestrict.ker) := by
    rw [MonoidHom.ker_rangeRestrict]
    have hmap_le : ((π.comp Z.subtype).ker).map Z.subtype ≤ π.ker := by
      rintro x ⟨z, hz, rfl⟩
      exact hz
    have hcard : Nat.card (((π.comp Z.subtype).ker).map Z.subtype)
        = Nat.card ((π.comp Z.subtype).ker) :=
      Subgroup.card_map_of_injective Z.subtype_injective
    have hdvd : Nat.card ((π.comp Z.subtype).ker) ∣ Nat.card π.ker := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hmap_le
    exact hker.of_dvd_nat hdvd
  have hE : IsPGroup 2 (P.subgroupOf π'.range) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPle').symm
  obtain ⟨A₀, hA₀, hA₀map, -⟩ := CFSG.RankThree.OddKernel.exists_two_subgroup_map_eq
    π'.rangeRestrict π'.rangeRestrict_surjective hker' (P.subgroupOf π'.range) hE
  refine ⟨A₀.map Z.subtype, hA₀.map Z.subtype, ?_, Subgroup.map_subtype_le A₀, ?_⟩
  · have hcomp : A₀.map π' = (A₀.map π'.rangeRestrict).map π'.range.subtype := by
      rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]
    rw [Subgroup.map_map]
    change A₀.map π' = P
    rw [hcomp, hA₀map, Subgroup.map_subgroupOf_eq_of_le hPle']
  · exact CFSG.RankThree.OddKernel.injective_restrict_of_odd π hker (hA₀.map Z.subtype)

theorem z4i_lift_two_ge [Finite X] (π : X →* Y) (hπ : Function.Surjective π)
    (hker : Odd (Nat.card π.ker)) {A : Subgroup X} (hA : IsPGroup 2 A) {P : Subgroup Y}
    (hP : IsPGroup 2 P) (hAP : A.map π ≤ P) :
    ∃ P' : Subgroup X, IsPGroup 2 P' ∧ A ≤ P' ∧ P'.map π = P ∧
      Function.Injective (π.comp P'.subtype) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X₁ : Subgroup X := P.comap π
  have hA_le : A ≤ X₁ := fun a ha => hAP (Subgroup.mem_map_of_mem π ha)
  have hA' : IsPGroup 2 (A.subgroupOf X₁) :=
    hA.of_equiv (Subgroup.subgroupOfEquivOfLe hA_le).symm
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hA'
  have htop : (⊤ : Subgroup P).map P.subtype = P := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  refine ⟨(S : Subgroup X₁).map X₁.subtype, S.2.map X₁.subtype, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hA_le]
    exact Subgroup.map_mono hS
  · let ψ : X₁ →* P := (π.comp X₁.subtype).codRestrict P (fun x => x.2)
    have hψ : Function.Surjective ψ := by
      intro p
      obtain ⟨x, hx⟩ := hπ (p : Y)
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      rw [Subgroup.mem_comap, hx]
      exact p.2
    have hSψ : ((S.mapSurjective hψ : Sylow 2 P) : Subgroup P) = ⊤ :=
      ((S.mapSurjective hψ).3 (hP.of_equiv Subgroup.topEquiv.symm) le_top).symm
    have hmap : (S : Subgroup X₁).map ψ = ⊤ := by
      rw [← Sylow.coe_mapSurjective hψ S]
      exact hSψ
    have hcomp : P.subtype.comp ψ = π.comp X₁.subtype := by ext x; rfl
    rw [Subgroup.map_map, ← hcomp, ← Subgroup.map_map, hmap, htop]
  · exact CFSG.RankThree.OddKernel.injective_restrict_of_odd π hker (S.2.map X₁.subtype)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
