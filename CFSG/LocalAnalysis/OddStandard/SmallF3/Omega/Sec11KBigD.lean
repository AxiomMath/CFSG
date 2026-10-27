module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11KBigC
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralCentralOddComplement
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneSylowNormalizer

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

open scoped Pointwise

variable {G : Type} [Group G]

theorem sec11KB_card_le_sylow [Finite G] {X P Y : Subgroup G} (hP : IsSylow2Of P X)
    (hY : IsPGroup 2 Y) (hYX : Y ≤ X) : Nat.card Y ≤ Nat.card P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hP.exists_sylow
  have hY2 : IsPGroup 2 (Y.subgroupOf X) :=
    hY.of_equiv (Subgroup.subgroupOfEquivOfLe hYX).symm
  obtain ⟨S', hS'⟩ := hY2.exists_le_sylow
  have hcardY : Nat.card (Y.subgroupOf X) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv
  have hcardS : Nat.card (S : Subgroup ↥X) = Nat.card P := by
    rw [← hS, Subgroup.card_map_of_injective X.subtype_injective]
  have hcardS' : Nat.card (S' : Subgroup ↥X) = Nat.card (S : Subgroup ↥X) := by
    rw [Sylow.card_eq_multiplicity S', Sylow.card_eq_multiplicity S]
  calc Nat.card Y = Nat.card (Y.subgroupOf X) := hcardY.symm
    _ ≤ Nat.card (S' : Subgroup ↥X) := Subgroup.card_le_of_le hS'
    _ = Nat.card (S : Subgroup ↥X) := hcardS'
    _ = Nat.card P := hcardS

theorem sec11KB_dih_complement [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X) {m : ℕ}
    (hm : 2 ≤ m) (hPd : Nonempty (↥P ≃* DihedralGroup (2 ^ m))) {z : G} (hzX : z ∈ X)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ x ∈ X, x * z = z * x) :
    oddCoreIn X ⊔ P = X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hP.exists_sylow
  have hSsub : (S : Subgroup ↥X) = P.subgroupOf X := by
    change (S : Subgroup ↥X) = P.comap X.subtype
    rw [← hS, Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
  have hzX' : (⟨z, hzX⟩ : ↥X) ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2)
  have hz2' : (⟨z, hzX⟩ : ↥X) * ⟨z, hzX⟩ = 1 := by
    ext
    exact hz2
  have hz1' : (⟨z, hzX⟩ : ↥X) ≠ 1 := fun h => hz1 (Subtype.ext_iff.mp h)
  have hzo : orderOf (⟨z, hzX⟩ : ↥X) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hz2') hz1'
  have hSiso : Nonempty (DihedralGroup (2 ^ ((m + 1) - 1)) ≃* (S : Subgroup ↥X)) := by
    rw [Nat.add_sub_cancel, hSsub]
    obtain ⟨e⟩ := hPd
    exact ⟨e.symm.trans (Subgroup.subgroupOfEquivOfLe hP.1).symm⟩
  obtain ⟨N, hNnormal, ⟨hNodd, _⟩, -, -, -, hNprod, -, -⟩ :=
    CFSG.Semidihedral.Principal.dihedral_central_involution_normal_odd_complement
      S (n := m + 1) (by omega) hSiso ⟨⟨z, hzX⟩, hzX', hzo⟩
  have hN'le : N.map X.subtype ≤ X := Subgroup.map_subtype_le N
  have hN'norm : ∀ x ∈ X, ∀ y ∈ N.map X.subtype, x * y * x⁻¹ ∈ N.map X.subtype := by
    intro x hx y hy
    rcases Subgroup.mem_map.mp hy with ⟨n, hn, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hx⟩ * n * ⟨x, hx⟩⁻¹, hNnormal.conj_mem n hn ⟨x, hx⟩, rfl⟩
  have hN'odd : Odd (Nat.card (N.map X.subtype)) := by
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact hNodd
  have hcore : N.map X.subtype ≤ oddCoreIn X := sec11KB_le_oddCore hN'le hN'norm hN'odd
  refine le_antisymm (sup_le (sec11KB_oddCore_le X) hP.1) ?_
  intro x hx
  have hxprod : (⟨x, hx⟩ : ↥X) ∈ (N : Set ↥X) * (S : Set ↥X) := by
    rw [hNprod]
    exact Set.mem_univ _
  rcases Set.mem_mul.mp hxprod with ⟨n, hn, s, hs, hns⟩
  have hnG : (n : G) ∈ oddCoreIn X :=
    hcore (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
  have hsG : (s : G) ∈ P :=
    Subgroup.mem_subgroupOf.mp (hSsub ▸ hs)
  have hxmul : x = (n : G) * (s : G) := by
    have h := congrArg Subtype.val hns
    simp only [Subgroup.coe_mul] at h
    exact h.symm
  rw [hxmul]
  exact Subgroup.mul_mem_sup hnG hsG

theorem sec11KB_aut_dih {P : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (hPd : Nonempty (↥P ≃* DihedralGroup (2 ^ m))) : IsPGroup 2 (MulAut ↥P) := by
  obtain ⟨e⟩ := hPd
  exact (GorensteinWalter.dihedral_mulAut_is_twoGroup hm).of_equiv (MulAut.congr e).symm

theorem sec11KB_aut_sd {P : Subgroup G} {n : ℕ} (hn : 4 ≤ n)
    (hPd : Nonempty (↥P ≃* CFSG.Open.SemidihedralGroup n)) : IsPGroup 2 (MulAut ↥P) := by
  obtain ⟨e⟩ := hPd
  exact (Semidihedral.FieldFactorOne.semidihedral_automorphism_isPGroup hn).of_equiv
    (MulAut.congr e).symm

end CFSG.OddStandard.SmallF3.Omega
