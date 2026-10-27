module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoE3a

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

theorem exists_cyclic_of_dihedral {X : Type} [Group X] {z : X} {n : ℕ} [NeZero n] (hn : Even n)
    (hn2 : n ≠ 2) (e : ↥(Subgroup.centralizer ({z} : Set X)) ≃* DihedralGroup n) :
    ∃ C : Subgroup X, IsCyclic ↥C ∧ z ∈ C ∧
      ∀ x ∈ Subgroup.centralizer ({z} : Set X), x ∉ C → x * x = 1 := by
  set Cz := Subgroup.centralizer ({z} : Set X) with hCz
  set R : Subgroup (DihedralGroup n) := Subgroup.zpowers (DihedralGroup.r 1) with hR
  have hrR : ∀ i : ZMod n, DihedralGroup.r i ∈ R := by
    intro i
    refine Subgroup.mem_zpowers_iff.mpr ⟨(i.val : ℤ), ?_⟩
    rw [zpow_natCast, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
  have hsR : ∀ i : ZMod n, DihedralGroup.sr i ∉ R := by
    intro i h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [DihedralGroup.r_one_zpow] at hk
    cases hk
  have hzz : z ∈ Cz := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine ⟨(R.comap e.toMonoidHom).map Cz.subtype, ?_, ?_, ?_⟩
  · haveI : IsCyclic ↥R := Subgroup.isCyclic_zpowers _
    haveI : IsCyclic ↥(R.comap e.toMonoidHom) :=
      isCyclic_of_surjective ((R.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
        (MulEquiv.subgroupCongr (by
          ext x
          simp only [Subgroup.mem_map, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
          constructor
          · rintro ⟨y, hy, rfl⟩
            simpa using hy
          · intro hx
            exact ⟨e x, hx, by simp⟩))) (MulEquiv.surjective _)
    exact isCyclic_of_surjective ((R.comap e.toMonoidHom).equivMapOfInjective _
      Cz.subtype_injective) (MulEquiv.surjective _)
  ·
    have hzc : (⟨z, hzz⟩ : ↥Cz) ∈ Subgroup.center ↥Cz := by
      refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
      exact (Subgroup.mem_centralizer_singleton_iff.mp g.2)
    have hc : e ⟨z, hzz⟩ ∈ Subgroup.center (DihedralGroup n) := by
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hzc g']
    rw [DihedralGroup.center_eq_closure_of_even_ne_two hn hn2] at hc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
    rw [DihedralGroup.r_zpow] at hk
    refine ⟨⟨z, hzz⟩, ?_, rfl⟩
    show e ⟨z, hzz⟩ ∈ R
    rw [← hk]
    exact hrR _
  · intro x hx hxC
    have hxR : e ⟨x, hx⟩ ∉ R := fun h => hxC ⟨⟨x, hx⟩, h, rfl⟩
    have hsq : e ⟨x, hx⟩ * e ⟨x, hx⟩ = 1 := by
      rcases h : e ⟨x, hx⟩ with i | i
      · exact absurd (h ▸ hrR i) hxR
      · exact DihedralGroup.sr_mul_self i
    rw [← map_mul, ← map_one e] at hsq
    exact congrArg Subtype.val (e.injective hsq)

theorem l2CentDihedral : L2CentDihedral := by
  intro X _ _ p f hp hp2 hfe hl2 z hz
  have hM := hl2.statedClassicalModel (by decide)
  have hf : 1 ≤ f := hl2.admissible.2.1
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hM
  let φ : X ≃* PSL(2, K) :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  haveI : Fact p.Prime := ⟨hp⟩
  have hp8 : p ^ f % 8 = 1 := by
    obtain ⟨k, rfl⟩ := hfe
    have h2 : p ^ 2 % 8 = 1 := by
      have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
      have : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
      rcases this with h | h | h | h <;> simp [Nat.pow_mod, h]
    rw [show k + k = 2 * k by ring, pow_mul, Nat.pow_mod, h2, one_pow]
    norm_num
  have hpf : 3 ≤ p ^ f := (hp.two_le.lt_of_ne hp2.symm).trans_le (Nat.le_self_pow (by omega) p)
  have ht : orderOf (φ z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz
  obtain ⟨hcd, -⟩ := CFSG.Walter.psl2_centralizer_involution K hK (hp.odd_of_ne_two hp2)
    (by omega) ht
  obtain ⟨-, ⟨eD⟩⟩ := hcd (by omega)
  have hmap : (Subgroup.centralizer ({z} : Set X)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ z} : Set PSL(2, K)) := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      have h1 := congrArg φ hy
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
    · intro hy
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy
  have hn0 : (p ^ f - 1) / 2 ≠ 0 := by omega
  haveI : NeZero ((p ^ f - 1) / 2) := ⟨hn0⟩
  exact exists_cyclic_of_dihedral (Nat.even_iff.mpr (by omega)) (by omega)
    (((φ.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)).trans eD)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident
