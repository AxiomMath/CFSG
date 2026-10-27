module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSymCore
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Tower

open CFSG.Open Subgroup
open scoped commutatorElement

variable {R : Type*} [Group R]

@[expose] def towerHat (S : Sylow 2 R) : Subgroup R :=
  CFSG.pCore 3 R ⊔ normalizer ((S : Subgroup R) : Set R)

theorem pCore_three_le_towerHat (S : Sylow 2 R) : CFSG.pCore 3 R ≤ towerHat S :=
  le_sup_left

theorem normalizer_le_towerHat (S : Sylow 2 R) :
    normalizer ((S : Subgroup R) : Set R) ≤ towerHat S :=
  le_sup_right

theorem sylow_le_towerHat (S : Sylow 2 R) : (S : Subgroup R) ≤ towerHat S :=
  Subgroup.le_normalizer.trans (normalizer_le_towerHat S)

theorem isSolvable_normalizer_sylow [Finite R] (S : Sylow 2 R) :
    Group.IsSolvable ↥(normalizer ((S : Subgroup R) : Set R)) := by
  set N := normalizer ((S : Subgroup R) : Set R) with hN
  have hSN : (S : Subgroup R) ≤ N := Subgroup.le_normalizer
  have hTn : ((S : Subgroup R).subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hS : Group.IsSolvable ↥(S : Subgroup R) := by
    have := S.isPGroup'.isNilpotent
    infer_instance
  have hT : Group.IsSolvable ↥((S : Subgroup R).subgroupOf N) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hSN).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hSN).injective
  have hodd : Odd (Nat.card (↥N ⧸ (S : Subgroup R).subgroupOf N)) := by
    change Odd ((S : Subgroup R).relIndex N)
    refine Nat.not_even_iff_odd.1 fun he => S.not_dvd_index ?_
    exact dvd_trans (even_iff_two_dvd.1 he) (Subgroup.relIndex_dvd_index_of_le hSN)
  have hQ : Group.IsSolvable (↥N ⧸ (S : Subgroup R).subgroupOf N) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_ker_le_range ((S : Subgroup R).subgroupOf N).subtype
    (QuotientGroup.mk' ((S : Subgroup R).subgroupOf N))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_sup_of_normal {N B : Subgroup R} [N.Normal] [Group.IsSolvable N]
    [Group.IsSolvable B] : Group.IsSolvable ↥(N ⊔ B) := by
  let quotient := QuotientGroup.mk' N
  let image := B.map quotient
  let restriction : B →* image :=
    (quotient.domRestrict B).codRestrict image
      (fun member => Subgroup.mem_map_of_mem quotient member.property)
  have hsurjective : Function.Surjective restriction := by
    intro member
    obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp member.property
    exact ⟨⟨lift, hlift⟩, Subtype.ext heq⟩
  have : Group.IsSolvable image := Group.isSolvable_of_surjective hsurjective
  have himage : (N ⊔ B).map quotient = image := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  let projection : (N ⊔ B : Subgroup R) →* image :=
    (quotient.domRestrict (N ⊔ B)).codRestrict image
      (fun member => himage ▸ Subgroup.mem_map_of_mem quotient member.property)
  let inclusion : N →* (N ⊔ B : Subgroup R) := Subgroup.inclusion le_sup_left
  have hkernel : projection.ker ≤ inclusion.range := by
    intro member hmember
    have hleft : member.val ∈ N := (QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val (MonoidHom.mem_ker.mp hmember))
    exact ⟨⟨member.val, hleft⟩, Subtype.ext rfl⟩
  exact Group.isSolvable_of_ker_le_range inclusion projection hkernel

theorem isSolvable_towerHat [Finite R] (S : Sylow 2 R) : Group.IsSolvable ↥(towerHat S) := by
  haveI : (CFSG.pCore 3 R).Normal := CFSG.pCore_normal
  haveI : Group.IsSolvable ↥(CFSG.pCore 3 R) := by
    have := (CFSG.pCore_isPGroup (p := 3) (G := R)).isNilpotent
    infer_instance
  haveI : Group.IsSolvable ↥(normalizer ((S : Subgroup R) : Set R)) :=
    isSolvable_normalizer_sylow S
  exact isSolvable_sup_of_normal (N := CFSG.pCore 3 R)
    (B := normalizer ((S : Subgroup R) : Set R))

theorem eq_bot_of_perfect_of_le_solvable [Finite R] {U K : Subgroup R} [Group.IsSolvable ↥U]
    (hKU : K ≤ U) (hK : ⁅K, K⁆ = K) : K = ⊥ := by
  by_contra hne
  have hK' : K.subgroupOf U ≠ ⊥ := by
    intro h
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hKU, h, Subgroup.map_bot]
  have hlt := Group.isSolvable_iff_commutator_lt.1 inferInstance (K.subgroupOf U) hK'
  have heq : ⁅K.subgroupOf U, K.subgroupOf U⁆ = K.subgroupOf U := by
    apply Subgroup.map_injective U.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKU]
    exact hK
  exact hlt.ne heq

theorem le_towerHat_of_subnormal [Finite R] (S : Sylow 2 R) {X : Subgroup R}
    (hX : Sym.IsSymThree X) (hXs : IsSubnormal X ⊤) : X ≤ towerHat S := by
  obtain ⟨s, hsS, hsX, hs2, hs1⟩ := Sym.exists_involution_mem_sylow hX hXs S
  obtain ⟨a, haX, ha1, ha3, hXa, -, -⟩ := Sym.symThree_data hX
  obtain ⟨-, hXeq⟩ := hXa s hsX hs2 hs1
  have haN : a ∈ CFSG.pCore 3 R := Sym.mem_pCore_three hX hXs haX ha3 ha1
  rw [hXeq, Subgroup.closure_le]
  intro y hy
  rcases hy with rfl | rfl
  · exact pCore_three_le_towerHat S haN
  · exact sylow_le_towerHat S hsS

theorem false_of_towerHat_le_normalizer [Finite R] (S : Sylow 2 R)
    (hS : towerHat S ≤ normalizer ((S : Subgroup R) : Set R)) {X : Subgroup R}
    (hX : Sym.IsSymThree X) (hXs : IsSubnormal X ⊤) : False := by
  obtain ⟨s, hsS, hsX, hs2, hs1⟩ := Sym.exists_involution_mem_sylow hX hXs S
  obtain ⟨a, haX, ha1, ha3, hXa, -, -⟩ := Sym.symThree_data hX
  obtain ⟨hinv, -⟩ := hXa s hsX hs2 hs1
  have haN : a ∈ CFSG.pCore 3 R := Sym.mem_pCore_three hX hXs haX ha3 ha1
  have haS : a ∈ normalizer ((S : Subgroup R) : Set R) := hS (pCore_three_le_towerHat S haN)
  have h1 : s * a * s⁻¹ * a⁻¹ ∈ (S : Subgroup R) := by
    have h2 : a * s⁻¹ * a⁻¹ ∈ (S : Subgroup R) :=
      (Subgroup.mem_normalizer_iff.1 haS _).1 ((S : Subgroup R).inv_mem hsS)
    have := (S : Subgroup R).mul_mem hsS h2
    simpa [mul_assoc] using this
  have h3 : s * a * s⁻¹ * a⁻¹ ∈ CFSG.pCore 3 R := by
    have : s * a * s⁻¹ ∈ CFSG.pCore 3 R := CFSG.pCore_normal.conj_mem a haN s
    exact (CFSG.pCore 3 R).mul_mem this ((CFSG.pCore 3 R).inv_mem haN)
  have h4 : s * a * s⁻¹ * a⁻¹ = 1 := by
    refine Sym.eq_one_of_pow_two_pow_three ?_ ?_
    · obtain ⟨i, hi⟩ := S.isPGroup' ⟨_, h1⟩
      exact ⟨i, by simpa using congrArg Subtype.val hi⟩
    · obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 3) (G := R)) ⟨_, h3⟩
      exact ⟨j, by simpa using congrArg Subtype.val hj⟩
  have h5 : a⁻¹ = a := by
    calc a⁻¹ = s * a * s⁻¹ := hinv.symm
      _ = (s * a * s⁻¹ * a⁻¹) * a := by group
      _ = a := by rw [h4, one_mul]
  have ha2 : a ^ 2 = 1 := by
    calc a ^ 2 = a * a := pow_two a
      _ = a * a⁻¹ := by rw [h5]
      _ = 1 := mul_inv_cancel a
  apply ha1
  calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
    _ = 1 := by rw [ha3, ha2]; group

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Tower
