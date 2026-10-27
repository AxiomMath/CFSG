module

public import CFSG.GF2Type.SmithTypeE.E6Defs
public import CFSG.GF2Type.SmithTypeE.E6Outcome
public import CFSG.LargeExtraspecial.S14C12SmHolt
public import CFSG.LargeExtraspecial.S14C12SmGraph

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE

open Subgroup CFSG.Open CFSG.Blueprint CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.Timmesfeld.Connectivity CFSG.RankThree.PartTwo.Sec21 Equiv
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem not_thirteen_dvd_card_M_of_L6 (S : Setting G) (hw : S.width = 10)
    (hL : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) : ¬ 13 ∣ Nat.card S.M := by
  obtain ⟨hk, hM⟩ := card_M_of_L6 S hw hL
  rw [hM]
  rcases (Nat.dvd_prime Nat.prime_two).mp hk with hk | hk <;> rw [hk] <;> norm_num

theorem false_of_mulEquiv_alternatingGroup_of_L6 (S : Setting G) (hw : S.width = 10)
    (hL : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) {m : ℕ} (e : G ≃* alternatingGroup (Fin m)) :
    False := by
  have h2 := factorization_card_of_L6 S hw hL
  have h36 : 2 ^ 36 ∣ Nat.card G :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mpr (by omega)
  by_cases hm : m ≤ 36
  · have h1 : Nat.card G ∣ Nat.factorial 36 := by
      rw [Nat.card_congr e.toEquiv]
      refine (Subgroup.card_subgroup_dvd_card _).trans ?_
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      exact Nat.factorial_dvd_factorial hm
    exact absurd (h36.trans h1) (by decide)
  · push Not at hm
    have hσ : orderOf ((e S.z : alternatingGroup (Fin m)) : Perm (Fin m)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, S.orderOf_z]
    have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' 13
      (SmithAlt.thirteen_dvd_card_centralizer (by omega) hσ)
    have hh' : orderOf (h : Perm (Fin m)) = 13 := by rw [Subgroup.orderOf_coe, hh]
    set h₁ : alternatingGroup (Fin m) :=
      ⟨h, Perm.mem_alternatingGroup.mpr (SmithAlt.sign_eq_one_of_orderOf hh')⟩ with hh₁
    have hcomm : h₁ * e S.z = e S.z * h₁ :=
      Subtype.ext (mem_centralizer_singleton_iff.mp h.2)
    have hy : e.symm h₁ ∈ S.M := by
      rw [mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hcomm]
    have hord : orderOf (⟨e.symm h₁, hy⟩ : S.M) = 13 := by
      rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hh₁, Subgroup.orderOf_mk, hh']
    exact not_thirteen_dvd_card_M_of_L6 S hw hL (hord ▸ orderOf_dvd_natCard _)

theorem exists_isConj_orderOf_mul_eq_four_of_L6 [IsSimpleGroup G]
    (hAS : AschbacherSmithWideInput) (hDW : DW.DW37Statement) (S : Setting G)
    (hw : S.width = 10) (hL : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) :
    ∃ a b : G, IsConj S.z a ∧ IsConj S.z b ∧ orderOf (a * b) = 4 := by
  have h2 := factorization_card_of_L6 S hw hL
  by_cases hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z
  · exfalso
    obtain ⟨e⟩ := hAS G S (by omega) hW
    rw [hw] at e
    have h38 : 2 ^ 38 ∣ Nat.card G := by
      rw [Nat.card_congr e.toEquiv]
      exact SmithQ.two_pow_dvd_card_timmesfeldPSU_twelve
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h38
    omega
  · push Not at hW
    obtain ⟨g, hgQ, hne⟩ := hW
    by_contra hno
    have hcomm : ∀ x y : G, IsConj S.z x → x ∈ S.QG → IsConj S.z y → y ∈ S.QG →
        x * y = y * x := by
      intro x y hx hxQ hy hyQ
      by_contra hxy
      exact hno ⟨x, y, hx, hy, SmithQ.orderOf_mul_eq_four S hxQ hyQ
        (SmithQ.mul_self_eq_one_of_isConj S hx) (SmithQ.mul_self_eq_one_of_isConj S hy) hxy⟩
    obtain ⟨e⟩ := hDW G S g (by omega) hgQ hne
      (SmithQ.isReducible_of_commute S (by omega) (isConj_iff.mpr ⟨g, rfl⟩) hgQ hne hcomm)
    have h66 : (Nat.card G).factorization 2 = (S.width + 2) * (S.width + 2 - 1) / 2 := by
      rw [Nat.card_congr e.toEquiv]
      exact SmithQ.factorization_card_psl _
    rw [hw] at h66
    omega

theorem reach_conjugatesOf_of_L6 [IsSimpleGroup G]
    (hHolt : HoltUniqueFixedPointSimple) (S : Setting G) (hw : S.width = 10)
    (hL : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)))
    {d e : G} (hd : IsConj S.z d) (he : IsConj S.z e) (h4 : orderOf (d * e) = 4)
    {t : G} (ht : IsConj S.z t) : Reach (conjugatesOf S.z) S.z t := by
  by_contra hnt
  have hd2 := SmithQ.mul_self_eq_one_of_isConj S hd
  have he2 := SmithQ.mul_self_eq_one_of_isConj S he
  have hnonab : ∃ a b : G, a * b ≠ b * a := by
    refine ⟨d, e, fun hc => ?_⟩
    have h1 : (d * e) ^ 2 = 1 := by
      rw [_root_.sq, show d * e * (d * e) = d * (e * d) * e by group, ← hc,
        show d * (d * e) * e = (d * d) * (e * e) by group, hd2, he2, one_mul]
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [h4] at h2
    norm_num at h2
  rcases RankThree.Holt.holt_commutingComponent hHolt hnonab S.orderOf_z
      (SmithHolt.exists_sylow_twoCentral S) ⟨t, ht, hnt⟩ with ⟨H, hH⟩ | ⟨m, -, ⟨φ⟩⟩
  · exact SmithHolt.false_of_isStronglyEmbedded hH (S.orderOf_of_isConj hd)
      (S.orderOf_of_isConj he) h4
  · exact false_of_mulEquiv_alternatingGroup_of_L6 S hw hL φ

theorem local_of_input_of_L6 (hLoc : SmithL62LocalInput) [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 10) (hL : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) (x y : G)
    (hx : IsConj S.z x) (hy : IsConj S.z y) (hxM : x ∈ S.M) (hyM : y ∈ S.M) :
    orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
      (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2)) := by
  by_cases hxQ : x ∈ S.QG
  · by_cases hyQ : y ∈ S.QG
    · exact SmithQ.orderOf_mul_mem_of_mem_QG S hxQ hyQ
    · obtain ⟨h1, h2⟩ := hLoc G S hw hL y x hy hx hyM hxM hyQ
      have hord : orderOf (y * x) = orderOf (x * y) := by
        rw [show y * x = MulAut.conj y (x * y) by rw [MulAut.conj_apply]; group,
          MulEquiv.orderOf_eq]
      rw [hord] at h1 h2
      refine ⟨h1, fun h4 => ?_⟩
      rw [show (x * y) ^ 2 = x * (y * x) ^ 2 * x⁻¹ by rw [_root_.sq, _root_.sq]; group]
      exact (h2 h4).trans (isConj_iff.mpr ⟨x, rfl⟩)
  · exact hLoc G S hw hL x y hx hy hxM hyM hxQ

theorem smithL62ThreeFourInput_of (hAS : AschbacherSmithWideInput)
    (hDW : DW.DW37Statement) (hHolt : HoltUniqueFixedPointSimple) (hLoc : SmithL62LocalInput)
    (hPath : SmithL62PathInput) : SmithL62ThreeFourInput := by
  intro G _ _ _ S hw hL
  obtain ⟨d, e, hd, he, h4⟩ := exists_isConj_orderOf_mul_eq_four_of_L6 hAS hDW S hw hL
  refine ⟨fun a b ha hb => ?_, ⟨d, e, hd, he, h4⟩⟩
  have hra := reach_conjugatesOf_of_L6 hHolt S hw hL hd he h4 ha
  have hrb := reach_conjugatesOf_of_L6 hHolt S hw hL hd he h4 hb
  obtain ⟨v, hv, hav, hvb⟩ :=
    SmithGraph.exists_common_of_reach (hPath G S hw hL) ha (reach_trans (reach_symm hra) hrb)
  exact SmithGraph.threeFour_of_common S (local_of_input_of_L6 hLoc S hw hL) ha hb hv hav hvb

theorem smithL62Input_of_threeFour (h : SmithL62ThreeFourInput) : SmithL62Input := by
  intro G _ _ _ S hw hL
  obtain ⟨hprod, hnd⟩ := h G S hw hL
  exact e6_of_threeFourPlus S hw hL (threeFourPlusClass_of_products S hprod) hnd

theorem partB_of_local_path (hAS : AschbacherSmithWideInput) (hDW : DW.DW37Statement)
    (hHolt : HoltUniqueFixedPointSimple) (hLoc : SmithL62LocalInput)
    (hPath : SmithL62PathInput) : PartB :=
  partB_of_smithL62Input
    (smithL62Input_of_threeFour (smithL62ThreeFourInput_of hAS hDW hHolt hLoc hPath))

end CFSG.GF2Type.SmithTypeE
