module

public import CFSG.LargeExtraspecial.AS35DQ
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherShapeExclusionShapes
public import CFSG.LocalAnalysis.RankTwoShapes.SylowShapes
import CFSG.Walter.TwoRank
public import CFSG.CharacterTheory.Semidihedral.DerivedAndIndexTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Aschbacher1977

open CFSG CFSG.LargeExtraspecial CFSG.ComponentClassification.AschbacherKnownGroup

variable {G : Type} [Group G] [Finite G]

theorem false_of_abelian_index_two (S : Setting G) (hw : S.width = 2) {P : Subgroup G}
    (hQP : S.QG ≤ P) {R : Type} [Group R] (e : P ≃* R) {B : Subgroup R}
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hidx : B.index = 2) : False := by
  let A : Subgroup G := (B.comap e.toMonoidHom).map P.subtype
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    simp only [A, Subgroup.mem_map, Subgroup.mem_comap] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have h1 : e (a * b) = e (b * a) := by
      rw [map_mul e a b, map_mul e b a]
      exact hB (e a) ha (e b) hb
    exact congrArg Subtype.val (e.injective h1)
  have hsub : A.subgroupOf P = B.comap e.toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hrelP : A.relIndex P = 2 := by
    show (A.subgroupOf P).index = 2
    rw [hsub, Subgroup.index_comap_of_surjective B e.surjective, hidx]
  let I : Subgroup G := A ⊓ S.QG
  let r : ℕ := I.relIndex S.QG
  have hrA : r = A.relIndex S.QG := Subgroup.inf_relIndex_right A S.QG
  have hrle : r ≤ 2 := by
    rw [hrA]
    have h := Subgroup.relIndex_le_of_le_right (H := A) (K := S.QG) (L := P) hQP
      (by rw [hrelP]; norm_num)
    exact h.trans (le_of_eq hrelP)
  have hcard : Nat.card I ≤ 8 := by
    have h := S.card_le_of_commute (A := I) inf_le_right
      (fun x hx y hy => hcommA x hx.1 y hy.1)
    rw [hw] at h
    norm_num at h
    exact h
  have hprod : r * Nat.card I = 32 := by
    have h1 := Subgroup.card_mul_index (I.subgroupOf S.QG)
    have hcardeq : Nat.card ↥(I.subgroupOf S.QG) = Nat.card I :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have hidxeq : (I.subgroupOf S.QG).index = r := rfl
    rw [hcardeq, hidxeq] at h1
    have hQG : Nat.card (↥S.QG) = 32 := by
      have h := S.card_QG_eq_card_Q
      rw [S.card_Q_eq, hw] at h
      rw [h]
      norm_num
    rw [hQG] at h1
    rw [mul_comm] at h1
    exact h1
  have hle : r * Nat.card I ≤ 2 * 8 := Nat.mul_le_mul hrle hcard
  rw [hprod] at hle
  omega

private theorem false_of_dihedral (S : Setting G) (hw : S.width = 2) {P : Subgroup G}
    (hQP : S.QG ≤ P) {m : ℕ} [NeZero m] (e : P ≃* DihedralGroup m) : False := by
  let B : Subgroup (DihedralGroup m) := Subgroup.zpowers (DihedralGroup.r (1 : ZMod m))
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    rw [Subgroup.mem_zpowers_iff] at hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    rw [← ha, ← hb]
    exact (Commute.zpow_zpow_self (DihedralGroup.r (1 : ZMod m)) a b).eq
  have hidx : B.index = 2 := by
    have hcard := Subgroup.card_mul_index B
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card,
      Nat.mul_comm 2 m] at hcard
    exact Nat.mul_left_cancel (Nat.pos_of_neZero m) hcard
  exact false_of_abelian_index_two S hw hQP e hcomm hidx

private theorem false_of_semidihedral (S : Setting G) (hw : S.width = 2) {P : Subgroup G}
    (hQP : S.QG ≤ P) {n : ℕ} (hn : 3 ≤ n) (e : P ≃* CFSG.Open.SemidihedralGroup n) : False := by
  refine false_of_abelian_index_two S hw hQP e
    (B := CFSG.Semidihedral.rotationSubgroup n) ?_ ?_
  · intro x hx y hy
    unfold CFSG.Semidihedral.rotationSubgroup at hx hy
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self (CFSG.Semidihedral.r n) a b).eq
  · exact CFSG.Semidihedral.rotationSubgroup_index n hn

private theorem false_of_wreathed (S : Setting G) (hw : S.width = 2) {P : Subgroup G}
    (hQP : S.QG ≤ P) {n : ℕ} (e : P ≃* CFSG.Open.WreathedTwoGroup n) : False := by
  have hn : 0 < 2 ^ n := by positivity
  haveI : IsMulCommutative (CFSG.Wreathed.baseSubgroup (2 ^ n)) :=
    CFSG.Wreathed.base_is_abelian (2 ^ n)
  exact false_of_abelian_index_two S hw hQP e
    (B := CFSG.Wreathed.baseSubgroup (2 ^ n))
    (fun x hx y hy => setLike_mul_comm hx hy)
    (CFSG.Wreathed.base_index_two (2 ^ n) hn)

private theorem false_of_unitary_sylow (S : Setting G) (hw : S.width = 2) {P : Sylow 2 G}
    (hQP : S.QG ≤ (P : Subgroup G)) {H : Type} [Group H]
    (hH : CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2) (U : Sylow 2 H)
    (e : (P : Subgroup G) ≃* (U : Subgroup H)) : False := by
  obtain ⟨t, htQ, ht2, ht1, htz⟩ := S.exists_noncentral_involution (by omega)
  have htP : t ∈ (P : Subgroup G) := hQP htQ
  let tP : (P : Subgroup G) := ⟨t, htP⟩
  have htP2 : tP ^ 2 = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow, Subgroup.coe_one, pow_two] using ht2
  have htZ : tP ∈ Subgroup.center (P : Subgroup G) :=
    ((CFSG.LyonsUnitaryFour.unitary_four_sylow_structure hH P U ⟨e⟩).2.2.1 tP).mp htP2
  have ht_zpow : t ∈ Subgroup.zpowers S.z := by
    rw [← S.map_center_eq_zpowers P.isPGroup' hQP]
    exact ⟨tP, htZ, rfl⟩
  rcases (CFSG.LargeExtraspecial.Setting.mem_zpowers_iff_of_mul_self S.z_mul_z).mp ht_zpow with
    h | h
  · exact ht1 h
  · exact htz h

theorem false_of_isRankTwoSylowShape (S : Setting G) (hw : S.width = 2) {P : Sylow 2 G}
    (hQP : S.QG ≤ (P : Subgroup G))
    (hshape : ShapeExclusion.IsRankTwoSylowShape (P : Subgroup G)) : False := by
  rcases hshape with ⟨n, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩ | ⟨H, _, U, hH, ⟨e⟩⟩
  · exact false_of_dihedral S hw hQP e
  · exact false_of_semidihedral S hw hQP (by omega) e
  · exact false_of_wreathed S hw hQP e
  · exact false_of_unitary_sylow S hw hQP hH U e

theorem three_le_twoRank_of_width_two
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Setting G) (hw : S.width = 2) : 3 ≤ CFSG.Open.twoRank G := by
  by_contra h
  push Not at h
  obtain ⟨P, hQP, _⟩ := S.exists_sylow_le_M
  have heven : Even (Nat.card G) := by
    rw [even_iff_two_dvd]
    exact S.orderOf_z ▸ orderOf_dvd_natCard S.z
  have h2 : 2 ≤ CFSG.Assembly.twoRank G := CFSG.Walter.two_le_twoRank G hnonab heven
  have hrank : CFSG.Assembly.twoRank G = 2 := by omega
  exact false_of_isRankTwoSylowShape S hw hQP
    (CFSG.RankTwoShapes.rank_two_sylow_shapes hnonab hrank P)

end CFSG.GF2Type.Aschbacher1977
