module

public import CFSG.ClassicalInvolution.RouteD.TypeULift
public import CFSG.ClassicalInvolution.Q3.Q3WALoc

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

theorem oddCoverSU3_three : OddCoverSU3 (GaloisField 3 2) 3 1 := by
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 3
  have hnc : NoCover.{0} Odd (StatedSU 3 (3 ^ 1) (GaloisField 3 2)) := by
    intro E _ _ _ π hπ hC hodd
    exact CFSG.SectionRank.OddCover.prime_classical_three_perfect_odd_extension_trivial
      Nat.prime_three (by norm_num) (Or.inr ⟨rfl, by simpa using hK, rfl⟩) π hπ hC hodd
  exact NoCover.of_mulEquiv (conjEquiv P hP) (NoCover.of_mulEquiv (equivStatedSU hK 3).symm hnc)

theorem isPerfect_su_three_le {n : ℕ} (hn3 : 3 ≤ n) :
    Group.IsPerfect (Su (GaloisField 3 2) 3 1 n) := by
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  have h := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (n := n) hK hn3
    (by intro h; have := congrArg Prod.snd h; norm_num at this)).1
  have h2 := CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
    (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK n)).symm h
  exact h2.1

theorem su2_pow_twelve : ∀ x : Su (GaloisField 3 2) 3 1 2, x ^ 12 = 1 := by
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_su_two (K := GaloisField 3 2) (p := 3) (f := 1) hK
  have hcard : Nat.card (CFSG.LieType.Steinberg.fixedSubfield (GaloisField 3 2) 3 1) = 3 := by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hK]
    norm_num
  obtain ⟨r⟩ := nonempty_ringEquiv_zmod_three hcard
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [← map_pow]
  have h1 : y ^ 12 = 1 := by
    apply (slEquiv r 2).injective
    rw [map_pow, sl2_pow_twelve, map_one]
  rw [h1, map_one]

theorem B12U_eq_range :
    B12 (GaloisField 3 2) 3 1 = (blockEmb (GaloisField 3 2) 3 1 3 2 0 (by omega)).range := by
  rw [B12, embSUid_two_eq_blockEmb]

theorem B23U_eq_range :
    B23 (GaloisField 3 2) 3 1 = (blockEmb (GaloisField 3 2) 3 1 3 2 1 (by omega)).range := by
  rw [B23, embSUid_zero_eq_blockEmb]

theorem pow_twelve_conj_B12U (c : Su (GaloisField 3 2) 3 1 3) :
    ∀ y ∈ (B12 (GaloisField 3 2) 3 1).map (MulAut.conj c⁻¹).toMonoidHom, y ^ 12 = 1 := by
  rintro _ ⟨b, hb, rfl⟩
  rw [B12U_eq_range] at hb
  obtain ⟨A, rfl⟩ := hb
  rw [← map_pow, ← map_pow, su2_pow_twelve A, map_one, map_one]

theorem pow_twelve_conj_B23U (c : Su (GaloisField 3 2) 3 1 3) :
    ∀ y ∈ (B23 (GaloisField 3 2) 3 1).map (MulAut.conj c⁻¹).toMonoidHom, y ^ 12 = 1 := by
  rintro _ ⟨b, hb, rfl⟩
  rw [B23U_eq_range] at hb
  obtain ⟨A, rfl⟩ := hb
  rw [← map_pow, ← map_pow, su2_pow_twelve A, map_one, map_one]

theorem unitaryBlockStandardPair_lift3 {Y : Type} [Group Y] [Finite Y] {O : Subgroup Y}
    [O.Normal] (hOc : O ≤ Subgroup.center Y) (hOodd : Odd (Nat.card O))
    (hO3 : ¬ 3 ∣ Nat.card O) {A B : Subgroup Y} (hA : ∀ a ∈ A, a ^ 12 = 1)
    (hB : ∀ b ∈ B, b ^ 12 = 1) {W : Subgroup (Y ⧸ O)}
    (h : UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (A.map (QuotientGroup.mk' O))
      (B.map (QuotientGroup.mk' O))) :
    ∃ W' : Subgroup Y, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W' A B := by
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  have hq2 : 3 ^ 1 ≠ 2 := by norm_num
  have : Group.IsPerfect (Su (GaloisField 3 2) 3 1 3) := isPerfect_su_three_le le_rfl
  have hW : W ≤ A.map (QuotientGroup.mk' O) ⊔ B.map (QuotientGroup.mk' O) :=
    (typeU_standardPair_eq_sup hK hq2 h).le
  obtain ⟨θb, c, hrange, hker, hcases⟩ := h
  have hθ : θb.range ≤ ((QuotientGroup.mk' O).comp (A ⊔ B).subtype).range := by
    rw [hrange]
    refine hW.trans (sup_le ?_ ?_)
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨⟨a, Subgroup.mem_sup_left ha⟩, rfl⟩
    · rintro _ ⟨b, hb, rfl⟩
      exact ⟨⟨b, Subgroup.mem_sup_right hb⟩, rfl⟩
  have hcen' : ((QuotientGroup.mk' O).comp (A ⊔ B).subtype).ker ≤ Subgroup.center ↥(A ⊔ B) := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro r
    have : (y : Y) ∈ O := by
      have := MonoidHom.mem_ker.mp hy
      exact (QuotientGroup.eq_one_iff _).mp this
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hOc this) (r : Y))
  have hodd' : Odd (Nat.card ((QuotientGroup.mk' O).comp (A ⊔ B).subtype).ker) := by
    refine hOodd.of_dvd_nat ?_
    let g : ((QuotientGroup.mk' O).comp (A ⊔ B).subtype).ker →* O :=
      { toFun := fun y => ⟨(y.1 : Y), (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp y.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Subgroup.card_dvd_of_injective g fun y₁ y₂ h =>
      Subtype.ext (Subtype.ext (congrArg (fun x : O => (x : Y)) h))
  obtain ⟨θ', hθ'⟩ := exists_lift_of_oddCoverSU3 oddCoverSU3_three
    ((QuotientGroup.mk' O).comp (A ⊔ B).subtype) hcen' hodd' θb hθ
  set θ : Su (GaloisField 3 2) 3 1 3 →* Y := (A ⊔ B).subtype.comp θ' with hθdef
  have hπθ : (QuotientGroup.mk' O).comp θ = θb := by
    ext s
    exact DFunLike.congr_fun hθ' s
  have hmapθ : ∀ X : Subgroup (Su (GaloisField 3 2) 3 1 3),
      (X.map θ).map (QuotientGroup.mk' O) = X.map θb := by
    intro X
    rw [Subgroup.map_map, hπθ]
  have hexp : ∀ X : Subgroup (Su (GaloisField 3 2) 3 1 3), (∀ y ∈ X, y ^ 12 = 1) →
      ∀ y ∈ X.map θ, y ^ 12 = 1 := by
    rintro X hX _ ⟨y, hy, rfl⟩
    rw [← map_pow, hX y hy, map_one]
  have hker0 : (QuotientGroup.mk' O).ker ≤ Subgroup.center Y := by
    rw [QuotientGroup.ker_mk']
    exact hOc
  have hcop : ∀ n ∈ (QuotientGroup.mk' O).ker, Nat.Coprime (orderOf n) 6 := by
    intro n hn
    rw [QuotientGroup.ker_mk'] at hn
    exact orderOf_coprime_six hOodd hO3 hn
  have heq : ∀ X : Subgroup (Su (GaloisField 3 2) 3 1 3), ∀ U : Subgroup Y,
      (∀ y ∈ X, y ^ 12 = 1) → (∀ u ∈ U, u ^ 12 = 1) →
      X.map θb = U.map (QuotientGroup.mk' O) → X.map θ = U := by
    intro X U hX hU hmap
    have hmap' : (X.map θ).map (QuotientGroup.mk' O) = U.map (QuotientGroup.mk' O) :=
      (hmapθ X).trans hmap
    refine le_antisymm ?_ ?_
    · refine le_of_map_le_of_exponent (QuotientGroup.mk' O) hker0 hcop (hexp X hX) hU
        fun l hl => ?_
      rw [← hmap']
      exact ⟨l, hl, rfl⟩
    · refine le_of_map_le_of_exponent (QuotientGroup.mk' O) hker0 hcop hU (hexp X hX)
        fun l hl => ?_
      rw [hmap']
      exact ⟨l, hl, rfl⟩
  refine ⟨θ.range, θ, c, rfl, ?_, ?_⟩
  · intro x hx
    apply hker
    rw [MonoidHom.mem_ker, ← hπθ, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hx, map_one]
  · rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨heq _ A (pow_twelve_conj_B12U c) hA h1, heq _ B (pow_twelve_conj_B23U c) hB h2⟩
    · right
      exact ⟨heq _ B (pow_twelve_conj_B12U c) hB h1, heq _ A (pow_twelve_conj_B23U c) hA h2⟩

theorem unitaryBlockStandardPair_of_locImg3 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (hO3 : LocalOddThreeFree3 Ω x) {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x}) {W : Subgroup (locQuot Ω x)}
    (h : UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (locImg Ω x L) (locImg Ω x L')) :
    ∃ W' : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W' L L' := by
  have hexp : ∀ M ∈ centralizingMembers Ω {x},
      ∀ m ∈ M.subgroupOf (locLayer Ω x), m ^ 12 = 1 := by
    intro M hM m hm
    obtain ⟨z, hz⟩ := hΩ.classical M hM.1
    have := pow_twelve_of_exact hz (hex M hM.1) (m : G) (Subgroup.mem_subgroupOf.mp hm)
    exact Subtype.ext (by simpa using this)
  obtain ⟨W', hW'⟩ := unitaryBlockStandardPair_lift3
    (O := classicalInvolutionOddCore ↥(locLayer Ω x)) hP1
    (CFSG.ComponentClassification.OddCore.odd_card _) hO3 (hexp L hL) (hexp L' hL') h
  have := unitaryBlockStandardPair_map hW' (locLayer Ω x).subtype
    (locLayer Ω x).subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (le_centralizingLayer hL), inf_eq_left.mpr (le_centralizingLayer hL')] at this
  exact ⟨_, this⟩

end CFSG.ClassicalInvolution.Q3.Q3W
