
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Lin2Act
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourSylow

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace L238

section Abstract

theorem eq_bot_of_normal_solvable {Y : Type*} [Group Y] (hq : CFSG.IsQuasisimple Y)
    (hc : ∀ t ∈ Subgroup.center Y, t = 1) (S : Subgroup Y) [S.Normal]
    (hS : Group.IsSolvable S) : S = ⊥ := by
  have hne : S ≠ ⊤ := by
    intro htop
    obtain ⟨hperf, hsimple, -⟩ := hq
    have hsolv : Group.IsSolvable Y := by
      subst htop
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.topEquiv (G := Y)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := Y)).symm.injective
    have hnt : Nontrivial Y := by
      have : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hsimple
      exact (QuotientGroup.mk'_surjective (Subgroup.center Y)).nontrivial
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial Y
    exact absurd hperf.commutator_eq_top hlt.ne
  have hle := C1GN.le_center_of_ne_top (Or.inl hq) S hne
  rw [eq_bot_iff]
  intro s hs
  exact Subgroup.mem_bot.2 (hc s (hle hs))

theorem center_alt_trivial {m : ℕ} (hm : 5 ≤ m) :
    ∀ t ∈ Subgroup.center (alternatingGroup (Fin m)), t = 1 := by
  intro t ht
  have h4 : 4 ≤ Nat.card (Fin m) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hc := alternatingGroup.center_eq_bot h4
  rw [hc] at ht
  exact Subgroup.mem_bot.1 ht

end Abstract

section Blocks

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem chiBlock_type_cases {X L : Subgroup G} (hL : IsChiBlock X L) (h3 : ¬ IsAltType L 3) :
    (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ ∃ m : ℕ, 5 ≤ m ∧ IsAltType L m := by
  rcases hL.2 with ⟨n, hn, hlin⟩ | ⟨m, hm, hm3, halt⟩
  · exact Or.inl ⟨n, hn, hlin⟩
  · by_cases hm3' : m = 3
    · subst hm3'
      exact absurd halt h3
    · exact Or.inr ⟨m, by obtain ⟨k, rfl⟩ := hm; omega, halt⟩

omit [Finite G] in
theorem isQuasisimple_of_isChiBlock {X L : Subgroup G} (hL : IsChiBlock X L)
    (h3 : ¬ IsAltType L 3) : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  refine hL.1.1.2.2.2.1.resolve_right ?_
  rcases chiBlock_type_cases hL h3 with ⟨n, hn, hlin⟩ | ⟨m, hm, halt⟩
  · exact card_ne_three_of_isLin2Type hn hlin
  · exact card_ne_three_of_isAltType hm halt

omit [Finite G] in
theorem center_quot_trivial_of_lin2 {L : Subgroup G} {n : ℕ} (hn : 1 < n) (h : IsLin2Type L n) :
    ∀ t ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L), t = 1 := by
  obtain ⟨F, hF, hFin, hcard, α, hαs, hαk, -⟩ := h
  have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hq
  let φ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  intro t ht
  have hφt : φ t ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro u
    obtain ⟨y, rfl⟩ := φ.surjective u
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 ht y]
  obtain ⟨r, hr, hrt⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hφt
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)
  have hφ1 : φ t = 1 := by
    apply Subtype.ext
    rw [← hrt, hr1]
    simp
  exact φ.injective (by rw [hφ1, map_one])

omit [Finite G] in
theorem center_quot_trivial_of_alt {L : Subgroup G} {m : ℕ} (hm : 5 ≤ m) (h : IsAltType L m) :
    ∀ t ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L), t = 1 := by
  obtain ⟨α, hαs, hαk, -⟩ := h
  let φ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin m) :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  intro t ht
  have hφt : φ t ∈ Subgroup.center (alternatingGroup (Fin m)) := by
    rw [Subgroup.mem_center_iff]
    intro u
    obtain ⟨y, rfl⟩ := φ.surjective u
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 ht y]
  exact φ.injective (by rw [center_alt_trivial hm (φ t) hφt, map_one])

omit [Finite G] in
theorem center_quot_trivial {X L : Subgroup G} (hL : IsChiBlock X L) (h3 : ¬ IsAltType L 3) :
    ∀ t ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L), t = 1 := by
  rcases chiBlock_type_cases hL h3 with ⟨n, hn, hlin⟩ | ⟨m, hm, halt⟩
  · exact center_quot_trivial_of_lin2 hn hlin
  · exact center_quot_trivial_of_alt hm halt

theorem eq_bot_of_normal_solvable_img {X N : Subgroup G} (hN : IsChiBlock X N)
    (h3 : ¬ IsAltType N 3) {S : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)}
    (hSN : S ≤ modO2Image X N) (hSn : (S.subgroupOf (modO2Image X N)).Normal)
    (hS : Group.IsSolvable S) : S = ⊥ := by
  classical
  have hNc : N ∈ cComp X := mem_cComp_of_isChiBlock hN h3
  obtain ⟨e⟩ := modO2_mulEquiv hNc
  have hq := isQuasisimple_of_isChiBlock hN h3
  have hZ := center_quot_trivial hN h3
  let T : Subgroup (↥N ⧸ CFSG.pCore 2 ↥N) :=
    (S.subgroupOf (modO2Image X N)).comap e.toMonoidHom
  have hTn : T.Normal := Subgroup.Normal.comap hSn _
  have hTs : Group.IsSolvable T := by
    let f : T →* S := MonoidHom.codRestrict
      ((modO2Image X N).subtype.comp (e.toMonoidHom.comp T.subtype)) S (fun x => by
        have h : (e.toMonoidHom x.1 : ↥(modO2Image X N)) ∈ S.subgroupOf (modO2Image X N) := x.2
        exact Subgroup.mem_subgroupOf.1 h)
    refine Group.isSolvable_of_isSolvable_injective (f := f) ?_
    intro x y hxy
    have h0 : ((f x : ↥S) : ↥X ⧸ CFSG.pCore 2 ↥X) = ((f y : ↥S) : ↥X ⧸ CFSG.pCore 2 ↥X) :=
      congrArg Subtype.val hxy
    have h1 : (e x : ↥(modO2Image X N)) = e y := Subtype.ext h0
    exact Subtype.ext (e.injective h1)
  have hT : T = ⊥ := eq_bot_of_normal_solvable hq hZ T hTs
  rw [eq_bot_iff]
  intro s hs
  have hsN : s ∈ modO2Image X N := hSN hs
  have hmem : e.symm ⟨s, hsN⟩ ∈ T := by
    show e.toMonoidHom (e.symm ⟨s, hsN⟩) ∈ S.subgroupOf (modO2Image X N)
    rw [Subgroup.mem_subgroupOf]
    simpa using hs
  rw [hT, Subgroup.mem_bot] at hmem
  have h1 : (⟨s, hsN⟩ : ↥(modO2Image X N)) = 1 := by
    rw [← e.apply_symm_apply ⟨s, hsN⟩, hmem, map_one]
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)

theorem center_img_trivial {X N : Subgroup G} (hN : IsChiBlock X N) (h3 : ¬ IsAltType N 3)
    {z : ↥X ⧸ CFSG.pCore 2 ↥X} (hz : z ∈ modO2Image X N)
    (hc : ∀ u ∈ modO2Image X N, z * u = u * z) : z = 1 := by
  have hzn : ((Subgroup.zpowers z).subgroupOf (modO2Image X N)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hn)
    have hcomm : (g : ↥X ⧸ CFSG.pCore 2 ↥X) * (n : ↥X ⧸ CFSG.pCore 2 ↥X) =
        (n : ↥X ⧸ CFSG.pCore 2 ↥X) * (g : ↥X ⧸ CFSG.pCore 2 ↥X) := by
      rw [← hk]
      exact ((Commute.zpow_left (hc g g.2) k).eq).symm
    have h1 : g * n * g⁻¹ = n := by
      rw [mul_inv_eq_iff_eq_mul]
      exact Subtype.ext hcomm
    rw [h1]
    exact hn
  have hsolv : Group.IsSolvable (Subgroup.zpowers z) := by
    refine Group.isSolvable_of_comm (fun a b => ?_)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 b.2
    apply Subtype.ext
    show (a : ↥X ⧸ CFSG.pCore 2 ↥X) * (b : ↥X ⧸ CFSG.pCore 2 ↥X) =
      (b : ↥X ⧸ CFSG.pCore 2 ↥X) * (a : ↥X ⧸ CFSG.pCore 2 ↥X)
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  have hbot := eq_bot_of_normal_solvable_img hN h3 (S := Subgroup.zpowers z)
    (Subgroup.zpowers_le.2 hz) hzn hsolv
  exact Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_zpowers z)

theorem commute_img_NN {X N₁ N₂ : Subgroup G} (h37 : A37Statement (↥X ⧸ CFSG.pCore 2 ↥X))
    (h₁ : IsChiBlock X N₁) (h₂ : IsChiBlock X N₂) (a₁ : ¬ IsAltType N₁ 3)
    (a₂ : ¬ IsAltType N₂ 3) (hne : N₁ ≠ N₂) :
    ⁅modO2Image X N₁, modO2Image X N₂⁆ = ⊥ := by
  have c₁ := mem_cComp_of_isChiBlock h₁ a₁
  have c₂ := mem_cComp_of_isChiBlock h₂ a₂
  exact h37 _ (modO2Image_mem_cComp c₁) _ (modO2Image_mem_cComp c₂)
    (fun h => hne (modO2Image_injOn X c₁ c₂ h))

theorem pow_three_eq_one_of_mem_img {X A : Subgroup G} (hA : IsBlock2 X A) (hA3 : IsAltType A 3)
    {u : ↥X ⧸ CFSG.pCore 2 ↥X} (hu : u ∈ modO2Image X A) : u ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu' : u ∈ (A.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := hu
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hu'
  have hbA : (b : G) ∈ A := hb
  obtain ⟨α, -, hαk, -⟩ := hA3
  let a : ↥A := ⟨(b : G), hbA⟩
  have hcube : ∀ g : alternatingGroup (Fin 3), g ^ 3 = 1 := by decide
  have h1 : a ^ 3 ∈ CFSG.pCore 2 ↥A := by
    rw [← hαk, MonoidHom.mem_ker, map_pow, hcube]
  have h2 : ((a ^ 3 : ↥A) : G) ∈ blockQ A := (C56.mem_blockQ_iff (a ^ 3)).2 h1
  have h3 : ((a ^ 3 : ↥A) : G) ∈ pCoreOf 2 X :=
    A4.pCoreOf_le_of_subnormal 2 (C1GN.isSubnormal_of_isBlock2 hA) h2
  have h4 : (b ^ 3 : ↥X) ∈ CFSG.pCore 2 ↥X := (C56.mem_blockQ_iff (b ^ 3)).1 h3
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).2 h4

theorem commute_img_NA {X N A : Subgroup G} (hN : IsChiBlock X N) (hN3 : ¬ IsAltType N 3)
    (hA : IsBlock2 X A) (hA3 : IsAltType A 3) :
    ⁅modO2Image X N, modO2Image X A⁆ = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNc : N ∈ cComp X := mem_cComp_of_isChiBlock hN hN3
  have hNb := modO2Image_mem_cComp hNc
  have hAsub : (modO2Image X A).IsSubnormal :=
    Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X)) hA.2.2
  have hAgrp : IsPGroup 3 (modO2Image X A) := fun u => ⟨1, by
    have := pow_three_eq_one_of_mem_img hA hA3 u.2
    exact Subtype.ext (by simpa using this)⟩
  have hAP : modO2Image X A ≤ CFSG.Open.pCore 3 (↥X ⧸ CFSG.pCore 2 ↥X) :=
    S14110.Commute.le_pCore_of_isSubnormal 3 hAsub le_rfl (by
      rw [Subgroup.subgroupOf_self]
      exact Subgroup.normal_top) hAgrp
  have hPn : (CFSG.Open.pCore 3 (↥X ⧸ CFSG.pCore 2 ↥X)).Normal :=
    CFSG.LieType.BorelTits.pCore_normal 3
  have hPs : Group.IsSolvable (CFSG.Open.pCore 3 (↥X ⧸ CFSG.pCore 2 ↥X)) := by
    have : Group.IsNilpotent ↥(CFSG.Open.pCore 3 (↥X ⧸ CFSG.pCore 2 ↥X)) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 3 (G := ↥X ⧸ CFSG.pCore 2 ↥X)).isNilpotent
    infer_instance
  have hcomm := cComp_commutator_perfectCore hNb (le_top) hPs
    (by have := hPn; exact Subgroup.le_normalizer_of_normal)
  have hle : ⁅modO2Image X N, CFSG.Open.pCore 3 (↥X ⧸ CFSG.pCore 2 ↥X)⁆ ≤
      modO2Image X N ⊓ CFSG.Open.pCore 3 (↥X ⧸ CFSG.pCore 2 ↥X) :=
    le_inf hcomm.1 (Subgroup.commutator_le_right _ _)
  have hbot : modO2Image X N ⊓ CFSG.Open.pCore 3 (↥X ⧸ CFSG.pCore 2 ↥X) = ⊥ := by
    refine eq_bot_of_normal_solvable_img hN hN3 inf_le_left ?_ ?_
    · rw [Subgroup.inf_subgroupOf_left]
      exact Subgroup.normal_subgroupOf
    · exact Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (inf_le_right :
          modO2Image X N ⊓ CFSG.Open.pCore 3 (↥X ⧸ CFSG.pCore 2 ↥X) ≤ _))
        (Subgroup.inclusion_injective _)
  exact le_bot_iff.1 ((Subgroup.commutator_mono le_rfl hAP).trans (hle.trans hbot.le))

end Blocks

end L238

end CFSG.QuasithinUnique
