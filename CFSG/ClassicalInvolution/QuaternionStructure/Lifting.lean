module

public import CFSG.ClassicalInvolution.QuaternionStructure.CentralQuotient
public import CFSG.LieType.CentralExt.SL2Lift
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup

public section

namespace CFSG.ClassicalInvolution.QuaternionStructure

open CFSG CFSG.GorensteinWalter
open scoped MatrixGroups

universe u

theorem mem_zpowers_iff_of_orderOf_eq_two {G : Type*} [Group G] {g x : G} (hg : orderOf g = 2) :
    x ∈ Subgroup.zpowers g ↔ x = 1 ∨ x = g := by
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    have hg2 : g ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hg)
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      obtain ⟨m, rfl⟩ : 2 ∣ k := Int.dvd_of_emod_eq_zero hk
      rw [zpow_mul, zpow_ofNat, hg2, one_zpow]
    · right
      have : k = 2 * (k / 2) + 1 := by omega
      rw [this, zpow_add, zpow_mul, zpow_ofNat, hg2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact ⟨0, zpow_zero g⟩
    · exact ⟨1, zpow_one x⟩

theorem isPGroup_of_isPGroup_quotient {G : Type*} [Group G] [Finite G] (Z : Subgroup G) [Z.Normal]
    (hZ : Nat.card Z = 2) (hH : IsPGroup 2 (G ⧸ Z)) : IsPGroup 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hH.exists_card_eq
  refine IsPGroup.of_card (n := a + 1) ?_
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z, ha, hZ, pow_succ]

section SL2

variable {K : Type*} [Field K]

theorem mem_center_specialLinearGroup_two_iff {A : SL(2, K)} :
    A ∈ Subgroup.center SL(2, K) ↔ A = 1 ∨ A = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
  constructor
  · rintro ⟨r, hr, hA⟩
    have : (r - 1) * (r + 1) = 0 := by linear_combination hr
    rcases mul_eq_zero.mp this with h | h
    · left
      apply Subtype.ext
      rw [← hA, sub_eq_zero.mp h]
      simp
    · right
      apply Subtype.ext
      rw [← hA, Matrix.SpecialLinearGroup.coe_neg, eq_neg_of_add_eq_zero_left h]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Matrix.one_apply_ne hij]
  · rintro (rfl | rfl)
    · exact ⟨1, by norm_num, by simp⟩
    · refine ⟨-1, by norm_num, ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_neg]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Matrix.one_apply_ne hij]

theorem orderOf_neg_one_specialLinearGroup_two (h2 : (2 : K) ≠ 0) :
    orderOf (-1 : SL(2, K)) = 2 :=
  CFSG.Semidihedral.OddFieldSL2.minusIdentity_orderOf K h2

theorem center_specialLinearGroup_two_eq_zpowers (h2 : (2 : K) ≠ 0) :
    Subgroup.center SL(2, K) = Subgroup.zpowers (-1 : SL(2, K)) := by
  ext x
  rw [mem_center_specialLinearGroup_two_iff,
    mem_zpowers_iff_of_orderOf_eq_two (orderOf_neg_one_specialLinearGroup_two h2)]

theorem natCard_center_specialLinearGroup_two (h2 : (2 : K) ≠ 0) :
    Nat.card (Subgroup.center SL(2, K)) = 2 := by
  rw [center_specialLinearGroup_two_eq_zpowers h2, Nat.card_zpowers]
  exact orderOf_neg_one_specialLinearGroup_two h2

theorem natCard_specialLinearGroup_two (h2 : (2 : K) ≠ 0) :
    Nat.card SL(2, K) = Nat.card (PSL2 K) * 2 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(2, K)),
    natCard_center_specialLinearGroup_two h2]

end SL2

namespace QuaternionSetting

variable {G : Type u} [Group G] {z : G} {r : ℕ} (h : QuaternionSetting G z r)

include h

theorem exists_mulEquiv_specialLinearGroup [Finite G] [(Subgroup.zpowers z).Normal]
    {K : Type*} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    (N : Subgroup (G ⧸ Subgroup.zpowers z)) (e : N ≃* PSL2 K) :
    Nonempty ((N.comap (QuotientGroup.mk' (Subgroup.zpowers z))) ≃* SL(2, K)) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  let π : G →* G ⧸ Subgroup.zpowers z := QuotientGroup.mk' (Subgroup.zpowers z)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.zpowers z := QuotientGroup.ker_mk' _
  let M : Subgroup G := N.comap π
  let ρ : M →* N := (π.comp M.subtype).codRestrict N (fun x => x.2)
  have hρ : Function.Surjective ρ := by
    intro y
    obtain ⟨x, hx⟩ := hπ y
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change π x ∈ N
    rw [hx]
    exact y.2
  let p : M →* PSL2 K := e.toMonoidHom.comp ρ
  have hp : Function.Surjective p := e.surjective.comp hρ
  have hpker : ∀ x : M, p x = 1 ↔ (x : G) ∈ Subgroup.zpowers z := by
    intro x
    change e (ρ x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← QuotientGroup.eq_one_iff (x : G)]
    exact Subtype.ext_iff
  have hcen : p.ker ≤ Subgroup.center M := by
    intro x hx
    have hxz : (x : G) ∈ Subgroup.zpowers z := (hpker x).mp hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (h.zpowers_le_center hxz) (y : G)
  have hz2 : z ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq h.orderOf_eq_two)
  have h2p : IsPGroup 2 p.ker := by
    intro x
    refine ⟨1, ?_⟩
    have hxz : ((x : M) : G) ∈ Subgroup.zpowers z := (hpker _).mp x.2
    have hsq : ((x : M) : G) ^ 2 = 1 := by
      rcases (mem_zpowers_iff_of_orderOf_eq_two h.orderOf_eq_two).mp hxz with h1 | h1
      · rw [h1, one_pow]
      · rw [h1, hz2]
    apply Subtype.ext
    apply Subtype.ext
    simpa using hsq
  obtain ⟨β, hβ⟩ := CFSG.LieType.CentralExt.exists_lift hK hp hcen h2p
    (QuotientGroup.mk' (Subgroup.center SL(2, K)))
  have hβx : ∀ x, p (β x) = (QuotientGroup.mk x : PSL2 K) := fun x => DFunLike.congr_fun hβ x
  have hβneg : β (-1) ≠ 1 := by
    intro hneg
    let w := CFSG.Semidihedral.OddLinearNormals.quarterTurn K
    have hw2 : w ^ 2 = -1 := CFSG.Semidihedral.OddFieldSL2.quarterTurn_square K
    have hβw2 : (β w) ^ 2 = 1 := by rw [← map_pow, hw2, hneg]
    have hwc : (QuotientGroup.mk w : PSL2 K) ≠ 1 := fun h1 =>
      CFSG.Semidihedral.OddLinearNormals.quarterTurn_not_mem_center K
        ((QuotientGroup.eq_one_iff w).mp h1)
    have hβw1 : β w ≠ 1 := by
      intro h1
      apply hwc
      rw [← hβx w, h1, map_one]
    have hord : orderOf ((β w : M) : G) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime hβw2 hβw1
    have hzeq := h.eq_of_orderOf_eq_two _ hord
    have hp1 : p (β w) = 1 := (hpker _).mpr (by rw [hzeq]; exact Subgroup.mem_zpowers z)
    exact hwc (by rw [← hβx w]; exact hp1)
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : β x = 1 := hx
    have hx2 : (QuotientGroup.mk x : PSL2 K) = 1 := by rw [← hβx x, hx1, map_one]
    have hxc : x ∈ Subgroup.center SL(2, K) := (QuotientGroup.eq_one_iff x).mp hx2
    rcases mem_center_specialLinearGroup_two_iff.mp hxc with rfl | rfl
    · exact one_mem _
    · exact absurd hx1 hβneg
  have hcardM : Nat.card M = Nat.card SL(2, K) := by
    rw [natCard_comap_eq π hπ N, hker, h.natCard_zpowers, natCard_specialLinearGroup_two h2,
      Nat.card_congr e.toEquiv]
    ring
  have hbij : Function.Bijective β := hinj.bijective_of_nat_card_le (le_of_eq hcardM)
  exact ⟨(MulEquiv.ofBijective β hbij).symm⟩

theorem commutator_eq_top_of_quotient_perfect [Finite G] [(Subgroup.zpowers z).Normal]
    (hperf : commutator (G ⧸ Subgroup.zpowers z) = ⊤)
    (heven : 2 ∣ Nat.card (G ⧸ Subgroup.zpowers z)) : commutator G = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : G →* G ⧸ Subgroup.zpowers z := QuotientGroup.mk' (Subgroup.zpowers z)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.zpowers z := QuotientGroup.ker_mk' _
  have hmap : (commutator G).map π = ⊤ := by
    rw [map_commutator_eq G π, MonoidHom.range_eq_top.mpr hπ]
    exact hperf
  by_cases hzC : z ∈ commutator G
  · have hsup : commutator G ⊔ π.ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
    rw [hker] at hsup
    rwa [sup_eq_left.mpr (Subgroup.zpowers_le.mpr hzC)] at hsup
  · exfalso
    let C : Subgroup G := commutator G
    let f : C →* G ⧸ Subgroup.zpowers z := π.comp C.subtype
    have hfinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have h1 : π (x : G) = 1 := hx
      have h2 : (x : G) ∈ Subgroup.zpowers z := by rw [← hker]; exact h1
      rcases (mem_zpowers_iff_of_orderOf_eq_two h.orderOf_eq_two).mp h2 with h3 | h3
      · exact Subtype.ext h3
      · exact absurd (by rw [← h3]; exact x.2) hzC
    have hfsurj : Function.Surjective f := by
      intro y
      have : y ∈ (commutator G).map π := by rw [hmap]; trivial
      obtain ⟨c, hc, hcy⟩ := this
      exact ⟨⟨c, hc⟩, hcy⟩
    have hcard : Nat.card C = Nat.card (G ⧸ Subgroup.zpowers z) :=
      Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (hcard ▸ heven)
    have hcG : orderOf (c : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hc
    have hcz := h.eq_of_orderOf_eq_two _ hcG
    exact hzC (by rw [← hcz]; exact c.2)

theorem alt7_structure [Finite G] [(Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* alternatingGroup (Fin 7)) :
    commutator G = ⊤ ∧ Subgroup.center G = Subgroup.zpowers z ∧
      IsSimpleGroup (G ⧸ Subgroup.center G) ∧ Nat.card (Subgroup.center G) = 2 ∧
      Nonempty ((G ⧸ Subgroup.center G) ≃* alternatingGroup (Fin 7)) := by
  let π : G →* G ⧸ Subgroup.zpowers z := QuotientGroup.mk' (Subgroup.zpowers z)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.zpowers z := QuotientGroup.ker_mk' _
  have hsimple7 : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  have hperf7 : Group.IsPerfect (alternatingGroup (Fin 7)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by norm_num))
  have hperfH : Group.IsPerfect (G ⧸ Subgroup.zpowers z) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcard7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    norm_num [Nat.factorial]
  have heven : 2 ∣ Nat.card (G ⧸ Subgroup.zpowers z) := by
    rw [Nat.card_congr e.toEquiv, hcard7]
    norm_num
  have hcomm : commutator G = ⊤ :=
    h.commutator_eq_top_of_quotient_perfect (Group.isPerfect_def.mp hperfH) heven
  have hsimpleH : IsSimpleGroup (G ⧸ Subgroup.zpowers z) :=
    (MulEquiv.isSimpleGroup_congr e).mpr hsimple7
  have hHcenter : Subgroup.center (G ⧸ Subgroup.zpowers z) = ⊥ := by
    rcases hsimpleH.eq_bot_or_eq_top_of_normal (Subgroup.center (G ⧸ Subgroup.zpowers z))
      with hbot | htop
    · exact hbot
    · exfalso
      have hc : IsMulCommutative (G ⧸ Subgroup.zpowers z) := Subgroup.center_eq_top_iff.mp htop
      exact Group.IsPerfect.not_isMulCommutative (G ⧸ Subgroup.zpowers z) hc
  have hcenter : Subgroup.center G = Subgroup.zpowers z := by
    apply le_antisymm
    · intro g hg
      have h1 : π g ∈ Subgroup.center (G ⧸ Subgroup.zpowers z) :=
        Subgroup.map_center_le_center hπ ⟨g, hg, rfl⟩
      rw [hHcenter] at h1
      have h2 : π g = 1 := h1
      rw [← hker]
      exact h2
    · exact h.zpowers_le_center
  have eC : (G ⧸ Subgroup.center G) ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans e
  exact ⟨hcomm, hcenter, (MulEquiv.isSimpleGroup_congr eC).mpr hsimple7,
    by rw [hcenter, h.natCard_zpowers], ⟨eC⟩⟩

end QuaternionSetting

theorem exists_normal_psl2_core_of_pgl2 {R : Type u} [Group R] [Finite R] (N : Subgroup R)
    (hN : N.Normal) {K : Type u} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (e : N ≃* PGL2 K) :
    ∃ L : Subgroup R, L.Normal ∧ L ≤ N ∧ Nonempty (L ≃* PSL2 K) := by
  by_cases h3 : Nat.card K = 3
  · have : Fintype K := Fintype.ofFinite K
    let eK : ZMod 3 ≃+* K :=
      ZMod.ringEquivOfPrime K Nat.prime_three (by simpa [Nat.card_eq_fintype_card] using h3)
    obtain ⟨M, hMn, hMle, ⟨eM⟩⟩ :=
      CFSG.GorensteinWalter.exists_normal_psl2_three_core_of_normal_mulEquiv_pgl2_three N hN
        (e.trans (CFSG.GorensteinWalter.pgl2RingEquiv eK).symm)
    exact ⟨M, hMn, hMle, ⟨eM.trans (CFSG.GorensteinWalter.psl2RingEquiv eK)⟩⟩
  · have hodd : Odd (Nat.card K) := by
      obtain ⟨p, f, -, hpodd, -, hq⟩ := hK
      rw [hq]
      exact hpodd.pow
    have hone : 1 < Nat.card K := Finite.one_lt_card
    have hgt : 3 < Nat.card K := by
      obtain ⟨k, hk⟩ := hodd
      omega
    exact CFSG.GorensteinWalter.exists_normal_psl2_core_of_normal_mulEquiv_pgl2_card_gt_three N hN
      K hK hgt e

theorem ringChar_ne_two_of_odd_natCard (K : Type*) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) : ringChar K ≠ 2 := by
  intro hr
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  apply h2
  have h0 : ((ringChar K : ℕ) : K) = 0 := ringChar.Nat.cast_ringChar
  rw [hr] at h0
  simpa using h0

theorem odd_natCard_of_isOddPrimePower {n : ℕ} (hK : IsOddPrimePower n) : Odd n := by
  obtain ⟨p, f, -, hpodd, -, hq⟩ := hK
  rw [hq]
  exact hpodd.pow

theorem sylow_le_of_normal_of_odd_index {G : Type*} [Group G] [Finite G] (L : Subgroup G)
    [L.Normal] (hL : Odd L.index) (P : Sylow 2 G) : (P : Subgroup G) ≤ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  have h1 : orderOf (QuotientGroup.mk' L x) ∣ 2 ^ k := hk ▸ orderOf_map_dvd (QuotientGroup.mk' L) x
  have h2 : orderOf (QuotientGroup.mk' L x) ∣ L.index :=
    (Subgroup.index_eq_card L) ▸ orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) L.index := (Nat.coprime_two_left.mpr hL).pow_left k
  have h3 : orderOf (QuotientGroup.mk' L x) = 1 :=
    Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h3)

namespace QuaternionSetting

variable {G : Type u} [Group G] {z : G} {r : ℕ} (h : QuaternionSetting G z r)

include h

theorem sylow_equiv_of_odd_index [Finite G] (L : Subgroup G) [L.Normal] (hL : Odd L.index)
    (T : Sylow 2 L) : Nonempty ((T : Subgroup L) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 G) := inferInstance
  have hPL := sylow_le_of_normal_of_odd_index L hL P
  obtain ⟨e⟩ := h.sylow_equiv P
  exact ⟨((Sylow.equiv T (P.subtype hPL)).trans (Subgroup.subgroupOfEquivOfLe hPL)).trans e⟩

end QuaternionSetting

end CFSG.ClassicalInvolution.QuaternionStructure
