module

public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne
public import CFSG.CharacterTheory.Semidihedral.ProjectiveSL2Cover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup

namespace RankOneCover

@[expose] def quatToDih (m : ℕ) : QuaternionGroup m →* DihedralGroup m where
  toFun g := match g with
    | .a i => .r (ZMod.castHom (dvd_mul_left m 2) (ZMod m) i)
    | .xa i => .sr (ZMod.castHom (dvd_mul_left m 2) (ZMod m) i)
  map_one' := by
    change DihedralGroup.r (ZMod.castHom (dvd_mul_left m 2) (ZMod m) 0) = DihedralGroup.r 0
    rw [map_zero]
  map_mul' x y := by
    rcases x with i | i <;> rcases y with j | j
    · change DihedralGroup.r _ = DihedralGroup.r _ * DihedralGroup.r _
      rw [DihedralGroup.r_mul_r, map_add]
    · change DihedralGroup.sr _ = DihedralGroup.r _ * DihedralGroup.sr _
      rw [DihedralGroup.r_mul_sr, map_sub]
    · change DihedralGroup.sr _ = DihedralGroup.sr _ * DihedralGroup.r _
      rw [DihedralGroup.sr_mul_r, map_add]
    · change DihedralGroup.r _ = DihedralGroup.sr _ * DihedralGroup.sr _
      rw [DihedralGroup.sr_mul_sr, map_sub, map_add, map_natCast, ZMod.natCast_self, zero_add]

theorem quatToDih_surjective (m : ℕ) [NeZero m] : Function.Surjective (quatToDih m) := by
  have hcast : ∀ j : ZMod m, ZMod.castHom (dvd_mul_left m 2) (ZMod m) (j.val : ZMod (2 * m)) =
      j := fun j => by
    rw [map_natCast, ZMod.natCast_zmod_val]
  rintro (j | j)
  · exact ⟨QuaternionGroup.a (j.val : ZMod (2 * m)), by
      change DihedralGroup.r _ = _
      rw [hcast]⟩
  · exact ⟨QuaternionGroup.xa (j.val : ZMod (2 * m)), by
      change DihedralGroup.sr _ = _
      rw [hcast]⟩

theorem quatToDih_a_m (m : ℕ) : quatToDih m (QuaternionGroup.a (m : ZMod (2 * m))) = 1 := by
  change DihedralGroup.r _ = DihedralGroup.r 0
  rw [map_natCast, ZMod.natCast_self]

theorem eq_one_of_odd_orderOf_of_pow {G : Type*} [Group G] {x : G} (hodd : Odd (orderOf x))
    {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  · rw [hj, pow_succ] at hodd
    exact absurd hodd (Nat.not_odd_iff_even.mpr (even_two.mul_left _))

theorem exists_two_pow_of_mem_center {A : Type*} [Group A] [Finite A]
    (hA : CFSG.oddCore A = ⊥) {x : A} (hx : x ∈ center A) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨k, ?_⟩
  have hy : orderOf (x ^ 2 ^ k) = m := by
    rw [orderOf_pow' x (pow_ne_zero k two_ne_zero), hkm, Nat.gcd_eq_right (dvd_mul_right _ _),
      Nat.mul_div_cancel_left m (pow_pos two_pos k)]
  have hyc : x ^ 2 ^ k ∈ center A := pow_mem hx _
  have hnorm : (zpowers (x ^ 2 ^ k)).Normal := normal_of_le_center (zpowers_le.mpr hyc)
  have hodd : Odd (Nat.card (zpowers (x ^ 2 ^ k))) := by
    rw [Nat.card_zpowers, hy]
    exact hm
  have hle := UnbalancedCatalog.EvenCatalog.le_oddCore_of_normal hnorm hodd
  rw [hA, le_bot_iff, zpowers_eq_bot] at hle
  exact hle

theorem isPGroup_zpowers_of_pow {G : Type*} [Group G] {x : G} {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    IsPGroup 2 (zpowers x) := by
  rintro ⟨g, n, rfl⟩
  refine ⟨k, Subtype.ext ?_⟩
  change ((fun n : ℤ => x ^ n) n) ^ 2 ^ k = 1
  simp only
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]

theorem orderOf_a_m {m : ℕ} (hm : 1 ≤ m) :
    orderOf (QuaternionGroup.a (m : ZMod (2 * m))) = 2 := by
  apply orderOf_eq_prime
  · rw [sq, QuaternionGroup.a_mul_a, ← Nat.cast_add, ← two_mul, ZMod.natCast_self]
    rfl
  · intro h
    have h1 : (m : ZMod (2 * m)) = 0 := QuaternionGroup.a.inj (h.trans QuaternionGroup.one_def)
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := Nat.le_of_dvd (by omega) h1
    omega

theorem quaternion_central_eq {S : Type*} [Group S] {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* QuaternionGroup m) {x : S} (hx : ∀ s : S, s * x = x * s) (hx1 : x ≠ 1) :
    e x = QuaternionGroup.a (m : ZMod (2 * m)) := by
  have hcen : e x ∈ center (QuaternionGroup m) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨s, rfl⟩ := e.surjective q
    rw [← map_mul, ← map_mul, hx s]
  rcases ((CFSG.GroupTheory.quaternion_centralizers hm).2.2.1 _).mp hcen with h | h
  · exfalso
    apply hx1
    apply e.injective
    rw [h, map_one]
    rfl
  · exact h

theorem center_eq_zpowers {A : Type*} [Group A] [Finite A] (hA : CFSG.oddCore A = ⊥)
    {z : A} (hzZ : z ∈ center A) (huniq : ∀ y : A, orderOf y = 2 → y = z)
    (hsyl : ∀ S : Sylow 2 A, ∃ r : ℕ, 3 ≤ r ∧ Nonempty (S ≃* QuaternionGroup (2 ^ (r - 2)))) :
    center A = zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro x hx
    obtain ⟨k, hk⟩ := exists_two_pow_of_mem_center hA hx
    obtain ⟨S, hS⟩ := (isPGroup_zpowers_of_pow hk).exists_le_sylow
    have hxS : x ∈ (S : Subgroup A) := hS (mem_zpowers x)
    obtain ⟨r, hr, ⟨e⟩⟩ := hsyl S
    have hm : 2 ≤ 2 ^ (r - 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem _
    have hx1' : (⟨x, hxS⟩ : S) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hcomm : ∀ s : S, s * ⟨x, hxS⟩ = ⟨x, hxS⟩ * s := fun s =>
      Subtype.ext (mem_center_iff.mp hx s)
    have hex := quaternion_central_eq hm e hcomm hx1'
    have hord : orderOf x = 2 := by
      rw [← Subgroup.orderOf_mk x hxS, ← MulEquiv.orderOf_eq e, hex, orderOf_a_m (by omega)]
    rw [huniq x hord]
    exact mem_zpowers z
  · rw [zpowers_le]
    exact hzZ

theorem sylow_mulEquiv_map {J : Type*} [Group J] [Finite J] (D : Sylow 2 J) :
    Nonempty ((D : Subgroup J) ≃*
      (D.mapSurjective (QuotientGroup.mk'_surjective (CFSG.oddCore J)) :
        Subgroup (J ⧸ CFSG.oddCore J))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := (QuotientGroup.mk' (CFSG.oddCore J)).comp (D : Subgroup J).subtype with hfdef
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have hdO : (d : J) ∈ CFSG.oddCore J := (QuotientGroup.eq_one_iff _).mp hd
    have hodd : Odd (orderOf (d : J)) :=
      UnbalancedCatalog.EvenCatalog.odd_card_oddCore.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hdO)
    obtain ⟨k, hk⟩ := D.isPGroup' d
    have hk' : (d : J) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      rwa [Subgroup.coe_pow, OneMemClass.coe_one] at this
    exact Subtype.ext (eq_one_of_odd_orderOf_of_pow hodd hk')
  refine ⟨(MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr ?_)⟩
  rw [hfdef, MonoidHom.range_comp, range_subtype]
  rfl

theorem image_sylow_dihedral {A : Type*} [Group A] [Finite A] {z : A} (hz : orderOf z = 2)
    (hZ : center A = zpowers z) (S : Sylow 2 A) {r : ℕ} (hr : 3 ≤ r)
    (e : S ≃* QuaternionGroup (2 ^ (r - 2))) :
    Nonempty ((S.mapSurjective (QuotientGroup.mk'_surjective (center A)) :
      Subgroup (A ⧸ center A)) ≃* DihedralGroup (2 ^ (r - 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set m := 2 ^ (r - 2) with hmdef
  have hm2 : 2 ≤ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : NeZero m := ⟨by omega⟩
  have hzS : z ∈ (S : Subgroup A) := by
    have hP : IsPGroup 2 (center A) := by
      rw [hZ]
      exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
    exact hP.le_sylow_of_normal S (by rw [hZ]; exact mem_zpowers z)
  set z' : S := ⟨z, hzS⟩ with hz'
  have hz'1 : z' ≠ 1 := by
    intro h
    have h1 : z = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hz
    omega
  have hzZ : z ∈ center A := hZ ▸ mem_zpowers z
  have hz'c : ∀ s : S, s * z' = z' * s := fun s =>
    Subtype.ext (mem_center_iff.mp hzZ s)
  have hez : e z' = QuaternionGroup.a (m : ZMod (2 * m)) := quaternion_central_eq hm2 e hz'c hz'1
  set π' := (QuotientGroup.mk' (center A)).comp (S : Subgroup A).subtype with hπ'
  set ψ := (RankOneCover.quatToDih m).comp e.toMonoidHom with hψ
  have hψs : Function.Surjective ψ := (quatToDih_surjective m).comp e.surjective
  have hkerπ : π'.ker = zpowers z' := by
    ext s
    rw [MonoidHom.mem_ker, hπ', MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hZ]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by simpa [hz'] using hn)⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, by simp [hz']⟩
  have hkerψ : ψ.ker = zpowers z' := by
    have hle : zpowers z' ≤ ψ.ker := by
      rw [zpowers_le, MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hez,
        quatToDih_a_m]
    have hcardS : Nat.card S = 4 * m := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have hcardK : Nat.card ψ.ker = 2 := by
      have h1 := ψ.ker.card_eq_card_quotient_mul_card_subgroup
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv,
        DihedralGroup.nat_card, hcardS] at h1
      have h2 : 4 * m = 2 * m * 2 := by ring
      rw [h2] at h1
      exact (Nat.eq_of_mul_eq_mul_left (by omega) h1).symm
    have hcardZ : Nat.card (zpowers z') = 2 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz]
    exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (hcardK.trans hcardZ.symm))).symm
  have hrange : π'.range = (S.mapSurjective (QuotientGroup.mk'_surjective (center A)) :
      Subgroup (A ⧸ center A)) := by
    rw [hπ', MonoidHom.range_comp, range_subtype]
    rfl
  exact ⟨((MulEquiv.subgroupCongr hrange).symm.trans
    (QuotientGroup.quotientKerEquivRange π').symm).trans
      ((QuotientGroup.quotientMulEquivOfEq (hkerπ.trans hkerψ.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψs))⟩

theorem central_double_cover {A : Type*} [Group A] [Finite A] {z : A} (hz : orderOf z = 2)
    (hzZ : z ∈ center A) (hZ : center A = zpowers z) (S : Sylow 2 A) {r : ℕ} (hr : 3 ≤ r)
    (e : S ≃* QuaternionGroup (2 ^ (r - 2))) (k : Type*) [Field k] [Finite k]
    (hk : ringChar k ≠ 2)
    (φ : A ⧸ center A ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 k) :
    ∃ F : A ≃* Matrix.SpecialLinearGroup (Fin 2) k,
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 2 k).comp F.toMonoidHom =
        φ.toMonoidHom.comp (QuotientGroup.mk' (center A)) ∧
      ((F z : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = -1 := by
  set Ψ := CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
    2 k with hΨ
  set pi : A →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    Ψ.symm.toMonoidHom.comp (φ.toMonoidHom.comp (QuotientGroup.mk' (center A))) with hpidef
  have hpi : Function.Surjective pi :=
    Ψ.symm.surjective.comp (φ.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : pi.ker = zpowers z := by
    rw [← hZ]
    ext x
    rw [MonoidHom.mem_ker, hpidef, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨F, hF, hFz⟩ := CFSG.Semidihedral.ProjectiveSL2Cover.quaternion_central_double_cover_native
    k hk z hz hzZ pi hpi hker S r hr e
  refine ⟨F, ?_, ?_⟩
  · ext x
    have h1 := congrArg (fun f : A →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k => f x) hF
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1 ⊢
    change Ψ (CFSG.Semidihedral.ProjectiveSL2Cover.nativeQuotient k (F x)) = _
    rw [h1, hpidef, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  · rw [hFz, CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_matrix, map_neg, map_one]

end RankOneCover

open RankOneCover

theorem rank_one_quasisimple_odd_core_quotient_central_cover {J : Type*} [Group J] [Finite J]
    (hrank : CFSG.pRank 2 J ≤ 1) (hA : CFSG.IsQuasisimple (J ⧸ CFSG.oddCore J)) :
    CFSG.oddCore (J ⧸ CFSG.oddCore J) = ⊥ ∧
    ∃ z : J ⧸ CFSG.oddCore J, orderOf z = 2 ∧ (∀ y : J ⧸ CFSG.oddCore J, orderOf y = 2 → y = z) ∧
      center (J ⧸ CFSG.oddCore J) = zpowers z ∧ Nat.card (center (J ⧸ CFSG.oddCore J)) = 2 ∧
      ∃ r : ℕ, 3 ≤ r ∧
        (∀ S : Sylow 2 J, Nonempty (S ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
        (∀ S : Sylow 2 (J ⧸ CFSG.oddCore J), Nonempty (S ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
        IsSimpleGroup ((J ⧸ CFSG.oddCore J) ⧸ center (J ⧸ CFSG.oddCore J)) ∧
        (∃ a b : (J ⧸ CFSG.oddCore J) ⧸ center (J ⧸ CFSG.oddCore J), a * b ≠ b * a) ∧
        (∀ P : Sylow 2 ((J ⧸ CFSG.oddCore J) ⧸ center (J ⧸ CFSG.oddCore J)),
          Nonempty (P ≃* DihedralGroup (2 ^ (r - 2))) ∧ Nat.card P = 2 ^ (r - 1) ∧
          (r = 3 → IsKleinFour P)) ∧
        ∀ (k : Type*) [Field k] [Finite k], ringChar k ≠ 2 →
          ∀ φ : (J ⧸ CFSG.oddCore J) ⧸ center (J ⧸ CFSG.oddCore J) ≃*
            CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 k,
            ∃ F : J ⧸ CFSG.oddCore J ≃* Matrix.SpecialLinearGroup (Fin 2) k,
              (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 2 k).comp F.toMonoidHom =
                φ.toMonoidHom.comp (QuotientGroup.mk' (center (J ⧸ CFSG.oddCore J))) ∧
              ((F z : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = -1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.oddCore J with hOdef
  have hOA : CFSG.oddCore (J ⧸ O) = ⊥ := CFSG.ComponentClassification.OddCore.quotient_corefree J
  have hOodd : ¬ 2 ∣ Nat.card O := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact UnbalancedCatalog.EvenCatalog.odd_card_oddCore
  have hrankA : CFSG.pRank 2 (J ⧸ O) ≤ 1 := by
    rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_quotient_eq O hOodd,
      ← SectionRank.pRank_eq_open_pRank_top]
    exact hrank
  obtain ⟨-, ⟨z, hz, hzuniq⟩, hcentral, hsyl⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.quasisimple_rank_one_unique_central_involution hA hrankA
  have hzZ : z ∈ center (J ⧸ O) := hcentral z hz
  have huniq : ∀ y : J ⧸ O, orderOf y = 2 → y = z := fun y hy => hzuniq y hy
  have hZ : center (J ⧸ O) = zpowers z := center_eq_zpowers hOA hzZ huniq hsyl
  have hZcard : Nat.card (center (J ⧸ O)) = 2 := by rw [hZ, Nat.card_zpowers, hz]
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 (J ⧸ O)) := inferInstance
  obtain ⟨r, hr, ⟨e₀⟩⟩ := hsyl S₀
  have hsylA : ∀ S : Sylow 2 (J ⧸ O), Nonempty (S ≃* QuaternionGroup (2 ^ (r - 2))) :=
    fun S => ⟨(Sylow.equiv S S₀).trans e₀⟩
  have hsylJ : ∀ S : Sylow 2 J, Nonempty (S ≃* QuaternionGroup (2 ^ (r - 2))) := by
    intro S
    obtain ⟨e₁⟩ := sylow_mulEquiv_map S
    obtain ⟨e₂⟩ := hsylA (S.mapSurjective (QuotientGroup.mk'_surjective O))
    exact ⟨e₁.trans e₂⟩
  obtain ⟨eD⟩ := image_sylow_dihedral hz hZ S₀ hr e₀
  have hsylT : ∀ P : Sylow 2 ((J ⧸ O) ⧸ center (J ⧸ O)),
      Nonempty (P ≃* DihedralGroup (2 ^ (r - 2))) ∧ Nat.card P = 2 ^ (r - 1) ∧
        (r = 3 → IsKleinFour P) := by
    intro P
    have eP := (Sylow.equiv P (S₀.mapSurjective
      (QuotientGroup.mk'_surjective (center (J ⧸ O))))).trans eD
    have hcard : Nat.card P = 2 ^ (r - 1) := by
      rw [Nat.card_congr eP.toEquiv, DihedralGroup.nat_card, ← pow_succ']
      congr 1
      omega
    refine ⟨⟨eP⟩, hcard, fun hr3 => ?_⟩
    subst hr3
    refine ⟨by rw [hcard]; rfl, ?_⟩
    rw [Monoid.exponent_eq_of_mulEquiv eP]
    show Monoid.exponent (DihedralGroup 2) = 2
    exact IsKleinFour.exponent_two
  refine ⟨hOA, z, hz, huniq, hZ, hZcard, r, hr, hsylJ, hsylA, hA.2.1, hA.2.2, hsylT,
    fun k _ _ hk φ => central_double_cover hz hzZ hZ S₀ hr e₀ k hk φ⟩

end CFSG.ComponentClassification.UnbalancedGS
