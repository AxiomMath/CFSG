module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneAffineTrivialPair
public import CFSG.LocalAnalysis.SeitzReduction.RankOneDegreeEightPerm
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV CFSG.LocalAnalysis.SteinbergBX
open scoped Pointwise LinearAlgebra.Projectivization CFSG.SeitzReduction.RankOne.DegreeEight

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem mem_of_sq_eq_one_of_odd_card_quotient {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    [E.Normal] (hodd : Odd (Nat.card (G ⧸ E))) {g : G} (hg : g ^ 2 = 1) : g ∈ E := by
  obtain ⟨k, hk⟩ := hodd
  have h1 : ((g : G ⧸ E)) ^ Nat.card (G ⧸ E) = 1 := pow_card_eq_one'
  rw [hk, pow_succ, pow_mul, ← QuotientGroup.mk_pow, hg, QuotientGroup.mk_one, one_pow,
    one_mul] at h1
  exact (QuotientGroup.eq_one_iff g).1 h1

theorem two_pow_mod_seven (j : ℕ) : 2 ^ j % 7 = 1 ∨ 2 ^ j % 7 = 2 ∨ 2 ^ j % 7 = 4 := by
  induction j with
  | zero => left; rfl
  | succ j ih => rw [pow_succ, Nat.mul_mod]; rcases ih with h | h | h <;> rw [h] <;> simp

section GMS

variable {D : Type} [Group D] {J R X U P : Subgroup D} {n : ℕ}

theorem card_range_gmsRootConjugateAction [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) :
    Nat.card (gmsRootConjugateAction (U ⊔ R) R).range =
      2 ^ n * Nat.card (gmsPermStabilizer U R) := by
  classical
  set R₀ : gmsRootConjugates (U ⊔ R) R := ⟨R, gms_R_mem⟩
  have hΔcard : Nat.card (gmsRootConjugates (U ⊔ R) R) = 2 ^ n := by
    rw [Nat.card_coe_set_eq]
    exact (gms_normal_root_partition_and_two_transitivity h h3).2.1
  have : MulAction.IsPretransitive (gmsRootConjugateAction (U ⊔ R) R).range
      (gmsRootConjugates (U ⊔ R) R) := ⟨fun Q Z => by
    have := gms_isPretransitive h
    obtain ⟨l, hl⟩ := MulAction.exists_smul_eq (normalizer ((U ⊔ R : Subgroup D) : Set D)) Q Z
    exact ⟨⟨gmsRootConjugateAction (U ⊔ R) R l, l, rfl⟩, hl⟩⟩
  have hNstab := Subgroup.card_mul_index
    (MulAction.stabilizer (gmsRootConjugateAction (U ⊔ R) R).range R₀)
  rw [MulAction.index_stabilizer_of_transitive, hΔcard] at hNstab
  have hNRstab : (MulAction.stabilizer (gmsRootConjugateAction (U ⊔ R) R).range R₀).map
      (gmsRootConjugateAction (U ⊔ R) R).range.subtype = gmsPermStabilizer U R := by
    ext x
    rw [GMSDichotomy.mem_gmsPermStabilizer]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, MulAction.mem_stabilizer_iff.1 hy⟩
    · rintro ⟨hx, hxR⟩
      exact ⟨⟨x, hx⟩, MulAction.mem_stabilizer_iff.2 hxR, rfl⟩
  rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hNRstab] at hNstab
  rw [← hNstab, mul_comm]

theorem card_gmsPermStabilizer [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) :
    Nat.card (gmsPermStabilizer U R) = (2 ^ n - 1) * Nat.card (gmsPermStabilizer U R ⧸
      (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) := by
  have hT'card : Nat.card ((gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) =
      2 ^ n - 1 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (GMSDichotomy.gmsSingerPermImage_le h)).toEquiv,
      (GMSDichotomy.isCyclic_gmsSingerPermImage h h3).2]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)), hT'card, mul_comm]

theorem comap_gmsRootConjugateAction_package (V R : Subgroup D)
    {M : Subgroup (Equiv.Perm (gmsRootConjugates V R))}
    (hMN : M ≤ (gmsRootConjugateAction V R).range)
    (hMn : (M.subgroupOf (gmsRootConjugateAction V R).range).Normal) :
    (M.comap (gmsRootConjugateAction V R)).Normal ∧
      gmsRootKernel V R ≤ M.comap (gmsRootConjugateAction V R) ∧
      Nonempty (↥(M.comap (gmsRootConjugateAction V R)) ⧸
          (gmsRootKernel V R).subgroupOf (M.comap (gmsRootConjugateAction V R)) ≃* M) := by
  refine ⟨⟨fun l hl g => ?_⟩, fun l hl => ?_, ?_⟩
  · rw [mem_comap] at hl ⊢
    have h1 := hMn.conj_mem ⟨_, hMN hl⟩ (mem_subgroupOf.2 hl) ⟨_, ⟨g, rfl⟩⟩
    rw [mem_subgroupOf] at h1
    rw [map_mul, map_mul, map_inv]
    exact h1
  · rw [← ker_gmsRootConjugateAction, MonoidHom.mem_ker] at hl
    rw [mem_comap, hl]
    exact one_mem M
  · set φ : M.comap (gmsRootConjugateAction V R) →* M :=
      ((gmsRootConjugateAction V R).comp
        (M.comap (gmsRootConjugateAction V R)).subtype).codRestrict M (fun x => x.2) with hφ
    have hφsurj : Function.Surjective φ := by
      rintro ⟨e, he⟩
      obtain ⟨l, hl⟩ := hMN he
      exact ⟨⟨l, by rw [mem_comap, hl]; exact he⟩, Subtype.ext hl⟩
    have hφker : φ.ker = (gmsRootKernel V R).subgroupOf (M.comap (gmsRootConjugateAction V R)) := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf, ← ker_gmsRootConjugateAction, MonoidHom.mem_ker]
      exact ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)⟩

theorem gms_regular_normal_package [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard)
    (hodd : Odd (Nat.card (gmsPermStabilizer U R)))
    (E : Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)))
    (hEN : E ≤ (gmsRootConjugateAction (U ⊔ R) R).range)
    (hEn : (E.subgroupOf (gmsRootConjugateAction (U ⊔ R) R).range).Normal)
    (hreg : ∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃! a : E,
      (a : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) Q = Z) :
    (∀ σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range, σ ∈ E ↔ σ = 1 ∨ orderOf σ = 2) ∧
    IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ n ∧
    E ⊓ gmsSingerPermImage X U R = ⊥ ∧
    E ⊔ gmsPermStabilizer U R = (gmsRootConjugateAction (U ⊔ R) R).range ∧
    E ⊔ gmsSingerPermImage X U R ≤ (gmsRootConjugateAction (U ⊔ R) R).range ∧
    ((E ⊔ gmsSingerPermImage X U R).subgroupOf
      (gmsRootConjugateAction (U ⊔ R) R).range).Normal ∧
    Nat.card (E ⊔ gmsSingerPermImage X U R : Subgroup _) = 2 ^ n * (2 ^ n - 1) ∧
    (∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃ f ∈ E ⊔ gmsSingerPermImage X U R, f Q = Z) ∧
    (∀ f ∈ E ⊔ gmsSingerPermImage X U R, f ≠ 1 → ∀ Q Z : gmsRootConjugates (U ⊔ R) R,
      f Q = Q → f Z = Z → Q = Z) ∧
    (E.comap (gmsRootConjugateAction (U ⊔ R) R)).Normal ∧
    gmsRootKernel (U ⊔ R) R ≤ E.comap (gmsRootConjugateAction (U ⊔ R) R) ∧
    Nonempty (↥(E.comap (gmsRootConjugateAction (U ⊔ R) R)) ⧸
        (gmsRootKernel (U ⊔ R) R).subgroupOf (E.comap (gmsRootConjugateAction (U ⊔ R) R)) ≃*
      E) ∧
    ((E ⊔ gmsSingerPermImage X U R).comap (gmsRootConjugateAction (U ⊔ R) R)).Normal ∧
    gmsRootKernel (U ⊔ R) R ≤
      (E ⊔ gmsSingerPermImage X U R).comap (gmsRootConjugateAction (U ⊔ R) R) ∧
    Nonempty (↥((E ⊔ gmsSingerPermImage X U R).comap (gmsRootConjugateAction (U ⊔ R) R)) ⧸
        (gmsRootKernel (U ⊔ R) R).subgroupOf
          ((E ⊔ gmsSingerPermImage X U R).comap (gmsRootConjugateAction (U ⊔ R) R)) ≃*
      ↥(E ⊔ gmsSingerPermImage X U R)) := by
  classical
  set R₀ : gmsRootConjugates (U ⊔ R) R := ⟨R, gms_R_mem⟩
  obtain ⟨hEel, hEcard, hFN, hFn, hFcard, hFtrans, hFfrob⟩ :=
    (gms_normal_root_action_dichotomy_branch_completion h h3).2.2.2.2.2.2.2.2.1 E hEN hEn hreg
  have hNRN : gmsPermStabilizer U R ≤ (gmsRootConjugateAction (U ⊔ R) R).range := inf_le_left
  have hEfree : ∀ a ∈ E, ∀ Q, a Q = Q → a = 1 := by
    intro a ha Q haQ
    obtain ⟨b, -, hb⟩ := hreg Q Q
    exact congrArg Subtype.val ((hb ⟨a, ha⟩ haQ).trans (hb 1 rfl).symm)
  have hinv : ∀ σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range,
      σ ∈ E ↔ σ = 1 ∨ orderOf σ = 2 := by
    intro σ hσ
    constructor
    · intro hσE
      have hsq : σ ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian σ hσE
      rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hsq) with h1 | h1
      · exact Or.inl (orderOf_eq_one_iff.1 h1)
      · exact Or.inr h1
    · rintro (rfl | h2)
      · exact one_mem E
      · have := hEn
        have hq : Nat.card ((gmsRootConjugateAction (U ⊔ R) R).range ⧸
            E.subgroupOf (gmsRootConjugateAction (U ⊔ R) R).range) =
            Nat.card (gmsPermStabilizer U R) := by
          have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
            (E.subgroupOf (gmsRootConjugateAction (U ⊔ R) R).range)
          rw [card_range_gmsRootConjugateAction h h3,
            Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv, hEcard] at h1
          exact (Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ n)
            (h1.trans (mul_comm _ _))).symm
        have h1 := mem_of_sq_eq_one_of_odd_card_quotient (hq ▸ hodd)
          (g := (⟨σ, hσ⟩ : (gmsRootConjugateAction (U ⊔ R) R).range)) (by
            rw [← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_mk, h2])
        exact mem_subgroupOf.1 h1
  have hET : E ⊓ gmsSingerPermImage X U R = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨haE, haT⟩ := mem_inf.1 ha
    rw [mem_bot]
    exact hEfree a haE R₀ (GMSDichotomy.mem_gmsPermStabilizer.1
      (GMSDichotomy.gmsSingerPermImage_le h haT)).2
  have hENR : E ⊔ gmsPermStabilizer U R = (gmsRootConjugateAction (U ⊔ R) R).range := by
    refine le_antisymm (sup_le hEN hNRN) (fun x hx => ?_)
    obtain ⟨⟨a, ha⟩, haR, -⟩ := hreg R₀ (x R₀)
    have haR' : a R₀ = x R₀ := haR
    have hm : a⁻¹ * x ∈ gmsPermStabilizer U R := GMSDichotomy.mem_gmsPermStabilizer.2
      ⟨mul_mem (inv_mem (hEN ha)) hx, by rw [Equiv.Perm.mul_apply, ← haR',
        GMSAffine.perm_inv_apply]⟩
    have hx' : x = a * (a⁻¹ * x) := by group
    rw [hx']
    exact mul_mem (mem_sup_left ha) (mem_sup_right hm)
  obtain ⟨hEc1, hEc2, hEc3⟩ := comap_gmsRootConjugateAction_package (U ⊔ R) R hEN hEn
  obtain ⟨hFc1, hFc2, hFc3⟩ := comap_gmsRootConjugateAction_package (U ⊔ R) R hFN hFn
  exact ⟨hinv, hEel, hEcard, hET, hENR, hFN, hFn, hFcard, hFtrans, hFfrob, hEc1, hEc2, hEc3,
    hFc1, hFc2, hFc3⟩

theorem exists_gmsSingerPermImage_generator [Finite D] (h : GMSNormalRootData J R X U P 3)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) :
    ∃ a ∈ gmsSingerPermImage X U R, orderOf a = 7 ∧
      ∀ t ∈ gmsSingerPermImage X U R, ∃ m : ℕ, a ^ m = t := by
  obtain ⟨hcyc, hcard⟩ := GMSDichotomy.isCyclic_gmsSingerPermImage h h3
  obtain ⟨⟨a, ha⟩, hgen⟩ := hcyc.exists_generator
  have hord : orderOf (⟨a, ha⟩ : gmsSingerPermImage X U R) = 7 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, hcard]
    norm_num
  refine ⟨a, ha, by rw [← Subgroup.orderOf_mk a ha, hord], fun t ht => ?_⟩
  obtain ⟨m, hm⟩ := mem_powers_iff_mem_zpowers.2 (hgen ⟨t, ht⟩)
  exact ⟨m, by simpa using congrArg Subtype.val hm⟩

theorem exists_pairStabilizer_conj_eq_sq [Finite D] (h : GMSNormalRootData J R X U P 3)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) (β : gmsRootConjugates (U ⊔ R) R)
    (hβ : (β : Subgroup D) ≠ R) (hB : Nat.card (gmsPairStabilizer U R β) = 3)
    {a : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)} (ha : a ∈ gmsSingerPermImage X U R)
    (ha7 : orderOf a = 7) :
    ∃ b ∈ gmsPairStabilizer U R β, b * a * b⁻¹ = a ^ 2 := by
  obtain ⟨-, hTB, -, -, -⟩ := gms_pairStabilizer_structure h h3 β hβ (X := X)
  have hBne : gmsPairStabilizer U R β ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hB]
    norm_num
  obtain ⟨⟨b₀, hb₀B⟩, hb₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hBne
  have hb₀1' : b₀ ≠ 1 := fun h1 => hb₀1 (Subtype.ext h1)
  have hb₀H : b₀ ∈ gmsPermStabilizer U R := (mem_inf.1 hb₀B).1
  obtain ⟨j, hj⟩ := GMSDichotomy.exists_conj_eq_pow_perm h h3 hb₀H
  have ha7' : a ^ 7 = 1 := by rw [← ha7]; exact pow_orderOf_eq_one a
  have hT7 : ∀ t ∈ gmsSingerPermImage X U R, t ^ 7 = 1 := fun t ht => by
    have h1 := pow_card_eq_one' (G := gmsSingerPermImage X U R) (x := ⟨t, ht⟩)
    rw [(GMSDichotomy.isCyclic_gmsSingerPermImage h h3).2] at h1
    exact congrArg Subtype.val h1
  rcases two_pow_mod_seven j with h1 | h2 | h4
  · exfalso
    apply hb₀1'
    have hcomm : ∀ t ∈ gmsSingerPermImage X U R, b₀ * t = t * b₀ := by
      intro t ht
      have h2 := hj t ht
      rw [pow_eq_pow_mod _ (hT7 t ht), h1, pow_one] at h2
      calc b₀ * t = b₀ * t * b₀⁻¹ * b₀ := by group
        _ = t * b₀ := by rw [h2]
    have hb₀T := GMSDichotomy.mem_gmsSingerPermImage_of_commute h h3 hb₀H hcomm
    have h5 : b₀ ∈ gmsSingerPermImage X U R ⊓ gmsPairStabilizer U R β := mem_inf.2 ⟨hb₀T, hb₀B⟩
    rwa [hTB, mem_bot] at h5
  · exact ⟨b₀, hb₀B, by rw [hj a ha, pow_eq_pow_mod _ ha7', h2]⟩
  · refine ⟨b₀ ^ 2, pow_mem hb₀B 2, ?_⟩
    calc b₀ ^ 2 * a * (b₀ ^ 2)⁻¹ = b₀ * (b₀ * a * b₀⁻¹) * b₀⁻¹ := by
          rw [pow_two, mul_inv_rev]; group
      _ = b₀ * a ^ (2 ^ j) * b₀⁻¹ := by rw [hj a ha]
      _ = (b₀ * a * b₀⁻¹) ^ (2 ^ j) := by rw [conj_pow]
      _ = (a ^ (2 ^ j)) ^ (2 ^ j) := by rw [hj a ha]
      _ = a ^ 2 := by rw [← pow_mul, pow_eq_pow_mod _ ha7', Nat.mul_mod, h4]

theorem exists_degreeEight_label [Finite D] (h : GMSNormalRootData J R X U P 3)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard)
    {a : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)} (ha : a ∈ gmsSingerPermImage X U R)
    (ha7 : orderOf a = 7) {β : gmsRootConjugates (U ⊔ R) R} (hβ : (β : Subgroup D) ≠ R) :
    ∃ e : Option (ZMod 7) ≃ gmsRootConjugates (U ⊔ R) R, e none = ⟨R, gms_R_mem⟩ ∧
      ∀ i : ZMod 7, e (some i) = (a ^ i.val) β := by
  classical
  set R₀ : gmsRootConjugates (U ⊔ R) R := ⟨R, gms_R_mem⟩ with hR₀
  have haR : a R₀ = R₀ :=
    (GMSDichotomy.mem_gmsPermStabilizer.1 (GMSDichotomy.gmsSingerPermImage_le h ha)).2
  have hapowR : ∀ m : ℕ, (a ^ m) R₀ = R₀ := fun m => by
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, haR]
  have hfR : ∀ i : ZMod 7, (a ^ i.val) β ≠ R₀ := by
    intro i hi
    apply hβ
    have h1 : β = (a ^ i.val)⁻¹ R₀ := by rw [← hi, GMSAffine.perm_inv_apply]
    have h2 : (a ^ i.val)⁻¹ R₀ = R₀ := by rw [Equiv.Perm.inv_eq_iff_eq, hapowR]
    rw [h1, h2]
  let f : Option (ZMod 7) → gmsRootConjugates (U ⊔ R) R := fun z =>
    Option.elim z R₀ (fun i => (a ^ i.val) β)
  have hinj : Function.Injective f := by
    rintro (_ | i) (_ | j) hij
    · rfl
    · exact absurd hij.symm (hfR j)
    · exact absurd hij (hfR i)
    · have hij' : (a ^ i.val) β = (a ^ j.val) β := hij
      have h1 : (a ^ j.val)⁻¹ * a ^ i.val ∈ gmsSingerPermImage X U R :=
        mul_mem (inv_mem (pow_mem ha _)) (pow_mem ha _)
      have h2 : ((a ^ j.val)⁻¹ * a ^ i.val) β = β := by
        rw [Equiv.Perm.mul_apply, hij', GMSAffine.perm_inv_apply]
      have h4 : a ^ i.val = a ^ j.val :=
        inv_mul_eq_one.1 (GMSDichotomy.eq_one_of_mem_gmsSingerPermImage h h3 h1 hβ h2) |>.symm
      have h5 : i.val = j.val :=
        pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, ha7]; exact ZMod.val_lt i)
          (by rw [Set.mem_Iio, ha7]; exact ZMod.val_lt j) h4
      rw [ZMod.val_injective _ h5]
  have hcard : Nat.card (gmsRootConjugates (U ⊔ R) R) ≤ Nat.card (Option (ZMod 7)) := by
    rw [Nat.card_coe_set_eq, (gms_normal_root_partition_and_two_transitivity h h3).2.1,
      Nat.card_eq_fintype_card]
    decide
  exact ⟨Equiv.ofBijective f (hinj.bijective_of_nat_card_le hcard), rfl, fun i => rfl⟩

theorem exists_degreeEight_coords [Finite D] (h : GMSNormalRootData J R X U P 3)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) (β : gmsRootConjugates (U ⊔ R) R)
    (hβ : (β : Subgroup D) ≠ R) (hB : Nat.card (gmsPairStabilizer U R β) = 3) :
    ∃ e : Option (ZMod 7) ≃ gmsRootConjugates (U ⊔ R) R,
      e none = ⟨R, gms_R_mem⟩ ∧ e (some 0) = β ∧
      DegreeEight.shift ∈ (gmsRootConjugateAction (U ⊔ R) R).range.map
        e.symm.permCongrHom.toMonoidHom ∧
      DegreeEight.dbl ∈ (gmsRootConjugateAction (U ⊔ R) R).range.map
        e.symm.permCongrHom.toMonoidHom ∧
      (∀ σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range.map e.symm.permCongrHom.toMonoidHom,
        σ none = none → DegreeEight.IsAffine σ) ∧
      ∃ s ∈ (gmsRootConjugateAction (U ⊔ R) R).range.map e.symm.permCongrHom.toMonoidHom,
        s none = some 0 ∧ s (some 0) = none := by
  classical
  set R₀ : gmsRootConjugates (U ⊔ R) R := ⟨R, gms_R_mem⟩ with hR₀
  obtain ⟨a, ha, ha7, hagen⟩ := exists_gmsSingerPermImage_generator h h3
  obtain ⟨b, hbB, hba⟩ := exists_pairStabilizer_conj_eq_sq h h3 β hβ hB ha ha7
  obtain ⟨e, heinf, hei⟩ := exists_degreeEight_label h h3 ha ha7 hβ
  obtain ⟨hdec, -, -, -, -⟩ := gms_pairStabilizer_structure h h3 β hβ (X := X)
  obtain ⟨-, -, -, -, h2tr, -⟩ := gms_normal_root_partition_and_two_transitivity h h3
  have hTle := GMSDichotomy.gmsSingerPermImage_le h (X := X)
  have hNR : gmsPermStabilizer U R ≤ (gmsRootConjugateAction (U ⊔ R) R).range := inf_le_left
  have hbH : b ∈ gmsPermStabilizer U R := (mem_inf.1 hbB).1
  have haR : a R₀ = R₀ := (GMSDichotomy.mem_gmsPermStabilizer.1 (hTle ha)).2
  have hbR : b R₀ = R₀ := (GMSDichotomy.mem_gmsPermStabilizer.1 hbH).2
  have hbβ : b β = β := by
    have h1 := (mem_inf.1 hbB).2
    rwa [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at h1
  have ha7' : a ^ 7 = 1 := by rw [← ha7]; exact pow_orderOf_eq_one a
  have he0 : e (some 0) = β := by rw [hei]; rfl
  have hb1 : b ≠ 1 := by
    rintro rfl
    have h1 : a * a = a * 1 := by
      rw [mul_one, ← pow_two, ← hba, one_mul, inv_one, mul_one]
    rw [mul_left_cancel h1, orderOf_one] at ha7
    norm_num at ha7
  have hbord : orderOf b = 3 := by
    have h1 := (gmsPairStabilizer U R β).orderOf_dvd_natCard hbB
    rw [hB] at h1
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.1 h2) hb1
    · exact h2
  have hBeq : Subgroup.zpowers b = gmsPairStabilizer U R β :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hbB)
      (by rw [hB, Nat.card_zpowers, hbord])
  have hBgen : ∀ b' ∈ gmsPairStabilizer U R β, ∃ j : ℕ, b ^ j = b' := fun b' hb' => by
    rw [← hBeq] at hb'
    exact mem_powers_iff_mem_zpowers.2 hb'
  set κ := e.symm.permCongrHom with hκ
  have hκapply : ∀ σ z, κ σ z = e.symm (σ (e z)) := fun σ z => rfl
  have hκa : κ a = DegreeEight.shift := by
    refine Equiv.ext fun z => ?_
    rw [hκapply, Equiv.symm_apply_eq]
    cases z with
    | none => rw [DegreeEight.shift_none, heinf, haR]
    | some i =>
      have hv1 : (1 : ZMod 7).val = 1 := rfl
      rw [DegreeEight.shift_some, hei, hei, ← Equiv.Perm.mul_apply, ← pow_succ',
        pow_eq_pow_mod _ ha7', pow_eq_pow_mod (i + 1).val ha7', ZMod.val_add, hv1, Nat.mod_mod]
  have hbapow : ∀ m : ℕ, b * a ^ m * b⁻¹ = a ^ (2 * m) := fun m => by
    rw [← conj_pow, hba, ← pow_mul]
  have hκb : κ b = DegreeEight.dbl := by
    refine Equiv.ext fun z => ?_
    rw [hκapply, Equiv.symm_apply_eq]
    cases z with
    | none => rw [DegreeEight.dbl_none, heinf, hbR]
    | some i =>
      have hbinv : b⁻¹ β = β := by rw [Equiv.Perm.inv_eq_iff_eq, hbβ]
      rw [DegreeEight.dbl_some, hei, hei]
      calc b ((a ^ i.val) β) = (b * a ^ i.val * b⁻¹) β := by
            rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hbinv]
        _ = (a ^ (2 * i).val) β := by
            have hv2 : (2 : ZMod 7).val = 2 := rfl
            rw [hbapow, pow_eq_pow_mod _ ha7', pow_eq_pow_mod (2 * i).val ha7', ZMod.val_mul, hv2,
              Nat.mod_mod]
  refine ⟨e, heinf, he0, ⟨a, hNR (hTle ha), hκa⟩, ⟨b, hNR hbH, hκb⟩, ?_, ?_⟩
  · rintro _ ⟨σ, hσ, rfl⟩ hσinf
    have hσR : σ R₀ = R₀ := by
      have h1 : e.symm (σ (e none)) = none := hσinf
      rw [Equiv.symm_apply_eq, heinf] at h1
      exact h1
    obtain ⟨t, ht, b', hb', rfl⟩ := hdec σ (GMSDichotomy.mem_gmsPermStabilizer.2 ⟨hσ, hσR⟩)
    obtain ⟨m, rfl⟩ := hagen t ht
    obtain ⟨j, rfl⟩ := hBgen b' hb'
    change DegreeEight.IsAffine (κ (a ^ m * b ^ j))
    rw [map_mul, map_pow, map_pow, hκa, hκb]
    exact DegreeEight.isAffine_shift_pow_mul_dbl_pow m j
  · have hβR₀ : β ≠ R₀ := fun h1 => hβ (congrArg Subtype.val h1)
    obtain ⟨σ, hσ, hσ1, hσ2⟩ := h2tr R₀ β β R₀ hβR₀.symm hβR₀
    refine ⟨κ σ, ⟨σ, hσ, rfl⟩, ?_, ?_⟩
    · change e.symm (σ (e none)) = some 0
      rw [heinf, hσ1, Equiv.symm_apply_eq, he0]
    · change e.symm (σ (e (some 0))) = none
      rw [he0, hσ2, Equiv.symm_apply_eq, heinf]

theorem card_natPSL : Nat.card DegreeEight.natPSL = 168 := by
  have hinj : Function.Injective (DegreeEight.projEquiv.symm.permCongrHom.toMonoidHom.comp
      Projectivization.PSLAction.toPermHom :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) →* Equiv.Perm (Option (ZMod 7))) :=
    DegreeEight.projEquiv.symm.permCongrHom.injective.comp
      Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective
  have h1 : Nat.card DegreeEight.natPSL =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have h2 : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) * 2 =
      7 * (7 ^ 2 - 1) :=
    GMSDichotomy.card_PSL_two_mul_two 7 (by norm_num)
  rw [h1]
  rw [show (7 : ℕ) * (7 ^ 2 - 1) = 336 by norm_num] at h2
  omega

theorem gms_normal_root_degree_eight_pair_three [Finite D] (h : GMSNormalRootData J R X U P 3)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) (β : gmsRootConjugates (U ⊔ R) R)
    (hβ : (β : Subgroup D) ≠ R) (hB : Nat.card (gmsPairStabilizer U R β) = 3) :
    (∃ E : Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)),
      E ≤ (gmsRootConjugateAction (U ⊔ R) R).range ∧
      (E.subgroupOf (gmsRootConjugateAction (U ⊔ R) R).range).Normal ∧
      ∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃! a : E,
        (a : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) Q = Z) ∨
    ∃ β' : gmsRootConjugates (U ⊔ R) R ≃ ℙ (ZMod 7) (Fin 2 → ZMod 7),
      ∀ σ : Equiv.Perm (gmsRootConjugates (U ⊔ R) R),
        σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range ↔
          ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7), ∀ Q, β' (σ Q) = g • β' Q := by
  obtain ⟨e, -, -, hshift, hdbl, hstab, hswap⟩ := exists_degreeEight_coords h h3 β hβ hB
  set κ := e.symm.permCongrHom with hκ
  have hκapply : ∀ σ z, κ σ z = e.symm (σ (e z)) := fun σ z => rfl
  have hκsymm : ∀ σ Q, κ.symm σ Q = e (σ (e.symm Q)) := fun σ Q => rfl
  rcases DegreeEight.degreeEight_classification hshift hdbl hstab hswap with
    ⟨E', hE'N, hE'n, hreg⟩ | hpro
  · left
    refine ⟨E'.comap κ.toMonoidHom, fun x hx => ?_, ⟨fun x hx g => ?_⟩, fun Q Z => ?_⟩
    · obtain ⟨y, hy, hyx⟩ := hE'N (mem_comap.1 hx)
      rwa [← κ.injective hyx]
    · rw [mem_subgroupOf, mem_comap] at hx ⊢
      have h1 := hE'n.conj_mem ⟨_, hE'N hx⟩ (mem_subgroupOf.2 hx) ⟨κ g, ⟨g, g.2, rfl⟩⟩
      rw [mem_subgroupOf] at h1
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom, map_mul,
        map_inv] using h1
    · obtain ⟨⟨x', hx'⟩, hx'Q, huniq⟩ := hreg (e.symm Q) (e.symm Z)
      have hx'Q' : x' (e.symm Q) = e.symm Z := hx'Q
      refine ⟨⟨κ.symm x', by
        rw [mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]; exact hx'⟩, ?_, ?_⟩
      · change κ.symm x' Q = Z
        rw [hκsymm, hx'Q', Equiv.apply_symm_apply]
      · rintro ⟨y, hy⟩ hyQ
        have hyQ' : y Q = Z := hyQ
        have h1 := huniq ⟨κ y, hy⟩ (by
          change κ y (e.symm Q) = e.symm Z
          rw [hκapply, Equiv.apply_symm_apply, hyQ'])
        have h2 : κ y = x' := congrArg Subtype.val h1
        apply Subtype.ext
        change y = κ.symm x'
        rw [← h2, MulEquiv.symm_apply_apply]
  · right
    refine ⟨e.symm.trans DegreeEight.projEquiv, fun σ => ?_⟩
    have hBq := (gms_pairStabilizer_structure h h3 β hβ (X := X)).2.2.1
    have hcardN : Nat.card (gmsRootConjugateAction (U ⊔ R) R).range = 168 := by
      rw [card_range_gmsRootConjugateAction h h3, card_gmsPermStabilizer h h3, ← hBq, hB]
      norm_num
    have hcardS : Nat.card (DegreeEight.natPSL.comap κ.toMonoidHom) = 168 := by
      rw [← card_natPSL]
      exact Nat.card_congr (κ.toEquiv.subtypeEquiv fun σ => Iff.rfl)
    have hNeq : (gmsRootConjugateAction (U ⊔ R) R).range =
        DegreeEight.natPSL.comap κ.toMonoidHom :=
      Subgroup.eq_of_le_of_card_ge (fun σ hσ => hpro ⟨σ, hσ, rfl⟩) (by rw [hcardN, hcardS])
    rw [hNeq, mem_comap, MulEquiv.coe_toMonoidHom, DegreeEight.mem_natPSL_iff]
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g, fun Q => ?_⟩
      have h1 := hg (e.symm Q)
      rw [hκapply, Equiv.apply_symm_apply] at h1
      exact h1
    · rintro ⟨g, hg⟩
      refine ⟨g, fun z => ?_⟩
      have h1 := hg (e z)
      rw [hκapply]
      simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using h1

theorem gms_normal_root_degree_eight_completion [Finite D]
    (h : GMSNormalRootData J R X U P 3) (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) :
    (gmsRootConjugates (U ⊔ R) R).ncard = 8 ∧
    (∀ β : gmsRootConjugates (U ⊔ R) R, (β : Subgroup D) ≠ R →
      Nat.card (gmsPairStabilizer U R β) = Nat.card (gmsPermStabilizer U R ⧸
        (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R))) ∧
    (Nat.card (gmsPermStabilizer U R ⧸
        (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) = 1 ∨
      Nat.card (gmsPermStabilizer U R ⧸
        (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) = 3) ∧
    Nat.card (gmsRootConjugateAction (U ⊔ R) R).range = 56 * Nat.card (gmsPermStabilizer U R ⧸
      (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) ∧
    ((∃ E : Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)),
      E ≤ (gmsRootConjugateAction (U ⊔ R) R).range ∧
      (E.subgroupOf (gmsRootConjugateAction (U ⊔ R) R).range).Normal ∧
      (∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃! a : E,
        (a : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) Q = Z) ∧
      (∀ σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range, σ ∈ E ↔ σ = 1 ∨ orderOf σ = 2) ∧
      IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧
      E ⊓ gmsSingerPermImage X U R = ⊥ ∧
      E ⊔ gmsPermStabilizer U R = (gmsRootConjugateAction (U ⊔ R) R).range ∧
      E ⊔ gmsSingerPermImage X U R ≤ (gmsRootConjugateAction (U ⊔ R) R).range ∧
      ((E ⊔ gmsSingerPermImage X U R).subgroupOf
        (gmsRootConjugateAction (U ⊔ R) R).range).Normal ∧
      Nat.card (E ⊔ gmsSingerPermImage X U R : Subgroup _) = 56 ∧
      (∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃ f ∈ E ⊔ gmsSingerPermImage X U R, f Q = Z) ∧
      (∀ f ∈ E ⊔ gmsSingerPermImage X U R, f ≠ 1 → ∀ Q Z : gmsRootConjugates (U ⊔ R) R,
        f Q = Q → f Z = Z → Q = Z) ∧
      (Nat.card (gmsPermStabilizer U R ⧸
          (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) = 1 →
        E ⊔ gmsSingerPermImage X U R = (gmsRootConjugateAction (U ⊔ R) R).range) ∧
      (E.comap (gmsRootConjugateAction (U ⊔ R) R)).Normal ∧
      gmsRootKernel (U ⊔ R) R ≤ E.comap (gmsRootConjugateAction (U ⊔ R) R) ∧
      Nonempty (↥(E.comap (gmsRootConjugateAction (U ⊔ R) R)) ⧸
          (gmsRootKernel (U ⊔ R) R).subgroupOf (E.comap (gmsRootConjugateAction (U ⊔ R) R)) ≃*
        E) ∧
      ((E ⊔ gmsSingerPermImage X U R).comap (gmsRootConjugateAction (U ⊔ R) R)).Normal ∧
      gmsRootKernel (U ⊔ R) R ≤
        (E ⊔ gmsSingerPermImage X U R).comap (gmsRootConjugateAction (U ⊔ R) R) ∧
      Nonempty (↥((E ⊔ gmsSingerPermImage X U R).comap (gmsRootConjugateAction (U ⊔ R) R)) ⧸
          (gmsRootKernel (U ⊔ R) R).subgroupOf
            ((E ⊔ gmsSingerPermImage X U R).comap (gmsRootConjugateAction (U ⊔ R) R)) ≃*
        ↥(E ⊔ gmsSingerPermImage X U R))) ∨
    (Nat.card (gmsPermStabilizer U R ⧸
        (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) = 3 ∧
      ∃ β : gmsRootConjugates (U ⊔ R) R ≃ ℙ (ZMod 7) (Fin 2 → ZMod 7),
        (∀ σ : Equiv.Perm (gmsRootConjugates (U ⊔ R) R),
          σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range ↔
            ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7), ∀ Q, β (σ Q) = g • β Q) ∧
        ⁅(gmsRootConjugateAction (U ⊔ R) R).range, (gmsRootConjugateAction (U ⊔ R) R).range⁆ =
          (gmsRootConjugateAction (U ⊔ R) R).range ∧
        CFSG.Blueprint.LieModel ↥⁅(gmsRootConjugateAction (U ⊔ R) R).range,
          (gmsRootConjugateAction (U ⊔ R) R).range⁆ .PSL 3 2 1 ∧
        CFSG.Blueprint.LieModel (↥(commutator (normalizer ((U ⊔ R : Subgroup D) : Set D))) ⧸
          (gmsRootKernel (U ⊔ R) R).subgroupOf
            (commutator (normalizer ((U ⊔ R : Subgroup D) : Set D)))) .PSL 3 2 1)) := by
  classical
  have hΔ8 : (gmsRootConjugates (U ⊔ R) R).ncard = 8 := by
    rw [(gms_normal_root_partition_and_two_transitivity h h3).2.1]
    norm_num
  obtain ⟨Q₀, hQ₀, hQ₀R⟩ :=
    Set.exists_ne_of_one_lt_ncard (s := gmsRootConjugates (U ⊔ R) R) (by omega) R
  set β₀ : gmsRootConjugates (U ⊔ R) R := ⟨Q₀, hQ₀⟩ with hβ₀
  have hβ₀R : (β₀ : Subgroup D) ≠ R := hQ₀R
  have hBd : ∀ β : gmsRootConjugates (U ⊔ R) R, (β : Subgroup D) ≠ R →
      Nat.card (gmsPairStabilizer U R β) = Nat.card (gmsPermStabilizer U R ⧸
        (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) := fun β hβ =>
    (gms_pairStabilizer_structure h h3 β hβ (X := X)).2.2.1
  have hd : Nat.card (gmsPermStabilizer U R ⧸
        (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) = 1 ∨
      Nat.card (gmsPermStabilizer U R ⧸
        (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) = 3 := by
    have h1 := (gms_pairStabilizer_structure h h3 β₀ hβ₀R (X := X)).2.2.2.2
    rw [hBd β₀ hβ₀R] at h1
    exact (Nat.dvd_prime Nat.prime_three).1 h1
  have hNcard : Nat.card (gmsRootConjugateAction (U ⊔ R) R).range = 56 * Nat.card
      (gmsPermStabilizer U R ⧸ (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) := by
    rw [card_range_gmsRootConjugateAction h h3, card_gmsPermStabilizer h h3, ← mul_assoc]
    norm_num
  have hodd : Odd (Nat.card (gmsPermStabilizer U R)) := by
    rw [card_gmsPermStabilizer h h3]
    rcases hd with h1 | h1 <;> rw [h1] <;> decide
  have hpack : ∀ E : Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)),
      E ≤ (gmsRootConjugateAction (U ⊔ R) R).range →
      (E.subgroupOf (gmsRootConjugateAction (U ⊔ R) R).range).Normal →
      (∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃! a : E,
        (a : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) Q = Z) →
      (Nat.card (gmsPermStabilizer U R ⧸
          (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) = 1 →
        E ⊔ gmsSingerPermImage X U R = (gmsRootConjugateAction (U ⊔ R) R).range) →
      ∃ E : Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)),
      E ≤ (gmsRootConjugateAction (U ⊔ R) R).range ∧
      (E.subgroupOf (gmsRootConjugateAction (U ⊔ R) R).range).Normal ∧
      (∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃! a : E,
        (a : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) Q = Z) ∧
      (∀ σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range, σ ∈ E ↔ σ = 1 ∨ orderOf σ = 2) ∧
      IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧
      E ⊓ gmsSingerPermImage X U R = ⊥ ∧
      E ⊔ gmsPermStabilizer U R = (gmsRootConjugateAction (U ⊔ R) R).range ∧
      E ⊔ gmsSingerPermImage X U R ≤ (gmsRootConjugateAction (U ⊔ R) R).range ∧
      ((E ⊔ gmsSingerPermImage X U R).subgroupOf
        (gmsRootConjugateAction (U ⊔ R) R).range).Normal ∧
      Nat.card (E ⊔ gmsSingerPermImage X U R : Subgroup _) = 56 ∧
      (∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃ f ∈ E ⊔ gmsSingerPermImage X U R, f Q = Z) ∧
      (∀ f ∈ E ⊔ gmsSingerPermImage X U R, f ≠ 1 → ∀ Q Z : gmsRootConjugates (U ⊔ R) R,
        f Q = Q → f Z = Z → Q = Z) ∧
      (Nat.card (gmsPermStabilizer U R ⧸
          (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) = 1 →
        E ⊔ gmsSingerPermImage X U R = (gmsRootConjugateAction (U ⊔ R) R).range) ∧
      (E.comap (gmsRootConjugateAction (U ⊔ R) R)).Normal ∧
      gmsRootKernel (U ⊔ R) R ≤ E.comap (gmsRootConjugateAction (U ⊔ R) R) ∧
      Nonempty (↥(E.comap (gmsRootConjugateAction (U ⊔ R) R)) ⧸
          (gmsRootKernel (U ⊔ R) R).subgroupOf (E.comap (gmsRootConjugateAction (U ⊔ R) R)) ≃*
        E) ∧
      ((E ⊔ gmsSingerPermImage X U R).comap (gmsRootConjugateAction (U ⊔ R) R)).Normal ∧
      gmsRootKernel (U ⊔ R) R ≤
        (E ⊔ gmsSingerPermImage X U R).comap (gmsRootConjugateAction (U ⊔ R) R) ∧
      Nonempty (↥((E ⊔ gmsSingerPermImage X U R).comap (gmsRootConjugateAction (U ⊔ R) R)) ⧸
          (gmsRootKernel (U ⊔ R) R).subgroupOf
            ((E ⊔ gmsSingerPermImage X U R).comap (gmsRootConjugateAction (U ⊔ R) R)) ≃*
        ↥(E ⊔ gmsSingerPermImage X U R)) := by
    intro E hEN hEn hreg hd1
    obtain ⟨hinv, hEel, hEcard, hET, hENR, hFN, hFn, hFcard, hFtrans, hFfrob, hEc1, hEc2, hEc3,
      hFc1, hFc2, hFc3⟩ := gms_regular_normal_package h h3 hodd E hEN hEn hreg
    refine ⟨E, hEN, hEn, hreg, hinv, hEel, by rw [hEcard]; norm_num, hET, hENR, hFN, hFn,
      by rw [hFcard]; norm_num, hFtrans, hFfrob, hd1, hEc1, hEc2, hEc3, hFc1, hFc2, hFc3⟩
  refine ⟨hΔ8, hBd, hd, hNcard, ?_⟩
  rcases hd with hd1 | hd3
  ·
    have hB1 : gmsPairStabilizer U R β₀ = ⊥ := by
      rw [← Subgroup.card_eq_one, hBd β₀ hβ₀R, hd1]
    obtain ⟨-, -, -, -, -, -, E, hEN, hEn, hreg, -, -, -, -, -, hNF, -⟩ :=
      gms_normal_root_trivial_pair_completion h h3 β₀ hβ₀R hB1
    exact Or.inl (hpack E hEN hEn hreg fun _ => hNF)
  ·
    rcases gms_normal_root_degree_eight_pair_three h h3 β₀ hβ₀R (by rw [hBd β₀ hβ₀R, hd3]) with
      ⟨E, hEN, hEn, hreg⟩ | ⟨β, hβ⟩
    · exact Or.inl (hpack E hEN hEn hreg fun h1 => absurd (h1.symm.trans hd3) (by norm_num))
    · obtain ⟨-, -, -, -, -, -, -, -, -, hpsl, -⟩ :=
        gms_normal_root_action_dichotomy_branch_completion h h3
      obtain ⟨-, -, -, -, hperf, hLie1, hLie2⟩ := hpsl 7 Nat.prime_seven (by norm_num) (ZMod 7)
        (ZMod.card 7) _ le_rfl β hβ
      exact Or.inr ⟨hd3, β, hβ, hperf, hLie1, hLie2⟩

end GMS

end CFSG.SeitzReduction.RankOne
