module

public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Semidihedral.CenterAndOrders
public import CFSG.Dihedral.BlueprintDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.Semidihedral.LocalPrimeFailure

open CFSG.Open CFSG.DihedralBlueprint

variable {G : Type} [Group G]

theorem inf_range_eq_map_of_sylow {X : Type*} [Group X] {ell : ℕ} (φ : X →* G)
    (hφ : Function.Injective φ) (P : Sylow ell X) {Q : Subgroup G} (hQ : IsPGroup ell Q)
    (hPQ : (P : Subgroup X).map φ ≤ Q) : Q ⊓ φ.range = (P : Subgroup X).map φ := by
  have heq : Q.comap φ = P :=
    P.is_maximal' (hQ.comap_of_injective φ hφ) (Subgroup.map_le_iff_le_comap.mp hPQ)
  rw [inf_comm, ← Subgroup.map_comap_eq, heq]

theorem exists_sylow_of_isSylowIn [Finite G] {ell : ℕ} {H : Subgroup G} {M : Subgroup H}
    {Q : Subgroup G} (hQ : IsSylowIn ell Q (M.map H.subtype)) :
    ∃ Q₁ : Sylow ell M, ((Q₁ : Subgroup M).map M.subtype).map H.subtype = Q := by
  obtain ⟨hQle, hQp, hmax⟩ := hQ
  let φ : M →* G := H.subtype.comp M.subtype
  have hφ : Function.Injective φ := H.subtype_injective.comp M.subtype_injective
  have hrange : φ.range = M.map H.subtype := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨Q₁, hQ₁⟩ := (hQp.comap_of_injective φ hφ).exists_le_sylow
  refine ⟨Q₁, ?_⟩
  rw [Subgroup.map_map]
  refine hmax _ ?_ (Q₁.isPGroup'.map φ) ?_
  · rw [← hrange]
    exact Subgroup.map_le_range φ _
  · calc Q = (Q.comap φ).map φ := (Subgroup.map_comap_eq_self (hQle.trans hrange.ge)).symm
      _ ≤ (Q₁ : Subgroup M).map φ := Subgroup.map_mono hQ₁

theorem map_subtype_centralizer (H : Subgroup G) (A : Subgroup H) :
    (Subgroup.centralizer (A : Set H)).map H.subtype =
      H ⊓ Subgroup.centralizer ((A.map H.subtype : Subgroup G) : Set G) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx a ha)
  · rintro x ⟨hxH, hx⟩
    refine ⟨⟨x, hxH⟩, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx a ⟨a, ha, rfl⟩)

theorem map_centralizer_eq_inf {C : Subgroup G} (PC : Subgroup C) :
    (Subgroup.centralizer (PC : Set C)).map C.subtype =
      Subgroup.normalizer ((PC.map C.subtype : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ((PC.map C.subtype : Subgroup G) : Set G) ⊓ C := by
  have h := map_subtype_centralizer C PC
  apply le_antisymm
  · rw [h]
    rintro x ⟨hxC, hx⟩
    exact ⟨⟨Subgroup.centralizer_le_normalizer _ hx, hx⟩, hxC⟩
  · rw [h]
    rintro x ⟨⟨-, hx⟩, hxC⟩
    exact ⟨hxC, hx⟩

theorem centralizer_le_pPrimeCore_of_odd {X : Type*} [Group X] [Finite X] {ell : ℕ}
    [Fact ell.Prime] (Q : Sylow ell (CFSG.pPrimeCore 2 X))
    (hodd : Odd (Nat.card (Subgroup.centralizer
      (((Q : Subgroup (CFSG.pPrimeCore 2 X)).map (CFSG.pPrimeCore 2 X).subtype :
        Subgroup X) : Set X)))) :
    Subgroup.centralizer
      (((Q : Subgroup (CFSG.pPrimeCore 2 X)).map (CFSG.pPrimeCore 2 X).subtype :
        Subgroup X) : Set X) ≤ CFSG.pPrimeCore 2 X := by
  let O := CFSG.pPrimeCore 2 X
  let Qh : Subgroup X := (Q : Subgroup O).map O.subtype
  let K := Subgroup.centralizer (Qh : Set X)
  have hfrat : Subgroup.normalizer (Qh : Set X) ⊔ O = ⊤ := Sylow.normalizer_sup_eq_top Q
  have hKn : Subgroup.normalizer (Qh : Set X) ≤ Subgroup.normalizer (K : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      inferInstance
  have hnormal : (O ⊔ K).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hfrat]
    refine sup_le ?_ (le_sup_left.trans Subgroup.le_normalizer)
    refine (le_inf ?_ hKn).trans (Subgroup.inf_normalizer_le_normalizer_sup O K)
    exact le_top.trans_eq (Subgroup.normalizer_eq_top (H := O)).symm
  have hcard : O.relIndex K * Nat.card O = Nat.card (O ⊔ K : Subgroup X) := by
    have h := Subgroup.relIndex_mul_card O (O ⊔ K)
    rwa [inf_of_le_left le_sup_left, Subgroup.relIndex_sup_left] at h
  have hOodd : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))
  have hcop : Nat.Coprime 2 (Nat.card (O ⊔ K : Subgroup X)) := by
    rw [← hcard]
    exact Nat.coprime_two_left.mpr ((hodd.of_dvd_nat (O.relIndex_dvd_card K)).mul hOodd)
  have hle : O ⊔ K ≤ CFSG.pPrimeCore 2 X := le_sSup ⟨hnormal, hcop⟩
  exact le_sup_right.trans hle

theorem inf_centralizer_eq_bot_of_center_le [Finite G] {W A : Subgroup G} {t : G}
    (ht : orderOf t = 2) (hW : IsPGroup 2 W)
    (hcenter : W ⊓ Subgroup.centralizer (W : Set G) ≤ Subgroup.zpowers t)
    (hWA : W ≤ Subgroup.normalizer (A : Set G)) (htA : t ∉ Subgroup.centralizer (A : Set G)) :
    W ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
  have : Group.IsNilpotent W := hW.isNilpotent
  have hAC : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      inferInstance
  have : ((Subgroup.centralizer (A : Set G)).subgroupOf W).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hWA.trans hAC)
  have hM : (Subgroup.centralizer (A : Set G)).subgroupOf W = ⊥ := by
    by_contra hne
    apply Group.IsNilpotent.inf_center_ne_bot_of_normal hne
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxZ⟩
    have hxW : (x : G) ∈ W ⊓ Subgroup.centralizer (W : Set G) := by
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨y, hy⟩)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcenter hxW)
    rw [← zpow_mod_orderOf, ht, Nat.cast_ofNat] at hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero] at hk
      exact Subgroup.mem_bot.mpr (Subtype.ext hk.symm)
    · rw [h1, zpow_one] at hk
      exact absurd (hk ▸ Subgroup.mem_subgroupOf.mp hxA) htA
  rw [inf_comm, ← Subgroup.subgroupOf_map_subtype, hM, Subgroup.map_bot]

theorem odd_card_of_sylow_inf_eq_bot {X : Type*} [Group X] [Finite X] {M K : Subgroup X}
    (hKM : K ≤ M) (hK : (K.subgroupOf M).Normal) (T : Sylow 2 X) (hTM : (T : Subgroup X) ≤ M)
    (hTK : (T : Subgroup X) ⊓ K = ⊥) : Odd (Nat.card K) := by
  obtain ⟨U, hU⟩ := CFSG.Glauberman.sylow_inf_normal (T.subtype hTM) (N := K.subgroupOf M)
  have hUbot : (U : Subgroup (K.subgroupOf M)) = ⊥ := by
    rw [hU, eq_bot_iff]
    intro x hx
    have h : ((x : M) : X) ∈ (T : Subgroup X) ⊓ K := hx
    rw [hTK] at h
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp h)))
  have hcard : Nat.card (K.subgroupOf M) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  rw [← hcard]
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => U.ne_bot_of_dvd_card h hUbot)

theorem commutator_mem_of_factor {H R : Subgroup G} {t : G} (htH : t ∈ H)
    (hRn : H ≤ Subgroup.normalizer (R : Set G))
    (hfac : ∀ x ∈ H, ∃ a ∈ R, ∃ c ∈ Subgroup.centralizer ({t} : Set G), a * c = x) :
    ∀ x ∈ H, x * t * x⁻¹ * t⁻¹ ∈ R := by
  intro x hx
  obtain ⟨a, ha, c, hc, rfl⟩ := hfac x hx
  have hct : c * t * c⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
  have h : a * c * t * (a * c)⁻¹ * t⁻¹ = a * (t * a⁻¹ * t⁻¹) := by
    calc a * c * t * (a * c)⁻¹ * t⁻¹ = a * (c * t * c⁻¹) * a⁻¹ * t⁻¹ := by group
      _ = a * (t * a⁻¹ * t⁻¹) := by rw [hct]; group
  rw [h]
  exact R.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hRn htH) a⁻¹).mp (R.inv_mem ha))

theorem exists_mul_centralizer_of_commutator_mem [Finite G] {K M : Subgroup G} (hMK : M ≤ K)
    (hM : (M.subgroupOf K).Normal) (hodd : Odd (Nat.card M)) {t : G} (htK : t ∈ K)
    (ht : orderOf t = 2) (hcomm : ∀ x ∈ K, x * t * x⁻¹ * t⁻¹ ∈ M) :
    ∀ x ∈ K, ∃ m ∈ M, ∃ c ∈ K ⊓ Subgroup.centralizer ({t} : Set G), m * c = x := by
  intro x hx
  let M' := M.subgroupOf K
  let tK : K := ⟨t, htK⟩
  have hA : IsPGroup 2 (Subgroup.zpowers tK) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact (Subgroup.orderOf_coe tK).symm.trans ht
  have hM' : ¬ 2 ∣ Nat.card M' := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMK).toEquiv]
    exact hodd.not_two_dvd_nat
  have hcent := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 2 M' hM' _ hA
  have htop : Subgroup.centralizer (((Subgroup.zpowers tK).map (QuotientGroup.mk' M') :
      Subgroup (K ⧸ M')) : Set (K ⧸ M')) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective M' q
    rw [MonoidHom.map_zpowers, Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have h1 : QuotientGroup.mk' M' (y * tK * y⁻¹ * tK⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hcomm y y.2)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
      mul_inv_eq_iff_eq_mul] at h1
    exact (Commute.zpow_left h1.symm k).eq
  rw [htop] at hcent
  obtain ⟨c, hc, hceq⟩ := hcent.ge (Subgroup.mem_top (QuotientGroup.mk' M' ⟨x, hx⟩))
  have hcx : c⁻¹ * ⟨x, hx⟩ ∈ M' := QuotientGroup.eq.mp hceq
  have hm : (⟨x, hx⟩ : K) * c⁻¹ ∈ M' := by
    have h := hM.conj_mem _ hcx c
    rwa [mul_inv_cancel_left] at h
  refine ⟨x * (c : G)⁻¹, hm, (c : G), Subgroup.mem_inf.mpr ⟨c.2, ?_⟩,
    inv_mul_cancel_right x (c : G)⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val
    (Subgroup.mem_centralizer_iff.mp hc tK (Subgroup.mem_zpowers tK)).symm

theorem factorization_two_eq_of_odd_factor [Finite G] {K M D : Subgroup G} (hMK : M ≤ K)
    (hDK : D ≤ K) (hM : (M.subgroupOf K).Normal) (hodd : Odd (Nat.card M))
    (hfac : ∀ x ∈ K, ∃ m ∈ M, ∃ c ∈ D, m * c = x) :
    (Nat.card K).factorization 2 = (Nat.card D).factorization 2 := by
  let M' := M.subgroupOf K
  let D' := D.subgroupOf K
  have hsup : M' ⊔ D' = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    obtain ⟨m, hm, c, hc, rfl⟩ := hfac x hx
    exact Subgroup.mul_mem_sup (show (⟨m, hMK hm⟩ : K) ∈ M' from hm)
      (show (⟨c, hDK hc⟩ : K) ∈ D' from hc)
  have h1 : M'.relIndex D' * Nat.card M' = Nat.card K := by
    rw [← Subgroup.relIndex_sup_left, hsup, Subgroup.relIndex_top_right,
      Subgroup.index_mul_card]
  have h2 : M'.relIndex D' ∣ Nat.card D' := M'.relIndex_dvd_card D'
  have hcM : Nat.card M' = Nat.card M := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMK).toEquiv
  have hcD : Nat.card D' = Nat.card D := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv
  rw [hcM] at h1
  rw [hcD] at h2
  have hr : M'.relIndex D' ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  apply le_antisymm
  · rw [← h1, Nat.factorization_mul hr Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero]
    exact (Nat.factorization_le_iff_dvd hr Nat.card_pos.ne').mpr h2 2
  · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_dvd_of_le hDK) 2

theorem factorization_two_pPrimeCore_sup_zpowers_le [Finite G] {H : Subgroup G} {t : G}
    (htH : t ∈ H) (ht : orderOf t = 2) :
    (Nat.card ((CFSG.pPrimeCore 2 H).map H.subtype ⊔ Subgroup.zpowers t :
      Subgroup G)).factorization 2 ≤ 1 := by
  let O := CFSG.pPrimeCore 2 H
  let tH : H := ⟨t, htH⟩
  let T := Subgroup.zpowers tH
  have hmap : (O ⊔ T).map H.subtype = O.map H.subtype ⊔ Subgroup.zpowers t := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  have hcard : Nat.card ((O ⊔ T).map H.subtype) = Nat.card (O ⊔ T : Subgroup H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  have h1 : O.relIndex T * Nat.card O = Nat.card (O ⊔ T : Subgroup H) := by
    have h := Subgroup.relIndex_mul_card O (O ⊔ T)
    rwa [inf_of_le_left le_sup_left, Subgroup.relIndex_sup_left] at h
  have hT : Nat.card T = 2 := by
    rw [Nat.card_zpowers]
    exact (Subgroup.orderOf_coe tH).symm.trans ht
  have h2 : O.relIndex T ∣ 2 := hT ▸ O.relIndex_dvd_card T
  have hOodd : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))
  have hr : O.relIndex T ≠ 0 := fun h0 => by
    rw [h0] at h2
    exact absurd (Nat.eq_zero_of_zero_dvd h2) two_ne_zero
  rw [← hmap, hcard, ← h1, Nat.factorization_mul hr Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hOodd.not_two_dvd_nat, add_zero]
  calc (O.relIndex T).factorization 2 ≤ (2 : ℕ).factorization 2 :=
        (Nat.factorization_le_iff_dvd hr two_ne_zero).mpr h2 2
    _ = 1 := Nat.Prime.factorization_self Nat.prime_two

theorem sylow_center_eq_zpowers {n : ℕ} (hn : 4 ≤ n) {t : G} {K : Subgroup G} {B : Subgroup K}
    (S : Sylow 2 B) (fB : SemidihedralGroup n ≃* S) (hz : (((fB (z n) : B) : K) : G) = t) :
    ((S : Subgroup B).map B.subtype).map K.subtype ⊓
        Subgroup.centralizer ((((S : Subgroup B).map B.subtype).map K.subtype :
          Subgroup G) : Set G) = Subgroup.zpowers t := by
  have hZ : Subgroup.center S = Subgroup.zpowers (fB (z n)) := by
    rw [← Subgroup.map_center_eq fB, CFSG.Semidihedral.center_eq_zpowers n hn,
      MonoidHom.map_zpowers]
    rfl
  have hmem : ∀ x : G, x ∈ ((S : Subgroup B).map B.subtype).map K.subtype ↔
      ∃ s : (S : Subgroup B), (((s : B) : K) : G) = x := by
    intro x
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨_, ⟨_, s.2, rfl⟩, rfl⟩
  apply le_antisymm
  · rintro x ⟨hxS, hxC⟩
    obtain ⟨s, rfl⟩ := (hmem x).mp hxS
    have hs : s ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h := Subgroup.mem_centralizer_iff.mp hxC _ ((hmem _).mpr ⟨y, rfl⟩)
      exact Subtype.ext (Subtype.ext (Subtype.ext h))
    rw [hZ] at hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← hz]
    simp only [SubgroupClass.coe_zpow]
  · rw [Subgroup.zpowers_le]
    refine ⟨(hmem t).mpr ⟨fB (z n), hz⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    obtain ⟨s, rfl⟩ := (hmem y).mp hy
    have hzc : fB (z n) ∈ Subgroup.center S := by
      rw [hZ]
      exact Subgroup.mem_zpowers _
    rw [← hz]
    exact congrArg (fun u : (S : Subgroup B) => (((u : B) : K) : G))
      (Subgroup.mem_center_iff.mp hzc s)

end CFSG.Semidihedral.LocalPrimeFailure
