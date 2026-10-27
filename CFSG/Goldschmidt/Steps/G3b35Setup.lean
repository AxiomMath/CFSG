module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG
public import CFSG.Goldschmidt.Steps.G3bL2
public import CFSG.Walter.JRFacts

public section

namespace CFSG.Goldschmidt.G3b

open CFSG.Open CFSG.Walter CFSG.GorensteinWalter
open scoped MatrixGroups

theorem le_centralizer_sup {G : Type*} [Group G] {H K M : Subgroup G}
    (hH : M ≤ Subgroup.centralizer (H : Set G)) (hK : M ≤ Subgroup.centralizer (K : Set G)) :
    M ≤ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hle : H ⊔ K ≤ Subgroup.centralizer ({g} : Set G) := by
    refine sup_le (fun h hh => ?_) (fun k hk => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hH hg) h hh)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hK hg) k hk)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

section Setup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_mem_center_of_pow {L : Subgroup G} (hZ : Odd (Nat.card (Subgroup.center L)))
    {z : L} (hz : z ∈ Subgroup.center L) {k : ℕ} (hk : z ^ 2 ^ k = 1) : z = 1 := by
  have h1 : orderOf (⟨z, hz⟩ : Subgroup.center L) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk))
  have h2 : orderOf (⟨z, hz⟩ : Subgroup.center L) ∣ Nat.card (Subgroup.center L) :=
    orderOf_dvd_natCard _
  have h3 : orderOf (⟨z, hz⟩ : Subgroup.center L) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2
      (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hZ))) h1
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp h3)

theorem sstar_typeII_facts {L A : Subgroup G} [L.Normal] (hLq : CFSG.Open.IsQuasisimple L)
    (hII : IsGoldTypeII L) (hA : IsSStarIn L A) (hA1 : A ≠ ⊥) :
    A ≤ L ∧ IsMulCommutative A ∧ (∀ x ∈ A, x ^ 2 = 1) ∧
      (∀ P : Subgroup G, P ≤ L → IsPGroup 2 P → A ≤ P → P = A) ∧
      ∀ x ∈ L, ∀ y ∈ L, orderOf x = 2 → orderOf y = 2 → ∃ c ∈ L, c * x * c⁻¹ = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAL, hAab, T, hT, hAT, hcl, -⟩ := hA
  obtain ⟨hTL, hTp, hTmax⟩ := hT
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hLq.2
  have hZodd : Odd (Nat.card (Subgroup.center L)) := hII.1
  set π := QuotientGroup.mk' (Subgroup.center L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπne : ∀ x : L, x ≠ 1 → x ^ 2 = 1 → π x ≠ 1 := by
    intro x hx1 hx2 h
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact hx1 (eq_one_of_mem_center_of_pow hZodd h (k := 1) (by simpa using hx2))
  let TS : Sylow 2 L :=
    { toSubgroup := T.subgroupOf L
      isPGroup' := hTp.comap_subtype
      is_maximal' := fun {Q} hQ hTQ => by
        have hQL : Q.map L.subtype ≤ L := Subgroup.map_subtype_le Q
        have hTQ' : T ≤ Q.map L.subtype := fun x hx =>
          ⟨⟨x, hTL hx⟩, hTQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
        have h := hTmax _ hQL (hQ.map L.subtype) hTQ'
        rw [← h, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
          L.subtype_injective] }
  let TB : Sylow 2 (L ⧸ Subgroup.center L) := TS.mapSurjective hπs
  have hTB : (TB : Subgroup (L ⧸ Subgroup.center L)) = (T.subgroupOf L).map π :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨hTB2, hconjB⟩ : (∀ x ∈ (TB : Subgroup (L ⧸ Subgroup.center L)), x ^ 2 = 1) ∧
      ∀ x y : L ⧸ Subgroup.center L, orderOf x = 2 → orderOf y = 2 → IsConj x y := by
    rcases hII.2 with ⟨p, f, hp, hpodd, hf, -, h8, ⟨e⟩⟩ | hJR
    · have hK := sylow_isKleinFour_of_mulEquiv e hpodd hf h8 TB
      refine ⟨fun x hx => ?_, isConj_of_mulEquiv' e hpodd hf⟩
      have h := @IsKleinFour.mul_self _ _ hK ⟨x, hx⟩
      rw [pow_two]
      exact congrArg Subtype.val h
    ·
      obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
      have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
      obtain ⟨k, hk⟩ := hTp ⟨a, hAT haA⟩
      have : ∃ u : L ⧸ Subgroup.center L, orderOf u = 2 := by
        have hne : π ⟨a, hAL haA⟩ ≠ 1 := by
          intro h
          rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
          apply ha1'
          have := eq_one_of_mem_center_of_pow hZodd h (k := k)
            (Subtype.ext (by simpa using congrArg Subtype.val hk))
          exact congrArg Subtype.val this
        have hp : IsPGroup 2 (Subgroup.zpowers (π ⟨a, hAL haA⟩)) := by
          have hdvd : orderOf (π ⟨a, hAL haA⟩) ∣ 2 ^ k := by
            apply orderOf_dvd_of_pow_eq_one
            rw [← map_pow]
            have : (⟨a, hAL haA⟩ : L) ^ 2 ^ k = 1 :=
              Subtype.ext (by simpa using congrArg Subtype.val hk)
            rw [this, map_one]
          obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
          exact IsPGroup.of_card (n := c) (by rw [Nat.card_zpowers, hc])
        have h2 : 2 ∣ Nat.card (Subgroup.zpowers (π ⟨a, hAL haA⟩)) := by
          rcases hp.card_eq_or_dvd with h | h
          · rw [Nat.card_zpowers, orderOf_eq_one_iff] at h
            exact absurd h hne
          · exact h
        obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers _) 2 h2
        exact ⟨u, by rw [Subgroup.orderOf_coe, hu]⟩
      obtain ⟨u, hu⟩ := this
      have hnonab := hJR.exists_mul_ne_mul hu
      obtain ⟨hel, -⟩ := hJR.sylow_two_of_nonabelian hnonab TB
      exact ⟨fun x hx => elemPow_eq_one_of_isElementaryAbelian (p := 2)
          (A := (TB : Subgroup (L ⧸ Subgroup.center L))) x hx,
        fun x y hx hy => hJR.isConj_of_orderOf_eq_two hx hy⟩
  have hT2 : ∀ x ∈ T, x ^ 2 = 1 := by
    intro x hx
    have hxB : π ⟨x, hTL hx⟩ ∈ (TB : Subgroup (L ⧸ Subgroup.center L)) := by
      rw [hTB]
      exact ⟨⟨x, hTL hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have h := hTB2 _ hxB
    rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    obtain ⟨k, hk⟩ := hTp ⟨x, hx⟩
    have hk' : ((⟨x, hTL hx⟩ : L) ^ 2) ^ 2 ^ k = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      have : (⟨x, hTL hx⟩ : L) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [this, one_pow]
    have := eq_one_of_mem_center_of_pow hZodd h hk'
    simpa using congrArg Subtype.val this
  have hconjL : ∀ x ∈ L, ∀ y ∈ L, orderOf x = 2 → orderOf y = 2 → ∃ c ∈ L, c * x * c⁻¹ = y := by
    intro x hx y hy hx2 hy2
    have hord : ∀ z : L, orderOf (z : G) = 2 → orderOf (π z) = 2 := by
      intro z hz
      have hz2 : z ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, ← hz, pow_orderOf_eq_one,
        Subgroup.coe_one])
      have hz1 : z ≠ 1 := fun h => by rw [h, Subgroup.coe_one, orderOf_one] at hz; omega
      exact orderOf_eq_prime (by rw [← map_pow, hz2, map_one]) (hπne z hz1 hz2)
    obtain ⟨c, hc⟩ := isConj_iff.mp (hconjB _ _ (hord ⟨x, hx⟩ hx2) (hord ⟨y, hy⟩ hy2))
    obtain ⟨c', rfl⟩ := hπs c
    have h1 : π (c' * ⟨x, hx⟩ * c'⁻¹) = π ⟨y, hy⟩ := by rw [map_mul, map_mul, map_inv, hc]
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    set w := (c' * ⟨x, hx⟩ * c'⁻¹)⁻¹ * ⟨y, hy⟩ with hw
    have hwc : ∀ g : L, g * w = w * g := Subgroup.mem_center_iff.mp h1
    have hy' : (⟨y, hy⟩ : L) = c' * ⟨x, hx⟩ * c'⁻¹ * w := by rw [hw]; group
    have hx1 : (⟨x, hx⟩ : L) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← hx2, pow_orderOf_eq_one, Subgroup.coe_one])
    have hy1 : (⟨y, hy⟩ : L) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← hy2, pow_orderOf_eq_one, Subgroup.coe_one])
    have hw2 : w ^ 2 ^ 1 = 1 := by
      have h2 : (c' * ⟨x, hx⟩ * c'⁻¹) ^ 2 = 1 := by
        have hxx : (⟨x, hx⟩ : L) * ⟨x, hx⟩ = 1 := by rw [← pow_two]; exact hx1
        rw [pow_two]
        calc c' * ⟨x, hx⟩ * c'⁻¹ * (c' * ⟨x, hx⟩ * c'⁻¹) = c' * (⟨x, hx⟩ * ⟨x, hx⟩) * c'⁻¹ := by
              group
          _ = 1 := by rw [hxx]; group
      have h3 : (⟨y, hy⟩ : L) ^ 2 = (c' * ⟨x, hx⟩ * c'⁻¹) ^ 2 * w ^ 2 := by
        rw [hy']
        exact Commute.mul_pow (hwc _) 2
      rw [hy1, h2, one_mul] at h3
      rw [pow_one]
      exact h3.symm
    have hw1 : w = 1 := eq_one_of_mem_center_of_pow hZodd h1 hw2
    rw [hw1, mul_one] at hy'
    refine ⟨c', c'.2, ?_⟩
    have := congrArg Subtype.val hy'
    simpa using this.symm
  have hAeq : A = T := by
    refine le_antisymm hAT fun t ht => ?_
    by_cases ht1 : t = 1
    · rw [ht1]
      exact A.one_mem
    obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    obtain ⟨c, hcL, hc⟩ := hconjL a (hAL haA) t (hTL ht)
      (orderOf_eq_prime (hT2 a (hAT haA)) ha1') (orderOf_eq_prime (hT2 t ht) ht1)
    have h := hcl a haA c⁻¹ (L.inv_mem hcL) (by rwa [inv_inv, hc])
    rwa [inv_inv, hc] at h
  subst hAeq
  exact ⟨hAL, hAab, hT2, fun P hPL hPp hAP => hTmax P hPL hPp hAP, hconjL⟩

theorem mem_sup_centralizer_of_isPGroup_two {L A : Subgroup G} [L.Normal]
    (hLq : CFSG.Open.IsQuasisimple L) (hAL : A ≤ L) (hAab : IsMulCommutative A)
    (hA2 : IsPGroup 2 A) (hAmax : ∀ P : Subgroup G, P ≤ L → IsPGroup 2 P → A ≤ P → P = A)
    {w : G} (hw : IsPGroup 2 (Subgroup.zpowers w))
    (hwA : w ∈ Subgroup.centralizer (A : Set G)) :
    w ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := L ⊔ Subgroup.zpowers w with hH
  set P := A ⊔ Subgroup.zpowers w with hP
  have hLH : L ≤ H := le_sup_left
  have hwH : w ∈ H := le_sup_right (a := L) (Subgroup.mem_zpowers w)
  have hPH : P ≤ H := sup_le_sup_right hAL _
  have hwP : w ∈ P := le_sup_right (a := A) (Subgroup.mem_zpowers w)
  have hAP : A ≤ P := le_sup_left
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_mem_centralizer hwA
  have hPp : IsPGroup 2 P := by
    rw [hP, sup_comm]
    exact hw.to_sup_of_normal_right' hA2 hwN
  have hPab : IsMulCommutative P := by
    rw [← Subgroup.le_centralizer_iff_isMulCommutative]
    have hwA' : Subgroup.zpowers w ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.zpowers_le.mpr hwA
    have hzz : Subgroup.zpowers w ≤ Subgroup.centralizer (Subgroup.zpowers w : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
    apply le_centralizer_sup
    · exact sup_le (Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab) hwA'
    · exact sup_le (Subgroup.le_centralizer_iff.mp hwA') hzz
  let PS : Sylow 2 H :=
    { toSubgroup := P.subgroupOf H
      isPGroup' := hPp.comap_subtype
      is_maximal' := fun {Q} hQ hPQ => by
        apply le_antisymm _ hPQ
        intro q hq
        rw [Subgroup.mem_subgroupOf]
        set Qg := Q.map H.subtype with hQg
        have hPQg : P ≤ Qg := fun x hx => ⟨⟨x, hPH hx⟩, hPQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
        have hQgp : IsPGroup 2 Qg := hQ.map H.subtype
        obtain ⟨l, hl, c, hc, hlc⟩ := Subgroup.mem_sup_of_normal_left.mp q.2
        have hcQ : c ∈ Qg := hPQg ((Subgroup.zpowers_le.mpr hwP) hc)
        have hqQ : (q : G) ∈ Qg := ⟨q, hq, rfl⟩
        have hlQ : l ∈ Qg := by
          have : l = (q : G) * c⁻¹ := by rw [← hlc]; group
          rw [this]
          exact Qg.mul_mem hqQ (Qg.inv_mem hcQ)
        have hLQ : Qg ⊓ L = A := hAmax _ inf_le_right (hQgp.to_inf_left)
          (le_inf (hAP.trans hPQg) hAL)
        have hlA : l ∈ A := hLQ ▸ ⟨hlQ, hl⟩
        rw [← hlc]
        exact P.mul_mem (hAP hlA) ((Subgroup.zpowers_le.mpr hwP) hc) }
  have hPS : (PS : Subgroup H) = P.subgroupOf H := rfl
  have hHab : HasAbelianSylowTwo H := by
    intro Q
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H PS Q
    have hPab' : IsMulCommutative (PS : Subgroup H) := by
      rw [hPS]
      exact Subgroup.comap_injective_isMulCommutative P H.subtype_injective
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact Subgroup.map_isMulCommutative _ _
  have hLnt : Nontrivial L := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : IsSimpleGroup (L ⧸ Subgroup.center L) := hLq.2
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (L ⧸ Subgroup.center L)
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    exact hxy (by rw [Subsingleton.elim x' y'])
  have hLq' : GorensteinWalter.IsQuasisimple L := ⟨hLnt, hLq.1, hLq.2⟩
  set K := L.subgroupOf H with hK
  have hKq : GorensteinWalter.IsQuasisimple K :=
    isQuasisimple_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hLH).symm hLq'
  have hKn : K.Normal := Subgroup.normal_subgroupOf
  have hSK : (PS : Subgroup H) ≤ Subgroup.normalizer (K : Set H) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hKn]
    exact le_top
  obtain ⟨k, hkK, hk⟩ := exists_inner_of_isQuasisimple hHab K hKq PS hSK ⟨w, hwH⟩
    (by rw [hPS, Subgroup.mem_subgroupOf]; exact hwP)
  have hkL : (k : G) ∈ L := Subgroup.mem_subgroupOf.mp hkK
  have hc : (k : G)⁻¹ * w ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := congrArg Subtype.val (hk ⟨x, hLH hx⟩ (Subgroup.mem_subgroupOf.mpr hx))
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at h
    calc x * ((k : G)⁻¹ * w) = (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * w := by group
      _ = (k : G)⁻¹ * (w * x * w⁻¹) * w := by rw [h]
      _ = (k : G)⁻¹ * w * x := by group
  have : w = (k : G) * ((k : G)⁻¹ * w) := by group
  rw [this]
  exact Subgroup.mul_mem _ (le_sup_left (a := L) hkL) (le_sup_right (a := L) hc)

end Setup

end CFSG.Goldschmidt.G3b
