module

public import CFSG.HardMathSupport.Dickson.BMRows.M11M12
public import CFSG.HardMathSupport.Dickson.BMRows.M11Sylow
public import CFSG.HardMathSupport.Dickson.BMRows.M12Invol
public import CFSG.HardMathSupport.Dickson.BMRows.StronglyEmbedded
public import CFSG.Monster.Tri.GmatF1Type
public import CFSG.Monster.Existence.Census.TwoClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Card

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows.M11

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence CFSG.Monster.Tri
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.Gen11
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven
  CFSG.HardMathSupport.Dickson.BMRows.M12Invol

section Generic

variable {G : Type*} [Group G]

theorem card_centralizer_inf_map (σ : G ≃* G) (a b : G) :
    Nat.card (Subgroup.centralizer ({σ a} : Set G) ⊓ Subgroup.centralizer ({σ b} : Set G) :
      Subgroup G) =
      Nat.card (Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) :
        Subgroup G) := by
  refine (Nat.card_congr (σ.toEquiv.subtypeEquiv fun y => ?_)).symm
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe]
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, σ.injective.eq_iff, σ.injective.eq_iff]

theorem exists_conj_le_of_isMaximalTwoSubgroup [Finite G] {T L R : Subgroup G}
    (hT : IsMaximalTwoSubgroup T L) (hRL : R ≤ L) (hR : IsPGroup 2 R) :
    ∃ m ∈ L, ∀ r ∈ R, m * r * m⁻¹ ∈ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTL, hT2, hTmax⟩ := hT
  have hTl : IsPGroup 2 (T.subgroupOf L) := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm
  obtain ⟨P, hP⟩ := hTl.exists_le_sylow
  have hPT : (P : Subgroup ↥L).map L.subtype = T :=
    hTmax _ (Subgroup.map_subtype_le _) (P.isPGroup'.map _) fun t ht =>
      Subgroup.mem_map.2 ⟨⟨t, hTL ht⟩, hP ht, rfl⟩
  have hRl : IsPGroup 2 (R.subgroupOf L) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRL).symm
  obtain ⟨Q, hQ⟩ := hRl.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq ↥L Q P
  refine ⟨m, m.2, fun r hr => ?_⟩
  have hrQ : (⟨r, hRL hr⟩ : ↥L) ∈ (Q : Subgroup ↥L) := hQ hr
  have hmem : MulAut.conj m ⟨r, hRL hr⟩ ∈ (P : Subgroup ↥L) := by
    rw [← hm, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hrQ
  rw [← hPT]
  exact Subgroup.mem_map.2 ⟨_, hmem, by simp [MulAut.conj_apply]⟩

theorem exists_map_conj_eq [Finite G] {H P Q : Subgroup G} {k : ℕ} (hPH : P ≤ H) (hQH : Q ≤ H)
    (hP : Nat.card P = 2 ^ k) (hQ : Nat.card Q = 2 ^ k) (hk : ¬ 2 ^ (k + 1) ∣ Nat.card H) :
    ∃ m ∈ H, Q.map (MulAut.conj m).toMonoidHom = P := by
  obtain ⟨m, hmH, hm⟩ := exists_conj_le_of_isMaximalTwoSubgroup
    (IsMaximalTwoSubgroup.of_card hPH le_rfl hP hk) hQH (IsPGroup.of_card hQ)
  refine ⟨m, hmH, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    simpa [MulAut.conj_apply] using hm q hq
  · rw [Subgroup.card_map_of_injective (MulAut.conj m).injective, hP, hQ]

end Generic

section TwoA


theorem card_ker_centToCbar : Nat.card centToCbar.ker = 2 := by
  rw [← Subgroup.card_map_of_injective (cent tGmat).subtype_injective, map_ker_centToCbar,
    Nat.card_zpowers, orderOf_tGmat]


theorem card_centralizer_tGmat_inf_le
    (hB : ∀ y : CFSG.Blueprint.NativeSporadic.B, orderOf y = 11 →
      Nat.card (Subgroup.centralizer ({y} : Set CFSG.Blueprint.NativeSporadic.B)) ≤ 1320)
    {x : Gmat} (hx : orderOf x = 11) (hxt : x * tGmat = tGmat * x) :
    Nat.card (Subgroup.centralizer ({tGmat} : Set Gmat) ⊓ Subgroup.centralizer ({x} : Set Gmat) :
      Subgroup Gmat) ≤ 2 * 1320 := by
  have hxC : x ∈ cent tGmat := Subgroup.mem_centralizer_singleton_iff.2 hxt
  set x' : cent tGmat := ⟨x, hxC⟩ with hx'def
  have hcard : Nat.card (Subgroup.centralizer ({tGmat} : Set Gmat) ⊓
      Subgroup.centralizer ({x} : Set Gmat) : Subgroup Gmat) =
      Nat.card (Subgroup.centralizer ({x'} : Set (cent tGmat))) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩,
          Subgroup.mem_centralizer_singleton_iff.2
            (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2))⟩
        invFun := fun y => ⟨y.1.1, Subgroup.mem_inf.2 ⟨y.1.2,
          Subgroup.mem_centralizer_singleton_iff.2
            (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 y.2))⟩⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }
  rw [hcard]
  haveI := CFSG.Monster.B.Pinned.finite_B
  let e : cent tGmat ⧸ centToCbar.ker ≃* CFSG.Blueprint.NativeSporadic.B :=
    (QuotientGroup.quotientKerEquivOfSurjective _ centToCbar_surjective).trans phiB
  have hmk : orderOf (e (QuotientGroup.mk x')) = 11 := by
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    rw [MulEquiv.orderOf_eq]
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, show (11 : ℕ) = orderOf x' by
        rw [hx'def, Subgroup.orderOf_mk, hx], pow_orderOf_eq_one, QuotientGroup.mk_one]
    · intro h
      rw [QuotientGroup.eq_one_iff] at h
      have h2 : x ∈ Subgroup.zpowers tGmat := by
        rw [← map_ker_centToCbar]
        exact ⟨x', h, rfl⟩
      have h3 := orderOf_dvd_of_mem_zpowers h2
      rw [hx, orderOf_tGmat] at h3
      norm_num at h3
  refine (@card_centralizer_le_mul (cent tGmat) CFSG.Blueprint.NativeSporadic.B _ Units.instGroup
    _ _ centToCbar.ker _ e x').trans (Nat.mul_le_mul ?_ (hB _ hmk))
  rw [← card_ker_centToCbar]
  exact Subgroup.card_le_of_le inf_le_left

end TwoA

section TwoB


theorem card_centralizer_xGmat_inf_le {x : Gmat} (hx : orderOf x = 11)
    (hxt : x * xGmat = xGmat * x) :
    Nat.card (Subgroup.centralizer ({xGmat} : Set Gmat) ⊓ Subgroup.centralizer ({x} : Set Gmat) :
      Subgroup Gmat) ≤ 32 * 66 := by
  have hxC : x ∈ cent xGmat := Subgroup.mem_centralizer_singleton_iff.2 hxt
  set x' : cent xGmat := ⟨x, hxC⟩ with hx'def
  have hx' : orderOf x' = 11 := by rw [hx'def, Subgroup.orderOf_mk]; exact hx
  have hcard : Nat.card (Subgroup.centralizer ({xGmat} : Set Gmat) ⊓
      Subgroup.centralizer ({x} : Set Gmat) : Subgroup Gmat) =
      Nat.card (Subgroup.centralizer ({x'} : Set (cent xGmat))) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩,
          Subgroup.mem_centralizer_singleton_iff.2
            (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2))⟩
        invFun := fun y => ⟨y.1.1, Subgroup.mem_inf.2 ⟨y.1.2,
          Subgroup.mem_centralizer_singleton_iff.2
            (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 y.2))⟩⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }
  rw [hcard]
  exact card_centralizer_cent_xGmat_le hx'

end TwoB

section Census


theorem card_centralizer_inf_le_of_involution
    (hB : ∀ y : CFSG.Blueprint.NativeSporadic.B, orderOf y = 11 →
      Nat.card (Subgroup.centralizer ({y} : Set CFSG.Blueprint.NativeSporadic.B)) ≤ 1320)
    {x u : Gmat} (hx : orderOf x = 11) (hu : orderOf u = 2) (hxu : x * u = u * x) :
    Nat.card (Subgroup.centralizer ({x} : Set Gmat) ⊓ Subgroup.centralizer ({u} : Set Gmat) :
      Subgroup Gmat) ≤ 2640 := by
  have key : ∀ {s : Gmat} {c : Gmat}, c * s * c⁻¹ = u →
      Nat.card (Subgroup.centralizer ({x} : Set Gmat) ⊓ Subgroup.centralizer ({u} : Set Gmat) :
        Subgroup Gmat) =
        Nat.card (Subgroup.centralizer ({s} : Set Gmat) ⊓
          Subgroup.centralizer ({MulAut.conj c⁻¹ x} : Set Gmat) : Subgroup Gmat) ∧
        orderOf (MulAut.conj c⁻¹ x) = 11 ∧ MulAut.conj c⁻¹ x * s = s * MulAut.conj c⁻¹ x := by
    intro s c hc
    have hσu : MulAut.conj c⁻¹ u = s := by
      rw [← hc, MulAut.conj_apply]
      group
    refine ⟨?_, by rw [MulEquiv.orderOf_eq]; exact hx, ?_⟩
    · rw [← card_centralizer_inf_map (MulAut.conj c⁻¹) x u, hσu, inf_comm]
    · rw [← hσu, ← map_mul, hxu, map_mul]
  rcases CFSG.Monster.Existence.Census.generated_group_two_involution_classes u hu with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    obtain ⟨h1, h2, h3⟩ := key hc
    rw [h1]
    exact (card_centralizer_xGmat_inf_le h2 h3).trans (by norm_num)
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    obtain ⟨h1, h2, h3⟩ := key hc
    rw [h1]
    exact (card_centralizer_tGmat_inf_le hB h2 h3).trans (by norm_num)

end Census

section L


theorem commute_m12K_zpowers (k : m12K) (y : Subgroup.zpowers (gw gen11W0)) :
    Commute (m12K.subtype k) ((Subgroup.zpowers (gw gen11W0)).subtype y) := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 y.2
  have hk : Commute (k : Gmat) (gw gen11W0) :=
    Subgroup.mem_centralizer_singleton_iff.1 (m12K_le_centralizer k.2)
  change Commute (k : Gmat) (y : Gmat)
  rw [← hn]
  exact hk.zpow_right n

@[expose] noncomputable def m12LHom : m12K × Subgroup.zpowers (gw gen11W0) →* Gmat :=
  m12K.subtype.noncommCoprod (Subgroup.zpowers (gw gen11W0)).subtype commute_m12K_zpowers

theorem m12LHom_apply (k : m12K) (y : Subgroup.zpowers (gw gen11W0)) :
    m12LHom (k, y) = (k : Gmat) * y := rfl

@[expose] noncomputable def m12L : Subgroup Gmat := m12LHom.range

theorem m12K_le_m12L : m12K ≤ m12L := fun k hk =>
  ⟨(⟨k, hk⟩, 1), by rw [m12LHom_apply, OneMemClass.coe_one, mul_one]⟩

theorem m12L_le_centralizer : m12L ≤ Subgroup.centralizer ({gw gen11W0} : Set Gmat) := by
  rintro _ ⟨⟨k, y⟩, rfl⟩
  rw [m12LHom_apply]
  refine Subgroup.mul_mem _ (m12K_le_centralizer k.2) ?_
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 y.2
  rw [← hn, Subgroup.mem_centralizer_singleton_iff]
  exact ((Commute.refl (gw gen11W0)).zpow_left n).eq


theorem eq_one_of_mem_m12K_of_mem_zpowers {y : Gmat} (hyK : y ∈ m12K)
    (hyx : y ∈ Subgroup.zpowers (gw gen11W0)) : y = 1 := by
  have := isSimpleGroup_m12K
  have hN : ((Subgroup.zpowers (gw gen11W0)).subgroupOf m12K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (g : Gmat) * n = n * g := commute_m12K_zpowers g ⟨n, hn⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hc, mul_inv_cancel_right]
    exact hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((Subgroup.zpowers (gw gen11W0)).subgroupOf m12K) with h | h
  · have hmem : (⟨y, hyK⟩ : m12K) ∈ (Subgroup.zpowers (gw gen11W0)).subgroupOf m12K :=
      Subgroup.mem_subgroupOf.2 hyx
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    have hle : m12K ≤ Subgroup.zpowers (gw gen11W0) := Subgroup.subgroupOf_eq_top.1 h
    have hc := Subgroup.card_le_of_le hle
    rw [card_m12K, Nat.card_zpowers, orderOf_x11] at hc
    norm_num at hc

theorem m12LHom_injective : Function.Injective m12LHom := by
  rw [injective_iff_map_eq_one]
  rintro ⟨k, y⟩ h
  rw [m12LHom_apply] at h
  have hk : (k : Gmat) = 1 := eq_one_of_mem_m12K_of_mem_zpowers k.2 (by
    rw [eq_inv_of_mul_eq_one_left h]
    exact Subgroup.inv_mem _ y.2)
  rw [hk, one_mul] at h
  exact Prod.ext (Subtype.ext hk) (Subtype.ext h)

theorem card_m12L : Nat.card m12L = 1045440 := by
  rw [m12L, ← Nat.card_congr (MonoidHom.ofInjective m12LHom_injective).toEquiv, Nat.card_prod,
    card_m12K, Nat.card_zpowers, orderOf_x11]

theorem mem_m12K_of_mem_m12L {u : Gmat} (hu : u ∈ m12L) (hu2 : u * u = 1) : u ∈ m12K := by
  obtain ⟨⟨k, y⟩, rfl⟩ := hu
  have hp : ((k, y) : m12K × Subgroup.zpowers (gw gen11W0)) * (k, y) = 1 :=
    m12LHom_injective (by rw [map_mul, map_one]; exact hu2)
  have hy : y ^ 2 = 1 := by
    rw [pow_two]
    exact congrArg Prod.snd hp
  have hy1 : y = 1 := by
    have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy
    have h2 : orderOf y ∣ 11 := by
      have h := orderOf_dvd_natCard y
      rwa [Nat.card_zpowers, orderOf_x11] at h
    have h3 : orderOf y ∣ Nat.gcd 2 11 := Nat.dvd_gcd h1 h2
    rw [show Nat.gcd 2 11 = 1 by norm_num, Nat.dvd_one] at h3
    exact orderOf_eq_one_iff.1 h3
  rw [m12LHom_apply, hy1, OneMemClass.coe_one, mul_one]
  exact k.2

@[expose] noncomputable def m12LCent (u : m12K) : Subgroup Gmat :=
  ((Subgroup.centralizer ({u} : Set m12K)).prod ⊤).map m12LHom

theorem card_m12LCent (u : m12K) :
    Nat.card (m12LCent u) = Nat.card (Subgroup.centralizer ({u} : Set m12K)) * 11 := by
  rw [m12LCent, Subgroup.card_map_of_injective m12LHom_injective,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_top,
    Nat.card_zpowers, orderOf_x11]

theorem m12LCent_le (u : m12K) :
    m12LCent u ≤ Subgroup.centralizer ({gw gen11W0} : Set Gmat) ⊓
      Subgroup.centralizer ({(u : Gmat)} : Set Gmat) := by
  intro g hg
  obtain ⟨⟨k, y⟩, hp, rfl⟩ := Subgroup.mem_map.1 hg
  have hk : k * u = u * k :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_prod.1 hp).1
  refine Subgroup.mem_inf.2 ⟨m12L_le_centralizer ⟨_, rfl⟩, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff, m12LHom_apply]
  have h1 : (k : Gmat) * u = u * k := congrArg Subtype.val hk
  have h2 : (y : Gmat) * u = u * y := (commute_m12K_zpowers u y).eq.symm
  rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]

theorem exists_two_subgroup_m12K : ∃ S : Subgroup Gmat, S ≤ m12K ∧ Nat.card S = 2 ^ 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 6)
    (by rw [card_m12K]; norm_num : 2 ^ 6 ∣ Nat.card m12K)
  exact ⟨P.map m12K.subtype, Subgroup.map_subtype_le P,
    by rw [Subgroup.card_map_of_injective m12K.subtype_injective, hP]⟩

end L

section Bender


theorem centralizer_inf_le_m12L
    (hB : ∀ y : CFSG.Blueprint.NativeSporadic.B, orderOf y = 11 →
      Nat.card (Subgroup.centralizer ({y} : Set CFSG.Blueprint.NativeSporadic.B)) ≤ 1320)
    {u : Gmat} (huL : u ∈ m12L) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    Subgroup.centralizer ({gw gen11W0} : Set Gmat) ⊓ Subgroup.centralizer ({u} : Set Gmat) ≤
      m12L := by
  obtain ⟨e⟩ := nonempty_m12K_mulEquiv_native
  have huK := mem_m12K_of_mem_m12L huL hu2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  have ho' : orderOf (⟨u, huK⟩ : m12K) = 2 := by rw [Subgroup.orderOf_mk]; exact ho
  have hxu : gw gen11W0 * u = u * gw gen11W0 :=
    (Subgroup.mem_centralizer_singleton_iff.1 (m12L_le_centralizer huL)).symm
  have hle : m12LCent ⟨u, huK⟩ ≤ Subgroup.centralizer ({gw gen11W0} : Set Gmat) ⊓
      Subgroup.centralizer ({u} : Set Gmat) := m12LCent_le ⟨u, huK⟩
  have hdvd := Subgroup.card_dvd_of_le hle
  have hbd := card_centralizer_inf_le_of_involution hB orderOf_x11 ho hxu
  have hpos : 0 < Nat.card (Subgroup.centralizer ({gw gen11W0} : Set Gmat) ⊓
      Subgroup.centralizer ({u} : Set Gmat) : Subgroup Gmat) := Nat.card_pos
  have heq : Nat.card (Subgroup.centralizer ({gw gen11W0} : Set Gmat) ⊓
      Subgroup.centralizer ({u} : Set Gmat) : Subgroup Gmat) ≤ Nat.card (m12LCent ⟨u, huK⟩) := by
    obtain ⟨m, hm⟩ := hdvd
    rw [card_m12LCent] at hm ⊢
    rcases CFSG.Sporadic.Schreier.card_centralizer_involution_of_mulEquiv_M12 e ho' with h | h <;>
      rw [h] at hm ⊢ <;> omega
  rw [← Subgroup.eq_of_le_of_card_ge hle heq]
  exact Subgroup.map_le_range _ _

theorem normalizer_le_m12L
    (hB : ∀ y : CFSG.Blueprint.NativeSporadic.B, orderOf y = 11 →
      Nat.card (Subgroup.centralizer ({y} : Set CFSG.Blueprint.NativeSporadic.B)) ≤ 1320)
    {S : Subgroup Gmat} (hSK : S ≤ m12K) (hS : Nat.card S = 2 ^ 6) :
    ∀ g ∈ Subgroup.centralizer ({gw gen11W0} : Set Gmat),
      g ∈ Subgroup.normalizer (S : Set Gmat) → g ∈ m12L := by
  intro g hgH hgN
  obtain ⟨m, -, hm⟩ := exists_map_conj_eq (hSK.trans m12K_le_centralizer) m11S_le_centralizer hS
    card_m11S not_two_pow_seven_dvd_card_centralizer_x11
  have hconj : ∀ y, y ∈ S ↔ m⁻¹ * y * m ∈ m11S := by
    intro y
    rw [← hm]
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hq
    · intro hq
      exact ⟨_, hq, by simp [MulAut.conj_apply, mul_assoc]⟩
  set z := m * xGmat * m⁻¹ with hz
  have hzS : z ∈ S := (hconj z).2 (by simpa [hz, mul_assoc] using xGmat_mem_m11S)
  have hz1 : z ≠ 1 := fun h => xGmat_ne_one (conj_eq_one_iff.1 h)
  have hz2 : z * z = 1 := by
    rw [hz, conj_mul, xGmat_mul_self, mul_one, mul_inv_cancel]
  have hcen : ∀ y ∈ S, (∀ w ∈ S, y * w = w * y) → y = 1 ∨ y = z := by
    intro y hy hyc
    have hqc : ∀ w ∈ m11S, m⁻¹ * y * m * w = w * (m⁻¹ * y * m) := by
      intro w hw
      have hw' : m * w * m⁻¹ ∈ S := (hconj _).2 (by simpa [mul_assoc] using hw)
      have h := congrArg (fun t => m⁻¹ * t * m) (hyc _ hw')
      simpa [mul_assoc] using h
    rcases m11S_center _ ((hconj y).1 hy) hqc with h | h
    · left
      have h' := congrArg (fun t => m * t * m⁻¹) h
      simpa [mul_assoc] using h'
    · right
      have h' := congrArg (fun t => m * t * m⁻¹) h
      simpa [hz, mul_assoc] using h'
  have hzc : ∀ w ∈ S, z * w = w * z := by
    intro w hw
    have h := congrArg (fun t => m * t * m⁻¹) (xGmat_comm_m11S _ ((hconj w).1 hw))
    simpa [hz, mul_assoc] using h
  have hgz : g * z * g⁻¹ = z := by
    have hmem : g * z * g⁻¹ ∈ S := (Subgroup.mem_set_normalizer_iff.1 hgN z).1 hzS
    have hc : ∀ w ∈ S, g * z * g⁻¹ * w = w * (g * z * g⁻¹) := by
      intro w hw
      have hw' : g⁻¹ * w * g ∈ S :=
        (Subgroup.mem_set_normalizer_iff.1 hgN (g⁻¹ * w * g)).2 (by simpa [mul_assoc] using hw)
      have h := congrArg (fun t => g * t * g⁻¹) (hzc _ hw')
      simpa [mul_assoc] using h
    rcases hcen _ hmem hc with h | h
    · exact absurd (conj_eq_one_iff.1 h) hz1
    · exact h
  exact centralizer_inf_le_m12L hB (m12K_le_m12L (hSK hzS)) hz2 hz1
    (Subgroup.mem_inf.2 ⟨hgH, Subgroup.mem_centralizer_singleton_iff.2
      (mul_inv_eq_iff_eq_mul.1 hgz)⟩)


theorem m12L_eq_centralizer
    (hB : ∀ y : CFSG.Blueprint.NativeSporadic.B, orderOf y = 11 →
      Nat.card (Subgroup.centralizer ({y} : Set CFSG.Blueprint.NativeSporadic.B)) ≤ 1320) :
    m12L = Subgroup.centralizer ({gw gen11W0} : Set Gmat) := by
  obtain ⟨e⟩ := nonempty_m12K_mulEquiv_native
  obtain ⟨a, ha2, haC⟩ := exists_involution_card_centralizer_240_of_mulEquiv e
  obtain ⟨b, hb2, hbC⟩ := exists_involution_card_centralizer_192_of_mulEquiv e
  obtain ⟨S, hSK, hS⟩ := exists_two_subgroup_m12K
  have hinv : ∀ {c : m12K}, orderOf c = 2 → (c : Gmat) * c = 1 := fun hc => by
    rw [← Subgroup.coe_mul, ← pow_two, ← hc, pow_orderOf_eq_one, OneMemClass.coe_one]
  have hne : ∀ {c : m12K}, orderOf c = 2 → (c : Gmat) ≠ 1 := fun hc h => by
    rw [OneMemClass.coe_eq_one] at h
    rw [h, orderOf_one] at hc
    norm_num at hc
  refine eq_of_two_classes m12L_le_centralizer ?_ ?_ (hSK.trans m12K_le_m12L) hS
    not_two_pow_seven_dvd_card_centralizer_x11 (normalizer_le_m12L hB hSK hS)
    (m12K_le_m12L a.2) (m12K_le_m12L b.2) (hinv ha2) (hinv hb2) (hne ha2) (hne hb2) ?_
  · rw [card_m12L]
    exact ⟨522720, by norm_num⟩
  · intro u hu hu2 hu1 g hg hgu
    exact centralizer_inf_le_m12L hB hu hu2 hu1
      (Subgroup.mem_inf.2 ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 hgu⟩)
  · rintro _ ⟨⟨k, y⟩, rfl⟩ h
    rw [m12LHom_apply] at h
    have hya : (y : Gmat) * a = a * y := (commute_m12K_zpowers a y).eq.symm
    have h' : k * a * k⁻¹ = b := by
      apply Subtype.ext
      rw [← h, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev,
        mul_assoc (k : Gmat) y a, hya]
      group
    have hc := card_centralizer_conj_eq k a
    rw [h', haC, hbC] at hc
    norm_num at hc

theorem card_centralizer_x11
    (hB : ∀ y : CFSG.Blueprint.NativeSporadic.B, orderOf y = 11 →
      Nat.card (Subgroup.centralizer ({y} : Set CFSG.Blueprint.NativeSporadic.B)) ≤ 1320) :
    Nat.card (Subgroup.centralizer ({gw gen11W0} : Set Gmat)) = 1045440 := by
  rw [← m12L_eq_centralizer hB, card_m12L]

end Bender

end CFSG.HardMathSupport.Dickson.BMRows.M11
