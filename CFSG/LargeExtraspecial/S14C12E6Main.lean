module

public import CFSG.LargeExtraspecial.S14C12E6Stmt
public import CFSG.LargeExtraspecial.S14C12E6Center
public import CFSG.Monster.B.E6.StdF4FiberCount
public import CFSG.LieType.Chevalley.TwistedE6FieldTwoCyclicKernel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.C2E6Overlap (K barHom)
open CFSG.LieType.Chevalley.C2E6Std (stdGroup stdUnipotent0 nativeParabolic firstJ
  nativeParabolic_le_stdGroup card_stdUnipotent0 barHom_surjective)
open CFSG.Monster.B.E6.StdF4 (rootInv centralizer_rootInv card_nativeParabolic_firstJ)

theorem card_centralizer_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    Nat.card (centralizer ({e x} : Set H)) = Nat.card (centralizer ({x} : Set G)) := by
  refine (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun y => ?_)).symm
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe,
    MulEquiv.coe_toEquiv, ← map_mul, ← map_mul, e.injective.eq_iff]

theorem mem_sylow_centralizer {G : Type*} [Group G] [Finite G] {x : G} (hx : orderOf x = 2)
    (T : Sylow 2 (centralizer ({x} : Set G))) :
    (⟨x, mem_centralizer_singleton_iff.2 rfl⟩ : centralizer ({x} : Set G)) ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set xc : centralizer ({x} : Set G) := ⟨x, mem_centralizer_singleton_iff.2 rfl⟩
  have hxc : ∀ g : centralizer ({x} : Set G), g * xc = xc * g := fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
  have hN : (zpowers xc).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    rw [(Commute.zpow_right (hxc g) k).eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers xc) k⟩
  have hord : orderOf xc = 2 := by
    rw [← hx, ← orderOf_injective (centralizer ({x} : Set G)).subtype Subtype.val_injective xc]
    rfl
  have hp : IsPGroup 2 (zpowers xc) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hord, pow_one])
  exact hp.le_sylow_of_normal T (mem_zpowers xc)

theorem card_centralizer_stdGroup
    {x : stdGroup} (hx : orderOf x = 2)
    (hdvd : 2 ^ 36 ∣ Nat.card (centralizer ({x} : Set stdGroup))) :
    Nat.card (centralizer ({x} : Set stdGroup)) = 2 ^ 36 * 3 ^ 6 * 5 * 7 * 11 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have hUp : IsPGroup 2 (stdUnipotent0.subgroupOf stdGroup) :=
    isPGroup_graphFixedPosUnipotent_subgroupOf (t := TwistTag.E6) (σ := barHom) 2
  have hUi : ¬2 ∣ (stdUnipotent0.subgroupOf stdGroup).index :=
    not_dvd_index_graphFixedPosUnipotent (t := TwistTag.E6) 2 barHom_surjective
  set P : Sylow 2 stdGroup := hUp.toSylow hUi with hPdef
  have hP : (P : Subgroup stdGroup) = stdUnipotent0.subgroupOf stdGroup := IsPGroup.toSylow_coe _ _
  have hPcard : Nat.card P = 2 ^ 36 := by
    rw [hP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show stdUnipotent0 ≤ stdGroup from
      graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K barHom)).toEquiv,
      card_stdUnipotent0]
  obtain ⟨T⟩ : Nonempty (Sylow 2 (centralizer ({x} : Set stdGroup))) := inferInstance
  have hT36 : 2 ^ 36 ∣ Nat.card T := T.pow_dvd_card_of_pow_dvd_card hdvd
  have hT'p : IsPGroup 2 ((T : Subgroup _).map (centralizer ({x} : Set stdGroup)).subtype) :=
    T.isPGroup'.map _
  obtain ⟨Q, hQ⟩ := hT'p.exists_le_sylow
  have hQcard : Nat.card Q = 2 ^ 36 := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity P, hPcard]
  have hTQ : (T : Subgroup _).map (centralizer ({x} : Set stdGroup)).subtype = Q :=
    Subgroup.eq_of_le_of_card_ge hQ (by
      rw [hQcard, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      exact Nat.le_of_dvd Nat.card_pos hT36)
  have hxQ : x ∈ (Q : Subgroup stdGroup) := by
    rw [← hTQ]
    exact Subgroup.mem_map.2 ⟨_, mem_sylow_centralizer hx T, rfl⟩
  have hxcomm : ∀ y ∈ (Q : Subgroup stdGroup), x * y = y * x := by
    intro y hy
    rw [← hTQ] at hy
    obtain ⟨y', -, rfl⟩ := Subgroup.mem_map.1 hy
    exact (mem_centralizer_singleton_iff.1 y'.2).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq stdGroup Q P
  have hconj : ∀ (h : stdGroup) (R : Sylow 2 stdGroup), ∀ y ∈ (R : Subgroup stdGroup),
      h * y * h⁻¹ ∈ ((h • R : Sylow 2 stdGroup) : Subgroup stdGroup) := fun h R y hy => by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj h) _ hy
  have hg' : g⁻¹ • P = Q := by rw [← hg, inv_smul_smul]
  set y := g * x * g⁻¹ with hydef
  have hyP : y ∈ (P : Subgroup stdGroup) := hg ▸ hconj g Q x hxQ
  have hycomm : ∀ u ∈ (P : Subgroup stdGroup), y * u = u * y := by
    intro u hu
    have h1 := hxcomm _ (hg' ▸ hconj g⁻¹ P u hu)
    calc y * u = g * (x * (g⁻¹ * u * g⁻¹⁻¹)) * g⁻¹ := by rw [hydef]; group
      _ = g * ((g⁻¹ * u * g⁻¹⁻¹) * x) * g⁻¹ := by rw [h1]
      _ = u * y := by rw [hydef]; group
  have hyU : (y : ModGL Tag.E6 K) ∈ stdUnipotent0 := by
    have h := hyP
    rw [hP, Subgroup.mem_subgroupOf] at h
    exact h
  have hyc : ∀ v ∈ stdUnipotent0, (y : ModGL Tag.E6 K) * v = v * y := by
    intro v hv
    have hvG : v ∈ stdGroup := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K barHom hv
    have hvP : (⟨v, hvG⟩ : stdGroup) ∈ (P : Subgroup stdGroup) := by
      rw [hP, Subgroup.mem_subgroupOf]
      exact hv
    exact congrArg Subtype.val (hycomm _ hvP)
  have hyt : y = rootInv := by
    rcases TwoE6.eq_one_or_eq_pinnedX_theta_of_commute hyU hyc with h1 | ht
    · exfalso
      have hy1 : y = 1 := Subtype.ext h1
      rw [hydef, mul_inv_eq_one, mul_eq_left] at hy1
      rw [hy1, orderOf_one] at hx
      exact absurd hx (by norm_num)
    · exact Subtype.ext ht
  rw [← card_centralizer_mulEquiv (MulAut.conj g) x, MulAut.conj_apply, ← hydef, hyt,
    centralizer_rootInv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (nativeParabolic_le_stdGroup firstJ)).toEquiv, card_nativeParabolic_firstJ]
  norm_num

theorem twoE6TwoCentralInput_holds :
    TwoE6TwoCentralInput := by
  intro X _ _ hX z hz hdvd
  obtain ⟨L, _, _, σ, hL, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hX
  obtain ⟨e'⟩ := nonempty_mulEquiv_stdGroup_of_card_eq_four (by rw [hL]; norm_num) σ.toRingHom
    fun c => by simpa using hσ c
  rw [← card_centralizer_mulEquiv (e.trans e') z] at hdvd ⊢
  exact card_centralizer_stdGroup (by rw [MulEquiv.orderOf_eq]; exact hz) hdvd

theorem claim14_12U_of_reifartSmith
    (hRS : ReifartSmithU62Input) :
    Claim14_12U :=
  claim14_12U_of' hRS twoE6TwoCentralInput_holds

end CFSG.LargeExtraspecial.S14
