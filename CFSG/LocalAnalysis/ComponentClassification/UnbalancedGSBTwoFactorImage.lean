module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup
open scoped commutatorElement

theorem hom_eq_one_of_odd_range {R U : Type*} [Group R] [Group U] [Finite U]
    (hR : closure {r : R | ∃ k : ℕ, orderOf r = 2 ^ k} = ⊤) (f : R →* U)
    (hodd : Odd (Nat.card f.range)) : f = 1 := by
  have hle : closure {r : R | ∃ k : ℕ, orderOf r = 2 ^ k} ≤ f.ker := by
    rw [closure_le]
    rintro r ⟨k, hk⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have h1 : orderOf (f r) ∣ 2 ^ k := hk ▸ orderOf_map_dvd f r
    have h2 : orderOf (f r) ∣ Nat.card f.range := f.range.orderOf_dvd_natCard ⟨r, rfl⟩
    have h3 : Nat.Coprime (2 ^ k) (Nat.card f.range) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h3 h1 h2)
  rw [hR] at hle
  ext r
  exact MonoidHom.mem_ker.mp (hle (mem_top r))

theorem index_ne_two_of_perfect {G : Type*} [Group G] (hG : Group.IsPerfect G)
    (H : Subgroup G) : H.index ≠ 2 := by
  intro h2
  have : H.Normal := normal_of_index_eq_two h2
  have hcomm : ∀ a b : G ⧸ H, a * b = b * a := by
    have hcard : Nat.card (G ⧸ H) = 2 := by rw [← index_eq_card, h2]
    have : IsCyclic (G ⧸ H) := isCyclic_of_prime_card (p := 2) hcard
    exact isMulCommutative_iff.mp inferInstance
  have hle : commutator G ≤ H := by
    rw [_root_.commutator_def, commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  rw [Group.isPerfect_def.mp hG, top_le_iff] at hle
  rw [hle, index_top] at h2
  exact absurd h2 (by norm_num)

theorem commutator_range_eq_of_perfect {G H : Type*} [Group G] [Group H] (hG : Group.IsPerfect G)
    (f : G →* H) : ⁅f.range, f.range⁆ = f.range := by
  rw [MonoidHom.range_eq_map, ← map_commutator, ← _root_.commutator_def,
    Group.isPerfect_def.mp hG]

theorem isPerfect_of_commutator_eq {G : Type*} [Group G] {K : Subgroup G} (hK : ⁅K, K⁆ = K) :
    Group.IsPerfect K := by
  rw [Group.isPerfect_def, _root_.commutator_def]
  apply map_injective K.subtype_injective
  rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype, hK]

theorem commutatorElement_mul_left_of_mem_center {G : Type*} [Group G] {x : G}
    (hx : x ∈ center G) (y b : G) : ⁅x * y, b⁆ = ⁅y, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  have h := mem_center_iff.mp hx (y * b * y⁻¹)
  calc x * y * b * (y⁻¹ * x⁻¹) * b⁻¹ = x * (y * b * y⁻¹) * x⁻¹ * b⁻¹ := by group
    _ = (y * b * y⁻¹) * x * x⁻¹ * b⁻¹ := by rw [← h]
    _ = y * b * y⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_right_of_mem_center {G : Type*} [Group G] {x : G}
    (hx : x ∈ center G) (a y : G) : ⁅a, x * y⁆ = ⁅a, y⁆ := by
  rw [← commutatorElement_inv, commutatorElement_mul_left_of_mem_center hx,
    commutatorElement_inv]

theorem mem_zpowers_iff_eq_one_or_eq {G : Type*} [Group G] {g x : G} (hg : orderOf g = 2) :
    x ∈ zpowers g ↔ x = 1 ∨ x = g := by
  rw [mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    rw [← zpow_mod_orderOf, hg]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [Nat.cast_ofNat, h, zpow_zero]
    · right
      rw [Nat.cast_ofNat, h, zpow_one]
  · rintro (h | h)
    · rw [h]
      exact ⟨0, zpow_zero g⟩
    · rw [h]
      exact ⟨1, zpow_one g⟩

section TwoFactor

variable (A : Type*) [Group A]

@[expose] def centerDiagonal : Subgroup (A × A) where
  carrier := {x | x.1 ∈ center A ∧ x.1 = x.2}
  mul_mem' := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨ha, hab⟩ ⟨hc, hcd⟩
    exact ⟨mul_mem ha hc, by simp only [Prod.mk_mul_mk] at *; rw [hab, hcd]⟩
  one_mem' := ⟨one_mem _, rfl⟩
  inv_mem' := by
    rintro ⟨a, b⟩ ⟨ha, hab⟩
    exact ⟨inv_mem ha, by simp only [Prod.inv_mk] at *; rw [hab]⟩

variable {A}

theorem mem_centerDiagonal {x : A × A} : x ∈ centerDiagonal A ↔ x.1 ∈ center A ∧ x.1 = x.2 :=
  Iff.rfl

variable (A)

theorem centerDiagonal_le_center : centerDiagonal A ≤ center (A × A) := by
  rintro ⟨a, b⟩ ⟨ha, hab⟩
  simp only at ha hab
  subst hab
  rw [mem_center_iff]
  rintro ⟨c, d⟩
  ext
  · exact mem_center_iff.mp ha c
  · exact mem_center_iff.mp ha d

instance centerDiagonal_normal : (centerDiagonal A).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hc := mem_center_iff.mp (centerDiagonal_le_center A hn) g
  rw [hc, mul_inv_cancel_right]
  exact hn

@[expose] def twoFactorProjection :
    (A × A) ⧸ centerDiagonal A →* (A ⧸ center A) × (A ⧸ center A) :=
  QuotientGroup.lift _
    (MonoidHom.prodMap (QuotientGroup.mk' (center A)) (QuotientGroup.mk' (center A))) (by
      rintro ⟨a, b⟩ ⟨ha, hab⟩
      simp only at ha hab
      subst hab
      rw [MonoidHom.mem_ker]
      change ((a : A ⧸ center A), (a : A ⧸ center A)) = 1
      rw [Prod.mk_eq_one, QuotientGroup.eq_one_iff]
      exact ⟨ha, ha⟩)

variable {A}

theorem twoFactorProjection_mk (x y : A) :
    twoFactorProjection A ((x, y) : (A × A) ⧸ centerDiagonal A) =
      ((x : A ⧸ center A), (y : A ⧸ center A)) :=
  rfl

theorem twoFactorProjection_surjective : Function.Surjective (twoFactorProjection A) := by
  rintro ⟨s, t⟩
  induction s using QuotientGroup.induction_on with | H x => ?_
  induction t using QuotientGroup.induction_on with | H y => ?_
  exact ⟨((x, y) : (A × A) ⧸ centerDiagonal A), rfl⟩

theorem mk_eq_one_iff_centerDiagonal (x y : A) :
    ((x, y) : (A × A) ⧸ centerDiagonal A) = 1 ↔ x ∈ center A ∧ x = y :=
  QuotientGroup.eq_one_iff _

section Involution

variable {z : A}

theorem mem_center_iff_eq_one_or_eq (hZ : center A = zpowers z) (hz : orderOf z = 2) {w : A} :
    w ∈ center A ↔ w = 1 ∨ w = z := by
  rw [hZ, mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    rw [← zpow_mod_orderOf, hz]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [Nat.cast_ofNat, h, zpow_zero]
    · right
      rw [Nat.cast_ofNat, h, zpow_one]
  · rintro (h | h)
    · rw [h]
      exact ⟨0, zpow_zero z⟩
    · rw [h]
      exact ⟨1, zpow_one z⟩

theorem inv_eq_self_of_orderOf_two (hz : orderOf z = 2) : z⁻¹ = z := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hz, pow_orderOf_eq_one]

theorem centerDiagonal_eq_zpowers (hZ : center A = zpowers z) (hz : orderOf z = 2) :
    centerDiagonal A = zpowers (z, z) := by
  ext ⟨a, b⟩
  rw [mem_centerDiagonal, mem_zpowers_iff]
  simp only
  constructor
  · rintro ⟨ha, rfl⟩
    rcases (mem_center_iff_eq_one_or_eq hZ hz).mp ha with h | h
    · exact ⟨0, by rw [h, zpow_zero]; rfl⟩
    · exact ⟨1, by rw [h, zpow_one]⟩
  · rintro ⟨k, hk⟩
    have h1 : z ^ k = a := congrArg Prod.fst hk
    have h2 : z ^ k = b := congrArg Prod.snd hk
    refine ⟨?_, h1.symm.trans h2⟩
    rw [← h1, hZ]
    exact zpow_mem (mem_zpowers z) k

theorem mk_one_z_eq (hZ : center A = zpowers z) (hz : orderOf z = 2) :
    (((1, z) : A × A) : (A × A) ⧸ centerDiagonal A) =
      (((z, 1) : A × A) : (A × A) ⧸ centerDiagonal A) := by
  rw [QuotientGroup.eq, mem_centerDiagonal]
  simp only [Prod.inv_mk, Prod.mk_mul_mk, inv_one, one_mul, mul_one]
  exact ⟨hZ ▸ mem_zpowers z, (inv_eq_self_of_orderOf_two hz).symm⟩

theorem ker_twoFactorProjection (hZ : center A = zpowers z) (hz : orderOf z = 2) :
    (twoFactorProjection A).ker = zpowers (((z, 1) : A × A) : (A × A) ⧸ centerDiagonal A) := by
  apply le_antisymm
  · intro q hq
    induction q using QuotientGroup.induction_on with | H xy => ?_
    obtain ⟨x, y⟩ := xy
    rw [MonoidHom.mem_ker, twoFactorProjection_mk, Prod.mk_eq_one, QuotientGroup.eq_one_iff,
      QuotientGroup.eq_one_iff] at hq
    rw [mem_zpowers_iff]
    rcases (mem_center_iff_eq_one_or_eq hZ hz).mp hq.1 with hx | hx <;>
    rcases (mem_center_iff_eq_one_or_eq hZ hz).mp hq.2 with hy | hy <;> rw [hx, hy]
    · exact ⟨0, by rw [zpow_zero]; rfl⟩
    · exact ⟨1, by rw [zpow_one, mk_one_z_eq hZ hz]⟩
    · exact ⟨1, zpow_one _⟩
    · refine ⟨0, ?_⟩
      rw [zpow_zero, eq_comm, mk_eq_one_iff_centerDiagonal]
      exact ⟨hZ ▸ mem_zpowers z, rfl⟩
  · rw [zpowers_le, MonoidHom.mem_ker, twoFactorProjection_mk, Prod.mk_eq_one,
      QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff]
    exact ⟨hZ ▸ mem_zpowers z, one_mem _⟩

theorem orderOf_twoFactorCenter (hz : orderOf z = 2) :
    orderOf (((z, 1) : A × A) : (A × A) ⧸ centerDiagonal A) = 2 := by
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, Prod.pow_mk, one_pow, ← hz, pow_orderOf_eq_one]
    rfl
  · intro h
    rw [mk_eq_one_iff_centerDiagonal] at h
    rw [h.2, orderOf_one] at hz
    exact absurd hz (by norm_num)

theorem twoFactorCenter_mem_center (hZ : center A = zpowers z) :
    (((z, 1) : A × A) : (A × A) ⧸ centerDiagonal A) ∈ center ((A × A) ⧸ centerDiagonal A) := by
  rw [mem_center_iff]
  intro g
  induction g using QuotientGroup.induction_on with | H xy => ?_
  obtain ⟨x, y⟩ := xy
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  ext
  · exact mem_center_iff.mp (hZ ▸ mem_zpowers z) x
  · simp

theorem comap_twoFactorProjection_left (hZ : center A = zpowers z) (hz : orderOf z = 2) :
    ((⊤ : Subgroup (A ⧸ center A)).prod ⊥).comap (twoFactorProjection A) =
      ((⊤ : Subgroup A).prod ⊥).map (QuotientGroup.mk' (centerDiagonal A)) := by
  apply le_antisymm
  · intro q hq
    induction q using QuotientGroup.induction_on with | H xy => ?_
    obtain ⟨x, y⟩ := xy
    rw [mem_comap, twoFactorProjection_mk, mem_prod] at hq
    have hy : y ∈ center A := (QuotientGroup.eq_one_iff y).mp (mem_bot.mp hq.2)
    rcases (mem_center_iff_eq_one_or_eq hZ hz).mp hy with h | h
    · exact ⟨(x, y), mem_prod.mpr ⟨mem_top x, mem_bot.mpr h⟩, rfl⟩
    · refine ⟨(x * z, 1), mem_prod.mpr ⟨mem_top _, one_mem _⟩, ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq, mem_centerDiagonal, h]
      simp only [Prod.inv_mk, Prod.mk_mul_mk, inv_one, one_mul, mul_inv_rev, inv_mul_cancel_right]
      exact ⟨inv_mem (hZ ▸ mem_zpowers z), inv_eq_self_of_orderOf_two hz⟩
  · rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
    rw [SetLike.mem_coe, mem_prod] at hxy
    have hy : y = 1 := mem_bot.mp hxy.2
    rw [mem_comap, QuotientGroup.mk'_apply, twoFactorProjection_mk, mem_prod]
    refine ⟨mem_top _, ?_⟩
    show (y : A ⧸ center A) ∈ ⊥
    rw [hy, QuotientGroup.mk_one]
    exact one_mem _

theorem comap_twoFactorProjection_right (hZ : center A = zpowers z) (hz : orderOf z = 2) :
    ((⊥ : Subgroup (A ⧸ center A)).prod ⊤).comap (twoFactorProjection A) =
      ((⊥ : Subgroup A).prod ⊤).map (QuotientGroup.mk' (centerDiagonal A)) := by
  apply le_antisymm
  · intro q hq
    induction q using QuotientGroup.induction_on with | H xy => ?_
    obtain ⟨x, y⟩ := xy
    rw [mem_comap, twoFactorProjection_mk, mem_prod] at hq
    have hx : x ∈ center A := (QuotientGroup.eq_one_iff x).mp (mem_bot.mp hq.1)
    rcases (mem_center_iff_eq_one_or_eq hZ hz).mp hx with h | h
    · exact ⟨(x, y), mem_prod.mpr ⟨mem_bot.mpr h, mem_top y⟩, rfl⟩
    · refine ⟨(1, z * y), mem_prod.mpr ⟨one_mem _, mem_top _⟩, ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq, mem_centerDiagonal, h]
      simp only [Prod.inv_mk, Prod.mk_mul_mk, inv_one, one_mul, mul_inv_rev]
      refine ⟨hZ ▸ mem_zpowers z, ?_⟩
      rw [mul_assoc, show z⁻¹ * y = y * z⁻¹ from
          (mem_center_iff.mp (inv_mem (hZ ▸ mem_zpowers z : z ∈ center A)) y).symm,
        inv_mul_cancel_left, inv_eq_self_of_orderOf_two hz]
  · rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
    rw [SetLike.mem_coe, mem_prod] at hxy
    have hx : x = 1 := mem_bot.mp hxy.1
    rw [mem_comap, QuotientGroup.mk'_apply, twoFactorProjection_mk, mem_prod]
    refine ⟨?_, mem_top _⟩
    show (x : A ⧸ center A) ∈ ⊥
    rw [hx, QuotientGroup.mk_one]
    exact one_mem _

theorem mulAut_apply_eq_self (hZ : center A = zpowers z) (hz : orderOf z = 2) (α : MulAut A) :
    α z = z := by
  have hzc : z ∈ center A := hZ ▸ mem_zpowers z
  have hcen : α z ∈ center A := by
    rw [mem_center_iff]
    intro g
    obtain ⟨h, rfl⟩ := α.surjective g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hzc h]
  rcases (mem_center_iff_eq_one_or_eq hZ hz).mp hcen with h | h
  · exfalso
    rw [MulEquiv.map_eq_one_iff] at h
    rw [h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · exact h

@[expose] def diagonalHom (α : MulAut A) : A →* (A × A) ⧸ centerDiagonal A :=
  (QuotientGroup.mk' (centerDiagonal A)).comp ((MonoidHom.id A).prod α.toMonoidHom)

theorem diagonalHom_apply (α : MulAut A) (x : A) :
    diagonalHom α x = (((x, α x) : A × A) : (A × A) ⧸ centerDiagonal A) :=
  rfl

theorem ker_diagonalHom (hZ : center A = zpowers z) (hz : orderOf z = 2) (α : MulAut A) :
    (diagonalHom α).ker = center A := by
  ext x
  rw [MonoidHom.mem_ker, diagonalHom_apply, mk_eq_one_iff_centerDiagonal]
  constructor
  · exact fun h => h.1
  · intro hx
    refine ⟨hx, ?_⟩
    rcases (mem_center_iff_eq_one_or_eq hZ hz).mp hx with h | h
    · rw [h, map_one]
    · rw [h, mulAut_apply_eq_self hZ hz α]

theorem diagonal_eq_range (α : MulAut A) :
    ((MonoidHom.prod (MonoidHom.id A) α.toMonoidHom).range).map
      (QuotientGroup.mk' (centerDiagonal A)) = (diagonalHom α).range :=
  MonoidHom.map_range _ _

theorem card_range_diagonalHom (hZ : center A = zpowers z) (hz : orderOf z = 2)
    (α : MulAut A) : Nat.card (diagonalHom α).range = Nat.card (A ⧸ center A) := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (diagonalHom α)).toEquiv,
    Nat.card_congr (QuotientGroup.quotientMulEquivOfEq (ker_diagonalHom hZ hz α)).toEquiv]

theorem map_range_diagonalHom (α : MulAut A) (θ : MulAut (A ⧸ center A))
    (hαθ : ∀ x : A, ((α x : A) : A ⧸ center A) = θ (x : A ⧸ center A)) :
    (diagonalHom α).range.map (twoFactorProjection A) =
      ((MonoidHom.id (A ⧸ center A)).prod θ.toMonoidHom).range := by
  rw [MonoidHom.map_range]
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(x : A ⧸ center A), ?_⟩
    change ((x : A ⧸ center A), θ (x : A ⧸ center A)) =
      twoFactorProjection A (diagonalHom α x)
    rw [diagonalHom_apply, twoFactorProjection_mk, hαθ]
  · rintro ⟨s, rfl⟩
    induction s using QuotientGroup.induction_on with | H x => ?_
    refine ⟨x, ?_⟩
    change twoFactorProjection A (diagonalHom α x) =
      ((x : A ⧸ center A), θ (x : A ⧸ center A))
    rw [diagonalHom_apply, twoFactorProjection_mk, hαθ]

theorem twoFactorCenter_not_mem_diagonal (hZ : center A = zpowers z) (hz : orderOf z = 2)
    (α : MulAut A) :
    (((z, 1) : A × A) : (A × A) ⧸ centerDiagonal A) ∉ (diagonalHom α).range := by
  rintro ⟨x, hx⟩
  have hπ := congrArg (twoFactorProjection A) hx
  rw [diagonalHom_apply, twoFactorProjection_mk, twoFactorProjection_mk, Prod.mk.injEq] at hπ
  have hxz : (x : A ⧸ center A) = 1 := by
    rw [hπ.1, QuotientGroup.eq_one_iff]
    exact hZ ▸ mem_zpowers z
  have hxc : x ∈ (diagonalHom α).ker := by
    rw [ker_diagonalHom hZ hz α]
    exact (QuotientGroup.eq_one_iff x).mp hxz
  rw [MonoidHom.mem_ker] at hxc
  rw [hxc, eq_comm, mk_eq_one_iff_centerDiagonal] at hx
  rw [hx.2, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem twoFactorLeft_eq_range :
    ((⊤ : Subgroup A).prod ⊥).map (QuotientGroup.mk' (centerDiagonal A)) =
      ((QuotientGroup.mk' (centerDiagonal A)).comp (MonoidHom.inl A A)).range := by
  ext q
  constructor
  · rintro ⟨⟨x, y⟩, hxy, rfl⟩
    rw [SetLike.mem_coe, mem_prod] at hxy
    have hy : y = 1 := mem_bot.mp hxy.2
    exact ⟨x, by rw [hy]; rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(x, 1), mem_prod.mpr ⟨mem_top x, one_mem _⟩, rfl⟩

theorem twoFactorRight_eq_range :
    ((⊥ : Subgroup A).prod ⊤).map (QuotientGroup.mk' (centerDiagonal A)) =
      ((QuotientGroup.mk' (centerDiagonal A)).comp (MonoidHom.inr A A)).range := by
  ext q
  constructor
  · rintro ⟨⟨x, y⟩, hxy, rfl⟩
    rw [SetLike.mem_coe, mem_prod] at hxy
    have hx : x = 1 := mem_bot.mp hxy.1
    exact ⟨y, by rw [hx]; rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(1, x), mem_prod.mpr ⟨one_mem _, mem_top x⟩, rfl⟩

theorem inl_injective :
    Function.Injective ((QuotientGroup.mk' (centerDiagonal A)).comp (MonoidHom.inl A A)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  exact ((mk_eq_one_iff_centerDiagonal x 1).mp hx).2

theorem inr_injective :
    Function.Injective ((QuotientGroup.mk' (centerDiagonal A)).comp (MonoidHom.inr A A)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  exact ((mk_eq_one_iff_centerDiagonal 1 x).mp hx).2.symm

theorem card_comap_graph (hZ : center A = zpowers z) (hz : orderOf z = 2) [Finite A]
    (θ : MulAut (A ⧸ center A)) :
    Nat.card (((MonoidHom.id (A ⧸ center A)).prod θ.toMonoidHom).range.comap
      (twoFactorProjection A)) = 2 * Nat.card (A ⧸ center A) := by
  set Γ := ((MonoidHom.id (A ⧸ center A)).prod θ.toMonoidHom).range
  have hinj : Function.Injective ((MonoidHom.id (A ⧸ center A)).prod θ.toMonoidHom) :=
    fun s t h => congrArg Prod.fst h
  have hΓ : Nat.card Γ = Nat.card (A ⧸ center A) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h1 := card_mul_index (Γ.comap (twoFactorProjection A))
  rw [index_comap_of_surjective _ twoFactorProjection_surjective] at h1
  have h2 := card_ker_mul_card_of_surjective twoFactorProjection_surjective (f :=
    twoFactorProjection A)
  rw [ker_twoFactorProjection hZ hz, Nat.card_zpowers, orderOf_twoFactorCenter hz] at h2
  have h3 := card_mul_index Γ
  have hindex : Γ.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [← h2, ← h3, hΓ] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hindex) (h1.trans (by ring))

theorem comap_graph_structure (hZ : center A = zpowers z) (hz : orderOf z = 2) [Finite A]
    (hperf : Group.IsPerfect A) (α : MulAut A) (θ : MulAut (A ⧸ center A))
    (hαθ : ∀ x : A, ((α x : A) : A ⧸ center A) = θ (x : A ⧸ center A)) :
    (∃ e : ↥(zpowers (((z, 1) : A × A) : (A × A) ⧸ centerDiagonal A)) ×
        ↥(diagonalHom α).range ≃*
        ↥(((MonoidHom.id (A ⧸ center A)).prod θ.toMonoidHom).range.comap
          (twoFactorProjection A)), ∀ x y, (e (x, y) : (A × A) ⧸ centerDiagonal A) = x * y) ∧
    ⁅((MonoidHom.id (A ⧸ center A)).prod θ.toMonoidHom).range.comap (twoFactorProjection A),
      ((MonoidHom.id (A ⧸ center A)).prod θ.toMonoidHom).range.comap (twoFactorProjection A)⁆ =
      (diagonalHom α).range := by
  set c : (A × A) ⧸ centerDiagonal A := (((z, 1) : A × A) : (A × A) ⧸ centerDiagonal A)
    with hcdef
  set Γ := ((MonoidHom.id (A ⧸ center A)).prod θ.toMonoidHom).range with hΓdef
  set P := Γ.comap (twoFactorProjection A) with hPdef
  set Δ := (diagonalHom α).range with hΔdef
  have hΔP : Δ ≤ P := by
    intro x hx
    rw [hPdef, mem_comap, hΓdef, ← map_range_diagonalHom α θ hαθ]
    exact mem_map_of_mem _ hx
  have hcP : zpowers c ≤ P := by
    rw [hcdef, ← ker_twoFactorProjection hZ hz]
    exact MonoidHom.ker_le_comap _ _
  have hcc : c ∈ center ((A × A) ⧸ centerDiagonal A) := twoFactorCenter_mem_center hZ
  have hcomm : ∀ (x : zpowers c) (y : Δ), Commute (inclusion hcP x) (inclusion hΔP y) := by
    intro x y
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp x.2
    apply Subtype.ext
    change (x : (A × A) ⧸ centerDiagonal A) * y = y * x
    rw [← hk]
    exact (mem_center_iff.mp (zpow_mem hcc k) y).symm
  let φ := (inclusion hcP).noncommCoprod (inclusion hΔP) hcomm
  have hinj : Function.Injective φ := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨inclusion_injective _, inclusion_injective _, ?_⟩
    rw [disjoint_iff, eq_bot_iff]
    intro t ht
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := mem_inf.mp ht
    have htc : (t : (A × A) ⧸ centerDiagonal A) ∈ zpowers c := by rw [← hx]; exact x.2
    have htΔ : (t : (A × A) ⧸ centerDiagonal A) ∈ Δ := by rw [← hy]; exact y.2
    rcases (mem_zpowers_iff_eq_one_or_eq (orderOf_twoFactorCenter hz)).mp htc with h | h
    · exact mem_bot.mpr (Subtype.ext h)
    · exact absurd (h ▸ htΔ) (twoFactorCenter_not_mem_diagonal hZ hz α)
  have hcard : Nat.card (↥(zpowers c) × ↥Δ) = Nat.card P := by
    rw [Nat.card_prod, Nat.card_zpowers, orderOf_twoFactorCenter hz,
      card_range_diagonalHom hZ hz α, hPdef, hΓdef, card_comap_graph hZ hz θ]
  have hbij : Function.Bijective φ := (Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩
  refine ⟨⟨MulEquiv.ofBijective φ hbij, fun x y => rfl⟩, le_antisymm ?_ ?_⟩
  · rw [commutator_le]
    intro p hp p' hp'
    obtain ⟨⟨x, y⟩, hxy⟩ := hbij.2 ⟨p, hp⟩
    obtain ⟨⟨x', y'⟩, hxy'⟩ := hbij.2 ⟨p', hp'⟩
    have hp1 : p = x * y := (congrArg Subtype.val hxy).symm
    have hp2 : p' = x' * y' := (congrArg Subtype.val hxy').symm
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp x.2
    obtain ⟨k', hk'⟩ := mem_zpowers_iff.mp x'.2
    rw [hp1, hp2, ← hk, ← hk', commutatorElement_mul_left_of_mem_center (zpow_mem hcc k),
      commutatorElement_mul_right_of_mem_center (zpow_mem hcc k')]
    have hmem := commutator_mem_commutator y.2 y'.2
    rwa [commutator_range_eq_of_perfect hperf (diagonalHom α)] at hmem
  · calc Δ = ⁅Δ, Δ⁆ := (commutator_range_eq_of_perfect hperf (diagonalHom α)).symm
      _ ≤ ⁅P, P⁆ := commutator_mono hΔP hΔP

end Involution

theorem normal_le_center_of_ne_top [Finite A] (hperf : Group.IsPerfect A)
    [IsSimpleGroup (A ⧸ center A)] (N : Subgroup A) (hN : N.Normal) (hNtop : N ≠ ⊤) :
    N ≤ center A := by
  have hM : (N.map (QuotientGroup.mk' (center A))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (center A))) with
    h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · exfalso
    apply hNtop
    have hsup : N ⊔ center A = ⊤ := by
      rw [← QuotientGroup.ker_mk' (center A), ← comap_map_eq, h, comap_top]
    have hcomm : ∀ a b : A ⧸ N, a * b = b * a := by
      intro a b
      induction a using QuotientGroup.induction_on with | H x => ?_
      induction b using QuotientGroup.induction_on with | H y => ?_
      have hx : x ∈ N ⊔ center A := hsup ▸ mem_top x
      have hy : y ∈ N ⊔ center A := hsup ▸ mem_top y
      rw [← SetLike.mem_coe, mul_normal N (center A)] at hx hy
      obtain ⟨n, hn, w, hw, rfl⟩ := Set.mem_mul.mp hx
      obtain ⟨n', hn', w', hw', rfl⟩ := Set.mem_mul.mp hy
      have h1 : ((n * w : A) : A ⧸ N) = (w : A ⧸ N) := by
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
      have h2 : ((n' * w' : A) : A ⧸ N) = (w' : A ⧸ N) := by
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n').mpr hn', one_mul]
      rw [h1, h2, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hw' w]
    have hle : commutator A ≤ N := by
      rw [_root_.commutator_def, commutator_le]
      intro a _ b _
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    rw [Group.isPerfect_def.mp hperf] at hle
    exact top_unique hle

end TwoFactor

theorem two_factor_core {A : Type*} [Group A] [Finite A] {z : A} (hZ : center A = zpowers z)
    (hz : orderOf z = 2) {R : Type*} [Group R] [Finite R]
    (hR : closure {r : R | ∃ k : ℕ, orderOf r = 2 ^ k} = ⊤)
    (ν : R →* (A × A) ⧸ centerDiagonal A) (hν : Odd (Nat.card ν.ker))
    {Q₀ : Type*} [Group Q₀] [Finite Q₀] (e : R ⧸ pPrimeCore 2 R ≃* Q₀)
    [hQperf : Group.IsPerfect Q₀]
    (hQ1 : ∀ N : Subgroup Q₀, N.Normal → N ≠ ⊤ → N ≤ center Q₀)
    (hQ2 : (center Q₀).index = Nat.card (A ⧸ center A)) :
    Group.IsPerfect R ∧ ν.ker = pPrimeCore 2 R ∧ Nat.card ν.range = Nat.card Q₀ ∧
    (ν.range ≤ ((⊥ : Subgroup A).prod ⊤).map (QuotientGroup.mk' (centerDiagonal A)) ∨
      ν.range ≤ ((⊤ : Subgroup A).prod ⊥).map (QuotientGroup.mk' (centerDiagonal A)) ∨
      ∃ θ : MulAut (A ⧸ center A), ν.range.map (twoFactorProjection A) =
        ((MonoidHom.id (A ⧸ center A)).prod θ.toMonoidHom).range) := by
  set O := pPrimeCore 2 R with hOdef
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  let ρ : R →* Q₀ := e.toMonoidHom.comp (QuotientGroup.mk' O)
  have hρsurj : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective O)
  have hρker : ρ.ker = O := by
    ext r
    rw [MonoidHom.mem_ker]
    change e (r : R ⧸ O) = 1 ↔ r ∈ O
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hKL : ∀ N : Subgroup R, N.Normal → O ≤ N → N ≠ ⊤ →
      Nat.card (A ⧸ center A) ≤ N.index ∧ N ≤ (center Q₀).comap ρ := by
    intro N hN hON hNtop
    have hN₀normal : (N.map ρ).Normal := hN.map ρ hρsurj
    have hcomap : (N.map ρ).comap ρ = N := by
      rw [comap_map_eq, hρker, sup_eq_left.mpr hON]
    have hN₀top : N.map ρ ≠ ⊤ := fun h => hNtop (by rw [← hcomap, h, comap_top])
    have hN₀center := hQ1 _ hN₀normal hN₀top
    refine ⟨?_, ?_⟩
    · rw [← hcomap, index_comap_of_surjective _ hρsurj, ← hQ2]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero index_ne_zero_of_finite)
        (index_dvd_of_le hN₀center)
    · rw [← hcomap]
      exact comap_mono hN₀center
  have hRperf : Group.IsPerfect R := by
    have hQ' : Group.IsPerfect (R ⧸ O) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hsup : commutator R ⊔ O = ⊤ := by
      have hmap : (commutator R).map (QuotientGroup.mk' O) = ⊤ := by
        rw [_root_.commutator_def, map_commutator,
          map_top_of_surjective _ (QuotientGroup.mk'_surjective O), ← _root_.commutator_def]
        exact Group.isPerfect_def.mp hQ'
      rw [← QuotientGroup.ker_mk' O, ← comap_map_eq, hmap, comap_top]
    let f := QuotientGroup.mk' (commutator R)
    have hf : f = 1 := by
      apply hom_eq_one_of_odd_range hR f
      have hrange : f.range = O.map f := by
        rw [MonoidHom.range_eq_map, ← hsup, Subgroup.map_sup,
          (Subgroup.map_eq_bot_iff _).mpr (le_of_eq (QuotientGroup.ker_mk' _).symm), bot_sup_eq]
      rw [hrange]
      exact Odd.of_dvd_nat hOodd (card_map_dvd _ _)
    rw [Group.isPerfect_def, ← QuotientGroup.ker_mk' (commutator R)]
    change f.ker = ⊤
    rw [hf, MonoidHom.ker_one]
  have hkerle : ν.ker ≤ O := le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hν⟩
  have hψO : ∀ ψ : R →* A ⧸ center A, O.map ψ = ⊥ := by
    intro ψ
    set M := O.map ψ with hMdef
    set N := M.comap ψ with hNdef
    have hNnormal : N.Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [hNdef, mem_comap] at hn ⊢
      obtain ⟨o, ho, hon⟩ := mem_map.mp hn
      refine ⟨g * o * g⁻¹, (inferInstance : O.Normal).conj_mem o ho g, ?_⟩
      rw [map_mul, map_mul, map_inv, hon, map_mul, map_mul, map_inv]
    have hON : O ≤ N := le_comap_map ψ O
    by_cases hNtop : N = ⊤
    · have hrange : ψ.range = M := by
        apply le_antisymm
        · rintro _ ⟨r, rfl⟩
          have hr : r ∈ N := hNtop ▸ mem_top r
          exact hr
        · rw [hMdef]
          exact map_le_range ψ O
      have hψ1 : ψ = 1 := hom_eq_one_of_odd_range hR ψ
        (hrange ▸ Odd.of_dvd_nat hOodd (card_map_dvd _ _))
      rw [hMdef, hψ1]
      apply le_bot_iff.mp
      rintro _ ⟨o, -, rfl⟩
      exact mem_bot.mpr rfl
    · obtain ⟨hidx, -⟩ := hKL N hNnormal hON hNtop
      have hMle : M ≤ ψ.range := map_le_range ψ O
      have h1 : N.index = (M.subgroupOf ψ.range).index := index_comap M ψ
      have h2 := card_mul_index (M.subgroupOf ψ.range)
      rw [Nat.card_congr (subgroupOfEquivOfLe hMle).toEquiv] at h2
      have h3 : Nat.card ψ.range ≤ Nat.card (A ⧸ center A) := card_le_of_le le_top |>.trans
        (le_of_eq (card_top))
      have h4 : Nat.card M * Nat.card (A ⧸ center A) ≤ Nat.card (A ⧸ center A) := by
        calc Nat.card M * Nat.card (A ⧸ center A) ≤ Nat.card M * N.index :=
              Nat.mul_le_mul_left _ hidx
          _ = Nat.card ψ.range := by rw [h1, h2]
          _ ≤ Nat.card (A ⧸ center A) := h3
      have h5 : Nat.card M ≤ 1 := by
        have hpos : 0 < Nat.card (A ⧸ center A) := Nat.card_pos
        nlinarith
      exact eq_bot_of_card_le M h5
  set ψ₀ : R →* A ⧸ center A :=
    (MonoidHom.fst (A ⧸ center A) (A ⧸ center A)).comp ((twoFactorProjection A).comp ν)
    with hψ₀def
  set ψ₁ : R →* A ⧸ center A :=
    (MonoidHom.snd (A ⧸ center A) (A ⧸ center A)).comp ((twoFactorProjection A).comp ν)
    with hψ₁def
  have hπν : ∀ r : R, twoFactorProjection A (ν r) = (ψ₀ r, ψ₁ r) := fun r => rfl
  have hOker : O ≤ ν.ker := by
    have hmap : O.map ν ≤ (twoFactorProjection A).ker := by
      rintro _ ⟨o, ho, rfl⟩
      rw [MonoidHom.mem_ker, hπν, Prod.mk_eq_one]
      refine ⟨?_, ?_⟩
      · have : ψ₀ o ∈ O.map ψ₀ := mem_map_of_mem _ ho
        rwa [hψO ψ₀, mem_bot] at this
      · have : ψ₁ o ∈ O.map ψ₁ := mem_map_of_mem _ ho
        rwa [hψO ψ₁, mem_bot] at this
    have hdvd : Nat.card (O.map ν) ∣ 2 := by
      have := card_dvd_of_le hmap
      rwa [ker_twoFactorProjection hZ hz, Nat.card_zpowers, orderOf_twoFactorCenter hz] at this
    have hodd : Odd (Nat.card (O.map ν)) := Odd.of_dvd_nat hOodd (card_map_dvd _ _)
    have hone : Nat.card (O.map ν) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    rw [← Subgroup.map_eq_bot_iff]
    exact card_eq_one.mp hone
  have hker : ν.ker = O := le_antisymm hkerle hOker
  have hcardY : Nat.card ν.range = Nat.card Q₀ := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ν).toEquiv,
      Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv, Nat.card_congr e.toEquiv]
  set Zh := (center Q₀).comap ρ with hZhdef
  have hZhindex : Zh.index = Nat.card (A ⧸ center A) := by
    rw [hZhdef, index_comap_of_surjective _ hρsurj, hQ2]
  have hcoord : ∀ ψ : R →* A ⧸ center A, O ≤ ψ.ker → ψ ≠ 1 →
      Function.Surjective ψ ∧ ψ.ker = Zh := by
    intro ψ hOψ hψ
    have hktop : ψ.ker ≠ ⊤ := fun h => hψ (MonoidHom.ker_eq_top_iff.mp h)
    obtain ⟨hidx, hle⟩ := hKL ψ.ker inferInstance hOψ hktop
    have hrange : Nat.card ψ.range = Nat.card (A ⧸ center A) := by
      apply le_antisymm
      · exact (card_le_of_le le_top).trans (le_of_eq card_top)
      · rw [← index_ker]
        exact hidx
    have hsurj : Function.Surjective ψ := by
      rw [← MonoidHom.range_eq_top]
      exact eq_top_of_card_eq _ hrange
    refine ⟨hsurj, eq_of_le_of_card_ge hle ?_⟩
    have h1 := card_mul_index Zh
    have h2 := card_mul_index ψ.ker
    rw [index_ker, hrange] at h2
    rw [hZhindex] at h1
    exact le_of_eq (Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm))
  have hOψ₀ : O ≤ ψ₀.ker := fun o ho => by
    have := hOker ho
    rw [MonoidHom.mem_ker] at this ⊢
    rw [hψ₀def, MonoidHom.comp_apply, MonoidHom.comp_apply, this, map_one, map_one]
  have hOψ₁ : O ≤ ψ₁.ker := fun o ho => by
    have := hOker ho
    rw [MonoidHom.mem_ker] at this ⊢
    rw [hψ₁def, MonoidHom.comp_apply, MonoidHom.comp_apply, this, map_one, map_one]
  refine ⟨hRperf, hker, hcardY, ?_⟩
  by_cases h₀ : ψ₀ = 1
  · left
    rw [← comap_twoFactorProjection_right hZ hz]
    rintro _ ⟨r, rfl⟩
    rw [mem_comap, hπν, mem_prod]
    refine ⟨?_, mem_top _⟩
    rw [h₀]
    exact one_mem _
  by_cases h₁ : ψ₁ = 1
  · right
    left
    rw [← comap_twoFactorProjection_left hZ hz]
    rintro _ ⟨r, rfl⟩
    rw [mem_comap, hπν, mem_prod]
    refine ⟨mem_top _, ?_⟩
    rw [h₁]
    exact one_mem _
  right
  right
  obtain ⟨hs₀, hk₀⟩ := hcoord ψ₀ hOψ₀ h₀
  obtain ⟨hs₁, hk₁⟩ := hcoord ψ₁ hOψ₁ h₁
  let e₀ := QuotientGroup.liftEquiv Zh hs₀ hk₀.symm
  let e₁ := QuotientGroup.liftEquiv Zh hs₁ hk₁.symm
  let θ : MulAut (A ⧸ center A) := e₀.symm.trans e₁
  have hθ : ∀ r : R, θ (ψ₀ r) = ψ₁ r := by
    intro r
    change e₁ (e₀.symm (ψ₀ r)) = ψ₁ r
    rw [show ψ₀ r = e₀ (r : R ⧸ Zh) from rfl, MulEquiv.symm_apply_apply]
    rfl
  refine ⟨θ, ?_⟩
  ext p
  constructor
  · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
    exact ⟨ψ₀ r, by rw [hπν]; change (ψ₀ r, θ (ψ₀ r)) = _; rw [hθ]⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨r, rfl⟩ := hs₀ s
    refine ⟨ν r, ⟨r, rfl⟩, ?_⟩
    rw [hπν]
    change (ψ₀ r, ψ₁ r) = (ψ₀ r, θ (ψ₀ r))
    rw [hθ]

theorem odd_kernel_two_factor_coordinate_or_diagonal_image {A : Type*} [Group A] [Finite A]
    (hperf : Group.IsPerfect A) {z : A} (hZ : center A = zpowers z) (hz : orderOf z = 2)
    [IsSimpleGroup (A ⧸ center A)]
    (hlift : ∀ θ : MulAut (A ⧸ center A), ∃ α : MulAut A,
      ∀ x : A, ((α x : A) : A ⧸ center A) = θ (x : A ⧸ center A))
    {R : Type*} [Group R] [Finite R]
    (hR : closure {r : R | ∃ k : ℕ, orderOf r = 2 ^ k} = ⊤)
    (ν : R →* (A × A) ⧸ centerDiagonal A) (hν : Odd (Nat.card ν.ker))
    (hQ : Nonempty (R ⧸ pPrimeCore 2 R ≃* A) ∨
      Nonempty (R ⧸ pPrimeCore 2 R ≃* A ⧸ center A)) :
    centerDiagonal A = zpowers (z, z) ∧
    (((1, z) : A × A) : (A × A) ⧸ centerDiagonal A) =
      (((z, 1) : A × A) : (A × A) ⧸ centerDiagonal A) ∧
    Group.IsPerfect R ∧ ν.ker = pPrimeCore 2 R ∧
    (Nonempty (R ⧸ pPrimeCore 2 R ≃* A) →
      ν.range = ((⊤ : Subgroup A).prod ⊥).map (QuotientGroup.mk' (centerDiagonal A)) ∨
      ν.range = ((⊥ : Subgroup A).prod ⊤).map (QuotientGroup.mk' (centerDiagonal A))) ∧
    (Nonempty (R ⧸ pPrimeCore 2 R ≃* A ⧸ center A) →
      ∃ θ : MulAut (A ⧸ center A),
        ν.range.map (twoFactorProjection A) =
          ((MonoidHom.id (A ⧸ center A)).prod θ.toMonoidHom).range ∧
        (∀ θ' : MulAut (A ⧸ center A), ν.range.map (twoFactorProjection A) =
          ((MonoidHom.id (A ⧸ center A)).prod θ'.toMonoidHom).range → θ' = θ) ∧
        (∀ α : MulAut A, (∀ x : A, ((α x : A) : A ⧸ center A) = θ (x : A ⧸ center A)) →
          ν.range = ((MonoidHom.prod (MonoidHom.id A) α.toMonoidHom).range).map
            (QuotientGroup.mk' (centerDiagonal A)) ∧
          Nonempty (((MonoidHom.prod (MonoidHom.id A) α.toMonoidHom).range).map
            (QuotientGroup.mk' (centerDiagonal A)) ≃* A ⧸ center A) ∧
          (∃ e : ↥(zpowers (((z, 1) : A × A) : (A × A) ⧸ centerDiagonal A)) ×
              ↥(((MonoidHom.prod (MonoidHom.id A) α.toMonoidHom).range).map
                (QuotientGroup.mk' (centerDiagonal A))) ≃*
              ↥(((MonoidHom.id (A ⧸ center A)).prod θ.toMonoidHom).range.comap
                (twoFactorProjection A)),
            ∀ x y, (e (x, y) : (A × A) ⧸ centerDiagonal A) = x * y) ∧
          ⁅((MonoidHom.id (A ⧸ center A)).prod θ.toMonoidHom).range.comap
              (twoFactorProjection A),
            ((MonoidHom.id (A ⧸ center A)).prod θ.toMonoidHom).range.comap
              (twoFactorProjection A)⁆ =
            ((MonoidHom.prod (MonoidHom.id A) α.toMonoidHom).range).map
              (QuotientGroup.mk' (centerDiagonal A))) ∧
        ¬ ν.range ≤ ((⊤ : Subgroup A).prod ⊥).map (QuotientGroup.mk' (centerDiagonal A)) ∧
        ¬ ν.range ≤ ((⊥ : Subgroup A).prod ⊤).map (QuotientGroup.mk' (centerDiagonal A))) := by
  have : Group.IsPerfect A := hperf
  have hZS : center (A ⧸ center A) = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot A
  have hcardZ : Nat.card (center A) = 2 := by rw [hZ, Nat.card_zpowers, hz]
  have hcardA : Nat.card A = 2 * Nat.card (A ⧸ center A) := by
    rw [← hcardZ, ← index_eq_card, card_mul_index]
  have hSpos : 1 < Nat.card (A ⧸ center A) := Finite.one_lt_card
  have hQ1S : ∀ N : Subgroup (A ⧸ center A), N.Normal → N ≠ ⊤ → N ≤ center (A ⧸ center A) := by
    intro N hN hNtop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · rw [h]
      exact bot_le
    · exact absurd h hNtop
  have hQ2S : (center (A ⧸ center A)).index = Nat.card (A ⧸ center A) := by
    rw [hZS, index_bot]
  have hcoreA := fun e : R ⧸ pPrimeCore 2 R ≃* A =>
    two_factor_core hZ hz hR ν hν e (normal_le_center_of_ne_top hperf) (index_eq_card _)
  have hcoreS := fun e : R ⧸ pPrimeCore 2 R ≃* A ⧸ center A =>
    two_factor_core hZ hz hR ν hν e hQ1S hQ2S
  have hbase : Group.IsPerfect R ∧ ν.ker = pPrimeCore 2 R := by
    rcases hQ with he | he
    · obtain ⟨e⟩ := he
      exact ⟨(hcoreA e).1, (hcoreA e).2.1⟩
    · obtain ⟨e⟩ := he
      exact ⟨(hcoreS e).1, (hcoreS e).2.1⟩
  have hYperf : ⁅ν.range, ν.range⁆ = ν.range := commutator_range_eq_of_perfect hbase.1 ν
  set A₀ := ((⊤ : Subgroup A).prod ⊥).map (QuotientGroup.mk' (centerDiagonal A)) with hA₀def
  set A₁ := ((⊥ : Subgroup A).prod ⊤).map (QuotientGroup.mk' (centerDiagonal A)) with hA₁def
  have hcardA₀ : Nat.card A₀ = Nat.card A := by
    rw [hA₀def, twoFactorLeft_eq_range]
    exact (Nat.card_congr (MonoidHom.ofInjective inl_injective).toEquiv).symm
  have hcardA₁ : Nat.card A₁ = Nat.card A := by
    rw [hA₁def, twoFactorRight_eq_range]
    exact (Nat.card_congr (MonoidHom.ofInjective inr_injective).toEquiv).symm
  have hperfA₀ : Group.IsPerfect A₀ := by
    rw [Subgroup.isPerfect_iff, hA₀def, twoFactorLeft_eq_range]
    exact commutator_range_eq_of_perfect hperf _
  have hperfA₁ : Group.IsPerfect A₁ := by
    rw [Subgroup.isPerfect_iff, hA₁def, twoFactorRight_eq_range]
    exact commutator_range_eq_of_perfect hperf _
  have hdiag : ∀ (θ : MulAut (A ⧸ center A)) (α : MulAut A),
      (∀ x : A, ((α x : A) : A ⧸ center A) = θ (x : A ⧸ center A)) →
      ν.range.map (twoFactorProjection A) =
        ((MonoidHom.id (A ⧸ center A)).prod θ.toMonoidHom).range →
      ν.range ≤ (diagonalHom α).range := by
    intro θ α hα hθ
    have hP := (comap_graph_structure hZ hz hperf α θ hα).2
    have hYP : ν.range ≤ ((MonoidHom.id (A ⧸ center A)).prod θ.toMonoidHom).range.comap
        (twoFactorProjection A) := by
      rw [← hθ]
      exact le_comap_map _ _
    rw [← hYperf, ← hP]
    exact commutator_mono hYP hYP
  refine ⟨centerDiagonal_eq_zpowers hZ hz, mk_one_z_eq hZ hz, hbase.1, hbase.2, ?_, ?_⟩
  · intro he
    obtain ⟨e⟩ := he
    obtain ⟨-, -, hcard, htri⟩ := hcoreA e
    rcases htri with hY | hY | ⟨θ, hθ⟩
    · right
      exact eq_of_le_of_card_ge hY (by rw [hcardA₁, hcard])
    · left
      exact eq_of_le_of_card_ge hY (by rw [hcardA₀, hcard])
    · exfalso
      obtain ⟨α, hα⟩ := hlift θ
      have hle := card_le_of_le (hdiag θ α hα hθ)
      rw [card_range_diagonalHom hZ hz α, hcard, hcardA] at hle
      omega
  · intro he
    obtain ⟨e⟩ := he
    obtain ⟨-, -, hcard, htri⟩ := hcoreS e
    have hnot : ∀ B : Subgroup ((A × A) ⧸ centerDiagonal A), Group.IsPerfect B →
        Nat.card B = Nat.card A → ¬ ν.range ≤ B := by
      intro B hB hcardB hYB
      apply index_ne_two_of_perfect hB (ν.range.subgroupOf B)
      have h := card_mul_index (ν.range.subgroupOf B)
      rw [Nat.card_congr (subgroupOfEquivOfLe hYB).toEquiv, hcard, hcardB, hcardA] at h
      exact Nat.eq_of_mul_eq_mul_left (by omega) (h.trans (mul_comm _ _))
    have hnotA₀ := hnot A₀ hperfA₀ hcardA₀
    have hnotA₁ := hnot A₁ hperfA₁ hcardA₁
    rcases htri with hY | hY | ⟨θ, hθ⟩
    · exact absurd hY hnotA₁
    · exact absurd hY hnotA₀
    · refine ⟨θ, hθ, ?_, ?_, hnotA₀, hnotA₁⟩
      · intro θ' hθ'
        apply MulEquiv.ext
        intro s
        have hmem : (s, θ s) ∈ ((MonoidHom.id (A ⧸ center A)).prod θ'.toMonoidHom).range := by
          rw [← hθ', hθ]
          exact ⟨s, rfl⟩
        obtain ⟨t, ht⟩ := hmem
        have h1 : t = s := congrArg Prod.fst ht
        have h2 : θ' t = θ s := congrArg Prod.snd ht
        rw [← h1]
        rw [h1] at h2 ⊢
        exact h2
      · intro α hα
        rw [diagonal_eq_range]
        obtain ⟨hprod, hderiv⟩ := comap_graph_structure hZ hz hperf α θ hα
        have hYeq : ν.range = (diagonalHom α).range := by
          apply eq_of_le_of_card_ge (hdiag θ α hα hθ)
          rw [card_range_diagonalHom hZ hz α, hcard]
        refine ⟨hYeq, ⟨((QuotientGroup.quotientKerEquivRange (diagonalHom α)).symm.trans
          (QuotientGroup.quotientMulEquivOfEq (ker_diagonalHom hZ hz α)))⟩, hprod, hderiv⟩

end CFSG.ComponentClassification.UnbalancedGS
