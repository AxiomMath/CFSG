module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Assembly.Subnormal
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open CFSG.Assembly (IsComponentOf IsSubnormal IsElemAbelian pRank)

variable {G : Type*} [Group G]

theorem isElemAbelian_iff_isElementaryAbelian {p : ℕ} {E : Subgroup G} :
    IsElemAbelian p E ↔ IsElementaryAbelian p E :=
  CFSG.Open.isElemAbelian_iff_isElementaryAbelian

theorem isPGroup_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem isElemAbelian_sup_zpowers {E : Subgroup G} (hE : IsElemAbelian 2 E) {w : G}
    (hw : w ^ 2 = 1) (hwE : ∀ x ∈ E, x * w = w * x) : IsElemAbelian 2 (E ⊔ zpowers w) := by
  have : IsElementaryAbelian 2 E := isElemAbelian_iff_isElementaryAbelian.mp hE
  have : IsElementaryAbelian 2 (zpowers w) := IsElementaryAbelian.zpowers_of_pow_eq_one hw
  refine isElemAbelian_iff_isElementaryAbelian.mpr
    (IsElementaryAbelian.sup_of_le_centralizer ?_)
  rw [zpowers_le]
  exact mem_centralizer_iff.mpr hwE

theorem isElemAbelian_map {H : Type*} [Group H] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) (f : G →* H) : IsElemAbelian p (E.map f) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem pRank_eq_of_forall_card_le [Finite G] {p : ℕ} (hp : 1 < p) {H A : Subgroup G} {r : ℕ}
    (hAH : A ≤ H) (hA : IsElemAbelian p A) (hcard : Nat.card A = p ^ r)
    (hle : ∀ E : Subgroup G, E ≤ H → IsElemAbelian p E → Nat.card E ≤ p ^ r) :
    pRank p H = r := by
  have hmem : ∀ k ∈ {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k},
      k ≤ r := by
    rintro k ⟨E, hEH, hE, hk⟩
    exact (Nat.pow_le_pow_iff_right hp).mp (hk ▸ hle E hEH hE)
  unfold pRank
  exact le_antisymm (csSup_le ⟨r, A, hAH, hA, hcard⟩ hmem) (le_csSup ⟨r, hmem⟩ ⟨A, hAH, hA, hcard⟩)

theorem mem_smul_sylow_iff {H : Type*} [Group H] {p : ℕ} (P : Sylow p H) (g x : H) :
    x ∈ g • P ↔ g⁻¹ * x * g ∈ P := by
  change x ∈ ((g • P : Sylow p H) : Subgroup H) ↔ g⁻¹ * x * g ∈ (P : Subgroup H)
  rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply]

theorem exists_conj_mem_sylow [Finite G] {p : ℕ} [Fact p.Prime] {C E : Subgroup G}
    (hEC : E ≤ C) (hE : IsPGroup p E) (P : Sylow p C) :
    ∃ g : C, ∀ x : C, (x : G) ∈ E → g⁻¹ * x * g ∈ P := by
  have hE' : IsPGroup p (E.subgroupOf C) := hE.of_equiv (subgroupOfEquivOfLe hEC).symm
  obtain ⟨Q, hQ⟩ := hE'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C P Q
  refine ⟨g, fun x hx => ?_⟩
  have hxQ : x ∈ Q := hQ hx
  rw [← hg] at hxQ
  exact (mem_smul_sylow_iff P g x).mp hxQ

theorem isSubnormal_map (φ : MulAut G) {H K : Subgroup G} (h : IsSubnormal H K) :
    IsSubnormal (H.map φ.toMonoidHom) (K.map φ.toMonoidHom) :=
  h.map φ.toMonoidHom

theorem map_centralizer_singleton (φ : MulAut G) (a : G) :
    (centralizer {a}).map φ.toMonoidHom = centralizer {φ a} := by
  ext x
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg φ h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h'
  · intro h
    have h' := congrArg φ.symm h
    rwa [map_mul, map_mul, MulEquiv.symm_apply_apply] at h'

theorem map_conj_eq_of_mem_centralizer {J : Subgroup G} {d : G}
    (hd : d ∈ centralizer (J : Set G)) : J.map (MulAut.conj d).toMonoidHom = J := by
  ext x
  rw [mem_map_equiv, MulAut.conj_symm_apply]
  constructor
  · intro h
    have hc := mem_centralizer_iff.mp hd _ h
    have hx : d⁻¹ * x * d = x := by
      apply mul_right_cancel (b := d)
      rw [hc]
      group
    rwa [hx] at h
  · intro h
    rw [mul_assoc, mem_centralizer_iff.mp hd x h, inv_mul_cancel_left]
    exact h

section NoFourGroup

variable [Finite G] {C : Subgroup G} {a : G}

theorem eq_of_commute_of_no_four_group (haC : a ∈ C) (ha : orderOf a = 2)
    (hE : ∀ E : Subgroup G, E ≤ C → IsElemAbelian 2 E → a ∈ E → Nat.card E ≤ 2)
    {u : G} (huC : u ∈ C) (hu : orderOf u = 2) (hau : a * u = u * a) : u = a := by
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
  have hza : IsElemAbelian 2 (zpowers a) := isElemAbelian_iff_isElementaryAbelian.mpr
    (IsElementaryAbelian.zpowers_of_pow_eq_one ha2)
  have hEab : IsElemAbelian 2 (zpowers a ⊔ zpowers u) := by
    refine isElemAbelian_sup_zpowers hza hu2 ?_
    rintro _ ⟨k, rfl⟩
    exact ((Commute.zpow_left hau k)).eq
  have hEC : zpowers a ⊔ zpowers u ≤ C := sup_le (zpowers_le.mpr haC) (zpowers_le.mpr huC)
  have hcard := hE _ hEC hEab (mem_sup_left (mem_zpowers a))
  have heq : zpowers a = zpowers a ⊔ zpowers u :=
    eq_of_le_of_card_ge le_sup_left (by rw [Nat.card_zpowers, ha]; exact hcard)
  have huA : u ∈ zpowers a := heq ▸ mem_sup_right (mem_zpowers u)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp huA
  rw [← zpow_mod_orderOf, ha] at hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [Nat.cast_ofNat, h0, zpow_zero] at hk
    rw [← hk, orderOf_one] at hu
    exact absurd hu (by norm_num)
  · rw [Nat.cast_ofNat, h1, zpow_one] at hk
    exact hk.symm

theorem coe_eq_of_mem_sylow_of_no_four_group (haC : a ∈ C) (ha : orderOf a = 2)
    (hE : ∀ E : Subgroup G, E ≤ C → IsElemAbelian 2 E → a ∈ E → Nat.card E ≤ 2)
    (T : Sylow 2 C) (haT : (⟨a, haC⟩ : C) ∈ T) {u : C} (huT : u ∈ T) (hu : orderOf u = 2) :
    (u : G) = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha1 : (⟨⟨a, haC⟩, haT⟩ : T) ≠ 1 := by
    intro h
    have h' : a = 1 := congrArg (fun y : T => ((y : C) : G)) h
    rw [h', orderOf_one] at ha
    exact absurd ha (by norm_num)
  have : Nontrivial T := nontrivial_of_ne _ _ ha1
  have hZ : Nontrivial (center T) := T.isPGroup'.center_nontrivial
  obtain ⟨n, hn, hcardZ⟩ :=
    ((T.isPGroup'.to_subgroup (center T)).nontrivial_iff_card).mp hZ
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center T) 2
    (by rw [hcardZ]; exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn))
  have hzord : orderOf (((z : T) : C) : G) = 2 := by
    rw [orderOf_coe, orderOf_coe, orderOf_coe, hz]
  have hzcomm : ∀ y : T,
      ((y : C) : G) * (((z : T) : C) : G) = (((z : T) : C) : G) * ((y : C) : G) :=
    fun y => congrArg (fun w : T => ((w : C) : G)) (mem_center_iff.mp z.2 y)
  have hza : (((z : T) : C) : G) = a :=
    eq_of_commute_of_no_four_group haC ha hE ((z : T) : C).2 hzord
      (hzcomm ⟨⟨a, haC⟩, haT⟩)
  refine eq_of_commute_of_no_four_group haC ha hE u.2 (by rw [orderOf_coe, hu]) ?_
  have h := hzcomm ⟨u, huT⟩
  rw [hza] at h
  exact h.symm

theorem exists_conj_eq_of_no_four_group (haC : a ∈ C) (ha : orderOf a = 2)
    (hE : ∀ E : Subgroup G, E ≤ C → IsElemAbelian 2 E → a ∈ E → Nat.card E ≤ 2)
    {t : G} (htC : t ∈ C) (ht : orderOf t = 2) : ∃ c ∈ C, c⁻¹ * a * c = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpa : IsPGroup 2 (zpowers (⟨a, haC⟩ : C)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_mk, ha, pow_one])
  obtain ⟨T, hT⟩ := hpa.exists_le_sylow
  have hpt : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow (zpowers_le.mpr htC) hpt T
  have hgt := hg ⟨t, htC⟩ (mem_zpowers t)
  have hord : orderOf (g⁻¹ * ⟨t, htC⟩ * g) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) (⟨t, htC⟩ : C)
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, Subgroup.orderOf_mk, ht]
  have heq := coe_eq_of_mem_sylow_of_no_four_group haC ha hE T (hT (mem_zpowers _)) hgt hord
  refine ⟨(g : G)⁻¹, inv_mem g.2, ?_⟩
  rw [coe_mul, coe_mul, coe_inv] at heq
  rw [← heq]
  group

theorem card_le_two_of_no_four_group (haC : a ∈ C) (ha : orderOf a = 2)
    (hE : ∀ E : Subgroup G, E ≤ C → IsElemAbelian 2 E → a ∈ E → Nat.card E ≤ 2)
    {E : Subgroup G} (hEC : E ≤ C) (hEab : IsElemAbelian 2 E) : Nat.card E ≤ 2 := by
  rcases eq_or_ne E ⊥ with rfl | hne
  · rw [card_bot]
    norm_num
  obtain ⟨e, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have he1' : (e : G) ≠ 1 := fun h => he1 (Subtype.ext h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he2 : orderOf (e : G) = 2 := orderOf_eq_prime (hEab.2 e e.2) he1'
  obtain ⟨c, hcC, hce⟩ := exists_conj_eq_of_no_four_group haC ha hE (hEC e.2) he2
  have haE' : a ∈ E.map (MulAut.conj c).toMonoidHom := by
    refine ⟨e, e.2, ?_⟩
    change c * e * c⁻¹ = a
    rw [← hce]
    group
  have hE'C : E.map (MulAut.conj c).toMonoidHom ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hcC (hEC hx)) (inv_mem hcC)
  have h := hE _ hE'C (isElemAbelian_map hEab _) haE'
  rwa [card_map_of_injective (MulAut.conj c).injective] at h

end NoFourGroup

section Components

variable {a : G} {J : Subgroup G}

theorem mem_centralizer_of_le_centralizer_singleton (hJa : J ≤ centralizer {a}) :
    a ∈ centralizer (J : Set G) :=
  mem_centralizer_iff.mpr fun _ hj => mem_centralizer_singleton_iff.mp (hJa hj)

variable [Finite G]

theorem pRank_centralizer_eq_one_of_no_four_group (ha : orderOf a = 2)
    (hJ : IsComponentOf J (centralizer {a}))
    (hE : ∀ E : Subgroup G, E ≤ centralizer (J : Set G) → IsElemAbelian 2 E → a ∈ E →
      Nat.card E ≤ 2) :
    pRank 2 (centralizer (J : Set G)) = 1 := by
  have haC := mem_centralizer_of_le_centralizer_singleton hJ.1
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  refine pRank_eq_of_forall_card_le one_lt_two (zpowers_le.mpr haC)
    (isElemAbelian_iff_isElementaryAbelian.mpr (IsElementaryAbelian.zpowers_of_pow_eq_one ha2))
    (by rw [Nat.card_zpowers, ha, pow_one]) fun E hEC hEab => ?_
  rw [pow_one]
  exact card_le_two_of_no_four_group haC ha hE hEC hEab

theorem exists_conj_eq_of_component_no_four_group (ha : orderOf a = 2)
    (hJ : IsComponentOf J (centralizer {a}))
    (hE : ∀ E : Subgroup G, E ≤ centralizer (J : Set G) → IsElemAbelian 2 E → a ∈ E →
      Nat.card E ≤ 2)
    {t : G} (htC : t ∈ centralizer (J : Set G)) (ht : orderOf t = 2) :
    ∃ c ∈ centralizer (J : Set G), c⁻¹ * a * c = t :=
  exists_conj_eq_of_no_four_group (mem_centralizer_of_le_centralizer_singleton hJ.1) ha hE htC ht

theorem isComponentOf_centralizer_of_no_four_group (ha : orderOf a = 2)
    (hJ : IsComponentOf J (centralizer {a}))
    (hE : ∀ E : Subgroup G, E ≤ centralizer (J : Set G) → IsElemAbelian 2 E → a ∈ E →
      Nat.card E ≤ 2)
    {t : G} (htC : t ∈ centralizer (J : Set G)) (ht : orderOf t = 2) :
    IsComponentOf J (centralizer {t}) := by
  obtain ⟨c, hcC, hct⟩ := exists_conj_eq_of_component_no_four_group ha hJ hE htC ht
  refine ⟨fun j hj => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htC j hj), ?_,
    hJ.2.2⟩
  have h := isSubnormal_map (MulAut.conj c⁻¹) hJ.2.1
  rwa [map_conj_eq_of_mem_centralizer (inv_mem hcC), map_centralizer_singleton,
    MulAut.conj_apply, inv_inv, hct] at h

theorem no_four_group_witness_universal_component (ha : orderOf a = 2)
    (hJ : IsComponentOf J (centralizer {a}))
    (hE : ∀ E : Subgroup G, E ≤ centralizer (J : Set G) → IsElemAbelian 2 E → a ∈ E →
      Nat.card E ≤ 2) :
    pRank 2 (centralizer (J : Set G)) = 1 ∧
      ∀ t ∈ centralizer (J : Set G), orderOf t = 2 →
        (∃ c ∈ centralizer (J : Set G), c⁻¹ * a * c = t) ∧ IsComponentOf J (centralizer {t}) :=
  ⟨pRank_centralizer_eq_one_of_no_four_group ha hJ hE, fun _ htC ht =>
    ⟨exists_conj_eq_of_component_no_four_group ha hJ hE htC ht,
      isComponentOf_centralizer_of_no_four_group ha hJ hE htC ht⟩⟩

theorem pRank_centralizer_eq_pRank {A : Subgroup G} (hAJ : A ≤ centralizer (J : Set G))
    (hA : IsElemAbelian 2 A) (hA1 : A ≠ ⊥)
    (hcomp : ∀ a ∈ A, a ≠ 1 → IsComponentOf J (centralizer {a}))
    (hmax : ∀ t : G, orderOf t = 2 → IsComponentOf J (centralizer {t}) →
      ∀ B : Subgroup G, B ≤ centralizer (J : Set G) → IsElemAbelian 2 B → t ∈ B →
        Nat.card B ≤ Nat.card A) :
    pRank 2 (centralizer (J : Set G)) = pRank 2 A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (J : Set G) with hCdef
  obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hA).exists_card_eq
  have hrankA : pRank 2 A = k :=
    pRank_eq_of_forall_card_le one_lt_two le_rfl hA hk fun E hEA _ => hk ▸ card_le_of_le hEA
  rw [hrankA]
  have hA' : IsPGroup 2 (A.subgroupOf C) :=
    (isPGroup_of_isElemAbelian hA).of_equiv (subgroupOfEquivOfLe hAJ).symm
  obtain ⟨P, hP⟩ := hA'.exists_le_sylow
  obtain ⟨a₀, ha₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  have ha₀1 : (a₀ : G) ≠ 1 := fun h => ha₀ (Subtype.ext h)
  have ha₀2 : orderOf (a₀ : G) = 2 := orderOf_eq_prime (hA.2 _ a₀.2) ha₀1
  have ha₀P : (⟨a₀, hAJ a₀.2⟩ : C) ∈ P := hP a₀.2
  have : Nontrivial P := nontrivial_of_ne ⟨⟨a₀, hAJ a₀.2⟩, ha₀P⟩ 1
    (fun h => ha₀1 (congrArg (fun y : P => ((y : C) : G)) h))
  have hZ : Nontrivial (center P) := P.isPGroup'.center_nontrivial
  obtain ⟨n, hn, hcardZ⟩ := ((P.isPGroup'.to_subgroup (center P)).nontrivial_iff_card).mp hZ
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center P) 2
    (by rw [hcardZ]; exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn))
  set w : G := (((z : P) : C) : G) with hw
  have hwC : w ∈ C := ((z : P) : C).2
  have hword : orderOf w = 2 := by rw [hw, orderOf_coe, orderOf_coe, orderOf_coe, hz]
  have hw2 : w ^ 2 = 1 := hword ▸ pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := fun h => by
    rw [h, orderOf_one] at hword
    exact absurd hword (by norm_num)
  have hwP : ∀ y : C, y ∈ P → (y : G) * w = w * y := fun y hy =>
    congrArg (fun v : P => ((v : C) : G)) (mem_center_iff.mp z.2 ⟨y, hy⟩)
  have hwA : w ∈ A := by
    have hAz : IsElemAbelian 2 (A ⊔ zpowers w) :=
      isElemAbelian_sup_zpowers hA hw2 fun x hx => hwP ⟨x, hAJ hx⟩ (hP hx)
    have hAzC : A ⊔ zpowers w ≤ C := sup_le hAJ (zpowers_le.mpr hwC)
    have hcard := hmax _ ha₀2 (hcomp _ a₀.2 ha₀1) _ hAzC hAz (mem_sup_left a₀.2)
    have heq : A = A ⊔ zpowers w := eq_of_le_of_card_ge le_sup_left hcard
    rw [heq]
    exact mem_sup_right (mem_zpowers w)
  have hJw := hcomp w hwA hw1
  refine pRank_eq_of_forall_card_le one_lt_two hAJ hA hk fun E hEC hEab => ?_
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow hEC (isPGroup_of_isElemAbelian hEab) P
  set E' := E.map (MulAut.conj (g : G)⁻¹).toMonoidHom with hE'
  have hE'C : E' ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem (inv_mem g.2) (hEC hx)) (inv_mem (inv_mem g.2))
  have hE'w : ∀ y ∈ E', y * w = w * y := by
    rintro _ ⟨x, hx, rfl⟩
    have h := hwP (g⁻¹ * ⟨x, hEC hx⟩ * g) (hg ⟨x, hEC hx⟩ hx)
    rw [coe_mul, coe_mul, coe_inv] at h
    change (g : G)⁻¹ * x * ((g : G)⁻¹)⁻¹ * w = w * ((g : G)⁻¹ * x * ((g : G)⁻¹)⁻¹)
    rw [inv_inv]
    exact h
  have hE'z := isElemAbelian_sup_zpowers (isElemAbelian_map hEab _) hw2 hE'w
  have hcard := hmax w hword hJw _ (sup_le hE'C (zpowers_le.mpr hwC)) hE'z
    (mem_sup_right (mem_zpowers w))
  rw [← hk]
  calc Nat.card E = Nat.card E' := (card_map_of_injective (MulAut.conj _).injective).symm
    _ ≤ Nat.card ↥(E' ⊔ zpowers w) := card_le_of_le le_sup_left
    _ ≤ Nat.card A := hcard

end Components

end CFSG.LocalAnalysis.ComponentInitial
