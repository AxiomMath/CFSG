module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Prelim
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Adapters.LieModelSimple
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

structure GomiU42Setup (B : Type) [Group B] [Finite B] (e t : B) (J₀ E₂ : Subgroup B) : Prop where
  kGroup : CFSG.SectionRank.IsKGroupCat B
  e_central : ∀ y : B, y * e = e * y
  orderOf_e : orderOf e = 3
  t_sq : t * t = 1
  t_ne_one : t ≠ 1
  lieModel : CFSG.Blueprint.LieModel J₀ .PSU 4 2 1
  le_centralizer : J₀ ≤ centralizer ({t} : Set B)
  inf_e : zpowers e ⊓ J₀ = ⊥
  centralizer_eq : centralizer ({t} : Set B) = zpowers t ⊔ (zpowers e ⊔ J₀)
  inf_t : zpowers t ⊓ (zpowers e ⊔ J₀) = ⊥
  two_pow_dvd : 2 ^ 9 ∣ Nat.card B
  elementary : CFSG.IsElementaryAbelian 2 E₂
  card_E₂ : Nat.card E₂ = 2 ^ 8
  mem_normalizer : t ∈ normalizer (E₂ : Set B)
  isPGroup_sup : IsPGroup 2 ↥(E₂ ⊔ zpowers t)
  card_inf : Nat.card (E₂ ⊓ centralizer ({t} : Set B) : Subgroup B) = 2 ^ 4
  inf_le : E₂ ⊓ centralizer ({t} : Set B) ≤ J₀

namespace GomiU42Setup

variable {B : Type} [Group B] [Finite B] {e t : B} {J₀ E₂ : Subgroup B}

theorem zpowers_e_le_center (h : GomiU42Setup B e t J₀ E₂) : zpowers e ≤ center B := by
  rw [zpowers_le, mem_center_iff]
  exact fun y => h.e_central y

theorem normal_zpowers_e (h : GomiU42Setup B e t J₀ E₂) : (zpowers e).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h1 : g * n = n * g := mem_center_iff.1 (h.zpowers_e_le_center hn) g
  have : g * n * g⁻¹ = n := by
    calc g * n * g⁻¹ = (n * g) * g⁻¹ := by rw [h1]
      _ = n := by group
  rw [this]
  exact hn

theorem card_sup_mul_card_inf_of_le_normalizer' {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) (hK : K ≤ normalizer (H : Set G)) :
    Nat.card (H ⊔ K : Subgroup G) * Nat.card (H ⊓ K : Subgroup G) =
      Nat.card H * Nat.card K := by
  have := normal_subgroupOf_of_le_normalizer hK
  have := normal_subgroupOf_sup_of_le_normalizer hK
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient K H hK
  have h1 := card_eq_card_quotient_mul_card_subgroup (H.subgroupOf K)
  have h2 := card_eq_card_quotient_mul_card_subgroup (H.subgroupOf (K ⊔ H))
  have h3 : Nat.card (H.subgroupOf K) = Nat.card (H ⊓ K : Subgroup G) := by
    rw [← inf_subgroupOf_right]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
  have h4 : Nat.card (H.subgroupOf (K ⊔ H)) = Nat.card H :=
    Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv
  have h5 : Nat.card (↥K ⧸ H.subgroupOf K) = Nat.card (↥(K ⊔ H) ⧸ H.subgroupOf (K ⊔ H)) :=
    Nat.card_congr e.toEquiv
  rw [sup_comm, h2, h4, ← h5, h1, h3]
  ring

@[expose] noncomputable def equivMapOfInjOn {G H : Type*} [Group G] [Group H] (f : G →* H)
    (K : Subgroup G) (hf : Set.InjOn f K) : K ≃* K.map f :=
  MulEquiv.ofBijective (f.subgroupMap K)
    ⟨fun x y hxy => Subtype.ext (hf x.2 y.2 (congrArg Subtype.val hxy)),
      f.subgroupMap_surjective K⟩

theorem card_map_of_injOn {G H : Type*} [Group G] [Group H] (f : G →* H)
    (K : Subgroup G) (hf : Set.InjOn f K) : Nat.card (K.map f) = Nat.card K :=
  (Nat.card_congr (equivMapOfInjOn f K hf).toEquiv).symm

section Quot

variable [(zpowers e).Normal]

theorem injOn_of_isPGroup (h : GomiU42Setup B e t J₀ E₂) {P : Subgroup B} (hP : IsPGroup 2 P) :
    Set.InjOn (QuotientGroup.mk' (zpowers e)) P := by
  intro x hx y hy hxy
  have hz : x⁻¹ * y ∈ zpowers e := by
    have := (QuotientGroup.eq (s := zpowers e)).1 ((QuotientGroup.mk'_apply _ _).trans
      ((congrArg (fun z => z) hxy).trans (QuotientGroup.mk'_apply _ _).symm))
    exact this
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hz
  have hz3 : (x⁻¹ * y) ^ 3 = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← h.orderOf_e,
      pow_orderOf_eq_one, one_zpow]
  obtain ⟨m, hm⟩ := hP ⟨x⁻¹ * y, mul_mem (inv_mem hx) hy⟩
  have hm' : (x⁻¹ * y) ^ (2 ^ m) = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hd : orderOf (x⁻¹ * y) ∣ Nat.gcd 3 (2 ^ m) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hz3) (orderOf_dvd_of_pow_eq_one hm')
  have hc : Nat.Coprime 3 (2 ^ m) := Nat.Coprime.pow_right _ (by norm_num)
  rw [hc.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact inv_mul_eq_one.1 hd

theorem mk_eq_iff {x y : B} :
    QuotientGroup.mk' (zpowers e) x = QuotientGroup.mk' (zpowers e) y ↔ x⁻¹ * y ∈ zpowers e :=
  QuotientGroup.eq

theorem card_B_eq (h : GomiU42Setup B e t J₀ E₂) :
    Nat.card B = Nat.card (B ⧸ zpowers e) * 3 := by
  rw [card_eq_card_quotient_mul_card_subgroup (zpowers e), Nat.card_zpowers, h.orderOf_e]

theorem two_pow_dvd_card_quot (h : GomiU42Setup B e t J₀ E₂) :
    2 ^ 9 ∣ Nat.card (B ⧸ zpowers e) := by
  have := h.two_pow_dvd
  rw [card_B_eq h] at this
  exact Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) this

theorem injOn_J₀ (h : GomiU42Setup B e t J₀ E₂) :
    Set.InjOn (QuotientGroup.mk' (zpowers e)) J₀ := by
  intro x hx y hy hxy
  have hz : x⁻¹ * y ∈ zpowers e := mk_eq_iff.1 hxy
  have hx' : x ∈ J₀ := hx
  have hy' : y ∈ J₀ := hy
  have hz' : x⁻¹ * y ∈ zpowers e ⊓ J₀ := mem_inf.2 ⟨hz, mul_mem (inv_mem hx') hy'⟩
  rw [h.inf_e, mem_bot] at hz'
  exact inv_mul_eq_one.1 hz'

theorem not_mem_zpowers_e (h : GomiU42Setup B e t J₀ E₂) : t ∉ zpowers e := by
  intro ht
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 ht
  have h3 : t ^ 3 = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← h.orderOf_e,
      pow_orderOf_eq_one, one_zpow]
  have h2 : t ^ 2 = 1 := by rw [pow_two]; exact h.t_sq
  have : t = 1 := by
    calc t = t ^ 3 * (t ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; group
  exact h.t_ne_one this

theorem orderOf_mk_t (h : GomiU42Setup B e t J₀ E₂) :
    orderOf (QuotientGroup.mk' (zpowers e) t) = 2 := by
  have hsq : QuotientGroup.mk' (zpowers e) t ^ 2 = 1 := by
    rw [← map_pow, pow_two, h.t_sq, map_one]
  have hne : QuotientGroup.mk' (zpowers e) t ≠ 1 := by
    intro h1
    apply h.not_mem_zpowers_e
    exact (QuotientGroup.eq_one_iff t).1 h1
  exact orderOf_eq_prime hsq hne

theorem isSimpleGroup_J₀ (h : GomiU42Setup B e t J₀ E₂) : IsSimpleGroup J₀ :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h.lieModel

theorem card_J₀ (h : GomiU42Setup B e t J₀ E₂) : Nat.card J₀ = 25920 := by
  have := CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical
    (h.lieModel.statedClassicalModel (by decide))
  rw [this]
  decide

theorem nonabelian_J₀ (h : GomiU42Setup B e t J₀ E₂) : ∃ x y : J₀, x * y ≠ y * x := by
  by_contra hne
  push Not at hne
  haveI := h.isSimpleGroup_J₀
  letI : CommGroup J₀ := { (inferInstance : Group J₀) with mul_comm := fun x y => (hne x y) }
  have hp := IsSimpleGroup.prime_card (α := J₀)
  rw [h.card_J₀] at hp
  exact absurd hp (by norm_num)

noncomputable def equivJb (h : GomiU42Setup B e t J₀ E₂) :
    J₀ ≃* J₀.map (QuotientGroup.mk' (zpowers e)) :=
  equivMapOfInjOn _ J₀ h.injOn_J₀

theorem isSimpleGroup_Jb (h : GomiU42Setup B e t J₀ E₂) :
    IsSimpleGroup (J₀.map (QuotientGroup.mk' (zpowers e))) := by
  haveI := h.isSimpleGroup_J₀
  exact h.equivJb.symm.isSimpleGroup

theorem nonabelian_Jb (h : GomiU42Setup B e t J₀ E₂) :
    ∃ x y : J₀.map (QuotientGroup.mk' (zpowers e)), x * y ≠ y * x := by
  obtain ⟨x, y, hxy⟩ := h.nonabelian_J₀
  refine ⟨h.equivJb x, h.equivJb y, fun h' => hxy ?_⟩
  have h'' := congrArg h.equivJb.symm h'
  simpa only [map_mul, MulEquiv.symm_apply_apply] using h''

theorem card_Jb (h : GomiU42Setup B e t J₀ E₂) :
    Nat.card (J₀.map (QuotientGroup.mk' (zpowers e))) = 25920 := by
  rw [card_map_of_injOn _ J₀ h.injOn_J₀]
  exact h.card_J₀

theorem map_zpowers_e : (zpowers e).map (QuotientGroup.mk' (zpowers e)) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨x, hx, rfl⟩
  exact (QuotientGroup.eq_one_iff x).2 hx

theorem centralizer_bar (h : GomiU42Setup B e t J₀ E₂) :
    centralizer ({QuotientGroup.mk' (zpowers e) t} : Set (B ⧸ zpowers e)) =
      (centralizer ({t} : Set B)).map (QuotientGroup.mk' (zpowers e)) :=
  centralizer_quotient_zpowers h.e_central h.orderOf_e h.t_sq

theorem centralizer_bar_eq (h : GomiU42Setup B e t J₀ E₂) :
    centralizer ({QuotientGroup.mk' (zpowers e) t} : Set (B ⧸ zpowers e)) =
      zpowers (QuotientGroup.mk' (zpowers e) t) ⊔ J₀.map (QuotientGroup.mk' (zpowers e)) := by
  rw [h.centralizer_bar, h.centralizer_eq, Subgroup.map_sup, Subgroup.map_sup, map_zpowers_e,
    bot_sup_eq, MonoidHom.map_zpowers]

theorem inf_bar_eq_bot (h : GomiU42Setup B e t J₀ E₂) :
    zpowers (QuotientGroup.mk' (zpowers e) t) ⊓ J₀.map (QuotientGroup.mk' (zpowers e)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx1
  obtain ⟨j, hj, hjx⟩ := hx2
  have hz : (t ^ i)⁻¹ * j ∈ zpowers e := by
    apply mk_eq_iff.1
    rw [map_zpow]
    exact hjx.symm
  have ht : t ^ i ∈ zpowers t ⊓ (zpowers e ⊔ J₀) := by
    refine mem_inf.2 ⟨mem_zpowers_iff.2 ⟨i, rfl⟩, ?_⟩
    have : t ^ i = j * ((t ^ i)⁻¹ * j)⁻¹ := by group
    rw [this]
    exact mul_mem (mem_sup_right hj) (inv_mem (mem_sup_left hz))
  rw [h.inf_t, mem_bot] at ht
  rw [← map_zpow, ht, map_one]
  exact one_mem _

theorem isKGroupCat_F (h : GomiU42Setup B e t J₀ E₂) :
    CFSG.SectionRank.IsKGroupCat (B ⧸ zpowers e) :=
  h.kGroup.quotient (zpowers e)

theorem card_centralizer_bar (h : GomiU42Setup B e t J₀ E₂) :
    Nat.card (centralizer ({QuotientGroup.mk' (zpowers e) t} : Set (B ⧸ zpowers e))) =
      51840 := by
  rw [h.centralizer_bar_eq]
  have hn : zpowers (QuotientGroup.mk' (zpowers e) t) ≤
      normalizer ((J₀.map (QuotientGroup.mk' (zpowers e)) : Subgroup (B ⧸ zpowers e)) :
        Set (B ⧸ zpowers e)) := by
    rw [zpowers_le]
    apply centralizer_le_normalizer
    rw [mem_centralizer_iff]
    rintro _ ⟨j, hj, rfl⟩
    have hjt : j * t = t * j := mem_centralizer_singleton_iff.1 (h.le_centralizer hj)
    rw [← map_mul, ← map_mul, hjt]
  have key := card_sup_mul_card_inf_of_le_normalizer' (J₀.map (QuotientGroup.mk' (zpowers e)))
    (zpowers (QuotientGroup.mk' (zpowers e) t)) hn
  rw [sup_comm, inf_comm, h.inf_bar_eq_bot, Subgroup.card_bot, h.card_Jb, Nat.card_zpowers,
    h.orderOf_mk_t] at key
  omega

theorem sylow_not_central (h : GomiU42Setup B e t J₀ E₂) :
    ∀ S : Sylow 2 (B ⧸ zpowers e), QuotientGroup.mk' (zpowers e) t ∈ S →
      ∃ s ∈ S, s * QuotientGroup.mk' (zpowers e) t ≠ QuotientGroup.mk' (zpowers e) t * s :=
  exists_not_comm_of_dvd h.two_pow_dvd_card_quot (by rw [h.card_centralizer_bar]; norm_num)

theorem exists_four_group (h : GomiU42Setup B e t J₀ E₂) :
    ∃ E4 : Subgroup (B ⧸ zpowers e), E4 ≤ J₀.map (QuotientGroup.mk' (zpowers e)) ∧
      CFSG.IsElementaryAbelian 2 E4 ∧ Nat.card E4 = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := h.elementary
  set C : Subgroup B := E₂ ⊓ centralizer ({t} : Set B) with hC
  have hCE : C ≤ E₂ := inf_le_left
  have hcomm : ∀ x ∈ E₂, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := E₂)).comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ E₂, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E₂) x hx
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := C) 2 (n := 2)
    (by rw [hC, h.card_inf]; norm_num)
  set P' : Subgroup B := P.map C.subtype with hP'
  have hP'C : P' ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hP'E : P' ≤ E₂ := hP'C.trans hCE
  have hP'p : IsPGroup 2 ↥P' := (IsElementaryAbelian.isPGroup 2 E₂).to_le hP'E
  refine ⟨P'.map (QuotientGroup.mk' (zpowers e)), Subgroup.map_mono (hP'C.trans h.inf_le), ?_, ?_⟩
  · refine IsElementaryAbelian.two_of_forall_mul_self ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x (hP'E hx) y (hP'E hy)]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hsq x (hP'E hx), map_one]
  · rw [card_map_of_injOn _ P' (h.injOn_of_isPGroup hP'p), hP',
      card_map_of_injective C.subtype_injective, hP]
    norm_num

end Quot

end GomiU42Setup

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
