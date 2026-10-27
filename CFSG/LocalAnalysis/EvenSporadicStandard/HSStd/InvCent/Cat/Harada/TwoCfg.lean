module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.Step1
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed
open scoped commutatorElement

section Cfg

variable {G : Type*} [Group G]

theorem mem_sup_iff_of_commute {H K : Subgroup G} (h : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) {x : G} :
    x ∈ H ⊔ K ↔ ∃ a ∈ H, ∃ b ∈ K, a * b = x := by
  have hcomm : ∀ (m : H) (n : K), Commute (H.subtype m) (K.subtype n) :=
    fun m n => h m m.2 n n.2
  have hr := MonoidHom.noncommCoprod_range H.subtype K.subtype hcomm
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hr
  rw [← hr]
  constructor
  · rintro ⟨⟨m, n⟩, rfl⟩
    exact ⟨m, m.2, n, n.2, by rw [MonoidHom.noncommCoprod_apply]; rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), by rw [MonoidHom.noncommCoprod_apply]; rfl⟩

abbrev fourGroup (t v : G) : Subgroup G := zpowers t ⊔ zpowers v

structure TwoCfg (t v : G) (J : Subgroup G) : Prop where
  ht : orderOf t = 2
  hv : v * v = 1
  hJ : Nonempty (↥J ≃* Equiv.Perm (Fin 5))
  hdisj : fourGroup t v ⊓ J = ⊥
  hcomm : ∀ a ∈ fourGroup t v, ∀ b ∈ J, a * b = b * a
  hC : centralizer ({t} : Set G) = fourGroup t v ⊔ J
  hCv : centralizer ({v} : Set G) = centralizer ({t} : Set G)
  hCtv : centralizer ({t * v} : Set G) = centralizer ({t} : Set G)

theorem centralizer_singleton_one : centralizer ({1} : Set G) = ⊤ :=
  eq_top_iff.2 fun x _ => mem_centralizer_singleton_iff.2 (by simp)

namespace TwoCfg

variable {t v : G} {J : Subgroup G} (h : TwoCfg t v J)

include h

theorem t_sq : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two h.ht

theorem t_ne_one : t ≠ 1 := ne_one_of_orderOf_eq_two h.ht

theorem tv_comm : t * v = v * t := by
  have h1 : v ∈ centralizer ({v} : Set G) := mem_centralizer_singleton_iff.2 rfl
  rw [h.hCv] at h1
  exact (mem_centralizer_singleton_iff.1 h1).symm

theorem v_ne_one (htop : centralizer ({t} : Set G) ≠ ⊤) : v ≠ 1 := by
  rintro rfl
  apply htop
  rw [← h.hCv, centralizer_singleton_one]

theorem v_ne_t (htop : centralizer ({t} : Set G) ≠ ⊤) : v ≠ t := by
  rintro rfl
  apply htop
  rw [← h.hCtv, h.t_sq, centralizer_singleton_one]

theorem tv_ne_one (htop : centralizer ({t} : Set G) ≠ ⊤) : t * v ≠ 1 := by
  intro h1
  apply h.v_ne_t htop
  have h2 : v = t⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [h2]
  exact inv_eq_of_mul_eq_one_right h.t_sq

theorem zpowers_comm : ∀ a ∈ zpowers t, ∀ b ∈ zpowers v, a * b = b * a := by
  intro a ha b hb
  rcases (mem_zpowers_iff_of_mul_self_eq_one h.t_sq).1 ha with rfl | rfl <;>
    rcases (mem_zpowers_iff_of_mul_self_eq_one h.hv).1 hb with rfl | rfl <;>
      first | simp | exact h.tv_comm

theorem mem_fourGroup {x : G} : x ∈ fourGroup t v ↔ x = 1 ∨ x = t ∨ x = v ∨ x = t * v := by
  rw [mem_sup_iff_of_commute h.zpowers_comm]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rcases (mem_zpowers_iff_of_mul_self_eq_one h.t_sq).1 ha with rfl | rfl <;>
      rcases (mem_zpowers_iff_of_mul_self_eq_one h.hv).1 hb with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, one_mem _, 1, one_mem _, one_mul 1⟩
    · exact ⟨x, mem_zpowers x, 1, one_mem _, mul_one x⟩
    · exact ⟨1, one_mem _, x, mem_zpowers x, one_mul x⟩
    · exact ⟨t, mem_zpowers t, v, mem_zpowers v, rfl⟩

theorem card_fourGroup (htop : centralizer ({t} : Set G) ≠ ⊤) :
    Nat.card (fourGroup t v) = 4 := by
  have hset : ((fourGroup t v : Subgroup G) : Set G) = {1, t, v, t * v} := by
    ext x
    simp only [SetLike.mem_coe, h.mem_fourGroup, Set.mem_insert_iff, Set.mem_singleton_iff]
  have h1t : (1 : G) ≠ t := h.t_ne_one.symm
  have h1v : (1 : G) ≠ v := (h.v_ne_one htop).symm
  have h1tv : (1 : G) ≠ t * v := (h.tv_ne_one htop).symm
  have htv : t ≠ v := (h.v_ne_t htop).symm
  have htt : t ≠ t * v := fun h' => h.v_ne_one htop (by simpa using h'.symm)
  have hvt : v ≠ t * v := fun h' => h.t_ne_one (by simpa using h'.symm)
  rw [show Nat.card (fourGroup t v) = Nat.card ↥((fourGroup t v : Subgroup G) : Set G) from rfl,
    Nat.card_coe_set_eq, hset, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_pair hvt]
  · simp [htt, htv]
  · simp [h1t, h1v, h1tv]

theorem fourGroup_central {a c : G} (ha : a ∈ fourGroup t v) (hc : c ∈ centralizer ({t} : Set G)) :
    a * c = c * a := by
  rw [h.mem_fourGroup] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · simp
  · exact (mem_centralizer_singleton_iff.1 hc).symm
  · rw [← h.hCv] at hc
    exact (mem_centralizer_singleton_iff.1 hc).symm
  · rw [← h.hCtv] at hc
    exact (mem_centralizer_singleton_iff.1 hc).symm

theorem fourGroup_le_centralizer : fourGroup t v ≤ centralizer ({t} : Set G) := by
  rw [h.hC]
  exact le_sup_left

theorem le_centralizer_J : J ≤ centralizer ({t} : Set G) := by
  rw [h.hC]
  exact le_sup_right

theorem card_J : Nat.card J = 120 := by
  obtain ⟨e⟩ := h.hJ
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem card_centralizer (htop : centralizer ({t} : Set G) ≠ ⊤) :
    Nat.card (centralizer ({t} : Set G)) = 480 := by
  have hcomm : ∀ (m : fourGroup t v) (n : J),
      Commute ((fourGroup t v).subtype m) (J.subtype n) :=
    fun m n => h.hcomm m m.2 n n.2
  have hinj : Function.Injective ((fourGroup t v).subtype.noncommCoprod J.subtype hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨Subgroup.subtype_injective _, Subgroup.subtype_injective _, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff.2 h.hdisj
  have hrange : ((fourGroup t v).subtype.noncommCoprod J.subtype hcomm).range =
      centralizer ({t} : Set G) := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype, h.hC]
  rw [← hrange, show Nat.card ↥((fourGroup t v).subtype.noncommCoprod J.subtype hcomm).range =
      Nat.card (Set.range ((fourGroup t v).subtype.noncommCoprod J.subtype hcomm)) from rfl,
    Nat.card_range_of_injective hinj, Nat.card_prod, h.card_fourGroup htop, h.card_J]

end TwoCfg

theorem commutator_central_mul_left {a x y : G} (hax : a * x = x * a) (hay : a * y = y * a) :
    ⁅a * x, y⁆ = ⁅x, y⁆ := by
  have hax' : Commute a x := hax
  have hay' : Commute a y := hay
  have hc : Commute a (x * y * x⁻¹) := (hax'.mul_right hay').mul_right hax'.inv_right
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc a * x * y * (x⁻¹ * a⁻¹) * y⁻¹ = (a * (x * y * x⁻¹)) * a⁻¹ * y⁻¹ := by group
    _ = ((x * y * x⁻¹) * a) * a⁻¹ * y⁻¹ := by rw [hc.eq]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commutator_central_mul_right {a x y : G} (hax : a * x = x * a) (hay : a * y = y * a) :
    ⁅x, a * y⁆ = ⁅x, y⁆ := by
  rw [← commutatorElement_inv, commutator_central_mul_left hay hax, commutatorElement_inv]

@[expose] def embJ {B : Type*} [Group B] (J : Subgroup G) (e : ↥J ≃* B) : B →* G :=
  J.subtype.comp e.symm.toMonoidHom

theorem embJ_apply {B : Type*} [Group B] (J : Subgroup G) (e : ↥J ≃* B) (b : B) :
    embJ J e b = (e.symm b : G) := rfl

theorem embJ_injective {B : Type*} [Group B] (J : Subgroup G) (e : ↥J ≃* B) :
    Function.Injective (embJ J e) :=
  J.subtype_injective.comp e.symm.injective

theorem embJ_mem {B : Type*} [Group B] (J : Subgroup G) (e : ↥J ≃* B) (b : B) :
    embJ J e b ∈ J := (e.symm b).2

theorem embJ_range {B : Type*} [Group B] (J : Subgroup G) (e : ↥J ≃* B) :
    (embJ J e).range = J := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact embJ_mem J e b
  · intro hx
    exact ⟨e ⟨x, hx⟩, by rw [embJ_apply, MulEquiv.symm_apply_apply]⟩

theorem commutator_eq_map_alt (J : Subgroup G) (e : ↥J ≃* Equiv.Perm (Fin 5)) :
    ⁅J, J⁆ = (alternatingGroup (Fin 5)).map (embJ J e) := by
  rw [← alternatingGroup.commutator_perm_eq (α := Fin 5) (by simp), _root_.commutator_def,
    Subgroup.map_commutator, Subgroup.map_top, embJ_range]

namespace TwoCfg

variable {t v : G} {J : Subgroup G} (h : TwoCfg t v J)

include h

theorem centralizerDerived_eq (htop : centralizer ({t} : Set G) ≠ ⊤) :
    centralizerDerived t = ⁅J, J⁆ := by
  have hCC : centralizerDerived t =
      ⁅centralizer ({t} : Set G), centralizer ({t} : Set G)⁆ :=
    Subgroup.map_subtype_commutator _
  rw [hCC]
  refine le_antisymm ?_ (Subgroup.commutator_mono h.le_centralizer_J h.le_centralizer_J)
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  have hx' := hx
  have hy' := hy
  rw [h.hC] at hx' hy'
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute h.hcomm).1 hx'
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_sup_iff_of_commute h.hcomm).1 hy'
  have hbC : b ∈ centralizer ({t} : Set G) := h.le_centralizer_J hb
  have hdC : d ∈ centralizer ({t} : Set G) := h.le_centralizer_J hd
  rw [commutator_central_mul_left (h.fourGroup_central ha hbC) (h.fourGroup_central ha hy),
    commutator_central_mul_right (h.fourGroup_central hc hbC) (h.fourGroup_central hc hdC)]
  exact Subgroup.commutator_mem_commutator hb hd

end TwoCfg

end Cfg

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
