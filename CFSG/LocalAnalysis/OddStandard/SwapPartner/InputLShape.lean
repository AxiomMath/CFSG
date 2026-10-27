module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

structure SwapShape {X : Type*} [Group X] (t : X) (Sg V : Subgroup X) : Prop where
  order_eq : orderOf t = 2
  iso_sg : Nonempty (Sg ≃* Equiv.Perm (Fin 8))
  iso_v : Nonempty (V ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
  cent_eq : centralizer ({t} : Set X) = V ⊔ Sg
  comm_eq : ⁅V, Sg⁆ = ⊥
  inf_eq : V ⊓ Sg = ⊥

namespace SwapShape

variable {X : Type*} [Group X] {t : X} {Sg V : Subgroup X}

theorem sg_le_centralizer (h : SwapShape t Sg V) : Sg ≤ centralizer ({t} : Set X) := by
  rw [h.cent_eq]
  exact le_sup_right

theorem v_le_centralizer (h : SwapShape t Sg V) : V ≤ centralizer ({t} : Set X) := by
  rw [h.cent_eq]
  exact le_sup_left

theorem mul_comm_of_mem_v (h : SwapShape t Sg V) {a b : X} (ha : a ∈ V) (hb : b ∈ V) :
    a * b = b * a := by
  obtain ⟨eV⟩ := h.iso_v
  have key : (⟨a * b, V.mul_mem ha hb⟩ : V) = ⟨b * a, V.mul_mem hb ha⟩ := by
    apply eV.injective
    show eV (⟨a, ha⟩ * ⟨b, hb⟩) = eV (⟨b, hb⟩ * ⟨a, ha⟩)
    rw [map_mul, map_mul]
    exact mul_comm _ _
  exact Subtype.ext_iff.mp key

theorem mul_comm_of_mem_v_of_mem_sg (h : SwapShape t Sg V) {a b : X} (ha : a ∈ V) (hb : b ∈ Sg) :
    a * b = b * a := by
  have hmem : ⁅a, b⁆ ∈ (⁅V, Sg⁆ : Subgroup X) := Subgroup.commutator_mem_commutator ha hb
  rw [h.comm_eq, Subgroup.mem_bot] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hmem

theorem mul_comm_of_mem_v_of_mem_centralizer (h : SwapShape t Sg V) {a b : X} (ha : a ∈ V)
    (hb : b ∈ centralizer ({t} : Set X)) : a * b = b * a := by
  have hV : V ≤ Subgroup.centralizer ({a} : Set X) := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h.mul_comm_of_mem_v hv ha
  have hS : Sg ≤ Subgroup.centralizer ({a} : Set X) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (h.mul_comm_of_mem_v_of_mem_sg ha hs).symm
  have hle : centralizer ({t} : Set X) ≤ Subgroup.centralizer ({a} : Set X) := by
    rw [h.cent_eq]
    exact sup_le hV hS
  have hb' : b ∈ Subgroup.centralizer ({a} : Set X) := hle hb
  rw [Subgroup.mem_centralizer_singleton_iff] at hb'
  exact hb'.symm

private noncomputable def mulHom (h : SwapShape t Sg V) : V × Sg →* X :=
  MonoidHom.noncommCoprod V.subtype Sg.subtype
    (fun v s => (commute_iff_eq _ _).mpr (h.mul_comm_of_mem_v_of_mem_sg v.2 s.2))

private theorem mulHom_range (h : SwapShape t Sg V) : (mulHom h).range = V ⊔ Sg := by
  rw [mulHom, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]

private theorem mulHom_injective (h : SwapShape t Sg V) : Function.Injective (mulHom h) := by
  rw [mulHom, MonoidHom.noncommCoprod_injective]
  refine ⟨V.subtype_injective, Sg.subtype_injective, ?_⟩
  rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
  exact h.inf_eq

private theorem exists_mul_of_mem_centralizer (h : SwapShape t Sg V) {c : X}
    (hc : c ∈ centralizer ({t} : Set X)) : ∃ v ∈ V, ∃ s ∈ Sg, c = v * s := by
  have hc' : c ∈ (mulHom h).range := by
    rw [mulHom_range h, ← h.cent_eq]
    exact hc
  obtain ⟨⟨v, s⟩, hvs⟩ := MonoidHom.mem_range.mp hc'
  refine ⟨v, v.2, s, s.2, ?_⟩
  rw [← hvs]
  simp [mulHom]

theorem card_v (h : SwapShape t Sg V) : Nat.card V = 4 := by
  obtain ⟨eV⟩ := h.iso_v
  calc Nat.card V
      = Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := Nat.card_congr eV.toEquiv
    _ = Nat.card (Multiplicative (ZMod 2)) * Nat.card (Multiplicative (ZMod 2)) :=
        Nat.card_prod _ _
    _ = 4 := by
        rw [Nat.card_eq_fintype_card]
        simp [ZMod.card]

theorem card_sg (h : SwapShape t Sg V) : Nat.card Sg = 40320 := by
  obtain ⟨eS⟩ := h.iso_sg
  rw [Nat.card_congr eS.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num [Nat.factorial]

theorem card_centralizer (h : SwapShape t Sg V) : Nat.card (centralizer ({t} : Set X)) = 161280 := by
  let f : V × Sg → (V ⊔ Sg : Subgroup X) :=
    fun p => ⟨mulHom h p, by rw [← mulHom_range h]; exact MonoidHom.mem_range.mpr ⟨p, rfl⟩⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro p q hpq
      exact mulHom_injective h (Subtype.ext_iff.mp hpq)
    · intro y
      obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp (by rw [mulHom_range h]; exact y.2)
      exact ⟨p, Subtype.ext_iff.mpr hp⟩
  have hcard : Nat.card (V ⊔ Sg : Subgroup X) = Nat.card (V × Sg) :=
    (Nat.card_congr (Equiv.ofBijective f hbij)).symm
  rw [h.cent_eq, hcard, Nat.card_prod, h.card_v, h.card_sg]

theorem commutator_sg_le_centralizer (h : SwapShape t Sg V) :
    ⁅Sg, Sg⁆ ≤ centralizer ({t} : Set X) :=
  (Subgroup.commutator_le_self Sg).trans h.sg_le_centralizer

private theorem commutatorElement_mul_mul_of_commute {G : Type*} [Group G] {z₁ z₂ a b : G}
    (h₁a : Commute z₁ a) (h₁b : Commute z₁ b) (h₂a : Commute z₂ a) (h₂b : Commute z₂ b)
    (h₁₂ : Commute z₁ z₂) : ⁅z₁ * a, z₂ * b⁆ = ⁅a, b⁆ := by
  have hcomm : ∀ {z : G}, Commute z a → Commute z b → Commute z ⁅a, b⁆ := by
    intro z hza hzb
    rw [commutatorElement_def]
    exact ((hza.mul_right hzb).mul_right hza.inv_right).mul_right hzb.inv_right
  have h2 : ⁅a, z₂ * b⁆ = ⁅a, b⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj, h₂a.symm.commutator_eq, one_mul,
      (hcomm h₂a h₂b).mul_inv_cancel]
  rw [commutatorElement_mul_left_eq_conj_mul, h2, (h₁₂.mul_right h₁b).commutator_eq, mul_one,
    (hcomm h₁a h₁b).mul_inv_cancel]

private noncomputable def commutatorEquivAlt (h : SwapShape t Sg V) :
    (⁅Sg, Sg⁆ : Subgroup X) ≃* alternatingGroup (Fin 8) := by
  let eS : Sg ≃* Equiv.Perm (Fin 8) := Classical.choice h.iso_sg
  have hmap : (_root_.commutator Sg).map eS.toMonoidHom = alternatingGroup (Fin 8) := by
    rw [_root_.commutator_def, Subgroup.map_commutator]
    simp only [Subgroup.map_top_of_surjective eS.toMonoidHom eS.surjective]
    rw [← _root_.commutator_def]
    exact alternatingGroup.commutator_perm_eq (by simp)
  exact ((Subgroup.equivMapOfInjective (_root_.commutator Sg) Sg.subtype
        Sg.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator Sg))).symm.trans
    ((Subgroup.equivMapOfInjective (_root_.commutator Sg) eS.toMonoidHom
        eS.injective).trans
      (MulEquiv.subgroupCongr hmap))

theorem card_commutator_sg (h : SwapShape t Sg V) : Nat.card (⁅Sg, Sg⁆ : Subgroup X) = 20160 := by
  have hcardA : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  calc Nat.card (⁅Sg, Sg⁆ : Subgroup X) = Nat.card (alternatingGroup (Fin 8)) :=
        Nat.card_congr (commutatorEquivAlt h).toEquiv
    _ = 20160 := hcardA

theorem isSimpleGroup_commutator_sg (h : SwapShape t Sg V) : IsSimpleGroup (⁅Sg, Sg⁆ : Subgroup X) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  exact (commutatorEquivAlt h).isSimpleGroup

theorem commutator_centralizer_le (h : SwapShape t Sg V) :
    ⁅centralizer ({t} : Set X), centralizer ({t} : Set X)⁆ ≤ ⁅Sg, Sg⁆ := by
  rw [Subgroup.commutator_le]
  intro c₁ hc₁ c₂ hc₂
  obtain ⟨v₁, hv₁, s₁, hs₁, rfl⟩ := h.exists_mul_of_mem_centralizer hc₁
  obtain ⟨v₂, hv₂, s₂, hs₂, rfl⟩ := h.exists_mul_of_mem_centralizer hc₂
  have hv1s1 : Commute v₁ s₁ :=
    (commute_iff_eq _ _).mpr
      (h.mul_comm_of_mem_v_of_mem_centralizer hv₁ (h.sg_le_centralizer hs₁))
  have hv1s2 : Commute v₁ s₂ :=
    (commute_iff_eq _ _).mpr
      (h.mul_comm_of_mem_v_of_mem_centralizer hv₁ (h.sg_le_centralizer hs₂))
  have hv2s1 : Commute v₂ s₁ :=
    (commute_iff_eq _ _).mpr
      (h.mul_comm_of_mem_v_of_mem_centralizer hv₂ (h.sg_le_centralizer hs₁))
  have hv2s2 : Commute v₂ s₂ :=
    (commute_iff_eq _ _).mpr
      (h.mul_comm_of_mem_v_of_mem_centralizer hv₂ (h.sg_le_centralizer hs₂))
  have hv12 : Commute v₁ v₂ := (commute_iff_eq _ _).mpr (h.mul_comm_of_mem_v hv₁ hv₂)
  rw [commutatorElement_mul_mul_of_commute hv1s1 hv1s2 hv2s1 hv2s2 hv12]
  exact Subgroup.commutator_mem_commutator hs₁ hs₂

end SwapShape

end CFSG.OddStandard.AltStdSec.SwapPartner
