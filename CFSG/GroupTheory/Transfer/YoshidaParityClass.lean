module

public import CFSG.GroupTheory.Transfer.YoshidaParity

public import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G] [Finite G]

theorem card_conj_preimage_eq (t : G) (S : Set G) :
    Nat.card {g : G // g⁻¹ * t * g ∈ S} =
      Nat.card (Subgroup.centralizer ({t} : Set G)) *
        Set.ncard {y : G | IsConj t y ∧ y ∈ S} := by
  classical
  let T : Set G := {y | IsConj t y ∧ y ∈ S}
  have hex : ∀ y : T, ∃ g : G, g⁻¹ * t * g = y := by
    intro y
    obtain ⟨c, hc⟩ := isConj_iff.mp y.2.1
    exact ⟨c⁻¹, by simpa using hc⟩
  choose gy hgy using hex
  have hcent : ∀ c g : G, c * t = t * c → (c * g)⁻¹ * t * (c * g) = g⁻¹ * t * g := by
    intro c g hc
    have h : c⁻¹ * t * c = t := by
      calc c⁻¹ * t * c = c⁻¹ * (t * c) := mul_assoc _ _ _
        _ = c⁻¹ * (c * t) := by rw [hc]
        _ = t := inv_mul_cancel_left c t
    calc (c * g)⁻¹ * t * (c * g) = g⁻¹ * (c⁻¹ * t * c) * g := by group
      _ = g⁻¹ * t * g := by rw [h]
  let Ψ : ↥(Subgroup.centralizer ({t} : Set G)) × ↥T → {g : G // g⁻¹ * t * g ∈ S} := fun p =>
    ⟨p.1.1 * gy p.2, by
      show (p.1.1 * gy p.2)⁻¹ * t * (p.1.1 * gy p.2) ∈ S
      rw [hcent _ _ (Subgroup.mem_centralizer_singleton_iff.mp p.1.2), hgy]
      exact p.2.2.2⟩
  have hinj : Function.Injective Ψ := by
    intro p q hpq
    have h : p.1.1 * gy p.2 = q.1.1 * gy q.2 := congrArg Subtype.val hpq
    have hy : (p.2 : G) = q.2 := by
      have e1 := hcent _ (gy p.2) (Subgroup.mem_centralizer_singleton_iff.mp p.1.2)
      have e2 := hcent _ (gy q.2) (Subgroup.mem_centralizer_singleton_iff.mp q.1.2)
      rw [hgy] at e1 e2
      rw [← e1, ← e2, h]
    have hyy : p.2 = q.2 := Subtype.ext hy
    have hc : p.1.1 = q.1.1 := by
      rw [hyy] at h
      exact mul_right_cancel h
    exact Prod.ext (Subtype.ext hc) hyy
  have hsurj : Function.Surjective Ψ := by
    rintro ⟨g, hg⟩
    have hgT : g⁻¹ * t * g ∈ T :=
      ⟨isConj_iff.mpr ⟨g⁻¹, by simp⟩, hg⟩
    set y : T := ⟨g⁻¹ * t * g, hgT⟩ with hy
    have hcent' : g * (gy y)⁻¹ * t = t * (g * (gy y)⁻¹) := by
      have h := hgy y
      have h' : g⁻¹ * t * g = (gy y)⁻¹ * t * gy y := h.symm
      calc g * (gy y)⁻¹ * t = g * (gy y)⁻¹ * t * (gy y * g⁻¹) * (g * (gy y)⁻¹) := by group
        _ = g * ((gy y)⁻¹ * t * gy y) * g⁻¹ * (g * (gy y)⁻¹) := by group
        _ = g * (g⁻¹ * t * g) * g⁻¹ * (g * (gy y)⁻¹) := by rw [← h']
        _ = t * (g * (gy y)⁻¹) := by group
    refine ⟨(⟨g * (gy y)⁻¹, Subgroup.mem_centralizer_singleton_iff.mpr hcent'⟩, y), ?_⟩
    apply Subtype.ext
    show g * (gy y)⁻¹ * gy y = g
    group
  rw [← Nat.card_coe_set_eq T, ← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective Ψ ⟨hinj, hsurj⟩)).symm

theorem card_orbit_centralizer_quotient (H : Subgroup G) (t g : G) :
    Nat.card (MulAction.orbit ↥(Subgroup.centralizer ({t} : Set G)) ((g : G ⧸ H))) =
      (H ⊓ Subgroup.centralizer ({g⁻¹ * t * g} : Set G)).relIndex
        (Subgroup.centralizer ({g⁻¹ * t * g} : Set G)) := by
  classical
  set C := Subgroup.centralizer ({t} : Set G) with hC
  set C' := Subgroup.centralizer ({g⁻¹ * t * g} : Set G) with hC'
  let φ : G ≃* G := MulAut.conj g
  have hstab : MulAction.stabilizer ↥C ((g : G ⧸ H)) = (H.map φ.toMonoidHom).subgroupOf C := by
    ext c
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv]
    change ((c : G) • (g : G ⧸ H) = (g : G ⧸ H)) ↔ _
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
    have h : (c * g)⁻¹ * g = (g⁻¹ * (c : G) * g)⁻¹ := by group
    rw [h, inv_mem_iff]
    rfl
  have hCmap : C'.map φ.toMonoidHom = C := by
    ext x
    rw [Subgroup.mem_map_equiv, hC', hC, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    change g⁻¹ * x * g * (g⁻¹ * t * g) = g⁻¹ * t * g * (g⁻¹ * x * g) ↔ x * t = t * x
    constructor
    · intro hx
      calc x * t = g * (g⁻¹ * x * g * (g⁻¹ * t * g)) * g⁻¹ := by group
        _ = g * (g⁻¹ * t * g * (g⁻¹ * x * g)) * g⁻¹ := by rw [hx]
        _ = t * x := by group
    · intro hx
      calc g⁻¹ * x * g * (g⁻¹ * t * g) = g⁻¹ * (x * t) * g := by group
        _ = g⁻¹ * (t * x) * g := by rw [hx]
        _ = g⁻¹ * t * g * (g⁻¹ * x * g) := by group
  have h1 : Nat.card (MulAction.orbit ↥C ((g : G ⧸ H))) =
      (MulAction.stabilizer ↥C ((g : G ⧸ H))).index := by
    rw [MulAction.index_stabilizer, Nat.card_coe_set_eq]
  rw [h1, hstab]
  change (H.map φ.toMonoidHom).relIndex C = _
  rw [← hCmap, Subgroup.relIndex_map_map_of_injective H C' φ.injective, Subgroup.inf_relIndex_right]

end CFSG.GroupTheory
