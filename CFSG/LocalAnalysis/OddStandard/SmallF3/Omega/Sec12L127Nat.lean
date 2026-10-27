module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127A5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126Nc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import Certificates.Data.A5

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

local instance sec127_decidableIsEvenVec {n : ℕ} (v : Fin n → ZMod 2) :
    Decidable (IsEvenVec v) :=
  inferInstanceAs (Decidable (∑ i, v i = 0))

theorem sec127_perm_decide :
    ∀ σ : Equiv.Perm (Fin 5), σ ∈ alternatingGroup (Fin 5) → σ ≠ 1 →
      (∀ v : Fin 5 → ZMod 2, IsEvenVec v → permVec σ (permVec σ v) = v) →
      ∀ v : Fin 5 → ZMod 2, IsEvenVec v → permVec σ v = v →
        ∃ w : Fin 5 → ZMod 2, IsEvenVec w ∧ permVec σ w + w = v := by
  decide +kernel

theorem sec127_exists_moved :
    ∃ v : Fin 5 → ZMod 2, IsEvenVec v ∧
      permVec (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) v ≠ v := by
  decide +kernel

theorem sec127_isEvenVec_permVec (σ : Equiv.Perm (Fin 5)) {v : Fin 5 → ZMod 2}
    (hv : IsEvenVec v) : IsEvenVec (permVec σ v) := by
  unfold IsEvenVec permVec at *
  rw [show (∑ i, (v ∘ ⇑σ.symm) i) = ∑ i, v i from Equiv.sum_comp σ.symm v]
  exact hv

structure Sec127NatCoord (V1 X : Subgroup G) (φ : (Fin 5 → ZMod 2) → G) : Prop where
  normalizes : X ≤ normalizer (V1 : Set G)
  mem : ∀ v, IsEvenVec v → φ v ∈ V1
  mul : ∀ v w, IsEvenVec v → IsEvenVec w → φ (v + w) = φ v * φ w
  inj : ∀ v, IsEvenVec v → φ v = 1 → v = 0
  surj : ∀ x ∈ V1, ∃ v, IsEvenVec v ∧ φ v = x
  act : ∀ h ∈ X, ∃ σ ∈ alternatingGroup (Fin 5),
    ∀ v, IsEvenVec v → h * φ v * h⁻¹ = φ (permVec σ v)
  onto : ∀ σ ∈ alternatingGroup (Fin 5), ∃ h ∈ X,
    ∀ v, IsEvenVec v → h * φ v * h⁻¹ = φ (permVec σ v)

theorem sec127_natCoord_of {V1 X : Subgroup G} (h : IsNatModA5 V1 ⊥ X) :
    ∃ φ : (Fin 5 → ZMod 2) → G, Sec127NatCoord V1 X φ := by
  obtain ⟨φ, -, -, hXV, -, hmem, hmul, hker, hsurj, hact, honto⟩ := h
  refine ⟨φ, hXV, hmem, fun v w hv hw => ?_, fun v hv h1 => ?_, fun x hx => ?_,
    fun h hh => ?_, fun σ hσ => ?_⟩
  · have := Subgroup.mem_bot.mp (hmul v w hv hw)
    exact (inv_mul_eq_one.mp this).symm
  · have : v ∈ ({0} : Set (Fin 5 → ZMod 2)) := (hker v hv).mp (Subgroup.mem_bot.mpr h1)
    exact this
  · obtain ⟨v, hv, h1⟩ := hsurj x hx
    exact ⟨v, hv, inv_mul_eq_one.mp (Subgroup.mem_bot.mp h1)⟩
  · obtain ⟨σ, hσ, h1⟩ := hact h hh
    exact ⟨σ, hσ, fun v hv => inv_mul_eq_one.mp (Subgroup.mem_bot.mp (h1 v hv))⟩
  · obtain ⟨h, hh, h1⟩ := honto σ hσ
    exact ⟨h, hh, fun v hv => inv_mul_eq_one.mp (Subgroup.mem_bot.mp (h1 v hv))⟩

namespace Sec127NatCoord

variable {V1 X : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}

theorem map_zero (hc : Sec127NatCoord V1 X φ) : φ 0 = 1 := by
  have h0 : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
  have h := hc.mul 0 0 h0 h0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem mul_self (hc : Sec127NatCoord V1 X φ) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    φ v * φ v = 1 := by
  have hsq : v + v = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (v i)
  rw [← hc.mul v v hv hv, hsq, hc.map_zero]

theorem eq_iff (hc : Sec127NatCoord V1 X φ) {a b : Fin 5 → ZMod 2} (ha : IsEvenVec a)
    (hb : IsEvenVec b) : φ a = φ b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have hab : IsEvenVec (a + b) := by
    unfold IsEvenVec at *
    simp [Finset.sum_add_distrib, ha, hb]
  have h1 : φ (a + b) = 1 := by
    rw [hc.mul a b ha hb, h]
    exact hc.mul_self hb
  have h2 := hc.inj _ hab h1
  funext i
  have h3 := congrFun h2 i
  have key : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  exact key _ _ h3

end Sec127NatCoord

theorem sec127_le_normalizer_centralizer {V1 X : Subgroup G} (hX : X ≤ normalizer (V1 : Set G)) :
    X ≤ normalizer (centralizer (V1 : Set G) : Set G) := by
  intro g hg
  have hconj : CFSG.conjugate V1 g = V1 := by
    ext x
    rw [mem_conjugate_iff]
    exact (Subgroup.mem_normalizer_iff.mp (hX hg) x).symm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h := sec126_mem_centralizer_conjugate_iff (H := V1) (g := g) (x := x)
  rw [hconj] at h
  exact h

theorem sec127_nat_cent_bot {V1 X : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}
    (hc : Sec127NatCoord V1 X φ) (hA5 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) :
    X ⊓ centralizer (V1 : Set G) = ⊥ := by
  rcases sec127_simple_dich hA5 (sec127_le_normalizer_centralizer hc.normalizes) with h | h
  · exact h
  · exfalso
    have hσ : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 5) := by
      decide
    obtain ⟨g, hgX, hg⟩ := hc.onto _ hσ
    obtain ⟨v, hev, hne⟩ := sec127_exists_moved
    have hev' := sec127_isEvenVec_permVec (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) hev
    have h1 := hg v hev
    have h2 : g * φ v = φ v * g :=
      ((Subgroup.mem_centralizer_iff.mp (h hgX)) (φ v) (hc.mem v hev)).symm
    have h3 : g * φ v * g⁻¹ = φ v := by
      rw [h2]
      group
    rw [h1] at h3
    exact hne ((hc.eq_iff hev' hev).mp h3)

end CFSG.OddStandard.SmallF3.Omega
