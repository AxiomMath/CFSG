module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Orbit
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeBasic

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrime

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

@[expose] def Zset (t : G) (Q : Subgroup G) (ψ : V6 → G) : Set V6 :=
  {v | ∃ g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G), g * t * g⁻¹ = t * ψ v}

namespace Setting

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G} {c : G}
  {v₀ : ℕ} (hS : Setting ε t L U Q P a ψ p c v₀)
include hS

theorem conj_t_eq {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) :
    ∃ v, g * t * g⁻¹ = t * ψ v := by
  obtain ⟨v, h | h⟩ := hS.mem_E_iff.1 ((mem_normalizer_iff.1 hg t).1 t_mem_E)
  · exact absurd (h ▸ hS.Q_le_L (hS.rad.ψ_mem v)) (hS.shape.conj_not_mem hS.rad.odd g)
  · exact ⟨v, h⟩

theorem zero_mem_Zset : (0 : V6) ∈ Zset t Q ψ :=
  ⟨1, one_mem _, by rw [hS.rad.ψ_zero]; group⟩

theorem commute_of_mem_P {x : G} (hx : x ∈ P) : x * t = t * x :=
  hS.shape.commute_of_mem (hS.rad.P_le_L hx)

theorem lin_mem_Zset {x : G} (hx : x ∈ P) {v : V6} (hv : v ∈ Zset t Q ψ) :
    lin ψ x v ∈ Zset t Q ψ := by
  obtain ⟨g, hg, hgt⟩ := hv
  refine ⟨x * g, mul_mem (hS.P_le_normalizer_E hx) hg, ?_⟩
  have hxt : x * t * x⁻¹ = t := by rw [hS.commute_of_mem_P hx, mul_inv_cancel_right]
  rw [hS.rad.ψ_lin (hS.rad.P_le_normalizer hx)]
  calc x * g * t * (x * g)⁻¹ = x * (g * t * g⁻¹) * x⁻¹ := by group
    _ = x * t * x⁻¹ * (x * ψ v * x⁻¹) := by rw [hgt]; group
    _ = t * (x * ψ v * x⁻¹) := by rw [hxt]

theorem mem_Zset_of {v w : V6} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : qfV ε v = qfV ε w) (hvZ : v ∈ Zset t Q ψ) : w ∈ Zset t Q ψ := by
  obtain ⟨x, hx, rfl⟩ := hS.rad.exists_lin_eq hv hw h
  exact hS.lin_mem_Zset hx hvZ

theorem card_normalizer_E [Finite G] :
    Nat.card (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) =
      Nat.card (Zset t Q ψ) * Nat.card (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) : Subgroup G) := by
  have e : Zset t Q ψ ≃ {y : G // ∃ g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G),
      g * t * g⁻¹ = y} :=
    Equiv.ofBijective (fun v => ⟨t * ψ v, v.2⟩) ⟨fun v w h => Subtype.ext (hS.rad.ψ_inj
      (mul_left_cancel (congrArg Subtype.val h))), fun y => by
        obtain ⟨g, hg, hgy⟩ := y.2
        obtain ⟨v, hv⟩ := hS.conj_t_eq hg
        exact ⟨⟨v, g, hg, hv⟩, Subtype.ext (hv.symm.trans hgy)⟩⟩
  rw [Nat.card_congr e]
  exact (card_conj_orbit_mul _ t).symm

theorem c_pow_mem_L {k : ℕ} (hk : k < 4) (h : c ^ k ∈ L) : k = 0 := by
  have hc : c ∉ L := fun h => hS.shape.c_not_mem (mem_sup_left h)
  interval_cases k
  · rfl
  · exact absurd (by simpa using h) hc
  · exact absurd (by rw [pow_two, hS.shape.sq] at h; exact h) hS.shape.not_mem
  · exfalso
    apply hS.shape.c_not_mem
    have h3 : c ^ 3 * t = c := by
      rw [pow_succ, pow_two, hS.shape.sq, ← hS.shape.c_comm, mul_assoc, hS.shape.mul_self,
        mul_one]
    rw [← h3]
    exact mul_mem (mem_sup_left h) (mem_sup_right (mem_zpowers t))

theorem c_mem_NC : c ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ⊓
    centralizer ({t} : Set G) := ⟨hS.c_mem_normalizer_E, hS.shape.c_mem_centralizer⟩

theorem P_le_NC : P ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ⊓
    centralizer ({t} : Set G) := fun _ hx =>
  ⟨hS.P_le_normalizer_E hx, mem_centralizer_singleton_iff.2 (hS.commute_of_mem_P hx)⟩

theorem four_mul_card_P_le [Finite G] :
    4 * Nat.card P ≤ Nat.card (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer ({t} : Set G) : Subgroup G) := by
  set NC := normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G)
  have hmem : ∀ (x : P) (i : Fin 4), (x : G) * c ^ (i : ℕ) ∈ NC := fun x i =>
    mul_mem (hS.P_le_NC x.2) (pow_mem hS.c_mem_NC _)
  have hinj : Function.Injective fun xi : P × Fin 4 =>
      (⟨xi.1 * c ^ (xi.2 : ℕ), hmem _ _⟩ : NC) := by
    have key : ∀ (x y : P) (i j : Fin 4), (i : ℕ) ≤ j →
        (x : G) * c ^ (i : ℕ) = y * c ^ (j : ℕ) → x = y ∧ i = j := by
      intro x y i j hij h
      have h1 : (y : G)⁻¹ * x = c ^ ((j : ℕ) - i) := by
        have : (y : G)⁻¹ * x * c ^ (i : ℕ) = c ^ (j : ℕ) := by rw [mul_assoc, h]; group
        rw [← Nat.sub_add_cancel hij, pow_add] at this
        exact mul_right_cancel this
      have h2 : c ^ ((j : ℕ) - i) ∈ L := h1 ▸ hS.rad.P_le_L (mul_mem (inv_mem y.2) x.2)
      have h3 := hS.c_pow_mem_L (by omega) h2
      have hij' : i = j := Fin.ext (by omega)
      refine ⟨Subtype.ext ?_, hij'⟩
      rw [h3, pow_zero] at h1
      exact (inv_mul_eq_one.1 h1).symm
    rintro ⟨x, i⟩ ⟨y, j⟩ h
    have h' : (x : G) * c ^ (i : ℕ) = y * c ^ (j : ℕ) := congrArg Subtype.val h
    rcases le_total (i : ℕ) j with hij | hij
    · obtain ⟨hxy, hij⟩ := key x y i j hij h'
      rw [hxy, hij]
    · obtain ⟨hxy, hij⟩ := key y x j i hij h'.symm
      rw [hxy, hij]
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin, mul_comm] at this

end Setting

end CFSG.EvenSmallLie.OmegaEight.CPrime
