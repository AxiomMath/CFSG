module

public import CFSG.GH74.Uniqueness.Bender.AutFixed
public import CFSG.Sporadic.Schreier.RuAutInner

public section

namespace CFSG.GH74.Generic.S45

open CFSG.Blueprint CFSG.GH74.Uniqueness.Bender CFSG.Sporadic.RuSchreier

theorem ru_card_autFixed_congr {S T : Type} [Group S] [Group T] (e : S ≃* T) (yb : MulAut S) :
    Nat.card {x : T // (MulAut.congr e yb) x = x} = Nat.card ↥(autFixed yb) := by
  refine (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => ?_)).symm
  have h : (MulAut.congr e yb) (e x) = e (yb x) := by
    rw [MulAut.congr_apply]
    simp
  rw [mem_autFixed_iff]
  show yb x = x ↔ (MulAut.congr e yb) (e x) = e x
  rw [h]
  exact ⟨fun h => by rw [h], fun h => e.injective h⟩

theorem ru_card_inf_centralizer_conj {M : Type*} [Group M] {H : Subgroup M} {g : M} (hg : g ∈ H)
    (u : M) :
    Nat.card ↥(H ⊓ Subgroup.centralizer ({g * u * g⁻¹} : Set M)) =
      Nat.card ↥(H ⊓ Subgroup.centralizer ({u} : Set M)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g⁻¹).toEquiv fun x => ?_)
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe,
    MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨hx, hxu⟩
    refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩
    calc g⁻¹ * x * g * u = g⁻¹ * (x * (g * u * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * u * g⁻¹) * x) * g := by rw [hxu]
      _ = u * (g⁻¹ * x * g) := by group
  · rintro ⟨hx, hxu⟩
    have hx' : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    refine ⟨?_, ?_⟩
    · rw [hx']
      exact H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
    · calc x * (g * u * g⁻¹) = g * ((g⁻¹ * x * g) * u) * g⁻¹ := by group
        _ = g * (u * (g⁻¹ * x * g)) * g⁻¹ := by rw [hxu]
        _ = g * u * g⁻¹ * x := by group

theorem ru_card_centralizer_involution
    {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruP) (h2 : orderOf t = 2) :
    Nat.card ↥(ruP ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 4060)))) = 245760 ∨
      Nat.card ↥(ruP ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 4060)))) = 116480 := by
  have hinv : t ∈ {t | t ∈ ruP ∧ orderOf t = 2} := ⟨ht, h2⟩
  rw [ruInvolutions_eq] at hinv
  rcases hinv with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
  · left
    rw [ru_card_inf_centralizer_conj hg, ← ruC_eq_centralizer, card_ruC]
  · right
    rw [ru_card_inf_centralizer_conj hg, ruCentralizer_a, card_ruL]

theorem ru_fixed_card
    {S : Type} [Group S] (e : S ≃* NativeSporadic.Ru) (α : MulAut S) (hα : α * α = 1)
    (hα1 : α ≠ 1) :
    Nat.card ↥(autFixed α) = 245760 ∨ Nat.card ↥(autFixed α) = 116480 := by
  let φ : S ≃* ruP := e.trans ruEquivP
  have hβ2 : MulAut.congr φ α * MulAut.congr φ α = 1 := by rw [← map_mul, hα, map_one]
  have hβ1 : MulAut.congr φ α ≠ 1 := fun h =>
    hα1 ((MulAut.congr φ).injective (by rw [h, map_one]))
  obtain ⟨g, hg⟩ := conj_bijective.2 (MulAut.congr φ α)
  have hgg : g * g = 1 := by
    have h1 : MulAut.conj (g * g) = 1 := by rw [map_mul, hg, hβ2]
    have hc : g * g ∈ Subgroup.center ruP := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := congrArg (fun a : MulAut ruP => a z) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc z * (g * g) = (g * g * z * (g * g)⁻¹) * (g * g) := by rw [this]
        _ = g * g * z := by group
    rw [center_ruP, Subgroup.mem_bot] at hc
    exact hc
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hβ1 (by rw [← hg, map_one])
  have hord : orderOf (g : Equiv.Perm (Fin 4060)) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1
  have hkey : ∀ p : ruP, (MulAut.congr φ α) p = p ↔
      (p : Equiv.Perm (Fin 4060)) * (g : Equiv.Perm (Fin 4060)) =
        (g : Equiv.Perm (Fin 4060)) * (p : Equiv.Perm (Fin 4060)) := by
    intro p
    rw [← hg, MulAut.conj_apply]
    constructor
    · intro h
      have h' : p * g = g * p := by
        calc p * g = (g * p * g⁻¹) * g := by rw [h]
          _ = g * p := by group
      exact congrArg Subtype.val h'
    · intro h
      have h' : p * g = g * p := Subtype.ext h
      calc g * p * g⁻¹ = (p * g) * g⁻¹ := by rw [h']
        _ = p := by group
  have hfix : Nat.card {p : ruP // (MulAut.congr φ α) p = p} =
      Nat.card ↥(ruP ⊓ Subgroup.centralizer ({(g : Equiv.Perm (Fin 4060))} :
        Set (Equiv.Perm (Fin 4060)))) := by
    refine Nat.card_congr
      { toFun := fun p => ⟨(p.1 : Equiv.Perm (Fin 4060)), Subgroup.mem_inf.2 ⟨p.1.2,
          Subgroup.mem_centralizer_singleton_iff.2 ((hkey p.1).1 p.2)⟩⟩
        invFun := fun q => ⟨⟨q.1, (Subgroup.mem_inf.1 q.2).1⟩, (hkey _).2
          (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 q.2).2)⟩
        left_inv := fun p => rfl
        right_inv := fun q => rfl }
  have hall : Nat.card ↥(autFixed α) = Nat.card ↥(ruP ⊓ Subgroup.centralizer
      ({(g : Equiv.Perm (Fin 4060))} : Set (Equiv.Perm (Fin 4060)))) := by
    rw [← ru_card_autFixed_congr φ α]
    exact hfix
  rw [hall]
  exact ru_card_centralizer_involution g.2 hord

end CFSG.GH74.Generic.S45
