module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.TwoStep
public import Certificates.Data.A5

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup

theorem exists_orderOf_four_z2s5 :
    ∃ x : Multiplicative (ZMod 2) × Equiv.Perm (Fin 5), orderOf x = 4 := by
  set x : Multiplicative (ZMod 2) × Equiv.Perm (Fin 5) :=
    (1, Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3) with hx
  have h4 : x ^ 4 = 1 := by rw [hx]; decide
  have h2 : x ^ 2 ≠ 1 := by rw [hx]; decide
  refine ⟨x, ?_⟩
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x) (by simpa using h2)
    (by simpa using h4)
  exact this.trans (by norm_num)

namespace TwoCfg

variable {G : Type*} [Group G] {t v : G} {J : Subgroup G} (h : TwoCfg t v J)

include h

theorem exists_four_classes (htop : centralizer ({t} : Set G) ≠ ⊤) :
    ∃ x : ↥(fourGroup t v) → ↥(centralizer ({t} : Set G)), (∀ a, orderOf (x a) = 4) ∧
      ∀ (a b : ↥(fourGroup t v)) (y : ↥(centralizer ({t} : Set G))),
        y * x a * y⁻¹ = x b → a = b := by
  obtain ⟨e⟩ := h.hJ
  set c4 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 with hc4
  have hc4' : c4 ^ 4 = 1 := by rw [hc4]; decide
  have hc4'' : c4 ^ 2 ≠ 1 := by rw [hc4]; decide
  set g : G := embJ J e c4 with hg
  have hgJ : g ∈ J := embJ_mem J e c4
  have hg4 : g ^ 4 = 1 := by rw [hg, ← map_pow, hc4', map_one]
  have hg2 : g ^ 2 ≠ 1 := fun h2 =>
    hc4'' (embJ_injective J e (by rw [map_pow, ← hg, h2, map_one]))
  have hgC : g ∈ centralizer ({t} : Set G) := h.le_centralizer_J hgJ
  have hxC : ∀ a : ↥(fourGroup t v), (a : G) * g ∈ centralizer ({t} : Set G) := fun a =>
    Subgroup.mul_mem _ (h.fourGroup_le_centralizer a.2) hgC
  refine ⟨fun a => ⟨(a : G) * g, hxC a⟩, fun a => ?_, ?_⟩
  · have hcomm : Commute (a : G) g := h.hcomm a a.2 g hgJ
    have ha2 : (a : G) ^ 2 = 1 := by rw [pow_two]; exact h.mul_self_of_mem_fourGroup a.2
    have h4 : ((a : G) * g) ^ 4 = 1 := by
      rw [hcomm.mul_pow, show (a : G) ^ 4 = ((a : G) ^ 2) ^ 2 by group, ha2, hg4]
      simp
    have h2 : ((a : G) * g) ^ 2 ≠ 1 := by
      rw [hcomm.mul_pow, ha2, one_mul]
      exact hg2
    rw [Subgroup.orderOf_mk]
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := (a : G) * g) (by simpa using h2)
      (by simpa using h4)
    simpa using this
  · intro a b y hy
    have hy' : (y : G) * ((a : G) * g) * (y : G)⁻¹ = (b : G) * g := congrArg Subtype.val hy
    have hyC : (y : G) ∈ fourGroup t v ⊔ J := by
      rw [← h.hC]
      exact y.2
    obtain ⟨y₁, hy₁, y₂, hy₂, hyy⟩ := (mem_sup_iff_of_commute h.hcomm).1 hyC
    have hk : y₂ * g * y₂⁻¹ ∈ J :=
      J.mul_mem (J.mul_mem hy₂ hgJ) (J.inv_mem hy₂)
    have hyg : (y : G) * g * (y : G)⁻¹ = y₂ * g * y₂⁻¹ := by
      have h1 := h.hcomm y₁ hy₁ _ hk
      rw [← hyy]
      calc y₁ * y₂ * g * (y₁ * y₂)⁻¹ = y₁ * (y₂ * g * y₂⁻¹) * y₁⁻¹ := by group
        _ = (y₂ * g * y₂⁻¹) * y₁ * y₁⁻¹ := by rw [h1]
        _ = y₂ * g * y₂⁻¹ := by group
    have hya : (y : G) * (a : G) * (y : G)⁻¹ = (a : G) := by
      have h1 := h.fourGroup_central a.2 y.2
      calc (y : G) * (a : G) * (y : G)⁻¹ = ((y : G) * (a : G)) * (y : G)⁻¹ := rfl
        _ = ((a : G) * (y : G)) * (y : G)⁻¹ := by rw [h1]
        _ = (a : G) := by group
    have hconj : (a : G) * (y₂ * g * y₂⁻¹) = (b : G) * g := by
      rw [← hyg, ← hy']
      calc (a : G) * ((y : G) * g * (y : G)⁻¹) =
          ((y : G) * (a : G) * (y : G)⁻¹) * ((y : G) * g * (y : G)⁻¹) := by rw [hya]
        _ = (y : G) * ((a : G) * g) * (y : G)⁻¹ := by group
    have hmemV : (b : G)⁻¹ * (a : G) ∈ fourGroup t v :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ b.2) a.2
    have hmemJ : (b : G)⁻¹ * (a : G) ∈ J := by
      have : (b : G)⁻¹ * (a : G) = g * (y₂ * g * y₂⁻¹)⁻¹ := by
        have h2 : (a : G) = (b : G) * g * (y₂ * g * y₂⁻¹)⁻¹ := by
          rw [← hconj]
          group
        rw [h2]
        group
      rw [this]
      exact J.mul_mem hgJ (J.inv_mem hk)
    have h1 : (b : G)⁻¹ * (a : G) ∈ fourGroup t v ⊓ J := ⟨hmemV, hmemJ⟩
    rw [h.hdisj, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact Subtype.ext h1.symm

end TwoCfg

@[expose] def FewFour {M : Type*} [Group M] (n : ℕ) (Q : Subgroup M) : Prop :=
  ∃ reps : Finset M, reps.card ≤ n ∧
    ∀ x ∈ Q, orderOf x = 4 → ∃ r ∈ reps, ∃ c ∈ Q, x = c * r * c⁻¹

namespace TwoCfg

variable {G : Type*} [Group G] {t v : G} {J : Subgroup G} (h : TwoCfg t v J)

include h

theorem false_of_fewFour {M : Type*} [Group M] {Q : Subgroup M}
    (htop : centralizer ({t} : Set G) ≠ ⊤) (e : ↥(centralizer ({t} : Set G)) ≃* ↥Q)
    (hF : FewFour 3 Q) : False := by
  obtain ⟨reps, hrcard, hcov⟩ := hF
  obtain ⟨x, hx4, hxconj⟩ := h.exists_four_classes htop
  have hex : ∀ a : ↥(fourGroup t v), ∃ r' ∈ reps, ∃ c ∈ Q,
      ((e (x a) : ↥Q) : M) = c * r' * c⁻¹ := by
    intro a
    have h4 : orderOf ((e (x a) : ↥Q) : M) = 4 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx4]
    exact hcov _ (e (x a)).2 h4
  choose f hf c hc hfc using hex
  have hcardV : Nat.card ↥(fourGroup t v) = 4 := h.card_fourGroup htop
  haveI : Finite ↥(fourGroup t v) := Nat.finite_of_card_ne_zero (by rw [hcardV]; norm_num)
  haveI : Fintype ↥(fourGroup t v) := Fintype.ofFinite _
  have hlt : reps.card < (Finset.univ : Finset ↥(fourGroup t v)).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardV]
    omega
  obtain ⟨a, -, b, -, hab, hfab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt (fun a _ => hf a)
  have hd : c b * (c a)⁻¹ ∈ Q := Subgroup.mul_mem _ (hc b) (Subgroup.inv_mem _ (hc a))
  obtain ⟨y, hy⟩ := e.surjective ⟨c b * (c a)⁻¹, hd⟩
  have hyκ : ((e y : ↥Q) : M) = c b * (c a)⁻¹ := congrArg Subtype.val hy
  refine hab (hxconj a b y (e.injective (Subtype.ext ?_)))
  rw [map_mul, map_mul, map_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hyκ, hfc a, hfc b, ← hfab]
  group

end TwoCfg

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
