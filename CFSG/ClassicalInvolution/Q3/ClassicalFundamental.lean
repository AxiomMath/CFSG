module

public import CFSG.ClassicalInvolution.Q3.Lift
public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.ClassicalInvolution.Q3.Basic

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups commutatorElement

section Exact

variable {Y : Type} [Group Y] [Finite Y]

theorem IsClassicalMember3.oddCore_eq_bot_of_centralizer {L : Subgroup Y} {z : Y}
    (h : IsClassicalMember3 L z) (hC : CFSG.Assembly.Dichotomy.involutionOddCore z = ⊥) :
    classicalInvolutionOddCore L = ⊥ := by
  have h1 : oddCoreIn L ≤ oddCoreIn (Subgroup.centralizer ({z} : Set Y)) :=
    oddCoreIn_le_of_isSubnormal h.subnormal
  rw [← involutionOddCore_eq_oddCoreIn, hC, le_bot_iff] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h1

theorem oddCore_eq_bot_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : classicalInvolutionOddCore B = ⊥) : classicalInvolutionOddCore A = ⊥ := by
  have h1 := CFSG.ComponentClassification.OddCore.equiv_invariant e
  have h2 : componentClassificationOddCore B = ⊥ := h
  rw [h2, Subgroup.map_eq_bot_iff_of_injective _ (show Function.Injective e.toMonoidHom from
    e.injective)] at h1
  exact h1

end Exact

theorem isSubnormal_comap₃ {G H : Type*} [Group G] [Group H] (ψ : G →* H) {A B : Subgroup H}
    (h : IsSubnormal A B) : IsSubnormal (A.comap ψ) (B.comap ψ) :=
  h.comap ψ

section Lift

variable {K X : Type} [Group K] [Finite K] [Group X]

theorem IsClassicalMember3.exists_lift (ψ : K →* X) (hψ : Function.Surjective ψ)
    (hcen : ψ.ker ≤ Subgroup.center K) (h2 : IsPGroup 2 ψ.ker) {L : Subgroup X} {z : X}
    (h : IsClassicalMember3 L z) (hL : classicalInvolutionOddCore L = ⊥) :
    ∃ (L' : Subgroup K) (z' : K), IsClassicalMember3 L' z' ∧ L'.map ψ = L ∧ ψ z' = z ∧
      classicalInvolutionOddCore L' = ⊥ := by
  obtain ⟨e₀⟩ := h.nonempty_equiv_sl2 hL
  let e : SL(2, ZMod 3) ≃* L := e₀.symm
  obtain ⟨β, hβinj, hβ⟩ := exists_hom_lift_sl2Three ψ hψ hcen h2 L e
  have hodd : Odd (Nat.card (ZMod 3)) := by
    rw [Nat.card_zmod]
    decide
  have hzL : (⟨z, h.mem⟩ : L) = e (-1) := by
    have := (orderOf_eq_two_iff_of_equiv_sl2 hodd e₀ ⟨z, h.mem⟩).mp
      (by rw [Subgroup.orderOf_mk]; exact h.orderOf_eq_two)
    simpa [e] using this
  have hzz : z = (e (-1) : X) := congrArg Subtype.val hzL
  set L' : Subgroup K := β.range with hL'
  set z' : K := β (-1) with hz'
  have hψz' : ψ z' = z := by rw [hz', hβ, ← hzz]
  have hz'mem : z' ∈ L' := ⟨-1, rfl⟩
  have hneg : (-1 : SL(2, ZMod 3)) ≠ 1 := by decide +kernel
  have hnegsq : (-1 : SL(2, ZMod 3)) * (-1) = 1 := by decide +kernel
  have hz'ne : z' ≠ 1 := fun h1 => hneg (hβinj (by rw [hz'] at h1; rw [h1, map_one]))
  have hz'sq : z' ^ 2 = 1 := by
    rw [hz', ← map_pow, sq, hnegsq, map_one]
  have hz'ord : orderOf z' = 2 := orderOf_eq_prime hz'sq hz'ne
  have hL'map : L'.map ψ = L := by
    ext x
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      rw [hβ]
      exact (e s).2
    · intro hx
      obtain ⟨s, hs⟩ := e.surjective ⟨x, hx⟩
      exact ⟨β s, ⟨s, rfl⟩, by rw [hβ, hs]⟩
  have hLC : L' ≤ Subgroup.centralizer ({z'} : Set K) := by
    rintro _ ⟨s, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hz', ← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_center_iff.mp
      ((mem_center_sl2_iff (-1 : SL(2, ZMod 3))).mpr (Or.inr rfl))) s
  set Lpre : Subgroup K := L.comap ψ with hLpre
  have hL'le : L' ≤ Lpre := by
    intro x hx
    have : ψ x ∈ L'.map ψ := Subgroup.mem_map_of_mem ψ hx
    rwa [hL'map] at this
  have hdec : ∀ x ∈ Lpre, ∃ n ∈ ψ.ker, ∃ l ∈ L', x = n * l := by
    intro x hx
    have hx' : ψ x ∈ L'.map ψ := by rw [hL'map]; exact hx
    obtain ⟨l, hl, hlx⟩ := hx'
    refine ⟨x * l⁻¹, ?_, l, hl, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hlx, mul_inv_cancel]
  have hsub : IsSubnormal L' (Subgroup.centralizer ({z'} : Set K)) := by
    have h1 := isSubnormal_inf (isSubnormal_comap₃ ψ h.subnormal)
      (Subgroup.centralizer ({z'} : Set K))
    have h2' : (Subgroup.centralizer ({z} : Set X)).comap ψ ⊓
        Subgroup.centralizer ({z'} : Set K) = Subgroup.centralizer ({z'} : Set K) := by
      apply inf_eq_right.mpr
      intro c hc
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, ← hψz', ← map_mul,
        ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hc]
    rw [h2'] at h1
    refine isSubnormal_trans (isSubnormal_of_normal_subgroupOf (le_inf hL'le hLC) ?_) h1
    rw [Subgroup.normal_subgroupOf_iff (le_inf hL'le hLC)]
    intro x k hx hk
    obtain ⟨n, hn, l, hl, hkl⟩ := hdec k hk.1
    have hconj : k * x * k⁻¹ = l * x * l⁻¹ := by
      rw [hkl]
      calc n * l * x * (n * l)⁻¹ = n * (l * x * l⁻¹) * n⁻¹ := by group
        _ = l * x * l⁻¹ := by
          rw [← Subgroup.mem_center_iff.mp (hcen hn) (l * x * l⁻¹)]
          group
    rw [hconj]
    exact L'.mul_mem (L'.mul_mem hl hx) (L'.inv_mem hl)
  have hOL' : classicalInvolutionOddCore L' = ⊥ := by
    have hO1 : classicalInvolutionOddCore SL(2, ZMod 3) = ⊥ := oddCore_eq_bot_of_equiv e hL
    let e' : SL(2, ZMod 3) ≃* L' := MonoidHom.ofInjective hβinj
    exact oddCore_eq_bot_of_equiv e'.symm hO1
  refine ⟨L', z', ⟨hz'ord, hz'mem, hsub, ?_⟩, hL'map, hψz', hOL'⟩
  let e' : SL(2, ZMod 3) ≃* L' := MonoidHom.ofInjective hβinj
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hOL').trans QuotientGroup.quotientBot).trans
    e'.symm⟩

end Lift

end CFSG.ClassicalInvolution.Q3
