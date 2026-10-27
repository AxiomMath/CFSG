module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamOut
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModelL34
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFam
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

theorem l34_outer_commutator_cube {k : Type} [Field k] (hk : Nat.card k = 4) :
    ∀ τ ∈ ⁅(⊤ : Subgroup (MulAut (projectiveSL 3 k) ⧸
        LinearThreeFourOuter.innerAutGroup (projectiveSL 3 k))),
      (⊤ : Subgroup (MulAut (projectiveSL 3 k) ⧸
        LinearThreeFourOuter.innerAutGroup (projectiveSL 3 k)))⁆, τ ^ 3 = 1 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  obtain ⟨-, -, ⟨e, -⟩, -⟩ :=
    LinearThreeFourOuter.linear_three_four_outer_quotient_rank_two_restriction k hk _ hσ
  intro τ hτ
  let ρ := (SemidirectProduct.rightHom (N := kˣ) (G := Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
    (φ := LinearThreeFourOuter.inversionAction kˣ)).comp e.toMonoidHom
  have hle : ⁅(⊤ : Subgroup (MulAut (projectiveSL 3 k) ⧸
        LinearThreeFourOuter.innerAutGroup (projectiveSL 3 k))),
      (⊤ : Subgroup (MulAut (projectiveSL 3 k) ⧸
        LinearThreeFourOuter.innerAutGroup (projectiveSL 3 k)))⁆ ≤ ρ.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  have h1 : e τ ∈ (SemidirectProduct.rightHom (N := kˣ)
      (G := Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
      (φ := LinearThreeFourOuter.inversionAction kˣ)).ker := hle hτ
  rw [← SemidirectProduct.range_inl_eq_ker_rightHom] at h1
  obtain ⟨u, hu⟩ := h1
  apply e.injective
  rw [map_pow, ← hu, ← map_pow, LinearThreeFourOuter.units_pow_three hk u, map_one, map_one]

theorem l34_outer_commutator_cube' {k : Type} [Field k] (hk : Nat.card k = 4) :
    ∀ τ ∈ ⁅(⊤ : Subgroup (Outer (projectiveSL 3 k))), (⊤ : Subgroup (Outer (projectiveSL 3 k)))⁆,
      τ ^ 3 = 1 := l34_outer_commutator_cube hk


theorem lem711_l34 :
    Lem711Empty (fun X _ => LieModel X .PSL 3 2 2) := by
  intro X _ _ L K x y h hL
  obtain ⟨k, _, _, hk, ⟨eL⟩⟩ := CFSG.Quasithin.H13.exists_mulEquiv_projectiveSL_of_lieModel hL
  have hcube : ∀ τ ∈ ⁅(⊤ : Subgroup (Outer ↥L)), (⊤ : Subgroup (Outer ↥L))⁆, τ ^ 3 = 1 := by
    intro τ hτ
    let E := CFSG.ComponentClassification.OuterAutomorphisms.equivalence eL
    have h1 : E τ ∈ ⁅(⊤ : Subgroup (Outer (projectiveSL 3 k))),
        (⊤ : Subgroup (Outer (projectiveSL 3 k)))⁆ := by
      have h2 : (⁅(⊤ : Subgroup (Outer ↥L)), (⊤ : Subgroup (Outer ↥L))⁆).map E.toMonoidHom ≤
          ⁅(⊤ : Subgroup (Outer (projectiveSL 3 k))), (⊤ : Subgroup (Outer (projectiveSL 3 k)))⁆ := by
        rw [Subgroup.map_commutator]
        exact Subgroup.commutator_mono le_top le_top
      exact h2 ⟨τ, hτ, rfl⟩
    have h3 := l34_outer_commutator_cube' hk _ h1
    apply E.injective
    rw [map_pow, h3, map_one]
  have hxL : x ∈ L := h.x_mem_L_of_outer_commutator_cube hcube
  have h3K : 3 ∣ Nat.card ↥K := by
    have h360 : 360 ∣ Nat.card ↥K := by
      rw [← h.card_K_bar]
      exact Subgroup.card_quotient_dvd_card _
    exact (by norm_num : 3 ∣ 360).trans h360
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 h3K
  have haL : (a : X) ∈ L := h.K_le a.2
  have ha3 : orderOf (eL ⟨(a : X), haL⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    exact ha
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.hx, pow_two] at this
  have hx2 : orderOf (eL ⟨x, hxL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact h.hx
  have hcomm : (a : X) * x = x * (a : X) :=
    mem_centralizer_singleton_iff.1 (h.comp.1 a.2)
  refine CFSG.RankThree.PartTwo.KFacts.L34.mul_ne_mul_of_orderOf hk ha3 hx2 ?_
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hcomm


end CFSG.GH74.GLS
