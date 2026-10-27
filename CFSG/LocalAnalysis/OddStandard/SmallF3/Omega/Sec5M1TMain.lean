module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5M1TAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5M1TCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5M1TN2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5M1TLayer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5M1TSq
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverPocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5PocketOmega
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverActConv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec5m1t_main (hS : Asc82SchurU43) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {z : G} {K₁ K₂ : Subgroup G} (hz2 : orderOf z = 2) (hL : IsOm6Z2 L) (hodd : oddCoreIn L = ⊥)
    (hK₁ : Sl23PocketIn L z K₁) (hK₂ : Sl23PocketIn L z K₂) (hcomm : ⁅K₁, K₂⁆ = ⊥)
    (hprod : K₁ ⊔ K₂ = twoRes (L ⊓ centralizer ({z} : Set G))) {q : G} (hq : q ∈ K₁)
    (hq4 : orderOf q = 4) {c : G} (hc : c ∈ normalizer (L : Set G))
    (hcK : K₁ ⊔ K₂ ≤ centralizer ({c} : Set G))
    (hcz : ∀ y ∈ L, (c * c) * y * (c * c)⁻¹ = z * y * z⁻¹) :
    LieModel ↥(layerCent L (q * c)) .PSU 3 3 1 ∧ K₂ ≤ layerCent L (q * c) := by
  obtain ⟨V, _, _, _, Q, hQ, φ, hφ⟩ := t5_exists_cover hS hL
  haveI : Finite V := Module.finite_of_finite (ZMod 3)
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e₁ e₂ he => LinearEquiv.ext (congrFun he))
  haveI : Finite (OGroup Q) :=
    Finite.of_injective (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) Subtype.val_injective
  have hdim := hφ.finrank_eq
  have hsgn := hφ.quadSign_eq
  have hker : CFSG.oddCore ↥L = ⊥ := by
    have h : (CFSG.oddCore ↥L).map L.subtype = ⊥ := hodd
    exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.oddCore ↥L) L.subtype_injective).mp h
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, hφ.ker_eq, hker]
  have hsurj : Function.Surjective φ := hφ.surjective
  have hzL : z ∈ L := (Subgroup.mem_inf.mp (hK₁.2.1 hK₁.1)).1
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2]; exact pow_orderOf_eq_one z
  let zL : ↥L := ⟨z, hzL⟩
  have hφzz : φ zL * φ zL = 1 := by
    rw [← map_mul, show zL * zL = 1 from Subtype.ext hzz, map_one]
  have hφz1 : φ zL ≠ 1 := by
    intro h
    have h1 : zL = 1 := hinj (h.trans (map_one φ).symm)
    have h2 : z = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at hz2
    omega
  have hI4 : IsI4PlusIn (⊤ : Subgroup ↥(omegaGroup hQ)) (φ zL) :=
    (t5_isI4PlusIn_iff hL hφ hzL hz2).mp ⟨hz2, K₁, hK₁⟩
  have hztt : ((φ zL : omegaGroup hQ) : OGroup Q) * ((φ zL : omegaGroup hQ) : OGroup Q) = 1 :=
    congrArg Subtype.val hφzz
  have hzt4 : invType ((φ zL : omegaGroup hQ) : OGroup Q) = (4, 1) :=
    (t5_isI4PlusIn_omega_iff hdim hsgn hztt hφz1).mp hI4
  obtain ⟨x, hx⟩ := t5_exists_coverAct hL hφ hc
  have hcodd : ∀ l : ↥L, z * (l : G) = (l : G) * z → Odd (orderOf (l : G)) →
      c * (l : G) = (l : G) * c := by
    intro l hlz hlodd
    have hmem : (l : G) ∈ twoRes (L ⊓ centralizer ({z} : Set G)) :=
      Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr
        ⟨l.2, Subgroup.mem_centralizer_singleton_iff.mpr hlz.symm⟩, hlodd⟩
    have h := hcK (hprod ▸ hmem)
    exact (Subgroup.mem_centralizer_singleton_iff.mp h).symm
  obtain ⟨x₀, hxx₀, hx₀sq⟩ := sec5m1t_core hQ hdim hsgn hztt hzt4
    (sec5m1t_comm_odd hinj hsurj hzL hx hcodd) (sec5m1t_sq_act hsurj hzL hx hcz)
  subst hxx₀
  have hqL : q ∈ L := (Subgroup.mem_inf.mp (hK₁.2.1 hq)).1
  have hqq : q * q = z := sec5m1t_sq_eq hz2 hK₁ hq hq4
  have hqc : q * c = c * q :=
    Subgroup.mem_centralizer_singleton_iff.mp (hcK (Subgroup.mem_sup_left hq))
  have hφqq : φ ⟨q, hqL⟩ * φ ⟨q, hqL⟩ = φ zL := by
    rw [← map_mul]
    exact congrArg φ (Subtype.ext hqq)
  have hqt_sq : ((φ ⟨q, hqL⟩ : omegaGroup hQ) : OGroup Q) *
      ((φ ⟨q, hqL⟩ : omegaGroup hQ) : OGroup Q) = ((φ zL : omegaGroup hQ) : OGroup Q) :=
    congrArg Subtype.val hφqq
  have hx₀q : x₀ * ((φ ⟨q, hqL⟩ : omegaGroup hQ) : OGroup Q) =
      ((φ ⟨q, hqL⟩ : omegaGroup hQ) : OGroup Q) * x₀ := by
    have h := t5_cent_map_mem hx (l := ⟨q, hqL⟩) hqc.symm
    rw [simAct_orthToSim] at h
    calc x₀ * ((φ ⟨q, hqL⟩ : omegaGroup hQ) : OGroup Q)
        = x₀ * ((φ ⟨q, hqL⟩ : omegaGroup hQ) : OGroup Q) * x₀⁻¹ * x₀ := by group
      _ = ((φ ⟨q, hqL⟩ : omegaGroup hQ) : OGroup Q) * x₀ := by rw [h]
  have hp : (((φ ⟨q, hqL⟩ : omegaGroup hQ) : OGroup Q) * x₀) *
      (((φ ⟨q, hqL⟩ : omegaGroup hQ) : OGroup Q) * x₀) = piOrth Q := by
    calc (((φ ⟨q, hqL⟩ : omegaGroup hQ) : OGroup Q) * x₀) *
          (((φ ⟨q, hqL⟩ : omegaGroup hQ) : OGroup Q) * x₀)
        = ((φ ⟨q, hqL⟩ : omegaGroup hQ) : OGroup Q) *
            (x₀ * ((φ ⟨q, hqL⟩ : omegaGroup hQ) : OGroup Q)) * x₀ := by group
      _ = ((φ ⟨q, hqL⟩ : omegaGroup hQ) : OGroup Q) *
            (((φ ⟨q, hqL⟩ : omegaGroup hQ) : OGroup Q) * x₀) * x₀ := by rw [hx₀q]
      _ = (((φ ⟨q, hqL⟩ : omegaGroup hQ) : OGroup Q) *
            ((φ ⟨q, hqL⟩ : omegaGroup hQ) : OGroup Q)) * (x₀ * x₀) := by group
      _ = ((φ zL : omegaGroup hQ) : OGroup Q) *
            (piOrth Q * ((φ zL : omegaGroup hQ) : OGroup Q)) := by rw [hqt_sq, hx₀sq]
      _ = piOrth Q * (((φ zL : omegaGroup hQ) : OGroup Q) *
            ((φ zL : omegaGroup hQ) : OGroup Q)) := by
        rw [← mul_assoc, mul_piOrth_comm, mul_assoc]
      _ = piOrth Q := by rw [hztt]; exact mul_one _
  have hd : CoverAct L φ (q * c)
      (orthToSim Q (((φ ⟨q, hqL⟩ : omegaGroup hQ) : OGroup Q) * x₀)) :=
    t5_coverAct_mul_left hx hqL
  obtain ⟨N, hNY, hNn, hNidx, hNqs, hNlie, hπY, hπN, hcov⟩ := sec5m1t_N2 hQ hdim hsgn hp
  obtain ⟨ψ, hψ⟩ := sec5m1t_cent_equiv hinj hsurj hd
  obtain ⟨⟨e⟩, hmem⟩ := sec5m1t_layer_of_equiv ψ hNY hNn hNidx hNqs
  refine ⟨LieModel.of_mulEquiv e.symm hNlie, fun k hk => ?_⟩
  have hkL : k ∈ L := (Subgroup.mem_inf.mp (hK₂.2.1 hk)).1
  have hkq : k * q = q * k := by
    have h : q ∈ centralizer (K₂ : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hq
    exact Subgroup.mem_centralizer_iff.mp h k hk
  have hkc : k * c = c * k :=
    Subgroup.mem_centralizer_singleton_iff.mp (hcK (Subgroup.mem_sup_right hk))
  have hkH : k ∈ L ⊓ centralizer ({q * c} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hkL, Subgroup.mem_centralizer_singleton_iff.mpr (by
      rw [← mul_assoc, hkq, mul_assoc, hkc, mul_assoc])⟩
  have hK₂L : K₂ ≤ L := fun y hy => (Subgroup.mem_inf.mp (hK₂.2.1 hy)).1
  let f : ↥K₂ →* OGroup Q :=
    ((omegaGroup hQ).subtype.comp φ).comp (Subgroup.inclusion hK₂L)
  have hf : ∀ y : ↥K₂, f y ∈ omegaGroup hQ ⊓ centralizer ({((φ ⟨q, hqL⟩ : omegaGroup hQ) :
      OGroup Q) * x₀} : Set (OGroup Q)) := by
    intro y
    have hyH : (y : G) ∈ L ⊓ centralizer ({q * c} : Set G) := by
      have hyq : (y : G) * q = q * (y : G) := by
        have h : q ∈ centralizer (K₂ : Set G) :=
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hq
        exact Subgroup.mem_centralizer_iff.mp h y y.2
      have hyc : (y : G) * c = c * (y : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hcK (Subgroup.mem_sup_right y.2))
      exact Subgroup.mem_inf.mpr ⟨hK₂L y.2, Subgroup.mem_centralizer_singleton_iff.mpr (by
        rw [← mul_assoc, hyq, mul_assoc, hyc, mul_assoc])⟩
    have h := (ψ ⟨(y : G), hyH⟩).2
    rw [hψ ⟨(y : G), hyH⟩] at h
    exact h
  have hfk := sec5m1t_map_le_of_cover (fun g => (mul_piOrth_comm g).symm) hπY hπN hcov
    hK₂.2.2.2 f hf ⟨k, hk⟩
  exact (hmem k hkH).mpr (by rw [hψ ⟨k, hkH⟩]; exact hfk)

end CFSG.OddStandard.SmallF3.Omega
