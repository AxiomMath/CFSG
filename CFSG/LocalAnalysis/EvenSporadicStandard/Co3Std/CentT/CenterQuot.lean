module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

open scoped commutatorElement

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose]
noncomputable def centerQuotAut {K : Type} [Group K] (ζ : MulAut K) : MulAut (K ⧸ center K) :=
  QuotientGroup.congr (center K) (center K) ζ (Subgroup.map_center_eq ζ)

theorem centerQuotAut_mk {K : Type} [Group K] (ζ : MulAut K) (x : K) :
    centerQuotAut ζ (x : K ⧸ center K) = ((ζ x : K) : K ⧸ center K) :=
  rfl

theorem centerQuotAut_mul {K : Type} [Group K] (ζ ξ : MulAut K) :
    centerQuotAut (ζ * ξ) = centerQuotAut ζ * centerQuotAut ξ := by
  ext x
  refine QuotientGroup.induction_on x ?_
  intro a
  simp [centerQuotAut]

theorem centerQuotAut_one {K : Type} [Group K] : centerQuotAut (1 : MulAut K) = 1 := by
  ext x
  refine QuotientGroup.induction_on x ?_
  intro a
  simp [centerQuotAut]

theorem centerQuotAut_conj {K : Type} [Group K] (g : K) :
    centerQuotAut (MulAut.conj g) = MulAut.conj (g : K ⧸ center K) := by
  ext x
  refine QuotientGroup.induction_on x ?_
  intro a
  simp [centerQuotAut]

theorem centerQuotAut_injective {K : Type} [Group K] (hK : commutator K = ⊤) :
    Function.Injective (centerQuotAut (K := K)) := by
  let F : MulAut K →* MulAut (K ⧸ center K) :=
    { toFun := centerQuotAut
      map_one' := centerQuotAut_one
      map_mul' := centerQuotAut_mul }
  have key : ∀ ζ : MulAut K, centerQuotAut ζ = 1 → ζ = 1 := by
    intro ζ hζ
    have hmem : ∀ x : K, x⁻¹ * ζ x ∈ center K := by
      intro x
      have hQ : ((ζ x : K) : K ⧸ center K) = (x : K ⧸ center K) := by
        have h := congrArg (fun e : MulAut (K ⧸ center K) => e (x : K ⧸ center K)) hζ
        simpa [centerQuotAut_mk] using h
      exact QuotientGroup.eq.mp hQ.symm
    have hcomm : ∀ x y : K, ζ ⁅x, y⁆ = ⁅x, y⁆ := by
      intro x y
      have hx : ζ x = x * (x⁻¹ * ζ x) := by group
      have hy : ζ y = y * (y⁻¹ * ζ y) := by group
      rw [map_commutatorElement, hx, hy]
      rw [CFSG.ComponentClassification.CentralExtensions.commutator_mul_center_left
            x (x⁻¹ * ζ x) (y * (y⁻¹ * ζ y)) (hmem x),
          CFSG.ComponentClassification.CentralExtensions.commutator_mul_center_right
            x y (y⁻¹ * ζ y) (hmem y)]
    have hle : commutator K ≤ fixedSubgroup ζ := by
      rw [_root_.commutator_def]
      apply Subgroup.commutator_le.mpr
      intro x _ y _
      simpa [fixedSubgroup] using hcomm x y
    have htop : fixedSubgroup ζ = ⊤ := by
      rw [eq_top_iff]
      rw [← hK]
      exact hle
    ext x
    have hx : x ∈ fixedSubgroup ζ := by rw [htop]; exact Subgroup.mem_top x
    simpa [fixedSubgroup] using hx
  have hinj : Function.Injective F := by
    rw [injective_iff_map_eq_one F]
    intro a ha
    exact key a (by simpa [F] using ha)
  simpa [F] using hinj

theorem card_fixed_centerQuotAut_dvd {K : Type} [Group K] [Finite K] (ζ : MulAut K) :
    Nat.card (fixedSubgroup (centerQuotAut ζ)) ∣ Nat.card (fixedSubgroup ζ) := by
  let Fix : Subgroup (K ⧸ center K) := fixedSubgroup (centerQuotAut ζ)
  let X : Subgroup K := Fix.comap (QuotientGroup.mk' (center K))
  have hcX : center K ≤ X := by
    intro z hz
    change QuotientGroup.mk' (center K) z ∈ Fix
    have hz1 : QuotientGroup.mk' (center K) z = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hz
    rw [hz1]
    exact Fix.one_mem
  have hFixX : fixedSubgroup ζ ≤ X := by
    intro x hx
    change QuotientGroup.mk' (center K) x ∈ Fix
    have hx' : ζ x = x := by simpa [fixedSubgroup] using hx
    change centerQuotAut ζ (x : K ⧸ center K) = (x : K ⧸ center K)
    rw [centerQuotAut_mk, hx']
  have hdisp : ∀ x : X, (x : K)⁻¹ * ζ (x : K) ∈ center K := by
    intro x
    have hxmem : QuotientGroup.mk' (center K) (x : K) ∈ Fix := x.property
    have hfix : centerQuotAut ζ (QuotientGroup.mk' (center K) (x : K)) =
        QuotientGroup.mk' (center K) (x : K) := by
      simpa [Fix, fixedSubgroup] using hxmem
    have hQ : ((ζ (x : K) : K) : K ⧸ center K) = ((x : K) : K ⧸ center K) := by
      simpa [centerQuotAut_mk] using hfix
    exact QuotientGroup.eq.mp hQ.symm
  let φ0 : X →* K :=
    { toFun := fun x => (x : K)⁻¹ * ζ (x : K)
      map_one' := by simp
      map_mul' := fun x y => by
        have hc : ∀ g : K,
            g * ((x : K)⁻¹ * ζ (x : K)) = ((x : K)⁻¹ * ζ (x : K)) * g :=
          Subgroup.mem_center_iff.mp (hdisp x)
        show ((x : K) * (y : K))⁻¹ * ζ ((x : K) * (y : K)) =
          ((x : K)⁻¹ * ζ (x : K)) * ((y : K)⁻¹ * ζ (y : K))
        calc
          ((x : K) * (y : K))⁻¹ * ζ ((x : K) * (y : K))
              = (y : K)⁻¹ * (x : K)⁻¹ * ζ (x : K) * ζ (y : K) := by
                rw [map_mul, mul_inv_rev]
                group
          _ = (y : K)⁻¹ * ((x : K)⁻¹ * ζ (x : K)) * ζ (y : K) := by group
          _ = ((x : K)⁻¹ * ζ (x : K)) * (y : K)⁻¹ * ζ (y : K) := by
                rw [hc (y : K)⁻¹]
          _ = ((x : K)⁻¹ * ζ (x : K)) * ((y : K)⁻¹ * ζ (y : K)) := by group }
  let φ : X →* center K := φ0.codRestrict (center K) (fun x => hdisp x)
  have hφker : φ.ker = (fixedSubgroup ζ).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have h1 : (x : K)⁻¹ * ζ (x : K) = 1 := by
        simpa [φ, φ0] using congrArg Subtype.val hx
      have h2 : ζ (x : K) = (x : K) := by
        have h := congrArg (fun t : K => (x : K) * t) h1
        simpa using h
      simpa [fixedSubgroup] using h2
    · intro hx
      have hx' : ζ (x : K) = (x : K) := by simpa [fixedSubgroup] using hx
      apply Subtype.ext
      change (x : K)⁻¹ * ζ (x : K) = 1
      rw [hx', inv_mul_cancel]
  let ψ : X →* Fix :=
    ((QuotientGroup.mk' (center K)).comp X.subtype).codRestrict Fix (fun x => x.property)
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (center K) (y : K ⧸ center K)
    refine ⟨⟨k, ?_⟩, ?_⟩
    · change QuotientGroup.mk' (center K) k ∈ Fix
      rw [hk]
      exact y.property
    · apply Subtype.ext
      change QuotientGroup.mk' (center K) k = (y : K ⧸ center K)
      exact hk
  have hψker : ψ.ker = (center K).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : QuotientGroup.mk' (center K) (x : K) = 1 := by
        have h := congrArg Subtype.val hx
        change QuotientGroup.mk' (center K) (x : K) = 1 at h
        exact h
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
    · intro hx
      apply Subtype.ext
      change ((x : K) : K ⧸ center K) = 1
      rw [QuotientGroup.eq_one_iff]
      exact hx
  have hψkercard : Nat.card ψ.ker = Nat.card (center K) := by
    rw [hψker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcX).toEquiv
  have hφkercard : Nat.card φ.ker = Nat.card (fixedSubgroup ζ) := by
    rw [hφker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFixX).toEquiv
  have hXeq1 : Nat.card X = Nat.card Fix * Nat.card (center K) := by
    have h := Subgroup.card_ker_mul_card_of_surjective (f := ψ) hψsurj
    rw [hψkercard] at h
    rw [← h, Nat.mul_comm]
  have hXeq2 : Nat.card X = Nat.card (fixedSubgroup ζ) * Nat.card φ.range := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hφkercard] at h
    rw [← h]
  have hdiv : Nat.card φ.range ∣ Nat.card (center K) :=
    Subgroup.card_subgroup_dvd_card φ.range
  obtain ⟨k, hk⟩ := hdiv
  haveI : Nonempty φ.range := ⟨1, φ.range.one_mem⟩
  have hrpos : 0 < Nat.card φ.range := Nat.card_pos
  have hb : Nat.card (fixedSubgroup ζ) = Nat.card Fix * k := by
    have h1 : Nat.card Fix * (Nat.card φ.range * k) =
        Nat.card (fixedSubgroup ζ) * Nat.card φ.range := by
      rw [← hk]
      exact hXeq1.symm.trans hXeq2
    have h2 : Nat.card φ.range * (Nat.card Fix * k) =
        Nat.card φ.range * Nat.card (fixedSubgroup ζ) := by
      calc
        Nat.card φ.range * (Nat.card Fix * k)
            = Nat.card Fix * (Nat.card φ.range * k) := by ring
        _ = Nat.card (fixedSubgroup ζ) * Nat.card φ.range := h1
        _ = Nat.card φ.range * Nat.card (fixedSubgroup ζ) := by ring
    exact (Nat.mul_left_cancel hrpos h2).symm
  exact ⟨k, hb⟩

end CFSG.EvenSporadicStandard.Co3Std.CentT
