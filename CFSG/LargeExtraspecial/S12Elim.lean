module

public import CFSG.LargeExtraspecial.S12Classify

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

@[expose] noncomputable def fixVec12 (v : S.Qt) : Subgroup S.O where
  carrier := {m | (m : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v}
  mul_mem' {x y} hx hy := by
    change ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hy, hx]
  one_mem' := rfl
  inv_mem' {x} hx := by
    change ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
    have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := hx
    conv_lhs => rw [← e]
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl

@[expose] def S12FuseCert (g : G) (t : S.O) : Prop :=
  ∀ m ∈ S.Mbar, m * t * m⁻¹ = t → m ∈ normalizer (S.Lbar g : Set S.O)

@[expose] def S12GenCert (g : G) : Prop :=
  ∃ d₁ d₂ d₃ : S.O, d₁ ∈ S.Lbar g ∧ d₂ ∈ S.Lbar g ∧ d₃ ∈ S.Lbar g ∧
    IsTypeA S.q (d₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 ∧ IsTypeA S.q (d₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 ∧
    IsTypeA S.q (d₃ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 ∧
    ∃ h : S.M, ∃ d₄ d₅ : S.O, d₄ ∈ S.Lbar ((h : G) * g) ∧ d₅ ∈ S.Lbar ((h : G) * g) ∧
      IsTypeA S.q (d₄ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 ∧ IsTypeA S.q (d₅ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 ∧
      S.Xbar12 g = closure {d₁, d₂, d₃, d₄, d₅}

@[expose] def S12IndexCert (g : G) : Prop :=
  S.Xbar12 g ≤ normalizer (S.Lbar g : Set S.O) ∨
    2 ^ (2 * S.width) ≤ (normalizer (S.Lbar g : Set S.O)).relIndex (S.Xbar12 g)

variable {S}

theorem s12_apply_eq_iff {x y : S.O} {v : S.Qt} :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v ↔
      ((x⁻¹ * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  rw [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply]
  constructor
  · intro h
    rw [← h]
    exact (x : S.Qt ≃ₗ[ZMod 2] S.Qt).symm_apply_apply v
  · intro h
    have := congrArg (x : S.Qt ≃ₗ[ZMod 2] S.Qt) h
    rw [show ((x : S.Qt ≃ₗ[ZMod 2] S.Qt))⁻¹ = (x : S.Qt ≃ₗ[ZMod 2] S.Qt).symm from rfl,
      LinearEquiv.apply_symm_apply] at this
    exact this.symm

theorem relIndex_fixVec12_lt (H : Subgroup S.O) {v : S.Qt} (hv : v ≠ 0) :
    (S.fixVec12 v).relIndex H < 2 ^ (2 * S.width) := by
  classical
  have : Finite S.Qt := Module.finite_of_finite (ZMod 2)
  set K := (S.fixVec12 v).subgroupOf H
  have hK : ∀ h₁ h₂ : H, ((h₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      ((h₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ↔ h₁⁻¹ * h₂ ∈ K := fun h₁ h₂ => s12_apply_eq_iff
  let φ : H ⧸ K → {w : S.Qt // w ≠ 0} := Quotient.lift
    (fun h : H => ⟨((h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v, fun e =>
      hv (((h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).map_eq_zero_iff.mp e)⟩)
    (fun h₁ h₂ hh => Subtype.ext ((hK h₁ h₂).mpr (QuotientGroup.leftRel_apply.mp hh)))
  have hφ : Function.Injective φ := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H h₁ => ?_
    induction y using QuotientGroup.induction_on with | H h₂ => ?_
    exact QuotientGroup.eq.mpr ((hK h₁ h₂).mp (congrArg Subtype.val hxy))
  have h1 : Nat.card (H ⧸ K) ≤ Nat.card {w : S.Qt // w ≠ 0} :=
    Nat.card_le_card_of_injective φ hφ
  have h2 : Nat.card {w : S.Qt // w ≠ 0} < Nat.card S.Qt := by
    have : Fintype S.Qt := Fintype.ofFinite S.Qt
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
    have : 0 < Fintype.card S.Qt := Fintype.card_pos
    omega
  have h3 : Nat.card S.Qt = 2 ^ (2 * S.width) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), S.finrank_Qt_eq_two_mul_width,
      Nat.card_zmod]
  show Nat.card (H ⧸ K) < _
  omega

theorem mem_normalizer_Lbar_iff_fix {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {m : S.O} (hm : m ∈ S.Mbar) :
    m ∈ normalizer (S.Lbar g : Set S.O) ↔
      (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
  obtain ⟨h, rfl⟩ := hm
  exact S.timmesfeld_12_4_1 haQ hne hn h

theorem isReducible12_of_fuseCert {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hdeg : ¬ S.IsNondeg12 g)
    (hF : S.S12FuseCert g t) : S.IsReducible12 := by
  have htE : t ∈ S.Ebar12 g := mem_Ebar12_of_mem_Lbar ht htA
  refine S.s12_isReducible12_of_fuse haQ hne hn ht htA
    (fun m hm hmt => (mem_normalizer_Lbar_iff_fix haQ hne hn hm).mp (hF m hm hmt))
    fun m hm => ?_
  have hτ := conj_mem_Ebar12 hm htE
  have hle := Dbar12_rootInvolution.1 t (Ebar12_subset_Dbar12 htE) _ (Ebar12_subset_Dbar12 hτ)
  have hne4 : orderOf (t * (m * t * m⁻¹)) ≠ 4 := fun h4 => hdeg ⟨t, htE, _, hτ, h4⟩
  have hpos : 0 < orderOf (t * (m * t * m⁻¹)) := orderOf_pos _
  omega

theorem isReducible12_of_genCert {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 4 ≤ S.width) (hG : S.S12GenCert g) :
    S.IsReducible12 := by
  obtain ⟨d₁, d₂, d₃, h₁, h₂, h₃, hA₁, hA₂, hA₃, h, d₄, d₅, h₄, h₅, hA₄, hA₅, hgen⟩ := hG
  exact S.s12_isReducible12_of_gen_three_two haQ hne hn h h₁ h₂ h₃ h₄ h₅ hA₁ hA₂ hA₃ hA₄ hA₅
    hgen

theorem isReducible12_of_indexCert {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hI : S.S12IndexCert g) :
    S.IsReducible12 := by
  have ha0 := S.s12_cl_ne_zero_of_conj haQ hne
  have hsub : (normalizer (S.Lbar g : Set S.O)).subgroupOf (S.Xbar12 g) =
      (S.fixVec12 (S.cl (g * S.z * g⁻¹))).subgroupOf (S.Xbar12 g) := by
    ext x
    rw [mem_subgroupOf, mem_subgroupOf]
    exact mem_normalizer_Lbar_iff_fix haQ hne hn (Xbar12_le_Mbar x.2)
  rcases hI with hX | hidx
  · have htX : t ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)
    have hXne : S.Xbar12 g ≠ ⊥ := by
      intro h
      rw [h, mem_bot] at htX
      exact htA.2.1 (by rw [htX]; rfl)
    rcases S.s12_fixed_eq_zero_or Mbar_le_normalizer_Xbar12 hXne with h0 | hred
    · exact absurd (h0 _ fun y hy =>
        (mem_normalizer_Lbar_iff_fix haQ hne hn (Xbar12_le_Mbar hy)).mp (hX hy)) ha0
    · exact hred
  · have hlt := relIndex_fixVec12_lt (S.Xbar12 g) ha0
    rw [Subgroup.relIndex, ← hsub] at hlt
    exact absurd hidx (not_le.mpr hlt)

theorem false_of_card_Lbar_le {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 4 ≤ S.width) (h : Nat.card (S.Lbar g) ≤ 4) : False := by
  have h1 := S.card_Lbar_ge haQ hne
  have h2 : 2 ^ 3 ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Setting

end CFSG.LargeExtraspecial
