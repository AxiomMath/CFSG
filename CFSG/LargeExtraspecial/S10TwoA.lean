module

public import CFSG.LargeExtraspecial.S10ModelC
public import CFSG.LargeExtraspecial.S10Frame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem card_sup_mul_card_inf {X : Type*} [Group X] {A N : Subgroup X}
    (hAN : A ≤ normalizer (N : Set X)) :
    Nat.card (A ⊔ N : Subgroup X) * Nat.card (A ⊓ N : Subgroup X) = Nat.card A * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A N hAN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (A ⊔ N))
  have h3 : Nat.card (N.subgroupOf A) = Nat.card (A ⊓ N : Subgroup X) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (A ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

@[expose] def transposeEquiv : M2 ≃ₗ[ZMod 2] M2 where
  toFun := Matrix.transpose
  invFun := Matrix.transpose
  map_add' := Matrix.transpose_add
  map_smul' := fun c m => Matrix.transpose_smul c m
  left_inv := Matrix.transpose_transpose
  right_inv := Matrix.transpose_transpose

@[expose] def stabA : Subgroup Gm where
  carrier := {γ | act γ E00 = E00}
  mul_mem' := fun {γ δ} hγ hδ => by
    change act (γ * δ) E00 = E00
    rw [act_mul, show act δ E00 = E00 from hδ, show act γ E00 = E00 from hγ]
  one_mem' := act_one E00
  inv_mem' := fun {γ} hγ => by
    change act γ⁻¹ E00 = E00
    conv_lhs => rw [← show act γ E00 = E00 from hγ]
    rw [← act_mul, inv_mul_cancel, act_one]

theorem mem_stabA {γ : Gm} : γ ∈ stabA ↔ act γ E00 = E00 := Iff.rfl

theorem card_stabA : Nat.card stabA = 4 := by
  have e : stabA ≃ ({1, τ₁, τ₂, τ₁ * τ₂} : Finset Gm) :=
    Equiv.subtypeEquivRight fun γ => by
      rw [mem_stabA, act_E00_iff γ]
      simp
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  decide +kernel

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Frame

variable {X : Hyp10 S g t} (F : Frame X)

@[expose] noncomputable def pre (Γ' : Subgroup Gm) : Subgroup S.O :=
  (Γ'.comap F.π).map (Rbar S g t).subtype

theorem mem_pre {Γ' : Subgroup Gm} {x : S.O} :
    x ∈ F.pre Γ' ↔ ∃ hx : x ∈ Rbar S g t, F.π ⟨x, hx⟩ ∈ Γ' := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r.2, hr⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem pre_le_Rbar (Γ' : Subgroup Gm) : F.pre Γ' ≤ Rbar S g t := by
  rintro _ ⟨r, -, rfl⟩
  exact r.2

theorem Nbar_le_pre (Γ' : Subgroup Gm) : Nbar S g t ≤ F.pre Γ' := fun x hx =>
  (F.mem_pre).mpr ⟨Nbar_le_Rbar hx, by rw [(F.ker _).mpr hx]; exact one_mem _⟩

theorem card_pre (Γ' : Subgroup Gm) :
    Nat.card (F.pre Γ') = Nat.card Γ' * Nat.card (Nbar S g t) := by
  rw [pre, Subgroup.card_map_of_injective (Rbar S g t).subtype_injective]
  have h1 := Subgroup.card_mul_index (Γ'.comap F.π)
  rw [Subgroup.index_comap_of_surjective Γ' F.surj, F.card_Rbar] at h1
  have h2 := Subgroup.card_mul_index Γ'
  rw [card_Gm] at h2
  have hpos : 0 < Γ'.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have h3 : Nat.card (Γ'.comap F.π) * Γ'.index =
      (Nat.card Γ' * Nat.card (Nbar S g t)) * Γ'.index := by
    rw [h1, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos h3

theorem π_mem_stabA {l : S.O} (hl : l ∈ S.Lbar g) :
    F.π ⟨l, Lbar_le_Rbar X.ht hl⟩ ∈ stabA := by
  refine F.act_E00_of_fix _ ?_
  have : S.cl (g * S.z * g⁻¹) ∈ fixSub S (S.Lbar g) := by
    rw [X.H.fixSub_eq]
    exact Submodule.mem_span_singleton_self _
  exact this l hl

theorem exists_Lbar_of_stab {γ : Gm} (hγ : γ ∈ stabA) :
    ∃ l, ∃ hl : l ∈ S.Lbar g, F.π ⟨l, Lbar_le_Rbar X.ht hl⟩ = γ := by
  set ψ : S.Lbar g →* Gm := F.π.comp (Subgroup.inclusion (Lbar_le_Rbar X.ht)) with hψ
  have hrange : ψ.range ≤ stabA := by
    rintro _ ⟨l, rfl⟩
    exact F.π_mem_stabA l.2
  have hker : Nat.card ψ.ker = Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
    refine Nat.card_congr ?_
    refine (Equiv.subtypeEquivRight (q := fun l : S.Lbar g => (l : S.O) ∈ Nbar S g t)
      fun l => ?_).trans ?_
    · rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, F.ker]
      rfl
    · exact
        { toFun := fun l => ⟨l, l.1.2, l.2⟩
          invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
          left_inv := fun l => rfl
          right_inv := fun y => rfl }
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hker,
    X.C.card_Lbar, X.card_Abar] at h1
  have h3 : 3 ≤ S.width := X.H.two_lt_width
  have hcard : Nat.card ψ.range = 4 := by
    have e : 2 ^ (S.width - 1) = 4 * 2 ^ (S.width - 3) := by
      rw [show S.width - 1 = (S.width - 3) + 2 by omega, pow_add]
      ring
    rw [e] at h1
    exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (by positivity)) h1).symm
  have heq : ψ.range = stabA :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [hcard, card_stabA])
  rw [← heq] at hγ
  obtain ⟨l, rfl⟩ := hγ
  exact ⟨l, l.2, rfl⟩

@[expose] noncomputable def swap : Frame X where
  π := (MulEquiv.prodComm : Gm ≃* Gm).toMonoidHom.comp F.π
  φ := F.φ.trans transposeEquiv
  surj := fun γ => by
    obtain ⟨r, hr⟩ := F.surj γ.swap
    exact ⟨r, by simp [hr]⟩
  ker := fun r => by
    rw [← F.ker]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    exact ⟨fun h => by simpa using congrArg Prod.swap h, fun h => by rw [h]; rfl⟩
  compat := fun r v => by
    change (F.φ (resV X.haQ t r v)).transpose = act (F.π r).swap (F.φ v).transpose
    rw [F.compat, act_swap_transpose]
  base := by
    change (F.φ (aV X.ht)).transpose = E00
    rw [F.base, E00_transpose]
  beta_eq := fun v w => by
    change _ = pf (F.φ v).transpose (F.φ w).transpose
    rw [pf_transpose, F.beta_eq]
  sing := fun v hv => by
    change _ ↔ qf (F.φ v).transpose = 0
    rw [qf_transpose, F.sing v hv]

theorem swap_π (r : Rbar S g t) : F.swap.π r = (F.π r).swap := rfl

end Frame

end CFSG.LargeExtraspecial.S10
