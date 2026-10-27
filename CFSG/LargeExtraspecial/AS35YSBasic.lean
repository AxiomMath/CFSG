module

public import CFSG.LargeExtraspecial.AS35YSQuot
public import CFSG.LargeExtraspecial.AS35YLSBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

variable (S) in
@[expose] def fixW_YS : Submodule (ZMod 2) S.Qt where
  carrier := {v | ∀ l ∈ S.LbarAsc, ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v}
  add_mem' := fun ha hb l hl => by rw [map_add, ha l hl, hb l hl]
  zero_mem' := fun l _ => map_zero _
  smul_mem' := fun c v hv l hl => by rw [map_smul, hv l hl]

variable (S) in
noncomputable abbrev commU_YS : Submodule (ZMod 2) S.Qt :=
  LinearMap.BilinForm.orthogonal S.q.polarBilin (fixW_YS S)

theorem mem_fixW_YS {v : S.Qt} :
    v ∈ fixW_YS S ↔ ∀ l ∈ S.LbarAsc, ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
  Iff.rfl

theorem mem_commU_YS {v : S.Qt} : v ∈ commU_YS S ↔ ∀ w ∈ fixW_YS S, polar S.q v w = 0 :=
  OrthoF2.mem_orthogonal_iff_polar

theorem polar_O_YS (x : S.O) (a b : S.Qt) :
    polar S.q ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) a) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) b) = polar S.q a b :=
  AS35YS.polar_map_YS (fun v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2 v) a b

theorem fixW_YS_invariant (hst : S.Asc512Standing) {m : S.O} (hm : m ∈ S.Mbar) {w : S.Qt}
    (hw : w ∈ fixW_YS S) : (m : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ fixW_YS S := by
  intro g hg
  have hg' : m⁻¹ * g * m⁻¹⁻¹ ∈ S.LbarAsc := hst.normal m⁻¹ (S.Mbar.inv_mem hm) g hg
  have e := hw _ hg'
  rw [inv_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply,
    LinearEquiv.mul_apply] at e
  have e' := congrArg (m : S.Qt ≃ₗ[ZMod 2] S.Qt) e
  rwa [show (m : S.Qt ≃ₗ[ZMod 2] S.Qt) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹
    ((g : S.Qt ≃ₗ[ZMod 2] S.Qt) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) w))) =
      (g : S.Qt ≃ₗ[ZMod 2] S.Qt) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) w) from
    (m : S.Qt ≃ₗ[ZMod 2] S.Qt).apply_symm_apply _] at e'

theorem commU_YS_invariant (hst : S.Asc512Standing) {m : S.O} (hm : m ∈ S.Mbar) {u : S.Qt}
    (hu : u ∈ commU_YS S) : (m : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ commU_YS S := by
  rw [mem_commU_YS] at hu ⊢
  intro w hw
  have hw' := fixW_YS_invariant hst (S.Mbar.inv_mem hm) hw
  have e : w = (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel]
    rfl
  rw [e, polar_O_YS]
  exact hu _ hw'

theorem sub_mem_commU_YS {l : S.O} (hl : l ∈ S.LbarAsc) (v : S.Qt) :
    (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ commU_YS S := by
  rw [mem_commU_YS]
  intro w hw
  have e : polar S.q ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) v) w =
      polar S.q ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) v) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
    rw [hw l hl]
  rw [polar_sub_left, e, polar_O_YS, sub_self]

theorem commSpace_le_commU_YS {l : S.O} (hl : l ∈ S.LbarAsc) :
    commSpace (l : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ commU_YS S := by
  intro x hx
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
  exact sub_mem_commU_YS hl v

theorem fixW_inf_commSpace_YS (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) {d : S.O} (hd : d ∈ S.DbarAsc) :
    fixW_YS S ⊓ commSpace (d : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  rw [eq_bot_iff]
  intro a ha
  rw [Submodule.mem_bot]
  by_contra ha0
  obtain ⟨haW, had⟩ := Submodule.mem_inf.mp ha
  have hall : ∀ e ∈ S.DbarAsc, a ∈ commSpace (e : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    intro e he
    obtain ⟨l, hl, rfl⟩ := hst.conj d hd e he
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, commSpace_conj]
    exact ⟨a, had, haW l hl⟩
  obtain ⟨_, ⟨d₁, hd₁, rfl⟩, _, ⟨e₁, he₁, rfl⟩, h4⟩ := hnd
  have h4' := AS35YL.orderOf_eq_four_of_mk_YL
    (fun _ hd _ he => orderOf_mul_le_four_YL hS hd he) hd₁ he₁ h4
  have hA₁ := isTypeA_of_mem_DbarAsc_YL hS hd₁
  have hA₂ := isTypeA_of_mem_DbarAsc_YL hS he₁
  have hcomm : ((d₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * ((e₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      ((e₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * ((d₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    refine (commute_iff_of_isTypeA S.q_nondegenerate hA₁ hA₂).mpr (Or.inl fun h => ha0 ?_)
    have hmem : a ∈ commSpace ((d₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
        commSpace ((e₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨hall _ hd₁, hall _ he₁⟩
    rw [h, Submodule.mem_bot] at hmem
    exact hmem
  have hc : (d₁ : S.O) * e₁ = e₁ * d₁ := Subtype.ext hcomm
  have hdd : (d₁ : S.O) * d₁ = 1 := mul_self_of_mem_DbarAsc_YL hd₁
  have hee : (e₁ : S.O) * e₁ = 1 := mul_self_of_mem_DbarAsc_YL he₁
  have hsq : ((d₁ : S.O) * e₁) ^ 2 = 1 := by
    calc ((d₁ : S.O) * e₁) ^ 2 = d₁ * (e₁ * d₁) * e₁ := by rw [pow_two]; group
      _ = d₁ * (d₁ * e₁) * e₁ := by rw [hc]
      _ = (d₁ * d₁) * (e₁ * e₁) := by group
      _ = 1 := by rw [hdd, hee, one_mul]
  have hdvd := orderOf_dvd_of_pow_eq_one hsq
  rw [h4'] at hdvd
  exact absurd hdvd (by norm_num)

theorem orthogonal_commU_YS :
    LinearMap.BilinForm.orthogonal S.q.polarBilin (commU_YS S) = fixW_YS S :=
  LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl _

theorem finrank_commU_add_YS :
    finrank (ZMod 2) (commU_YS S) + finrank (ZMod 2) (fixW_YS S) = 2 * S.width := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  rw [LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate, ← S.finrank_Qt_eq_two_mul_width]
  have := Submodule.finrank_le (fixW_YS S)
  omega

theorem mem_fixW_of_mem_radU_YS {u : S.Qt} (hu : ∀ u' ∈ commU_YS S, polar S.q u u' = 0) :
    u ∈ fixW_YS S := by
  rw [← orthogonal_commU_YS, OrthoF2.mem_orthogonal_iff_polar]
  exact hu

end Setting

end CFSG.LargeExtraspecial
