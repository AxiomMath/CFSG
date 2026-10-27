module

public import CFSG.LargeExtraspecial.AS35TPBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

namespace AS35T

theorem card_map_ρ_mul_card_inf_QG {A : Subgroup G} (hA : A ≤ S.M) :
    Nat.card ((A.subgroupOf S.M).map S.ρ) * Nat.card (A ⊓ S.QG : Subgroup G) = Nat.card A := by
  set f : (A.subgroupOf S.M) →* S.O := S.ρ.comp (A.subgroupOf S.M).subtype with hf
  have h1 := Subgroup.card_ker_mul_card_range f
  have hrange : f.range = (A.subgroupOf S.M).map S.ρ := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card f.ker = Nat.card (A ⊓ S.QG : Subgroup G) := by
    refine Nat.card_eq_of_bijective (fun a => ⟨(((a : A.subgroupOf S.M) : S.M) : G),
      mem_inf.mpr ⟨mem_subgroupOf.mp (a : A.subgroupOf S.M).2, ?_⟩⟩) ⟨?_, ?_⟩
    · exact (S.ρ_eq_one_iff _).mp a.2
    · intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext (Subtype.ext (Subtype.ext hab))
    · intro x
      obtain ⟨hxA, hxQ⟩ := mem_inf.mp x.2
      have hxM : (x : G) ∈ S.M := S.QG_le_M hxQ
      refine ⟨⟨⟨⟨x, hxM⟩, mem_subgroupOf.mpr hxA⟩, ?_⟩, rfl⟩
      exact (S.ρ_eq_one_iff ⟨x, hxM⟩).mpr hxQ
  have hA' : Nat.card (A.subgroupOf S.M) = Nat.card A := by
    rw [← Subgroup.card_map_of_injective S.M.subtype_injective, subgroupOf_map_subtype,
      inf_of_le_left hA]
  rw [hrange, hker, hA'] at h1
  rw [mul_comm]
  exact h1

theorem mem_pbar_iff {g : G} {σ : S.O} :
    σ ∈ ((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ ↔ ∃ x : S.M, (x : G) ∈ S.Qa g ∧ S.ρ x = σ := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (mem_inf.mp (mem_subgroupOf.mp hx)).1, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, mem_subgroupOf.mpr (mem_inf.mpr ⟨hx, x.2⟩), rfl⟩

theorem rho_t_mem_pbar {g : G} (htM : g * S.z * g⁻¹ ∈ S.M) :
    S.ρ ⟨_, htM⟩ ∈ ((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ :=
  (AS35T.mem_pbar_iff S).mpr ⟨⟨_, htM⟩, S.conj_z_mem_Qa g, rfl⟩

section Pbar

variable {S}
variable (hS : S.SixHyp) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M)
include hS ht

theorem rho_t_ne_one : S.ρ ⟨_, htM⟩ ≠ 1 := fun h =>
  S.not_mem_QG_of_mem_ESet hS.weak ht.1 ((S.ρ_eq_one_iff _).mp h)

omit hS in
theorem rho_t_mul_self : S.ρ ⟨_, htM⟩ * S.ρ ⟨_, htM⟩ = 1 :=
  S.ρ_mul_self_eq_one htM (S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1))

theorem commute_of_mem_Qa_of_comm_mem_QG {x y : G} (hx : x ∈ S.Qa g) (hy : y ∈ S.Qa g)
    (hxy : x * y * x⁻¹ * y⁻¹ ∈ S.QG) : x * y = y * x := by
  rcases AS35T.commutator_eq_one_or_of_mem_Qa S hx hy with h | h
  · calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h, one_mul]
  · exact absurd (h ▸ hxy) (S.not_mem_QG_of_mem_ESet hS.weak ht.1)

theorem eq_one_or_of_commute_pbar {σ : S.O}
    (hσ : σ ∈ ((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ)
    (hc : ∀ τ ∈ ((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ, σ * τ = τ * σ) :
    σ = 1 ∨ σ = S.ρ ⟨_, htM⟩ := by
  obtain ⟨⟨x, hxM⟩, hxQt, rfl⟩ := (AS35T.mem_pbar_iff S).mp hσ
  obtain ⟨k, hk₁, hk₂⟩ := S.exists_swap_J hS ht rfl
  have hxP : ∀ y ∈ S.Qa g ⊓ S.M, x * y = y * x := by
    intro y hy
    obtain ⟨hyQt, hyM⟩ := mem_inf.mp hy
    have h1 := hc (S.ρ ⟨y, hyM⟩) ((AS35T.mem_pbar_iff S).mpr ⟨⟨y, hyM⟩, hyQt, rfl⟩)
    refine AS35T.commute_of_mem_Qa_of_comm_mem_QG hS ht hxQt hyQt ?_
    have e : S.ρ (⟨x, hxM⟩ * ⟨y, hyM⟩ * ⟨x, hxM⟩⁻¹ * ⟨y, hyM⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    exact (S.ρ_eq_one_iff _).mp e
  have hx' := AS35T.inv_conj_mem_cq_swap hk₁ hk₂ (mem_inf.mpr ⟨hxQt, hxM⟩)
  have hcl := S.cl_mem_commSpace_of_commute hS.sixFour hS.weak ht htM (mem_inf.mp hx').1
    (fun w hw => by
      have h1 := hxP _ (AS35T.conj_mem_Qa_inf_M_swap hk₁ hk₂ hw)
      calc w * (k⁻¹ * x * k) = k⁻¹ * ((k * w * k⁻¹) * x) * k := by group
        _ = k⁻¹ * (x * (k * w * k⁻¹)) * k := by rw [h1]
        _ = k⁻¹ * x * k * w := by group)
  obtain ⟨w, hw, hwx⟩ := AS35T.exists_mem_inf_Qa_cl_eq hS ht htM hcl
  have hkw := AS35T.conj_mem_inf_Qa_swap hk₁ hk₂ hw
  have hkwM : k * w * k⁻¹ ∈ S.M := S.QG_le_M (mem_inf.mp hkw).1
  have hρkw : S.ρ ⟨k * w * k⁻¹, hkwM⟩ = 1 := (S.ρ_eq_one_iff _).mpr (mem_inf.mp hkw).1
  rcases (S.cl_eq_cl_iff (mem_inf.mp hw).1 (mem_inf.mp hx').1).mp hwx with e | e
  · left
    have e' : x = k * w * k⁻¹ := by rw [← e]; group
    have : (⟨x, hxM⟩ : S.M) = ⟨k * w * k⁻¹, hkwM⟩ := Subtype.ext e'
    rw [this, hρkw]
  · right
    have e' : x = k * w * k⁻¹ * (g * S.z * g⁻¹) := by
      rw [← hk₁]
      calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
        _ = k * w * k⁻¹ * (k * S.z * k⁻¹) := by rw [e]; group
    have : (⟨x, hxM⟩ : S.M) = ⟨k * w * k⁻¹, hkwM⟩ * ⟨_, htM⟩ := Subtype.ext e'
    rw [this, map_mul, hρkw, one_mul]

theorem card_Qa_inf_M_eq :
    Nat.card (S.Qa g ⊓ S.M : Subgroup G) =
      Nat.card (S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G) : Subgroup G) := by
  obtain ⟨k, hk₁, hk₂⟩ := S.exists_swap_J hS ht rfl
  symm
  refine Nat.card_eq_of_bijective (fun y => ⟨k * y * k⁻¹, AS35T.conj_mem_Qa_inf_M_swap hk₁ hk₂ y.2⟩)
    ⟨fun a b hab => ?_, fun p => ?_⟩
  · have e := congrArg Subtype.val hab
    exact Subtype.ext (conj_injective k e)
  · refine ⟨⟨k⁻¹ * p * k, AS35T.inv_conj_mem_cq_swap hk₁ hk₂ p.2⟩, Subtype.ext ?_⟩
    change k * (k⁻¹ * p * k) * k⁻¹ = p
    group

theorem card_pbar :
    Nat.card (((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ) = 2 ^ (2 * S.width - 3) := by
  have h1 := AS35T.card_map_ρ_mul_card_inf_QG S (A := S.Qa g ⊓ S.M) inf_le_right
  have h2 : (S.Qa g ⊓ S.M) ⊓ S.QG = S.QG ⊓ S.Qa g := by
    rw [inf_assoc, inf_of_le_right S.QG_le_M, inf_comm]
  rw [h2, S.card_QG_inf_Qa_of_mem_DSet hS ht, AS35T.card_Qa_inf_M_eq hS ht] at h1
  have htM := S.mem_M_of_mem_ESet hS.sixFour ht.1
  have h3 := (S.fiveOne_two hS.sixFour hS.weak ht htM).2.1
  rw [S.card_QG_eq_card_Q, S.card_Q_eq] at h3
  have hn := hS.three_le_width
  have e : 1 + 2 * S.width = (2 * S.width - 3) + 4 := by omega
  rw [e, pow_add, show (2 : ℕ) ^ 4 = 16 by norm_num] at h3
  have h4 : Nat.card (((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ) * 16 =
      2 ^ (2 * S.width - 3) * 16 := by
    linarith
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h4

theorem conj_mem_pbar_of_commute {c : S.O} (hc : c ∈ S.Mbar)
    (hct : c * S.ρ ⟨_, htM⟩ = S.ρ ⟨_, htM⟩ * c) {σ : S.O}
    (hσ : σ ∈ ((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ) :
    c * σ * c⁻¹ ∈ ((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ := by
  obtain ⟨⟨m, hmM⟩, rfl⟩ := hc
  obtain ⟨m', hm'M, hm't, hm'ρ⟩ := S.exists_commute_rho_eq_J hS ht htM hmM hct
  obtain ⟨⟨x, hxM⟩, hxQt, rfl⟩ := (AS35T.mem_pbar_iff S).mp hσ
  rw [← hm'ρ]
  refine (AS35T.mem_pbar_iff S).mpr ⟨⟨m', hm'M⟩ * ⟨x, hxM⟩ * ⟨m', hm'M⟩⁻¹, ?_, by
    rw [map_mul, map_mul, map_inv]⟩
  exact S.conj_mem_Qa_of_commute_asc hm't hxQt

theorem pbar_fix_commSpace {σ : S.O} (hσ : σ ∈ ((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ)
    {v : S.Qt} (hv : v ∈ commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  obtain ⟨⟨x, hxM⟩, hxQt, rfl⟩ := (AS35T.mem_pbar_iff S).mp hσ
  obtain ⟨w, hw, rfl⟩ := AS35T.exists_mem_inf_Qa_cl_eq hS ht htM hv
  obtain ⟨hwQ, hwQt⟩ := mem_inf.mp hw
  rw [S.ρ_cl ⟨x, hxM⟩ hwQ]
  have hc := AS35T.commute_of_mem_Qa_of_comm_mem_QG hS ht hxQt hwQt
    (S.QG.mul_mem (S.conj_mem_QG hxM hwQ) (S.QG.inv_mem hwQ))
  congr 1
  change x * w * x⁻¹ = w
  rw [hc]
  group

theorem pbar_sub_mem_commSpace {σ : S.O}
    (hσ : σ ∈ ((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ) {v : S.Qt}
    (hv : v ∈ fixSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈
      commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  obtain ⟨⟨x, hxM⟩, hxQt, rfl⟩ := (AS35T.mem_pbar_iff S).mp hσ
  have hK := (S.fiveOne_two hS.sixFour hS.weak ht htM).2.2
  change v ∈ fixSpace (S.rhoL htM) at hv
  rw [← hK] at hv
  obtain ⟨y, hy, hyQ, rfl⟩ := S.mem_clSub_iff.mp hv
  have hyt := (S.mem_inf_centralizer_iff_conj.mp hy).2
  have hyt' : y * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * y := by
    calc y * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * y * (g * S.z * g⁻¹)⁻¹ * (g * S.z * g⁻¹) := by
          rw [hyt]
      _ = g * S.z * g⁻¹ * y := by group
  have hcQ : x * y * x⁻¹ * y⁻¹ ∈ S.QG :=
    S.QG.mul_mem (S.conj_mem_QG hxM hyQ) (S.QG.inv_mem hyQ)
  have hcQt : x * y * x⁻¹ * y⁻¹ ∈ S.Qa g := by
    rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
    exact (S.Qa g).mul_mem hxQt (S.conj_mem_Qa_of_commute_asc hyt' ((S.Qa g).inv_mem hxQt))
  have h1 := AS35T.cl_mem_commSpace_of_mem_inf_Qa hS ht htM (mem_inf.mpr ⟨hcQ, hcQt⟩)
  rw [S.cl_mul (S.conj_mem_QG hxM hyQ) (S.QG.inv_mem hyQ), S.cl_inv hyQ] at h1
  rw [S.ρ_cl ⟨x, hxM⟩ hyQ, sub_eq_add_vec (ZMod 2)]
  exact h1

theorem isExtraspecialPGroup_pbar :
    IsExtraspecialPGroup 2 (((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ) := by
  have htM := S.mem_M_of_mem_ESet hS.sixFour ht.1
  set P := ((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ with hP
  set τ := S.ρ ⟨_, htM⟩ with hτ
  have hτ2 : τ * τ = 1 := AS35T.rho_t_mul_self ht htM
  have hτP : τ ∈ P := AS35T.rho_t_mem_pbar S htM
  have h2 : IsPGroup 2 P := by
    have h0 : IsPGroup 2 (S.Qa g ⊓ S.M : Subgroup G) := (AS35T.isPGroup_Qa S g).to_le inf_le_left
    exact (h0.comap_of_injective (S.M.subtype) S.M.subtype_injective).map S.ρ
  have hτo : orderOf τ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hτ2) (AS35T.rho_t_ne_one hS ht htM)
  have hcen : ∀ σ : S.O, σ ∈ P → ((∀ σ' : S.O, σ' ∈ P → σ * σ' = σ' * σ) ↔ σ ∈ zpowers τ) := by
    intro σ hσ
    rw [mem_zpowers_iff_of_mul_self hτ2]
    constructor
    · exact AS35T.eq_one_or_of_commute_pbar hS ht htM hσ
    · rintro (rfl | rfl) σ' hσ'
      · rw [one_mul, mul_one]
      · obtain ⟨⟨y, hyM⟩, hyQt, rfl⟩ := (AS35T.mem_pbar_iff S).mp hσ'
        rw [hτ, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (AS35T.commute_of_mem_Qa S hyQt).symm
  have hcomm : ∀ σ : S.O, σ ∈ P → ∀ σ' : S.O, σ' ∈ P → ⁅σ, σ'⁆ ∈ zpowers τ := by
    intro σ hσ σ' hσ'
    obtain ⟨⟨x, hxM⟩, hxQt, rfl⟩ := (AS35T.mem_pbar_iff S).mp hσ
    obtain ⟨⟨y, hyM⟩, hyQt, rfl⟩ := (AS35T.mem_pbar_iff S).mp hσ'
    rw [← map_commutatorElement, mem_zpowers_iff_of_mul_self hτ2]
    rcases AS35T.commutator_eq_one_or_of_mem_Qa S hxQt hyQt with h | h
    · left
      have e : ⁅(⟨x, hxM⟩ : S.M), (⟨y, hyM⟩ : S.M)⁆ = 1 := Subtype.ext (by
        simpa [commutatorElement_def] using h)
      rw [e, map_one]
    · right
      have e : ⁅(⟨x, hxM⟩ : S.M), (⟨y, hyM⟩ : S.M)⁆ = (⟨_, htM⟩ : S.M) := Subtype.ext (by
        simpa [commutatorElement_def] using h)
      rw [e]
  have hsq : ∀ σ : S.O, σ ∈ P → σ ^ 2 ∈ zpowers τ := by
    intro σ hσ
    obtain ⟨⟨x, hxM⟩, hxQt, rfl⟩ := (AS35T.mem_pbar_iff S).mp hσ
    rw [← map_pow, mem_zpowers_iff_of_mul_self hτ2]
    rcases AS35T.sq_eq_one_or_of_mem_Qa S hxQt with h | h
    · left
      have e : (⟨x, hxM⟩ : S.M) ^ 2 = 1 := Subtype.ext (by simpa using h)
      rw [e, map_one]
    · right
      have e : (⟨x, hxM⟩ : S.M) ^ 2 = (⟨_, htM⟩ : S.M) := Subtype.ext (by simpa using h)
      rw [e]
  have hnab : ∃ σ : S.O, σ ∈ P ∧ ∃ σ' : S.O, σ' ∈ P ∧ σ * σ' ≠ σ' * σ := by
    by_contra hcon
    push Not at hcon
    have hle : P ≤ zpowers τ := fun σ hσ => (hcen σ hσ).mp (hcon σ hσ)
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hτo, AS35T.card_pbar hS ht] at h1
    have hn := hS.three_le_width
    have h3 : 2 ^ 3 ≤ 2 ^ (2 * S.width - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact (CFSG.LocalAnalysis.GorensteinLyons.isExtraspecialPGroup_two_of_forall h2 hτP hτo hcen
    hcomm hsq hnab).1

end Pbar

end AS35T

end Setting

end CFSG.LargeExtraspecial
