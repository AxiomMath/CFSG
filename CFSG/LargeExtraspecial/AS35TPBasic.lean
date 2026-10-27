module

public import CFSG.LargeExtraspecial.AS35JFiveNineTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] (S : Setting G)

namespace AS35T

theorem conj_eq_of_conj_mem_Qa (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    {g k : G} (hk : k * S.z * k⁻¹ ∈ S.Qa g) : k * S.z * k⁻¹ = g * S.z * g⁻¹ := by
  rw [S.mem_Qa_iff_inv_conj_mem] at hk
  have h1 := hW (g⁻¹ * k) (by
    rwa [show g⁻¹ * k * S.z * (g⁻¹ * k)⁻¹ = g⁻¹ * (k * S.z * k⁻¹) * g by group])
  calc k * S.z * k⁻¹ = g * (g⁻¹ * k * S.z * (g⁻¹ * k)⁻¹) * g⁻¹ := by group
    _ = g * S.z * g⁻¹ := by rw [h1]

theorem commutator_eq_one_or_of_mem_Qa {g x y : G} (hx : x ∈ S.Qa g) (hy : y ∈ S.Qa g) :
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = g * S.z * g⁻¹ :=
  (S.conjBy g).commutator_eq_one_or_z hx hy

theorem commute_of_mem_Qa {g x : G} (hx : x ∈ S.Qa g) :
    x * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * x :=
  (S.conjBy g).z_comm_QG hx

theorem isPGroup_Qa (g : G) : IsPGroup 2 (S.Qa g) := (S.conjBy g).isPGroup_QG

end AS35T

variable [Finite G]

namespace AS35T

theorem sq_eq_one_or_of_mem_Qa {g x : G} (hx : x ∈ S.Qa g) :
    x ^ 2 = 1 ∨ x ^ 2 = g * S.z * g⁻¹ :=
  (S.conjBy g).sq_eq_one_or_z hx

section Inter

variable {S}
variable (hS : S.SixHyp) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet)
include hS ht

theorem cl_mem_commSpace_of_mem_inf_Qa (htM : g * S.z * g⁻¹ ∈ S.M) {w : G}
    (hw : w ∈ S.QG ⊓ S.Qa g) : S.cl w ∈ commSpace (S.rhoL htM) :=
  S.cl_mem_commSpace_of_commute hS.sixFour hS.weak ht htM (mem_inf.mp hw).1
    (S.commute_of_mem_inf_Qa_J hS ht rfl hw)

theorem eq_of_cl_eq_of_mem_inf_Qa {w₁ w₂ : G} (h₁ : w₁ ∈ S.QG ⊓ S.Qa g)
    (h₂ : w₂ ∈ S.QG ⊓ S.Qa g) (h : S.cl w₁ = S.cl w₂) : w₁ = w₂ := by
  rcases (S.cl_eq_cl_iff (mem_inf.mp h₁).1 (mem_inf.mp h₂).1).mp h with e | e
  · exact e.symm
  · exfalso
    apply S.z_not_mem_Qa hS.weak (S.ne_z_of_mem_ESet ht.1)
    have e' : S.z = w₁⁻¹ * w₂ := by rw [e]; group
    rw [e']
    exact (S.Qa g).mul_mem ((S.Qa g).inv_mem (mem_inf.mp h₁).2) (mem_inf.mp h₂).2

theorem exists_mem_inf_Qa_cl_eq (htM : g * S.z * g⁻¹ ∈ S.M) {v : S.Qt}
    (hv : v ∈ commSpace (S.rhoL htM)) : ∃ w ∈ S.QG ⊓ S.Qa g, S.cl w = v := by
  set t := g * S.z * g⁻¹ with htdef
  have htt : t * t = 1 := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
  obtain ⟨u, rfl⟩ := mem_commSpace.mp hv
  obtain ⟨y, hy, rfl⟩ := S.exists_cl u
  obtain ⟨h1, h2⟩ := S.cl_conj_mul_eq htM htt hy
  have hpH : y * t * y⁻¹ ∈ S.zConj (S.HAt g) :=
    Asc77.conj_mem_conjIn_of_mem (le_sup_left (b := S.Qa g) hy)
      (S.mem_zConj_of_mem_ESet ht.1 rfl)
  by_cases hpt : y * t * y⁻¹ = t
  · refine ⟨1, one_mem _, ?_⟩
    rw [← h2, hpt, htt]
  · have hpz : y * t * y⁻¹ * S.z ∈ S.Qa g := S.mul_z_mem_Qa_of_mem_zConj hS ht rfl hpH hpt
    refine ⟨y * t * y⁻¹ * t * S.z, mem_inf.mpr ⟨S.QG.mul_mem h1 S.z_mem_QG, ?_⟩, ?_⟩
    · have e : y * t * y⁻¹ * t * S.z = y * t * y⁻¹ * S.z * t := by
        rw [mul_assoc (y * t * y⁻¹) t, S.mem_M_iff.mp htM, ← mul_assoc]
      rw [e]
      exact (S.Qa g).mul_mem hpz (S.conj_z_mem_Qa g)
    · rw [S.cl_mul_z h1, h2]

theorem sq_eq_one_of_mem_inf_Qa {w : G} (hw : w ∈ S.QG ⊓ S.Qa g) : w ^ 2 = 1 := by
  have htM := S.mem_M_of_mem_ESet hS.sixFour ht.1
  have hA := (S.fiveOne_two hS.sixFour hS.weak ht htM).1
  rw [← S.q_cl_eq_zero_iff (mem_inf.mp hw).1]
  exact hA.2.2.2.2 _ (AS35T.cl_mem_commSpace_of_mem_inf_Qa hS ht htM hw)

theorem commute_of_mem_inf_Qa_of_fix (htM : g * S.z * g⁻¹ ∈ S.M) {x : G} (hxM : x ∈ S.M)
    (hxQt : ∀ y ∈ S.Qa g, x * y * x⁻¹ ∈ S.Qa g)
    (hfix : ∀ v ∈ commSpace (S.rhoL htM), S.rhoL hxM v = v) {w : G}
    (hw : w ∈ S.QG ⊓ S.Qa g) : x * w * x⁻¹ = w := by
  obtain ⟨hwQ, hwQt⟩ := mem_inf.mp hw
  have h1 := hfix _ (AS35T.cl_mem_commSpace_of_mem_inf_Qa hS ht htM hw)
  rw [S.rhoL_cl hxM hwQ] at h1
  exact AS35T.eq_of_cl_eq_of_mem_inf_Qa hS ht
    (mem_inf.mpr ⟨S.conj_mem_QG hxM hwQ, hxQt w hwQt⟩) hw h1

end Inter

end AS35T

theorem card_QG_inf_Qa_of_mem_DSet (hS : S.SixHyp) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet) :
    Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 4 := by
  have htM := S.mem_M_of_mem_ESet hS.sixFour ht.1
  have hdim : finrank (ZMod 2) (commSpace (S.rhoL htM)) = 2 :=
    (S.fiveOne_two hS.sixFour hS.weak ht htM).1.2.2.2.1
  have hc : Nat.card (commSpace (S.rhoL htM)) = 4 := by
    rw [S.card_submodule, hdim]
    norm_num
  rw [← hc]
  refine Nat.card_eq_of_bijective
    (fun w => ⟨S.cl w, AS35T.cl_mem_commSpace_of_mem_inf_Qa hS ht htM w.2⟩) ⟨?_, ?_⟩
  · intro w₁ w₂ h
    exact Subtype.ext (AS35T.eq_of_cl_eq_of_mem_inf_Qa hS ht w₁.2 w₂.2 (congrArg Subtype.val h))
  · intro v
    obtain ⟨w, hw, hwv⟩ := AS35T.exists_mem_inf_Qa_cl_eq hS ht htM v.2
    exact ⟨⟨w, hw⟩, Subtype.ext hwv⟩

namespace AS35T

section Swap

variable {S}

omit [Finite G] in
theorem swap_inv {g k : G} (hk₁ : k * S.z * k⁻¹ = g * S.z * g⁻¹)
    (hk₂ : k * (g * S.z * g⁻¹) * k⁻¹ = S.z) : k⁻¹ * S.z * k⁻¹⁻¹ = g * S.z * g⁻¹ ∧
    k⁻¹ * (g * S.z * g⁻¹) * k⁻¹⁻¹ = S.z := by
  constructor
  · calc k⁻¹ * S.z * k⁻¹⁻¹ = k⁻¹ * (k * (g * S.z * g⁻¹) * k⁻¹) * k⁻¹⁻¹ := by rw [hk₂]
      _ = g * S.z * g⁻¹ := by group
  · calc k⁻¹ * (g * S.z * g⁻¹) * k⁻¹⁻¹ = k⁻¹ * (k * S.z * k⁻¹) * k⁻¹⁻¹ := by rw [hk₁]
      _ = S.z := by group

theorem conj_mem_Qa_of_mem_QG_swap {g k : G} (hk₁ : k * S.z * k⁻¹ = g * S.z * g⁻¹) {y : G}
    (hy : y ∈ S.QG) : k * y * k⁻¹ ∈ S.Qa g := by
  rw [← S.Qa_eq_of_conj_eq hk₁, S.mem_Qa_iff_inv_conj_mem]
  rwa [show k⁻¹ * (k * y * k⁻¹) * k = y by group]

omit [Finite G] in
theorem mul_self_mem_M_swap {g k : G} (hk₁ : k * S.z * k⁻¹ = g * S.z * g⁻¹)
    (hk₂ : k * (g * S.z * g⁻¹) * k⁻¹ = S.z) : k * k ∈ S.M := by
  apply S.mem_M_of_conj_eq_z
  rw [show k * k * S.z * (k * k)⁻¹ = k * (k * S.z * k⁻¹) * k⁻¹ by group, hk₁, hk₂]

theorem conj_mem_QG_of_mem_Qa_swap {g k : G} (hk₁ : k * S.z * k⁻¹ = g * S.z * g⁻¹)
    (hk₂ : k * (g * S.z * g⁻¹) * k⁻¹ = S.z) {y : G} (hy : y ∈ S.Qa g) :
    k * y * k⁻¹ ∈ S.QG := by
  rw [← S.Qa_eq_of_conj_eq hk₁, S.mem_Qa_iff_inv_conj_mem] at hy
  have h1 := S.conj_mem_QG (AS35T.mul_self_mem_M_swap hk₁ hk₂) hy
  rwa [show k * k * (k⁻¹ * y * k) * (k * k)⁻¹ = k * y * k⁻¹ by group] at h1

omit [Finite G] in
theorem conj_mem_M_of_commute_swap {g k : G} (hk₂ : k * (g * S.z * g⁻¹) * k⁻¹ = S.z) {y : G}
    (hy : y * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * y) : k * y * k⁻¹ ∈ S.M := by
  rw [S.mem_M_iff]
  calc k * y * k⁻¹ * S.z = k * y * k⁻¹ * (k * (g * S.z * g⁻¹) * k⁻¹) := by rw [hk₂]
    _ = k * (y * (g * S.z * g⁻¹)) * k⁻¹ := by group
    _ = k * (g * S.z * g⁻¹ * y) * k⁻¹ := by rw [hy]
    _ = k * (g * S.z * g⁻¹) * k⁻¹ * (k * y * k⁻¹) := by group
    _ = S.z * (k * y * k⁻¹) := by rw [hk₂]

omit [Finite G] in
theorem conj_commute_of_mem_M_swap {g k : G} (hk₁ : k * S.z * k⁻¹ = g * S.z * g⁻¹) {y : G}
    (hy : y ∈ S.M) : k * y * k⁻¹ * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * (k * y * k⁻¹) := by
  have hy' := S.mem_M_iff.mp hy
  calc k * y * k⁻¹ * (g * S.z * g⁻¹) = k * y * k⁻¹ * (k * S.z * k⁻¹) := by rw [hk₁]
    _ = k * (y * S.z) * k⁻¹ := by group
    _ = k * (S.z * y) * k⁻¹ := by rw [hy']
    _ = k * S.z * k⁻¹ * (k * y * k⁻¹) := by group
    _ = g * S.z * g⁻¹ * (k * y * k⁻¹) := by rw [hk₁]

theorem conj_mem_Qa_inf_M_swap {g k : G} (hk₁ : k * S.z * k⁻¹ = g * S.z * g⁻¹)
    (hk₂ : k * (g * S.z * g⁻¹) * k⁻¹ = S.z) {y : G}
    (hy : y ∈ S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G)) : k * y * k⁻¹ ∈ S.Qa g ⊓ S.M := by
  obtain ⟨hyQ, hyc⟩ := mem_inf.mp hy
  exact mem_inf.mpr ⟨AS35T.conj_mem_Qa_of_mem_QG_swap hk₁ hyQ,
    AS35T.conj_mem_M_of_commute_swap hk₂ (mem_centralizer_singleton_iff.mp hyc)⟩

theorem inv_conj_mem_cq_swap {g k : G} (hk₁ : k * S.z * k⁻¹ = g * S.z * g⁻¹)
    (hk₂ : k * (g * S.z * g⁻¹) * k⁻¹ = S.z) {p : G} (hp : p ∈ S.Qa g ⊓ S.M) :
    k⁻¹ * p * k ∈ S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G) := by
  obtain ⟨hi₁, hi₂⟩ := AS35T.swap_inv hk₁ hk₂
  obtain ⟨hpQt, hpM⟩ := mem_inf.mp hp
  have h1 := AS35T.conj_mem_QG_of_mem_Qa_swap hi₁ hi₂ hpQt
  have h2 := AS35T.conj_commute_of_mem_M_swap hi₁ hpM
  rw [inv_inv] at h1 h2
  exact mem_inf.mpr ⟨h1, mem_centralizer_singleton_iff.mpr h2⟩

theorem conj_mem_inf_Qa_swap {g k : G} (hk₁ : k * S.z * k⁻¹ = g * S.z * g⁻¹)
    (hk₂ : k * (g * S.z * g⁻¹) * k⁻¹ = S.z) {w : G} (hw : w ∈ S.QG ⊓ S.Qa g) :
    k * w * k⁻¹ ∈ S.QG ⊓ S.Qa g :=
  mem_inf.mpr ⟨AS35T.conj_mem_QG_of_mem_Qa_swap hk₁ hk₂ (mem_inf.mp hw).2,
    AS35T.conj_mem_Qa_of_mem_QG_swap hk₁ (mem_inf.mp hw).1⟩

end Swap

end AS35T

end Setting

end CFSG.LargeExtraspecial
