module

public import CFSG.LocalAnalysis.SeitzReduction.EnKLLevi
public import CFSG.LocalAnalysis.SeitzReduction.EnKLHeis
import CFSG.RankThree.GF2n.Stroth80.Sec117ConfigBasic

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.GF2n.Stroth80
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

variable {τ : Tag} {K : Type} [Field K]


private theorem highNode_eq_iθ (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    highNode τ = iθ τ := by
  rcases hτ with rfl | rfl | rfl <;> rfl

private theorem perpNodes_eq_Jθ (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    perpNodes τ = Jθ τ := by
  rcases hτ with rfl | rfl | rfl <;> rfl

private theorem highRadical_eq_subgroupOf_Qθ (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    highRadical τ K = (Qθ τ K).subgroupOf (adjointGroup τ K) := by
  rw [highRadical, perpNodes_eq_Jθ hτ]

private theorem closure_single_le_perpLevi (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    Subgroup.closure {u : adjointGroup τ K |
      ∃ j : Fin τ.rank, j ≠ iθ τ ∧ u = pinnedElt τ (Pi.single j 1) 1} ≤
      perpLevi τ K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro u ⟨j, hj, rfl⟩
  exact pinnedElt_mem_perpLevi (single_mem_perpRoots (by
    intro h
    exact hj (h.trans (highNode_eq_iθ hτ)))) 1

private theorem closure_neg_single_le_perpLevi (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    Subgroup.closure {u : adjointGroup τ K |
      ∃ j : Fin τ.rank, j ≠ iθ τ ∧ u = pinnedElt τ (-Pi.single j 1) 1} ≤
      perpLevi τ K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro u ⟨j, hj, rfl⟩
  exact pinnedElt_mem_perpLevi (neg_single_mem_perpRoots (by
    intro h
    exact hj (h.trans (highNode_eq_iθ hτ)))) 1

private theorem closure_single_le_posUnipotent :
    Subgroup.closure {u : adjointGroup τ K |
      ∃ j : Fin τ.rank, j ≠ iθ τ ∧ u = pinnedElt τ (Pi.single j 1) 1} ≤
      (posUnipotent τ K).subgroupOf (adjointGroup τ K) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro u ⟨j, -, rfl⟩
  exact Subgroup.mem_subgroupOf.2
    (pinnedX_mem_rootSpan (S := {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α})
      ⟨isRoot_single τ j, by rw [height_single]; norm_num⟩ 1)

private theorem closure_neg_single_le_negUnipotent :
    Subgroup.closure {u : adjointGroup τ K |
      ∃ j : Fin τ.rank, j ≠ iθ τ ∧ u = pinnedElt τ (-Pi.single j 1) 1} ≤
      (negUnipotent τ K).subgroupOf (adjointGroup τ K) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro u ⟨j, -, rfl⟩
  exact Subgroup.mem_subgroupOf.2
    (pinnedX_mem_rootSpan (S := {α : Fin τ.rank → ℤ | IsRoot τ α ∧ height α < 0})
      ⟨IsRoot.neg (isRoot_single τ j), by rw [height_neg, height_single]; norm_num⟩ 1)

private theorem isPGroup_closure_single [Finite K] [CharP K 2] :
    IsPGroup 2 (Subgroup.closure {u : adjointGroup τ K |
      ∃ j : Fin τ.rank, j ≠ iθ τ ∧ u = pinnedElt τ (Pi.single j 1) 1}) := by
  have h2 : IsPGroup 2 (posUnipotent τ K) :=
    ((positive_root_triangularity.{0, 0} τ).2 K 2).2.1
  exact (h2.comap_subtype).to_le closure_single_le_posUnipotent

private theorem isPGroup_closure_neg_single [Finite K] [CharP K 2] :
    IsPGroup 2 (Subgroup.closure {u : adjointGroup τ K |
      ∃ j : Fin τ.rank, j ≠ iθ τ ∧ u = pinnedElt τ (-Pi.single j 1) 1}) := by
  have h2 : IsPGroup 2 (negUnipotent τ K) :=
    ((positive_root_triangularity.{0, 0} τ).2 K 2).2.2.2
  exact (h2.comap_subtype).to_le closure_neg_single_le_negUnipotent

private theorem heisCoord_conj_eq_of_comm_mem [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {x : adjointGroup τ K}
    (hxQ : (x : ModGL τ K) ∈ Qθ τ K) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hγ0 : γ (iθ τ) = 0)
    (hfix : pinnedX τ K γ 1 * (x : ModGL τ K) * (pinnedX τ K γ 1)⁻¹ *
      (x : ModGL τ K)⁻¹ ∈ Uθ τ K) :
    heisCoord τ K (pinnedX τ K γ 1 * (x : ModGL τ K) * (pinnedX τ K γ 1)⁻¹) =
      heisCoord τ K (x : ModGL τ K) := by
  have hvQ : pinnedX τ K γ 1 * (x : ModGL τ K) * (pinnedX τ K γ 1)⁻¹ ∈ Qθ τ K :=
    (heisCoord_conj_pinnedX_of_deg_zero hτ hγ hγ0 1 hxQ).1
  have hxInvQ : (x : ModGL τ K)⁻¹ ∈ Qθ τ K := inv_mem hxQ
  have hzero : heisCoord τ K (pinnedX τ K γ 1 * (x : ModGL τ K) * (pinnedX τ K γ 1)⁻¹ *
      (x : ModGL τ K)⁻¹) = 0 :=
    ((heisCoord_spec τ K).eq_zero_iff _ (mul_mem hvQ hxInvQ)).2 hfix
  rw [(heisCoord_spec τ K).mul _ hvQ _ hxInvQ, heisCoord_inv hxQ] at hzero
  funext μ
  have hμ := congrFun hzero μ
  rw [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hμ
  exact sub_eq_zero.1 (by simpa [sub_eq_add_neg] using hμ)

private theorem heisCoord_eq_zero_of_forall_comm_mem [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {x : adjointGroup τ K}
    (hxQ : (x : ModGL τ K) ∈ Qθ τ K)
    (hfix : ∀ j : Fin τ.rank, j ≠ iθ τ →
      (pinnedElt τ (Pi.single j 1) 1 * x * (pinnedElt τ (Pi.single j 1) 1)⁻¹ * x⁻¹ :
        adjointGroup τ K) ∈ (Uθ τ K).subgroupOf (adjointGroup τ K))
    {μ : Fin τ.rank → ℤ} (hμ : μ ≠ highRoot τ - Pi.single (iθ τ) 1) :
    heisCoord τ K (x : ModGL τ K) μ = 0 := by
  refine heisCoord_eq_zero_of_forall_conj_single hτ hxQ ?_ hμ
  intro j hj
  have h : pinnedX τ K (Pi.single j 1) 1 * (x : ModGL τ K) *
      (pinnedX τ K (Pi.single j 1) 1)⁻¹ * (x : ModGL τ K)⁻¹ ∈ Uθ τ K := by
    simpa using Subgroup.mem_subgroupOf.1 (hfix j hj)
  exact heisCoord_conj_eq_of_comm_mem hτ hxQ (isRoot_single τ j)
    (by rw [Pi.single_eq_of_ne (Ne.symm hj)]) h

private theorem heisCoord_eq_zero_of_forall_comm_mem_neg [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {x : adjointGroup τ K}
    (hxQ : (x : ModGL τ K) ∈ Qθ τ K)
    (hfix : ∀ j : Fin τ.rank, j ≠ iθ τ →
      (pinnedElt τ (-Pi.single j 1) 1 * x * (pinnedElt τ (-Pi.single j 1) 1)⁻¹ * x⁻¹ :
        adjointGroup τ K) ∈ (Uθ τ K).subgroupOf (adjointGroup τ K))
    {μ : Fin τ.rank → ℤ} (hμ : μ ≠ Pi.single (iθ τ) 1) :
    heisCoord τ K (x : ModGL τ K) μ = 0 := by
  refine heisCoord_eq_zero_of_forall_conj_neg_single hτ hxQ ?_ hμ
  intro j hj
  have h : pinnedX τ K (-Pi.single j 1) 1 * (x : ModGL τ K) *
      (pinnedX τ K (-Pi.single j 1) 1)⁻¹ * (x : ModGL τ K)⁻¹ ∈ Uθ τ K := by
    simpa using Subgroup.mem_subgroupOf.1 (hfix j hj)
  exact heisCoord_conj_eq_of_comm_mem hτ hxQ (IsRoot.neg (isRoot_single τ j))
    (by rw [Pi.neg_apply, Pi.single_eq_of_ne (Ne.symm hj), neg_zero]) h

private theorem mem_Qθ_of_mem_highRadical (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {x : adjointGroup τ K} (hx : x ∈ highRadical τ K) : (x : ModGL τ K) ∈ Qθ τ K := by
  have h1 := hx
  rw [highRadical_eq_subgroupOf_Qθ hτ] at h1
  exact Subgroup.mem_subgroupOf.1 h1

private theorem conj_mem_subgroupOf_Uθ_of_mem_Qθ {x z : adjointGroup τ K}
    (hx : (x : ModGL τ K) ∈ Qθ τ K)
    (hz : z ∈ (Uθ τ K).subgroupOf (adjointGroup τ K)) :
    x * z * x⁻¹ ∈ (Uθ τ K).subgroupOf (adjointGroup τ K) := by
  have hxpos : (x : ModGL τ K) ∈ posUnipotent τ K :=
    parabolicRadical_le_posUnipotent _ hx
  have hzU : (z : ModGL τ K) ∈ Uθ τ K := Subgroup.mem_subgroupOf.1 hz
  have hcomm : (x : ModGL τ K) * (z : ModGL τ K) = (z : ModGL τ K) * (x : ModGL τ K) :=
    (CoordAux.Uθ_comm hzU hxpos).symm
  have heq : x * z * x⁻¹ = z := by
    apply Subtype.ext
    show (x : ModGL τ K) * z * x⁻¹ = z
    rw [hcomm, mul_assoc, Subgroup.coe_inv, mul_inv_cancel, mul_one]
  rwa [heq]

private theorem conj_mem_subgroupOf_Uθ_of_mem_rootSpan_perpRoots
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {u z : adjointGroup τ K}
    (hu : (u : ModGL τ K) ∈ rootSpan τ K (perpRoots τ))
    (hz : z ∈ (Uθ τ K).subgroupOf (adjointGroup τ K)) :
    u * z * u⁻¹ ∈ (Uθ τ K).subgroupOf (adjointGroup τ K) := by
  have hzU : (z : ModGL τ K) ∈ Uθ τ K := Subgroup.mem_subgroupOf.1 hz
  obtain ⟨c, hc⟩ := CFSG.Blueprint.Chevalley.mem_rootSubgroup.1 hzU
  have hcomm : (u : ModGL τ K) * (z : ModGL τ K) = (z : ModGL τ K) * (u : ModGL τ K) := by
    rw [← hc]
    exact commute_pinnedX_highRoot_of_mem_perpLevi hτ hu c
  have heq : u * z * u⁻¹ = z := by
    apply Subtype.ext
    show (u : ModGL τ K) * z * u⁻¹ = z
    rw [hcomm, mul_assoc, Subgroup.coe_inv, mul_inv_cancel, mul_one]
  rwa [heq]

private theorem mem_coord_supported_of_forall_comm_mem [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {x : adjointGroup τ K}
    (hxQ : (x : ModGL τ K) ∈ Qθ τ K)
    (hfix : ∀ u ∈ Subgroup.closure {u : adjointGroup τ K |
        ∃ j : Fin τ.rank, j ≠ iθ τ ∧ u = pinnedElt τ (Pi.single j 1) 1},
      u * x * u⁻¹ * x⁻¹ ∈ (Uθ τ K).subgroupOf (adjointGroup τ K)) :
    (x : ModGL τ K) ∈ Qθ τ K ∧ ∀ μ : Fin τ.rank → ℤ,
      μ ≠ highRoot τ - Pi.single (iθ τ) 1 → heisCoord τ K (x : ModGL τ K) μ = 0 :=
  ⟨hxQ, fun _μ hμ => heisCoord_eq_zero_of_forall_comm_mem hτ hxQ
    (fun j hj => hfix _ (Subgroup.subset_closure ⟨j, hj, rfl⟩)) hμ⟩

private theorem mem_coord_supported_of_forall_comm_mem_neg [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {x : adjointGroup τ K}
    (hxQ : (x : ModGL τ K) ∈ Qθ τ K)
    (hfix : ∀ u ∈ Subgroup.closure {u : adjointGroup τ K |
        ∃ j : Fin τ.rank, j ≠ iθ τ ∧ u = pinnedElt τ (-Pi.single j 1) 1},
      u * x * u⁻¹ * x⁻¹ ∈ (Uθ τ K).subgroupOf (adjointGroup τ K)) :
    (x : ModGL τ K) ∈ Qθ τ K ∧ ∀ μ : Fin τ.rank → ℤ,
      μ ≠ Pi.single (iθ τ) 1 → heisCoord τ K (x : ModGL τ K) μ = 0 :=
  ⟨hxQ, fun _μ hμ => heisCoord_eq_zero_of_forall_comm_mem_neg hτ hxQ
    (fun j hj => hfix _ (Subgroup.subset_closure ⟨j, hj, rfl⟩)) hμ⟩

private theorem mul_ne_mul_of_mem_coord_supported [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {v v' : adjointGroup τ K}
    (hv : (v : ModGL τ K) ∈ Qθ τ K) (hv' : (v' : ModGL τ K) ∈ Qθ τ K)
    (hsv : ∀ μ : Fin τ.rank → ℤ, μ ≠ highRoot τ - Pi.single (iθ τ) 1 →
      heisCoord τ K (v : ModGL τ K) μ = 0)
    (hsv' : ∀ μ : Fin τ.rank → ℤ, μ ≠ Pi.single (iθ τ) 1 →
      heisCoord τ K (v' : ModGL τ K) μ = 0)
    (hvU : v ∉ (Uθ τ K).subgroupOf (adjointGroup τ K))
    (hv'U : v' ∉ (Uθ τ K).subgroupOf (adjointGroup τ K)) :
    v * v' ≠ v' * v := by
  intro h
  exact mul_ne_mul_of_heisCoord_support hτ hv hv' hsv hsv'
    (fun h' => hvU (Subgroup.mem_subgroupOf.2 h'))
    (fun h' => hv'U (Subgroup.mem_subgroupOf.2 h'))
    (congrArg Subtype.val h)

private theorem conj_mem_A_of_le_perpLevi {a : ℕ} {N A : Subgroup (adjointGroup τ K)}
    (h : IsKLConfig (pinnedElt τ (highRoot τ) (1 : K)) a N A) (hDN : perpLevi τ K ≤ N)
    {H : Subgroup (adjointGroup τ K)} (hH : H ≤ perpLevi τ K) :
    ∀ u ∈ H, ∀ x ∈ A, u * x * u⁻¹ ∈ A :=
  fun u hu x hx => h.conj_mem u (hDN (hH hu)) x hx

private theorem conj_mem_subgroupOf_Uθ_of_le_perpLevi (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {H : Subgroup (adjointGroup τ K)} (hH : H ≤ perpLevi τ K) :
    ∀ u ∈ H, ∀ z ∈ (Uθ τ K).subgroupOf (adjointGroup τ K),
      u * z * u⁻¹ ∈ (Uθ τ K).subgroupOf (adjointGroup τ K) :=
  fun _u hu _z hz => conj_mem_subgroupOf_Uθ_of_mem_rootSpan_perpRoots hτ
    (Subgroup.mem_subgroupOf.1 (hH hu)) hz

private theorem conj_mem_subgroupOf_Uθ_of_mem_A (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {A : Subgroup (adjointGroup τ K)} (hAQ : A ≤ highRadical τ K) :
    ∀ x ∈ A, ∀ z ∈ (Uθ τ K).subgroupOf (adjointGroup τ K),
      x * z * x⁻¹ ∈ (Uθ τ K).subgroupOf (adjointGroup τ K) :=
  fun _x hx _z hz =>
    conj_mem_subgroupOf_Uθ_of_mem_Qθ (mem_Qθ_of_mem_highRadical hτ (hAQ hx)) hz

theorem le_rootSubgroup_highRoot_of_isKLConfig [Finite K] [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {a : ℕ} {N A : Subgroup (adjointGroup τ K)}
    (h : IsKLConfig (pinnedElt τ (highRoot τ) (1 : K)) a N A) (hDN : perpLevi τ K ≤ N)
    (hAQ : A ≤ highRadical τ K) :
    ∀ x ∈ A, (x : ModGL τ K) ∈ rootSubgroup τ K (highRoot τ) := by
  have hEnd : Finite (Module.End K (RootModule τ K)) := Module.finite_of_finite K
  have hGL : Finite (ModGL τ K) := Finite.of_injective Units.val fun _ _ h => Units.ext h
  have hAdj : Finite (adjointGroup τ K) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let Z₀ : Subgroup (adjointGroup τ K) := (Uθ τ K).subgroupOf (adjointGroup τ K)
  let U : Subgroup (adjointGroup τ K) := Subgroup.closure {u : adjointGroup τ K |
    ∃ j : Fin τ.rank, j ≠ iθ τ ∧ u = pinnedElt τ (Pi.single j 1) 1}
  let U' : Subgroup (adjointGroup τ K) := Subgroup.closure {u : adjointGroup τ K |
    ∃ j : Fin τ.rank, j ≠ iθ τ ∧ u = pinnedElt τ (-Pi.single j 1) 1}
  let V : Set (adjointGroup τ K) := {x | (x : ModGL τ K) ∈ Qθ τ K ∧
    ∀ μ : Fin τ.rank → ℤ, μ ≠ highRoot τ - Pi.single (iθ τ) 1 →
      heisCoord τ K (x : ModGL τ K) μ = 0}
  let V' : Set (adjointGroup τ K) := {x | (x : ModGL τ K) ∈ Qθ τ K ∧
    ∀ μ : Fin τ.rank → ℤ, μ ≠ Pi.single (iθ τ) 1 →
      heisCoord τ K (x : ModGL τ K) μ = 0}
  have hUA := conj_mem_A_of_le_perpLevi h hDN (closure_single_le_perpLevi hτ)
  have hU'A := conj_mem_A_of_le_perpLevi h hDN (closure_neg_single_le_perpLevi hτ)
  have hUZ := conj_mem_subgroupOf_Uθ_of_le_perpLevi (K := K) hτ (closure_single_le_perpLevi hτ)
  have hU'Z := conj_mem_subgroupOf_Uθ_of_le_perpLevi (K := K) hτ (closure_neg_single_le_perpLevi hτ)
  have hV : ∀ x ∈ A, (∀ u ∈ U, u * x * u⁻¹ * x⁻¹ ∈ Z₀) → x ∈ V :=
    fun x hx hfix => mem_coord_supported_of_forall_comm_mem hτ
      (mem_Qθ_of_mem_highRadical hτ (hAQ hx)) (by simpa only [U, Z₀] using hfix)
  have hV' : ∀ x ∈ A, (∀ u ∈ U', u * x * u⁻¹ * x⁻¹ ∈ Z₀) → x ∈ V' :=
    fun x hx hfix => mem_coord_supported_of_forall_comm_mem_neg hτ
      (mem_Qθ_of_mem_highRadical hτ (hAQ hx)) (by simpa only [U', Z₀] using hfix)
  have hVV' : ∀ v ∈ V, ∀ v' ∈ V', v ∉ Z₀ → v' ∉ Z₀ → v * v' ≠ v' * v := by
    intro v hv v' hv' hvZ hv'Z hvv'
    dsimp only [V, V', Z₀] at hv hv' hvZ hv'Z
    exact mul_ne_mul_of_mem_coord_supported hτ hv.1 hv'.1 hv.2 hv'.2 hvZ hv'Z hvv'
  have hmain : A ≤ Z₀ := le_of_fixed_of_ne_commute (U := U) (U' := U') (V := V)
    (V' := V') h.comm h.isPGroup (conj_mem_subgroupOf_Uθ_of_mem_A hτ hAQ)
    (isPGroup_closure_single (K := K)) hUA hUZ
    (isPGroup_closure_neg_single (K := K)) hU'A hU'Z hV hV' hVV'
  exact fun x hx => Subgroup.mem_subgroupOf.1 (hmain hx)

theorem false_of_isKLConfig_pinnedElt_highRoot [Finite K] [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hD : CFSG.IsQuasisimple (perpLevi τ K))
    (hDZ : center (perpLevi τ K) = ⊥) {a : ℕ} {N A : Subgroup (adjointGroup τ K)}
    (h : IsKLConfig (pinnedElt τ (highRoot τ) (1 : K)) a N A) : False := by
  have hDN := perpLevi_le_of_isA2PlaneKernel hτ hD hDZ h.kernel
  have hAU := le_rootSubgroup_highRoot_of_isKLConfig hτ h hDN
    (le_highRadical_of_isKLConfig hτ hD hDZ h hDN)
  obtain ⟨u, huD, hu3, huθ⟩ := exists_mem_perpLevi_orderOf_eq_three (K := K) hτ
  have hu1 : u = 1 := h.eq_one u (hDN huD) (by rw [hu3]; exact ⟨1, rfl⟩) fun x hx => by
    obtain ⟨c, hc⟩ := mem_rootSubgroup.1 (hAU x hx)
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc]
    exact huθ c
  rw [hu1, orderOf_one] at hu3
  omega

end CFSG.SeitzReduction.EPilot
