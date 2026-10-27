module

public import CFSG.ClassicalInvolution.Q3.Q3ExcAmalgam
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerBlocks
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthLift

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups commutatorElement

theorem exc3_involution_eq {Y : Type} [Group Y] {L : Subgroup Y} {z : Y}
    (hz : z ∈ L) (hz2 : orderOf z = 2) (e : SL(2, ZMod 3) ≃* L) :
    (⟨z, hz⟩ : L) = e (-1) := by
  have h1 : orderOf (e.symm ⟨z, hz⟩) = 2 := by
    have := orderOf_injective e.symm.toMonoidHom e.symm.injective ⟨z, hz⟩
    simp only [MulEquiv.coe_toMonoidHom] at this
    rw [this, Subgroup.orderOf_mk]
    exact hz2
  have h2 := exc3_eq_neg_one_of_orderOf_eq_two h1
  rw [← h2]
  exact (e.apply_symm_apply _).symm

theorem exc3_eq_one_or_eq_of_central {Y : Type} [Group Y] {L : Subgroup Y} {z : Y}
    (hz : z ∈ L) (hz2 : orderOf z = 2) (e : SL(2, ZMod 3) ≃* L) {x : Y} (hx : x ∈ L)
    (hc : ∀ y ∈ L, y * x = x * y) : x = 1 ∨ x = z := by
  have key : ∀ g : SL(2, ZMod 3), (∀ y : SL(2, ZMod 3), y * g = g * y) → g = 1 ∨ g = -1 := by
    decide +kernel
  have hc' : ∀ y : SL(2, ZMod 3), y * e.symm ⟨x, hx⟩ = e.symm ⟨x, hx⟩ * y := by
    intro y
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subtype.ext (hc _ (e y).2)
  have hzeq := exc3_involution_eq hz hz2 e
  rcases key _ hc' with h | h
  · left
    have : (⟨x, hx⟩ : L) = 1 := by
      have := congrArg e h
      rw [MulEquiv.apply_symm_apply, map_one] at this
      exact this
    exact congrArg Subtype.val this
  · right
    have : (⟨x, hx⟩ : L) = ⟨z, hz⟩ := by
      have := congrArg e h
      rw [MulEquiv.apply_symm_apply] at this
      rw [this, hzeq]
    exact congrArg Subtype.val this

theorem exc3_isClassicalMember3_map {K C : Type} [Group K] [Finite K] [Group C] (θ : K →* C)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center K) {L : Subgroup K} {z : K}
    (h : IsClassicalMember3 L z) (hO : classicalInvolutionOddCore L = ⊥) (hz : θ z ≠ 1) :
    IsClassicalMember3 (L.map θ) (θ z) ∧ classicalInvolutionOddCore (L.map θ) = ⊥ := by
  obtain ⟨e₀⟩ := h.nonempty_equiv_sl2 hO
  have e : SL(2, ZMod 3) ≃* L := e₀.symm
  have hinj : Function.Injective (θ.subgroupMap L) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hx1 : θ ((x : L) : K) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      simpa using this
    have hxc : ((x : L) : K) ∈ Subgroup.center K := hker (MonoidHom.mem_ker.mpr hx1)
    rcases exc3_eq_one_or_eq_of_central h.mem h.orderOf_eq_two e (x : L).2
        (fun y hy => (Subgroup.mem_center_iff.mp hxc y)) with h1 | h1
    · exact Subtype.ext h1
    · exact absurd (by rw [← h1]; exact hx1) hz
  let eθ : L ≃* L.map θ :=
    MulEquiv.ofBijective (θ.subgroupMap L) ⟨hinj, MonoidHom.subgroupMap_surjective θ L⟩
  have hO' : classicalInvolutionOddCore (L.map θ) = ⊥ := oddCore_eq_bot_of_equiv eθ.symm hO
  refine ⟨⟨?_, Subgroup.mem_map_of_mem θ h.mem, ?_, ?_⟩, hO'⟩
  · refine orderOf_eq_prime ?_ hz
    rw [← map_pow, ← h.orderOf_eq_two, pow_orderOf_eq_one, map_one]
  · have hA := isSubnormal_map θ h.subnormal
    set B := Subgroup.centralizer ({θ z} : Set C) with hB
    set A := (Subgroup.centralizer ({z} : Set K)).map θ with hA'
    have hle : A ≤ B := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hB, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp hx]
    have hcomm : ⁅B, B⁆ ≤ A := by
      have h1 := commutator_le_map_centralizer θ hker z
      rwa [MonoidHom.range_eq_top.2 hθ, top_inf_eq] at h1
    have hnorm : (A.subgroupOf B).Normal := by
      refine ⟨fun a ha x => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      have hc : ⁅(x : C), (a : C)⁆ ∈ A := hcomm (Subgroup.commutator_mem_commutator x.2 a.2)
      have e : ((x * a * x⁻¹ : B) : C) = ⁅(x : C), (a : C)⁆ * (a : C) := by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact A.mul_mem hc ha
    exact isSubnormal_trans hA (IsSubnormal.step hle hnorm (IsSubnormal.refl B))
  · exact ⟨((QuotientGroup.quotientMulEquivOfEq hO').trans QuotientGroup.quotientBot).trans
      (eθ.symm.trans e.symm)⟩

theorem exc3_false_of_central_involution {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) {L : Subgroup K} {z : K} (h : IsClassicalMember3 L z)
    (hO : classicalInvolutionOddCore L = ⊥) (hzc : z ∈ Subgroup.center K) : False := by
  obtain ⟨e₀⟩ := h.nonempty_equiv_sl2 hO
  have hC : Subgroup.centralizer ({z} : Set K) = ⊤ := by
    refine eq_top_iff.mpr fun g _ => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp hzc g)
  have hsub : IsSubnormal L ⊤ := hC ▸ h.subnormal
  have hqs : CFSG.Open.IsQuasisimple (⊤ : Subgroup K) :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv Subgroup.topEquiv hK
  exact not_isQuasisimple_of_member3 e₀.symm le_top hsub hqs

theorem exc3_closure_pow_three_eq_top {G : Type*} [Group G] {A B : Subgroup G}
    (hA : ∀ x ∈ A, x ^ 3 = 1) (hB : ∀ x ∈ B, x ^ 3 = 1) :
    Subgroup.closure {y : ↥(A ⊔ B) | y ^ 3 = 1} = ⊤ := by
  set T := Subgroup.closure {y : ↥(A ⊔ B) | y ^ 3 = 1} with hT
  have key : ∀ y, y ∈ Subgroup.closure ((A : Set G) ∪ (B : Set G)) →
      ∃ hy : y ∈ A ⊔ B, (⟨y, hy⟩ : ↥(A ⊔ B)) ∈ T := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨Subgroup.mem_sup_left hx, Subgroup.subset_closure (Subtype.ext (hA x hx))⟩
      · exact ⟨Subgroup.mem_sup_right hx, Subgroup.subset_closure (Subtype.ext (hB x hx))⟩
    | one => exact ⟨one_mem _, T.one_mem⟩
    | mul x y hx hy hxT hyT =>
      obtain ⟨h1, h2⟩ := hxT
      obtain ⟨h3, h4⟩ := hyT
      exact ⟨mul_mem h1 h3, T.mul_mem h2 h4⟩
    | inv x hx hxT =>
      obtain ⟨h1, h2⟩ := hxT
      exact ⟨inv_mem h1, T.inv_mem h2⟩
  rw [eq_top_iff]
  intro y _
  obtain ⟨_, h⟩ := key y.1 (by rw [← Subgroup.sup_eq_closure]; exact y.2)
  exact h

theorem exc3_ker_eq_center {K C : Type} [Group K] [Group C] (θ : K →* C)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center K)
    (hC : Subgroup.center C = ⊥) : θ.ker = Subgroup.center K := by
  refine le_antisymm hker fun c hc => ?_
  have h1 : θ c ∈ Subgroup.center C := map_center_le_center θ hθ ⟨c, hc, rfl⟩
  rw [hC, Subgroup.mem_bot] at h1
  exact MonoidHom.mem_ker.mpr h1

theorem exc3_simpleOddCentralizer_of_cover {K C : Type} [Group K] [Finite K] [Group C] [Finite C]
    (θ : K →* C) (hθ : Function.Surjective θ) (hker : θ.ker = Subgroup.center K)
    (hC : ∀ c : C, c * c = 1 → oddCoreIn (Subgroup.centralizer ({c} : Set C)) = ⊥)
    (s : K ⧸ Subgroup.center K) (hs : orderOf s = 2) :
    CFSG.Assembly.Dichotomy.involutionOddCore s = ⊥ := by
  let e : K ⧸ Subgroup.center K ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hθ)
  have hs2 : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs, pow_two] at this
  rw [involutionOddCore_eq_oddCoreIn]
  exact oddCoreIn_centralizer_eq_bot_of_mulEquiv e s (hC (e s) (by rw [← map_mul, hs2, map_one]))

end CFSG.ClassicalInvolution.Q3
