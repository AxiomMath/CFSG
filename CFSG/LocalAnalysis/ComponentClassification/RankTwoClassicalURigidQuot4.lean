module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidCore

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] {A : Subgroup G} {P : Type} [Group P] {θ : ↥A →* P}

theorem commute_of_theta_commute (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A)))
    {a x : ↥A} (hx : x ^ 2 = 1) (h : θ a * θ x = θ x * θ a) : a * x = x * a := by
  set c := a * x * a⁻¹ * x⁻¹ with hcdef
  have hc : c ∈ center ↥A := by
    rw [← hker, MonoidHom.mem_ker, hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have hcx : a * x * a⁻¹ = c * x := by rw [hcdef]; group
  have hcomm : c * x = x * c := (mem_center_iff.mp hc x).symm
  have h2 : (c * x) ^ 2 = 1 := by
    rw [← hcx, sq, show a * x * a⁻¹ * (a * x * a⁻¹) = a * (x * x) * a⁻¹ by group, ← sq, hx,
      mul_one, mul_inv_cancel]
  have hc2 : c ^ 2 = 1 := by
    rwa [(Commute.mul_pow hcomm 2), hx, mul_one] at h2
  have hc1 := CFSG.ComponentClassification.RankTwoClassical.eq_one_of_sq_eq_one_of_mem_center
    hodd hc hc2
  calc a * x = a * x * a⁻¹ * a := by group
    _ = x * a := by rw [hcx, hc1, one_mul]

theorem noNormalTwo_of_map_theta [Finite G] (hker : θ.ker = center ↥A)
    (hodd : Odd (Nat.card (center ↥A))) {M : Subgroup G} (hMA : M ≤ A)
    (h : NoNormalTwo ((M.subgroupOf A).map θ)) : NoNormalTwo M := by
  intro Q hQ hQ2 hN
  have hQA : Q ≤ A := hQ.trans hMA
  set Qθ : Subgroup P := (Q.subgroupOf A).map θ
  have h1 : Qθ ≤ (M.subgroupOf A).map θ := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, hQ ha, rfl⟩
  have hQ2' : IsPGroup 2 ↥(Q.subgroupOf A) := hQ2.of_equiv (subgroupOfEquivOfLe hQA).symm
  have h3 : (M.subgroupOf A).map θ ≤ normalizer (Qθ : Set P) := by
    rintro _ ⟨a, ha, rfl⟩
    have haN := hN ha
    rw [mem_normalizer_iff] at haN ⊢
    intro q
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨a * b * a⁻¹, (haN b).mp hb, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · rintro ⟨b, hb, hbq⟩
      have hb' : ((a⁻¹ * b * a : ↥A) : G) ∈ Q := by
        rw [haN]
        have e : (a : G) * ((a⁻¹ * b * a : ↥A) : G) * (a : G)⁻¹ = b := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        change (a : G) * ((a⁻¹ * b * a : ↥A) : G) * (a : G)⁻¹ ∈ Q
        rw [e]
        exact hb
      refine ⟨a⁻¹ * b * a, hb', ?_⟩
      rw [map_mul, map_mul, map_inv, hbq]
      group
  have hbot := h Qθ h1 (hQ2'.map θ) h3
  have hZ : Q.subgroupOf A ≤ center ↥A := by
    intro b hb
    rw [← hker, MonoidHom.mem_ker]
    have : θ b ∈ Qθ := ⟨b, hb, rfl⟩
    rwa [hbot, mem_bot] at this
  have hodd' : Odd (Nat.card ↥(Q.subgroupOf A)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hZ)
  have hbot' := eq_bot_of_isPGroup_two_of_odd hQ2' hodd'
  rw [eq_bot_iff]
  intro q hq
  have : (⟨q, hQA hq⟩ : ↥A) ∈ Q.subgroupOf A := hq
  rw [hbot', mem_bot] at this
  exact (mem_bot).mpr (congrArg Subtype.val this)

theorem exists_alpha_of_normalizer [Finite G] (hθ : Function.Surjective θ)
    (hker : θ.ker = center ↥A) {d : G} (hd : d ∈ normalizer (A : Set G)) :
    ∃ γ : MulAut ↥A, (∀ a : ↥A, ((γ a : ↥A) : G) = d * a * d⁻¹) ∧
      ∃ α : MulAut P, ∀ a, α (θ a) = θ (γ a) := by
  have hA : rightConjugate A d⁻¹ = A := (rightConjugate_eq_self_iff A d⁻¹).mpr (inv_mem hd)
  refine ⟨conjAut hA, fun a => by rw [coe_conjAut, inv_inv], ?_⟩
  refine exists_mulAut_comp_eq_of_ker θ hθ (conjAut hA) fun a ha => ?_
  have h1 : a ∈ center ↥A := by rw [← hker]; exact ha
  rw [← MonoidHom.mem_ker, hker]
  exact mulAut_mem_center _ h1

theorem fix_of_levLift (hker : θ.ker = center ↥A) {γ : MulAut ↥A} {α : MulAut P}
    (hαγ : ∀ a, α (θ a) = θ (γ a)) {S : Subgroup P} (hS : ∀ s ∈ S, α s = s)
    (hperf : ⁅levLift θ S, levLift θ S⁆ = levLift θ S) {l : G} (hl : l ∈ levLift θ S) :
    γ ⟨l, levLift_le hl⟩ = ⟨l, levLift_le hl⟩ := by
  have hz : ∀ y (hy : y ∈ levLift θ S),
      (γ ⟨y, levLift_le hy⟩ : ↥A) * (⟨y, levLift_le hy⟩ : ↥A)⁻¹ ∈ center ↥A := by
    intro y hy
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, ← hαγ, hS _ (theta_mem_of_mem_levLift hy),
      mul_inv_cancel]
  have hγz : ∀ y (hy : y ∈ levLift θ S), γ ⟨y, levLift_le hy⟩ =
      ⟨y, levLift_le hy⟩ * ((γ ⟨y, levLift_le hy⟩ : ↥A) * (⟨y, levLift_le hy⟩ : ↥A)⁻¹) := by
    intro y hy
    rw [mem_center_iff.mp (hz y hy) ⟨y, levLift_le hy⟩, inv_mul_cancel_right]
  set F : Subgroup G := ((γ.toMonoidHom).eqLocus (MonoidHom.id ↥A)).map A.subtype
  have hF : levLift θ S ≤ F := by
    rw [← hperf, Subgroup.commutator_le]
    intro a ha b hb
    have hab : ⁅a, b⁆ ∈ A := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (levLift_le ha) (levLift_le hb))
        (inv_mem (levLift_le ha))) (inv_mem (levLift_le hb))
    refine ⟨⟨⁅a, b⁆, hab⟩, ?_, rfl⟩
    change γ ⟨⁅a, b⁆, hab⟩ = ⟨⁅a, b⁆, hab⟩
    have e : (⟨⁅a, b⁆, hab⟩ : ↥A) = ⁅(⟨a, levLift_le ha⟩ : ↥A), ⟨b, levLift_le hb⟩⁆ := rfl
    have hza := hz a ha
    have hzb := hz b hb
    rw [e, map_commutatorElement, hγz a ha, hγz b hb]
    exact commutatorElement_mul_mul_of_commute' (mem_center_iff.mp hza _).symm
      (mem_center_iff.mp hzb _).symm (mem_center_iff.mp hzb _)
  obtain ⟨y, hy, hyl⟩ := hF hl
  have hy' : y = ⟨l, levLift_le hl⟩ := Subtype.ext hyl
  rw [← hy']
  exact hy

end CFSG.ComponentClassification.RankTwoClassical.URigid
