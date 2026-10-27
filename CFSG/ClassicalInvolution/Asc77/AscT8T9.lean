module

public import CFSG.ClassicalInvolution.Asc77.AscT8T8
public import CFSG.ClassicalInvolution.Asc77.AscT8T6
public import CFSG.ClassicalInvolution.Asc77.AscE187Img

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8T

section Vertex

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {M : Fin 3 → Subgroup G} {x : Fin 3 → G} {R : Fin 3 → Subgroup G}


theorem hyp51At_of_triFrame_pair (hst : AscStand p f Ω (M 0))
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) (hF : TriFrame Ω M x R)
    (hind : x 2 ∉ Subgroup.closure ({x 0, x 1} : Set G)) {i j : Fin 3} (hij : i ≠ j) {c : G}
    (hcB : c ∈ Subgroup.closure ({x 0, x 1, x 2} : Set G)) (hc1 : c ≠ 1)
    (hgen : ∀ k, x k ∈ Subgroup.closure ({x i, x j, c} : Set G)) :
    Hyp51At (Subgroup.closure ({x 0, x 1, x 2} : Set G)) c := by
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hB : IsElemAbelian 2 (Subgroup.closure ({x 0, x 1, x 2} : Set G)) :=
    isElemAbelian_closure_three (hF.sq 0) (hF.sq 1) (hF.sq 2) (hF.comm hp hΩ 0 1)
      (hF.comm hp hΩ 0 2) (hF.comm hp hΩ 1 2)
  have hB8 : Nat.card ↥(Subgroup.closure ({x 0, x 1, x 2} : Set G)) = 8 :=
    natCard_closure_three (hF.sq 0) (hF.sq 1) (hF.sq 2) (hF.comm hp hΩ 0 1) (hF.comm hp hΩ 0 2)
      (hF.comm hp hΩ 1 2) (hF.ne_one 0) (hF.ne_one 1) (hF.x_ne hnt (by decide)) (hF.ne_one 2) hind
  have hxB : ∀ k, x k ∈ Subgroup.closure ({x 0, x 1, x 2} : Set G) := by
    intro k
    apply Subgroup.subset_closure
    fin_cases k <;> simp
  have hBgen : Subgroup.closure ({x 0, x 1, x 2} : Set G) =
      Subgroup.closure ({x i, x j, c} : Set G) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro v hv
      rcases hv with rfl | rfl | rfl
      · exact hgen 0
      · exact hgen 1
      · exact hgen 2
    · rw [Subgroup.closure_le]
      intro v hv
      rcases hv with rfl | rfl | rfl
      · exact hxB i
      · exact hxB j
      · exact hcB
  have hcent : ∀ k, R k ≤ Subgroup.centralizer ({c} : Set G) := by
    intro k r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hrx : ∀ l, r * x l = x l * r := fun l =>
      Subgroup.mem_centralizer_singleton_iff.mp (hF.cent k l hr)
    have hrB : ∀ w ∈ Subgroup.closure ({x 0, x 1, x 2} : Set G), r * w = w * r := by
      intro w hw
      induction hw using Subgroup.closure_induction with
      | mem v hv =>
        rcases hv with rfl | rfl | rfl
        · exact hrx 0
        · exact hrx 1
        · exact hrx 2
      | one => simp
      | mul u v _ _ hu hv => rw [← mul_assoc, hu, mul_assoc, hv, mul_assoc]
      | inv u _ hu => exact (show Commute r u from hu).inv_right.eq
    exact hrB c hcB
  refine hyp51At_of_nonTwin_pair hst hB hB8 hBgen hc1 (hF.ne_one i) (hF.ne_one j)
    (hF.x_ne hnt hij) (M := M i) (M' := M j) (hF.mem_tqMembers hp hq hΩ hnt i hcB)
    (hF.mem_tqMembers hp hq hΩ hnt j hcB) (isClassicalMember_of_twin hΩ (hF.mem i) (hF.inv i))
    (isClassicalMember_of_twin hΩ (hF.mem j) (hF.inv j)) (hF.syl j) (hcent j) ?_
  intro r hr
  exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (hF.mem i)
    (hnt _ (hF.mem i)) (hF.inv i) (hF.cent j i hr)

omit [Finite G] [IsSimpleGroup G] in
theorem mem_closure_of_inv_mul {S : Set G} {a c t : G} (ha : a ∈ Subgroup.closure S)
    (hc : c ∈ Subgroup.closure S) (e : a⁻¹ * c = t) : t ∈ Subgroup.closure S :=
  e ▸ Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hc

variable (p f) in
theorem hyp51Tri_proved : Hyp51Tri p f := by
  intro G _ _ _ Ω M x R hst hnt hF hind
  have hp : p ≠ 2 := hst.odd
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have h01 := hF.comm hp hΩ 0 1
  have h02 := hF.comm hp hΩ 0 2
  have h12 := hF.comm hp hΩ 1 2
  have hB : IsElemAbelian 2 (Subgroup.closure ({x 0, x 1, x 2} : Set G)) :=
    isElemAbelian_closure_three (hF.sq 0) (hF.sq 1) (hF.sq 2) h01 h02 h12
  have hB8 : Nat.card ↥(Subgroup.closure ({x 0, x 1, x 2} : Set G)) = 8 :=
    natCard_closure_three (hF.sq 0) (hF.sq 1) (hF.sq 2) h01 h02 h12 (hF.ne_one 0) (hF.ne_one 1)
      (hF.x_ne hnt (by decide)) (hF.ne_one 2) hind
  refine ⟨hB, hB8, fun c hc hc1 => ?_⟩
  have hxB : ∀ k, x k ∈ Subgroup.closure ({x 0, x 1, x 2} : Set G) := by
    intro k
    apply Subgroup.subset_closure
    fin_cases k <;> simp
  rcases mem_closure_three_involutions (hF.sq 0) (hF.sq 1) (hF.sq 2) h01 h02 h12 hc with
    h | h | h | h | h | h | h | h
  · exact absurd h hc1
  ·
    subst h
    refine hyp51At_of_triFrame_pair hst hnt hF hind (i := 1) (j := 2) (by decide) hc hc1 ?_
    intro k
    fin_cases k <;> exact Subgroup.subset_closure (by simp)
  ·
    subst h
    refine hyp51At_of_triFrame_pair hst hnt hF hind (i := 0) (j := 2) (by decide) hc hc1 ?_
    intro k
    fin_cases k <;> exact Subgroup.subset_closure (by simp)
  ·
    subst h
    refine hyp51At_of_triFrame_pair hst hnt hF hind (i := 0) (j := 1) (by decide) hc hc1 ?_
    intro k
    fin_cases k <;> exact Subgroup.subset_closure (by simp)
  ·
    subst h
    refine hyp51At_of_triFrame_pair hst hnt hF hind (i := 2) (j := 0) (by decide) hc hc1 ?_
    intro k
    fin_cases k
    · exact Subgroup.subset_closure (by simp)
    · show x 1 ∈ _
      exact mem_closure_of_inv_mul (a := x 0) (c := x 0 * x 1) (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)) (by group)
    · exact Subgroup.subset_closure (by simp)
  ·
    subst h
    refine hyp51At_of_triFrame_pair hst hnt hF hind (i := 1) (j := 0) (by decide) hc hc1 ?_
    intro k
    fin_cases k
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · show x 2 ∈ _
      exact mem_closure_of_inv_mul (a := x 0) (c := x 0 * x 2) (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)) (by group)
  ·
    subst h
    refine hyp51At_of_triFrame_pair hst hnt hF hind (i := 0) (j := 1) (by decide) hc hc1 ?_
    intro k
    fin_cases k
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · show x 2 ∈ _
      exact mem_closure_of_inv_mul (a := x 1) (c := x 1 * x 2) (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)) (by group)
  ·
    subst h
    refine hyp51At_of_triFrame_pair hst hnt hF hind (i := 0) (j := 1) (by decide) hc hc1 ?_
    intro k
    fin_cases k
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · show x 2 ∈ _
      exact mem_closure_of_inv_mul (a := x 0 * x 1) (c := x 0 * x 1 * x 2)
        (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
        (Subgroup.subset_closure (by simp)) (by group)

end Vertex

end T8T

section Main

variable (p f : ℕ) [Fact p.Prime]


theorem c27_Oab_of_alphaConst' (hD4 : Ih8D4Star p f) (h2 : C27_2 p f) (h4a : C27_4a p f)
    (hA : T8T.C27_AlphaConst p f) : C27_Oab p f :=
  c27_Oab_of_alphaConst p f hD4 h2 h4a hA (T8T.hyp51Tri_proved p f)

end Main

end CFSG.ClassicalInvolution.Asc77
