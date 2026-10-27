module

import CFSG.ClassicalInvolution.Asc77.AscT8T1Eng
public import CFSG.ClassicalInvolution.Asc77.AscT8Y3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8T

section Frame

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

structure TriFrame (Ω : Set (Subgroup G)) (M : Fin 3 → Subgroup G) (x : Fin 3 → G)
    (R : Fin 3 → Subgroup G) : Prop where
  mem : ∀ i, M i ∈ Ω
  inv : ∀ i, IsUniqueInvolution (M i) (x i)
  nbr : ∀ i j, i ≠ j → M j ∈ omegaNbr Ω (M i)
  syl : ∀ i, IsSylow2In (R i) (M i)
  cent : ∀ i j, R i ≤ Subgroup.centralizer ({x j} : Set G)

variable {M : Fin 3 → Subgroup G} {x : Fin 3 → G} {R : Fin 3 → Subgroup G}

theorem TriFrame.sq (hF : TriFrame Ω M x R) (i : Fin 3) : x i * x i = 1 := (hF.inv i).sq

theorem TriFrame.ne_one (hF : TriFrame Ω M x R) (i : Fin 3) : x i ≠ 1 := (hF.inv i).ne_one

theorem TriFrame.x_ne (hF : TriFrame Ω M x R)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {i j : Fin 3} (hij : i ≠ j) : x i ≠ x j := by
  intro h
  have hj : IsUniqueInvolution (M j) (x i) := by rw [h]; exact hF.inv j
  exact (hF.nbr i j hij).2.1 (hnt _ (hF.mem i) _ ⟨hF.mem j, x i, hF.inv i, hj⟩)

section Comm

variable [Finite G] {p f : ℕ} [Fact p.Prime]

theorem TriFrame.comm (hF : TriFrame Ω M x R) (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    (i j : Fin 3) : x i * x j = x j * x i := by
  by_cases hij : i = j
  · rw [hij]
  · exact T8.mul_comm_of_mem_omegaNbr hp hΩ (hF.inv i) (hF.nbr i j hij) (hF.inv j)

end Comm

end Frame

section ThreeGroup

variable {G : Type} [Group G]

theorem closure_three_eq_sup {a b c : G} :
    Subgroup.closure ({a, b, c} : Set G) =
      Subgroup.closure ({a, b} : Set G) ⊔ Subgroup.zpowers c := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro v hv
    rcases hv with rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · refine sup_le ?_ (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
    rw [Subgroup.closure_le]
    intro v hv
    rcases hv with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)

theorem isElemAbelian_closure_three {a b c : G} (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    IsElemAbelian 2 (Subgroup.closure ({a, b, c} : Set G)) := by
  have hcomm : ∀ u ∈ ({a, b, c} : Set G), ∀ v ∈ ({a, b, c} : Set G), u * v = v * u := by
    intro u hu v hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · rfl
    · exact hab
    · exact hac
    · exact hab.symm
    · rfl
    · exact hbc
    · exact hac.symm
    · exact hbc.symm
    · rfl
  have hsq : ∀ u ∈ ({a, b, c} : Set G), u * u = 1 := by
    intro u hu
    rcases hu with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  refine ⟨⟨⟨fun u v => Subtype.ext (T7A.commutes_closure hcomm _ u.2 _ v.2)⟩⟩, fun y hy => ?_⟩
  rw [pow_two]
  exact T7A.sq_closure hsq hcomm y hy

variable [Finite G]

theorem natCard_closure_three {a b c : G} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hne : a ≠ b) (hc1 : c ≠ 1) (hcn : c ∉ Subgroup.closure ({a, b} : Set G)) :
    Nat.card ↥(Subgroup.closure ({a, b, c} : Set G)) = 8 := by
  have hD := T7A.isElemAbelian2_closure_pair ha hb ha1 hb1 hne hab
  have hc2 : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc) hc1
  have hcomm : Commutes (Subgroup.closure ({a, b} : Set G)) (Subgroup.zpowers c) := by
    have hle : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer ({c} : Set G) := by
      rw [Subgroup.closure_le]
      intro v hv
      rcases hv with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hac
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hbc
    intro v hv y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have : Commute v c := Subgroup.mem_centralizer_singleton_iff.mp (hle hv)
    exact (this.zpow_right i).eq
  have hinf : Subgroup.closure ({a, b} : Set G) ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rcases T7A.eq_one_or_eq_of_mem_zpowers hc2 hv.2 with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · exact absurd (h1 ▸ hv.1) hcn
  have hN := T7A.card_sup_mul_card_inf (T7A.le_normalizer_of_commutes hcomm)
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, hc2, hD.1, mul_one] at hN
  rw [closure_three_eq_sup, sup_comm, hN]
  norm_num

end ThreeGroup


section Extract

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem exists_triFrame_of_std8 (hs : Std8 p f Ω K J S R T W z t) (hE4 : ¬ MuIsoE4 Ω W)
    (hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x)
    (hE8 : ∀ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω J → ∀ z' : G, IsUniqueInvolution K' z' →
      z' ≠ z * t) :
    ∃ (K' R' : Subgroup G) (z' : G), TriFrame Ω ![K, J, K'] ![z, t, z'] ![R, T, R'] ∧
      z' ∉ Subgroup.closure ({z, t} : Set G) := by
  have hP := T8.partIHyp_of_std8 hs
  have hc := T8.ctxOf hP hs.hW.1
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨K', R', z', hmem, hinv, hnbr, hsyl, hcent, hz'⟩ :=
    exists_triFrame_of_std8E hnt (fun hM => hΩ.exists_uniqueInvolution hp hq hM) hs.hz hs.ht hs.hJ
      (T8.stdRepK hs) (T8.stdRepJ hs) rfl rfl rfl rfl (T8.exists_third_of_abelian hs hE4 hab)
      (T8.repElt_commute_iff hc) (T8.rep_le_centralizer hc)
      (T8.mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht) hab hE8
  exact ⟨K', R', z', ⟨hmem, hinv, hnbr, hsyl, hcent⟩, hz'⟩

end Extract

end T8T

end CFSG.ClassicalInvolution.Asc77
