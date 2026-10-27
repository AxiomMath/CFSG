module

public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c
open Classical in

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.conn_clique (ρ : Fin 4 → Rep Ω W)
    (hclos : ∀ (σ : Rep Ω W) (i : Fin 4), (σ.K = (ρ i).K ∨ σ.K ∈ omegaNbr Ω (ρ i).K) →
      ∃ j, σ.K = (ρ j).K) {b : ↥(muGroup Ω W)}
    (hb : Star3T.Conn (muDelta Ω W) (T7D.imgQ (ρ 0)) b) : ∃ j, b = T7D.imgQ (ρ j) := by
  induction hb with
  | refl => exact ⟨0, rfl⟩
  | @tail b₁ b₂ _ hadj ih =>
    obtain ⟨j, rfl⟩ := ih
    obtain ⟨-, hb₂Δ, hcomm⟩ := hadj
    obtain ⟨τ, hτ⟩ := exists_rep_of_mem_muDelta hb₂Δ
    have hτq : T7D.imgQ τ = b₂ := Subtype.ext hτ
    by_cases hK : τ.K = (ρ j).K
    · exact ⟨j, by rw [← hτq]; exact Subtype.ext (c.img_eq_of_K_eq τ (ρ j) hK)⟩
    · have hcomm' : (ρ j).img * τ.img = τ.img * (ρ j).img := by
        have := congrArg Subtype.val hcomm
        rw [← hτq] at this
        exact this
      obtain ⟨m, hm⟩ := hclos τ j (Or.inr (c.omega_of_comm (ρ j) τ (Ne.symm hK) hcomm'))
      exact ⟨m, by rw [← hτq]; exact Subtype.ext (c.img_eq_of_K_eq τ (ρ m) hm)⟩

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.exists_relation_far (hclC :
    Q3CL.ClassicalClause Ω) (hnc : ¬ DbarConnected Ω W) (ρ : Fin 4 → Rep Ω W)
    (hne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K)
    (hnbr : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K)
    (hclos : ∀ (σ : Rep Ω W) (i : Fin 4), (σ.K = (ρ i).K ∨ σ.K ∈ omegaNbr Ω (ρ i).K) →
      ∃ j, σ.K = (ρ j).K)
    (σ' : Rep Ω W) (hfar : ∀ j, σ'.K ≠ (ρ j).K) :
    ∃ (t : G) (g : Fin 4 → G), IsUniqueInvolution σ'.K t ∧
      (∀ i, g i ∈ (ρ i).K ⊓ W ∧ orderOf (g i) = 4) ∧ t = g 0 * g 1 * g 2 * g 3 := by
  classical
  have hP : PartIHyp Ω := ⟨c.hΩ, hclC, c.hA⟩
  have hTT : Star3T.IsTT (muDelta Ω W) :=
    isTT_muDelta c.hΩ c.hW (Q3CL.thompsonCube hP W c.hW)
  have hS : Star3T.IsStar (muDelta Ω W) :=
    isStar_muDelta c.hΩ c.hW (thompsonStar G Ω hP W c.hW)
  obtain ⟨rep, hrep⟩ : ∃ rep : ↥(muGroup Ω W) → Rep Ω W,
      ∀ x ∈ muDelta Ω W, (rep x).img = (x : NQuot (W ⊔ OCW W)) := by
    have hex : ∀ x ∈ muDelta Ω W, ∃ ρ : Rep Ω W, ρ.img = (x : NQuot (W ⊔ OCW W)) :=
      fun x hx => exists_rep_of_mem_muDelta hx
    have : Nonempty (Rep Ω W) := ⟨ρ 0⟩
    choose! rep hrep using hex
    exact ⟨rep, hrep⟩
  set x : Fin 4 → ↥(muGroup Ω W) := fun i => T7D.imgQ (ρ i) with hx
  have hxΔ : ∀ i, x i ∈ muDelta Ω W := fun i => T7D.imgQ_mem (ρ i)
  have hne_of : ∀ σ σ' : Rep Ω W, σ.K ≠ σ'.K → T7D.imgQ σ ≠ T7D.imgQ σ' := fun σ σ' hK e =>
    hK (c.K_eq_of_img_eq σ σ' (congrArg Subtype.val e))
  have hcomm_of : ∀ σ σ' : Rep Ω W, σ'.K ∈ omegaNbr Ω σ.K →
      T7D.imgQ σ * T7D.imgQ σ' = T7D.imgQ σ' * T7D.imgQ σ := fun σ σ' h =>
    Subtype.ext (c.comm_of_omega σ σ' h)
  have hxne : ∀ i j, i ≠ j → x i ≠ x j := fun i j hij => hne_of _ _ (hne i j hij)
  have hxC : ∀ i, x i ∈ Star3T.cent (muDelta Ω W) (x 0) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      exact Star3T.self_mem_cent (hxΔ 0)
    · exact ⟨hxΔ i, (hcomm_of (ρ 0) (ρ i) (hnbr 0 i (Ne.symm hi))).symm⟩
  have hxC' : ({x 0, x 1, x 2, x 3} : Finset ↥(muGroup Ω W)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hxne 0 1 (by decide), hxne 0 2 (by decide),
        hxne 0 3 (by decide)]),
      Finset.card_insert_of_notMem (by simp [hxne 1 2 (by decide), hxne 1 3 (by decide)]),
      Finset.card_insert_of_notMem (by simp [hxne 2 3 (by decide)]), Finset.card_singleton]
  have hC4 : (Star3T.cent (muDelta Ω W) (x 0)).ncard = 4 := by
    have hsub : (↑({x 0, x 1, x 2, x 3} : Finset ↥(muGroup Ω W)) : Set ↥(muGroup Ω W)) ⊆
        Star3T.cent (muDelta Ω W) (x 0) := by
      intro y hy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact hxC 0
      · exact hxC 1
      · exact hxC 2
      · exact hxC 3
    have hge : 4 ≤ (Star3T.cent (muDelta Ω W) (x 0)).ncard := by
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [Set.ncard_coe_finset, hxC'] at this
    rcases thompsonClique G Ω hP W c.hW hnc (x 0) (hxΔ 0) with h | h | ⟨h, -⟩
    · omega
    · omega
    · exact h
  set a : ↥(muGroup Ω W) := T7D.imgQ σ' with ha_def
  have haΔ : a ∈ muDelta Ω W := T7D.imgQ_mem σ'
  have hna : ¬ Star3T.Conn (muDelta Ω W) (x 0) a := fun hconn => by
    obtain ⟨j, hj⟩ := c.conn_clique ρ hclos hconn
    exact hfar j (c.K_eq_of_img_eq σ' (ρ j) (congrArg Subtype.val hj))
  have hcfg : Star3T.Cfg (muDelta Ω W) (x 0) a := ⟨hTT, hS, hxΔ 0, haΔ, hna⟩
  obtain ⟨n, B, hcard, hBC, hdB, hBn, hgen⟩ := hcfg.exists_generating_family
  have hn : n = 2 := by
    have h4 : 2 ^ n = 2 ^ 2 := by rw [← hcard, hC4]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h4
  have hB3 : B.card = 3 := by rw [hBn, hn]
  obtain ⟨P, hP', hPB⟩ : ∃ P ∈ Star3T.cent (muDelta Ω W) (x 0), P ∉ B := by
    by_contra hall
    push Not at hall
    have h1 : (Star3T.cent (muDelta Ω W) (x 0)).ncard ≤ B.card := by
      calc (Star3T.cent (muDelta Ω W) (x 0)).ncard ≤ (↑B : Set ↥(muGroup Ω W)).ncard :=
            Set.ncard_le_ncard (fun P hP => Finset.mem_coe.mpr (hall P hP)) (Set.toFinite _)
        _ = B.card := Set.ncard_coe_finset B
    omega
  have hsub := c.clique_subset rep hrep hcfg hBC hdB hgen hP' hPB
  obtain ⟨za, g, hza, hmem, hrel⟩ := c.clique_relation' rep hrep hcfg hBC hdB hgen hP' hPB hB3
  have hcardPB : (insert P B).card = 4 := by rw [Finset.card_insert_of_notMem hPB, hB3]
  have hSeq : ({x 0, x 1, x 2, x 3} : Finset ↥(muGroup Ω W)) = insert P B := by
    refine Finset.eq_of_subset_of_card_le ?_ (by rw [hxC', hcardPB])
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    have hyC : y ∈ Star3T.cent (muDelta Ω W) (x 0) := by
      rcases hy with rfl | rfl | rfl | rfl
      · exact hxC 0
      · exact hxC 1
      · exact hxC 2
      · exact hxC 3
    by_cases hyP : y = P
    · rw [hyP]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hsub y hyC hyP)
  have hKeq : ∀ i, (rep (x i)).K = (ρ i).K := fun i =>
    c.K_eq_of_img_eq (rep (x i)) (ρ i) (hrep (x i) (hxΔ i))
  have hxmem : ∀ i, x i ∈ insert P B := fun i => by
    rw [← hSeq]
    fin_cases i <;> simp [hx]
  have hKa : (rep a).K = σ'.K := c.K_eq_of_img_eq (rep a) σ' (hrep a haΔ)
  refine ⟨za, fun i => g (x i), hKa ▸ hza, ?_, ?_⟩
  · intro i
    have := hmem (x i) (hxmem i)
    rw [hKeq i] at this
    exact this
  · exact hrel (x 0) (x 1) (x 2) (x 3) (hxne 0 1 (by decide)) (hxne 0 2 (by decide))
      (hxne 0 3 (by decide)) (hxne 1 2 (by decide)) (hxne 1 3 (by decide))
      (hxne 2 3 (by decide)) hSeq
end Ctx
end Thompson
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
