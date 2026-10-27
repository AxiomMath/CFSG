module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL2Cert
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer

public section

namespace CFSG.ComponentClassification.HSFLit.AutL2

open CFSG Subgroup Equiv CFSG.GH74.KGroups
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] {J : Subgroup G}

theorem exists_l2Model'
    (h : IsL2Type 5 (Jhat J) ∨ IsL2Type 7 (Jhat J)) :
    ∃ (n : ℕ) (M : AutModel (Jhat J) (Perm (Fin n))), L2ModelFacts M.P M.A ∧
      Nat.card M.A ≤ 2 * Nat.card M.P := by
  rcases h with h5 | h7
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := GSThmB.statedClassicalModel_of_lieModel_ne_zero
      (by norm_num) h5
    obtain ⟨e'⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
      (Or.inr (by simpa using hF))
    have hbij := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num)
    let Φ' : (⊤ : Subgroup (Perm (Fin 5))) ≃* MulAut (alternatingGroup (Fin 5)) :=
      topEquiv.trans (MulEquiv.ofBijective _ hbij)
    refine ⟨5, AutModel.ofRealization (alternatingGroup (Fin 5)) ⊤ (e.trans e') Φ'
      (fun σ x => by
        show ((MulAut.conjNormal (σ : Perm (Fin 5)) x : alternatingGroup (Fin 5)) :
          Perm (Fin 5)) = σ * x * (σ : Perm (Fin 5))⁻¹
        rw [MulAut.conjNormal_apply]), a5Facts, ?_⟩
    show Nat.card (⊤ : Subgroup (Perm (Fin 5))) ≤ 2 * Nat.card (alternatingGroup (Fin 5))
    rw [card_top, nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
    decide
  · obtain ⟨e⟩ := L27.equiv_of_lieModel h7
    obtain ⟨M, hP, hA⟩ := L27.autModel e
    refine ⟨8, M, hP ▸ hA ▸ l27Facts, ?_⟩
    rw [hP, hA, card_group _ L27.QA_ok, card_group _ L27.QP_ok, L27.QA_valid.2, L27.QP_valid.2]

variable {n : ℕ}

theorem card_le_two_of_inv {P A : Subgroup (Perm (Fin n))} (hF : L2ModelFacts P A)
    {r : Perm (Fin n)} (hrA : r ∈ A) (hr2 : r * r = 1) (hr1 : r ≠ 1) (hrP : r ∉ P)
    {X : Subgroup (Perm (Fin n))} (hXP : X ≤ P) (hX2 : ∀ x ∈ X, x * x = 1)
    (hXr : ∀ x ∈ X, x * r = r * x) : Nat.card X ≤ 2 := by
  obtain ⟨y, hyP, hy3, hy1, -, hyn⟩ := hF.outer3 r hrA hr2 hr1 hrP
  have hinv : ∀ g ∈ X, g ≠ 1 → g * y * g⁻¹ = y * y := by
    intro g hg hg1
    rcases hyn g (hXP hg) (hXr g hg) with h | h
    · exfalso
      have hgy : y * g = g * y := by
        calc y * g = g * y * g⁻¹ * g := by rw [h]
          _ = g * y := by group
      have h16 := hF.inner g (hXP hg) (hX2 g hg) hg1 y (hF.le hyP) hgy
      apply hy1
      calc y = y ^ 16 * (y ^ 3)⁻¹ ^ 5 := by group
        _ = 1 := by rw [h16, hy3]; group
    · exact h
  have heq : ∀ g ∈ X, ∀ g' ∈ X, g ≠ 1 → g' ≠ 1 → g = g' := by
    intro g hg g' hg' hg1 hg'1
    by_contra hne
    have hgg : g * g' ≠ 1 := fun h => hne (by
      calc g = g * (g' * g') := by rw [hX2 g' hg', mul_one]
        _ = g * g' * g' := by group
        _ = g' := by rw [h, one_mul])
    have h1 := hinv _ (X.mul_mem hg hg') hgg
    have h2 : g * g' * y * (g * g')⁻¹ = g * (g' * y * g'⁻¹) * g⁻¹ := by group
    rw [h2, hinv g' hg' hg'1, show g * (y * y) * g⁻¹ = g * y * g⁻¹ * (g * y * g⁻¹) by group,
      hinv g hg hg1] at h1
    apply hy1
    have h3 : y * y * (y * y) = y := by
      calc y * y * (y * y) = y ^ 3 * y := by rw [pow_succ, pow_two]; group
        _ = y := by rw [hy3, one_mul]
    rw [h3] at h1
    calc y = y * y * y⁻¹ := by group
      _ = y * y * (y * y)⁻¹ := by rw [← h1]
      _ = 1 := by group
  classical
  by_cases h1 : ∃ g₀ ∈ X, g₀ ≠ 1
  · obtain ⟨g₀, hg₀, hg₀1⟩ := h1
    have hinj := Nat.card_le_card_of_injective (fun g : X => decide ((g : Perm (Fin n)) = 1))
      fun a b hab => by
        apply Subtype.ext
        by_cases ha : (a : Perm (Fin n)) = 1 <;> by_cases hb : (b : Perm (Fin n)) = 1
        · rw [ha, hb]
        · simp [ha, hb] at hab
        · simp [ha, hb] at hab
        · exact (heq _ a.2 g₀ hg₀ ha hg₀1).trans (heq _ b.2 g₀ hg₀ hb hg₀1).symm
    rwa [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hinj
  · push Not at h1
    rw [(eq_bot_iff_forall X).2 h1, card_bot]
    omega

theorem card_le_two_mul_inf {M' : Type*} [Group M'] [Finite M'] {P A X : Subgroup M'}
    (hPA : P ≤ A) (hcard : Nat.card A ≤ 2 * Nat.card P) (hXA : X ≤ A) :
    Nat.card X ≤ 2 * Nat.card ↥(P ⊓ X) := by
  have h1 := relIndex_mul_card P A
  rw [inf_eq_left.2 hPA] at h1
  have hpos : 0 < Nat.card P := Nat.card_pos
  have h2 : P.relIndex A ≤ 2 := by nlinarith
  have hne : P.relIndex A ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  have h3 := relIndex_mul_card P X
  have h4 := (relIndex_le_of_le_right hXA hne).trans h2
  rw [← h3]
  exact Nat.mul_le_mul_right _ h4

theorem card_eq_of_hom {M' : Type*} [Group M'] {N C : Subgroup G} (ψ : ↥N →* M')
    (hker : ∀ g, ψ g = 1 ↔ (g : G) ∈ C) {H : Subgroup G} (hH : H ≤ N) :
    Nat.card H = Nat.card ((H.subgroupOf N).map ψ) * Nat.card ↥(H ⊓ C) := by
  set H' := H.subgroupOf N
  set φ := ψ.comp H'.subtype
  have h1 := card_ker_mul_card_range φ
  have hr : φ.range = H'.map ψ := by
    rw [MonoidHom.range_comp, range_subtype]
  have hk : Nat.card φ.ker = Nat.card ↥(H ⊓ C) := Nat.card_congr
    { toFun := fun x => ⟨x.1.1.1, mem_inf.2 ⟨mem_subgroupOf.1 x.1.2, (hker _).1 x.2⟩⟩
      invFun := fun h => ⟨⟨⟨h.1, hH (mem_inf.1 h.2).1⟩, mem_subgroupOf.2 (mem_inf.1 h.2).1⟩,
        (hker _).2 (mem_inf.1 h.2).2⟩
      left_inv := fun x => rfl
      right_inv := fun h => rfl }
  rw [hr, hk, Nat.card_congr (subgroupOfEquivOfLe hH).toEquiv] at h1
  rw [← h1, mul_comm]

end CFSG.ComponentClassification.HSFLit.AutL2
