module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FGraphB
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FGraphA

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E27Lie

theorem reach0 : ∀ ε ∈ ({1, 2} : Finset ℕ), ∀ γ ∈ d4RootsAt 1, γ = rA 0 ∨ γ = rA 2 ∨
    permLattice (d4Rho ^ (2 * ε)) γ = rA 0 ∨ permLattice (d4Rho ^ (2 * ε)) γ = rA 2 ∨
      permLattice (d4Rho ^ (2 * ε)) (permLattice (d4Rho ^ (2 * ε)) γ) = rA 0 ∨
      permLattice (d4Rho ^ (2 * ε)) (permLattice (d4Rho ^ (2 * ε)) γ) = rA 2 := by decide +kernel

theorem reach1 : ∀ ε ∈ ({1, 2} : Finset ℕ), ∀ γ ∈ d4RootsAt 2, γ = rB 0 ∨
    permLattice (d4Rho ^ (2 * ε)) γ = rB 0 ∨
      permLattice (d4Rho ^ (2 * ε)) (permLattice (d4Rho ^ (2 * ε)) γ) = rB 0 := by decide +kernel

theorem reach2 : ∀ ε ∈ ({1, 2} : Finset ℕ), ∀ γ ∈ d4RootsAt 3, γ = rC 0 1 ∨
    permLattice (d4Rho ^ (2 * ε)) γ = rC 0 1 ∨
      permLattice (d4Rho ^ (2 * ε)) (permLattice (d4Rho ^ (2 * ε)) γ) = rC 0 1 := by decide +kernel

theorem single4 : ∀ γ ∈ d4RootsAt 4, γ = rT4 := by decide +kernel

theorem single5 : ∀ γ ∈ d4RootsAt 5, γ = rT5 := by decide +kernel

theorem d4_all_heights : ∀ γ ∈ rootFinset Tag.D4, 0 < height γ → height γ ≤ 5 := by decide +kernel

variable {K : Type} [Field K] [Finite K]


theorem maxHeight_D4 : maxHeight Tag.D4 = 5 := by
  apply le_antisymm
  · refine csSup_le ⟨height rT5, rT5, ⟨isPos_rT5.1, by rw [isPos_rT5.2]; norm_num⟩, rfl⟩ ?_
    rintro _ ⟨γ, ⟨hγ, hpos⟩, rfl⟩
    exact d4_all_heights γ (mem_rootFinset.2 hγ) hpos
  · have := height_le_maxHeight (τ := Tag.D4) isPos_rT5.1 (by rw [isPos_rT5.2]; norm_num)
    rwa [isPos_rT5.2] at this

theorem card_le_one_of_forall_eq_one {Q : Type*} [Group Q] [Finite Q] (S : Set Q)
    (h : ∀ q ∈ S, q = 1) : Nat.card S ≤ 1 :=
  Finite.card_le_one_iff_subsingleton.2 ⟨fun a b => Subtype.ext ((h a a.2).trans (h b b.2).symm)⟩

theorem unitRoot_mem_at {k : ℕ} (δ : UnitRoots Tag.D4 k) : δ.1 ∈ d4RootsAt ((k + 1 : ℕ) : ℤ) :=
  mem_d4RootsAt.2 ⟨δ.2.1, δ.2.2⟩

@[expose] def δA (o : D4Idx) : UnitRoots Tag.D4 0 :=
  ⟨rA o, (isPos_rA o).1, by rw [height_rA]; rfl⟩

theorem coord_unitPhi {k : ℕ} (x : unitN Tag.D4 K k) (δ : UnitRoots Tag.D4 k) :
    Multiplicative.toAdd (unitPhi Tag.D4 K k x) δ =
      pc δ.1 ((x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) :=
  (pc_of_pos (UnitRoots.pos Tag.D4 δ) _).symm

section Reach

variable {α : MulAut ↥(adjointGroup Tag.D4 K)} (la : LayerAct Tag.D4 α (1 : K ≃+* K)) {ε : ℕ}
  (hε : ε = 1 ∨ ε = 2)
  (hr : ∀ (k : ℕ) (δ : UnitRoots Tag.D4 k), (la.r k δ).1 = permLattice (d4Rho ^ (2 * ε)) δ.1)

include hε hr

theorem reach_layer0 :
    ∀ δ : UnitRoots Tag.D4 0, δ ∈ ({δA 0, δA 2} : Set (UnitRoots Tag.D4 0)) ∨
      la.r 0 δ ∈ ({δA 0, δA 2} : Set (UnitRoots Tag.D4 0)) ∨
      la.r 0 (la.r 0 δ) ∈ ({δA 0, δA 2} : Set (UnitRoots Tag.D4 0)) := by
  intro δ
  have h := reach0 ε (by rcases hε with rfl | rfl <;> simp) δ.1 (unitRoot_mem_at δ)
  have h1 : (la.r 0 δ).1 = permLattice (d4Rho ^ (2 * ε)) δ.1 := hr 0 δ
  have h2 : (la.r 0 (la.r 0 δ)).1 = permLattice (d4Rho ^ (2 * ε))
      (permLattice (d4Rho ^ (2 * ε)) δ.1) := by rw [hr 0 (la.r 0 δ), hr 0 δ]
  have key : ∀ δ' : UnitRoots Tag.D4 0, δ'.1 = rA 0 ∨ δ'.1 = rA 2 →
      δ' ∈ ({δA 0, δA 2} : Set (UnitRoots Tag.D4 0)) := by
    rintro δ' (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  rcases h with h | h | h | h | h | h
  · exact Or.inl (key δ (Or.inl h))
  · exact Or.inl (key δ (Or.inr h))
  · exact Or.inr (Or.inl (key _ (Or.inl (h1.trans h))))
  · exact Or.inr (Or.inl (key _ (Or.inr (h1.trans h))))
  · exact Or.inr (Or.inr (key _ (Or.inl (h2.trans h))))
  · exact Or.inr (Or.inr (key _ (Or.inr (h2.trans h))))

theorem reach_layer1 (δ₀ : UnitRoots Tag.D4 1) (hδ₀ : δ₀.1 = rB 0) :
    ∀ δ : UnitRoots Tag.D4 1, δ = δ₀ ∨ la.r 1 δ = δ₀ ∨ la.r 1 (la.r 1 δ) = δ₀ := by
  intro δ
  have h := reach1 ε (by rcases hε with rfl | rfl <;> simp) δ.1 (unitRoot_mem_at δ)
  rcases h with h | h | h
  · exact Or.inl (Subtype.ext (h.trans hδ₀.symm))
  · exact Or.inr (Or.inl (Subtype.ext ((hr 1 δ).trans (h.trans hδ₀.symm))))
  · refine Or.inr (Or.inr (Subtype.ext ?_))
    rw [hr 1 (la.r 1 δ), hr 1 δ]
    exact h.trans hδ₀.symm

theorem reach_layer2 (δ₀ : UnitRoots Tag.D4 2) (hδ₀ : δ₀.1 = rC 0 1) :
    ∀ δ : UnitRoots Tag.D4 2, δ = δ₀ ∨ la.r 2 δ = δ₀ ∨ la.r 2 (la.r 2 δ) = δ₀ := by
  intro δ
  have h := reach2 ε (by rcases hε with rfl | rfl <;> simp) δ.1 (unitRoot_mem_at δ)
  rcases h with h | h | h
  · exact Or.inl (Subtype.ext (h.trans hδ₀.symm))
  · exact Or.inr (Or.inl (Subtype.ext ((hr 2 δ).trans (h.trans hδ₀.symm))))
  · refine Or.inr (Or.inr (Subtype.ext ?_))
    rw [hr 2 (la.r 2 δ), hr 2 δ]
    exact h.trans hδ₀.symm

end Reach

theorem reach_single {k : ℕ} {γ₀ : D4Vec} (h : ∀ γ ∈ d4RootsAt ((k + 1 : ℕ) : ℤ), γ = γ₀)
    (δ₀ δ : UnitRoots Tag.D4 k) (hδ₀ : δ₀.1 = γ₀) : δ = δ₀ :=
  Subtype.ext ((h _ (unitRoot_mem_at δ)).trans hδ₀.symm)

theorem hp_of_eps {ε : ℕ} (hε : ε = 1 ∨ ε = 2) :
    ((d4Rho ^ (2 * ε)) 0 = 1 ∧ (d4Rho ^ (2 * ε)) 1 = 3 ∧ (d4Rho ^ (2 * ε)) 3 = 0 ∧
        (d4Rho ^ (2 * ε)) 2 = 2) ∨
      ((d4Rho ^ (2 * ε)) 0 = 3 ∧ (d4Rho ^ (2 * ε)) 1 = 0 ∧ (d4Rho ^ (2 * ε)) 3 = 1 ∧
        (d4Rho ^ (2 * ε)) 2 = 2) := by
  rcases hε with rfl | rfl <;> decide

section Main

variable {α : MulAut ↥(adjointGroup Tag.D4 K)} (la : LayerAct Tag.D4 α (1 : K ≃+* K)) {ε : ℕ}
  (hε : ε = 1 ∨ ε = 2)
  (hr : ∀ (k : ℕ) (δ : UnitRoots Tag.D4 k), (la.r k δ).1 = permLattice (d4Rho ^ (2 * ε)) δ.1)

include hε hr

theorem layer0_bound [CharP K 3] (h3 : α ^ 3 = 1) {A : Subgroup ↥(adjointGroup Tag.D4 K)}
    (hA0 : A ≤ unitN Tag.D4 K 0) (hcomm : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u)
    (hfix : ∀ a ∈ A, α a = a) :
    Nat.card (layerImage A 0) ≤ Nat.card K ∧
      (Nat.card (layerImage A 0) ≤ 1 ∨ Nat.card (layerImage A 1) ≤ 1 ∨
        Nat.card (layerImage A 3) ≤ 1) := by
  classical
  have hp := hp_of_eps hε
  have hreach0 := reach_layer0 la hε hr
  have hqpos : 1 ≤ Nat.card K := Nat.card_pos
  have hcoord : ∀ {q : UnitCoord Tag.D4 K 0}, q ∈ layerImage A 0 →
      ∃ x : ↥(adjointGroup Tag.D4 K), x ∈ A ∧ ∀ δ : UnitRoots Tag.D4 0,
        Multiplicative.toAdd q δ = pc δ.1 (x : ModGL Tag.D4 K) := by
    rintro q ⟨x, hxA, rfl⟩
    exact ⟨x.1, hxA, fun δ => coord_unitPhi x δ⟩
  have hmemS : ∀ δ : UnitRoots Tag.D4 0, δ ∈ ({δA 0, δA 2} : Set (UnitRoots Tag.D4 0)) →
      δ = δA 0 ∨ δ = δA 2 := fun δ h => h
  by_cases hA : ∀ u ∈ A, pc (rA 0) (u : ModGL Tag.D4 K) = 0 ∧ pc (rA 2) (u : ModGL Tag.D4 K) = 0
  ·
    have hall : ∀ q ∈ layerImage A 0, q = 1 := by
      intro q hq
      obtain ⟨x, hxA, hx⟩ := hcoord hq
      have := ev_inj (la.r 0) (la.f 0) {δA 0, δA 2} hreach0 (Multiplicative.toAdd q)
        (0 : UnitRoots Tag.D4 0 → K) (layerImage_coord la hfix 0 hq) (fun δ => by simp)
        (fun δ hδ => by
          rcases hmemS δ hδ with rfl | rfl
          · rw [hx]; exact (hA x hxA).1
          · rw [hx]; exact (hA x hxA).2)
      exact Multiplicative.toAdd.injective this
    have h1 := card_le_one_of_forall_eq_one _ hall
    exact ⟨h1.trans hqpos, Or.inl h1⟩
  · by_cases hX : ∃ u ∈ A, pc (rA 0) (u : ModGL Tag.D4 K) ≠ 0
    · obtain ⟨u₀, hu₀A, hu₀X⟩ := hX
      refine ⟨?_, Or.inr (Or.inl ?_)⟩
      · refine Nat.card_le_card_of_injective (fun q => Multiplicative.toAdd q.1 (δA 0)) ?_
        intro q q' h
        obtain ⟨x, hxA, hx⟩ := hcoord q.2
        obtain ⟨x', hx'A, hx'⟩ := hcoord q'.2
        have h0 : pc (rA 0) (x : ModGL Tag.D4 K) = pc (rA 0) (x' : ModGL Tag.D4 K) := by
          have := h
          simp only [hx (δA 0), hx' (δA 0)] at this
          exact this
        have c1 := claim_one hA0 hcomm hu₀A hxA
        have c2 := claim_one hA0 hcomm hu₀A hx'A
        have h2 : pc (rA 2) (x : ModGL Tag.D4 K) = pc (rA 2) (x' : ModGL Tag.D4 K) := by
          apply mul_left_cancel₀ hu₀X
          rw [c1, c2, h0]
        have := ev_inj (la.r 0) (la.f 0) {δA 0, δA 2} hreach0 (Multiplicative.toAdd q.1)
          (Multiplicative.toAdd q'.1) (layerImage_coord la hfix 0 q.2)
          (layerImage_coord la hfix 0 q'.2) (fun δ hδ => by
            rcases hmemS δ hδ with rfl | rfl
            · rw [hx, hx']; exact h0
            · rw [hx, hx']; exact h2)
        exact Subtype.ext (Multiplicative.toAdd.injective this)
      · refine card_le_one_of_forall_eq_one _ ?_
        rintro q ⟨x, hxA, rfl⟩
        have hx2 := claim_two la (p := d4Rho ^ (2 * ε)) hr hp h3 hA0 hcomm hfix hu₀A hu₀X hxA x.2
        exact unitPhi_triv Tag.D4 x hx2
    · push Not at hX
      obtain ⟨u₀, hu₀A, hu₀Y⟩ : ∃ u ∈ A, pc (rA 2) (u : ModGL Tag.D4 K) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hA fun u hu => ⟨hX u hu, hcon u hu⟩
      refine ⟨?_, Or.inr (Or.inr ?_)⟩
      · refine Nat.card_le_card_of_injective (fun q => Multiplicative.toAdd q.1 (δA 2)) ?_
        intro q q' h
        obtain ⟨x, hxA, hx⟩ := hcoord q.2
        obtain ⟨x', hx'A, hx'⟩ := hcoord q'.2
        have h2 : pc (rA 2) (x : ModGL Tag.D4 K) = pc (rA 2) (x' : ModGL Tag.D4 K) := by
          have := h
          simp only [hx (δA 2), hx' (δA 2)] at this
          exact this
        have := ev_inj (la.r 0) (la.f 0) {δA 0, δA 2} hreach0 (Multiplicative.toAdd q.1)
          (Multiplicative.toAdd q'.1) (layerImage_coord la hfix 0 q.2)
          (layerImage_coord la hfix 0 q'.2) (fun δ hδ => by
            rcases hmemS δ hδ with rfl | rfl
            · rw [hx, hx']; exact (hX x hxA).trans (hX x' hx'A).symm
            · rw [hx, hx']; exact h2)
        exact Subtype.ext (Multiplicative.toAdd.injective this)
      · refine card_le_one_of_forall_eq_one _ ?_
        rintro q ⟨x, hxA, rfl⟩
        have hx4 := claim_three hA0 hcomm hu₀A hu₀Y hxA x.2
        exact unitPhi_triv Tag.D4 x hx4

end Main

@[expose] def δB : UnitRoots Tag.D4 1 :=
  ⟨rB 0, (isPos_rB 0 (by simp)).1, by rw [(isPos_rB 0 (by simp)).2]; rfl⟩

@[expose] def δC : UnitRoots Tag.D4 2 :=
  ⟨rC 0 1, (isPos_rC 0 (by simp) 1 (by simp) (by decide)).1,
    by rw [(isPos_rC 0 (by simp) 1 (by simp) (by decide)).2]; rfl⟩

@[expose] def δT4 : UnitRoots Tag.D4 3 := ⟨rT4, isPos_rT4.1, by rw [isPos_rT4.2]; rfl⟩

@[expose] def δT5 : UnitRoots Tag.D4 4 := ⟨rT5, isPos_rT5.1, by rw [isPos_rT5.2]; rfl⟩

section Final

variable {α : MulAut ↥(adjointGroup Tag.D4 K)} (la : LayerAct Tag.D4 α (1 : K ≃+* K)) {ε : ℕ}
  (hε : ε = 1 ∨ ε = 2)
  (hr : ∀ (k : ℕ) (δ : UnitRoots Tag.D4 k), (la.r k δ).1 = permLattice (d4Rho ^ (2 * ε)) δ.1)

include hε hr

theorem card_le_of_graph [CharP K 3] (h3 : α ^ 3 = 1) {A : Subgroup ↥(adjointGroup Tag.D4 K)}
    (hA0 : A ≤ unitN Tag.D4 K 0) (hcomm : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u)
    (hfix : ∀ a ∈ A, α a = a) : Nat.card A ≤ Nat.card K ^ 4 := by
  classical
  obtain ⟨hL0, hcases⟩ := layer0_bound la hε hr h3 hA0 hcomm hfix
  have hL1 : Nat.card (layerImage A 1) ≤ Nat.card K :=
    layerImage_card_le la hfix 1 δB (reach_layer1 la hε hr δB rfl)
  have hL2 : Nat.card (layerImage A 2) ≤ Nat.card K :=
    layerImage_card_le la hfix 2 δC (reach_layer2 la hε hr δC rfl)
  have hL3 : Nat.card (layerImage A 3) ≤ Nat.card K :=
    layerImage_card_le la hfix 3 δT4 (fun δ => Or.inl (reach_single single4 δT4 δ rfl))
  have hL4 : Nat.card (layerImage A 4) ≤ Nat.card K :=
    layerImage_card_le la hfix 4 δT5 (fun δ => Or.inl (reach_single single5 δT5 δ rfl))
  have hd : (maxHeight Tag.D4).toNat = 5 := by rw [maxHeight_D4]; rfl
  have hbot : unitN Tag.D4 K 5 = ⊥ := by
    have := unitN_bot Tag.D4 (K := K)
    rwa [hd] at this
  have hprod := card_le_prod_of_filtration (unitN Tag.D4 K) (unitPhi Tag.D4 K) 5
    hbot (unitN_chain Tag.D4) unitPhi_eq_one_iff A hA0
    (fun k => Nat.card (layerImage A k)) (fun k _ => le_rfl)
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul] at hprod
  rcases hcases with h | h | h
  · calc Nat.card A ≤ _ := hprod
      _ ≤ 1 * Nat.card K * Nat.card K * Nat.card K * Nat.card K := by gcongr
      _ = Nat.card K ^ 4 := by ring
  · calc Nat.card A ≤ _ := hprod
      _ ≤ Nat.card K * 1 * Nat.card K * Nat.card K * Nat.card K := by gcongr
      _ = Nat.card K ^ 4 := by ring
  · calc Nat.card A ≤ _ := hprod
      _ ≤ Nat.card K * Nat.card K * Nat.card K * 1 * Nat.card K := by gcongr
      _ = Nat.card K ^ 4 := by ring

end Final

end CFSG.LocalAnalysis.GLTheoremA
