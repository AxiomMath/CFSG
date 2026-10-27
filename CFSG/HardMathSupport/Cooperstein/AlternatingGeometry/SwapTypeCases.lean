module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ReindexCaseTwo
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightBlockOfThetaX
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaSNormalizer
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaJJoin

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin

@[expose] def pairInv (r : ℕ) : Perm (OmegaE r 0) := Perm.sumCongr (blockFlip r) 1

theorem pairInv_inl (r : ℕ) (i : Fin r) (b : Bool) :
    pairInv r (Sum.inl (i, b)) = Sum.inl (i, !b) := rfl

theorem pairInv_ne (r : ℕ) (x : OmegaE r 0) : pairInv r x ≠ x := by
  rcases x with ⟨i, b⟩ | j
  · rw [pairInv_inl]; simp
  · exact j.elim0

theorem pairInv_invol (r : ℕ) (x : OmegaE r 0) : pairInv r (pairInv r x) = x := by
  rcases x with ⟨i, b⟩ | j
  · rw [pairInv_inl, pairInv_inl]; simp
  · exact j.elim0

theorem Wr_le_pairPres (r : ℕ) :
    Wr r 0 ≤ pairPres (pairInv r) (pairInv_ne r) (pairInv_invol r) := by
  rintro _ ⟨g, hg, rfl⟩ z
  rcases z with ⟨i, b⟩ | j
  · rw [embL_apply_inl]
    have h1 : (g (i, b)).1 = i := hg (i, b)
    rcases hg' : g (i, b) with ⟨k, c⟩
    rw [hg'] at h1
    simp only at h1
    subst h1
    cases b <;> cases c <;> simp [pairInv_inl]
  · exact j.elim0

theorem swap_pairInv_mem_Wr (r : ℕ) (x : OmegaE r 0) : swap x (pairInv r x) ∈ Wr r 0 := by
  rcases x with ⟨i, b⟩ | j
  · rw [pairInv_inl, embL_blockTransp r 0 i b]
    exact ⟨blockTransp i, swap_mem_blockFix rfl, rfl⟩
  · exact j.elim0

theorem Wr_zero_left (s : ℕ) : Wr 0 s = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨g, -, rfl⟩
  have : g = 1 := Equiv.ext fun p => p.1.elim0
  rw [this, map_one]
  exact one_mem _

variable {G : Type} [Group G] [Finite G] {S L : Subgroup G}

theorem eightTen_swapType_cases (hA : Asc81bHyp (L ⊔ S) S)
    (hLM : IsTwoPrimeComponent (L ⊔ S) L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hpS : pCoreOf 2 (L ⊔ S) ≤ S) {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hΩ : 9 ≤ Fintype.card Ω ∨ (7 ≤ Fintype.card Ω ∧ Odd (Fintype.card Ω)))
    (θ : ↥(L ⊔ S) →* Perm Ω)
    (hker : ∀ m : ↥(L ⊔ S), θ m = 1 ↔ (m : G) ∈ pCoreOf 2 (L ⊔ S))
    (hAltL : ∀ x ∈ alternatingGroup Ω,
      ∃ l : ↥L, θ ⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩ = x)
    (hsw : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      Offender.SwapType ((A.subgroupOf (L ⊔ S)).map θ))
    (hne : ((thompsonJ S).subgroupOf (L ⊔ S)).map θ ≠ ⊥) :
    (∃ r s : ℕ, 1 ≤ r ∧ 1 ≤ s ∧ 2 * r + s = Fintype.card Ω ∧
      EightBlockData (L ⊔ S) S L r s ∧ EightBlockDataX S L r s ∧ HasSym3Lift S L (L ⊔ S) ∧
      ((r = 1 ∨ r = 3 ∨ 5 ≤ r) → (s = 1 ∨ s = 3 ∨ 5 ≤ s) → HasSym3LiftS S L (L ⊔ S)) ∧
      ThetaTypeI S L r s ∧
      ∃ e : Ω ≃ OmegaE r s,
        ((thompsonJ S).subgroupOf (L ⊔ S)).map (e.permCongrHom.toMonoidHom.comp θ) = Wr r s) ∨
    (∃ n : ℕ, 5 ≤ n ∧ 2 * n = Fintype.card Ω ∧ PairActionData (L ⊔ S) S L n) := by
  classical
  obtain ⟨r, s, e, he⟩ := exists_omegaEquiv_Wr_of_offenders_swapType hA.twoRadical.isPGroup
    (le_sup_right : S ≤ L ⊔ S) θ hsw
  have hcard : 2 * r + s = Fintype.card Ω := by
    have := Fintype.card_congr e
    rw [this]
    simp [OmegaE, mul_comm]
  let θ' : ↥(L ⊔ S) →* Perm (OmegaE r s) := e.permCongrHom.toMonoidHom.comp θ
  have hθ' : ∀ m, θ' m = e.permCongr (θ m) := fun m => rfl
  have hker' : ∀ m : ↥(L ⊔ S), θ' m = 1 ↔ (m : G) ∈ pCoreOf 2 (L ⊔ S) := by
    intro m
    rw [hθ', ← hker m]
    constructor
    · intro h
      exact e.permCongr.injective (by rw [h]; exact (map_one e.permCongrHom).symm)
    · intro h
      rw [h]; exact (map_one e.permCongrHom)
  have hAlt' : ∀ x ∈ alternatingGroup (OmegaE r s),
      ∃ l : ↥L, θ' ⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩ = x := by
    intro x hx
    have hx' : e.permCongr.symm x ∈ alternatingGroup Ω := by
      rw [mem_alternatingGroup] at hx ⊢
      rw [← hx]
      have := Equiv.Perm.sign_permCongr e (e.permCongr.symm x)
      rw [← this]
      simp
    obtain ⟨l, hl⟩ := hAltL _ hx'
    exact ⟨l, by rw [hθ', hl]; exact Equiv.apply_symm_apply _ _⟩
  have hW' : ((thompsonJ S).subgroupOf (L ⊔ S)).map θ' = Wr r s := by
    rw [← he, Subgroup.map_map]
  have hr : 1 ≤ r := by
    by_contra h
    have hr0 : r = 0 := by omega
    subst hr0
    apply hne
    rw [Wr_zero_left] at he
    exact (Subgroup.map_eq_bot_iff_of_injective (f := e.permCongrHom.toMonoidHom) _ e.permCongrHom.injective).1 he
  have hT : ThetaTypeI S L r s :=
    ⟨θ', fun m h => hpS ((hker' m).1 h), fun x hx => by
      obtain ⟨l, hl⟩ := hAlt' x hx
      exact ⟨⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩, hl⟩, hW'⟩
  by_cases hs : s = 0
  · subst hs
    right
    have hc' : Fintype.card (OmegaE r 0) = 2 * r := by simp [OmegaE, mul_comm]
    have hr5 : 5 ≤ r := by
      rcases hΩ with h | ⟨h, k, hk⟩ <;> omega
    refine ⟨r, hr5, by omega, ?_⟩
    refine pairActionData_of_theta_perm hA hLM hSL hpS θ' hker' hAlt' (pairInv r)
      (pairInv_ne r) (pairInv_invol r) r hc' hr5 ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hW']; exact Wr_le_pairPres r
    · intro x y _ _ hx
      exact absurd (hW' ▸ swap_pairInv_mem_Wr r x) hx
    all_goals
      first
      | (intro h
         have h0 : (Finset.univ.filter fun x : OmegaE r 0 => swap x (pairInv r x) ∉
             (((thompsonJ S).subgroupOf (L ⊔ S)).map θ' : Subgroup (Perm (OmegaE r 0)))).card = 0 := by
           rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
           intro x _
           rw [hW']
           exact not_not.2 (swap_pairInv_mem_Wr r x)
         omega)
      | (intro h
         have h0 : (Finset.univ.filter fun x : OmegaE r 0 => swap x (pairInv r x) ∈
             (((thompsonJ S).subgroupOf (L ⊔ S)).map θ' : Subgroup (Perm (OmegaE r 0)))).card =
               Fintype.card (OmegaE r 0) := by
           rw [← Finset.card_univ]
           congr 1
           rw [Finset.filter_eq_self]
           intro x _
           rw [hW']
           exact swap_pairInv_mem_Wr r x
         omega)
  · left
    have h7 : 7 ≤ Fintype.card (OmegaE r s) := by
      have : Fintype.card (OmegaE r s) = 2 * r + s := by
        simp [OmegaE, mul_comm]
      rcases hΩ with h | ⟨h, -⟩ <;> omega
    refine ⟨r, s, hr, Nat.pos_of_ne_zero hs, hcard,
      eightBlockData_of_theta hA hLM hpS r s θ' hker' hAlt' hW',
      fun X hAX hLX hSLX hAut =>
        eightBlockData_of_theta_X (hAut (OmegaE r s) h7) hAX hLX hSLX hpS hr θ' hker' hAlt' hW',
      ?_, ?_, hT, e, hW'⟩
    swap
    · intro hr' hs'
      exact exists_sym3_liftS hA (le_sup_right : S ≤ L ⊔ S) (le_sup_left : L ≤ L ⊔ S) θ'
        (fun m h => hpS ((hker' m).1 h)) hAlt' (fun m hm => (hker' m).2 hm) hW' hr
        (Nat.pos_of_ne_zero hs) hr' hs'
    exact exists_sym3_lift hA.twoRadical.isPGroup (le_sup_right : S ≤ L ⊔ S)
      (le_sup_left : L ≤ L ⊔ S) θ' (fun m h => hpS ((hker' m).1 h)) hAlt'
      (fun m hm => (hker' m).2 hm) hW' hr (Nat.pos_of_ne_zero hs)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
