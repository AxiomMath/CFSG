module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FStable

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three

variable {K : Type} [Field K] [Finite K]


@[expose] def LayerAct.comp' {α β : MulAut ↥(adjointGroup Tag.D4 K)} {σ₁ σ₂ : K ≃+* K}
    (la₁ : LayerAct Tag.D4 α σ₁) (la₂ : LayerAct Tag.D4 β σ₂) :
    LayerAct Tag.D4 (α * β) (σ₁ * σ₂) where
  r k δ := la₂.r k (la₁.r k δ)
  f k δ := la₁.f k δ * σ₁ (la₂.f k (la₁.r k δ))
  stable k x hx := la₁.stable k _ (la₂.stable k x hx)
  coord k δ x hx := by
    have h1 := la₁.coord k δ (β x) (la₂.stable k x hx)
    have h2 := la₂.coord k (la₁.r k δ) x hx
    rw [MulAut.mul_apply, h1, h2, map_mul, mul_assoc]
    rfl


open scoped Classical in
theorem rootCoord_rootElt {k : ℕ} (δ γ : UnitRoots Tag.D4 k) (c : K) :
    rootCoord (UnitRoots.pos Tag.D4 δ) ((rootElt γ.1 c : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      if γ = δ then c else 0 := by
  have h := pc_pinnedX_same (K := K) (UnitRoots.pos Tag.D4 δ) (UnitRoots.pos Tag.D4 γ)
    (by rw [δ.2.2, γ.2.2]) c
  rw [pc_of_pos (UnitRoots.pos Tag.D4 δ)] at h
  rw [coe_rootElt, h]
  by_cases hγδ : γ = δ
  · rw [if_pos hγδ, if_pos (congrArg Subtype.val hγδ)]
  · rw [if_neg hγδ, if_neg (fun h => hγδ (Subtype.ext h))]

theorem rootElt_mem_unitN' {k : ℕ} (γ : UnitRoots Tag.D4 k) (c : K) : rootElt γ.1 c ∈ unitN Tag.D4 K k :=
  rootElt_mem_unitN ⟨γ.2.1, γ.2.2⟩ c

theorem layerAct_f_ne_zero' {α : MulAut ↥(adjointGroup Tag.D4 K)} {σ : K ≃+* K}
    (la : LayerAct Tag.D4 α σ) (k : ℕ) (δ : UnitRoots Tag.D4 k) : la.f k δ ≠ 0 := by
  intro h0
  set y : ↥(adjointGroup Tag.D4 K) := rootElt δ.1 1 with hy
  have hyN : y ∈ unitN Tag.D4 K k := rootElt_mem_unitN' δ 1
  let φ : unitN Tag.D4 K k → unitN Tag.D4 K k := fun x => ⟨α x, la.stable k x x.2⟩
  have hφinj : Function.Injective φ := fun a b h => Subtype.ext (α.injective (congrArg Subtype.val h))
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hφinj ⟨y, hyN⟩
  have hαx : α (x : ↥(adjointGroup Tag.D4 K)) = y := congrArg Subtype.val hx
  have h1 := la.coord k δ x x.2
  rw [hαx, h0, zero_mul] at h1
  have h2 := rootCoord_rootElt (K := K) δ δ 1
  rw [if_pos rfl] at h2
  rw [← hy] at h2
  rw [h2] at h1
  exact one_ne_zero h1

open scoped Classical in
theorem LayerAct.unique' {α : MulAut ↥(adjointGroup Tag.D4 K)} {σ σ' : K ≃+* K}
    (la : LayerAct Tag.D4 α σ) (la' : LayerAct Tag.D4 α σ') :
    (∀ k δ, la.r k δ = la'.r k δ) ∧ σ = σ' := by
  have key : ∀ (k : ℕ) (δ : UnitRoots Tag.D4 k), la.r k δ = la'.r k δ ∧ ∀ c : K, σ c = σ' c := by
    intro k δ
    have hx : ∀ c : K, rootElt (la.r k δ).1 c ∈ unitN Tag.D4 K k := fun c => rootElt_mem_unitN' _ c
    have e1 : ∀ c : K, la.f k δ * σ c = la'.f k δ * σ' (if la.r k δ = la'.r k δ then c else 0) := by
      intro c
      have h1 := la.coord k δ _ (hx c)
      have h2 := la'.coord k δ _ (hx c)
      rw [rootCoord_rootElt, if_pos rfl] at h1
      rw [rootCoord_rootElt] at h2
      exact h1.symm.trans h2
    have hf0 := layerAct_f_ne_zero' la k δ
    have hr : la.r k δ = la'.r k δ := by
      by_contra hne
      have := e1 1
      rw [if_neg hne, map_zero, mul_zero, map_one, mul_one] at this
      exact hf0 this
    have hf : la.f k δ = la'.f k δ := by
      have := e1 1
      rw [if_pos hr, map_one, map_one, mul_one, mul_one] at this
      exact this
    refine ⟨hr, fun c => ?_⟩
    have := e1 c
    rw [if_pos hr, ← hf] at this
    exact mul_left_cancel₀ hf0 this
  exact ⟨fun k δ => (key k δ).1, RingEquiv.ext (key 0 (δA 0)).2⟩


theorem ev_inj_sigma {K I : Type*} [CommRing K] (σ : K ≃+* K) (r : I → I) (f : I → K) (S : Set I)
    (hreach : ∀ δ, δ ∈ S ∨ r δ ∈ S ∨ r (r δ) ∈ S) (a b : I → K)
    (ha : ∀ δ, a δ = f δ * σ (a (r δ))) (hb : ∀ δ, b δ = f δ * σ (b (r δ)))
    (h : ∀ δ ∈ S, a δ = b δ) : a = b := by
  funext δ
  rcases hreach δ with h0 | h1 | h2
  · exact h δ h0
  · rw [ha δ, hb δ, h _ h1]
  · have e1 : a (r δ) = b (r δ) := by
      rw [ha (r δ), hb (r δ), h _ h2]
    rw [ha δ, hb δ, e1]

theorem layerImage_coord_sigma {α : MulAut ↥(adjointGroup Tag.D4 K)} {σ : K ≃+* K}
    (la : LayerAct Tag.D4 α σ) {A : Subgroup ↥(adjointGroup Tag.D4 K)}
    (hfix : ∀ a ∈ A, α a = a) (k : ℕ) {q : UnitCoord Tag.D4 K k} (hq : q ∈ layerImage A k)
    (δ : UnitRoots Tag.D4 k) :
    Multiplicative.toAdd q δ = la.f k δ * σ (Multiplicative.toAdd q (la.r k δ)) := by
  have h := congrArg (fun q' : UnitCoord Tag.D4 K k => Multiplicative.toAdd q' δ)
    (layerImage_fixed la hfix k hq)
  exact h.symm


theorem layerImage_pair_card {f g : MulAut ↥(adjointGroup Tag.D4 K)} {σf σg : K ≃+* K}
    (hσ3 : σf ^ 3 = 1) (hσ : σf ≠ 1)
    (laf : LayerAct Tag.D4 f σf) (lag : LayerAct Tag.D4 g σg)
    (hrf : ∀ k δ, laf.r k δ = δ)
    {A : Subgroup ↥(adjointGroup Tag.D4 K)} (hf : ∀ a ∈ A, f a = a) (hg : ∀ a ∈ A, g a = a)
    (k : ℕ) (S : Finset (UnitRoots Tag.D4 k))
    (hreach : ∀ δ : UnitRoots Tag.D4 k, δ ∈ S ∨ lag.r k δ ∈ S ∨ lag.r k (lag.r k δ) ∈ S) :
    Nat.card (layerImage A k) ^ 3 ≤ Nat.card K ^ S.card := by
  classical
  let τ : (S → K) →+ (S → K) :=
    { toFun := fun w s => laf.f k s.1 * σf (w s)
      map_zero' := by ext s; simp
      map_add' := by intro a b; ext s; simp [mul_add] }
  have hτ : ∀ (c : K) (a : S → K), τ (c • a) = σf c • τ a := by
    intro c a
    ext s
    simp only [τ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  have hinj : Nat.card (layerImage A k) ≤ Nat.card {w : S → K // τ w = w} := by
    refine Nat.card_le_card_of_injective (fun q => ⟨fun s => Multiplicative.toAdd q.1 s.1, ?_⟩) ?_
    · funext s
      have h := layerImage_coord_sigma laf hf k q.2 s.1
      rw [hrf] at h
      exact h.symm
    · intro q q' h
      have hh := congrArg Subtype.val h
      have := ev_inj_sigma σg (lag.r k) (lag.f k) (S : Set (UnitRoots Tag.D4 k)) hreach
        (Multiplicative.toAdd q.1) (Multiplicative.toAdd q'.1)
        (layerImage_coord_sigma lag hg k q.2) (layerImage_coord_sigma lag hg k q'.2)
        (fun δ hδ => congrFun hh ⟨δ, hδ⟩)
      exact Subtype.ext (Multiplicative.toAdd.injective this)
  calc Nat.card (layerImage A k) ^ 3 ≤ Nat.card {w : S → K // τ w = w} ^ 3 :=
        Nat.pow_le_pow_left hinj 3
    _ ≤ Nat.card K ^ Fintype.card S := card_fixed_pow_le σf hσ3 hσ τ hτ
    _ = Nat.card K ^ S.card := by rw [Fintype.card_coe]


section ReachSigma

variable {α : MulAut ↥(adjointGroup Tag.D4 K)} {σ : K ≃+* K} (la : LayerAct Tag.D4 α σ) {ε : ℕ}
  (hε : ε = 1 ∨ ε = 2)
  (hr : ∀ (k : ℕ) (δ : UnitRoots Tag.D4 k), (la.r k δ).1 = permLattice (d4Rho ^ (2 * ε)) δ.1)

include hε hr

theorem reach_layer0_sigma :
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

theorem reach_layer1_sigma (δ₀ : UnitRoots Tag.D4 1) (hδ₀ : δ₀.1 = rB 0) :
    ∀ δ : UnitRoots Tag.D4 1, δ = δ₀ ∨ la.r 1 δ = δ₀ ∨ la.r 1 (la.r 1 δ) = δ₀ := by
  intro δ
  have h := reach1 ε (by rcases hε with rfl | rfl <;> simp) δ.1 (unitRoot_mem_at δ)
  rcases h with h | h | h
  · exact Or.inl (Subtype.ext (h.trans hδ₀.symm))
  · exact Or.inr (Or.inl (Subtype.ext ((hr 1 δ).trans (h.trans hδ₀.symm))))
  · refine Or.inr (Or.inr (Subtype.ext ?_))
    rw [hr 1 (la.r 1 δ), hr 1 δ]
    exact h.trans hδ₀.symm

theorem reach_layer2_sigma (δ₀ : UnitRoots Tag.D4 2) (hδ₀ : δ₀.1 = rC 0 1) :
    ∀ δ : UnitRoots Tag.D4 2, δ = δ₀ ∨ la.r 2 δ = δ₀ ∨ la.r 2 (la.r 2 δ) = δ₀ := by
  intro δ
  have h := reach2 ε (by rcases hε with rfl | rfl <;> simp) δ.1 (unitRoot_mem_at δ)
  rcases h with h | h | h
  · exact Or.inl (Subtype.ext (h.trans hδ₀.symm))
  · exact Or.inr (Or.inl (Subtype.ext ((hr 2 δ).trans (h.trans hδ₀.symm))))
  · refine Or.inr (Or.inr (Subtype.ext ?_))
    rw [hr 2 (la.r 2 δ), hr 2 δ]
    exact h.trans hδ₀.symm

end ReachSigma


theorem card_pow_le_of_pair {f g : MulAut ↥(adjointGroup Tag.D4 K)} {σf σg : K ≃+* K}
    (hσ3 : σf ^ 3 = 1) (hσ : σf ≠ 1)
    (laf : LayerAct Tag.D4 f σf) (lag : LayerAct Tag.D4 g σg)
    (hrf : ∀ k δ, laf.r k δ = δ) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hrg : ∀ (k : ℕ) (δ : UnitRoots Tag.D4 k), (lag.r k δ).1 = permLattice (d4Rho ^ (2 * ε)) δ.1)
    {A : Subgroup ↥(adjointGroup Tag.D4 K)} (hA0 : A ≤ unitN Tag.D4 K 0)
    (hf : ∀ a ∈ A, f a = a) (hg : ∀ a ∈ A, g a = a) : Nat.card A ^ 3 ≤ Nat.card K ^ 6 := by
  classical
  have hqpos : 1 ≤ Nat.card K := Nat.card_pos
  have hL0 : Nat.card (layerImage A 0) ^ 3 ≤ Nat.card K ^ 2 := by
    have := layerImage_pair_card hσ3 hσ laf lag hrf hf hg 0 {δA 0, δA 2} (fun δ => by
      simpa using reach_layer0_sigma lag hε hrg δ)
    exact this.trans (Nat.pow_le_pow_right hqpos (Finset.card_le_two))
  have hL1 : Nat.card (layerImage A 1) ^ 3 ≤ Nat.card K := by
    have := layerImage_pair_card hσ3 hσ laf lag hrf hf hg 1 {δB} (fun δ => by
      simpa using reach_layer1_sigma lag hε hrg δB rfl δ)
    simpa using this
  have hL2 : Nat.card (layerImage A 2) ^ 3 ≤ Nat.card K := by
    have := layerImage_pair_card hσ3 hσ laf lag hrf hf hg 2 {δC} (fun δ => by
      simpa using reach_layer2_sigma lag hε hrg δC rfl δ)
    simpa using this
  have hL3 : Nat.card (layerImage A 3) ^ 3 ≤ Nat.card K := by
    have := layerImage_pair_card hσ3 hσ laf lag hrf hf hg 3 {δT4} (fun δ => by
      simpa using Or.inl (reach_single single4 δT4 δ rfl))
    simpa using this
  have hL4 : Nat.card (layerImage A 4) ^ 3 ≤ Nat.card K := by
    have := layerImage_pair_card hσ3 hσ laf lag hrf hf hg 4 {δT5} (fun δ => by
      simpa using Or.inl (reach_single single5 δT5 δ rfl))
    simpa using this
  have hd : (maxHeight Tag.D4).toNat = 5 := by rw [maxHeight_D4]; rfl
  have hbot : unitN Tag.D4 K 5 = ⊥ := by
    have := unitN_bot Tag.D4 (K := K)
    rwa [hd] at this
  have hprod := card_le_prod_of_filtration (unitN Tag.D4 K) (unitPhi Tag.D4 K) 5
    hbot (unitN_chain Tag.D4) unitPhi_eq_one_iff A hA0
    (fun k => Nat.card (layerImage A k)) (fun k _ => le_rfl)
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul] at hprod
  calc Nat.card A ^ 3 ≤ (Nat.card (layerImage A 0) * Nat.card (layerImage A 1) *
        Nat.card (layerImage A 2) * Nat.card (layerImage A 3) * Nat.card (layerImage A 4)) ^ 3 :=
        Nat.pow_le_pow_left hprod 3
    _ = Nat.card (layerImage A 0) ^ 3 * Nat.card (layerImage A 1) ^ 3 *
        Nat.card (layerImage A 2) ^ 3 * Nat.card (layerImage A 3) ^ 3 *
        Nat.card (layerImage A 4) ^ 3 := by ring
    _ ≤ Nat.card K ^ 2 * Nat.card K * Nat.card K * Nat.card K * Nat.card K := by gcongr
    _ = Nat.card K ^ 6 := by ring

end CFSG.LocalAnalysis.GLTheoremA
