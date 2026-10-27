module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ExtractAT
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.SwapGenerated
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairPreserving

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

theorem exists_finBlockEquiv {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (σ : Perm Ω)
    (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x) (n : ℕ) (hn : Fintype.card Ω = 2 * n) :
    ∃ e : Ω ≃ Fin n × Bool, ∀ x, e (σ x) = ((e x).1, !(e x).2) := by
  obtain ⟨ι, i1, i2, e, hc, he⟩ := exists_blockEquiv σ hσ1 hσ2
  have hι : Fintype.card ι = n := by omega
  let f : ι ≃ Fin n := Fintype.equivFinOfCardEq hι
  refine ⟨e.trans (Equiv.prodCongr f (Equiv.refl Bool)), fun x => ?_⟩
  simp [he]

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem reindex_blockFix {n : ℕ} (σ : Perm Ω) (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x)
    (e : Ω ≃ Fin n × Bool) (he : ∀ x, e (σ x) = ((e x).1, !(e x).2))
    {W : Subgroup (Perm Ω)} (hWF : W ≤ pairPres σ hσ1 hσ2) :
    W.map e.permCongrHom.toMonoidHom ≤ blockFix (Fin n) := by
  rintro _ ⟨g, hg, rfl⟩ ⟨i, b⟩
  show ((e.permCongrHom g) (i, b)).1 = (i, b).1
  show (e (g (e.symm (i, b)))).1 = i
  rcases hWF hg (e.symm (i, b)) with h | h
  · rw [h]; simp
  · rw [h, he]; simp

theorem permCongr_swap_matching {n : ℕ} (σ : Perm Ω) (e : Ω ≃ Fin n × Bool)
    (he : ∀ x, e (σ x) = ((e x).1, !(e x).2)) (x : Ω) :
    e.permCongrHom (swap x (σ x)) = blockTransp (e x).1 := by
  rw [permCongr_swap_eq, he]
  obtain ⟨i, b⟩ := e x
  cases b
  · simp [blockTransp]
  · simp [blockTransp, swap_comm]

theorem blockTransp_mem_map_iff {n : ℕ} (σ : Perm Ω) (e : Ω ≃ Fin n × Bool)
    (he : ∀ x, e (σ x) = ((e x).1, !(e x).2)) {W : Subgroup (Perm Ω)} (x : Ω) :
    blockTransp (e x).1 ∈ W.map e.permCongrHom.toMonoidHom ↔ swap x (σ x) ∈ W := by
  rw [← permCongr_swap_matching σ e he x]
  exact Subgroup.mem_map_iff_mem (f := e.permCongrHom.toMonoidHom) e.permCongrHom.injective

theorem reindex_hD {n : ℕ} (σ : Perm Ω) (e : Ω ≃ Fin n × Bool)
    (he : ∀ x, e (σ x) = ((e x).1, !(e x).2)) (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x)
    {W : Subgroup (Perm Ω)}
    (hD : ∀ x y, y ≠ x → y ≠ σ x → swap x (σ x) ∉ W → swap y (σ y) ∉ W →
      swap x (σ x) * swap y (σ y) ∈ W) :
    ∀ i j : Fin n, blockTransp i ∉ W.map e.permCongrHom.toMonoidHom →
      blockTransp j ∉ W.map e.permCongrHom.toMonoidHom →
      blockTransp i * blockTransp j ∈ W.map e.permCongrHom.toMonoidHom := by
  have hbt := permCongr_swap_matching σ e he
  have hmem := blockTransp_mem_map_iff (W := W) σ e he
  intro i j hi hj
  by_cases hij : i = j
  · subst hij
    have : blockTransp i * blockTransp i = 1 := swap_mul_self _ _
    rw [this]; exact one_mem _
  set x := e.symm (i, false) with hx
  set y := e.symm (j, false) with hy
  have hex : (e x).1 = i := by simp [hx]
  have hey : (e y).1 = j := by simp [hy]
  have hxW : swap x (σ x) ∉ W := fun h => hi (by rw [← hex]; exact (hmem x).2 h)
  have hyW : swap y (σ y) ∉ W := fun h => hj (by rw [← hey]; exact (hmem y).2 h)
  have hyx : y ≠ x := fun h => hij (by rw [← hex, ← hey, h])
  have hyσ : y ≠ σ x := fun h => hij (by
    have := congrArg (fun z => (e z).1) h
    simp only [he] at this
    rw [← hex, ← hey]; exact this.symm)
  have := hD x y hyx hyσ hxW hyW
  have h2 := Subgroup.mem_map_of_mem e.permCongrHom.toMonoidHom this
  rw [map_mul] at h2
  have e1 : e.permCongrHom.toMonoidHom (swap x (σ x)) = blockTransp i := by
    show e.permCongrHom (swap x (σ x)) = _
    rw [hbt, hex]
  have e2 : e.permCongrHom.toMonoidHom (swap y (σ y)) = blockTransp j := by
    show e.permCongrHom (swap y (σ y)) = _
    rw [hbt, hey]
  rwa [e1, e2] at h2

theorem card_filter_swap_eq {n : ℕ} (σ : Perm Ω) (e : Ω ≃ Fin n × Bool)
    (he : ∀ x, e (σ x) = ((e x).1, !(e x).2)) {W : Subgroup (Perm Ω)} (q : Prop → Prop)
    [DecidablePred fun x : Ω => q (swap x (σ x) ∈ W)]
    [DecidablePred fun i : Fin n => q (blockTransp i ∈ W.map e.permCongrHom.toMonoidHom)] :
    (Finset.univ.filter fun x : Ω => q (swap x (σ x) ∈ W)).card =
      2 * (Finset.univ.filter fun i : Fin n => q (blockTransp i ∈ W.map e.permCongrHom.toMonoidHom)).card := by
  have hmem := blockTransp_mem_map_iff (W := W) σ e he
  have : (Finset.univ.filter fun x : Ω => q (swap x (σ x) ∈ W)).card =
      ((Finset.univ.filter fun i : Fin n =>
        q (blockTransp i ∈ W.map e.permCongrHom.toMonoidHom)) ×ˢ (Finset.univ : Finset Bool)).card := by
    refine Finset.card_equiv e fun x => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, and_true]
    rw [hmem x]
  rw [this, Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm]

section GroupLevel

open CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {S L : Subgroup G}

open scoped Classical in
theorem pairActionData_of_theta_perm (hA : Asc81bHyp (L ⊔ S) S)
    (hLM : IsTwoPrimeComponent (L ⊔ S) L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hpS : pCoreOf 2 (L ⊔ S) ≤ S) {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (θ : ↥(L ⊔ S) →* Perm Ω)
    (hker : ∀ m : ↥(L ⊔ S), θ m = 1 ↔ (m : G) ∈ pCoreOf 2 (L ⊔ S))
    (hAltL : ∀ x ∈ alternatingGroup Ω,
      ∃ l : ↥L, θ ⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩ = x)
    (σ : Perm Ω) (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x) (n : ℕ)
    (hn : Fintype.card Ω = 2 * n) (hn5 : 5 ≤ n)
    (hWF : (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω)) ≤ pairPres σ hσ1 hσ2)
    (hD : ∀ x y, y ≠ x → y ≠ σ x →
      swap x (σ x) ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω)) →
      swap y (σ y) ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω)) →
      swap x (σ x) * swap y (σ y) ∈
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω)))
    (hN1 : (Finset.univ.filter fun x : Ω => swap x (σ x) ∉
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω))).card ≠ 2 * 1)
    (hN2 : (Finset.univ.filter fun x : Ω => swap x (σ x) ∉
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω))).card ≠ 2 * 2)
    (hN4 : (Finset.univ.filter fun x : Ω => swap x (σ x) ∉
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω))).card ≠ 2 * 4)
    (hC2 : (Finset.univ.filter fun x : Ω => swap x (σ x) ∈
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω))).card ≠ 2 * 2)
    (hC4 : (Finset.univ.filter fun x : Ω => swap x (σ x) ∈
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω))).card ≠ 2 * 4) :
    PairActionData (L ⊔ S) S L n := by
  obtain ⟨e, he⟩ := exists_finBlockEquiv σ hσ1 hσ2 n hn
  let θ' : ↥(L ⊔ S) →* Perm (Fin n × Bool) := e.permCongrHom.toMonoidHom.comp θ
  have hθ' : ∀ m, θ' m = e.permCongr (θ m) := fun m => rfl
  have hW' : ((thompsonJ S).subgroupOf (L ⊔ S)).map θ' =
      (((thompsonJ S).subgroupOf (L ⊔ S)).map θ).map e.permCongrHom.toMonoidHom := by
    rw [Subgroup.map_map]
  refine pairActionData_of_caseTwo hA hLM hSL hpS n hn5 θ' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro m
    rw [hθ', ← hker m]
    constructor
    · intro h
      exact e.permCongr.injective (by rw [h]; exact (map_one e.permCongrHom).symm)
    · intro h
      rw [h]; exact (map_one e.permCongrHom)
  · intro x hx
    have hx' : e.permCongr.symm x ∈ alternatingGroup Ω := by
      rw [mem_alternatingGroup] at hx ⊢
      rw [← hx]
      have := Equiv.Perm.sign_permCongr e (e.permCongr.symm x)
      rw [← this]
      simp
    obtain ⟨l, hl⟩ := hAltL _ hx'
    exact ⟨l, by rw [hθ', hl]; exact Equiv.apply_symm_apply _ _⟩
  · rw [hW']; exact reindex_blockFix σ hσ1 hσ2 e he hWF
  · rw [hW']; exact reindex_hD σ e he hσ1 hσ2 hD
  · rw [hW']
    intro h
    apply hN1
    rw [card_filter_swap_eq σ e he Not, h]
  · rw [hW']
    intro h
    apply hN2
    rw [card_filter_swap_eq σ e he Not, h]
  · rw [hW']
    intro h
    apply hN4
    rw [card_filter_swap_eq σ e he Not, h]
  · rw [hW']
    intro h
    apply hC2
    have h' := card_filter_swap_eq σ e he (W := ((thompsonJ S).subgroupOf (L ⊔ S)).map θ) id
    simp only [id_eq] at h'
    rw [h', h]
  · rw [hW']
    intro h
    apply hC4
    have h' := card_filter_swap_eq σ e he (W := ((thompsonJ S).subgroupOf (L ⊔ S)).map θ) id
    simp only [id_eq] at h'
    rw [h', h]

end GroupLevel

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
