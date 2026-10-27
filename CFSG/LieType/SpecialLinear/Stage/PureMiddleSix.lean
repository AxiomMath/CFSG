module

public import CFSG.LieType.SpecialLinear.Stage.Active
public import CFSG.LieType.SpecialLinear.Stage.GraphSymmetry
public import CFSG.LieType.SpecialLinear.Stage.InnerDichotomy
public import CFSG.LieType.SpecialLinear.SLModel.Recognition
public import CFSG.LieType.SpecialLinear.SLModel.CubeModel
public import CFSG.LieType.SpecialLinear.TypeLabel.StagePeriod
public import CFSG.LieType.SpecialLinear.TypeLabel.Rotation
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusNum

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
  CFSG.LieType.SpecialLinear.ExteriorModel CFSG.LieType.SpecialLinear.SLModel
  CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar CFSG.LieType.SpecialLinear.PureMiddle
  CFSG.HardMathSupport.GuralnickMalle
open Module
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.Theory.Representation
open scoped TensorProduct

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
  {E : Type} [Field E] [Fintype E] [CharP E 2] [Algebra (ZMod 2) E]
  {k : Type} [Field k] [CharP k 2] [Algebra E k] [Algebra F k]
  {D : Type} [Group D] [Finite D]
  {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Module E X]
  [IsScalarTower (ZMod 2) E X] [Finite X]

omit [Algebra (ZMod 2) E] [IsScalarTower (ZMod 2) E X] in
theorem stage_pm6_false (hq : 4 ≤ Fintype.card F)
    (σ : Representation E (SpecialLinearGroup (Fin 6) F) X)
    (hsimp : IsSimpleRep (extendScalars k σ))
    {y : k ⊗[E] X} {χ : SpecialLinearGroup (Fin 6) F → k} {J : Finset (Fin 5)}
    (ht : IsCoverType (rankOne 5 F 2) (extendScalars k σ) y χ J)
    (hJ : J = {0, 1, 3, 4})
    (δ : Representation (ZMod 2) D X)
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (_hD : IsPGroup 2 D) (hD2 : ∀ d, δ d * δ d = 1)
    (hquad : ∀ a b x, δ b (δ a x - x) = δ a x - x)
    (hcompat : ∀ d, ∃ A : GL (Fin 6) F, IsUpperGL A ∧
      ∃ (τ : F ≃+* F) (ε : ℕ),
        ∀ g x, δ d (σ g x) = σ (borelStd 6 F A τ ε g) (δ d x))
    (hgraph : ∃ d, ∃ A : GL (Fin 6) F, IsUpperGL A ∧ ∃ τ : F ≃+* F,
      ∀ g x, δ d (σ g x) = σ (borelStd 6 F A τ 1 g) (δ d x))
    (hered : ∀ Z : Submodule (ZMod 2) X, (∀ d, ∀ z ∈ Z, δ d z ∈ Z) →
      IsOffenderOn δ ⊤ Z) : False := by
  classical
  obtain ⟨f₀, -, hF₀⟩ := FiniteField.card F 2
  let f : ℕ := f₀
  have hF : Fintype.card F = 2 ^ f := by simpa only [f] using hF₀
  have hq2 : 2 < Fintype.card F := by omega
  have hf2 : 2 ≤ f := by
    have h4 : 4 ≤ 2 ^ f := by rw [← hF]; exact hq
    by_contra hlt
    push Not at hlt
    interval_cases f <;> norm_num at h4
  obtain ⟨s₀, -, hE₀⟩ := FiniteField.card E 2
  let s : ℕ := s₀
  have hE : Fintype.card E = 2 ^ s := by simpa only [s] using hE₀
  have hs1 : 1 ≤ s := by
    have h2 : 1 < Fintype.card E := Fintype.one_lt_card
    rw [hE] at h2
    by_contra h
    push Not at h
    have h0 : s = 0 := by omega
    rw [h0] at h2
    norm_num at h2
  have h2J : (2 : Fin 5) ∉ J := by
    rw [hJ]
    simp
  obtain ⟨g₀, hg₀⟩ := exists_ne_one_of_not_mem_isCoverType (n := 5) (p := 2) (F := F)
    (V := k ⊗[E] X) (ρ := extendScalars k σ) ht h2J
  obtain ⟨g₀, hg₀⟩ := exists_ne_one_of_extendScalars (E := E) (k := k) σ ⟨g₀, hg₀⟩
  have hne : ∃ g, σ g ≠ 1 := ⟨g₀, hg₀⟩
  have hD1 : ∃ d, δ d ≠ 1 :=
    exists_actor_ne_one_of_graph (n := 5) (by norm_num) σ hne δ hgraph
  have hoff : IsOffenderOn δ ⊤ ⊤ := hered ⊤ (fun d z hz => by simp)
  obtain ⟨ε, h0, hχε, hJε, β, hβ⟩ :=
    SLModel.exists_iso_slModelRep (F := F) (k := k) (m := 5) hF hsimp ht
  have hsub3 : ∀ r, ε r ⊆ {3} := by
    intro r j hj
    by_cases hj0 : j = 0
    · rw [hj0] at hj
      exact absurd hj (h0 r)
    · obtain ⟨t, ht⟩ := Fin.exists_succ_eq_of_ne_zero hj0
      have htJ : t ∉ J := by
        intro htj
        exact (hJε t).mp htj r (ht ▸ hj)
      have ht2 : t = 2 := by
        rw [hJ] at htJ
        fin_cases t <;> simp_all
      rw [← ht, ht2]
      simp [Fin.succ]
  have hε_or : ∀ r, ε r = ∅ ∨ ε r = {3} := by
    intro r
    by_cases h : ε r = ∅
    · exact Or.inl h
    · right
      have hne : (ε r).Nonempty := Finset.nonempty_iff_ne_empty.mpr h
      obtain ⟨j, hj⟩ := hne
      have hj3 : j = 3 := by
        simpa using hsub3 r hj
      exact Finset.Subset.antisymm (hsub3 r) (by
        rw [Finset.singleton_subset_iff]
        rwa [hj3] at hj)
  have hsupp : ∃ r, ε r ≠ ∅ := by
    by_contra h
    push Not at h
    have hmem : (2 : Fin 5) ∈ J := (hJε 2).mpr fun r => by rw [h r]; simp
    rw [hJ] at hmem
    simp at hmem
  let h : ℕ := (Finset.univ.filter fun r => ε r ≠ ∅).card
  have hh1 : 1 ≤ h := by
    obtain ⟨r, hr⟩ := hsupp
    simp only [h]
    exact Finset.card_pos.mpr ⟨r, by simp [hr]⟩
  have hbdeg3 : ∀ p : Fin f × Fin 6, bdeg ε p = 3 ↔ p.2 = 3 ∧ p.2 ∈ ε p.1 := by
    intro p
    rw [bdeg]
    by_cases hmem : p.2 ∈ ε p.1
    · rw [if_pos hmem]
      constructor
      · intro hp
        exact ⟨Fin.ext hp, hmem⟩
      · rintro ⟨hp, -⟩
        exact congrArg Fin.val hp
    · rw [if_neg hmem]
      exact ⟨fun h => absurd h (by norm_num), fun h => absurd h.2 hmem⟩
  have hd : ∀ p : Fin f × Fin 6, bdeg ε p = 0 ∨ bdeg ε p = 3 := by
    intro p
    rw [bdeg]
    by_cases hmem : p.2 ∈ ε p.1
    · right
      have h3 : p.2 = 3 := by simpa using hsub3 p.1 hmem
      rw [if_pos hmem, h3]
      norm_num
    · left
      rw [if_neg hmem]
  have hcount : (Finset.univ.filter fun p : Fin f × Fin 6 => bdeg ε p = 3).card = h := by
    simp only [h]
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      intro hemp
      have h3 := (hbdeg3 p).mp hp
      rw [hemp] at h3
      simp at h3
    · intro p hp q hq hpq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
      have hp2 := ((hbdeg3 p).mp hp).1
      have hq2 := ((hbdeg3 q).mp hq).1
      exact Prod.ext hpq (hp2.trans hq2.symm)
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      have hr3 : ε r = {3} := (hε_or r).resolve_left hr
      refine ⟨(r, 3), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hbdeg3]
      exact ⟨rfl, by simp [hr3]⟩
  have hεcard : ∀ r, (ε r).card ≤ 1 := by
    intro r
    rcases hε_or r with h' | h' <;> simp [h']
  let e : BModel k ε ≃ₗ[k] (BIdx ε → k) := bModelEquivOfCardLeOne (k := k) ε hεcard
  have he : ∀ (g : SpecialLinearGroup (Fin 6) F) (v : BModel k ε),
      e (slModelRep (F := F) (k := k) ε g v) =
        bMat ε (fun r => (g : Matrix (Fin 6) (Fin 6) F).map (frobTwist F k f r)) *ᵥ e v := by
    intro g v
    have h := bModelEquivOfCardLeOne_bRep (k := k) (n := 6) (τ := Fin f) ε hεcard
      (twistHom (frobTwist F k f) g) v
    exact h
  let M : SpecialLinearGroup (Fin 6) F → Matrix (BIdx ε) (BIdx ε) k :=
    fun g => bMat ε (fun r => (g : Matrix (Fin 6) (Fin 6) F).map (frobTwist F k f r))
  have hM1 : M 1 = 1 := by
    simp only [M]
    have hfam : (fun r => ((1 : SpecialLinearGroup (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F).map (frobTwist F k f r)) =
        fun _ => (1 : Matrix (Fin 6) (Fin 6) k) := by
      funext r
      rw [Matrix.SpecialLinearGroup.coe_one, Matrix.map_one]
      · exact (frobTwist F k f r).map_zero
      · exact (frobTwist F k f r).map_one
    rw [hfam, bMat_one]
  let ρm : Representation k (SpecialLinearGroup (Fin 6) F) (BIdx ε → k) :=
    { toFun := fun g => (M g).mulVecLin
      map_one' := by
        rw [hM1, Matrix.mulVecLin_one]
        rfl
      map_mul' := by
        intro g g'
        apply LinearMap.ext
        intro v
        have hmat : M (g * g') = M g * M g' := by
          simp only [M]
          rw [Matrix.SpecialLinearGroup.coe_mul]
          rw [show (fun r => ((g : Matrix (Fin 6) (Fin 6) F) *
              (g' : Matrix (Fin 6) (Fin 6) F)).map (frobTwist F k f r)) =
              fun r => (g : Matrix (Fin 6) (Fin 6) F).map (frobTwist F k f r) *
                (g' : Matrix (Fin 6) (Fin 6) F).map (frobTwist F k f r) from
            funext fun r => Matrix.map_mul]
          rw [bMat_mul]
        rw [hmat, Matrix.mulVecLin_mul]
        rfl }
  let γ : (k ⊗[E] X) ≃ₗ[k] (BIdx ε → k) := β.trans e
  have hγ : ∀ (g : SpecialLinearGroup (Fin 6) F) (v : k ⊗[E] X),
      γ (extendScalars k σ g v) = M g *ᵥ γ v := by
    intro g v
    simp only [γ, LinearEquiv.trans_apply, M]
    rw [hβ g v, he g (β v)]
  have hγm : ∀ (g : SpecialLinearGroup (Fin 6) F) (v : k ⊗[E] X),
      γ (extendScalars k σ g v) = ρm g (γ v) := by
    intro g v
    rw [hγ g v]
    rfl
  have hrank_eq : ∀ g : SpecialLinearGroup (Fin 6) F,
      finrank k (LinearMap.range (extendScalars k σ g - 1)) = (M g - 1).rank := by
    intro g
    rw [finrank_range_sub_one_eq_of_equiv γ hγm g]
    have hsub : ρm g - 1 = (M g - 1).mulVecLin := by
      ext v
      simp [ρm]
    rw [hsub]
    rfl
  have hgu : ∀ u : SpecialLinearGroup (Fin 6) F, u * u = 1 →
      (u : Matrix (Fin 6) (Fin 6) F) * (u : Matrix (Fin 6) (Fin 6) F) = 1 := by
    intro u hu
    rw [← Matrix.SpecialLinearGroup.coe_mul, hu, Matrix.SpecialLinearGroup.coe_one]
  have hgu1 : ∀ u : SpecialLinearGroup (Fin 6) F, u ≠ 1 →
      (u : Matrix (Fin 6) (Fin 6) F) ≠ 1 := by
    intro u hu1 h
    apply hu1
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have := congrFun (congrFun h i) j
    simpa using this
  have hrank6 : ∀ u : SpecialLinearGroup (Fin 6) F, u * u = 1 → u ≠ 1 →
      6 ≤ finrank k (LinearMap.range (extendScalars k σ u - 1)) := by
    intro u hu hu1
    rw [hrank_eq u]
    have h6 := six_mul_le_rank_kronMinor_sub_one (K := F) (k := k) (ι := Fin f × Fin 6)
      (d := bdeg ε) hd (fun p => frobTwist F k f p.1) (u : Matrix (Fin 6) (Fin 6) F)
      (hgu u hu) (hgu1 u hu1) (by rw [hcount]; exact hh1)
    have h6' : 6 ≤ 6 * h := by omega
    refine h6'.trans ?_
    rw [← hcount]
    simpa only [M, bMat] using h6
  by_cases h2 : 2 ≤ h
  ·
    have hrank12 : ∀ u : SpecialLinearGroup (Fin 6) F, u * u = 1 → u ≠ 1 →
        12 * h ≤ finrank k (LinearMap.range (extendScalars k σ u - 1)) := by
      intro u hu hu1
      rw [hrank_eq u]
      have h12 := twelve_mul_le_rank_kronMinor_sub_one (K := F) (k := k) (ι := Fin f × Fin 6)
        (d := bdeg ε) hd (fun p => frobTwist F k f p.1) (u : Matrix (Fin 6) (Fin 6) F)
        (hgu u hu) (hgu1 u hu1) (by rw [hcount]; exact h2)
      rw [← hcount]
      simpa only [M, bMat] using h12
    have hdich := stage_inner_dichotomy (n := 5) (c := 4) (by norm_num)
      σ hsimp hne δ hδE hD2 hD1 hquad hcompat hoff (Or.inl rfl)
    rcases hdich with hfirst | hsecond
    · obtain ⟨u, -, hu1, hu, hle⟩ := hfirst
      have h6 := hrank6 u hu hu1
      have hE2 : 2 ≤ Nat.card E := by
        have h2 : 1 < Nat.card E := by
          rw [Nat.card_eq_fintype_card]
          exact Fintype.one_lt_card
        omega
      have : 16 < Nat.card E ^ finrank k (LinearMap.range (extendScalars k σ u - 1)) :=
        calc 16 < 2 ^ 6 := by norm_num
          _ ≤ Nat.card E ^ 6 := Nat.pow_le_pow_left hE2 6
          _ ≤ Nat.card E ^ finrank k (LinearMap.range (extendScalars k σ u - 1)) :=
              Nat.pow_le_pow_right (by positivity) h6
      omega
    ·
      obtain ⟨A₀, -, hA₀ne, hA₀2, -, hbound⟩ := hsecond
      obtain ⟨a, ha, ha1⟩ : ∃ a ∈ A₀, a ≠ 1 := by
        by_contra h
        push Not at h
        exact hA₀ne ((Subgroup.eq_bot_iff_forall A₀).mpr h)
      have hcodim : 12 * h ≤ finrank k (k ⊗[E] X) -
          finrank k (fixSub (extendScalars k σ) A₀) :=
        (hrank12 a (hA₀2 a ha) ha1).trans
          (finrank_range_sub_one_le (extendScalars k σ) A₀ ha)
      have hPel : CFSG.IsElementaryAbelian 2 A₀ := by
        refine CFSG.IsElementaryAbelian.of_forall (p := 2) (E := A₀) ?_ ?_
        · intro x hx y hy
          have hxy : x * y * (x * y) = 1 := hA₀2 _ (A₀.mul_mem hx hy)
          have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hA₀2 x hx)
          have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hA₀2 y hy)
          calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
            _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
            _ = y * x := by rw [hx', hy']
        · intro x hx
          rw [pow_two]
          exact hA₀2 x hx
      have hA₀card : Nat.card A₀ ≤ Nat.card F ^ 9 := by
        have hmapel : CFSG.Open.IsElemAbelian 2
            (A₀.map Matrix.SpecialLinearGroup.toGL) := by
          have hA₀el' : CFSG.Open.IsElemAbelian 2 A₀ :=
            CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hPel
          exact hA₀el'.map Matrix.SpecialLinearGroup.toGL
        have h := CFSG.HardMathSupport.GuralnickMalle.card_le_pow_half_sq
          (K := F) (n := 6) (p := 2) Nat.prime_two hmapel
        have h6 : 6 ^ 2 / 4 = 9 := by norm_num
        rw [h6] at h
        have hcard : Nat.card (A₀.map Matrix.SpecialLinearGroup.toGL) = Nat.card A₀ :=
          Subgroup.card_map_of_injective (by
            intro x y hxy
            apply Matrix.SpecialLinearGroup.ext
            intro i j
            exact congrArg (fun z : GL (Fin 6) F => ((z : Matrix (Fin 6) (Fin 6) F) i j)) hxy)
        rwa [hcard] at h
      have hper : f ≤ s * h := by
        have hper' := le_mul_card_active_of_isCoverType_extendScalars (m := 5)
          (f := f) (by rw [← hF, Nat.card_eq_fintype_card]) (s := s)
          (by rw [← hE, Nat.card_eq_fintype_card]) (k := k) σ hsimp ht h0 hχε hsupp
        simpa only [h] using hper'
      have hbound' : Nat.card E ^ (12 * h) ≤ 4 * Nat.card F ^ 9 := by
        have h1 : Nat.card E ^ (12 * h) ≤ Nat.card E ^ (finrank k (k ⊗[E] X) -
            finrank k (fixSub (extendScalars k σ) A₀)) :=
          Nat.pow_le_pow_right Nat.card_pos hcodim
        exact h1.trans (hbound.trans (Nat.mul_le_mul_left 4 hA₀card))
      have hnum : 2 ^ (12 * (s * h)) ≤ 2 ^ (2 + 9 * (s * h)) := by
        have hE' : Nat.card E = 2 ^ s := by rw [Nat.card_eq_fintype_card, hE]
        have h1 : (2 : ℕ) ^ (12 * (s * h)) = Nat.card E ^ (12 * h) := by
          rw [hE', ← pow_mul]
          ring_nf
        rw [h1]
        refine hbound'.trans ?_
        calc 4 * Nat.card F ^ 9 = 2 ^ 2 * 2 ^ (9 * f) := by
              rw [show Nat.card F = 2 ^ f by rw [Nat.card_eq_fintype_card, hF]]
              ring
          _ = 2 ^ (2 + 9 * f) := by rw [← pow_add]
          _ ≤ 2 ^ (2 + 9 * (s * h)) :=
              Nat.pow_le_pow_right (by norm_num) (by omega)
      have hlt : 2 ^ (2 + 9 * (s * h)) < 2 ^ (12 * (s * h)) := by
        apply Nat.pow_lt_pow_right (by norm_num)
        have : 2 ≤ s * h := Nat.mul_le_mul hs1 h2
        omega
      exact absurd hnum (not_le.mpr hlt)
  ·
    have h1 : h = 1 := by omega
    obtain ⟨r₀, hr₀⟩ : ∃ r : Fin f, ε r = {3} := by
      obtain ⟨r, hr⟩ := hsupp
      exact ⟨r, (hε_or r).resolve_left hr⟩
    have hsupp_eq : (Finset.univ.filter fun r => ε r ≠ ∅) = {r₀} := by
      have hcard : (Finset.univ.filter fun r => ε r ≠ ∅).card = 1 := by
        rw [show (Finset.univ.filter fun r => ε r ≠ ∅).card = h from rfl, h1]
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
      · simp [hr₀]
      · intro r hr
        by_contra hne
        have h2' : 2 ≤ (Finset.univ.filter fun r => ε r ≠ ∅).card := by
          have hmem : r₀ ∈ Finset.univ.filter fun r => ε r ≠ ∅ := by simp [hr₀]
          have hmem' : r ∈ Finset.univ.filter fun r => ε r ≠ ∅ := by simpa using hr
          have hsub : ({r, r₀} : Finset (Fin f)) ⊆
              Finset.univ.filter fun r => ε r ≠ ∅ := by
            intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rcases Finset.mem_insert.mp hx with rfl | hx'
            · simpa using hmem'
            · have : x = r₀ := by simpa using hx'
              subst this
              simpa using hmem
          have hc := Finset.card_le_card hsub
          rw [Finset.card_pair hne] at hc
          exact hc
        omega
    have hlr : ∀ r, ε r ≠ ∅ → r = r₀ := by
      intro r hr
      have hmem : r ∈ (Finset.univ.filter fun r => ε r ≠ ∅) := by simpa using hr
      rw [hsupp_eq] at hmem
      simpa using hmem
    have hτ : ∀ (d : D) (A : GL (Fin 6) F), IsUpperGL A → ∀ (τ : F ≃+* F),
        (∀ g x, δ d (σ g x) = σ (borelStd 6 F A τ 0 g) (δ d x)) → τ = RingEquiv.refl F := by
      intro d A hA τ hd
      obtain ⟨T, -, hT⟩ := stage_actor_intertwine (k := k) σ δ hδE hD2 hd
      obtain ⟨e₀, he₀, hτe⟩ :=
        CFSG.ClassicalInvolution.ModelFacts.ChevAut.exists_ringEquiv_eq_frobenius_pow
          Nat.prime_two (by omega : 1 ≤ f)
          (by rw [← hF, Nat.card_eq_fintype_card]) τ
      have hrot : ε ⟨(r₀ + e₀) % f, Nat.mod_lt _ r₀.pos⟩ = ε r₀ :=
        rotate_eq_of_intertwine_stdAut (m := 5) (f := f) hF A hA τ (a := e₀) hτe
          hsimp hT ht ε h0 hχε r₀
      have hmem : ε ⟨(r₀ + e₀) % f, Nat.mod_lt _ r₀.pos⟩ ≠ ∅ := by
        rw [hrot, hr₀]
        simp
      have hfin : (⟨(r₀ + e₀) % f, Nat.mod_lt _ r₀.pos⟩ : Fin f) = r₀ := hlr _ hmem
      have hsum : r₀ + (⟨e₀, he₀⟩ : Fin f) = r₀ := by
        have h1 : r₀ + (⟨e₀, he₀⟩ : Fin f) =
            (⟨(r₀ + e₀) % f, Nat.mod_lt _ r₀.pos⟩ : Fin f) :=
          Fin.ext (by rw [Fin.val_add])
        exact h1.trans hfin
      have he0 : e₀ = 0 := by
        have hx : (⟨e₀, he₀⟩ : Fin f) = 0 := by
          have h' : r₀ + (⟨e₀, he₀⟩ : Fin f) = r₀ + 0 := by simpa using hsum
          simpa using add_left_cancel h'
        exact congrArg Fin.val hx
      apply RingEquiv.ext
      intro x
      rw [hτe x, he0]
      norm_num
    rcases stage_inner_dichotomy (n := 5) (c := 2) (by norm_num)
      σ hsimp hne δ hδE hD2 hD1 hquad hcompat hoff (Or.inr ⟨rfl, Or.inr hτ⟩) with
      hfirst | hsecond
    · obtain ⟨u, -, hu1, hu, hle⟩ := hfirst
      have h6 := hrank6 u hu hu1
      have hE2 : 2 ≤ Nat.card E := by
        have h2 : 1 < Nat.card E := by
          rw [Nat.card_eq_fintype_card]
          exact Fintype.one_lt_card
        omega
      have : 16 < Nat.card E ^ finrank k (LinearMap.range (extendScalars k σ u - 1)) :=
        calc 16 < 2 ^ 6 := by norm_num
          _ ≤ Nat.card E ^ 6 := Nat.pow_le_pow_left hE2 6
          _ ≤ Nat.card E ^ finrank k (LinearMap.range (extendScalars k σ u - 1)) :=
              Nat.pow_le_pow_right (by positivity) h6
      omega
    · obtain ⟨A₀, -, hA₀ne, hA₀2, -, hbound⟩ := hsecond
      have hcodim : finrank k (k ⊗[E] X) - finrank k (fixSub (extendScalars k σ) A₀) =
          finrank k (BModel k ε) - finrank k (fixSub (slModelRep (F := F) (k := k) ε) A₀) := by
        congr 1
        · exact β.finrank_eq
        · have h := finrank_fixSubGen_eq_of_equiv (τ := extendScalars k σ)
            (τ' := slModelRep (F := F) (k := k) ε) β hβ A₀
          change finrank k (fixSubGen (extendScalars k σ) A₀) =
            finrank k (fixSubGen (slModelRep (F := F) (k := k) ε) A₀)
          exact h
      have hper : f ≤ s := by
        have hper' := le_mul_card_active_of_isCoverType_extendScalars (m := 5)
          (f := f) (by rw [← hF, Nat.card_eq_fintype_card]) (s := s)
          (by rw [← hE, Nat.card_eq_fintype_card]) (k := k) σ hsimp ht h0 hχε hsupp
        simpa only [h, h1, mul_one] using hper'
      have hN : 2 ^ f ≤ Nat.card E := by
        rw [Nat.card_eq_fintype_card, hE]
        exact Nat.pow_le_pow_right (by norm_num) hper
      have hcube := SLModel.two_mul_card_lt_pow_codim_slModelRep_cube (F := F) (k := k)
        (f := f) hF hq2 ε r₀ (fun r hr => by
          rcases hε_or r with h' | h'
          · exact h'
          · exfalso
            have : r = r₀ := hlr r (by rw [h']; simp)
            exact hr this) hr₀ hN hA₀ne hA₀2
      rw [hcodim] at hbound
      exact absurd hbound (not_le.mpr hcube)

end CFSG.LieType.SpecialLinear
