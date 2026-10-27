module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusBase
public import CFSG.ClassicalGroups.Orthogonal.OddOrder

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.Open
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.SpCell
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

variable {n : ℕ} {F : Type} [Field F] {S : Finset ℕ}

section Preserve

theorem spLev_topσ (w : Fin (topN n S) ⊕ Fin (topN n S)) : spLev n S (topσ n S w) = S.card :=
  (top_range _).2 ⟨w, rfl⟩

noncomputable def topExt (v : Fin (topN n S) ⊕ Fin (topN n S) → F) : Fin n ⊕ Fin n → F :=
  Function.extend (topσ n S) v 0

theorem topExt_apply (v : Fin (topN n S) ⊕ Fin (topN n S) → F) (w : Fin (topN n S) ⊕ Fin (topN n S)) :
    topExt (S := S) v (topσ n S w) = v w :=
  (topσ_injective (r := n) (S := S)).extend_apply v 0 w

theorem topExt_apply_of_not_mem (v : Fin (topN n S) ⊕ Fin (topN n S) → F) {u : Fin n ⊕ Fin n}
    (hu : u ∉ Set.range (topσ n S)) : topExt (S := S) v u = 0 := by
  simp [topExt, Function.extend_apply' _ _ _ hu]

theorem quad_topExt (v : Fin (topN n S) ⊕ Fin (topN n S) → F) :
    StatedQuadPlus n F (topExt (S := S) v) = StatedQuadPlus (topN n S) F v := by
  unfold StatedQuadPlus
  symm
  refine Fintype.sum_of_injective (topEmb n S) topEmb_injective _ _ ?_ ?_
  · intro a ha
    have : (Sum.inl a : Fin n ⊕ Fin n) ∉ Set.range (topσ n S) := by
      rintro ⟨w, hw⟩
      rcases w with j | j
      · exact ha ⟨j, by simpa [topσ] using hw⟩
      · simp [topσ] at hw
    rw [topExt_apply_of_not_mem v this, zero_mul]
  · intro j
    exact (by
      have h1 := topExt_apply (S := S) v (Sum.inl j)
      have h2 := topExt_apply (S := S) v (Sum.inr j)
      simp only [topσ, Sum.map_inl, Sum.map_inr] at h1 h2
      rw [h1, h2])

variable (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n)
include hS

theorem topHomGL_mulVec_topσ (g : ↥(Jfl n F S)) (v : Fin (topN n S) ⊕ Fin (topN n S) → F)
    (u : Fin (topN n S) ⊕ Fin (topN n S)) :
    (spMat (g : StatedSp n F) *ᵥ topExt (S := S) v) (topσ n S u) =
      (((topHomGL hS g : GL (Fin (topN n S) ⊕ Fin (topN n S)) F) :
        Matrix (Fin (topN n S) ⊕ Fin (topN n S)) (Fin (topN n S) ⊕ Fin (topN n S)) F) *ᵥ v) u := by
  rw [coe_topHomGL]
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  refine (Fintype.sum_of_injective (topσ n S) topσ_injective _ _ ?_ ?_).symm
  · intro c hc
    rw [topExt_apply_of_not_mem v hc, mul_zero]
  · intro c
    rw [topExt_apply]

theorem topHomGL_mulVec_eq_zero (g : ↥(Jfl n F S)) (v : Fin (topN n S) ⊕ Fin (topN n S) → F)
    {u : Fin n ⊕ Fin n} (hu : S.card < spLev n S u) :
    (spMat (g : StatedSp n F) *ᵥ topExt (S := S) v) u = 0 := by
  have hbt := spMat_blockTriangular hS g.2
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : c ∈ Set.range (topσ n S)
  · obtain ⟨w, rfl⟩ := hc
    rw [hbt (by rw [spLev_topσ]; exact hu), zero_mul]
  · rw [topExt_apply_of_not_mem v hc, mul_zero]

theorem topHom_preserves [CharP F 2] (g : ↥(JO n F S)) (v : Fin (topN n S) ⊕ Fin (topN n S) → F) :
    StatedQuadPlus (topN n S) F
        (((topHomGL hS (jToJfl S g) : GL (Fin (topN n S) ⊕ Fin (topN n S)) F) :
          Matrix (Fin (topN n S) ⊕ Fin (topN n S)) (Fin (topN n S) ⊕ Fin (topN n S)) F) *ᵥ v) =
      StatedQuadPlus (topN n S) F v := by
  set M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    spMat ((jToJfl S g : ↥(Jfl n F S)) : StatedSp n F) with hM
  have hpres : StatedQuadPlus n F (M *ᵥ topExt (S := S) v) = StatedQuadPlus (topN n S) F v := by
    rw [← quad_topExt (S := S) v]
    exact om_preserves g.1.2 (topExt (S := S) v)
  rw [← hpres]
  unfold StatedQuadPlus
  refine Fintype.sum_of_injective (topEmb n S) topEmb_injective _ _ ?_ ?_
  · intro a ha
    have hlt : cnt S a < S.card := by
      have := cnt_le_card S a
      refine lt_of_le_of_ne this fun h => ha (exists_topEmb_eq (S := S) h)
    have hgt : S.card < spLev n S (Sum.inr a) := by
      have hne : spLev n S (Sum.inr a) ≠ S.card := fun h => by
        obtain ⟨w, hw⟩ := (top_range _).1 h
        rcases w with j | j
        · simp [topσ] at hw
        · exact ha ⟨j, by simpa [topσ] using hw⟩
      by_contra hle
      have hlt' : spLev n S (Sum.inr a) < S.card := lt_of_le_of_ne (not_lt.1 hle) hne
      obtain ⟨b, hb⟩ := (step_range (S := S) hlt' (Sum.inr a)).1 rfl
      simp at hb
    have hz := topHomGL_mulVec_eq_zero hS (jToJfl S g) v (u := Sum.inr a) hgt
    rw [hz, mul_zero]
  · intro j
    have h1 := topHomGL_mulVec_topσ hS (jToJfl S g) v (Sum.inl j)
    have h2 := topHomGL_mulVec_topσ hS (jToJfl S g) v (Sum.inr j)
    simp only [topσ, Sum.map_inl, Sum.map_inr] at h1 h2
    rw [h1, h2]

end Preserve

section TopO

variable [CharP F 2]

@[expose] noncomputable def topO (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n) :
    ↥(JO n F S) →* ↥(orthGroup (StatedQuadPlus (topN n S) F)) :=
  ((topHomGL hS).comp (jToJfl S)).codRestrict _
    (fun g => Subgroup.subset_closure (fun v => topHom_preserves hS g v))

end TopO

section Odd

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

theorem odd_mem_statedOmega [CharP F 2] {t : ℕ} (ht : 3 ≤ t) {y : GL (Fin t ⊕ Fin t) F}
    (hy : ∀ v, StatedQuadPlus t F ((y : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) F) *ᵥ v) =
      StatedQuadPlus t F v) {m : ℕ} (hm : Odd m) (hym : y ^ m = 1) :
    y ∈ StatedOmega (StatedQuadPlus t F) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hg : toLinEquiv (Fin t ⊕ Fin t) F y ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus t F) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
      rw [toLinEquiv_apply, coe_quadPlus]
      exact hy v
  have hgm : toLinEquiv (Fin t ⊕ Fin t) F y ^ m = 1 := by rw [← map_pow, hym, map_one]
  have := mem_elementaryGroup_quadPlus_of_odd_pow h2 ht hg hm hgm
  rw [statedOmega_quadPlus_eq_map ht]
  exact ⟨_, this, by simp⟩

end Odd

section Levi

theorem inl_not_mem_range_topσ {a : Fin n} (ha : cnt S a ≠ S.card) :
    (Sum.inl a : Fin n ⊕ Fin n) ∉ Set.range (topσ n S) := by
  rintro ⟨w, hw⟩
  rcases w with j | j
  · have : topEmb n S j = a := by simpa [topσ] using hw
    subst this
    exact ha (cnt_topEmb j)
  · simp [topσ] at hw

theorem inr_not_mem_range_topσ {a : Fin n} (ha : cnt S a ≠ S.card) :
    (Sum.inr a : Fin n ⊕ Fin n) ∉ Set.range (topσ n S) := by
  rintro ⟨w, hw⟩
  rcases w with j | j
  · simp [topσ] at hw
  · have : topEmb n S j = a := by simpa [topσ] using hw
    subst this
    exact ha (cnt_topEmb j)

theorem quad_split (v : Fin n ⊕ Fin n → F) :
    StatedQuadPlus n F v = StatedQuadPlus (topN n S) F (fun w => v (topσ n S w)) +
      ∑ a : Fin n, if cnt S a = S.card then 0 else v (Sum.inl a) * v (Sum.inr a) := by
  have h1 : ∑ a : Fin n, v (Sum.inl a) * v (Sum.inr a) =
      ∑ a : Fin n, ((if cnt S a = S.card then v (Sum.inl a) * v (Sum.inr a) else 0) +
        if cnt S a = S.card then 0 else v (Sum.inl a) * v (Sum.inr a)) :=
    Finset.sum_congr rfl fun a _ => by split_ifs <;> simp
  unfold StatedQuadPlus
  rw [h1, Finset.sum_add_distrib]
  congr 1
  symm
  refine Fintype.sum_of_injective (topEmb n S) topEmb_injective _ _ ?_ ?_
  · intro a ha
    have : cnt S a ≠ S.card := fun h => ha (exists_topEmb_eq (S := S) h)
    simp [this]
  · intro j
    simp [cnt_topEmb j, topσ]

theorem topLeviGL_apply_σ (B : GL (Fin (topN n S) ⊕ Fin (topN n S)) F)
    (u c : Fin (topN n S) ⊕ Fin (topN n S)) :
    ((topLeviGL S B : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      (topσ n S u) (topσ n S c) = (B : Matrix _ _ F) u c := by
  rw [coe_topLeviGL, extendId_apply_pos (P := fun u : Fin n ⊕ Fin n => spLev n S u = S.card) _
    (spLev_topσ u) (spLev_topσ c)]
  have h : ∀ w, (topLeviEquiv n S).symm ⟨topσ n S w, spLev_topσ w⟩ = w := fun w =>
    ((topLeviEquiv n S).symm_apply_eq).2 rfl
  simp only [Matrix.submatrix_apply, h]

theorem topLeviGL_mulVec_topσ (B : GL (Fin (topN n S) ⊕ Fin (topN n S)) F)
    (v : Fin n ⊕ Fin n → F) (u : Fin (topN n S) ⊕ Fin (topN n S)) :
    (((topLeviGL S B : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v)
        (topσ n S u) =
      ((B : Matrix (Fin (topN n S) ⊕ Fin (topN n S)) (Fin (topN n S) ⊕ Fin (topN n S)) F) *ᵥ
        (fun w => v (topσ n S w))) u := by
  simp only [Matrix.mulVec, dotProduct]
  refine (Fintype.sum_of_injective (topσ n S) topσ_injective
    (fun c => (B : Matrix (Fin (topN n S) ⊕ Fin (topN n S)) (Fin (topN n S) ⊕ Fin (topN n S)) F) u c *
      v (topσ n S c))
    (fun c => ((topLeviGL S B : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (topσ n S u) c * v c) ?_ ?_).symm
  · intro c hc
    have hP : ¬ spLev n S c = S.card := fun h => hc ((top_range c).1 h)
    have hne : topσ n S u ≠ c := fun h => hc ⟨u, h⟩
    rw [coe_topLeviGL, extendId_apply_neg (P := fun u : Fin n ⊕ Fin n => spLev n S u = S.card) _
      (fun h => hP h.2), Matrix.one_apply_ne hne, zero_mul]
  · intro c
    simp only [topLeviGL_apply_σ]

theorem topLeviGL_mulVec_of_not_mem (B : GL (Fin (topN n S) ⊕ Fin (topN n S)) F)
    (v : Fin n ⊕ Fin n → F) {u : Fin n ⊕ Fin n} (hu : u ∉ Set.range (topσ n S)) :
    (((topLeviGL S B : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v) u =
      v u := by
  have hP : ¬ spLev n S u = S.card := fun h => hu ((top_range u).1 h)
  have hrow : ∀ c, ((topLeviGL S B : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) u c = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) u c := by
    intro c
    rw [coe_topLeviGL]
    exact extendId_apply_neg (P := fun u : Fin n ⊕ Fin n => spLev n S u = S.card) _ (fun h => hP h.1)
  have : (((topLeviGL S B : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v) u =
      ((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v) u := by
    simp only [Matrix.mulVec, dotProduct, hrow]
  rw [this, Matrix.one_mulVec]

theorem topLeviGL_preserves {B : GL (Fin (topN n S) ⊕ Fin (topN n S)) F}
    (hB : ∀ v, StatedQuadPlus (topN n S) F
      ((B : Matrix (Fin (topN n S) ⊕ Fin (topN n S)) (Fin (topN n S) ⊕ Fin (topN n S)) F) *ᵥ v) =
        StatedQuadPlus (topN n S) F v) (v : Fin n ⊕ Fin n → F) :
    StatedQuadPlus n F
        (((topLeviGL S B : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v) =
      StatedQuadPlus n F v := by
  rw [quad_split (S := S), quad_split (S := S) v]
  congr 1
  · have : (fun w => (((topLeviGL S B : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v) (topσ n S w)) =
        (B : Matrix (Fin (topN n S) ⊕ Fin (topN n S)) (Fin (topN n S) ⊕ Fin (topN n S)) F) *ᵥ
          (fun w => v (topσ n S w)) := funext (topLeviGL_mulVec_topσ B v)
    rw [this, hB]
  · refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : cnt S a = S.card
    · simp [ha]
    · simp only [ha, ite_false]
      rw [topLeviGL_mulVec_of_not_mem B v (inl_not_mem_range_topσ ha),
        topLeviGL_mulVec_of_not_mem B v (inr_not_mem_range_topσ ha)]

theorem topLeviGL_mem_orthGroup {B : GL (Fin (topN n S) ⊕ Fin (topN n S)) F}
    (hB : B ∈ orthGroup (StatedQuadPlus (topN n S) F)) :
    topLeviGL S B ∈ orthGroup (StatedQuadPlus n F) := by
  have : orthGroup (StatedQuadPlus (topN n S) F) ≤
      (orthGroup (StatedQuadPlus n F)).comap (topLeviGL (r := n) (K := F) S) := by
    rw [orthGroup, Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (fun v => topLeviGL_preserves hA v)
  exact this hB

theorem topLeviGL_mem_om {B : GL (Fin (topN n S) ⊕ Fin (topN n S)) F}
    (hB : B ∈ Om (topN n S) F) : topLeviGL S B ∈ Om n F := by
  have : Om (topN n S) F ≤ (Om n F).comap (topLeviGL (r := n) (K := F) S) := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [Subgroup.mem_comap, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
      ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (topLeviGL_mem_orthGroup ha)
      (topLeviGL_mem_orthGroup hb)
  exact this hB

@[expose] noncomputable def topLeviO (S : Finset ℕ) :
    ↥(Om (topN n S) F) →* ↥(Om n F) :=
  ((topLeviGL (r := n) (K := F) S).comp (Om (topN n S) F).subtype).codRestrict _
    (fun B => topLeviGL_mem_om B.2)

variable [CharP F 2]

theorem omSp_topLeviO (B : ↥(Om (topN n S) F)) :
    omSp (topLeviO S B) = topLevi S ⟨(B : GL _ F), om_le_sp B.2⟩ := rfl

theorem topLeviO_mem (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n) (B : ↥(Om (topN n S) F)) :
    topLeviO S B ∈ JO n F S := by
  rw [mem_JO, omSp_topLeviO]
  exact topLevi_mem hS _

omit [CharP F 2] in
theorem topLeviO_injective : Function.Injective (topLeviO (n := n) (F := F) S) := fun _ _ h =>
  Subtype.ext (topLeviGL_injective S (congrArg Subtype.val h))

theorem topHomGL_topLeviO (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n) (B : ↥(Om (topN n S) F))
    (h : topLeviO S B ∈ JO n F S) :
    topHomGL hS (jToJfl S ⟨topLeviO S B, h⟩) = (B : GL (Fin (topN n S) ⊕ Fin (topN n S)) F) := by
  refine Units.ext (Matrix.ext fun u c => ?_)
  rw [coe_topHomGL]
  show ((topLeviGL S (B : GL _ F) : GL (Fin n ⊕ Fin n) F) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (topσ n S u) (topσ n S c) = _
  exact topLeviGL_apply_σ _ u c

theorem exists_topLeviO (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n) :
    ∃ φ : ↥(StatedOmega (StatedQuadPlus (topN n S) F)) →* ↥(Om n F), Function.Injective φ ∧
      (∀ B, φ B ∈ JO n F S) ∧
      ∀ B (h : φ B ∈ JO n F S),
        topHomGL hS (jToJfl S ⟨φ B, h⟩) = (B : GL (Fin (topN n S) ⊕ Fin (topN n S)) F) :=
  ⟨topLeviO S, topLeviO_injective, topLeviO_mem hS, topHomGL_topLeviO hS⟩

end Levi

section Cyclic

theorem isCyclic_of_pGroup_le {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {H : Subgroup G} (hH : ¬ p ^ 2 ∣ Nat.card H) {Q : Subgroup G} (hQH : Q ≤ H)
    (hQ : IsPGroup p Q) : IsCyclic Q := by
  have hQ' : IsPGroup p (Q.subgroupOf H) := by
    intro g
    obtain ⟨m, hm⟩ := hQ (⟨(g.1 : G), g.2⟩ : Q)
    exact ⟨m, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hm))⟩
  have hc := isCyclic_of_isPGroup_of_not_sq_dvd hp hH hQ'
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQH).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hQH).surjective

variable [Finite F] [CharP F 2]

theorem isCyclic_map_top_of_A1 {p : ℕ} (hp57 : p = 5 ∨ p = 7) (ht : 3 ≤ topN n S)
    (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n)
    (hA1 : ∀ X : Subgroup ↥(Om n F), X ≤ JO n F S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X)
    (E' : Subgroup ↥(JO n F S)) (hE' : ∀ e ∈ E', e ^ p = 1) :
    IsCyclic ↥(E'.map ((topHomGL hS).comp (jToJfl S))) := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hodd : Odd p := by rcases hp57 with rfl | rfl <;> decide
  obtain ⟨φ, hinj, hmem, -⟩ := exists_topLeviO (F := F) hS
  have hq : CFSG.Open.IsQuasisimple ↥(Om (topN n S) F) :=
    open_of_isQuasisimple (CFSG.LieType.Universal.Spin.isQuasisimple_statedOmega_quadPlus ht)
  have hcard : ¬ p ^ 2 ∣ Nat.card ↥(Om (topN n S) F) := by
    intro hd
    have hX : CFSG.Open.IsQuasisimple ↥φ.range :=
      CFSG.ComponentClassification.Components.quasisimple_of_equiv
        (MonoidHom.ofInjective hinj).symm hq
    exact hA1 φ.range (by rintro _ ⟨B, rfl⟩; exact hmem B) hX
      (by rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]; exact hd)
  refine isCyclic_of_pGroup_le hp hcard (fun y hy => ?_) ?_
  · obtain ⟨e, he, rfl⟩ := hy
    refine odd_mem_statedOmega ht (topHom_preserves hS e) hodd ?_
    show topHomGL hS (jToJfl S e) ^ p = 1
    rw [← map_pow, ← map_pow, hE' e he, map_one, map_one]
  · have : Fact p.Prime := ⟨hp⟩
    intro y
    obtain ⟨e, he, hey⟩ := y.2
    refine ⟨1, Subtype.ext ?_⟩
    show (y : GL (Fin (topN n S) ⊕ Fin (topN n S)) F) ^ (p ^ 1) = 1
    rw [pow_one, ← hey]
    show topHomGL hS (jToJfl S e) ^ p = 1
    rw [← map_pow, ← map_pow, hE' e he, map_one, map_one]

end Cyclic

section TopN

theorem topN_ne_one (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n) (hS1 : n - 1 ∈ S → n ∈ S)
    (hne : S.Nonempty) : topN n S ≠ 1 := by
  have key : ∀ a : ℕ, cnt S a = S.card ↔ ∀ i ∈ S, i ≤ a := by
    intro a
    constructor
    · intro h i hi
      by_contra hia
      have h1 := cnt_lt_of_cut S hi (not_le.1 hia) le_rfl
      have := cnt_le_card S i
      omega
    · intro h
      refine le_antisymm (cnt_le_card S a) (not_lt.1 fun hlt => ?_)
      obtain ⟨i, hi, hai⟩ := exists_cut_of_cnt_lt_card S hlt
      exact absurd (h i hi) (not_le.2 hai)
  intro h1
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.1 h1
  have hmem : ∀ b : Fin n, cnt S b = S.card ↔ b = a.1 := fun b =>
    ⟨fun hb => congrArg Subtype.val (ha ⟨b, hb⟩), fun hb => hb ▸ a.2⟩
  obtain ⟨m, hm, hmax⟩ : ∃ m ∈ S, ∀ i ∈ S, i ≤ m := ⟨S.max' hne, S.max'_mem hne, fun i hi =>
    S.le_max' i hi⟩
  have hm1 := hS m hm
  by_cases hnS : n ∈ S
  · have := (key a.1).1 a.2 n hnS
    have := a.1.2
    omega
  · have hn1 : n - 1 ∉ S := fun h => hnS (hS1 h)
    have hmn : m ≤ n - 2 := by
      have : m ≠ n - 1 := fun h => hn1 (h ▸ hm)
      have : m ≠ n := fun h => hnS (h ▸ hm)
      omega
    have hall : ∀ b : ℕ, m ≤ b → ∀ hb : b < n, cnt S b = S.card := fun b hb hbn =>
      (key b).2 fun i hi => (hmax i hi).trans hb
    have e1 := (hmem ⟨n - 1, by omega⟩).1 (hall (n - 1) (by omega) (by omega))
    have e2 := (hmem ⟨n - 2, by omega⟩).1 (hall (n - 2) hmn (by omega))
    have := congrArg Fin.val (e1.trans e2.symm)
    simp at this
    omega

end TopN

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
