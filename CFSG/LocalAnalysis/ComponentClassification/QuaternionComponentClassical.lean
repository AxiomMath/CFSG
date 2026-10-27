module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.Adapters.LinearFieldTransport

public section

namespace CFSG.ComponentClassification.QuaternionComponent

open Matrix CFSG.Assembly.LowTwoRank

namespace FieldTransport

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K L : Type} [Field K] [Field L]

@[expose] def glFieldEquiv (ι : Type) [Fintype ι] [DecidableEq ι] (σ : K ≃+* L) :
    GL ι K ≃* GL ι L :=
  Units.mapEquiv (σ.mapMatrix (m := ι)).toMulEquiv

@[simp] theorem coe_glFieldEquiv (σ : K ≃+* L) (A : GL ι K) :
    ((glFieldEquiv ι σ A : GL ι L) : Matrix ι ι L) = (A : Matrix ι ι K).map σ :=
  rfl

theorem map_eq_map_iff {κ : Type} (σ : K ≃+* L) {M N : Matrix κ κ K} :
    M.map σ = N.map σ ↔ M = N :=
  (Matrix.map_injective σ.injective).eq_iff

theorem map_closure_of_iff {M N : Type*} [Group M] [Group N] (e : M ≃* N) {s : Set M}
    {s' : Set N} (h : ∀ x, x ∈ s ↔ e x ∈ s') :
    (Subgroup.closure s).map (e : M →* N) = Subgroup.closure s' := by
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).1 hx
  · intro hy
    exact ⟨e.symm y, (h _).2 (by rwa [MulEquiv.apply_symm_apply]), e.apply_symm_apply y⟩

theorem nonempty_statedProj_mulEquiv_of_map_eq (σ : K ≃+* L) {H : Subgroup (GL ι K)}
    {H' : Subgroup (GL ι L)} (h : H.map (glFieldEquiv ι σ : GL ι K →* GL ι L) = H') :
    Nonempty (StatedProj H ≃* StatedProj H') := by
  let P : ProjGenLinGroup ι K ≃* ProjGenLinGroup ι L :=
    QuotientGroup.congr _ _ (glFieldEquiv ι σ) (Subgroup.map_center_eq (glFieldEquiv ι σ))
  have hP : (H.map (ProjGenLinGroup.mk : GL ι K →* ProjGenLinGroup ι K)).map
      (P : ProjGenLinGroup ι K →* ProjGenLinGroup ι L) = H'.map ProjGenLinGroup.mk := by
    rw [← h, Subgroup.map_map, Subgroup.map_map]
    rfl
  exact ⟨(ClassicalModelStatedBridge.mapMkEquivStatedProj H).symm.trans
    ((P.subgroupMap _).trans ((MulEquiv.subgroupCongr hP).trans
      (ClassicalModelStatedBridge.mapMkEquivStatedProj H')))⟩

theorem map_glFieldEquiv_statedSL (σ : K ≃+* L) (n : ℕ) :
    (StatedSL n K).map (glFieldEquiv (Fin n) σ : GL (Fin n) K →* GL (Fin n) L) = StatedSL n L := by
  unfold StatedSL
  refine map_closure_of_iff (glFieldEquiv _ σ) fun A => ?_
  have hdet : ((A : Matrix (Fin n) (Fin n) K).map σ).det = σ (A : Matrix (Fin n) (Fin n) K).det :=
    (σ.map_det _).symm
  change (A : Matrix (Fin n) (Fin n) K).det = 1 ↔ ((A : Matrix (Fin n) (Fin n) K).map σ).det = 1
  rw [hdet, map_eq_one_iff σ σ.injective]

theorem map_glFieldEquiv_statedSU (σ : K ≃+* L) (n q : ℕ) :
    (StatedSU n q K).map (glFieldEquiv (Fin n) σ : GL (Fin n) K →* GL (Fin n) L) =
      StatedSU n q L := by
  unfold StatedSU
  refine map_closure_of_iff (glFieldEquiv _ σ) fun A => ?_
  set M : Matrix (Fin n) (Fin n) K := (A : Matrix (Fin n) (Fin n) K)
  have hdet : (M.map σ).det = σ M.det := (σ.map_det _).symm
  have hform : ((M.map σ).map (· ^ q))ᵀ * M.map σ = ((M.map (· ^ q))ᵀ * M).map σ := by
    ext i j
    simp [Matrix.mul_apply, map_sum, map_mul, map_pow]
  change M.det = 1 ∧ (M.map (· ^ q))ᵀ * M = 1 ↔
    (M.map σ).det = 1 ∧ ((M.map σ).map (· ^ q))ᵀ * M.map σ = 1
  rw [hdet, map_eq_one_iff σ σ.injective, hform,
    ← Matrix.map_one σ (map_zero σ) (map_one σ), map_eq_map_iff]

theorem map_glFieldEquiv_statedSp (σ : K ≃+* L) (n : ℕ) :
    (StatedSp n K).map (glFieldEquiv (Fin n ⊕ Fin n) σ :
      GL (Fin n ⊕ Fin n) K →* GL (Fin n ⊕ Fin n) L) =
      StatedSp n L := by
  unfold StatedSp
  refine map_closure_of_iff (glFieldEquiv _ σ) fun A => ?_
  set M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
  have hJ : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map σ =
      Matrix.fromBlocks 0 1 (-1) 0 := by
    rw [Matrix.fromBlocks_map, Matrix.map_zero σ (map_zero σ), Matrix.map_neg σ (map_neg σ),
      Matrix.map_one σ (map_zero σ) (map_one σ)]
  change Mᵀ * Matrix.fromBlocks 0 1 (-1) 0 * M = Matrix.fromBlocks 0 1 (-1) 0 ↔
    (M.map σ)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * M.map σ = Matrix.fromBlocks 0 1 (-1) 0
  rw [← hJ, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, map_eq_map_iff]

theorem mem_isometries_iff (σ : K ≃+* L) {Q : (ι → K) → K} {Q' : (ι → L) → L}
    (hQ : ∀ v, Q' (σ ∘ v) = σ (Q v)) (A : GL ι K) :
    A ∈ {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} ↔
      glFieldEquiv ι σ A ∈ {A : GL ι L | ∀ w, Q' ((A : Matrix ι ι L) *ᵥ w) = Q' w} := by
  have hmv : ∀ v, ((A : Matrix ι ι K).map σ) *ᵥ (σ ∘ v) = σ ∘ ((A : Matrix ι ι K) *ᵥ v) :=
    fun v => funext fun i => (RingHom.map_mulVec σ.toRingHom _ v i).symm
  change (∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v) ↔
    ∀ w, Q' (((A : Matrix ι ι K).map σ) *ᵥ w) = Q' w
  constructor
  · intro h w
    have hw : w = σ ∘ (σ.symm ∘ w) := funext fun i => (σ.apply_symm_apply (w i)).symm
    rw [hw, hmv, hQ, hQ, h]
  · intro h v
    apply σ.injective
    rw [← hQ, ← hQ, ← hmv, h]

theorem map_glFieldEquiv_statedOmega (σ : K ≃+* L) {Q : (ι → K) → K} {Q' : (ι → L) → L}
    (hQ : ∀ v, Q' (σ ∘ v) = σ (Q v)) :
    (StatedOmega Q).map (glFieldEquiv ι σ : GL ι K →* GL ι L) = StatedOmega Q' := by
  rw [StatedOmega, Subgroup.map_commutator,
    map_closure_of_iff (glFieldEquiv ι σ) (mem_isometries_iff σ hQ)]
  rfl

theorem statedQuadOdd_comp (σ : K ≃+* L) (n : ℕ) (v : Fin n ⊕ Fin n ⊕ Unit → K) :
    StatedQuadOdd n L (σ ∘ v) = σ (StatedQuadOdd n K v) := by
  simp [StatedQuadOdd, map_sum, map_add, map_mul, map_pow]

theorem statedQuadPlus_comp (σ : K ≃+* L) (n : ℕ) (v : Fin n ⊕ Fin n → K) :
    StatedQuadPlus n L (σ ∘ v) = σ (StatedQuadPlus n K v) := by
  simp [StatedQuadPlus, map_sum, map_mul]

theorem statedQuadMinus_comp (σ : K ≃+* L) (n : ℕ) (b c : K)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus n L (σ b) (σ c) (σ ∘ v) = σ (StatedQuadMinus n K b c v) := by
  simp [StatedQuadMinus, map_sum, map_add, map_mul, map_pow]

end FieldTransport

open FieldTransport

theorem classicalModel_of_statedClassicalModel {X : Type} [Group X]
    (t : Assembly.ComponentType.ClassicalTag) (n p f : ℕ) [Fact p.Prime]
    (h : StatedClassicalModel X (ClassicalModelStatedBridge.ClassicalTag.toStated t) n p f) :
    Assembly.ComponentType.ClassicalModel X t n p f := by
  cases t with
  | PSL =>
    obtain ⟨⟨hp, hf, hn, h22, h23⟩, K, _, _, hK, ⟨e⟩⟩ := h
    obtain ⟨e'⟩ := nonempty_statedProj_mulEquiv_of_map_eq
      (ClassicalModels.finiteFieldEquivGaloisField K p f hf hK) (map_glFieldEquiv_statedSL _ n)
    refine ⟨⟨hp, hf, hn, ?_⟩,
      ⟨e.trans (e'.trans (ClassicalModelStatedBridge.pslModelEquiv n p f).symm)⟩⟩
    rintro ⟨rfl, h2 | h3⟩
    · exact h22 (by rw [h2])
    · exact h23 (by rw [h3])
  | PSU =>
    obtain ⟨⟨hp, hf, hn, h32⟩, K, _, _, hK, ⟨e⟩⟩ := h
    obtain ⟨e'⟩ := nonempty_statedProj_mulEquiv_of_map_eq
      (ClassicalModels.finiteFieldEquivGaloisField K p (2 * f) (by omega)
        (by rw [hK, ← pow_mul, mul_comm]))
      (map_glFieldEquiv_statedSU _ n (p ^ f))
    exact ⟨⟨hp, hf, hn, fun ⟨h3, h2⟩ => h32 (by rw [h3, h2])⟩,
      ⟨e.trans (e'.trans (ClassicalModelStatedBridge.psuModelEquiv n p f).symm)⟩⟩
  | PSp =>
    obtain ⟨⟨hp, hf, hn, h22⟩, K, _, _, hK, ⟨e⟩⟩ := h
    obtain ⟨e'⟩ := nonempty_statedProj_mulEquiv_of_map_eq
      (ClassicalModels.finiteFieldEquivGaloisField K p f hf hK) (map_glFieldEquiv_statedSp _ n)
    exact ⟨⟨hp, hf, hn, fun ⟨h2, h2'⟩ => h22 (by rw [h2, h2'])⟩,
      ⟨e.trans (e'.trans (ClassicalModelStatedBridge.pspModelEquiv n p f).symm)⟩⟩
  | POmegaOdd =>
    obtain ⟨⟨hp, hf, hn, hp2⟩, K, _, _, hK, ⟨e⟩⟩ := h
    let σ := ClassicalModels.finiteFieldEquivGaloisField K p f hf hK
    obtain ⟨e'⟩ := nonempty_statedProj_mulEquiv_of_map_eq σ
      (map_glFieldEquiv_statedOmega σ (statedQuadOdd_comp σ n))
    exact ⟨⟨hp, hf, hn, hp2⟩,
      ⟨e.trans (e'.trans (ClassicalModelStatedBridge.omegaModelOddEquiv n _).symm)⟩⟩
  | POmegaPlus =>
    obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := h
    let σ := ClassicalModels.finiteFieldEquivGaloisField K p f hf hK
    obtain ⟨e'⟩ := nonempty_statedProj_mulEquiv_of_map_eq σ
      (map_glFieldEquiv_statedOmega σ (statedQuadPlus_comp σ n))
    exact ⟨⟨hp, hf, hn⟩,
      ⟨e.trans (e'.trans (ClassicalModelStatedBridge.omegaModelPlusEquiv n _).symm)⟩⟩
  | POmegaMinus =>
    obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := h
    let σ := ClassicalModels.finiteFieldEquivGaloisField K p f hf hK
    obtain ⟨e'⟩ := nonempty_statedProj_mulEquiv_of_map_eq σ
      (map_glFieldEquiv_statedOmega σ (statedQuadMinus_comp σ n b c))
    refine ⟨⟨hp, hf, hn⟩, σ b, σ c, fun s hs => hbc (σ.symm s) (σ.injective ?_),
      ⟨e.trans (e'.trans (ClassicalModelStatedBridge.omegaModelMinusEquiv n (σ b) (σ c)).symm)⟩⟩
    rw [map_add, map_add, map_mul, map_pow, σ.apply_symm_apply, map_zero]
    exact hs

theorem oddLieType_of_statedClassicalModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : StatedClassicalModel X t n p f) :
    Assembly.ComponentType.OddLieType X := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have key : ∀ t' : Assembly.ComponentType.ClassicalTag,
      ClassicalModelStatedBridge.ClassicalTag.toStated t' = t →
        Assembly.ComponentType.OddLieType X := by
    rintro t' rfl
    exact Or.inl ⟨t', n, p, f, hfact, hp2, classicalModel_of_statedClassicalModel t' n p f h⟩
  cases t
  case PSL => exact key .PSL rfl
  case PSU => exact key .PSU rfl
  case PSp => exact key .PSp rfl
  case POmegaOdd => exact key .POmegaOdd rfl
  case POmegaPlus => exact key .POmegaPlus rfl
  case POmegaMinus => exact key .POmegaMinus rfl
  all_goals exact (h.2 : False).elim

theorem oddLieType_of_blueprint_of_exceptional {X : Type} [Group X]
    (hExc : ∀ (t : StatedLieTag) (p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible t 0 p f →
      (t ∈ Blueprint.chevalleyExceptionalTags ∧ Blueprint.ChevalleyExceptionalModel X t p f) ∨
        (t ∈ Blueprint.reeTitsTags ∧ Blueprint.ReeTitsModel X t p f) →
      Assembly.ComponentType.OddLieType X)
    (h : Blueprint.OddLieType X) : Assembly.ComponentType.OddLieType X := by
  obtain ⟨t, n, p, f, hp, hp2, hadm, hmodel⟩ := h
  rcases hmodel with ⟨-, hc⟩ | ⟨rfl, ht, he⟩ | ⟨rfl, ht, he⟩ | ⟨-, -, hs⟩
  · exact oddLieType_of_statedClassicalModel hp hp2 hc
  · exact hExc t p f hp hp2 hadm (Or.inl ⟨ht, he⟩)
  · exact hExc t p f hp hp2 hadm (Or.inr ⟨ht, he⟩)
  · exact absurd hs.1 hp2

end CFSG.ComponentClassification.QuaternionComponent
