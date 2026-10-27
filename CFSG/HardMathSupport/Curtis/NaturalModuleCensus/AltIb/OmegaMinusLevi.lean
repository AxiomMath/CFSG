module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusLevels

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus

open Matrix CFSG.Assembly.LowTwoRank CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.SpCell
  (cnt cnt_le_card cnt_lt_of_cut StepCoord topN topEmb cnt_topEmb exists_topEmb_eq
    topEmb_injective reindexGL coe_reindexGL stepLeviGL stepLeviGL_injective stepLeviGL_ne_one
    open_of_isQuasisimple)

variable {r : ℕ} {F : Type} [Field F] {b c : F}

@[expose] def leviOMat (A A' : Matrix (Fin r) (Fin r) F) : Matrix (Idx r) (Idx r) F :=
  Matrix.fromBlocks A 0 0 (Matrix.fromBlocks A'ᵀ 0 0 1)

theorem leviOMat_mul (A B A' B' : Matrix (Fin r) (Fin r) F) :
    leviOMat A A' * leviOMat B B' = leviOMat (A * B) (B' * A') := by
  simp [leviOMat, Matrix.fromBlocks_multiply, Matrix.transpose_mul]

theorem leviOMat_one : leviOMat (1 : Matrix (Fin r) (Fin r) F) 1 = 1 := by
  simp [leviOMat]

@[expose] def leviO : GL (Fin r) F →* GL (Idx r) F :=
  MonoidHom.mk' (fun A => ⟨leviOMat (A : Matrix _ _ F) ((A⁻¹ : GL (Fin r) F) : Matrix _ _ F),
      leviOMat ((A⁻¹ : GL (Fin r) F) : Matrix _ _ F) (A : Matrix _ _ F), by
        rw [leviOMat_mul]; simp [leviOMat_one],
      by rw [leviOMat_mul]; simp [leviOMat_one]⟩)
    (fun A B => by
      apply Units.ext
      simp only [Units.val_mul, leviOMat_mul, _root_.mul_inv_rev])

theorem coe_leviO (A : GL (Fin r) F) :
    ((leviO A : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) =
      leviOMat (A : Matrix _ _ F) ((A⁻¹ : GL (Fin r) F) : Matrix _ _ F) := rfl

theorem leviO_injective : Function.Injective (leviO (r := r) (F := F)) := by
  intro A B h
  apply Units.ext
  have := congrArg (fun M : GL (Idx r) F => (M : Matrix (Idx r) (Idx r) F)) h
  simp only [coe_leviO, leviOMat, Matrix.fromBlocks_inj] at this
  exact this.1

theorem Qm_leviO (A : GL (Fin r) F) (v : Idx r → F) :
    Qm r F b c ((leviO A : Matrix (Idx r) (Idx r) F) *ᵥ v) = Qm r F b c v := by
  have hdot : ((A : Matrix (Fin r) (Fin r) F) *ᵥ (v ∘ Sum.inl)) ⬝ᵥ
      (((A⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)ᵀ *ᵥ (v ∘ Sum.inr ∘ Sum.inl)) =
      (v ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr ∘ Sum.inl) := by
    rw [Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, dotProduct_comm]
  simp only [Qm, StatedQuadMinus]
  have hM : (leviOMat (A : Matrix (Fin r) (Fin r) F) ((A⁻¹ : GL (Fin r) F) : Matrix _ _ F)) *ᵥ v =
      Sum.elim ((A : Matrix (Fin r) (Fin r) F) *ᵥ (v ∘ Sum.inl))
        (Sum.elim ((((A⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F))ᵀ *ᵥ (v ∘ Sum.inr ∘ Sum.inl))
          (v ∘ Sum.inr ∘ Sum.inr)) := by
    simp only [leviOMat, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
      Matrix.one_mulVec]
    rfl
  rw [coe_leviO, hM]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hd : (∑ i, ((A : Matrix (Fin r) (Fin r) F) *ᵥ (v ∘ Sum.inl)) i *
      ((((A⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)ᵀ *ᵥ (v ∘ Sum.inr ∘ Sum.inl)) i)) =
      ∑ i, v (Sum.inl i) * v (Sum.inr (Sum.inl i)) := hdot
  exact congrArg₂ (fun x y => x + (v ∘ Sum.inr ∘ Sum.inr) 0 ^ 2 + b * (v ∘ Sum.inr ∘ Sum.inr) 0 *
    (v ∘ Sum.inr ∘ Sum.inr) 1 + c * (v ∘ Sum.inr ∘ Sum.inr) 1 ^ 2) hd hd



theorem leviO_mem_orthGroup (A : GL (Fin r) F) :
    leviO A ∈ orthGroup (Qm r F b c) :=
  Subgroup.subset_closure (fun v => Qm_leviO A v)

theorem Ωm_eq : Ωm r F b c = ⁅orthGroup (Qm r F b c), orthGroup (Qm r F b c)⁆ := rfl

theorem mem_Ωm_of_perfect {G : Type*} [Group G] (hG : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = (⊤ : Subgroup G))
    (φ : G →* GL (Idx r) F) (hφ : ∀ g, φ g ∈ orthGroup (Qm r F b c)) (g : G) :
    φ g ∈ Ωm r F b c := by
  have h1 : g ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := by rw [hG]; exact Subgroup.mem_top g
  have h2 : φ g ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆.map φ := Subgroup.mem_map_of_mem φ h1
  rw [Subgroup.map_commutator] at h2
  rw [Ωm_eq]
  have hle : (⊤ : Subgroup G).map φ ≤ orthGroup (Qm r F b c) := by
    rintro _ ⟨g, -, rfl⟩
    exact hφ g
  exact Subgroup.commutator_mono hle hle h2

theorem SL_perfect_or_subsingleton [Finite F] [CharP F 2] (k : ℕ)
    (hk : ¬ (k = 2 ∧ Nat.card F = 2)) :
    ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin k) F)),
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin k) F))⁆ = ⊤ ∨
      Subsingleton (Matrix.SpecialLinearGroup (Fin k) F) := by
  rcases Nat.lt_or_ge k 3 with h3 | h3
  · interval_cases k
    · exact Or.inr ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    · refine Or.inr ⟨fun a b => Subtype.ext ?_⟩
      ext i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst hi; subst hj
      have ha := a.2
      have hb := b.2
      rw [Matrix.det_unique] at ha hb
      exact ha.trans hb.symm
    · left
      have hK4 : 4 ≤ Nat.card F := by
        have hpos : 0 < Nat.card F := Nat.card_pos
        have := Fintype.ofFinite F
        obtain ⟨n, -, hn⟩ := FiniteField.card F 2
        rw [← Nat.card_eq_fintype_card] at hn
        have h1 : 1 ≤ (n : ℕ) := n.pos
        have h4 : 2 ^ 1 ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h1
        rcases Nat.lt_or_ge 1 (n : ℕ) with h | h
        · have : 2 ^ 2 ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h
          omega
        · have : (n : ℕ) = 1 := by omega
          exact absurd ⟨rfl, by rw [hn, this]; norm_num⟩ hk
      exact Group.isPerfect_def.1 (LieType.HighestRoot.isQuasisimple_SL2_of_four_le hK4).1
  · left
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact Group.isPerfect_def.1 (LieType.Universal.SpecialLinear.isQuasisimple m F (by omega)).1

@[expose] def Pd (r d : ℕ) (u : Idx r) : Prop := ∃ a : Fin r, (a : ℕ) < d ∧ u = Sum.inl a

theorem mem_eSub' {d : ℕ} {v : Idx r → F} :
    v ∈ eSub r F d ↔ ∀ u, ¬ Pd r d u → v u = 0 := by
  rw [mem_eSub]
  refine forall_congr' fun u => ?_
  simp only [Pd, not_exists, not_and]

theorem mulVec_mem_eSub {d : ℕ} {M : Matrix (Idx r) (Idx r) F}
    (hM : ∀ u w, M u w ≠ (1 : Matrix (Idx r) (Idx r) F) u w → (Pd r d u ↔ Pd r d w))
    {v : Idx r → F} (hv : v ∈ eSub r F d) : M *ᵥ v ∈ eSub r F d := by
  rw [mem_eSub'] at hv ⊢
  intro u hu
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun w _ => ?_
  by_cases hw : Pd r d w
  · have hne : u ≠ w := fun h => hu (h ▸ hw)
    have : M u w = (1 : Matrix (Idx r) (Idx r) F) u w := by
      by_contra h
      exact hu ((hM u w h).2 hw)
    rw [this, Matrix.one_apply_ne hne, zero_mul]
  · rw [hv w hw, mul_zero]

theorem mem_JΩ_of_supp {S : Finset ℕ} {g : GL (Idx r) F} (hg : g ∈ Ωm r F b c)
    (h1 : ∀ d ∈ S, ∀ u w, (g : Matrix (Idx r) (Idx r) F) u w ≠ (1 : Matrix (Idx r) (Idx r) F) u w →
      (Pd r d u ↔ Pd r d w))
    (h2 : ∀ d ∈ S, ∀ u w, ((g⁻¹ : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) u w ≠
      (1 : Matrix (Idx r) (Idx r) F) u w → (Pd r d u ↔ Pd r d w)) :
    g ∈ JΩ r F b c S := by
  refine ⟨hg, fun d hd v => ⟨fun hv => mulVec_mem_eSub (h1 d hd) hv, fun hv => ?_⟩⟩
  have := mulVec_mem_eSub (h2 d hd) hv
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec] at this

@[expose] def LQ (Q : Fin r → Prop) : Idx r → Prop
  | Sum.inl a => Q a
  | Sum.inr (Sum.inl a) => Q a
  | Sum.inr (Sum.inr _) => False

theorem leviO_supp {Q : Fin r → Prop} (A : GL (Fin r) F)
    (h1 : ∀ a b, (A : Matrix (Fin r) (Fin r) F) a b ≠ (1 : Matrix (Fin r) (Fin r) F) a b → Q a ∧ Q b)
    (h2 : ∀ a b, ((A⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a b ≠
      (1 : Matrix (Fin r) (Fin r) F) a b → Q a ∧ Q b)
    (u w : Idx r)
    (h : (leviO A : Matrix (Idx r) (Idx r) F) u w ≠ (1 : Matrix (Idx r) (Idx r) F) u w) :
    (∃ a b, Q a ∧ Q b ∧ u = Sum.inl a ∧ w = Sum.inl b) ∨
      (∃ a b, Q a ∧ Q b ∧ u = Sum.inr (Sum.inl a) ∧ w = Sum.inr (Sum.inl b)) := by
  rw [coe_leviO] at h
  rcases u with a | a | k <;> rcases w with b | b | l
  · left
    simp only [leviOMat, Matrix.fromBlocks_apply₁₁] at h
    obtain ⟨ha, hb⟩ := h1 a b (fun h' => h (by rw [h']; simp [Matrix.one_apply]))
    exact ⟨a, b, ha, hb, rfl, rfl⟩
  · simp [leviOMat] at h
  · simp [leviOMat] at h
  · simp [leviOMat] at h
  · right
    simp only [leviOMat, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁,
      Matrix.transpose_apply] at h
    obtain ⟨hb, ha⟩ := h2 b a (fun h' => h (by rw [h']; simp [Matrix.one_apply, eq_comm]))
    exact ⟨a, b, ha, hb, rfl, rfl⟩
  · simp [leviOMat] at h
  · simp [leviOMat] at h
  · simp [leviOMat] at h
  · exfalso
    apply h
    simp [leviOMat, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]

variable {S : Finset ℕ}

@[expose] def stepLeviΩ (S : Finset ℕ) (ℓ : ℕ) :
    Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord r S ℓ))) F →* GL (Idx r) F :=
  leviO.comp (stepLeviGL (r := r) (K := F) S ℓ)

theorem stepLeviΩ_injective (S : Finset ℕ) (ℓ : ℕ) :
    Function.Injective (stepLeviΩ (r := r) (F := F) S ℓ) :=
  leviO_injective.comp (stepLeviGL_injective S ℓ)

theorem stepLeviΩ_mem_orthGroup (S : Finset ℕ) (ℓ : ℕ)
    (A : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord r S ℓ))) F) :
    stepLeviΩ S ℓ A ∈ orthGroup (Qm r F b c) :=
  leviO_mem_orthGroup _

theorem stepLeviΩ_supp (S : Finset ℕ) (ℓ : ℕ)
    (A : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord r S ℓ))) F) (u w : Idx r)
    (h : (stepLeviΩ S ℓ A : Matrix (Idx r) (Idx r) F) u w ≠ (1 : Matrix (Idx r) (Idx r) F) u w) :
    (∃ a b : Fin r, cnt S a = ℓ ∧ cnt S b = ℓ ∧ u = Sum.inl a ∧ w = Sum.inl b) ∨
      (∃ a b : Fin r, cnt S a = ℓ ∧ cnt S b = ℓ ∧ u = Sum.inr (Sum.inl a) ∧
        w = Sum.inr (Sum.inl b)) := by
  refine leviO_supp (Q := fun a => cnt S a = ℓ) _ ?_ ?_ u w h
  · intro a b hab
    exact stepLeviGL_ne_one S ℓ A hab
  · intro a b hab
    rw [← map_inv] at hab
    exact stepLeviGL_ne_one S ℓ A⁻¹ hab

theorem Pd_iff_of_cnt_eq {d : ℕ} (hd : d ∈ S) {a b : Fin r} (h : cnt S a = cnt S b) :
    (a : ℕ) < d ↔ (b : ℕ) < d := by
  constructor
  · intro ha
    by_contra hb
    push Not at hb
    have := cnt_lt_of_cut S hd ha hb
    omega
  · intro hb
    by_contra ha
    push Not at ha
    have := cnt_lt_of_cut S hd hb ha
    omega

theorem stepLeviΩ_mem (_hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) [Finite F] [CharP F 2] {ℓ : ℕ}
    (hk : ¬ (Fintype.card (StepCoord r S ℓ) = 2 ∧ Nat.card F = 2))
    (A : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord r S ℓ))) F) :
    stepLeviΩ S ℓ A ∈ JΩ r F b c S := by
  have hsupp : ∀ A' : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord r S ℓ))) F,
      ∀ d ∈ S, ∀ u w, (stepLeviΩ S ℓ A' : Matrix (Idx r) (Idx r) F) u w ≠
        (1 : Matrix (Idx r) (Idx r) F) u w → (Pd r d u ↔ Pd r d w) := by
    intro A' d hd u w h
    rcases stepLeviΩ_supp S ℓ A' u w h with ⟨a, b, ha, hb, rfl, rfl⟩ | ⟨a, b, ha, hb, rfl, rfl⟩
    · have := Pd_iff_of_cnt_eq hd (ha.trans hb.symm)
      simp only [Pd, Sum.inl.injEq]
      constructor <;> rintro ⟨x, hx, rfl⟩
      · exact ⟨b, this.1 hx, rfl⟩
      · exact ⟨a, this.2 hx, rfl⟩
    · simp [Pd]
  refine mem_JΩ_of_supp ?_ (hsupp A) ?_
  · rcases SL_perfect_or_subsingleton (F := F) _ hk with hp | hs
    · exact mem_Ωm_of_perfect hp (stepLeviΩ S ℓ) (fun A => stepLeviΩ_mem_orthGroup S ℓ A) A
    · have : A = 1 := Subsingleton.elim _ _
      rw [this, map_one]
      exact one_mem _
  · have : (stepLeviΩ S ℓ A : GL (Idx r) F)⁻¹ = stepLeviΩ S ℓ A⁻¹ := (map_inv _ _).symm
    rw [this]
    exact hsupp A⁻¹

variable (r) in
@[expose] def topEquiv (S : Finset ℕ) :
    Idx (topN r S) ≃ {u : Idx r // omLev r S u = S.card} :=
  Equiv.ofBijective (fun w => ⟨topσ r S w, (top_range _).2 ⟨w, rfl⟩⟩)
    ⟨fun a b h => topσ_injective (congrArg Subtype.val h), fun u => by
      obtain ⟨w, hw⟩ := (top_range u.1).1 u.2
      exact ⟨w, Subtype.ext hw⟩⟩

@[expose] def topLeviGL (S : Finset ℕ) : GL (Idx (topN r S)) F →* GL (Idx r) F :=
  (extendGL (fun u : Idx r => omLev r S u = S.card)).comp
    (reindexGL (topEquiv r S)).toMonoidHom

theorem topLeviGL_injective (S : Finset ℕ) : Function.Injective (topLeviGL (r := r) (F := F) S) := by
  intro A B h
  exact (reindexGL (K := F) (topEquiv r S)).injective
    (extendGL_injective (K := F) (fun u : Idx r => omLev r S u = S.card) h)

theorem coe_topLeviGL (S : Finset ℕ) (B : GL (Idx (topN r S)) F) :
    ((topLeviGL S B : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) =
      extendId (fun u : Idx r => omLev r S u = S.card)
        ((B : Matrix _ _ F).submatrix (topEquiv r S).symm (topEquiv r S).symm) := rfl

theorem topLeviGL_support (S : Finset ℕ) (B : GL (Idx (topN r S)) F) {u w : Idx r}
    (h : ((topLeviGL S B : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) u w ≠
      (1 : Matrix (Idx r) (Idx r) F) u w) : omLev r S u = S.card ∧ omLev r S w = S.card := by
  rw [coe_topLeviGL] at h
  exact extendId_ne_one _ h

theorem topLeviGL_mulVec_of_not (S : Finset ℕ) (B : GL (Idx (topN r S)) F) (v : Idx r → F)
    {u : Idx r} (hu : omLev r S u ≠ S.card) :
    (((topLeviGL S B : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) *ᵥ v) u = v u := by
  have : ∀ w, ((topLeviGL S B : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) u w =
      (1 : Matrix (Idx r) (Idx r) F) u w := fun w => by
    rw [coe_topLeviGL]
    exact extendId_apply_neg _ (fun h => hu h.1)
  have h2 : (((topLeviGL S B : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) *ᵥ v) u =
      ((1 : Matrix (Idx r) (Idx r) F) *ᵥ v) u := by
    simp only [Matrix.mulVec, dotProduct, this]
  rw [h2, Matrix.one_mulVec]

theorem topLeviGL_mulVec_top (S : Finset ℕ) (B : GL (Idx (topN r S)) F) (v : Idx r → F)
    (j : Idx (topN r S)) :
    (((topLeviGL S B : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) *ᵥ v) (topσ r S j) =
      ((B : Matrix (Idx (topN r S)) (Idx (topN r S)) F) *ᵥ (v ∘ topσ r S)) j := by
  set P : Idx r → Prop := fun u => omLev r S u = S.card with hP
  set M := ((topLeviGL S B : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) with hM
  have hj : P (topσ r S j) := (top_range _).2 ⟨j, rfl⟩
  rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct,
    ← Fintype.sum_subtype_add_sum_subtype P]
  have h0 : ∑ w : {w // ¬ P w}, M (topσ r S j) w * v w = 0 :=
    Finset.sum_eq_zero fun w _ => by
      rw [hM, coe_topLeviGL, extendId_apply_neg _ (fun h => w.2 h.2),
        Matrix.one_apply_ne (fun h => w.2 (by rw [← h]; exact hj)), zero_mul]
  rw [h0, add_zero]
  rw [← (topEquiv r S).sum_comp]
  refine Finset.sum_congr rfl fun j' _ => ?_
  have h1 : M (topσ r S j) ((topEquiv r S j' : {u // P u}) : Idx r) =
      (B : Matrix _ _ F) j j' := by
    rw [hM, coe_topLeviGL, extendId_apply_pos _ hj (topEquiv r S j').2]
    simp only [Matrix.submatrix_apply]
    have e1 : (topEquiv r S).symm ⟨topσ r S j, hj⟩ = j := by
      rw [Equiv.symm_apply_eq]; rfl
    rw [e1, Equiv.symm_apply_apply]
  rw [h1]
  rfl

theorem Qm_split (S : Finset ℕ) (v : Idx r → F) :
    Qm r F b c v =
      (∑ a ∈ Finset.univ.filter (fun a : Fin r => cnt S a ≠ S.card),
        v (Sum.inl a) * v (Sum.inr (Sum.inl a))) + Qm (topN r S) F b c (v ∘ topσ r S) := by
  have himg : Finset.univ.image (topEmb r S) =
      Finset.univ.filter (fun a : Fin r => ¬ cnt S a ≠ S.card) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, not_not]
    constructor
    · rintro ⟨j, rfl⟩; exact cnt_topEmb j
    · intro h; exact exists_topEmb_eq h
  have key : ∑ a : Fin r, v (Sum.inl a) * v (Sum.inr (Sum.inl a)) =
      (∑ a ∈ Finset.univ.filter (fun a : Fin r => cnt S a ≠ S.card),
        v (Sum.inl a) * v (Sum.inr (Sum.inl a))) +
      ∑ j : Fin (topN r S), (v ∘ topσ r S) (Sum.inl j) * (v ∘ topσ r S) (Sum.inr (Sum.inl j)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : Fin r => cnt S a ≠ S.card),
      ← himg, Finset.sum_image (fun x _ y _ h => topEmb_injective h)]
    rfl
  show (∑ a : Fin r, v (Sum.inl a) * v (Sum.inr (Sum.inl a))) + v (Sum.inr (Sum.inr 0)) ^ 2 +
      b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) + c * v (Sum.inr (Sum.inr 1)) ^ 2 = _ +
    ((∑ j : Fin (topN r S), (v ∘ topσ r S) (Sum.inl j) * (v ∘ topσ r S) (Sum.inr (Sum.inl j))) +
      (v ∘ topσ r S) (Sum.inr (Sum.inr 0)) ^ 2 +
      b * (v ∘ topσ r S) (Sum.inr (Sum.inr 0)) * (v ∘ topσ r S) (Sum.inr (Sum.inr 1)) +
      c * (v ∘ topσ r S) (Sum.inr (Sum.inr 1)) ^ 2)
  rw [key]
  show _ = _ + (_ + v (Sum.inr (Sum.inr 0)) ^ 2 + b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
    c * v (Sum.inr (Sum.inr 1)) ^ 2)
  ring

theorem Qm_topLeviGL (S : Finset ℕ) {B : GL (Idx (topN r S)) F}
    (hB : ∀ v, Qm (topN r S) F b c ((B : Matrix _ _ F) *ᵥ v) = Qm (topN r S) F b c v)
    (v : Idx r → F) :
    Qm r F b c (((topLeviGL S B : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) *ᵥ v) =
      Qm r F b c v := by
  set w := ((topLeviGL S B : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) *ᵥ v with hw
  rw [Qm_split (S := S) w, Qm_split (S := S) v]
  congr 1
  · refine Finset.sum_congr rfl fun a ha => ?_
    have hca : cnt S a ≠ S.card := (Finset.mem_filter.1 ha).2
    have h1 : omLev r S (Sum.inl a) ≠ S.card := hca
    have h2 : omLev r S (Sum.inr (Sum.inl a)) ≠ S.card := by
      have := cnt_le_card S a
      show 2 * S.card - cnt S a ≠ S.card
      omega
    rw [hw, topLeviGL_mulVec_of_not S B v h1, topLeviGL_mulVec_of_not S B v h2]
  · have : (w ∘ topσ r S) = (B : Matrix _ _ F) *ᵥ (v ∘ topσ r S) := by
      funext j
      exact topLeviGL_mulVec_top S B v j
    rw [this, hB]

theorem topLeviGL_mem_orthGroup (S : Finset ℕ) {B : GL (Idx (topN r S)) F}
    (hB : B ∈ orthGroup (Qm (topN r S) F b c)) : topLeviGL S B ∈ orthGroup (Qm r F b c) :=
  Subgroup.subset_closure (Qm_topLeviGL S (fun v => orthGroup_preserves _ hB v))

theorem topLeviGL_mem_Ωm (S : Finset ℕ) {B : GL (Idx (topN r S)) F}
    (hB : B ∈ Ωm (topN r S) F b c) : topLeviGL S B ∈ Ωm r F b c := by
  have h2 : topLeviGL S B ∈ (Ωm (topN r S) F b c).map (topLeviGL (r := r) (F := F) S) :=
    Subgroup.mem_map_of_mem _ hB
  rw [Ωm_eq, Subgroup.map_commutator] at h2
  have hle : (orthGroup (Qm (topN r S) F b c)).map (topLeviGL (r := r) (F := F) S) ≤
      orthGroup (Qm r F b c) := by
    rintro _ ⟨B', hB', rfl⟩
    exact topLeviGL_mem_orthGroup S hB'
  rw [Ωm_eq]
  exact Subgroup.commutator_mono hle hle h2

@[expose] def topLevi (S : Finset ℕ) : ↥(Ωm (topN r S) F b c) →* GL (Idx r) F :=
  (topLeviGL (r := r) (F := F) S).comp (Ωm (topN r S) F b c).subtype

theorem topLevi_injective (S : Finset ℕ) :
    Function.Injective (topLevi (r := r) (F := F) (b := b) (c := c) S) := by
  intro A B h
  exact Subtype.ext (topLeviGL_injective S h)

theorem topLevi_mem_Ωm (S : Finset ℕ) (B : ↥(Ωm (topN r S) F b c)) :
    topLevi S B ∈ Ωm r F b c :=
  topLeviGL_mem_Ωm S B.2

theorem Pd_omLev {d : ℕ} (hd : d ∈ S) {u : Idx r} (hu : Pd r d u) : omLev r S u ≠ S.card := by
  obtain ⟨a, ha, rfl⟩ := hu
  show cnt S a ≠ S.card
  have h1 := cnt_lt_of_cut S hd ha (le_refl d)
  have h2 := cnt_le_card S d
  omega

theorem topLevi_mem (_hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) (B : ↥(Ωm (topN r S) F b c)) :
    topLevi S B ∈ JΩ r F b c S := by
  have hsupp : ∀ B' : ↥(Ωm (topN r S) F b c), ∀ d ∈ S, ∀ u w,
      (topLevi S B' : Matrix (Idx r) (Idx r) F) u w ≠ (1 : Matrix (Idx r) (Idx r) F) u w →
        (Pd r d u ↔ Pd r d w) := by
    intro B' d hd u w h
    obtain ⟨hu, hw⟩ := topLeviGL_support S _ h
    exact ⟨fun h' => absurd hu (Pd_omLev hd h'), fun h' => absurd hw (Pd_omLev hd h')⟩
  refine mem_JΩ_of_supp (topLevi_mem_Ωm S B) (hsupp B) ?_
  have : (topLevi S B : GL (Idx r) F)⁻¹ = topLevi S B⁻¹ := (map_inv _ _).symm
  rw [this]
  exact hsupp B⁻¹

theorem commute_of_supp_GL {D E : Idx r → Prop} {g h : GL (Idx r) F}
    (hg : ∀ u w, (g : Matrix (Idx r) (Idx r) F) u w ≠ (1 : Matrix (Idx r) (Idx r) F) u w →
      D u ∧ D w)
    (hh : ∀ u w, (h : Matrix (Idx r) (Idx r) F) u w ≠ (1 : Matrix (Idx r) (Idx r) F) u w →
      E u ∧ E w)
    (hDE : ∀ u, ¬ (D u ∧ E u)) : g * h = h * g :=
  Units.ext (by rw [Units.val_mul, Units.val_mul]; exact commute_of_supp hg hh hDE)

@[expose] def StepSupp (S : Finset ℕ) (ℓ : ℕ) (u : Idx r) : Prop :=
  ∃ a : Fin r, cnt S a = ℓ ∧ (u = Sum.inl a ∨ u = Sum.inr (Sum.inl a))

theorem stepLeviΩ_stepSupp (S : Finset ℕ) (ℓ : ℕ)
    (A : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord r S ℓ))) F) (u w : Idx r)
    (h : (stepLeviΩ S ℓ A : Matrix (Idx r) (Idx r) F) u w ≠ (1 : Matrix (Idx r) (Idx r) F) u w) :
    StepSupp S ℓ u ∧ StepSupp S ℓ w := by
  rcases stepLeviΩ_supp S ℓ A u w h with ⟨a, b, ha, hb, rfl, rfl⟩ | ⟨a, b, ha, hb, rfl, rfl⟩
  · exact ⟨⟨a, ha, Or.inl rfl⟩, ⟨b, hb, Or.inl rfl⟩⟩
  · exact ⟨⟨a, ha, Or.inr rfl⟩, ⟨b, hb, Or.inr rfl⟩⟩

theorem stepLeviΩ_commute_stepLeviΩ {ℓ ℓ' : ℕ} (hne : ℓ ≠ ℓ')
    (A : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord r S ℓ))) F)
    (B : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord r S ℓ'))) F) :
    stepLeviΩ S ℓ A * stepLeviΩ S ℓ' B = stepLeviΩ S ℓ' B * stepLeviΩ S ℓ A :=
  commute_of_supp_GL (D := StepSupp S ℓ) (E := StepSupp S ℓ')
    (stepLeviΩ_stepSupp S ℓ A) (stepLeviΩ_stepSupp S ℓ' B) (fun u => by
      rintro ⟨⟨a, ha, hu⟩, ⟨b, hb, hu'⟩⟩
      have hab : a = b := by
        rcases hu with h1 | h1 <;> rcases hu' with h2 | h2 <;>
          first
          | exact Sum.inl_injective (h1.symm.trans h2)
          | exact Sum.inl_injective (Sum.inr_injective (h1.symm.trans h2))
          | (exfalso; have := h1.symm.trans h2; simp at this)
      subst hab
      exact hne (ha.symm.trans hb))

theorem stepLeviΩ_commute_topLevi {ℓ : ℕ} (hℓ : ℓ < S.card)
    (A : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord r S ℓ))) F)
    (B : ↥(Ωm (topN r S) F b c)) :
    stepLeviΩ S ℓ A * topLevi S B = topLevi S B * stepLeviΩ S ℓ A :=
  commute_of_supp_GL (D := StepSupp S ℓ) (E := fun u => omLev r S u = S.card)
    (stepLeviΩ_stepSupp S ℓ A) (fun u w h => topLeviGL_support S _ h) (fun u => by
      rintro ⟨⟨a, ha, rfl | rfl⟩, hu⟩
      · have : cnt S a = S.card := hu
        omega
      · have h1 : 2 * S.card - cnt S a = S.card := hu
        omega)

section Torus

@[expose] def diagGL {ι : Type} [Fintype ι] [DecidableEq ι] :
    (ι → Fˣ) →* GL ι F :=
  MonoidHom.mk' (fun d => ⟨Matrix.diagonal (fun u => (d u : F)),
      Matrix.diagonal (fun u => ((d u)⁻¹ : Fˣ) : ι → F), by
        rw [Matrix.diagonal_mul_diagonal]; simp,
      by rw [Matrix.diagonal_mul_diagonal]; simp⟩)
    (fun d e => by
      apply Units.ext
      simp [Matrix.diagonal_mul_diagonal])

theorem coe_diagGL {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → Fˣ) :
    ((diagGL d : GL ι F) : Matrix ι ι F) = Matrix.diagonal (fun u => (d u : F)) := rfl

theorem diagGL_injective {ι : Type} [Fintype ι] [DecidableEq ι] :
    Function.Injective (diagGL (ι := ι) (F := F)) := by
  intro d e h
  funext u
  have := congrFun (congrFun (congrArg (fun M : GL ι F => (M : Matrix ι ι F)) h) u) u
  simp only [coe_diagGL, Matrix.diagonal_apply_eq] at this
  exact Units.ext this

@[expose] def torusVec (m : ℕ) : (Fin m → Fˣ) →* (Idx m → Fˣ) :=
  MonoidHom.mk' (fun t => Sum.elim t (Sum.elim (fun i => (t i)⁻¹) (fun _ => 1)))
    (fun s t => by
      funext u
      rcases u with i | i | k <;> simp [mul_comm])

theorem torusVec_inl (m : ℕ) (t : Fin m → Fˣ) (i : Fin m) : torusVec m t (Sum.inl i) = t i := rfl

theorem torusVec_inr_inl (m : ℕ) (t : Fin m → Fˣ) (i : Fin m) :
    torusVec m t (Sum.inr (Sum.inl i)) = (t i)⁻¹ := rfl

theorem torusVec_inr_inr (m : ℕ) (t : Fin m → Fˣ) (k : Fin 2) :
    torusVec m t (Sum.inr (Sum.inr k)) = 1 := rfl

@[expose] def swapIdx (m : ℕ) : Idx m → Idx m
  | Sum.inl i => Sum.inr (Sum.inl i)
  | Sum.inr (Sum.inl i) => Sum.inl i
  | Sum.inr (Sum.inr k) => Sum.inr (Sum.inr k)

theorem swapIdx_swapIdx (m : ℕ) (u : Idx m) : swapIdx m (swapIdx m u) = u := by
  rcases u with i | i | k <;> rfl

@[expose] def swapMat (m : ℕ) : Matrix (Idx m) (Idx m) F :=
  (1 : Matrix (Idx m) (Idx m) F).submatrix (swapIdx m) id

theorem swapMat_apply (m : ℕ) (u v : Idx m) :
    (swapMat m : Matrix (Idx m) (Idx m) F) u v = if swapIdx m u = v then 1 else 0 := by
  simp [swapMat, Matrix.one_apply]

theorem swapMat_mul_self (m : ℕ) : (swapMat m : Matrix (Idx m) (Idx m) F) * swapMat m = 1 := by
  ext u v
  rw [Matrix.mul_apply]
  simp only [swapMat_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (swapIdx m u)]
  · simp [swapIdx_swapIdx]
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

@[expose] def swapGL (m : ℕ) : GL (Idx m) F :=
  ⟨swapMat m, swapMat m, swapMat_mul_self m, swapMat_mul_self m⟩

theorem swapGL_mulVec (m : ℕ) (v : Idx m → F) (u : Idx m) :
    (((swapGL m : GL (Idx m) F) : Matrix (Idx m) (Idx m) F) *ᵥ v) u = v (swapIdx m u) := by
  show ((swapMat m : Matrix (Idx m) (Idx m) F) *ᵥ v) u = _
  simp [Matrix.mulVec, dotProduct, swapMat_apply]

theorem Qm_swapGL (m : ℕ) (v : Idx m → F) :
    Qm m F b c (((swapGL m : GL (Idx m) F) : Matrix (Idx m) (Idx m) F) *ᵥ v) = Qm m F b c v := by
  simp only [Qm, StatedQuadMinus, swapGL_mulVec]
  have key : ∑ i : Fin m, v (swapIdx m (Sum.inl i)) * v (swapIdx m (Sum.inr (Sum.inl i))) =
      ∑ i : Fin m, v (Sum.inl i) * v (Sum.inr (Sum.inl i)) :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  exact congrArg (fun x => x + v (Sum.inr (Sum.inr 0)) ^ 2 +
    b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) + c * v (Sum.inr (Sum.inr 1)) ^ 2) key

theorem swapGL_mem_orthGroup (m : ℕ) : (swapGL m : GL (Idx m) F) ∈ orthGroup (Qm m F b c) :=
  Subgroup.subset_closure (fun v => Qm_swapGL m v)

theorem diagGL_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → Fˣ) (v : ι → F) (u : ι) :
    (((diagGL d : GL ι F) : Matrix ι ι F) *ᵥ v) u = (d u : F) * v u := by
  rw [coe_diagGL, Matrix.mulVec_diagonal]

theorem Qm_diagGL_torusVec (m : ℕ) (t : Fin m → Fˣ) (v : Idx m → F) :
    Qm m F b c (((diagGL (torusVec m t) : GL (Idx m) F) : Matrix (Idx m) (Idx m) F) *ᵥ v) =
      Qm m F b c v := by
  simp only [Qm, StatedQuadMinus, diagGL_mulVec, torusVec_inr_inr, Units.val_one, one_mul]
  have key : ∑ i : Fin m, ((torusVec m t (Sum.inl i) : Fˣ) : F) * v (Sum.inl i) *
      (((torusVec m t (Sum.inr (Sum.inl i)) : Fˣ) : F) * v (Sum.inr (Sum.inl i))) =
      ∑ i : Fin m, v (Sum.inl i) * v (Sum.inr (Sum.inl i)) :=
    Finset.sum_congr rfl fun i _ => by
      rw [torusVec_inl, torusVec_inr_inl]
      calc _ = ((t i : Fˣ) * (t i)⁻¹ : Fˣ) * (v (Sum.inl i) * v (Sum.inr (Sum.inl i))) := by
            push_cast; ring
        _ = _ := by rw [mul_inv_cancel]; simp
  exact congrArg (fun x => x + v (Sum.inr (Sum.inr 0)) ^ 2 +
    b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) + c * v (Sum.inr (Sum.inr 1)) ^ 2) key

@[expose] def torusHom (m : ℕ) : (Fin m → Fˣ) →* GL (Idx m) F := (diagGL (F := F)).comp (torusVec m)

theorem torusHom_injective (m : ℕ) : Function.Injective (torusHom (F := F) m) := by
  intro s t h
  have := congrFun (diagGL_injective h) 
  funext i
  exact this (Sum.inl i)

theorem swapGL_mul_torus (m : ℕ) (s : Fin m → Fˣ) :
    (swapGL m : GL (Idx m) F) * torusHom m s⁻¹ = torusHom m s * swapGL m := by
  apply Units.ext
  show (swapMat m : Matrix (Idx m) (Idx m) F) * Matrix.diagonal _ = Matrix.diagonal _ * swapMat m
  ext u v
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, swapMat_apply]
  by_cases h : swapIdx m u = v
  · subst h
    rcases u with i | i | k <;> simp [swapIdx, torusVec]
  · simp [h]

theorem torusHom_mem_Ωm [Finite F] [CharP F 2] (m : ℕ) (t : Fin m → Fˣ) :
    torusHom m t ∈ Ωm m F b c := by
  have hsq : ∀ x : Fˣ, ∃ y : Fˣ, y * y = x := fun x => by
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨y, hy⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (x : F)
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy
    exact ⟨Units.mk0 y hy0, Units.ext (by simpa using hy.symm)⟩
  choose f hf using hsq
  set s : Fin m → Fˣ := fun i => f (t i) with hs
  have hts : t = s * s := funext fun i => (hf (t i)).symm
  have hmem : torusHom m s ∈ orthGroup (Qm m F b c) :=
    Subgroup.subset_closure (fun v => Qm_diagGL_torusVec m s v)
  have hcomm : ⁅torusHom (F := F) m s, (swapGL m : GL (Idx m) F)⁆ = torusHom m t := by
    rw [commutatorElement_def, hts, map_mul]
    have h1 : (swapGL m : GL (Idx m) F)⁻¹ = swapGL m := by
      rw [inv_eq_iff_mul_eq_one]
      exact Units.ext (swapMat_mul_self m)
    rw [h1]
    have h2 := swapGL_mul_torus (F := F) m s
    rw [map_inv] at h2
    calc torusHom m s * swapGL m * (torusHom m s)⁻¹ * swapGL m
        = torusHom m s * (swapGL m * (torusHom m s)⁻¹) * swapGL m := by group
      _ = torusHom m s * (torusHom m s * swapGL m) * swapGL m := by rw [h2]
      _ = torusHom m s * torusHom m s * (swapGL m * swapGL m) := by group
      _ = torusHom m s * torusHom m s := by
          rw [← Units.val_inj]
          simp [swapGL, swapMat_mul_self]
  rw [Ωm_eq, ← hcomm]
  exact Subgroup.commutator_mem_commutator hmem (swapGL_mem_orthGroup m)

theorem card_pow_dvd_card_Ωm [Finite F] [CharP F 2] (m : ℕ) (b c : F) :
    (Nat.card F - 1) ^ m ∣ Nat.card ↥(Ωm m F b c) := by
  have hle : (torusHom (F := F) m).range ≤ Ωm m F b c := by
    rintro _ ⟨t, rfl⟩
    exact torusHom_mem_Ωm m t
  have h1 : Nat.card (torusHom (F := F) m).range = (Nat.card F - 1) ^ m := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (torusHom_injective m)).toEquiv,
      Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_units]
  rw [← h1]
  exact Subgroup.card_dvd_of_le hle

end Torus

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus
