module

public import CFSG.LieType.SpecialLinear.ExteriorModel.Weights

public section

namespace CFSG.LieType.SpecialLinear.ExteriorModel

open Matrix

variable {k : Type} [Field k] {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]

omit [Fintype τ] [DecidableEq τ] in
theorem bdeg_eq_of_mem {ε : τ → Finset (Fin n)} {r : τ} {j : Fin n} (h : j ∈ ε r) :
    bdeg ε (r, j) = (j : ℕ) := by
  simp [bdeg, h]

omit [Fintype τ] [DecidableEq τ] in
theorem bdeg_eq_zero_of_notMem {ε : τ → Finset (Fin n)} {r : τ} {j : Fin n}
    (h : j ∉ ε r) : bdeg ε (r, j) = 0 := by
  simp [bdeg, h]

omit [Fintype τ] in
theorem bdeg_eq_zero_of_ne_of_single {ε : τ → Finset (Fin n)} {r₀ : τ} {j : Fin n}
    (hε : ε r₀ = {j}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅) {p : τ × Fin n}
    (hp : p ≠ (r₀, j)) : bdeg ε p = 0 := by
  rcases p with ⟨r, j'⟩
  by_cases hr : r = r₀
  · subst hr
    apply bdeg_eq_zero_of_notMem
    intro hmem
    rw [hε] at hmem
    have hj' : j' = j := by simpa using hmem
    exact hp (by simp [hj'])
  · apply bdeg_eq_zero_of_notMem
    rw [hε' r hr]
    simp

omit [Fintype τ] in
theorem bdeg_eq_zero_of_ne_of_pair {ε : τ → Finset (Fin n)} {r₁ r₂ : τ}
    {j₁ j₂ : Fin n} (h₁ : ε r₁ = {j₁}) (h₂ : ε r₂ = {j₂})
    (hε' : ∀ r, r ≠ r₁ → r ≠ r₂ → ε r = ∅) {p : τ × Fin n}
    (hp₁ : p ≠ (r₁, j₁)) (hp₂ : p ≠ (r₂, j₂)) : bdeg ε p = 0 := by
  rcases p with ⟨r, j⟩
  by_cases hr₁ : r = r₁
  · subst hr₁
    apply bdeg_eq_zero_of_notMem
    intro hmem
    rw [h₁] at hmem
    have hj : j = j₁ := by simpa using hmem
    exact hp₁ (by simp [hj])
  · by_cases hr₂ : r = r₂
    · subst hr₂
      apply bdeg_eq_zero_of_notMem
      intro hmem
      rw [h₂] at hmem
      have hj : j = j₂ := by simpa using hmem
      exact hp₂ (by simp [hj])
    · apply bdeg_eq_zero_of_notMem
      rw [hε' r hr₁ hr₂]
      simp

omit [Fintype τ] [DecidableEq τ] in
theorem exists_bPerm_btop_eq_of_card_le_one (ε : τ → Finset (Fin n))
    (hε : ∀ r, (ε r).card ≤ 1) (s : BIdx ε) :
    ∃ π : τ → Equiv.Perm (Fin n), bPerm ε π (btop ε) = s := by
  classical
  have hper : ∀ r : τ, ∃ σ : Equiv.Perm (Fin n),
      ∀ j : Fin n,
        ((btop ε (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) : Finset (Fin n)).map
            σ.toEmbedding =
          ((s (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) : Finset (Fin n)) := by
    intro r
    by_cases hne : (ε r).Nonempty
    · obtain ⟨j₀, hj₀⟩ := hne
      have huniq : ∀ j ∈ ε r, j = j₀ := by
        intro j hj
        exact (Finset.card_le_one.mp (hε r)) j hj j₀ hj₀
      obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq
        ((btop ε (r, j₀) : Set.powersetCard (Fin n) (bdeg ε (r, j₀))) : Finset (Fin n))
        ((s (r, j₀) : Set.powersetCard (Fin n) (bdeg ε (r, j₀))) : Finset (Fin n))
        (by rw [Set.powersetCard.card_eq, Set.powersetCard.card_eq])
      refine ⟨σ, fun j => ?_⟩
      by_cases hj : j ∈ ε r
      · have hjj : j = j₀ := huniq j hj
        subst hjj
        exact hσ
      · have hdegj : bdeg ε (r, j) = 0 := bdeg_eq_zero_of_notMem hj
        have hbtop : ((btop ε (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) :
            Finset (Fin n)) = ∅ := by
          simp [btop, ktop, initSeg, hdegj]
        have hs : ((s (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) :
            Finset (Fin n)) = ∅ := by
          apply Finset.card_eq_zero.mp
          rw [Set.powersetCard.card_eq]
          exact hdegj
        rw [hbtop, hs, Finset.map_empty]
    · have hempty : ε r = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      refine ⟨1, fun j => ?_⟩
      have hdegj : bdeg ε (r, j) = 0 := bdeg_eq_zero_of_notMem (by simp [hempty])
      have hbtop : ((btop ε (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) :
          Finset (Fin n)) = ∅ := by
        simp [btop, ktop, initSeg, hdegj]
      have hs : ((s (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) :
          Finset (Fin n)) = ∅ := by
        apply Finset.card_eq_zero.mp
        rw [Set.powersetCard.card_eq]
        exact hdegj
      rw [hbtop, hs, Finset.map_empty]
  choose π hπ using hper
  refine ⟨π, ?_⟩
  funext p
  exact Subtype.ext (hπ p.1 p.2)

theorem bCyc_eq_top_of_card_le_one [CharP k 2] (ε : τ → Finset (Fin n))
    (hε : ∀ r, (ε r).card ≤ 1) : bCyc (k := k) ε = ⊤ := by
  classical
  rw [Submodule.eq_top_iff']
  intro v
  have hv : v = ∑ s : BIdx ε, v s • Pi.single s (1 : k) := by
    funext p
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  refine Submodule.sum_mem _ fun s _ => ?_
  refine Submodule.smul_mem _ _ ?_
  obtain ⟨π, hπ⟩ := exists_bPerm_btop_eq_of_card_le_one ε hε s
  rw [← hπ]
  exact single_bPerm_btop_mem_bCyc ε π

theorem dotRad_top_eq_bot {I : Type*} [Fintype I] [DecidableEq I] :
    dotRad (⊤ : Submodule k (I → k)) = ⊥ := by
  ext x
  rw [mem_dotRad, Submodule.mem_bot]
  constructor
  · rintro ⟨-, hx⟩
    funext i
    rw [← dotProduct_single_one x i]
    exact hx (Pi.single i 1) (Submodule.mem_top)
  · rintro rfl
    exact ⟨Submodule.zero_mem _, fun y _ => by simp⟩

theorem bRad_eq_bot_of_card_le_one [CharP k 2] (ε : τ → Finset (Fin n))
    (hε : ∀ r, (ε r).card ≤ 1) : bRad (k := k) ε = ⊥ := by
  rw [bRad, bCyc_eq_top_of_card_le_one ε hε]
  exact dotRad_top_eq_bot (k := k) (I := BIdx ε)

@[expose] noncomputable def bModelToFun [CharP k 2] (ε : τ → Finset (Fin n))
    (hε : ∀ r, (ε r).card ≤ 1) : BModel k ε →ₗ[k] (BIdx ε → k) :=
  Submodule.liftQ ((bRad (k := k) ε).comap (bCyc (k := k) ε).subtype)
    (bCyc (k := k) ε).subtype (by
      rw [bRad_eq_bot_of_card_le_one ε hε]
      simp)

@[expose] noncomputable def bModelEquivOfCardLeOne [CharP k 2] (ε : τ → Finset (Fin n))
    (hε : ∀ r, (ε r).card ≤ 1) : BModel k ε ≃ₗ[k] (BIdx ε → k) :=
  LinearEquiv.ofBijective (bModelToFun ε hε) (by
    constructor
    · intro x y hxy
      revert hxy
      refine Submodule.Quotient.induction_on
        (p := (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype) x ?_
      intro wx
      refine Submodule.Quotient.induction_on
        (p := (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype) y ?_
      intro wy hxy
      have h : (wx : BIdx ε → k) = (wy : BIdx ε → k) := by
        simpa [bModelToFun, Submodule.liftQ_apply] using hxy
      have hw : wx = wy := Subtype.ext h
      rw [hw]
    · intro v
      refine ⟨Submodule.Quotient.mk ⟨v, ?_⟩, ?_⟩
      · rw [bCyc_eq_top_of_card_le_one ε hε]
        exact Submodule.mem_top
      · simp [bModelToFun, Submodule.liftQ_apply])

theorem bModelEquivOfCardLeOne_bRep [CharP k 2] (ε : τ → Finset (Fin n))
    (hε : ∀ r, (ε r).card ≤ 1) (h : τ → Matrix.SpecialLinearGroup (Fin n) k)
    (x : BModel k ε) :
    bModelEquivOfCardLeOne (k := k) ε hε (bRep ε h x) =
      bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k)) *ᵥ
        bModelEquivOfCardLeOne (k := k) ε hε x := by
  refine Submodule.Quotient.induction_on
    (p := (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype) x ?_
  intro w
  rw [bRep_mk]
  simp [bModelEquivOfCardLeOne, bModelToFun, Submodule.liftQ_apply]

@[expose] noncomputable def bIdxEquivSingle (ε : τ → Finset (Fin n)) (r₀ : τ) (j : Fin n)
    (hε : ε r₀ = {j}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    BIdx ε ≃ Set.powersetCard (Fin n) j := by
  classical
  let toFun : BIdx ε → Set.powersetCard (Fin n) j := fun s =>
    ⟨((s (r₀, j) : Set.powersetCard (Fin n) (bdeg ε (r₀, j))) : Finset (Fin n)), by
      rw [Set.powersetCard.mem_iff, Set.powersetCard.card_eq, bdeg_eq_of_mem (by simp [hε])]⟩
  let invFun : Set.powersetCard (Fin n) j → BIdx ε := fun t p =>
    if h : p = (r₀, j) then
      ⟨(t : Finset (Fin n)), by
        rw [Set.powersetCard.mem_iff, h, bdeg_eq_of_mem (by simp [hε])]
        exact Set.powersetCard.card_eq t⟩
    else
      ⟨∅, by
        rw [Set.powersetCard.mem_iff, bdeg_eq_zero_of_ne_of_single hε hε' h]
        simp⟩
  refine ⟨toFun, invFun, ?_, ?_⟩
  · intro s
    funext p
    by_cases hp : p = (r₀, j)
    · subst hp
      apply Subtype.ext
      simp [toFun, invFun]
    · apply Subtype.ext
      dsimp only [toFun, invFun]
      rw [dif_neg hp]
      have hs : (s p).val = ∅ := by
        apply Finset.card_eq_zero.mp
        rw [Set.powersetCard.card_eq]
        exact bdeg_eq_zero_of_ne_of_single hε hε' hp
      rw [hs]
  · intro t
    apply Subtype.ext
    simp [toFun, invFun]

omit [Fintype τ] in
@[simp] theorem bIdxEquivSingle_apply_val (ε : τ → Finset (Fin n)) (r₀ : τ) (j : Fin n)
    (hε : ε r₀ = {j}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (s : BIdx ε) :
    ((bIdxEquivSingle ε r₀ j hε hε' s : Set.powersetCard (Fin n) j) : Finset (Fin n)) =
      ((s (r₀, j) : Set.powersetCard (Fin n) (bdeg ε (r₀, j))) : Finset (Fin n)) :=
  rfl

theorem minor_eq_of_val_eq {m : ℕ} {R : Type*} [CommRing R] (g : Matrix (Fin m) (Fin m) R)
    {n₁ n₂ : ℕ} (hdeg : n₁ = n₂) {s₁ : Set.powersetCard (Fin m) n₁}
    {s₂ : Set.powersetCard (Fin m) n₂}
    (hs : (s₁ : Finset (Fin m)) = (s₂ : Finset (Fin m)))
    {t₁ : Set.powersetCard (Fin m) n₁} {t₂ : Set.powersetCard (Fin m) n₂}
    (ht : (t₁ : Finset (Fin m)) = (t₂ : Finset (Fin m))) :
    minor g s₁ t₁ = minor g s₂ t₂ := by
  subst hdeg
  rw [Subtype.ext hs, Subtype.ext ht]

theorem minor_eq_one_of_card_eq_zero {m : ℕ} {R : Type*} [CommRing R]
    (g : Matrix (Fin m) (Fin m) R) {n : ℕ} (s t : Set.powersetCard (Fin m) n)
    (hn : n = 0) : minor g s t = 1 := by
  subst hn
  rw [minor]
  exact Matrix.det_isEmpty

theorem bMat_apply_of_single (ε : τ → Finset (Fin n)) (r₀ : τ) (j : Fin n)
    (hε : ε r₀ = {j}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅)
    (h : τ → Matrix (Fin n) (Fin n) k) (s t : BIdx ε) :
    bMat ε h s t =
      minor (h r₀) (bIdxEquivSingle ε r₀ j hε hε' s) (bIdxEquivSingle ε r₀ j hε hε' t) := by
  classical
  rw [bMat, kronMinor_apply]
  rw [Fintype.prod_eq_single (r₀, j)]
  · exact minor_eq_of_val_eq (h r₀) (bdeg_eq_of_mem (by simp [hε]))
      (bIdxEquivSingle_apply_val ε r₀ j hε hε' s).symm
      (bIdxEquivSingle_apply_val ε r₀ j hε hε' t).symm
  · intro p hp
    exact minor_eq_one_of_card_eq_zero (h p.1) (s p) (t p)
      (bdeg_eq_zero_of_ne_of_single hε hε' hp)

@[expose] noncomputable def bIdxEquivPair (ε : τ → Finset (Fin n)) {r₁ r₂ : τ} (hr : r₁ ≠ r₂)
    (j₁ j₂ : Fin n) (h₁ : ε r₁ = {j₁}) (h₂ : ε r₂ = {j₂})
    (hε' : ∀ r, r ≠ r₁ → r ≠ r₂ → ε r = ∅) :
    BIdx ε ≃ Set.powersetCard (Fin n) j₁ × Set.powersetCard (Fin n) j₂ := by
  classical
  let toFun : BIdx ε → Set.powersetCard (Fin n) j₁ × Set.powersetCard (Fin n) j₂ := fun s =>
    (⟨((s (r₁, j₁) : Set.powersetCard (Fin n) (bdeg ε (r₁, j₁))) : Finset (Fin n)), by
        rw [Set.powersetCard.mem_iff, Set.powersetCard.card_eq, bdeg_eq_of_mem (by simp [h₁])]⟩,
      ⟨((s (r₂, j₂) : Set.powersetCard (Fin n) (bdeg ε (r₂, j₂))) : Finset (Fin n)), by
        rw [Set.powersetCard.mem_iff, Set.powersetCard.card_eq, bdeg_eq_of_mem (by simp [h₂])]⟩)
  let invFun : Set.powersetCard (Fin n) j₁ × Set.powersetCard (Fin n) j₂ → BIdx ε := fun t p =>
    if h₁p : p = (r₁, j₁) then
      ⟨(t.1 : Finset (Fin n)), by
        rw [Set.powersetCard.mem_iff, h₁p, bdeg_eq_of_mem (by simp [h₁])]
        exact Set.powersetCard.card_eq t.1⟩
    else if h₂p : p = (r₂, j₂) then
      ⟨(t.2 : Finset (Fin n)), by
        rw [Set.powersetCard.mem_iff, h₂p, bdeg_eq_of_mem (by simp [h₂])]
        exact Set.powersetCard.card_eq t.2⟩
    else
      ⟨∅, by
        rw [Set.powersetCard.mem_iff, bdeg_eq_zero_of_ne_of_pair h₁ h₂ hε' h₁p h₂p]
        simp⟩
  refine ⟨toFun, invFun, ?_, ?_⟩
  · intro s
    funext p
    by_cases hp₁ : p = (r₁, j₁)
    · subst hp₁
      apply Subtype.ext
      simp [toFun, invFun]
    · by_cases hp₂ : p = (r₂, j₂)
      · subst hp₂
        apply Subtype.ext
        simp [toFun, invFun, hp₁]
      · apply Subtype.ext
        dsimp only [toFun, invFun]
        rw [dif_neg hp₁, dif_neg hp₂]
        have hs : (s p).val = ∅ := by
          apply Finset.card_eq_zero.mp
          rw [Set.powersetCard.card_eq]
          exact bdeg_eq_zero_of_ne_of_pair h₁ h₂ hε' hp₁ hp₂
        rw [hs]
  · intro t
    apply Prod.ext
    · apply Subtype.ext
      simp [toFun, invFun]
    · apply Subtype.ext
      have hne : ¬ ((r₂, j₂) = (r₁, j₁)) := by
        intro h
        exact hr (congrArg Prod.fst h).symm
      simp [toFun, invFun, hne]

omit [Fintype τ] in
@[simp] theorem bIdxEquivPair_apply_fst_val (ε : τ → Finset (Fin n)) {r₁ r₂ : τ}
    (hr : r₁ ≠ r₂) (j₁ j₂ : Fin n) (h₁ : ε r₁ = {j₁}) (h₂ : ε r₂ = {j₂})
    (hε' : ∀ r, r ≠ r₁ → r ≠ r₂ → ε r = ∅) (s : BIdx ε) :
    ((bIdxEquivPair ε hr j₁ j₂ h₁ h₂ hε' s).1 : Finset (Fin n)) =
      ((s (r₁, j₁) : Set.powersetCard (Fin n) (bdeg ε (r₁, j₁))) : Finset (Fin n)) :=
  rfl

omit [Fintype τ] in
@[simp] theorem bIdxEquivPair_apply_snd_val (ε : τ → Finset (Fin n)) {r₁ r₂ : τ}
    (hr : r₁ ≠ r₂) (j₁ j₂ : Fin n) (h₁ : ε r₁ = {j₁}) (h₂ : ε r₂ = {j₂})
    (hε' : ∀ r, r ≠ r₁ → r ≠ r₂ → ε r = ∅) (s : BIdx ε) :
    ((bIdxEquivPair ε hr j₁ j₂ h₁ h₂ hε' s).2 : Finset (Fin n)) =
      ((s (r₂, j₂) : Set.powersetCard (Fin n) (bdeg ε (r₂, j₂))) : Finset (Fin n)) :=
  rfl

theorem bMat_apply_of_pair (ε : τ → Finset (Fin n)) {r₁ r₂ : τ} (hr : r₁ ≠ r₂)
    (j₁ j₂ : Fin n) (h₁ : ε r₁ = {j₁}) (h₂ : ε r₂ = {j₂})
    (hε' : ∀ r, r ≠ r₁ → r ≠ r₂ → ε r = ∅)
    (h : τ → Matrix (Fin n) (Fin n) k) (s t : BIdx ε) :
    bMat ε h s t =
      minor (h r₁) (bIdxEquivPair ε hr j₁ j₂ h₁ h₂ hε' s).1
          (bIdxEquivPair ε hr j₁ j₂ h₁ h₂ hε' t).1 *
        minor (h r₂) (bIdxEquivPair ε hr j₁ j₂ h₁ h₂ hε' s).2
          (bIdxEquivPair ε hr j₁ j₂ h₁ h₂ hε' t).2 := by
  classical
  rw [bMat, kronMinor_apply]
  rw [Fintype.prod_eq_mul (r₁, j₁) (r₂, j₂)]
  · rw [show minor (h r₁) (s (r₁, j₁)) (t (r₁, j₁)) =
        minor (h r₁) (bIdxEquivPair ε hr j₁ j₂ h₁ h₂ hε' s).1
          (bIdxEquivPair ε hr j₁ j₂ h₁ h₂ hε' t).1 from
      minor_eq_of_val_eq (h r₁) (bdeg_eq_of_mem (by simp [h₁]))
        (bIdxEquivPair_apply_fst_val ε hr j₁ j₂ h₁ h₂ hε' s).symm
        (bIdxEquivPair_apply_fst_val ε hr j₁ j₂ h₁ h₂ hε' t).symm]
    rw [show minor (h r₂) (s (r₂, j₂)) (t (r₂, j₂)) =
        minor (h r₂) (bIdxEquivPair ε hr j₁ j₂ h₁ h₂ hε' s).2
          (bIdxEquivPair ε hr j₁ j₂ h₁ h₂ hε' t).2 from
      minor_eq_of_val_eq (h r₂) (bdeg_eq_of_mem (by simp [h₂]))
        (bIdxEquivPair_apply_snd_val ε hr j₁ j₂ h₁ h₂ hε' s).symm
        (bIdxEquivPair_apply_snd_val ε hr j₁ j₂ h₁ h₂ hε' t).symm]
  · intro hpq
    exact hr (congrArg Prod.fst hpq)
  · intro p hp
    exact minor_eq_one_of_card_eq_zero (h p.1) (s p) (t p)
      (bdeg_eq_zero_of_ne_of_pair h₁ h₂ hε' hp.1 hp.2)

@[expose] noncomputable def powersetCardOneEquiv : Set.powersetCard (Fin n) 1 ≃ Fin n :=
  (Set.powersetCard.ofSingleton (α := Fin n)).symm

theorem minor_singleton (h : Matrix (Fin n) (Fin n) k) (a b : Fin n) :
    minor h (⟨{a}, Finset.card_singleton a⟩ : Set.powersetCard (Fin n) 1)
      (⟨{b}, Finset.card_singleton b⟩ : Set.powersetCard (Fin n) 1) = h a b := by
  rw [minor, Matrix.det_fin_one]
  have ha : Set.powersetCard.ofFinEmbEquiv.symm
      (⟨{a}, Finset.card_singleton a⟩ : Set.powersetCard (Fin n) 1) (0 : Fin 1) = a := by
    change Finset.orderEmbOfFin ({a} : Finset (Fin n)) (Finset.card_singleton a)
      (0 : Fin 1) = a
    simp
  have hb : Set.powersetCard.ofFinEmbEquiv.symm
      (⟨{b}, Finset.card_singleton b⟩ : Set.powersetCard (Fin n) 1) (0 : Fin 1) = b := by
    change Finset.orderEmbOfFin ({b} : Finset (Fin n)) (Finset.card_singleton b)
      (0 : Fin 1) = b
    simp
  rw [Matrix.submatrix_apply, ha, hb]

theorem minor_powersetCardOneEquiv_symm (h : Matrix (Fin n) (Fin n) k) (a b : Fin n) :
    minor h (powersetCardOneEquiv.symm a) (powersetCardOneEquiv.symm b) = h a b := by
  have ha : powersetCardOneEquiv.symm a =
      (⟨{a}, Finset.card_singleton a⟩ : Set.powersetCard (Fin n) 1) := rfl
  have hb : powersetCardOneEquiv.symm b =
      (⟨{b}, Finset.card_singleton b⟩ : Set.powersetCard (Fin n) 1) := rfl
  rw [ha, hb]
  exact minor_singleton h a b

end CFSG.LieType.SpecialLinear.ExteriorModel
