module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Blocks
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.G2
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.FixedEscape
public import CFSG.LieType.HighestRoot.CentTrialityThree

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.SpCell

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.Open
  CFSG.QuasithinUnique CFSG.AGLEmbedding.LieOut
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (flagStabilizer)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (flag stabilizer mem_stabilizer mem_flag_of_le
  mem_isoFlag isoFlag mem_orthogonal_isoFlag)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

variable {r : ℕ} {K : Type} [Field K]

def cnt (S : Finset ℕ) (a : ℕ) : ℕ := (S.filter (· ≤ a)).card

theorem cnt_le_card (S : Finset ℕ) (a : ℕ) : cnt S a ≤ S.card := Finset.card_filter_le _ _

theorem cnt_mono (S : Finset ℕ) {a b : ℕ} (h : a ≤ b) : cnt S a ≤ cnt S b :=
  Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.trans h⟩

theorem exists_cut_of_cnt_lt (S : Finset ℕ) {a b : ℕ} (h : cnt S a < cnt S b) :
    ∃ i ∈ S, a < i ∧ i ≤ b := by
  by_contra hcon
  push Not at hcon
  have : cnt S b ≤ cnt S a := by
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    by_contra hia
    exact absurd hi.2 (not_le.2 (hcon i hi.1 (not_le.1 hia)))
  omega

theorem cnt_lt_of_cut (S : Finset ℕ) {a b i : ℕ} (hi : i ∈ S) (hbi : b < i) (hia : i ≤ a) :
    cnt S b < cnt S a := by
  have h1 : cnt S b ≤ cnt S a := cnt_mono S (by omega)
  have h2 : cnt S b ≠ cnt S a := by
    intro heq
    have hsub : S.filter (· ≤ b) ⊆ S.filter (· ≤ a) := fun j hj => by
      simp only [Finset.mem_filter] at hj ⊢
      exact ⟨hj.1, hj.2.trans (by omega)⟩
    have := Finset.eq_of_subset_of_card_le hsub (by unfold cnt at heq; omega)
    have hmem : i ∈ S.filter (· ≤ a) := Finset.mem_filter.2 ⟨hi, hia⟩
    rw [← this] at hmem
    have := (Finset.mem_filter.1 hmem).2
    omega
  omega

theorem exists_cut_of_cnt_lt_card (S : Finset ℕ) {a : ℕ} (h : cnt S a < S.card) :
    ∃ i ∈ S, a < i := by
  by_contra hcon
  push Not at hcon
  have : S.filter (· ≤ a) = S := Finset.filter_true_of_mem fun i hi => hcon i hi
  unfold cnt at h
  rw [this] at h
  exact lt_irrefl _ h

def spLev (r : ℕ) (S : Finset ℕ) : Fin r ⊕ Fin r → ℕ
  | Sum.inl a => cnt S a
  | Sum.inr a => 2 * S.card - cnt S a

theorem flag_eq_isoFlag {i : ℕ} (hi : i ≤ r) : flag r K i = isoFlag r K i := by
  rw [flag, ite_eq_left hi]

theorem spMat_mulVec_mem_perp {i : ℕ} {g : StatedSp r K} (hg : g ∈ stabilizer r K (isoFlag r K i))
    {w : Fin r ⊕ Fin r → K} (hw : w ∈ (pairedSympForm K r).orthogonal (isoFlag r K i)) :
    spMat g *ᵥ w ∈ (pairedSympForm K r).orthogonal (isoFlag r K i) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hw ⊢
  intro f hf
  have h1 : spMat g⁻¹ *ᵥ f ∈ isoFlag r K i := spMat_mulVec_mem_of_mem_stabilizer (inv_mem hg) hf
  have h2 := hw _ h1
  have h3 : spMat g *ᵥ (spMat g⁻¹ *ᵥ f) = f := by
    rw [mulVec_mulVec, spMat_mul_inv, one_mulVec]
  show pairedSympForm K r f (spMat g *ᵥ w) = 0
  rw [← h3, pairedSympForm_spMat_mulVec]
  exact h2

theorem single_inl_mem_perp {i : ℕ} (b : Fin r) :
    (Pi.single (Sum.inl b) 1 : Fin r ⊕ Fin r → K) ∈
      (pairedSympForm K r).orthogonal (isoFlag r K i) := by
  rw [mem_orthogonal_isoFlag]
  intro j _
  exact Pi.single_eq_of_ne (by simp) _

theorem single_inr_mem_perp {i : ℕ} {b : Fin r} (hib : i ≤ (b : ℕ)) :
    (Pi.single (Sum.inr b) 1 : Fin r ⊕ Fin r → K) ∈
      (pairedSympForm K r).orthogonal (isoFlag r K i) := by
  rw [mem_orthogonal_isoFlag]
  intro j hj
  refine Pi.single_eq_of_ne ?_ _
  intro h
  have := Sum.inr_injective h
  have h2 : (j : ℕ) = b := by simpa using congrArg Fin.val this
  omega

theorem spMat_blockTriangular {S : Finset ℕ} (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) {g : StatedSp r K}
    (hg : g ∈ flagStabilizer r K (S : Set ℕ)) : (spMat g).BlockTriangular (spLev r S) := by
  have hgi : ∀ i ∈ S, g ∈ stabilizer r K (isoFlag r K i) := fun i hi => by
    have := SymplecticHigher.mem_flagStabilizer.mp hg i hi
    rwa [flag_eq_isoFlag (hS i hi).2] at this
  intro u v huv
  have hcard : ∀ a : ℕ, cnt S a ≤ S.card := cnt_le_card S
  rcases u with a | a <;> rcases v with b | b
  ·
    have huv' : cnt S b < cnt S a := huv
    obtain ⟨i, hiS, hbi, hia⟩ := exists_cut_of_cnt_lt S huv'
    have hmem := spMat_mulVec_mem_of_mem_stabilizer (hgi i hiS)
      (single_mem_flag (K := K) (hS i hiS).2 b b.2 hbi |> fun h => by
        rwa [flag_eq_isoFlag (hS i hiS).2] at h)
    rw [mem_isoFlag, Matrix.mulVec_single_one] at hmem
    exact hmem.2 a hia
  ·
    have huv' : 2 * S.card - cnt S b < cnt S a := huv
    have := hcard a; have := hcard b
    omega
  ·
    have huv' : cnt S b < 2 * S.card - cnt S a := huv
    by_cases hb : ∃ i ∈ S, (b : ℕ) < i
    · obtain ⟨i, hiS, hbi⟩ := hb
      have hmem := spMat_mulVec_mem_of_mem_stabilizer (hgi i hiS)
        (single_mem_flag (K := K) (hS i hiS).2 b b.2 hbi |> fun h => by
          rwa [flag_eq_isoFlag (hS i hiS).2] at h)
      rw [mem_isoFlag, Matrix.mulVec_single_one] at hmem
      exact hmem.1 a
    · push Not at hb
      have hcb : cnt S b = S.card := by
        unfold cnt
        rw [Finset.filter_true_of_mem hb]
      have hca : cnt S a < S.card := by
        have := hcard a
        omega
      obtain ⟨i, hiS, hai⟩ := exists_cut_of_cnt_lt_card S hca
      have hmem := spMat_mulVec_mem_perp (hgi i hiS) (single_inl_mem_perp (K := K) (i := i) b)
      rw [mem_orthogonal_isoFlag, Matrix.mulVec_single_one] at hmem
      exact hmem a hai
  ·
    have huv' : 2 * S.card - cnt S b < 2 * S.card - cnt S a := huv
    have hab : cnt S a < cnt S b := by
      have := hcard a; have := hcard b
      omega
    obtain ⟨i, hiS, hai, hib⟩ := exists_cut_of_cnt_lt S hab
    have hmem := spMat_mulVec_mem_perp (hgi i hiS) (single_inr_mem_perp (K := K) hib)
    rw [mem_orthogonal_isoFlag, Matrix.mulVec_single_one] at hmem
    exact hmem a hai

theorem spMat_inv_blockTriangular {lev : Fin r ⊕ Fin r → ℕ} {g : StatedSp r K}
    (hg : (spMat g).BlockTriangular lev) : (spMat g⁻¹).BlockTriangular lev := by
  have : Invertible (spMat g) := Units.invertible (g : GL (Fin r ⊕ Fin r) K)
  have h1 := Matrix.blockTriangular_inv_of_blockTriangular hg
  have h2 : spMat g⁻¹ = (spMat g)⁻¹ := (Matrix.inv_eq_right_inv (spMat_mul_inv g)).symm
  rw [h2]
  exact h1

theorem mem_flagStabilizer_of_blockTriangular {S : Finset ℕ} (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r)
    {g : StatedSp r K} (hg : (spMat g).BlockTriangular (spLev r S)) :
    g ∈ flagStabilizer r K (S : Set ℕ) := by
  have key : ∀ {h : StatedSp r K}, (spMat h).BlockTriangular (spLev r S) → ∀ i ∈ S,
      ∀ v ∈ isoFlag r K i, spMat h *ᵥ v ∈ isoFlag r K i := by
    intro h hh i hi v hv
    rw [mem_isoFlag] at hv ⊢
    have hvsupp : ∀ c, v c ≠ 0 → ∃ j : Fin r, c = Sum.inl j ∧ (j : ℕ) < i := by
      intro c hc
      rcases c with j | j
      · refine ⟨j, rfl, ?_⟩
        by_contra hj
        exact hc (hv.2 j (not_lt.1 hj))
      · exact absurd (hv.1 j) hc
    refine ⟨fun a => ?_, fun a ha => ?_⟩
    · rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hvc : v c = 0
      · rw [hvc, mul_zero]
      · obtain ⟨j, rfl, hji⟩ := hvsupp c hvc
        have : spLev r S (Sum.inl j) < spLev r S (Sum.inr a) := by
          have h1 : cnt S j < S.card := by
            by_contra hcon
            push Not at hcon
            have hall : S.filter (· ≤ (j : ℕ)) = S :=
              Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hcon
            have : i ∈ S.filter (· ≤ (j : ℕ)) := by rw [hall]; exact hi
            have := (Finset.mem_filter.1 this).2
            omega
          have h2 := cnt_le_card S a
          show cnt S j < 2 * S.card - cnt S a
          omega
        rw [hh this, zero_mul]
    · rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hvc : v c = 0
      · rw [hvc, mul_zero]
      · obtain ⟨j, rfl, hji⟩ := hvsupp c hvc
        have : spLev r S (Sum.inl j) < spLev r S (Sum.inl a) :=
          cnt_lt_of_cut S hi hji ha
        rw [hh this, zero_mul]
  rw [SymplecticHigher.mem_flagStabilizer]
  intro i hi
  rw [flag_eq_isoFlag (hS i hi).2]
  exact SymplecticFlag.mem_stabilizer_of_mulVec_mem (fun v hv => key hg i hi v hv)
    (fun v hv => key (spMat_inv_blockTriangular hg) i hi v hv)

section Blocks

variable (r K) (S : Finset ℕ)

abbrev Jfl : Subgroup (StatedSp r K) := flagStabilizer r K (S : Set ℕ)

@[expose] def πJ : ↥(Jfl r K S) →* GL (Fin r ⊕ Fin r) K :=
  (StatedSp r K).subtype.comp (Jfl r K S).subtype

variable {r K S}

theorem πJ_blockTriangular (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) (g : ↥(Jfl r K S)) :
    ((πJ r K S g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).BlockTriangular
      (spLev r S) := spMat_blockTriangular hS g.2

abbrev StepCoord (r : ℕ) (S : Finset ℕ) (ℓ : ℕ) := {a : Fin r // cnt S a = ℓ}

theorem step_injective (ℓ : ℕ) :
    Function.Injective (fun a : StepCoord r S ℓ => (Sum.inl a.1 : Fin r ⊕ Fin r)) :=
  fun _ _ h => Subtype.ext (Sum.inl_injective h)

theorem step_range {ℓ : ℕ} (hℓ : ℓ < S.card) (u : Fin r ⊕ Fin r) :
    spLev r S u = ℓ ↔ u ∈ Set.range (fun a : StepCoord r S ℓ => (Sum.inl a.1 : Fin r ⊕ Fin r)) := by
  rcases u with a | a
  · constructor
    · intro h
      exact ⟨⟨a, h⟩, rfl⟩
    · rintro ⟨b, hb⟩
      have := Sum.inl_injective hb
      subst this
      exact b.2
  · constructor
    · intro h
      have : 2 * S.card - cnt S a = ℓ := h
      have := cnt_le_card S a
      omega
    · rintro ⟨b, hb⟩
      exact absurd hb (by simp)

@[expose] def stepHom (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) {ℓ : ℕ} (hℓ : ℓ < S.card) :
    ↥(Jfl r K S) →* GL (StepCoord r S ℓ) K :=
  levelHom (πJ r K S) (πJ_blockTriangular hS) (step_injective ℓ) (step_range hℓ)

theorem coe_stepHom (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) {ℓ : ℕ} (hℓ : ℓ < S.card) (g : ↥(Jfl r K S)) :
    ((stepHom hS hℓ g : GL (StepCoord r S ℓ) K) : Matrix (StepCoord r S ℓ) (StepCoord r S ℓ) K) =
      (spMat (g : StatedSp r K)).submatrix (fun a => Sum.inl a.1) (fun a => Sum.inl a.1) :=
  coe_levelHom _ _ _ _ g

end Blocks

section Top

variable (r) (S : Finset ℕ)

@[expose] def topN : ℕ := Fintype.card {a : Fin r // cnt S a = S.card}

@[expose] def topEmb : Fin (topN r S) → Fin r := fun j =>
  ((Fintype.equivFin {a : Fin r // cnt S a = S.card}).symm j).1

@[expose] def topσ : Fin (topN r S) ⊕ Fin (topN r S) → Fin r ⊕ Fin r :=
  Sum.map (topEmb r S) (topEmb r S)

variable {r S}

theorem topEmb_injective : Function.Injective (topEmb r S) := fun _ _ h =>
  (Fintype.equivFin {a : Fin r // cnt S a = S.card}).symm.injective (Subtype.ext h)

theorem cnt_topEmb (j : Fin (topN r S)) : cnt S (topEmb r S j) = S.card :=
  ((Fintype.equivFin {a : Fin r // cnt S a = S.card}).symm j).2

theorem exists_topEmb_eq {a : Fin r} (h : cnt S a = S.card) : ∃ j, topEmb r S j = a :=
  ⟨Fintype.equivFin {a : Fin r // cnt S a = S.card} ⟨a, h⟩, by simp [topEmb]⟩

theorem topσ_injective : Function.Injective (topσ r S) :=
  Sum.map_injective.2 ⟨topEmb_injective, topEmb_injective⟩

theorem top_range (u : Fin r ⊕ Fin r) :
    spLev r S u = S.card ↔ u ∈ Set.range (topσ r S) := by
  rcases u with a | a
  · constructor
    · intro h
      obtain ⟨j, hj⟩ := exists_topEmb_eq (S := S) (a := a) h
      exact ⟨Sum.inl j, by simp [topσ, hj]⟩
    · rintro ⟨v, hv⟩
      rcases v with j | j
      · have : topEmb r S j = a := by simpa [topσ] using hv
        subst this
        exact cnt_topEmb j
      · simp [topσ] at hv
  · constructor
    · intro h
      have h' : 2 * S.card - cnt S a = S.card := h
      have := cnt_le_card S a
      obtain ⟨j, hj⟩ := exists_topEmb_eq (S := S) (a := a) (by omega)
      exact ⟨Sum.inr j, by simp [topσ, hj]⟩
    · rintro ⟨v, hv⟩
      rcases v with j | j
      · simp [topσ] at hv
      · have : topEmb r S j = a := by simpa [topσ] using hv
        subst this
        show 2 * S.card - cnt S (topEmb r S j) = S.card
        rw [cnt_topEmb j]
        omega

@[expose] def topHomGL (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) :
    ↥(Jfl r K S) →* GL (Fin (topN r S) ⊕ Fin (topN r S)) K :=
  levelHom (πJ r K S) (πJ_blockTriangular hS) topσ_injective top_range

theorem coe_topHomGL (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) (g : ↥(Jfl r K S)) :
    ((topHomGL hS g : GL (Fin (topN r S) ⊕ Fin (topN r S)) K) :
      Matrix (Fin (topN r S) ⊕ Fin (topN r S)) (Fin (topN r S) ⊕ Fin (topN r S)) K) =
      (spMat (g : StatedSp r K)).submatrix (topσ r S) (topσ r S) :=
  coe_levelHom _ _ _ _ g

theorem fromBlocks_submatrix_topσ :
    (Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) K) 1 (-1) 0).submatrix (topσ r S) (topσ r S) =
      Matrix.fromBlocks (0 : Matrix (Fin (topN r S)) (Fin (topN r S)) K) 1 (-1) 0 := by
  ext u v
  rcases u with a | a <;> rcases v with b | b <;>
    simp [topσ, Matrix.one_apply, topEmb_injective.eq_iff]

omit [Field K] in
theorem sum_sum_restrict {ι κ M : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid M] [DecidableEq ι]
    {σ : κ → ι} (hσ : Function.Injective σ) (f : ι → ι → M)
    (h0 : ∀ c d, ¬ (c ∈ Set.range σ ∧ d ∈ Set.range σ) → f c d = 0) :
    ∑ c, ∑ d, f c d = ∑ c', ∑ d', f (σ c') (σ d') := by
  classical
  have h1 : ∀ c, ∑ d, f c d = ∑ d', f c (σ d') ∨ c ∉ Set.range σ := by
    intro c
    by_cases hc : c ∈ Set.range σ
    · left
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image σ)),
        Finset.sum_image (fun x _ y _ h => hσ h)]
      intro d _ hd
      refine h0 c d fun h => hd (Finset.mem_image.2 ?_)
      obtain ⟨k, hk⟩ := h.2
      exact ⟨k, Finset.mem_univ _, hk⟩
    · right; exact hc
  have h2 : ∑ c, ∑ d, f c d = ∑ c, ∑ d', f c (σ d') := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rcases h1 c with h | h
    · exact h
    · rw [Finset.sum_eq_zero fun d _ => h0 c d fun h' => h h'.1,
        Finset.sum_eq_zero fun d _ => h0 c _ fun h' => h h'.1]
  rw [h2, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d' _ => ?_
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image σ)),
    Finset.sum_image (fun x _ y _ h => hσ h)]
  intro c _ hc
  exact h0 c (σ d') fun h => hc (Finset.mem_image.2 (by
    obtain ⟨k, hk⟩ := h.1
    exact ⟨k, Finset.mem_univ _, hk⟩))

theorem fromBlocks_ne_zero {c d : Fin r ⊕ Fin r}
    (h : (Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) K) 1 (-1) 0) c d ≠ 0) :
    (∃ a, c = Sum.inl a ∧ d = Sum.inr a) ∨ ∃ a, c = Sum.inr a ∧ d = Sum.inl a := by
  rcases c with a | a <;> rcases d with b | b
  · simp at h
  · left
    have : a = b := by
      by_contra hab
      apply h
      simp [Matrix.one_apply_ne hab]
    exact ⟨a, rfl, by rw [this]⟩
  · right
    have : a = b := by
      by_contra hab
      apply h
      simp [Matrix.one_apply_ne hab]
    exact ⟨a, rfl, by rw [this]⟩
  · simp at h

theorem topHomGL_mem_statedSp (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) (g : ↥(Jfl r K S)) :
    (topHomGL hS g : GL (Fin (topN r S) ⊕ Fin (topN r S)) K) ∈ StatedSp (topN r S) K := by
  rw [SymplecticTorusWeyl.mem_statedSp_iff, coe_topHomGL]
  set M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := spMat (g : StatedSp r K) with hM
  set Jr : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) K) 1 (-1) 0 with hJr
  have hsp : Mᵀ * Jr * M = Jr :=
    SymplecticTorusWeyl.mem_statedSp_iff.1 (g : StatedSp r K).2
  have hbt : M.BlockTriangular (spLev r S) := spMat_blockTriangular hS g.2
  have hJ : Jr.submatrix (topσ r S) (topσ r S) = Matrix.fromBlocks
      (0 : Matrix (Fin (topN r S)) (Fin (topN r S)) K) 1 (-1) 0 := fromBlocks_submatrix_topσ
  ext u v
  rw [← hJ]
  have hx : ∀ w : Fin (topN r S) ⊕ Fin (topN r S), spLev r S (topσ r S w) = S.card :=
    fun w => (top_range _).2 ⟨w, rfl⟩
  have hrhs : Jr.submatrix (topσ r S) (topσ r S) u v =
      (Mᵀ * Jr * M) (topσ r S u) (topσ r S v) := by
    rw [hsp]; rfl
  rw [hrhs]
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  rw [sum_sum_restrict (σ := topσ r S) topσ_injective]
  · intro c d hcd
    by_contra hne
    have h1 : M c (topσ r S u) ≠ 0 := fun h => hne (by rw [h]; simp)
    have h2 : M d (topσ r S v) ≠ 0 := fun h => hne (by rw [h]; simp)
    have h3 : Jr c d ≠ 0 := fun h => hne (by rw [h]; simp)
    have hc : spLev r S c ≤ S.card := by
      by_contra hcon
      exact h1 (hbt (by rw [hx]; omega))
    have hd : spLev r S d ≤ S.card := by
      by_contra hcon
      exact h2 (hbt (by rw [hx]; omega))
    apply hcd
    have hle := cnt_le_card S
    rcases fromBlocks_ne_zero h3 with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl⟩
    · have hc' : cnt S a ≤ S.card := hle a
      have hd' : 2 * S.card - cnt S a ≤ S.card := hd
      exact ⟨(top_range _).1 (by show cnt S a = S.card; omega),
        (top_range _).1 (by show 2 * S.card - cnt S a = S.card; omega)⟩
    · have hd' : cnt S a ≤ S.card := hle a
      have hc' : 2 * S.card - cnt S a ≤ S.card := hc
      exact ⟨(top_range _).1 (by show 2 * S.card - cnt S a = S.card; omega),
        (top_range _).1 (by show cnt S a = S.card; omega)⟩

@[expose] def topHom (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) :
    ↥(Jfl r K S) →* ↥(StatedSp (topN r S) K) :=
  (topHomGL hS).codRestrict (StatedSp (topN r S) K) (topHomGL_mem_statedSp hS)

theorem coe_topHom (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) (g : ↥(Jfl r K S)) :
    (((topHom hS g : ↥(StatedSp (topN r S) K)) : GL (Fin (topN r S) ⊕ Fin (topN r S)) K) :
      Matrix (Fin (topN r S) ⊕ Fin (topN r S)) (Fin (topN r S) ⊕ Fin (topN r S)) K) =
      (spMat (g : StatedSp r K)).submatrix (topσ r S) (topσ r S) :=
  coe_topHomGL hS g

end Top

section Kernel

variable {S : Finset ℕ}

theorem spMat_apply_eq_of_stepHom_eq_one (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) {ℓ : ℕ} (hℓ : ℓ < S.card)
    {g : ↥(Jfl r K S)} (hg : stepHom hS hℓ g = 1) (u v : Fin r ⊕ Fin r) (hu : spLev r S u = ℓ)
    (hv : spLev r S v = ℓ) :
    spMat (g : StatedSp r K) u v = (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) u v := by
  obtain ⟨a, rfl⟩ := (step_range hℓ u).1 hu
  obtain ⟨b, rfl⟩ := (step_range hℓ v).1 hv
  have h1 : spMat (g : StatedSp r K) (Sum.inl a.1) (Sum.inl b.1) =
      ((stepHom hS hℓ g : GL (StepCoord r S ℓ) K) : Matrix (StepCoord r S ℓ) (StepCoord r S ℓ) K)
        a b := by
    rw [coe_stepHom]; rfl
  rw [h1, hg, Units.val_one]
  simp [Matrix.one_apply, Subtype.ext_iff]

theorem spMat_apply_eq_of_topHom_eq_one (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r)
    {g : ↥(Jfl r K S)} (hg : topHom hS g = 1) (u v : Fin r ⊕ Fin r) (hu : spLev r S u = S.card)
    (hv : spLev r S v = S.card) :
    spMat (g : StatedSp r K) u v = (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) u v := by
  obtain ⟨a, rfl⟩ := (top_range u).1 hu
  obtain ⟨b, rfl⟩ := (top_range v).1 hv
  have h1 : spMat (g : StatedSp r K) (topσ r S a) (topσ r S b) =
      (((topHom hS g : ↥(StatedSp (topN r S) K)) : GL (Fin (topN r S) ⊕ Fin (topN r S)) K) :
        Matrix (Fin (topN r S) ⊕ Fin (topN r S)) (Fin (topN r S) ⊕ Fin (topN r S)) K) a b := by
    rw [coe_topHom]; rfl
  rw [h1, hg]
  simp [Matrix.one_apply, topσ_injective.eq_iff]

theorem eq_one_of_blocks_trivial (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) {p : ℕ} (hp : (p : K) ≠ 0)
    {g : ↥(Jfl r K S)} (hgp : g ^ p = 1) (hstep : ∀ ℓ (hℓ : ℓ < S.card), stepHom hS hℓ g = 1)
    (htop : topHom hS g = 1) : g = 1 := by
  set M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := spMat (g : StatedSp r K) with hM
  have hMp : M ^ p = 1 := by
    have : (g : StatedSp r K) ^ p = 1 := congrArg Subtype.val hgp
    rw [hM, ← spMat_pow, this, spMat_one]
  have hbt : M.BlockTriangular (spLev r S) := spMat_blockTriangular hS g.2
  have hblk : ∀ u v, spLev r S u = spLev r S v → spLev r S u < S.card + 1 →
      M u v = (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) u v := by
    intro u v huv hu
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hlt | heq
    · exact spMat_apply_eq_of_stepHom_eq_one hS hlt (hstep _ hlt) u v rfl huv.symm
    · exact spMat_apply_eq_of_topHom_eq_one hS htop u v heq (huv.symm.trans heq)
  have hfix := mulVec_eq_of_blocks_one hbt hp hMp (S.card + 1) hblk
  have hall : ∀ w : Fin r ⊕ Fin r → K, M *ᵥ w = w := by
    let U : ℕ → Submodule K (Fin r ⊕ Fin r → K) := fun j =>
      if j = 0 then ⊥ else if j = 1 then levelSpace (spLev r S) (S.card + 1) else ⊤
    have key := fixes_of_chain hp (mulVecLin_pow_eq_one hMp) U (by simp [U]) 2 (by
      intro j hj v hv
      interval_cases j
      · have hv' : v ∈ levelSpace (K := K) (spLev r S) (S.card + 1) := by simpa [U] using hv
        have : M *ᵥ v = v := hfix v hv'
        simp [U, this]
      · simp only [U] at hv ⊢
        simp only [one_ne_zero, ↓reduceIte]
        rw [mem_levelSpace]
        intro u hu
        rcases u with a | b
        · have : cnt S a ≤ S.card := cnt_le_card S a
          exact absurd hu (by show ¬ S.card + 1 ≤ cnt S a; omega)
        ·
          have hmem : (Pi.single (Sum.inl b) 1 : Fin r ⊕ Fin r → K) ∈
              levelSpace (K := K) (spLev r S) (S.card + 1) := by
            rw [mem_levelSpace]
            intro u hu
            rcases u with a | a
            · have : cnt S a ≤ S.card := cnt_le_card S a
              exact absurd hu (by show ¬ S.card + 1 ≤ cnt S a; omega)
            · exact Pi.single_eq_of_ne (by simp) _
          have h1 := hfix _ hmem
          have h2 := pairedSympForm_spMat_mulVec (g : StatedSp r K)
            (Pi.single (Sum.inl b) 1) v
          rw [show spMat (g : StatedSp r K) *ᵥ (Pi.single (Sum.inl b) 1 : Fin r ⊕ Fin r → K) =
            Pi.single (Sum.inl b) 1 from h1] at h2
          have h3 := SymplecticFlag.pairedSympForm_single_inl (K := K) b (M *ᵥ v - v)
          rw [map_sub, h2, sub_self] at h3
          exact h3.symm)
    intro w
    exact key w (by simp [U])
  have hM1 : M = 1 := by
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
    rw [this]
    simp [Matrix.one_apply, Pi.single_apply]
  exact Subtype.ext (spMat_injective (hM1.trans spMat_one.symm))

theorem false_of_step_escape (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) {p : ℕ} (hp : (p : K) ≠ 0)
    {x : StatedSp r K} (hxp : x ^ p = 1)
    (hfix : ∀ g : StatedSp r K, g * x = x * g → g ∈ Jfl r K S) {ℓ : ℕ} (hℓ : ℓ < S.card)
    (hxJ : x ∈ Jfl r K S) (hx1 : stepHom hS hℓ ⟨x, hxJ⟩ = 1)
    (hne : Nonempty (StepCoord r S ℓ)) : False := by
  obtain ⟨a⟩ := hne
  set M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := spMat x with hM
  have hMp : M ^ p = 1 := by rw [hM, ← spMat_pow, hxp, spMat_one]
  have hbt : M.BlockTriangular (spLev r S) := spMat_blockTriangular hS hxJ
  have hgi : ∀ i ∈ S, x ∈ stabilizer r K (isoFlag r K i) := fun i hi => by
    have := SymplecticHigher.mem_flagStabilizer.mp hxJ i hi
    rwa [flag_eq_isoFlag (hS i hi).2] at this
  have hT : (S.filter (fun j => (a.1 : ℕ) < j)).Nonempty := by
    obtain ⟨i, hiS, hai⟩ := exists_cut_of_cnt_lt_card S (a := a.1) (by rw [a.2]; exact hℓ)
    exact ⟨i, Finset.mem_filter.2 ⟨hiS, hai⟩⟩
  set i := (S.filter (fun j => (a.1 : ℕ) < j)).min' hT with hi
  have hi' := Finset.min'_mem _ hT
  rw [← hi] at hi'
  obtain ⟨hiS, hai⟩ := Finset.mem_filter.1 hi'
  have hmin : ∀ i' ∈ S, (a.1 : ℕ) < i' → i ≤ i' := fun i' hi'S hai' =>
    Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hi'S, hai'⟩)
  set B : Submodule K (Fin r ⊕ Fin r → K) := isoFlag r K i with hB
  set A : Submodule K (Fin r ⊕ Fin r → K) := B ⊓ levelSpace (spLev r S) ℓ with hA
  have hsubB : ∀ b ∈ B, b ∈ levelSpace (K := K) (spLev r S) (ℓ + 1) := by
    intro b hb
    rw [hB, mem_isoFlag] at hb
    rw [mem_levelSpace]
    intro u hu
    rcases u with j | j
    · apply hb.2
      by_contra hji
      push Not at hji
      have hlt : cnt S a.1 < cnt S j := by
        have : spLev r S (Sum.inl j) = cnt S j := rfl
        rw [a.2]; omega
      obtain ⟨i', hi'S, hai', hi'j⟩ := exists_cut_of_cnt_lt S hlt
      have := hmin i' hi'S hai'
      omega
    · exact hb.1 j
  have hblk : ∀ u v, spLev r S u = ℓ → spLev r S v = ℓ → M u v =
      (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) u v := fun u v hu hv =>
    spMat_apply_eq_of_stepHom_eq_one hS hℓ hx1 u v hu hv
  have hstep : ∀ b ∈ B, M.mulVecLin b - b ∈ A := by
    intro b hb
    refine ⟨?_, ?_⟩
    · have h1 : M *ᵥ b ∈ B := spMat_mulVec_mem_of_mem_stabilizer (hgi i hiS) hb
      rw [Matrix.mulVecLin_apply]
      exact B.sub_mem h1 hb
    · rw [Matrix.mulVecLin_apply]
      exact mulVec_sub_mem_levelSpace hbt hblk (hsubB b hb)
  have hb0B : (Pi.single (Sum.inl a.1) 1 : Fin r ⊕ Fin r → K) ∈ B := by
    have := single_mem_flag (K := K) (hS i hiS).2 a.1 a.1.2 hai
    rwa [flag_eq_isoFlag (hS i hiS).2] at this
  have hb0A : (Pi.single (Sum.inl a.1) 1 : Fin r ⊕ Fin r → K) ∉ A := by
    intro hmem
    have := hmem.2 (Sum.inl a.1) (by show ℓ ≤ cnt S a.1; rw [a.2])
    simp at this
  obtain ⟨a0, ha0B, ha0, hga0⟩ := exists_fixed_of_trivial_step hp (mulVecLin_pow_eq_one hMp)
    (inf_le_left : A ≤ B) hstep hb0B hb0A
  have hhi : i ∈ (S : Set ℕ) := hiS
  refine SpResidual.FixedEscape.false_of_fixed_vector_flag hp (I := (S : Set ℕ))
    (fun i hi => hS i hi) hxp hfix hhi ?_ ha0 ?_
  · rw [flag_eq_isoFlag (hS i hiS).2]; exact ha0B
  · rw [← Matrix.mulVecLin_apply]; exact hga0

end Kernel

section Levi

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (leviSp coe_leviSp)

@[expose] noncomputable def reindexGL {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ']
    [DecidableEq κ'] (e : κ ≃ κ') : GL κ K ≃* GL κ' K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K e).toMulEquiv

theorem coe_reindexGL {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (e : κ ≃ κ') (A : GL κ K) :
    ((reindexGL e A : GL κ' K) : Matrix κ' κ' K) = (A : Matrix κ κ K).submatrix e.symm e.symm := rfl

variable {S : Finset ℕ}

@[expose] noncomputable def stepLeviGL (S : Finset ℕ) (ℓ : ℕ) :
    Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord r S ℓ))) K →* GL (Fin r) K :=
  (extendGL (fun a : Fin r => cnt S a = ℓ)).comp
    ((reindexGL (Fintype.equivFin (StepCoord r S ℓ)).symm).toMonoidHom.comp
      Matrix.SpecialLinearGroup.toGL)

theorem stepLeviGL_injective (S : Finset ℕ) (ℓ : ℕ) :
    Function.Injective (stepLeviGL (r := r) (K := K) S ℓ) := by
  intro A B h
  have h1 := extendGL_injective (K := K) (fun a : Fin r => cnt S a = ℓ) h
  have h2 := (reindexGL (K := K) (Fintype.equivFin (StepCoord r S ℓ)).symm).injective h1
  exact Matrix.SpecialLinearGroup.toGL_injective h2

theorem stepLeviGL_support (S : Finset ℕ) (ℓ : ℕ)
    (A : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord r S ℓ))) K) {a b : Fin r}
    (h : ((stepLeviGL S ℓ A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) a b ≠ 0) :
    cnt S a = cnt S b := by
  by_contra hne
  apply h
  have hnn : ¬ (cnt S a = ℓ ∧ cnt S b = ℓ) := fun h' => hne (h'.1.trans h'.2.symm)
  have hab : a ≠ b := fun h' => hne (by rw [h'])
  show extendId (fun a : Fin r => cnt S a = ℓ) _ a b = 0
  rw [extendId_apply_neg _ hnn, Matrix.one_apply_ne hab]

@[expose] noncomputable def stepLevi (S : Finset ℕ) (ℓ : ℕ) :
    Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord r S ℓ))) K →* StatedSp r K :=
  leviSp.comp (stepLeviGL (r := r) (K := K) S ℓ)

theorem stepLevi_injective (S : Finset ℕ) (ℓ : ℕ) :
    Function.Injective (stepLevi (r := r) (K := K) S ℓ) := by
  intro A B h
  have h' := congrArg (fun g : StatedSp r K => ((g : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h
  simp only [stepLevi, MonoidHom.comp_apply, coe_leviSp, Matrix.fromBlocks_inj] at h'
  exact stepLeviGL_injective S ℓ (Units.ext h'.1)

theorem stepLevi_mem (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) (ℓ : ℕ)
    (A : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord r S ℓ))) K) :
    stepLevi S ℓ A ∈ Jfl r K S := by
  apply mem_flagStabilizer_of_blockTriangular hS
  intro u v huv
  rw [stepLevi, MonoidHom.comp_apply]
  show (((leviSp (stepLeviGL S ℓ A) : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) u v = 0
  rw [coe_leviSp]
  have hle := cnt_le_card S
  rcases u with a | a <;> rcases v with b | b
  · have : cnt S b < cnt S a := huv
    simp only [Matrix.fromBlocks_apply₁₁]
    by_contra hne
    have := stepLeviGL_support S ℓ A hne
    omega
  · simp
  · simp
  · have : 2 * S.card - cnt S b < 2 * S.card - cnt S a := huv
    simp only [Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply]
    rw [← map_inv]
    by_contra hne
    have h1 := hle a
    have h2 := hle b
    have := stepLeviGL_support S ℓ A⁻¹ hne
    omega

variable (r) in
@[expose] noncomputable def topLeviEquiv (S : Finset ℕ) :
    Fin (topN r S) ⊕ Fin (topN r S) ≃ {u : Fin r ⊕ Fin r // spLev r S u = S.card} :=
  Equiv.ofBijective (fun w => ⟨topσ r S w, (top_range _).2 ⟨w, rfl⟩⟩)
    ⟨fun a b h => topσ_injective (congrArg Subtype.val h), fun u => by
      obtain ⟨w, hw⟩ := (top_range u.1).1 u.2
      exact ⟨w, Subtype.ext hw⟩⟩

@[expose] noncomputable def topLeviGL (S : Finset ℕ) :
    GL (Fin (topN r S) ⊕ Fin (topN r S)) K →* GL (Fin r ⊕ Fin r) K :=
  (extendGL (fun u : Fin r ⊕ Fin r => spLev r S u = S.card)).comp
    (reindexGL (topLeviEquiv r S)).toMonoidHom

theorem topLeviGL_injective (S : Finset ℕ) : Function.Injective (topLeviGL (r := r) (K := K) S) := by
  intro A B h
  exact (reindexGL (K := K) (topLeviEquiv r S)).injective
    (extendGL_injective (K := K) (fun u : Fin r ⊕ Fin r => spLev r S u = S.card) h)

theorem coe_topLeviGL (S : Finset ℕ) (B : GL (Fin (topN r S) ⊕ Fin (topN r S)) K) :
    ((topLeviGL S B : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      extendId (fun u : Fin r ⊕ Fin r => spLev r S u = S.card)
        ((B : Matrix _ _ K).submatrix (topLeviEquiv r S).symm (topLeviEquiv r S).symm) := rfl

theorem topLeviGL_support (S : Finset ℕ) (B : GL (Fin (topN r S) ⊕ Fin (topN r S)) K)
    {u v : Fin r ⊕ Fin r}
    (h : ((topLeviGL S B : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) u v ≠
      (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) u v) :
    spLev r S u = S.card ∧ spLev r S v = S.card := by
  rw [coe_topLeviGL] at h
  exact extendId_ne_one _ h

theorem topLeviGL_mem_statedSp (S : Finset ℕ) {B : GL (Fin (topN r S) ⊕ Fin (topN r S)) K}
    (hB : B ∈ StatedSp (topN r S) K) : topLeviGL S B ∈ StatedSp r K := by
  rw [SymplecticTorusWeyl.mem_statedSp_iff] at hB ⊢
  rw [coe_topLeviGL]
  set e := topLeviEquiv r S with he
  set Jr : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) K) 1 (-1) 0 with hJr
  have hJs : Jr.submatrix (Subtype.val : {u : Fin r ⊕ Fin r // spLev r S u = S.card} → _)
      Subtype.val = (Matrix.fromBlocks (0 : Matrix (Fin (topN r S)) (Fin (topN r S)) K) 1 (-1) 0).submatrix
        e.symm e.symm := by
    have hσ : ∀ x : {u : Fin r ⊕ Fin r // spLev r S u = S.card}, x.1 = topσ r S (e.symm x) := fun x =>
      (congrArg Subtype.val (e.apply_symm_apply x)).symm
    ext x y
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hσ x, hσ y, ← fromBlocks_submatrix_topσ]
    rfl
  apply extendId_isometry (P := fun u : Fin r ⊕ Fin r => spLev r S u = S.card)
  · intro u v huv
    have := fromBlocks_ne_zero (K := K) (c := u) (d := v) huv
    rcases this with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl⟩
    · have := cnt_le_card S a
      show cnt S a = S.card ↔ 2 * S.card - cnt S a = S.card
      omega
    · have := cnt_le_card S a
      show 2 * S.card - cnt S a = S.card ↔ cnt S a = S.card
      omega
  · rw [hJs]
    have h1 : ((B : Matrix _ _ K).submatrix e.symm e.symm)ᵀ =
        (Bᵀ : Matrix _ _ K).submatrix e.symm e.symm := Matrix.transpose_submatrix _ _ _
    rw [h1, ← Matrix.submatrix_mul _ _ _ _ _ e.symm.bijective,
      ← Matrix.submatrix_mul _ _ _ _ _ e.symm.bijective, hB]

@[expose] noncomputable def topLevi (S : Finset ℕ) :
    ↥(StatedSp (topN r S) K) →* ↥(StatedSp r K) :=
  ((topLeviGL (r := r) (K := K) S).comp (StatedSp (topN r S) K).subtype).codRestrict
    (StatedSp r K) (fun B => topLeviGL_mem_statedSp S B.2)

theorem topLevi_injective (S : Finset ℕ) : Function.Injective (topLevi (r := r) (K := K) S) := by
  intro A B h
  have h' := congrArg Subtype.val h
  exact Subtype.ext (topLeviGL_injective S h')

theorem coe_topLevi (S : Finset ℕ) (B : ↥(StatedSp (topN r S) K)) :
    spMat (topLevi S B) = ((topLeviGL S (B : GL _ K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := rfl

theorem topLevi_mem (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) (B : ↥(StatedSp (topN r S) K)) :
    topLevi S B ∈ Jfl r K S := by
  apply mem_flagStabilizer_of_blockTriangular hS
  intro u v huv
  rw [coe_topLevi]
  by_contra hne
  by_cases h1 : ((topLeviGL S (B : GL _ K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) u v = (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) u v
  · rw [h1] at hne
    have : u = v := by
      by_contra huv'
      exact hne (Matrix.one_apply_ne huv')
    subst this
    exact lt_irrefl _ huv
  · obtain ⟨hu, hv⟩ := topLeviGL_support S _ h1
    rw [hu, hv] at huv
    exact lt_irrefl _ huv

end Levi

section Orders

theorem open_of_isQuasisimple {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q := ⟨Group.isPerfect_def.1 h.1, h.2.1⟩

variable [Finite K]

theorem card_GL_eq_mul_card_SL (n : ℕ) [NeZero n] :
    Nat.card (GL (Fin n) K) = (Nat.card K - 1) * Nat.card (Matrix.SpecialLinearGroup (Fin n) K) := by
  have : Fintype K := Fintype.ofFinite K
  rw [Matrix.card_SL_field, Matrix.card_GL_field, ← Nat.card_eq_fintype_card]
  have hdvd : Nat.card K - 1 ∣ ∏ i : Fin n, (Nat.card K ^ n - Nat.card K ^ (i : ℕ)) := by
    have h0 : (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) :=
      Finset.mem_univ _
    refine (?_ : Nat.card K - 1 ∣ Nat.card K ^ n - Nat.card K ^ ((⟨0, _⟩ : Fin n) : ℕ)).trans
      (Finset.dvd_prod_of_mem (fun i : Fin n => Nat.card K ^ n - Nat.card K ^ (i : ℕ)) h0)
    have := Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 n
    simpa using this
  rw [Nat.mul_div_cancel' hdvd]

theorem not_sq_dvd_card_SL {G : Type*} [Group G] {J : Subgroup G} {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hK : Nat.card K = 2 ∨ 4 ≤ Nat.card K)
    (hA1 : ∀ X : Subgroup G, X ≤ J → CFSG.Open.IsQuasisimple ↥X → ¬ p ^ 2 ∣ Nat.card X) {k : ℕ}
    (φ : Matrix.SpecialLinearGroup (Fin k) K →* G) (hφ : Function.Injective φ)
    (hφJ : ∀ A, φ A ∈ J) : ¬ p ^ 2 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin k) K) := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp2 : 6 < p ^ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  have hq : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin k) K) →
      ¬ p ^ 2 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin k) K) := by
    intro h hd
    have hX : CFSG.Open.IsQuasisimple ↥φ.range :=
      CFSG.ComponentClassification.Components.quasisimple_of_equiv
        (MonoidHom.ofInjective hφ).symm h
    exact hA1 φ.range (by rintro _ ⟨A, rfl⟩; exact hφJ A) hX
      (by rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]; exact hd)
  have : Fintype K := Fintype.ofFinite K
  have hKpos : 2 ≤ Nat.card K := by omega
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k
    ·
      have : Subsingleton (Matrix.SpecialLinearGroup (Fin 0) K) :=
        ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
      rw [Nat.card_of_subsingleton (1 : Matrix.SpecialLinearGroup (Fin 0) K)]
      intro hd
      have := Nat.le_of_dvd one_pos hd
      omega
    ·
      have h1 := Matrix.card_SL_field (𝔽 := K) 1
      rw [← Nat.card_eq_fintype_card] at h1
      simp only [Fin.prod_univ_one, Fin.val_zero, pow_one, pow_zero] at h1
      rw [h1, Nat.div_self (by omega)]
      intro hd
      have := Nat.le_of_dvd one_pos hd
      omega
    ·
      rcases hK with hK2 | hK4
      · have h1 := Matrix.card_SL_field (𝔽 := K) 2
        rw [← Nat.card_eq_fintype_card, hK2] at h1
        simp [Fin.prod_univ_two] at h1
        rw [h1]
        intro hd
        have := Nat.le_of_dvd (by norm_num) hd
        omega
      · exact hq (open_of_isQuasisimple (LieType.HighestRoot.isQuasisimple_SL2_of_four_le hK4))
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact hq (open_of_isQuasisimple (LieType.Universal.SpecialLinear.isQuasisimple m K (by omega)))

theorem not_sq_dvd_card_Sp {G : Type*} [Group G] {J : Subgroup G} {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hK : Nat.card K = 2 ∨ 4 ≤ Nat.card K)
    (hA1 : ∀ X : Subgroup G, X ≤ J → CFSG.Open.IsQuasisimple ↥X → ¬ p ^ 2 ∣ Nat.card X) {m : ℕ}
    (φ : ↥(StatedSp m K) →* G) (hφ : Function.Injective φ) (hφJ : ∀ A, φ A ∈ J) :
    ¬ p ^ 2 ∣ Nat.card ↥(StatedSp m K) := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hq : CFSG.Open.IsQuasisimple ↥(StatedSp m K) → ¬ p ^ 2 ∣ Nat.card ↥(StatedSp m K) := by
    intro h hd
    have hX : CFSG.Open.IsQuasisimple ↥φ.range :=
      CFSG.ComponentClassification.Components.quasisimple_of_equiv
        (MonoidHom.ofInjective hφ).symm h
    exact hA1 φ.range (by rintro _ ⟨A, rfl⟩; exact hφJ A) hX
      (by rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]; exact hd)
  have : Fintype K := Fintype.ofFinite K
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h1 : Nat.card ↥(StatedSp 0 K) = 1 := by
      rw [SymplecticFlag.card_statedSp]; simp
    rw [h1]
    intro hd
    have := Nat.le_of_dvd one_pos hd
    rcases hp57 with rfl | rfl <;> omega
  · by_cases hbig : 4 ≤ Nat.card K ∨ (Nat.card K = 2 ∧ 3 ≤ m)
    · refine hq (open_of_isQuasisimple (LieType.Universal.Symplectic.isQuasisimple m K hm ?_))
      rcases hbig with h4 | h2
      · exact Or.inl (Or.inr h4)
      · exact Or.inr (Or.inr h2)
    · push Not at hbig
      have hK2 : Nat.card K = 2 := by omega
      have hm2 : m < 3 := hbig.2 hK2
      interval_cases m
      · intro hd
        rw [SymplecticFlag.card_statedSp, hK2] at hd
        norm_num [Finset.prod_Icc_succ_top] at hd
        have := Nat.le_of_dvd (by norm_num) hd
        rcases hp57 with rfl | rfl <;> omega
      · intro hd
        rw [SymplecticFlag.card_statedSp, hK2] at hd
        norm_num [Finset.prod_Icc_succ_top] at hd
        rcases hp57 with rfl | rfl <;> omega

end Orders

section Nonsplit

variable [Finite K] {S : Finset ℕ}

@[expose] def BlockTy (r : ℕ) (K : Type) [Field K] (S : Finset ℕ) : Fin S.card ⊕ Unit → Type
  | Sum.inl ℓ => GL (StepCoord r S ℓ) K
  | Sum.inr _ => ↥(StatedSp (topN r S) K)

noncomputable instance instGroupBlockTy {S : Finset ℕ} : ∀ i : Fin S.card ⊕ Unit,
    Group (BlockTy r K S i)
  | Sum.inl _ => inferInstanceAs (Group (GL _ K))
  | Sum.inr _ => inferInstanceAs (Group ↥(StatedSp _ K))

instance instFiniteBlockTy {S : Finset ℕ} : ∀ i : Fin S.card ⊕ Unit, Finite (BlockTy r K S i)
  | Sum.inl _ => inferInstanceAs (Finite (GL _ K))
  | Sum.inr _ => inferInstanceAs (Finite ↥(StatedSp _ K))

@[expose] noncomputable def blockHom (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) :
    ∀ i : Fin S.card ⊕ Unit, ↥(Jfl r K S) →* BlockTy r K S i
  | Sum.inl ℓ => stepHom hS ℓ.2
  | Sum.inr _ => topHom hS

omit [Finite K] in
theorem pCast_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K 2] : (p : K) ≠ 0 := by
  intro h
  have := (CharP.cast_eq_zero_iff K 2 p).1 h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm

@[expose] noncomputable def spFlagBlocks (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) {p : ℕ}
    (hp0 : (p : K) ≠ 0) : FlagBlocks p ↥(Jfl r K S) :=
  { ι := Fin S.card ⊕ Unit
    H := BlockTy r K S
    grp := instGroupBlockTy (S := S)
    ρ := blockHom hS
    inj_of_pow := fun _ he hall => eq_one_of_blocks_trivial hS hp0 he
      (fun ℓ hℓ => hall (Sum.inl ⟨ℓ, hℓ⟩)) (hall (Sum.inr ())) }

omit [Finite K] in
theorem card_GL_congr {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (e : κ ≃ κ') : Nat.card (GL κ K) = Nat.card (GL κ' K) :=
  Nat.card_congr (reindexGL e).toEquiv

theorem not_sq_dvd_card_step {p : ℕ} (hp57 : p = 5 ∨ p = 7) (hK : Nat.card K = 2 ∨ 4 ≤ Nat.card K)
    (hpq : ¬ p ∣ Nat.card K - 1) {S : Finset ℕ} (ℓ : ℕ)
    (hA1 : ∀ X : Subgroup (StatedSp r K), X ≤ Jfl r K S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X) (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) :
    ¬ p ^ 2 ∣ Nat.card (GL (StepCoord r S ℓ) K) := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  rw [card_GL_congr (Fintype.equivFin (StepCoord r S ℓ))]
  set k := Fintype.card (StepCoord r S ℓ) with hk
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0]
    have : Subsingleton (GL (Fin 0) K) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    rw [Nat.card_of_subsingleton (1 : GL (Fin 0) K)]
    intro hd
    have := Nat.le_of_dvd one_pos hd
    rcases hp57 with rfl | rfl <;> omega
  · have : NeZero k := ⟨hpos.ne'⟩
    rw [card_GL_eq_mul_card_SL]
    intro hd
    have hcop : Nat.Coprime (p ^ 2) (Nat.card K - 1) :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq)
    exact not_sq_dvd_card_SL hp57 hK hA1 (stepLevi S ℓ) (stepLevi_injective S ℓ)
      (stepLevi_mem hS ℓ) (hcop.dvd_of_dvd_mul_left hd)

theorem false_of_nonsplit [CharP K 2] {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hK : Nat.card K = 2 ∨ 4 ≤ Nat.card K) (hpq : ¬ p ∣ Nat.card K - 1) {S : Finset ℕ}
    (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r)
    (hA1 : ∀ X : Subgroup (StatedSp r K), X ≤ Jfl r K S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X)
    {x : StatedSp r K} (hxp : x ^ p = 1)
    (hfix : ∀ g : StatedSp r K, g * x = x * g → g ∈ Jfl r K S)
    {V E : Subgroup (StatedSp r K)} (hVJ : V ≤ Jfl r K S)
    (hVx : V ≤ Subgroup.centralizer ({x} : Set (StatedSp r K))) (hV : ⁅V, V⁆ = V) (hEV : E ≤ V)
    (hEel : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) : False := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  have hp0 : (p : K) ≠ 0 := pCast_ne_zero hp hp2
  have hxJ : x ∈ Jfl r K S := hfix x rfl
  set J := Jfl r K S with hJ
  let B : FlagBlocks p ↥J := spFlagBlocks hS hp0
  have hBfin : ∀ i, Finite (B.H i) := fun i => instFiniteBlockTy (S := S) i
  have hE' : ∀ e ∈ E.subgroupOf J, e ^ p = 1 := fun e he => Subtype.ext (by
    have := hEel.2 _ (Subgroup.mem_subgroupOf.1 he)
    simpa using this)
  have hH : ∀ i, ¬ p ^ 2 ∣ Nat.card (B.H i) := by
    intro i
    rcases i with ℓ | _
    · exact not_sq_dvd_card_step hp57 hK hpq ℓ.1 hA1 hS
    · exact not_sq_dvd_card_Sp hp57 hK hA1 (topLevi S) (topLevi_injective S) (topLevi_mem hS)
  have hEc' : p ^ 2 ≤ Nat.card (E.subgroupOf J) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEV.trans hVJ)).toEquiv, hEc]
  have hxV : ∀ v ∈ V.subgroupOf J, v * (⟨x, hxJ⟩ : ↥J) = ⟨x, hxJ⟩ * v := by
    intro v hv
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.1 (hVx (Subgroup.mem_subgroupOf.1 hv)) x
      (Set.mem_singleton x)
    exact this.symm
  refine B.false_of_nonsplit hp hH (fun i => i = Sum.inr ()) (fun i j hi hj => hi.trans hj.symm)
    (commutator_subgroupOf_eq hVJ hV)
    (fun e he => Subgroup.mem_subgroupOf.2 (hEV (Subgroup.mem_subgroupOf.1 he))) hE' hEc'
    (x := ⟨x, hxJ⟩) (Subtype.ext (by simpa using hxp)) hxV ?_
  intro i hi hx1 hdvd
  rcases i with ℓ | u
  · by_cases hne : Nonempty (StepCoord r S ℓ)
    · exact false_of_step_escape hS hp0 hxp hfix ℓ.2 hxJ hx1 hne
    · have hempty : IsEmpty (StepCoord r S ℓ) := not_nonempty_iff.1 hne
      have hsub : Subsingleton (GL (StepCoord r S ℓ) K) :=
        ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
      have hsub' : Subsingleton ↥((V.subgroupOf J).map (stepHom hS ℓ.2)) :=
        ⟨fun a b => Subtype.ext (Subsingleton.elim (α := GL (StepCoord r S ℓ) K) _ _)⟩
      have hdvd' : p ∣ Nat.card ↥((V.subgroupOf J).map (stepHom hS ℓ.2)) := hdvd
      rw [Nat.card_of_subsingleton (1 : ↥((V.subgroupOf J).map (stepHom hS ℓ.2)))] at hdvd'
      have := Nat.le_of_dvd one_pos hdvd'
      rcases hp57 with rfl | rfl <;> omega
  · exact absurd rfl hi

end Nonsplit

section Reduction

open CFSG.QuasithinUnique CFSG.AGLEmbedding

theorem exists_model_b {G : Type} [Group G] (hX : IsLieOf IdxB G) :
    ∃ (r : ℕ) (K : Type) (_ : Field K), Finite K ∧ CharP K 2 ∧ 2 ≤ r ∧
      (Nat.card K = 2 ∨ 4 ≤ Nat.card K) ∧ Nonempty (G ≃* StatedSp r K) := by
  obtain ⟨⟨d, hv⟩, hPd, ⟨e⟩⟩ := hX
  cases d with
  | B r q =>
    have hq2 : q.p = 2 := hPd
    have hr : 2 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1 |>.1
    have hmodel : StatedClassicalModel G .PSp r 2 q.exponent := by
      by_cases h2 : r = 2
      · subst h2
        have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
        rwa [hq2] at hm
      · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2
          (by omega) e
        rwa [hq2] at hm
    obtain ⟨-, K, hK, hKfin, hcard, ⟨e'⟩⟩ := hmodel
    have hf1 : 1 ≤ q.exponent := q.exponent_pos
    have hchar : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf1
        hcard
    have : NeZero r := ⟨by omega⟩
    have hbij := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.even_symplectic_semilinear_normal_form
      (r := r) (K := K) hf1 hcard).1
    let π : StatedSp r K ≃* StatedProj (StatedSp r K) := MulEquiv.ofBijective _ hbij
    refine ⟨r, K, hK, hKfin, hchar, hr, ?_, ⟨e'.trans π.symm⟩⟩
    rw [hcard]
    rcases Nat.eq_or_lt_of_le hf1 with h1 | h2
    · left; rw [← h1]; norm_num
    · right
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h2
  | _ => exact hPd.elim

end Reduction

section Conj

variable [Finite K] [CharP K 2]

theorem exists_conj_flagStabilizer {J : Subgroup (StatedSp r K)}
    (hT : ∃ T : Subgroup (StatedSp r K), IsSylowTwoOf T ⊤ ∧
      Subgroup.normalizer (T : Set (StatedSp r K)) ≤ J) :
    ∃ (c : StatedSp r K ≃* StatedSp r K) (S : Finset ℕ), (∀ i ∈ S, 1 ≤ i ∧ i ≤ r) ∧
      J.map c.toMonoidHom = Jfl r K S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hNJ⟩ := hT
  have hidx : ¬ 2 ∣ T.index := by
    have h2 := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h2
  let T' : Sylow 2 (StatedSp r K) := hT.2.1.toSylow hidx
  obtain ⟨U, hU⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 r
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (StatedSp r K) U T'
  have hTx : T = (SymplecticFlag.unipotent r K).map (MulAut.conj x).toMonoidHom := by
    have h1 : ((x • U : Sylow 2 (StatedSp r K)) : Subgroup (StatedSp r K)) = T := by
      rw [hx]; rfl
    rw [← h1, Sylow.coe_subgroup_smul, hU]
    rfl
  let e : StatedSp r K ≃* StatedSp r K := MulAut.conj x⁻¹
  have heT : T.map e.toMonoidHom = SymplecticFlag.unipotent r K := by
    rw [hTx, Subgroup.map_map]
    have : e.toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id _ := by
      refine MonoidHom.ext fun z => ?_
      show x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z
      group
    rw [this, Subgroup.map_id]
  have hbij : Function.Bijective e.toMonoidHom := e.bijective
  have hNmap : (Subgroup.normalizer (T : Set (StatedSp r K))).map e.toMonoidHom =
      SymplecticFlag.borelSubgroup r K := by
    rw [Subgroup.map_normalizer_eq_of_bijective T hbij, heT]
    exact SymplecticHigher.normalizer_unipotent
  have hB : SymplecticFlag.borelSubgroup r K ≤ J.map e.toMonoidHom := by
    rw [← hNmap]
    exact Subgroup.map_mono hNJ
  obtain ⟨I, hI, hJ'⟩ : ∃ I : Set ℕ, (∀ i ∈ I, 1 ≤ i ∧ i ≤ r) ∧
      J.map e.toMonoidHom = flagStabilizer r K I :=
    ⟨SymplecticHigher.borelCuts K (J.map e.toMonoidHom),
      SymplecticHigher.borelCuts_le _, (SymplecticHigher.borel_overgroups _ hB).1⟩
  have hfin : I.Finite := (Set.finite_Icc 1 r).subset fun i hi => ⟨(hI i hi).1, (hI i hi).2⟩
  refine ⟨e, hfin.toFinset, fun i hi => hI i (hfin.mem_toFinset.1 hi), ?_⟩
  rw [hJ']
  simp [Jfl]

end Conj

section Main

open CFSG.AGLEmbedding

@[expose] def SpSplitCell : Prop :=
  ∀ (r : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), (p = 5 ∨ p = 7) →
    (Nat.card K = 2 ∨ 4 ≤ Nat.card K) → p ∣ Nat.card K - 1 → ∀ (S : Finset ℕ),
    (∀ i ∈ S, 1 ≤ i ∧ i ≤ r) →
    (∀ X : Subgroup (StatedSp r K), X ≤ Jfl r K S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X) →
    (∀ X₁ X₂ : Subgroup (StatedSp r K), X₁ ≤ Jfl r K S → X₂ ≤ Jfl r K S →
      CFSG.Open.IsQuasisimple ↥X₁ → CFSG.Open.IsQuasisimple ↥X₂ →
      X₂ ≤ Subgroup.centralizer (X₁ : Set (StatedSp r K)) → p ∣ Nat.card X₁ →
      p ∣ Nat.card X₂ → CFSG.AGLEmbedding.LieOut.NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) →
      CFSG.AGLEmbedding.LieOut.NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False) →
    ∀ x : StatedSp r K, x ^ p = 1 → (∀ g : StatedSp r K, g * x = x * g → g ∈ Jfl r K S) →
    ∀ V E : Subgroup (StatedSp r K), V ≤ Jfl r K S →
      V ≤ Subgroup.centralizer ({x} : Set (StatedSp r K)) → ⁅V, V⁆ = V → E ≤ V →
      IsElemAbelian p E → Nat.card E = p ^ 2 → False

theorem altIbBarCell_b_of_split (hsplit : SpSplitCell) : AltIbBarCell (IsLieOf IdxB) := by
  intro G _ _ hX Jb hsyl hJtop p hp57 a1 a2 x hxp hfix V E hVJ hVx hV hEV hEel hEc
  obtain ⟨r, K, _, hfin, hchar, hr, hK, ⟨ee⟩⟩ := exists_model_b hX
  have : Finite K := hfin
  have : CharP K 2 := hchar
  obtain ⟨T, hT, hNT⟩ := hsyl
  have hT' : ∃ T' : Subgroup (StatedSp r K), IsSylowTwoOf T' ⊤ ∧
      Subgroup.normalizer (T' : Set (StatedSp r K)) ≤ Jb.map ee.toMonoidHom := by
    refine ⟨T.map ee.toMonoidHom, ⟨le_top, hT.2.1.map _, ?_⟩, ?_⟩
    · have h2 := hT.2.2
      rw [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h2
      have h3 : (T.map ee.toMonoidHom).index = T.index := Subgroup.index_map_equiv T ee
      rw [show ((T.map ee.toMonoidHom).subgroupOf ⊤).index = (T.map ee.toMonoidHom).index from
        Subgroup.relIndex_top_right _, h3]
      exact h2
    · rw [← Subgroup.map_normalizer_eq_of_bijective T ee.bijective]
      exact Subgroup.map_mono hNT
  obtain ⟨c, S, hS, hc⟩ := exists_conj_flagStabilizer hT'
  set θ : G ≃* StatedSp r K := ee.trans c with hθdef
  have hθ : Jb.map θ.toMonoidHom = Jfl r K S := by
    rw [← hc, Subgroup.map_map]
    rfl
  have hA1 := transport_a1 θ a1
  have hA2 := transport_a2 θ a2
  rw [hθ] at hA1 hA2
  have hxp' : (θ x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have hfix' : ∀ g : StatedSp r K, g * θ x = θ x * g → g ∈ Jfl r K S := by
    intro g hg
    have : θ.symm g * x = x * θ.symm g := by
      apply θ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hg
    rw [← hθ]
    exact ⟨θ.symm g, hfix _ this, by simp⟩
  have hVJ' : V.map θ.toMonoidHom ≤ Jfl r K S := by
    rw [← hθ]; exact Subgroup.map_mono hVJ
  have hVx' : V.map θ.toMonoidHom ≤ Subgroup.centralizer ({θ x} : Set (StatedSp r K)) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    show θ x * θ v = θ v * θ x
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 (hVx hv) x (Set.mem_singleton x))]
  have hV' : ⁅V.map θ.toMonoidHom, V.map θ.toMonoidHom⁆ = V.map θ.toMonoidHom := by
    rw [← Subgroup.map_commutator, hV]
  have hEc' : Nat.card (E.map θ.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective θ.injective, hEc]
  by_cases hpq : p ∣ Nat.card K - 1
  · exact hsplit r K p hp57 hK hpq S hS hA1 hA2 (θ x) hxp' hfix' _ _ hVJ' hVx' hV'
      (Subgroup.map_mono hEV) (isElemAbelian_map θ hEel) hEc'
  · exact false_of_nonsplit hp57 hK hpq hS hA1 hxp' hfix' hVJ' hVx' hV' (Subgroup.map_mono hEV)
      (isElemAbelian_map θ hEel) hEc'

end Main

section Split

variable [Finite K]

theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 5)
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 5)), Fintype.card_perm,
    Fintype.card_fin] at h
  have h5 : (5 : ℕ).factorial = 120 := by decide
  rw [h5] at h
  omega

theorem card_alt_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 7)
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 7)), Fintype.card_perm,
    Fintype.card_fin] at h
  have h7 : (7 : ℕ).factorial = 5040 := by decide
  rw [h7] at h
  omega

theorem card_SL2_eq : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
    Nat.card K * (Nat.card K ^ 2 - 1) := by
  have : Fintype K := Fintype.ofFinite K
  have h := Matrix.card_SL_field (𝔽 := K) 2
  rw [← Nat.card_eq_fintype_card] at h
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  rw [h]
  have hq : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  obtain ⟨a, ha⟩ : ∃ a, Nat.card K = a + 1 := ⟨Nat.card K - 1, by omega⟩
  rw [ha]
  apply Nat.div_eq_of_eq_mul_left (by omega)
  have h1 : (a + 1) ^ 2 - 1 = a * (a + 2) := by
    have : (a + 1) ^ 2 = a * (a + 2) + 1 := by ring
    omega
  have h2 : (a + 1) ^ 2 - (a + 1) = (a + 1) * a := by
    have : (a + 1) ^ 2 = (a + 1) * a + (a + 1) := by ring
    omega
  rw [h1, h2]
  have : a + 1 - 1 = a := by omega
  rw [this]
  ring

theorem noAp_sl2 [CharP K 2] {p : ℕ} (hp57 : p = 5 ∨ p = 7) (hpq : p ∣ Nat.card K - 1) :
    NoAp p (Matrix.SpecialLinearGroup (Fin 2) K ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) := by
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
    have hz : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) = 1 := by
      rw [CFSG.AGLEmbedding.ParabPrime.sl2_center_eq_bot (k := K), Subgroup.card_bot]
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
    rw [hz, mul_one, card_SL2_eq] at h
    exact h.symm
  have hf' : ∃ f : ℕ, Nat.card K = 2 ^ f := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨m, -, hm⟩ := FiniteField.card (K := K) 2
    exact ⟨m, by rw [Nat.card_eq_fintype_card]; exact hm⟩
  obtain ⟨f, hf⟩ := hf'
  have hq2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  rw [hf] at hq2 hpq
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0] at hq2; norm_num at hq2
    · exact h0
  rcases Nat.lt_or_ge f 4 with hf4 | hf4
  ·
    interval_cases f
    · rcases hp57 with rfl | rfl <;> norm_num at hpq
    · rcases hp57 with rfl | rfl <;> norm_num at hpq
    · rcases hp57 with rfl | rfl
      · norm_num at hpq
      · exact noAp_seven_of_card_eq (by rw [hcard, hf]; norm_num)
  · have h16 : 16 ≤ 2 ^ f := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf4
    refine NoAp.of_card_lt ?_
    rw [hcard, hf]
    have hbig : 4080 ≤ 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
      have h1 : 16 * (16 ^ 2 - 1) ≤ 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
        Nat.mul_le_mul h16 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h16 2) 1)
      simpa using h1
    rcases hp57 with rfl | rfl
    · rw [card_alt_five]; omega
    · rw [card_alt_seven]; omega

end Split

section SplitBounds

variable [Finite K]

theorem sub_one_dvd_pow_sub_pow_self {q : ℕ} (hq : 0 < q) (i k : ℕ) (hi : i ≤ k) :
    q - 1 ∣ q ^ k - q ^ i := by
  have h1 := Nat.sub_dvd_pow_sub_pow q 1 k
  have h2 := Nat.sub_dvd_pow_sub_pow q 1 i
  simp only [one_pow] at h1 h2
  have h3 := Nat.dvd_sub h1 h2
  have hle : q ^ i ≤ q ^ k := Nat.pow_le_pow_right hq hi
  have hpos : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
  have : q ^ k - 1 - (q ^ i - 1) = q ^ k - q ^ i := by omega
  rwa [this] at h3

theorem pow_dvd_card_SL (k : ℕ) (hk : 1 ≤ k) :
    (Nat.card K - 1) ^ (k - 1) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin k) K) := by
  have : Fintype K := Fintype.ofFinite K
  have : NeZero k := ⟨by omega⟩
  have hq : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have h := Matrix.card_SL_field (𝔽 := K) k
  rw [← Nat.card_eq_fintype_card] at h
  rw [h]
  have hdvd : (Nat.card K - 1) ^ k ∣ ∏ i : Fin k, (Nat.card K ^ k - Nat.card K ^ (i : ℕ)) := by
    have := Finset.prod_dvd_prod_of_dvd (s := (Finset.univ : Finset (Fin k)))
      (fun _ => Nat.card K - 1) (fun i : Fin k => Nat.card K ^ k - Nat.card K ^ (i : ℕ))
      (fun i _ => sub_one_dvd_pow_sub_pow_self (by omega) _ _ (by omega))
    simpa [Finset.prod_const] using this
  obtain ⟨c, hc⟩ := hdvd
  rw [hc]
  have hk' : k = (k - 1) + 1 := by omega
  have hpos : 0 < Nat.card K - 1 := by omega
  rw [hk', pow_succ, mul_assoc]
  rw [show (Nat.card K - 1) ^ (k - 1) * ((Nat.card K - 1) * c) =
      (Nat.card K - 1) * ((Nat.card K - 1) ^ (k - 1) * c) by ring, Nat.mul_div_cancel_left _ hpos]
  simp only [Nat.add_sub_cancel]
  exact Dvd.intro _ rfl

theorem pow_dvd_card_Sp (m : ℕ) : (Nat.card K - 1) ^ m ∣ Nat.card (StatedSp m K) := by
  have : Fintype K := Fintype.ofFinite K
  have hq : 0 < Nat.card K := Nat.card_pos
  rw [SymplecticFlag.card_statedSp]
  refine Dvd.dvd.mul_left ?_ _
  have := Finset.prod_dvd_prod_of_dvd (s := Finset.Icc 1 m)
    (fun _ => Nat.card K - 1) (fun j : ℕ => Nat.card K ^ (2 * j) - 1)
    (fun j _ => by
      have := Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 (2 * j)
      simpa using this)
  simpa [Finset.prod_const] using this

end SplitBounds

section SplitSizes

variable [Finite K] {S : Finset ℕ}

theorem step_card_le_two {p : ℕ} (hp57 : p = 5 ∨ p = 7) (hK : Nat.card K = 2 ∨ 4 ≤ Nat.card K)
    (hpq : p ∣ Nat.card K - 1) (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r)
    (hA1 : ∀ X : Subgroup (StatedSp r K), X ≤ Jfl r K S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X) (ℓ : ℕ) : Fintype.card (StepCoord r S ℓ) ≤ 2 := by
  by_contra hk
  push Not at hk
  refine not_sq_dvd_card_SL hp57 hK hA1 (stepLevi S ℓ) (stepLevi_injective S ℓ)
    (stepLevi_mem hS ℓ) ?_
  have h1 := pow_dvd_card_SL (K := K) (Fintype.card (StepCoord r S ℓ)) (by omega)
  exact ((pow_dvd_pow_of_dvd hpq 2).trans (pow_dvd_pow _ (by omega))).trans h1

theorem topN_le_one {p : ℕ} (hp57 : p = 5 ∨ p = 7) (hK : Nat.card K = 2 ∨ 4 ≤ Nat.card K)
    (hpq : p ∣ Nat.card K - 1) (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r)
    (hA1 : ∀ X : Subgroup (StatedSp r K), X ≤ Jfl r K S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X) : topN r S ≤ 1 := by
  by_contra hm
  push Not at hm
  refine not_sq_dvd_card_Sp hp57 hK hA1 (topLevi S) (topLevi_injective S) (topLevi_mem hS) ?_
  exact ((pow_dvd_pow_of_dvd hpq 2).trans (pow_dvd_pow _ (by omega))).trans
    (pow_dvd_card_Sp (K := K) (topN r S))

end SplitSizes

section SplitCyclic

variable [Finite K]

omit [Finite K] in
theorem gl_comm_of_card_eq_one {κ : Type} [Fintype κ] [DecidableEq κ] (hk : Fintype.card κ = 1)
    (a b : GL κ K) : a * b = b * a := by
  obtain ⟨hu⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 hk
  apply Units.ext
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  exact mul_comm _ _

end SplitCyclic

section SplitCyclic2

variable [Finite K]

omit [Finite K] in
theorem le_ker_det_of_perfect {κ : Type} [Fintype κ] [DecidableEq κ] {P : Subgroup (GL κ K)}
    (hP : ⁅P, P⁆ = P) : P ≤ (Matrix.GeneralLinearGroup.det (n := κ) (R := K)).ker := by
  rw [← hP, Subgroup.commutator_le]
  intro g _ h _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def]
  simp

theorem isCyclic_of_perfect_gl [CharP K 2] {κ : Type} [Fintype κ] [DecidableEq κ]
    (hk : Fintype.card κ ≤ 2) (hK : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup (GL κ K)} (hP : ⁅P, P⁆ = P) {Q : Subgroup (GL κ K)} (hQP : Q ≤ P)
    (hQ : IsPGroup p Q) : IsCyclic Q := by
  have : Fact p.Prime := ⟨hp⟩
  rcases Nat.lt_or_ge (Fintype.card κ) 2 with hlt | hge
  · rcases Nat.lt_or_ge (Fintype.card κ) 1 with h0 | h1
    · have h0' : Fintype.card κ = 0 := by omega
      have : IsEmpty κ := Fintype.card_eq_zero_iff.1 h0'
      have : Subsingleton (GL κ K) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
      have : Subsingleton Q := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
      infer_instance
    · have h1' : Fintype.card κ = 1 := by omega
      have hPbot : P = ⊥ := by
        rw [← hP, eq_bot_iff, Subgroup.commutator_le]
        intro g _ h _
        rw [Subgroup.mem_bot, commutatorElement_def]
        simp [gl_comm_of_card_eq_one h1' g h]
      have : Q = ⊥ := eq_bot_iff.2 (hPbot ▸ hQP)
      rw [this]
      infer_instance
  · have h2 : Fintype.card κ = 2 := by omega
    set e : Fin 2 ≃ κ := (Fintype.equivFinOfCardEq h2).symm with he
    let ψ : Matrix.SpecialLinearGroup (Fin 2) K →* GL κ K :=
      (reindexGL e).toMonoidHom.comp Matrix.SpecialLinearGroup.toGL
    have hker : P ≤ ψ.range := by
      intro g hg
      have hdet : (g : Matrix κ κ K).det = 1 := by
        have := le_ker_det_of_perfect hP hg
        rw [MonoidHom.mem_ker] at this
        have h' := congrArg Units.val this
        simpa [Matrix.GeneralLinearGroup.det] using h'
      refine ⟨⟨(g : Matrix κ κ K).submatrix e e, ?_⟩, ?_⟩
      · rw [← hdet]
        exact Matrix.det_submatrix_equiv_self e _
      · apply Units.ext
        ext i j
        show ((g : Matrix κ κ K).submatrix e e) (e.symm i) (e.symm j) = (g : Matrix κ κ K) i j
        simp
    exact isCyclic_of_le_range ψ (sylow_isCyclic_sl2 hK hp hp2) (hQP.trans hker) hQ

end SplitCyclic2

section SplitTop

variable [Finite K]

theorem isCyclic_of_pGroup_statedSp [CharP K 2] {m : ℕ} (hm : m ≤ 1) (hK : 4 ≤ Nat.card K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup (StatedSp m K)} (hQ : IsPGroup p Q) :
    IsCyclic Q := by
  have : Fact p.Prime := ⟨hp⟩
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · have : Subsingleton (StatedSp 0 K) :=
      ⟨fun a b => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
    have : Subsingleton Q := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    infer_instance
  · obtain rfl : m = 1 := le_antisymm hm hpos
    exact isCyclic_of_le_range (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).toMonoidHom
      (sylow_isCyclic_sl2 hK hp hp2)
      (by intro g _; exact ⟨_, ((CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).apply_symm_apply g)⟩) hQ

end SplitTop

section SplitLevi

variable [Finite K]

omit [Finite K] in
theorem perfect_eq_bot_of_card_le_one {κ : Type} [Fintype κ] [DecidableEq κ]
    (hk : Fintype.card κ ≤ 1) {P : Subgroup (GL κ K)} (hP : ⁅P, P⁆ = P) : P = ⊥ := by
  rcases Nat.lt_or_ge (Fintype.card κ) 1 with h0 | h1
  · have h0' : Fintype.card κ = 0 := by omega
    have : IsEmpty κ := Fintype.card_eq_zero_iff.1 h0'
    have : Subsingleton (GL κ K) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    exact Subsingleton.elim _ _
  · have h1' : Fintype.card κ = 1 := by omega
    rw [← hP, eq_bot_iff, Subgroup.commutator_le]
    intro g _ h _
    rw [Subgroup.mem_bot, commutatorElement_def]
    simp [gl_comm_of_card_eq_one h1' g h]

theorem levi_data_sl2 [CharP K 2] {G : Type} [Group G] {J : Subgroup G} {p : ℕ}
    (hp57 : p = 5 ∨ p = 7) (hK : Nat.card K = 2 ∨ 4 ≤ Nat.card K) (hpq : p ∣ Nat.card K - 1)
    {k : ℕ} (hk : k = 2) (φ : Matrix.SpecialLinearGroup (Fin k) K →* G)
    (hφ : Function.Injective φ) (hφJ : ∀ A, φ A ∈ J) :
    φ.range ≤ J ∧ CFSG.Open.IsQuasisimple ↥φ.range ∧ p ∣ Nat.card φ.range ∧
      NoAp p (↥φ.range ⧸ Subgroup.center ↥φ.range) := by
  subst hk
  have hK4 : 4 ≤ Nat.card K := by
    rcases hK with h2 | h4
    · rw [h2] at hpq
      have : p ≤ 1 := Nat.le_of_dvd one_pos (by simpa using hpq)
      rcases hp57 with rfl | rfl <;> omega
    · exact h4
  have e := (MonoidHom.ofInjective hφ)
  refine ⟨by rintro _ ⟨A, rfl⟩; exact hφJ A, ?_, ?_, ?_⟩
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm
      (open_of_isQuasisimple (LieType.HighestRoot.isQuasisimple_SL2_of_four_le hK4))
  · rw [← Nat.card_congr e.toEquiv, card_SL2_eq]
    refine Dvd.dvd.mul_left ?_ _
    have hq1 : Nat.card K - 1 ∣ Nat.card K ^ 2 - 1 := by
      have := Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 2
      simpa using this
    exact hpq.trans hq1
  · exact noAp_center_quotient_of_surjective e.symm.toMonoidHom (MulEquiv.surjective _)
      (noAp_sl2 hp57 hpq)

theorem levi_data_sp1 [CharP K 2] {G : Type} [Group G] {J : Subgroup G} {p : ℕ}
    (hp57 : p = 5 ∨ p = 7) (hK : Nat.card K = 2 ∨ 4 ≤ Nat.card K) (hpq : p ∣ Nat.card K - 1)
    {m : ℕ} (hm : m = 1) (φ : ↥(StatedSp m K) →* G) (hφ : Function.Injective φ)
    (hφJ : ∀ A, φ A ∈ J) :
    φ.range ≤ J ∧ CFSG.Open.IsQuasisimple ↥φ.range ∧ p ∣ Nat.card φ.range ∧
      NoAp p (↥φ.range ⧸ Subgroup.center ↥φ.range) := by
  subst hm
  have hK4 : 4 ≤ Nat.card K := by
    rcases hK with h2 | h4
    · rw [h2] at hpq
      have : p ≤ 1 := Nat.le_of_dvd one_pos (by simpa using hpq)
      rcases hp57 with rfl | rfl <;> omega
    · exact h4
  have e := (MonoidHom.ofInjective hφ)
  have eSL := CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K
  refine ⟨by rintro _ ⟨A, rfl⟩; exact hφJ A, ?_, ?_, ?_⟩
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm
      (open_of_isQuasisimple (LieType.Universal.Symplectic.isQuasisimple 1 K le_rfl
        (Or.inl (Or.inr hK4))))
  · rw [← Nat.card_congr e.toEquiv, ← Nat.card_congr eSL.toEquiv, card_SL2_eq]
    refine Dvd.dvd.mul_left ?_ _
    have hq1 : Nat.card K - 1 ∣ Nat.card K ^ 2 - 1 := by
      have := Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 2
      simpa using this
    exact hpq.trans hq1
  · exact noAp_center_quotient_of_surjective e.symm.toMonoidHom (MulEquiv.surjective _)
      (noAp_center_quotient_of_surjective eSL.symm.toMonoidHom (MulEquiv.surjective _)
        (noAp_sl2 hp57 hpq))

end SplitLevi

section SplitCommute

variable {S : Finset ℕ}

theorem stepLeviGL_ne_one (S : Finset ℕ) (ℓ : ℕ)
    (A : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord r S ℓ))) K) {a b : Fin r}
    (h : ((stepLeviGL S ℓ A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) a b ≠
      (1 : Matrix (Fin r) (Fin r) K) a b) : cnt S a = ℓ ∧ cnt S b = ℓ := by
  have h' : extendId (fun a : Fin r => cnt S a = ℓ) _ a b ≠ (1 : Matrix (Fin r) (Fin r) K) a b := h
  exact extendId_ne_one _ h'

theorem stepLevi_supp (S : Finset ℕ) (ℓ : ℕ)
    (A : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord r S ℓ))) K)
    (u v : Fin r ⊕ Fin r)
    (h : spMat (stepLevi S ℓ A) u v ≠ (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) u v) :
    (spLev r S u = ℓ ∨ spLev r S u = 2 * S.card - ℓ) ∧
      (spLev r S v = ℓ ∨ spLev r S v = 2 * S.card - ℓ) := by
  have hm : spMat (stepLevi S ℓ A) = Matrix.fromBlocks
      ((stepLeviGL S ℓ A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) 0 0
      (((stepLeviGL S ℓ A)⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ := by
    rw [stepLevi, MonoidHom.comp_apply]
    exact CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.coe_leviSp _
  rw [hm] at h
  rcases u with a | a <;> rcases v with b | b
  · simp only [Matrix.fromBlocks_apply₁₁] at h
    have h1 : ((stepLeviGL S ℓ A : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) a b ≠
        (1 : Matrix (Fin r) (Fin r) K) a b := by
      intro h'; apply h; rw [h']; simp [Matrix.one_apply]
    obtain ⟨ha, hb⟩ := stepLeviGL_ne_one S ℓ A h1
    exact ⟨Or.inl ha, Or.inl hb⟩
  · simp [Matrix.fromBlocks_apply₁₂] at h
  · simp [Matrix.fromBlocks_apply₂₁] at h
  · simp only [Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply] at h
    rw [← map_inv] at h
    have h1 : ((stepLeviGL S ℓ A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) b a ≠
        (1 : Matrix (Fin r) (Fin r) K) b a := by
      intro h'; apply h; rw [h']; simp [Matrix.one_apply, eq_comm]
    obtain ⟨hb, ha⟩ := stepLeviGL_ne_one S ℓ A⁻¹ h1
    exact ⟨Or.inr (by show 2 * S.card - cnt S a = _; rw [ha]),
      Or.inr (by show 2 * S.card - cnt S b = _; rw [hb])⟩

theorem commute_of_supp_sp {D E : Fin r ⊕ Fin r → Prop} {g h : StatedSp r K}
    (hg : ∀ u v, spMat g u v ≠ (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) u v → D u ∧ D v)
    (hh : ∀ u v, spMat h u v ≠ (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) u v → E u ∧ E v)
    (hDE : ∀ u, ¬ (D u ∧ E u)) : g * h = h * g :=
  spMat_injective (by rw [spMat_mul, spMat_mul]; exact commute_of_supp hg hh hDE)

theorem stepLevi_commute_stepLevi {ℓ ℓ' : ℕ} (hℓ : ℓ < S.card) (hℓ' : ℓ' < S.card)
    (hne : ℓ ≠ ℓ')
    (A : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord r S ℓ))) K)
    (B : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord r S ℓ'))) K) :
    stepLevi S ℓ A * stepLevi S ℓ' B = stepLevi S ℓ' B * stepLevi S ℓ A :=
  commute_of_supp_sp (D := fun u => spLev r S u = ℓ ∨ spLev r S u = 2 * S.card - ℓ)
    (E := fun u => spLev r S u = ℓ' ∨ spLev r S u = 2 * S.card - ℓ')
    (stepLevi_supp S ℓ A) (stepLevi_supp S ℓ' B) (fun u h => by omega)

theorem stepLevi_commute_topLevi {ℓ : ℕ} (hℓ : ℓ < S.card)
    (A : Matrix.SpecialLinearGroup (Fin (Fintype.card (StepCoord r S ℓ))) K)
    (B : ↥(StatedSp (topN r S) K)) :
    stepLevi S ℓ A * (topLevi S B : StatedSp r K) = (topLevi S B : StatedSp r K) * stepLevi S ℓ A :=
  commute_of_supp_sp (D := fun u => spLev r S u = ℓ ∨ spLev r S u = 2 * S.card - ℓ)
    (E := fun u => spLev r S u = S.card)
    (stepLevi_supp S ℓ A) (fun u v h => topLeviGL_support S _ h) (fun u h => by omega)

end SplitCommute

section SplitCore

variable [Finite K] {S : Finset ℕ}

theorem false_of_split [CharP K 2] {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hK : Nat.card K = 2 ∨ 4 ≤ Nat.card K) (hpq : p ∣ Nat.card K - 1)
    (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r)
    (hA1 : ∀ X : Subgroup (StatedSp r K), X ≤ Jfl r K S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X)
    (hA2 : ∀ X₁ X₂ : Subgroup (StatedSp r K), X₁ ≤ Jfl r K S → X₂ ≤ Jfl r K S →
      CFSG.Open.IsQuasisimple ↥X₁ → CFSG.Open.IsQuasisimple ↥X₂ →
      X₂ ≤ Subgroup.centralizer (X₁ : Set (StatedSp r K)) → p ∣ Nat.card X₁ →
      p ∣ Nat.card X₂ → NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) →
      NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False)
    {x : StatedSp r K} (hxp : x ^ p = 1)
    (hfix : ∀ g : StatedSp r K, g * x = x * g → g ∈ Jfl r K S)
    {V E : Subgroup (StatedSp r K)} (hVJ : V ≤ Jfl r K S)
    (_hVx : V ≤ Subgroup.centralizer ({x} : Set (StatedSp r K))) (hV : ⁅V, V⁆ = V) (hEV : E ≤ V)
    (hEel : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) : False := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  have hp0 : (p : K) ≠ 0 := pCast_ne_zero hp hp2
  have hK4 : 4 ≤ Nat.card K := by
    rcases hK with h2 | h4
    · rw [h2] at hpq
      have : p ≤ 1 := Nat.le_of_dvd one_pos (by simpa using hpq)
      rcases hp57 with rfl | rfl <;> omega
    · exact h4
  have hxJ : x ∈ Jfl r K S := hfix x rfl
  set J := Jfl r K S with hJ
  let B : FlagBlocks p ↥J := spFlagBlocks hS hp0
  have hBfin : ∀ i, Finite (B.H i) := fun i => instFiniteBlockTy (S := S) i
  have hV' : ⁅V.subgroupOf J, V.subgroupOf J⁆ = V.subgroupOf J := commutator_subgroupOf_eq hVJ hV
  have hEV' : E.subgroupOf J ≤ V.subgroupOf J := fun e he =>
    Subgroup.mem_subgroupOf.2 (hEV (Subgroup.mem_subgroupOf.1 he))
  have hE' : ∀ e ∈ E.subgroupOf J, e ^ p = 1 := fun e he => Subtype.ext (by
    have := hEel.2 _ (Subgroup.mem_subgroupOf.1 he)
    simpa using this)
  have hEc' : p ^ 2 ≤ Nat.card (E.subgroupOf J) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEV.trans hVJ)).toEquiv, hEc]
  have hpg : ∀ {H : Type} [Group H] (ρ : ↥J →* H),
      ∀ y ∈ (E.subgroupOf J).map ρ, y ^ p = 1 := by
    intro H _ ρ y hy
    obtain ⟨e, he, rfl⟩ := hy
    rw [← map_pow, hE' e he, map_one]
  have hP : ∀ {H : Type} [Group H] (ρ : ↥J →* H),
      ⁅(V.subgroupOf J).map ρ, (V.subgroupOf J).map ρ⁆ = (V.subgroupOf J).map ρ := by
    intro H _ ρ
    rw [← Subgroup.map_commutator, hV']
  have hcyc_step : ∀ ℓ : Fin S.card, IsCyclic ↥((E.subgroupOf J).map (stepHom hS ℓ.2)) := by
    intro ℓ
    exact isCyclic_of_perfect_gl (step_card_le_two hp57 hK hpq hS hA1 ℓ.1) hK4 hp hp2
      (hP (stepHom hS ℓ.2)) (Subgroup.map_mono hEV') (isPGroup_of_pow_eq_one (hpg _))
  have hcyc_top : IsCyclic ↥((E.subgroupOf J).map (topHom hS)) :=
    isCyclic_of_pGroup_statedSp (topN_le_one hp57 hK hpq hS hA1) hK4 hp hp2
      (isPGroup_of_pow_eq_one (hpg _))
  have act_step : ∀ ℓ : Fin S.card, (E.subgroupOf J).map (stepHom hS ℓ.2) ≠ ⊥ →
      Fintype.card (StepCoord r S ℓ.1) = 2 := by
    intro ℓ hne
    by_contra hk2
    have hk := step_card_le_two hp57 hK hpq hS hA1 ℓ.1
    have hPbot := perfect_eq_bot_of_card_le_one (K := K) (by omega) (hP (stepHom hS ℓ.2))
    apply hne
    have := Subgroup.map_mono (f := stepHom hS ℓ.2) hEV'
    rw [hPbot] at this
    exact le_bot_iff.1 this
  have act_top : (E.subgroupOf J).map (topHom hS) ≠ ⊥ → topN r S = 1 := by
    intro hne
    have hm := topN_le_one hp57 hK hpq hS hA1
    rcases Nat.eq_zero_or_pos (topN r S) with h0 | h1
    · exfalso
      apply hne
      have : Subsingleton (StatedSp (topN r S) K) := by
        rw [h0]
        exact ⟨fun a b => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
      exact (Subgroup.eq_bot_iff_forall _).2 fun y _ => Subsingleton.elim y 1
    · omega
  have hcomm_sub : ∀ (X₁ X₂ : Subgroup (StatedSp r K)),
      (∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) → X₂ ≤ Subgroup.centralizer (X₁ : Set (StatedSp r K)) :=
    fun X₁ X₂ h b hb => Subgroup.mem_centralizer_iff.2 fun a ha => h a ha b hb
  refine B.false_of_split hp hE' hEc' (E := E.subgroupOf J) ?_ ?_
  · intro i
    rcases i with ℓ | u
    · exact hcyc_step ℓ
    · exact hcyc_top
  · intro i j hij hi hj
    rcases i with ℓ | u <;> rcases j with ℓ' | u'
    · have hne : ℓ.1 ≠ ℓ'.1 := fun h => hij (by rw [Fin.ext h])
      obtain ⟨hX₁J, hX₁q, hX₁p, hX₁n⟩ := levi_data_sl2 (J := J) hp57 hK hpq
        (act_step ℓ hi) (stepLevi S ℓ.1) (stepLevi_injective S ℓ.1) (stepLevi_mem hS ℓ.1)
      obtain ⟨hX₂J, hX₂q, hX₂p, hX₂n⟩ := levi_data_sl2 (J := J) hp57 hK hpq
        (act_step ℓ' hj) (stepLevi S ℓ'.1) (stepLevi_injective S ℓ'.1) (stepLevi_mem hS ℓ'.1)
      refine hA2 _ _ hX₁J hX₂J hX₁q hX₂q (hcomm_sub _ _ ?_) hX₁p hX₂p hX₁n hX₂n
      rintro _ ⟨A, rfl⟩ _ ⟨B', rfl⟩
      exact stepLevi_commute_stepLevi ℓ.2 ℓ'.2 hne A B'
    · obtain ⟨hX₁J, hX₁q, hX₁p, hX₁n⟩ := levi_data_sl2 (J := J) hp57 hK hpq
        (act_step ℓ hi) (stepLevi S ℓ.1) (stepLevi_injective S ℓ.1) (stepLevi_mem hS ℓ.1)
      obtain ⟨hX₂J, hX₂q, hX₂p, hX₂n⟩ := levi_data_sp1 (J := J) hp57 hK hpq
        (act_top hj) (topLevi S) (topLevi_injective S) (topLevi_mem hS)
      refine hA2 _ _ hX₁J hX₂J hX₁q hX₂q (hcomm_sub _ _ ?_) hX₁p hX₂p hX₁n hX₂n
      rintro _ ⟨A, rfl⟩ _ ⟨B', rfl⟩
      exact stepLevi_commute_topLevi ℓ.2 A B'
    · obtain ⟨hX₁J, hX₁q, hX₁p, hX₁n⟩ := levi_data_sp1 (J := J) hp57 hK hpq
        (act_top hi) (topLevi S) (topLevi_injective S) (topLevi_mem hS)
      obtain ⟨hX₂J, hX₂q, hX₂p, hX₂n⟩ := levi_data_sl2 (J := J) hp57 hK hpq
        (act_step ℓ' hj) (stepLevi S ℓ'.1) (stepLevi_injective S ℓ'.1) (stepLevi_mem hS ℓ'.1)
      refine hA2 _ _ hX₁J hX₂J hX₁q hX₂q (hcomm_sub _ _ ?_) hX₁p hX₂p hX₁n hX₂n
      rintro _ ⟨A, rfl⟩ _ ⟨B', rfl⟩
      exact (stepLevi_commute_topLevi ℓ'.2 B' A).symm
    · exact hij rfl

end SplitCore

section Final

theorem spSplitCell : SpSplitCell := by
  intro r K _ _ _ p hp57 hK hpq S hS hA1 hA2 x hxp hfix V E hVJ hVx hV hEV hEel hEc
  exact false_of_split hp57 hK hpq hS hA1 hA2 hxp hfix hVJ hVx hV hEV hEel hEc

end Final

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.SpCell

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

open CFSG.AGLEmbedding

theorem altIbBarCell_b : AltIbBarCell (IsLieOf IdxB) :=
  SpCell.altIbBarCell_b_of_split SpCell.spSplitCell

theorem altIbCell_b (hSch : KFactCatalogSchreier)
    (hGA : CFSG.Open.GriessAllModelsStatement) : AltIbCell (IsLieOf IdxB) :=
  altIbCell_of_barCell hSch hGA (fun _ _ hX => Or.inl hX) altIbBarCell_b

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
