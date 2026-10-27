module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinPrimeBlocks
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Transfer
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagBasic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.LinCell

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding CFSG.AGLEmbedding.ToralCensus
  CFSG.RankThree.CALinearPlane CFSG.QuasithinUnique CFSG.AGLEmbedding.LieOut
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def blockHomGL {I : Set ℕ} {a b : ℕ} (h : IsConsecutiveCut n I a b) :
    flagStabilizer n K I →* GL (Fin (b - a)) K :=
  (cutBlockHom h).toHomUnits

theorem coe_blockHomGL {I : Set ℕ} {a b : ℕ} (h : IsConsecutiveCut n I a b)
    (g : flagStabilizer n K I) :
    ((blockHomGL h g : GL (Fin (b - a)) K) : Matrix (Fin (b - a)) (Fin (b - a)) K) =
      cutBlock ((g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) a b h.2.1 :=
  rfl

theorem blockHomGL_eq_one_iff {I : Set ℕ} {a b : ℕ} (h : IsConsecutiveCut n I a b)
    (g : flagStabilizer n K I) :
    blockHomGL h g = 1 ↔
      cutBlock ((g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) a b h.2.1 = 1 := by
  rw [← Units.val_eq_one, coe_blockHomGL]

omit [Field K] in
theorem exists_isConsecutiveCut_pred {I : Set ℕ} {d : ℕ} (hd0 : 0 < d) (hdn : d ≤ n)
    (hd : d = n ∨ d ∈ I) : ∃ a, IsConsecutiveCut n I a d := by
  classical
  obtain ⟨a, hak, haI, hamax⟩ : ∃ a, a ≤ d - 1 ∧ (a = 0 ∨ a ∈ I) ∧ ∀ c ∈ I, c ≤ d - 1 → c ≤ a := by
    refine ⟨Nat.findGreatest (· ∈ I) (d - 1), Nat.findGreatest_le _, ?_,
      fun c hc hck => Nat.le_findGreatest hck hc⟩
    by_cases h0 : Nat.findGreatest (· ∈ I) (d - 1) = 0
    · exact Or.inl h0
    · exact Or.inr (Nat.findGreatest_of_ne_zero rfl h0)
  refine ⟨a, by omega, hdn, haI, hd, fun c hc ⟨hac, hcd⟩ => ?_⟩
  have := hamax c hc (by omega)
  omega

omit [Field K] in
theorem cut_disjoint {I : Set ℕ} {a b a' b' : ℕ} (h : IsConsecutiveCut n I a b)
    (h' : IsConsecutiveCut n I a' b') (hne : (a, b) ≠ (a', b')) : b ≤ a' ∨ b' ≤ a := by
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · left
    have hI : a' ∈ I := h'.2.2.1.resolve_left (by omega)
    by_contra hlb
    exact h.2.2.2.2 a' hI ⟨hlt, by omega⟩
  · subst heq
    exfalso
    rcases lt_trichotomy b b' with hlt | heq | hgt
    · have hI : b ∈ I := h.2.2.2.1.resolve_left (by have := h'.2.1; omega)
      exact h'.2.2.2.2 b hI ⟨h.1, hlt⟩
    · exact hne (by rw [heq])
    · have hI : b' ∈ I := h'.2.2.2.1.resolve_left (by have := h.2.1; omega)
      exact h.2.2.2.2 b' hI ⟨h'.1, hgt⟩
  · right
    have hI : a ∈ I := h.2.2.1.resolve_left (by omega)
    by_contra hlb
    exact h'.2.2.2.2 a hI ⟨hgt, by omega⟩

theorem entry_of_block_eq_one {g : Matrix (Fin n) (Fin n) K} {a b : ℕ} (hb : b ≤ n)
    (hg : cutBlock g a b hb = 1) {k j : Fin n} (hk : a ≤ (k : ℕ) ∧ (k : ℕ) < b)
    (hj : a ≤ (j : ℕ) ∧ (j : ℕ) < b) : g k j = if k = j then 1 else 0 := by
  have h := congrFun (congrFun hg ⟨(k : ℕ) - a, by omega⟩) ⟨(j : ℕ) - a, by omega⟩
  rw [cutBlock_apply, Matrix.one_apply] at h
  have e1 : (⟨a + ((k : ℕ) - a), by omega⟩ : Fin n) = k := Fin.ext (by simp; omega)
  have e2 : (⟨a + ((j : ℕ) - a), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
  rw [e1, e2] at h
  rw [h]
  by_cases hkj : k = j
  · subst hkj; simp
  · have : (⟨(k : ℕ) - a, by omega⟩ : Fin (b - a)) ≠ ⟨(j : ℕ) - a, by omega⟩ := fun e => by
      have := congrArg Fin.val e
      simp at this
      exact hkj (Fin.ext (by omega))
    simp [hkj, this]

theorem mulVec_mem_flagSpace {d : ℕ} {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ stabilizer (flagSpace n K d)) {v : Fin n → K} (hv : v ∈ flagSpace n K d) :
    (g : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ flagSpace n K d :=
  (mem_stabilizer.mp hg) ▸ ⟨v, hv, rfl⟩

theorem mulVec_sub_mem_of_block_eq_one {I : Set ℕ} {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ flagStabilizer n K I) {a d : ℕ} (h : IsConsecutiveCut n I a d)
    (hblk : cutBlock (g : Matrix (Fin n) (Fin n) K) a d h.2.1 = 1) {v : Fin n → K}
    (hv : v ∈ flagSpace n K d) :
    (g : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ flagSpace n K a := by
  rw [mem_flagSpace]
  intro k hk
  rw [Pi.sub_apply, sub_eq_zero]
  by_cases hkd : d ≤ (k : ℕ)
  · rcases h.2.2.2.1 with rfl | hdI
    · exact absurd k.2 (by omega)
    · have := mem_flagSpace.mp (mulVec_mem_flagSpace (mem_flagStabilizer.mp hg d hdI) hv) k hkd
      rw [this, mem_flagSpace.mp hv k hkd]
  · simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single k]
    · rw [entry_of_block_eq_one h.2.1 hblk ⟨hk, by omega⟩ ⟨hk, by omega⟩]
      simp
    · intro j _ hjk
      by_cases hjd : d ≤ (j : ℕ)
      · rw [mem_flagSpace.mp hv j hjd, mul_zero]
      · by_cases hja : (j : ℕ) < a
        · rw [apply_eq_zero_of_mem_flagStabilizer h.2.2.1 hg hja hk, zero_mul]
        · rw [entry_of_block_eq_one h.2.1 hblk ⟨hk, by omega⟩ ⟨by omega, by omega⟩]
          simp [Ne.symm hjk]
    · simp

theorem eq_of_sub_fixed {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι K} {m : ℕ}
    (hm : (m : K) ≠ 0) (hM : M ^ m = 1) {v : ι → K}
    (h : M *ᵥ (M *ᵥ v - v) = M *ᵥ v - v) : M *ᵥ v = v := by
  set u : ι → K := M *ᵥ v - v with hu
  have hpow : ∀ k : ℕ, (M ^ k) *ᵥ v = v + (k : K) • u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, Matrix.mulVec_smul, h, hu]
      rw [Nat.cast_succ, add_smul, one_smul]
      abel
  have h1 := hpow m
  rw [hM, Matrix.one_mulVec] at h1
  have h2 : (m : K) • u = 0 := by
    have := congrArg (fun w => w - v) h1
    simpa using this.symm
  have h3 : u = 0 := by
    rcases smul_eq_zero.1 h2 with h | h
    · exact absurd h hm
    · exact h
  exact sub_eq_zero.1 h3

theorem fixes_flagSpace_of_blocks_trivial {I : Set ℕ} {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ flagStabilizer n K I) {m : ℕ} (hm : (m : K) ≠ 0)
    (hgm : (g : Matrix (Fin n) (Fin n) K) ^ m = 1)
    (hblk : ∀ a b (h : IsConsecutiveCut n I a b),
      cutBlock (g : Matrix (Fin n) (Fin n) K) a b h.2.1 = 1) :
    ∀ d, d ≤ n → (d = 0 ∨ d = n ∨ d ∈ I) → ∀ v ∈ flagSpace n K d,
      (g : Matrix (Fin n) (Fin n) K) *ᵥ v = v := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hdn hd v hv
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · have : v = 0 := funext fun j => mem_flagSpace.mp hv j (Nat.zero_le _)
      rw [this, Matrix.mulVec_zero]
    · obtain ⟨a, ha⟩ := exists_isConsecutiveCut_pred hd0 hdn (hd.resolve_left (by omega))
      have hau := mulVec_sub_mem_of_block_eq_one hg ha (hblk a d ha) hv
      have hfix := ih a ha.1 (by have := ha.1; omega)
        (ha.2.2.1.elim Or.inl fun h => Or.inr (Or.inr h)) _ hau
      exact eq_of_sub_fixed hm hgm hfix

theorem eq_one_of_blocks_trivial_pow {I : Set ℕ} {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ flagStabilizer n K I) {m : ℕ} (hm : (m : K) ≠ 0) (hgm : g ^ m = 1)
    (hblk : ∀ a b (h : IsConsecutiveCut n I a b),
      cutBlock (g : Matrix (Fin n) (Fin n) K) a b h.2.1 = 1) : g = 1 := by
  have hfix := fixes_flagSpace_of_blocks_trivial hg hm (LinearThreeKit.coe_pow_eq_one hgm) hblk n
    le_rfl (Or.inr (Or.inl rfl))
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  have hv : Pi.single j (1 : K) ∈ flagSpace n K n :=
    mem_flagSpace.mpr fun l hl => absurd l.2 (by omega)
  have := congrFun (hfix _ hv) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem pow_apply_first_eq_one {I : Set ℕ} {x : SpecialLinearGroup (Fin n) K}
    (hxI : x ∈ flagStabilizer n K I) {a b : ℕ} (h : IsConsecutiveCut n I a b) (han : a < n)
    (hx : cutBlock (x : Matrix (Fin n) (Fin n) K) a b h.2.1 = 1) (i : ℕ) :
    ((x : Matrix (Fin n) (Fin n) K) ^ i) ⟨a, han⟩ ⟨a, han⟩ = 1 := by
  have hpow := map_pow (cutBlockHom (K := K) h) ⟨x, hxI⟩ i
  rw [cutBlockHom_apply, cutBlockHom_apply] at hpow
  change cutBlock ((x ^ i : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) a b
    h.2.1 = cutBlock (x : Matrix (Fin n) (Fin n) K) a b h.2.1 ^ i at hpow
  rw [hx, one_pow, Matrix.SpecialLinearGroup.coe_pow] at hpow
  have h' := congrFun (congrFun hpow ⟨0, by have := h.1; omega⟩) ⟨0, by have := h.1; omega⟩
  rw [cutBlock_apply, Matrix.one_apply_eq] at h'
  simpa using h'

theorem exists_fixed_of_trivial_block [CharP K 2] {I : Set ℕ} {p : ℕ}
    {x : SpecialLinearGroup (Fin n) K} (hxI : x ∈ flagStabilizer n K I) (hxp : x ^ p = 1)
    {a b : ℕ} (h : IsConsecutiveCut n I a b) (han : a < n)
    (hx : cutBlock (x : Matrix (Fin n) (Fin n) K) a b h.2.1 = 1) :
    ∃ v : Fin n → K, (x : Matrix (Fin n) (Fin n) K) *ᵥ v = v ∧ v ⟨a, han⟩ = p ∧
      ∀ d ∈ I, a < d → v ∈ flagSpace n K d := by
  refine ⟨unitFixedVec p (x : Matrix (Fin n) (Fin n) K) ⟨a, han⟩,
    LinearThreeKit.mulVec_fixedSum (LinearThreeKit.coe_pow_eq_one hxp) _, ?_, ?_⟩
  · rw [unitFixedVec_apply_self, Finset.sum_congr rfl fun i _ =>
      pow_apply_first_eq_one hxI h han hx i, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
  · intro d hd had
    exact unitFixedVec_mem_flagSpace hxI hd p (j := ⟨a, han⟩) had

theorem false_of_trivialBlocks [CharP K 2] {I : Set ℕ} {p : ℕ} (hp : Odd p)
    {x : SpecialLinearGroup (Fin n) K} (hxI : x ∈ flagStabilizer n K I) (hxp : x ^ p = 1)
    (hfix : Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin n) K)) ≤
      flagStabilizer n K I)
    {a b a' b' : ℕ} (h : IsConsecutiveCut n I a b) (h' : IsConsecutiveCut n I a' b')
    (hba' : b ≤ a') (hx : cutBlock (x : Matrix (Fin n) (Fin n) K) a b h.2.1 = 1)
    (hx' : cutBlock (x : Matrix (Fin n) (Fin n) K) a' b' h'.2.1 = 1) : False := by
  have hab := h.1
  have hab' := h'.1
  have hk'I : a' ∈ I := h'.2.2.1.resolve_left (by omega)
  have hpK := natCast_ne_zero_of_odd_charTwo (K := K) hp
  have han : a < n := lt_of_lt_of_le h.1 h.2.1
  have han' : a' < n := lt_of_lt_of_le h'.1 h'.2.1
  set X := (x : Matrix (Fin n) (Fin n) K) with hX
  have hXp : X ^ p = 1 := LinearThreeKit.coe_pow_eq_one hxp
  obtain ⟨v, hvfix, hvj, hvF⟩ := exists_fixed_of_trivial_block hxI hxp h han hx
  obtain ⟨v', hv'fix, hvj', -⟩ := exists_fixed_of_trivial_block hxI hxp h' han' hx'
  set E := LinearMap.ker (Matrix.mulVecLin X - (1 : K) • LinearMap.id) with hE
  have hvE : v ∈ E := mem_ker_sub_smul_iff.mpr (by rw [one_smul]; exact hvfix)
  have hv'E : v' ∈ E := mem_ker_sub_smul_iff.mpr (by rw [one_smul]; exact hv'fix)
  have hvF' : v ∈ flagSpace n K a' := hvF a' hk'I (by omega)
  have hv0 : v ≠ 0 := fun h0 => hpK (by rw [← hvj, h0, Pi.zero_apply])
  have hv'F : v' ∉ flagSpace n K a' := fun h0 =>
    hpK (by rw [← hvj', mem_flagSpace.mp h0 ⟨a', han'⟩ le_rfl])
  have hli := LinearThreeKit.linearIndependent_pair_of_notMem hvF' hv0 hv'F
  have hdim : 2 ≤ Module.finrank K E := by
    have hspan : Submodule.span K (Set.range ![v, v']) ≤ E := by
      rw [Submodule.span_le, Set.range_subset_iff]
      intro i
      fin_cases i
      · exact hvE
      · exact hv'E
    have h2 := Submodule.finrank_mono hspan
    rwa [finrank_span_eq_card hli, Fintype.card_fin] at h2
  have hW : ∀ g ∈ Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin n) K)),
      ∀ w ∈ flagSpace n K a', (g : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ flagSpace n K a' := by
    intro g hg w hw
    exact mulVec_mem_flagSpace (mem_flagStabilizer.mp (hfix hg) a' hk'I) hw
  rcases eigenSpaceRigid_holds K n p hp x 1 1 (by rw [hXp, map_one]) hdim
      (flagSpace n K a') hW with h0 | h0
  · exact hv0 ((Submodule.mem_bot K).mp (h0 ▸ ⟨hvF', hvE⟩))
  · exact hv'F (h0 hv'E)

@[expose] def CoverA1 (n : ℕ) (K : Type) [Field K] (I : Set ℕ) (p : ℕ) : Prop :=
  ∀ X : Subgroup (SpecialLinearGroup (Fin n) K), X ≤ flagStabilizer n K I →
    X ⊓ Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ → CFSG.Open.IsQuasisimple ↥X →
    ¬ p ^ 2 ∣ Nat.card X

@[expose] def CoverA2 (n : ℕ) (K : Type) [Field K] (I : Set ℕ) (p : ℕ) : Prop :=
  ∀ X₁ X₂ : Subgroup (SpecialLinearGroup (Fin n) K), X₁ ≤ flagStabilizer n K I →
    X₂ ≤ flagStabilizer n K I → X₁ ⊓ Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ →
    X₂ ⊓ Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ → CFSG.Open.IsQuasisimple ↥X₁ →
    CFSG.Open.IsQuasisimple ↥X₂ → X₂ ≤ Subgroup.centralizer (X₁ : Set (SpecialLinearGroup (Fin n) K)) →
    p ∣ Nat.card X₁ → p ∣ Nat.card X₂ → NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) →
    NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False

theorem card_eq_two_or_four_le [Finite K] [CharP K 2] : Nat.card K = 2 ∨ 4 ≤ Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card (K := K) 2
  rw [Nat.card_eq_fintype_card, hm]
  have hm1 : 1 ≤ (m : ℕ) := m.pos
  rcases Nat.eq_or_lt_of_le hm1 with h | h
  · left
    rw [← h]
    simp
  · right
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (m : ℕ) := Nat.pow_le_pow_right (by norm_num) h

theorem open_of_isQuasisimple {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q := ⟨Group.isPerfect_def.1 h.1, h.2.1⟩

theorem coordBlockSL_inf_center {J : Finset (Fin n)} (hJ : J.card < n) :
    coordBlockSL K J ⊓ Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgJ, hgc⟩
  obtain ⟨i, hi⟩ : ∃ i : Fin n, i ∉ J := by
    by_contra hcon
    push Not at hcon
    have : J = Finset.univ := Finset.eq_univ_of_forall hcon
    rw [this, Finset.card_univ, Fintype.card_fin] at hJ
    exact lt_irrefl _ hJ
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hgc
  have h1 := mem_coordBlockSL_iff.1 hgJ i i (Or.inl hi)
  rw [← hr, scalar_apply, diagonal_apply_eq] at h1
  have h1' : r = 1 := by simpa using h1
  rw [Subgroup.mem_bot]
  exact Subtype.ext (by rw [← hr, h1', map_one, Matrix.SpecialLinearGroup.coe_one])

theorem isQuasisimple_SL2_of_four_le [Finite K] (hK4 : 4 ≤ Nat.card K) :
    CFSG.Open.IsQuasisimple (SpecialLinearGroup (Fin 2) K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hK4)
  exact open_of_isQuasisimple (CFSG.RankThree.Classical.isQuasisimple_SL2 ⟨s, hs⟩)

theorem not_sq_dvd_card_SL_of [Finite K] {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hK : Nat.card K = 2 ∨ 4 ≤ Nat.card K) {k : ℕ}
    (hq : 2 ≤ k → CFSG.Open.IsQuasisimple (SpecialLinearGroup (Fin k) K) →
      ¬ p ^ 2 ∣ Nat.card (SpecialLinearGroup (Fin k) K)) :
    ¬ p ^ 2 ∣ Nat.card (SpecialLinearGroup (Fin k) K) := by
  have : Fintype K := Fintype.ofFinite K
  have hKpos : 2 ≤ Nat.card K := by omega
  have hp2 : 6 < p ^ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k
    · have : Subsingleton (Matrix.SpecialLinearGroup (Fin 0) K) :=
        ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
      rw [Nat.card_of_subsingleton (1 : Matrix.SpecialLinearGroup (Fin 0) K)]
      intro hd
      have := Nat.le_of_dvd one_pos hd
      omega
    · have h1 := Matrix.card_SL_field (𝔽 := K) 1
      rw [← Nat.card_eq_fintype_card] at h1
      simp only [Fin.prod_univ_one, Fin.val_zero, pow_one, pow_zero] at h1
      rw [h1, Nat.div_self (by omega)]
      intro hd
      have := Nat.le_of_dvd one_pos hd
      omega
    · rcases hK with hK2 | hK4
      · have h1 := Matrix.card_SL_field (𝔽 := K) 2
        rw [← Nat.card_eq_fintype_card, hK2] at h1
        simp [Fin.prod_univ_two] at h1
        rw [h1]
        intro hd
        have := Nat.le_of_dvd (by norm_num) hd
        omega
      · exact hq le_rfl (isQuasisimple_SL2_of_four_le hK4)
  · exact hq (by omega) (open_of_isQuasisimple
      (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup hk))

theorem a1_blocks [Finite K] [CharP K 2] {I : Set ℕ} {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hA1 : CoverA1 n K I p) {a b : ℕ} (h : IsConsecutiveCut n I a b) (hlt : b - a < n) :
    ¬ p ^ 2 ∣ Nat.card (SpecialLinearGroup (Fin (b - a)) K) := by
  have hK := card_eq_two_or_four_le (K := K)
  by_cases hk2 : 2 ≤ b - a
  · set J : Finset (Fin n) := intervalCoords n a b h.2.1 with hJ
    have hJc : J.card = b - a := card_intervalCoords
    have key : ¬ p ^ 2 ∣ Nat.card (SpecialLinearGroup (Fin J.card) K) := by
      refine not_sq_dvd_card_SL_of hp57 hK fun _ hq hd => ?_
      have e := MonoidHom.ofInjective (blockSLOn_injective (k := K) J)
      refine hA1 (blockSLOn K J).range ?_ ?_ ?_ ?_
      · rw [range_blockSLOn]
        exact coordBlockSL_le_flagStabilizer h
      · rw [range_blockSLOn]
        exact coordBlockSL_inf_center (by omega)
      · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm hq
      · rwa [← Nat.card_congr e.toEquiv]
    rw [hJc] at key
    exact key
  · exact not_sq_dvd_card_SL_of hp57 hK fun h2 _ => absurd h2 hk2

theorem pow_apply_first_eq_pow {I : Set ℕ} {x : SpecialLinearGroup (Fin n) K}
    (hxI : x ∈ flagStabilizer n K I) {a b : ℕ} (h : IsConsecutiveCut n I a b) (han : a < n)
    {ξ : K} (hx : cutBlock (x : Matrix (Fin n) (Fin n) K) a b h.2.1 =
      ξ • (1 : Matrix (Fin (b - a)) (Fin (b - a)) K)) (i : ℕ) :
    ((x : Matrix (Fin n) (Fin n) K) ^ i) ⟨a, han⟩ ⟨a, han⟩ = ξ ^ i := by
  have hpow := map_pow (cutBlockHom (K := K) h) ⟨x, hxI⟩ i
  rw [cutBlockHom_apply, cutBlockHom_apply] at hpow
  change cutBlock ((x ^ i : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) a b
    h.2.1 = cutBlock (x : Matrix (Fin n) (Fin n) K) a b h.2.1 ^ i at hpow
  rw [hx, smul_pow, one_pow, Matrix.SpecialLinearGroup.coe_pow] at hpow
  have h' := congrFun (congrFun hpow ⟨0, by have := h.1; omega⟩) ⟨0, by have := h.1; omega⟩
  rw [cutBlock_apply] at h'
  simpa using h'

theorem exists_eigen_of_scalar_block {I : Set ℕ} {p : ℕ} {x : SpecialLinearGroup (Fin n) K}
    (hxI : x ∈ flagStabilizer n K I) {ξ : K} (hξ : ξ ≠ 0)
    (hxp : (x : Matrix (Fin n) (Fin n) K) ^ p = Matrix.scalar (Fin n) (ξ ^ p)) {a b : ℕ}
    (h : IsConsecutiveCut n I a b) (han : a < n)
    (hx : cutBlock (x : Matrix (Fin n) (Fin n) K) a b h.2.1 =
      ξ • (1 : Matrix (Fin (b - a)) (Fin (b - a)) K)) :
    ∃ v : Fin n → K, (x : Matrix (Fin n) (Fin n) K) *ᵥ v = ξ • v ∧ v ⟨a, han⟩ = p ∧
      ∀ d ∈ I, a < d → v ∈ flagSpace n K d := by
  set X := (x : Matrix (Fin n) (Fin n) K) with hX
  set Y : Matrix (Fin n) (Fin n) K := ξ⁻¹ • X with hY
  have hYp : Y ^ p = 1 := by
    rw [hY, smul_pow, hxp, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, smul_smul,
      ← mul_pow, inv_mul_cancel₀ hξ, one_pow, one_smul]
  have hYi : ∀ i : ℕ, Y ^ i = ξ⁻¹ ^ i • X ^ i := fun i => by rw [hY, smul_pow]
  refine ⟨unitFixedVec p Y ⟨a, han⟩, ?_, ?_, ?_⟩
  · have hfix := LinearThreeKit.mulVec_fixedSum hYp (Pi.single (⟨a, han⟩ : Fin n) (1 : K))
    have hXY : X = ξ • Y := by rw [hY, smul_inv_smul₀ hξ]
    rw [unitFixedVec, hXY, Matrix.smul_mulVec, hfix]
  · rw [unitFixedVec_apply_self, Finset.sum_congr rfl fun i _ => by
      rw [hYi, Matrix.smul_apply, pow_apply_first_eq_pow hxI h han hx i, smul_eq_mul,
        ← mul_pow, inv_mul_cancel₀ hξ, one_pow], Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  · intro d hd had
    rw [unitFixedVec, LinearThreeKit.fixedSum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hxi : x ^ i ∈ stabilizer (flagSpace n K d) :=
      mem_flagStabilizer.mp (Subgroup.pow_mem _ hxI i) d hd
    rw [hYi, Matrix.smul_mulVec, hX, ← Matrix.SpecialLinearGroup.coe_pow]
    exact Submodule.smul_mem _ _ (mulVec_mem_flagSpace hxi (single_mem_flagSpace_of_lt had))

theorem false_of_scalarBlocks [CharP K 2] {I : Set ℕ} {p : ℕ} (hp : Odd p)
    {x : SpecialLinearGroup (Fin n) K} (hxI : x ∈ flagStabilizer n K I) {ξ : K} (hξ : ξ ≠ 0)
    (hxp : (x : Matrix (Fin n) (Fin n) K) ^ p = Matrix.scalar (Fin n) (ξ ^ p))
    (hfix : Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin n) K)) ≤
      flagStabilizer n K I)
    {a b a' b' : ℕ} (h : IsConsecutiveCut n I a b) (h' : IsConsecutiveCut n I a' b')
    (hba' : b ≤ a')
    (hx : cutBlock (x : Matrix (Fin n) (Fin n) K) a b h.2.1 =
      ξ • (1 : Matrix (Fin (b - a)) (Fin (b - a)) K))
    (hx' : cutBlock (x : Matrix (Fin n) (Fin n) K) a' b' h'.2.1 =
      ξ • (1 : Matrix (Fin (b' - a')) (Fin (b' - a')) K)) : False := by
  have hab := h.1
  have hab' := h'.1
  have hk'I : a' ∈ I := h'.2.2.1.resolve_left (by omega)
  have hpK := natCast_ne_zero_of_odd_charTwo (K := K) hp
  have han : a < n := lt_of_lt_of_le h.1 h.2.1
  have han' : a' < n := lt_of_lt_of_le h'.1 h'.2.1
  set X := (x : Matrix (Fin n) (Fin n) K) with hX
  obtain ⟨v, hvfix, hvj, hvF⟩ := exists_eigen_of_scalar_block hxI hξ hxp h han hx
  obtain ⟨v', hv'fix, hvj', -⟩ := exists_eigen_of_scalar_block hxI hξ hxp h' han' hx'
  set E := LinearMap.ker (Matrix.mulVecLin X - ξ • LinearMap.id) with hE
  have hvE : v ∈ E := mem_ker_sub_smul_iff.mpr hvfix
  have hv'E : v' ∈ E := mem_ker_sub_smul_iff.mpr hv'fix
  have hvF' : v ∈ flagSpace n K a' := hvF a' hk'I (by omega)
  have hv0 : v ≠ 0 := fun h0 => hpK (by rw [← hvj, h0, Pi.zero_apply])
  have hv'F : v' ∉ flagSpace n K a' := fun h0 =>
    hpK (by rw [← hvj', mem_flagSpace.mp h0 ⟨a', han'⟩ le_rfl])
  have hli := LinearThreeKit.linearIndependent_pair_of_notMem hvF' hv0 hv'F
  have hdim : 2 ≤ Module.finrank K E := by
    have hspan : Submodule.span K (Set.range ![v, v']) ≤ E := by
      rw [Submodule.span_le, Set.range_subset_iff]
      intro i
      fin_cases i
      · exact hvE
      · exact hv'E
    have h2 := Submodule.finrank_mono hspan
    rwa [finrank_span_eq_card hli, Fintype.card_fin] at h2
  have hW : ∀ g ∈ Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin n) K)),
      ∀ w ∈ flagSpace n K a', (g : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ flagSpace n K a' := by
    intro g hg w hw
    exact mulVec_mem_flagSpace (mem_flagStabilizer.mp (hfix hg) a' hk'I) hw
  rcases eigenSpaceRigid_holds K n p hp x (ξ ^ p) ξ hxp hdim (flagSpace n K a') hW with h0 | h0
  · exact hv0 ((Submodule.mem_bot K).mp (h0 ▸ ⟨hvF', hvE⟩))
  · exact hv'F (h0 hv'E)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.LinCell
