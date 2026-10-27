module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaSpA

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp)

variable {K : Type} [Field K] {n : ℕ}

section Partner

@[expose] def spAPar (k : Fin n) : Fin n :=
  if h : k.val % 2 = 0 ∧ k.val + 1 < n then ⟨k.val + 1, h.2⟩
  else if k.val % 2 = 1 then ⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.2⟩ else k

variable {j : ℕ}

theorem spAPar_val (hjn : 2 * j ≤ n) {k : Fin n} (hk : k.val < 2 * j) :
    (spAPar k).val = if k.val % 2 = 0 then k.val + 1 else k.val - 1 := by
  unfold spAPar
  by_cases h0 : k.val % 2 = 0
  · rw [dite_eq_left ⟨h0, by omega⟩, ite_eq_left h0]
  · rw [dite_eq_right (fun h => h0 h.1), ite_eq_left (by omega), ite_eq_right h0]

theorem spAPar_lt (hjn : 2 * j ≤ n) {k : Fin n} (hk : k.val < 2 * j) : (spAPar k).val < 2 * j := by
  rw [spAPar_val hjn hk]
  split_ifs <;> omega

theorem spAPar_spAPar (hjn : 2 * j ≤ n) {k : Fin n} (hk : k.val < 2 * j) :
    spAPar (spAPar k) = k := by
  apply Fin.ext
  rw [spAPar_val hjn (spAPar_lt hjn hk), spAPar_val hjn hk]
  split_ifs <;> omega

theorem spARepMat_apply (hjn : 2 * j ≤ n) (m l : Fin n) :
    (spARepMat n j : Matrix (Fin n) (Fin n) K) m l =
      if l.val < 2 * j ∧ m = spAPar l then 1 else 0 := by
  rw [spARepMat, of_apply]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h4, Fin.ext ?_⟩
    rw [spAPar_val hjn h4]
    have h2' : m.val ≠ l.val := fun h => h2 (Fin.ext h)
    split_ifs <;> omega
  · rintro ⟨h4, rfl⟩
    have hv := spAPar_val hjn h4
    refine ⟨?_, fun h => ?_, spAPar_lt hjn h4, h4⟩
    · rw [hv]
      split_ifs <;> omega
    · have := congrArg Fin.val h
      rw [hv] at this
      split_ifs at this <;> omega

theorem sum_mul_spARepMat (hjn : 2 * j ≤ n) (φ : Fin n → K) (l : Fin n) :
    ∑ m, φ m * (spARepMat n j : Matrix (Fin n) (Fin n) K) m l =
      if l.val < 2 * j then φ (spAPar l) else 0 := by
  simp only [spARepMat_apply hjn]
  split_ifs with hl
  · rw [Finset.sum_eq_single (spAPar l)]
    · rw [ite_eq_left ⟨hl, rfl⟩, mul_one]
    · intro m _ hm
      rw [ite_eq_right (fun h => hm h.2), mul_zero]
    · simp
  · exact Finset.sum_eq_zero fun m _ => by rw [ite_eq_right (fun h => hl h.1), mul_zero]

theorem sum_spARepMat_mul (hjn : 2 * j ≤ n) (φ : Fin n → K) (k : Fin n) :
    ∑ m, (spARepMat n j : Matrix (Fin n) (Fin n) K) k m * φ m =
      if k.val < 2 * j then φ (spAPar k) else 0 := by
  have h : ∀ m, (spARepMat n j : Matrix (Fin n) (Fin n) K) k m =
      (spARepMat n j : Matrix (Fin n) (Fin n) K) m k := fun m => by
    rw [← transpose_apply (spARepMat n j : Matrix (Fin n) (Fin n) K) m k, spARepMat_transpose]
  simp only [h, mul_comm _ (φ _)]
  exact sum_mul_spARepMat hjn φ k

end Partner

section Nil

variable (K n) in
@[expose] def spANil (j : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  fromBlocks 0 (spARepMat n j) 0 0

variable {j : ℕ}

theorem mat_spARep_eq : mat n K (spARep n j) = 1 + spANil K n j := by
  rw [spARep, mat_upperUnipotentSp, spANil, ← fromBlocks_one, fromBlocks_add]
  simp

theorem mul_spANil_inl (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (r : Fin n ⊕ Fin n)
    (l : Fin n) : (G * spANil K n j) r (Sum.inl l) = 0 := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp [spANil]

theorem mul_spANil_inr (hjn : 2 * j ≤ n) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (r : Fin n ⊕ Fin n) (l : Fin n) :
    (G * spANil K n j) r (Sum.inr l) = if l.val < 2 * j then G r (Sum.inl (spAPar l)) else 0 := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [spANil, fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero]
  exact sum_mul_spARepMat hjn (fun m => G r (Sum.inl m)) l

theorem spANil_mul_inr (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (k : Fin n)
    (t : Fin n ⊕ Fin n) : (spANil K n j * G) (Sum.inr k) t = 0 := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp [spANil]

theorem spANil_mul_inl (hjn : 2 * j ≤ n) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (k : Fin n) (t : Fin n ⊕ Fin n) :
    (spANil K n j * G) (Sum.inl k) t = if k.val < 2 * j then G (Sum.inr (spAPar k)) t else 0 := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [spANil, fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add]
  exact sum_spARepMat_mul hjn (fun m => G (Sum.inr m) t) k

theorem mul_spANil_transpose_inr (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (r : Fin n ⊕ Fin n) (l : Fin n) : (G * (spANil K n j)ᵀ) r (Sum.inr l) = 0 := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp [spANil]

theorem mul_spANil_transpose_inl (hjn : 2 * j ≤ n) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (r : Fin n ⊕ Fin n) (l : Fin n) :
    (G * (spANil K n j)ᵀ) r (Sum.inl l) =
      if l.val < 2 * j then G r (Sum.inr (spAPar l)) else 0 := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [spANil, fromBlocks_transpose, spARepMat_transpose, transpose_zero,
    fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero, Finset.sum_const_zero,
    zero_add]
  exact sum_mul_spARepMat hjn (fun m => G r (Sum.inr m)) l

theorem spANil_transpose_mul_inl (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (k : Fin n)
    (t : Fin n ⊕ Fin n) : ((spANil K n j)ᵀ * G) (Sum.inl k) t = 0 := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp [spANil]

theorem spANil_transpose_mul_inr (hjn : 2 * j ≤ n) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (k : Fin n) (t : Fin n ⊕ Fin n) :
    ((spANil K n j)ᵀ * G) (Sum.inr k) t =
      if k.val < 2 * j then G (Sum.inl (spAPar k)) t else 0 := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [spANil, fromBlocks_transpose, spARepMat_transpose, transpose_zero,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero]
  exact sum_spARepMat_mul hjn (fun m => G (Sum.inl m) t) k

theorem commute_spARep_iff {g : StatedSp n K} :
    g * spARep n j = spARep n j * g ↔ mat n K g * spANil K n j = spANil K n j * mat n K g := by
  rw [← mat_injective.eq_iff, map_mul, map_mul, mat_spARep_eq, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul, add_right_inj]

end Nil

section Levi

variable (j : ℕ)

@[expose] def spABlk : Fin n ⊕ Fin n → Fin 3 :=
  Sum.elim (fun k => if k.val < 2 * j then 0 else 2) (fun k => if k.val < 2 * j then 1 else 2)

variable {j}

@[simp] theorem spABlk_inl (k : Fin n) :
    spABlk j (Sum.inl k) = if k.val < 2 * j then 0 else 2 := rfl

@[simp] theorem spABlk_inr (k : Fin n) :
    spABlk j (Sum.inr k) = if k.val < 2 * j then 1 else 2 := rfl

theorem spABlk_par (r : Fin n ⊕ Fin n) :
    spABlk j (par r) = if spABlk j r = 0 then 1 else if spABlk j r = 1 then 0 else 2 := by
  rcases r with k | k <;> by_cases hk : k.val < 2 * j <;> simp [hk]

theorem spABlk_fin_three_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  fin_cases x <;> simp

variable (j) in
@[expose] def spALeviPart (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.of fun r t => if spABlk j r = spABlk j t then G r t else 0

theorem spALeviPart_apply (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (r t : Fin n ⊕ Fin n) :
    spALeviPart j G r t = if spABlk j r = spABlk j t then G r t else 0 := rfl

theorem spALeviPart_one :
    spALeviPart j (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 := by
  ext r t
  rw [spALeviPart_apply]
  split_ifs with h
  · rfl
  · rw [Matrix.one_apply_ne (by rintro rfl; exact h rfl)]

theorem spALeviPart_spALeviPart (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    spALeviPart j (spALeviPart j G) = spALeviPart j G := by
  ext r t
  simp only [spALeviPart_apply]
  split_ifs <;> rfl

variable (j) in
@[expose] def SpABlockCond (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) : Prop :=
  (∀ r u, spABlk j u = 0 → spABlk j r ≠ 0 → G r u = 0) ∧
    ∀ u t, spABlk j u = 1 → spABlk j t ≠ 1 → G u t = 0

theorem spALeviPart_mul {G H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hG : SpABlockCond j G) (hH : SpABlockCond j H) :
    spALeviPart j (G * H) = spALeviPart j G * spALeviPart j H := by
  ext r t
  simp only [spALeviPart_apply, Matrix.mul_apply]
  split_ifs with hrt
  · refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hru : spABlk j r = spABlk j u
    · rw [ite_eq_left hru, ite_eq_left (hru.symm.trans hrt)]
    · rw [ite_eq_right hru, zero_mul]
      rcases spABlk_fin_three_cases (spABlk j r) with h0 | h1 | h2
      · rw [hH.1 u t (hrt ▸ h0) (fun h => hru (h0.trans h.symm)), mul_zero]
      · rw [hG.2 r u h1 (fun h => hru (h1.trans h.symm)), zero_mul]
      · rcases spABlk_fin_three_cases (spABlk j u) with hu0 | hu1 | hu2
        · rw [hG.1 r u hu0 (by rw [h2]; decide), zero_mul]
        · rw [hH.2 u t hu1 (by rw [← hrt, h2]; decide), mul_zero]
        · exact absurd (h2.trans hu2.symm) hru
  · symm
    refine Finset.sum_eq_zero fun u _ => ?_
    split_ifs with h1 h2
    · exact absurd (h1.trans h2) hrt
    · rw [mul_zero]
    · rw [zero_mul]
    · rw [zero_mul]

theorem spALeviPart_symplectic {g : StatedSp n K} (hg : SpABlockCond j (mat n K g)) :
    (spALeviPart j (mat n K g))ᵀ * gram K n * spALeviPart j (mat n K g) = gram K n := by
  set σ : Fin 3 → Fin 3 := fun x => if x = 0 then 1 else if x = 1 then 0 else 2 with hσ
  have hbp : ∀ r : Fin n ⊕ Fin n, spABlk j (par r) = σ (spABlk j r) := spABlk_par
  ext a b
  rw [transpose_mul_gram_mul_apply]
  simp only [spALeviPart_apply]
  by_cases hab : spABlk j b = σ (spABlk j a)
  · have key := congrFun (congrFun (mat_transpose_mul_gram_mul g) a) b
    rw [transpose_mul_gram_mul_apply] at key
    rw [← key]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hca : spABlk j c = spABlk j a
    · rw [ite_eq_left hca, ite_eq_left (by rw [hbp, hca, hab])]
    · rw [ite_eq_right hca, zero_mul]
      rcases spABlk_fin_three_cases (spABlk j a) with ha0 | ha1 | ha2
      · rw [hg.1 c a ha0 (fun h => hca (h.trans ha0.symm)), zero_mul]
      · have hb0 : spABlk j b = 0 := by rw [hab, ha1]; decide
        have hpc : spABlk j (par c) ≠ 0 := by
          rw [hbp]
          intro h
          apply hca
          rw [ha1]
          rcases spABlk_fin_three_cases (spABlk j c) with h' | h' | h' <;> rw [h'] at h ⊢ <;> simp_all
        rw [hg.1 (par c) b hb0 hpc, mul_zero, mul_zero]
      · have hb2 : spABlk j b = 2 := by rw [hab, ha2]; decide
        rcases spABlk_fin_three_cases (spABlk j c) with hc0 | hc1 | hc2
        · have hpc : spABlk j (par c) = 1 := by rw [hbp, hc0]; decide
          rw [hg.2 (par c) b hpc (by rw [hb2]; decide), mul_zero, mul_zero]
        · rw [hg.2 c a hc1 (by rw [ha2]; decide), zero_mul]
        · exact absurd (hc2.trans ha2.symm) hca
  · rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply, ite_eq_right_iff.2
      (fun h => absurd (by rw [h, hbp]) hab)]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hca : spABlk j c = spABlk j a
    · have hpc : ¬ spABlk j (par c) = spABlk j b := fun h => hab (by rw [← h, hbp, hca])
      simp only [hpc, ite_false, mul_zero]
    · simp only [hca, ite_false, zero_mul]

theorem spABlockCond_of_commute (hjn : 2 * j ≤ n) {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (h : G * spANil K n j = spANil K n j * G) : SpABlockCond j G := by
  refine ⟨fun r u hu hr => ?_, fun u t hu ht => ?_⟩
  · rcases u with m | m
    · have hm : m.val < 2 * j := by
        by_contra hm
        simp [hm] at hu
      have e := congrFun (congrFun h r) (Sum.inr (spAPar m))
      rw [mul_spANil_inr hjn, ite_eq_left (spAPar_lt hjn hm), spAPar_spAPar hjn hm] at e
      rw [e]
      rcases r with k | k
      · have hk : ¬ k.val < 2 * j := fun hk => hr (by simp [hk])
        rw [spANil_mul_inl hjn, ite_eq_right hk]
      · rw [spANil_mul_inr]
    · exfalso
      by_cases hm : m.val < 2 * j <;> simp [hm] at hu
  · rcases u with m | m
    · exfalso
      by_cases hm : m.val < 2 * j <;> simp [hm] at hu
    · have hm : m.val < 2 * j := by
        by_contra hm
        simp [hm] at hu
      have e := congrFun (congrFun h (Sum.inl (spAPar m))) t
      rw [spANil_mul_inl hjn, ite_eq_left (spAPar_lt hjn hm), spAPar_spAPar hjn hm] at e
      rw [← e]
      rcases t with l | l
      · rw [mul_spANil_inl]
      · have hl : ¬ l.val < 2 * j := fun hl => ht (by simp [hl])
        rw [mul_spANil_inr hjn, ite_eq_right hl]

theorem spALeviPart_commute (hjn : 2 * j ≤ n) {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (h : G * spANil K n j = spANil K n j * G) :
    spALeviPart j G * spANil K n j = spANil K n j * spALeviPart j G := by
  ext r t
  rcases t with l | l
  · rw [mul_spANil_inl]
    rcases r with k | k
    · rw [spANil_mul_inl hjn]
      split_ifs with hk
      · rw [spALeviPart_apply, ite_eq_right]
        intro hb
        have h1 := spAPar_lt hjn hk
        by_cases hl : l.val < 2 * j <;> simp [h1, hl] at hb
      · rfl
    · rw [spANil_mul_inr]
  · rw [mul_spANil_inr hjn]
    rcases r with k | k
    · rw [spANil_mul_inl hjn]
      by_cases hl : l.val < 2 * j <;> by_cases hk : k.val < 2 * j
      · have e := congrFun (congrFun h (Sum.inl k)) (Sum.inr l)
        rw [mul_spANil_inr hjn, spANil_mul_inl hjn, ite_eq_left hl, ite_eq_left hk] at e
        rw [ite_eq_left hl, ite_eq_left hk, spALeviPart_apply, spALeviPart_apply,
          ite_eq_left (by simp [hk, spAPar_lt hjn hl]),
          ite_eq_left (by simp [hl, spAPar_lt hjn hk]), e]
      · rw [ite_eq_left hl, ite_eq_right hk, spALeviPart_apply, ite_eq_right]
        simp [hk, spAPar_lt hjn hl]
      · rw [ite_eq_right hl, ite_eq_left hk, spALeviPart_apply, ite_eq_right]
        simp [hl, spAPar_lt hjn hk]
      · rw [ite_eq_right hl, ite_eq_right hk]
    · rw [spANil_mul_inr]
      split_ifs with hl
      · rw [spALeviPart_apply, ite_eq_right]
        by_cases hk : k.val < 2 * j <;> simp [hk, spAPar_lt hjn hl]
      · rfl

end Levi

section Hom

variable {j : ℕ} (hjn : 2 * j ≤ n)
include hjn

theorem spABlockCond_of_mem {g : StatedSp n K}
    (hg : g ∈ centralizer ({spARep n j} : Set (StatedSp n K))) : SpABlockCond j (mat n K g) :=
  spABlockCond_of_commute hjn (commute_spARep_iff.1 (mem_centralizer_singleton_iff.1 hg))

@[expose] noncomputable def spALeviHom :
    centralizer ({spARep n j} : Set (StatedSp n K)) →* StatedSp n K where
  toFun g := ofSymplecticMat (spALeviPart j (mat n K g))
    (spALeviPart_symplectic (spABlockCond_of_mem hjn g.2))
  map_one' := mat_injective (by
    rw [mat_ofSymplecticMat, OneMemClass.coe_one, map_one, spALeviPart_one])
  map_mul' g h := mat_injective (by
    rw [map_mul, mat_ofSymplecticMat, mat_ofSymplecticMat, mat_ofSymplecticMat,
      Subgroup.coe_mul, map_mul]
    exact spALeviPart_mul (spABlockCond_of_mem hjn g.2) (spABlockCond_of_mem hjn h.2))

theorem mat_spALeviHom (g : centralizer ({spARep n j} : Set (StatedSp n K))) :
    mat n K (spALeviHom hjn g) = spALeviPart j (mat n K g) := rfl

theorem spALeviHom_mem_centralizer (g : centralizer ({spARep n j} : Set (StatedSp n K))) :
    spALeviHom hjn g ∈ centralizer ({spARep n j} : Set (StatedSp n K)) := by
  rw [mem_centralizer_singleton_iff, commute_spARep_iff, mat_spALeviHom]
  exact spALeviPart_commute hjn (commute_spARep_iff.1 (mem_centralizer_singleton_iff.1 g.2))

theorem spALeviHom_spALeviHom (g : centralizer ({spARep n j} : Set (StatedSp n K))) :
    spALeviHom hjn ⟨spALeviHom hjn g, spALeviHom_mem_centralizer hjn g⟩ = spALeviHom hjn g := by
  apply mat_injective
  rw [mat_spALeviHom, mat_spALeviHom]
  exact spALeviPart_spALeviPart _

omit hjn in
variable (K n j) in
@[expose] noncomputable def spARadical (hjn : 2 * j ≤ n) : Subgroup (StatedSp n K) :=
  (spALeviHom hjn).ker.map (centralizer ({spARep n j} : Set (StatedSp n K))).subtype

theorem mem_spARadical_iff {x : StatedSp n K} :
    x ∈ spARadical K n j hjn ↔ ∃ hx : x ∈ centralizer ({spARep n j} : Set (StatedSp n K)),
      spALeviHom hjn ⟨x, hx⟩ = 1 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, hg⟩
  · rintro ⟨hx, h1⟩
    exact ⟨⟨x, hx⟩, h1, rfl⟩

theorem spARadical_le_centralizer :
    spARadical K n j hjn ≤ centralizer ({spARep n j} : Set (StatedSp n K)) := by
  rintro _ ⟨g, -, rfl⟩
  exact g.2

theorem centralizer_spARep_le_sup :
    centralizer ({spARep n j} : Set (StatedSp n K)) ≤
      (spALeviHom hjn).range ⊔ spARadical K n j hjn := by
  set C := centralizer ({spARep n j} : Set (StatedSp n K))
  intro g hg
  set g' : C := ⟨g, hg⟩
  set m' : C := ⟨spALeviHom hjn g', spALeviHom_mem_centralizer hjn g'⟩
  have hq : ((g' * m'⁻¹ : C) : StatedSp n K) ∈ spARadical K n j hjn :=
    ⟨g' * m'⁻¹, show g' * m'⁻¹ ∈ (spALeviHom hjn).ker by
      rw [MonoidHom.mem_ker, map_mul, map_inv, spALeviHom_spALeviHom, mul_inv_cancel], rfl⟩
  have e : g = spALeviHom hjn g' * (spALeviHom hjn g')⁻¹ * ((g' * m'⁻¹ : C) : StatedSp n K) *
      spALeviHom hjn g' := by
    simp [g', m']
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ (mem_sup_right hq)) (mem_sup_left ⟨g', rfl⟩)
  rw [mul_inv_cancel]
  exact Subgroup.one_mem _

theorem spARadical_inf_range_eq_bot : spARadical K n j hjn ⊓ (spALeviHom hjn).range = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨hq, ⟨g, rfl⟩⟩
  obtain ⟨hx, h1⟩ := (mem_spARadical_iff hjn).1 hq
  have h2 : spALeviHom hjn ⟨spALeviHom hjn g, hx⟩ = spALeviHom hjn g :=
    spALeviHom_spALeviHom hjn g
  rw [h1] at h2
  rw [mem_bot, ← h2]

theorem range_spALeviHom_le_normalizer :
    (spALeviHom hjn).range ≤ normalizer (spARadical K n j hjn : Set (StatedSp n K)) := by
  set C := centralizer ({spARep n j} : Set (StatedSp n K))
  have key : ∀ (c : StatedSp n K) (hc : c ∈ C) {x : StatedSp n K}, x ∈ spARadical K n j hjn →
      c * x * c⁻¹ ∈ spARadical K n j hjn := by
    intro c hc x hx
    obtain ⟨hxC, h1⟩ := (mem_spARadical_iff hjn).1 hx
    refine (mem_spARadical_iff hjn).2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hxC)
      (Subgroup.inv_mem _ hc), ?_⟩
    have e : (⟨c * x * c⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hxC)
        (Subgroup.inv_mem _ hc)⟩ : C) = ⟨c, hc⟩ * ⟨x, hxC⟩ * (⟨c, hc⟩ : C)⁻¹ := rfl
    rw [e, map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]
  rintro _ ⟨g, rfl⟩
  have hmC := spALeviHom_mem_centralizer hjn g
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key _ hmC, fun hx => ?_⟩
  have := key _ (Subgroup.inv_mem _ hmC) hx
  simpa [mul_assoc] using this

end Hom

section TwoGroup

variable {j : ℕ}

@[expose] def spAOrd : Fin 3 → ℕ := ![0, 2, 1]

theorem spAOrd_le_two (x : Fin 3) : spAOrd x ≤ 2 := by
  fin_cases x <;> simp [spAOrd]

theorem spA_cube_eq_zero {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hM : ∀ r t, M r t ≠ 0 → spAOrd (spABlk j r) < spAOrd (spABlk j t)) : M * M * M = 0 := by
  have h2 : ∀ r t, (M * M) r t ≠ 0 → spAOrd (spABlk j r) + 2 ≤ spAOrd (spABlk j t) := by
    intro r t h
    rw [Matrix.mul_apply] at h
    obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 := hM r u (left_ne_zero_of_mul hu)
    have h2 := hM u t (right_ne_zero_of_mul hu)
    omega
  ext r t
  rw [Matrix.zero_apply]
  by_contra h
  rw [Matrix.mul_apply] at h
  obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 := h2 r u (left_ne_zero_of_mul hu)
  have h3 := hM u t (right_ne_zero_of_mul hu)
  have h4 := spAOrd_le_two (spABlk j t)
  omega

variable [CharP K 2] (hjn : 2 * j ≤ n)
include hjn

theorem pow_four_eq_one_of_mem_spARadical {x : StatedSp n K} (hx : x ∈ spARadical K n j hjn) :
    x ^ 4 = 1 := by
  obtain ⟨hxC, h1⟩ := (mem_spARadical_iff hjn).1 hx
  have hc := spABlockCond_of_mem hjn hxC
  have hL : spALeviPart j (mat n K x) = 1 := by
    have := congrArg (mat n K) h1
    rwa [mat_spALeviHom, map_one] at this
  set G := mat n K x with hG
  set M := G - 1 with hMdef
  have hM : ∀ r t, M r t ≠ 0 → spAOrd (spABlk j r) < spAOrd (spABlk j t) := by
    intro r t h
    rw [hMdef, Matrix.sub_apply] at h
    by_cases hrt : spABlk j r = spABlk j t
    · have e := congrFun (congrFun hL r) t
      rw [spALeviPart_apply, ite_eq_left hrt] at e
      exact absurd (by rw [e, sub_self]) h
    · have hrt' : r ≠ t := fun h' => hrt (by rw [h'])
      rw [Matrix.one_apply_ne hrt', sub_zero] at h
      have ht0 : spABlk j t ≠ 0 := fun ht => h (hc.1 r t ht (fun hr => hrt (hr.trans ht.symm)))
      have hr1 : spABlk j r ≠ 1 := fun hr => h (hc.2 r t hr (fun ht => hrt (hr.trans ht.symm)))
      rcases spABlk_fin_three_cases (spABlk j r) with h0 | h1 | h2 <;>
        rcases spABlk_fin_three_cases (spABlk j t) with h0' | h1' | h2' <;>
        simp_all [spAOrd]
  have hM3 := spA_cube_eq_zero hM
  have hMM : M + M = 0 := by rw [← two_smul K M, CharTwo.two_eq_zero, zero_smul]
  have hGM : G = 1 + M := by rw [hMdef, add_sub_cancel]
  have hsq : G * G = 1 + M * M := by
    rw [hGM, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, add_assoc, ← add_assoc M M, hMM, zero_add]
  have hMM2 : M * M + M * M = 0 := by rw [← two_smul K (M * M), CharTwo.two_eq_zero, zero_smul]
  have h4 : G * G * (G * G) = 1 := by
    rw [hsq, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, add_assoc, ← add_assoc (M * M) (M * M), hMM2, zero_add,
      ← Matrix.mul_assoc, hM3, Matrix.zero_mul, add_zero]
  apply mat_injective
  rw [map_pow, map_one, show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two, ← hG, h4]

theorem isPGroup_spARadical : IsPGroup 2 (spARadical K n j hjn) := by
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
  exact pow_four_eq_one_of_mem_spARadical hjn g.2

end TwoGroup

end CFSG.SeitzReduction.SymplecticPilot
