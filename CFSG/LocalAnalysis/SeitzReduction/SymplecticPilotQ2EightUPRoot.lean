module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryModel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)

section Matrix

variable {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ}

omit σ in
theorem diagonal_mul_single_ctua (t : Fin n → F) (i j : Fin n) (c : F) :
    diagonal t * single i j c = single i j (t i * c) := by
  ext a b
  rw [diagonal_mul, single_apply, single_apply]
  split_ifs with h
  · rw [h.1]
  · rw [mul_zero]

omit σ in
theorem single_mul_diagonal_ctua (t : Fin n → F) (i j : Fin n) (c : F) :
    single i j c * diagonal t = single i j (c * t j) := by
  ext a b
  rw [mul_diagonal, single_apply, single_apply]
  split_ifs with h
  · rw [h.2]
  · rw [zero_mul]

theorem diagonal_mul_rootMatrix {t : Fin n → F} {i j : Fin n} (hj : t j ≠ 0)
    (hui : σ (t i) * t (Fin.rev i) = 1) (huj : σ (t j) * t (Fin.rev j) = 1) (c : F) :
    diagonal t * rootMatrix σ i j c = rootMatrix σ i j (t i * (t j)⁻¹ * c) * diagonal t := by
  have h1 : t (Fin.rev j) = (σ (t j))⁻¹ := eq_inv_of_mul_eq_one_right huj
  have e1 : t i * c = t i * (t j)⁻¹ * c * t j := by field_simp
  have e2 : t (Fin.rev j) * σ c = σ (t i * (t j)⁻¹ * c) * t (Fin.rev i) := by
    rw [map_mul, map_mul, map_inv₀, h1]
    calc (σ (t j))⁻¹ * σ c = (σ (t j))⁻¹ * σ c * (σ (t i) * t (Fin.rev i)) := by
          rw [hui, mul_one]
      _ = σ (t i) * (σ (t j))⁻¹ * σ c * t (Fin.rev i) := by ring
  rw [rootMatrix, rootMatrix]
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, diagonal_mul_single_ctua, single_mul_diagonal_ctua]
  rw [e1, e2]

theorem rootMatrix_rev_rev_ctua (hσ : ∀ c, σ (σ c) = c) (i j : Fin n) (c : F) :
    rootMatrix σ (Fin.rev j) (Fin.rev i) c = rootMatrix σ i j (-σ c) := by
  rw [rootMatrix, rootMatrix, Fin.rev_rev, Fin.rev_rev, map_neg, hσ, ← Matrix.single_neg,
    ← Matrix.single_neg]
  abel

end Matrix

section Group

variable {F : Type*} [Field F] (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c) {n : ℕ}

theorem conj_rootHom_of_diagonal {g : SU σ n} {t : Fin n → F}
    (hg : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal t) {i j : Fin n}
    (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) (c : Multiplicative F) :
    g * rootHom σ hσ hij hi hj c * g⁻¹ =
      rootHom σ hσ hij hi hj (Multiplicative.ofAdd (t i * (t j)⁻¹ * Multiplicative.toAdd c)) := by
  have hu := unitary_of_coe_eq_diagonal hg
  have htj : t j ≠ 0 := by
    intro h
    have h' := hu (Fin.rev j)
    rw [Fin.rev_rev, h, mul_zero] at h'
    exact zero_ne_one h'
  apply mul_inv_eq_of_eq_mul
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hg, coe_rootHom,
    coe_rootHom, toAdd_ofAdd]
  exact diagonal_mul_rootMatrix σ htj (hu i) (hu j) _

theorem rootHom_rev_rev_ctua {i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) (hij' : Fin.rev j ≠ Fin.rev i) (hi' : Fin.rev j ≠ Fin.rev (Fin.rev j))
    (hj' : Fin.rev i ≠ Fin.rev (Fin.rev i)) (c : Multiplicative F) :
    rootHom σ hσ hij' hi' hj' c =
      rootHom σ hσ hij hi hj (Multiplicative.ofAdd (-σ (Multiplicative.toAdd c))) :=
  Subtype.ext (Units.ext (by rw [coe_rootHom, coe_rootHom, toAdd_ofAdd,
    rootMatrix_rev_rev_ctua σ hσ]))

variable {σ} {hσ}

theorem rankOne_short_le_of_rootHom {k : Fin (n / 2)} (hk : k.val + 1 < n / 2)
    {H : Subgroup (SU σ n)}
    (hH : ∀ (i j : Fin n) (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j),
      ((i = lowIdx k ∧ j = lowIdx ⟨k.val + 1, hk⟩) ∨
        (i = Fin.rev (lowIdx ⟨k.val + 1, hk⟩) ∧ j = Fin.rev (lowIdx k)) ∨
        (i = lowIdx ⟨k.val + 1, hk⟩ ∧ j = lowIdx k) ∨
        (i = Fin.rev (lowIdx k) ∧ j = Fin.rev (lowIdx ⟨k.val + 1, hk⟩))) →
      (rootHom σ hσ hij hi hj).range ≤ H) :
    rankOne (rootGroup σ hσ n) k ≤ H := by
  obtain ⟨h1, h2, h3, h4⟩ := short_facts (n := n) hk
  have h5 : lowIdx (n := n) k ≠ Fin.rev (lowIdx ⟨k.val + 1, hk⟩) := lowIdx_ne_rev _ _
  have hX : ∀ γ : Fin (n / 2) → ℤ,
      (toStd n γ = weight n (lowIdx k) - weight n (lowIdx (n := n) ⟨k.val + 1, hk⟩) ∨
        toStd n γ = weight n (lowIdx (n := n) ⟨k.val + 1, hk⟩) - weight n (lowIdx k)) →
      rootGroup σ hσ n γ ≤ H := by
    intro γ hγ
    unfold rootGroup
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
        iSup_le fun hj => iSup_le fun _ => iSup_le fun hw => ?_
      apply hH i j hij hi hj
      rcases hγ with hγ | hγ <;> rw [hγ] at hw
      · rcases eq_of_weight_sub_eq_sub h1 h2 h3 h4 hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · rcases eq_of_weight_sub_eq_sub h1.symm h3 h2 h5 hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · refine iSup_le fun i => iSup_le fun _ => iSup_le fun hw => ?_
      exfalso
      have hkk := congrFun hw k
      have hlt : 2 * (k.val + 1) < n := by omega
      rcases hγ with hγ | hγ <;> rw [hγ] at hkk <;>
        simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, Pi.sub_apply, weight_apply',
          val_lowIdx] at hkk <;>
        split_ifs at hkk <;> omega
    · refine iSup_le fun i => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
        iSup_le fun _ => iSup_le fun hw => ?_
      exfalso
      rcases hγ with hγ | hγ <;> rw [hγ] at hw
      · exact weight_ne_weight_sub h1 h2 h3 h4 hw
      · exact weight_ne_weight_sub h1.symm h3 h2 h5 hw
  exact sup_le (hX _ (Or.inl (toStd_short hk))) (hX _ (Or.inr (toStd_short_neg hk)))

end Group

section Four

variable {F : Type*} [Field F] [CharP F 2]

theorem mul_self_ne_one_of_ne_one_charTwo {x : F} (hx : x ≠ 1) : x * x ≠ 1 := by
  intro h
  apply hx
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h3 : (x + 1) * (x + 1) = 0 := by linear_combination h + (x + 1) * h2
  have h4 : x + 1 = 0 := mul_self_eq_zero.1 h3
  linear_combination h4 - h2

theorem eq_zero_or_one_or_of_card_four_ctua [Fintype F] (hF : Fintype.card F = 4) {x : F}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) (c : F) : c = 0 ∨ c = 1 ∨ c = x ∨ c = 1 + x := by
  classical
  by_contra h
  simp only [not_or] at h
  obtain ⟨h0, h1, hx, h1x⟩ := h
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hy0 : (1 : F) + x ≠ 0 := fun h => hx1 (by linear_combination h - h2)
  have hy1 : (1 : F) + x ≠ 1 := fun h => hx0 (by linear_combination h)
  have hyx : (1 : F) + x ≠ x := fun h => one_ne_zero (by linear_combination h)
  have hcard : ({c, 0, 1, x, 1 + x} : Finset F).card = 5 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h0, h1, hx, h1x⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨zero_ne_one, hx0.symm, hy0.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hx1.symm, hy1.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact hyx.symm),
      Finset.card_singleton]
  have hle := Finset.card_le_univ ({c, 0, 1, x, 1 + x} : Finset F)
  rw [hcard, hF] at hle
  omega

variable {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c} {n : ℕ}

theorem rootHom_mem_of_card_four [Fintype F] (hF : Fintype.card F = 4) {i j : Fin n}
    {hij : i ≠ j} {hi : i ≠ Fin.rev i} {hj : j ≠ Fin.rev j} {H : Subgroup (SU σ n)} {x : F}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (h1 : rootHom σ hσ hij hi hj (Multiplicative.ofAdd 1) ∈ H)
    (hx : rootHom σ hσ hij hi hj (Multiplicative.ofAdd x) ∈ H) (c : F) :
    rootHom σ hσ hij hi hj (Multiplicative.ofAdd c) ∈ H := by
  rcases eq_zero_or_one_or_of_card_four_ctua hF hx0 hx1 c with rfl | rfl | rfl | rfl
  · rw [ofAdd_zero, map_one]
    exact one_mem H
  · exact h1
  · exact hx
  · rw [ofAdd_add, map_mul]
    exact mul_mem h1 hx

theorem rankOne_short_le_of_shortTorus [Fintype F] (hF : Fintype.card F = 4)
    {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) {ω : F} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1)
    {H : Subgroup (SU σ n)}
    (hd : shortTorus σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _) ω ∈ H)
    (h1 : rootHom σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _)
      (Multiplicative.ofAdd 1) ∈ H)
    (h2 : rootHom σ hσ (lowIdx_ne_succ hk).symm (lowIdx_ne_rev _ _) (lowIdx_ne_rev k k)
      (Multiplicative.ofAdd 1) ∈ H) :
    rankOne (rootGroup σ hσ n) k ≤ H := by
  obtain ⟨g1, g2, g3, g4⟩ := short_facts (n := n) hk
  have hdmat := coe_shortTorus σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _)
    (lowIdx_ne_rev _ _) hω0
  have hta : shortTorusFun σ (lowIdx (n := n) k) (lowIdx ⟨k.val + 1, hk⟩) ω (lowIdx k) = ω :=
    shortTorusFun_left _ _ ω
  have htb : shortTorusFun σ (lowIdx (n := n) k) (lowIdx ⟨k.val + 1, hk⟩) ω
      (lowIdx ⟨k.val + 1, hk⟩) = ω⁻¹ := shortTorusFun_right g1 ω
  have hinv0 : ω⁻¹ ≠ 0 := inv_ne_zero hω0
  have hinv1 : ω⁻¹ ≠ 1 := fun h => hω1 (by rw [← inv_inv ω, h, inv_one])
  have hab : ∀ c : F, rootHom σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _)
      (Multiplicative.ofAdd c) ∈ H := by
    have hx : rootHom σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _)
        (Multiplicative.ofAdd (ω * ω)) ∈ H := by
      have h := conj_rootHom_of_diagonal σ hσ hdmat (lowIdx_ne_succ hk) (lowIdx_ne_rev k k)
        (lowIdx_ne_rev _ _) (Multiplicative.ofAdd 1)
      rw [hta, htb, inv_inv, toAdd_ofAdd, mul_one] at h
      rw [← h]
      exact mul_mem (mul_mem hd h1) (inv_mem hd)
    exact rootHom_mem_of_card_four hF (mul_ne_zero hω0 hω0)
      (mul_self_ne_one_of_ne_one_charTwo hω1) h1 hx
  have hba : ∀ c : F, rootHom σ hσ (lowIdx_ne_succ hk).symm (lowIdx_ne_rev _ _)
      (lowIdx_ne_rev k k) (Multiplicative.ofAdd c) ∈ H := by
    have hx : rootHom σ hσ (lowIdx_ne_succ hk).symm (lowIdx_ne_rev _ _) (lowIdx_ne_rev k k)
        (Multiplicative.ofAdd (ω⁻¹ * ω⁻¹)) ∈ H := by
      have h := conj_rootHom_of_diagonal σ hσ hdmat (lowIdx_ne_succ hk).symm (lowIdx_ne_rev _ _)
        (lowIdx_ne_rev k k) (Multiplicative.ofAdd 1)
      rw [hta, htb, toAdd_ofAdd, mul_one] at h
      rw [← h]
      exact mul_mem (mul_mem hd h2) (inv_mem hd)
    exact rootHom_mem_of_card_four hF (mul_ne_zero hinv0 hinv0)
      (mul_self_ne_one_of_ne_one_charTwo hinv1) h2 hx
  refine rankOne_short_le_of_rootHom hk fun i j hij hi hj hcase => ?_
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rintro _ ⟨c, rfl⟩
    exact hab (Multiplicative.toAdd c)
  · rintro _ ⟨c, rfl⟩
    rw [rootHom_rev_rev_ctua σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _)]
    exact hab _
  · rintro _ ⟨c, rfl⟩
    exact hba (Multiplicative.toAdd c)
  · rintro _ ⟨c, rfl⟩
    rw [rootHom_rev_rev_ctua σ hσ (lowIdx_ne_succ hk).symm (lowIdx_ne_rev _ _)
      (lowIdx_ne_rev k k)]
    exact hba _

end Four

section Model

variable {F : Type} [Field F] {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c} {N ε : ℕ}

theorem shortTorusFun_rev_left {n : ℕ} {a b : Fin n} (h1 : Fin.rev a ≠ a) (h2 : Fin.rev a ≠ b)
    (c : F) : shortTorusFun σ a b c (Fin.rev a) = (σ c)⁻¹ := by
  simp [shortTorusFun, h1, h2]

theorem shortTorusFun_rev_right {n : ℕ} {a b : Fin n} (h1 : Fin.rev b ≠ a) (h2 : Fin.rev b ≠ b)
    (h3 : Fin.rev b ≠ Fin.rev a) (c : F) : shortTorusFun σ a b c (Fin.rev b) = σ c := by
  simp [shortTorusFun, h1, h2, h3]

theorem eq_or_eq_rev_of_mem_ctuPlanes_singleton (hε : ε ≤ 1) {p : Fin N}
    {s : Fin (2 * N + ε)} (hs : s ∈ ctuPlanes ε {p}) :
    s = ctuCoord N ε (Sum.inl (Sum.inl p)) ∨ s = Fin.rev (ctuCoord N ε (Sum.inl (Sum.inl p))) := by
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective s
  rw [ctuCoord_mem_ctuPlanes] at hs
  rcases w with (q | q) | i
  · simp only [inPlanes_inl, planeOf_inl, Finset.mem_singleton] at hs
    subst hs
    exact Or.inl rfl
  · simp only [inPlanes_inl, planeOf_inr, Finset.mem_singleton] at hs
    subst hs
    right
    rw [ctuCoord_rev hε, ctuPar_inl, par_inl]
  · exact absurd hs (not_inPlanes_inr _ i)

theorem shortTorus_mem_ctuBlock {a b : Fin (2 * N + ε)} (hab : a ≠ b) (ha : a ≠ Fin.rev a)
    (hb : b ≠ Fin.rev b) (hba : b ≠ Fin.rev a) {c : F} (hc : c ≠ 0) {R : Finset (Fin N)}
    (hR : ∀ s ∈ ctuPlanes ε R, s ≠ a ∧ s ≠ b ∧ s ≠ Fin.rev a ∧ s ≠ Fin.rev b) :
    shortTorus σ hσ hab ha hb c ∈ ctuBlock σ ε R := by
  rw [mem_ctuBlock]
  intro i j hij
  rw [coe_shortTorus σ hσ hab ha hb hba hc]
  by_cases h : i = j
  · subst h
    have hi : i ∈ ctuPlanes ε R := hij.elim id id
    obtain ⟨h1, h2, h3, h4⟩ := hR i hi
    rw [diagonal_apply_eq, one_apply_eq, shortTorusFun_of_ne h1 h2 h3 h4]
  · rw [diagonal_apply_ne _ h, one_apply_ne h]

theorem commute_diagonal_ctuEmbed {K : Type} [Field K] [CharP K 2] {hε : ε ≤ 1} {ι : K →+* F}
    {hι : ∀ c, σ (ι c) = ι c} {g : SU σ (2 * N + ε)} {t : Fin (2 * N + ε) → F}
    (hg : ((g : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) =
      diagonal t) {p : Fin N}
    (ht : ∀ s ∈ ctuPlanes ε {p}, ∀ s' ∈ ctuPlanes ε {p}, t s = t s') {y : StatedSp N K}
    (hy : y ∈ spBlock K {p}) : g * ctuEmbed ε hε σ ι hι y = ctuEmbed ε hε σ ι hι y * g := by
  have hM := mem_blockSpecialLinear.1
    (ctuToSL_ctuEmbed_mem_blockSpecialLinear (σ := σ) (hε := hε) (ι := ι) (hι := hι) hy)
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hg]
  ext i j
  rw [diagonal_mul, mul_diagonal]
  by_cases hij : i ∈ ctuPlanes ε {p} ∧ j ∈ ctuPlanes ε {p}
  · rw [ht i hij.1 j hij.2, mul_comm]
  · have h1 := hM i j (not_and_or.1 hij)
    rw [coe_ctuToSL] at h1
    rw [h1]
    by_cases h : i = j
    · subst h
      rw [one_apply_eq, mul_one, one_mul]
    · rw [one_apply_ne h, mul_zero, zero_mul]

theorem commute_shortTorus_ctuEmbed {K : Type} [Field K] [CharP K 2] {hε : ε ≤ 1}
    {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c} {a b : Fin (2 * N + ε)} (hab : a ≠ b)
    (ha : a ≠ Fin.rev a) (hb : b ≠ Fin.rev b) (hba : b ≠ Fin.rev a) {c : F} (hc0 : c ≠ 0)
    (hc : σ c * c = 1) {p : Fin N}
    (hp : (∀ s ∈ ctuPlanes ε {p}, s = a ∨ s = Fin.rev a) ∨
      (∀ s ∈ ctuPlanes ε {p}, s = b ∨ s = Fin.rev b)) {y : StatedSp N K}
    (hy : y ∈ spBlock K {p}) :
    shortTorus σ hσ hab ha hb c * ctuEmbed ε hε σ ι hι y =
      ctuEmbed ε hε σ ι hι y * shortTorus σ hσ hab ha hb c := by
  have hσc' : σ c = c⁻¹ := eq_inv_of_mul_eq_one_left hc
  have hσc : (σ c)⁻¹ = c := by rw [hσc', inv_inv]
  have hra : shortTorusFun σ a b c (Fin.rev a) = shortTorusFun σ a b c a := by
    rw [shortTorusFun_rev_left (Ne.symm ha) (Ne.symm hba) c, shortTorusFun_left, hσc]
  have hrb : shortTorusFun σ a b c (Fin.rev b) = shortTorusFun σ a b c b := by
    rw [shortTorusFun_rev_right (fun h => hba (by rw [← h, Fin.rev_rev])) (Ne.symm hb)
      (fun h => hab (Fin.rev_injective h).symm) c, shortTorusFun_right hab, hσc']
  refine commute_diagonal_ctuEmbed (coe_shortTorus σ hσ hab ha hb hba hc0) ?_ hy
  intro s hs s' hs'
  rcases hp with hp | hp
  · rcases hp s hs with rfl | rfl <;> rcases hp s' hs' with rfl | rfl <;>
      simp only [hra]
  · rcases hp s hs with rfl | rfl <;> rcases hp s' hs' with rfl | rfl <;>
      simp only [hrb]

theorem shortTorus_pow_three {n : ℕ} {a b : Fin n} (hab : a ≠ b) (ha : a ≠ Fin.rev a)
    (hb : b ≠ Fin.rev b) (hba : b ≠ Fin.rev a) {c : F} (hc0 : c ≠ 0) (hc : c ^ 3 = 1) :
    shortTorus σ hσ hab ha hb c ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, coe_shortTorus σ hσ hab ha hb hba hc0,
    diagonal_pow, Subgroup.coe_one, Units.val_one, ← diagonal_one]
  congr 1
  funext s
  have hσ3 : σ c ^ 3 = 1 := by rw [← map_pow, hc, map_one]
  simp only [Pi.pow_apply, shortTorusFun]
  split_ifs
  · exact hc
  · rw [inv_pow, hc, inv_one]
  · rw [inv_pow, hσ3, inv_one]
  · exact hσ3
  · exact one_pow 3

end Model

end CFSG.SeitzReduction.SymplecticPilot
