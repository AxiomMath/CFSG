module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniMatrix
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherHermitian

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.AGLEmbedding.LeviBlock

section Transvection

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ} (h : UnitaryFieldData p f K)

@[expose] noncomputable def tvMat (v : HypIndex r ε → K) (a : K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K :=
  1 + Matrix.vecMulVec (a • v) (fun j => h.bar (v (hypPartner j)))

theorem dotProduct_partner (v x : HypIndex r ε → K) :
    (fun j => h.bar (v (hypPartner j))) ⬝ᵥ x = hypForm h r ε v x := by
  rw [hypForm_apply, dotProduct]
  exact Fintype.sum_equiv (Function.Involutive.toPerm hypPartner hypPartner_involutive) _ _
    (fun j => by simp)

variable {h}

theorem tvMat_mulVec (v : HypIndex r ε → K) (a : K) (x : HypIndex r ε → K) :
    tvMat h v a *ᵥ x = x + (a * hypForm h r ε v x) • v := by
  rw [tvMat, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
    dotProduct_partner h]
  rw [op_smul_eq_smul, smul_smul, mul_comm]

theorem det_tvMat (v : HypIndex r ε → K) (a : K) :
    (tvMat h v a).det = 1 + a * hypForm h r ε v v := by
  have hu : (tvMat h v a) = 1 + Matrix.replicateCol Unit (a • v) *
      Matrix.replicateRow Unit (fun j => h.bar (v (hypPartner j))) := by
    rw [tvMat, Matrix.vecMulVec_eq Unit]
  rw [hu, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    dotProduct_partner h]
  simp [smul_eq_mul]

theorem hypForm_tvMat_mulVec {v : HypIndex r ε → K} (hv : hypForm h r ε v v = 0) {a : K}
    (ha : a + h.bar a = 0) (x y : HypIndex r ε → K) :
    hypForm h r ε (tvMat h v a *ᵥ x) (tvMat h v a *ᵥ y) = hypForm h r ε x y := by
  rw [tvMat_mulVec, tvMat_mulVec]
  have hsymm : ∀ u w : HypIndex r ε → K, h.bar (hypForm h r ε u w) = hypForm h r ε w u :=
    fun u w => (hypForm_isSymm h).eq u w
  simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hv,
    mul_zero, add_zero, map_mul, hsymm, RingHom.id_apply]
  have : h.bar a = -a := by linear_combination ha
  rw [this]
  ring

theorem exists_tv_mem {v : HypIndex r ε → K} (hv : hypForm h r ε v v = 0) {a : K}
    (ha : a + h.bar a = 0) : ∃ g : hypSU h r ε,
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = tvMat h v a := by
  have hdet : (tvMat h v a).det = 1 := by rw [det_tvMat, hv, mul_zero, add_zero]
  let g : GL (HypIndex r ε) K :=
    GeneralLinearGroup.mkOfDetNeZero _ (by rw [hdet]; exact one_ne_zero)
  exact ⟨⟨g, mem_gramSU_iff_isometry.mpr ⟨hypForm_tvMat_mulVec hv ha, hdet⟩⟩, rfl⟩

end Transvection

section Invariant

variable {f : ℕ} {K : Type} [Field K] {s ε : ℕ} (h : UnitaryFieldData 2 f K)

theorem hypForm_single_left (x : HypIndex s ε) (w : HypIndex s ε → K) :
    hypForm h s ε (Pi.single x 1) w = w (hypPartner x) := by
  rw [hypForm_apply, Finset.sum_eq_single x]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

theorem hypForm_single_single (x y : HypIndex s ε) :
    hypForm h s ε (Pi.single x 1) (Pi.single y 1) = if y = hypPartner x then 1 else 0 := by
  rw [hypForm_single_left]
  simp [Pi.single_apply, eq_comm]

theorem exists_add_bar_eq_one : ∃ c : K, c + h.bar c = 1 := by
  haveI : CharP K 2 := h.charP
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  have hu : c₀ + h.bar c₀ ≠ 0 := fun h0 => hc₀ (by
    have := CharTwo.add_eq_zero.mp h0
    exact this.symm)
  have hubar : h.bar (c₀ + h.bar c₀) = c₀ + h.bar c₀ := by
    rw [map_add, h.bar_bar, add_comm]
  refine ⟨c₀ / (c₀ + h.bar c₀), ?_⟩
  rw [map_div₀, hubar, ← add_div, div_self hu]

theorem eq_top_of_invariant (hs : 1 ≤ s) (W : Submodule K (HypIndex s ε → K))
    (hW : ∀ v : HypIndex s ε → K, hypForm h s ε v v = 0 → ∀ w ∈ W, hypForm h s ε v w • v ∈ W)
    (w₀ : HypIndex s ε → K) (hw₀ : w₀ ∈ W) (hw₀0 : w₀ ≠ 0) : W = ⊤ := by
  haveI : CharP K 2 := h.charP
  set e₀ : HypIndex s ε := .inl ⟨0, hs⟩ with he₀
  set f₀ : HypIndex s ε := .inr (.inr ⟨0, hs⟩) with hf₀
  have hef : hypPartner e₀ = f₀ := rfl
  have hfe : hypPartner f₀ = e₀ := rfl
  have hne : e₀ ≠ f₀ := by simp [he₀, hf₀]
  have stepA : ∀ y : HypIndex s ε, hypPartner y ≠ y → ∀ w ∈ W, w y ≠ 0 →
      (Pi.single (hypPartner y) (1 : K) : HypIndex s ε → K) ∈ W := by
    intro y hy w hw hwy
    have hiso : hypForm h s ε (Pi.single (hypPartner y) 1) (Pi.single (hypPartner y) 1) = 0 := by
      rw [hypForm_single_single, if_neg]
      intro hc
      exact hy (by rw [hypPartner_hypPartner] at hc; exact hc)
    have h1 := hW _ hiso w hw
    rw [hypForm_single_left, hypPartner_hypPartner] at h1
    have h2 := W.smul_mem (w y)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hwy, one_smul] at h2
  obtain ⟨c, hc⟩ := exists_add_bar_eq_one h
  have hv₁ : ∀ y : HypIndex s ε, hypPartner y = y →
      hypForm h s ε (Pi.single e₀ 1 + Pi.single y 1 + c • Pi.single f₀ 1)
        (Pi.single e₀ 1 + Pi.single y 1 + c • Pi.single f₀ 1) = 0 := by
    intro y hy
    have hye : y ≠ e₀ := fun he => by rw [he, hef] at hy; exact hne hy.symm |>.elim
    have hyf : y ≠ f₀ := fun he => by rw [he, hfe] at hy; exact hne hy |>.elim
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      hypForm_single_single, RingHom.id_apply, hy, hef, hfe, hye, hyf, hne, hne.symm, hye.symm,
      hyf.symm, if_true, if_false, mul_one, mul_zero, add_zero, zero_add, map_one]
    linear_combination hc + CharTwo.add_self_eq_zero (1 : K)
  have hef' : hypPartner e₀ ≠ e₀ := by rw [hef]; exact hne.symm
  have hfe' : hypPartner f₀ ≠ f₀ := by rw [hfe]; exact hne
  have step1 : ∃ x : HypIndex s ε, hypPartner x ≠ x ∧
      (Pi.single x (1 : K) : HypIndex s ε → K) ∈ W := by
    by_cases hnz : ∃ y : HypIndex s ε, hypPartner y ≠ y ∧ w₀ y ≠ 0
    · obtain ⟨y, hy, hwy⟩ := hnz
      exact ⟨hypPartner y, by rw [hypPartner_hypPartner]; exact hy.symm, stepA y hy w₀ hw₀ hwy⟩
    · push Not at hnz
      obtain ⟨y, hy⟩ : ∃ y, w₀ y ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hw₀0 (funext hall)
      have hyz : hypPartner y = y := by
        by_contra hne'
        exact hy (hnz y hne')
      have hye : y ≠ e₀ := fun he => by rw [he, hef] at hyz; exact hne hyz.symm |>.elim
      have hyf : y ≠ f₀ := fun he => by rw [he, hfe] at hyz; exact hne hyz |>.elim
      have h1 := hW _ (hv₁ y hyz) w₀ hw₀
      have hform : hypForm h s ε (Pi.single e₀ 1 + Pi.single y 1 + c • Pi.single f₀ 1) w₀ =
          w₀ y := by
        simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
          hypForm_single_left, hef, hfe, hyz, RingHom.id_apply]
        rw [hnz f₀ hfe', hnz e₀ hef']
        ring
      rw [hform] at h1
      have h2 := W.smul_mem (w₀ y)⁻¹ h1
      rw [smul_smul, inv_mul_cancel₀ hy, one_smul] at h2
      have he₀v : (Pi.single e₀ 1 + Pi.single y 1 + c • Pi.single f₀ 1 :
          HypIndex s ε → K) e₀ ≠ 0 := by
        simp [Pi.single_apply, hye.symm, hne]
      have h3 := stepA e₀ hef' _ h2 he₀v
      rw [hef] at h3
      exact ⟨f₀, hfe', h3⟩
  obtain ⟨x, hx, hxW⟩ := step1
  have hx' : (Pi.single (hypPartner x) 1 : HypIndex s ε → K) ∈ W :=
    stepA x hx _ hxW (by simp)
  have step2 : ∀ y : HypIndex s ε, hypPartner y ≠ y →
      (Pi.single y (1 : K) : HypIndex s ε → K) ∈ W := by
    intro y hy
    by_cases hyx : y = x
    · rw [hyx]
      exact hxW
    by_cases hyx' : y = hypPartner x
    · rw [hyx']
      exact hx'
    have hy1 : y ≠ hypPartner y := fun h' => hy h'.symm
    have hiso : hypForm h s ε (Pi.single y 1 + Pi.single (hypPartner x) 1)
        (Pi.single y 1 + Pi.single (hypPartner x) 1) = 0 := by
      simp only [map_add, LinearMap.add_apply, hypForm_single_single, hypPartner_hypPartner]
      have h2 : hypPartner x ≠ hypPartner y := fun h' => hyx (hypPartner_injective h').symm
      have h3 : hypPartner x ≠ x := fun h' => hx h'
      simp [hy1, h2, h3, hyx, hyx', Ne.symm hyx, Ne.symm hyx']
    have hform : hypForm h s ε (Pi.single y 1 + Pi.single (hypPartner x) 1)
        (Pi.single x 1) = 1 := by
      simp only [map_add, LinearMap.add_apply, hypForm_single_single, hypPartner_hypPartner]
      have h2 : x ≠ hypPartner y := fun h' => hyx' (by rw [h', hypPartner_hypPartner])
      simp [h2]
    have h1 := hW _ hiso _ hxW
    rw [hform, one_smul] at h1
    have h2 := W.sub_mem h1 hx'
    simpa using h2
  have step3 : ∀ y : HypIndex s ε, hypPartner y = y →
      (Pi.single y (1 : K) : HypIndex s ε → K) ∈ W := by
    intro y hy
    have hye : y ≠ e₀ := fun he => by rw [he, hef] at hy; exact hne hy.symm |>.elim
    have hyf : y ≠ f₀ := fun he => by rw [he, hfe] at hy; exact hne hy |>.elim
    have hf₀W := step2 f₀ hfe'
    have he₀W := step2 e₀ hef'
    have h1 := hW _ (hv₁ y hy) _ hf₀W
    have hform : hypForm h s ε (Pi.single e₀ 1 + Pi.single y 1 + c • Pi.single f₀ 1)
        (Pi.single f₀ 1) = 1 := by
      simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        hypForm_single_single, RingHom.id_apply, hef, hfe, hyf, hne, hne.symm, if_true, if_false]
      simp [hy, hyf, hyf.symm]
    rw [hform, one_smul] at h1
    have h2 := W.sub_mem (W.sub_mem h1 he₀W) (W.smul_mem c hf₀W)
    have h3 : (Pi.single e₀ 1 + Pi.single y 1 + c • Pi.single f₀ 1 : HypIndex s ε → K) -
        Pi.single e₀ 1 - c • Pi.single f₀ 1 = Pi.single y 1 := by abel
    rwa [h3] at h2
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  refine Submodule.sum_mem _ fun a _ => ?_
  have hsingle : (Pi.single a (w a) : HypIndex s ε → K) = w a • Pi.single a 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hsingle]
  refine W.smul_mem _ ?_
  by_cases ha : hypPartner a = a
  · exact step3 a ha
  · exact step2 a ha

end Invariant

section ResRel

variable {f : ℕ} {K : Type} [Field K] {s ε : ℕ} (h : UnitaryFieldData 2 f K)

theorem tvMat_single (x : HypIndex s ε) (a : K) :
    tvMat h (Pi.single x 1) a = 1 + Matrix.single x (hypPartner x) a := by
  ext i j
  simp only [tvMat, Matrix.add_apply]
  congr 1
  have hL : (a • Pi.single x (1 : K) : HypIndex s ε → K) i = if i = x then a else 0 := by
    simp [Pi.single_apply]
  have hR : h.bar ((Pi.single x (1 : K) : HypIndex s ε → K) (hypPartner j)) =
      if j = hypPartner x then 1 else 0 := by
    simp [Pi.single_apply, hypPartner_eq_iff]
  rw [Matrix.vecMulVec_apply, hL, hR, Matrix.single_apply]
  by_cases hi : i = x <;> by_cases hj : j = hypPartner x
  · subst hi
    subst hj
    simp
  · have hj' : ¬ hypPartner x = j := fun h' => hj h'.symm
    simp [hi, hj, hj']
  · have hi' : ¬ x = i := fun h' => hi h'.symm
    simp [hi, hj, hi']
  · have hi' : ¬ x = i := fun h' => hi h'.symm
    simp [hi, hj, hi']

variable {h}

theorem map_one_add_single_hyp {ι : Type} [DecidableEq ι] (σ : K ≃+* K) (i j : ι) (a : K) :
    (1 + Matrix.single i j a : Matrix ι ι K).map σ = 1 + Matrix.single i j (σ a) := by
  ext k l
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem one_add_single_mul_self [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι] {i j : ι}
    (hij : i ≠ j) (a : K) :
    (1 + Matrix.single i j a) * (1 + Matrix.single i j a) = (1 : Matrix ι ι K) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hEE : Matrix.single i j a * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne a i j i hij.symm a
  have hE2 : Matrix.single i j a + Matrix.single i j a = 0 := by
    rw [← two_smul K, h2, zero_smul]
  calc (1 + Matrix.single i j a) * (1 + Matrix.single i j a)
      = 1 + (Matrix.single i j a + Matrix.single i j a) +
        Matrix.single i j a * Matrix.single i j a := by noncomm_ring
    _ = 1 := by rw [hE2, hEE, add_zero, add_zero]

theorem eq_one_of_rel_involution [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {M M' B : Matrix ι ι K} (σ : K ≃+* K) {c : K} (hMM' : M' * M = 1) (hBB : B * B = 1)
    (hrel : M * B.map σ = c • (B * M)) : c = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hσσ : B.map σ * B.map σ = 1 := by
    rw [← Matrix.map_mul, hBB, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have e1 : M = (c * c) • M := by
    calc M = M * (B.map σ * B.map σ) := by rw [hσσ, mul_one]
      _ = (M * B.map σ) * B.map σ := by rw [Matrix.mul_assoc]
      _ = (c • (B * M)) * B.map σ := by rw [hrel]
      _ = c • (B * (M * B.map σ)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = c • (B * (c • (B * M))) := by rw [hrel]
      _ = (c * c) • ((B * B) * M) := by
        rw [Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = (c * c) • M := by rw [hBB, Matrix.one_mul]
  have e2 : (1 : Matrix ι ι K) = (c * c) • (1 : Matrix ι ι K) := by
    have := congrArg (fun N => M' * N) e1
    simpa [Matrix.mul_smul, hMM'] using this
  obtain ⟨i⟩ := ‹Nonempty ι›
  have e3 := congrFun (congrFun e2 i) i
  simp at e3
  have hcc : c * c = 1 := e3.symm
  have : (c - 1) * (c - 1) = 0 := by linear_combination hcc + (1 - c) * h2
  exact sub_eq_zero.mp (mul_self_eq_zero.mp this)

theorem entries_of_mul_single_eq {ι : Type} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι K}
    {i j : ι} {a b : K} (hX : X * Matrix.single i j b = Matrix.single i j a * X) :
    X i i * b = a * X j j ∧ ∀ k, k ≠ i → X k i * b = 0 := by
  constructor
  · have := congrFun (congrFun hX i) j
    rwa [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same] at this
  · intro k hk
    have := congrFun (congrFun hX k) j
    rwa [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne a i j k j hk] at this

theorem sigma_fixes_traceZero (hs : 1 ≤ s) {Mr Mr' : Matrix (HypIndex s ε) (HypIndex s ε) K}
    (hMM' : Mr' * Mr = 1) (σ : K ≃+* K)
    (hrel : ∀ B : hypSU h s ε, ∃ c : K,
      Mr * ((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K).map σ =
        c • (((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K) * Mr)) :
    ∀ a : K, a + h.bar a = 0 → σ a = a := by
  haveI : CharP K 2 := h.charP
  set e₀ : HypIndex s ε := .inl ⟨0, hs⟩ with he₀
  set f₀ : HypIndex s ε := .inr (.inr ⟨0, hs⟩) with hf₀
  have hef : hypPartner e₀ = f₀ := rfl
  have hne : e₀ ≠ f₀ := by simp [he₀, hf₀]
  haveI : Nonempty (HypIndex s ε) := ⟨e₀⟩
  have key : ∀ a : K, a + h.bar a = 0 →
      Mr * Matrix.single e₀ f₀ (σ a) = Matrix.single e₀ f₀ a * Mr := by
    intro a ha
    have hiso : hypForm h s ε (Pi.single e₀ 1) (Pi.single e₀ 1) = 0 := by
      rw [hypForm_single_single, if_neg]
      rw [hef]
      exact hne
    obtain ⟨g, hg⟩ := exists_tv_mem hiso ha
    rw [tvMat_single, hef] at hg
    obtain ⟨c, hc⟩ := hrel g
    rw [hg] at hc
    have hBB := one_add_single_mul_self (K := K) hne a
    have hc1 : c = 1 := eq_one_of_rel_involution σ hMM' hBB hc
    rw [map_one_add_single_hyp, hc1, one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul] at hc
    exact add_left_cancel hc
  have h1 : (1 : K) + h.bar 1 = 0 := by
    rw [map_one]
    exact CharTwo.add_self_eq_zero 1
  obtain ⟨hdiag1, hcol1⟩ := entries_of_mul_single_eq (key 1 h1)
  rw [map_one, mul_one, one_mul] at hdiag1
  have hcol1' : ∀ k, k ≠ e₀ → Mr k e₀ = 0 := fun k hk => by
    have := hcol1 k hk
    rwa [map_one, mul_one] at this
  have hne0 : Mr e₀ e₀ ≠ 0 := by
    have h2 := congrFun (congrFun hMM' e₀) e₀
    rw [Matrix.mul_apply, Finset.sum_eq_single e₀] at h2
    · rw [Matrix.one_apply_eq] at h2
      exact right_ne_zero_of_mul_eq_one h2
    · intro k _ hk
      rw [hcol1' k hk, mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ e₀) hmem
  intro a ha
  obtain ⟨hdiag, -⟩ := entries_of_mul_single_eq (key a ha)
  have h3 : Mr e₀ e₀ * σ a = Mr e₀ e₀ * a := by
    rw [hdiag, ← hdiag1, mul_comm]
  exact mul_left_cancel₀ hne0 h3

theorem tvMat_mul_self [CharP K 2] {v : HypIndex s ε → K} (hv : hypForm h s ε v v = 0) :
    tvMat h v 1 * tvMat h v 1 = 1 := by
  refine Matrix.ext_iff_mulVec.mpr fun x => ?_
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, tvMat_mulVec, tvMat_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hv,
    mul_zero, add_zero, one_mul]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have : hypForm h s ε v x • v + hypForm h s ε v x • v = 0 := by
    rw [← two_smul K, h2, zero_smul]
  rw [add_assoc, this, add_zero]

theorem eq_smul_one_of_res_rel (hs : 1 ≤ s) {Mr Mr' : Matrix (HypIndex s ε) (HypIndex s ε) K}
    (hMM' : Mr' * Mr = 1) (σ : K ≃+* K) (hσ : ∀ t, σ t = t)
    (hrel : ∀ B : hypSU h s ε, ∃ c : K,
      Mr * ((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K).map σ =
        c • (((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K) * Mr)) :
    ∃ c : K, Mr = c • 1 := by
  haveI : CharP K 2 := h.charP
  set e₀ : HypIndex s ε := .inl ⟨0, hs⟩ with he₀
  set f₀ : HypIndex s ε := .inr (.inr ⟨0, hs⟩) with hf₀
  have hef : hypPartner e₀ = f₀ := rfl
  have hne : e₀ ≠ f₀ := by simp [he₀, hf₀]
  haveI : Nonempty (HypIndex s ε) := ⟨e₀⟩
  have h1 : (1 : K) + h.bar 1 = 0 := by
    rw [map_one]
    exact CharTwo.add_self_eq_zero 1
  have hcomm : ∀ v : HypIndex s ε → K, hypForm h s ε v v = 0 →
      Mr * tvMat h v 1 = tvMat h v 1 * Mr := by
    intro v hv
    obtain ⟨g, hg⟩ := exists_tv_mem hv h1
    obtain ⟨c, hc⟩ := hrel g
    rw [hg] at hc
    have hmap : (tvMat h v 1).map σ = tvMat h v 1 := by
      ext i j
      simp [hσ]
    rw [hmap] at hc
    have hc1 : c = 1 := eq_one_of_rel_involution σ hMM' (tvMat_mul_self hv) (by rw [hmap]; exact hc)
    rw [hc1, one_smul] at hc
    exact hc
  have hiso₀ : hypForm h s ε (Pi.single e₀ 1) (Pi.single e₀ 1) = 0 := by
    rw [hypForm_single_single, if_neg]
    rw [hef]
    exact hne
  set lam : K := (Mr *ᵥ (Pi.single f₀ 1 : HypIndex s ε → K)) f₀ with hlam
  have heig : Mr *ᵥ (Pi.single e₀ 1 : HypIndex s ε → K) = lam • Pi.single e₀ 1 := by
    have h2 := congrArg (fun N : Matrix (HypIndex s ε) (HypIndex s ε) K =>
      N *ᵥ (Pi.single f₀ 1 : HypIndex s ε → K)) (hcomm _ hiso₀)
    simp only [← Matrix.mulVec_mulVec, tvMat_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
      hypForm_single_left, hef, Pi.single_eq_same, one_mul, one_smul] at h2
    exact add_left_cancel h2
  let W : Submodule K (HypIndex s ε → K) :=
    { carrier := {w | Mr *ᵥ w = lam • w}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [Matrix.mulVec_add, ha, hb, smul_add]
      zero_mem' := by simp
      smul_mem' := fun c w hw => by
        simp only [Set.mem_setOf_eq] at hw ⊢
        rw [Matrix.mulVec_smul, hw, smul_comm] }
  have hδ₀ : (Pi.single e₀ 1 : HypIndex s ε → K) ∈ W := heig
  have hδ₀0 : (Pi.single e₀ 1 : HypIndex s ε → K) ≠ 0 := by
    intro h0
    have := congrFun h0 e₀
    simp at this
  have hW : ∀ v : HypIndex s ε → K, hypForm h s ε v v = 0 → ∀ w ∈ W,
      hypForm h s ε v w • v ∈ W := by
    intro v hv w hw
    have hw' : Mr *ᵥ w = lam • w := hw
    have h3 := congrArg (fun N : Matrix (HypIndex s ε) (HypIndex s ε) K => N *ᵥ w)
      (hcomm v hv)
    simp only [← Matrix.mulVec_mulVec, tvMat_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hw',
      one_mul, map_smul, smul_eq_mul, smul_add] at h3
    have h4 := add_left_cancel h3
    show Mr *ᵥ (hypForm h s ε v w • v) = lam • (hypForm h s ε v w • v)
    rw [Matrix.mulVec_smul]
    exact h4
  have htop := eq_top_of_invariant h hs W hW _ hδ₀ hδ₀0
  refine ⟨lam, Matrix.ext fun k y => ?_⟩
  have hy : (Pi.single y 1 : HypIndex s ε → K) ∈ W := by rw [htop]; exact Submodule.mem_top
  have h5 := congrFun
    (show Mr *ᵥ (Pi.single y 1 : HypIndex s ε → K) = lam • Pi.single y 1 from hy) k
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at h5
  rw [h5]
  simp [Matrix.one_apply, Pi.single_apply]

end ResRel

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni
