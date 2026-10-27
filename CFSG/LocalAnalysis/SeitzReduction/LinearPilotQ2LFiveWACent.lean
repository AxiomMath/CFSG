module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OuterTwo
public import CFSG.LocalAnalysis.EvenSmallLie.Setup
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamilies
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWAOrbit
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCores
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWModel

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag

section Model

variable {n : ℕ} {K : Type*} [Field K]

theorem pointRadMat_single {c j : Fin n} (hjc : j ≠ c) :
    pointRadMat c (Pi.single j (1 : K)) =
      1 + vecMulVec (Pi.single c (1 : K)) (Pi.single j (1 : K)) := by
  rw [pointRadMat]
  congr 2
  rw [Function.update_eq_self_iff, Pi.single_apply, ite_eq_right hjc.symm]

theorem proj_pointRadElem_single_mem {c j : Fin n} (hjc : j ≠ c) :
    proj n K (pointRadElem c (Pi.single j (1 : K))) ∈ pointRadical c := by
  refine ⟨_, ⟨Pi.single j (1 : K), fun k hk => ?_, rfl⟩, rfl⟩
  rw [Finset.mem_compl, Finset.mem_singleton, not_not] at hk
  subst hk
  rw [Pi.single_apply, ite_eq_right hjc.symm]

theorem mul_eq_mul_of_proj_mul_eq (hK : Nat.card K = 2) {A B : SpecialLinearGroup (Fin n) K}
    (h : proj n K A * proj n K B = proj n K B * proj n K A) :
    (A : Matrix (Fin n) (Fin n) K) * B = B * A := by
  rw [← map_mul, ← map_mul] at h
  exact congrArg Subtype.val (proj_injective_of_natCard_eq_two hK h)

theorem vecMulVec_eq_of_commute_one_add {B : Matrix (Fin n) (Fin n) K} {u w u' w' : Fin n → K}
    (h : B * (1 + vecMulVec u w) = (1 + vecMulVec u' w') * B) :
    vecMulVec (B *ᵥ u) w = vecMulVec u' (w' ᵥ* B) := by
  rw [mul_add, add_mul, Matrix.mul_one, Matrix.one_mul] at h
  rw [← mul_vecMulVec, ← vecMulVec_mul]
  exact add_left_cancel h

theorem exists_two_ne_of_three_le (hn : 3 ≤ n) (c : Fin n) :
    ∃ j₁ j₂ : Fin n, j₁ ≠ c ∧ j₂ ≠ c ∧ j₁ ≠ j₂ := by
  have hcard : 1 < (({c}ᶜ : Finset (Fin n))).card := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    omega
  obtain ⟨j₁, hj₁, j₂, hj₂, h12⟩ := Finset.one_lt_card.1 hcard
  simp only [Finset.mem_compl, Finset.mem_singleton] at hj₁ hj₂
  exact ⟨j₁, j₂, hj₁, hj₂, h12⟩

theorem mem_pointRadical_of_forall_commute (hK : Nat.card K = 2) (hn : 2 ≤ n) {c : Fin n}
    {p : projectiveSL n K} (hp : ∀ v ∈ pointRadical (K := K) c, p * v = v * p) :
    p ∈ pointRadical (K := K) c := by
  classical
  obtain ⟨B, rfl⟩ := proj_surjective n K p
  have hrel : ∀ j : Fin n, j ≠ c → ∀ i k : Fin n,
      (B : Matrix (Fin n) (Fin n) K) i c * (Pi.single j (1 : K) : Fin n → K) k =
        (Pi.single c (1 : K) : Fin n → K) i * (B : Matrix (Fin n) (Fin n) K) j k := by
    intro j hjc i k
    have h1 := mul_eq_mul_of_proj_mul_eq hK (hp _ (proj_pointRadElem_single_mem hjc))
    rw [coe_pointRadElem, pointRadMat_single hjc] at h1
    have h2 := congrFun₂ (vecMulVec_eq_of_commute_one_add h1) i k
    simpa only [vecMulVec_apply, mulVec_single_one, single_one_vecMul, col_apply,
      row_apply] using h2
  obtain ⟨j₀, hj₀⟩ : ∃ j : Fin n, j ≠ c := by
    have hcard : 0 < (({c}ᶜ : Finset (Fin n))).card := by
      rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
      omega
    obtain ⟨j, hj⟩ := Finset.card_pos.1 hcard
    exact ⟨j, by simpa using hj⟩
  have hrow : ∀ j : Fin n, j ≠ c → ∀ k : Fin n,
      (B : Matrix (Fin n) (Fin n) K) j k =
        (B : Matrix (Fin n) (Fin n) K) c c * (Pi.single j (1 : K) : Fin n → K) k := by
    intro j hjc k
    have := hrel j hjc c k
    rw [Pi.single_eq_same, one_mul] at this
    exact this.symm
  have hcc : (B : Matrix (Fin n) (Fin n) K) c c = 1 := by
    rcases eq_zero_or_eq_one_of_natCard_eq_two hK ((B : Matrix (Fin n) (Fin n) K) c c) with h0 | h1
    · exfalso
      have hdet : (B : Matrix (Fin n) (Fin n) K).det = 0 :=
        det_eq_zero_of_row_eq_zero j₀ fun k => by rw [hrow j₀ hj₀ k, h0, zero_mul]
      rw [B.2] at hdet
      exact one_ne_zero hdet
    · exact h1
  set r : Fin n → K := fun k => (B : Matrix (Fin n) (Fin n) K) c k with hr
  have hB : pointRadElem c r = B := by
    apply Subtype.ext
    ext i k
    rw [coe_pointRadElem, pointRadMat_apply]
    by_cases hi : i = c
    · subst hi
      by_cases hk : k = i
      · subst hk
        rw [one_apply_eq, hcc]
        simp
      · rw [one_apply_ne (Ne.symm hk), zero_add, ite_eq_left ⟨rfl, hk⟩]
    · rw [ite_eq_right (fun h => hi h.1), add_zero, hrow i hi k, hcc, one_mul, Pi.single_apply,
        one_apply]
      by_cases hik : i = k
      · rw [ite_eq_left hik, ite_eq_left hik.symm]
      · rw [ite_eq_right hik, ite_eq_right (Ne.symm hik)]
  refine ⟨B, ⟨Function.update r c 0, fun j hj => ?_, ?_⟩, rfl⟩
  · rw [Finset.mem_compl, Finset.mem_singleton, not_not] at hj
    subst hj
    exact Function.update_self _ _ _
  · rw [← hB]
    apply Subtype.ext
    rw [coe_pointRadElem, coe_pointRadElem, pointRadMat, pointRadMat, Function.update_idem]

theorem not_forall_conj_dualAut_eq [CharP K 2] (hK : Nat.card K = 2) (hn : 3 ≤ n) (c : Fin n)
    (p : projectiveSL n K) :
    ¬ ∀ v ∈ pointRadical (K := K) c, p * dualAut n K v * p⁻¹ = v := by
  classical
  intro h
  obtain ⟨B, rfl⟩ := proj_surjective n K p
  have hcol : ∀ j : Fin n, j ≠ c → ∀ i : Fin n,
      (B : Matrix (Fin n) (Fin n) K) i j =
        (Pi.single c (1 : K) : Fin n → K) i * (B : Matrix (Fin n) (Fin n) K) j c := by
    intro j hjc i
    set g := pointRadElem c (Pi.single j (1 : K)) with hg
    have hg2 : g⁻¹ = g := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [hg, pointRadElem_mul, show (Pi.single j (1 : K) : Fin n → K) + Pi.single j (1 : K) = 0
        from by
        ext k
        simp only [Pi.add_apply, Pi.zero_apply]
        rw [← two_mul, CharTwo.two_eq_zero, zero_mul], pointRadElem_zero]
    have h1 := h _ (proj_pointRadElem_single_mem hjc)
    rw [← hg, dualAut_proj, hg2] at h1
    have h1' : proj n K B * proj n K g.transpose = proj n K g * proj n K B := by
      rw [← h1]
      group
    rw [← map_mul, ← map_mul] at h1'
    have h2 : (B : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)ᵀ =
        (g : Matrix (Fin n) (Fin n) K) * B :=
      congrArg Subtype.val (proj_injective_of_natCard_eq_two hK h1')
    rw [hg, coe_pointRadElem, pointRadMat_single hjc, transpose_add, transpose_one,
      transpose_vecMulVec] at h2
    have h3 := congrFun₂ (vecMulVec_eq_of_commute_one_add h2) i c
    simpa only [vecMulVec_apply, mulVec_single_one, single_one_vecMul, col_apply, row_apply,
      Pi.single_eq_same, mul_one] using h3
  obtain ⟨j₁, j₂, hj₁, hj₂, h12⟩ := exists_two_ne_of_three_le hn c
  have hzero : ∀ j : Fin n, j ≠ c → ∀ i : Fin n, i ≠ c → (B : Matrix (Fin n) (Fin n) K) i j = 0 :=
    fun j hj i hi => by rw [hcol j hj i, Pi.single_apply, ite_eq_right hi, zero_mul]
  have hdet : (B : Matrix (Fin n) (Fin n) K).det = 0 := by
    rcases eq_zero_or_eq_one_of_natCard_eq_two hK ((B : Matrix (Fin n) (Fin n) K) c j₁) with
      h0 | h1
    · refine det_eq_zero_of_column_eq_zero j₁ fun i => ?_
      by_cases hi : i = c
      · rw [hi, h0]
      · exact hzero j₁ hj₁ i hi
    rcases eq_zero_or_eq_one_of_natCard_eq_two hK ((B : Matrix (Fin n) (Fin n) K) c j₂) with
      h0' | h1'
    · refine det_eq_zero_of_column_eq_zero j₂ fun i => ?_
      by_cases hi : i = c
      · rw [hi, h0']
      · exact hzero j₂ hj₂ i hi
    refine det_zero_of_column_eq h12 fun i => ?_
    by_cases hi : i = c
    · rw [hi, h1, h1']
    · rw [hzero j₁ hj₁ i hi, hzero j₂ hj₂ i hi]
  rw [B.2] at hdet
  exact one_ne_zero hdet

end Model

section Setting

variable {G : Type*} [Group G] {L : Subgroup G}

@[expose] def conjAutOfMemNormalizer {g : G} (hg : g ∈ normalizer (L : Set G)) : MulAut L where
  toFun x := ⟨g * x * g⁻¹, (mem_normalizer_iff.1 hg x).1 x.2⟩
  invFun x := ⟨g⁻¹ * x * g, by
    have := (mem_normalizer_iff.1 (inv_mem hg) x).1 x.2
    rwa [inv_inv] at this⟩
  left_inv x := by ext; simp only; group
  right_inv x := by ext; simp only; group
  map_mul' x y := by ext; simp only [coe_mul]; group

theorem coe_conjAutOfMemNormalizer_apply {g : G} (hg : g ∈ normalizer (L : Set G)) (x : L) :
    ((conjAutOfMemNormalizer hg x : L) : G) = g * x * g⁻¹ :=
  rfl

end Setting

section Seitz

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem centralizer_pointRadical_inf_le (hset : SeitzSetting G L) {n : ℕ} (hn : 3 ≤ n)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL n K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin n) :
    centralizer (modelToG e (pointRadical c) : Set G) ⊓ centralizer ({t} : Set G) ≤
      modelToG e (pointRadical c) ⊔ zpowers t := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have htC : t ∈ centralizer (L : Set G) := by
    have h := mem_zpowers t
    rw [← hKt] at h
    exact (Subgroup.mem_inf.1 h).1
  have hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht
  rintro g ⟨hgV, hgt⟩
  have hgL : g ∈ normalizer (L : Set G) := hCN hgt
  set α : MulAut (projectiveSL n K) := e.symm.trans ((conjAutOfMemNormalizer hgL).trans e)
    with hα
  have hαapp : ∀ x : projectiveSL n K, ((e.symm (α x) : L) : G) = g * (e.symm x : G) * g⁻¹ := by
    intro x
    rw [hα, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      coe_conjAutOfMemNormalizer_apply]
  have hαV : ∀ v ∈ pointRadical (K := K) c, α v = v := by
    intro v hv
    apply e.symm.injective
    apply Subtype.ext
    rw [hαapp]
    exact conj_eq_of_mem_centralizer hgV (symm_mem_modelToG e hv)
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := K) hn).2 α
  rw [SeitzQ2.fieldAut_eq_one_of_card_eq_two hK σ, mul_one] at hαeq
  obtain ⟨p, hp⟩ := SeitzQ2.conjAut_mem_inner_of_card_eq_two hK A
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · rw [pow_zero, mul_one, ← hp] at hαeq
    set l : L := e.symm p with hl
    have hgl : ∀ y : L, g * (y : G) * g⁻¹ = (l : G) * y * (l : G)⁻¹ := by
      intro y
      have h1 := hαapp (e y)
      rw [hαeq, MulAut.conj_apply, MulEquiv.symm_apply_apply] at h1
      rw [← h1, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
      rfl
    have hlt : (l : G) ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 htC) l l.2)
    have hlg : (l : G)⁻¹ * g ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
      refine Subgroup.mem_inf.2 ⟨mem_centralizer_iff.2 fun y hy => ?_, mul_mem (inv_mem hlt) hgt⟩
      have h1 := hgl ⟨y, hy⟩
      calc y * ((l : G)⁻¹ * g) = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * g := by group
        _ = (l : G)⁻¹ * (g * y * g⁻¹) * g := by rw [← h1]
        _ = (l : G)⁻¹ * g * y := by group
    rw [hKt] at hlg
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hlg
    have hgeq : g = (l : G) * t ^ k := by rw [hk]; group
    have htV : t ∈ centralizer (modelToG e (pointRadical c) : Set G) :=
      mem_centralizer_iff.2 fun v hv => (mem_centralizer_iff.1 htC) v (modelToG_le e _ hv)
    have hlV : (l : G) ∈ centralizer (modelToG e (pointRadical c) : Set G) := by
      have he : (l : G) = g * (t ^ k)⁻¹ := by rw [hgeq]; group
      rw [he]
      exact mul_mem hgV (inv_mem (zpow_mem htV k))
    have hpV : p ∈ pointRadical (K := K) c := by
      refine mem_pointRadical_of_forall_commute hK (by omega) fun v hv => ?_
      have h1 := (mem_centralizer_iff.1 hlV) _ (symm_mem_modelToG e hv)
      apply e.symm.injective
      apply Subtype.ext
      rw [map_mul, map_mul, coe_mul, coe_mul, ← hl]
      exact h1.symm
    rw [hgeq]
    exact mul_mem (mem_sup_left ((mem_modelToG e).2 ⟨p, hpV, rfl⟩))
      (mem_sup_right (zpow_mem (mem_zpowers t) k))
  · rw [pow_one, ← hp] at hαeq
    refine absurd (fun v hv => ?_) (not_forall_conj_dualAut_eq hK hn c p)
    have h1 := hαV v hv
    rw [hαeq] at h1
    simpa only [MulAut.mul_apply, MulAut.conj_apply] using h1

end Seitz

end CFSG.SeitzReduction.LinearPilot
