module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagCone
import CFSG.ClassicalInvolution.Phan.PhanDn.CommonNbrQTwo
import CFSG.ClassicalInvolution.Phan.PhanDn.ConeFiveCoordQTwo
import CFSG.ClassicalGroups.Orthogonal.LineStabilizer

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalGroups.Orthogonal (polar_map_of_linearIsometry)

variable {K : Type} [Field K] {σ : K ≃+* K} {m : ℕ}

private theorem inr_eq_zero_of_polar_stdE {n : ℕ} {v : Fin n ⊕ Fin n → K} {i : Fin n}
    (h : polar (quadPlus n K) (stdE (K := K) i) v = 0) : v (.inr i) = 0 := by
  rw [polar_quadPlus] at h
  rw [Finset.sum_eq_single i] at h
  · simpa using h
  · intro j _ hj
    simp [stdE, hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem inl_eq_zero_of_flipHerm_stdE {n : ℕ} (hσ : ∀ x, σ (σ x) = x)
    {v : Fin n ⊕ Fin n → K} {i : Fin n} (h : flipHerm σ (stdE (K := K) i) v = 0) :
    v (.inl i) = 0 := by
  have h1 : flipHerm σ v (stdE (K := K) i) = 0 := (flipHerm_eq_zero_iff hσ).mp h
  rwa [flipHerm_stdE_right] at h1

private theorem qPerp_map_of_quadPlus_map {n : ℕ}
    {L : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (hQ : ∀ y, quadPlus n K (L y) = quadPlus n K y)
    (U : Submodule K (Fin n ⊕ Fin n → K)) :
    (qPerp n K U).map L.toLinearMap = qPerp n K (U.map L.toLinearMap) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    replace hw := mem_qPerp.mp hw
    refine mem_qPerp.mpr ?_
    intro u hu
    obtain ⟨u₀, hu₀, rfl⟩ := Submodule.mem_map.mp hu
    change polar (quadPlus n K) (L u₀) (L w) = 0
    rw [polar_map_of_linearIsometry (quadPlus n K) L hQ u₀ w]
    exact hw u₀ hu₀
  · intro hv
    obtain ⟨w, rfl⟩ := L.surjective v
    refine Submodule.mem_map_of_mem ?_
    replace hv := mem_qPerp.mp hv
    refine mem_qPerp.mpr ?_
    intro u hu
    have h := hv (L u) (Submodule.mem_map_of_mem hu)
    change polar (quadPlus n K) (L u) (L w) = 0 at h
    rwa [polar_map_of_linearIsometry (quadPlus n K) L hQ u w] at h

private theorem flipOrth_map_of_quadPlus_map {n : ℕ}
    {L : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (hQ : ∀ y, quadPlus n K (L y) = quadPlus n K y)
    (hL : ∀ y, L (dFlip σ y) = dFlip σ (L y))
    (U : Submodule K (Fin n ⊕ Fin n → K)) :
    (flipOrth σ U).map L.toLinearMap = flipOrth σ (U.map L.toLinearMap) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    replace hw := mem_flipOrth.mp hw
    refine mem_flipOrth.mpr ?_
    intro u hu
    obtain ⟨u₀, hu₀, rfl⟩ := Submodule.mem_map.mp hu
    change flipHerm σ (L u₀) (L w) = 0
    rw [flipHerm_map_linearEquiv L hQ hL u₀ w]
    exact hw u₀ hu₀
  · intro hv
    obtain ⟨w, rfl⟩ := L.surjective v
    refine Submodule.mem_map_of_mem ?_
    replace hv := mem_flipOrth.mp hv
    refine mem_flipOrth.mpr ?_
    intro u hu
    have h := hv (L u) (Submodule.mem_map_of_mem hu)
    change flipHerm σ (L u) (L w) = 0 at h
    rwa [flipHerm_map_linearEquiv L hQ hL u w] at h

private theorem eq_smul_stdE_add_smul_stdF_of_coords_zero
    {γ : Fin (4 + 1) ⊕ Fin (4 + 1) → K}
    (h1 : γ (.inl 1) = 0 ∧ γ (.inr 1) = 0)
    (h2 : γ (.inl 2) = 0 ∧ γ (.inr 2) = 0)
    (h3 : γ (.inl 3) = 0 ∧ γ (.inr 3) = 0)
    (h4 : γ (.inl 4) = 0 ∧ γ (.inr 4) = 0) :
    γ = γ (.inl 0) • stdE (K := K) (n := 4 + 1) 0 +
      γ (.inr 0) • stdF (K := K) (n := 4 + 1) 0 := by
  funext x
  cases x with
  | inl i =>
    fin_cases i <;> simp [stdE, stdF, h1.1, h2.1, h3.1, h4.1]
  | inr i =>
    fin_cases i <;> simp [stdE, stdF, h1.2, h2.2, h3.2, h4.2]

private theorem mul_eq_zero_of_quadPlus_eq_zero {K : Type} [Field K]
    {γ : Fin (4 + 1) ⊕ Fin (4 + 1) → K}
    (h1 : γ (.inl 1) = 0 ∧ γ (.inr 1) = 0)
    (h2 : γ (.inl 2) = 0 ∧ γ (.inr 2) = 0)
    (h3 : γ (.inl 3) = 0 ∧ γ (.inr 3) = 0)
    (h4 : γ (.inl 4) = 0 ∧ γ (.inr 4) = 0)
    (hQ : quadPlus (4 + 1) K γ = 0) : γ (.inl 0) * γ (.inr 0) = 0 := by
  rw [quadPlus_apply, Fin.sum_univ_five] at hQ
  simpa [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2] using hQ

private theorem polar_eq_zero_of_le_qPerp {n : ℕ} {A B : Submodule K (Fin n ⊕ Fin n → K)}
    (h : B ≤ qPerp n K A) : ∀ a ∈ A, ∀ b ∈ B, polar (quadPlus n K) a b = 0 := by
  intro a ha b hb
  exact (mem_qPerp.mp (h hb)) a ha

private theorem polar_eq_zero_of_le_qPerp_comm {n : ℕ}
    {A B : Submodule K (Fin n ⊕ Fin n → K)} (h : B ≤ qPerp n K A) :
    ∀ b ∈ B, ∀ a ∈ A, polar (quadPlus n K) b a = 0 := by
  intro b hb a ha
  rw [polar_comm]
  exact (mem_qPerp.mp (h hb)) a ha

private theorem flipHerm_eq_zero_of_le_flipOrth {n : ℕ}
    {A B : Submodule K (Fin n ⊕ Fin n → K)} (h : B ≤ flipOrth σ A) :
    ∀ a ∈ A, ∀ b ∈ B, flipHerm σ a b = 0 := by
  intro a ha b hb
  exact (mem_flipOrth.mp (h hb)) a ha

private theorem flipHerm_eq_zero_of_le_flipOrth_comm (hσ : ∀ x, σ (σ x) = x) {n : ℕ}
    {A B : Submodule K (Fin n ⊕ Fin n → K)} (h : B ≤ flipOrth σ A) :
    ∀ b ∈ B, ∀ a ∈ A, flipHerm σ b a = 0 := by
  intro b hb a ha
  exact (flipHerm_eq_zero_iff hσ).mpr ((mem_flipOrth.mp (h hb)) a ha)

private theorem isFlipflopSub_sup_point (hσ : ∀ x, σ (σ x) = x) {n : ℕ}
    {A p : Submodule K (Fin n ⊕ Fin n → K)} (hA : IsFlipflopSub σ A)
    (hp : IsFlipflopPt σ p) (hf : p ≤ qPerp n K A) (hh : p ≤ flipOrth σ A) :
    IsFlipflopSub σ (A ⊔ p) ∧ Disjoint A p ∧
      Module.finrank K ↥(A ⊔ p) = Module.finrank K A + 1 := by
  have hAq : A ≤ qPerp n K p := by
    intro a ha
    refine mem_qPerp.mpr ?_
    intro b hb
    rw [polar_comm]
    exact (mem_qPerp.mp (hf hb)) a ha
  have hAh : A ≤ flipOrth σ p := by
    intro a ha
    refine mem_flipOrth.mpr ?_
    intro b hb
    exact (flipHerm_eq_zero_iff hσ).mpr ((mem_flipOrth.mp (hh hb)) a ha)
  have h := IsFlipflopSub.sup_of_orth hσ hA (IsFlipflopPt.isFlipflopSub hp) hAq hAh
  refine ⟨h.1, h.2, ?_⟩
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq A p
  rw [h.2.eq_bot, finrank_bot, add_zero, IsFlipflopPt.finrank_eq_one hp] at hdim
  exact hdim

private structure PairOrth (σ : K ≃+* K)
    (a z1 z2 f1 f2 : Submodule K (Fin (4 + 1) ⊕ Fin (4 + 1) → K)) : Prop where
  hQ_A_Z1 : ∀ u ∈ a, ∀ v ∈ z1, polar (quadPlus (4 + 1) K) u v = 0
  hQ_A_Z2 : ∀ u ∈ a, ∀ v ∈ z2, polar (quadPlus (4 + 1) K) u v = 0
  hQ_A_F1 : ∀ u ∈ a, ∀ v ∈ f1, polar (quadPlus (4 + 1) K) u v = 0
  hQ_A_F2 : ∀ u ∈ a, ∀ v ∈ f2, polar (quadPlus (4 + 1) K) u v = 0
  hQ_Z1_Z2 : ∀ u ∈ z1, ∀ v ∈ z2, polar (quadPlus (4 + 1) K) u v = 0
  hQ_Z1_F1 : ∀ u ∈ z1, ∀ v ∈ f1, polar (quadPlus (4 + 1) K) u v = 0
  hQ_Z1_F2 : ∀ u ∈ z1, ∀ v ∈ f2, polar (quadPlus (4 + 1) K) u v = 0
  hQ_Z2_F1 : ∀ u ∈ z2, ∀ v ∈ f1, polar (quadPlus (4 + 1) K) u v = 0
  hQ_Z2_F2 : ∀ u ∈ z2, ∀ v ∈ f2, polar (quadPlus (4 + 1) K) u v = 0
  hQ_F1_F2 : ∀ u ∈ f1, ∀ v ∈ f2, polar (quadPlus (4 + 1) K) u v = 0
  hH_A_Z1 : ∀ u ∈ a, ∀ v ∈ z1, flipHerm σ u v = 0
  hH_A_Z2 : ∀ u ∈ a, ∀ v ∈ z2, flipHerm σ u v = 0
  hH_A_F1 : ∀ u ∈ a, ∀ v ∈ f1, flipHerm σ u v = 0
  hH_A_F2 : ∀ u ∈ a, ∀ v ∈ f2, flipHerm σ u v = 0
  hH_Z1_Z2 : ∀ u ∈ z1, ∀ v ∈ z2, flipHerm σ u v = 0
  hH_Z1_F1 : ∀ u ∈ z1, ∀ v ∈ f1, flipHerm σ u v = 0
  hH_Z1_F2 : ∀ u ∈ z1, ∀ v ∈ f2, flipHerm σ u v = 0
  hH_Z2_F1 : ∀ u ∈ z2, ∀ v ∈ f1, flipHerm σ u v = 0
  hH_Z2_F2 : ∀ u ∈ z2, ∀ v ∈ f2, flipHerm σ u v = 0
  hH_F1_F2 : ∀ u ∈ f1, ∀ v ∈ f2, flipHerm σ u v = 0

private theorem pairOrth (hσ : ∀ x, σ (σ x) = x)
    {a z1 z2 f1 f2 : Submodule K (Fin (4 + 1) ⊕ Fin (4 + 1) → K)}
    (hz1Y : z1 ≤ qPerp (4 + 1) K ((a ⊔ f1) ⊔ f2))
    (hz2Y1 : z2 ≤ qPerp (4 + 1) K (((a ⊔ f1) ⊔ f2) ⊔ z1))
    (hz1Yh : z1 ≤ flipOrth σ ((a ⊔ f1) ⊔ f2))
    (hz2Y1h : z2 ≤ flipOrth σ (((a ⊔ f1) ⊔ f2) ⊔ z1))
    (hf1X : f1 ≤ qPerp (4 + 1) K a) (hf1Xh : f1 ≤ flipOrth σ a)
    (hf2X : f2 ≤ qPerp (4 + 1) K (a ⊔ f1)) (hf2Xh : f2 ≤ flipOrth σ (a ⊔ f1)) :
    PairOrth σ a z1 z2 f1 f2 := by
  have hA_Y : a ≤ (a ⊔ f1) ⊔ f2 := le_sup_left.trans le_sup_left
  have hF1_Y : f1 ≤ (a ⊔ f1) ⊔ f2 := le_sup_right.trans le_sup_left
  have hF2_Y : f2 ≤ (a ⊔ f1) ⊔ f2 := le_sup_right
  have hA_A1 : a ≤ a ⊔ f1 := le_sup_left
  have hF1_A1 : f1 ≤ a ⊔ f1 := le_sup_right
  have hY_Y1 : ((a ⊔ f1) ⊔ f2) ≤ ((a ⊔ f1) ⊔ f2) ⊔ z1 := le_sup_left
  have hZ1_Y1 : z1 ≤ ((a ⊔ f1) ⊔ f2) ⊔ z1 := le_sup_right
  have hA_Y1 : a ≤ ((a ⊔ f1) ⊔ f2) ⊔ z1 := hA_Y.trans hY_Y1
  have hF1_Y1 : f1 ≤ ((a ⊔ f1) ⊔ f2) ⊔ z1 := hF1_Y.trans hY_Y1
  have hF2_Y1 : f2 ≤ ((a ⊔ f1) ⊔ f2) ⊔ z1 := hF2_Y.trans hY_Y1
  refine
    { hQ_A_Z1 := polar_eq_zero_of_le_qPerp (hz1Y.trans (qPerp_antitone hA_Y))
      hQ_A_Z2 := polar_eq_zero_of_le_qPerp (hz2Y1.trans (qPerp_antitone hA_Y1))
      hQ_A_F1 := polar_eq_zero_of_le_qPerp hf1X
      hQ_A_F2 := polar_eq_zero_of_le_qPerp (hf2X.trans (qPerp_antitone hA_A1))
      hQ_Z1_Z2 := polar_eq_zero_of_le_qPerp (hz2Y1.trans (qPerp_antitone hZ1_Y1))
      hQ_Z1_F1 := polar_eq_zero_of_le_qPerp_comm (hz1Y.trans (qPerp_antitone hF1_Y))
      hQ_Z1_F2 := polar_eq_zero_of_le_qPerp_comm (hz1Y.trans (qPerp_antitone hF2_Y))
      hQ_Z2_F1 := polar_eq_zero_of_le_qPerp_comm (hz2Y1.trans (qPerp_antitone hF1_Y1))
      hQ_Z2_F2 := polar_eq_zero_of_le_qPerp_comm (hz2Y1.trans (qPerp_antitone hF2_Y1))
      hQ_F1_F2 := polar_eq_zero_of_le_qPerp (hf2X.trans (qPerp_antitone hF1_A1))
      hH_A_Z1 := flipHerm_eq_zero_of_le_flipOrth (hz1Yh.trans (flipOrth_antitone hA_Y))
      hH_A_Z2 := flipHerm_eq_zero_of_le_flipOrth (hz2Y1h.trans (flipOrth_antitone hA_Y1))
      hH_A_F1 := flipHerm_eq_zero_of_le_flipOrth hf1Xh
      hH_A_F2 := flipHerm_eq_zero_of_le_flipOrth (hf2Xh.trans (flipOrth_antitone hA_A1))
      hH_Z1_Z2 := flipHerm_eq_zero_of_le_flipOrth (hz2Y1h.trans (flipOrth_antitone hZ1_Y1))
      hH_Z1_F1 := flipHerm_eq_zero_of_le_flipOrth_comm hσ
        (hz1Yh.trans (flipOrth_antitone hF1_Y))
      hH_Z1_F2 := flipHerm_eq_zero_of_le_flipOrth_comm hσ
        (hz1Yh.trans (flipOrth_antitone hF2_Y))
      hH_Z2_F1 := flipHerm_eq_zero_of_le_flipOrth_comm hσ
        (hz2Y1h.trans (flipOrth_antitone hF1_Y1))
      hH_Z2_F2 := flipHerm_eq_zero_of_le_flipOrth_comm hσ
        (hz2Y1h.trans (flipOrth_antitone hF2_Y1))
      hH_F1_F2 := flipHerm_eq_zero_of_le_flipOrth (hf2Xh.trans (flipOrth_antitone hF1_A1)) }

private def frameFive (hσ : ∀ x, σ (σ x) = x)
    (a z1 z2 f1 f2 : Submodule K (Fin (4 + 1) ⊕ Fin (4 + 1) → K))
    (ha : IsFlipflopPt σ a) (hz1 : IsFlipflopPt σ z1) (hz2 : IsFlipflopPt σ z2)
    (hf1 : IsFlipflopPt σ f1) (hf2 : IsFlipflopPt σ f2)
    (P : PairOrth σ a z1 z2 f1 f2) : FlipFrame σ (4 + 1) where
  line := ![a, z1, z2, f1, f2]
  isFlipflopPt_line := by
    intro i
    fin_cases i <;> assumption
  polar_eq_zero := by
    intro i j hij u hu v hv
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | exact P.hQ_A_Z1 u hu v hv
      | exact (polar_comm (quadPlus (4 + 1) K) u v).trans (P.hQ_A_Z1 v hv u hu)
      | exact P.hQ_A_Z2 u hu v hv
      | exact (polar_comm (quadPlus (4 + 1) K) u v).trans (P.hQ_A_Z2 v hv u hu)
      | exact P.hQ_A_F1 u hu v hv
      | exact (polar_comm (quadPlus (4 + 1) K) u v).trans (P.hQ_A_F1 v hv u hu)
      | exact P.hQ_A_F2 u hu v hv
      | exact (polar_comm (quadPlus (4 + 1) K) u v).trans (P.hQ_A_F2 v hv u hu)
      | exact P.hQ_Z1_Z2 u hu v hv
      | exact (polar_comm (quadPlus (4 + 1) K) u v).trans (P.hQ_Z1_Z2 v hv u hu)
      | exact P.hQ_Z1_F1 u hu v hv
      | exact (polar_comm (quadPlus (4 + 1) K) u v).trans (P.hQ_Z1_F1 v hv u hu)
      | exact P.hQ_Z1_F2 u hu v hv
      | exact (polar_comm (quadPlus (4 + 1) K) u v).trans (P.hQ_Z1_F2 v hv u hu)
      | exact P.hQ_Z2_F1 u hu v hv
      | exact (polar_comm (quadPlus (4 + 1) K) u v).trans (P.hQ_Z2_F1 v hv u hu)
      | exact P.hQ_Z2_F2 u hu v hv
      | exact (polar_comm (quadPlus (4 + 1) K) u v).trans (P.hQ_Z2_F2 v hv u hu)
      | exact P.hQ_F1_F2 u hu v hv
      | exact (polar_comm (quadPlus (4 + 1) K) u v).trans (P.hQ_F1_F2 v hv u hu)
  flipHerm_eq_zero := by
    intro i j hij u hu v hv
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | exact P.hH_A_Z1 u hu v hv
      | exact (flipHerm_eq_zero_iff hσ).mpr (P.hH_A_Z1 v hv u hu)
      | exact P.hH_A_Z2 u hu v hv
      | exact (flipHerm_eq_zero_iff hσ).mpr (P.hH_A_Z2 v hv u hu)
      | exact P.hH_A_F1 u hu v hv
      | exact (flipHerm_eq_zero_iff hσ).mpr (P.hH_A_F1 v hv u hu)
      | exact P.hH_A_F2 u hu v hv
      | exact (flipHerm_eq_zero_iff hσ).mpr (P.hH_A_F2 v hv u hu)
      | exact P.hH_Z1_Z2 u hu v hv
      | exact (flipHerm_eq_zero_iff hσ).mpr (P.hH_Z1_Z2 v hv u hu)
      | exact P.hH_Z1_F1 u hu v hv
      | exact (flipHerm_eq_zero_iff hσ).mpr (P.hH_Z1_F1 v hv u hu)
      | exact P.hH_Z1_F2 u hu v hv
      | exact (flipHerm_eq_zero_iff hσ).mpr (P.hH_Z1_F2 v hv u hu)
      | exact P.hH_Z2_F1 u hu v hv
      | exact (flipHerm_eq_zero_iff hσ).mpr (P.hH_Z2_F1 v hv u hu)
      | exact P.hH_Z2_F2 u hu v hv
      | exact (flipHerm_eq_zero_iff hσ).mpr (P.hH_Z2_F2 v hv u hu)
      | exact P.hH_F1_F2 u hu v hv
      | exact (flipHerm_eq_zero_iff hσ).mpr (P.hH_F1_F2 v hv u hu)

private theorem exists_gammaPrime (hσ : IsUnitaryInvolution σ)
    {c : FlipPt σ (4 + 1)} {γ : Fin (4 + 1) ⊕ Fin (4 + 1) → K}
    (hγspan : c.1 = K ∙ γ) (hγ0 : γ ≠ 0) (hQγ : quadPlus (4 + 1) K γ = 0)
    (hhγ : flipHerm σ γ γ ≠ 0)
    {f1 f2 : Submodule K (Fin (4 + 1) ⊕ Fin (4 + 1) → K)}
    (hf1γ : ∀ v ∈ f1, polar (quadPlus (4 + 1) K) v γ = 0 ∧ flipHerm σ v γ = 0)
    (hf2γ : ∀ v ∈ f2, polar (quadPlus (4 + 1) K) v γ = 0 ∧ flipHerm σ v γ = 0)
    {L : (Fin (4 + 1) ⊕ Fin (4 + 1) → K) ≃ₗ[K] (Fin (4 + 1) ⊕ Fin (4 + 1) → K)}
    (hLQ : ∀ y, quadPlus (4 + 1) K (L y) = quadPlus (4 + 1) K y)
    (hLflip : ∀ y, L (dFlip σ y) = dFlip σ (L y))
    (hL3 : (K ∙ stdE (K := K) (n := 4 + 1) 3).map L.toLinearMap = f1)
    (hL4 : (K ∙ stdE (K := K) (n := 4 + 1) 4).map L.toLinearMap = f2) :
    ∃ γ' : Fin (4 + 1) ⊕ Fin (4 + 1) → K,
      L γ' = γ ∧ IsFlipflopPt σ (K ∙ γ') ∧ quadPlus (4 + 1) K γ' = 0 ∧
        (γ' (.inl 3) = 0 ∧ γ' (.inr 3) = 0) ∧
        (γ' (.inl 4) = 0 ∧ γ' (.inr 4) = 0) ∧
        c.1 = (K ∙ γ').map L.toLinearMap := by
  set γ' : Fin (4 + 1) ⊕ Fin (4 + 1) → K := L.symm γ with hγ'def
  have hLγ' : L γ' = γ := by
    rw [hγ'def, L.apply_symm_apply]
  have hγ'0 : γ' ≠ 0 := by
    intro h
    apply hγ0
    rw [← hLγ', h, map_zero]
  have hQγ' : quadPlus (4 + 1) K γ' = 0 := by
    rw [← hLQ γ', hLγ', hQγ]
  have hhγ' : flipHerm σ γ' γ' ≠ 0 := by
    rw [← flipHerm_map_linearEquiv L hLQ hLflip γ' γ', hLγ']
    exact hhγ
  have hγ'pt : IsFlipflopPt σ (K ∙ γ') :=
    (isFlipflopPt_span_singleton_iff hγ'0).mpr ⟨hQγ', hhγ'⟩
  have hm3 : L (stdE (K := K) (n := 4 + 1) 3) ∈ f1 := by
    rw [← hL3]
    exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
  have hp3 : polar (quadPlus (4 + 1) K) (stdE (K := K) (n := 4 + 1) 3) γ' = 0 := by
    rw [← polar_map_of_linearIsometry (quadPlus _ K) L hLQ (stdE (K := K) (n := 4 + 1) 3) γ',
      L.apply_symm_apply]
    exact (hf1γ _ hm3).1
  have hh3 : flipHerm σ (stdE (K := K) (n := 4 + 1) 3) γ' = 0 := by
    rw [← flipHerm_map_linearEquiv L hLQ hLflip (stdE (K := K) (n := 4 + 1) 3) γ',
      L.apply_symm_apply]
    exact (hf1γ _ hm3).2
  have h3 : γ' (.inl 3) = 0 ∧ γ' (.inr 3) = 0 :=
    ⟨inl_eq_zero_of_flipHerm_stdE hσ.invol hh3, inr_eq_zero_of_polar_stdE hp3⟩
  have hm4 : L (stdE (K := K) (n := 4 + 1) 4) ∈ f2 := by
    rw [← hL4]
    exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
  have hp4 : polar (quadPlus (4 + 1) K) (stdE (K := K) (n := 4 + 1) 4) γ' = 0 := by
    rw [← polar_map_of_linearIsometry (quadPlus _ K) L hLQ (stdE (K := K) (n := 4 + 1) 4) γ',
      L.apply_symm_apply]
    exact (hf2γ _ hm4).1
  have hh4 : flipHerm σ (stdE (K := K) (n := 4 + 1) 4) γ' = 0 := by
    rw [← flipHerm_map_linearEquiv L hLQ hLflip (stdE (K := K) (n := 4 + 1) 4) γ',
      L.apply_symm_apply]
    exact (hf2γ _ hm4).2
  have h4 : γ' (.inl 4) = 0 ∧ γ' (.inr 4) = 0 :=
    ⟨inl_eq_zero_of_flipHerm_stdE hσ.invol hh4, inr_eq_zero_of_polar_stdE hp4⟩
  have hc_map : c.1 = (K ∙ γ').map L.toLinearMap := by
    rw [hγspan, Submodule.map_span, Set.image_singleton]
    change K ∙ γ = K ∙ L γ'
    rw [hLγ']
  exact ⟨γ', hLγ', hγ'pt, hQγ', h3, h4, hc_map⟩

private theorem flipColl_of_coords_zero (hσ : IsUnitaryInvolution σ)
    {a c : FlipPt σ (4 + 1)} (hadj : ¬ (flipGraph σ (4 + 1)).Adj a c)
    {L : (Fin (4 + 1) ⊕ Fin (4 + 1) → K) ≃ₗ[K] (Fin (4 + 1) ⊕ Fin (4 + 1) → K)}
    (hLQ : ∀ y, quadPlus (4 + 1) K (L y) = quadPlus (4 + 1) K y)
    (hLflip : ∀ y, L (dFlip σ y) = dFlip σ (L y))
    {γ' : Fin (4 + 1) ⊕ Fin (4 + 1) → K}
    (hL0 : (K ∙ stdE (K := K) (n := 4 + 1) 0).map L.toLinearMap = a.1)
    (hc_map : c.1 = (K ∙ γ').map L.toLinearMap)
    (h0inl : γ' (.inl 0) = 0) (h0inr : γ' (.inr 0) = 0) : False := by
  have ha_map : a.1 = (K ∙ stdE (K := K) (n := 4 + 1) 0).map L.toLinearMap := hL0.symm
  have hp0 : polar (quadPlus (4 + 1) K) (stdE (K := K) (n := 4 + 1) 0) γ' = 0 := by
    rw [polar_quadPlus]
    simp [h0inr]
  have hh0 : flipHerm σ (stdE (K := K) (n := 4 + 1) 0) γ' = 0 := by
    rw [flipHerm_apply]
    simp [h0inl]
  have hf : a.1 ≤ qPerp (4 + 1) K c.1 := by
    intro u hu
    refine mem_qPerp.mpr ?_
    intro v hv
    rw [ha_map] at hu
    rw [hc_map] at hv
    obtain ⟨u0, hu0, rfl⟩ := Submodule.mem_map.mp hu
    obtain ⟨v0, hv0, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu0
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv0
    change polar (quadPlus (4 + 1) K) (L (t • γ'))
      (L (s • stdE (K := K) (n := 4 + 1) 0)) = 0
    rw [polar_map_of_linearIsometry (quadPlus _ K) L hLQ, polar_smul_left, polar_smul_right,
      polar_comm (quadPlus (4 + 1) K) γ' (stdE (K := K) (n := 4 + 1) 0), hp0]
    simp
  have hh : a.1 ≤ flipOrth σ c.1 := by
    intro u hu
    refine mem_flipOrth.mpr ?_
    intro v hv
    rw [ha_map] at hu
    rw [hc_map] at hv
    obtain ⟨u0, hu0, rfl⟩ := Submodule.mem_map.mp hu
    obtain ⟨v0, hv0, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu0
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv0
    change flipHerm σ (L (t • γ')) (L (s • stdE (K := K) (n := 4 + 1) 0)) = 0
    rw [flipHerm_map_linearEquiv L hLQ hLflip, flipHerm_smul_left,
      flipHerm_smul_right, (flipHerm_eq_zero_iff hσ.invol).mp hh0]
    simp
  exact hadj (flipColl_of_orth hσ.invol a.2 c.2 hf hh)

private theorem eq_or_eq_dFlip_of_coords_zero
    {a c : FlipPt σ (4 + 1)} (hac : a ≠ c) (hc : c.1 ≠ dFlipSub σ a.1)
    {γ' : Fin (4 + 1) ⊕ Fin (4 + 1) → K}
    (hγ'0 : γ' ≠ 0) (hQγ' : quadPlus (4 + 1) K γ' = 0)
    {L : (Fin (4 + 1) ⊕ Fin (4 + 1) → K) ≃ₗ[K] (Fin (4 + 1) ⊕ Fin (4 + 1) → K)}
    (hLflip : ∀ y, L (dFlip σ y) = dFlip σ (L y))
    (hL0 : (K ∙ stdE (K := K) (n := 4 + 1) 0).map L.toLinearMap = a.1)
    (hc_map : c.1 = (K ∙ γ').map L.toLinearMap)
    (h3 : γ' (.inl 3) = 0 ∧ γ' (.inr 3) = 0)
    (h4 : γ' (.inl 4) = 0 ∧ γ' (.inr 4) = 0) :
    ¬ (γ' (.inl 1) = 0 ∧ γ' (.inr 1) = 0 ∧
      γ' (.inl 2) = 0 ∧ γ' (.inr 2) = 0) := by
  rintro ⟨h1i, h1r, h2i, h2r⟩
  have hsupp : γ' = γ' (.inl 0) • stdE (K := K) (n := 4 + 1) 0 +
      γ' (.inr 0) • stdF (K := K) (n := 4 + 1) 0 :=
    eq_smul_stdE_add_smul_stdF_of_coords_zero ⟨h1i, h1r⟩ ⟨h2i, h2r⟩ h3 h4
  have hprod : γ' (.inl 0) * γ' (.inr 0) = 0 :=
    mul_eq_zero_of_quadPlus_eq_zero ⟨h1i, h1r⟩ ⟨h2i, h2r⟩ h3 h4 hQγ'
  have ha_line : a.1 = K ∙ L (stdE (K := K) (n := 4 + 1) 0) := by
    rw [← hL0, Submodule.map_span, Set.image_singleton]
    rfl
  rcases mul_eq_zero.mp hprod with h0inl | h0inr
  · have hsuppF : γ' = γ' (.inr 0) • stdF (K := K) (n := 4 + 1) 0 := by
      rw [hsupp, h0inl, zero_smul, zero_add]
      simp [stdF, Pi.smul_apply, smul_eq_mul]
    have hF0ne : stdF (K := K) (n := 4 + 1) 0 ≠ 0 := by
      intro h
      have := congrFun h (.inr 0)
      simp [stdF] at this
    have hmemF : γ' ∈ K ∙ stdF (K := K) (n := 4 + 1) 0 := by
      rw [Submodule.mem_span_singleton]
      exact ⟨γ' (.inr 0), hsuppF.symm⟩
    have hKγ' : K ∙ γ' = K ∙ stdF (K := K) (n := 4 + 1) 0 := by
      rw [eq_span_singleton_of_mem_of_finrank_eq_one (finrank_span_singleton hF0ne)
        hmemF hγ'0]
    have hLdf : L (stdF (K := K) (n := 4 + 1) 0) =
        dFlip σ (L (stdE (K := K) (n := 4 + 1) 0)) := by
      rw [← dFlip_stdE (σ := σ) (n := 4 + 1) 0, hLflip]
    have hdF : c.1 = dFlipSub σ a.1 := by
      rw [hc_map, hKγ', Submodule.map_span, Set.image_singleton, ha_line,
        dFlipSub_span_singleton]
      change K ∙ L (stdF (K := K) (n := 4 + 1) 0) =
        K ∙ dFlip σ (L (stdE (K := K) (n := 4 + 1) 0))
      rw [hLdf]
    exact hc hdF
  · have hsuppE : γ' = γ' (.inl 0) • stdE (K := K) (n := 4 + 1) 0 := by
      rw [hsupp, h0inr, zero_smul, add_zero]
      simp [stdE, Pi.smul_apply, smul_eq_mul]
    have hE0ne : stdE (K := K) (n := 4 + 1) 0 ≠ 0 := by
      intro h
      have := congrFun h (.inl 0)
      simp [stdE] at this
    have hmemE : γ' ∈ K ∙ stdE (K := K) (n := 4 + 1) 0 := by
      rw [Submodule.mem_span_singleton]
      exact ⟨γ' (.inl 0), hsuppE.symm⟩
    have hKγ' : K ∙ γ' = K ∙ stdE (K := K) (n := 4 + 1) 0 := by
      rw [eq_span_singleton_of_mem_of_finrank_eq_one (finrank_span_singleton hE0ne)
        hmemE hγ'0]
    have hca : a.1 = c.1 := by
      rw [hc_map, hKγ', Submodule.map_span, Set.image_singleton]
      change a.1 = K ∙ L (stdE (K := K) (n := 4 + 1) 0)
      rw [ha_line]
    exact hac (Subtype.ext hca)

theorem coneConnected_five_of_card_eq_four [Finite K] [CharP K 2] (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) (a c : FlipPt σ (4 + 1)) (hac : a ≠ c)
    (hadj : ¬ (flipGraph σ (4 + 1)).Adj a c) (hc : c.1 ≠ dFlipSub σ a.1) :
    ConeConnected σ 4 (qPerp (4 + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1)) := by
  obtain ⟨γ, hγspan, hQγ, hhγ⟩ := c.2.exists_eq_span
  have hγ0 : γ ≠ 0 := by
    intro h
    have hbot : K ∙ γ = ⊥ := by rw [h, Submodule.span_singleton_eq_bot]
    have h1 := IsFlipflopPt.finrank_eq_one c.2
    rw [hγspan, hbot, finrank_bot] at h1
    omega
  obtain ⟨f1, hf1pt, hf1X, hf1Xh, hf1γ⟩ :=
    exists_isFlipflopPt_orth_orth_of_card_eq_four (n := 4 + 1) hσ hK
      (X := a.1) (IsFlipflopPt.isFlipflopSub a.2)
      (by rw [IsFlipflopPt.finrank_eq_one a.2]; omega) γ
  have hAf1 := isFlipflopSub_sup_point hσ.invol (IsFlipflopPt.isFlipflopSub a.2) hf1pt
    hf1X hf1Xh
  have hdimAf1 : Module.finrank K ↥(a.1 ⊔ f1) = 2 := by
    rw [hAf1.2.2, IsFlipflopPt.finrank_eq_one a.2]
  obtain ⟨f2, hf2pt, hf2X, hf2Xh, hf2γ⟩ :=
    exists_isFlipflopPt_orth_orth_of_card_eq_four (n := 4 + 1) hσ hK
      (X := a.1 ⊔ f1) hAf1.1 (by omega) γ
  have hY := isFlipflopSub_sup_point hσ.invol hAf1.1 hf2pt hf2X hf2Xh
  have hdimY : Module.finrank K ↥((a.1 ⊔ f1) ⊔ f2) = 3 := by
    rw [hY.2.2, hdimAf1]
  obtain ⟨z1, hz1pt, hz1Y, hz1Yh⟩ :=
    IsFlipflopSub.exists_isFlipflopPt_orth_of_lt hσ hY.1 (by rw [hdimY]; omega)
  have hY1 := isFlipflopSub_sup_point hσ.invol hY.1 hz1pt hz1Y hz1Yh
  have hdimY1 : Module.finrank K ↥(((a.1 ⊔ f1) ⊔ f2) ⊔ z1) = 4 := by
    rw [hY1.2.2, hdimY]
  obtain ⟨z2, hz2pt, hz2Y1, hz2Y1h⟩ :=
    IsFlipflopSub.exists_isFlipflopPt_orth_of_lt hσ hY1.1 (by rw [hdimY1]; omega)
  have P := pairOrth hσ.invol hz1Y hz2Y1 hz1Yh hz2Y1h hf1X hf1Xh hf2X hf2Xh
  let fr : FlipFrame σ (4 + 1) :=
    frameFive hσ.invol a.1 z1 z2 f1 f2 a.2 hz1pt hz2pt hf1pt hf2pt P
  have hN : ∀ d : K, σ d = d → d ≠ 0 → ∃ x : K, x * σ x = d := by
    intro d hd hd0
    obtain ⟨x, hx⟩ := hσ.norm_surj d hd hd0
    exact ⟨x, by rw [mul_comm, hx]⟩
  obtain ⟨L, hLQ, hLflip, hLline⟩ := fr.exists_isometry hσ.invol hN
  have hfrline : fr.line = ![a.1, z1, z2, f1, f2] := rfl
  have hL0 : (K ∙ stdE (K := K) (n := 4 + 1) 0).map L.toLinearMap = a.1 := by
    have := hLline 0
    rw [hfrline] at this
    simpa using this
  have hL3 : (K ∙ stdE (K := K) (n := 4 + 1) 3).map L.toLinearMap = f1 := by
    have := hLline 3
    rw [hfrline] at this
    simpa using this
  have hL4 : (K ∙ stdE (K := K) (n := 4 + 1) 4).map L.toLinearMap = f2 := by
    have := hLline 4
    rw [hfrline] at this
    simpa using this
  obtain ⟨γ', hLγ', hγ'pt, hQγ', h3, h4, hc_map⟩ :=
    exists_gammaPrime hσ hγspan hγ0 hQγ hhγ hf1γ hf2γ hLQ hLflip hL3 hL4
  have hγ'0 : γ' ≠ 0 := by
    intro h
    have hbot : K ∙ γ' = ⊥ := by rw [h, Submodule.span_singleton_eq_bot]
    have h1 := IsFlipflopPt.finrank_eq_one hγ'pt
    rw [hbot, finrank_bot] at h1
    omega
  have h0 : γ' (.inl 0) ≠ 0 ∨ γ' (.inr 0) ≠ 0 := by
    by_contra h
    push Not at h
    exact flipColl_of_coords_zero hσ hadj hLQ hLflip hL0 hc_map h.1 h.2
  have h12 := eq_or_eq_dFlip_of_coords_zero hac hc hγ'0 hQγ' hLflip hL0 hc_map h3 h4
  have hEmap : (qPerp (4 + 1) K ((K ∙ stdE (K := K) (n := 4 + 1) 0) ⊔ K ∙ γ') ⊓
      flipOrth σ ((K ∙ stdE (K := K) (n := 4 + 1) 0) ⊔ K ∙ γ')).map L.toLinearMap =
      qPerp (4 + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1) := by
    rw [Submodule.map_inf (f := L.toLinearMap) L.injective]
    rw [qPerp_map_of_quadPlus_map hLQ, flipOrth_map_of_quadPlus_map hLQ hLflip]
    simp only [Submodule.map_sup, hL0, hc_map]
  have hcoord := coneConnected_five_coord_of_card_eq_four hσ hK hγ'pt h3 h4 h0 h12
  have hmap := ConeConnected.map_linearEquiv (m := 4) hσ.invol L hLQ hLflip hcoord
  rwa [hEmap] at hmap

end CFSG.ClassicalInvolution.PhanDn
