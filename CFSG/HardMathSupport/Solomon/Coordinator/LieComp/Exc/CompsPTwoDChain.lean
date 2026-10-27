module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDPair
public import CFSG.ClassicalInvolution.WeakCT.Standard

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.WeakCT.SU4
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Universal.Unitary CFSG.Blueprint
  CFSG.Assembly.LowTwoRank
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CompsPTwoDChain

@[expose] def dEdge (n i j : ℕ) : Prop :=
  (i + 1 = j ∧ j + 1 < n) ∨ (i + 3 = n ∧ j + 1 = n)

section Natural

variable {K k : Type} [Field K] [Field k]

theorem map_blockMat (φ : K →+* k) (m i : ℕ) {kk : ℕ} (A : Matrix (Fin kk) (Fin kk) K) :
    (CFSG.ClassicalInvolution.Phan.blockMat m i A).map φ =
      CFSG.ClassicalInvolution.Phan.blockMat m i (A.map φ) := by
  ext a b
  simp only [Matrix.map_apply, CFSG.ClassicalInvolution.Phan.blockMat_apply]
  split_ifs with h
  · rfl
  · simp only [Matrix.one_apply]
    split_ifs <;> simp

theorem map_blockSL {m kk i : ℕ} (h : i + kk ≤ m) (φ : K →+* k) (A : SL(kk, K)) :
    Matrix.SpecialLinearGroup.map φ (blockSL K m kk i h A) =
      blockSL k m kk i h (Matrix.SpecialLinearGroup.map φ A) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_blockSL, coe_blockSL,
    Matrix.SpecialLinearGroup.map_apply_coe]
  exact map_blockMat φ m i _

theorem map_blockSL2 (φ : K →+* k) {n : ℕ} (c : Fin n) (A : SL(2, K)) :
    Matrix.SpecialLinearGroup.map φ (blockSL2 K n c A) =
      blockSL2 k n c (Matrix.SpecialLinearGroup.map φ A) :=
  map_blockSL _ φ A

theorem map_injective_sl (φ : K →+* k) (d : ℕ) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin d) φ) := by
  intro A B h
  refine Subtype.ext (Matrix.ext fun i j => φ.injective ?_)
  have := congrArg (fun M : SL(d, k) => (M : Matrix (Fin d) (Fin d) k) i j) h
  simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this

theorem map_map_sl {F : Type} [Field F] (φ : F →+* K) (ψ : K →+* k) (d : ℕ) (A : SL(d, F)) :
    Matrix.SpecialLinearGroup.map ψ (Matrix.SpecialLinearGroup.map φ A) =
      Matrix.SpecialLinearGroup.map (ψ.comp φ) A :=
  Subtype.ext rfl

end Natural

section Pair

variable {K : Type} [Field K] {G : Type} [Group G]

theorem linearBlockStandardPair_of_blocks' {θ : SL(3, K) →* G}
    (hker : θ.ker ≤ Subgroup.center SL(3, K)) {U V : Subgroup G} (hU : (B12 K).map θ = U)
    (hV : (B23 K).map θ = V) : LinearBlockStandardPair K θ.range U V := by
  have hc : ∀ H : Subgroup SL(3, K),
      H.map (MulAut.conj (1 : SL(3, K))⁻¹).toMonoidHom = H := fun H => by ext x; simp
  exact ⟨θ, 1, rfl, hker, Or.inl ⟨by rw [hc]; exact hU, by rw [hc]; exact hV⟩⟩

theorem linearBlockStandardPair_eq_sup' {W U V : Subgroup G}
    (h : LinearBlockStandardPair K W U V) : W = U ⊔ V := by
  obtain ⟨θ, c, hrange, -, hor⟩ := h
  have htop : (B12 K).map (MulAut.conj c⁻¹).toMonoidHom ⊔
      (B23 K).map (MulAut.conj c⁻¹).toMonoidHom = ⊤ := by
    rw [← Subgroup.map_sup, B12_sup_B23, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (MulAut.conj c⁻¹).surjective
  have hW : W = ((B12 K).map (MulAut.conj c⁻¹).toMonoidHom).map θ ⊔
      ((B23 K).map (MulAut.conj c⁻¹).toMonoidHom).map θ := by
    rw [← hrange, MonoidHom.range_eq_map, ← Subgroup.map_sup, htop]
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hW, h1, h2]
  · rw [hW, h1, h2, sup_comm]

theorem map_codRestrict_eq_subgroupOf' {S : Type*} [Group S] (θ : S →* G) (N : Subgroup G)
    (hN : ∀ g, θ g ∈ N) (H : Subgroup S) :
    H.map (θ.codRestrict N hN) = (H.map θ).subgroupOf N := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, hgx⟩
    exact ⟨g, hg, Subtype.ext hgx⟩

theorem linearBlockStandardPair_subgroupOf' {W U V : Subgroup G}
    (h : LinearBlockStandardPair K W U V) (N : Subgroup G) (hU : U ≤ N) (hV : V ≤ N) :
    LinearBlockStandardPair K (W.subgroupOf N) (U.subgroupOf N) (V.subgroupOf N) := by
  have hW : W ≤ N := (linearBlockStandardPair_eq_sup' h) ▸ sup_le hU hV
  obtain ⟨θ, c, hrange, hker, hor⟩ := h
  have hN : ∀ g, θ g ∈ N := fun g => hW (hrange ▸ ⟨g, rfl⟩)
  refine ⟨θ.codRestrict N hN, c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map, map_codRestrict_eq_subgroupOf', ← MonoidHom.range_eq_map, hrange]
  · rw [MonoidHom.ker_codRestrict]
    exact hker
  · rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [map_codRestrict_eq_subgroupOf', map_codRestrict_eq_subgroupOf', h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [map_codRestrict_eq_subgroupOf', map_codRestrict_eq_subgroupOf', h1, h2]
      exact ⟨rfl, rfl⟩

end Pair

section Linear

variable {F k : Type} [Field F] [Field k] {G : Type} [Group G]

theorem exists_ne_one_of_injective_comp {m : ℕ} (θ : SL(m, k) →* G) (ψ : SL(2, k) →* SL(m, k))
    (h : Function.Injective (θ.comp ψ)) : ∃ x, θ x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have h1 : (θ.comp ψ) (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2))
      (j := 1) (by decide) (1 : k)) = (θ.comp ψ) 1 := by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hcon, hcon]
  have h2 := h h1
  have h3 := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 1) h2
  simp [CFSG.LinearGroups.coe_transvection] at h3

theorem linearPair_of_frame (ι : F →+* k) {θ : SL(3, k) →* G} {ρi ρj : SL(2, k) →* G}
    (h0 : θ.comp (blockSL k 3 2 0 (by omega)) = ρi)
    (h1 : θ.comp (blockSL k 3 2 1 (by omega)) = ρj) (hnt : ∃ x, θ x ≠ 1) (C : Subgroup G)
    (hi : (ρi.comp (Matrix.SpecialLinearGroup.map ι)).range ≤ C)
    (hj : (ρj.comp (Matrix.SpecialLinearGroup.map ι)).range ≤ C) :
    ∃ W, LinearBlockStandardPair F W
      ((ρi.comp (Matrix.SpecialLinearGroup.map ι)).range.subgroupOf C)
      ((ρj.comp (Matrix.SpecialLinearGroup.map ι)).range.subgroupOf C) := by
  set θ0 : SL(3, F) →* G := θ.comp (Matrix.SpecialLinearGroup.map ι) with hθ0
  have hker : θ0.ker ≤ Subgroup.center SL(3, F) := by
    have hk := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 k le_rfl) hnt
    intro x hx
    rw [MonoidHom.mem_ker, hθ0, MonoidHom.comp_apply] at hx
    have hc := hk hx
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro y
    apply map_injective_sl ι 3
    rw [map_mul, map_mul]
    exact hc _
  have e0 : θ0.comp (blockSL F 3 2 0 (by omega)) = ρi.comp (Matrix.SpecialLinearGroup.map ι) := by
    rw [hθ0, MonoidHom.comp_assoc]
    ext A : 1
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, map_blockSL, ← h0]
    rfl
  have e1 : θ0.comp (blockSL F 3 2 1 (by omega)) = ρj.comp (Matrix.SpecialLinearGroup.map ι) := by
    rw [hθ0, MonoidHom.comp_assoc]
    ext A : 1
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, map_blockSL, ← h1]
    rfl
  have hpair := linearBlockStandardPair_of_blocks' (θ := θ0) hker
    (U := (ρi.comp (Matrix.SpecialLinearGroup.map ι)).range)
    (V := (ρj.comp (Matrix.SpecialLinearGroup.map ι)).range)
    (by rw [B12, ← MonoidHom.range_comp, e0]) (by rw [B23, ← MonoidHom.range_comp, e1])
  exact ⟨_, linearBlockStandardPair_subgroupOf' hpair C hi hj⟩

end Linear

section Fork

variable {F K k : Type} [Field F] [Field K] [Field k] [Algebra F K] {G : Type} [Group G]
  {σ₀ : K ≃+* K}

theorem phi_usbSL (ι : K →+* k) (hσ : ∀ x : K, σ₀.toRingHom (σ₀.toRingHom x) = x)
    (Φ : SL(4, k) →* G) {ρ₀ ρ₂ : SL(2, k) →* G} (h0 : Φ.comp (blockSL2 k 3 0) = ρ₀)
    (h2 : Φ.comp (blockSL2 k 3 2) = ρ₂) (B : SL(2, K)) :
    Φ (Matrix.SpecialLinearGroup.map ι (usbSL σ₀.toRingHom hσ B)) =
      ρ₀ (Matrix.SpecialLinearGroup.map ι B) *
        ρ₂ (Matrix.SpecialLinearGroup.map (ι.comp σ₀.toRingHom) B) := by
  have hb : Matrix.SpecialLinearGroup.map ι (fieldAutSL (involEquiv σ₀.toRingHom hσ) 2 B) =
      Matrix.SpecialLinearGroup.map (ι.comp σ₀.toRingHom) B :=
    Subtype.ext (by
      ext i j
      simp [coe_fieldAutSL, involEquiv_apply, Matrix.SpecialLinearGroup.map_apply_coe])
  rw [usbSL_apply, map_mul, map_mul, map_blockSL2, map_blockSL2, hb]
  rw [← h0, ← h2]
  rfl

theorem mul_comm_of_mul {a x y : G} (hx : a * x = x * a) (hy : a * y = y * a) :
    a * (x * y) = (x * y) * a := by
  rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]

end Fork

section Main


theorem lieModel_of_chain {k : Type} [Field k] {G : Type} [Group G] {n p f : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p f) (hp2 : p ≠ 2)
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F] (hF : Nat.card F = p ^ f)
    (hq : 4 ≤ Nat.card F) {σ₀ : K ≃+* K} {b c : F} (D : KleinData F K σ₀ b c)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (ι : K →+* k) (ρ : ℕ → SL(2, k) →* G) (hρ : ∀ i, i < n → Function.Injective (ρ i))
    (hcomm : ∀ i j : ℕ, i < n → j < n → i ≠ j → ¬ dEdge n i j → ¬ dEdge n j i →
      ∀ A B, ρ i A * ρ j B = ρ j B * ρ i A)
    (hfr : ∀ i : ℕ, i + 3 < n → ∃ θ : SL(3, k) →* G,
      θ.comp (blockSL k 3 2 0 (by omega)) = ρ i ∧
        θ.comp (blockSL k 3 2 1 (by omega)) = ρ (i + 1))
    (Φ : SL(4, k) →* G) (hΦ0 : Φ.comp (blockSL2 k 3 0) = ρ (n - 2))
    (hΦ1 : Φ.comp (blockSL2 k 3 1) = ρ (n - 3)) (hΦ2 : Φ.comp (blockSL2 k 3 2) = ρ (n - 1))
    (C : Subgroup G)
    (hC : (⨆ i : Fin (n - 1),
      if i.val + 2 < n then
        ((ρ i.val).comp (Matrix.SpecialLinearGroup.map (ι.comp (algebraMap F K)))).range
      else ((Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp
        (usbSL σ₀.toRingHom (CompsPTwoDPair.σσ' D))).range) = C) :
    LieModel (↥C ⧸ Subgroup.center ↥C) .POmegaMinus n p f ∧ CFSG.IsQuasisimple ↥C := by
  classical
  have hn4 : 4 ≤ n := hadm.2.2
  have h2F : (2 : F) ≠ 0 := by
    have hp := hadm.1
    have hf := hadm.2.1
    have hqc : (ringChar F).Prime := by
      rw [ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hF]
      exact hp
    rw [Ne, ClassicalGroups.Orthogonal.two_eq_zero_iff_ringChar_eq_two hqc,
      ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hF]
    exact hp2
  set ιF : F →+* k := ι.comp (algebraMap F K) with hιF
  set Vg : Subgroup G := ((Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp
    (usbSL σ₀.toRingHom (CompsPTwoDPair.σσ' D))).range with hVg
  set nodeG : Fin (n - 1) → Subgroup G := fun i =>
    if i.val + 2 < n then ((ρ i.val).comp (Matrix.SpecialLinearGroup.map ιF)).range else Vg
    with hnodeG
  have hCeq : (⨆ i, nodeG i) = C := hC
  have hN : ∀ i, nodeG i ≤ C := fun i => hCeq ▸ le_iSup nodeG i
  set U : Fin (n - 1) → Subgroup ↥C := fun i => (nodeG i).subgroupOf C with hU
  have hgen : ⨆ i, U i = ⊤ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    have : ∀ i, (U i).map C.subtype = nodeG i := fun i => by
      rw [hU, Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.2 (hN i)
    simp only [this]
    exact hCeq
  have hlongVg : ∀ i : ℕ, i + 4 ≤ n → ∀ (A : SL(2, k)) (B : SL(2, K)),
      ρ i A * Φ (Matrix.SpecialLinearGroup.map ι (usbSL σ₀.toRingHom (CompsPTwoDPair.σσ' D) B)) =
        Φ (Matrix.SpecialLinearGroup.map ι (usbSL σ₀.toRingHom (CompsPTwoDPair.σσ' D) B)) *
          ρ i A := by
    intro i hi A B
    rw [phi_usbSL ι _ Φ hΦ0 hΦ2]
    exact mul_comm_of_mul
      (hcomm i (n - 2) (by omega) (by omega) (by omega) (by simp only [dEdge]; omega)
        (by simp only [dEdge]; omega) _ _)
      (hcomm i (n - 1) (by omega) (by omega) (by omega) (by simp only [dEdge]; omega)
        (by simp only [dEdge]; omega) _ _)
  have hcommU : ∀ i j : Fin (n - 1), i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j,
      u * v = v * u := by
    intro i j hij u hu v hv
    have hi2 : i.val + 2 < n := by have := j.isLt; omega
    refine Subtype.ext ?_
    simp only [hU, hnodeG, if_pos hi2, Subgroup.mem_subgroupOf] at hu
    obtain ⟨A, hA⟩ := hu
    by_cases hj2 : j.val + 2 < n
    · simp only [hU, hnodeG, if_pos hj2, Subgroup.mem_subgroupOf] at hv
      obtain ⟨B, hB⟩ := hv
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hA, ← hB]
      exact hcomm i.val j.val (by omega) (by omega) (by omega) (by simp only [dEdge]; omega)
        (by simp only [dEdge]; omega) _ _
    · simp only [hU, hnodeG, if_neg hj2, Subgroup.mem_subgroupOf, hVg] at hv
      obtain ⟨B, hB⟩ := hv
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hA, ← hB]
      exact hlongVg i.val (by have := j.isLt; omega) _ _
  have hpairU : ∀ i j : Fin (n - 1), i.val + 1 = j.val → j.val + 2 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j) := by
    intro i j hij hj
    have hi2 : i.val + 2 < n := by omega
    obtain ⟨θk, h0, h1⟩ := hfr i.val (by omega)
    have hnt := exists_ne_one_of_injective_comp θk (blockSL k 3 2 0 (by omega))
      (by rw [h0]; exact hρ _ (by omega))
    have hjv : j.val = i.val + 1 := hij.symm
    have hi' : ((ρ i.val).comp (Matrix.SpecialLinearGroup.map ιF)).range ≤ C := by
      have := hN i
      simpa only [hnodeG, if_pos hi2] using this
    have hj' : ((ρ (i.val + 1)).comp (Matrix.SpecialLinearGroup.map ιF)).range ≤ C := by
      have := hN j
      simpa only [hnodeG, if_pos hj, hjv] using this
    obtain ⟨W, hW⟩ := linearPair_of_frame ιF h0 h1 hnt C hi' hj'
    refine ⟨W, ?_⟩
    have hj3 : i.val + 1 + 2 < n := by omega
    simp only [hU, hnodeG, if_pos hi2, hjv, if_pos hj3]
    exact hW
  have htwU : ∀ i j : Fin (n - 1), i.val + 3 = n → j.val + 2 = n →
      ∃ W, TwistedB2BlockPair hirr W (U i) (U j) := by
    intro i j hi hj
    have hiv : i.val = n - 3 := by omega
    have hi2 : i.val + 2 < n := by omega
    have hj2 : ¬ j.val + 2 < n := by omega
    have hni : nodeG i = ((ρ (n - 3)).comp (Matrix.SpecialLinearGroup.map ιF)).range := by
      simp only [hnodeG, if_pos hi2, hiv]
    have hnj : nodeG j = Vg := by simp only [hnodeG, if_neg hj2]
    have hΦinj : Function.Injective
        ((Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp (blockSL2 K 3 1)) := by
      have e : (Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp (blockSL2 K 3 1) =
          (ρ (n - 3)).comp (Matrix.SpecialLinearGroup.map ι) := by
        ext A : 1
        simp only [MonoidHom.comp_apply, map_blockSL2]
        rw [← hΦ1]
        rfl
      rw [e]
      exact (hρ _ (by omega)).comp (map_injective_sl ι 2)
    have eU : (Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp
        ((blockSL2 K 3 1).comp (Matrix.SpecialLinearGroup.map (algebraMap F K))) =
        (ρ (n - 3)).comp (Matrix.SpecialLinearGroup.map ιF) := by
      ext A : 1
      simp only [MonoidHom.comp_apply, map_blockSL2, map_map_sl]
      rw [← hΦ1]
      rfl
    have hUC : ((Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp
        ((blockSL2 K 3 1).comp (Matrix.SpecialLinearGroup.map (algebraMap F K)))).range ≤ C := by
      rw [eU]
      have := hN i
      rwa [hni] at this
    have hVC : ((Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp
        (usbSL σ₀.toRingHom (CompsPTwoDPair.σσ' D))).range ≤ C := by
      have := hN j
      rwa [hnj] at this
    obtain ⟨W, hW⟩ := CompsPTwoDPair.twistedB2BlockPair_of_sl4 D hirr h2F
      (Φ.comp (Matrix.SpecialLinearGroup.map ι)) hΦinj C hUC hVC
    refine ⟨W, ?_⟩
    rw [eU] at hW
    simp only [hU, hni, hnj, hVg]
    exact hW
  obtain ⟨Ψ, -, -, hq', -, hlie, -⟩ := weakCT_spinMinus_of_pair hadm hp2 hF hq hirr U hgen
    hcommU hpairU htwU
  exact ⟨hlie, hq'⟩

end Main

end CompsPTwoDChain

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
