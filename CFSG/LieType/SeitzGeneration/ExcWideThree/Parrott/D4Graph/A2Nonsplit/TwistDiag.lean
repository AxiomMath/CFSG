module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.Frame
public import CFSG.HardMathSupport.Seitz.Proving.OrderThreeSLConj

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator CFSG.HardMathSupport.Seitz.Proving
open scoped commutatorElement

section Pure

variable {K : Type} [Field K] [Finite K]

theorem mem_center_of_forall_commutator_mem_center (hK4 : 4 ≤ Nat.card K) {w : SL2 K}
    (h : ∀ E : SL2 K, ⁅E, w⁆ ∈ Subgroup.center (SL2 K)) : w ∈ Subgroup.center (SL2 K) := by
  let φ : SL2 K →* ↥(Subgroup.center (SL2 K)) :=
    { toFun := fun E => ⟨⁅E, w⁆, h E⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun E₁ E₂ => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, commutatorElement_def]
        have hz := Subgroup.mem_center_iff.1 (h E₂)
        rw [commutatorElement_def] at hz
        calc E₁ * E₂ * w * (E₁ * E₂)⁻¹ * w⁻¹ =
            E₁ * (E₂ * w * E₂⁻¹ * w⁻¹) * w * E₁⁻¹ * w⁻¹ := by group
          _ = (E₂ * w * E₂⁻¹ * w⁻¹) * (E₁ * w * E₁⁻¹ * w⁻¹) := by rw [hz E₁]; group
          _ = E₁ * w * E₁⁻¹ * w⁻¹ * (E₂ * w * E₂⁻¹ * w⁻¹) := (hz _).symm }
  have hperf : commutator (SL2 K) = ⊤ :=
    (CFSG.GH74.GLS.IVK.GHInv.isQuasisimple_sl2 hK4).1.commutator_eq_top
  have hle : commutator (SL2 K) ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact Subtype.ext (Subgroup.mem_center_iff.1 (φ b).2 _)
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ φ.ker := hle (by rw [hperf]; trivial)
  rw [MonoidHom.mem_ker] at hg
  have h1 : ⁅g, w⁆ = 1 := congrArg Subtype.val hg
  exact (commutatorElement_eq_one_iff_commute.1 h1).eq

theorem eq_top_of_normal_of_not_le_center (hK4 : 4 ≤ Nat.card K) (N : Subgroup (SL2 K))
    [N.Normal] {x : SL2 K} (hx : x ∈ N) (hxZ : x ∉ Subgroup.center (SL2 K)) : N = ⊤ :=
  (CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple
    (CFSG.GH74.GLS.IVK.GHInv.isQuasisimple_sl2 hK4) N).resolve_left fun hle => hxZ (hle hx)

theorem twistDiag (hK4 : 4 ≤ Nat.card K) {B : SL2 K} (hB : B ∉ Subgroup.center (SL2 K))
    (hwit : ∃ C : SL2 K,
      ⁅B * (C * B * C⁻¹), B⁻¹ * (C * B⁻¹ * C⁻¹)⁆ ∉ Subgroup.center (SL2 K))
    (L : Subgroup (SL2 K × SL2 K))
    (hL : ∀ C : SL2 K, ∀ p ∈ L, ((C, C) : SL2 K × SL2 K) * p * (C, C)⁻¹ ∈ L)
    (hBL : ((B, B⁻¹) : SL2 K × SL2 K) ∈ L) (X : SL2 K) : ((X, 1) : SL2 K × SL2 K) ∈ L := by
  have hcomm : ∀ p ∈ L, ∀ C : SL2 K, ((⁅C, p.1⁆, ⁅C, p.2⁆) : SL2 K × SL2 K) ∈ L := by
    intro p hp C
    have h := L.mul_mem (hL C p hp) (L.inv_mem hp)
    convert h using 1
  set L₁ := L.comap (MonoidHom.inl (SL2 K) (SL2 K)) with hL₁
  have hL₁N : L₁.Normal := ⟨fun x hx C => by
    have h := hL C _ hx
    simpa [hL₁] using h⟩
  set L₂ := L.comap (MonoidHom.inr (SL2 K) (SL2 K)) with hL₂
  have hL₂N : L₂.Normal := ⟨fun x hx C => by
    have h := hL C _ hx
    simpa [hL₂] using h⟩
  by_contra hX
  have hL₁Z : L₁ ≤ Subgroup.center (SL2 K) := by
    intro x hx
    by_contra hxZ
    have htop := eq_top_of_normal_of_not_le_center hK4 L₁ hx hxZ
    exact hX (show X ∈ L₁ by rw [htop]; trivial)
  have hL₂Z : L₂ ≤ Subgroup.center (SL2 K) := by
    intro y hy
    by_contra hyZ
    have htop := eq_top_of_normal_of_not_le_center hK4 L₂ hy hyZ
    have h1 : ((1, B) : SL2 K × SL2 K) ∈ L := show B ∈ L₂ by rw [htop]; trivial
    have h2 : ((B, 1) : SL2 K × SL2 K) ∈ L := by
      have := L.mul_mem hBL h1
      simpa using this
    exact hB (hL₁Z (show B ∈ L₁ from h2))
  have hZ : ∀ p ∈ L, ∀ C : SL2 K, ⁅C, p.1⁆ ∈ Subgroup.center (SL2 K) →
      ⁅C, p.2⁆ ∈ Subgroup.center (SL2 K) := by
    intro p hp C hC
    refine mem_center_of_forall_commutator_mem_center hK4 fun E => hL₂Z ?_
    have h := hcomm _ (hcomm p hp C) E
    have h1 : ⁅E, ⁅C, p.1⁆⁆ = 1 := commutatorElement_eq_one_iff_commute.2
      (Subgroup.mem_center_iff.1 hC E)
    rw [h1] at h
    exact h
  obtain ⟨C, hC⟩ := hwit
  have hp : ((B * (C * B * C⁻¹), B⁻¹ * (C * B⁻¹ * C⁻¹)) : SL2 K × SL2 K) ∈ L := by
    have h := L.mul_mem hBL (hL C _ hBL)
    convert h using 1
  have h1 : ⁅B * (C * B * C⁻¹), B * (C * B * C⁻¹)⁆ ∈ Subgroup.center (SL2 K) := by
    rw [commutatorElement_self]
    exact one_mem _
  exact hC (hZ _ hp _ h1)

theorem coe_uSL (t : K) : ((uSL t : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![1, t; 0, 1] := rfl

theorem coe_witnessX (t : K) :
    ((orderThreeSL K * (uSL t * orderThreeSL K * (uSL t)⁻¹) : SL2 K) :
      Matrix (Fin 2) (Fin 2) K) = !![-1, t - 1; t + 1, -t ^ 2] := by
  rw [CFSG.LieType.Chevalley.uSL_inv]
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, orderThreeSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem coe_witnessY (t : K) :
    (((orderThreeSL K)⁻¹ * (uSL t * (orderThreeSL K)⁻¹ * (uSL t)⁻¹) : SL2 K) :
      Matrix (Fin 2) (Fin 2) K) = !![-t, t ^ 2 + 1; t - 1, -t ^ 2 + t - 1] := by
  rw [CFSG.LieType.Chevalley.uSL_inv]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_uSL,
    orderThreeSL_val, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem witness_entry (t : K) :
    ((⁅orderThreeSL K * (uSL t * orderThreeSL K * (uSL t)⁻¹),
        (orderThreeSL K)⁻¹ * (uSL t * (orderThreeSL K)⁻¹ * (uSL t)⁻¹)⁆ : SL2 K) :
      Matrix (Fin 2) (Fin 2) K) 0 1 = -3 * t - 4 * t ^ 3 - t ^ 5 := by
  have hX := coe_witnessX (K := K) t
  have hY := coe_witnessY (K := K) t
  set X := orderThreeSL K * (uSL t * orderThreeSL K * (uSL t)⁻¹)
  set Y := (orderThreeSL K)⁻¹ * (uSL t * (orderThreeSL K)⁻¹ * (uSL t)⁻¹)
  rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv, hX, hY,
    Matrix.adjugate_fin_two_of, Matrix.adjugate_fin_two_of, Matrix.mul_fin_two,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

theorem exists_witness_orderThreeSL (hK4 : 4 ≤ Nat.card K) :
    ∃ C : SL2 K, ⁅orderThreeSL K * (C * orderThreeSL K * C⁻¹),
      (orderThreeSL K)⁻¹ * (C * (orderThreeSL K)⁻¹ * C⁻¹)⁆ ∉ Subgroup.center (SL2 K) := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : K, -3 * t - 4 * t ^ 3 - t ^ 5 ≠ 0 := by
    by_cases h2 : (2 : K) = 0
    · obtain ⟨t, ht0, ht1⟩ : ∃ t : K, t ≠ 0 ∧ t ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have : Fintype K := Fintype.ofFinite K
        have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
          by_cases hx : x = 0
          · simp [hx]
          · simp [hcon x hx]
        have := Finset.card_le_card hsub
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
        have h01 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
        omega
      refine ⟨t, fun h => ?_⟩
      have e : -3 * t - 4 * t ^ 3 - t ^ 5 = t * (t + 1) ^ 4 := by
        linear_combination (-2 * t - 2 * t ^ 2 - 5 * t ^ 3 - 2 * t ^ 4 - t ^ 5) * h2
      rw [e] at h
      rcases mul_eq_zero.1 h with h | h
      · exact ht0 h
      · have : t + 1 = 0 := pow_eq_zero_iff (by norm_num) |>.1 h
        exact ht1 (by linear_combination this - h2)
    · refine ⟨1, fun h => h2 ?_⟩
      have h8 : (2 : K) ^ 3 = 0 := by linear_combination -h
      exact pow_eq_zero_iff (by norm_num) |>.1 h8
  refine ⟨uSL t, fun hc => ht ?_⟩
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  rw [← witness_entry t, ← hr]
  simp

end Pure

section D4


variable {K : Type} [Field K]

local notation "𝕩" => xPar (rootOperatorFamily Tag.D4)

theorem frameDiag_conj_frameK₂ (C X : SL2 K) :
    frameDiag C * frameK₂ K X * (frameDiag C)⁻¹ = frameK₂ K (C * X * C⁻¹) := by
  obtain ⟨-, h12, -⟩ := frameK_commute (K := K) C (C * X * C⁻¹)
  obtain ⟨-, -, h32⟩ := frameK_commute (K := K) C (C * X * C⁻¹)
  have e : frameK₂ K (C * X * C⁻¹) = frameK₂ K C * frameK₂ K X * (frameK₂ K C)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [e] at h12 h32 ⊢
  rw [frameDiag]
  calc frameK₁ K C * frameK₃ K C * frameK₂ K C * frameK₂ K X *
        (frameK₁ K C * frameK₃ K C * frameK₂ K C)⁻¹ =
      frameK₁ K C * (frameK₃ K C * (frameK₂ K C * frameK₂ K X * (frameK₂ K C)⁻¹) *
        (frameK₃ K C)⁻¹) * (frameK₁ K C)⁻¹ := by group
    _ = _ := by rw [h32.eq, mul_inv_cancel_right, h12.eq, mul_inv_cancel_right]

theorem frameDiag_conj_frameK₃ (C Y : SL2 K) :
    frameDiag C * frameK₃ K Y * (frameDiag C)⁻¹ = frameK₃ K (C * Y * C⁻¹) := by
  obtain ⟨h13, -, -⟩ := frameK_commute (K := K) C (C * Y * C⁻¹)
  obtain ⟨-, -, h32⟩ := frameK_commute (K := K) Y C
  have e : frameK₃ K (C * Y * C⁻¹) = frameK₃ K C * frameK₃ K Y * (frameK₃ K C)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [e] at h13 ⊢
  rw [frameDiag]
  exact conj_eq_of_commute h13 h32.symm

theorem frameK_mem_closure [Finite K] (hK4 : 4 ≤ Nat.card K) {B : SL2 K}
    (hB : B ∉ Subgroup.center (SL2 K))
    (hwit : ∃ C : SL2 K,
      ⁅B * (C * B * C⁻¹), B⁻¹ * (C * B⁻¹ * C⁻¹)⁆ ∉ Subgroup.center (SL2 K)) (A : SL2 K) :
    frameK₁ K A ∈ Subgroup.closure ((fixedSubgroup (gammaP K B) : Set ↥(adjointGroup Tag.D4 K)) ∪
        {frameD K B}) ∧
      frameK₃ K A ∈ Subgroup.closure ((fixedSubgroup (gammaP K B) :
        Set ↥(adjointGroup Tag.D4 K)) ∪ {frameD K B}) ∧
      frameK₂ K A ∈ Subgroup.closure ((fixedSubgroup (gammaP K B) :
        Set ↥(adjointGroup Tag.D4 K)) ∪ {frameD K B}) := by
  set M := Subgroup.closure ((fixedSubgroup (gammaP K B) : Set ↥(adjointGroup Tag.D4 K)) ∪
    {frameD K B}) with hM
  have hΔ : ∀ C, frameDiag C ∈ M := fun C =>
    Subgroup.subset_closure (Or.inl (gammaP_frameDiag B C))
  have hd : frameD K B ∈ M := Subgroup.subset_closure (Or.inr rfl)
  set f := (frameK₂ K).noncommCoprod (frameK₃ K)
    (fun X Y => ((frameK_commute (K := K) Y X).2.2).symm) with hf
  have hfapp : ∀ p : SL2 K × SL2 K, f p = frameK₂ K p.1 * frameK₃ K p.2 := fun p => rfl
  set L := M.comap f with hL
  have hLn : ∀ C : SL2 K, ∀ p ∈ L, ((C, C) : SL2 K × SL2 K) * p * (C, C)⁻¹ ∈ L := by
    intro C p hp
    have hp' : frameK₂ K p.1 * frameK₃ K p.2 ∈ M := by rw [← hfapp]; exact hp
    show f _ ∈ M
    rw [hfapp]
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
    rw [← frameDiag_conj_frameK₂, ← frameDiag_conj_frameK₃,
      show frameDiag C * frameK₂ K p.1 * (frameDiag C)⁻¹ *
          (frameDiag C * frameK₃ K p.2 * (frameDiag C)⁻¹) =
        frameDiag C * (frameK₂ K p.1 * frameK₃ K p.2) * (frameDiag C)⁻¹ by group]
    exact M.mul_mem (M.mul_mem (hΔ C) hp') (M.inv_mem (hΔ C))
  have hBL : ((B, B⁻¹) : SL2 K × SL2 K) ∈ L := by
    show f _ ∈ M
    rw [hfapp, map_inv]
    exact hd
  have h2 : ∀ X, frameK₂ K X ∈ M := by
    intro X
    have h := twistDiag hK4 hB hwit L hLn hBL X
    have h' : f (X, 1) ∈ M := h
    rwa [hfapp, map_one, mul_one] at h'
  have h3 : ∀ Y, frameK₃ K Y ∈ M := by
    set N := M.comap (frameK₃ K) with hN
    have hNn : N.Normal := ⟨fun y hy C => by
      show frameK₃ K (C * y * C⁻¹) ∈ M
      rw [← frameDiag_conj_frameK₃]
      exact M.mul_mem (M.mul_mem (hΔ C) hy) (M.inv_mem (hΔ C))⟩
    have hBN : B⁻¹ ∈ N := by
      show frameK₃ K B⁻¹ ∈ M
      have e : frameK₃ K B⁻¹ = (frameK₂ K B)⁻¹ * frameD K B := by
        rw [frameD, map_inv, inv_mul_cancel_left]
      rw [e]
      exact M.mul_mem (M.inv_mem (h2 B)) hd
    have hBZ : B⁻¹ ∉ Subgroup.center (SL2 K) := fun h => hB (by
      simpa using (Subgroup.center (SL2 K)).inv_mem h)
    have htop := eq_top_of_normal_of_not_le_center hK4 N hBN hBZ
    intro Y
    show Y ∈ N
    rw [htop]
    trivial
  refine ⟨?_, h3 A, h2 A⟩
  have e : frameK₁ K A = frameDiag A * (frameK₂ K A)⁻¹ * (frameK₃ K A)⁻¹ := by
    rw [frameDiag]
    group
  rw [e]
  exact M.mul_mem (M.mul_mem (hΔ A) (M.inv_mem (h2 A))) (M.inv_mem (h3 A))

theorem IsFrameHom.xPar_mem {f : SL2 K →* ↥(adjointGroup Tag.D4 K)} {β : Fin Tag.D4.rank → ℤ}
    (hf : IsFrameHom f β) {M : Subgroup ↥(adjointGroup Tag.D4 K)} (hM : ∀ A, f A ∈ M) (c : K) :
    𝕩 β c ∈ M ∧ 𝕩 (-β) c ∈ M := by
  obtain ⟨⟨ε, hε, hu⟩, ⟨ε', hε', hv⟩⟩ := hf
  refine ⟨?_, ?_⟩
  · have h := hM (uSL (ε * c))
    rwa [hu, ← mul_assoc, hε, one_mul] at h
  · have h := hM (vSL (ε' * c))
    rwa [hv, ← mul_assoc, hε', one_mul] at h

theorem xPar_frame_mem_closure [Finite K] (hK4 : 4 ≤ Nat.card K) {B : SL2 K}
    (hB : B ∉ Subgroup.center (SL2 K))
    (hwit : ∃ C : SL2 K,
      ⁅B * (C * B * C⁻¹), B⁻¹ * (C * B⁻¹ * C⁻¹)⁆ ∉ Subgroup.center (SL2 K))
    {β : Fin Tag.D4.rank → ℤ} (hβ : β ∈ longOrthRoots) (c : K) :
    𝕩 β c ∈ Subgroup.closure ((fixedSubgroup (gammaP K B) : Set ↥(adjointGroup Tag.D4 K)) ∪
        {frameD K B}) ∧
      𝕩 (-β) c ∈ Subgroup.closure ((fixedSubgroup (gammaP K B) :
        Set ↥(adjointGroup Tag.D4 K)) ∪ {frameD K B}) := by
  have h := frameK_mem_closure hK4 hB hwit
  rw [longOrthRoots_eq] at hβ
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hβ
  rcases hβ with rfl | rfl | rfl
  · exact isFrameHom_frameK₁.xPar_mem (fun A => (h A).1) c
  · exact isFrameHom_frameK₂.xPar_mem (fun A => (h A).2.2) c
  · exact isFrameHom_frameK₃.xPar_mem (fun A => (h A).2.1) c

end D4

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
