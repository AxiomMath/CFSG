module

public import CFSG.CharacterTheory.SteinbergBSExceptionalCharacterTools
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Characters
public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7.SuzukiCoh

open CFSG CFSG.GH74.QTGen4.Recog.G23.P7
open scoped Classical

variable {G : Type} [Group G] [Fintype G]

theorem bip_comm (f g : G → ℂ) :
    BlocksInnerProduct f g = starRingEnd ℂ (BlocksInnerProduct g f) := by
  unfold BlocksInnerProduct
  rw [map_mul, map_sum, map_inv₀, Complex.conj_natCast]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem bip_add_left (f g h : G → ℂ) :
    BlocksInnerProduct (f + g) h = BlocksInnerProduct f h + BlocksInnerProduct g h := by
  unfold BlocksInnerProduct
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.add_apply]
  ring

theorem bip_sub_left (f g h : G → ℂ) :
    BlocksInnerProduct (f - g) h = BlocksInnerProduct f h - BlocksInnerProduct g h := by
  unfold BlocksInnerProduct
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.sub_apply]
  ring

theorem bip_smul_left (c : ℂ) (f g : G → ℂ) :
    BlocksInnerProduct (c • f) g = c * BlocksInnerProduct f g := by
  unfold BlocksInnerProduct
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem bip_sub_right (f g h : G → ℂ) :
    BlocksInnerProduct f (g - h) = BlocksInnerProduct f g - BlocksInnerProduct f h := by
  rw [bip_comm, bip_sub_left, map_sub, bip_comm f g, bip_comm f h]

theorem bip_smul_right (c : ℂ) (f g : G → ℂ) :
    BlocksInnerProduct f (c • g) = starRingEnd ℂ c * BlocksInnerProduct f g := by
  rw [bip_comm, bip_smul_left, map_mul, bip_comm f g]

theorem bip_sum_left {ι : Type*} [Fintype ι] (c : ι → ℂ) (f : ι → G → ℂ) (h : G → ℂ) :
    BlocksInnerProduct (fun x => ∑ i, c i * f i x) h = ∑ i, c i * BlocksInnerProduct (f i) h := by
  unfold BlocksInnerProduct
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring

theorem bip_irr {X Y : G → ℂ} (hX : X ∈ BlocksIrr G) (hY : Y ∈ BlocksIrr G) :
    BlocksInnerProduct X Y = if X = Y then 1 else 0 := by
  have h := blocksInnerProduct_irreducible (G := G) ⟨X, hX⟩ ⟨Y, hY⟩
  simpa only [Subtype.mk.injEq] using h

theorem bip_one : BlocksInnerProduct (fun _ : G => (1 : ℂ)) (fun _ => 1) = 1 := by
  have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold BlocksInnerProduct
  simp only [map_one, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Nat.card_eq_fintype_card]
  exact inv_mul_cancel₀ hG

theorem one_mem_irr : (fun _ : G => (1 : ℂ)) ∈ BlocksIrr G :=
  CFSG.BrauerThirdMainTheorem.Helpers.trivial_mem_irr G

theorem bip_two_irr {A B Y : G → ℂ} (hA : A ∈ BlocksIrr G) (hB : B ∈ BlocksIrr G)
    (hY : Y ∈ BlocksIrr G) (a b : ℤ) :
    BlocksInnerProduct ((a : ℂ) • A + (b : ℂ) • B) Y =
      (a : ℂ) * (if A = Y then 1 else 0) + (b : ℂ) * (if B = Y then 1 else 0) := by
  rw [bip_add_left, bip_smul_left, bip_smul_left, bip_irr hA hY, bip_irr hB hY]

theorem bessel_four {Y : Fin 4 → G → ℂ} (hY : ∀ i, Y i ∈ BlocksIrr G) (hinj : Function.Injective Y)
    {f : G → ℂ} (hf : f ∈ BlocksVChar G) {N : ℤ} (hN : BlocksInnerProduct f f = (N : ℂ))
    (c : Fin 4 → ℤ) (hc : ∀ i, BlocksInnerProduct f (Y i) = (c i : ℂ)) :
    (∑ i, c i ^ 2 ≤ N) ∧ (∑ i, c i ^ 2 = N → f = fun x => ∑ i, (c i : ℂ) * Y i x) := by
  have hv : ∀ i, Y i ∈ BlocksVChar G := fun i => AddSubgroup.subset_closure (hY i)
  have horth : ∀ i j, BlocksInnerProduct (Y i) (Y j) = if i = j then 1 else 0 := by
    intro i j
    rw [bip_irr (hY i) (hY j)]
    simp only [hinj.eq_iff]
  have key := blocksInnerProduct_orthonormal_residual Y hv horth f hf c hc
  rw [hN] at key
  set M : ℤ := N - ∑ i, c i ^ 2 with hM
  have hkey : BlocksInnerProduct (f - fun x => ∑ i, (c i : ℂ) * Y i x)
      (f - fun x => ∑ i, (c i : ℂ) * Y i x) = (M : ℂ) := by
    rw [key, hM]
    push_cast
    ring
  have hre := blocksInnerProduct_self_re_nonneg (f - fun x => ∑ i, (c i : ℂ) * Y i x)
  simp only [hkey, Complex.intCast_re] at hre
  have hM0 : 0 ≤ M := by
    have : (0 : ℝ) ≤ (M : ℝ) := hre
    exact_mod_cast this
  refine ⟨by omega, fun heq => ?_⟩
  have hM' : M = 0 := by omega
  rw [hM'] at hkey
  have hzero := blocksInnerProduct_self_zero _ (by rw [hkey]; simp)
  exact sub_eq_zero.mp hzero

noncomputable abbrev indψ {H : Subgroup G} (χ : Fin 20 → H → ℂ) (k : Fin 15) : G → ℂ :=
  CFSG.TwoRankLowerBound.Helpers.inducedFunction H (psiFun H χ k)

@[expose] def thetaOf {H : Subgroup G} (χ : Fin 20 → H → ℂ) (i : Fin 4) : H → ℂ :=
  χ ⟨16 + i.val, by have := i.isLt; omega⟩

theorem thetaOf_inj {H : Subgroup G} {χ : Fin 20 → H → ℂ} (hinj : Function.Injective χ) :
    Function.Injective (thetaOf χ) := by
  intro i j hij
  have h := hinj hij
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [Fin.val_mk] at this
  omega

theorem list_mem {H : Subgroup G} (χ : Fin 20 → H → ℂ) (hirr : ∀ i, χ i ∈ BlocksIrr H) :
    ∀ L : List (Fin 20 × ℤ),
      (fun y : H => (L.map fun p => (p.2 : ℂ) * χ p.1 y).sum) ∈ BlocksVChar H
  | [] => by
      have h0 : (fun y : H => (([] : List (Fin 20 × ℤ)).map fun p => (p.2 : ℂ) * χ p.1 y).sum)
          = 0 := by
        funext y
        simp
      rw [h0]
      exact zero_mem _
  | p :: L => by
      have h1 : (fun y : H => ((p :: L).map fun q => (q.2 : ℂ) * χ q.1 y).sum) =
          (p.2 : ℤ) • χ p.1 + (fun y : H => (L.map fun q => (q.2 : ℂ) * χ q.1 y).sum) := by
        funext y
        simp [zsmul_eq_mul]
      rw [h1]
      exact add_mem (zsmul_mem (AddSubgroup.subset_closure (hirr p.1)) _) (list_mem χ hirr L)

theorem psi_mem {H : Subgroup G} (χ : Fin 20 → H → ℂ) (hirr : ∀ i, χ i ∈ BlocksIrr H)
    (k : Fin 15) : psiFun H χ k ∈ BlocksVChar H :=
  list_mem χ hirr (psiTerms k)

theorem psi_class {H : Subgroup G} (χ : Fin 20 → H → ℂ) (hirr : ∀ i, χ i ∈ BlocksIrr H)
    (k : Fin 15) : BlocksIsClassFunction (psiFun H χ k) :=
  blocksVChar_isClassFunction (psi_mem χ hirr k)

theorem psi0 {H : Subgroup G} (χ : Fin 20 → H → ℂ) :
    psiFun H χ 0 = χ 0 - χ 8 + χ 19 := by
  funext y
  simp [psiFun, psiTerms]
  ring

theorem psi5 {H : Subgroup G} (χ : Fin 20 → H → ℂ) : psiFun H χ 5 = χ 16 - χ 19 := by
  funext y
  simp [psiFun, psiTerms]
  ring

theorem psi6 {H : Subgroup G} (χ : Fin 20 → H → ℂ) : psiFun H χ 6 = χ 17 - χ 19 := by
  funext y
  simp [psiFun, psiTerms]
  ring

theorem psi7 {H : Subgroup G} (χ : Fin 20 → H → ℂ) : psiFun H χ 7 = χ 18 - χ 19 := by
  funext y
  simp [psiFun, psiTerms]
  ring

theorem pm_sq {ε : ℤ} (h : ε = 1 ∨ ε = -1) : (ε : ℂ) * ε = 1 := by
  rcases h with rfl | rfl <;> norm_num

theorem conj_pm (ε : ℤ) : starRingEnd ℂ (ε : ℂ) = ε := map_intCast _ _

theorem cover_lemma {A B Y V : G → ℂ} {a b : ℤ} (hV : V = (a : ℂ) • A + (b : ℂ) • B)
    (hA : A ∈ BlocksIrr G) (hB : B ∈ BlocksIrr G) (hY : Y ∈ BlocksIrr G)
    (h : BlocksInnerProduct V Y ≠ 0) : A = Y ∨ B = Y := by
  rw [hV, bip_two_irr hA hB hY] at h
  by_contra hc
  obtain ⟨hc1, hc2⟩ := not_or.mp hc
  rw [if_neg hc1, if_neg hc2] at h
  simp at h

theorem three_in_two {A B Y0 Y1 Y2 : G → ℂ} (h01 : Y0 ≠ Y1) (h02 : Y0 ≠ Y2) (h12 : Y1 ≠ Y2)
    (h0 : Y0 = A ∨ Y0 = B) (h1 : Y1 = A ∨ Y1 = B) (h2 : Y2 = A ∨ Y2 = B) : False := by
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    first
    | exact h01 (h0.trans h1.symm)
    | exact h02 (h0.trans h2.symm)
    | exact h12 (h1.trans h2.symm)

theorem geom_contra {f Y0 Y1 Y2 : G → ℂ} (h0 : Y0 ∈ BlocksIrr G) (h1 : Y1 ∈ BlocksIrr G)
    (h2 : Y2 ∈ BlocksIrr G) (s : ℤ) (hs : s ≠ 0) (hf1 : f 1 = 0)
    (hfeq : f = fun x => (s : ℂ) * Y0 x + (s : ℂ) * Y1 x + (s : ℂ) * Y2 x) : False := by
  have h := congrFun hfeq 1
  simp only [hf1] at h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    Complex.zero_re, zero_mul, sub_zero] at hre
  have p0 := blocksIrr_identity_re_pos ⟨Y0, h0⟩
  have p1 := blocksIrr_identity_re_pos ⟨Y1, h1⟩
  have p2 := blocksIrr_identity_re_pos ⟨Y2, h2⟩
  have hsum : (s : ℝ) * ((Y0 1).re + (Y1 1).re + (Y2 1).re) = 0 := by linarith
  have hpos : (0 : ℝ) < (Y0 1).re + (Y1 1).re + (Y2 1).re := by linarith
  rcases mul_eq_zero.mp hsum with h' | h'
  · exact hs (by exact_mod_cast h')
  · linarith

theorem rel_of_smul {f Y0 Y3 : G → ℂ} {ε : ℤ} {g : ℂ} (hε : (ε : ℂ) * ε = 1)
    (h : BlocksInnerProduct f ((ε : ℂ) • (Y0 - Y3)) = g) :
    BlocksInnerProduct f Y0 = BlocksInnerProduct f Y3 + (ε : ℂ) * g := by
  rw [bip_smul_right, bip_sub_right, conj_pm] at h
  linear_combination (ε : ℂ) * h - (BlocksInnerProduct f Y0 - BlocksInnerProduct f Y3) * hε

theorem decompose {A B Y V : G → ℂ} (hA : A ∈ BlocksIrr G) (hB : B ∈ BlocksIrr G)
    (hY : Y ∈ BlocksIrr G) (hAB : A ≠ B) {a b ε : ℤ} (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) (hε : ε = 1 ∨ ε = -1) (hV : V = (a : ℂ) • A + (b : ℂ) • B)
    (hVY : BlocksInnerProduct V Y = (ε : ℂ)) :
    ∃ X : G → ℂ, X ∈ BlocksIrr G ∧ ∃ ε₂ : ℤ, (ε₂ = 1 ∨ ε₂ = -1) ∧ X ≠ Y ∧
      V = (ε : ℂ) • Y + (ε₂ : ℂ) • X := by
  have hε0 : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  rw [hV, bip_two_irr hA hB hY] at hVY
  by_cases hAY : A = Y
  · have hBY : B ≠ Y := fun h => hAB (hAY.trans h.symm)
    rw [if_pos hAY, if_neg hBY] at hVY
    have ha' : a = ε := by
      have : (a : ℂ) = ε := by simpa using hVY
      exact_mod_cast this
    refine ⟨B, hB, b, hb, hBY, ?_⟩
    rw [hV, ha', hAY]
  · by_cases hBY : B = Y
    · rw [if_neg hAY, if_pos hBY] at hVY
      have hb' : b = ε := by
        have : (b : ℂ) = ε := by simpa using hVY
        exact_mod_cast this
      refine ⟨A, hA, a, ha, hAY, ?_⟩
      rw [hV, hb', hBY, add_comm]
    · rw [if_neg hAY, if_neg hBY] at hVY
      simp at hVY
      exact absurd hVY.symm hε0

theorem coeff_claim {f : G → ℂ} {Y : Fin 4 → G → ℂ} (hY : ∀ i, Y i ∈ BlocksIrr G)
    (hinj : Function.Injective Y) (hf : f ∈ BlocksVChar G) (hf1 : f 1 = 0)
    {N g g6 g7 ε c : ℤ} (hε : ε = 1 ∨ ε = -1) (hN : BlocksInnerProduct f f = (N : ℂ))
    (hN3 : N ≤ 3) (hg6 : g6 = g) (hg7 : g7 = g)
    (h3 : BlocksInnerProduct f (Y 3) = (c : ℂ))
    (h0 : BlocksInnerProduct f (Y 0) = (c : ℂ) + (ε : ℂ) * (g : ℂ))
    (h1 : BlocksInnerProduct f (Y 1) = (c : ℂ) + (ε : ℂ) * (g6 : ℂ))
    (h2 : BlocksInnerProduct f (Y 2) = (c : ℂ) + (ε : ℂ) * (g7 : ℂ)) :
    c + ε * g = 0 := by
  by_contra hne
  have hs0 : c + ε * g ≠ 0 := hne
  have hbes : ∀ i, BlocksInnerProduct f (Y i) =
      (((![c + ε * g, c + ε * g, c + ε * g, c] : Fin 4 → ℤ) i : ℤ) : ℂ) := by
    intro i
    fin_cases i
    · show BlocksInnerProduct f (Y 0) = ((c + ε * g : ℤ) : ℂ)
      rw [h0]; push_cast; ring
    · show BlocksInnerProduct f (Y 1) = ((c + ε * g : ℤ) : ℂ)
      rw [h1, hg6]; push_cast; ring
    · show BlocksInnerProduct f (Y 2) = ((c + ε * g : ℤ) : ℂ)
      rw [h2, hg7]; push_cast; ring
    · show BlocksInnerProduct f (Y 3) = ((c : ℤ) : ℂ)
      exact h3
  obtain ⟨hle, heq⟩ := bessel_four hY hinj hf hN ![c + ε * g, c + ε * g, c + ε * g, c] hbes
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.cons_val_fin_one]
    at hle heq
  have hss : 0 < (c + ε * g) * (c + ε * g) := mul_self_pos.mpr hs0
  have hcc : c * c ≤ 0 := by nlinarith
  have hc0 : c = 0 := mul_self_eq_zero.mp (le_antisymm hcc (mul_self_nonneg c))
  have hSN : (c + ε * g) ^ 2 + (c + ε * g) ^ 2 + (c + ε * g) ^ 2 + c ^ 2 = N := by
    nlinarith
  have hfe : f = fun x => ((c + ε * g : ℤ) : ℂ) * Y 0 x + ((c + ε * g : ℤ) : ℂ) * Y 1 x +
      ((c + ε * g : ℤ) : ℂ) * Y 2 x := by
    have := heq hSN
    rw [this]
    funext x
    simp [Fin.sum_univ_four, hc0]
  exact geom_contra (hY 0) (hY 1) (hY 2) (c + ε * g) hs0 hf1 hfe

theorem val2_of_orth {H : Subgroup G} {z : G} {χ : Fin 20 → H → ℂ} (hχ : HCharProps H z χ)
    (hinv : ∀ x ∈ specialD z H, ∀ h ∈ H, h * x * h⁻¹ ∈ specialD z H)
    (X : G → ℂ) (hX : BlocksIsClassFunction X) (ε₂ : ℂ)
    (hk : ∀ k, BlocksInnerProduct (fun y : H => X y + ε₂ * χ 8 y) (psiFun H χ k) = 0) :
    ∀ y : H, (y : G) ∈ specialD z H → X y + ε₂ * χ 8 y = 0 := by
  have hirr8 : χ 8 ∈ BlocksIrr H := hχ.irr 8
  have hfc : BlocksIsClassFunction (fun y : H => X y + ε₂ * χ 8 y) := by
    intro g h
    have hc := CFSG.SmallDefect.isClassFunction_of_mem hirr8 g h
    have hcoe : ((h * g * h⁻¹ : H) : G) = (h : G) * (g : G) * (h : G)⁻¹ := by simp
    simp only [hcoe, hc]
    rw [hX (g : G) (h : G)]
  set w : H → ℂ := fun y => if (y : G) ∈ specialD z H then X y + ε₂ * χ 8 y else 0 with hw
  have hwc : BlocksIsClassFunction w := by
    intro g h
    have hcoe : ((h * g * h⁻¹ : H) : G) = (h : G) * (g : G) * (h : G)⁻¹ := by simp
    by_cases hg : (g : G) ∈ specialD z H
    · have hgh : ((h * g * h⁻¹ : H) : G) ∈ specialD z H := by
        rw [hcoe]; exact hinv _ hg _ h.2
      simp only [hw, hgh, hg, if_true]
      exact hfc g h
    · have hgh : ((h * g * h⁻¹ : H) : G) ∉ specialD z H := by
        intro hmem
        apply hg
        have h2 := hinv _ hmem _ (H.inv_mem h.2)
        have hg' : (h : G)⁻¹ * ((h * g * h⁻¹ : H) : G) * ((h : G)⁻¹)⁻¹ = (g : G) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rwa [hg'] at h2
      simp only [hw, hgh, hg, if_false]
  have hwv : ∀ y : H, (y : G) ∉ specialD z H → w y = 0 := fun y hy => by
    simp only [hw, if_neg hy]
  obtain ⟨c', hc'⟩ := hχ.span w hwc hwv
  have hbw : ∀ k, BlocksInnerProduct w (psiFun H χ k) = 0 := by
    intro k
    have : BlocksInnerProduct w (psiFun H χ k) =
        BlocksInnerProduct (fun y : H => X y + ε₂ * χ 8 y) (psiFun H χ k) := by
      unfold BlocksInnerProduct
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hy : (y : G) ∈ specialD z H
      · simp [hw, hy]
      · simp [hw, hy, hχ.vanish k y hy]
    rw [this, hk k]
  have hww : BlocksInnerProduct w w = 0 := by
    calc BlocksInnerProduct w w
        = BlocksInnerProduct (fun y : H => ∑ k, c' k * psiFun H χ k y) w := by rw [← hc']
      _ = ∑ k, c' k * BlocksInnerProduct (psiFun H χ k) w := bip_sum_left c' _ w
      _ = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [bip_comm, hbw k, map_zero, mul_zero]
  have hw0 := blocksInnerProduct_self_zero w hww
  intro y hy
  have := congrFun hw0 y
  simpa [hw, hy] using this

theorem psiGram_symm : ∀ k l : Fin 15, psiGram k l = psiGram l k := by decide

theorem psiGram_diag_le : ∀ k : Fin 15, psiGram k k ≤ 3 := by decide

theorem psiGram_six_seven : ∀ k : Fin 15, k.val ≠ 0 → k.val ≠ 5 → k.val ≠ 6 → k.val ≠ 7 →
    psiGram 6 k = psiGram 5 k ∧ psiGram 7 k = psiGram 5 k := by decide

theorem psiGram_identity : ∀ k : Fin 15, k.val ≠ 0 → k.val ≠ 5 →
    psiGram 0 k - (if k = 0 ∨ k = 10 then 1 else 0) + psiGram 5 k = 0 := by decide

theorem suzukiCoherent_core {H : Subgroup G} {z : G} {χ : Fin 20 → H → ℂ}
    (hcent : ∀ a ∈ specialD z H, Subgroup.centralizer {a} ≤ H)
    (hfus : ∀ a ∈ specialD z H, ∀ b ∈ specialD z H, IsConj a b → ∃ h ∈ H, h * a * h⁻¹ = b)
    (hcen : ∀ h ∈ H, h * z * h⁻¹ = z)
    (hχ : HCharProps H z χ) :
    ∃ (X₁ X₂ : G → ℂ) (ε₁ ε₂ : ℤ), SuzukiCoherent H (specialD z H) χ X₁ X₂ ε₁ ε₂ := by
  have hirr : ∀ i, χ i ∈ BlocksIrr H := hχ.irr
  have hinj : Function.Injective χ := hχ.inj
  have hD1 : (1 : G) ∉ specialD z H := by
    rintro ⟨_, h | ⟨k, hk, hord, _⟩⟩
    · exact h.2 rfl
    · rw [orderOf_one] at hord
      omega
  have hinv : ∀ x ∈ specialD z H, ∀ h ∈ H, h * x * h⁻¹ ∈ specialD z H := by
    rintro x ⟨hxH, hx⟩ h hh
    refine ⟨H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh), ?_⟩
    have hpow : ∀ n : ℕ, (h * x * h⁻¹) ^ n = h * x ^ n * h⁻¹ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, ih, pow_succ]; group
    rcases hx with ⟨hx3, hx1⟩ | ⟨k, hk, hord, hpowz⟩
    · left
      refine ⟨by rw [hpow, hx3]; group, ?_⟩
      intro h1
      apply hx1
      have hx' : x = h⁻¹ * (h * x * h⁻¹) * h := by group
      rw [hx', h1]
      group
    · right
      refine ⟨k, hk, ?_, ?_⟩
      · rw [← hord]
        have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective x
        simpa [MulAut.conj_apply] using this
      · rw [hpow, hpowz, hcen h hh]
  have hψz : ∀ k (y : H), (y : G) ∉ specialD z H → psiFun H χ k y = 0 := hχ.vanish
  have hψc : ∀ k, BlocksIsClassFunction (psiFun H χ k) := fun k => psi_class χ hirr k
  have hindv : ∀ k, indψ χ k ∈ BlocksVChar G := fun k =>
    inducedFunction_mem_blocksVChar H (psi_mem χ hirr k)
  have hind1 : ∀ k, indψ χ k 1 = 0 := fun k =>
    CFSG.CharacterTheory.SteinbergBS.inducedFunction_suzuki_vanish (hψz k) 1 (fun a ha hc => by
      rw [isConj_one_right] at hc
      exact hD1 (hc ▸ ha))
  have hgram : ∀ k l, BlocksInnerProduct (indψ χ k) (indψ χ l) = (psiGram k l : ℂ) := fun k l => by
    rw [(CFSG.CharacterTheory.SteinbergBS.suzuki_induction_special_classes hcent hfus
      (hψc k) (hψz k) (hψc l) (hψz l)).1, hχ.gram k l]
  have hgram' : ∀ k l, BlocksInnerProduct (indψ χ k) (indψ χ l) = (psiGram l k : ℂ) := fun k l => by
    rw [hgram k l, psiGram_symm k l]
  have hbone : ∀ k, BlocksInnerProduct (indψ χ k) (fun _ : G => (1 : ℂ)) =
      if k = 0 ∨ k = 10 then 1 else 0 := by
    intro k
    rw [blocksInnerProduct_inducedFunction_left H (psiFun H χ k) (fun _ => (1 : ℂ))
      (fun _ _ => rfl)]
    have hχ0 : (fun h : H => (1 : ℂ)) = χ 0 := funext fun h => (hχ.triv h).symm
    have := hχ.inner_triv k
    rw [← hχ0] at this
    exact this
  obtain ⟨ε, Y, hεpm, hYirr, hYinj, hYdiff⟩ :=
    CFSG.CharacterTheory.SteinbergBS.suzuki_exceptional_characters hcent hfus hD1 (n := 4)
      (by norm_num) (thetaOf χ) (fun i => hirr _) (thetaOf_inj hinj) (by
        intro i j h hh
        have e5 : χ 16 h - χ 19 h = 0 := by
          have := hψz 5 h hh
          rwa [psi5] at this
        have e6 : χ 17 h - χ 19 h = 0 := by
          have := hψz 6 h hh
          rwa [psi6] at this
        have e7 : χ 18 h - χ 19 h = 0 := by
          have := hψz 7 h hh
          rwa [psi7] at this
        have key : ∀ m : Fin 4, thetaOf χ m h = χ 19 h := by
          intro m
          fin_cases m
          · exact sub_eq_zero.mp e5
          · exact sub_eq_zero.mp e6
          · exact sub_eq_zero.mp e7
          · rfl
        rw [key i, key j, sub_self])
  have hY5 : indψ χ 5 = (ε : ℂ) • (Y 0 - Y 3) := by
    have e : psiFun H χ 5 = thetaOf χ 0 - thetaOf χ 3 := by
      rw [psi5]
      rfl
    show CFSG.TwoRankLowerBound.Helpers.inducedFunction H (psiFun H χ 5) = _
    rw [e]
    exact hYdiff 0 3
  have hY6 : indψ χ 6 = (ε : ℂ) • (Y 1 - Y 3) := by
    have e : psiFun H χ 6 = thetaOf χ 1 - thetaOf χ 3 := by
      rw [psi6]
      rfl
    show CFSG.TwoRankLowerBound.Helpers.inducedFunction H (psiFun H χ 6) = _
    rw [e]
    exact hYdiff 1 3
  have hY7 : indψ χ 7 = (ε : ℂ) • (Y 2 - Y 3) := by
    have e : psiFun H χ 7 = thetaOf χ 2 - thetaOf χ 3 := by
      rw [psi7]
      rfl
    show CFSG.TwoRankLowerBound.Helpers.inducedFunction H (psiFun H χ 7) = _
    rw [e]
    exact hYdiff 2 3
  have hεne : (ε : ℂ) ≠ 0 := by rcases hεpm with rfl | rfl <;> norm_num
  have hbYone : ∀ i, BlocksInnerProduct (Y i) (fun _ : G => (1 : ℂ)) =
      if Y i = (fun _ : G => (1 : ℂ)) then 1 else 0 :=
    fun i => bip_irr (hYirr i) one_mem_irr
  have r0 : BlocksInnerProduct (Y 0) (fun _ : G => (1 : ℂ)) =
      BlocksInnerProduct (Y 3) (fun _ : G => (1 : ℂ)) := by
    have h := hbone 5
    rw [hY5, bip_smul_left, bip_sub_left] at h
    rw [show (if (5 : Fin 15) = 0 ∨ (5 : Fin 15) = 10 then (1 : ℂ) else 0) = 0 by simp] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hεne
    · exact sub_eq_zero.mp h'
  have r1 : BlocksInnerProduct (Y 1) (fun _ : G => (1 : ℂ)) =
      BlocksInnerProduct (Y 3) (fun _ : G => (1 : ℂ)) := by
    have h := hbone 6
    rw [hY6, bip_smul_left, bip_sub_left] at h
    rw [show (if (6 : Fin 15) = 0 ∨ (6 : Fin 15) = 10 then (1 : ℂ) else 0) = 0 by simp] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hεne
    · exact sub_eq_zero.mp h'
  have r2 : BlocksInnerProduct (Y 2) (fun _ : G => (1 : ℂ)) =
      BlocksInnerProduct (Y 3) (fun _ : G => (1 : ℂ)) := by
    have h := hbone 7
    rw [hY7, bip_smul_left, bip_sub_left] at h
    rw [show (if (7 : Fin 15) = 0 ∨ (7 : Fin 15) = 10 then (1 : ℂ) else 0) = 0 by simp] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hεne
    · exact sub_eq_zero.mp h'
  have hY1zero : ∀ i, BlocksInnerProduct (Y i) (fun _ : G => (1 : ℂ)) = 0 := by
    have t3 : BlocksInnerProduct (Y 3) (fun _ : G => (1 : ℂ)) = 0 := by
      by_contra hne
      have hY3one : Y 3 = (fun _ : G => (1 : ℂ)) := by
        by_contra hc
        exact hne (by rw [hbYone 3, if_neg hc])
      have hY0one : Y 0 = (fun _ : G => (1 : ℂ)) := by
        by_contra hc
        apply hne
        rw [← r0, hbYone 0, if_neg hc]
      exact (hYinj.ne (by decide : (0 : Fin 4) ≠ 3)) (hY0one.trans hY3one.symm)
    intro i
    fin_cases i
    · exact r0.trans t3
    · exact r1.trans t3
    · exact r2.trans t3
    · exact t3
  have hYne1 : ∀ i, Y i ≠ (fun _ : G => (1 : ℂ)) := fun i h => by
    have := hY1zero i
    rw [h, bip_one] at this
    exact one_ne_zero this
  obtain ⟨V, hVdef⟩ : ∃ V : G → ℂ, V = indψ χ 0 - fun _ => (1 : ℂ) := ⟨_, rfl⟩
  have hVmem : V ∈ BlocksVChar G := by
    rw [hVdef]
    exact (BlocksVChar G).sub_mem (hindv 0) (AddSubgroup.subset_closure one_mem_irr)
  have hVbip : ∀ i, BlocksInnerProduct V (Y i) = BlocksInnerProduct (indψ χ 0) (Y i) := by
    intro i
    have h1i : BlocksInnerProduct (fun _ : G => (1 : ℂ)) (Y i) = 0 := by
      rw [bip_comm, hY1zero i, map_zero]
    rw [hVdef, bip_sub_left, h1i, sub_zero]
  have hb0 : BlocksInnerProduct (indψ χ 0) (fun _ : G => (1 : ℂ)) = 1 := by
    rw [hbone 0]
    simp
  have hb0' : BlocksInnerProduct (fun _ : G => (1 : ℂ)) (indψ χ 0) = 1 := by
    rw [bip_comm, hb0, map_one]
  have hPP : BlocksInnerProduct (indψ χ 0) (indψ χ 0) = 3 := by
    rw [hgram 0 0, show psiGram 0 0 = 3 by decide]
    norm_num
  have hVnorm : BlocksInnerProduct V V = 2 := by
    rw [hVdef, bip_sub_left, bip_sub_right, bip_sub_right, hPP, hb0, hb0', bip_one]
    norm_num
  obtain ⟨A, B, a, b, hAB, ha, hb, hVeq⟩ :=
    CFSG.blocksVChar_norm_two_signed_irreducibles hVmem hVnorm
  obtain ⟨n3, hn3⟩ := blocksInnerProduct_virtual_integer (hindv 0)
    (AddSubgroup.subset_closure (hYirr 3))
  have g05 : (psiGram 0 5 : ℂ) = -1 := by
    rw [show psiGram 0 5 = -1 by decide]
    norm_num
  have g06 : (psiGram 0 6 : ℂ) = -1 := by
    rw [show psiGram 0 6 = -1 by decide]
    norm_num
  have g07 : (psiGram 0 7 : ℂ) = -1 := by
    rw [show psiGram 0 7 = -1 by decide]
    norm_num
  have hr0 : BlocksInnerProduct (indψ χ 0) (Y 0) =
      BlocksInnerProduct (indψ χ 0) (Y 3) + (ε : ℂ) * (-1) := by
    have h := hgram 0 5
    rw [hY5, g05] at h
    exact rel_of_smul (pm_sq hεpm) h
  have hr1 : BlocksInnerProduct (indψ χ 0) (Y 1) =
      BlocksInnerProduct (indψ χ 0) (Y 3) + (ε : ℂ) * (-1) := by
    have h := hgram 0 6
    rw [hY6, g06] at h
    exact rel_of_smul (pm_sq hεpm) h
  have hr2 : BlocksInnerProduct (indψ χ 0) (Y 2) =
      BlocksInnerProduct (indψ χ 0) (Y 3) + (ε : ℂ) * (-1) := by
    have h := hgram 0 7
    rw [hY7, g07] at h
    exact rel_of_smul (pm_sq hεpm) h
  have hn3ε : n3 = ε := by
    by_contra hne
    have hval0 : BlocksInnerProduct V (Y 0) = ((n3 - ε : ℤ) : ℂ) := by
      rw [hVbip 0, hr0, hn3]
      push_cast
      ring
    have hval1 : BlocksInnerProduct V (Y 1) = ((n3 - ε : ℤ) : ℂ) := by
      rw [hVbip 1, hr1, hn3]
      push_cast
      ring
    have hval2 : BlocksInnerProduct V (Y 2) = ((n3 - ε : ℤ) : ℂ) := by
      rw [hVbip 2, hr2, hn3]
      push_cast
      ring
    have hne' : ((n3 - ε : ℤ) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr hne
    have c0 := cover_lemma hVeq A.2 B.2 (hYirr 0) (by rw [hval0]; exact hne')
    have c1 := cover_lemma hVeq A.2 B.2 (hYirr 1) (by rw [hval1]; exact hne')
    have c2 := cover_lemma hVeq A.2 B.2 (hYirr 2) (by rw [hval2]; exact hne')
    exact three_in_two (hYinj.ne (by decide : (0 : Fin 4) ≠ 1))
      (hYinj.ne (by decide : (0 : Fin 4) ≠ 2)) (hYinj.ne (by decide : (1 : Fin 4) ≠ 2))
      (c0.imp Eq.symm Eq.symm) (c1.imp Eq.symm Eq.symm) (c2.imp Eq.symm Eq.symm)
  have hbY3 : BlocksInnerProduct (indψ χ 0) (Y 3) = (ε : ℂ) := by
    rw [hn3, hn3ε]
  have hVY3 : BlocksInnerProduct V (Y 3) = (ε : ℂ) := by
    rw [hVbip 3, hbY3]
  obtain ⟨X₂, hX₂irr, ε₂, hε₂, hX₂ne, hVX⟩ :=
    decompose A.2 B.2 (hYirr 3) (fun h => hAB (Subtype.ext h)) ha hb hεpm hVeq hVY3
  have hPform : indψ χ 0 = (fun _ : G => (1 : ℂ)) + (ε : ℂ) • Y 3 + (ε₂ : ℂ) • X₂ := by
    have hP : indψ χ 0 = V + (fun _ : G => (1 : ℂ)) := by
      rw [hVdef]
      abel
    rw [hP, hVX]
    abel
  have hX₂ne1 : X₂ ≠ (fun _ : G => (1 : ℂ)) := by
    intro h
    have h1 : BlocksInnerProduct V (fun _ : G => (1 : ℂ)) = (ε₂ : ℂ) := by
      rw [hVX, h, bip_add_left, bip_smul_left, bip_smul_left, hY1zero 3, bip_one]
      ring
    have h2 : BlocksInnerProduct V (fun _ : G => (1 : ℂ)) = 0 := by
      rw [hVdef, bip_sub_left, hb0, bip_one, sub_self]
    rw [h2] at h1
    rcases hε₂ with rfl | rfl <;> norm_num at h1
  have hX₂class : BlocksIsClassFunction X₂ := CFSG.SmallDefect.isClassFunction_of_mem hX₂irr
  have hck : ∀ k : Fin 15, ∃ n : ℤ, BlocksInnerProduct (indψ χ k) (Y 3) = (n : ℂ) :=
    fun k => blocksInnerProduct_virtual_integer (hindv k) (AddSubgroup.subset_closure (hYirr 3))
  choose c hc using hck
  have hcε0 : c 0 = ε := by
    have h := hc 0
    rw [hbY3] at h
    exact_mod_cast h.symm
  have b03 : BlocksInnerProduct (Y 0) (Y 3) = 0 := by
    rw [bip_irr (hYirr 0) (hYirr 3), if_neg (hYinj.ne (by decide : (0 : Fin 4) ≠ 3))]
  have b13 : BlocksInnerProduct (Y 1) (Y 3) = 0 := by
    rw [bip_irr (hYirr 1) (hYirr 3), if_neg (hYinj.ne (by decide : (1 : Fin 4) ≠ 3))]
  have b23 : BlocksInnerProduct (Y 2) (Y 3) = 0 := by
    rw [bip_irr (hYirr 2) (hYirr 3), if_neg (hYinj.ne (by decide : (2 : Fin 4) ≠ 3))]
  have b33 : BlocksInnerProduct (Y 3) (Y 3) = 1 := by
    rw [bip_irr (hYirr 3) (hYirr 3), if_pos rfl]
  have hc5 : c 5 = -ε := by
    have h := hc 5
    rw [hY5, bip_smul_left, bip_sub_left, b03, b33] at h
    have h' : ((c 5 : ℤ) : ℂ) = ((-ε : ℤ) : ℂ) := by
      rw [← h]
      push_cast
      ring
    exact_mod_cast h'
  have hc6 : c 6 = -ε := by
    have h := hc 6
    rw [hY6, bip_smul_left, bip_sub_left, b13, b33] at h
    have h' : ((c 6 : ℤ) : ℂ) = ((-ε : ℤ) : ℂ) := by
      rw [← h]
      push_cast
      ring
    exact_mod_cast h'
  have hc7 : c 7 = -ε := by
    have h := hc 7
    rw [hY7, bip_smul_left, bip_sub_left, b23, b33] at h
    have h' : ((c 7 : ℤ) : ℂ) = ((-ε : ℤ) : ℂ) := by
      rw [← h]
      push_cast
      ring
    exact_mod_cast h'
  have hrel0k : ∀ k, BlocksInnerProduct (indψ χ k) (Y 0) =
      BlocksInnerProduct (indψ χ k) (Y 3) + (ε : ℂ) * (psiGram 5 k : ℂ) := by
    intro k
    have h := hgram' k 5
    rw [hY5] at h
    exact rel_of_smul (pm_sq hεpm) h
  have hrel1k : ∀ k, BlocksInnerProduct (indψ χ k) (Y 1) =
      BlocksInnerProduct (indψ χ k) (Y 3) + (ε : ℂ) * (psiGram 6 k : ℂ) := by
    intro k
    have h := hgram' k 6
    rw [hY6] at h
    exact rel_of_smul (pm_sq hεpm) h
  have hrel2k : ∀ k, BlocksInnerProduct (indψ χ k) (Y 2) =
      BlocksInnerProduct (indψ χ k) (Y 3) + (ε : ℂ) * (psiGram 7 k : ℂ) := by
    intro k
    have h := hgram' k 7
    rw [hY7] at h
    exact rel_of_smul (pm_sq hεpm) h
  have hcall : ∀ k : Fin 15, k.val ≠ 0 → k.val ≠ 5 → c k = -(ε * psiGram 5 k) := by
    intro k h0 h5
    by_cases h67 : k.val = 6 ∨ k.val = 7
    · rcases h67 with h6 | h7
      · have hk : k = 6 := Fin.ext h6
        subst hk
        rw [hc6, show psiGram 5 6 = 1 by decide]
        ring
      · have hk : k = 7 := Fin.ext h7
        subst hk
        rw [hc7, show psiGram 5 7 = 1 by decide]
        ring
    · have hk6 : k.val ≠ 6 := fun h => h67 (Or.inl h)
      have hk7 : k.val ≠ 7 := fun h => h67 (Or.inr h)
      obtain ⟨hg6, hg7⟩ := psiGram_six_seven k h0 h5 hk6 hk7
      have key := coeff_claim (f := indψ χ k) (Y := Y) hYirr hYinj (hindv k) (hind1 k) hεpm
        (hgram k k) (psiGram_diag_le k) hg6 hg7 (hc k)
        (by rw [hrel0k k, hc k]) (by rw [hrel1k k, hc k]) (by rw [hrel2k k, hc k])
      linarith
  have hX₂eq : X₂ = (ε₂ : ℂ) • (V - (ε : ℂ) • Y 3) := by
    have h1 : V - (ε : ℂ) • Y 3 = (ε₂ : ℂ) • X₂ := by
      rw [hVX]
      abel
    rw [h1, smul_smul, pm_sq hε₂, one_smul]
  have hXind : ∀ k, BlocksInnerProduct (indψ χ k) X₂ =
      (ε₂ : ℂ) * ((psiGram 0 k : ℂ) - (if k = 0 ∨ k = 10 then 1 else 0) - (ε : ℂ) * (c k : ℂ)) := by
    intro k
    have hVk : BlocksInnerProduct (indψ χ k) V =
        (psiGram 0 k : ℂ) - (if k = 0 ∨ k = 10 then 1 else 0) := by
      rw [hVdef, bip_sub_right, hgram' k 0, hbone k]
    rw [hX₂eq, bip_smul_right, conj_pm, bip_sub_right, bip_smul_right, conj_pm, hVk, hc k]
  have hXk : ∀ k : Fin 15, k.val ≠ 0 → BlocksInnerProduct (indψ χ k) X₂ = 0 := by
    intro k h0
    rw [hXind k]
    have hsq := pm_sq hεpm
    by_cases h5 : k.val = 5
    · have hk : k = 5 := Fin.ext h5
      subst hk
      rw [hc5]
      have e2 : (if (5 : Fin 15) = 0 ∨ (5 : Fin 15) = 10 then (1 : ℂ) else 0) = 0 := by simp
      rw [g05, e2]
      push_cast
      linear_combination (ε₂ : ℂ) * hsq
    · have hcal := hcall k h0 h5
      rw [hcal]
      have hidk := psiGram_identity k h0 h5
      have hidC : (psiGram 0 k : ℂ) - (if k = 0 ∨ k = 10 then 1 else 0) + (psiGram 5 k : ℂ) = 0 := by
        have := congrArg (fun t : ℤ => (t : ℂ)) hidk
        push_cast at this
        exact this
      push_cast
      linear_combination (ε₂ : ℂ) * hidC + (ε₂ : ℂ) * (psiGram 5 k : ℂ) * hsq
  have hXk0 : BlocksInnerProduct (indψ χ 0) X₂ = (ε₂ : ℂ) := by
    rw [hXind 0, hcε0, if_pos (Or.inl rfl)]
    have hsq := pm_sq hεpm
    have g00 : (psiGram 0 0 : ℂ) = 3 := by
      rw [show psiGram 0 0 = 3 by decide]
      norm_num
    rw [g00]
    push_cast
    linear_combination (-(ε₂ : ℂ)) * hsq
  have hψ0χ8 : BlocksInnerProduct (psiFun H χ 0) (χ 8) = -1 := by
    rw [psi0, bip_add_left, bip_sub_left, bip_irr (hirr 0) (hirr 8), bip_irr (hirr 8) (hirr 8),
      bip_irr (hirr 19) (hirr 8), if_neg (hinj.ne (by decide : (0 : Fin 20) ≠ 8)), if_pos rfl,
      if_neg (hinj.ne (by decide : (19 : Fin 20) ≠ 8))]
    ring
  have hfH : ∀ k, BlocksInnerProduct (fun y : H => X₂ y + (ε₂ : ℂ) * χ 8 y) (psiFun H χ k) = 0 := by
    intro k
    have hfun : (fun y : H => X₂ y + (ε₂ : ℂ) * χ 8 y) =
        (fun y : H => X₂ y) + (ε₂ : ℂ) • χ 8 := by
      funext y
      simp
    have hfrob : BlocksInnerProduct (indψ χ k) X₂ =
        BlocksInnerProduct (psiFun H χ k) (fun y : H => X₂ y) :=
      blocksInnerProduct_inducedFunction_left H (psiFun H χ k) X₂ hX₂class
    rw [hfun, bip_add_left, bip_smul_left, bip_comm (fun y : H => X₂ y) (psiFun H χ k),
      ← hfrob, bip_comm (χ 8) (psiFun H χ k)]
    by_cases hk : k = 0
    · subst hk
      rw [hXk0, hψ0χ8, conj_pm, map_neg, map_one]
      ring
    · simp [hXk k (fun h => hk (Fin.ext h)), hχ.chi9_absent k hk]
  have hval2 := val2_of_orth hχ hinv X₂ hX₂class (ε₂ : ℂ) hfH
  have hval1 : ∀ x : H, (x : G) ∈ specialD z H → Y 3 x = (ε : ℂ) * χ 19 x := by
    intro x hx
    have e1 : indψ χ 0 x = psiFun H χ 0 x :=
      CFSG.CharacterTheory.SteinbergBS.inducedFunction_suzuki_apply hcent hfus (hψc 0) (hψz 0) x hx
    have e2 : indψ χ 0 x = 1 + (ε : ℂ) * Y 3 x + (ε₂ : ℂ) * X₂ x := by
      have := congrFun hPform x
      simpa using this
    have e3 : psiFun H χ 0 x = χ 0 x - χ 8 x + χ 19 x := by
      rw [psi0]
      rfl
    have e4 : X₂ x + (ε₂ : ℂ) * χ 8 x = 0 := hval2 x hx
    have e5 : χ 0 x = 1 := hχ.triv x
    have hF : (ε : ℂ) * Y 3 x + (ε₂ : ℂ) * X₂ x + χ 8 x - χ 19 x = 0 := by
      linear_combination -e2 + e1 + e3 + e5
    have hsq := pm_sq hεpm
    have hsq2 := pm_sq hε₂
    linear_combination (ε : ℂ) * hF - (ε : ℂ) * (ε₂ : ℂ) * e4 - (Y 3 x) * hsq +
      (ε : ℂ) * (χ 8 x) * hsq2
  refine ⟨Y 3, X₂, ε, ε₂, ?_⟩
  exact
    { ε₁_pm := hεpm
      ε₂_pm := hε₂
      irr₁ := hYirr 3
      irr₂ := hX₂irr
      ne := fun h => hX₂ne h.symm
      ne_triv₁ := hYne1 3
      ne_triv₂ := hX₂ne1
      ind := hPform
      val₁ := hval1
      val₂ := fun x hx => by linear_combination hval2 x hx }

end CFSG.GH74.QTGen4.Recog.G23.P7.SuzukiCoh

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open scoped Classical in
theorem leafSuzukiCoherence : LeafSuzukiCoherence := by
  intro G _ _ H e χ hD hχ
  exact SuzukiCoh.suzukiCoherent_core hD.cent_le hD.fusion hD.central hχ

end CFSG.GH74.QTGen4.Recog.G23.P7

end
