module

public import CFSG.HardMathSupport.Timmesfeld.Torality.A2Block
public import CFSG.HardMathSupport.Timmesfeld.Torality.CycMonomial
public import CFSG.HardMathSupport.Timmesfeld.Torality.PeelBlockN

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open Matrix MatrixGroups CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE

section SL5

variable {L : Type} [Field L]

abbrev tvSL5 (i j : Fin 5) (hij : i ≠ j) (s : L) : SL(5, L) :=
  Matrix.SpecialLinearGroup.transvection hij s

theorem coe_tvSL5 (i j : Fin 5) (hij : i ≠ j) (s : L) :
    ((tvSL5 i j hij s : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) = 1 + Matrix.single i j s :=
  Matrix.SpecialLinearGroup.transvection_coe hij s

theorem kappa_tvSL5 (i j : Fin 5) (hij : i ≠ j) (hji : j ≠ i) (l m : L) (hl : l ≠ 0)
    (h : (tvSL5 i j hij l * tvSL5 j i hji (-m) * tvSL5 i j hij l) * tvSL5 i j hij l =
      tvSL5 j i hji (-m) * (tvSL5 i j hij l * tvSL5 j i hji (-m) * tvSL5 i j hij l)) :
    l * m = 1 := by
  have h' := congrArg (fun A : SL(5, L) => (A : Matrix (Fin 5) (Fin 5) L) i j) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tvSL5] at h'
  fin_cases i <;> fin_cases j <;> (try exact absurd rfl hij) <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply, Matrix.add_apply,
        Matrix.one_apply] at h'
     rcases h' with h' | h'
     · linear_combination -h'
     · exact absurd h' hl)

@[expose] def wSL5 (i j : Fin 5) (hij : i ≠ j) : SL(5, L) :=
  tvSL5 i j hij 1 * tvSL5 j i hij.symm (-1) * tvSL5 i j hij 1

@[expose] def coxSL5 : SL(5, L) :=
  wSL5 0 1 (by decide) * wSL5 1 2 (by decide) * wSL5 2 3 (by decide) * wSL5 3 4 (by decide)

theorem coe_wSL5_01 : ((wSL5 0 1 (by decide) : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) =
    !![0, 1, 0, 0, 0; -1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1] := by
  ext a b
  simp only [wSL5, Matrix.SpecialLinearGroup.coe_mul, coe_tvSL5]
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply, Matrix.add_apply,
      Matrix.one_apply]

theorem coe_wSL5_12 : ((wSL5 1 2 (by decide) : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) =
    !![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, -1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1] := by
  ext a b
  simp only [wSL5, Matrix.SpecialLinearGroup.coe_mul, coe_tvSL5]
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply, Matrix.add_apply,
      Matrix.one_apply]

theorem coe_wSL5_23 : ((wSL5 2 3 (by decide) : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) =
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, -1, 0, 0; 0, 0, 0, 0, 1] := by
  ext a b
  simp only [wSL5, Matrix.SpecialLinearGroup.coe_mul, coe_tvSL5]
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply, Matrix.add_apply,
      Matrix.one_apply]

theorem coe_wSL5_34 : ((wSL5 3 4 (by decide) : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) =
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, -1, 0] := by
  ext a b
  simp only [wSL5, Matrix.SpecialLinearGroup.coe_mul, coe_tvSL5]
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply, Matrix.add_apply,
      Matrix.one_apply]

theorem coe_coxSL5 :
    ((coxSL5 : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) = cycMat5 ![-1, -1, -1, -1, 1] := by
  simp only [coxSL5, Matrix.SpecialLinearGroup.coe_mul, coe_wSL5_01, coe_wSL5_12, coe_wSL5_23,
    coe_wSL5_34]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [cycMat5, Matrix.mul_apply, Fin.sum_univ_five]

end SL5

section Core


variable {τ : Tag} {L : Type} [Field L]

theorem mono_of_transv {G : Type*} [Group G] (ρ : G →* ModGL τ L) (hρ : Function.Injective ρ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (X Y : L → G) {a b : Lˣ}
    (hX : ∀ s, ρ (X s) = pinnedX τ L α ((a : L) * s))
    (hY : ∀ t, ρ (Y t) = pinnedX τ L (-α) ((b : L) * t))
    (hkappa : ∀ l m : L, l ≠ 0 →
      (X l * Y (-m) * X l) * X l = Y (-m) * (X l * Y (-m) * X l) → l * m = 1) :
    ∃ hm : ρ (X 1 * Y (-1) * X 1) ∈ monomialSubgroup τ L,
      weylQuotientHom τ L ⟨ρ (X 1 * Y (-1) * X 1), hm⟩ = rootReflection α := by
  obtain ⟨ε₂, hε₂, hv⟩ := exists_rootSL2_vSL_eq (K := L) hα
  have hu := rootSL2_uSL_eq (τ := τ) (K := L) (β := α)
  obtain ⟨ε₁, hε₁, hε₁'⟩ : ∃ ε₁ : L, ε₁ * ε₁ = 1 ∧ ∀ z : L,
      rootSL2 τ L α (uSL z) = pinnedX τ L α (ε₁ * z) := by
    refine ⟨(((pinnedData τ α).2.2 : ℤ) : L), ?_, fun z => ?_⟩
    · rcases pinnedSign_eq τ α with h | h <;> rw [h] <;> simp
    · rw [hu, zsmul_eq_mul]
  set l : L := ε₁ * ((a⁻¹ : Lˣ) : L) with hl
  set m : L := ε₂ * ((b⁻¹ : Lˣ) : L) with hm
  have hau : (a : L) * ((a⁻¹ : Lˣ) : L) = 1 := by simp
  have hbu : (b : L) * ((b⁻¹ : Lˣ) : L) = 1 := by simp
  have hRu : ∀ z : L, rootSL2 τ L α (uSL z) = ρ (X (l * z)) := by
    intro z
    rw [hε₁', hX]
    congr 1
    calc ε₁ * z = ((a : L) * ((a⁻¹ : Lˣ) : L)) * (ε₁ * z) := by rw [hau, one_mul]
      _ = (a : L) * (l * z) := by rw [hl]; ring
  have hRv : ∀ z : L, rootSL2 τ L α (vSL z) = ρ (Y (m * z)) := by
    intro z
    rw [hv, hY]
    congr 1
    calc ε₂ * z = ((b : L) * ((b⁻¹ : Lˣ) : L)) * (ε₂ * z) := by rw [hbu, one_mul]
      _ = (b : L) * (m * z) := by rw [hm]; ring
  have hl0 : l ≠ 0 := by
    have hε₁0 : ε₁ ≠ 0 := fun h0 => by rw [h0, zero_mul] at hε₁; exact zero_ne_one hε₁
    exact mul_ne_zero hε₁0 (a⁻¹).ne_zero
  have hrel : (X l * Y (-m) * X l) * X l = Y (-m) * (X l * Y (-m) * X l) := by
    apply hρ
    have h1 := congrArg (rootSL2 τ L α) (WSL_mul_uSL_one (K := L))
    rw [WSL_eq_uSL_vSL_uSL' (K := L)] at h1
    simp only [map_mul, hRu, hRv, mul_one, mul_neg] at h1
    simp only [map_mul]
    exact h1
  have hlm : l * m = 1 := hkappa l m hl0 hrel
  have hm_eq : m = l⁻¹ := eq_inv_of_mul_eq_one_right hlm
  set c : Lˣ := Units.mk0 l⁻¹ (inv_ne_zero hl0) with hc
  have hw : ρ (X 1 * Y (-1) * X 1) = rootWeylSL2 τ L α c := by
    have e1 : ρ (X 1) = rootSL2 τ L α (uSL (c : L)) := by
      rw [hRu]
      congr 2
      simp [hc, hl0]
    have e2 : ρ (Y (-1)) = rootSL2 τ L α (vSL (-((c⁻¹ : Lˣ) : L))) := by
      rw [hRv]
      congr 2
      simp [hc, hm_eq, hl0]
    rw [map_mul, map_mul, e1, e2, rootWeylSL2, ← map_mul, ← map_mul, ← nSL_eq_uSL_vSL_uSL]
  obtain ⟨h, hq⟩ := (exceptional_Lang_root_rank_one_torus_transport τ L hα).2.2.1 c
  refine ⟨by rw [hw]; exact h, ?_⟩
  have e : (⟨ρ (X 1 * Y (-1) * X 1), by rw [hw]; exact h⟩ : monomialSubgroup τ L) =
      ⟨rootWeylSL2 τ L α c, h⟩ := Subtype.ext hw
  rw [e]
  exact hq

end Core


theorem natCast_ne_zero_of_ringChar_ne {L : Type} [Field L] {p : ℕ} (hp : p.Prime)
    (h : ringChar L ≠ p) : (p : L) ≠ 0 := by
  intro h0
  have h1 : ringChar L ∣ p := (CharP.cast_eq_zero_iff L (ringChar L) p).1 h0
  rcases CharP.char_is_prime_or_zero L (ringChar L) with hq | hq
  · exact h ((Nat.prime_dvd_prime_iff_eq hq hp).1 h1)
  · rw [hq] at h1
    exact absurd (Nat.eq_zero_of_zero_dvd h1) hp.ne_zero

section Frame

variable {τ : Tag} {L : Type} [Field L]

@[expose] def frameRoots5 (σ : Fin 5 → Fin 5 → Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {r | ∃ i j : Fin 5, i ≠ j ∧ r = σ i j}

structure IsA4Frame (ρ : SL(5, L) →* ModGL τ L) (σ : Fin 5 → Fin 5 → Fin τ.rank → ℤ) : Prop where
  injective : Function.Injective ρ
  isRoot : ∀ i j, i ≠ j → IsRoot τ (σ i j)
  neg : ∀ i j, σ j i = -σ i j
  add : ∀ i j k, σ i j + σ j k = σ i k
  transv : ∀ (i j : Fin 5) (hij : i ≠ j), ∃ ε : Lˣ, ∀ t : L,
    ρ (Matrix.SpecialLinearGroup.transvection hij t) = pinnedX τ L (σ i j) ((ε : L) * t)
  range : ρ.range = rootSpan τ L (frameRoots5 σ)
  torus : ∀ b : Fin τ.rank → Lˣ, ∃ d : Fin 5 → Lˣ, ∀ A : SL(5, L),
    rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ (conjDiagn d A)
  diag : ∀ A : SL(5, L), (∀ i j, i ≠ j → (A : Matrix (Fin 5) (Fin 5) L) i j = 0) →
    ρ A ∈ torusGroup τ L

end Frame

section Block


variable {τ : Tag} {L : Type} [Field L]

theorem frame_wSL5 {ρ : SL(5, L) →* ModGL τ L} {σ : Fin 5 → Fin 5 → Fin τ.rank → ℤ}
    (hfr : IsA4Frame ρ σ) (i j : Fin 5) (hij : i ≠ j) :
    ∃ hm : ρ (wSL5 i j hij) ∈ monomialSubgroup τ L,
      weylQuotientHom τ L ⟨ρ (wSL5 i j hij), hm⟩ = rootReflection (σ i j) := by
  have hji : j ≠ i := hij.symm
  obtain ⟨a, ha⟩ := hfr.transv i j hij
  obtain ⟨b, hb⟩ := hfr.transv j i hji
  rw [hfr.neg i j] at hb
  exact mono_of_transv ρ hfr.injective (hfr.isRoot i j hij) (tvSL5 i j hij) (tvSL5 j i hji)
    ha hb fun l m hl h => kappa_tvSL5 i j hij hji l m hl h

theorem a4BlockAt_of_frame [IsAlgClosed L] (hL : ringChar L ≠ 5)
    {ρ : SL(5, L) →* ModGL τ L} {σ : Fin 5 → Fin 5 → Fin τ.rank → ℤ} (hfr : IsA4Frame ρ σ) :
    ∃ m ∈ rootSpan τ L (frameRoots5 σ), ∃ hm : m ∈ monomialSubgroup τ L,
      weylQuotientHom τ L ⟨m, hm⟩ = rootReflection (σ 0 1) * rootReflection (σ 1 2) *
        rootReflection (σ 2 3) * rootReflection (σ 3 4) ∧
      ∀ t ∈ torusGroup τ L, ∃ y ∈ rootSpan τ L (frameRoots5 σ), y * (m * t) * y⁻¹ ∈
        torusGroup τ L := by
  obtain ⟨hm01, hq01⟩ := frame_wSL5 hfr 0 1 (by decide)
  obtain ⟨hm12, hq12⟩ := frame_wSL5 hfr 1 2 (by decide)
  obtain ⟨hm23, hq23⟩ := frame_wSL5 hfr 2 3 (by decide)
  obtain ⟨hm34, hq34⟩ := frame_wSL5 hfr 3 4 (by decide)
  have M01 : MapsRootLines (ρ (wSL5 0 1 (by decide))) (rootReflection (σ 0 1)) := by
    have := mapsRootLines_weylQuotientHom (τ := τ) (R := L) ⟨_, hm01⟩
    rwa [hq01] at this
  have M12 : MapsRootLines (ρ (wSL5 1 2 (by decide))) (rootReflection (σ 1 2)) := by
    have := mapsRootLines_weylQuotientHom (τ := τ) (R := L) ⟨_, hm12⟩
    rwa [hq12] at this
  have M23 : MapsRootLines (ρ (wSL5 2 3 (by decide))) (rootReflection (σ 2 3)) := by
    have := mapsRootLines_weylQuotientHom (τ := τ) (R := L) ⟨_, hm23⟩
    rwa [hq23] at this
  have M34 : MapsRootLines (ρ (wSL5 3 4 (by decide))) (rootReflection (σ 3 4)) := by
    have := mapsRootLines_weylQuotientHom (τ := τ) (R := L) ⟨_, hm34⟩
    rwa [hq34] at this
  have hcox : ρ coxSL5 = ρ (wSL5 0 1 (by decide)) * ρ (wSL5 1 2 (by decide)) *
      ρ (wSL5 2 3 (by decide)) * ρ (wSL5 3 4 (by decide)) := by
    simp only [coxSL5, map_mul]
  have hmono : ρ coxSL5 ∈ monomialSubgroup τ L := by
    rw [hcox]
    exact mul_mem (mul_mem (mul_mem hm01 hm12) hm23) hm34
  refine ⟨ρ coxSL5, ?_, hmono, ?_, ?_⟩
  · rw [← hfr.range]
    exact ⟨coxSL5, rfl⟩
  · refine weylQuotientHom_eq (g := ⟨ρ coxSL5, hmono⟩) ?_
    have := ((M01.mul M12).mul M23).mul M34
    simpa only [hcox] using this
  · intro t ht
    have : NeZero ((5 : ℕ) : L) :=
      ⟨by exact_mod_cast natCast_ne_zero_of_ringChar_ne Nat.prime_five hL⟩
    obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 5
    have hconj : ∀ (d' : Fin 5 → Lˣ) (hd' : ∏ i, (d' i : L) = 1), ∃ g : SL(5, L), ∀ i j, i ≠ j →
        ((g⁻¹ * (coxSL5 * diagSLn d' hd') * g : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) i j = 0 := by
      intro d' hd'
      have hm : ((coxSL5 * diagSLn d' hd' : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) =
          cycMat5 (fun j => (![-1, -1, -1, -1, 1] : Fin 5 → L) j * (d' j : L)) := by
        rw [Matrix.SpecialLinearGroup.coe_mul, coe_coxSL5, coe_diagSLn, cycMat5_mul_diagonal]
      have hprod : (![-1, -1, -1, -1, 1] : Fin 5 → L) 0 * (d' 0 : L) *
          ((![-1, -1, -1, -1, 1] : Fin 5 → L) 1 * (d' 1 : L)) *
          ((![-1, -1, -1, -1, 1] : Fin 5 → L) 2 * (d' 2 : L)) *
          ((![-1, -1, -1, -1, 1] : Fin 5 → L) 3 * (d' 3 : L)) *
          ((![-1, -1, -1, -1, 1] : Fin 5 → L) 4 * (d' 4 : L)) = 1 := by
        simp only [Fin.prod_univ_five] at hd'
        simp
        linear_combination hd'
      obtain ⟨g, d, hg⟩ := exists_sl5_conj_diagonal_cyc hω hprod _ hm
      refine ⟨g, fun i j hij => ?_⟩
      rw [hg]
      simp [hij]
    obtain ⟨g, h, hh, t₁, ht₁, -, he⟩ := peel_block_gen (by norm_num) ρ hfr.torus hfr.diag coxSL5
      hconj ht (u := 1) (fun A => by simp)
    refine ⟨ρ g, ?_, ?_⟩
    · rw [← hfr.range]
      exact ⟨g, rfl⟩
    · rw [mul_one] at he
      rw [he]
      simpa using mul_mem hh ht₁

end Block

end CFSG.HardMathSupport.Timmesfeld.Torality
