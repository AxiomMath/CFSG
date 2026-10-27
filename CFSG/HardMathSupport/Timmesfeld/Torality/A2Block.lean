module

public import CFSG.HardMathSupport.Timmesfeld.Torality.PeelBlock
public import CFSG.RankThree.PartOne.KF4.A2Frame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeyl

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open Matrix MatrixGroups CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4 CFSG.HardMathSupport.Timmesfeld.CrossChar

section SL3

variable {L : Type} [Field L]

abbrev tvSL (i j : Fin 3) (hij : i ≠ j) (s : L) : SL(3, L) :=
  Matrix.SpecialLinearGroup.transvection hij s

theorem coe_tvSL (i j : Fin 3) (hij : i ≠ j) (s : L) :
    ((tvSL i j hij s : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = 1 + Matrix.single i j s :=
  Matrix.SpecialLinearGroup.transvection_coe hij s

theorem kappa_tvSL (i j : Fin 3) (hij : i ≠ j) (hji : j ≠ i) (l m : L) (hl : l ≠ 0)
    (h : (tvSL i j hij l * tvSL j i hji (-m) * tvSL i j hij l) * tvSL i j hij l =
      tvSL j i hji (-m) * (tvSL i j hij l * tvSL j i hji (-m) * tvSL i j hij l)) :
    l * m = 1 := by
  have h' := congrArg (fun A : SL(3, L) => (A : Matrix (Fin 3) (Fin 3) L) i j) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tvSL] at h'
  fin_cases i <;> fin_cases j <;> (try exact absurd rfl hij) <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.add_apply,
        Matrix.one_apply] at h'
     rcases h' with h' | h'
     · linear_combination -h'
     · exact absurd h' hl)

@[expose] def wSL3 (i j : Fin 3) (hij : i ≠ j) : SL(3, L) :=
  tvSL i j hij 1 * tvSL j i hij.symm (-1) * tvSL i j hij 1

@[expose] def coxSL3 : SL(3, L) :=
  wSL3 0 1 (by decide) * wSL3 1 2 (by decide)

theorem coe_coxSL3 :
    ((coxSL3 : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = monoM₁ (-1) (-1) 1 := by
  ext a b
  simp only [coxSL3, wSL3, Matrix.SpecialLinearGroup.coe_mul, coe_tvSL]
  fin_cases a <;> fin_cases b <;>
    simp [monoM₁, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.add_apply,
      Matrix.one_apply]

end SL3

section SL2

variable {K : Type} [Field K]

theorem nSL_eq_uSL_vSL_uSL (c : Kˣ) :
    nSL c = uSL (c : K) * vSL (-((c⁻¹ : Kˣ) : K)) * uSL (c : K) := by
  have hc : (c : K) ≠ 0 := c.ne_zero
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [nSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_uSL,
      coe_vSL, hc]

theorem WSL_mul_uSL_one : (WSL : SL2 K) * uSL 1 = vSL (-1) * WSL := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_uSL, coe_vSL,
      coe_WSL]

theorem WSL_eq_uSL_vSL_uSL' : (WSL : SL2 K) = uSL 1 * vSL (-1) * uSL 1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_uSL, coe_vSL,
      coe_WSL]

end SL2

theorem three_ne_zero_of_ringChar_ne_three {L : Type} [Field L] (h : ringChar L ≠ 3) :
    (3 : L) ≠ 0 := by
  intro h0
  have h1 : ringChar L ∣ 3 := (CharP.cast_eq_zero_iff L (ringChar L) 3).1 (by exact_mod_cast h0)
  rcases CharP.char_is_prime_or_zero L (ringChar L) with hp | hp
  · exact h ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h1)
  · rw [hp] at h1
    exact absurd (Nat.eq_zero_of_zero_dvd h1) (by norm_num)

section Frame


variable {τ : Tag} {L : Type} [Field L]

theorem frame_wSL3 {ρ : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    (hfr : IsA2Frame ρ σ) (i j : Fin 3) (hij : i ≠ j) :
    ∃ hm : ρ (wSL3 i j hij) ∈ monomialSubgroup τ L,
      weylQuotientHom τ L ⟨ρ (wSL3 i j hij), hm⟩ = rootReflection (σ i j) := by
  have hji : j ≠ i := hij.symm
  obtain ⟨a, ha⟩ := hfr.transv i j hij
  obtain ⟨b, hb⟩ := hfr.transv j i hji
  have hα := hfr.isRoot i j hij
  rw [hfr.neg i j] at hb
  obtain ⟨ε₂, hε₂, hv⟩ := exists_rootSL2_vSL_eq (K := L) hα
  have hu := rootSL2_uSL_eq (τ := τ) (K := L) (β := σ i j)
  obtain ⟨ε₁, hε₁, hε₁'⟩ : ∃ ε₁ : L, ε₁ * ε₁ = 1 ∧ ∀ z : L,
      rootSL2 τ L (σ i j) (uSL z) = pinnedX τ L (σ i j) (ε₁ * z) := by
    refine ⟨(((pinnedData τ (σ i j)).2.2 : ℤ) : L), ?_, fun z => ?_⟩
    · rcases pinnedSign_eq τ (σ i j) with h | h <;> rw [h] <;> simp
    · rw [hu, zsmul_eq_mul]
  set l : L := ε₁ * ((a⁻¹ : Lˣ) : L) with hl
  set m : L := ε₂ * ((b⁻¹ : Lˣ) : L) with hm
  have hau : (a : L) * ((a⁻¹ : Lˣ) : L) = 1 := by simp
  have hbu : (b : L) * ((b⁻¹ : Lˣ) : L) = 1 := by simp
  have hRu : ∀ z : L, rootSL2 τ L (σ i j) (uSL z) = ρ (tvSL i j hij (l * z)) := by
    intro z
    rw [hε₁', ha]
    congr 1
    calc ε₁ * z = ((a : L) * ((a⁻¹ : Lˣ) : L)) * (ε₁ * z) := by rw [hau, one_mul]
      _ = (a : L) * (l * z) := by rw [hl]; ring
  have hRv : ∀ z : L, rootSL2 τ L (σ i j) (vSL z) = ρ (tvSL j i hji (m * z)) := by
    intro z
    rw [hv, hb]
    congr 1
    calc ε₂ * z = ((b : L) * ((b⁻¹ : Lˣ) : L)) * (ε₂ * z) := by rw [hbu, one_mul]
      _ = (b : L) * (m * z) := by rw [hm]; ring
  have hl0 : l ≠ 0 := by
    have hε₁0 : ε₁ ≠ 0 := fun h0 => by rw [h0, zero_mul] at hε₁; exact zero_ne_one hε₁
    exact mul_ne_zero hε₁0 (a⁻¹).ne_zero
  have hrel : (tvSL i j hij l * tvSL j i hji (-m) * tvSL i j hij l) * tvSL i j hij l =
      tvSL j i hji (-m) * (tvSL i j hij l * tvSL j i hji (-m) * tvSL i j hij l) := by
    apply hfr.injective
    have h1 := congrArg (rootSL2 τ L (σ i j)) (WSL_mul_uSL_one (K := L))
    rw [WSL_eq_uSL_vSL_uSL' (K := L)] at h1
    simp only [map_mul, hRu, hRv, mul_one, mul_neg] at h1
    simp only [map_mul]
    exact h1
  have hlm : l * m = 1 := kappa_tvSL i j hij hji l m hl0 hrel
  have hm_eq : m = l⁻¹ := eq_inv_of_mul_eq_one_right hlm
  set c : Lˣ := Units.mk0 l⁻¹ (inv_ne_zero hl0) with hc
  have hw : ρ (wSL3 i j hij) = rootWeylSL2 τ L (σ i j) c := by
    have e1 : ρ (tvSL i j hij 1) = rootSL2 τ L (σ i j) (uSL (c : L)) := by
      rw [hRu]
      congr 2
      simp [hc, hl0]
    have e2 : ρ (tvSL j i hji (-1)) =
        rootSL2 τ L (σ i j) (vSL (-((c⁻¹ : Lˣ) : L))) := by
      rw [hRv]
      congr 2
      simp [hc, hm_eq, hl0]
    rw [wSL3, map_mul, map_mul, e1, e2, rootWeylSL2, ← map_mul, ← map_mul,
      ← nSL_eq_uSL_vSL_uSL]
  obtain ⟨h, hq⟩ := (exceptional_Lang_root_rank_one_torus_transport τ L hα).2.2.1 c
  refine ⟨by rw [hw]; exact h, ?_⟩
  have e : (⟨ρ (wSL3 i j hij), by rw [hw]; exact h⟩ : monomialSubgroup τ L) =
      ⟨rootWeylSL2 τ L (σ i j) c, h⟩ := Subtype.ext hw
  rw [e]
  exact hq

theorem a2BlockAt_of_frame [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {ρ : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hfr : IsA2Frame ρ σ) :
    ∃ m ∈ rootSpan τ L (a2Roots (σ 0 1) (σ 1 2)), ∃ hm : m ∈ monomialSubgroup τ L,
      weylQuotientHom τ L ⟨m, hm⟩ = rootReflection (σ 0 1) * rootReflection (σ 1 2) ∧
      ∀ t ∈ torusGroup τ L, ∃ y ∈ rootSpan τ L (a2Roots (σ 0 1) (σ 1 2)),
        y * (m * t) * y⁻¹ ∈ torusGroup τ L := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have e02 : σ 0 2 = σ 0 1 + σ 1 2 := (hfr.add 0 1 2).symm
  have e10 : σ 1 0 = -σ 0 1 := hfr.neg 0 1
  have e21 : σ 2 1 = -σ 1 2 := hfr.neg 1 2
  have e20 : σ 2 0 = -σ 0 2 := hfr.neg 0 2
  have hspan : rootSpan τ L (a2Roots (σ 0 1) (σ 1 2)) = ρ.range := by
    rw [hfr.range]
    congr 1
    ext r
    simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact ⟨0, 1, by decide, rfl⟩
      · exact ⟨1, 0, by decide, e10.symm⟩
      · exact ⟨1, 2, by decide, rfl⟩
      · exact ⟨2, 1, by decide, e21.symm⟩
      · exact ⟨0, 2, by decide, e02.symm⟩
      · exact ⟨2, 0, by decide, by rw [e20, e02]⟩
    · rintro ⟨i, j, hij, rfl⟩
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | simp [e02, e10, e21, e20]
  obtain ⟨hm01, hq01⟩ := frame_wSL3 hfr 0 1 h01
  obtain ⟨hm12, hq12⟩ := frame_wSL3 hfr 1 2 h12
  have M1 : MapsRootLines (ρ (wSL3 0 1 h01)) (rootReflection (σ 0 1)) := by
    have := mapsRootLines_weylQuotientHom (τ := τ) (R := L) ⟨_, hm01⟩
    rwa [hq01] at this
  have M2 : MapsRootLines (ρ (wSL3 1 2 h12)) (rootReflection (σ 1 2)) := by
    have := mapsRootLines_weylQuotientHom (τ := τ) (R := L) ⟨_, hm12⟩
    rwa [hq12] at this
  refine ⟨ρ (wSL3 0 1 h01) * ρ (wSL3 1 2 h12), ?_, mul_mem hm01 hm12, ?_, ?_⟩
  · rw [hspan]
    exact ⟨wSL3 0 1 h01 * wSL3 1 2 h12, map_mul ρ _ _⟩
  · exact weylQuotientHom_eq (M1.mul M2)
  · intro t ht
    have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial L).degree = 2 := by
      compute_degree!
    obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial L)
      (by rw [hdeg]; norm_num)
    have hω' : ω ^ 2 + ω + 1 = 0 := by simpa [Polynomial.IsRoot, Polynomial.eval_add] using hω
    have hcox : ρ (wSL3 0 1 h01) * ρ (wSL3 1 2 h12) = ρ coxSL3 := (map_mul ρ _ _).symm
    obtain ⟨g, h, hh, t₁, ht₁, -, he⟩ := peel_block hω' (three_ne_zero_of_ringChar_ne_three hL) ρ
      (fun b => ⟨fun i => rootChar b (σ i 0), fun A => hfr.torus b A⟩) hfr.diag
      (a := -1) (b := -1) (c := 1) (by norm_num) coxSL3 (Or.inl coe_coxSL3) (t := t) (u := 1) ht
      (fun A => by simp)
    refine ⟨ρ g, ?_, ?_⟩
    · rw [hspan]
      exact ⟨g, rfl⟩
    · rw [hcox]
      rw [mul_one] at he
      rw [he]
      simpa using mul_mem hh ht₁

end Frame

end CFSG.HardMathSupport.Timmesfeld.Torality
