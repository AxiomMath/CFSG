module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZRootTorus
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.RankThree.Chevalley.SteinbergCFERootSL2Traces
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEInnerRoots
public import CFSG.GH74.GLS.IVK.L2.TorusMatrices

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (exists_conj_lower_eq_zero_of_isAlgClosed
  baseChangeGL_rootSL2_of_field)

section SL2

variable {L : Type} [Field L]

theorem uSL_pow (s : L) (n : ℕ) : uSL s ^ n = uSL ((n : L) * s) := by
  induction n with
  | zero =>
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_uSL]
  | succ n ih =>
    rw [pow_succ, ih]
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_uSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring

theorem HSL_pow (c : Lˣ) (n : ℕ) : HSL c ^ n = HSL (c ^ n) := by
  induction n with
  | zero =>
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_HSL]
  | succ n ih =>
    rw [pow_succ, ih]
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_HSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        pow_succ] <;> ring

theorem HSL_one : HSL (1 : Lˣ) = 1 := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_HSL]

theorem inv_mul_mul_pow_eq {G : Type*} [Group G] (Q A : G) (n : ℕ) :
    (Q⁻¹ * A * Q) ^ n = Q⁻¹ * A ^ n * Q := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; group

theorem HSL_neg_one_mul_comm (g : SL2 L) : HSL (-1) * g = g * HSL (-1) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_HSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_conj_eq_HSL_of_pow_eq_one [IsAlgClosed L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpL : (p : L) ≠ 0) {A : SL2 L} (hAp : A ^ p = 1) (hA1 : A ≠ 1) :
    ∃ (P : SL2 L) (c : Lˣ), c ^ p = 1 ∧ c ≠ 1 ∧ c ^ 2 ≠ 1 ∧ P⁻¹ * A * P = HSL c := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hsq : ∀ c : Lˣ, c ^ p = 1 → c ^ 2 = 1 → c = 1 := by
    intro c h1 h2
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul] at h1
    exact h1
  obtain ⟨Q, hQ⟩ := exists_conj_lower_eq_zero_of_isAlgClosed A
  set M := Q⁻¹ * A * Q with hM
  have hMp : M ^ p = 1 := by rw [hM, inv_mul_mul_pow_eq, hAp, mul_one, inv_mul_cancel]
  have hM1 : M ≠ 1 := fun h => hA1 (by
    have : A = Q * M * Q⁻¹ := by rw [hM]; group
    rw [this, h, mul_one, mul_inv_cancel])
  have hMe := eq_HSL_mul_uSL hQ
  set a : Lˣ := Units.mk0 ((M : Matrix (Fin 2) (Fin 2) L) 0 0) (SL2_apply_zero_zero_ne_zero hQ)
    with ha
  set s : L := (M : Matrix (Fin 2) (Fin 2) L) 0 1 / (M : Matrix (Fin 2) (Fin 2) L) 0 0 with hs
  change M = HSL a * uSL s at hMe
  have ha2 : a ^ 2 ≠ 1 := by
    intro ha2
    have hcomm : Commute (HSL a) (uSL s) := by
      have ha' : a = 1 ∨ a = -1 := by
        have h : ((a : L) - 1) * ((a : L) + 1) = 0 := by
          have := congrArg Units.val ha2
          push_cast at this
          linear_combination this
        rcases mul_eq_zero.1 h with h | h
        · exact Or.inl (Units.ext (by simpa using sub_eq_zero.1 h))
        · exact Or.inr (Units.ext (by simpa using eq_neg_of_add_eq_zero_left h))
      rcases ha' with h1 | h1
      · rw [h1, HSL_one]
        exact Commute.one_left _
      · rw [h1]
        exact HSL_neg_one_mul_comm _
    have h1 := hMp
    rw [hMe, hcomm.mul_pow, HSL_pow, uSL_pow] at h1
    have hap : a ^ p = 1 := by
      have := congrArg (fun g : SL2 L => (g : Matrix (Fin 2) (Fin 2) L) 0 0) h1
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_HSL,
        coe_uSL] at this
      simp at this
      exact Units.ext (by simpa using this)
    have hs0 : s = 0 := by
      rw [hap, HSL_one, one_mul] at h1
      have := congrArg (fun g : SL2 L => (g : Matrix (Fin 2) (Fin 2) L) 0 1) h1
      simp only [coe_uSL, Matrix.SpecialLinearGroup.coe_one] at this
      have hps : (p : L) * s = 0 := by simpa using this
      exact (mul_eq_zero.1 hps).resolve_left hpL
    apply hM1
    rw [hMe, hsq a hap ha2, hs0, HSL_one, one_mul]
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_uSL]
  have hne : (a : L) ≠ ((a⁻¹ : Lˣ) : L) := by
    intro h
    apply ha2
    have h' : a = a⁻¹ := Units.ext h
    rw [sq]
    nth_rw 2 [h']
    exact mul_inv_cancel a
  have htr : (A : Matrix (Fin 2) (Fin 2) L) 0 0 + (A : Matrix (Fin 2) (Fin 2) L) 1 1 =
      (a : L) + ((a⁻¹ : Lˣ) : L) := by
    have h1 : (A : Matrix (Fin 2) (Fin 2) L).trace = (M : Matrix (Fin 2) (Fin 2) L).trace := by
      rw [hM, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
        mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
    rw [Matrix.trace_fin_two, Matrix.trace_fin_two, hMe] at h1
    rw [h1]
    simp [coe_HSL, coe_uSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  obtain ⟨P, hP⟩ := CFSG.GH74.GLS.IVK.L2Torus.exists_conj_mem_diagSub_of_eigenvalue
    (g := A) (a := (a : L)) (b := ((a⁻¹ : Lˣ) : L)) (by simp) hne htr
  obtain ⟨h01, h10⟩ := CFSG.GH74.GLS.IVK.L2Torus.mem_diagSub.1 hP
  set D := P⁻¹ * A * P with hD
  have hDe := eq_HSL_mul_uSL (g := D) h10
  set c : Lˣ := Units.mk0 ((D : Matrix (Fin 2) (Fin 2) L) 0 0) (SL2_apply_zero_zero_ne_zero h10)
    with hc
  have hDc : D = HSL c := by
    rw [hDe]
    have h01' : (D : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := h01
    rw [h01', zero_div]
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_HSL, coe_uSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        hc]
  have hDp : D ^ p = 1 := by rw [hD, inv_mul_mul_pow_eq, hAp, mul_one, inv_mul_cancel]
  have hcp : c ^ p = 1 := by
    rw [hDc, HSL_pow] at hDp
    have := congrArg (fun g : SL2 L => (g : Matrix (Fin 2) (Fin 2) L) 0 0) hDp
    simp [coe_HSL] at this
    exact Units.ext (by simpa using this)
  have hc1 : c ≠ 1 := by
    intro h1
    apply hA1
    have hD1 : D = 1 := by rw [hDc, h1, HSL_one]
    have : A = P * D * P⁻¹ := by rw [hD]; group
    rw [this, hD1, mul_one, mul_inv_cancel]
  exact ⟨P, c, hcp, hc1, fun h2 => hc1 (hsq c hcp h2), hDc⟩

end SL2

variable {τ : Tag}

theorem corootPair_highRoot_single (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (i : Fin τ.rank) :
    2 * iform (highRoot τ) (Pi.single i 1) / iform (highRoot τ) (highRoot τ) =
      if i = highNode τ then 1 else 0 := by
  rcases hτ with rfl | rfl | rfl | rfl <;> revert i <;> decide +kernel

theorem rootTorusSL2_highRoot (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L]
    (c : Lˣ) :
    rootTorusSL2 τ L (highRoot τ) c = rootDiagUnit τ (Pi.mulSingle (highNode τ) c) := by
  rw [CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair
    (isRoot_highRoot τ) c]
  congr 1
  funext i
  rw [corootPair_highRoot_single hτ i]
  split_ifs with h
  · subst h
    rw [Pi.mulSingle_eq_same, zpow_one]
  · rw [Pi.mulSingle_eq_of_ne h, zpow_zero]

theorem centralizer_rootSL2_highRoot_le (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) {A : SL2 K}
    (hAp : A ^ p = 1) (hA1 : A ≠ 1)
    (hC : ∀ c : (AlgebraicClosure K)ˣ, c ≠ 1 → c ^ 2 ≠ 1 →
      toralCentralizer τ (AlgebraicClosure K) (Pi.mulSingle (highNode τ) c) ≤
        toralCentralizer τ (AlgebraicClosure K) (Pi.mulSingle (highNode τ) (-1))) :
    adjointGroup τ K ⊓ Subgroup.centralizer {rootSL2 τ K (highRoot τ) A} ≤
      toralCentralizer τ K (Pi.mulSingle (highNode τ) (-1)) := by
  set L := AlgebraicClosure K
  set f : K →+* L := algebraMap K L with hf
  set ρ := rootSL2 τ L (highRoot τ) with hρ
  have hpL : (p : L) ≠ 0 := by
    rw [← map_natCast f]
    exact (map_ne_zero f).2 hpK
  set A' := Matrix.SpecialLinearGroup.map f A with hA'
  have hA'p : A' ^ p = 1 := by rw [hA', ← map_pow, hAp, map_one]
  have hA'1 : A' ≠ 1 := by
    intro h
    apply hA1
    refine Subtype.ext ?_
    ext i j
    have := congrArg (fun g : SL2 L => (g : Matrix (Fin 2) (Fin 2) L) i j) h
    simp only [hA', Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.SpecialLinearGroup.coe_one] at this
    rw [Matrix.SpecialLinearGroup.coe_one]
    apply f.injective
    rw [this]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  obtain ⟨P, c, -, hc1, hc2, hPc⟩ := exists_conj_eq_HSL_of_pow_eq_one hp hp2 hpL hA'p hA'1
  have hρP : ρ P ∈ adjointGroup τ L :=
    (exceptional_Lang_root_rank_one_data τ L (highRoot τ)).2.2.2.2.1 P
  have htL : rootDiagUnit τ (Pi.mulSingle (highNode τ) (-1 : Lˣ)) = ρ (HSL (-1)) := by
    rw [← rootTorusSL2_highRoot hτ]
    rfl
  have hPt : ρ P * rootDiagUnit τ (Pi.mulSingle (highNode τ) (-1 : Lˣ)) =
      rootDiagUnit τ (Pi.mulSingle (highNode τ) (-1 : Lˣ)) * ρ P := by
    rw [htL, ← map_mul, ← map_mul, HSL_neg_one_mul_comm]
  have hft : baseChangeGL f (rootDiagUnit τ (Pi.mulSingle (highNode τ) (-1 : Kˣ))) =
      rootDiagUnit τ (Pi.mulSingle (highNode τ) (-1 : Lˣ)) := by
    rw [baseChangeGL_rootDiagUnit]
    congr 1
    funext i
    by_cases h : i = highNode τ
    · subst h
      simp
    · simp [Pi.mulSingle_eq_of_ne h]
  intro x hxmem
  obtain ⟨hx, hxr⟩ := Subgroup.mem_inf.1 hxmem
  rw [Subgroup.mem_centralizer_singleton_iff] at hxr
  refine ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  set x' := baseChangeGL f x with hx'
  have hx'L : x' ∈ adjointGroup τ L := baseChangeGL_mem_adjointGroup f hx
  have hA'e : A' = P * HSL c * P⁻¹ := by rw [← hPc]; group
  have hx'r : x' * ρ A' = ρ A' * x' := by
    have h := congrArg (baseChangeGL f) hxr
    rwa [map_mul, map_mul, baseChangeGL_rootSL2_of_field] at h
  set y := (ρ P)⁻¹ * x' * ρ P with hy
  have hyL : y ∈ adjointGroup τ L :=
    mul_mem (mul_mem (inv_mem hρP) hx'L) hρP
  have hyd : y * rootDiagUnit τ (Pi.mulSingle (highNode τ) c) =
      rootDiagUnit τ (Pi.mulSingle (highNode τ) c) * y := by
    rw [← rootTorusSL2_highRoot hτ c]
    change y * ρ (HSL c) = ρ (HSL c) * y
    have e : ρ (HSL c) = (ρ P)⁻¹ * ρ A' * ρ P := by
      rw [hA'e, map_mul, map_mul, map_inv]
      group
    rw [e, hy]
    calc (ρ P)⁻¹ * x' * ρ P * ((ρ P)⁻¹ * ρ A' * ρ P)
        = (ρ P)⁻¹ * (x' * ρ A') * ρ P := by group
      _ = (ρ P)⁻¹ * (ρ A' * x') * ρ P := by rw [hx'r]
      _ = (ρ P)⁻¹ * ρ A' * ρ P * ((ρ P)⁻¹ * x' * ρ P) := by group
  have hyt := Subgroup.mem_centralizer_singleton_iff.1
    (Subgroup.mem_inf.1 (hC c hc1 hc2 (Subgroup.mem_inf.2
      ⟨hyL, Subgroup.mem_centralizer_singleton_iff.2 hyd⟩))).2
  set t := rootDiagUnit τ (Pi.mulSingle (highNode τ) (-1 : Lˣ)) with htdef
  have hx't : x' * t = t * x' := by
    have e : x' = ρ P * y * (ρ P)⁻¹ := by rw [hy]; group
    have hPt' : (ρ P)⁻¹ * t = t * (ρ P)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hPt, mul_assoc, mul_inv_cancel, mul_one]
    calc x' * t = ρ P * y * ((ρ P)⁻¹ * t) := by rw [e]; group
      _ = ρ P * (y * t) * (ρ P)⁻¹ := by rw [hPt']; group
      _ = ρ P * (t * y) * (ρ P)⁻¹ := by rw [hyt]
      _ = (ρ P * t) * y * (ρ P)⁻¹ := by group
      _ = t * x' := by rw [hPt, e]; group
  apply baseChangeGL_injective f
  rw [map_mul, map_mul, hft]
  exact hx't

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
