module

public import CFSG.Fischer.Classification.PartII.Herm.Classify
public import CFSG.LieType.Universal.Unitary.Hermitian
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField
public import TauCeti.LinearAlgebra.Matrix.CrossProduct

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open Module Matrix

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] noncomputable def wedge3 (a b c : V) : ⋀[K]^3 V :=
  exteriorPower.ιMulti (R := K) (M := V) 3 ![a, b, c]

theorem wedge3_map (f : V →ₗ[K] V) (a b c : V) :
    exteriorPower.map 3 f (wedge3 (K := K) a b c) = wedge3 (K := K) (f a) (f b) (f c) := by
  rw [wedge3, wedge3, exteriorPower.map_apply_ιMulti (R := K) (M := V)]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem wedge3_add_first (a a' b c : V) :
    wedge3 (K := K) (a + a') b c = wedge3 (K := K) a b c + wedge3 (K := K) a' b c := by
  rw [wedge3, wedge3, wedge3]
  have h : (![a + a', b, c] : Fin 3 → V) = Function.update ![a, b, c] 0 (a + a') := by
    funext i
    fin_cases i <;> simp
  have h' := (exteriorPower.ιMulti (R := K) (M := V) 3).map_update_add
    (![a, b, c] : Fin 3 → V) 0 a a'
  have h1 : Function.update ![a, b, c] 0 a = ![a, b, c] := by
    funext i
    fin_cases i <;> simp
  have h2 : Function.update ![a, b, c] 0 a' = ![a', b, c] := by
    funext i
    fin_cases i <;> simp
  rw [h1, h2] at h'
  simpa [h] using h'

theorem wedge3_add_second (a b b' c : V) :
    wedge3 (K := K) a (b + b') c = wedge3 (K := K) a b c + wedge3 (K := K) a b' c := by
  rw [wedge3, wedge3, wedge3]
  have h : (![a, b + b', c] : Fin 3 → V) = Function.update ![a, b, c] 1 (b + b') := by
    funext i
    fin_cases i <;> simp
  have h' := (exteriorPower.ιMulti (R := K) (M := V) 3).map_update_add
    (![a, b, c] : Fin 3 → V) 1 b b'
  have h1 : Function.update ![a, b, c] 1 b = ![a, b, c] := by
    funext i
    fin_cases i <;> simp
  have h2 : Function.update ![a, b, c] 1 b' = ![a, b', c] := by
    funext i
    fin_cases i <;> simp
  rw [h1, h2] at h'
  simpa [h] using h'

theorem wedge3_add_third (a b c c' : V) :
    wedge3 (K := K) a b (c + c') = wedge3 (K := K) a b c + wedge3 (K := K) a b c' := by
  rw [wedge3, wedge3, wedge3]
  have h : (![a, b, c + c'] : Fin 3 → V) = Function.update ![a, b, c] 2 (c + c') := by
    funext i
    fin_cases i <;> simp
  have h' := (exteriorPower.ιMulti (R := K) (M := V) 3).map_update_add
    (![a, b, c] : Fin 3 → V) 2 c c'
  have h1 : Function.update ![a, b, c] 2 c = ![a, b, c] := by
    funext i
    fin_cases i <;> simp
  have h2 : Function.update ![a, b, c] 2 c' = ![a, b, c'] := by
    funext i
    fin_cases i <;> simp
  rw [h1, h2] at h'
  simpa [h] using h'

theorem wedge3_eq_zero_of_eq {a b c : V} (h : a = b ∨ a = c ∨ b = c) :
    wedge3 (K := K) a b c = 0 := by
  rw [wedge3]
  rcases h with h | h | h
  · subst h
    exact (exteriorPower.ιMulti (R := K) (M := V) 3).map_eq_zero_of_eq (v := ![a, a, c])
      (i := 0) (j := 1) (by simp) (by decide)
  · subst h
    exact (exteriorPower.ιMulti (R := K) (M := V) 3).map_eq_zero_of_eq (v := ![a, b, a])
      (i := 0) (j := 2) (by simp) (by decide)
  · subst h
    exact (exteriorPower.ιMulti (R := K) (M := V) 3).map_eq_zero_of_eq (v := ![a, b, b])
      (i := 1) (j := 2) (by simp) (by decide)

theorem exteriorPower.ιMulti_ne_zero_of_linearIndependent
    [FiniteDimensional K V] {v : Fin 3 → V} (h : LinearIndependent K v) :
    exteriorPower.ιMulti (R := K) (M := V) 3 v ≠ 0 := by
  have hinj : LinearMap.ker (Fintype.linearCombination K v) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (LinearIndependent.fintypeLinearCombination_injective h)
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  have hφv : ∀ j, φ (v j) = Pi.single j 1 := by
    intro j
    have := LinearMap.congr_fun hφ (Pi.single j 1)
    simpa [Fintype.linearCombination_apply_single] using this
  let Λ : V [⋀^Fin 3]→ₗ[K] K :=
    (Matrix.detRowAlternating : (Fin 3 → K) [⋀^Fin 3]→ₗ[K] K).compLinearMap φ
  intro h0
  have h1 : (exteriorPower.alternatingMapLinearEquiv Λ) (exteriorPower.ιMulti (R := K) (M := V) 3 v) = Λ v :=
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti Λ v
  rw [h0, map_zero] at h1
  have h2 : Λ v = 1 := by
    show Matrix.det (Matrix.of fun j => φ (v j)) = 1
    have : (Matrix.of fun j => φ (v j)) = (1 : Matrix (Fin 3) (Fin 3) K) := by
      ext j i
      rw [Matrix.of_apply, hφv j, Pi.single_apply, Matrix.one_apply]
      simp [eq_comm]
    rw [this, Matrix.det_one]
  rw [h2] at h1
  exact one_ne_zero h1.symm

theorem wedge3_ne_zero_of_linearIndependent [FiniteDimensional K V] {a b c : V}
    (h : LinearIndependent K ![a, b, c]) : wedge3 (K := K) a b c ≠ 0 :=
  exteriorPower.ιMulti_ne_zero_of_linearIndependent h


theorem sub_one_mul_sub_one_eq_zero_of_exteriorPower_three {K V : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {x y : V →ₗ[K] V} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    (hq : (exteriorPower.map 3 x - 1) * (exteriorPower.map 3 y - 1) = 0) :
    (x - 1) * (y - 1) = 0 := by
  classical
  let N : V →ₗ[K] V := x - 1
  let M : V →ₗ[K] V := y - 1
  have hxN : x = 1 + N := by
    ext v
    simp [N]
  have hyM : y = 1 + M := by
    ext v
    simp [M]
  have hN2_apply : ∀ v, N (N v) = 0 := by
    intro v
    have hx_eval : x (x v) = v := by
      have h := congrArg (fun f : Module.End K V => f v) hx
      simpa [Module.End.mul_apply] using h
    have h2v : v + v = 0 := by
      rw [← two_nsmul v, ← Nat.cast_smul_eq_nsmul (R := K) 2 v, CharP.cast_eq_zero K 2, zero_smul]
    have h2xv : x v + x v = 0 := by
      rw [← two_nsmul (x v), ← Nat.cast_smul_eq_nsmul (R := K) 2 (x v), CharP.cast_eq_zero K 2,
        zero_smul]
    calc N (N v) = x (x v - v) - (x v - v) := by
          simp [N, LinearMap.sub_apply]
      _ = (x (x v) - x v) - (x v - v) := by rw [map_sub]
      _ = (v - x v) - (x v - v) := by rw [hx_eval]
      _ = (v + v) - (x v + x v) := by abel
      _ = 0 := by rw [h2v, h2xv, sub_self]
  have hM2_apply : ∀ v, M (M v) = 0 := by
    intro v
    have hy_eval : y (y v) = v := by
      have h := congrArg (fun f : Module.End K V => f v) hy
      simpa [Module.End.mul_apply] using h
    have h2v : v + v = 0 := by
      rw [← two_nsmul v, ← Nat.cast_smul_eq_nsmul (R := K) 2 v, CharP.cast_eq_zero K 2, zero_smul]
    have h2yv : y v + y v = 0 := by
      rw [← two_nsmul (y v), ← Nat.cast_smul_eq_nsmul (R := K) 2 (y v), CharP.cast_eq_zero K 2,
        zero_smul]
    calc M (M v) = y (y v - v) - (y v - v) := by
          simp [M, LinearMap.sub_apply]
      _ = (y (y v) - y v) - (y v - v) := by rw [map_sub]
      _ = (v - y v) - (y v - v) := by rw [hy_eval]
      _ = (v + v) - (y v + y v) := by abel
      _ = 0 := by rw [h2v, h2yv, sub_self]
  have hN2 : N * N = 0 := by
    ext v
    simpa [Module.End.mul_apply] using hN2_apply v
  have hM2 : M * M = 0 := by
    ext v
    simpa [Module.End.mul_apply] using hM2_apply v
  have hNM : N * M = M * N := by
    have h := hxy
    rw [hxN, hyM] at h
    have h' : (1 + N) * (1 + M) - (1 + M) * (1 + N) = 0 := sub_eq_zero.mpr h
    calc N * M = M * N + ((1 + N) * (1 + M) - (1 + M) * (1 + N)) := by noncomm_ring
      _ = M * N := by rw [h']; simp
  change N * M = 0
  by_contra hNM0
  have hex : ∃ w : V, N (M w) ≠ 0 := by
    by_contra h
    push Not at h
    exact hNM0 (by ext v; exact h v)
  obtain ⟨w, hw⟩ := hex
  have hMN_apply : ∀ v, M (N v) = N (M v) := by
    intro v
    have h := congrArg (fun f : Module.End K V => f v) hNM
    simpa [Module.End.mul_apply] using h.symm
  set p : V := w
  set q : V := M w
  set r : V := N w
  set s : V := N (M w) with hs
  have hs_ne : s ≠ 0 := by simpa [s] using hw
  have hNp : N p = r := by simp [p, r]
  have hMp : M p = q := by simp [p, q]
  have hNq : N q = s := by simp [q, s]
  have hMq : M q = 0 := by simpa [q] using hM2_apply w
  have hNr : N r = 0 := by simpa [r] using hN2_apply w
  have hMr : M r = s := by simpa [r, s] using hMN_apply w
  have hNs : N s = 0 := by simpa [s] using hN2_apply (M w)
  have hMs : M s = 0 := by
    calc M s = M (N (M w)) := by simp [s]
      _ = N (M (M w)) := hMN_apply (M w)
      _ = N 0 := by rw [hM2_apply w]
      _ = 0 := by simp
  have hli : LinearIndependent K ![p, r, q, s] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsum : c 0 • p + c 1 • r + c 2 • q + c 3 • s = 0 := by
      simpa [Fin.sum_univ_four] using hc
    have hNMsum := congrArg (fun v => (N * M) v) hsum
    have hNMsum' : c 0 • s = 0 := by
      simpa [map_add, map_smul, Module.End.mul_apply, hMp, hMq, hMr, hMs, hNq, hNr, hNs]
        using hNMsum
    have hc0 : c 0 = 0 := (smul_eq_zero.mp hNMsum').resolve_right hs_ne
    have hsum1 : c 1 • r + c 2 • q + c 3 • s = 0 := by
      simpa [hc0] using hsum
    have hNsum := congrArg (fun v => N v) hsum1
    have hNsum' : c 2 • s = 0 := by
      simpa [map_add, map_smul, hNq, hNr, hNs] using hNsum
    have hc2 : c 2 = 0 := (smul_eq_zero.mp hNsum').resolve_right hs_ne
    have hsum2 : c 1 • r + c 3 • s = 0 := by
      simpa [hc2] using hsum1
    have hMsum := congrArg (fun v => M v) hsum2
    have hMsum' : c 1 • s = 0 := by
      simpa [map_add, map_smul, hMr, hMs] using hMsum
    have hc1 : c 1 = 0 := (smul_eq_zero.mp hMsum').resolve_right hs_ne
    have hsum3 : c 3 • s = 0 := by
      simpa [hc1] using hsum2
    have hc3 : c 3 = 0 := (smul_eq_zero.mp hsum3).resolve_right hs_ne
    intro i
    fin_cases i
    exacts [hc0, hc1, hc2, hc3]
  have hli_triple : LinearIndependent K ![r, q, s] := by
    have hcomp : ![r, q, s] = ![p, r, q, s] ∘ (Fin.succ : Fin 3 → Fin 4) := by
      funext i
      fin_cases i <;> rfl
    rw [hcomp]
    exact hli.comp (Fin.succ : Fin 3 → Fin 4) (Fin.succ_injective 3)
  let ξ : ⋀[K]^3 V := wedge3 (K := K) p q r
  let wden : ⋀[K]^3 V := wedge3 (K := K) p q s
  let target : ⋀[K]^3 V := wedge3 (K := K) r q s
  have hyξ : exteriorPower.map 3 y ξ = ξ + wden := by
    have hyp : y p = p + q := by rw [hyM]; simp [hMp]
    have hyq : y q = q := by rw [hyM]; simp [hMq]
    have hyr : y r = r + s := by rw [hyM]; simp [hMr]
    change exteriorPower.map 3 y (wedge3 (K := K) p q r) = _
    rw [wedge3_map, hyp, hyq, hyr]
    simp [wedge3_add_first, wedge3_add_third, wedge3_eq_zero_of_eq]
    abel
  have hxden : exteriorPower.map 3 x wden = wden + target := by
    have hxp : x p = p + r := by rw [hxN]; simp [hNp]
    have hxq : x q = q + s := by rw [hxN]; simp [hNq]
    have hxs : x s = s := by rw [hxN]; simp [hNs]
    change exteriorPower.map 3 x (wedge3 (K := K) p q s) = _
    rw [wedge3_map, hxp, hxq, hxs]
    simp [wedge3_add_first, wedge3_add_second, wedge3_eq_zero_of_eq]
    abel
  have h1 : ((exteriorPower.map 3 y - 1) ξ) = wden := by
    simp only [LinearMap.sub_apply, Module.End.one_apply, hyξ]
    abel
  have h2 : ((exteriorPower.map 3 x - 1) wden) = target := by
    simp only [LinearMap.sub_apply, Module.End.one_apply, hxden]
    abel
  have hzero : target = 0 := by
    have hcomp : ((exteriorPower.map 3 x - 1) * (exteriorPower.map 3 y - 1)) ξ = 0 := by
      rw [hq]
      rfl
    rwa [Module.End.mul_apply, h1, h2] at hcomp
  exact (wedge3_ne_zero_of_linearIndependent hli_triple) hzero


section PartB

variable {K : Type} [Field K] [Finite K] {f : ℕ} {σ : K ≃+* K}

open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary

omit [Finite K] in
private theorem herm_mulVec_conjTr (hσ : ∀ c, σ (σ c) = c)
    (B : Matrix (Fin 3) (Fin 3) K) (x y : Fin 3 → K) :
    herm σ x (B *ᵥ y) = herm σ (conjTr σ B *ᵥ x) y := by
  rw [herm_def, herm_def]
  simp only [Matrix.mulVec, dotProduct, conjTr, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring


omit [Finite K] in
private theorem conjTr_mul_mul_apply (_hσ : ∀ c, σ (σ c) = c)
    (P : GL (Fin 3) K) (B : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (conjTr σ P.val * B * P.val) i j =
      herm σ (P.val *ᵥ Pi.single i 1) (B *ᵥ (P.val *ᵥ Pi.single j 1)) := by
  rw [herm_def]
  simp only [Matrix.mul_apply, conjTr, Matrix.map_apply, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_mul, Finset.mul_sum,
    map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hki : k = i <;> by_cases hlj : l = j <;> simp [hki, hlj] <;> ring

omit [Finite K] in
private theorem exists_diagonal_congruence_rank_two
    (hσ : IsUnitaryInvolution σ) {B : Matrix (Fin 3) (Fin 3) K}
    (hB : conjTr σ B = B)
    (hrank : finrank K (LinearMap.range B.mulVecLin) = 2) :
    ∃ P : GL (Fin 3) K,
      conjTr σ P.val * B * P.val = Matrix.diagonal ![0, 1, 1] ∧
      B.mulVecLin (P.val *ᵥ Pi.single 0 1) = 0 := by
  classical
  let ker := LinearMap.ker B.mulVecLin
  have hkerdim : finrank K ker = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
    have hrank' : finrank K (LinearMap.range B.mulVecLin) = 2 := hrank
    rw [hrank'] at h
    have hV : finrank K (Fin 3 → K) = 2 + 1 := by simp
    rw [hV] at h
    exact Nat.add_left_cancel h
  have hker_ne : ker ≠ ⊥ := by
    intro h
    rw [h] at hkerdim
    simp at hkerdim
  obtain ⟨k, hk_mem, hk_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  have hk_eq : B *ᵥ k = 0 := by
    rw [← Matrix.mulVecLin_apply]
    exact hk_mem
  have hkerspan : ker = K ∙ k :=
    eq_span_singleton_of_mem_of_finrank_eq_one hkerdim hk_mem hk_ne
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl ker
  have hdimW : finrank K W = 2 := by
    have h := Submodule.finrank_add_eq_of_isCompl hW
    rw [hkerdim] at h
    have hV : finrank K (Fin 3 → K) = 3 := by simp
    omega
  let hWform : W → W → K := fun x y => herm σ (x : Fin 3 → K) (B *ᵥ (y : Fin 3 → K))
  have hh : CFSG.Fischer.Classification.Herm.IsHermForm σ hWform := by
    refine ⟨?_, ?_, ?_⟩
    · intro x x' y
      simp [hWform, herm_add_left]
    · intro c x y
      simp [hWform, herm_smul_left]
    · intro x y
      change herm σ (y : Fin 3 → K) (B *ᵥ (x : Fin 3 → K)) =
        σ (herm σ (x : Fin 3 → K) (B *ᵥ (y : Fin 3 → K)))
      rw [herm_mulVec_conjTr hσ.invol B (y : Fin 3 → K) (x : Fin 3 → K), hB,
        herm_conj σ hσ.invol]
  have hnondeg : ∀ x : W, (∀ y : W, hWform x y = 0) → x = 0 := by
    intro x hx
    have hxorth : ∀ u ∈ LinearMap.range B.mulVecLin, herm σ (x : Fin 3 → K) u = 0 := by
      rintro u ⟨y, rfl⟩
      obtain ⟨⟨k', w⟩, hkw, -⟩ := Submodule.existsUnique_add_of_isCompl_prod hW y
      have hk' : B.mulVecLin (k' : Fin 3 → K) = 0 := k'.property
      have hy : B.mulVecLin y = B.mulVecLin (w : Fin 3 → K) := by
        rw [← hkw, map_add, hk', zero_add]
      rw [hy]
      exact hx w
    have hBx : B.mulVecLin (x : Fin 3 → K) = 0 := by
      apply eq_zero_of_herm σ
      intro y
      rw [← hB, Matrix.mulVecLin_apply,
        ← herm_mulVec_conjTr hσ.invol B (x : Fin 3 → K) y]
      exact hxorth (B.mulVecLin y) ⟨y, rfl⟩
    have hxbot : (x : Fin 3 → K) ∈ (⊥ : Submodule K (Fin 3 → K)) := by
      have hmem : (x : Fin 3 → K) ∈ ker ⊓ W := ⟨hBx, x.property⟩
      rwa [hW.disjoint.eq_bot] at hmem
    simpa using hxbot
  obtain ⟨e, he⟩ := CFSG.Fischer.Classification.exists_linearEquiv_herm_of_form
    (V := W) hσ hh hnondeg (m := 2) hdimW
  let bW : Basis (Fin 2) K W := (Pi.basisFun K (Fin 2)).map e.symm
  have hbW : ∀ i j, hWform (bW i) (bW j) = if i = j then 1 else 0 := by
    intro i j
    rw [← he (bW i) (bW j)]
    simp [bW, herm_single_right, Pi.single_apply, eq_comm]
  have hv : LinearIndependent K (fun i : Fin 2 => (bW i : Fin 3 → K)) := by
    have h := bW.linearIndependent
    have hker : LinearMap.ker (Submodule.subtype W) = ⊥ := by simp
    exact h.map' (Submodule.subtype W) hker
  have hspanW : Submodule.span K (Set.range fun i : Fin 2 => (bW i : Fin 3 → K)) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (bW i).property
    · intro w hw
      have hw' : w ∈ Submodule.map (Submodule.subtype W)
          (Submodule.span K (Set.range bW)) := by
        rw [bW.span_eq, Submodule.map_subtype_top]
        exact hw
      rw [Submodule.map_span, ← Set.range_comp] at hw'
      change w ∈ Submodule.span K (Set.range fun i : Fin 2 => (bW i : Fin 3 → K))
      exact hw'
  have hk_notW : k ∉ W := by
    intro hkW
    have hmem : k ∈ ker ⊓ W := ⟨hk_mem, hkW⟩
    have hbot : k ∈ (⊥ : Submodule K (Fin 3 → K)) := by
      rwa [hW.disjoint.eq_bot] at hmem
    exact hk_ne (by simpa using hbot)
  have hk_not_span : k ∉ Submodule.span K (Set.range fun i : Fin 2 => (bW i : Fin 3 → K)) := by
    rwa [hspanW]
  let v : Fin 3 → Fin 3 → K := ![k, (bW 0 : Fin 3 → K), (bW 1 : Fin 3 → K)]
  have hvcons : v = Fin.cons k (fun i : Fin 2 => (bW i : Fin 3 → K)) := by
    funext i
    fin_cases i <;> rfl
  have hli : LinearIndependent K v := by
    rw [hvcons]
    exact hv.finCons hk_not_span
  let b : Basis (Fin 3) K (Fin 3 → K) :=
    basisOfLinearIndependentOfCardEqFinrank' v hli (by simp)
  have hb : ∀ i, b i = v i := fun i => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  have hb0 : (b 0 : Fin 3 → K) = k := by
    rw [hb]
    rfl
  have hb1 : (b 1 : Fin 3 → K) = (bW 0 : Fin 3 → K) := by
    rw [hb]
    rfl
  have hb2 : (b 2 : Fin 3 → K) = (bW 1 : Fin 3 → K) := by
    rw [hb]
    rfl
  have hborth : ∀ i j, herm σ (b i) (B *ᵥ b j) = if i = j then (if i = 0 then 0 else 1) else 0 := by
    intro i j
    fin_cases i <;> fin_cases j
    · change herm σ (b 0) (B *ᵥ b 0) = 0
      rw [hb0, herm_mulVec_conjTr hσ.invol B k k, hB, hk_eq]
      simp
    · change herm σ (b 0) (B *ᵥ b 1) = 0
      rw [hb0, hb1, herm_mulVec_conjTr hσ.invol B k (bW 0 : Fin 3 → K), hB, hk_eq]
      simp
    · change herm σ (b 0) (B *ᵥ b 2) = 0
      rw [hb0, hb2, herm_mulVec_conjTr hσ.invol B k (bW 1 : Fin 3 → K), hB, hk_eq]
      simp
    · change herm σ (b 1) (B *ᵥ b 0) = 0
      rw [hb1, hb0, hk_eq]; simp
    · change herm σ (b 1) (B *ᵥ b 1) = 1
      simpa [hb1, hWform] using hbW (0 : Fin 2) (0 : Fin 2)
    · change herm σ (b 1) (B *ᵥ b 2) = 0
      simpa [hb1, hb2, hWform] using hbW (0 : Fin 2) (1 : Fin 2)
    · change herm σ (b 2) (B *ᵥ b 0) = 0
      rw [hb2, hb0, hk_eq]; simp
    · change herm σ (b 2) (B *ᵥ b 1) = 0
      simpa [hb2, hb1, hWform] using hbW (1 : Fin 2) (0 : Fin 2)
    · change herm σ (b 2) (B *ᵥ b 2) = 1
      simpa [hb2, hWform] using hbW (1 : Fin 2) (1 : Fin 2)
  let b0 : Basis (Fin 3) K (Fin 3 → K) := Pi.basisFun K (Fin 3)
  let P : GL (Fin 3) K :=
    { val := b0.toMatrix b
      inv := b.toMatrix b0
      val_inv := b0.toMatrix_mul_toMatrix_flip b
      inv_val := b.toMatrix_mul_toMatrix_flip b0 }
  have hcol : ∀ i : Fin 3, P.val *ᵥ Pi.single i 1 = b i := by
    intro i
    ext j
    simp [P, b0, Module.Basis.toMatrix_apply]
  refine ⟨P, ?_, ?_⟩
  · ext i j
    rw [conjTr_mul_mul_apply hσ.invol P B i j, hcol i, hcol j, hborth i j]
    fin_cases i <;> fin_cases j <;> simp
  · rw [hcol 0, hb0]
    simpa [Matrix.mulVecLin_apply] using hk_eq

omit [Finite K] in
private theorem eq_smul_one_of_cross_add_cross (_hσ : ∀ c, σ (σ c) = c)
    (E : (Fin 3 → K) →ₗ[K] (Fin 3 → K))
    (h : ∀ u v, crossProduct (E u) v + crossProduct u (E v) = 0) :
    ∃ c : K, E = c • 1 := by
  have hcross01 : crossProduct (Pi.single (1 : Fin 3) (1 : K))
      (Pi.single (2 : Fin 3) (1 : K)) = Pi.single (0 : Fin 3) (1 : K) := by
    funext i
    fin_cases i <;> simp [cross_apply]
  have hcross12 : crossProduct (Pi.single (2 : Fin 3) (1 : K))
      (Pi.single (0 : Fin 3) (1 : K)) = Pi.single (1 : Fin 3) (1 : K) := by
    funext i
    fin_cases i <;> simp [cross_apply]
  have hcross20 : crossProduct (Pi.single (0 : Fin 3) (1 : K))
      (Pi.single (1 : Fin 3) (1 : K)) = Pi.single (2 : Fin 3) (1 : K) := by
    funext i
    fin_cases i <;> simp [cross_apply]
  let M : Matrix (Fin 3) (Fin 3) K := LinearMap.toMatrix' E
  have hM : ∀ u v : Fin 3 → K,
      crossProduct (M *ᵥ u) v + crossProduct u (M *ᵥ v) = 0 := by
    intro u v
    rw [show M *ᵥ u = E u from LinearMap.toMatrix'_mulVec E u,
      show M *ᵥ v = E v from LinearMap.toMatrix'_mulVec E v]
    exact h u v
  have hbasis (i : Fin 3) : Mᵀ *ᵥ Pi.single i 1 = M.trace • Pi.single i 1 := by
    fin_cases i
    · have hh := hM (Pi.single (1 : Fin 3) (1 : K)) (Pi.single (2 : Fin 3) (1 : K))
      rw [Matrix.mulVec_cross_add_cross_mulVec, hcross01, sub_eq_zero] at hh
      exact hh.symm
    · have hh := hM (Pi.single (2 : Fin 3) (1 : K)) (Pi.single (0 : Fin 3) (1 : K))
      rw [Matrix.mulVec_cross_add_cross_mulVec, hcross12, sub_eq_zero] at hh
      exact hh.symm
    · have hh := hM (Pi.single (0 : Fin 3) (1 : K)) (Pi.single (1 : Fin 3) (1 : K))
      rw [Matrix.mulVec_cross_add_cross_mulVec, hcross20, sub_eq_zero] at hh
      exact hh.symm
  have htrans : Mᵀ = M.trace • (1 : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    have hh := congrFun (hbasis j) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm] using hh
  have hM_eq : M = M.trace • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have h := congrArg Matrix.transpose htrans
    simpa [transpose_transpose, transpose_smul, transpose_one] using h
  refine ⟨M.trace, ?_⟩
  apply LinearMap.ext
  intro x
  change E x = M.trace • x
  rw [← LinearMap.toMatrix'_mulVec E x]
  change M *ᵥ x = M.trace • x
  conv_lhs => rw [hM_eq]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]

omit [Finite K] in
private theorem exists_smul_of_cross_of_invertible (hσ : IsUnitaryInvolution σ)
    {B D : Matrix (Fin 3) (Fin 3) K} (_hB : conjTr σ B = B) (_hD : conjTr σ D = D)
    (hBinv : Function.Bijective B.mulVecLin)
    (hpol : ∀ α β : Fin 3 → K,
      crossProduct (B *ᵥ α) (D *ᵥ β) + crossProduct (D *ᵥ α) (B *ᵥ β) = 0) :
    ∃ c : K, D = c • B := by
  classical
  let e : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) := LinearEquiv.ofBijective B.mulVecLin hBinv
  let E : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
    D.mulVecLin.comp (e.symm : (Fin 3 → K) →ₗ[K] (Fin 3 → K))
  have hB_e (u : Fin 3 → K) : B *ᵥ (e.symm u) = u := by
    change B.mulVecLin (e.symm u) = u
    simp [e]
  have hD_e (u : Fin 3 → K) : D *ᵥ (e.symm u) = E u := by
    simp [E]
  have hE : ∀ u v : Fin 3 → K,
      crossProduct (E u) v + crossProduct u (E v) = 0 := by
    intro u v
    have h := hpol (e.symm u) (e.symm v)
    simpa [add_comm, hB_e u, hB_e v, hD_e u, hD_e v] using h
  obtain ⟨c, hc⟩ := eq_smul_one_of_cross_add_cross hσ.invol E hE
  refine ⟨c, ?_⟩
  have hEB (x : Fin 3 → K) : E (B *ᵥ x) = D *ᵥ x := by
    change D.mulVecLin (e.symm (e x)) = D.mulVecLin x
    rw [e.symm_apply_apply]
  have hDvec (x : Fin 3 → K) : D *ᵥ x = c • (B *ᵥ x) := by
    calc
      D *ᵥ x = E (B *ᵥ x) := (hEB x).symm
      _ = (c • 1 : Module.End K (Fin 3 → K)) (B *ᵥ x) :=
        congrArg (fun f : Module.End K (Fin 3 → K) => f (B *ᵥ x)) hc
      _ = c • (B *ᵥ x) := by simp
  ext i j
  have h := congrFun (hDvec (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h

omit [Finite K] in
private theorem eq_smul_of_image_le_span (_hσ : ∀ c, σ (σ c) = c)
    {B D : Matrix (Fin 3) (Fin 3) K} (hB : conjTr σ B = B) (hD : conjTr σ D = D)
    {u : Fin 3 → K} (hu : u ≠ 0)
    (hBim : ∀ y : Fin 3 → K, ∃ c : K, B *ᵥ y = c • u)
    (hDim : ∀ y : Fin 3 → K, ∃ c : K, D *ᵥ y = c • u)
    (hBne : B ≠ 0) :
    ∃ c : K, D = c • B := by
  classical
  have hu_exists : ∃ i0, u i0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext fun i => by simpa using h i)
  obtain ⟨i0, hi0⟩ := hu_exists
  have hcol : ∀ M : Matrix (Fin 3) (Fin 3) K,
      (∀ y : Fin 3 → K, ∃ c : K, M *ᵥ y = c • u) →
      ∃ coef : Fin 3 → K, ∀ i j, M i j = u i * coef j := by
    intro M hM
    choose coef hcoef using hM
    let colCoef : Fin 3 → K := fun j => coef (Pi.single j 1)
    refine ⟨colCoef, fun i j => ?_⟩
    have h := congrFun (hcoef (Pi.single j 1)) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm, colCoef] using h
  obtain ⟨coefB, hBcol⟩ := hcol B hBim
  obtain ⟨coefD, hDcol⟩ := hcol D hDim
  have hconjB (i j : Fin 3) : B j i = σ (B i j) := by
    have h := congrFun (congrFun hB j) i
    simpa [conjTr, Matrix.map_apply, Matrix.transpose_apply] using h.symm
  have hconjD (i j : Fin 3) : D j i = σ (D i j) := by
    have h := congrFun (congrFun hD j) i
    simpa [conjTr, Matrix.map_apply, Matrix.transpose_apply] using h.symm
  have hBrel (i j : Fin 3) : u j * coefB i = σ (u i) * σ (coefB j) := by
    have h := hconjB i j
    rw [hBcol j i, hBcol i j, map_mul] at h
    exact h
  have hDrel (i j : Fin 3) : u j * coefD i = σ (u i) * σ (coefD j) := by
    have h := hconjD i j
    rw [hDcol j i, hDcol i j, map_mul] at h
    exact h
  let M0 : Matrix (Fin 3) (Fin 3) K := fun i j => u i * σ (u j)
  let kB : K := σ (coefB i0) / u i0
  let kD : K := σ (coefD i0) / u i0
  have hB_M0 : B = kB • M0 := by
    ext i j
    have hrel := hBrel j i0
    have hcoef : coefB j = σ (u j) * kB := by
      dsimp [kB]
      rw [div_eq_mul_inv]
      field_simp [hi0]
      linear_combination hrel
    rw [hBcol i j]
    show u i * coefB j = kB * M0 i j
    rw [hcoef]
    show u i * (σ (u j) * kB) = kB * (u i * σ (u j))
    ring
  have hD_M0 : D = kD • M0 := by
    ext i j
    have hrel := hDrel j i0
    have hcoef : coefD j = σ (u j) * kD := by
      dsimp [kD]
      rw [div_eq_mul_inv]
      field_simp [hi0]
      linear_combination hrel
    rw [hDcol i j]
    show u i * coefD j = kD * M0 i j
    rw [hcoef]
    show u i * (σ (u j) * kD) = kD * (u i * σ (u j))
    ring
  have hkB : kB ≠ 0 := by
    intro hk
    apply hBne
    rw [hB_M0, hk, zero_smul]
  refine ⟨kD / kB, ?_⟩
  rw [hD_M0, hB_M0]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  field_simp [hkB]

omit [Finite K] in
private theorem exists_mulVec_ne_zero_of_ne_zero {B : Matrix (Fin 3) (Fin 3) K}
    (hB : B ≠ 0) : ∃ z : Fin 3 → K, B *ᵥ z ≠ 0 := by
  by_contra h
  push Not at h
  apply hB
  ext i j
  have hh := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hh

omit [Finite K] in
private theorem exists_smul_of_cross_eq_zero {u v : Fin 3 → K} (hu : u ≠ 0)
    (h : crossProduct u v = 0) : ∃ c : K, v = c • u := by
  by_contra hc
  push Not at hc
  have hli : LinearIndependent K ![u, v] := by
    rw [LinearIndependent.pair_iff' hu]
    intro a ha
    exact (hc a) ha.symm
  exact (crossProduct_ne_zero_iff_linearIndependent.mpr hli) h

omit [Finite K] in
private theorem eq_zero_of_herm_right (hσ : ∀ c, σ (σ c) = c) {x : Fin 3 → K}
    (h : ∀ y : Fin 3 → K, herm σ y x = 0) : x = 0 := by
  apply eq_zero_of_herm (σ := σ)
  intro y
  rw [herm_conj σ hσ, h y, map_zero]

omit [Finite K] in
private theorem eq_smul_of_forall_herm_eq_zero (hσ : IsUnitaryInvolution σ)
    {u : Fin 3 → K} (hu : u ≠ 0) {v : Fin 3 → K}
    (h : ∀ x : Fin 3 → K, herm σ x u = 0 → herm σ x v = 0) :
    ∃ c : K, v = c • u := by
  obtain ⟨w, hw⟩ := exists_herm_eq_one (σ := σ) hu
  have hw' : herm σ w u = 1 := by
    rw [herm_conj σ hσ.invol, hw, map_one]
  let c : K := herm σ w v
  refine ⟨c, ?_⟩
  have hzero : v - c • u = 0 := by
    apply eq_zero_of_herm_right hσ.invol
    intro x
    let t : K := σ.symm (herm σ x u)
    have ht : σ t = herm σ x u := σ.apply_symm_apply _
    have hxH : herm σ (x - t • w) u = 0 := by
      rw [herm_sub_left, herm_smul_left, ht, hw', mul_one, sub_self]
    have hxv := h (x - t • w) hxH
    have hx_eq : herm σ x v = c * herm σ x u := by
      rw [herm_sub_left, herm_smul_left, ht, sub_eq_zero] at hxv
      dsimp [c]
      linear_combination hxv
    rw [herm_sub_right, herm_smul_right, hx_eq, sub_self]
  exact sub_eq_zero.mp hzero
omit [Finite K] in
private theorem exists_smul_of_cross_of_rank_one (hσ : IsUnitaryInvolution σ)
    {B D : Matrix (Fin 3) (Fin 3) K} (hB : conjTr σ B = B) (hD : conjTr σ D = D)
    (hBne : B ≠ 0) (hBrank : finrank K (LinearMap.range B.mulVecLin) = 1)
    (hDrank : finrank K (LinearMap.range D.mulVecLin) ≤ 1)
    (hpol : ∀ α β : Fin 3 → K,
      crossProduct (B *ᵥ α) (D *ᵥ β) + crossProduct (D *ᵥ α) (B *ᵥ β) = 0) :
    ∃ c : K, D = c • B := by
  classical
  obtain ⟨z, hz⟩ := exists_mulVec_ne_zero_of_ne_zero hBne
  let u : Fin 3 → K := B *ᵥ z
  have hu : u ≠ 0 := hz
  have hu_mem : u ∈ LinearMap.range B.mulVecLin := ⟨z, rfl⟩
  have hBspan : LinearMap.range B.mulVecLin = K ∙ u :=
    eq_span_singleton_of_mem_of_finrank_eq_one hBrank hu_mem hu
  have hBim : ∀ y : Fin 3 → K, ∃ c : K, B *ᵥ y = c • u := by
    intro y
    have hy : B *ᵥ y ∈ (K ∙ u : Submodule K (Fin 3 → K)) := by
      rw [← hBspan]
      exact ⟨y, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨c, hc.symm⟩
  let H : Submodule K (Fin 3 → K) :=
    { carrier := {x | herm σ x u = 0}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        show herm σ (x + y) u = 0
        rw [herm_add_left, hx, hy, add_zero]
      smul_mem' := by
        intro c x hx
        show herm σ (c • x) u = 0
        rw [herm_smul_left, hx, mul_zero] }
  have hBH : ∀ h : H, B *ᵥ (h : Fin 3 → K) = 0 := by
    intro h
    apply eq_zero_of_herm (σ := σ)
    intro y
    have hBh : B *ᵥ (h : Fin 3 → K) = (conjTr σ B) *ᵥ (h : Fin 3 → K) := by
      rw [hB]
    rw [hBh, ← herm_mulVec_conjTr hσ.invol B (h : Fin 3 → K) y]
    obtain ⟨c, hc⟩ := hBim y
    rw [hc, herm_smul_right, h.property, mul_zero]
  have hDH : ∀ h : H, ∃ c : K, D *ᵥ (h : Fin 3 → K) = c • u := by
    intro h
    have hcond := hpol z (h : Fin 3 → K)
    have hcross : crossProduct u (D *ᵥ (h : Fin 3 → K)) = 0 := by
      simpa [u, hBH h] using hcond
    exact exists_smul_of_cross_eq_zero hu hcross
  have hHorth : ∀ v : Fin 3 → K,
      (∀ h : H, herm σ (h : Fin 3 → K) v = 0) → v ∈ (K ∙ u : Submodule K (Fin 3 → K)) := by
    intro v hv
    have h : ∀ x : Fin 3 → K, herm σ x u = 0 → herm σ x v = 0 := by
      intro x hx
      exact hv ⟨x, hx⟩
    obtain ⟨c, hc⟩ := eq_smul_of_forall_herm_eq_zero hσ hu h
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  have hDim : ∀ y : Fin 3 → K, ∃ c : K, D *ᵥ y = c • u := by
    by_cases hzero : ∀ h : H, D *ᵥ (h : Fin 3 → K) = 0
    · intro y
      have horth : ∀ h : H, herm σ (h : Fin 3 → K) (D *ᵥ y) = 0 := by
        intro h
        rw [herm_mulVec_conjTr hσ.invol D (h : Fin 3 → K) y, hD, hzero h]
        simp
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hHorth (D *ᵥ y) horth)
      exact ⟨a, ha.symm⟩
    · push Not at hzero
      obtain ⟨h, hh⟩ := hzero
      obtain ⟨c, hc⟩ := hDH h
      have hc0 : c ≠ 0 := by
        intro hc0
        apply hh
        rw [hc, hc0, zero_smul]
      have hu_memD : u ∈ LinearMap.range D.mulVecLin := by
        refine ⟨c⁻¹ • (h : Fin 3 → K), ?_⟩
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_smul, hc, smul_smul,
          inv_mul_cancel₀ hc0, one_smul]
      have hDrank1 : finrank K (LinearMap.range D.mulVecLin) = 1 := by
        have hpos : 1 ≤ finrank K (LinearMap.range D.mulVecLin) := by
          have hle : (K ∙ u : Submodule K (Fin 3 → K)) ≤ LinearMap.range D.mulVecLin := by
            intro x hx
            obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
            exact Submodule.smul_mem _ a hu_memD
          have hf := Submodule.finrank_mono hle
          rwa [finrank_span_singleton hu] at hf
        omega
      have hDspan : LinearMap.range D.mulVecLin = K ∙ u :=
        eq_span_singleton_of_mem_of_finrank_eq_one hDrank1 hu_memD hu
      intro y
      have hy : D *ᵥ y ∈ (K ∙ u : Submodule K (Fin 3 → K)) := by
        rw [← hDspan]
        exact ⟨y, rfl⟩
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy
      exact ⟨a, ha.symm⟩
  exact eq_smul_of_image_le_span hσ.invol hB hD hu hBim hDim hBne

private theorem card_fixed_eq [Fact (Nat.Prime 2)] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσeq : σ = CFSG.LieType.BorelTits.unitaryInvolution K 2 f) :
    Nat.card {c : K // σ c = c} = 2 ^ f := by
  classical
  let e : {c : K // σ c = c} ≃ CFSG.LieType.Steinberg.fixedSubfield K 2 f :=
    { toFun := fun c => ⟨c.1, by
        rw [CFSG.LieType.Steinberg.mem_fixedSubfield, ← hσeq]
        exact c.2⟩
      invFun := fun c => ⟨c.1, by
        have h := (CFSG.LieType.Steinberg.mem_fixedSubfield).mp c.2
        simpa [hσeq] using h⟩
      left_inv := by intro c; rfl
      right_inv := by intro c; rfl }
  rw [Nat.card_congr e]
  exact CFSG.LieType.Steinberg.card_fixedSubfield (F := K) (p := 2) (f := f) hK

private theorem card_le_of_smul_line [Fact (Nat.Prime 2)] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K}
    (hσeq : σ = CFSG.LieType.BorelTits.unitaryInvolution K 2 f)
    {B0 : Matrix (Fin 3) (Fin 3) K} (hB0 : conjTr σ B0 = B0) (hB0ne : B0 ≠ 0)
    {S : Set (Matrix (Fin 3) (Fin 3) K)}
    (hS : ∀ D ∈ S, ∃ c : K, D = c • B0)
    (hherm : ∀ B ∈ S, conjTr σ B = B) :
    Nat.card S ≤ 2 ^ f := by
  classical
  let toF : S → {c : K // σ c = c} := fun D =>
    ⟨Classical.choose (hS D D.property), by
      let c := Classical.choose (hS D D.property)
      have hc : (D : Matrix (Fin 3) (Fin 3) K) = c • B0 :=
        Classical.choose_spec (hS D D.property)
      have hDherm : conjTr σ (D : Matrix (Fin 3) (Fin 3) K) = D :=
        hherm D D.property
      have hEq : σ c • B0 = c • B0 := by
        calc
          σ c • B0 = conjTr σ (c • B0) := by
            rw [conjTr_smul, hB0]
          _ = conjTr σ (D : Matrix (Fin 3) (Fin 3) K) := by rw [← hc]
          _ = D := hDherm
          _ = c • B0 := hc
      obtain ⟨z, hz⟩ := exists_mulVec_ne_zero_of_ne_zero hB0ne
      have hzEq : σ c • (B0 *ᵥ z) = c • (B0 *ᵥ z) := by
        have := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M *ᵥ z) hEq
        simpa [Matrix.smul_mulVec] using this
      have hv : ∃ i : Fin 3, (B0 *ᵥ z) i ≠ 0 := by
        by_contra h
        push Not at h
        exact hz (funext fun i => by simpa using h i)
      obtain ⟨i, hi⟩ := hv
      have hzi := congrFun hzEq i
      simp only [Pi.smul_apply, smul_eq_mul] at hzi
      exact mul_right_cancel₀ hi hzi⟩
  have hinj : Function.Injective toF := by
    intro D E hDE
    have hc : Classical.choose (hS D D.property) = Classical.choose (hS E E.property) :=
      congrArg Subtype.val hDE
    have hD := Classical.choose_spec (hS D D.property)
    have hE := Classical.choose_spec (hS E E.property)
    apply Subtype.ext
    rw [hD, hE, hc]
  have hle := Nat.card_le_card_of_injective toF hinj
  rwa [card_fixed_eq hK σ hσeq] at hle

omit [Finite K] in
private theorem eq_zero_of_cross_single_one_two {u : Fin 3 → K}
    (h1 : crossProduct u (Pi.single (1 : Fin 3) 1) = 0)
    (h2 : crossProduct u (Pi.single (2 : Fin 3) 1) = 0) : u = 0 := by
  have h10 := congrFun h1 0
  have h12 := congrFun h1 2
  have h20 := congrFun h2 0
  simp [cross_apply] at h10 h12 h20
  funext i
  fin_cases i
  · exact h12
  · exact h20
  · exact h10

omit [Finite K] in
private theorem block_form_diag (_hσ : IsUnitaryInvolution σ)
    {D : Matrix (Fin 3) (Fin 3) K} (_hD : conjTr σ D = D)
    (h : ∀ α β : Fin 3 → K,
      crossProduct (Matrix.diagonal ![0, 1, 1] *ᵥ α) (D *ᵥ β) +
        crossProduct (D *ᵥ α) (Matrix.diagonal ![0, 1, 1] *ᵥ β) = 0) :
    D *ᵥ Pi.single (0 : Fin 3) 1 = 0 ∧ D 1 1 + D 2 2 = 0 := by
  have hB (α : Fin 3 → K) : Matrix.diagonal ![0, 1, 1] *ᵥ α = ![0, α 1, α 2] := by
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.diagonal]
  have hB0 : Matrix.diagonal ![0, 1, 1] *ᵥ Pi.single (0 : Fin 3) 1 = 0 := by
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.diagonal, Pi.single_apply]
  have hB1 : Matrix.diagonal ![0, 1, 1] *ᵥ Pi.single (1 : Fin 3) 1 =
      Pi.single (1 : Fin 3) 1 := by
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.diagonal, Pi.single_apply]
  have hB2 : Matrix.diagonal ![0, 1, 1] *ᵥ Pi.single (2 : Fin 3) 1 =
      Pi.single (2 : Fin 3) 1 := by
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.diagonal, Pi.single_apply]
  have hDe1 : crossProduct (D *ᵥ Pi.single (0 : Fin 3) 1) (Pi.single (1 : Fin 3) 1) = 0 := by
    have hh := h (Pi.single (0 : Fin 3) 1) (Pi.single (1 : Fin 3) 1)
    simpa [hB0, hB1] using hh
  have hDe2 : crossProduct (D *ᵥ Pi.single (0 : Fin 3) 1) (Pi.single (2 : Fin 3) 1) = 0 := by
    have hh := h (Pi.single (0 : Fin 3) 1) (Pi.single (2 : Fin 3) 1)
    simpa [hB0, hB2] using hh
  have hzero : D *ᵥ Pi.single (0 : Fin 3) 1 = 0 :=
    eq_zero_of_cross_single_one_two hDe1 hDe2
  have hcol1 : D *ᵥ Pi.single (1 : Fin 3) 1 = ![D 0 1, D 1 1, D 2 1] := by
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hcol2 : D *ᵥ Pi.single (2 : Fin 3) 1 = ![D 0 2, D 1 2, D 2 2] := by
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  refine ⟨hzero, ?_⟩
  have hh := h (Pi.single (1 : Fin 3) 1) (Pi.single (2 : Fin 3) 1)
  simp only [hcol1, hcol2] at hh
  have h0 := congrFun hh 0
  simpa [add_comm, cross_apply] using h0

omit [Finite K] in
private theorem trace_relation_block [CharP K 2] (_hσ : IsUnitaryInvolution σ)
    {D E : Matrix (Fin 3) (Fin 3) K} (hD : conjTr σ D = D) (hE : conjTr σ E = E)
    (_hD0 : D *ᵥ Pi.single (0 : Fin 3) 1 = 0)
    (_hE0 : E *ᵥ Pi.single (0 : Fin 3) 1 = 0)
    (hDtr : D 1 1 + D 2 2 = 0) (hEtr : E 1 1 + E 2 2 = 0)
    (h : ∀ α β : Fin 3 → K,
      crossProduct (D *ᵥ α) (E *ᵥ β) + crossProduct (E *ᵥ α) (D *ᵥ β) = 0) :
    D 1 2 * σ (E 1 2) + σ (D 1 2) * E 1 2 = 0 := by
  have hD21 : D 2 1 = σ (D 1 2) := by
    have hh := congrFun (congrFun hD 2) 1
    simpa [conjTr, Matrix.map_apply, Matrix.transpose_apply] using hh.symm
  have hE21 : E 2 1 = σ (E 1 2) := by
    have hh := congrFun (congrFun hE 2) 1
    simpa [conjTr, Matrix.map_apply, Matrix.transpose_apply] using hh.symm
  have hD22 : D 2 2 = D 1 1 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination hDtr - h2 * D 1 1
  have hE22 : E 2 2 = E 1 1 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination hEtr - h2 * E 1 1
  have hh := congrFun (h (Pi.single (2 : Fin 3) 1) (Pi.single (1 : Fin 3) 1)) 0
  simp [cross_apply, hD21, hE21, hD22, hE22] at hh

  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination hh + h2 * (D 1 1 * E 1 1)

omit [Finite K] in
private theorem conjTr_mul_mul_injective (P : GL (Fin 3) K) :
    Function.Injective (fun D : Matrix (Fin 3) (Fin 3) K =>
      conjTr σ P.val * D * P.val) := by
  intro D E h
  change conjTr σ P.val * D * P.val = conjTr σ P.val * E * P.val at h
  have hP1 : P.val * P.inv = 1 := P.val_inv
  have hP2 : P.inv * P.val = 1 := P.inv_val
  have hQ1 : conjTr σ P.val * conjTr σ P.inv = 1 := by
    rw [← conjTr_mul, hP2, conjTr_one]
  have hQ2 : conjTr σ P.inv * conjTr σ P.val = 1 := by
    rw [← conjTr_mul, hP1, conjTr_one]
  calc
    D = (conjTr σ P.inv * conjTr σ P.val) * D * (P.val * P.inv) := by
      rw [hQ2, hP1, one_mul, mul_one]
    _ = conjTr σ P.inv * (conjTr σ P.val * D * P.val) * P.inv := by
      noncomm_ring
    _ = conjTr σ P.inv * (conjTr σ P.val * E * P.val) * P.inv := by rw [h]
    _ = (conjTr σ P.inv * conjTr σ P.val) * E * (P.val * P.inv) := by
      noncomm_ring
    _ = E := by rw [hQ2, hP1, one_mul, mul_one]

private def blockMat (a b : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 0; 0, a, b; 0, σ b, a]

omit [Finite K] in
private theorem eq_blockMat_of_block [CharP K 2] (_hσ : IsUnitaryInvolution σ)
    {D : Matrix (Fin 3) (Fin 3) K} (hD : conjTr σ D = D)
    (h0 : D *ᵥ Pi.single (0 : Fin 3) 1 = 0) (htr : D 1 1 + D 2 2 = 0) :
    D = blockMat (σ := σ) (D 1 1) (D 1 2) := by
  have hD00 : D 0 0 = 0 := by
    have h := congrFun h0 0
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
  have hD10 : D 1 0 = 0 := by
    have h := congrFun h0 1
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
  have hD20 : D 2 0 = 0 := by
    have h := congrFun h0 2
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
  have hD01 : D 0 1 = 0 := by
    have h := congrFun (congrFun hD 0) 1
    simpa [conjTr, Matrix.map_apply, Matrix.transpose_apply, hD10] using h.symm
  have hD02 : D 0 2 = 0 := by
    have h := congrFun (congrFun hD 0) 2
    simpa [conjTr, Matrix.map_apply, Matrix.transpose_apply, hD20] using h.symm
  have hD21 : D 2 1 = σ (D 1 2) := by
    have h := congrFun (congrFun hD 2) 1
    simpa [conjTr, Matrix.map_apply, Matrix.transpose_apply] using h.symm
  have hD22 : D 2 2 = D 1 1 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination htr - h2 * D 1 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, hD00, hD10, hD20, hD01, hD02, hD21, hD22]

theorem crossProduct_mulVec_mulVec {R : Type*} [CommRing R]
    (M : Matrix (Fin 3) (Fin 3) R) (u v : Fin 3 → R) :
    crossProduct (M *ᵥ u) (M *ᵥ v) =
      (Matrix.adjugate M)ᵀ *ᵥ crossProduct u v := by
  ext i
  fin_cases i <;>
    simp [cross_apply, Matrix.adjugate_fin_three, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] <;>
    ring

private theorem card_le_sq_of_rank_two [CharP K 2] [Fact (Nat.Prime 2)]
    (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : IsUnitaryInvolution σ)
    (hσeq : σ = CFSG.LieType.BorelTits.unitaryInvolution K 2 f)
    {B0 : Matrix (Fin 3) (Fin 3) K} {S : Set (Matrix (Fin 3) (Fin 3) K)}
    (hB0S : B0 ∈ S) (hB0rank : finrank K (LinearMap.range B0.mulVecLin) = 2)
    (hherm : ∀ B ∈ S, conjTr σ B = B)
    (hpol : ∀ B ∈ S, ∀ D ∈ S, ∀ α β : Fin 3 → K,
      crossProduct (B *ᵥ α) (D *ᵥ β) + crossProduct (D *ᵥ α) (B *ᵥ β) = 0) :
    Nat.card S ≤ (2 ^ f) ^ 2 := by
  classical
  obtain ⟨P, hPdiag, -⟩ :=
    exists_diagonal_congruence_rank_two hσ (hherm B0 hB0S) hB0rank
  let T : Matrix (Fin 3) (Fin 3) K → Matrix (Fin 3) (Fin 3) K :=
    fun D => conjTr σ P.val * D * P.val
  have hTinj : Function.Injective T := conjTr_mul_mul_injective (σ := σ) P
  have hTB : T B0 = Matrix.diagonal ![0, 1, 1] := hPdiag
  have hcondT : ∀ D ∈ S, ∀ E ∈ S, ∀ α β : Fin 3 → K,
      crossProduct (T D *ᵥ α) (T E *ᵥ β) + crossProduct (T E *ᵥ α) (T D *ᵥ β) = 0 := by
    intro D hD E hE α β
    let M : Matrix (Fin 3) (Fin 3) K := conjTr σ P.val
    have hM : ∀ u v : Fin 3 → K,
        crossProduct (M *ᵥ u) (M *ᵥ v) = (Matrix.adjugate M)ᵀ *ᵥ crossProduct u v :=
      fun u v => crossProduct_mulVec_mulVec M u v
    have hTD : T D *ᵥ α = M *ᵥ (D *ᵥ (P.val *ᵥ α)) := by
      simp [T, M, Matrix.mulVec_mulVec, mul_assoc]
    have hTE : T E *ᵥ β = M *ᵥ (E *ᵥ (P.val *ᵥ β)) := by
      simp [T, M, Matrix.mulVec_mulVec, mul_assoc]
    have hTEα : T E *ᵥ α = M *ᵥ (E *ᵥ (P.val *ᵥ α)) := by
      simp [T, M, Matrix.mulVec_mulVec, mul_assoc]
    have hTDβ : T D *ᵥ β = M *ᵥ (D *ᵥ (P.val *ᵥ β)) := by
      simp [T, M, Matrix.mulVec_mulVec, mul_assoc]
    rw [hTD, hTE, hTEα, hTDβ, hM, hM, ← Matrix.mulVec_add]
    rw [hpol D hD E hE (P.val *ᵥ α) (P.val *ᵥ β), Matrix.mulVec_zero]
  have hDherm (D : S) : conjTr σ (T (D : Matrix (Fin 3) (Fin 3) K)) = T (D : Matrix (Fin 3) (Fin 3) K) := by
    change conjTr σ (conjTr σ P.val * (D : Matrix (Fin 3) (Fin 3) K) * P.val) =
      conjTr σ P.val * (D : Matrix (Fin 3) (Fin 3) K) * P.val
    rw [conjTr_mul, conjTr_mul, conjTr_conjTr hσ.invol, hherm D D.property]
    noncomm_ring
  have hDcond (D : S) : ∀ α β : Fin 3 → K,
      crossProduct (Matrix.diagonal ![0, 1, 1] *ᵥ α) (T (D : Matrix (Fin 3) (Fin 3) K) *ᵥ β) +
        crossProduct (T (D : Matrix (Fin 3) (Fin 3) K) *ᵥ α) (Matrix.diagonal ![0, 1, 1] *ᵥ β) = 0 := by
    intro α β
    simpa [hTB] using hcondT B0 hB0S D D.property α β
  have hD0 (D : S) : T (D : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single (0 : Fin 3) 1 = 0 :=
    (block_form_diag hσ (hDherm D) (hDcond D)).1
  have hDtr (D : S) : (T (D : Matrix (Fin 3) (Fin 3) K)) 1 1 +
      (T (D : Matrix (Fin 3) (Fin 3) K)) 2 2 = 0 :=
    (block_form_diag hσ (hDherm D) (hDcond D)).2
  have hDmat (D : S) : T (D : Matrix (Fin 3) (Fin 3) K) =
      blockMat (σ := σ) ((T (D : Matrix (Fin 3) (Fin 3) K)) 1 1)
        ((T (D : Matrix (Fin 3) (Fin 3) K)) 1 2) :=
    eq_blockMat_of_block hσ (hDherm D) (hD0 D) (hDtr D)
  have hDa (D : S) : σ ((T (D : Matrix (Fin 3) (Fin 3) K)) 1 1) =
      (T (D : Matrix (Fin 3) (Fin 3) K)) 1 1 := by
    have h := congrFun (congrFun (hDherm D) 1) 1
    simpa [conjTr, Matrix.map_apply, Matrix.transpose_apply] using h
  have hDrel (D E : S) :
      (T (D : Matrix (Fin 3) (Fin 3) K)) 1 2 * σ ((T (E : Matrix (Fin 3) (Fin 3) K)) 1 2) +
        σ ((T (D : Matrix (Fin 3) (Fin 3) K)) 1 2) *
          (T (E : Matrix (Fin 3) (Fin 3) K)) 1 2 = 0 :=
    trace_relation_block hσ (hDherm D) (hDherm E) (hD0 D) (hD0 E) (hDtr D) (hDtr E)
      (fun α β => hcondT D D.property E E.property α β)
  let F := {c : K // σ c = c}
  have hcardF : Nat.card F = 2 ^ f := card_fixed_eq hK σ hσeq
  by_cases hb : ∃ D : S, (T (D : Matrix (Fin 3) (Fin 3) K)) 1 2 ≠ 0
  · obtain ⟨D0, hD0ne⟩ := hb
    let b0 : K := (T (D0 : Matrix (Fin 3) (Fin 3) K)) 1 2
    have hb0ne : b0 ≠ 0 := hD0ne
    have hsb0 : σ b0 ≠ 0 := by
      intro h
      apply hb0ne
      have := congrArg σ h
      simpa [hσ.invol] using this
    let toF : S → F × F := fun D =>
      (⟨(T (D : Matrix (Fin 3) (Fin 3) K)) 1 1, hDa D⟩,
        ⟨(T (D : Matrix (Fin 3) (Fin 3) K)) 1 2 * σ b0, by
          have hrel := hDrel D D0
          have hx : (T (D : Matrix (Fin 3) (Fin 3) K)) 1 2 * σ b0 +
              σ ((T (D : Matrix (Fin 3) (Fin 3) K)) 1 2 * σ b0) = 0 := by
            rw [map_mul, hσ.invol]
            exact hrel
          have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
          have hneg : σ ((T (D : Matrix (Fin 3) (Fin 3) K)) 1 2 * σ b0) =
              -((T (D : Matrix (Fin 3) (Fin 3) K)) 1 2 * σ b0) := by
            linear_combination hx
          have hxx : -((T (D : Matrix (Fin 3) (Fin 3) K)) 1 2 * σ b0) =
              (T (D : Matrix (Fin 3) (Fin 3) K)) 1 2 * σ b0 := by
            linear_combination -h2 * ((T (D : Matrix (Fin 3) (Fin 3) K)) 1 2 * σ b0)
          exact hneg.trans hxx⟩)
    have htoFinj : Function.Injective toF := by
      intro D E hDE
      have ha : (T (D : Matrix (Fin 3) (Fin 3) K)) 1 1 = (T (E : Matrix (Fin 3) (Fin 3) K)) 1 1 :=
        congrArg (fun p : F × F => (p.1 : K)) hDE
      have hx : (T (D : Matrix (Fin 3) (Fin 3) K)) 1 2 * σ b0 =
          (T (E : Matrix (Fin 3) (Fin 3) K)) 1 2 * σ b0 :=
        congrArg (fun p : F × F => (p.2 : K)) hDE
      have hbEq : (T (D : Matrix (Fin 3) (Fin 3) K)) 1 2 =
          (T (E : Matrix (Fin 3) (Fin 3) K)) 1 2 :=
        mul_right_cancel₀ hsb0 hx
      apply Subtype.ext
      apply hTinj
      rw [hDmat D, hDmat E, ha, hbEq]
    have hle := Nat.card_le_card_of_injective toF htoFinj
    calc
      Nat.card S ≤ Nat.card (F × F) := hle
      _ = Nat.card F * Nat.card F := Nat.card_prod F F
      _ = (2 ^ f) ^ 2 := by rw [hcardF, pow_two]
  · push Not at hb
    let toF : S → F × F := fun D =>
      (⟨(T (D : Matrix (Fin 3) (Fin 3) K)) 1 1, hDa D⟩, ⟨0, by simp⟩)
    have htoFinj : Function.Injective toF := by
      intro D E hDE
      have ha : (T (D : Matrix (Fin 3) (Fin 3) K)) 1 1 = (T (E : Matrix (Fin 3) (Fin 3) K)) 1 1 :=
        congrArg (fun p : F × F => (p.1 : K)) hDE
      have hbEq : (T (D : Matrix (Fin 3) (Fin 3) K)) 1 2 =
          (T (E : Matrix (Fin 3) (Fin 3) K)) 1 2 := by
        rw [hb D, hb E]
      apply Subtype.ext
      apply hTinj
      rw [hDmat D, hDmat E, ha, hbEq]
    have hle := Nat.card_le_card_of_injective toF htoFinj
    calc
      Nat.card S ≤ Nat.card (F × F) := hle
      _ = Nat.card F * Nat.card F := Nat.card_prod F F
      _ = (2 ^ f) ^ 2 := by rw [hcardF, pow_two]

set_option linter.style.haveILetI false in
theorem card_le_sq_of_hermitian_polarized_cross {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (S : Set (Matrix (Fin 3) (Fin 3) K))
    (hherm : ∀ B ∈ S, (B.map (· ^ (2 ^ f)))ᵀ = B)
    (hpol : ∀ B ∈ S, ∀ D ∈ S, ∀ α β : Fin 3 → K,
      crossProduct (B *ᵥ α) (D *ᵥ β) + crossProduct (D *ᵥ α) (B *ᵥ β) = 0) :
    Nat.card S ≤ (2 ^ f) ^ 2 := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hchar : CharP K 2 := charP_of_card_sq (p := 2) (f := f) hK
  let σ : K ≃+* K := CFSG.LieType.BorelTits.unitaryInvolution K 2 f
  have hσ : IsUnitaryInvolution σ :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (p := 2) (f := f) hK
  have hσeq : σ = CFSG.LieType.BorelTits.unitaryInvolution K 2 f := rfl
  have hmap : (⇑σ : K → K) = fun x => x ^ (2 ^ f) := by
    funext x
    exact CFSG.LieType.BorelTits.unitaryInvolution_apply (K := K) (p := 2) (f := f) x
  have hherm' : ∀ B ∈ S, conjTr σ B = B := by
    intro B hB
    rw [conjTr]
    rw [hmap]
    exact hherm B hB
  have hq : 1 ≤ 2 ^ f := Nat.one_le_pow f 2 (by norm_num)
  have hq1 : 1 ≤ (2 ^ f) ^ 2 := by nlinarith
  have hqle : 2 ^ f ≤ (2 ^ f) ^ 2 := by nlinarith
  by_cases hzero : ∀ B ∈ S, B = 0
  · have hcard : Nat.card S ≤ 1 := by
      have hinj : Function.Injective (fun _ : S => (0 : Fin 1)) := by
        intro D E _
        apply Subtype.ext
        rw [hzero D D.property, hzero E E.property]
      have hle := Nat.card_le_card_of_injective (fun _ : S => (0 : Fin 1)) hinj
      simpa using hle
    exact le_trans hcard hq1
  · by_cases hinv : ∃ B ∈ S, Function.Bijective B.mulVecLin
    · obtain ⟨B, hB, hBbij⟩ := hinv
      have hBherm : conjTr σ B = B := hherm' B hB
      have hBne : B ≠ 0 := by
        intro hB0
        obtain ⟨x, hx⟩ := hBbij.2 (Pi.single (0 : Fin 3) 1)
        rw [hB0] at hx
        have hx' : (0 : Fin 3 → K) =
            (Pi.single (0 : Fin 3) (1 : K) : Fin 3 → K) := by
          simpa [Matrix.mulVecLin_zero] using hx
        have hsingle : (Pi.single (0 : Fin 3) (1 : K) : Fin 3 → K) ≠ 0 := by
          rw [Pi.single_ne_zero_iff]
          exact one_ne_zero
        exact hsingle hx'.symm
      have hline : ∀ D ∈ S, ∃ c : K, D = c • B := by
        intro D hD
        exact exists_smul_of_cross_of_invertible hσ hBherm (hherm' D hD) hBbij
          (hpol B hB D hD)
      exact le_trans (card_le_of_smul_line hK hσeq hBherm hBne hline hherm') hqle
    · by_cases hrank2 : ∃ B ∈ S, finrank K (LinearMap.range B.mulVecLin) = 2
      · obtain ⟨B, hB, hBrank⟩ := hrank2
        exact card_le_sq_of_rank_two hK hσ hσeq hB hBrank hherm' hpol
      · push Not at hzero hinv hrank2
        obtain ⟨B, hB, hBne⟩ := hzero
        have hrank_le_one : ∀ D ∈ S, finrank K (LinearMap.range D.mulVecLin) ≤ 1 := by
          intro D hD
          have hle3 : finrank K (LinearMap.range D.mulVecLin) ≤ 3 := by
            have h := Submodule.finrank_le (LinearMap.range D.mulVecLin)
            simpa using h
          have hne2 : finrank K (LinearMap.range D.mulVecLin) ≠ 2 := fun h => hrank2 D hD h
          have hne3 : finrank K (LinearMap.range D.mulVecLin) ≠ 3 := by
            intro h3
            apply hinv D hD
            have htop : LinearMap.range D.mulVecLin = ⊤ := by
              apply Submodule.eq_top_of_finrank_eq
              rw [h3]
              simp
            have hsurj : Function.Surjective D.mulVecLin := LinearMap.range_eq_top.mp htop
            have hinj : Function.Injective D.mulVecLin :=
              LinearMap.injective_iff_surjective.mpr hsurj
            exact ⟨hinj, hsurj⟩
          omega
        have hBrank : finrank K (LinearMap.range B.mulVecLin) = 1 := by
          have hle := hrank_le_one B hB
          have hpos : 0 < finrank K (LinearMap.range B.mulVecLin) := by
            obtain ⟨z, hz⟩ := exists_mulVec_ne_zero_of_ne_zero hBne
            have hmem : B *ᵥ z ∈ LinearMap.range B.mulVecLin := ⟨z, rfl⟩
            have hspan_le : (K ∙ (B *ᵥ z) : Submodule K (Fin 3 → K)) ≤
                LinearMap.range B.mulVecLin := by
              intro x hx
              obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
              exact Submodule.smul_mem _ a hmem
            have hf := Submodule.finrank_mono hspan_le
            rw [finrank_span_singleton hz] at hf
            omega
          omega
        have hline : ∀ D ∈ S, ∃ c : K, D = c • B := by
          intro D hD
          exact exists_smul_of_cross_of_rank_one hσ (hherm' B hB) (hherm' D hD) hBne
            hBrank (hrank_le_one D hD) (hpol B hB D hD)
        exact le_trans (card_le_of_smul_line hK hσeq (hherm' B hB) hBne hline hherm') hqle

end PartB

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
