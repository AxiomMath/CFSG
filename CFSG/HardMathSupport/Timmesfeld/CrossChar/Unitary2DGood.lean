module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalNonsplit

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryLines CFSG.RankThree.PartOne.KCUnitaryOne
  CFSG.RankThree.PartOne.KCUnitaryFrame CFSG.RankThree.PartOne.KCUnitaryBlock
  CFSG.RankThree.PartOne.KCUnitaryScalar CFSG.RankThree.PartOne.KCUnitaryPair
  CFSG.HardMathSupport.Timmesfeld.Balance

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem good_eigen_data (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hq : ℓ ^ f = 2)
    {x : primeFormUnitary h (idGram K n)} (hx : x ^ 3 = 1) {ν : K}
    (hdim : 4 ≤ Module.finrank K (primaryComponent ((toLinU h n x :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (X - C ν))) :
    ∃ (_ : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n x))
      (hmem : (X - C ν : K[X]) ∈ primaryFactors ((toLinU h n x :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))),
      IsGoodBlock h (toLinU h n x) ⟨X - C ν, hmem⟩ ∧ h.bar ν * ν = 1 ∧
      3 ∣ Nat.card ((gBlock h x (X - C ν)).map (primeFormConjHom h (idGram K n))) ∧
      ∃ e : Fin 3 → Fin n → K, IsOrthonormalFamily h e ∧
        ∀ i, ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          Module.End K (Fin n → K)) (e i) = ν • e i := by
  classical
  have := h.finite
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hℓ : ℓ = 2 := by
    have : ℓ ∣ 2 := hq ▸ dvd_pow_self ℓ (by have := h.one_le; omega)
    exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this
  have hpℓ : 3 ≠ ℓ := by omega
  have hpq : 3 ∣ ℓ ^ f + 1 := by rw [hq]
  have hxgl : (x : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) (1 : Kˣ) := by
    have := congrArg (fun y : primeFormUnitary h (idGram K n) => (y : GL (Fin n) K)) hx
    simpa using this
  have H0 := primaryData_of_pow_eq_scalar hp3 hpℓ hxgl
  have hsq := H0.squarefree
  set T : Module.End K (Fin n → K) := ((toLinU h n x :
    LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) with hT
  have hdim2 : 4 ≤ Module.finrank K (primaryComponent ((toLinU h n x :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (X - C ν)) := hdim
  have hW : primaryComponent T (X - C ν) ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hdim
    omega
  obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hv₀eig := mem_primaryComponent_X_sub_C.mp hv₀
  have hνp : ν ^ 3 = 1 := eigenvalue_pow_eq_one hx hv₀0 hv₀eig
  have hνb : h.bar ν * ν = 1 := bar_eq_inv_of_pow_eq_one h hpq hνp
  have hev : Module.End.HasEigenvalue T ν :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hv₀eig, hv₀0⟩
  have hmem := X_sub_C_mem_primaryFactors hev
  have hsep := separatingLeft_primaryComponent_selfDual H0 hmem (dualPoly_X_sub_C_self hνb)
  obtain ⟨e, he_mem, he_on⟩ := exists_orthonormal_triple hsep (by omega)
  have hSe : ∀ i, T (e i) = ν • e i := fun i => mem_primaryComponent_X_sub_C.mp (he_mem i)
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have hgood : IsGoodBlock h (toLinU h n x) ⟨X - C ν, hmem⟩ := by
    refine isGoodBlock_X_sub_C (hK := h) hmem (by omega) ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or, hq]
    omega
  obtain ⟨ζ, hζ, hζn⟩ := exists_norm_one_primitiveRoot (h := h) hp3 hpq
  have hcard := dvd_card_map_gBlock_of_torus hp3 (by omega) hn hne H0 hνb hmem (he_on.pair h01)
    (hSe 0) (hSe 1) hζ hζn
  exact ⟨H0, hmem, hgood, hνb, hcard, e, he_on, hSe⟩

theorem commute_gBlock_of_good_eigen (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hq : ℓ ^ f = 2) {x : primeFormUnitary h (idGram K n)} (hx : x ^ 3 = 1) {ν : K}
    (hdim : 4 ≤ Module.finrank K (primaryComponent ((toLinU h n x :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (X - C ν)))
    {E H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H)
    {g : MulAut (primeFormP h (idGram K n))} (hg : g ∈ localDeltaIn 3 H E)
    (hxE : primeFormConjHom h (idGram K n) x ∈ E) (hx1 : primeFormConjHom h (idGram K n) x ≠ 1) :
    ∀ Y ∈ gBlock h x (X - C ν),
      g * primeFormConjHom h (idGram K n) Y = primeFormConjHom h (idGram K n) Y * g := by
  obtain ⟨H0, hmem, hgood, -, hcard, -⟩ := good_eigen_data hn hne hq hx hdim
  exact commute_of_mem_localDeltaIn_gBlock Nat.prime_three hn hne (by omega) H0 ⟨X - C ν, hmem⟩
    hgood hH hg hxE hx1 hcard

theorem good_eigen_tau (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hq : ℓ ^ f = 2)
    {x : primeFormUnitary h (idGram K n)} (hx : x ^ 3 = 1) {ν : K}
    (hdim : 4 ≤ Module.finrank K (primaryComponent ((toLinU h n x :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (X - C ν)))
    {E H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H)
    {M : primeFormUnitary h (idGram K n)} {τ : K ≃+* K}
    (hg : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩ ∈ localDeltaIn 3 H E)
    (hxE : primeFormConjHom h (idGram K n) x ∈ E) (hx1 : primeFormConjHom h (idGram K n) x ≠ 1) :
    τ = RingEquiv.refl K := by
  obtain ⟨H0, hmem, hgood, hνb, -, e, he_on, hSe⟩ := good_eigen_data hn hne hq hx hdim
  have hβ := commute_gBlock_of_good_eigen hn hne hq hx hdim hH hg hxE hx1
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hq2 : 2 ≤ ℓ ^ f := by omega
  have hTC01 := torusComm_of_block hn hne hq2 H0 hνb hmem hgood (he_on.pair h01) (hSe 0) (hSe 1)
    M τ hβ
  have hTC02 := torusComm_of_block hn hne hq2 H0 hνb hmem hgood (he_on.pair h02) (hSe 0) (hSe 2)
    M τ hβ
  exact tau_eq_one_of_torus h (M : GL (Fin n) K).isUnit (he_on.pair h01) (he_on.pair h02)
    (he_on.linearIndependent_triple h01 h02 h12) hTC01 hTC02

theorem good_eigen_scalar (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hq : ℓ ^ f = 2)
    {x : primeFormUnitary h (idGram K n)} (hx : x ^ 3 = 1) {ν : K}
    (hdim : 4 ≤ Module.finrank K (primaryComponent ((toLinU h n x :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (X - C ν)))
    {E H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H)
    {M : primeFormUnitary h (idGram K n)}
    (hg : primeFormConjHom h (idGram K n) M ∈ localDeltaIn 3 H E)
    (hxE : primeFormConjHom h (idGram K n) x ∈ E) (hx1 : primeFormConjHom h (idGram K n) x ≠ 1)
    (hMx : M * x = x * M) :
    ∃ c : K, ∀ v : Fin n → K, ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = ν • v →
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v := by
  obtain ⟨H0, hmem, hgood, -, -, -⟩ := good_eigen_data hn hne hq hx hdim
  have hg' : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, RingEquiv.refl K⟩ ∈
      localDeltaIn 3 H E := by
    rw [psi_refl_eq]
    exact hg
  have hβ := commute_gBlock_of_good_eigen hn hne hq hx hdim hH hg' hxE hx1
  have hF : Group.IsPerfect (gBlock h x (X - C ν)) :=
    (isQuasisimple_gBlock (by omega) H0 ⟨X - C ν, hmem⟩ hgood).1
  have hblock : ∀ Y ∈ gBlock h x (X - C ν), M * Y = Y * M := by
    intro Y hY
    have := matrix_comm_of_perfect hn hne hF M (RingEquiv.refl K) hβ Y hY
    rw [hmat_refl] at this
    exact Subtype.ext (Units.ext this)
  exact exists_scalar_of_commute_gBlock_X_sub_C (by omega) H0 hmem hgood M hMx hblock

end CFSG.HardMathSupport.Timmesfeld.CrossChar
