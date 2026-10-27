module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.PSUTwoAux.Basic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.PSUTwoAux.SmallSU
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.PSUTwoAux.Frame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DBase
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DCube
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DGood
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalOuter

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo

open Polynomial Module Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryScalar
  CFSG.RankThree.PartOne.KCUnitary

variable {ℓ f n m : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem exists_perp_frame (u : Fin m → Fin n → K) (hmn : m < n) :
    ∃ w : Fin n → K, w ≠ 0 ∧ frameAdj h u *ᵥ w = 0 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (frameAdj h u))
  have h2 : Module.finrank K (LinearMap.range (Matrix.toLin' (frameAdj h u))) ≤ m := by
    have := Submodule.finrank_le (LinearMap.range (Matrix.toLin' (frameAdj h u)))
    simpa using this
  have h3 : 0 < Module.finrank K (LinearMap.ker (Matrix.toLin' (frameAdj h u))) := by
    simp only [Module.finrank_fin_fun] at h1
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.mp h3)
  exact ⟨w, hw0, by simpa [Matrix.toLin'_apply] using hw⟩

section Small

theorem small_eigen_scalar (hn : 4 ≤ n) (hq : ℓ ^ f = 2) (hm : m = 2 ∨ m = 3)
    {D H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →* MulAut (primeFormP h (idGram K n))).range ≤ H)
    {x M : primeFormUnitary h (idGram K n)}
    (hxD : primeFormConjHom h (idGram K n) x ∈ D) (hx1 : primeFormConjHom h (idGram K n) x ≠ 1)
    (hg : primeFormConjHom h (idGram K n) M ∈ localDeltaIn 3 H D) (hMx : M * x = x * M)
    {ν : K} (hν : h.bar ν * ν = 1) {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u)
    (hxu : ∀ i, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u i = ν • u i)
    (hspan : ∀ w, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = ν • w →
      w ∈ Submodule.span K (Set.range u)) :
    ∃ c : K, ∀ v, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = ν • v →
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v := by
  classical
  have hfin := h.finite
  have hℓ : ℓ = 2 := by
    have : ℓ ∣ 2 := hq ▸ dvd_pow_self ℓ (by have := h.one_le; omega)
    exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this
  subst hℓ
  have hmn : m < n := by omega
  have hm2 : 2 ≤ m := by omega
  have hn3 : 3 ≤ n := by omega
  have hne : ¬(n = 3 ∧ 2 ^ f = 2) := fun h' => by omega
  set ρn := primeFormConjHom h (idGram K n) with hρn
  set xm : Matrix (Fin n) (Fin n) K := ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hxm
  obtain ⟨N, hN1, hN2⟩ := exists_frameConj hu x M hxu hspan hMx
  obtain ⟨w, hw0, hw⟩ := exists_perp_frame (h := h) u hmn
  have hxA : xm * frameMat u = ν • frameMat u := by
    ext k i
    rw [mul_frameMat_apply, hxu i]
    rfl
  have hxadj : adj h xm * xm = 1 := mem_primeFormUnitary_iff_adj.1 x.2
  have hBx : frameAdj h u * xm = ν • frameAdj h u := frameAdj_mul_eigen hν hxA hxadj
  let Φ : gramSU h (idGram K m) →* gramSU h (idGram K n) := frameSU h hu
  let ι : gramSU h (idGram K m) →* MulAut (primeFormP h (idGram K n)) :=
    ρn.comp ((toUnitary h n).comp Φ)
  have hιconj : ∀ Y, ι Y = MulAut.conj ((Φ Y : gramSU h (idGram K n)) :
      primeFormP h (idGram K n)) := fun Y => primeFormConjHom_eq_conj h _ (Φ Y)
  have hιH : ∀ Y, ι Y ∈ H := fun Y => by
    rw [hιconj]
    exact hH ⟨_, rfl⟩
  have hιcomm : ∀ Y, ι Y * ρn x = ρn x * ι Y := fun Y => by
    change ρn (toUnitary h n (Φ Y)) * ρn x = ρn x * ρn (toUnitary h n (Φ Y))
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    exact (frameEmb_comm hxA hBx _).symm
  have hιC : ∀ Y, ι Y ∈ H ⊓ Subgroup.centralizer ({ρn x} : Set (MulAut (primeFormP h (idGram K n)))) :=
    fun Y => ⟨hιH Y, Subgroup.mem_centralizer_singleton_iff.2 (hιcomm Y)⟩
  have hιinj : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro Y hY
    rw [Subgroup.mem_bot]
    have hY1 : ρn (toUnitary h n (Φ Y)) = 1 := hY
    rw [primeFormConjHom_eq_one_iff_of_ne hn3 hne] at hY1
    obtain ⟨c, -, hc⟩ := hY1
    have hmat : frameEmb h u ((Y : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
        (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
      rw [← scalar_coe_eq_smul_one, ← this]
      rfl
    have h1 := frameEmb_mulVec_of_adj_eq_zero (h := h) (u := u)
      ((Y : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) hw
    rw [hmat, smul_one_mulVec] at h1
    have hc1 : (c : K) = 1 := by
      by_contra hc1
      have : ((c : K) - 1) • w = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      rcases smul_eq_zero.1 this with h2 | h2
      · exact hc1 (sub_eq_zero.1 h2)
      · exact hw0 h2
    rw [hc1, one_smul] at hmat
    have : frameEmb h u ((Y : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = frameEmb h u 1 := by
      rw [hmat, frameEmb_one]
    exact Subtype.ext (Units.ext (frameEmb_injective hu this))
  have hcore : ρn M ∈ GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer
      ({ρn x} : Set (MulAut (primeFormP h (idGram K n))))) :=
    le_core_of_mem_localDeltaIn hg hxD hx1
  set R : Subgroup (gramSU h (idGram K m)) := (GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer
      ({ρn x} : Set (MulAut (primeFormP h (idGram K n)))))).comap ι with hR
  have hRcop : Nat.Coprime 3 (Nat.card R) := by
    have hle : R.map ι ≤ GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer
        ({ρn x} : Set (MulAut (primeFormP h (idGram K n))))) := Subgroup.map_comap_le _ _
    have h1 : Nat.card R ∣ Nat.card (GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer
        ({ρn x} : Set (MulAut (primeFormP h (idGram K n)))))) := by
      rw [← Subgroup.card_map_of_injective hιinj]
      exact Subgroup.card_dvd_of_le hle
    exact (coprime_card_gLAPPrimeCoreOf' Nat.prime_three _).coprime_dvd_right h1
  have hRbot : R = ⊥ := by
    have hNN : NoNormalPPrime 3 (gramSU h (idGram K m)) :=
      noNormalPPrime_three_gramSU_of_mem h hq hm
    have h1 : R.map (gramSU h (idGram K m)).subtype = ⊥ := by
      refine hNN _ (Subgroup.map_subtype_le R) ?_ ?_
      · rintro y hy _ ⟨r, hr, rfl⟩
        have hr' : r ∈ R := hr
        refine ⟨⟨y, hy⟩ * r * ⟨y, hy⟩⁻¹, ?_, by simp⟩
        show _ ∈ R
        rw [hR, Subgroup.mem_comap, map_mul, map_mul, map_inv]
        exact gLAPPrimeCoreOf_conj_mem' _ (hιC _) _ (Subgroup.mem_comap.1 hr')
      · rw [Subgroup.card_map_of_injective (gramSU h (idGram K m)).subtype_injective]
        exact hRcop
    exact (Subgroup.map_eq_bot_iff_of_injective R
      (gramSU h (idGram K m)).subtype_injective).1 h1
  have hcomm : ∀ Y : gramSU h (idGram K m),
      (N : GL (Fin m) K) * (Y : GL (Fin m) K) = (Y : GL (Fin m) K) * (N : GL (Fin m) K) := by
    intro Y
    let A : gramSU h (idGram K m) :=
      ⟨(N : GL (Fin m) K) * (Y : GL (Fin m) K) * (N : GL (Fin m) K)⁻¹,
        conj_mem_gramSU h _ N.2 Y.2⟩
    have hιA : ι A = ρn M * ι Y * (ρn M)⁻¹ := by
      have : toUnitary h n (Φ A) = M * toUnitary h n (Φ Y) * M⁻¹ := by
        apply Subtype.ext
        change ((frameGL h hu (A : GL (Fin m) K) : GL (Fin n) K)) =
          (M : GL (Fin n) K) * ((frameGL h hu (Y : GL (Fin m) K) : GL (Fin n) K)) *
            (M : GL (Fin n) K)⁻¹
        rw [hN2]
      change ρn (toUnitary h n (Φ A)) = _
      rw [this, map_mul, map_mul, map_inv]
      rfl
    have hmem : ι (A * Y⁻¹) ∈ GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer
        ({ρn x} : Set (MulAut (primeFormP h (idGram K n))))) := by
      rw [map_mul, map_inv, hιA]
      exact commutator_mem_core hcore (hιC Y)
    have h1 : A * Y⁻¹ ∈ R := hmem
    rw [hRbot, Subgroup.mem_bot, mul_inv_eq_one] at h1
    have h2 := congrArg (fun z : gramSU h (idGram K m) => (z : GL (Fin m) K)) h1
    have h3 : (N : GL (Fin m) K) * (Y : GL (Fin m) K) * (N : GL (Fin m) K)⁻¹ =
        (Y : GL (Fin m) K) := h2
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3
  have hcommM : ∀ A ∈ gramSU h (1 : Matrix (Fin m) (Fin m) K),
      Commute (A : Matrix (Fin m) (Fin m) K) ((N : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
    intro A hA
    have := congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K))
      (hcomm ⟨A, hA⟩)
    exact this.symm
  obtain ⟨c, hc⟩ := CFSG.RankThree.PartOne.KCUnitary.exists_smul_one_of_commute_gramSU h hm2 (by rw [hq]) hcommM
  refine ⟨c, fun v hv => ?_⟩
  have hva := frame_expand hu (hspan v hv)
  set a := frameAdj h u *ᵥ v with ha
  calc ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v
      = ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (frameMat u *ᵥ a) := by rw [hva]
    _ = (((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * frameMat u) *ᵥ a :=
        Matrix.mulVec_mulVec _ _ _
    _ = (frameMat u * ((N : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) *ᵥ a := by rw [hN1]
    _ = frameMat u *ᵥ (((N : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ a) := by
        rw [← Matrix.mulVec_mulVec]
    _ = frameMat u *ᵥ (c • a) := by rw [hc, smul_one_mulVec]
    _ = c • (frameMat u *ᵥ a) := Matrix.mulVec_smul _ _ _
    _ = c • v := by rw [hva]

end Small

section Inner

theorem eigen_scalar_of_finrank_eq_one {xm Mm : Matrix (Fin n) (Fin n) K} {ν : K}
    (hcomm : xm * Mm = Mm * xm)
    (hd : Module.finrank K (primaryComponent (Matrix.toLin' xm) (X - C ν)) = 1) :
    ∃ c : K, ∀ v, xm *ᵥ v = ν • v → Mm *ᵥ v = c • v := by
  obtain ⟨v₀, hv₀0, hv₀⟩ := finrank_eq_one_iff'.1 hd
  have h1 : Matrix.toLin' Mm (v₀ : Fin n → K) ∈
      primaryComponent (Matrix.toLin' xm) (X - C ν) := by
    have hv₀e : xm *ᵥ (v₀ : Fin n → K) = ν • (v₀ : Fin n → K) := by
      have := mem_primaryComponent_X_sub_C.1 v₀.2
      simpa using this
    rw [mem_primaryComponent_X_sub_C]
    simp only [Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hv₀e, Matrix.mulVec_smul]
  obtain ⟨c, hc⟩ := hv₀ ⟨_, h1⟩
  have hc' : c • (v₀ : Fin n → K) = Mm *ᵥ (v₀ : Fin n → K) :=
    congrArg Subtype.val hc
  refine ⟨c, fun v hv => ?_⟩
  have hvW : v ∈ primaryComponent (Matrix.toLin' xm) (X - C ν) := by
    rw [mem_primaryComponent_X_sub_C]
    simpa using hv
  obtain ⟨t, ht⟩ := hv₀ ⟨v, hvW⟩
  have ht' : t • (v₀ : Fin n → K) = v := congrArg Subtype.val ht
  rw [← ht', Matrix.mulVec_smul, ← hc', smul_comm]

theorem eq_one_of_mem_localDeltaIn_inner (hn : 4 ≤ n) (hq : ℓ ^ f = 2)
    {D H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →* MulAut (primeFormP h (idGram K n))).range ≤ H)
    {x : primeFormUnitary h (idGram K n)} (hx : x ^ 3 = 1)
    (hxD : primeFormConjHom h (idGram K n) x ∈ D) (hx1 : primeFormConjHom h (idGram K n) x ≠ 1)
    {M : primeFormUnitary h (idGram K n)}
    (hg : primeFormConjHom h (idGram K n) M ∈ localDeltaIn 3 H D) :
    primeFormConjHom h (idGram K n) M = 1 := by
  classical
  have hfin := h.finite
  have hn3 : 3 ≤ n := by omega
  have hne : ¬(n = 3 ∧ ℓ ^ f = 2) := fun h' => by omega
  have : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have hcop := coprime_orderOf_of_mem_localDeltaIn Nat.prime_three hg hxD hx1
  have hMx : M * x = x * M := commute_of_commute_psi_coprime hn3 hne hq hcop
    (commute_of_mem_localDeltaIn hg hxD)
  have hℓ : ℓ = 2 := by
    have : ℓ ∣ 2 := hq ▸ dvd_pow_self ℓ (by have := h.one_le; omega)
    exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this
  have hpℓ : 3 ≠ ℓ := by omega
  have hpq : 3 ∣ ℓ ^ f + 1 := by rw [hq]
  have hxgl : (x : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) (1 : Kˣ) := by
    have := congrArg (fun y : primeFormUnitary h (idGram K n) => (y : GL (Fin n) K)) hx
    simpa using this
  have H0 := primaryData_of_pow_eq_scalar Nat.prime_three hpℓ hxgl
  set xm : Matrix (Fin n) (Fin n) K := ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hxm
  set Mm : Matrix (Fin n) (Fin n) K := ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hMm
  have hxM : xm * Mm = Mm * xm :=
    (congrArg (fun g : primeFormUnitary h (idGram K n) => ((g : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) hMx).symm
  have hM3 : M ^ 3 = 1 := by
    refine pow_three_eq_one_of_eigen_scalar hq hx (fun ν => ?_)
    by_cases hev : ∃ v : Fin n → K, v ≠ 0 ∧ xm *ᵥ v = ν • v
    swap
    · refine ⟨0, fun v hv => ?_⟩
      by_cases hv0 : v = 0
      · simp [hv0]
      · exact absurd ⟨v, hv0, hv⟩ hev
    obtain ⟨v₀, hv₀, hv₀e⟩ := hev
    have hνp : ν ^ 3 = 1 := eigenvalue_pow_eq_one hx hv₀ hv₀e
    have hνb : h.bar ν * ν = 1 := bar_eq_inv_of_pow_eq_one h hpq hνp
    set T : Module.End K (Fin n → K) := ((toLinU h n x :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) with hT
    have hTe : ∀ v, T v = xm *ᵥ v := fun v => rfl
    have hHasEig : T.HasEigenvalue ν :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr (by rw [hTe]; exact hv₀e), hv₀⟩
    have hmem := X_sub_C_mem_primaryFactors hHasEig
    have hWmem : ∀ v, v ∈ primaryComponent T (X - C ν) ↔ xm *ᵥ v = ν • v := fun v => by
      rw [mem_primaryComponent_X_sub_C, hTe]
    have hd1 : 1 ≤ Module.finrank K (primaryComponent T (X - C ν)) :=
      Submodule.one_le_finrank_iff.2 (fun hbot => hv₀ (by
        have : v₀ ∈ primaryComponent T (X - C ν) := (hWmem v₀).2 hv₀e
        rw [hbot] at this
        exact (Submodule.mem_bot K).1 this))
    rcases Nat.lt_or_ge (Module.finrank K (primaryComponent T (X - C ν))) 4 with hlt | hge
    · rcases (by omega : Module.finrank K (primaryComponent T (X - C ν)) = 1 ∨
          Module.finrank K (primaryComponent T (X - C ν)) = 2 ∨
          Module.finrank K (primaryComponent T (X - C ν)) = 3) with hd | hd | hd
      · exact eigen_scalar_of_finrank_eq_one hxM hd
      all_goals
        have hsep := separatingLeft_primaryComponent_selfDual H0 hmem
          (dualPoly_X_sub_C_self hνb)
        obtain ⟨u, huW, hu⟩ := KCUnitaryLines.exists_orthonormal_family hsep
          (m := Module.finrank K (primaryComponent T (X - C ν))) le_rfl
        exact small_eigen_scalar hn hq (by omega) hH hxD hx1 hg hMx hνb hu
          (fun i => (hWmem (u i)).1 (huW i))
          (fun w hw => by
            rw [span_eq_of_orthonormal hu huW rfl]
            exact (hWmem w).2 hw)
    · exact good_eigen_scalar hn3 hne hq hx hge hH hg hxD hx1 hMx
  have h3 : primeFormConjHom h (idGram K n) M ^ 3 = 1 := by rw [← map_pow, hM3, map_one]
  have h4 : orderOf (primeFormConjHom h (idGram K n) M) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop.symm h4)

end Inner

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo
