module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalNoNormal
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.PSUTwoAux.Frame
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwoAux.Unitary
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.NonsplitGen
public import CFSG.RankThree.PartOne.KC.UnitaryInnerPlaneKernel
public import CFSG.RankThree.PartOne.KC.UnitaryOrthonormalEigenbasis
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityScalar
import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalNonsplit

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open Polynomial Module Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryScalar
  CFSG.RankThree.PartOne.KCUnitary
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo

section NoNormal

variable {f : ℕ} {K : Type} [Field K]

theorem noNormalPPrime_three_gramSU_two_eight (hE : UnitaryFieldData 2 f K)
    (hf : 2 ^ f = 2 ∨ 2 ^ f = 8) (m : ℕ) :
    NoNormalPPrime 3 (gramSU hE (idGram K m)) := by
  classical
  haveI := hE.finite
  have hG : ((idGram K m).map hE.bar)ᵀ = idGram K m := by
    simp [idGram, Matrix.map_one _ (map_zero hE.bar) (map_one hE.bar)]
  have hHs : (gramForm hE (idGram K m)).IsSymm := gramForm_isSymm hE hG
  have hHl : (gramForm hE (idGram K m)).SeparatingLeft :=
    gramForm_separatingLeft hE (by simp [idGram])
  obtain ⟨ψ⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE
    (Pi.basisFun K (Fin m)) (G := idGram K m) (fun i j => by
      rw [Pi.basisFun_apply, Pi.basisFun_apply]
      exact gramForm_single hE _ i j)
  have hN : NoNormalPPrime 3 (sesqSpecialUnitaryGroup (gramForm hE (idGram K m))) := by
    rcases hf with hf | hf
    · exact W2.noNormalPPrime_three_sesqSpecialUnitaryGroup hE hf hHs hHl
    · exact noNormalPPrime_three_sesqSpecialUnitaryGroup_eight hE hf hHs hHl
  rw [← W2.noNormalPPrime_top_iff] at hN ⊢
  exact W2.noNormalPPrime_top_of_mulEquiv ψ.symm hN

end NoNormal

section Abstract

variable {G H : Type*} [Group G] [Group H]

theorem eq_of_frame_conj {p : ℕ} (hNN : NoNormalPPrime p (⊤ : Subgroup G)) {Φ : G →* H}
    (hΦ : Function.Injective Φ) {x y : H} {N : Subgroup H} (hNc : Nat.Coprime p (Nat.card N))
    (hy : y ∈ N) (hNn : ∀ c : H, c * x = x * c → ∀ z ∈ N, c * z * c⁻¹ ∈ N)
    (hΦc : ∀ Y : G, Φ Y * x = x * Φ Y) {Y A : G} (hA : Φ A = y * Φ Y * y⁻¹) : A = Y := by
  set R : Subgroup G := N.comap Φ with hR
  have hRcop : Nat.Coprime p (Nat.card R) := by
    have h1 : Nat.card R ∣ Nat.card N := by
      rw [← Subgroup.card_map_of_injective hΦ]
      exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)
    exact hNc.coprime_dvd_right h1
  have hRn : ∀ Z : G, ∀ r ∈ R, Z * r * Z⁻¹ ∈ R := by
    intro Z r hr
    rw [hR, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hNn (Φ Z) (hΦc Z) (Φ r) (Subgroup.mem_comap.1 hr)
  have hRbot : R = ⊥ := hNN R le_top (fun Z _ r hr => hRn Z r hr) hRcop
  have hmem : A * Y⁻¹ ∈ R := by
    rw [hR, Subgroup.mem_comap, map_mul, map_inv, hA]
    have h1 := N.mul_mem hy (hNn (Φ Y) (hΦc Y) y⁻¹ (N.inv_mem hy))
    simpa only [mul_assoc] using h1
  rw [hRbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact hmem

end Abstract

section Scalar

variable {ℓ f n m : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem eigen_scalar_of_normal (hq : 2 ≤ ℓ ^ f) (hm : 1 ≤ m)
    (hNN : NoNormalPPrime 3 (gramSU h (idGram K m)))
    {x : gramSU h (idGram K n)} {N : Subgroup (gramSU h (idGram K n))}
    (hNc : Nat.Coprime 3 (Nat.card N))
    (hNx : ∀ y ∈ N, y * x = x * y)
    (hNn : ∀ c : gramSU h (idGram K n), c * x = x * c → ∀ y ∈ N, c * y * c⁻¹ ∈ N)
    {ν : K} (hν : h.bar ν * ν = 1) {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u)
    (hxu : ∀ i, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u i = ν • u i)
    (hspan : ∀ w, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = ν • w →
      w ∈ Submodule.span K (Set.range u))
    {y : gramSU h (idGram K n)} (hy : y ∈ N) :
    ∃ c : K, h.bar c * c = 1 ∧
      ∀ v, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = ν • v →
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v := by
  classical
  have hyx : toUnitary h n y * toUnitary h n x = toUnitary h n x * toUnitary h n y := by
    rw [← map_mul, ← map_mul, hNx y hy]
  obtain ⟨Ny, hN1, hN2⟩ := exists_frameConj hu (toUnitary h n x) (toUnitary h n y) hxu hspan hyx
  have hxA : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * frameMat u = ν • frameMat u := by
    ext k i
    rw [mul_frameMat_apply, hxu i]
    rfl
  have hxadj : adj h ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
    mem_primeFormUnitary_iff_adj.1 x.2.1
  have hBx : frameAdj h u * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ν • frameAdj h u := frameAdj_mul_eigen hν hxA hxadj
  have hΦcomm : ∀ Y : gramSU h (idGram K m), frameSU h hu Y * x = x * frameSU h hu Y := by
    intro Y
    apply Subtype.ext
    apply Units.ext
    exact (frameEmb_comm hxA hBx _).symm
  have hNN' : NoNormalPPrime 3 (⊤ : Subgroup (gramSU h (idGram K m))) :=
    (W2.noNormalPPrime_top_iff _).2 hNN
  have hcomm : ∀ Y : gramSU h (idGram K m),
      (Ny : GL (Fin m) K) * (Y : GL (Fin m) K) = (Y : GL (Fin m) K) * (Ny : GL (Fin m) K) := by
    intro Y
    let A : gramSU h (idGram K m) :=
      ⟨(Ny : GL (Fin m) K) * (Y : GL (Fin m) K) * (Ny : GL (Fin m) K)⁻¹,
        conj_mem_gramSU h _ Ny.2 Y.2⟩
    have hΦA : frameSU h hu A = y * frameSU h hu Y * y⁻¹ :=
      Subtype.ext (hN2 (Y : GL (Fin m) K)).symm
    have h2 := congrArg (fun z : gramSU h (idGram K m) => (z : GL (Fin m) K))
      (eq_of_frame_conj hNN' (frameSU_injective hu) hNc hy hNn hΦcomm hΦA)
    have h3 : (Ny : GL (Fin m) K) * (Y : GL (Fin m) K) * (Ny : GL (Fin m) K)⁻¹ =
        (Y : GL (Fin m) K) := h2
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3
  obtain ⟨c, hc⟩ : ∃ c : K, ((Ny : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      c • (1 : Matrix (Fin m) (Fin m) K) := by
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · obtain rfl : m = 1 := by omega
      refine ⟨((Ny : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) 0 0, ?_⟩
      ext i j
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      simp
    · refine exists_smul_one_of_commute_gramSU h hm2 hq (fun A hA => ?_)
      have := congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K))
        (hcomm ⟨A, hA⟩)
      exact this.symm
  have hNyu : adj h ((Ny : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
      ((Ny : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 :=
    mem_primeFormUnitary_iff_adj.1 Ny.2
  have hnorm : h.bar c * c = 1 := by
    rw [hc, adj_smul, adj_one, Matrix.smul_mul, Matrix.one_mul, smul_smul] at hNyu
    have := congrFun (congrFun hNyu ⟨0, hm⟩) ⟨0, hm⟩
    simpa using this
  refine ⟨c, hnorm, fun v hv => ?_⟩
  have hN1' : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * frameMat u =
      frameMat u * ((Ny : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := hN1
  have hva := frame_expand hu (hspan v hv)
  set a := frameAdj h u *ᵥ v with ha
  calc ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v
      = ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (frameMat u *ᵥ a) := by rw [hva]
    _ = (((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * frameMat u) *ᵥ a :=
        Matrix.mulVec_mulVec _ _ _
    _ = (frameMat u * ((Ny : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) *ᵥ a := by rw [hN1']
    _ = frameMat u *ᵥ (((Ny : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ a) := by
        rw [← Matrix.mulVec_mulVec]
    _ = frameMat u *ᵥ (c • a) := by rw [hc, smul_one_mulVec]
    _ = c • (frameMat u *ᵥ a) := Matrix.mulVec_smul _ _ _
    _ = c • v := by rw [hva]

end Scalar

section Frame

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem exists_eigen_frame (hpℓ : 3 ≠ ℓ) (hpq : 3 ∣ ℓ ^ f + 1) {x : gramSU h (idGram K n)}
    (hx : x ^ 3 = 1) {ν : K} {v₀ : Fin n → K} (hv₀ : v₀ ≠ 0)
    (hv₀e : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v₀ = ν • v₀) :
    h.bar ν * ν = 1 ∧ ∃ (m : ℕ) (u : Fin m → Fin n → K), 1 ≤ m ∧ IsOrthonormalFamily h u ∧
      (∀ i, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u i = ν • u i) ∧
      (∀ w, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = ν • w →
        w ∈ Submodule.span K (Set.range u)) := by
  classical
  have hxu : toUnitary h n x ^ 3 = 1 := by rw [← map_pow, hx, map_one]
  have hxgl : ((toUnitary h n x : primeFormUnitary h (idGram K n)) : GL (Fin n) K) ^ 3 =
      GeneralLinearGroup.scalar (Fin n) (1 : Kˣ) := by
    have := congrArg (fun y : primeFormUnitary h (idGram K n) => (y : GL (Fin n) K)) hxu
    simpa using this
  have H0 := primaryData_of_pow_eq_scalar Nat.prime_three hpℓ hxgl
  set xm : Matrix (Fin n) (Fin n) K := ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hxm
  set T : Module.End K (Fin n → K) := ((toLinU h n (toUnitary h n x) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) with hT
  have hTe : ∀ v, T v = xm *ᵥ v := fun v => rfl
  have hνp : ν ^ 3 = 1 := eigenvalue_pow_eq_one hxu hv₀ (by rw [hTe]; exact hv₀e)
  have hνb : h.bar ν * ν = 1 := bar_eq_inv_of_pow_eq_one h hpq hνp
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
  have hsep := separatingLeft_primaryComponent_selfDual H0 hmem (dualPoly_X_sub_C_self hνb)
  obtain ⟨u, huW, hu⟩ := KCUnitaryLines.exists_orthonormal_family hsep
    (m := Module.finrank K (primaryComponent T (X - C ν))) le_rfl
  refine ⟨hνb, _, u, hd1, hu, fun i => (hWmem (u i)).1 (huW i), fun w hw => ?_⟩
  rw [span_eq_of_orthonormal hu huW rfl]
  exact (hWmem w).2 hw

end Frame

section Pow

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem pow_eq_one_of_eigen_scalar (hpℓ : 3 ≠ ℓ) (hpq : 3 ∣ ℓ ^ f + 1)
    {Z : primeFormUnitary h (idGram K n)} (hZ : Z ^ 3 = 1) {M : GL (Fin n) K} {k : ℕ}
    (hM : ∀ ν : K, ∃ c : K, c ^ k = 1 ∧ ∀ v : Fin n → K,
      ((Z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = ν • v →
        (M : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v) : M ^ k = 1 := by
  classical
  have := h.finite
  have hZgl : (Z : GL (Fin n) K) ^ 3 = 1 := by
    have := congrArg (fun y : primeFormUnitary h (idGram K n) => (y : GL (Fin n) K)) hZ
    simpa using this
  have hZs : (Z : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) (1 : Kˣ) := by
    rw [hZgl, map_one]
  have H0 := primaryData_of_pow_eq_scalar Nat.prime_three hpℓ hZs
  obtain ⟨ω, hω⟩ := KCUnitaryPlane.exists_primitiveRoot_of_dvd h Nat.prime_three hpq
  set A : Matrix (Fin n) (Fin n) K := (M : Matrix (Fin n) (Fin n) K) with hA
  have hext : Matrix.toLin' (A ^ k) = LinearMap.id := by
    refine ext_primaryComponent H0.squarefree fun a ha v hv => ?_
    obtain ⟨ν, rfl⟩ := exists_eq_X_sub_C_of_mem_primaryFactors (p := 3) (by norm_num) hω hZgl ha
    have hZv : ((Z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = ν • v :=
      mem_primaryComponent_X_sub_C.1 hv
    obtain ⟨c, hck, hc⟩ := hM ν
    have hMv : A *ᵥ v = c • v := hc v hZv
    have hpow : ∀ j : ℕ, (A ^ j) *ᵥ v = c ^ j • v := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
    rw [Matrix.toLin'_apply, LinearMap.id_apply, hpow k, hck, one_smul]
  have hAk : A ^ k = 1 := by
    apply Matrix.toLin'.injective
    rw [hext, Matrix.toLin'_one]
  exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hAk)

end Pow

section Centralizer

variable {f n : ℕ} {K : Type} [Field K]

theorem noNormalPPrime_three_centralizer_gramSU (hE : UnitaryFieldData 2 f K)
    (hf : 2 ^ f = 2 ∨ 2 ^ f = 8) {x : gramSU hE (idGram K n)} (hx : x ^ 3 = 1) :
    NoNormalPPrime 3 (Subgroup.centralizer {x}) := by
  classical
  intro N hNC hNn hNc
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hq : 2 ≤ 2 ^ f := by rcases hf with hf | hf <;> omega
  have hpq : 3 ∣ 2 ^ f + 1 := by rcases hf with hf | hf <;> rw [hf] <;> norm_num
  have hpℓ : (3 : ℕ) ≠ 2 := by norm_num
  have hNx : ∀ z ∈ N, z * x = x * z := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.1 (hNC hz)
  have hNn' : ∀ c : gramSU hE (idGram K n), c * x = x * c → ∀ z ∈ N, c * z * c⁻¹ ∈ N :=
    fun c hc z hz => hNn c (Subgroup.mem_centralizer_singleton_iff.2 hc) z hz
  have hxu : toUnitary hE n x ^ 3 = 1 := by rw [← map_pow, hx, map_one]
  have hy1 : (y : GL (Fin n) K) ^ (2 ^ f + 1) = 1 := by
    refine pow_eq_one_of_eigen_scalar hpℓ hpq (Z := toUnitary hE n x) hxu fun ν => ?_
    by_cases hev : ∃ v : Fin n → K, v ≠ 0 ∧
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = ν • v
    · obtain ⟨v₀, hv₀, hv₀e⟩ := hev
      obtain ⟨hνb, m, u, hm, hu, hxu', hspan⟩ := exists_eigen_frame hpℓ hpq hx hv₀ hv₀e
      obtain ⟨c, hcb, hc⟩ := eigen_scalar_of_normal hq hm
        (noNormalPPrime_three_gramSU_two_eight hE hf m) hNc hNx hNn' hνb hu hxu' hspan hy
      refine ⟨c, ?_, hc⟩
      rw [UnitaryFieldData.bar_apply, ← pow_succ] at hcb
      exact hcb
    · refine ⟨1, one_pow _, fun v hv => ?_⟩
      have hv0 : v = 0 := by
        by_contra hv0
        exact hev ⟨v, hv0, hv⟩
      simp [hv0]
  have hyk : y ^ (2 ^ f + 1) = 1 := Subtype.ext (by simpa using hy1)
  have hord1 : orderOf y ∣ 2 ^ f + 1 := orderOf_dvd_of_pow_eq_one hyk
  have hord2 : orderOf y ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hy
  have hcop : Nat.Coprime (2 ^ f + 1) (Nat.card N) := by
    rcases hf with hf | hf <;> rw [hf]
    · simpa using hNc
    · simpa using Nat.Coprime.pow_left 2 hNc
  exact orderOf_eq_one_iff.1 ((hcop.coprime_dvd_left hord1).eq_one_of_dvd hord2)

end Centralizer

end CFSG.HardMathSupport.Dickson.Bal207

end
