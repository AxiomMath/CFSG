module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryPow

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3

open Matrix CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.SeitzGeneration.Centers
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryAux

section Lifts

variable {ℓ f n : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem smul_def_gu (h : UnitaryFieldData ℓ f K) (A : primeFormUnitary h (idGram K n))
    (v : Fin n → K) : A • v = ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v := rfl

theorem herm_mulVec_gu (h : UnitaryFieldData ℓ f K) {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h (idGram K n)) (u v : Fin n → K) :
    herm σ₀ ((A : Matrix (Fin n) (Fin n) K) *ᵥ u) ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      herm σ₀ u v := by
  have h1 := (toLin_mem_sesqUnitaryGroup_iff (h := h) A).2 hA
  rw [mem_sesqUnitaryGroup] at h1
  have h2 := h1 u v
  rw [Nonsplit.idForm_eq_herm h, Nonsplit.idForm_eq_herm h] at h2
  simpa [Matrix.toLin'_apply] using h2

theorem herm_smul_smul_gu (h : UnitaryFieldData ℓ f K) (A : primeFormUnitary h (idGram K n))
    (u v : Fin n → K) : herm σ₀ (A • u) (A • v) = herm σ₀ u v :=
  herm_mulVec_gu h A.2 u v

theorem coe_comm_gu (h : UnitaryFieldData ℓ f K) {x s : primeFormUnitary h (idGram K n)}
    (hxs : x * s = s * x) :
    ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((s : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have := congrArg (fun g : primeFormUnitary h (idGram K n) =>
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hxs
  simpa only [Subgroup.coe_mul, Units.val_mul] using this

theorem coe_pow_mul_pow_gu (h : UnitaryFieldData ℓ f K) (x s : primeFormUnitary h (idGram K n))
    (a b : ℕ) :
    (((x ^ a * s ^ b : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ a *
        ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ b := by
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val]

theorem pow_word_of_comm_gu (h : UnitaryFieldData ℓ f K) {p : ℕ}
    {x s : primeFormUnitary h (idGram K n)} (hxs : x * s = s * x) {α β : K}
    (hxp : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = α • 1)
    (hsp : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1) (a b : ℕ) :
    (((x ^ a * s ^ b : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) ^ p = (α ^ a * β ^ b) • 1 := by
  have hc : Commute ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := coe_comm_gu h hxs
  rw [coe_pow_mul_pow_gu, (hc.pow_pow a b).mul_pow, ← pow_mul, ← pow_mul, mul_comm a p,
    mul_comm b p, pow_mul, pow_mul, hxp, hsp, smul_pow, smul_pow, one_pow, one_pow,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]

theorem bar_mul_eq_one_of_gu_scalar (h : UnitaryFieldData ℓ f K) (hn : 0 < n)
    {s : primeFormUnitary h (idGram K n)} {k : ℕ} {β : K}
    (hsk : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ k = β • 1) : h.bar β * β = 1 := by
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  have h1 := herm_smul_smul_gu h (s ^ k) (Pi.single ⟨0, hn⟩ 1) (Pi.single ⟨0, hn⟩ 1)
  rw [smul_def_gu, Subgroup.coe_pow, Units.val_pow_eq_pow_val, hsk, Matrix.smul_mulVec,
    Matrix.one_mulVec, herm_smul_left, herm_smul_right, herm_single_left, map_one, one_mul,
    Pi.single_eq_same, mul_one] at h1
  rw [← hσb]
  simpa using h1

theorem bar_mul_eq_one_of_gu_pow (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) (hn : 0 < n) {s : primeFormUnitary h (idGram K n)}
    {ν : K} (hν : ν ≠ 0)
    (hsp : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ν ^ p) • 1) :
    h.bar ν * ν = 1 := by
  have hνpN : h.bar (ν ^ p) * ν ^ p = 1 := bar_mul_eq_one_of_gu_scalar h hn hsp
  exact bar_mul_eq_one_of_pow_eq h hp hp2 hpq hν rfl (planeW_pow_card_succ h hνpN)

theorem herm_eq_zero_of_eigen_gu (h : UnitaryFieldData ℓ f K)
    {s : primeFormUnitary h (idGram K n)} {u v : Fin n → K} {l₁ l₂ : K}
    (hu : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u = l₁ • u)
    (hv : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = l₂ • v)
    (hl : σ₀ l₁ * l₂ ≠ 1) : herm σ₀ u v = 0 := by
  have h1 := herm_smul_smul_gu h s u v
  rw [smul_def_gu, smul_def_gu, hu, hv, herm_smul_left, herm_smul_right] at h1
  have h2 : (σ₀ l₁ * l₂ - 1) * herm σ₀ u v = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (sub_eq_zero.1 h3) hl
  · exact h3

end Lifts

section Ext

variable {ℓ f n m : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

variable (h : UnitaryFieldData ℓ f K)

theorem resMat_mulVec_eq_gu {x : Fin m → Fin n → K} (hx : ONExt.IsON σ₀ x)
    {s : primeFormUnitary h (idGram K n)} {c d : Fin m → K}
    (hd : s • orthoEmb x c = orthoEmb x d) :
    ONExt.resMat σ₀ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c = d :=
  resMat_mulVec_of_eq hx hd

theorem orthoEmb_resMat_mulVec_gu {x : Fin m → Fin n → K} (hx : ONExt.IsON σ₀ x)
    {s : primeFormUnitary h (idGram K n)} (hs : ∀ c, ∃ d, s • orthoEmb x c = orthoEmb x d)
    (c : Fin m → K) :
    orthoEmb x (ONExt.resMat σ₀ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c) =
      s • orthoEmb x c := by
  obtain ⟨d, hd⟩ := hs c
  rw [resMat_mulVec_eq_gu h hx hd, hd]

theorem resMat_mul_gu {x : Fin m → Fin n → K} (hx : ONExt.IsON σ₀ x)
    {s t : primeFormUnitary h (idGram K n)} (hs : ∀ c, ∃ d, s • orthoEmb x c = orthoEmb x d)
    (ht : ∀ c, ∃ d, t • orthoEmb x c = orthoEmb x d) :
    ONExt.resMat σ₀ x (((s * t : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
      ONExt.resMat σ₀ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ONExt.resMat σ₀ x ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← mulVec_mulVec]
  apply ONExt.orthoEmb_injective hx
  have hst : ∀ c, ∃ d, (s * t) • orthoEmb x c = orthoEmb x d := fun c => by
    obtain ⟨d, hd⟩ := ht c
    obtain ⟨d', hd'⟩ := hs d
    exact ⟨d', by rw [mul_smul, hd, hd']⟩
  rw [orthoEmb_resMat_mulVec_gu h hx hst, orthoEmb_resMat_mulVec_gu h hx hs,
    orthoEmb_resMat_mulVec_gu h hx ht, mul_smul]

theorem resMat_one_gu {x : Fin m → Fin n → K} (hx : ONExt.IsON σ₀ x) :
    ONExt.resMat σ₀ x (((1 : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 := by
  rw [show (((1 : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 from rfl, ONExt.resMat, Matrix.mul_one,
    ONExt.coordMat_mul_colMat hx]

theorem resMat_pow_gu {x : Fin m → Fin n → K} (hx : ONExt.IsON σ₀ x)
    {s : primeFormUnitary h (idGram K n)} (hs : ∀ c, ∃ d, s • orthoEmb x c = orthoEmb x d)
    (k : ℕ) :
    ONExt.resMat σ₀ x (((s ^ k : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
      ONExt.resMat σ₀ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ k := by
  have hsk : ∀ k : ℕ, ∀ c, ∃ d, (s ^ k) • orthoEmb x c = orthoEmb x d := by
    intro k
    induction k with
    | zero => exact fun c => ⟨c, by rw [pow_zero, one_smul]⟩
    | succ k ih =>
      intro c
      obtain ⟨d, hd⟩ := hs c
      obtain ⟨d', hd'⟩ := ih d
      exact ⟨d', by rw [pow_succ, mul_smul, hd, hd']⟩
  induction k with
  | zero => rw [pow_zero, pow_zero, resMat_one_gu h hx]
  | succ k ih => rw [pow_succ, resMat_mul_gu h hx (hsk k) hs, ih, pow_succ]

theorem herm_resMat_gu {x : Fin m → Fin n → K} (hx : ONExt.IsON σ₀ x)
    {s : primeFormUnitary h (idGram K n)} (hs : ∀ c, ∃ d, s • orthoEmb x c = orthoEmb x d)
    (c d : Fin m → K) :
    herm σ₀ (ONExt.resMat σ₀ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c)
      (ONExt.resMat σ₀ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ d) =
        herm σ₀ c d := by
  rw [← herm_orthoEmb hx, orthoEmb_resMat_mulVec_gu h hx hs, orthoEmb_resMat_mulVec_gu h hx hs,
    herm_smul_smul_gu, herm_orthoEmb hx]

theorem resMat_eq_smul_of_eigen_gu {x : Fin m → Fin n → K} (hx : ONExt.IsON σ₀ x)
    {s : primeFormUnitary h (idGram K n)} {lam : K}
    (hs : ∀ c, s • orthoEmb x c = lam • orthoEmb x c) :
    ONExt.resMat σ₀ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = lam • 1 := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  apply ONExt.orthoEmb_injective hx
  rw [orthoEmb_resMat_mulVec_gu h hx (fun c => ⟨lam • c, by rw [hs, map_smul]⟩), hs,
    Matrix.smul_mulVec, Matrix.one_mulVec, map_smul]

theorem commute_ext_of_resMat_gu (hσ : ∀ c, σ₀ (σ₀ c) = c) {x : Fin m → Fin n → K}
    (hx : ONExt.IsON σ₀ x)
    {s : primeFormUnitary h (idGram K n)} (hs : ∀ c, ∃ d, s • orthoEmb x c = orthoEmb x d)
    (hs' : ∀ c, ∃ d, s⁻¹ • orthoEmb x c = orthoEmb x d) {g : SUid σ₀ m}
    (hg : ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
        ONExt.resMat σ₀ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ONExt.resMat σ₀ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) :
    ((ONExt.ext hσ hx g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((ONExt.ext hσ hx g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  (commute_extMat_of_GL hσ hx (M := (s : GL (Fin n) K)) (herm_mulVec_gu h s.2) hs hs' hg).symm

@[expose] noncomputable def resGL_gu {x : Fin m → Fin n → K} (hx : ONExt.IsON σ₀ x)
    (s : primeFormUnitary h (idGram K n)) (hs : ∀ c, ∃ d, s • orthoEmb x c = orthoEmb x d)
    (hs' : ∀ c, ∃ d, s⁻¹ • orthoEmb x c = orthoEmb x d) : GL (Fin m) K where
  val := ONExt.resMat σ₀ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  inv := ONExt.resMat σ₀ x ((s⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K)
  val_inv := by
    rw [← resMat_mul_gu h hx hs hs', mul_inv_cancel, resMat_one_gu h hx]
  inv_val := by
    rw [← resMat_mul_gu h hx hs' hs, inv_mul_cancel, resMat_one_gu h hx]

theorem coe_resGL_gu {x : Fin m → Fin n → K} (hx : ONExt.IsON σ₀ x)
    (s : primeFormUnitary h (idGram K n)) (hs : ∀ c, ∃ d, s • orthoEmb x c = orthoEmb x d)
    (hs' : ∀ c, ∃ d, s⁻¹ • orthoEmb x c = orthoEmb x d) :
    ((resGL_gu h hx s hs hs' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      ONExt.resMat σ₀ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl

theorem exists_orthoEmb_of_stable_gu {x : Fin m → Fin n → K}
    {W : Submodule K (Fin n → K)} (hW : Submodule.span K (Set.range x) = W)
    {s : primeFormUnitary h (idGram K n)} (hs : ∀ v ∈ W, s • v ∈ W) (c : Fin m → K) :
    ∃ d, s • orthoEmb x c = orthoEmb x d := by
  have h1 : orthoEmb x c ∈ W := hW ▸ orthoEmb_mem_span x c
  have h2 := hs _ h1
  rw [← hW] at h2
  obtain ⟨d, hd⟩ := (mem_span_range_iff x _).1 h2
  exact ⟨d, hd.symm⟩

end Ext

section Crit

variable {ℓ f n : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

@[expose] def HyperLift (h : UnitaryFieldData ℓ f K) {Γ : Type*} [Group Γ]
    (κ : primeFormUnitary h (idGram K n) →* Γ) (E : Subgroup Γ) (H : Subgroup (SUid σ₀ n)) :
    Prop :=
  ∀ (g : SUid σ₀ n) (a b : primeFormUnitary h (idGram K n)), κ a ∈ E → κ b ∈ E → κ a ≠ 1 →
    κ b ∉ Subgroup.zpowers (κ a) →
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
    g ∈ H

end Crit

section Block

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem allCenters_eigen_gu (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) (hq2 : ℓ ^ f ≠ 2) {Γ : Type*} [Group Γ]
    (κ : primeFormUnitary h (idGram K n) →* Γ) {E : Subgroup Γ} {H : Subgroup (SUid σ₀ n)}
    (hH : HyperLift h κ E H)
    {x z y : primeFormUnitary h (idGram K n)} (hxE : κ x ∈ E) (hzE : κ z ∈ E) (hyE : κ y ∈ E)
    (hz1 : κ z ≠ 1)
    (hxz : κ x ∉ Subgroup.zpowers (κ z)) (hyz : κ y ∉ Subgroup.zpowers (κ z))
    (hxy : x * y = y * x) (hxzc : x * z = z * x) (hyzc : y * z = z * y) {α μ ν : K}
    (hxp : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = α • 1)
    (hα : ¬ ∃ c : K, c ^ p = α) (hμ : μ ≠ 0)
    (hzp : ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (μ ^ p) • 1) (hν : ν ≠ 0)
    (hyp : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ν ^ p) • 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hζN : h.bar ζ * ζ = 1) (j : Fin p) :
    AllCenters H
      (Module.End.eigenspace (Matrix.toLin' ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        (μ * ζ ^ (j : ℕ))) := by
  classical
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  have hpK : (p : K) ≠ 0 := heis_natCast_ne_zero hζ hp.two_le
  set zm : Matrix (Fin n) (Fin n) K := ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hzm
  set xm : Matrix (Fin n) (Fin n) K := ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hxm
  set ym : Matrix (Fin n) (Fin n) K := ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hym
  set V : Fin p → Submodule K (Fin n → K) :=
    fun i => Module.End.eigenspace (Matrix.toLin' zm) (μ * ζ ^ (i : ℕ)) with hV
  show AllCenters H (V j)
  by_cases hU0 : V j = ⊥
  · intro v hv _
    rw [hU0, Submodule.mem_bot] at hv
    rw [hv]
    exact isCenter_zero
  have hmemV : ∀ i v, v ∈ V i ↔ zm *ᵥ v = (μ * ζ ^ (i : ℕ)) • v := fun i v => by
    rw [hV, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have hzT3 : (Matrix.toLin' zm) ^ p = algebraMap K (Module.End K (Fin n → K)) (μ ^ p) := by
    have h2 := congrArg Matrix.toLinAlgEquiv' hzp
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  have hsup : ⨆ i, V i = ⊤ := NonPth.iSup_eigenspace_eq_top_p hp hpK hζ hμ hzT3
  obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      exact absurd (Subsingleton.elim v₀ 0) hv₀0
    · exact h0
  have hzU : ∀ u w, herm σ₀ (zm *ᵥ u) (zm *ᵥ w) = herm σ₀ u w := fun u w =>
    herm_smul_smul_gu h z u w
  have hμN : h.bar μ * μ = 1 := bar_mul_eq_one_of_gu_pow h hp hp2 hpq hn hμ hzp
  have hlamN : ∀ k : ℕ, h.bar (μ * ζ ^ k) * (μ * ζ ^ k) = 1 := fun k => by
    rw [map_mul, map_pow]
    calc h.bar μ * h.bar ζ ^ k * (μ * ζ ^ k) = (h.bar μ * μ) * (h.bar ζ * ζ) ^ k := by ring
      _ = 1 := by rw [hμN, hζN, one_pow, one_mul]
  have hlam_ne : ∀ i i' : Fin p, i ≠ i' → h.bar (μ * ζ ^ (i : ℕ)) * (μ * ζ ^ (i' : ℕ)) ≠ 1 := by
    intro i i' hii he
    have key : μ * ζ ^ (i' : ℕ) = μ * ζ ^ (i : ℕ) := by
      linear_combination (-(μ * ζ ^ (i' : ℕ))) * hlamN i + (μ * ζ ^ (i : ℕ)) * he
    have h2 : ζ ^ (i' : ℕ) = ζ ^ (i : ℕ) := mul_left_cancel₀ hμ key
    exact hii (Fin.ext (hζ.pow_inj i'.2 i.2 h2).symm)
  set B := idForm h n with hBdef
  have hzB : ∀ u w, B (Matrix.toLin' zm u) (Matrix.toLin' zm w) = B u w := fun u w => by
    rw [hBdef, Nonsplit.idForm_eq_herm h, Nonsplit.idForm_eq_herm h, Matrix.toLin'_apply,
      Matrix.toLin'_apply]
    exact hzU u w
  have hV_orth : ∀ i i' : Fin p, i ≠ i' → ∀ u ∈ V i, ∀ v ∈ V i', B u v = 0 := by
    intro i i' hii u hu v hv
    exact NonCube.eigen_orthogonal hzB (hlam_ne i i' hii)
      (by rw [Matrix.toLin'_apply]; exact (hmemV i u).1 hu)
      (by rw [Matrix.toLin'_apply]; exact (hmemV i' v).1 hv)
  have hnd : (B.domRestrict₁₂ (V j) (V j)).SeparatingLeft :=
    NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n) V hV_orth hsup j
  have hstab : ∀ s : primeFormUnitary h (idGram K n), s * z = z * s → ∀ v ∈ V j, s • v ∈ V j := by
    intro s hsz v hv
    rw [hmemV] at hv ⊢
    rw [smul_def_gu, mulVec_mulVec, ← coe_comm_gu h hsz, ← mulVec_mulVec, hv, mulVec_smul]
  have hinv : ∀ s : primeFormUnitary h (idGram K n), s * z = z * s → s⁻¹ * z = z * s⁻¹ := by
    intro s hsz
    exact (Commute.inv_left hsz).eq
  have hxT3 : (Matrix.toLin' xm) ^ p = algebraMap K (Module.End K (Fin n → K)) α := by
    have h2 := congrArg Matrix.toLinAlgEquiv' hxp
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  have hdim : p ≤ Module.finrank K (V j) :=
    NonPth.p_le_finrank_of_stable hp hxT3 hα (fun s hs => by
      rw [Matrix.toLin'_apply]; exact hstab x hxzc s hs) hU0
  have hON : HasONBasis σ₀ (V j) := by
    refine Nonsplit.hasONBasis_of_separatingLeft h (V j) hnd ?_
    rcases Nat.lt_or_ge p 4 with hp4 | hp4
    · obtain ⟨s, hs0, hs1⟩ := Nonsplit.exists_norm_ne_one h hq2
      exact Or.inr ⟨by have := hp.two_le; omega, s, hs0, by rw [hσb]; exact hs1⟩
    · exact Or.inl (by omega)
  obtain ⟨m, xs, hxs, hspan, -⟩ := hON
  have hxsON : ONExt.IsON σ₀ xs := hxs
  have hsU : ∀ s : primeFormUnitary h (idGram K n), s * z = z * s →
      ∀ c, ∃ d, s • orthoEmb xs c = orthoEmb xs d :=
    fun s hsz => exists_orthoEmb_of_stable_gu h hspan (hstab s hsz)
  have hsU' : ∀ s : primeFormUnitary h (idGram K n), s * z = z * s →
      ∀ c, ∃ d, s⁻¹ • orthoEmb xs c = orthoEmb xs d :=
    fun s hsz => exists_orthoEmb_of_stable_gu h hspan (hstab s⁻¹ (hinv s hsz))
  have hzlam : ∀ c, z • orthoEmb xs c = (μ * ζ ^ (j : ℕ)) • orthoEmb xs c := by
    intro c
    have h1 : orthoEmb xs c ∈ V j := hspan ▸ orthoEmb_mem_span xs c
    exact (hmemV j _).1 h1
  have hzres : ONExt.resMat σ₀ xs zm = (μ * ζ ^ (j : ℕ)) • 1 :=
    resMat_eq_smul_of_eigen_gu h hxsON hzlam
  have hzz : z * z = z * z := rfl
  set ε := ONExt.ext hσ.invol hxsON with hε
  set HU := H.comap ε with hHU
  have hcentU : ∀ s : primeFormUnitary h (idGram K n), s * z = z * s → κ s ∈ E →
      κ s ∉ Subgroup.zpowers (κ z) →
      HeisTensor.Cent HU (ONExt.resMat σ₀ xs ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    intro s hsz hsE hs g hg
    have h1 := commute_ext_of_resMat_gu h hσ.invol hxsON (hsU s hsz) (hsU' s hsz) hg
    have h2 := commute_ext_of_resMat_gu h hσ.invol hxsON (hsU z hzz) (hsU' z hzz) (g := g) (by
      rw [hzres, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul])
    show ε g ∈ H
    exact hH (ε g) z s hzE hsE hz1 hs h2 h1
  have hXmem : ∀ s : primeFormUnitary h (idGram K n),
      ∀ (hs : ∀ c, ∃ d, s • orthoEmb xs c = orthoEmb xs d)
      (hs' : ∀ c, ∃ d, s⁻¹ • orthoEmb xs c = orthoEmb xs d),
      resGL_gu h hxsON s hs hs' ∈ primeFormUnitary h (idGram K m) := by
    intro s hs hs'
    refine mem_primeFormUnitary_of_herm h fun u v => ?_
    rw [coe_resGL_gu]
    exact herm_resMat_gu h hxsON hs u v
  have hpowres : ∀ s : primeFormUnitary h (idGram K n),
      ∀ (hs : ∀ c, ∃ d, s • orthoEmb xs c = orthoEmb xs d) {β : K},
      ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1 →
      (ONExt.resMat σ₀ xs ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ p = β • 1 := by
    intro s hs β hβ
    rw [← resMat_pow_gu h hxsON hs p]
    have : (((s ^ p : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = β • 1 := by
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hβ]
    rw [this, resMat_smul_one hxsON]
  set X := resGL_gu h hxsON x (hsU x hxzc) (hsU' x hxzc) with hX
  set Y := resGL_gu h hxsON y (hsU y hyzc) (hsU' y hyzc) with hY
  have hXG : X ∈ primeFormUnitary h (idGram K m) := hXmem x _ _
  have hYG : Y ∈ primeFormUnitary h (idGram K m) := hXmem y _ _
  have hXp : ((X ^ p : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = α • 1 := by
    rw [Units.val_pow_eq_pow_val, hX, coe_resGL_gu]
    exact hpowres x (hsU x hxzc) hxp
  have hYp : ((Y ^ p : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = (ν ^ p) • 1 := by
    rw [Units.val_pow_eq_pow_val, hY, coe_resGL_gu]
    exact hpowres y (hsU y hyzc) hyp
  have hXY : X * Y = Y * X := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hX, hY, coe_resGL_gu, coe_resGL_gu,
      ← resMat_mul_gu h hxsON (hsU x hxzc) (hsU y hyzc),
      ← resMat_mul_gu h hxsON (hsU y hyzc) (hsU x hxzc), hxy]
  have hCX : HeisTensor.Cent HU ((X : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) :=
    hcentU x hxzc hxE hxz
  have hCY : HeisTensor.Cent HU ((Y : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) :=
    hcentU y hyzc hyE hyz
  have htop : HU = ⊤ := by
    by_cases hYs : ∃ c : K, ((Y : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = c • 1
    · obtain ⟨c, hc⟩ := hYs
      rw [eq_top_iff]
      intro g _
      apply hCY g
      rw [hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
    push Not at hYs
    have hνpN : h.bar (ν ^ p) * ν ^ p = 1 := bar_mul_eq_one_of_scalar_pow h
      (by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · exfalso
          subst h0
          exact hYs 0 (Subsingleton.elim _ _)
        · exact h0) hYG hYp
    have hνN : h.bar ν * ν = 1 :=
      bar_mul_eq_one_of_pow_eq h hp hp2 hpq hν rfl (planeW_pow_card_succ h hνpN)
    rcases Nat.lt_or_ge p 5 with hp5 | hp5
    ·
      have hp3 : p = 3 := by
        have := hp.two_le
        interval_cases p
        · exact absurd rfl hp2
        · rfl
        · exact absurd hp (by decide)
      subst hp3
      exact NonCube.eq_top_of_noncube_pair h hq2 hXG hYG hXY hXp hα hYp hν hνN
        hζ.pow_eq_one (hζ.ne_one (by norm_num)) hζN hYs hCX hCY
    ·
      have hν'N : h.bar ν⁻¹ * ν⁻¹ = 1 := by
        rw [map_inv₀, ← mul_inv, hνN, inv_one]
      set Y' : GL (Fin m) K :=
        Matrix.GeneralLinearGroup.scalar (Fin m) (Units.mk0 ν⁻¹ (inv_ne_zero hν)) * Y with hY'
      have hY'M : ((Y' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
          ν⁻¹ • ((Y : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
        rw [hY', Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          Units.val_mk0, ← Matrix.smul_eq_diagonal_mul]
      have hY'G : Y' ∈ primeFormUnitary h (idGram K m) :=
        Subgroup.mul_mem _ (planeW_scalar_mem h (inv_ne_zero hν) hν'N) hYG
      have hY'p : ((Y' ^ p : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 := by
        rw [Units.val_pow_eq_pow_val, hY'M, smul_pow, ← Units.val_pow_eq_pow_val, hYp,
          smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hν), one_smul]
      have hXY' : X * Y' = Y' * X := by
        apply Units.ext
        show ((X : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) * ((Y' : GL (Fin m) K) :
            Matrix (Fin m) (Fin m) K) = ((Y' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
              ((X : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)
        rw [hY'M, Matrix.mul_smul, Matrix.smul_mul]
        congr 1
        rw [← Units.val_mul, ← Units.val_mul, hXY]
      have hY'1 : ∀ c : K, ((Y' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) ≠ c • 1 := by
        intro c hc
        apply hYs (ν * c)
        rw [hY'M] at hc
        calc ((Y : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)
            = ν • (ν⁻¹ • ((Y : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) := by
              rw [smul_smul, mul_inv_cancel₀ hν, one_smul]
          _ = (ν * c) • 1 := by rw [hc, smul_smul]
      have hCY' : HeisTensor.Cent HU ((Y' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
        rw [hY'M]
        exact HeisTensor.Cent.smul hCY (inv_ne_zero hν)
      exact NonPth.eq_top_of_nonpth_pair h hp hp5 hpq hXG hY'G hXY' hXp hα hY'p hY'1 hCX hCY'
  have hall : ∀ g, ε g ∈ H := fun g => by
    have : g ∈ HU := by rw [htop]; exact Subgroup.mem_top g
    exact this
  rw [← hspan]
  exact ONExt.allCenters_of_forall_ext_mem hσ.invol hxsON hall

end Block

section Choice

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem exists_pth_word_gu (h : UnitaryFieldData ℓ f K) (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) (hn : 0 < n) {Γ : Type*} [Group Γ]
    (κ : primeFormUnitary h (idGram K n) →* Γ)
    (hker : ∀ g ∈ κ.ker, ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1)
    {E : Subgroup Γ} (hE : IsElemAbelian p E) {x s : primeFormUnitary h (idGram K n)}
    (hxs : x * s = s * x) {α : K}
    (hα0 : α ≠ 0) (hxp : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = α • 1)
    (hα : ¬ ∃ c : K, c ^ p = α) (hsE : κ s ∈ E) :
    ∃ a b : ℕ, ¬ p ∣ b ∧ ∃ ν : K, ν ≠ 0 ∧
      (((x ^ a * s ^ b : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) ^ p = (ν ^ p) • 1 := by
  have hsp : κ (s ^ p) = 1 := by rw [map_pow]; exact hE.2 _ hsE
  obtain ⟨β, hβ⟩ := hker (s ^ p) hsp
  have hβ' : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1 := by
    rw [← hβ, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have hβ0 : β ≠ 0 := scalar_ne_zero_of_matPow hn hβ'
  obtain ⟨a, b, hab, ν, hν⟩ := exists_pth_power_word hp hpK hα0 hβ0
  have hb : ¬ p ∣ b := by
    rintro ⟨t, rfl⟩
    have hpa : ¬ p ∣ a := fun hpa => hab ⟨hpa, dvd_mul_right p t⟩
    apply hα
    refine pth_power_of_pow_coprime hp hα0 hpa (s := ν * (β ^ t)⁻¹) ?_
    rw [mul_pow, inv_pow, ← pow_mul, hν, mul_comm t p, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hβ0), mul_one]
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hν
    exact mul_ne_zero (pow_ne_zero _ hα0) (pow_ne_zero _ hβ0) hν.symm
  exact ⟨a, b, hb, ν, hν0, by rw [pow_word_of_comm_gu h hxs hxp hβ' a b, ← hν]⟩

theorem exists_pth_lines_gu (h : UnitaryFieldData ℓ f K) (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) (hn : 0 < n) {Γ : Type*} [Group Γ] [Finite Γ]
    (κ : primeFormUnitary h (idGram K n) →* Γ) {E : Subgroup Γ}
    (hEκ : ∀ e ∈ E, ∃ a : primeFormUnitary h (idGram K n), κ a = e)
    (hker : ∀ g ∈ κ.ker, ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1)
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    (hcomm : ∀ a b : primeFormUnitary h (idGram K n), κ a ∈ E → κ b ∈ E → a * b = b * a)
    {x : primeFormUnitary h (idGram K n)} (hxE : κ x ∈ E) (hx1 : κ x ≠ 1) {α : K} (hα0 : α ≠ 0)
    (hxp : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = α • 1)
    (hα : ¬ ∃ c : K, c ^ p = α) :
    ∃ y₁ y₂ : primeFormUnitary h (idGram K n), κ y₁ ∈ E ∧ κ y₂ ∈ E ∧ κ y₁ ≠ 1 ∧
      κ y₂ ∉ Subgroup.zpowers (κ y₁) ∧
      κ x ∉ Subgroup.closure ({κ y₁, κ y₂} : Set Γ) ∧ ∃ ν₁ ν₂ : K, ν₁ ≠ 0 ∧ ν₂ ≠ 0 ∧
        ((y₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ν₁ ^ p) • 1 ∧
        ((y₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ν₂ ^ p) • 1 := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hexp : ∀ e ∈ E, e ^ p = 1 := hE.2
  have hox : orderOf (κ x) = p := orderOf_eq_prime (hexp _ hxE) hx1
  obtain ⟨e₁, he₁E, he₁⟩ := exists_not_mem_of_card hp (S := Subgroup.zpowers (κ x)) hcard
    (k := 1) (by norm_num) (by rw [Nat.card_zpowers, hox, pow_one])
  obtain ⟨s₁, rfl⟩ := hEκ e₁ he₁E
  obtain ⟨a₁, b₁, hb₁, ν₁, hν₁, hy₁⟩ :=
    exists_pth_word_gu h hp hpK hn κ hker hE (hcomm x s₁ hxE he₁E) hα0 hxp hα he₁E
  set y₁ := x ^ a₁ * s₁ ^ b₁ with hy₁def
  have hy₁E : κ y₁ ∈ E := by
    rw [hy₁def, map_mul, map_pow, map_pow]
    exact E.mul_mem (E.pow_mem hxE _) (E.pow_mem he₁E _)
  have hy₁x : κ y₁ ∉ Subgroup.zpowers (κ x) := by
    intro hmem
    apply he₁
    refine mem_of_pow_mem hp (hexp _ he₁E) hb₁ ?_
    have : (κ s₁) ^ b₁ = ((κ x) ^ a₁)⁻¹ * κ y₁ := by
      rw [hy₁def, map_mul, map_pow, map_pow, inv_mul_cancel_left]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ _)) hmem
  have hy₁1 : κ y₁ ≠ 1 := fun h1 => hy₁x (h1 ▸ Subgroup.one_mem _)
  have hc2 : Nat.card (Subgroup.closure ({κ x, κ y₁} : Set Γ)) = p ^ 2 :=
    card_closure_pair_of_not_mem hp hE hxE hy₁E hx1 hy₁x
  obtain ⟨e₂, he₂E, he₂⟩ := exists_not_mem_of_card hp hcard (k := 2) (by norm_num) hc2
  obtain ⟨s₂, rfl⟩ := hEκ e₂ he₂E
  obtain ⟨a₂, b₂, hb₂, ν₂, hν₂, hy₂⟩ :=
    exists_pth_word_gu h hp hpK hn κ hker hE (hcomm x s₂ hxE he₂E) hα0 hxp hα he₂E
  set y₂ := x ^ a₂ * s₂ ^ b₂ with hy₂def
  have hy₂E : κ y₂ ∈ E := by
    rw [hy₂def, map_mul, map_pow, map_pow]
    exact E.mul_mem (E.pow_mem hxE _) (E.pow_mem he₂E _)
  have hxcl : κ x ∈ Subgroup.closure ({κ x, κ y₁} : Set Γ) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hy₁cl : κ y₁ ∈ Subgroup.closure ({κ x, κ y₁} : Set Γ) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hy₂cl : κ y₂ ∉ Subgroup.closure ({κ x, κ y₁} : Set Γ) := by
    intro hmem
    apply he₂
    refine mem_of_pow_mem hp (hexp _ he₂E) hb₂ ?_
    have : (κ s₂) ^ b₂ = ((κ x) ^ a₂)⁻¹ * κ y₂ := by
      rw [hy₂def, map_mul, map_pow, map_pow, inv_mul_cancel_left]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hxcl _)) hmem
  have hy₂y₁ : κ y₂ ∉ Subgroup.zpowers (κ y₁) := fun hmem =>
    hy₂cl (Subgroup.zpowers_le.2 hy₁cl hmem)
  refine ⟨y₁, y₂, hy₁E, hy₂E, hy₁1, hy₂y₁, ?_, ν₁, ν₂, hν₁, hν₂, hy₁, hy₂⟩
  intro hxmem
  have hc2' : Nat.card (Subgroup.closure ({κ y₁, κ y₂} : Set Γ)) = p ^ 2 :=
    card_closure_pair_of_not_mem hp hE hy₁E hy₂E hy₁1 hy₂y₁
  have hle : Subgroup.closure ({κ x, κ y₁} : Set Γ) ≤ Subgroup.closure ({κ y₁, κ y₂} : Set Γ) :=
    (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hxmem, Set.singleton_subset_iff.2
      (Subgroup.subset_closure (Set.mem_insert _ _))⟩)
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hc2, hc2'])
  exact hy₂cl (heq ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

end Choice

section CaseB

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem hyperGen_of_nonpth_gu (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) (hq2 : ℓ ^ f ≠ 2) (hn : 0 < n) {Γ : Type*} [Group Γ] [Finite Γ]
    (κ : primeFormUnitary h (idGram K n) →* Γ) {E : Subgroup Γ}
    (hEκ : ∀ e ∈ E, ∃ a : primeFormUnitary h (idGram K n), κ a = e)
    (hker : ∀ g ∈ κ.ker, ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1)
    (hker' : ∀ g : primeFormUnitary h (idGram K n),
      (∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) → κ g = 1)
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) {H : Subgroup (SUid σ₀ n)}
    (hH : HyperLift h κ E H)
    (hcomm : ∀ a b : primeFormUnitary h (idGram K n), κ a ∈ E → κ b ∈ E → a * b = b * a)
    {x : primeFormUnitary h (idGram K n)} (hxE : κ x ∈ E) {α : K}
    (hxp : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = α • 1)
    (hα : ¬ ∃ c : K, c ^ p = α) : H = ⊤ := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  have hpK1 : p ∣ Nat.card K - 1 := dvd_card_sub_one_of_unitary h hpq
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hα ⟨0, zero_pow hp.ne_zero⟩
  have hx1 : κ x ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := hker x h1
    apply hα
    refine ⟨c, ?_⟩
    rw [hc, smul_pow, one_pow] at hxp
    have := congrFun (congrFun hxp ⟨0, hn⟩) ⟨0, hn⟩
    simpa using this
  obtain ⟨ζ, hζ, hζN⟩ := NonPth.exists_primitive_prime_root_bar h hp hpq
  have hpK : (p : K) ≠ 0 := heis_natCast_ne_zero hζ hp.two_le
  obtain ⟨y₁, y₂, hy₁E, hy₂E, hy₁1, hy₂y₁, hxcl, ν₁, ν₂, hν₁, hν₂, hy₁p, hy₂p⟩ :=
    exists_pth_lines_gu h hp hpK1 hn κ hEκ hker hE hcard hcomm hxE hx1 hα0 hxp hα
  have hexp : ∀ e ∈ E, e ^ p = 1 := hE.2
  have hxy₁ : x * y₁ = y₁ * x := hcomm x y₁ hxE hy₁E
  have hxy₂ : x * y₂ = y₂ * x := hcomm x y₂ hxE hy₂E
  have hy₁y₂ : y₁ * y₂ = y₂ * y₁ := hcomm y₁ y₂ hy₁E hy₂E
  have hν₁N := bar_mul_eq_one_of_gu_pow h hp hp2 hpq hn hν₁ hy₁p
  have hν₂N := bar_mul_eq_one_of_gu_pow h hp hp2 hpq hn hν₂ hy₂p
  have hy₁cl : κ y₁ ∈ Subgroup.closure ({κ y₁, κ y₂} : Set Γ) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hy₂cl : κ y₂ ∈ Subgroup.closure ({κ y₁, κ y₂} : Set Γ) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hc2 : Nat.card (Subgroup.closure ({κ y₁, κ y₂} : Set Γ)) = p ^ 2 :=
    card_closure_pair_of_not_mem hp hE hy₁E hy₂E hy₁1 hy₂y₁
  set xm : Matrix (Fin n) (Fin n) K := ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hxm
  set y₁m : Matrix (Fin n) (Fin n) K := ((y₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hy₁m
  set y₂m : Matrix (Fin n) (Fin n) K := ((y₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hy₂m
  have hpowT : ∀ (M : Matrix (Fin n) (Fin n) K) (c : K), M ^ p = c • 1 →
      (Matrix.toLin' M) ^ p = algebraMap K (Module.End K (Fin n → K)) c := by
    intro M c hM
    have h2 := congrArg Matrix.toLinAlgEquiv' hM
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  set W : Fin p × Fin p → Submodule K (Fin n → K) := fun ij =>
    Module.End.eigenspace (Matrix.toLin' y₁m) (ν₁ * ζ ^ (ij.1 : ℕ)) ⊓
      Module.End.eigenspace (Matrix.toLin' y₂m) (ν₂ * ζ ^ (ij.2 : ℕ)) with hW
  have hWtop : ⨆ ij, W ij = ⊤ := by
    refine iSup_inf_eigenspace_eq_top hp hpK hζ ?_ hν₁ hν₂ (hpowT _ _ hy₁p) (hpowT _ _ hy₂p)
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, Module.End.mul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec, mulVec_mulVec, coe_comm_gu h hy₁y₂]
  have hmemW : ∀ ij v, v ∈ W ij ↔ y₁m *ᵥ v = (ν₁ * ζ ^ (ij.1 : ℕ)) • v ∧
      y₂m *ᵥ v = (ν₂ * ζ ^ (ij.2 : ℕ)) • v := by
    intro ij v
    rw [hW, Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff,
      Matrix.toLin'_apply, Matrix.toLin'_apply]
  have hW_orth : ∀ ij ij' : Fin p × Fin p, ij ≠ ij' → ∀ u ∈ W ij, ∀ v ∈ W ij',
      herm σ₀ u v = 0 := by
    intro ij ij' hne u hu v hv
    rw [hmemW] at hu hv
    by_cases h1 : ij.1 = ij'.1
    · have h2 : ij.2 ≠ ij'.2 := fun h2 => hne (Prod.ext h1 h2)
      exact herm_eq_zero_of_eigen_gu h hu.2 hv.2 (bar_mul_ne_one h hν₂ hν₂N hζ hζN h2)
    · exact herm_eq_zero_of_eigen_gu h hu.1 hv.1 (bar_mul_ne_one h hν₁ hν₁N hζ hζN h1)
  have hWsep : ∀ ij, ((idForm h n).domRestrict₁₂ (W ij) (W ij)).SeparatingLeft :=
    NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n) W
      (fun ij ij' hne u hu v hv => by
        rw [Nonsplit.idForm_eq_herm h]; exact hW_orth ij ij' hne u hu v hv) hWtop
  have hWx : ∀ ij, ∀ v ∈ W ij, Matrix.toLin' xm v ∈ W ij := by
    intro ij v hv
    rw [Matrix.toLin'_apply]
    rw [hmemW] at hv ⊢
    constructor
    · rw [mulVec_mulVec, ← coe_comm_gu h hxy₁, ← mulVec_mulVec, hv.1, mulVec_smul]
    · rw [mulVec_mulVec, ← coe_comm_gu h hxy₂, ← mulVec_mulVec, hv.2, mulVec_smul]
  have hWdim : ∀ ij, W ij ≠ ⊥ → p ≤ Module.finrank K (W ij) := fun ij hne =>
    NonPth.p_le_finrank_of_stable hp (hpowT _ _ hxp) hα (hWx ij) hne
  have hWON : ∀ ij, W ij ≠ ⊥ → HasONBasis σ₀ (W ij) := by
    intro ij hne
    refine Nonsplit.hasONBasis_of_separatingLeft h (W ij) (hWsep ij) ?_
    have hd := hWdim ij hne
    rcases Nat.lt_or_ge p 4 with hp4 | hp4
    · obtain ⟨s, hs0, hs1⟩ := Nonsplit.exists_norm_ne_one h hq2
      exact Or.inr ⟨by have := hp.two_le; omega, s, hs0, by rw [hσb]; exact hs1⟩
    · exact Or.inl (by omega)
  have hcl_le : ∀ a b : ℕ, Subgroup.zpowers (κ (y₁ ^ a * y₂ ^ b)) ≤
      Subgroup.closure ({κ y₁, κ y₂} : Set Γ) := by
    intro a b
    rw [Subgroup.zpowers_le, map_mul, map_pow, map_pow]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hy₁cl _) (Subgroup.pow_mem _ hy₂cl _)
  have hword : ∀ a b : ℕ, ¬ (p ∣ a ∧ p ∣ b) → ∀ k : Fin p,
      AllCenters H (Module.End.eigenspace (Matrix.toLin'
        (((y₁ ^ a * y₂ ^ b : primeFormUnitary h (idGram K n)) :
          GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ((ν₁ ^ a * ν₂ ^ b) * ζ ^ (k : ℕ))) := by
    intro a b hab k
    set z := y₁ ^ a * y₂ ^ b with hz
    have hzE : κ z ∈ E := by
      rw [hz, map_mul, map_pow, map_pow]
      exact E.mul_mem (E.pow_mem hy₁E _) (E.pow_mem hy₂E _)
    have hz1 : κ z ≠ 1 := by
      intro h1
      rw [hz, map_mul, map_pow, map_pow] at h1
      exact hab (dvd_of_pow_mul_pow_eq_one hp (hexp _ hy₁E) (hexp _ hy₂E) hy₁1 hy₂y₁ h1)
    have hxz : κ x ∉ Subgroup.zpowers (κ z) := fun hm => hxcl (hcl_le a b hm)
    have hcz : ∀ t : primeFormUnitary h (idGram K n), t * y₁ = y₁ * t → t * y₂ = y₂ * t →
        t * z = z * t := by
      intro t h1 h2
      rw [hz]
      exact ((Commute.pow_right h1 a).mul_right (Commute.pow_right h2 b)).eq
    have hzp : (((z : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) ^ p = ((ν₁ ^ a * ν₂ ^ b) ^ p) • 1 := by
      rw [hz, pow_word_of_comm_gu h hy₁y₂ hy₁p hy₂p a b, mul_pow, ← pow_mul, ← pow_mul,
        ← pow_mul, ← pow_mul, mul_comm p a, mul_comm p b]
    have hμ : ν₁ ^ a * ν₂ ^ b ≠ 0 := mul_ne_zero (pow_ne_zero _ hν₁) (pow_ne_zero _ hν₂)
    by_cases hy₁z : κ y₁ ∈ Subgroup.zpowers (κ z)
    · have hy₂z : κ y₂ ∉ Subgroup.zpowers (κ z) := by
        intro hy₂z
        have hle : Subgroup.closure ({κ y₁, κ y₂} : Set Γ) ≤ Subgroup.zpowers (κ z) :=
          (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hy₁z,
            Set.singleton_subset_iff.2 hy₂z⟩)
        have h1 := Subgroup.card_le_of_le hle
        rw [hc2, Nat.card_zpowers, orderOf_eq_prime (hexp _ hzE) hz1] at h1
        have := Nat.pow_lt_pow_right hp.one_lt (by norm_num : 1 < 2)
        rw [pow_one] at this
        omega
      exact allCenters_eigen_gu h hp hp2 hpq hq2 κ hH hxE hzE hy₂E hz1 hxz hy₂z hxy₂
        (hcz x hxy₁ hxy₂) (hcz y₂ hy₁y₂.symm rfl) hxp hα hμ hzp hν₂ hy₂p hζ hζN k
    · exact allCenters_eigen_gu h hp hp2 hpq hq2 κ hH hxE hzE hy₁E hz1 hxz hy₁z hxy₁
        (hcz x hxy₁ hxy₂) (hcz y₁ rfl hy₁y₂) hxp hα hμ hzp hν₁ hy₁p hζ hζN k
  have hAll : ∀ ij, AllCenters H (W ij) := by
    intro ij v hv hvi
    have hp1 : ¬ p ∣ 1 := fun hd => hp.one_lt.ne' (Nat.dvd_one.1 hd)
    have h1 := hword 1 0 (fun hd => hp1 hd.1) ij.1
    simp only [pow_one, pow_zero, mul_one] at h1
    refine h1 v ?_ hvi
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact ((hmemW ij v).1 hv).1
  have hmix : ∀ ij ij' : Fin p × Fin p, ij ≠ ij' → W ij ≠ ⊥ → W ij' ≠ ⊥ →
      ∃ w₁ ∈ W ij, ∃ w₂ ∈ W ij', w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ IsCenter H (w₁ + w₂) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hne h0 h0'
    set a : ℕ := (((j' : ℕ) : ZMod p) - ((j : ℕ) : ZMod p)).val with ha
    set b : ℕ := (((i : ℕ) : ZMod p) - ((i' : ℕ) : ZMod p)).val with hb
    have haZ : (a : ZMod p) = ((j' : ℕ) : ZMod p) - ((j : ℕ) : ZMod p) := ZMod.natCast_zmod_val _
    have hbZ : (b : ZMod p) = ((i : ℕ) : ZMod p) - ((i' : ℕ) : ZMod p) := ZMod.natCast_zmod_val _
    have hfin : ∀ u v : Fin p, ((u : ℕ) : ZMod p) = ((v : ℕ) : ZMod p) → u = v := by
      intro u v huv
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt u.2, Nat.mod_eq_of_lt v.2] at huv
      exact Fin.ext huv
    have hab : ¬ (p ∣ a ∧ p ∣ b) := by
      rintro ⟨hpa, hpb⟩
      apply hne
      have h1 : (a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff a p).2 hpa
      have h2 : (b : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff b p).2 hpb
      rw [haZ, sub_eq_zero] at h1
      rw [hbZ, sub_eq_zero] at h2
      rw [hfin _ _ h1, hfin _ _ h2]
    set k : Fin p := ⟨(a * i + b * j) % p, Nat.mod_lt _ hp.pos⟩ with hk
    have hcong : (a * i' + b * j') % p = (a * i + b * j) % p := by
      rw [← ZMod.natCast_eq_natCast_iff']
      push_cast
      rw [haZ, hbZ]
      ring
    set z := y₁ ^ a * y₂ ^ b with hz
    have hzv : ∀ (i₀ j₀ : Fin p) (v : Fin n → K), v ∈ W (i₀, j₀) →
        (((z : primeFormUnitary h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
          ((ν₁ ^ a * ν₂ ^ b) * ζ ^ ((a * i₀ + b * j₀) % p)) • v := by
      intro i₀ j₀ v hv
      rw [hmemW] at hv
      have hpow : ∀ (M : Matrix (Fin n) (Fin n) K) (c : K) (t : ℕ), M *ᵥ v = c • v →
          (M ^ t) *ᵥ v = c ^ t • v := by
        intro M c t hMv
        induction t with
        | zero => simp
        | succ t ih =>
          rw [pow_succ, ← mulVec_mulVec, hMv, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
      rw [hz, coe_pow_mul_pow_gu, ← mulVec_mulVec, hpow _ _ b hv.2, mulVec_smul, hpow _ _ a hv.1,
        smul_smul, ← pow_eq_pow_mod hζ]
      congr 1
      simp only [mul_pow, ← pow_mul]
      rw [pow_add]
      ring
    have hUc := hword a b hab k
    obtain ⟨u₀, hu₀, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    obtain ⟨w₁, hw₁, hw₁i, hw₁0⟩ := Nonsplit.exists_isotropic_pairing hσ (hWON _ h0) hu₀ hu₀0
    obtain ⟨u₀', hu₀', hu₀0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0'
    obtain ⟨w₂, hw₂, hw₂i, hw₂0⟩ := Nonsplit.exists_isotropic_pairing hσ (hWON _ h0') hu₀' hu₀0'
    have hw₁ne : w₁ ≠ 0 := by rintro rfl; exact hw₁0 (herm_zero_right σ₀ _)
    have hw₂ne : w₂ ≠ 0 := by rintro rfl; exact hw₂0 (herm_zero_right σ₀ _)
    refine ⟨w₁, hw₁, w₂, hw₂, hw₁ne, hw₂ne, hUc _ ?_ ?_⟩
    · rw [Module.End.mem_eigenspace_iff, map_add, Matrix.toLin'_apply, Matrix.toLin'_apply,
        hzv i j w₁ hw₁, hzv i' j' w₂ hw₂, hcong, smul_add]
    · have h12 := hW_orth (i, j) (i', j') hne w₁ hw₁ w₂ hw₂
      have h21 := hW_orth (i', j') (i, j) (Ne.symm hne) w₂ hw₂ w₁ hw₁
      simp only [herm_add_left, herm_add_right, hw₁i, hw₂i, h12, h21, add_zero]
  have hpair : ∃ ij ij' : Fin p × Fin p, ij ≠ ij' ∧ W ij ≠ ⊥ ∧ W ij' ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨ij₀, hij₀⟩ : ∃ ij₀, ∀ ij, ij ≠ ij₀ → W ij = ⊥ := by
      by_cases hex : ∃ ij₀, W ij₀ ≠ ⊥
      · obtain ⟨ij₀, hij₀⟩ := hex
        exact ⟨ij₀, fun ij hij => hcon ij₀ ij (Ne.symm hij) hij₀⟩
      · push Not at hex
        exact ⟨(⟨0, hp.pos⟩, ⟨0, hp.pos⟩), fun ij _ => hex ij⟩
    have hall : ∀ v, y₁m *ᵥ v = (ν₁ * ζ ^ (ij₀.1 : ℕ)) • v := by
      intro v
      have hv : v ∈ ⨆ ij, W ij := by rw [hWtop]; exact Submodule.mem_top
      have hle : (⨆ ij, W ij) ≤ W ij₀ := iSup_le fun ij => by
        by_cases hij : ij = ij₀
        · rw [hij]
        · rw [hij₀ ij hij]; exact bot_le
      exact ((hmemW ij₀ v).1 (hle hv)).1
    apply hy₁1
    refine hker' y₁ ⟨ν₁ * ζ ^ (ij₀.1 : ℕ), ?_⟩
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [hall, Matrix.smul_mulVec, Matrix.one_mulVec]
  obtain ⟨ij₀, ij₁, hne₀₁, h₀, h₁⟩ := hpair
  have hn4 : 4 ≤ n := by
    have hd₀ := hWdim ij₀ h₀
    have hd₁ := hWdim ij₁ h₁
    have hdisj : Disjoint (W ij₀) (W ij₁) := by
      rw [Submodule.disjoint_def]
      intro v hv0 hv1
      have hvv : herm σ₀ v v = 0 := hW_orth ij₀ ij₁ hne₀₁ v hv0 v hv1
      have hsep := hWsep ij₀
      have : (⟨v, hv0⟩ : W ij₀) = 0 := by
        apply hsep
        rintro ⟨w, hw⟩
        simp only [LinearMap.domRestrict₁₂_apply]
        rw [Nonsplit.idForm_eq_herm h]
        exact hW_orth ij₁ ij₀ (Ne.symm hne₀₁) v hv1 w hw
      exact congrArg Subtype.val this
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq (W ij₀) (W ij₁)
    rw [hdisj.eq_bot, finrank_bot] at h3
    have h4 := Submodule.finrank_le (W ij₀ ⊔ W ij₁)
    rw [Module.finrank_fin_fun] at h4
    have := hp.two_le
    omega
  let ι := {ij : Fin p × Fin p // W ij ≠ ⊥}
  have : Nonempty ι := ⟨⟨ij₀, h₀⟩⟩
  refine Centers.eq_top_of_blocks hσ hn4 (fun i : ι => W i.1) (fun i => hWON i.1 i.2)
    (fun i i' hii u hu v hv => hW_orth i.1 i'.1 (fun h' => hii (Subtype.ext h')) u hu v hv)
    (fun i => hAll i.1)
    (fun i i' hii => hmix i.1 i'.1 (fun h' => hii (Subtype.ext h')) i.2 i'.2) ?_
  rw [eq_top_iff, ← hWtop]
  refine iSup_le fun ij => ?_
  by_cases hij : W ij = ⊥
  · rw [hij]; exact bot_le
  · exact le_iSup_of_le (⟨ij, hij⟩ : ι) le_rfl

end CaseB

section Diag

open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.CTP CFSG.ClassicalInvolution.Phan

theorem exists_pair_of_index {Γ : Type*} [Group Γ] {p : ℕ} (hp : p.Prime) {E : Subgroup Γ}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) {F : Subgroup E} (hF : F.index = p) :
    ∃ a b : E, a ∈ F ∧ b ∈ F ∧ (a : Γ) ≠ 1 ∧ (b : Γ) ∉ Subgroup.zpowers (a : Γ) := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hfin : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  have hcF : Nat.card F = p ^ 2 := by
    have h1 := Subgroup.card_mul_index F
    rw [hF, hcard] at h1
    refine Nat.eq_of_mul_eq_mul_right hp.pos ?_
    rw [h1]
    ring
  have hexp : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hE.2 x x.2)
  obtain ⟨a, haF, ha1⟩ : ∃ a ∈ F, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 hcon
    rw [this, Subgroup.card_bot] at hcF
    have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hp.one_lt
    omega
  have hord : orderOf a = p := orderOf_eq_prime (hexp a) ha1
  obtain ⟨b, hbF, hb⟩ : ∃ b ∈ F, b ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have hle : F ≤ Subgroup.zpowers a := fun x hx => hcon x hx
    have h1 := Subgroup.card_le_of_le hle
    rw [hcF, Nat.card_zpowers, hord] at h1
    have h2 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h2
    omega
  refine ⟨a, b, haF, hbF, fun h1 => ha1 (Subtype.ext h1), fun hmem => hb ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow, hk])⟩

variable {ℓ f p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem hyperGen_of_unitary_diag_gu (h : UnitaryFieldData ℓ f K) {n : ℕ} (hp : p.Prime)
    (hpq : p ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2) {Γ : Type*} [Group Γ]
    (κ : primeFormUnitary h (idGram K (n + 1)) →* Γ) {E : Subgroup Γ}
    (hEκ : ∀ e ∈ E, ∃ a : primeFormUnitary h (idGram K (n + 1)), κ a = e)
    (hker : ∀ g ∈ κ.ker, ∃ c : K,
      ((g : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = c • 1)
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) {H : Subgroup (SUid σ₀ (n + 1))}
    (hH : HyperLift h κ E H)
    (hcomm : ∀ x y : primeFormUnitary h (idGram K (n + 1)), κ x ∈ E → κ y ∈ E → x * y = y * x)
    (hpow : ∀ x : primeFormUnitary h (idGram K (n + 1)), κ x ∈ E → x ^ (ℓ ^ f + 1) = 1) :
    H = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  set Eh : Subgroup (primeFormUnitary h (idGram K (n + 1))) := E.comap κ with hEh
  have hGcomm : ∀ u ∈ Eh, ∀ v ∈ Eh, u * v = v * u := fun u hu v hv => hcomm u v hu hv
  have hGpow : ∀ u ∈ Eh, u ^ (ℓ ^ f + 1) = 1 := fun u hu => hpow u hu
  have hdvdK : ℓ ^ f + 1 ∣ Nat.card K - 1 := by
    have h1 : Nat.card K - 1 = (ℓ ^ f - 1) * (ℓ ^ f + 1) := by
      rw [h.card_eq_sq, mul_comm]
      have := Nat.mul_self_sub_mul_self_eq (ℓ ^ f) 1
      simpa [sq] using this
    rw [h1]
    exact Dvd.intro_left _ rfl
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd_natCard_sub_one hdvdK
  haveI : NeZero (ℓ ^ f + 1) := ⟨by omega⟩
  obtain ⟨P, hP⟩ :=
    CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m h hζ dvd_rfl Eh hGcomm hGpow
  let Pg : GL (Fin (n + 1)) K := (P : GL (Fin (n + 1)) K)
  let Dg : primeFormUnitary h (idGram K (n + 1)) → GL (Fin (n + 1)) K := fun x =>
    Pg⁻¹ * (x : GL (Fin (n + 1)) K) * Pg
  have hdiag : ∀ x : Eh,
      ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K).IsDiag :=
    fun x => hP x x.2
  have hDmul : ∀ x y : primeFormUnitary h (idGram K (n + 1)), Dg (x * y) = Dg x * Dg y := by
    intro x y
    simp only [Dg, Subgroup.coe_mul]
    group
  have hD1 : Dg 1 = 1 := by simp [Dg]
  let χ : Fin (n + 1) → Eh →* K := fun c =>
    { toFun := fun x => ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c
      map_one' := by simp [hD1]
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul, hDmul, Units.val_mul]
        exact mul_apply_diag_of_isDiag (hdiag x) c }
  have hnz : ∀ (x : Eh) (c : Fin (n + 1)),
      ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c ≠ 0 := by
    intro x c
    have h1 : (((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
        (((Dg x)⁻¹ : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) c c = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [mul_apply_diag_of_isDiag (hdiag x)] at h1
    exact left_ne_zero_of_mul_eq_one h1
  let π' : Eh →* E := (κ.comp Eh.subtype).codRestrict E fun x => x.2
  have hπ' : Function.Surjective π' := by
    rintro ⟨e, he⟩
    obtain ⟨g, hg⟩ := hEκ e he
    exact ⟨⟨g, show κ g ∈ E by rw [hg]; exact he⟩, Subtype.ext hg⟩
  have hπ'v : ∀ x : Eh, ((π' x : E) : Γ) = κ x := fun _ => rfl
  have hscal : ∀ x : Eh, π' x = 1 → ∀ a b : Fin (n + 1), χ a x = χ b x := by
    intro x hx a b
    have hx' : (x : primeFormUnitary h (idGram K (n + 1))) ∈ κ.ker := by
      rw [MonoidHom.mem_ker, ← hπ'v, hx]
      rfl
    obtain ⟨c, hc⟩ := hker _ hx'
    have hD : ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = c • 1 := by
      have hPinv : ((Pg⁻¹ : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
          (Pg : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = 1 := Units.inv_mul _
      simp only [Dg, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPinv]
    show ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) a a =
      ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) b b
    rw [hD]
    simp
  have hexpE : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hE.2 x x.2)
  have hhyper : ∀ i : Fin n, ∃ F : Subgroup E, F.index = p ∧ ∀ x : Eh, π' x ∈ F →
      χ i.castSucc x = χ i.succ x := by
    intro i
    let ρ : Eh →* Kˣ := (χ i.castSucc).toHomUnits / (χ i.succ).toHomUnits
    have hkerρ : π'.ker ≤ ρ.ker := fun x hx =>
      (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeInnerAux.ratio_apply_eq_one_iff
        _ _ x).2 (hscal x hx _ _)
    let ρb : E →* Kˣ := (QuotientGroup.lift π'.ker ρ hkerρ).comp
      (QuotientGroup.quotientKerEquivOfSurjective π' hπ').symm.toMonoidHom
    have hρb : ∀ x : Eh, ρb (π' x) = ρ x := by
      intro x
      have h1 : (QuotientGroup.quotientKerEquivOfSurjective π' hπ').symm (π' x) =
          (x : Eh ⧸ π'.ker) := (MulEquiv.symm_apply_eq _).2 rfl
      show QuotientGroup.lift π'.ker ρ hkerρ
        ((QuotientGroup.quotientKerEquivOfSurjective π' hπ').symm (π' x)) = ρ x
      rw [h1]
      rfl
    obtain ⟨F, hF, hFeq⟩ := exists_hyperplane_eq_of_hom hp hexpE hcard
      ((Units.coeHom K).comp ρb) 1
    refine ⟨F, hF, fun x hx => ?_⟩
    have h1 : ρb (π' x) = 1 := Units.ext (by simpa using hFeq _ hx)
    rw [hρb] at h1
    exact (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeInnerAux.ratio_apply_eq_one_iff
      _ _ x).1 h1
  let ε : SUid σ₀ (n + 1) ≃* unitarySU ℓ f K (n + 1) :=
    MulEquiv.subgroupCongr (suid_unitaryInvolution_eq h (n + 1))
  have hS : H.comap ε.symm.toMonoidHom = ⊤ := by
    refine eq_top_of_blocks_mem h hq P _ fun i y A hA => ?_
    obtain ⟨F, hF, hFc⟩ := hhyper i
    obtain ⟨e₁, e₂, he₁F, he₂F, he₁1, he₂⟩ := exists_pair_of_index hp hE hcard hF
    obtain ⟨x₁, rfl⟩ := hπ' e₁
    obtain ⟨x₂, rfl⟩ := hπ' e₂
    have hcx : ∀ x : Eh, π' x ∈ F →
        (((conjSU h P y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
            (((x : primeFormUnitary h (idGram K (n + 1))) : GL (Fin (n + 1)) K) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
          (((x : primeFormUnitary h (idGram K (n + 1))) : GL (Fin (n + 1)) K) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
            (((conjSU h P y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) K) := by
      intro x hx
      have hxχ := hFc x hx
      have hD : ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
          Matrix.diagonal (fun c => ((Dg x : GL (Fin (n + 1)) K) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c) := ((hdiag x).diagonal_diag).symm
      have hYD : ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Dg x =
          Dg x * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) := by
        apply Units.ext
        simp only [Units.val_mul]
        rw [hA, hD]
        exact blockMat_mul_diagonal_comm (by omega) _ (hnz x) i.castSucc i.succ (by simp)
          (by simp) hxχ A
      have hxeq : ((x : primeFormUnitary h (idGram K (n + 1))) : GL (Fin (n + 1)) K) =
          Pg * Dg x * Pg⁻¹ := by simp [Dg, mul_assoc]
      have hcxG : ((conjSU h P y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) *
          ((x : primeFormUnitary h (idGram K (n + 1))) : GL (Fin (n + 1)) K) =
          ((x : primeFormUnitary h (idGram K (n + 1))) : GL (Fin (n + 1)) K) *
            ((conjSU h P y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) := by
        rw [coe_conjSU, hxeq]
        calc Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ * (Pg * Dg x * Pg⁻¹)
            = Pg * (((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Dg x) * Pg⁻¹ := by
              group
          _ = Pg * (Dg x * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K)) * Pg⁻¹ := by
              rw [hYD]
          _ = Pg * Dg x * Pg⁻¹ *
              (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹) := by group
      have := congrArg Units.val hcxG
      simpa only [Units.val_mul] using this
    show ε.symm (conjSU h P y) ∈ H
    exact hH (ε.symm (conjSU h P y)) x₁ x₂ (π' x₁).2 (π' x₂).2 he₁1 he₂ (hcx x₁ he₁F)
      (hcx x₂ he₂F)
  rw [eq_top_iff]
  intro g _
  have hg : ε g ∈ H.comap ε.symm.toMonoidHom := by rw [hS]; exact Subgroup.mem_top _
  have : ε.symm (ε g) ∈ H := hg
  rwa [MulEquiv.symm_apply_apply] at this

end Diag

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3

end
