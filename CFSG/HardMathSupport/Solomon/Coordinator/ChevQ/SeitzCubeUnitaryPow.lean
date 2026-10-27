module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryRest

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryPowAux

open Matrix CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.SeitzGeneration.Centers
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryAux
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryRestAux

section FourTv

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] def tvMap (σ : K ≃+* K) (x : Fin n → K) (γ : K) (v : Fin n → K) : Fin n → K :=
  v + (γ * herm σ x v) • x

theorem tvMap_def (x : Fin n → K) (γ : K) (v : Fin n → K) :
    tvMap σ x γ v = v + (γ * herm σ x v) • x := rfl

theorem false_of_four_tvMap (hσ : ∀ c, σ (σ c) = c) {a b d u : Fin n → K} {γ lam : K}
    (hγ : γ ≠ 0) (hindep : ∀ x y z : K, x • a + y • b + z • d = 0 → x = 0 ∧ y = 0 ∧ z = 0)
    (hbb : herm σ b b = 0) (hbd : herm σ b d = herm σ a b) (hu : herm σ d u ≠ 0)
    (hb' : tvMap σ d γ (tvMap σ b (-γ) (tvMap σ a γ (tvMap σ b (-γ) b))) = lam • b)
    (hd' : tvMap σ d γ (tvMap σ b (-γ) (tvMap σ a γ (tvMap σ b (-γ) d))) = lam • d)
    (hu' : tvMap σ d γ (tvMap σ b (-γ) (tvMap σ a γ (tvMap σ b (-γ) u))) = lam • u) : False := by
  have hab : herm σ a b = 0 ∧ lam = 1 := by
    have e1 : tvMap σ b (-γ) b = b := by rw [tvMap_def, hbb, mul_zero, zero_smul, add_zero]
    rw [e1] at hb'
    set t := herm σ d (tvMap σ b (-γ) (tvMap σ a γ b)) with ht
    have e : tvMap σ b (-γ) (tvMap σ a γ b) + (γ * t) • d = lam • b := hb'
    rw [tvMap_def, tvMap_def, herm_add_right, herm_smul_right, hbb] at e
    obtain ⟨h1, h2, -⟩ := hindep (γ * herm σ a b) (1 - γ * (γ * herm σ a b * herm σ b a) - lam)
      (γ * t) (by linear_combination (norm := module) e)
    have hs : herm σ a b = 0 := (mul_eq_zero.mp h1).resolve_left hγ
    refine ⟨hs, ?_⟩
    rw [hs] at h2
    linear_combination -h2
  obtain ⟨hs, hl⟩ := hab
  subst hl
  have hba : herm σ b a = 0 := by rw [herm_conj σ hσ, hs, map_zero]
  have hbd0 : herm σ b d = 0 := by rw [hbd, hs]
  have hdb : herm σ d b = 0 := by rw [herm_conj σ hσ, hbd0, map_zero]
  have had : herm σ a d = 0 := by
    have e1 : tvMap σ b (-γ) d = d := by rw [tvMap_def, hbd0, mul_zero, zero_smul, add_zero]
    rw [e1] at hd'
    set t := herm σ d (tvMap σ b (-γ) (tvMap σ a γ d)) with ht
    have e : tvMap σ b (-γ) (tvMap σ a γ d) + (γ * t) • d = (1 : K) • d := hd'
    rw [tvMap_def, tvMap_def, herm_add_right, herm_smul_right, hbd0, hba] at e
    obtain ⟨h1, -, -⟩ := hindep (γ * herm σ a d) 0 (γ * t - 0)
      (by linear_combination (norm := module) e)
    exact (mul_eq_zero.mp h1).resolve_left hγ
  have hda : herm σ d a = 0 := by rw [herm_conj σ hσ, had, map_zero]
  have e : tvMap σ d γ (tvMap σ b (-γ) (tvMap σ a γ (tvMap σ b (-γ) u))) = (1 : K) • u := hu'
  simp only [tvMap_def, herm_add_right, herm_smul_right, hbb, hs, hba, hbd0, hdb, had,
    hda] at e
  obtain ⟨-, -, h3⟩ := hindep (γ * herm σ a u) (-(2 * γ * herm σ b u)) (γ * herm σ d u)
    (by linear_combination (norm := module) e)
  exact hu ((mul_eq_zero.mp h3).resolve_left hγ)

end FourTv

section ExtMat

variable {K : Type*} [Field K] {σ : K ≃+* K} {n m : ℕ}

theorem extMat_mul {x : Fin m → Fin n → K} (hx : ONExt.IsON σ x)
    (g g' : Matrix (Fin m) (Fin m) K) :
    ONExt.extMat σ x (g * g') = ONExt.extMat σ x g * ONExt.extMat σ x g' := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← mulVec_mulVec]
  obtain ⟨c, u, hu, hv⟩ := ONExt.exists_decomp hx (Pi.single i 1)
  rw [hv, ONExt.extMat_mulVec hx _ c hu, ONExt.extMat_mulVec hx _ c hu,
    ONExt.extMat_mulVec hx _ _ hu, mulVec_mulVec]

theorem extMat_one (x : Fin m → Fin n → K) : ONExt.extMat σ x 1 = 1 := by
  simp [ONExt.extMat]

theorem mat_eq_of_eigen {p : ℕ} {B M M' : Matrix (Fin n) (Fin n) K} {lam ζ : K}
    (hsup : ⨆ j : Fin p, Module.End.eigenspace (Matrix.toLin' B) (lam * ζ ^ (j : ℕ)) = ⊤)
    (h : ∀ (j : Fin p) (v : Fin n → K), B *ᵥ v = (lam * ζ ^ (j : ℕ)) • v → M *ᵥ v = M' *ᵥ v) :
    M = M' := by
  apply Matrix.toLin'.injective
  have hle : (⨆ j : Fin p, Module.End.eigenspace (Matrix.toLin' B) (lam * ζ ^ (j : ℕ))) ≤
      LinearMap.eqLocus (Matrix.toLin' M) (Matrix.toLin' M') := by
    refine iSup_le fun j v hv => ?_
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv
    rw [LinearMap.mem_eqLocus, Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact h j v hv
  rw [hsup] at hle
  exact LinearMap.ext fun v => hle Submodule.mem_top

end ExtMat


section Shift

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem pow_fin_add_one [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p) (j : Fin p) :
    ζ ^ ((j + 1 : Fin p) : ℕ) = ζ ^ (j : ℕ) * ζ := by
  rw [Fin.val_add, ← pow_eq_pow_mod hζ, pow_add]
  congr 1
  rw [pow_eq_pow_mod hζ ((1 : Fin p) : ℕ), Fin.val_one', Nat.mod_mod, ← pow_eq_pow_mod hζ,
    pow_one]

theorem mulVec_X_eig [NeZero p] {X B : SUid σ₀ n} {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hBX : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {lam : K} (j : Fin p) {v : Fin n → K}
    (hv : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = (lam * ζ ^ (j : ℕ)) • v) :
    ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (X • v) =
      (lam * ζ ^ ((j + 1 : Fin p) : ℕ)) • (X • v) := by
  rw [smul_def, mulVec_mulVec, hBX, Matrix.smul_mulVec, ← mulVec_mulVec, hv, mulVec_smul,
    smul_smul, pow_fin_add_one hζ]
  congr 1
  ring

theorem mulVec_Xinv_eig [NeZero p] {X B : SUid σ₀ n} {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hp : 2 ≤ p)
    (hBX : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {lam : K} (j : Fin p) {v : Fin n → K}
    (hv : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = (lam * ζ ^ (j : ℕ)) • v) :
    ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (X⁻¹ • v) =
      (lam * ζ ^ ((j - 1 : Fin p) : ℕ)) • (X⁻¹ • v) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  set u := X⁻¹ • v with hu
  have hXu : X • u = v := by rw [hu, smul_inv_smul]
  have h1 : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (X • u) =
      ζ • (X • (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u)) := by
    rw [smul_def, smul_def, mulVec_mulVec, hBX, Matrix.smul_mulVec, ← mulVec_mulVec]
  rw [hXu, hv] at h1
  have h2 : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u =
      (ζ⁻¹ * (lam * ζ ^ (j : ℕ))) • u := by
    have h3 := congrArg (fun z => X⁻¹ • z) h1
    simp only [smul_comm X⁻¹ (lam * ζ ^ (j : ℕ)), smul_comm X⁻¹ ζ, inv_smul_smul] at h3
    rw [← hu] at h3
    rw [← smul_smul, h3, smul_smul, inv_mul_cancel₀ hζ0, one_smul]
  rw [h2]
  congr 1
  have h4 := pow_fin_add_one hζ (j - 1)
  rw [sub_add_cancel] at h4
  rw [h4]
  field_simp

end Shift

section Local

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem exists_mem_eq_four_tv [NeZero p] (h : UnitaryFieldData ℓ f K) (hp : p.Prime)
    (hp2 : p ≠ 2) {G : Type*} [Group G] [Finite G] (π : SUid σ₀ n →* G) {E : Subgroup G}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    {X B r : SUid σ₀ n} (hXE : π X ∈ E) (hBE : π B ∈ E) (hrE : π r ∈ E) (hr1 : π r ≠ 1)
    (hB1 : π B ≠ 1) (hBr : π B ∉ Subgroup.zpowers (π r)) (hXB : π X ∉ Subgroup.zpowers (π B))
    (hXr : π X ∉ Subgroup.zpowers (π r)) (hrX : r * X = X * r) (hrB : r * B = B * r)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hζN : h.bar ζ * ζ = 1)
    (hBX : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {β : K} (hXp : ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1)
    {lam : K} (hlamN : h.bar lam * lam = 1)
    (hBp : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (lam ^ p) • 1)
    {m : ℕ} {xs : Fin m → Fin n → K} (hxsON : ONExt.IsON σ₀ xs)
    (hspan : Submodule.span K (Set.range xs) = Module.End.eigenspace
      (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) lam)
    {w : Fin n → K} (hwU : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = lam • w)
    (hww : herm σ₀ w w = 0) {γ : K} (hγ : γ + σ₀ γ = 0) :
    ∃ y : SUid σ₀ n, π y ∈ hyperClosure p ⊤ E ∧
      (∀ (j : Fin p) (v : Fin n → K), j ≠ 0 →
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = (lam * ζ ^ (j : ℕ)) • v →
          y • v = v) ∧
      ∀ v : Fin n → K, ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = lam • v →
        y • v = tvMap σ₀ (r • w) γ (tvMap σ₀ w (-γ) (tvMap σ₀ (r⁻¹ • w) γ
          (tvMap σ₀ w (-γ) v))) := by
  classical
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  have hσi := hσ.invol
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpK : (p : K) ≠ 0 := heis_natCast_ne_zero hζ hp.two_le
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have h10 : (1 : Fin p) ≠ 0 := by
    intro h0
    have := congrArg Fin.val h0
    rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega : 1 < p)] at this
    omega
  set Bm : Matrix (Fin n) (Fin n) K := ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hBm
  set Xm : Matrix (Fin n) (Fin n) K := ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hXm
  set rm : Matrix (Fin n) (Fin n) K := ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hrm
  set rim : Matrix (Fin n) (Fin n) K := (((r⁻¹ : SUid σ₀ n) : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K) with hrim
  set Xim : Matrix (Fin n) (Fin n) K := (((X⁻¹ : SUid σ₀ n) : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K) with hXim
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      subst h0
      apply hr1
      have : r = 1 := Subtype.ext (Units.ext (Subsingleton.elim _ _))
      rw [this, map_one]
    · exact h0
  have hβN : σ₀ β * β = 1 := by rw [hσb]; exact bar_mul_eq_one_of_SUid_scalar h hn hXp
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hlamN
    exact zero_ne_one hlamN
  have hpowT : ∀ (M : Matrix (Fin n) (Fin n) K) (c : K), M ^ p = c • 1 →
      (Matrix.toLin' M) ^ p = algebraMap K (Module.End K (Fin n → K)) c := by
    intro M c hM
    have h2 := congrArg Matrix.toLinAlgEquiv' hM
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  have hsup : ⨆ j : Fin p, Module.End.eigenspace (Matrix.toLin' Bm) (lam * ζ ^ (j : ℕ)) = ⊤ :=
    NonPth.iSup_eigenspace_eq_top_p hp hpK hζ hlam0 (hpowT _ _ hBp)
  have hlamkN : ∀ k : ℕ, h.bar (lam * ζ ^ k) * (lam * ζ ^ k) = 1 := by
    intro k
    rw [map_mul, map_pow]
    calc h.bar lam * h.bar ζ ^ k * (lam * ζ ^ k) = (h.bar lam * lam) * (h.bar ζ * ζ) ^ k := by
          ring
      _ = 1 := by rw [hlamN, hζN, one_pow, one_mul]
  have horthB : ∀ j j' : Fin p, j ≠ j' → ∀ u v, Bm *ᵥ u = (lam * ζ ^ (j : ℕ)) • u →
      Bm *ᵥ v = (lam * ζ ^ (j' : ℕ)) • v → herm σ₀ u v = 0 := fun j j' hjj u v hu hv =>
    herm_eq_zero_of_eigen hu hv (bar_mul_ne_one h hlam0 hlamN hζ hζN hjj)
  have heig0 : ∀ v, Bm *ᵥ v = lam • v ↔ Bm *ᵥ v = (lam * ζ ^ ((0 : Fin p) : ℕ)) • v := by
    intro v
    rw [Fin.val_zero, pow_zero, mul_one]
  have hmemU : ∀ v, v ∈ Module.End.eigenspace (Matrix.toLin' Bm) lam ↔ Bm *ᵥ v = lam • v :=
    fun v => by rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have hxsU : ∀ i, Bm *ᵥ xs i = lam • xs i := fun i =>
    (hmemU _).1 (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)
  have horthU : ∀ (j : Fin p) (v : Fin n → K), j ≠ 0 → Bm *ᵥ v = (lam * ζ ^ (j : ℕ)) • v →
      ∀ i, herm σ₀ (xs i) v = 0 := fun j v hj hv i =>
    horthB 0 j (Ne.symm hj) _ _ ((heig0 _).1 (hxsU i)) hv
  have hrri : rm * rim = 1 := by
    rw [hrm, hrim, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have hrir : rim * rm = 1 := by
    rw [hrm, hrim, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hXXi : Xm * Xim = 1 := by
    rw [hXm, hXim, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have hXiX : Xim * Xm = 1 := by
    rw [hXm, hXim, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hrBm : rm * Bm = Bm * rm := coe_comm hrB
  have hriB : r⁻¹ * B = B * r⁻¹ := (Commute.inv_left hrB).eq
  have hriBm : rim * Bm = Bm * rim := coe_comm hriB
  have hrXi : r * X⁻¹ = X⁻¹ * r := (Commute.inv_right hrX).eq
  have hriX : r⁻¹ * X = X * r⁻¹ := (Commute.inv_left hrX).eq
  have hrEig : ∀ (j : Fin p) v, Bm *ᵥ v = (lam * ζ ^ (j : ℕ)) • v →
      Bm *ᵥ (r • v) = (lam * ζ ^ (j : ℕ)) • (r • v) := by
    intro j v hv
    rw [smul_def, mulVec_mulVec, ← hrBm, ← mulVec_mulVec, hv, mulVec_smul]
  have hriE : ∀ (j : Fin p) v, Bm *ᵥ v = (lam * ζ ^ (j : ℕ)) • v →
      Bm *ᵥ (r⁻¹ • v) = (lam * ζ ^ (j : ℕ)) • (r⁻¹ • v) := by
    intro j v hv
    rw [smul_def, mulVec_mulVec, ← hriBm, ← mulVec_mulVec, hv, mulVec_smul]
  have hcomE : ∀ g : SUid σ₀ n, g * B = B * g → ∀ (j : Fin p) v,
      Bm *ᵥ v = (lam * ζ ^ (j : ℕ)) • v → Bm *ᵥ (g • v) = (lam * ζ ^ (j : ℕ)) • (g • v) := by
    intro g hg j v hv
    rw [smul_def, mulVec_mulVec, ← coe_comm hg, ← mulVec_mulVec, hv, mulVec_smul]
  have hrUst : ∀ c, ∃ d, r • orthoEmb xs c = orthoEmb xs d := by
    refine exists_orthoEmb_of_stable hspan fun v hv => ?_
    rw [hmemU] at hv ⊢
    exact hrEig 0 v ((heig0 v).1 hv) |>.trans (by rw [Fin.val_zero, pow_zero, mul_one])
  have hrUst' : ∀ c, ∃ d, r⁻¹ • orthoEmb xs c = orthoEmb xs d := by
    refine exists_orthoEmb_of_stable hspan fun v hv => ?_
    rw [hmemU] at hv ⊢
    exact hriE 0 v ((heig0 v).1 hv) |>.trans (by rw [Fin.val_zero, pow_zero, mul_one])
  set Rr := ONExt.resMat σ₀ xs rm with hRr
  set Rri := ONExt.resMat σ₀ xs rim with hRri
  set Dm := ONExt.extMat σ₀ xs Rr with hDm
  set Dim := ONExt.extMat σ₀ xs Rri with hDim
  have hRR : Rr * Rri = 1 := by
    rw [hRr, hRri, ← ONExt.resMat_mul hxsON hrUst hrUst', mul_inv_cancel, ONExt.resMat_one hxsON]
  have hRR' : Rri * Rr = 1 := by
    rw [hRr, hRri, ← ONExt.resMat_mul hxsON hrUst' hrUst, inv_mul_cancel, ONExt.resMat_one hxsON]
  have hDDi : Dm * Dim = 1 := by rw [hDm, hDim, ← extMat_mul hxsON, hRR, extMat_one]
  have hDiD : Dim * Dm = 1 := by rw [hDm, hDim, ← extMat_mul hxsON, hRR', extMat_one]
  have hDiso : ∀ u v, herm σ₀ (Dm *ᵥ u) (Dm *ᵥ v) = herm σ₀ u v :=
    ONExt.herm_extMat hσi hxsON (ONExt.herm_resMat hxsON hrUst)
  have hDiiso : ∀ u v, herm σ₀ (Dim *ᵥ u) (Dim *ᵥ v) = herm σ₀ u v :=
    ONExt.herm_extMat hσi hxsON (ONExt.herm_resMat hxsON hrUst')
  have hDU : ∀ v, Bm *ᵥ v = lam • v → Dm *ᵥ v = r • v := by
    intro v hv
    obtain ⟨c, rfl⟩ := (mem_span_range_iff xs v).1 (hspan ▸ (hmemU v).2 hv)
    rw [hDm, ONExt.extMat_mulVec_orthoEmb hxsON, ONExt.orthoEmb_resMat_mulVec hxsON hrUst]
  have hDiU : ∀ v, Bm *ᵥ v = lam • v → Dim *ᵥ v = r⁻¹ • v := by
    intro v hv
    obtain ⟨c, rfl⟩ := (mem_span_range_iff xs v).1 (hspan ▸ (hmemU v).2 hv)
    rw [hDim, ONExt.extMat_mulVec_orthoEmb hxsON, ONExt.orthoEmb_resMat_mulVec hxsON hrUst']
  have hDo : ∀ (j : Fin p) v, j ≠ 0 → Bm *ᵥ v = (lam * ζ ^ (j : ℕ)) • v → Dm *ᵥ v = v :=
    fun j v hj hv => ONExt.extMat_mulVec_of_orth xs _ (horthU j v hj hv)
  have hDio : ∀ (j : Fin p) v, j ≠ 0 → Bm *ᵥ v = (lam * ζ ^ (j : ℕ)) • v → Dim *ᵥ v = v :=
    fun j v hj hv => ONExt.extMat_mulVec_of_orth xs _ (horthU j v hj hv)
  set cm := Xm * Dm * Xim * Dim with hcm
  have hcdet : cm.det = 1 := by
    have h1 : Xm.det * Xim.det = 1 := by rw [← det_mul, hXXi, det_one]
    have h2 : Dm.det * Dim.det = 1 := by rw [← det_mul, hDDi, det_one]
    rw [hcm, det_mul, det_mul, det_mul]
    linear_combination Dm.det * Dim.det * h1 + h2
  have hciso : ∀ u v, herm σ₀ (cm *ᵥ u) (cm *ᵥ v) = herm σ₀ u v := by
    intro u v
    rw [hcm, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
      ← mulVec_mulVec, ← mulVec_mulVec]
    rw [← smul_def σ₀ X, ← smul_def σ₀ X, herm_smul_smul, hDiso, ← smul_def σ₀ X⁻¹,
      ← smul_def σ₀ X⁻¹, herm_smul_smul, hDiiso]
  set c : SUid σ₀ n := mkSU σ₀ cm hcdet hciso with hc
  have hcv : ∀ v : Fin n → K, c • v = X • (Dm *ᵥ (X⁻¹ • (Dim *ᵥ v))) := by
    intro v
    rw [hc, mkSU_smul, hcm, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, smul_def,
      smul_def]
  have hc0 : ∀ v, Bm *ᵥ v = lam • v → c • v = r⁻¹ • v := by
    intro v hv
    have hv0 := (heig0 v).1 hv
    have h1 := hriE 0 v hv0
    have h2 := mulVec_Xinv_eig hζ hp.two_le hBX 0 h1
    have h01 : (0 - 1 : Fin p) ≠ 0 := by
      rw [zero_sub, neg_ne_zero]
      exact h10
    rw [hcv, hDiU v hv, hDo _ _ h01 h2, smul_inv_smul]
  have hc1 : ∀ v, Bm *ᵥ v = (lam * ζ ^ ((1 : Fin p) : ℕ)) • v → c • v = r • v := by
    intro v hv
    have h2 := mulVec_Xinv_eig hζ hp.two_le hBX 1 hv
    rw [sub_self] at h2
    rw [hcv, hDio 1 v h10 hv, hDU _ ((heig0 _).2 h2), ← mul_smul, ← hrX, mul_smul,
      smul_inv_smul]
  have hc2 : ∀ (j : Fin p) v, j ≠ 0 → j ≠ 1 → Bm *ᵥ v = (lam * ζ ^ (j : ℕ)) • v → c • v = v := by
    intro j v hj0 hj1 hv
    have h2 := mulVec_Xinv_eig hζ hp.two_le hBX j hv
    have hj : j - 1 ≠ 0 := fun h0 => hj1 (sub_eq_zero.mp h0)
    rw [hcv, hDio j v hj0 hv, hDo _ _ hj h2, smul_inv_smul]
  have hcE : ∀ (j : Fin p) v, Bm *ᵥ v = (lam * ζ ^ (j : ℕ)) • v →
      Bm *ᵥ (c • v) = (lam * ζ ^ (j : ℕ)) • (c • v) := by
    intro j v hv
    by_cases hj0 : j = 0
    · subst hj0
      rw [hc0 v ((heig0 v).2 hv)]
      exact hriE 0 v hv
    · by_cases hj1 : j = 1
      · subst hj1
        rw [hc1 v hv]
        exact hrEig 1 v hv
      · rw [hc2 j v hj0 hj1 hv]
        exact hv
  have hcB : c * B = B * c := by
    apply Subtype.ext
    apply Units.ext
    show (((c : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Bm =
      Bm * (((c : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    refine mat_eq_of_eigen hsup fun j v hv => ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, hv, mulVec_smul, ← smul_def σ₀ c v, hcE j v hv]
  have hcr : c * r = r * c := by
    apply Subtype.ext
    apply Units.ext
    show (((c : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * rm =
      rm * (((c : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    refine mat_eq_of_eigen hsup fun j v hv => ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← smul_def σ₀ r v, ← smul_def σ₀ c (r • v),
      ← smul_def σ₀ c v, ← smul_def σ₀ r (c • v)]
    have hrv := hrEig j v hv
    by_cases hj0 : j = 0
    · subst hj0
      rw [hc0 _ ((heig0 _).2 hrv), hc0 v ((heig0 v).2 hv), inv_smul_smul, smul_inv_smul]
    · by_cases hj1 : j = 1
      · subst hj1
        rw [hc1 _ hrv, hc1 v hv]
      · rw [hc2 j _ hj0 hj1 hrv, hc2 j v hj0 hj1 hv]
  set H := (hyperClosure p ⊤ E).comap π with hH
  have hcH : c ∈ H := mem_hyperClosure_of_comm hp hE hcard hrE hBE hr1 hBr
    (by rw [← map_mul, ← map_mul, hcr]) (by rw [← map_mul, ← map_mul, hcB])
  have hXH : X ∈ H := mem_hyperClosure_of_comm hp hE hcard hrE hXE hr1 hXr
    (by rw [← map_mul, ← map_mul, hrX]) rfl
  set ci := c * (X * c * X⁻¹) with hci
  have hciv : ∀ v : Fin n → K, ci • v = c • (X • (c • (X⁻¹ • v))) := by
    intro v
    rw [hci, mul_smul, mul_smul, mul_smul]
  have hci0 : ∀ v, Bm *ᵥ v = lam • v → ci • v = r⁻¹ • v := by
    intro v hv
    have hv0 := (heig0 v).1 hv
    have h2 := mulVec_Xinv_eig hζ hp.two_le hBX 0 hv0
    have h01 : (0 - 1 : Fin p) ≠ 0 := by
      rw [zero_sub, neg_ne_zero]; exact h10
    have h11 : (0 - 1 : Fin p) ≠ 1 := by
      intro h0
      have h3 : (0 : Fin p) = 1 + 1 := sub_eq_iff_eq_add.mp h0
      have h4 := congrArg Fin.val h3
      rw [Fin.val_zero, Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < p),
        Nat.mod_eq_of_lt (by omega : 2 < p)] at h4
      omega
    rw [hciv, hc2 _ _ h01 h11 h2, smul_inv_smul, hc0 v hv]
  have hci1 : ∀ v, Bm *ᵥ v = (lam * ζ ^ ((1 : Fin p) : ℕ)) • v → ci • v = v := by
    intro v hv
    have h2 := mulVec_Xinv_eig hζ hp.two_le hBX 1 hv
    rw [sub_self] at h2
    rw [hciv, hc0 _ ((heig0 _).2 h2), ← mul_smul X r⁻¹, ← hriX, mul_smul,
      smul_inv_smul, hc1 _ (hriE 1 v hv), smul_inv_smul]
  have hciE : ∀ (j : Fin p) v, Bm *ᵥ v = (lam * ζ ^ (j : ℕ)) • v →
      Bm *ᵥ (ci • v) = (lam * ζ ^ (j : ℕ)) • (ci • v) := by
    intro j v hv
    rw [hciv]
    refine hcE j _ ?_
    have h2 := mulVec_Xinv_eig hζ hp.two_le hBX j hv
    have h3 := hcE _ _ h2
    have h4 := mulVec_X_eig hζ hBX _ h3
    rwa [sub_add_cancel] at h4
  have hciB : ci * B = B * ci := by
    apply Subtype.ext
    apply Units.ext
    show (((ci : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Bm =
      Bm * (((ci : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    refine mat_eq_of_eigen hsup fun j v hv => ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, hv, mulVec_smul, ← smul_def σ₀ ci v, hciE j v hv]
  have hciH : ci ∈ H := H.mul_mem hcH (H.mul_mem (H.mul_mem hXH hcH) (H.inv_mem hXH))
  have hwB0 : Bm *ᵥ w = (lam * ζ ^ 0) • w := by rw [pow_zero, mul_one]; exact hwU
  have hXkB : ∀ k : ℕ, Bm *ᵥ ((X ^ k) • w) = (lam * ζ ^ k) • ((X ^ k) • w) := fun k => by
    have := mulVec_pow_smul_of_qcomm hBX k 0 w hwB0
    rwa [zero_add] at this
  have horthS : ∀ k k' : Fin p, herm σ₀ ((X ^ (k : ℕ)) • w) ((X ^ (k' : ℕ)) • w) = 0 := by
    intro k k'
    by_cases hkk : k = k'
    · subst hkk
      rw [herm_smul_smul, hww]
    · exact horthB k k' hkk _ _ (hXkB k) (hXkB k')
  obtain ⟨S, hS, hXS⟩ := exists_siegel_orbit hσi (p := p) hXp hβN horthS hγ
  have hBS : B * S = S * B := siegel_comm_of_eigen hS
    (lam := fun k : Fin p => lam * ζ ^ (k : ℕ)) (fun k => by rw [smul_def]; exact hXkB k)
    (fun k => by rw [hσb]; exact hlamkN _)
  have hSH : S ∈ H := mem_hyperClosure_of_comm hp hE hcard hBE hXE hB1 hXB
    (by rw [← map_mul, ← map_mul, hBS]) (by rw [← map_mul, ← map_mul, hXS])
  have hS0 : ∀ v, Bm *ᵥ v = lam • v → S • v = tvMap σ₀ w γ v := by
    intro v hv
    have hv0 := (heig0 v).1 hv
    rw [hS, tvMap_def]
    congr 1
    rw [Finset.sum_eq_single (0 : Fin p)]
    · simp
    · intro k _ hk0
      have h0 : herm σ₀ ((X ^ (k : ℕ)) • w) v = 0 := by
        refine horthB k 0 hk0 _ _ ?_ hv0
        simpa using hXkB k
      rw [h0, mul_zero, zero_smul]
    · intro h0
      exact absurd (Finset.mem_univ _) h0
  have htvU : ∀ v, Bm *ᵥ v = lam • v → ∀ γ' : K,
      Bm *ᵥ (tvMap σ₀ w γ' v) = lam • tvMap σ₀ w γ' v := by
    intro v hv γ'
    rw [tvMap_def, mulVec_add, mulVec_smul, hv, hwU, smul_add, smul_comm lam]
  have hSi0 : ∀ v, Bm *ᵥ v = lam • v → S⁻¹ • v = tvMap σ₀ w (-γ) v := by
    intro v hv
    rw [inv_smul_eq_iff, hS0 _ (htvU v hv _), tvMap_def, tvMap_def, herm_add_right,
      herm_smul_right, hww]
    module
  have hSE : ∀ (j : Fin p) v, Bm *ᵥ v = (lam * ζ ^ (j : ℕ)) • v →
      Bm *ᵥ (S • v) = (lam * ζ ^ (j : ℕ)) • (S • v) := hcomE S hBS.symm
  have hSiE : ∀ (j : Fin p) v, Bm *ᵥ v = (lam * ζ ^ (j : ℕ)) • v →
      Bm *ᵥ (S⁻¹ • v) = (lam * ζ ^ (j : ℕ)) • (S⁻¹ • v) :=
    hcomE S⁻¹ (Commute.inv_left hBS.symm).eq
  set Z := S * c * S⁻¹ * c⁻¹ with hZ
  have hZH : Z ∈ H := H.mul_mem (H.mul_mem (H.mul_mem hSH hcH) (H.inv_mem hSH)) (H.inv_mem hcH)
  have hrU : ∀ v, Bm *ᵥ v = lam • v → Bm *ᵥ (r • v) = lam • (r • v) := fun v hv =>
    (hrEig 0 v ((heig0 v).1 hv)).trans (by rw [Fin.val_zero, pow_zero, mul_one])
  have hriU : ∀ v, Bm *ᵥ v = lam • v → Bm *ᵥ (r⁻¹ • v) = lam • (r⁻¹ • v) := fun v hv =>
    (hriE 0 v ((heig0 v).1 hv)).trans (by rw [Fin.val_zero, pow_zero, mul_one])
  have hcinv0 : ∀ v, Bm *ᵥ v = lam • v → c⁻¹ • v = r • v := by
    intro v hv
    rw [inv_smul_eq_iff, hc0 _ (hrU v hv), inv_smul_smul]
  have hcinv2 : ∀ (j : Fin p) v, j ≠ 0 → j ≠ 1 → Bm *ᵥ v = (lam * ζ ^ (j : ℕ)) • v →
      c⁻¹ • v = v := by
    intro j v hj0 hj1 hv
    rw [inv_smul_eq_iff, hc2 j v hj0 hj1 hv]
  have hZ0 : ∀ v, Bm *ᵥ v = lam • v →
      Z • v = tvMap σ₀ w γ (r⁻¹ • tvMap σ₀ w (-γ) (r • v)) := by
    intro v hv
    have h1 := hrU v hv
    have h2 := htvU _ h1 (-γ)
    rw [hZ, mul_smul, mul_smul, mul_smul, hcinv0 v hv, hSi0 _ h1, hc0 _ h2, hS0 _ (hriU _ h2)]
  have hZE : ∀ (j : Fin p) v, Bm *ᵥ v = (lam * ζ ^ (j : ℕ)) • v →
      Bm *ᵥ (Z⁻¹ • v) = (lam * ζ ^ (j : ℕ)) • (Z⁻¹ • v) := by
    intro j v hv
    have hBZ : Commute B Z := by
      have h1 : Commute B S := hBS
      have h2 : Commute B c := Commute.symm hcB
      rw [hZ]
      exact ((h1.mul_right h2).mul_right h1.inv_right).mul_right h2.inv_right
    exact hcomE Z⁻¹ (Commute.symm hBZ.inv_right).eq j v hv
  have hZinv0 : ∀ v, Bm *ᵥ v = lam • v →
      Z⁻¹ • v = r⁻¹ • tvMap σ₀ w γ (r • tvMap σ₀ w (-γ) v) := by
    intro v hv
    have h1 := htvU v hv (-γ)
    have h2 := hrU _ h1
    have hZi : Z⁻¹ = c * S * c⁻¹ * S⁻¹ := by rw [hZ]; group
    rw [hZi, mul_smul, mul_smul, mul_smul, hSi0 v hv, hcinv0 _ h1, hS0 _ h2, hc0 _ (htvU _ h2 γ)]
  have hZ2 : ∀ (j : Fin p) v, j ≠ 0 → j ≠ 1 → Bm *ᵥ v = (lam * ζ ^ (j : ℕ)) • v → Z • v = v := by
    intro j v hj0 hj1 hv
    have h1 := hSiE j v hv
    rw [hZ, mul_smul, mul_smul, mul_smul, hcinv2 j v hj0 hj1 hv, hc2 j _ hj0 hj1 h1,
      smul_inv_smul]
  refine ⟨ci⁻¹ * Z * ci * Z⁻¹, ?_, ?_, ?_⟩
  · exact H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem hciH) hZH) hciH) (H.inv_mem hZH)
  · intro j v hj0 hv
    rw [mul_smul, mul_smul, mul_smul]
    by_cases hj1 : j = 1
    · subst hj1
      have h1 := hZE 1 v hv
      rw [hci1 _ h1, smul_inv_smul, inv_smul_eq_iff, hci1 v hv]
    · have hZi : Z⁻¹ • v = v := by rw [inv_smul_eq_iff, hZ2 j v hj0 hj1 hv]
      rw [hZi, hZ2 j _ hj0 hj1 (hciE j v hv), inv_smul_smul]
  · intro v hv
    have h1 := htvU v hv (-γ)
    have h2 := hrU _ h1
    have h3 := htvU _ h2 γ
    have h4 := hriU _ h3
    rw [mul_smul, mul_smul, mul_smul, hZinv0 v hv, hci0 _ h4, hZ0 _ (hriU _ h4)]
    have hcinv : ci⁻¹ • (tvMap σ₀ w γ (r⁻¹ • tvMap σ₀ w (-γ) (r • (r⁻¹ • (r⁻¹ •
        tvMap σ₀ w γ (r • tvMap σ₀ w (-γ) v)))))) =
        r • (tvMap σ₀ w γ (r⁻¹ • tvMap σ₀ w (-γ) (r • (r⁻¹ • (r⁻¹ •
        tvMap σ₀ w γ (r • tvMap σ₀ w (-γ) v)))))) := by
      rw [inv_smul_eq_iff, hci0 _ (hrU _ ?_), inv_smul_smul]
      refine htvU _ (hriU _ (htvU _ (hrU _ (hriU _ h4)) _)) _
    rw [hcinv, smul_inv_smul]
    have hconj : ∀ (x u : Fin n → K) (γ' : K), r • tvMap σ₀ x γ' (r⁻¹ • u) =
        tvMap σ₀ (r • x) γ' u := by
      intro x u γ'
      rw [tvMap_def, tvMap_def, smul_add, smul_inv_smul, smul_comm]
      congr 3
      rw [← herm_smul_smul σ₀ r, smul_inv_smul]
    have hconj' : ∀ (x u : Fin n → K) (γ' : K), r⁻¹ • tvMap σ₀ x γ' (r • u) =
        tvMap σ₀ (r⁻¹ • x) γ' u := by
      intro x u γ'
      rw [tvMap_def, tvMap_def, smul_add, inv_smul_smul, smul_comm]
      congr 3
      rw [← herm_smul_smul σ₀ r⁻¹, inv_smul_smul]
    rw [hconj, hconj']

end Local


section Centres

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem indep_three {r : SUid σ₀ n} (hp : p.Prime) (hp3 : 3 ≤ p) {α : K}
    (hrp : ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = α • 1)
    (hα : ¬ ∃ c : K, c ^ p = α) {w : Fin n → K} (hw : w ≠ 0) (x y z : K)
    (h0 : x • (r⁻¹ • w) + y • w + z • (r • w) = 0) : x = 0 ∧ y = 0 ∧ z = 0 := by
  classical
  set T := Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hT
  have hrT : T ^ p = algebraMap K (Module.End K (Fin n → K)) α := by
    have h2 := congrArg Matrix.toLinAlgEquiv' hrp
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  have hv0 : r⁻¹ • w ≠ 0 := fun h1 => hw (by simpa using congrArg (fun u => r • u) h1)
  have hT1 : T (r⁻¹ • w) = w := by rw [hT, Matrix.toLin'_apply, ← smul_def, smul_inv_smul]
  have hT2 : T w = r • w := by rw [hT, Matrix.toLin'_apply, ← smul_def]
  set c : Fin 3 → K := ![x, y, z] with hc
  have haev : Polynomial.aeval T (∑ i : Fin 3, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))
      (r⁻¹ • w) = x • (r⁻¹ • w) + y • w + z • (r • w) := by
    rw [Fin.sum_univ_three, map_add, map_add, map_mul, map_mul, map_mul, Polynomial.aeval_C,
      Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X_pow, Polynomial.aeval_X_pow,
      Polynomial.aeval_X_pow]
    simp only [LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, Module.End.one_apply, sq, hT1,
      hT2]
    rfl
  have hq := NonPth.eq_zero_of_aeval_eq_zero hp hrT hα hv0
    (q := ∑ i : Fin 3, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))
    (lt_of_lt_of_le (Polynomial.degree_sum_fin_lt _) (by exact_mod_cast hp3))
    (by rw [haev]; exact h0)
  have hci : ∀ i : Fin 3, c i = 0 := by
    intro i
    have := congrArg (fun r : Polynomial K => r.coeff (i : ℕ)) hq
    simpa [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj] using this
  exact ⟨hci 0, hci 1, hci 2⟩

theorem allCenters_eigen_pow [NeZero p] (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) (hq2 : ℓ ^ f ≠ 2) {G : Type*} [Group G] [Finite G]
    (π : SUid σ₀ n →* G) {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    {X B r : SUid σ₀ n} (hXE : π X ∈ E) (hBE : π B ∈ E) (hrE : π r ∈ E) (hr1 : π r ≠ 1)
    (hB1 : π B ≠ 1) (hBr : π B ∉ Subgroup.zpowers (π r)) (hXB : π X ∉ Subgroup.zpowers (π B))
    (hXr : π X ∉ Subgroup.zpowers (π r)) (hrX : r * X = X * r) (hrB : r * B = B * r)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hζN : h.bar ζ * ζ = 1)
    (hBX : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {β μ α : K} (hXp : ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1)
    (hμ : μ ≠ 0) (hBp : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (μ ^ p) • 1)
    (hrp : ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = α • 1)
    (hα : ¬ ∃ c : K, c ^ p = α) (l : Fin p) :
    AllCenters ((hyperClosure p ⊤ E).comap π) (Module.End.eigenspace
      (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (μ * ζ ^ (l : ℕ))) := by
  classical
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  have hσi := hσ.invol
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpK : (p : K) ≠ 0 := heis_natCast_ne_zero hζ hp.two_le
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  set Bm : Matrix (Fin n) (Fin n) K := ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hBm
  set rm : Matrix (Fin n) (Fin n) K := ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hrm
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      subst h0
      apply hr1
      have : r = 1 := Subtype.ext (Units.ext (Subsingleton.elim _ _))
      rw [this, map_one]
    · exact h0
  have hpowT : ∀ (M : Matrix (Fin n) (Fin n) K) (c : K), M ^ p = c • 1 →
      (Matrix.toLin' M) ^ p = algebraMap K (Module.End K (Fin n → K)) c := by
    intro M c hM
    have h2 := congrArg Matrix.toLinAlgEquiv' hM
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  have hmemE : ∀ (M : Matrix (Fin n) (Fin n) K) (a : K) (v : Fin n → K),
      v ∈ Module.End.eigenspace (Matrix.toLin' M) a ↔ M *ᵥ v = a • v := fun M a v => by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have hμN := bar_mul_eq_one_of_SUid_pow h hp hp2 hpq hn hμ hBp
  set lam := μ * ζ ^ (l : ℕ) with hlam
  have hlamN : h.bar lam * lam = 1 := by
    rw [hlam, map_mul, map_pow]
    calc h.bar μ * h.bar ζ ^ (l : ℕ) * (μ * ζ ^ (l : ℕ)) =
          (h.bar μ * μ) * (h.bar ζ * ζ) ^ (l : ℕ) := by ring
      _ = 1 := by rw [hμN, hζN, one_pow, one_mul]
  have hlam0 : lam ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hlamN
    exact zero_ne_one hlamN
  have hBl : Bm ^ p = (lam ^ p) • 1 := by
    rw [hBp, hlam, mul_pow, ← pow_mul, mul_comm (l : ℕ) p, pow_mul, hζ.pow_eq_one, one_pow,
      mul_one]
  set U := Module.End.eigenspace (Matrix.toLin' Bm) lam with hU
  have hcU := card_mul_finrank_eigen hp hζ hBX hμ hBp l
  have hU0 : U ≠ ⊥ := by
    intro h0
    have : Module.finrank K U = 0 := by rw [h0, finrank_bot]
    rw [← hlam, this, mul_zero] at hcU
    omega
  have hrT : (Matrix.toLin' rm) ^ p = algebraMap K (Module.End K (Fin n → K)) α := hpowT _ _ hrp
  have hrBm : rm * Bm = Bm * rm := coe_comm hrB
  have hstab : ∀ s ∈ U, Matrix.toLin' rm s ∈ U := by
    intro s hs
    rw [hU, hmemE] at hs ⊢
    rw [Matrix.toLin'_apply, mulVec_mulVec, ← hrBm, ← mulVec_mulVec, hs, mulVec_smul]
  have hdim : p ≤ Module.finrank K U := NonPth.p_le_finrank_of_stable hp hrT hα hstab hU0
  have hsup : ⨆ j : Fin p, Module.End.eigenspace (Matrix.toLin' Bm) (lam * ζ ^ (j : ℕ)) = ⊤ :=
    NonPth.iSup_eigenspace_eq_top_p hp hpK hζ hlam0 (hpowT _ _ hBl)
  have horthB : ∀ j j' : Fin p, j ≠ j' → ∀ u v, Bm *ᵥ u = (lam * ζ ^ (j : ℕ)) • u →
      Bm *ᵥ v = (lam * ζ ^ (j' : ℕ)) • v → herm σ₀ u v = 0 := fun j j' hjj u v hu hv =>
    herm_eq_zero_of_eigen hu hv (bar_mul_ne_one h hlam0 hlamN hζ hζN hjj)
  have hnd : ((idForm h n).domRestrict₁₂ U U).SeparatingLeft := by
    have := NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n)
      (fun j : Fin p => Module.End.eigenspace (Matrix.toLin' Bm) (lam * ζ ^ (j : ℕ)))
      (fun j j' hjj u hu v hv => by
        rw [Nonsplit.idForm_eq_herm h]
        exact horthB j j' hjj u v ((hmemE _ _ u).1 hu) ((hmemE _ _ v).1 hv)) hsup 0
    have this' : ((idForm h n).domRestrict₁₂
        (Module.End.eigenspace (Matrix.toLin' Bm) (lam * ζ ^ ((0 : Fin p) : ℕ)))
        (Module.End.eigenspace (Matrix.toLin' Bm) (lam * ζ ^ ((0 : Fin p) : ℕ)))).SeparatingLeft :=
      this
    rwa [Fin.val_zero, pow_zero, mul_one] at this'
  obtain ⟨m, xs, hxs, hspan, hm⟩ := Nonsplit.hasONBasis_of_separatingLeft h U hnd (by
    obtain ⟨s, hs0, hs1⟩ := Nonsplit.exists_norm_ne_one h hq2
    exact Or.inr ⟨by omega, s, hs0, by rw [hσb]; exact hs1⟩)
  have hxsON : ONExt.IsON σ₀ xs := hxs
  have hm3 : 3 ≤ m := by rcases hm with h4 | ⟨h3, -⟩ <;> omega
  have h3m : m = 3 → ∃ s : K, s ≠ 0 ∧ σ₀ s * s ≠ 1 := fun _ => by
    obtain ⟨s, hs0, hs1⟩ := Nonsplit.exists_norm_ne_one h hq2
    exact ⟨s, hs0, by rw [hσb]; exact hs1⟩
  have hmemU : ∀ v, v ∈ U ↔ Bm *ᵥ v = lam • v := fun v => hmemE _ _ v
  have horthU : ∀ (j : Fin p) (v : Fin n → K), j ≠ 0 → Bm *ᵥ v = (lam * ζ ^ (j : ℕ)) • v →
      ∀ i, herm σ₀ (xs i) v = 0 := by
    intro j v hj hv i
    refine horthB 0 j (Ne.symm hj) _ _ ?_ hv
    rw [Fin.val_zero, pow_zero, mul_one]
    exact (hmemU _).1 (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨a₀, ha₀0, ha₀⟩ := exists_isotropic_ne_zero hσ (by omega : 2 ≤ m)
  set w := orthoEmb xs a₀ with hw
  have hwU : Bm *ᵥ w = lam • w := (hmemU w).1 (hspan ▸ orthoEmb_mem_span xs a₀)
  have hww : herm σ₀ w w = 0 := by rw [hw, herm_orthoEmb hxsON]; exact ha₀
  have hw0 : w ≠ 0 := fun h0 => ha₀0 (ONExt.orthoEmb_injective hxsON (by rw [← hw, h0,
    map_zero]))
  obtain ⟨γ, hγ0, hγ⟩ := hσ.exists_traceZero
  obtain ⟨y, hyH, hyo, hyU⟩ := exists_mem_eq_four_tv h hp hp2 π hE hcard hXE hBE hrE hr1 hB1
    hBr hXB hXr hrX hrB hζ hζN hBX hXp hlamN hBl hxsON hspan hwU hww hγ
  have htvU : ∀ (x v : Fin n → K) (γ' : K), Bm *ᵥ x = lam • x → Bm *ᵥ v = lam • v →
      Bm *ᵥ (tvMap σ₀ x γ' v) = lam • tvMap σ₀ x γ' v := by
    intro x v γ' hx hv
    rw [tvMap_def, mulVec_add, mulVec_smul, hv, hx, smul_add, smul_comm lam]
  have hrU : ∀ v, Bm *ᵥ v = lam • v → Bm *ᵥ (r • v) = lam • (r • v) := by
    intro v hv
    rw [smul_def, mulVec_mulVec, ← hrBm, ← mulVec_mulVec, hv, mulVec_smul]
  have hriU : ∀ v, Bm *ᵥ v = lam • v → Bm *ᵥ (r⁻¹ • v) = lam • (r⁻¹ • v) := by
    intro v hv
    rw [smul_def, mulVec_mulVec, ← coe_comm (Commute.inv_left hrB).eq, ← mulVec_mulVec, hv,
      mulVec_smul]
  have hyUU : ∀ v, Bm *ᵥ v = lam • v → Bm *ᵥ (y • v) = lam • (y • v) := by
    intro v hv
    rw [hyU v hv]
    exact htvU _ _ _ (hrU w hwU) (htvU _ _ _ hwU (htvU _ _ _ (hriU w hwU)
      (htvU _ _ _ hwU hv)))
  have hyst : ∀ c, ∃ d, y • orthoEmb xs c = orthoEmb xs d :=
    exists_orthoEmb_of_stable hspan fun v hv => (hmemU _).2 (hyUU v ((hmemU v).1 hv))
  set ym : Matrix (Fin n) (Fin n) K := ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hym
  have hext : ONExt.extMat σ₀ xs (ONExt.resMat σ₀ xs ym) = ym := by
    refine mat_eq_of_eigen hsup fun j v hv => ?_
    by_cases hj : j = 0
    · subst hj
      have hv' : Bm *ᵥ v = lam • v := by rwa [Fin.val_zero, pow_zero, mul_one] at hv
      obtain ⟨c, rfl⟩ := (mem_span_range_iff xs v).1 (hspan ▸ (hmemU v).2 hv')
      rw [ONExt.extMat_mulVec_orthoEmb hxsON, ONExt.orthoEmb_resMat_mulVec hxsON hyst, smul_def]
    · rw [ONExt.extMat_mulVec_of_orth xs _ (horthU j v hj hv), ← smul_def σ₀ y v,
        hyo j v hj hv]
  have hdet : (ONExt.resMat σ₀ xs ym).det = 1 := by
    rw [← ONExt.det_extMat hxsON, hext]
    exact ((mem_SUid_iff σ₀).1 y.2).1
  set y₀ : SUid σ₀ m := mkSU σ₀ (ONExt.resMat σ₀ xs ym) hdet (ONExt.herm_resMat hxsON hyst)
    with hy₀
  have hεy : ONExt.ext hσi hxsON y₀ = y := by
    refine ext_smul σ₀ fun v => ?_
    rw [ONExt.ext_smul_eq, smul_def]
    show ONExt.extMat σ₀ xs (ONExt.resMat σ₀ xs ym) *ᵥ v = ym *ᵥ v
    rw [hext]
  set H := (hyperClosure p ⊤ E).comap π with hH
  set ε := ONExt.ext hσi hxsON with hε
  set HU := H.comap ε with hHU
  have hy₀HU : y₀ ∈ HU := by
    show π (ε y₀) ∈ hyperClosure p ⊤ E
    rw [hε, hεy]
    exact hyH
  have hy₀s : ∀ c : K, ((y₀ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) ≠ c • 1 := by
    intro c hc
    have hyc : ∀ v, Bm *ᵥ v = lam • v → y • v = c • v := by
      intro v hv
      obtain ⟨d, rfl⟩ := (mem_span_range_iff xs v).1 (hspan ▸ (hmemU v).2 hv)
      rw [← hεy, ONExt.ext_smul_orthoEmb, smul_def, hc, Matrix.smul_mulVec, Matrix.one_mulVec,
        map_smul]
    have hrw0 : r • w ≠ 0 := fun h0 => hw0 (by simpa using congrArg (fun u => r⁻¹ • u) h0)
    obtain ⟨u, huU, hu⟩ : ∃ u ∈ U, herm σ₀ (r • w) u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hrwU : r • w ∈ U := (hmemU _).2 (hrU w hwU)
      have h0 : (⟨r • w, hrwU⟩ : U) = 0 := hnd ⟨r • w, hrwU⟩ fun u' => by
        simp only [LinearMap.domRestrict₁₂_apply]
        rw [Nonsplit.idForm_eq_herm h]
        exact hcon u' u'.2
      exact hrw0 (congrArg Subtype.val h0)
    have huB := (hmemU u).1 huU
    exact false_of_four_tvMap hσi (a := r⁻¹ • w) (b := w) (d := r • w) (u := u) hγ0
      (indep_three hp hp3 hrp hα hw0) hww
      (by rw [← herm_smul_smul σ₀ r (r⁻¹ • w) w, smul_inv_smul])
      hu ((hyU w hwU).symm.trans (hyc w hwU)) ((hyU _ (hrU w hwU)).symm.trans
        (hyc _ (hrU w hwU))) ((hyU u huB).symm.trans (hyc u huB))
  have hβN := bar_mul_eq_one_of_SUid_scalar h hn hXp
  have hlamkN : ∀ k : ℕ, h.bar (lam * ζ ^ k) * (lam * ζ ^ k) = 1 := by
    intro k
    rw [map_mul, map_pow]
    calc h.bar lam * h.bar ζ ^ k * (lam * ζ ^ k) = (h.bar lam * lam) * (h.bar ζ * ζ) ^ k := by
          ring
      _ = 1 := by rw [hlamN, hζN, one_pow, one_mul]
  have hnorm : ∀ g ∈ HU, ∀ t : SUid σ₀ m, t * g * t⁻¹ ∈ HU := by
    refine conj_mem_of_tv hσ (by omega) h3m ?_
    intro a ha c' hc' g hg
    set w' := orthoEmb xs a with hw'
    have hwB : Bm *ᵥ w' = (lam * ζ ^ 0) • w' := by
      rw [pow_zero, mul_one]
      exact (hmemU _).1 (hspan ▸ orthoEmb_mem_span xs a)
    have hXkB : ∀ k : ℕ, Bm *ᵥ ((X ^ k) • w') = (lam * ζ ^ k) • ((X ^ k) • w') := fun k => by
      have := mulVec_pow_smul_of_qcomm hBX k 0 w' hwB
      rwa [zero_add] at this
    have horthk : ∀ k k' : ℕ, k % p ≠ k' % p → ∀ u v, Bm *ᵥ u = (lam * ζ ^ k) • u →
        Bm *ᵥ v = (lam * ζ ^ k') • v → herm σ₀ u v = 0 := by
      intro k k' hkk u v hu hv
      rw [pow_eq_pow_mod hζ k] at hu
      rw [pow_eq_pow_mod hζ k'] at hv
      exact horthB ⟨k % p, Nat.mod_lt _ hp.pos⟩ ⟨k' % p, Nat.mod_lt _ hp.pos⟩
        (fun he => hkk (congrArg Fin.val he)) u v hu hv
    have horthS : ∀ k k' : Fin p, herm σ₀ ((X ^ (k : ℕ)) • w') ((X ^ (k' : ℕ)) • w') = 0 := by
      intro k k'
      by_cases hkk : k = k'
      · subst hkk
        rw [herm_smul_smul, hw', herm_orthoEmb hxsON, ha]
      · refine horthk k k' ?_ _ _ (hXkB k) (hXkB k')
        rw [Nat.mod_eq_of_lt k.2, Nat.mod_eq_of_lt k'.2]
        exact fun he => hkk (Fin.ext he)
    obtain ⟨S, hS, hXS⟩ :=
      exists_siegel_orbit hσi (p := p) hXp (by rw [hσb]; exact hβN) horthS hc'
    have hBS : B * S = S * B := siegel_comm_of_eigen hS
      (lam := fun k : Fin p => lam * ζ ^ (k : ℕ)) (fun k => by rw [smul_def]; exact hXkB k)
      (fun k => by rw [hσb]; exact hlamkN _)
    have hSH : S ∈ H := mem_hyperClosure_of_comm hp hE hcard hBE hXE hB1 hXB
      (by rw [← map_mul, ← map_mul, hBS]) (by rw [← map_mul, ← map_mul, hXS])
    have hSU : ∀ c'', S • orthoEmb xs c'' = ε (tv hσi ha hc') • orthoEmb xs c'' := by
      intro c''
      have hc''B : Bm *ᵥ orthoEmb xs c'' = (lam * ζ ^ 0) • orthoEmb xs c'' := by
        rw [pow_zero, mul_one]
        exact (hmemU _).1 (hspan ▸ orthoEmb_mem_span xs c'')
      rw [hS, ONExt.ext_tv_smul hσi hxsON ha hc', ← hw']
      congr 1
      rw [Finset.sum_eq_single (0 : Fin p)]
      · simp
      · intro k _ hk0
        have h0 : herm σ₀ ((X ^ (k : ℕ)) • w') (orthoEmb xs c'') = 0 := by
          refine horthk k 0 ?_ _ _ (hXkB k) hc''B
          rw [Nat.mod_eq_of_lt k.2, Nat.zero_mod]
          exact fun he => hk0 (Fin.ext he)
        rw [h0, mul_zero, zero_smul]
      · intro h0
        exact absurd (Finset.mem_univ _) h0
    set T := (ε (tv hσi ha hc'))⁻¹ * S with hT
    have hTU : ∀ c'', T • orthoEmb xs c'' = orthoEmb xs c'' := by
      intro c''
      rw [hT, mul_smul, hSU, inv_smul_smul]
    have hTU' : ∀ c'', T⁻¹ • orthoEmb xs c'' = orthoEmb xs c'' := by
      intro c''
      rw [inv_smul_eq_iff, hTU]
    have hTres : ONExt.resMat σ₀ xs ((T : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [resMat_eq_smul_of_eigen hxsON (lam := 1) (fun c'' => by rw [hTU, one_smul]), one_smul]
    have hTg : T * ε g = ε g * T :=
      commute_ext_of_resMat hσi hxsON (fun c'' => ⟨c'', hTU c''⟩) (fun c'' => ⟨c'', hTU' c''⟩)
        (by rw [hTres, Matrix.mul_one, Matrix.one_mul])
    have hS' : S = ε (tv hσi ha hc') * T := by rw [hT, mul_inv_cancel_left]
    have hconj : T * ε g * T⁻¹ = ε g := by rw [hTg, mul_inv_cancel_right]
    have key : ε (tv hσi ha hc' * g * (tv hσi ha hc')⁻¹) = S * ε g * S⁻¹ := by
      calc ε (tv hσi ha hc' * g * (tv hσi ha hc')⁻¹)
          = ε (tv hσi ha hc') * ε g * (ε (tv hσi ha hc'))⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = ε (tv hσi ha hc') * (T * ε g * T⁻¹) * (ε (tv hσi ha hc'))⁻¹ := by rw [hconj]
        _ = (ε (tv hσi ha hc') * T) * ε g * (ε (tv hσi ha hc') * T)⁻¹ := by group
        _ = S * ε g * S⁻¹ := by rw [← hS']
    show ε (tv hσi ha hc' * g * (tv hσi ha hc')⁻¹) ∈ H
    rw [key]
    exact H.mul_mem (H.mul_mem hSH hg) (H.inv_mem hSH)
  have htop : HU = ⊤ := eq_top_of_normal_of_nonscalar hσ hm3 h3m hnorm hy₀HU hy₀s
  rw [← hspan]
  exact ONExt.allCenters_of_forall_ext_mem hσi hxsON fun g => by
    have : g ∈ HU := by rw [htop]; exact Subgroup.mem_top g
    exact this

end Centres


section Mix

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem isCenter_sum_of_components (hσ : IsUnitaryInvolution σ) {H : Subgroup (SUid σ n)}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (W : ι → Submodule K (Fin n → K))
    (hON : ∀ i, HasONBasis σ (W i))
    (horth : ∀ i j, i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j, herm σ u v = 0)
    (hA : ∀ i, AllCenters H (W i)) {a b : ι → Fin n → K}
    (ha : ∀ i, a i ∈ W i ∧ a i ≠ 0 ∧ herm σ (a i) (a i) = 0)
    (hb : ∀ i, b i ∈ W i ∧ b i ≠ 0 ∧ herm σ (b i) (b i) = 0)
    (hC : IsCenter H (∑ i, a i)) : IsCenter H (∑ i, b i) := by
  classical
  have hmem : ∀ (T : Finset ι) (i : ι), (if i ∈ T then b i else a i) ∈ W i := by
    intro T i
    split_ifs
    exacts [(hb i).1, (ha i).1]
  have key : ∀ T : Finset ι, IsCenter H (∑ i, if i ∈ T then b i else a i) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using hC
    | insert k T hk ih =>
      obtain ⟨m, x, hx, hspan, hm⟩ := hON k
      have hm3 : 3 ≤ m := by rcases hm with h4 | ⟨h3, -⟩ <;> omega
      obtain ⟨c, hc⟩ := (mem_span_range_iff x (a k)).1 (hspan ▸ (ha k).1)
      obtain ⟨c', hc'⟩ := (mem_span_range_iff x (b k)).1 (hspan ▸ (hb k).1)
      have hcent : ∀ d, herm σ d d = 0 → IsCenter H (orthoEmb x d) := fun d hd =>
        hA k _ (hspan ▸ orthoEmb_mem_span x d) (by rw [herm_orthoEmb hx]; exact hd)
      have hc0 : c ≠ 0 := fun h0 => (ha k).2.1 (by rw [← hc, h0, map_zero])
      have hc0' : c' ≠ 0 := fun h0 => (hb k).2.1 (by rw [← hc', h0, map_zero])
      have hci : herm σ c c = 0 := by rw [← herm_orthoEmb hx, hc]; exact (ha k).2.2
      have hci' : herm σ c' c' = 0 := by rw [← herm_orthoEmb hx, hc']; exact (hb k).2.2
      obtain ⟨g, hg, hgc, hgfix⟩ :=
        exists_mem_fix_of_iso hσ hm3 (herm_orthoEmb hx) hcent hc0 hci hc0' hci'
      have hsplit : ∀ T' : Finset ι, (∑ i, if i ∈ T' then b i else a i) =
          (if k ∈ T' then b k else a k) +
            ∑ i ∈ Finset.univ.erase k, (if i ∈ T' then b i else a i) := fun T' =>
        (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
      have hfix : g • (∑ i ∈ Finset.univ.erase k, (if i ∈ T then b i else a i)) =
          ∑ i ∈ Finset.univ.erase k, (if i ∈ T then b i else a i) := by
        refine hgfix _ fun u => ?_
        rw [herm_sum_right]
        refine Finset.sum_eq_zero fun i hi => ?_
        exact horth k i (Ne.symm (Finset.ne_of_mem_erase hi)) _
          (hspan ▸ orthoEmb_mem_span x u) _ (hmem T i)
      have hrest : ∑ i ∈ Finset.univ.erase k, (if i ∈ insert k T then b i else a i) =
          ∑ i ∈ Finset.univ.erase k, (if i ∈ T then b i else a i) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hik : i ≠ k := Finset.ne_of_mem_erase hi
        simp [Finset.mem_insert, hik]
      have heq : (∑ i, if i ∈ insert k T then b i else a i) =
          g • (∑ i, if i ∈ T then b i else a i) := by
        rw [hsplit, hsplit T, smul_add, hfix, if_neg hk, if_pos (Finset.mem_insert_self k T),
          ← hc, hgc, hc', hrest]
      rw [heq]
      exact ih.map hg
  simpa using key Finset.univ

theorem exists_mix_of_center (hσ : IsUnitaryInvolution σ) {H : Subgroup (SUid σ n)}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (W : ι → Submodule K (Fin n → K))
    (hON : ∀ i, HasONBasis σ (W i))
    (horth : ∀ i j, i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j, herm σ u v = 0)
    (hA : ∀ i, AllCenters H (W i)) {a : ι → Fin n → K}
    (ha : ∀ i, a i ∈ W i ∧ a i ≠ 0 ∧ herm σ (a i) (a i) = 0)
    (hC : IsCenter H (∑ i, a i)) {lam : K} (hlam0 : lam ≠ 0) (hlam1 : 1 + lam ≠ 0)
    (i j : ι) (hij : i ≠ j) :
    ∃ w₁ ∈ W i, ∃ w₂ ∈ W j, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ IsCenter H (w₁ + w₂) := by
  classical
  have hσi := hσ.invol
  obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
  obtain ⟨w₀, hw₀, hw₀i, hw₀a⟩ :=
    Nonsplit.exists_isotropic_pairing hσ (hON i) (ha i).1 (ha i).2.1
  set a' := (τ / herm σ (a i) w₀) • w₀ with ha'
  have ha'W : a' ∈ W i := (W i).smul_mem _ hw₀
  have ha'i : herm σ a' a' = 0 := by rw [ha', herm_smul_left, herm_smul_right, hw₀i]; ring
  have haa' : herm σ (a i) a' = τ := by
    rw [ha', herm_smul_right]
    field_simp
  have ha'0 : a' ≠ 0 := by
    rintro h0
    rw [h0, herm_zero_right] at haa'
    exact hτ0 haa'.symm
  have ha'a : herm σ a' (a i) = σ τ := by rw [herm_conj σ hσi, haa']
  set b : ι → Fin n → K := fun k => if k = i then a' else if k = j then lam • a k else -a k
    with hbdef
  have hb : ∀ k, b k ∈ W k ∧ b k ≠ 0 ∧ herm σ (b k) (b k) = 0 := by
    intro k
    by_cases hki : k = i
    · subst hki
      simp only [hbdef, if_true]
      exact ⟨ha'W, ha'0, ha'i⟩
    · by_cases hkj : k = j
      · subst hkj
        simp only [hbdef, if_neg hki, if_true]
        exact ⟨(W k).smul_mem _ (ha k).1, smul_ne_zero hlam0 (ha k).2.1,
          by rw [herm_smul_left, herm_smul_right, (ha k).2.2]; ring⟩
      · simp only [hbdef, if_neg hki, if_neg hkj]
        exact ⟨(W k).neg_mem (ha k).1, neg_ne_zero.mpr (ha k).2.1,
          by rw [herm_neg_left, herm_neg_right, neg_neg, (ha k).2.2]⟩
  have hCb := isCenter_sum_of_components hσ W hON horth hA ha hb hC
  set w₁ := a i + a' with hw₁
  set w₂ := (1 + lam) • a j with hw₂
  have hsum : (∑ k, a k) + (∑ k, b k) = w₁ + w₂ := by
    rw [← Finset.sum_add_distrib]
    have hpt : ∀ k, a k + b k = (if k = i then w₁ else 0) + (if k = j then w₂ else 0) := by
      intro k
      by_cases hki : k = i
      · subst hki
        simp [hbdef, hw₁, hij]
      · by_cases hkj : k = j
        · subst hkj
          simp only [hbdef, if_neg hki, if_pos rfl, hw₂, add_smul, one_smul]
          simp
        · simp [hbdef, hki, hkj]
    rw [Finset.sum_congr rfl fun k _ => hpt k, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq']
    simp
  have hw₁W : w₁ ∈ W i := (W i).add_mem (ha i).1 ha'W
  have hw₂W : w₂ ∈ W j := (W j).smul_mem _ (ha j).1
  have h12 : herm σ w₁ w₂ = 0 := horth i j hij _ hw₁W _ hw₂W
  have h21 : herm σ w₂ w₁ = 0 := horth j i (Ne.symm hij) _ hw₂W _ hw₁W
  have hw₁i : herm σ w₁ w₁ = 0 := by
    rw [hw₁, herm_add_left, herm_add_right, herm_add_right, (ha i).2.2, ha'i, haa', ha'a]
    linear_combination hτ
  have hw₂i : herm σ w₂ w₂ = 0 := by
    rw [hw₂, herm_smul_left, herm_smul_right, (ha j).2.2]
    ring
  have hiso : herm σ (w₁ + w₂) (w₁ + w₂) = 0 := by
    have e : herm σ (w₁ + w₂) (w₁ + w₂) =
        herm σ w₁ w₁ + herm σ w₁ w₂ + (herm σ w₂ w₁ + herm σ w₂ w₂) := by
      rw [herm_add_left, herm_add_right σ w₁ w₁ w₂, herm_add_right σ w₂ w₁ w₂]
    rw [e, hw₁i, hw₂i, h12, h21]
    ring
  have hpair : herm σ (∑ k, b k) (∑ k, a k) ≠ 0 := by
    have hbsum : (∑ k, b k) = w₁ + w₂ - ∑ k, a k := by rw [← hsum]; abel
    rw [hbsum, herm_sub_left, hC.1, sub_zero, herm_add_left, herm_sum_right, herm_sum_right,
      Finset.sum_eq_single i (fun k _ hki => horth i k (Ne.symm hki) _ hw₁W _ (ha k).1)
        (by simp),
      Finset.sum_eq_single j (fun k _ hkj => horth j k (Ne.symm hkj) _ hw₂W _ (ha k).1)
        (by simp),
      hw₁, hw₂, herm_add_left, (ha i).2.2, ha'a, herm_smul_left, (ha j).2.2, mul_zero, zero_add,
      add_zero]
    intro h0
    apply hτ0
    rw [← hσi τ, h0, map_zero]
  have hC2 := IsCenter.add hσi hC hCb (by rw [hsum]; exact hiso) hpair
  rw [hsum] at hC2
  refine ⟨w₁, hw₁W, w₂, hw₂W, ?_, smul_ne_zero hlam1 (ha j).2.1, hC2⟩
  intro h0
  have : herm σ (a i) w₁ = τ := by rw [hw₁, herm_add_right, (ha i).2.2, haa', zero_add]
  rw [h0, herm_zero_right] at this
  exact hτ0 this.symm

end Mix


section Pow

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem hyperGen_of_nonab_pow (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) (hq2 : ℓ ^ f ≠ 2) {G : Type*} [Group G] [Finite G]
    (π : SUid σ₀ n →* G) (hπ : Function.Surjective π)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    {X Y r : SUid σ₀ n} (hXE : π X ∈ E) (hYE : π Y ∈ E) (hrE : π r ∈ E) (hr1 : π r ≠ 1)
    (hYr : π Y ∉ Subgroup.zpowers (π r))
    (hXcl : π X ∉ Subgroup.closure ({π r, π Y} : Set G))
    (hrX : r * X = X * r) (hrY : r * Y = Y * r)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hζN : h.bar ζ * ζ = 1)
    (hYX : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {β ν α : K} (hXp : ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1)
    (hν : ν ≠ 0) (hYp : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ν ^ p) • 1)
    (hrp : ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = α • 1)
    (hα : ¬ ∃ c : K, c ^ p = α) :
    HyperGen p (⊤ : Subgroup G) E := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpK : (p : K) ≠ 0 := heis_natCast_ne_zero hζ hp.two_le
  have hexp : ∀ e ∈ E, e ^ p = 1 := hE.2
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      subst h0
      apply hr1
      have : r = 1 := Subtype.ext (Units.ext (Subsingleton.elim _ _))
      rw [this, map_one]
    · exact h0
  set Xm : Matrix (Fin n) (Fin n) K := ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hXm
  set Ym : Matrix (Fin n) (Fin n) K := ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hYm
  set rm : Matrix (Fin n) (Fin n) K := ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hrm
  have hpowT : ∀ (M : Matrix (Fin n) (Fin n) K) (c : K), M ^ p = c • 1 →
      (Matrix.toLin' M) ^ p = algebraMap K (Module.End K (Fin n → K)) c := by
    intro M c hM
    have h2 := congrArg Matrix.toLinAlgEquiv' hM
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  have hmemE : ∀ (M : Matrix (Fin n) (Fin n) K) (a : K) (v : Fin n → K),
      v ∈ Module.End.eigenspace (Matrix.toLin' M) a ↔ M *ᵥ v = a • v := fun M a v => by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have hα0 : α ≠ 0 := scalar_ne_zero_of_matPow hn hrp
  have hβ0 : β ≠ 0 := scalar_ne_zero_of_matPow hn hXp
  obtain ⟨a, b, hab, ξ, hξ⟩ :=
    exists_pth_power_word hp (dvd_card_sub_one_of_unitary h hpq) hα0 hβ0
  have hb : ¬ p ∣ b := by
    rintro ⟨t, rfl⟩
    have hpa : ¬ p ∣ a := fun hpa => hab ⟨hpa, dvd_mul_right p t⟩
    apply hα
    refine pth_power_of_pow_coprime hp hα0 hpa (s := ξ * (β ^ t)⁻¹) ?_
    rw [mul_pow, inv_pow, hξ, ← pow_mul, mul_comm t p, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hβ0), mul_one]
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hξ
    exact mul_ne_zero (pow_ne_zero _ hα0) (pow_ne_zero _ hβ0) hξ.symm
  set X' := X ^ b * r ^ a with hX'
  have hX'm : ((X' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Xm ^ b * rm ^ a := by
    simp only [hX', Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val,
      hXm, hrm]
  have hrXc : Commute rm Xm := coe_comm hrX
  have hrYc : Commute rm Ym := coe_comm hrY
  have hX'p : ((X' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ξ ^ p) • 1 := by
    rw [hX'm, (hrXc.symm.pow_pow b a).mul_pow p, ← pow_mul, ← pow_mul, mul_comm b p,
      mul_comm a p, pow_mul, pow_mul, hXp, hrp, smul_pow, smul_pow, one_pow, one_pow,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, hξ, mul_comm]
  have hcop : Nat.Coprime b p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hb)
  set ζ' := ζ ^ b with hζ'def
  have hζ' : IsPrimitiveRoot ζ' p := hζ.pow_of_coprime b hcop
  have hζ'N : h.bar ζ' * ζ' = 1 := by rw [hζ'def, map_pow, ← mul_pow, hζN, one_pow]
  have hζ'0 : ζ' ≠ 0 := hζ'.ne_zero hp.ne_zero
  have hYX' : Ym * ((X' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ' • (((X' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Ym) := by
    rw [hX'm, ← Matrix.mul_assoc]
    have h1 : Ym * Xm ^ b = ζ' • (Xm ^ b * Ym) := by
      have := qcommMat_pow_pow hYX b 1
      simpa only [pow_one, mul_one] using this
    rw [h1, Matrix.smul_mul, Matrix.mul_assoc, ← (hrYc.pow_left a).eq, ← Matrix.mul_assoc]
  have hrX' : r * X' = X' * r := by
    rw [hX']
    exact ((Commute.pow_right hrX b).mul_right (Commute.self_pow r a)).eq
  have hX'E : π X' ∈ E := by
    rw [hX', map_mul, map_pow, map_pow]
    exact E.mul_mem (E.pow_mem hXE _) (E.pow_mem hrE _)
  have hrcl : π r ∈ Subgroup.closure ({π r, π Y} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hYcl : π Y ∈ Subgroup.closure ({π r, π Y} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hX'cl : π X' ∉ Subgroup.closure ({π r, π Y} : Set G) := by
    intro hmem
    apply hXcl
    refine mem_of_pow_mem hp (hexp _ hXE) hb ?_
    have : (π X) ^ b = π X' * ((π r) ^ a)⁻¹ := by
      rw [hX', map_mul, map_pow, map_pow, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ (Subgroup.pow_mem _ hrcl _))
  have hX'r : π X' ∉ Subgroup.zpowers (π r) := fun hm => hX'cl (Subgroup.zpowers_le.2 hrcl hm)
  have hX'Y : π X' ∉ Subgroup.zpowers (π Y) := fun hm => hX'cl (Subgroup.zpowers_le.2 hYcl hm)
  have hY1 : π Y ≠ 1 := fun h1 => hYr (h1 ▸ Subgroup.one_mem _)
  have hX'1 : π X' ≠ 1 := fun h1 => hX'r (h1 ▸ Subgroup.one_mem _)
  have hYX'z : π Y ∉ Subgroup.zpowers (π X') := by
    intro hm
    have hle := Subgroup.zpowers_le.2 hm
    have heq := Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime (hexp _ hX'E) hX'1,
        orderOf_eq_prime (hexp _ hYE) hY1])
    apply hX'Y
    rw [heq]
    exact Subgroup.mem_zpowers _
  set W : Fin p → Submodule K (Fin n → K) :=
    fun l => Module.End.eigenspace (Matrix.toLin' Ym) (ν * ζ' ^ (l : ℕ)) with hW
  set H := (hyperClosure p ⊤ E).comap π with hH
  have hA : ∀ l, AllCenters H (W l) := fun l =>
    allCenters_eigen_pow h hp hp2 hpq hq2 π hE hcard hX'E hYE hrE hr1 hY1 hYr hX'Y hX'r hrX' hrY
      hζ' hζ'N hYX' hX'p hν hYp hrp hα l
  have hX'Y' : ((X' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Ym =
      ζ'⁻¹ • (Ym * ((X' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    rw [hYX', smul_smul, inv_mul_cancel₀ hζ'0, one_smul]
  have hζ'iN : h.bar ζ'⁻¹ * ζ'⁻¹ = 1 := by rw [map_inv₀, ← mul_inv, hζ'N, inv_one]
  have hA' := allCenters_eigen_pow h hp hp2 hpq hq2 π hE hcard (X := Y) (B := X') hYE hX'E hrE
    hr1 hX'1 hX'r hYX'z hYr hrY hrX' hζ'.inv hζ'iN hX'Y' hYp hξ0 hX'p hrp hα 0
  have hνN := bar_mul_eq_one_of_SUid_pow h hp hp2 hpq hn hν hYp
  have hWorth : ∀ l l' : Fin p, l ≠ l' → ∀ u ∈ W l, ∀ v ∈ W l', herm σ₀ u v = 0 :=
    fun l l' hll u hu v hv => herm_eq_zero_of_eigen ((hmemE _ _ u).1 hu) ((hmemE _ _ v).1 hv)
      (bar_mul_ne_one h hν hνN hζ' hζ'N hll)
  have hWtop : ⨆ l, W l = ⊤ := NonPth.iSup_eigenspace_eq_top_p hp hpK hζ' hν (hpowT _ _ hYp)
  have hWsep : ∀ l, ((idForm h n).domRestrict₁₂ (W l) (W l)).SeparatingLeft :=
    NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n) W
      (fun l l' hne u hu v hv => by
        rw [Nonsplit.idForm_eq_herm h]; exact hWorth l l' hne u hu v hv) hWtop
  have hrT : (Matrix.toLin' rm) ^ p = algebraMap K (Module.End K (Fin n → K)) α := hpowT _ _ hrp
  have hWdim : ∀ l, p ≤ Module.finrank K (W l) := by
    intro l
    have hc := card_mul_finrank_eigen hp hζ' hYX' hν hYp l
    have hW0 : W l ≠ ⊥ := by
      intro h0
      have : Module.finrank K (W l) = 0 := by rw [h0, finrank_bot]
      rw [show Module.finrank K (Module.End.eigenspace (Matrix.toLin' Ym)
        (ν * ζ' ^ (l : ℕ))) = 0 from this, mul_zero] at hc
      omega
    refine NonPth.p_le_finrank_of_stable hp hrT hα (fun s hs => ?_) hW0
    rw [hW, hmemE] at hs ⊢
    rw [Matrix.toLin'_apply, mulVec_mulVec, ← hrYc.eq, ← mulVec_mulVec, hs, mulVec_smul]
  have hON : ∀ l, HasONBasis σ₀ (W l) := by
    intro l
    refine Nonsplit.hasONBasis_of_separatingLeft h (W l) (hWsep l) ?_
    obtain ⟨s, hs0, hs1⟩ := Nonsplit.exists_norm_ne_one h hq2
    exact Or.inr ⟨le_trans hp3 (hWdim l), s, hs0, by rw [hσb]; exact hs1⟩
  obtain ⟨m₀, x₀, hx₀, hspan₀, hm₀⟩ := hON 0
  obtain ⟨c₀, hc₀0, hc₀⟩ := exists_isotropic_ne_zero hσ
    (by rcases hm₀ with h4 | ⟨h3, -⟩ <;> omega : 2 ≤ m₀)
  set v₀ := orthoEmb x₀ c₀ with hv₀
  have hv₀W : v₀ ∈ W 0 := hspan₀ ▸ orthoEmb_mem_span x₀ c₀
  have hv₀i : herm σ₀ v₀ v₀ = 0 := by rw [hv₀, herm_orthoEmb hx₀]; exact hc₀
  have hv₀0 : v₀ ≠ 0 := fun h0 => hc₀0 (ONExt.orthoEmb_injective hx₀ (by rw [← hv₀, h0,
    map_zero]))
  have hYv₀ : Ym *ᵥ v₀ = (ν * ζ' ^ 0) • v₀ := by
    have := (hmemE _ _ _).1 hv₀W
    rwa [Fin.val_zero] at this
  set vv : Fin p → Fin n → K := fun k => (ξ⁻¹) ^ (k : ℕ) • ((X' ^ (k : ℕ)) • v₀) with hvv
  have hvvW : ∀ k, vv k ∈ W k := by
    intro k
    rw [hW, hmemE]
    have := mulVec_pow_smul_of_qcomm hYX' (k : ℕ) 0 v₀ hYv₀
    rw [zero_add] at this
    rw [hvv, mulVec_smul, this, smul_comm]
  have hvv0 : ∀ k, vv k ≠ 0 := by
    intro k h0
    apply hv₀0
    have h1 : (X' ^ (k : ℕ)) • v₀ = 0 := by
      rcases smul_eq_zero.1 h0 with h2 | h2
      · exact absurd h2 (pow_ne_zero _ (inv_ne_zero hξ0))
      · exact h2
    simpa using congrArg (fun u => (X' ^ (k : ℕ))⁻¹ • u) h1
  have hvvi : ∀ k, herm σ₀ (vv k) (vv k) = 0 := by
    intro k
    rw [hvv, herm_smul_left, herm_smul_right, herm_smul_smul, hv₀i]
    ring
  have hX'pv : (X' ^ p) • v₀ = (ξ ^ p) • v₀ := by
    rw [smul_def, Subgroup.coe_pow, Units.val_pow_eq_pow_val, hX'p, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have hshift : ∀ k : Fin p, X' • vv k = ξ • vv (k + 1) := by
    intro k
    have hk1 : ((k + 1 : Fin p) : ℕ) = ((k : ℕ) + 1) % p := by
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < p)]
    simp only [hvv]
    rw [smul_comm X', ← mul_smul X', ← pow_succ', hk1, smul_smul]
    rcases Nat.lt_or_ge ((k : ℕ) + 1) p with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]
      congr 1
      rw [pow_succ, mul_comm ((ξ⁻¹) ^ (k : ℕ)) ξ⁻¹, ← mul_assoc, mul_inv_cancel₀ hξ0, one_mul]
    · have hkp : (k : ℕ) + 1 = p := by have := k.2; omega
      rw [hkp, Nat.mod_self, pow_zero, pow_zero, one_smul, mul_one, hX'pv, smul_smul]
      congr 1
      have h1 : ξ ^ p = ξ ^ ((k : ℕ) + 1) := by rw [hkp]
      rw [h1, pow_succ, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hξ0, one_pow, one_mul]
  have hsumX : ((X' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (∑ k, vv k) =
      (ξ * ζ'⁻¹ ^ ((0 : Fin p) : ℕ)) • ∑ k, vv k := by
    rw [Fin.val_zero, pow_zero, mul_one, ← smul_def σ₀ X', Finset.smul_sum, Finset.smul_sum,
      Finset.sum_congr rfl fun k _ => hshift k]
    exact Equiv.sum_comp (Equiv.addRight 1) (fun k => ξ • vv k)
  have hsumi : herm σ₀ (∑ k, vv k) (∑ k, vv k) = 0 := by
    rw [herm_sum_left]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [herm_sum_right, Finset.sum_eq_single k
      (fun k' _ hk' => hWorth k k' (Ne.symm hk') _ (hvvW k) _ (hvvW k')) (by simp)]
    exact hvvi k
  have hC : IsCenter H (∑ k, vv k) := hA' _ ((hmemE _ _ _).2 hsumX) hsumi
  have hζ'1 : 1 + ζ' ≠ 0 := by
    intro h0
    have h1 : ζ' ^ 2 = 1 := by
      have : ζ' = -1 := by linear_combination h0
      rw [this]
      ring
    have := Nat.le_of_dvd (by norm_num) (hζ'.dvd_of_pow_eq_one 2 h1)
    omega
  have hmix : ∀ l l' : Fin p, l ≠ l' →
      ∃ w₁ ∈ W l, ∃ w₂ ∈ W l', w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ IsCenter H (w₁ + w₂) :=
    fun l l' hll => exists_mix_of_center hσ W hON hWorth hA (a := vv)
      (fun k => ⟨hvvW k, hvv0 k, hvvi k⟩) hC hζ'0 hζ'1 l l' hll
  have hn4 : 4 ≤ n := by
    have hc := card_mul_finrank_eigen hp hζ' hYX' hν hYp 0
    have h1 := hWdim 0
    have h2 : p * p ≤ p * Module.finrank K (W 0) := Nat.mul_le_mul_left p h1
    have h3 : 9 ≤ p * p := Nat.mul_le_mul hp3 hp3
    change p * Module.finrank K (W 0) = n at hc
    omega
  have hHtop : H = ⊤ := Centers.eq_top_of_blocks hσ hn4 W hON hWorth hA hmix hWtop
  intro k _
  obtain ⟨g, rfl⟩ := hπ k
  have hg : g ∈ H := by rw [hHtop]; exact Subgroup.mem_top g
  exact hg

end Pow

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryPowAux

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryAux
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryRestAux
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryPowAux

theorem seitzGoodInnerUnitaryNonabRest : SeitzGoodInnerUnitaryNonabRest := by
  classical
  rintro d p hp hp2 hpd hlist E₀ hE hcard ⟨hrest, -, -, ℓ, f, n, K, _, h, π, hπ, hker,
    hpq, hq2, ⟨x, y, hxE, hyE, hxy⟩, -⟩
  haveI : Finite K := h.finite
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : CharP K ℓ := h.charP
  obtain ⟨m, q, hd, -, -⟩ := hrest
  let ε : CFSG.LieType.Universal.Unitary.SUid (CFSG.LieType.BorelTits.unitaryInvolution K ℓ f)
      (n + 1) ≃* CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K (n + 1) :=
    MulEquiv.subgroupCongr (suid_unitaryInvolution_eq h (n + 1))
  let πS := π.comp ε.toMonoidHom
  have hπS : Function.Surjective πS := hπ.comp ε.surjective
  have hkerS : ∀ g ∈ πS.ker, ∃ c : K,
      ((g : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = c • 1 :=
    fun g hg => hker (ε g) hg
  have hπSε : ∀ z : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K (n + 1),
      πS (ε.symm z) = π z := fun z => by
    show π (ε (ε.symm z)) = π z
    rw [MulEquiv.apply_symm_apply]
  haveI : Finite (Cat d) := Finite.of_surjective πS hπS
  set a := ε.symm x with ha
  set b := ε.symm y with hb
  have haE : πS a ∈ E₀ := by rw [ha, hπSε]; exact hxE
  have hbE : πS b ∈ E₀ := by rw [hb, hπSε]; exact hyE
  have hab' : a * b ≠ b * a := by
    intro he
    apply hxy
    have := congrArg ε he
    rwa [map_mul, map_mul, ha, hb, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      at this
  obtain ⟨ha1, hba, r, hrE, hrcl, hra, hrb, -⟩ :=
    exists_radical hp (Nat.succ_pos n) πS hπS hkerS hE hcard haE hbE hab'
  obtain ⟨X, Y, ζ, ν, hXE, hYE, hYr, hXcl, hrX, hrY, hζ, hζN, hYX, hν, hYp⟩ :=
    exists_heis_pair h hp hp2 hpq (Nat.succ_pos n) πS hkerS hE hcard haE hbE hab' ha1 hba
      hrE hrcl hra hrb
  have hXp1 : πS (X ^ p) = 1 := by rw [map_pow]; exact hE.2 _ hXE
  obtain ⟨β, hβ⟩ := hkerS (X ^ p) hXp1
  have hXp : ((X : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) ^ p = β • 1 := by
    rw [← hβ, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have hr1 : πS r ≠ 1 := fun h1 => hrcl (h1 ▸ Subgroup.one_mem _)
  have hrp1 : πS (r ^ p) = 1 := by rw [map_pow]; exact hE.2 _ hrE
  obtain ⟨α, hα⟩ := hkerS (r ^ p) hrp1
  have hrpα : ((r : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) ^ p = α • 1 := by
    rw [← hα, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  by_cases hcl : ∃ ρ : K, ρ ^ p = α
  ·
    obtain ⟨ρ, hρ⟩ := hcl
    have hρ0 : ρ ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hρ
      exact scalar_ne_zero_of_matPow (Nat.succ_pos n) hrpα hρ.symm
    have hrp : ((r : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) ^ p =
        (ρ ^ p) • 1 := by rw [hρ]; exact hrpα
    have hn3 : 3 ≤ n + 1 := by
      have hc := card_mul_finrank_eigen hp hζ hYX hν hYp ⟨0, hp.pos⟩
      have hpos : 0 < Module.finrank K (Module.End.eigenspace
          (Matrix.toLin' ((Y : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K))
          (ν * ζ ^ ((⟨0, hp.pos⟩ : Fin p) : ℕ))) := by
        rcases Nat.eq_zero_or_pos (Module.finrank K (Module.End.eigenspace
          (Matrix.toLin' ((Y : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K))
          (ν * ζ ^ ((⟨0, hp.pos⟩ : Fin p) : ℕ)))) with h0 | h0
        · rw [h0, mul_zero] at hc
          omega
        · exact h0
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have := Nat.mul_le_mul_left p hpos
      omega
    have hker'S : ∀ g : CFSG.LieType.Universal.Unitary.SUid
        (CFSG.LieType.BorelTits.unitaryInvolution K ℓ f) (n + 1), (∃ c : K,
          ((g : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = c • 1) →
        πS g = 1 :=
      fun g hg => map_scalar_eq_one hd h hq2 hn3 πS hπS hkerS hab' g hg
    by_cases hn : n + 1 ≤ 2 * p
    · exact hyperGen_of_nonab_two h hp hp2 hpq hq2 hn πS hπS hker'S hE hcard hXE hYE hrE hr1
        hYr hXcl hrX hrY hζ hζN hYX hXp hν hYp hρ0 hrp
    · exact hyperGen_of_nonab_pth h hp hp2 hpq hq2 (by omega) πS hπS hker'S hE hcard hXE hYE hrE
        hr1 hYr hXcl hrX hrY hζ hζN hYX hXp hν hYp hρ0 hrp
  ·
    exact hyperGen_of_nonab_pow h hp hp2 hpq hq2 πS hπS hE hcard hXE hYE hrE hr1 hYr hXcl hrX hrY
      hζ hζN hYX hXp hν hYp hrpα hcl

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
