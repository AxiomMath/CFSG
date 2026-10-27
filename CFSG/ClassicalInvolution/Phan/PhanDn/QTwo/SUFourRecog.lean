module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.SUFourStab
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.SUFour
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1310u
public import CFSG.RankThree.PartOne.KF.R12Lin
public import CFSG.LocalAnalysis.StandardType.GGQTwoSU34Aux5
public import CFSG.Fischer.Classification.PartII.Herm.Classify
public import CFSG.ClassicalInvolution.Phan.Frames.Action

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg
open scoped Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private noncomputable def toL {n : ℕ} (g : Su K 2 1 n) :
    (Fin n → K) →ₗ[K] (Fin n → K) :=
  Matrix.toLin' (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))

private theorem toL_apply {n : ℕ} (g : Su K 2 1 n) (v : Fin n → K) :
    toL g v = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v := rfl

private theorem toL_smul {n : ℕ} (g : Su K 2 1 n) (v : Fin n → K) : toL g v = g • v := by
  rw [toL_apply, smul_def]

private theorem toL_one {n : ℕ} : toL (1 : Su K 2 1 n) = 1 := by
  apply LinearMap.ext
  intro v
  rw [toL_smul, one_smul]
  rfl

private theorem toL_mul {n : ℕ} (g h : Su K 2 1 n) : toL (g * h) = toL g * toL h := by
  apply LinearMap.ext
  intro v
  simp only [toL_apply, Module.End.mul_apply, Subgroup.coe_mul, Units.val_mul,
    Matrix.mulVec_mulVec]

private theorem toL_pow {n : ℕ} (g : Su K 2 1 n) (k : ℕ) : toL (g ^ k) = toL g ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, toL_one]
  | succ k ih => rw [pow_succ, pow_succ, toL_mul, ih]

private theorem toL_injective {n : ℕ} (g : Su K 2 1 n) : Function.Injective (toL g) := by
  intro a b h
  rw [toL_smul, toL_smul] at h
  calc a = g⁻¹ • (g • a) := (inv_smul_smul g a).symm
    _ = g⁻¹ • (g • b) := by rw [h]
    _ = b := inv_smul_smul g b

private theorem toL_inj {n : ℕ} {g h : Su K 2 1 n} (H : toL g = toL h) : g = h := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hv := congrFun (congrArg (fun f : (Fin n → K) →ₗ[K] (Fin n → K) =>
    f (Pi.single j 1)) H) i
  rw [toL_apply, toL_apply, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hv
  exact hv

theorem smul_smul_vector {n : ℕ} (g : Su K 2 1 n) (a : K) (v : Fin n → K) :
    g • (a • v) = a • (g • v) := by
  rw [smul_def, smul_def, Matrix.mulVec_smul]

omit [Finite K] in
private theorem three_ne_zero : (3 : K) ≠ 0 := by
  intro h
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3 : (3 : K) = 1 := by
    rw [show (3 : K) = 2 + 1 by norm_num, h2, zero_add]
  rw [h3] at h
  exact one_ne_zero h

omit [CharP K 2] in
private theorem units_pow_three (hK : Nat.card K = 4) (u : Kˣ) : u ^ 3 = 1 := by
  have hcard : Nat.card Kˣ = 3 := by
    rw [CFSG.ClassicalGroups.Unitary.card_units_of_card (p := 2) (f := 1)
      (by rw [hK]; norm_num)]
    norm_num
  rw [← hcard, pow_card_eq_one']

theorem fixSU_smul_single {a : K} (ha : a ≠ 0) (v : Fin 4 → K) :
    fixSU {a • v} = fixSU {v} := by
  ext g
  simp only [fixSU, Subgroup.mem_iInf, Set.mem_singleton_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro h i hi
    have h1 : g • (a • v) = a • v := h (a • v) rfl
    rw [smul_smul_vector] at h1
    have h2 : g • v = v := by
      funext j
      exact mul_left_cancel₀ ha (congrFun h1 j)
    rw [hi, h2]
  · intro h i hi
    rw [hi, smul_smul_vector, h v rfl]

private theorem herm_single_three :
    herm (unitaryInvolution K 2 1) (Pi.single (3 : Fin 4) (1 : K))
      (Pi.single (3 : Fin 4) (1 : K)) = 1 := by
  rw [herm_single_left]
  simp

private theorem card_fixSU_three (hK : Nat.card K = 4) :
    Nat.card (fixSU {Pi.single (3 : Fin 4) (1 : K)}) = 216 := by
  rw [fixSU_std.1]
  have hinj : Function.Injective (blk012 K) := by
    simpa [blk012] using blockEmb_injective (K := K) (p := 2) (f := 1) (m := 4) (k := 3)
      (i := 0) (by norm_num)
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top]
  exact CFSG.StandardType.QTwo.qTwoS34_card_Su_three hK

private theorem card_fixSU_zero_one (hK : Nat.card K = 4) :
    Nat.card (fixSU {Pi.single (0 : Fin 4) (1 : K), Pi.single (1 : Fin 4) (1 : K)}) = 6 := by
  rw [fixSU_std.2.2.2.2]
  have hinj : Function.Injective (blk123 K) := by
    simpa [blk123] using blockEmb_injective (K := K) (p := 2) (f := 1) (m := 4) (k := 3)
      (i := 1) (by norm_num)
  rw [Subgroup.card_map_of_injective hinj]
  change Nat.card ((embSUid (unitaryInvolution K 2 1) 0).range) = 6
  rw [MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (embSUid_injective (unitaryInvolution K 2 1) 0),
    Subgroup.card_top]
  exact CFSG.StandardType.QTwo.qTwoS34_card_Su_two hK

theorem card_fixSU_single (hK : Nat.card K = 4) {v : Fin 4 → K}
    (hv : herm (unitaryInvolution K 2 1) v v = 1) : Nat.card (fixSU {v}) = 216 := by
  have hσ : IsUnitaryInvolution (unitaryInvolution K 2 1) :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) (by rw [hK]; norm_num)
  obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_norm_one hσ (n := 4) (by norm_num)
    herm_single_three hv
  have hfix : fixSU {v} = (fixSU {Pi.single (3 : Fin 4) (1 : K)}).map
      (MulAut.conj t).toMonoidHom := by
    rw [← ht, ← Set.smul_set_singleton, fixSU_smul]
  rw [hfix, Subgroup.card_map_of_injective (MulAut.conj t).injective]
  exact card_fixSU_three hK

theorem fixSU_smul_pair {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (v x : Fin 4 → K) : fixSU {a • v, b • x} = fixSU {v, x} := by
  ext g
  simp only [fixSU, Subgroup.mem_iInf, Set.mem_insert_iff, Set.mem_singleton_iff,
    MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h1 : g • (a • v) = a • v := h (a • v) (Or.inl rfl)
    have h2 : g • (b • x) = b • x := h (b • x) (Or.inr rfl)
    rw [smul_smul_vector] at h1 h2
    have hv : g • v = v := by
      funext j
      exact mul_left_cancel₀ ha (congrFun h1 j)
    have hx : g • x = x := by
      funext j
      exact mul_left_cancel₀ hb (congrFun h2 j)
    rintro y (rfl | rfl)
    · exact hv
    · exact hx
  · intro h y hy
    rcases hy with rfl | rfl
    · rw [smul_smul_vector, h v (Or.inl rfl)]
    · rw [smul_smul_vector, h x (Or.inr rfl)]

private theorem exists_orthonormal_four (hK : Nat.card K = 4) {v x : Fin 4 → K}
    (hv : herm (unitaryInvolution K 2 1) v v = 1)
    (hx : herm (unitaryInvolution K 2 1) x x = 1)
    (hvx : herm (unitaryInvolution K 2 1) v x = 0) :
    ∃ w : Fin 4 → Fin 4 → K, w 0 = v ∧ w 1 = x ∧
      ∀ i j, herm (unitaryInvolution K 2 1) (w i) (w j) = if i = j then 1 else 0 := by
  have hσ : IsUnitaryInvolution (unitaryInvolution K 2 1) :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) (by rw [hK]; norm_num)
  let hh : CFSG.Fischer.Classification.Herm.IsHermForm (unitaryInvolution K 2 1)
      (herm (unitaryInvolution K 2 1) (n := 4)) :=
    { add_left := fun x x' y => herm_add_left _ x x' y
      smul_left := fun c x y => herm_smul_left _ c x y
      conj := fun x y => herm_conj _ hσ.invol x y }
  let B : (Fin 4 → K) →ₛₗ[((unitaryInvolution K 2 1 : K ≃+* K) : K →+* K)]
      (Fin 4 → K) →ₗ[K] K := CFSG.Fischer.Classification.Herm.mkForm hσ.invol hh
  have hB : B.IsSymm := CFSG.Fischer.Classification.Herm.isSymm_mkForm hσ.invol hh
  have hnd : B.SeparatingLeft := by
    intro y hy
    refine eq_zero_of_herm (unitaryInvolution K 2 1) fun z => ?_
    have hyz := hy z
    change herm (unitaryInvolution K 2 1) y z = 0 at hyz
    exact hyz
  let b2 : Fin 2 → (Fin 4 → K) := ![v, x]
  have hb2 : ∀ i j, B (b2 i) (b2 j) = if i = j then 1 else 0 := by
    intro i j
    change herm (unitaryInvolution K 2 1) (b2 i) (b2 j) = if i = j then 1 else 0
    fin_cases i <;> fin_cases j <;> simp [b2]
    all_goals first
      | exact hv
      | exact hx
      | exact hvx
      | exact herm_eq_zero_comm (unitaryInvolution K 2 1) hσ.invol hvx
  obtain ⟨z, hz, hzz⟩ :=
    CFSG.Fischer.Classification.Herm.exists_norm_one_perp (B := B) hb2 hσ hB hnd
      (k := 2) (by simp)
  let b3 : Fin 3 → (Fin 4 → K) := Fin.snoc b2 z
  have hb3 : ∀ i j, B (b3 i) (b3 j) = if i = j then 1 else 0 := by
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa only [b3, Fin.snoc_last, ite_true] using hzz
      | cast j =>
        simp only [b3, Fin.snoc_last, Fin.snoc_castSucc]
        rw [if_neg (Fin.castSucc_lt_last j).ne',
          CFSG.Fischer.Classification.Herm.form_conj hB (b2 j) z, hz j, map_zero]
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [b3, Fin.snoc_last, Fin.snoc_castSucc]
        rw [if_neg (Fin.castSucc_lt_last i).ne, hz i]
      | cast j => simpa only [b3, Fin.snoc_castSucc, Fin.castSucc_inj] using hb2 i j
  obtain ⟨w, hw, hww⟩ :=
    CFSG.Fischer.Classification.Herm.exists_norm_one_perp (B := B) hb3 hσ hB hnd
      (k := 3) (by simp)
  let b4 : Fin 4 → (Fin 4 → K) := Fin.snoc b3 w
  have hb4 : ∀ i j, B (b4 i) (b4 j) = if i = j then 1 else 0 := by
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa only [b4, Fin.snoc_last, ite_true] using hww
      | cast j =>
        simp only [b4, Fin.snoc_last, Fin.snoc_castSucc]
        rw [if_neg (Fin.castSucc_lt_last j).ne',
          CFSG.Fischer.Classification.Herm.form_conj hB (b3 j) w, hw j, map_zero]
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [b4, Fin.snoc_last, Fin.snoc_castSucc]
        rw [if_neg (Fin.castSucc_lt_last i).ne, hw i]
      | cast j => simpa only [b4, Fin.snoc_castSucc, Fin.castSucc_inj] using hb3 i j
  refine ⟨b4, ?_, ?_, fun i j => ?_⟩
  · simp [b4, b3, b2]
  · simp [b4, b3, b2]
  · have h := hb4 i j
    change herm (unitaryInvolution K 2 1) (b4 i) (b4 j) = _ at h
    exact h

theorem card_fixSU_pair (hK : Nat.card K = 4) {v x : Fin 4 → K}
    (hv : herm (unitaryInvolution K 2 1) v v = 1)
    (hx : herm (unitaryInvolution K 2 1) x x = 1)
    (hvx : herm (unitaryInvolution K 2 1) v x = 0) :
    Nat.card (fixSU {v, x}) = 6 := by
  obtain ⟨w, hw0, hw1, hw⟩ := exists_orthonormal_four hK hv hx hvx
  obtain ⟨g, hg⟩ := exists_mem_SUid_smul_single (σ := unitaryInvolution K 2 1) hw
  obtain ⟨a0, ha0, hg0⟩ := hg 0
  obtain ⟨a1, ha1, hg1⟩ := hg 1
  have hfix : fixSU {v, x} = (fixSU {Pi.single (0 : Fin 4) (1 : K),
      Pi.single (1 : Fin 4) (1 : K)}).map (MulAut.conj g).toMonoidHom := by
    calc fixSU {v, x} = fixSU {a0 • v, a1 • x} := (fixSU_smul_pair ha0 ha1 v x).symm
      _ = fixSU {g • Pi.single (0 : Fin 4) (1 : K), g • Pi.single (1 : Fin 4) (1 : K)} := by
        rw [hg0, hg1, hw0, hw1]
      _ = fixSU (g • ({Pi.single (0 : Fin 4) (1 : K),
          Pi.single (1 : Fin 4) (1 : K)} : Set (Fin 4 → K))) := by
        congr 1
        ext y
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_smul_set]
        constructor
        · rintro (rfl | rfl)
          · exact ⟨_, Or.inl rfl, rfl⟩
          · exact ⟨_, Or.inr rfl, rfl⟩
        · rintro ⟨z, (rfl | rfl), rfl⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
      _ = _ := fixSU_smul g _
  rw [hfix, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact card_fixSU_zero_one hK

private theorem finrank_eigenspaces_eq_four {ω : K}
    (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) {t : Su K 2 1 4} (ht : t ^ 3 = 1) :
    Module.finrank K (Module.End.eigenspace (toL t) 1) +
      Module.finrank K (Module.End.eigenspace (toL t) ω) +
      Module.finrank K (Module.End.eigenspace (toL t) (ω ^ 2)) = 4 := by
  have ht' : toL t ^ 3 = 1 := by rw [← toL_pow, ht, toL_one]
  have h := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310u.finrank_eq_add_add
    three_ne_zero hω1 hω3 ht' (U := ⊤) (fun _ _ => Submodule.mem_top)
  rw [top_inf_eq, top_inf_eq, top_inf_eq, finrank_top,
    Module.finrank_fintype_fun_eq_card] at h
  simpa only [Fintype.card_fin] using h.symm

private theorem eigenspace_map_of_commute {t s : Su K 2 1 4} (h : s * t = t * s) (μ : K) :
    ∀ v ∈ Module.End.eigenspace (toL t) μ, toL s v ∈ Module.End.eigenspace (toL t) μ := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have hcomm : toL s * toL t = toL t * toL s := by
    rw [← toL_mul, h, toL_mul]
  calc toL t (toL s v) = (toL t * toL s) v := rfl
    _ = (toL s * toL t) v := by rw [hcomm]
    _ = toL s (toL t v) := rfl
    _ = toL s (μ • v) := by rw [hv]
    _ = μ • toL s v := (toL s).map_smul μ v

private theorem eigenspace_inv_map {t s : Su K 2 1 4}
    (h : s * t * s⁻¹ = t⁻¹) {μ : K} (hμ : μ ≠ 0) :
    ∀ v ∈ Module.End.eigenspace (toL t) μ, toL s v ∈ Module.End.eigenspace (toL t) μ⁻¹ := by
  have hinv : s * t⁻¹ * s⁻¹ = t := by
    have := congrArg (fun x : Su K 2 1 4 => x⁻¹) h
    simpa [mul_assoc] using this
  have hts : t * s = s * t⁻¹ := by
    calc t * s = (s * t⁻¹ * s⁻¹) * s := by rw [hinv]
      _ = s * t⁻¹ := by group
  have hts' : toL t * toL s = toL s * toL t⁻¹ := by
    rw [← toL_mul, ← toL_mul, hts]
  intro v hv
  have hv' : toL t v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  rw [Module.End.mem_eigenspace_iff]
  have htinv : toL t⁻¹ v = μ⁻¹ • v := by
    apply toL_injective t
    calc toL t (toL t⁻¹ v) = (toL t * toL t⁻¹) v := rfl
      _ = (toL (t * t⁻¹)) v := by rw [toL_mul]
      _ = v := by rw [mul_inv_cancel, toL_one, Module.End.one_apply]
      _ = (μ⁻¹ * μ) • v := by rw [inv_mul_cancel₀ hμ, one_smul]
      _ = μ⁻¹ • (μ • v) := by rw [smul_smul]
      _ = μ⁻¹ • toL t v := by rw [hv']
      _ = toL t (μ⁻¹ • v) := ((toL t).map_smul μ⁻¹ v).symm
  calc toL t (toL s v) = (toL t * toL s) v := rfl
    _ = (toL s * toL t⁻¹) v := by rw [hts']
    _ = toL s (toL t⁻¹ v) := rfl
    _ = toL s (μ⁻¹ • v) := by rw [htinv]
    _ = μ⁻¹ • toL s v := (toL s).map_smul μ⁻¹ v

private theorem finrank_eigenspace_eq_of_inv {t s : Su K 2 1 4}
    (h : s * t * s⁻¹ = t⁻¹) (hs2 : s * s = 1) {μ : K} (hμ : μ ≠ 0) :
    Module.finrank K (Module.End.eigenspace (toL t) μ) =
      Module.finrank K (Module.End.eigenspace (toL t) μ⁻¹) := by
  have hmap : ∀ v ∈ Module.End.eigenspace (toL t) μ, toL s v ∈ Module.End.eigenspace (toL t) μ⁻¹ :=
    eigenspace_inv_map h hμ
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have h' : s⁻¹ * t * (s⁻¹)⁻¹ = t⁻¹ := by
    simpa [hsinv] using h
  have hμ' : μ⁻¹ ≠ 0 := inv_ne_zero hμ
  have hmap' : ∀ v ∈ Module.End.eigenspace (toL t) μ⁻¹,
      toL s⁻¹ v ∈ Module.End.eigenspace (toL t) μ := by
    have := eigenspace_inv_map h' hμ'
    simpa [inv_inv] using this
  let f : Module.End.eigenspace (toL t) μ →ₗ[K] Module.End.eigenspace (toL t) μ⁻¹ :=
    (toL s).restrict hmap
  let g : Module.End.eigenspace (toL t) μ⁻¹ →ₗ[K] Module.End.eigenspace (toL t) μ :=
    (toL s⁻¹).restrict hmap'
  have hfg : f.comp g = 1 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change toL s (toL s⁻¹ (v : Fin 4 → K)) = (v : Fin 4 → K)
    calc toL s (toL s⁻¹ v) = (toL s * toL s⁻¹) v := rfl
      _ = (toL (s * s⁻¹)) v := by rw [toL_mul]
      _ = v := by rw [mul_inv_cancel, toL_one, Module.End.one_apply]
  have hgf : g.comp f = 1 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change toL s⁻¹ (toL s (v : Fin 4 → K)) = (v : Fin 4 → K)
    calc toL s⁻¹ (toL s v) = (toL s⁻¹ * toL s) v := rfl
      _ = (toL (s⁻¹ * s)) v := by rw [toL_mul]
      _ = v := by rw [inv_mul_cancel, toL_one, Module.End.one_apply]
  exact LinearEquiv.finrank_eq (LinearEquiv.ofLinear f g hfg hgf)

private theorem eq_zero_or_eq_three_of_dvd {d : ℕ} (h3 : 3 ∣ d) (h4 : d ≤ 4) :
    d = 0 ∨ d = 3 := by
  obtain ⟨k, rfl⟩ := h3
  have hk : k = 0 ∨ k = 1 := by omega
  rcases hk with rfl | rfl <;> omega

private noncomputable def omegaUnit {ω : K}
    (hω : unitaryInvolution K 2 1 ω * ω = 1) : normOne (unitaryInvolution K 2 1) :=
  ⟨Units.mk0 ω (by
    rintro rfl
    simp at hω), hω⟩

private theorem coe_omegaUnit {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    ((omegaUnit hω : normOne (unitaryInvolution K 2 1)) : Kˣ).val = ω := rfl

private theorem omegaUnit_pow_three {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    omegaUnit hω ^ 3 = 1 := by
  have hω3 : ω ^ 3 = 1 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]
    rwa [unitaryInvolution_apply] at hω
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_omegaUnit, hω3]
  simp

private theorem omegaUnit_ne_one {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1)
    (hω1 : ω ≠ 1) : omegaUnit hω ≠ 1 := by
  intro h
  apply hω1
  have := congrArg (fun u : normOne (unitaryInvolution K 2 1) => ((u : Kˣ) : K)) h
  simpa [coe_omegaUnit] using this

private noncomputable def cDiag {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    Fin 3 → normOne (unitaryInvolution K 2 1) :=
  fun i => if i = 0 then 1 else if i = 1 then omegaUnit hω else omegaUnit hω ^ 2

private theorem cDiag_zero {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    cDiag hω 0 = 1 := by simp [cDiag]

private theorem cDiag_one {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    cDiag hω 1 = omegaUnit hω := by simp [cDiag]

private theorem cDiag_two {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    cDiag hω 2 = omegaUnit hω ^ 2 := by simp [cDiag]

private theorem cDiag_mem_detKer {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    cDiag hω ∈ detKer (unitaryInvolution K 2 1) 3 := by
  rw [mem_detKer, Fin.prod_univ_three, cDiag_zero, cDiag_one, cDiag_two, one_mul,
    ← pow_succ']
  exact omegaUnit_pow_three hω

private noncomputable def cElt {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    Su K 2 1 3 :=
  diagSU (unitaryInvolution K 2 1) (cDiag hω) (cDiag_mem_detKer hω)

private noncomputable def wElt {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    Su K 2 1 3 :=
  diagSU (unitaryInvolution K 2 1) (fun _ => omegaUnit hω) (by
    rw [mem_detKer, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact omegaUnit_pow_three hω)

private def cycMat : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j =>
    if i = 0 ∧ j = 2 then 1 else if i = 1 ∧ j = 0 then 1 else if i = 2 ∧ j = 1 then 1 else 0

set_option linter.unusedSectionVars false in
private theorem cycMat_det : (cycMat (K := K)).det = 1 := by
  simp [cycMat, Matrix.det_fin_three]

private theorem cycMat_conj :
    conjTr (unitaryInvolution K 2 1) (cycMat (K := K)) * cycMat = 1 := by
  rw [conjTr]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat, Matrix.mul_apply]

private theorem cycMat_isometry (x y : Fin 3 → K) :
    herm (unitaryInvolution K 2 1) ((cycMat (K := K)) *ᵥ x) ((cycMat (K := K)) *ᵥ y) =
      herm (unitaryInvolution K 2 1) x y := by
  rw [herm_mulVec, cycMat_conj, Matrix.one_mulVec]

private noncomputable def dElt : Su K 2 1 3 :=
  mkSU (unitaryInvolution K 2 1) (cycMat (K := K)) cycMat_det cycMat_isometry

private theorem dElt_smul_zero :
    (dElt (K := K)) • (Pi.single (0 : Fin 3) (1 : K) : Fin 3 → K) =
      (Pi.single (1 : Fin 3) (1 : K) : Fin 3 → K) := by
  change mkSU (unitaryInvolution K 2 1) (cycMat (K := K)) cycMat_det cycMat_isometry •
    (Pi.single (0 : Fin 3) (1 : K) : Fin 3 → K) =
      (Pi.single (1 : Fin 3) (1 : K) : Fin 3 → K)
  rw [mkSU_smul]
  rw [Matrix.mulVec_single_one]
  ext i
  fin_cases i <;> simp [cycMat]

private theorem dElt_smul_one :
    (dElt (K := K)) • (Pi.single (1 : Fin 3) (1 : K) : Fin 3 → K) =
      (Pi.single (2 : Fin 3) (1 : K) : Fin 3 → K) := by
  change mkSU (unitaryInvolution K 2 1) (cycMat (K := K)) cycMat_det cycMat_isometry •
    (Pi.single (1 : Fin 3) (1 : K) : Fin 3 → K) =
      (Pi.single (2 : Fin 3) (1 : K) : Fin 3 → K)
  rw [mkSU_smul]
  rw [Matrix.mulVec_single_one]
  ext i
  fin_cases i <;> simp [cycMat]

private theorem dElt_smul_two :
    (dElt (K := K)) • (Pi.single (2 : Fin 3) (1 : K) : Fin 3 → K) =
      (Pi.single (0 : Fin 3) (1 : K) : Fin 3 → K) := by
  change mkSU (unitaryInvolution K 2 1) (cycMat (K := K)) cycMat_det cycMat_isometry •
    (Pi.single (2 : Fin 3) (1 : K) : Fin 3 → K) =
      (Pi.single (0 : Fin 3) (1 : K) : Fin 3 → K)
  rw [mkSU_smul]
  rw [Matrix.mulVec_single_one]
  ext i
  fin_cases i <;> simp [cycMat]

private theorem cElt_smul_zero {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    cElt hω • (Pi.single (0 : Fin 3) (1 : K) : Fin 3 → K) =
      Pi.single (0 : Fin 3) (1 : K) := by
  rw [cElt, smul_single_diagSU, cDiag_zero]
  simp

private theorem cElt_smul_one {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    cElt hω • (Pi.single (1 : Fin 3) (1 : K) : Fin 3 → K) =
      ω • (Pi.single (1 : Fin 3) (1 : K) : Fin 3 → K) := by
  rw [cElt, smul_single_diagSU, cDiag_one, coe_omegaUnit]

private theorem cElt_smul_two {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    cElt hω • (Pi.single (2 : Fin 3) (1 : K) : Fin 3 → K) =
      ω ^ 2 • (Pi.single (2 : Fin 3) (1 : K) : Fin 3 → K) := by
  rw [cElt, smul_single_diagSU, cDiag_two]
  simp [coe_omegaUnit]

private theorem wElt_smul {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1)
    (v : Fin 3 → K) : wElt hω • v = ω • v := by
  funext i
  rw [wElt, diagSU_smul]
  simp [coe_omegaUnit]

private theorem wElt_toL {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    toL (wElt hω) = ω • (1 : Module.End K (Fin 3 → K)) := by
  apply LinearMap.ext
  intro v
  rw [toL_smul, wElt_smul]
  rfl

private theorem wElt_central {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1)
    (g : Su K 2 1 3) : wElt hω * g = g * wElt hω := by
  apply toL_inj
  rw [toL_mul, toL_mul, wElt_toL]
  apply LinearMap.ext
  intro v
  simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply]
  rw [map_smul]

private theorem wElt_pow_three {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    wElt hω ^ 3 = 1 := by
  apply toL_inj
  rw [toL_pow, toL_one, wElt_toL]
  apply LinearMap.ext
  intro v
  rw [pow_three]
  simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply]
  have hω3 : ω ^ 3 = 1 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]
    rwa [unitaryInvolution_apply] at hω
  calc ω • ω • ω • v = (ω ^ 3) • v := by module
    _ = v := by rw [hω3, one_smul]

private theorem wElt_ne_one {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1)
    (hω1 : ω ≠ 1) : wElt hω ≠ 1 := by
  intro h
  have h1 : toL (wElt hω) = toL (1 : Su K 2 1 3) := by rw [h]
  rw [toL_one, wElt_toL] at h1
  have h2 := congrFun (congrArg (fun f : Module.End K (Fin 3 → K) =>
    f (Pi.single (0 : Fin 3) (1 : K))) h1) 0
  simp [LinearMap.smul_apply] at h2
  exact hω1 h2

private theorem toL_ext_basis {n : ℕ} {g h : Su K 2 1 n}
    (H : ∀ j : Fin n, g • (Pi.single j (1 : K) : Fin n → K) = h • Pi.single j 1) :
    g = h := by
  apply toL_inj
  apply (Pi.basisFun K (Fin n)).ext
  intro j
  simpa only [Pi.basisFun_apply, toL_smul] using H j

private theorem omega_pow_three {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    ω ^ 3 = 1 := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]
  rwa [unitaryInvolution_apply] at hω

private theorem cElt_mul_dElt_zero {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    (cElt hω * dElt) • (Pi.single (0 : Fin 3) (1 : K) : Fin 3 → K) =
      (wElt hω * dElt * cElt hω) • (Pi.single (0 : Fin 3) (1 : K) : Fin 3 → K) := by
  simp only [mul_smul]
  rw [dElt_smul_zero, cElt_smul_one, cElt_smul_zero, dElt_smul_zero, wElt_smul]

private theorem cElt_mul_dElt_one {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    (cElt hω * dElt) • (Pi.single (1 : Fin 3) (1 : K) : Fin 3 → K) =
      (wElt hω * dElt * cElt hω) • (Pi.single (1 : Fin 3) (1 : K) : Fin 3 → K) := by
  simp only [mul_smul]
  rw [dElt_smul_one, cElt_smul_two, cElt_smul_one, smul_smul_vector, dElt_smul_one,
    wElt_smul, smul_smul, pow_two]

private theorem cElt_mul_dElt_two {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    (cElt hω * dElt) • (Pi.single (2 : Fin 3) (1 : K) : Fin 3 → K) =
      (wElt hω * dElt * cElt hω) • (Pi.single (2 : Fin 3) (1 : K) : Fin 3 → K) := by
  simp only [mul_smul]
  rw [dElt_smul_two, cElt_smul_two, cElt_smul_zero, smul_smul_vector, dElt_smul_two,
    wElt_smul, smul_smul, ← pow_succ', omega_pow_three hω, one_smul]

private theorem cElt_mul_dElt {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    cElt hω * dElt = wElt hω * dElt * cElt hω := by
  apply toL_ext_basis
  intro j
  fin_cases j
  · exact cElt_mul_dElt_zero hω
  · exact cElt_mul_dElt_one hω
  · exact cElt_mul_dElt_two hω

private theorem pow_finrank_eigenspace_of_mul_eq {z x y : Su K 2 1 4} {μ : K}
    (hzx : x * z = z * x) (hzy : y * z = z * y) (hxy : x * y = z * y * x) :
    μ ^ Module.finrank K (Module.End.eigenspace (toL z) μ) = 1 := by
  let W := Module.End.eigenspace (toL z) μ
  have hxW : ∀ w ∈ W, toL x w ∈ W := eigenspace_map_of_commute hzx μ
  have hyW : ∀ w ∈ W, toL y w ∈ W := eigenspace_map_of_commute hzy μ
  have hrel : ∀ w : W, (toL x).restrict hxW ((toL y).restrict hyW w) =
      μ • (toL y).restrict hyW ((toL x).restrict hxW w) := by
    intro w
    apply Subtype.ext
    change toL x (toL y (w : Fin 4 → K)) = μ • toL y (toL x (w : Fin 4 → K))
    calc toL x (toL y w) = toL (x * y) w := by rw [toL_mul, Module.End.mul_apply]
      _ = toL (z * y * x) w := by rw [hxy]
      _ = toL z (toL y (toL x w)) := by
        rw [show z * y * x = z * (y * x) by group, toL_mul, toL_mul]
        rfl
      _ = μ • toL y (toL x w) :=
        Module.End.mem_eigenspace_iff.mp (hyW (toL x w) (hxW w w.2))
  have hx_inj : Function.Injective ((toL x).restrict hxW) := by
    intro a b h
    apply Subtype.ext
    exact toL_injective x (congrArg Subtype.val h)
  have hy_inj : Function.Injective ((toL y).restrict hyW) := by
    intro a b h
    apply Subtype.ext
    exact toL_injective y (congrArg Subtype.val h)
  have h := CFSG.RankThree.PartOne.KFU.comm_scalar_pow_finrank (W := ⊤)
    ((toL x).restrict hxW) ((toL y).restrict hyW)
    (fun _ _ => Submodule.mem_top) (fun _ _ => Submodule.mem_top) hx_inj hy_inj μ hrel
  simpa [W] using h

private theorem finrank_eigenspace_one_of_heisenberg {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {zS xS yS : Su K 2 1 4} (hz3 : zS ^ 3 = 1) (hz1 : zS ≠ 1)
    (hzx : xS * zS = zS * xS) (hzy : yS * zS = zS * yS)
    (hxy : xS * yS = zS * yS * xS) :
    Module.finrank K (Module.End.eigenspace (toL zS) 1) = 1 := by
  have hdim := finrank_eigenspaces_eq_four hω1 hω3 hz3
  set d1 : ℕ := Module.finrank K (Module.End.eigenspace (toL zS) 1)
  set dω : ℕ := Module.finrank K (Module.End.eigenspace (toL zS) ω)
  set dω2 : ℕ := Module.finrank K (Module.End.eigenspace (toL zS) (ω ^ 2))
  have hdim' : d1 + dω + dω2 = 4 := by simpa [d1, dω, dω2] using hdim
  have hωprim : IsPrimitiveRoot ω 3 :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hω3 hω1)
  have hω2prim : IsPrimitiveRoot (ω ^ 2) 3 :=
    hωprim.pow_of_coprime 2 (by decide)
  have hpowω : ω ^ dω = 1 := by
    have h := pow_finrank_eigenspace_of_mul_eq hzx hzy hxy
      (z := zS) (x := xS) (y := yS) (μ := ω)
    simpa [dω] using h
  have hpowω2 : (ω ^ 2) ^ dω2 = 1 := by
    have h := pow_finrank_eigenspace_of_mul_eq hzx hzy hxy
      (z := zS) (x := xS) (y := yS) (μ := ω ^ 2)
    simpa [dω2] using h
  have h3dvdω : 3 ∣ dω := hωprim.dvd_of_pow_eq_one dω hpowω
  have h3dvdω2 : 3 ∣ dω2 := hω2prim.dvd_of_pow_eq_one dω2 hpowω2
  have hdωle : dω ≤ 4 := by
    have := Submodule.finrank_le (Module.End.eigenspace (toL zS) ω)
    simpa [dω, Module.finrank_fintype_fun_eq_card] using this
  have hdω2le : dω2 ≤ 4 := by
    have := Submodule.finrank_le (Module.End.eigenspace (toL zS) (ω ^ 2))
    simpa [dω2, Module.finrank_fintype_fun_eq_card] using this
  have hdωcases : dω = 0 ∨ dω = 3 := eq_zero_or_eq_three_of_dvd h3dvdω hdωle
  have hdω2cases : dω2 = 0 ∨ dω2 = 3 := eq_zero_or_eq_three_of_dvd h3dvdω2 hdω2le
  have hzlin_ne : toL zS ≠ 1 := by
    intro h
    apply hz1
    apply toL_inj
    rw [h, toL_one]
  have hnot4 : d1 ≠ 4 := by
    intro h4
    apply hzlin_ne
    apply LinearMap.ext
    intro v
    have h4' : Module.finrank K (Module.End.eigenspace (toL zS) 1) =
        Module.finrank K (Fin 4 → K) := by
      change d1 = Module.finrank K (Fin 4 → K)
      rw [h4, Module.finrank_fintype_fun_eq_card]
      norm_num
    have hv : v ∈ Module.End.eigenspace (toL zS) 1 := by
      rw [Submodule.eq_top_of_finrank_eq h4']
      exact Submodule.mem_top
    simpa using Module.End.mem_eigenspace_iff.mp hv
  have hd1 : d1 = 1 := by
    rcases hdωcases with h | h <;> rcases hdω2cases with h' | h' <;> omega
  simpa [d1] using hd1

private theorem exists_eigenspace_one_eq_span {zS : Su K 2 1 4}
    (hd1 : Module.finrank K (Module.End.eigenspace (toL zS) 1) = 1) :
    ∃ v₀ : Fin 4 → K, v₀ ≠ 0 ∧ Module.End.eigenspace (toL zS) 1 = K ∙ v₀ := by
  have hE1ne : Module.End.eigenspace (toL zS) 1 ≠ ⊥ := by
    intro hbot
    have : Module.finrank K (Module.End.eigenspace (toL zS) 1) = 0 := by
      rw [hbot, finrank_bot]
    omega
  obtain ⟨v₀, hv₀mem, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE1ne
  have hE1span : Module.End.eigenspace (toL zS) 1 = K ∙ v₀ :=
    eq_span_singleton_of_mem_of_finrank_eq_one (by simpa using hd1) hv₀mem hv₀0
  exact ⟨v₀, hv₀0, hE1span⟩

private theorem herm_eq_zero_of_mem_eigenspace {zS : Su K 2 1 4} {v₀ : Fin 4 → K}
    (hzfix : zS • v₀ = v₀) {μ : K} (hμ1 : μ ≠ 1)
    {w : Fin 4 → K} (hw : w ∈ Module.End.eigenspace (toL zS) μ) :
    herm (unitaryInvolution K 2 1) v₀ w = 0 := by
  have hzw : zS • w = μ • w := by
    simpa [toL_smul] using Module.End.mem_eigenspace_iff.mp hw
  have h := herm_smul_smul (unitaryInvolution K 2 1) zS v₀ w
  rw [hzfix, hzw, herm_smul_right] at h
  have h2 : (μ - 1) * herm (unitaryInvolution K 2 1) v₀ w = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hμ1)

private theorem herm_self_ne_zero_of_perp_eigenspaces {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (hω2ne : ω ^ 2 ≠ 1) {zS : Su K 2 1 4} (hz3 : zS ^ 3 = 1)
    {v₀ : Fin 4 → K} (hv₀0 : v₀ ≠ 0)
    (hE1span : Module.End.eigenspace (toL zS) 1 = K ∙ v₀)
    (hperp : ∀ (μ : K), μ ≠ 1 →
      ∀ w ∈ Module.End.eigenspace (toL zS) μ,
        herm (unitaryInvolution K 2 1) v₀ w = 0) :
    herm (unitaryInvolution K 2 1) v₀ v₀ ≠ 0 := by
  intro h0
  apply hv₀0
  refine eq_zero_of_herm (unitaryInvolution K 2 1) fun y => ?_
  have hzlin3 : toL zS ^ 3 = 1 := by rw [← toL_pow, hz3, toL_one]
  obtain ⟨y0, y1, y2, hy0, hy1, hy2, ht0, ht1, ht2, hsum⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310u.exists_eigen_decomp
      three_ne_zero hω1 hω3 hzlin3 (U := ⊤) (fun _ _ => Submodule.mem_top)
      (u := y) (Submodule.mem_top)
  have h1 : herm (unitaryInvolution K 2 1) v₀ y1 = 0 :=
    hperp ω hω1 y1 (Module.End.mem_eigenspace_iff.mpr ht1)
  have h2 : herm (unitaryInvolution K 2 1) v₀ y2 = 0 :=
    hperp (ω ^ 2) hω2ne y2 (Module.End.mem_eigenspace_iff.mpr ht2)
  have h0' : herm (unitaryInvolution K 2 1) v₀ y0 = 0 := by
    have hy0' : y0 ∈ K ∙ v₀ := by
      rw [← hE1span]
      exact Module.End.mem_eigenspace_iff.mpr (by simpa using ht0)
    obtain ⟨e0, rfl⟩ := Submodule.mem_span_singleton.mp hy0'
    rw [herm_smul_right, h0, mul_zero]
  rw [← hsum, herm_add_right, herm_add_right, h0', h1, h2, add_zero, add_zero]

private theorem le_fixSU_of_commute_of_eigenspace (hK : Nat.card K = 4)
    {J : Subgroup (Su K 2 1 4)} (e : Su K 2 1 3 ≃* J) {zS : Su K 2 1 4}
    (hz_comm : ∀ g : J, (g : Su K 2 1 4) * zS = zS * (g : Su K 2 1 4))
    {v₀ v : Fin 4 → K} {a : K} (hvdef : v = a • v₀) (hzfix : zS • v₀ = v₀)
    (hE1span : Module.End.eigenspace (toL zS) 1 = K ∙ v₀) (hv₀0 : v₀ ≠ 0) :
    J ≤ fixSU {v} := by
  have hpres : ∀ g : J, ∃ d : K, d ≠ 0 ∧ (g : Su K 2 1 4) • v₀ = d • v₀ := by
    intro g
    have hmem : (g : Su K 2 1 4) • v₀ ∈ Module.End.eigenspace (toL zS) 1 := by
      have hmem : v₀ ∈ Module.End.eigenspace (toL zS) 1 := by
        rw [Module.End.mem_eigenspace_iff]
        simpa [toL_smul] using hzfix
      have := eigenspace_map_of_commute (hz_comm g) 1 v₀ hmem
      simpa [toL_smul] using this
    rw [hE1span, Submodule.mem_span_singleton] at hmem
    obtain ⟨d, hd⟩ := hmem
    refine ⟨d, ?_, hd.symm⟩
    rintro rfl
    rw [zero_smul] at hd
    have h := congrArg (fun x => (g : Su K 2 1 4)⁻¹ • x) hd
    simp only [inv_smul_smul, inv_smul_smul] at h
    exact hv₀0 (by simpa using h.symm)
  choose d hd0 hd using hpres
  have hmul : ∀ g h : J, d (g * h) = d g * d h := by
    intro g h
    have h2 : d (g * h) • v₀ = (d g * d h) • v₀ := by
      rw [← hd (g * h)]
      calc ((g * h : J) : Su K 2 1 4) • v₀ =
            ((g : Su K 2 1 4) * (h : Su K 2 1 4)) • v₀ := rfl
        _ = (g : Su K 2 1 4) • ((h : Su K 2 1 4) • v₀) := mul_smul _ _ _
        _ = (g : Su K 2 1 4) • (d h • v₀) := by rw [hd h]
        _ = d h • ((g : Su K 2 1 4) • v₀) := smul_smul_vector _ _ _
        _ = d h • (d g • v₀) := by rw [hd g]
        _ = (d h * d g) • v₀ := by rw [smul_smul]
        _ = (d g * d h) • v₀ := by rw [mul_comm]
    exact (smul_left_inj hv₀0).mp h2
  let χ : J →* Kˣ :=
    MonoidHom.mk' (fun g => Units.mk0 (d g) (hd0 g)) (by
      intro g h
      apply Units.ext
      exact hmul g h)
  have hχe : χ.comp e.toMonoidHom = 1 :=
    eq_one_of_hom_Su_three hK (χ.comp e.toMonoidHom) (units_pow_three hK)
  have hchi : ∀ g : J, χ g = 1 := by
    intro g
    obtain ⟨h, rfl⟩ := e.surjective g
    have := congrArg (fun f : Su K 2 1 3 →* Kˣ => f h) hχe
    simpa [MonoidHom.comp_apply] using this
  intro g hg
  let gJ : J := ⟨g, hg⟩
  have h1 : d gJ = 1 := by
    have := congrArg Units.val (hchi gJ)
    simpa [χ] using this
  have h3 : (gJ : Su K 2 1 4) • v₀ = v₀ := by rw [hd gJ, h1, one_smul]
  have h4 : g • v = v := by
    change (gJ : Su K 2 1 4) • v = v
    rw [hvdef, smul_smul_vector, h3]
  simpa [fixSU, MulAction.mem_stabilizer_iff] using h4

private theorem exists_smul_herm_self_eq_one (hσ : IsUnitaryInvolution (unitaryInvolution K 2 1))
    {v₀ : Fin 4 → K} (hself : herm (unitaryInvolution K 2 1) v₀ v₀ ≠ 0) :
    ∃ (a : K) (v : Fin 4 → K), a ≠ 0 ∧ v = a • v₀ ∧
      herm (unitaryInvolution K 2 1) v v = 1 := by
  obtain ⟨a, ha⟩ := exists_smul_norm_one hσ hself
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul, herm_zero_left] at ha
    exact zero_ne_one ha
  exact ⟨a, a • v₀, ha0, rfl, ha⟩

private theorem exists_eq_fixSU_of_le (hK : Nat.card K = 4) {J : Subgroup (Su K 2 1 4)}
    (e : Su K 2 1 3 ≃* J) {v : Fin 4 → K}
    (hv : herm (unitaryInvolution K 2 1) v v = 1) (hJle : J ≤ fixSU {v}) :
    ∃ v : Fin 4 → K, herm (unitaryInvolution K 2 1) v v = 1 ∧ J = fixSU {v} := by
  have hcardJ : Nat.card J = 216 := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.StandardType.QTwo.qTwoS34_card_Su_three hK
  have hcardF : Nat.card (fixSU {v}) = 216 := card_fixSU_single hK hv
  exact ⟨v, hv, Subgroup.eq_of_le_of_card_ge hJle (by rw [hcardF, hcardJ])⟩

theorem eq_fixSU_of_mulEquiv (hK : Nat.card K = 4) {J : Subgroup (Su K 2 1 4)}
    (e : Su K 2 1 3 ≃* J) : ∃ v : Fin 4 → K, herm (unitaryInvolution K 2 1) v v = 1 ∧
      J = fixSU {v} := by
  have hσ : IsUnitaryInvolution (unitaryInvolution K 2 1) :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) (by rw [hK]; norm_num)
  obtain ⟨ω, hω, hω1⟩ := hσ.exists_norm_one_ne_one
  have hω3 : ω ^ 3 = 1 := omega_pow_three hω
  have hω2ne : ω ^ 2 ≠ 1 := by
    intro h
    have h2 : orderOf ω ∣ 2 := orderOf_dvd_of_pow_eq_one h
    have h3 : orderOf ω ∣ 3 := orderOf_dvd_of_pow_eq_one hω3
    have h1 : orderOf ω = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num) h2 h3
    rw [orderOf_eq_one_iff] at h1
    exact hω1 h1
  let c := cElt hω
  let w := wElt hω
  let x : J := e c
  let y : J := e dElt
  let z : J := e w
  have hz3J : z ^ 3 = 1 := by
    change (e w) ^ 3 = 1
    rw [← map_pow, wElt_pow_three hω, map_one]
  have hz1J : z ≠ 1 := by
    intro h
    apply wElt_ne_one hω hω1
    apply e.injective
    rw [map_one]
    exact h
  have hz_comm : ∀ g : J, g * z = z * g := by
    intro g
    obtain ⟨h, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, wElt_central hω h]
  have hxy : x * y = z * y * x := by
    change e c * e dElt = e w * e dElt * e c
    rw [← map_mul, ← map_mul, ← map_mul, cElt_mul_dElt hω]
  let zS : Su K 2 1 4 := z
  let xS : Su K 2 1 4 := x
  let yS : Su K 2 1 4 := y
  have hz3 : zS ^ 3 = 1 := by
    have := congrArg (fun q : J => (q : Su K 2 1 4)) hz3J
    simpa [zS] using this
  have hz1 : zS ≠ 1 := by
    intro h
    apply hz1J
    apply Subtype.ext
    exact h
  have hzx : xS * zS = zS * xS := by
    have := congrArg (fun q : J => (q : Su K 2 1 4)) (hz_comm x)
    simpa [xS, zS] using this
  have hzy : yS * zS = zS * yS := by
    have := congrArg (fun q : J => (q : Su K 2 1 4)) (hz_comm y)
    simpa [yS, zS] using this
  have hxy' : xS * yS = zS * yS * xS := by
    have := congrArg (fun q : J => (q : Su K 2 1 4)) hxy
    simpa [xS, yS, zS] using this
  have hd1 : Module.finrank K (Module.End.eigenspace (toL zS) 1) = 1 :=
    finrank_eigenspace_one_of_heisenberg hω1 hω3 hz3 hz1 hzx hzy hxy'
  obtain ⟨v₀, hv₀0, hE1span⟩ := exists_eigenspace_one_eq_span hd1
  have hv₀mem : v₀ ∈ Module.End.eigenspace (toL zS) 1 := by
    rw [hE1span]
    exact Submodule.mem_span_singleton.mpr ⟨1, by simp⟩
  have hzfix : zS • v₀ = v₀ := by
    simpa [toL_smul] using Module.End.mem_eigenspace_iff.mp hv₀mem
  have hperp : ∀ (μ : K), μ ≠ 1 →
      ∀ w ∈ Module.End.eigenspace (toL zS) μ,
        herm (unitaryInvolution K 2 1) v₀ w = 0 :=
    fun μ hμ1 w hw => herm_eq_zero_of_mem_eigenspace hzfix hμ1 hw
  have hself : herm (unitaryInvolution K 2 1) v₀ v₀ ≠ 0 :=
    herm_self_ne_zero_of_perp_eigenspaces hω1 hω3 hω2ne hz3 hv₀0 hE1span hperp
  obtain ⟨a, v, _ha0, hvdef, hv⟩ := exists_smul_herm_self_eq_one hσ hself
  have hJle : J ≤ fixSU {v} :=
    le_fixSU_of_commute_of_eigenspace hK e (by
      intro g
      simpa [zS] using congrArg (fun q : J => (q : Su K 2 1 4)) (hz_comm g))
      hvdef hzfix hE1span hv₀0
  exact exists_eq_fixSU_of_le hK e hv hJle

private noncomputable def t0Diag {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    Fin 2 → normOne (unitaryInvolution K 2 1) :=
  fun i => if i = 0 then omegaUnit hω else omegaUnit hω ^ 2

private theorem t0Diag_zero {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    t0Diag hω 0 = omegaUnit hω := by simp [t0Diag]

private theorem t0Diag_one {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    t0Diag hω 1 = omegaUnit hω ^ 2 := by simp [t0Diag]

private theorem t0Diag_mem_detKer {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    t0Diag hω ∈ detKer (unitaryInvolution K 2 1) 2 := by
  rw [mem_detKer, Fin.prod_univ_two, t0Diag_zero, t0Diag_one, ← pow_succ']
  exact omegaUnit_pow_three hω

private noncomputable def t0Elt {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    Su K 2 1 2 :=
  diagSU (unitaryInvolution K 2 1) (t0Diag hω) (t0Diag_mem_detKer hω)

private theorem t0Elt_smul_zero {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    t0Elt hω • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) =
      ω • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) := by
  rw [t0Elt, smul_single_diagSU, t0Diag_zero, coe_omegaUnit]

private theorem t0Elt_smul_one {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    t0Elt hω • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) =
      ω ^ 2 • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) := by
  rw [t0Elt, smul_single_diagSU, t0Diag_one]
  simp [coe_omegaUnit]

private def swap2Mat : Matrix (Fin 2) (Fin 2) K := !![(0 : K), 1; 1, 0]

omit [Finite K] in
private theorem swap2Mat_det : (swap2Mat (K := K)).det = 1 := by
  rw [swap2Mat, Matrix.det_fin_two]
  norm_num
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination -h2

private theorem swap2Mat_conj :
    conjTr (unitaryInvolution K 2 1) (swap2Mat (K := K)) * swap2Mat = 1 := by
  rw [conjTr]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap2Mat, Matrix.mul_apply, Fin.sum_univ_two]

private theorem swap2Mat_isometry (x y : Fin 2 → K) :
    herm (unitaryInvolution K 2 1) ((swap2Mat (K := K)) *ᵥ x) ((swap2Mat (K := K)) *ᵥ y) =
      herm (unitaryInvolution K 2 1) x y := by
  rw [herm_mulVec, swap2Mat_conj, Matrix.one_mulVec]

private noncomputable def s0Elt : Su K 2 1 2 :=
  mkSU (unitaryInvolution K 2 1) (swap2Mat (K := K)) swap2Mat_det swap2Mat_isometry

private theorem s0Elt_smul_zero :
    (s0Elt (K := K)) • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) =
      (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) := by
  change mkSU (unitaryInvolution K 2 1) (swap2Mat (K := K)) swap2Mat_det swap2Mat_isometry •
    (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) = _
  rw [mkSU_smul, Matrix.mulVec_single_one]
  ext i
  fin_cases i <;> simp [swap2Mat]

private theorem s0Elt_smul_one :
    (s0Elt (K := K)) • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) =
      (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) := by
  change mkSU (unitaryInvolution K 2 1) (swap2Mat (K := K)) swap2Mat_det swap2Mat_isometry •
    (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) = _
  rw [mkSU_smul, Matrix.mulVec_single_one]
  ext i
  fin_cases i <;> simp [swap2Mat]

private theorem s0Elt_sq : (s0Elt (K := K)) * s0Elt = 1 := by
  apply toL_ext_basis
  intro j
  fin_cases j
  · change ((s0Elt (K := K)) * s0Elt) • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) =
      (1 : Su K 2 1 2) • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K)
    rw [mul_smul, s0Elt_smul_zero, s0Elt_smul_one, one_smul]
  · change ((s0Elt (K := K)) * s0Elt) • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) =
      (1 : Su K 2 1 2) • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K)
    rw [mul_smul, s0Elt_smul_one, s0Elt_smul_zero, one_smul]

private theorem t0Elt_pow_three {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    t0Elt hω ^ 3 = 1 := by
  apply toL_ext_basis
  intro j
  fin_cases j
  · change (t0Elt hω ^ 3) • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) =
      (1 : Su K 2 1 2) • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K)
    rw [pow_three, mul_smul, mul_smul, t0Elt_smul_zero, smul_smul_vector, smul_smul_vector,
      t0Elt_smul_zero, smul_smul_vector, t0Elt_smul_zero, one_smul]
    calc ω • ω • ω • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) =
        (ω ^ 3) • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) := by module
      _ = _ := by rw [omega_pow_three hω, one_smul]
  · change (t0Elt hω ^ 3) • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) =
      (1 : Su K 2 1 2) • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K)
    rw [pow_three, mul_smul, mul_smul, t0Elt_smul_one, smul_smul_vector, smul_smul_vector,
      t0Elt_smul_one, smul_smul_vector, t0Elt_smul_one, one_smul]
    calc ω ^ 2 • ω ^ 2 • ω ^ 2 • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) =
        ((ω ^ 2) ^ 3) • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) := by module
      _ = _ := by
        rw [show (ω ^ 2) ^ 3 = 1 by
          rw [show (3 : ℕ) = 3 * 1 by norm_num, ← pow_mul, show 2 * 3 = 6 by norm_num]
          rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, omega_pow_three hω, one_pow],
          one_smul]

private theorem t0Elt_ne_one {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1)
    (hω1 : ω ≠ 1) : t0Elt hω ≠ 1 := by
  intro h
  have h1 : t0Elt hω • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) =
      (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) := by rw [h, one_smul]
  rw [t0Elt_smul_zero] at h1
  have h2 := congrFun h1 0
  simp at h2
  exact hω1 h2

private theorem s0Elt_conj_t0Elt {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    (s0Elt (K := K)) * t0Elt hω * (s0Elt (K := K))⁻¹ = (t0Elt hω)⁻¹ := by
  have hs : (s0Elt (K := K))⁻¹ = s0Elt := inv_eq_of_mul_eq_one_right s0Elt_sq
  have ht_inv : (t0Elt hω)⁻¹ = t0Elt hω ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ', t0Elt_pow_three hω])
  have hω_inv : ω⁻¹ = ω ^ 2 := by
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ', omega_pow_three hω])
  have hω2_inv : (ω ^ 2)⁻¹ = ω := by
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ, omega_pow_three hω])
  apply toL_ext_basis
  intro j
  fin_cases j
  · change (s0Elt * t0Elt hω * s0Elt⁻¹) •
        (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) =
      (t0Elt hω)⁻¹ • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K)
    have hL : (s0Elt * t0Elt hω * s0Elt⁻¹) •
        (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) =
        ω ^ 2 • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) := by
      rw [hs, mul_smul, mul_smul, s0Elt_smul_zero, t0Elt_smul_one, smul_smul_vector,
        s0Elt_smul_one]
    have hR : (t0Elt hω)⁻¹ • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) =
        ω ^ 2 • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) := by
      rw [ht_inv, pow_two]
      rw [mul_smul, t0Elt_smul_zero, smul_smul_vector, t0Elt_smul_zero, smul_smul, pow_two]
    rw [hL, hR]
  · change (s0Elt * t0Elt hω * s0Elt⁻¹) •
        (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) =
      (t0Elt hω)⁻¹ • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K)
    have hL : (s0Elt * t0Elt hω * s0Elt⁻¹) •
        (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) =
        ω • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) := by
      rw [hs, mul_smul, mul_smul, s0Elt_smul_one, t0Elt_smul_zero, smul_smul_vector,
        s0Elt_smul_zero]
    have hR : (t0Elt hω)⁻¹ • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) =
        ω • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) := by
      rw [ht_inv, pow_two]
      rw [mul_smul, t0Elt_smul_one, smul_smul_vector, t0Elt_smul_one, smul_smul]
      rw [show ω ^ 2 * ω ^ 2 = ω ^ 4 by ring, show (4 : ℕ) = 3 + 1 by norm_num,
        pow_succ, omega_pow_three hω, one_mul]
    rw [hL, hR]

private theorem conj_eq_self_or_inv_of_mem_zpowers {G : Type*} [Group G] {t y : G}
    (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) (hy : y * t * y⁻¹ ∈ Subgroup.zpowers t) :
    y * t * y⁻¹ = t ∨ y * t * y⁻¹ = t⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hk' : y * t * y⁻¹ = t ^ k := hk.symm
  have hk1 : t ^ k ≠ 1 := by
    intro h
    have h1 : y * t * y⁻¹ = 1 := by rw [hk', h]
    have h2 : t = 1 := by
      have := congrArg (fun z => y⁻¹ * z * y) h1
      simpa [mul_assoc] using this
    exact ht1 h2
  have hred : t ^ k = t ^ (k % 3) := zpow_eq_zpow_emod' k ht3
  have hmod0 : k % 3 ≠ 0 := by
    intro h0
    apply hk1
    rw [hred, h0]
    norm_num
  set r : ℤ := k % 3 with hr
  have hr0 : r ≠ 0 := by simpa [hr] using hmod0
  have hrge : 0 ≤ r := by
    rw [hr]
    exact Int.emod_nonneg k (by norm_num)
  have hrlt : r < 3 := by
    rw [hr]
    exact Int.emod_lt_of_pos k (by norm_num)
  interval_cases r
  · exact absurd rfl hr0
  · left
    rw [hk', hred]
    simp
  · right
    have h2 : t ^ 2 = t⁻¹ := by
      have h : t * t ^ 2 = 1 := by rw [← pow_succ', ht3]
      exact (inv_eq_of_mul_eq_one_right h).symm
    rw [hk', hred]
    simpa [← hr] using h2

private theorem eigenspace_one_map_of_conj {t y : Su K 2 1 4}
    (h : y * t * y⁻¹ = t ∨ y * t * y⁻¹ = t⁻¹) :
    ∀ w ∈ Module.End.eigenspace (toL t) 1, toL y w ∈ Module.End.eigenspace (toL t) 1 := by
  intro w hw
  have hw' : toL t w = w := by simpa using Module.End.mem_eigenspace_iff.mp hw
  rcases h with h | h
  · have hgroup : t * y = y * t := by
      have h' : y * t = t * y := by
        have := congrArg (fun q => q * y) h
        simpa [mul_assoc] using this
      exact h'.symm
    exact eigenspace_map_of_commute hgroup.symm 1 w hw
  · have hgroup : t * y = y * t⁻¹ := by
      have hinv : y * t⁻¹ * y⁻¹ = t := by
        have := congrArg (fun q : Su K 2 1 4 => q⁻¹) h
        simpa [mul_assoc] using this
      have h1 : y * t = t⁻¹ * y := by
        have := congrArg (fun q => q * y) h
        simpa [mul_assoc] using this
      have h2 : t * y * t = y := by
        have := congrArg (fun q => t * q) h1
        simpa [mul_assoc] using this
      calc t * y = (t * y * t) * t⁻¹ := by group
        _ = y * t⁻¹ := by rw [h2]
    have hty : toL t * toL y = toL y * toL t⁻¹ := by
      rw [← toL_mul, ← toL_mul, hgroup]
    have htinv : toL t⁻¹ w = w := by
      apply toL_injective t
      calc toL t (toL t⁻¹ w) = (toL t * toL t⁻¹) w := rfl
        _ = (toL (t * t⁻¹)) w := by rw [toL_mul]
        _ = w := by rw [mul_inv_cancel, toL_one, Module.End.one_apply]
        _ = toL t w := by rw [hw']
    rw [Module.End.mem_eigenspace_iff]
    calc toL t (toL y w) = (toL t * toL y) w := rfl
      _ = (toL y * toL t⁻¹) w := by rw [hty]
      _ = toL y (toL t⁻¹ w) := rfl
      _ = toL y w := by rw [htinv]
      _ = ((1 : K) • toL y w) := by rw [one_smul]

private theorem finrank_eigenspaces_of_conj_inv {ω : K}
    (hω : unitaryInvolution K 2 1 ω * ω = 1) (hω1 : ω ≠ 1)
    {tS sS : Su K 2 1 4} (ht3 : tS ^ 3 = 1) (ht1 : tS ≠ 1)
    (hs2 : sS * sS = 1) (hconj : sS * tS * sS⁻¹ = tS⁻¹)
    {v : Fin 4 → K} (hv : herm (unitaryInvolution K 2 1) v v = 1)
    (hvE : v ∈ Module.End.eigenspace (toL tS) 1) :
    Module.finrank K (Module.End.eigenspace (toL tS) 1) = 2 ∧
      Module.finrank K (Module.End.eigenspace (toL tS) ω) = 1 := by
  have hω3 : ω ^ 3 = 1 := omega_pow_three hω
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have hdim := finrank_eigenspaces_eq_four hω1 hω3 ht3
  set d1 : ℕ := Module.finrank K (Module.End.eigenspace (toL tS) 1)
  set dω : ℕ := Module.finrank K (Module.End.eigenspace (toL tS) ω)
  set dω2 : ℕ := Module.finrank K (Module.End.eigenspace (toL tS) (ω ^ 2))
  have hdim' : d1 + dω + dω2 = 4 := by simpa [d1, dω, dω2] using hdim
  have hωinv : ω⁻¹ = ω ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hω3])
  have hdωeq : dω = dω2 := by
    have h := finrank_eigenspace_eq_of_inv hconj hs2 (μ := ω) hω0
    rw [hωinv] at h
    simpa [dω, dω2] using h
  have htlin_ne : toL tS ≠ 1 := by
    intro h
    apply ht1
    apply toL_inj
    rw [h, toL_one]
  have hd1ne4 : d1 ≠ 4 := by
    intro h4
    apply htlin_ne
    apply LinearMap.ext
    intro y
    have h4' : Module.finrank K (Module.End.eigenspace (toL tS) 1) =
        Module.finrank K (Fin 4 → K) := by
      have h4fin : Module.finrank K (Module.End.eigenspace (toL tS) 1) = 4 := by
        simpa using h4
      rw [h4fin, Module.finrank_fintype_fun_eq_card]
      norm_num
    have hy : y ∈ Module.End.eigenspace (toL tS) 1 := by
      rw [Submodule.eq_top_of_finrank_eq h4']
      exact Submodule.mem_top
    simpa using Module.End.mem_eigenspace_iff.mp hy
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [herm_zero_left] at hv
    exact zero_ne_one hv
  have hE1ne : Module.End.eigenspace (toL tS) 1 ≠ ⊥ := by
    intro hbot
    have : v = 0 := by
      rw [hbot] at hvE
      simpa using hvE
    exact hv0 this
  have hd1pos : 0 < d1 := by
    have hpos : 0 < Module.finrank K (Module.End.eigenspace (toL tS) 1) := by
      rw [Module.finrank_pos_iff]
      exact Submodule.nontrivial_iff_ne_bot.mpr hE1ne
    simpa [d1] using hpos
  have hd1 : d1 = 2 := by omega
  have hdω1 : dω = 1 := by omega
  exact ⟨by simpa [d1] using hd1, by simpa [dω] using hdω1⟩

private theorem exists_eigenspace_inf_ker_eq_span {v : Fin 4 → K}
    (hv : herm (unitaryInvolution K 2 1) v v = 1)
    {E1 : Submodule K (Fin 4 → K)} (hE1 : Module.finrank K E1 = 2) (hvE : v ∈ E1) :
    ∃ x₀ : Fin 4 → K, x₀ ≠ 0 ∧ herm (unitaryInvolution K 2 1) v x₀ = 0 ∧
      x₀ ∈ E1 ∧ E1 ⊓ LinearMap.ker (hermL (unitaryInvolution K 2 1) v) = K ∙ x₀ := by
  let H : Submodule K (Fin 4 → K) := LinearMap.ker (hermL (unitaryInvolution K 2 1) v)
  have hHfin : Module.finrank K H = 3 := by
    have hne : hermL (unitaryInvolution K 2 1) v ≠ 0 := by
      intro h
      have h1 : herm (unitaryInvolution K 2 1) v v = 0 := by
        have := congrArg (fun f => f v) h
        simpa [hermL_apply] using this
      rw [hv] at h1
      exact zero_ne_one h1.symm
    have h :=
      Module.Dual.finrank_ker_add_one_of_ne_zero (f := hermL (unitaryInvolution K 2 1) v) hne
    rw [Module.finrank_fintype_fun_eq_card] at h
    have ha : Fintype.card (Fin 4) = 4 := by simp
    rw [ha] at h
    norm_num at h
    omega
  have hWpos : 0 < Module.finrank K ↥(E1 ⊓ H) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq E1 H
    have hle : Module.finrank K ↥(E1 ⊔ H) ≤ 4 := by
      have := Submodule.finrank_le (E1 ⊔ H)
      simpa [Module.finrank_fintype_fun_eq_card] using this
    have hE1' : Module.finrank K E1 = 2 := hE1
    have hH : Module.finrank K H = 3 := hHfin
    have h5 : Module.finrank K ↥(E1 ⊔ H) + Module.finrank K ↥(E1 ⊓ H) = 5 := by
      rw [h, hE1', hH]
    omega
  have hWne : E1 ⊓ H ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hWpos
    omega
  obtain ⟨x₀, hx₀mem, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  have hx₀E : x₀ ∈ E1 := (Submodule.mem_inf.mp hx₀mem).1
  have hx₀H : x₀ ∈ H := (Submodule.mem_inf.mp hx₀mem).2
  have hx₀perp : herm (unitaryInvolution K 2 1) v x₀ = 0 := by
    simpa [H, hermL_apply] using hx₀H
  have hWfin : Module.finrank K ↥(E1 ⊓ H) = 1 := by
    have hle : E1 ⊓ H ≤ E1 := inf_le_left
    have h2 : Module.finrank K ↥(E1 ⊓ H) ≤ 2 := by
      have := Submodule.finrank_mono hle
      have hE1' : Module.finrank K E1 = 2 := hE1
      omega
    have hpos : 0 < Module.finrank K ↥(E1 ⊓ H) := hWpos
    have hne : E1 ⊓ H ≠ E1 := by
      intro heq
      have hvH : v ∈ H := by
        have : v ∈ E1 ⊓ H := by rw [heq]; exact hvE
        exact (Submodule.mem_inf.mp this).2
      have h1 : herm (unitaryInvolution K 2 1) v v = 0 := by
        simpa [H, hermL_apply] using hvH
      rw [hv] at h1
      exact zero_ne_one h1.symm
    have hDne2 : Module.finrank K ↥(E1 ⊓ H) ≠ 2 := by
      intro hD
      apply hne
      have hE1' : Module.finrank K E1 = 2 := hE1
      exact Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hD, hE1'])
    omega
  have hline : E1 ⊓ H = K ∙ x₀ :=
    eq_span_singleton_of_mem_of_finrank_eq_one hWfin hx₀mem hx₀0
  exact ⟨x₀, hx₀0, hx₀perp, hx₀E, hline⟩

omit [Finite K] [CharP K 2] in
private theorem span_sup_span_eq_of_finrank_two {v x₀ : Fin 4 → K}
    {E1 : Submodule K (Fin 4 → K)} (hE1 : Module.finrank K E1 = 2)
    (hvE : v ∈ E1) (hx₀E : x₀ ∈ E1) (hv0 : v ≠ 0) (hx₀0 : x₀ ≠ 0)
    (hx₀not : x₀ ∉ K ∙ v) :
    (K ∙ v) ⊔ (K ∙ x₀) = E1 := by
  have hle : (K ∙ v) ⊔ (K ∙ x₀) ≤ E1 := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem]; exact hvE
    · rw [Submodule.span_singleton_le_iff_mem]; exact hx₀E
  have hdim : Module.finrank K ↥((K ∙ v) ⊔ (K ∙ x₀)) = 2 := by
    have hv1 : Module.finrank K ↥(K ∙ v) = 1 := finrank_span_singleton hv0
    have hx1 : Module.finrank K ↥(K ∙ x₀) = 1 := finrank_span_singleton hx₀0
    have hinf : (K ∙ v) ⊓ (K ∙ x₀) = ⊥ := by
      refine eq_bot_iff.mpr ?_
      intro z hz
      obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.mp hz
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz1
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hz2
      by_cases hb0 : b = 0
      · rw [hb0, zero_smul] at hb
        rw [← hb]
        exact Submodule.zero_mem _
      · exfalso
        apply hx₀not
        have hx0eq : x₀ = b⁻¹ • (a • v) := by
          rw [← hb, smul_smul, inv_mul_cancel₀ hb0, one_smul]
        rw [hx0eq]
        exact Submodule.smul_mem _ _ hz1
    have h := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ v) (K ∙ x₀)
    rw [hinf, finrank_bot, hv1, hx1] at h
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hdim, hE1])

private theorem herm_eq_zero_of_herm_self_eq_zero
    (hσ : IsUnitaryInvolution (unitaryInvolution K 2 1))
    {v x₀ : Fin 4 → K} (hx₀perp : herm (unitaryInvolution K 2 1) v x₀ = 0)
    {E1 : Submodule K (Fin 4 → K)} (hspan : (K ∙ v) ⊔ (K ∙ x₀) = E1) :
    herm (unitaryInvolution K 2 1) x₀ x₀ = 0 →
      ∀ y ∈ E1, herm (unitaryInvolution K 2 1) x₀ y = 0 := by
  intro h0 y hy
  rw [← hspan] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hb
  rw [herm_add_right, herm_smul_right, herm_smul_right,
    herm_eq_zero_comm (unitaryInvolution K 2 1) hσ.invol hx₀perp, h0, mul_zero, mul_zero,
    add_zero]

private theorem herm_self_ne_zero_of_eigenspace {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (hω2ne : ω ^ 2 ≠ 1) {tS : Su K 2 1 4} (ht3 : tS ^ 3 = 1)
    {x₀ : Fin 4 → K} (hx₀0 : x₀ ≠ 0)
    (hx₀eig : x₀ ∈ Module.End.eigenspace (toL tS) 1)
    (hx₀E1 : herm (unitaryInvolution K 2 1) x₀ x₀ = 0 →
      ∀ y ∈ Module.End.eigenspace (toL tS) 1,
        herm (unitaryInvolution K 2 1) x₀ y = 0) :
    herm (unitaryInvolution K 2 1) x₀ x₀ ≠ 0 := by
  intro h0
  apply hx₀0
  refine eq_zero_of_herm (unitaryInvolution K 2 1) fun y => ?_
  have htlin3 : toL tS ^ 3 = 1 := by rw [← toL_pow, ht3, toL_one]
  obtain ⟨y0, y1, y2, hy0, hy1, hy2, ht0, ht1, ht2, hsum⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310u.exists_eigen_decomp
      three_ne_zero hω1 hω3 htlin3 (U := ⊤) (fun _ _ => Submodule.mem_top)
      (u := y) (Submodule.mem_top)
  have h1 : herm (unitaryInvolution K 2 1) x₀ y1 = 0 := by
    have hmem : y1 ∈ Module.End.eigenspace (toL tS) ω :=
      Module.End.mem_eigenspace_iff.mpr ht1
    have hz : tS • y1 = ω • y1 := by
      simpa [toL_smul] using Module.End.mem_eigenspace_iff.mp hmem
    have hfix : tS • x₀ = x₀ := by
      simpa [toL_smul] using Module.End.mem_eigenspace_iff.mp hx₀eig
    have h := herm_smul_smul (unitaryInvolution K 2 1) tS x₀ y1
    rw [hfix, hz, herm_smul_right] at h
    have h2 : (ω - 1) * herm (unitaryInvolution K 2 1) x₀ y1 = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hω1)
  have h2 : herm (unitaryInvolution K 2 1) x₀ y2 = 0 := by
    have hmem : y2 ∈ Module.End.eigenspace (toL tS) (ω ^ 2) :=
      Module.End.mem_eigenspace_iff.mpr ht2
    have hz : tS • y2 = ω ^ 2 • y2 := by
      simpa [toL_smul] using Module.End.mem_eigenspace_iff.mp hmem
    have hfix : tS • x₀ = x₀ := by
      simpa [toL_smul] using Module.End.mem_eigenspace_iff.mp hx₀eig
    have h := herm_smul_smul (unitaryInvolution K 2 1) tS x₀ y2
    rw [hfix, hz, herm_smul_right] at h
    have h3 : (ω ^ 2 - 1) * herm (unitaryInvolution K 2 1) x₀ y2 = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hω2ne)
  have h0' : herm (unitaryInvolution K 2 1) x₀ y0 = 0 := by
    have hy0' : y0 ∈ Module.End.eigenspace (toL tS) 1 :=
      Module.End.mem_eigenspace_iff.mpr (by simpa using ht0)
    exact hx₀E1 h0 y0 hy0'
  rw [← hsum, herm_add_right, herm_add_right, h0', h1, h2, add_zero, add_zero]

private theorem pair_commutes_or_inv (hK : Nat.card K = 4)
    {X : Subgroup (Su K 2 1 4)} (e : Su K 2 1 2 ≃* X) {t : X}
    (ht3X : t ^ 3 = 1) (ht1X : t ≠ 1) :
    ∀ y : X, y * t * y⁻¹ = t ∨ y * t * y⁻¹ = t⁻¹ := by
  intro y
  have ht_order : orderOf t = 3 := orderOf_eq_prime ht3X ht1X
  have hKcard : Nat.card (Subgroup.zpowers t) = 3 := by
    rw [Nat.card_zpowers, ht_order]
  have hXcard : Nat.card X = 6 := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.StandardType.QTwo.qTwoS34_card_Su_two hK
  have hIndex : (Subgroup.zpowers t).index = 2 := by
    rw [Subgroup.index_eq_card_div, hKcard, hXcard]
  have hNormal : (Subgroup.zpowers t).Normal := Subgroup.normal_of_index_eq_two hIndex
  exact conj_eq_self_or_inv_of_mem_zpowers ht3X ht1X
    (hNormal.conj_mem t (Subgroup.mem_zpowers t) y)

private theorem le_fixSU_pair_of_eigenspace_inf_ker (hK : Nat.card K = 4)
    {X : Subgroup (Su K 2 1 4)} (e : Su K 2 1 2 ≃* X) {t : X}
    (ht3X : t ^ 3 = 1) (ht1X : t ≠ 1) {tS : Su K 2 1 4}
    (htS : tS = (t : Su K 2 1 4)) {v x₀ : Fin 4 → K}
    (hx₀perp : herm (unitaryInvolution K 2 1) v x₀ = 0) (hx₀0 : x₀ ≠ 0)
    (hline : Module.End.eigenspace (toL tS) 1 ⊓
      LinearMap.ker (hermL (unitaryInvolution K 2 1) v) = K ∙ x₀)
    (hx₀eig : x₀ ∈ Module.End.eigenspace (toL tS) 1) (hX : X ≤ fixSU {v}) :
    X ≤ fixSU {v, x₀} := by
  have hconj_or_inv := pair_commutes_or_inv hK e ht3X ht1X
  have hpres : ∀ y : X, ∃ d : K, d ≠ 0 ∧ (y : Su K 2 1 4) • x₀ = d • x₀ := by
    intro y
    have hconjS : (y : Su K 2 1 4) * tS * (y : Su K 2 1 4)⁻¹ = tS ∨
        (y : Su K 2 1 4) * tS * (y : Su K 2 1 4)⁻¹ = tS⁻¹ := by
      rcases hconj_or_inv y with h | h
      · left
        simpa [htS] using congrArg (fun q : X => (q : Su K 2 1 4)) h
      · right
        simpa [htS] using congrArg (fun q : X => (q : Su K 2 1 4)) h
    have hmemE : (y : Su K 2 1 4) • x₀ ∈
        Module.End.eigenspace (toL tS) 1 := eigenspace_one_map_of_conj hconjS x₀ hx₀eig
    have hmemH : (y : Su K 2 1 4) • x₀ ∈
        LinearMap.ker (hermL (unitaryInvolution K 2 1) v) := by
      have hyv : (y : Su K 2 1 4) • v = v := by
        have := hX y.2
        simpa [fixSU, MulAction.mem_stabilizer_iff] using this
      have h := herm_smul_smul (unitaryInvolution K 2 1) (y : Su K 2 1 4) v x₀
      rw [hyv, hx₀perp] at h
      simpa [hermL_apply] using h
    have hmem : (y : Su K 2 1 4) • x₀ ∈ K ∙ x₀ := by
      rw [← hline]
      exact Submodule.mem_inf.mpr ⟨hmemE, hmemH⟩
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hmem
    refine ⟨d, ?_, hd.symm⟩
    rintro rfl
    rw [zero_smul] at hd
    have h := congrArg (fun z => (y : Su K 2 1 4)⁻¹ • z) hd
    simp only [inv_smul_smul, inv_smul_smul] at h
    exact hx₀0 (by simpa using h.symm)
  choose d hd0 hd using hpres
  have hmul : ∀ g h : X, d (g * h) = d g * d h := by
    intro g h
    have h2 : d (g * h) • x₀ = (d g * d h) • x₀ := by
      rw [← hd (g * h)]
      calc ((g * h : X) : Su K 2 1 4) • x₀ =
            ((g : Su K 2 1 4) * (h : Su K 2 1 4)) • x₀ := rfl
        _ = (g : Su K 2 1 4) • ((h : Su K 2 1 4) • x₀) := mul_smul _ _ _
        _ = (g : Su K 2 1 4) • (d h • x₀) := by rw [hd h]
        _ = d h • ((g : Su K 2 1 4) • x₀) := smul_smul_vector _ _ _
        _ = d h • (d g • x₀) := by rw [hd g]
        _ = (d h * d g) • x₀ := by rw [smul_smul]
        _ = (d g * d h) • x₀ := by rw [mul_comm]
    exact (smul_left_inj hx₀0).mp h2
  let χ : X →* Kˣ :=
    MonoidHom.mk' (fun g => Units.mk0 (d g) (hd0 g)) (by
      intro g h
      apply Units.ext
      exact hmul g h)
  have hχe : χ.comp e.toMonoidHom = 1 :=
    eq_one_of_hom_Su_two hK (χ.comp e.toMonoidHom) (units_pow_three hK)
  have hchi : ∀ g : X, χ g = 1 := by
    intro g
    obtain ⟨h, rfl⟩ := e.surjective g
    have := congrArg (fun f : Su K 2 1 2 →* Kˣ => f h) hχe
    simpa [MonoidHom.comp_apply] using this
  intro g hg
  let gX : X := ⟨g, hg⟩
  have h1 : d gX = 1 := by
    have := congrArg Units.val (hchi gX)
    simpa [χ] using this
  have h3 : (gX : Su K 2 1 4) • x₀ = x₀ := by rw [hd gX, h1, one_smul]
  have h4 : (gX : Su K 2 1 4) • v = v := by
    have := hX hg
    simpa [fixSU, MulAction.mem_stabilizer_iff] using this
  simp only [fixSU, Subgroup.mem_iInf, Set.mem_insert_iff, Set.mem_singleton_iff,
    MulAction.mem_stabilizer_iff]
  intro z hz
  rcases hz with rfl | rfl
  · exact h4
  · exact h3

private theorem exists_eq_fixSU_pair_of_le (hK : Nat.card K = 4) {v x₀ : Fin 4 → K}
    (hv : herm (unitaryInvolution K 2 1) v v = 1)
    (hx₀perp : herm (unitaryInvolution K 2 1) v x₀ = 0)
    (hx₀self : herm (unitaryInvolution K 2 1) x₀ x₀ ≠ 0)
    {X : Subgroup (Su K 2 1 4)} (e : Su K 2 1 2 ≃* X)
    (hXle : X ≤ fixSU {v, x₀}) :
    ∃ x : Fin 4 → K, herm (unitaryInvolution K 2 1) x x = 1 ∧
      herm (unitaryInvolution K 2 1) v x = 0 ∧ X = fixSU {v, x} := by
  obtain ⟨c, hc⟩ := exists_smul_norm_one
    (isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) (by rw [hK]; norm_num)) hx₀self
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, herm_zero_left] at hc
    exact zero_ne_one hc
  let x' := c • x₀
  have hx' : herm (unitaryInvolution K 2 1) x' x' = 1 := hc
  have hvx' : herm (unitaryInvolution K 2 1) v x' = 0 := by
    rw [herm_smul_right, hx₀perp, mul_zero]
  have hfixpair : fixSU {v, x'} = fixSU {v, x₀} := by
    have := fixSU_smul_pair (a := 1) (b := c) (by norm_num) hc0 v x₀
    simpa [x'] using this
  have hXle' : X ≤ fixSU {v, x'} := by
    rw [hfixpair]
    exact hXle
  have hcardX : Nat.card X = 6 := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.StandardType.QTwo.qTwoS34_card_Su_two hK
  have hcardF : Nat.card (fixSU {v, x'}) = 6 := card_fixSU_pair hK hv hx' hvx'
  refine ⟨x', hx', hvx', Subgroup.eq_of_le_of_card_ge hXle' ?_⟩
  rw [hcardF, hcardX]

theorem eq_fixSU_pair (hK : Nat.card K = 4) {v : Fin 4 → K}
    (hv : herm (unitaryInvolution K 2 1) v v = 1)
    {X : Subgroup (Su K 2 1 4)} (e : Su K 2 1 2 ≃* X) (hX : X ≤ fixSU {v}) :
    ∃ x : Fin 4 → K, herm (unitaryInvolution K 2 1) x x = 1 ∧
      herm (unitaryInvolution K 2 1) v x = 0 ∧ X = fixSU {v, x} := by
  have hσ : IsUnitaryInvolution (unitaryInvolution K 2 1) :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) (by rw [hK]; norm_num)
  obtain ⟨ω, hω, hω1⟩ := hσ.exists_norm_one_ne_one
  have hω3 : ω ^ 3 = 1 := omega_pow_three hω
  have hω2ne : ω ^ 2 ≠ 1 := by
    intro h
    have h2 : orderOf ω ∣ 2 := orderOf_dvd_of_pow_eq_one h
    have h3 : orderOf ω ∣ 3 := orderOf_dvd_of_pow_eq_one hω3
    have h1 : orderOf ω = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num) h2 h3
    rw [orderOf_eq_one_iff] at h1
    exact hω1 h1
  let t : X := e (t0Elt hω)
  let s : X := e s0Elt
  have ht3X : t ^ 3 = 1 := by
    change (e (t0Elt hω)) ^ 3 = 1
    rw [← map_pow, t0Elt_pow_three hω, map_one]
  have ht1X : t ≠ 1 := by
    intro h
    apply t0Elt_ne_one hω hω1
    apply e.injective
    rw [map_one]
    exact h
  have hs2X : s * s = 1 := by
    change e s0Elt * e s0Elt = 1
    rw [← map_mul, s0Elt_sq, map_one]
  have hconjX : s * t * s⁻¹ = t⁻¹ := by
    change e s0Elt * e (t0Elt hω) * (e s0Elt)⁻¹ = (e (t0Elt hω))⁻¹
    rw [← map_mul, ← map_inv, ← map_mul, s0Elt_conj_t0Elt hω, map_inv]
  let tS : Su K 2 1 4 := t
  let sS : Su K 2 1 4 := s
  have ht3 : tS ^ 3 = 1 := by
    have := congrArg (fun q : X => (q : Su K 2 1 4)) ht3X
    simpa [tS] using this
  have ht1 : tS ≠ 1 := by
    intro h
    apply ht1X
    apply Subtype.ext
    exact h
  have hs2 : sS * sS = 1 := by
    have := congrArg (fun q : X => (q : Su K 2 1 4)) hs2X
    simpa [sS] using this
  have hconj : sS * tS * sS⁻¹ = tS⁻¹ := by
    have := congrArg (fun q : X => (q : Su K 2 1 4)) hconjX
    simpa [tS, sS] using this
  have htX : (t : Su K 2 1 4) ∈ X := t.property
  have htv : tS • v = v := by
    have := hX htX
    simpa [fixSU, MulAction.mem_stabilizer_iff, tS] using this
  have hvE : v ∈ Module.End.eigenspace (toL tS) 1 := by
    rw [Module.End.mem_eigenspace_iff]
    simpa [toL_smul] using htv
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [herm_zero_left] at hv
    exact zero_ne_one hv
  obtain ⟨hE1, _hEω⟩ := finrank_eigenspaces_of_conj_inv hω hω1 ht3 ht1 hs2 hconj hv hvE
  obtain ⟨x₀, hx₀0, hx₀perp, hx₀E, hline⟩ := exists_eigenspace_inf_ker_eq_span hv hE1 hvE
  have hx₀not : x₀ ∉ K ∙ v := by
    intro hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hmem
    have hc : c = 0 := by
      have h := hx₀perp
      rw [herm_smul_right, hv, mul_one] at h
      exact h
    exact hx₀0 (by rw [hc, zero_smul])
  have hspan : (K ∙ v) ⊔ (K ∙ x₀) = Module.End.eigenspace (toL tS) 1 :=
    span_sup_span_eq_of_finrank_two hE1 hvE hx₀E hv0 hx₀0 hx₀not
  have hx₀E1 : herm (unitaryInvolution K 2 1) x₀ x₀ = 0 →
      ∀ y ∈ Module.End.eigenspace (toL tS) 1, herm (unitaryInvolution K 2 1) x₀ y = 0 :=
    herm_eq_zero_of_herm_self_eq_zero hσ hx₀perp hspan
  have hx₀self : herm (unitaryInvolution K 2 1) x₀ x₀ ≠ 0 :=
    herm_self_ne_zero_of_eigenspace hω1 hω3 hω2ne ht3 hx₀0 hx₀E hx₀E1
  have hXle : X ≤ fixSU {v, x₀} :=
    le_fixSU_pair_of_eigenspace_inf_ker hK e ht3X ht1X (tS := tS) rfl hx₀perp hx₀0 hline hx₀E hX
  exact exists_eq_fixSU_pair_of_le hK hv hx₀perp hx₀self e hXle

private noncomputable def d4Diag {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    Fin 4 → normOne (unitaryInvolution K 2 1) :=
  fun i => if i = 0 then omegaUnit hω else if i = 1 then omegaUnit hω ^ 2 else 1

private theorem d4Diag_zero {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    d4Diag hω 0 = omegaUnit hω := by simp [d4Diag]

private theorem d4Diag_one {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    d4Diag hω 1 = omegaUnit hω ^ 2 := by simp [d4Diag]

private theorem d4Diag_two {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    d4Diag hω 2 = 1 := by simp [d4Diag]

private theorem d4Diag_three {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    d4Diag hω 3 = 1 := by simp [d4Diag]

private theorem d4Diag_mem_detKer {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    d4Diag hω ∈ detKer (unitaryInvolution K 2 1) 4 := by
  rw [mem_detKer, Fin.prod_univ_four, d4Diag_zero, d4Diag_one, d4Diag_two, d4Diag_three]
  rw [mul_one, mul_one, ← pow_succ']
  exact omegaUnit_pow_three hω

private noncomputable def d4Elt {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    Su K 2 1 4 :=
  diagSU (unitaryInvolution K 2 1) (d4Diag hω) (d4Diag_mem_detKer hω)

private theorem d4Elt_smul {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1)
    (k : Fin 4) :
    d4Elt hω • (Pi.single k (1 : K) : Fin 4 → K) =
      ((d4Diag hω k : normOne (unitaryInvolution K 2 1)) : Kˣ).val •
        (Pi.single k (1 : K) : Fin 4 → K) := by
  rw [d4Elt, smul_single_diagSU]

private theorem d4Elt_smul_zero {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    d4Elt hω • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) =
      ω • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) := by
  rw [d4Elt_smul, d4Diag_zero, coe_omegaUnit]

private theorem d4Elt_smul_one {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    d4Elt hω • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) =
      ω ^ 2 • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) := by
  rw [d4Elt_smul, d4Diag_one]
  simp [coe_omegaUnit]

private theorem d4Elt_smul_two {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    d4Elt hω • (Pi.single (2 : Fin 4) (1 : K) : Fin 4 → K) =
      (Pi.single (2 : Fin 4) (1 : K) : Fin 4 → K) := by
  rw [d4Elt_smul, d4Diag_two]
  simp

private theorem d4Elt_smul_three {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1) :
    d4Elt hω • (Pi.single (3 : Fin 4) (1 : K) : Fin 4 → K) =
      (Pi.single (3 : Fin 4) (1 : K) : Fin 4 → K) := by
  rw [d4Elt_smul, d4Diag_three]
  simp

private noncomputable def p4Elt : Su K 2 1 4 :=
  mkSU (unitaryInvolution K 2 1) ((Equiv.swap (0 : Fin 4) 1).permMatrix K)
    (by
      rw [Matrix.det_permutation, Equiv.Perm.sign_swap (by norm_num : (0 : Fin 4) ≠ 1)]
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      linear_combination -h2)
    (by
      have hmap : ((Equiv.swap (0 : Fin 4) 1).permMatrix K).map (unitaryInvolution K 2 1) =
          (Equiv.swap (0 : Fin 4) 1).permMatrix K := by
        ext i j
        simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
          Equiv.toPEquiv_apply]
        split_ifs <;> simp
      intro x y
      rw [herm_mulVec, conjTr, hmap, Matrix.transpose_permMatrix, Equiv.swap_inv,
        ← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one,
        Matrix.one_mulVec])

private theorem p4Elt_smul_zero :
    (p4Elt (K := K)) • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) =
      (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) := by
  rw [p4Elt, mkSU_smul, Matrix.permMatrix_mulVec]
  funext i
  fin_cases i <;> simp [Equiv.swap_apply_def]

private theorem p4Elt_smul_one :
    (p4Elt (K := K)) • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) =
      (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) := by
  rw [p4Elt, mkSU_smul, Matrix.permMatrix_mulVec]
  funext i
  fin_cases i <;> simp [Equiv.swap_apply_def]

private theorem p4Elt_smul_two :
    (p4Elt (K := K)) • (Pi.single (2 : Fin 4) (1 : K) : Fin 4 → K) =
      (Pi.single (2 : Fin 4) (1 : K) : Fin 4 → K) := by
  rw [p4Elt, mkSU_smul, Matrix.permMatrix_mulVec]
  funext i
  fin_cases i <;> simp [Equiv.swap_apply_def]

private theorem p4Elt_smul_three :
    (p4Elt (K := K)) • (Pi.single (3 : Fin 4) (1 : K) : Fin 4 → K) =
      (Pi.single (3 : Fin 4) (1 : K) : Fin 4 → K) := by
  rw [p4Elt, mkSU_smul, Matrix.permMatrix_mulVec]
  funext i
  fin_cases i <;> simp [Equiv.swap_apply_def]


private theorem eq_smul_single_of_diagSU_smul {d : Fin 4 → normOne (unitaryInvolution K 2 1)}
    (hd : d ∈ detKer (unitaryInvolution K 2 1) 4) {μ : K} (k : Fin 4)
    (h : ∀ i, i ≠ k → (((d i : normOne (unitaryInvolution K 2 1)) : Kˣ).val) ≠ μ)
    {y : Fin 4 → K} (hy : diagSU (unitaryInvolution K 2 1) d hd • y = μ • y) :
    y = y k • (Pi.single k (1 : K) : Fin 4 → K) := by
  funext i
  by_cases hik : i = k
  · subst i; simp
  · have hi : y i = 0 := by
      have hc := congrFun hy i
      rw [diagSU_smul] at hc
      simp only [Pi.smul_apply, smul_eq_mul] at hc
      have h' : ((((d i : normOne (unitaryInvolution K 2 1)) : Kˣ).val) - μ) * y i = 0 := by
        rw [sub_mul, sub_eq_zero]
        exact hc
      exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (h i hik))
    simp [hik, hi]

private theorem d4Elt_line_zero {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1)
    (hω1 : ω ≠ 1) {y : Fin 4 → K} (hy : d4Elt hω • y = ω • y) :
    y = y 0 • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) := by
  have hω2ne : ω ^ 2 ≠ ω := by
    intro h
    have h2 : ω ^ 2 = ω * ω := by rw [pow_two]
    rw [h2] at h
    have : ω * ω = ω * 1 := by rw [h, mul_one]
    exact hω1 (mul_left_cancel₀ (by rintro rfl; norm_num at hω) this)
  change diagSU (unitaryInvolution K 2 1) (d4Diag hω) (d4Diag_mem_detKer hω) • y = ω • y at hy
  refine eq_smul_single_of_diagSU_smul (d4Diag_mem_detKer hω) (0 : Fin 4) ?_ hy
  intro i hi
  fin_cases i
  · exact absurd rfl hi
  · change (((d4Diag hω 1 : normOne (unitaryInvolution K 2 1)) : Kˣ).val) ≠ ω
    rw [d4Diag_one]
    change ((omegaUnit hω ^ 2 : Kˣ).val) ≠ ω
    rw [Units.val_pow_eq_pow_val, coe_omegaUnit]
    exact hω2ne
  · change (((d4Diag hω 2 : normOne (unitaryInvolution K 2 1)) : Kˣ).val) ≠ ω
    rw [d4Diag_two]; exact fun h => hω1 h.symm
  · change (((d4Diag hω 3 : normOne (unitaryInvolution K 2 1)) : Kˣ).val) ≠ ω
    rw [d4Diag_three]; exact fun h => hω1 h.symm

private theorem d4Elt_line_one {ω : K} (hω : unitaryInvolution K 2 1 ω * ω = 1)
    (hω1 : ω ≠ 1) {y : Fin 4 → K} (hy : d4Elt hω • y = ω ^ 2 • y) :
    y = y 1 • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) := by
  have hω3 : ω ^ 3 = 1 := omega_pow_three hω
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0] at hω3
    norm_num at hω3
  have hω2ne : ω ^ 2 ≠ ω := by
    intro h
    have h2 : ω ^ 2 = ω * ω := by rw [pow_two]
    rw [h2] at h
    have : ω * ω = ω * 1 := by rw [h, mul_one]
    exact hω1 (mul_left_cancel₀ hω0 this)
  have hω2ne1 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω1
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by
          field_simp [hω0]
      _ = 1 * 1⁻¹ := by rw [hω3, h]
      _ = 1 := by norm_num
  change diagSU (unitaryInvolution K 2 1) (d4Diag hω) (d4Diag_mem_detKer hω) • y = ω ^ 2 • y at hy
  refine eq_smul_single_of_diagSU_smul (d4Diag_mem_detKer hω) (1 : Fin 4) ?_ hy
  intro i hi
  fin_cases i
  · change (((d4Diag hω 0 : normOne (unitaryInvolution K 2 1)) : Kˣ).val) ≠ ω ^ 2
    rw [d4Diag_zero, coe_omegaUnit]
    exact fun h => hω2ne h.symm
  · exact absurd rfl hi
  · change (((d4Diag hω 2 : normOne (unitaryInvolution K 2 1)) : Kˣ).val) ≠ ω ^ 2
    rw [d4Diag_two]
    exact fun h => hω2ne1 h.symm
  · change (((d4Diag hω 3 : normOne (unitaryInvolution K 2 1)) : Kˣ).val) ≠ ω ^ 2
    rw [d4Diag_three]
    exact fun h => hω2ne1 h.symm

private theorem exists_smul_single_zero_of_commute {ω : K}
    (hω : unitaryInvolution K 2 1 ω * ω = 1) (hω1 : ω ≠ 1)
    {X : Subgroup (Su K 2 1 4)}
    (hX : ∀ x ∈ X, ∀ y ∈ fixSU {(Pi.single (2 : Fin 4) (1 : K) : Fin 4 → K),
      (Pi.single (3 : Fin 4) (1 : K) : Fin 4 → K)}, x * y = y * x)
    (hd4 : d4Elt hω ∈ fixSU {(Pi.single (2 : Fin 4) (1 : K) : Fin 4 → K),
      (Pi.single (3 : Fin 4) (1 : K) : Fin 4 → K)}) :
    ∃ α : X → K, (∀ x, α x ≠ 0) ∧
      ∀ x : X, (x : Su K 2 1 4) • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) =
        α x • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) := by
  have hu0 : (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) ≠ 0 := by
    intro h; have := congrFun h 0; simp at this
  have hline0 : ∀ x : X, ∃ α : K, α ≠ 0 ∧
      (x : Su K 2 1 4) • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) =
        α • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) := by
    intro x
    have hcomm := hX x x.2 (d4Elt hω) hd4
    have hy : d4Elt hω • ((x : Su K 2 1 4) •
        (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K)) =
        ω • ((x : Su K 2 1 4) • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K)) := by
      calc d4Elt hω • ((x : Su K 2 1 4) •
            (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K)) =
            (d4Elt hω * (x : Su K 2 1 4)) •
              (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) := by rw [mul_smul]
        _ = ((x : Su K 2 1 4) * d4Elt hω) •
              (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) := by rw [← hcomm]
        _ = (x : Su K 2 1 4) • (d4Elt hω •
              (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K)) := by rw [mul_smul]
        _ = (x : Su K 2 1 4) •
              (ω • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K)) := by rw [d4Elt_smul_zero]
        _ = ω • ((x : Su K 2 1 4) •
              (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K)) := by rw [smul_smul_vector]
    have hline := d4Elt_line_zero hω hω1 hy
    refine ⟨((x : Su K 2 1 4) •
      (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K)) 0, ?_, hline⟩
    intro hα
    have hzero : (x : Su K 2 1 4) •
        (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) = 0 := by
      rw [hline, hα, zero_smul]
    have h := congrArg (fun z => (x : Su K 2 1 4)⁻¹ • z) hzero
    simp at h
  choose α hα0 hα using hline0
  exact ⟨α, hα0, hα⟩

private theorem le_fixSU_std_of_commute (hK : Nat.card K = 4)
    {X : Subgroup (Su K 2 1 4)} (e : Su K 2 1 2 ≃* X) {α : X → K}
    (hα0 : ∀ x : X, α x ≠ 0)
    (hα : ∀ x : X, (x : Su K 2 1 4) • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) =
      α x • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K))
    (hX : ∀ x ∈ X, ∀ y ∈ fixSU {(Pi.single (2 : Fin 4) (1 : K) : Fin 4 → K),
      (Pi.single (3 : Fin 4) (1 : K) : Fin 4 → K)}, x * y = y * x)
    (hp4 : p4Elt ∈ fixSU {(Pi.single (2 : Fin 4) (1 : K) : Fin 4 → K),
      (Pi.single (3 : Fin 4) (1 : K) : Fin 4 → K)}) :
    X ≤ fixSU {(Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K),
      (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K)} := by
  have hu0 : (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) ≠ 0 := by
    intro h; have := congrFun h 0; simp at this
  have hmul : ∀ x y : X, α (x * y) = α x * α y := by
    intro x y
    have h2 : α (x * y) •
        (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) =
        (α x * α y) • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) := by
      rw [← hα (x * y)]
      calc ((x * y : X) : Su K 2 1 4) •
            (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) =
            ((x : Su K 2 1 4) * (y : Su K 2 1 4)) •
              (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) := rfl
        _ = (x : Su K 2 1 4) • ((y : Su K 2 1 4) •
              (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K)) := by rw [mul_smul]
        _ = (x : Su K 2 1 4) •
              (α y • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K)) := by rw [hα y]
        _ = α y • ((x : Su K 2 1 4) •
              (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K)) := by rw [smul_smul_vector]
        _ = α y • (α x • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K)) := by rw [hα x]
        _ = (α y * α x) • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) := by rw [smul_smul]
        _ = (α x * α y) • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) := by rw [mul_comm]
    exact (smul_left_inj hu0).mp h2
  let χ : X →* Kˣ :=
    MonoidHom.mk' (fun x => Units.mk0 (α x) (hα0 x)) (by
      intro x y
      apply Units.ext
      exact hmul x y)
  have hχe : χ.comp e.toMonoidHom = 1 :=
    eq_one_of_hom_Su_two hK (χ.comp e.toMonoidHom) (units_pow_three hK)
  have hχ : ∀ x : X, χ x = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    have := congrArg (fun f : Su K 2 1 2 →* Kˣ => f y) hχe
    simpa [MonoidHom.comp_apply] using this
  have hfix0 : ∀ x : X,
      (x : Su K 2 1 4) • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) =
        (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) := by
    intro x
    have h1 : α x = 1 := by
      have := congrArg Units.val (hχ x)
      simpa [χ] using this
    rw [hα x, h1, one_smul]
  have hfix1 : ∀ x : X,
      (x : Su K 2 1 4) • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) =
        (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) := by
    intro x
    have hcomm := hX x x.2 p4Elt hp4
    calc (x : Su K 2 1 4) • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) =
          (x : Su K 2 1 4) • (p4Elt •
            (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K)) := by rw [p4Elt_smul_zero]
      _ = ((x : Su K 2 1 4) * p4Elt) •
            (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) := by rw [mul_smul]
      _ = (p4Elt * (x : Su K 2 1 4)) •
            (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) := by rw [hcomm]
      _ = p4Elt • ((x : Su K 2 1 4) •
            (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K)) := by rw [mul_smul]
      _ = p4Elt • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) := by rw [hfix0]
      _ = (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) := p4Elt_smul_zero
  intro g hg
  let gX : X := ⟨g, hg⟩
  simp only [fixSU, Subgroup.mem_iInf, Set.mem_insert_iff, Set.mem_singleton_iff,
    MulAction.mem_stabilizer_iff]
  intro z hz
  rcases hz with rfl | rfl
  · exact hfix0 gX
  · exact hfix1 gX

private theorem eq_fixSU_std (hK : Nat.card K = 4) {X : Subgroup (Su K 2 1 4)}
    (e : Su K 2 1 2 ≃* X)
    (hX : ∀ x ∈ X, ∀ y ∈ fixSU {(Pi.single (2 : Fin 4) (1 : K) : Fin 4 → K),
      (Pi.single (3 : Fin 4) (1 : K) : Fin 4 → K)}, x * y = y * x) :
    X = fixSU {(Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K),
      (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K)} := by
  have hσ : IsUnitaryInvolution (unitaryInvolution K 2 1) :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) (by rw [hK]; norm_num)
  obtain ⟨ω, hω, hω1⟩ := hσ.exists_norm_one_ne_one
  have hω3 : ω ^ 3 = 1 := omega_pow_three hω
  let u0 : Fin 4 → K := Pi.single (0 : Fin 4) (1 : K)
  let u1 : Fin 4 → K := Pi.single (1 : Fin 4) (1 : K)
  let u2 : Fin 4 → K := Pi.single (2 : Fin 4) (1 : K)
  let u3 : Fin 4 → K := Pi.single (3 : Fin 4) (1 : K)
  have hu0 : u0 ≠ 0 := by
    intro h; have := congrFun h 0; simp [u0] at this
  have hu1 : u1 ≠ 0 := by
    intro h; have := congrFun h 1; simp [u1] at this
  have hd4 : d4Elt hω ∈ fixSU {u2, u3} := by
    simp only [fixSU, Subgroup.mem_iInf, Set.mem_insert_iff, Set.mem_singleton_iff,
      MulAction.mem_stabilizer_iff]
    intro z hz
    rcases hz with rfl | rfl
    · exact d4Elt_smul_two hω
    · exact d4Elt_smul_three hω
  have hp4 : p4Elt ∈ fixSU {u2, u3} := by
    simp only [fixSU, Subgroup.mem_iInf, Set.mem_insert_iff, Set.mem_singleton_iff,
      MulAction.mem_stabilizer_iff]
    intro z hz
    rcases hz with rfl | rfl
    · exact p4Elt_smul_two
    · exact p4Elt_smul_three
  obtain ⟨α, hα0, hα⟩ := exists_smul_single_zero_of_commute hω hω1 hX hd4
  have hle : X ≤ fixSU {u0, u1} :=
    le_fixSU_std_of_commute hK e hα0 hα hX hp4
  have hcardX : Nat.card X = 6 := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.StandardType.QTwo.qTwoS34_card_Su_two hK
  have hv0 : herm (unitaryInvolution K 2 1) u0 u0 = 1 := by
    rw [herm, Fin.sum_univ_four]
    simp [u0]
  have hv1 : herm (unitaryInvolution K 2 1) u1 u1 = 1 := by
    rw [herm, Fin.sum_univ_four]
    simp [u1]
  have hv01 : herm (unitaryInvolution K 2 1) u0 u1 = 0 := by
    rw [herm, Fin.sum_univ_four]
    simp [u0, u1]
  have hcardF : Nat.card (fixSU {u0, u1}) = 6 := card_fixSU_pair hK hv0 hv1 hv01
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcardF, hcardX]

private theorem map_conj_fixSU_std_pair (hK : Nat.card K = 4) {v : Fin 4 → Fin 4 → K}
    (hon : ∀ j k, herm (unitaryInvolution K 2 1) (v j) (v k) = if j = k then 1 else 0)
    {g : Su K 2 1 4} {a : Fin 4 → K} (ha : ∀ k, a k ≠ 0)
    (hG : ∀ k, g • (Pi.single k (1 : K) : Fin 4 → K) = a k • v k)
    (hg_inv : ∀ k, g⁻¹ • v k = (a k)⁻¹ • (Pi.single k (1 : K) : Fin 4 → K)) :
    (fixSU {(Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K),
      (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K)}).map
        (MulAut.conj g : Su K 2 1 4 →* Su K 2 1 4) = fixSU {v 0, v 1} := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    simp only [fixSU, Subgroup.mem_iInf, Set.mem_insert_iff, Set.mem_singleton_iff,
      MulAction.mem_stabilizer_iff] at hy ⊢
    intro w hw
    rcases hw with rfl | rfl
    · change (g * y * g⁻¹) • v 0 = v 0
      calc (g * y * g⁻¹) • v 0 = g • (y • (g⁻¹ • v 0)) := by simp [mul_smul]
        _ = g • (y • ((a 0)⁻¹ • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K))) := by
              rw [hg_inv]
        _ = g • ((a 0)⁻¹ • (y • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K))) := by
              rw [smul_smul_vector]
        _ = g • ((a 0)⁻¹ • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K)) := by
              rw [hy (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) (by simp)]
        _ = (a 0)⁻¹ • (g • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K)) := by
              rw [smul_smul_vector]
        _ = (a 0)⁻¹ • (a 0 • v 0) := by rw [hG]
        _ = v 0 := by rw [smul_smul, inv_mul_cancel₀ (ha 0), one_smul]
    · change (g * y * g⁻¹) • v 1 = v 1
      calc (g * y * g⁻¹) • v 1 = g • (y • (g⁻¹ • v 1)) := by simp [mul_smul]
        _ = g • (y • ((a 1)⁻¹ • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K))) := by
              rw [hg_inv]
        _ = g • ((a 1)⁻¹ • (y • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K))) := by
              rw [smul_smul_vector]
        _ = g • ((a 1)⁻¹ • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K)) := by
              rw [hy (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) (by simp)]
        _ = (a 1)⁻¹ • (g • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K)) := by
              rw [smul_smul_vector]
        _ = (a 1)⁻¹ • (a 1 • v 1) := by rw [hG]
        _ = v 1 := by rw [smul_smul, inv_mul_cancel₀ (ha 1), one_smul]
  · rw [Subgroup.card_map_of_injective
      (MulEquiv.injective (MulAut.conj g : Su K 2 1 4 ≃* Su K 2 1 4))]
    let u0 : Fin 4 → K := Pi.single (0 : Fin 4) (1 : K)
    let u1 : Fin 4 → K := Pi.single (1 : Fin 4) (1 : K)
    have hv0 : herm (unitaryInvolution K 2 1) (v 0) (v 0) = 1 := by simpa using hon 0 0
    have hv1 : herm (unitaryInvolution K 2 1) (v 1) (v 1) = 1 := by simpa using hon 1 1
    have hv01 : herm (unitaryInvolution K 2 1) (v 0) (v 1) = 0 := by simpa using hon 0 1
    have hcardv : Nat.card (fixSU {v 0, v 1}) = 6 := card_fixSU_pair hK hv0 hv1 hv01
    have hu0 : herm (unitaryInvolution K 2 1) u0 u0 = 1 := by
      rw [herm, Fin.sum_univ_four]; simp [u0]
    have hu1 : herm (unitaryInvolution K 2 1) u1 u1 = 1 := by
      rw [herm, Fin.sum_univ_four]; simp [u1]
    have hu01 : herm (unitaryInvolution K 2 1) u0 u1 = 0 := by
      rw [herm, Fin.sum_univ_four]; simp [u0, u1]
    have hcardu : Nat.card (fixSU {u0, u1}) = 6 := card_fixSU_pair hK hu0 hu1 hu01
    rw [hcardv, hcardu]

private theorem map_conj_conj {X : Subgroup (Su K 2 1 4)} {g : Su K 2 1 4} :
    (X.map (MulAut.conj g⁻¹ : Su K 2 1 4 →* Su K 2 1 4)).map
      (MulAut.conj g : Su K 2 1 4 →* Su K 2 1 4) = X := by
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj g : Su K 2 1 4 →* Su K 2 1 4).comp
      (MulAut.conj g⁻¹ : Su K 2 1 4 →* Su K 2 1 4) =
      MonoidHom.id (Su K 2 1 4) := by
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp, Subgroup.map_id]

theorem eq_fixSU_of_commute (hK : Nat.card K = 4) {v : Fin 4 → Fin 4 → K}
    (hon : ∀ j k, herm (unitaryInvolution K 2 1) (v j) (v k) = if j = k then 1 else 0)
    {X : Subgroup (Su K 2 1 4)} (e : Su K 2 1 2 ≃* X)
    (hX : ∀ x ∈ X, ∀ y ∈ fixSU {v 2, v 3}, x * y = y * x) :
    X = fixSU {v 0, v 1} := by
  let u0 : Fin 4 → K := Pi.single (0 : Fin 4) (1 : K)
  let u1 : Fin 4 → K := Pi.single (1 : Fin 4) (1 : K)
  let u2 : Fin 4 → K := Pi.single (2 : Fin 4) (1 : K)
  let u3 : Fin 4 → K := Pi.single (3 : Fin 4) (1 : K)
  obtain ⟨g, hG⟩ := exists_mem_SUid_smul_single (σ := unitaryInvolution K 2 1) hon
  choose a ha hG using hG
  have hg_inv : ∀ k, g⁻¹ • v k = (a k)⁻¹ • (Pi.single k (1 : K) : Fin 4 → K) := by
    intro k
    have h := congrArg (fun z => g⁻¹ • z) (hG k)
    simp only [inv_smul_smul, smul_smul_vector] at h
    calc g⁻¹ • v k = (a k)⁻¹ • (a k • (g⁻¹ • v k)) := by
          rw [smul_smul, inv_mul_cancel₀ (ha k), one_smul]
      _ = (a k)⁻¹ • (Pi.single k (1 : K) : Fin 4 → K) := by rw [← h]
  let φ : Su K 2 1 4 ≃* Su K 2 1 4 := MulAut.conj g⁻¹
  let ψ : Su K 2 1 4 ≃* Su K 2 1 4 := MulAut.conj g
  let X' : Subgroup (Su K 2 1 4) := X.map (φ : Su K 2 1 4 →* Su K 2 1 4)
  have hX' : ∀ x' ∈ X', ∀ y' ∈ fixSU {u2, u3}, x' * y' = y' * x' := by
    intro x' hx' y' hy'
    have hx : φ.symm x' ∈ X := Subgroup.mem_map_equiv.mp hx'
    have hy : φ.symm y' ∈ fixSU {v 2, v 3} := by
      simp only [fixSU, Subgroup.mem_iInf, Set.mem_insert_iff, Set.mem_singleton_iff,
        MulAction.mem_stabilizer_iff] at hy' ⊢
      intro z hz
      rcases hz with rfl | rfl
      · change (g * y' * g⁻¹) • v 2 = v 2
        calc (g * y' * g⁻¹) • v 2 = g • (y' • (g⁻¹ • v 2)) := by simp [mul_smul]
          _ = g • (y' • ((a 2)⁻¹ • u2)) := by rw [hg_inv]
          _ = g • ((a 2)⁻¹ • (y' • u2)) := by rw [smul_smul_vector]
          _ = g • ((a 2)⁻¹ • u2) := by rw [hy' u2 (by simp)]
          _ = (a 2)⁻¹ • (g • u2) := by rw [smul_smul_vector]
          _ = (a 2)⁻¹ • (a 2 • v 2) := by rw [hG]
          _ = v 2 := by rw [smul_smul, inv_mul_cancel₀ (ha 2), one_smul]
      · change (g * y' * g⁻¹) • v 3 = v 3
        calc (g * y' * g⁻¹) • v 3 = g • (y' • (g⁻¹ • v 3)) := by simp [mul_smul]
          _ = g • (y' • ((a 3)⁻¹ • u3)) := by rw [hg_inv]
          _ = g • ((a 3)⁻¹ • (y' • u3)) := by rw [smul_smul_vector]
          _ = g • ((a 3)⁻¹ • u3) := by rw [hy' u3 (by simp)]
          _ = (a 3)⁻¹ • (g • u3) := by rw [smul_smul_vector]
          _ = (a 3)⁻¹ • (a 3 • v 3) := by rw [hG]
          _ = v 3 := by rw [smul_smul, inv_mul_cancel₀ (ha 3), one_smul]
    have hcomm := hX (φ.symm x') hx (φ.symm y') hy
    calc x' * y' = φ (φ.symm x') * φ (φ.symm y') := by simp
      _ = φ (φ.symm x' * φ.symm y') := by rw [map_mul]
      _ = φ (φ.symm y' * φ.symm x') := by rw [hcomm]
      _ = φ (φ.symm y') * φ (φ.symm x') := by rw [map_mul]
      _ = y' * x' := by simp
  let e' : Su K 2 1 2 ≃* X' := e.trans (MulEquiv.subgroupMap φ X)
  have hX'eq : X' = fixSU {u0, u1} := eq_fixSU_std hK e' hX'
  have hmapfix : (fixSU {u0, u1}).map (ψ : Su K 2 1 4 →* Su K 2 1 4) =
      fixSU {v 0, v 1} := by
    simpa [ψ] using map_conj_fixSU_std_pair hK hon ha hG hg_inv
  have hmapX : X'.map (ψ : Su K 2 1 4 →* Su K 2 1 4) = X := by
    simpa [X', φ, ψ] using map_conj_conj (X := X) (g := g)
  calc X = X'.map (ψ : Su K 2 1 4 →* Su K 2 1 4) := hmapX.symm
    _ = (fixSU {u0, u1}).map (ψ : Su K 2 1 4 →* Su K 2 1 4) := by rw [hX'eq]
    _ = fixSU {v 0, v 1} := hmapfix
