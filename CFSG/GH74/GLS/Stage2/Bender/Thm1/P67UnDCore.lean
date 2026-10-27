module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UnKey
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Un

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.GLS.Stage2.OddAut CFSG.LinearGroups


section Iso2

variable {K : Type} [Field K] (h : UnitaryFieldData 3 1 K)

theorem isom2_eq_one {C : Type} [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    {β : C →ₛₗ[h.bar] C →ₗ[K] K} (hβ : β.IsSymm) (hβl : β.SeparatingLeft)
    (hdim : Module.finrank K C = 2) {s : ℕ} (hs2 : ¬ 2 ∣ s) (hs3 : ¬ 3 ∣ s) (φ : C →ₗ[K] C)
    (hφ : ∀ x y, β (φ x) (φ y) = β x y) (hφs : φ ^ s = 1) : φ = 1 := by
  have hcard := (unitary_full_group_order h hβ hβl hdim (by norm_num)).1
  have hcard96 : Nat.card (sesqUnitaryGroup β) = 96 := by
    have h96 : (Nat.card (sesqUnitaryGroup β) : ℤ) = 96 := by
      rw [hcard]
      norm_num [Finset.prod_Icc_succ_top]
    exact_mod_cast h96
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs2 (dvd_zero 2)
  have hcop : Nat.Coprime s 96 := by
    have h2 : Nat.Coprime s 2 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hs2 |>.symm
    have h3 : Nat.Coprime s 3 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hs3 |>.symm
    have : (96 : ℕ) = 2 ^ 5 * 3 := by norm_num
    rw [this]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right 5 h2) h3
  have hs1 : s - 1 + 1 = s := Nat.sub_add_cancel (Nat.pos_of_ne_zero hs0)
  let u : LinearMap.GeneralLinearGroup K C :=
    ⟨φ, φ ^ (s - 1), by rw [← pow_succ', hs1, hφs], by rw [← pow_succ, hs1, hφs]⟩
  have hu : u ∈ sesqUnitaryGroup β := fun x y => hφ x y
  have hus : (⟨u, hu⟩ : sesqUnitaryGroup β) ^ s = 1 := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
    exact hφs
  have h1 : orderOf (⟨u, hu⟩ : sesqUnitaryGroup β) ∣ 96 := hcard96 ▸ orderOf_dvd_natCard _
  have h2 : orderOf (⟨u, hu⟩ : sesqUnitaryGroup β) ∣ s := orderOf_dvd_of_pow_eq_one hus
  have h3 : orderOf (⟨u, hu⟩ : sesqUnitaryGroup β) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
  have h4 : (⟨u, hu⟩ : sesqUnitaryGroup β) = 1 := orderOf_eq_one_iff.mp h3
  have h5 := congrArg (fun x : sesqUnitaryGroup β => ((x : LinearMap.GeneralLinearGroup K C) :
    C →ₗ[K] C)) h4
  have h6 : ((u : LinearMap.GeneralLinearGroup K C) : C →ₗ[K] C) = 1 := by simpa using h5
  exact h6

end Iso2

section LemmaA

variable {K : Type} [Field K] (h : UnitaryFieldData 3 1 K) {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Matrix ι ι K}

theorem act_pow_succ (b : gramSU h G) (k : ℕ) (x : ι → K) :
    act (b ^ (k + 1)) x = act b (act (b ^ k) x) := by
  rw [pow_succ', act_mul]

theorem eq_one_of_fix_isotropic [CharP K 3] (hG : HermGram h G) (hι : Fintype.card ι = 4)
    {b : gramSU h G} {s : ℕ} (hs2 : ¬ 2 ∣ s) (hs3 : ¬ 3 ∣ s) (hbs : b ^ s = 1)
    {w : ι → K} (hw0 : w ≠ 0) (hww : gramForm h G w w = 0) (hbw : act b w = w) : b = 1 := by
  classical
  set B := gramForm h G with hB
  have hBs : B.IsSymm := gramForm_isSymm h hG.herm
  have hBl : B.SeparatingLeft := gramForm_separatingLeft h hG.det_ne
  have hfin : Module.finrank K (ι → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, hι]
  obtain ⟨⟨f', hwf, hff⟩, hsplit⟩ := hermitian_hyperbolic_splitting h hBs hBl hw0 hww
  obtain ⟨hHdim, -, hcompl, hUsep, hUdim⟩ := hsplit f' hwf hff
  set H := Submodule.span K {w, f'} with hH
  set U := H.orthogonalBilin B with hU
  have hfw : B f' w = 1 := by rw [← hBs.eq w f', hwf, map_one]
  have hwH : w ∈ H := Submodule.subset_span (by simp)
  have hf'H : f' ∈ H := Submodule.subset_span (by simp)
  have hmemU : ∀ y, y ∈ U ↔ B w y = 0 ∧ B f' y = 0 := by
    intro y
    rw [hU, Submodule.mem_orthogonalBilin]
    constructor
    · intro hy
      exact ⟨hy w hwH, hy f' hf'H⟩
    · rintro ⟨h1, h2⟩ n hn
      obtain ⟨a, c, rfl⟩ := Submodule.mem_span_pair.mp hn
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1,
        h2, mul_zero, add_zero]
  have hBw0 : ∀ y, B w y = 0 → B y w = 0 := fun y hy => B_eq_zero_comm hG hy
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let pr : (ι → K) →ₗ[K] (ι → K) :=
    LinearMap.id - (B f').smulRight w - (B w).smulRight f'
  have hpr : ∀ y, pr y = y - B f' y • w - B w y • f' := fun y => by simp [pr]
  have hprU : ∀ y, pr y ∈ U := by
    intro y
    rw [hmemU, hpr]
    constructor
    · simp only [map_sub, map_smul, smul_eq_mul, hww, hwf, mul_zero, mul_one, sub_zero]
      ring
    · simp only [map_sub, map_smul, smul_eq_mul, hfw, hff, mul_zero, mul_one, sub_zero]
      ring
  have hprfix : ∀ x ∈ U, pr x = x := by
    intro x hx
    rw [hmemU] at hx
    rw [hpr, hx.1, hx.2]
    simp
  let bLin : (ι → K) →ₗ[K] (ι → K) := Matrix.mulVecLin (mx (b : GL ι K))
  have hbLin : ∀ x, bLin x = act b x := fun x => rfl
  let φ : U →ₗ[K] U := LinearMap.codRestrict U ((pr ∘ₗ bLin) ∘ₗ U.subtype) (fun x => hprU _)
  have hφ : ∀ x : U, ((φ x : U) : ι → K) = pr (act b x) := fun x => rfl
  have hBb : ∀ x y, B (act b x) (act b y) = B x y := B_act b
  have hBwb : ∀ x, B w (act b x) = B w x := fun x => by
    conv_lhs => rw [← hbw]
    exact hBb w x
  have hdec : ∀ x : U, act b x = ((φ x : U) : ι → K) + B f' (act b x) • w := by
    intro x
    have hx := (hmemU x).mp x.2
    have h1 : B w (act b x) = 0 := by rw [hBwb, hx.1]
    rw [hφ, hpr, h1]
    simp
  have hφ' : ∀ x : U, ((φ x : U) : ι → K) = act b x - B f' (act b x) • w := fun x => by
    rw [eq_sub_iff_add_eq]
    exact (hdec x).symm
  have hiso : ∀ x y : U, (B.domRestrict₁₂ U U) (φ x) (φ y) = (B.domRestrict₁₂ U U) x y := by
    intro x y
    simp only [LinearMap.domRestrict₁₂_apply]
    have hx := (hmemU x).mp x.2
    have hy := (hmemU y).mp y.2
    have e1 : B (act b x) w = 0 := hBw0 _ (by rw [hBwb, hx.1])
    have e2 : B w (act b y) = 0 := by rw [hBwb, hy.1]
    rw [hφ' x, hφ' y]
    simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, e1, e2,
      hww, mul_zero, sub_zero, hBb]
  have hpow : ∀ k : ℕ, ∀ x : U, ∃ α : K,
      act (b ^ k) (x : ι → K) = (((φ ^ k) x : U) : ι → K) + α • w := by
    intro k
    induction k with
    | zero =>
      intro x
      exact ⟨0, by simp [act_one]⟩
    | succ k ih =>
      intro x
      obtain ⟨α, hα⟩ := ih x
      obtain ⟨c, hc⟩ : ∃ c : K, act b (((φ ^ k) x : U) : ι → K) =
          ((φ ((φ ^ k) x) : U) : ι → K) + c • w := ⟨_, hdec ((φ ^ k) x)⟩
      refine ⟨c + α, ?_⟩
      rw [act_pow_succ, hα, act_add, act_smul, hbw, hc, pow_succ', Module.End.mul_apply, add_smul]
      abel
  have hφs : φ ^ s = 1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    obtain ⟨α, hα⟩ := hpow s x
    rw [hbs, act_one] at hα
    have hmem : α • w ∈ H := H.smul_mem α hwH
    have hmem' : α • w ∈ U := by
      have : α • w = (x : ι → K) - (((φ ^ s) x : U) : ι → K) := by
        rw [hα]
        abel
      rw [this]
      exact U.sub_mem x.2 ((φ ^ s) x).2
    have h0 : α • w = 0 := (Submodule.disjoint_def.mp hcompl.disjoint) _ hmem hmem'
    have : (x : ι → K) = (((φ ^ s) x : U) : ι → K) := by
      rw [h0, add_zero] at hα
      exact hα
    simp only [Module.End.one_apply]
    exact this.symm
  have hφ1 : φ = 1 := by
    refine isom2_eq_one h (β := B.domRestrict₁₂ U U) ⟨fun x y => ?_⟩ hUsep (by omega) hs2 hs3 φ
      hiso hφs
    simp only [LinearMap.domRestrict₁₂_apply]
    exact hBs.eq x y
  have hbU : ∀ x ∈ U, ∃ α : K, act b x = x + α • w := by
    intro x hx
    have h1 := hdec ⟨x, hx⟩
    rw [hφ1] at h1
    exact ⟨_, by simpa using h1⟩
  have hD1 : ∀ y, B w y = 0 → ∃ α : K, act b y - y = α • w := by
    intro y hy
    have e2 : y = pr y + B f' y • w := by rw [hpr, hy]; simp
    obtain ⟨α, hα⟩ := hbU (pr y) (hprU y)
    have e1 : act b y = pr y + α • w + B f' y • w := by
      have := congrArg (act b) e2
      rw [act_add, act_smul, hbw, hα] at this
      exact this
    refine ⟨α, ?_⟩
    calc act b y - y = act b y - (pr y + B f' y • w) := by rw [← e2]
      _ = α • w := by rw [e1]; abel
  have hD3 : ∀ y, B w y = 0 → act b (act b y - y) - (act b y - y) = 0 := by
    intro y hy
    obtain ⟨α, hα⟩ := hD1 y hy
    rw [hα, act_smul, hbw, sub_self]
  have hN3 : (mx (b : GL ι K) - 1) ^ 3 = 0 := by
    apply mat_eq_of_mulVec_eq
    intro v
    rw [Matrix.zero_mulVec]
    rw [pow_succ_mulVec, pow_succ_mulVec, pow_succ_mulVec, pow_zero, Matrix.one_mulVec,
      mx_sub_one_mulVec, mx_sub_one_mulVec, mx_sub_one_mulVec]
    refine hD3 _ ?_
    rw [map_sub, hBwb, sub_self]
  have hb3 : b ^ 3 = 1 := by
    set M : Matrix ι ι K := mx (b : GL ι K) with hM
    have hMp : M ^ 3 = 1 := by
      have h1 : M = (M - 1) + 1 := by abel
      rw [h1, add_pow_char_of_commute 3 (Commute.one_right (M - 1)), hN3, one_pow, zero_add]
    apply Subtype.ext
    apply Units.ext
    simpa [hM, mx] using hMp
  have hcop3 : Nat.Coprime s 3 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hs3).symm
  have h13 : b ^ Nat.gcd s 3 = 1 := pow_gcd_eq_one.mpr ⟨hbs, hb3⟩
  rwa [hcop3, pow_one] at h13

end LemmaA

section LemmaB

variable {K : Type} [Field K] (h : UnitaryFieldData 3 1 K) {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Matrix ι ι K}

theorem act_pow_eq_pow_succ' (b : gramSU h G) (k : ℕ) (x : ι → K) :
    act (b ^ (k + 1)) x = act (b ^ k) (act b x) := by
  rw [pow_succ, act_mul]

theorem exists_fixed_isotropic [CharP K 3] (hG : HermGram h G) (hι : Fintype.card ι = 4)
    {g b : gramSU h G} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hgb : g * b = b * g) {s : ℕ}
    (hs2 : ¬ 2 ∣ s) (hs3 : ¬ 3 ∣ s) (hbs : b ^ s = 1) :
    ∃ w : ι → K, w ≠ 0 ∧ gramForm h G w w = 0 ∧ act b w = w := by
  classical
  set B := gramForm h G with hB
  have hBs : B.IsSymm := gramForm_isSymm h hG.herm
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hfin : Module.finrank K (ι → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, hι]
  set Nm : Matrix ι ι K := mx (g : GL ι K) - 1 with hNm
  have hNv : ∀ v, Nm *ᵥ v = act g v - v := fun v => mx_sub_one_mulVec g v
  have hNp : Nm ^ 3 = 0 := by
    have hMp : (mx (g : GL ι K)) ^ 3 = 1 := by
      have := congrArg (fun x : gramSU h G => mx (x : GL ι K)) hg3
      simpa [mx] using this
    rw [hNm, sub_pow_char_of_commute 3 (Commute.one_right _), hMp, one_pow, sub_self]
  have hNne : Nm ≠ 0 := by
    intro h0
    apply hg1
    have : mx (g : GL ι K) = 1 := sub_eq_zero.mp h0
    apply Subtype.ext
    apply Units.ext
    simpa [mx] using this
  obtain ⟨e, he0, hNe, v0, hv0⟩ := exists_mem_ker_range_of_nilpotent hNp hNne
  let Nl : (ι → K) →ₗ[K] (ι → K) := Matrix.mulVecLin Nm
  have hNl : ∀ v, Nl v = act g v - v := hNv
  set W : Submodule K (ι → K) := LinearMap.ker Nl ⊓ LinearMap.range Nl with hW
  have memW : ∀ x, x ∈ W ↔ Nl x = 0 ∧ x ∈ LinearMap.range Nl := fun x => by
    rw [hW, Submodule.mem_inf, LinearMap.mem_ker]
  have heW : e ∈ W := (memW e).mpr ⟨hNe, ⟨v0, hv0⟩⟩
  have hbg : ∀ v, act b (act g v) = act g (act b v) := fun v => by
    rw [← act_mul, ← act_mul, ← hgb]
  have hbN : ∀ v, act b (Nl v) = Nl (act b v) := fun v => by
    rw [hNl, hNl, act_sub, hbg]
  have hbW : ∀ x ∈ W, act b x ∈ W := by
    intro x hx
    obtain ⟨hx1, v, rfl⟩ := (memW x).mp hx
    refine (memW _).mpr ⟨?_, act b v, (hbN v).symm⟩
    rw [← hbN, hx1, act_zero]
  have hrange : ∀ x y, Nl x = 0 → B x (Nl y) = 0 := by
    intro x y hx
    have h1 : act g x = x := by
      have := hNl x
      rw [hx] at this
      exact (sub_eq_zero.mp this.symm)
    have h2 : act g⁻¹ x = x := by
      calc act g⁻¹ x = act g⁻¹ (act g x) := by rw [h1]
        _ = x := act_inv_act g x
    have h3 : B x (act g y) = B (act g⁻¹ x) y := by
      conv_lhs => rw [← act_act_inv g x]
      rw [B_act]
    rw [hNl, map_sub, h3, h2, sub_self]
  have hiso : ∀ x ∈ W, ∀ y ∈ W, B x y = 0 := by
    intro x hx y hy
    obtain ⟨hx1, -⟩ := (memW x).mp hx
    obtain ⟨-, v, rfl⟩ := (memW y).mp hy
    exact hrange x v hx1
  by_contra hcon
  push Not at hcon
  have hnofix : ∀ w ∈ W, w ≠ 0 → act b w ≠ w := fun w hw hw0 hfix =>
    hcon w hw0 (hiso w hw w hw) hfix
  have hKcard : Nat.card K = 9 := by rw [h.card]; norm_num
  have : Finite K := h.finite
  have : Fintype K := Fintype.ofFinite K
  have hcop8 : Nat.Coprime s 8 := by
    have h2 : Nat.Coprime s 2 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hs2).symm
    have : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [this]
    exact Nat.Coprime.pow_right 3 h2
  have hpowb : ∀ (k : ℕ) (c : K) (w : ι → K), act b w = c • w → act (b ^ k) w = c ^ k • w := by
    intro k c w hw
    induction k with
    | zero => simp [act_one]
    | succ k ih =>
      rw [act_pow_eq_pow_succ', hw, act_smul, ih, smul_smul, pow_succ, mul_comm]
  have hdim1 : Module.finrank K W ≠ 1 := by
    intro hdim
    have hw0 : (⟨e, heW⟩ : W) ≠ 0 := fun h0 => he0 (congrArg Subtype.val h0)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨e, heW⟩ : W) hw0).mp hdim
      ⟨act b e, hbW e heW⟩
    have hce : act b e = c • e := (congrArg Subtype.val hc).symm
    have h1 := hpowb s c e hce
    rw [hbs, act_one] at h1
    have h2 : (c ^ s - 1) • e = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    have h3 : c ^ s = 1 := sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right he0)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow (by rintro rfl; exact hs2 (dvd_zero 2))] at h3
      exact zero_ne_one h3
    have h8 : c ^ 8 = 1 := by
      have : c ^ 9 = c := by
        have hfc : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card, hKcard]
        have := FiniteField.pow_card c
        rwa [hfc] at this
      have h9 : c ^ 8 * c = 1 * c := by rw [one_mul, ← pow_succ, this]
      exact mul_right_cancel₀ hc0 h9
    have h13 : c ^ Nat.gcd s 8 = 1 := pow_gcd_eq_one.mpr ⟨h3, h8⟩
    rw [hcop8, pow_one] at h13
    exact hnofix e heW he0 (by rw [hce, h13, one_smul])
  have hWpos : 0 < Module.finrank K W :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨e, heW⟩, fun h0 => he0 (congrArg Subtype.val h0)⟩
  have hWle_ker : W ≤ LinearMap.ker Nl := inf_le_left
  have hWle_rng : W ≤ LinearMap.range Nl := inf_le_right
  have hrn := LinearMap.finrank_range_add_finrank_ker Nl
  have hk1 := Submodule.finrank_mono hWle_ker
  have hk2 := Submodule.finrank_mono hWle_rng
  have hW2 : Module.finrank K W = 2 := by omega
  have hker : LinearMap.ker Nl = W :=
    (Submodule.eq_of_le_of_finrank_eq hWle_ker (by omega)).symm
  have hrng : LinearMap.range Nl = W :=
    (Submodule.eq_of_le_of_finrank_eq hWle_rng (by omega)).symm
  have hNW : ∀ v, Nl v ∈ W := fun v => hrng ▸ LinearMap.mem_range_self Nl v
  have hskew : ∀ x y, B x (Nl y) = - B (Nl x) y := by
    intro x y
    have h1 : B (act g x) (act g y) = B x y := B_act g x y
    have hx : act g x = x + Nl x := by rw [hNl]; abel
    have hy : act g y = y + Nl y := by rw [hNl]; abel
    rw [hx, hy] at h1
    have h0 : B (Nl x) (Nl y) = 0 := hiso _ (hNW x) _ (hNW y)
    simp only [map_add, LinearMap.add_apply, h0, add_zero] at h1
    linear_combination h1
  let Nr : (ι → K) →ₗ[K] W := Nl.codRestrict W hNW
  have hNr : LinearMap.range Nr = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro w
    have hw : (w : ι → K) ∈ LinearMap.range Nl := by rw [hrng]; exact w.2
    obtain ⟨v, hv⟩ := hw
    exact ⟨v, Subtype.ext hv⟩
  obtain ⟨S, hS⟩ := LinearMap.exists_rightInverse_of_surjective Nr hNr
  have hS' : ∀ w : W, Nl (S w) = (w : ι → K) := fun w => by
    have := congrArg (fun F : W →ₗ[K] W => ((F w : W) : ι → K)) hS
    simpa [Nr] using this
  obtain ⟨i0, hi0, hi0t⟩ := exists_traceZero_ne_zero h
  let γ : W →ₛₗ[h.bar] W →ₗ[K] K := i0 • ((B.comp S).domRestrict₂ W)
  have hγ : ∀ x y : W, γ x y = i0 * B (S x) (y : ι → K) := fun x y => rfl
  have hbari0 : h.bar i0 = -i0 := by linear_combination hi0t
  have hγs : γ.IsSymm := ⟨fun x y => by
    rw [hγ, hγ, map_mul, hbari0]
    have e1 : h.bar (B (S x) (y : ι → K)) = B (y : ι → K) (S x) := B_herm hG _ _
    have e2 : B (y : ι → K) (S x) = - B (S y) (x : ι → K) := by
      have := hskew (S y) (S x)
      rw [hS', hS'] at this
      linear_combination this
    rw [e1, e2]
    ring⟩
  have hγsep : γ.SeparatingLeft := by
    intro x hx
    have hx' : ∀ v : ι → K, B x v = 0 := by
      intro v
      have h1 := hx ⟨Nl v, hNW v⟩
      rw [hγ] at h1
      have h2 : B (S x) (Nl v) = 0 := (mul_eq_zero.mp h1).resolve_left hi0
      have h3 := hskew (S x) v
      rw [hS'] at h3
      linear_combination h3 - h2
    exact Subtype.ext (eq_zero_of_forall_B hG (fun v => B_eq_zero_comm hG (hx' v)))
  let bLin : (ι → K) →ₗ[K] (ι → K) := Matrix.mulVecLin (mx (b : GL ι K))
  let φ : W →ₗ[K] W := bLin.restrict hbW
  have hφ : ∀ x : W, ((φ x : W) : ι → K) = act b x := fun x => rfl
  have hφiso : ∀ x y : W, γ (φ x) (φ y) = γ x y := by
    intro x y
    rw [hγ, hγ]
    have e1 : S (φ x) - act b (S x) ∈ W := by
      have e0 : S (φ x) - act b (S x) ∈ LinearMap.ker Nl := by
        rw [LinearMap.mem_ker, map_sub, hS', ← hbN, hS', hφ, sub_self]
      rwa [hker] at e0
    have e2 : B (S (φ x) - act b (S x)) (act b y) = 0 := hiso _ e1 _ (hbW y y.2)
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at e2
    rw [hφ, e2]
    have : B (act b (S x)) (act b y) = B (S x) y := B_act b _ _
    rw [this]
  have hφpow : ∀ (k : ℕ) (x : W), (((φ ^ k) x : W) : ι → K) = act (b ^ k) (x : ι → K) := by
    intro k
    induction k with
    | zero => intro x; simp [act_one]
    | succ k ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, hφ, ih, act_pow_succ]
  have hφs : φ ^ s = 1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [hφpow, hbs, act_one]
    rfl
  have hφ1 : φ = 1 := isom2_eq_one h (β := γ) hγs hγsep hW2 hs2 hs3 φ hφiso hφs
  have hfixe : act b e = e := by
    have := congrArg (fun F : W →ₗ[K] W => ((F ⟨e, heW⟩ : W) : ι → K)) hφ1
    simpa [hφ] using this
  exact hnofix e heW he0 hfixe

end LemmaB

section Main

variable {K : Type} [Field K] (h : UnitaryFieldData 3 1 K) {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Matrix ι ι K}

theorem eq_one_of_commute_order_three [CharP K 3] (hG : HermGram h G) (hι : Fintype.card ι = 4)
    {g b : gramSU h G} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hgb : g * b = b * g) {s : ℕ}
    (hs2 : ¬ 2 ∣ s) (hs3 : ¬ 3 ∣ s) (hbs : b ^ s = 1) : b = 1 := by
  obtain ⟨w, hw0, hww, hbw⟩ := exists_fixed_isotropic h hG hι hg3 hg1 hgb hs2 hs3 hbs
  exact eq_one_of_fix_isotropic h hG hι hs2 hs3 hbs hw0 hww hbw

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Un
