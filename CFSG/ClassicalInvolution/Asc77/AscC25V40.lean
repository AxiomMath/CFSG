module

public import CFSG.ClassicalInvolution.Asc77.AscC25V35

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.GorensteinWalter
open scoped MatrixGroups commutatorElement

section Diag

variable {F : Type} [Field F] [Finite F]

theorem exists_toPGL_of_diagPGL_eq_one (h : PGL2 F) (hh : diagPGL h = 1) :
    ∃ y : PSL2 F, h = Matrix.ProjectiveSpecialLinearGroup.toPGL y := by
  classical
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective h
  have hsq : IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) := (sqHom_eq_one_iff _).mp hh
  obtain ⟨μ, hμ⟩ := hsq
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hμ
    exact (Matrix.GeneralLinearGroup.det g).ne_zero hμ
  have hdetM : (μ⁻¹ • (g : Matrix (Fin 2) (Fin 2) F)).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin]
    have h1 : (g : Matrix (Fin 2) (Fin 2) F).det = μ * μ := by
      have := hμ
      simpa using this
    rw [h1]
    field_simp
  refine ⟨QuotientGroup.mk ⟨μ⁻¹ • (g : Matrix (Fin 2) (Fin 2) F), hdetM⟩, ?_⟩
  show Matrix.ProjGenLinGroup.mk g = Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL
    ⟨μ⁻¹ • (g : Matrix (Fin 2) (Fin 2) F), hdetM⟩)
  rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 μ⁻¹ (inv_ne_zero hμ0), ?_⟩
  apply Units.ext
  have e : ((Matrix.SpecialLinearGroup.toGL
      (⟨μ⁻¹ • (g : Matrix (Fin 2) (Fin 2) F), hdetM⟩ : Matrix.SpecialLinearGroup (Fin 2) F) :
        GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = μ⁻¹ • (g : Matrix (Fin 2) (Fin 2) F) := rfl
  rw [e]
  ext i j
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
    Matrix.smul_apply, smul_eq_mul]
  fin_cases j <;> simp [Matrix.diagonal_apply, mul_comm]

end Diag

section Nu

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] noncomputable def nuK (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) :
    Subgroup.normalizer (K : Set G) →* PGammaL2 (GaloisField p f) :=
  normalizerToPGammaL2Mod e (gf_facts hp hq).2.1 (gf_facts hp hq).2.2.1 (gf_facts hp hq).2.2.2

theorem fieldChar_eq_rightHom (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    (x : Subgroup.normalizer (K : Set G)) :
    fieldChar hp hq e x = SemidirectProduct.rightHom (nuK hp hq e x) := rfl

theorem diagChar_eq_diagGamma (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    (x : Subgroup.normalizer (K : Set G)) :
    diagChar hp hq e x = diagGamma (nuK hp hq e x) := rfl

@[expose] noncomputable def nuG (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) (x : G) :
    PGammaL2 (GaloisField p f) := by
  classical
  exact if hx : x ∈ Subgroup.normalizer (K : Set G) then nuK hp hq e ⟨x, hx⟩ else 1

variable (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
  (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))

include hp hq in
theorem nuG_of_mem {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    nuG hp hq e x = nuK hp hq e ⟨x, hx⟩ := by
  simp [nuG, hx]

include hp hq in
theorem nuG_mul {a b : G} (ha : a ∈ Subgroup.normalizer (K : Set G))
    (hb : b ∈ Subgroup.normalizer (K : Set G)) :
    nuG hp hq e (a * b) = nuG hp hq e a * nuG hp hq e b := by
  have hmul : (⟨a * b, Subgroup.mul_mem _ ha hb⟩ : Subgroup.normalizer (K : Set G)) =
      ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
  rw [nuG_of_mem hp hq e ha, nuG_of_mem hp hq e hb,
    nuG_of_mem hp hq e (Subgroup.mul_mem _ ha hb), hmul, map_mul]

include hp hq in
theorem nuG_inv {a : G} (ha : a ∈ Subgroup.normalizer (K : Set G)) :
    nuG hp hq e a⁻¹ = (nuG hp hq e a)⁻¹ := by
  have hinv : (⟨a⁻¹, Subgroup.inv_mem _ ha⟩ : Subgroup.normalizer (K : Set G)) = ⟨a, ha⟩⁻¹ := rfl
  rw [nuG_of_mem hp hq e ha, nuG_of_mem hp hq e (Subgroup.inv_mem _ ha), hinv, map_inv]

include hp hq in
theorem nuG_pow {a : G} (ha : a ∈ Subgroup.normalizer (K : Set G)) (m : ℕ) :
    nuG hp hq e (a ^ m) = (nuG hp hq e a) ^ m := by
  have hpow : (⟨a ^ m, Subgroup.pow_mem _ ha m⟩ : Subgroup.normalizer (K : Set G)) =
      ⟨a, ha⟩ ^ m := rfl
  rw [nuG_of_mem hp hq e ha, nuG_of_mem hp hq e (Subgroup.pow_mem _ ha m), hpow, map_pow]

include hp hq in
theorem nuG_conj {a b : G} (ha : a ∈ Subgroup.normalizer (K : Set G))
    (hb : b ∈ Subgroup.normalizer (K : Set G)) :
    nuG hp hq e (a * b * a⁻¹) = nuG hp hq e a * nuG hp hq e b * (nuG hp hq e a)⁻¹ := by
  rw [nuG_mul hp hq e (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha), nuG_mul hp hq e ha hb,
    nuG_inv hp hq e ha]

include hp hq in
theorem nuG_one : nuG hp hq e (1 : G) = 1 := by
  have hone : (⟨1, Subgroup.one_mem _⟩ : Subgroup.normalizer (K : Set G)) = 1 := rfl
  rw [nuG_of_mem hp hq e (Subgroup.one_mem _), hone, map_one]

include hp hq in
theorem nuG_eq_one_iff {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    nuG hp hq e n = 1 ↔ ∀ l ∈ K, ⁅n, l⁆ ∈ oddCoreOf K := by
  rw [nuG_of_mem hp hq e hn]
  exact Hall196.normalizerToPGammaL2Mod_eq_one_iff e (gf_facts hp hq).2.1
    (gf_facts hp hq).2.2.1 (gf_facts hp hq).2.2.2 ⟨n, hn⟩

include hp hq in
theorem fieldChar_eq_rightHom_nuG {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    fieldChar hp hq e ⟨n, hn⟩ = SemidirectProduct.rightHom (nuG hp hq e n) := by
  rw [nuG_of_mem hp hq e hn]
  rfl

include hp hq in
theorem diagChar_eq_diagGamma_nuG {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    diagChar hp hq e ⟨n, hn⟩ = diagGamma (nuG hp hq e n) := by
  rw [nuG_of_mem hp hq e hn]
  rfl

include hp hq in
theorem exists_mem_K_nuG_eq_inr {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G))
    (hδ : diagChar hp hq e ⟨n, hn⟩ = 1) :
    ∃ k ∈ K, nuG hp hq e (k⁻¹ * n) = SemidirectProduct.inr (fieldChar hp hq e ⟨n, hn⟩) := by
  classical
  let α : PGammaL2 (GaloisField p f) := nuK hp hq e ⟨n, hn⟩
  have hαδ : diagPGL α.left = 1 := by
    rw [← diagGamma_apply]
    exact hδ
  obtain ⟨y, hy⟩ := exists_toPGL_of_diagPGL_eq_one α.left hαδ
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨κ, hκ⟩ := QuotientGroup.mk_surjective (e.symm s)
  have hs : e (QuotientGroup.mk κ) = s := by rw [hκ, MulEquiv.apply_symm_apply]
  refine ⟨(κ : G), κ.2, ?_⟩
  have hκN : (κ : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer κ.2
  have hk := Hall196.normalizerToPGammaL2Mod_of_mem e (gf_facts hp hq).2.1
    (gf_facts hp hq).2.2.1 (gf_facts hp hq).2.2.2 κ.2
  rw [hs] at hk
  rw [nuG_of_mem hp hq e (Subgroup.mul_mem _ (Subgroup.inv_mem _ hκN) hn)]
  have e1 : (⟨(κ : G)⁻¹ * n, Subgroup.mul_mem _ (Subgroup.inv_mem _ hκN) hn⟩ :
      Subgroup.normalizer (K : Set G)) = ⟨(κ : G), hκN⟩⁻¹ * ⟨n, hn⟩ := rfl
  rw [e1, map_mul, map_inv]
  change (nuK hp hq e ⟨(κ : G), hκN⟩)⁻¹ * α = _
  have hk' : nuK hp hq e ⟨(κ : G), hκN⟩ = SemidirectProduct.inl α.left := by
    rw [hy]
    exact hk
  rw [hk']
  have hα : SemidirectProduct.inl α.left * SemidirectProduct.inr α.right = α :=
    SemidirectProduct.inl_left_mul_inr_right α
  calc (SemidirectProduct.inl α.left)⁻¹ * α =
      (SemidirectProduct.inl α.left)⁻¹ *
        (SemidirectProduct.inl α.left * SemidirectProduct.inr α.right) := by rw [hα]
    _ = SemidirectProduct.inr α.right := inv_mul_cancel_left _ _
    _ = _ := rfl

end Nu

section Lift

variable {G : Type} [Group G] [Finite G]

theorem mul_mul_inv_mem_oddCoreOf_of_mem {K : Subgroup G} {l o : G} (hl : l ∈ K)
    (ho : o ∈ oddCoreOf K) : l * o * l⁻¹ ∈ oddCoreOf K := by
  obtain ⟨hoK, ho'⟩ := mem_oddCoreOf_iff.mp ho
  refine mem_oddCoreOf_iff.mpr ⟨?_, ?_⟩
  · exact K.mul_mem (K.mul_mem hl hoK) (K.inv_mem hl)
  · exact (inferInstance : (classicalInvolutionOddCore ↥K).Normal).conj_mem _ ho' ⟨l, hl⟩

theorem exists_commute_of_comm_mod_odd {K : Subgroup G} {h u : G} {k : ℕ}
    (hh : h ^ 2 ^ k = 1) (hhK : h ∈ Subgroup.normalizer (K : Set G))
    (hcomm : ∀ l ∈ K, ⁅h, l⁆ ∈ oddCoreOf K) (huK : u ∈ K) :
    ∃ v ∈ K, u⁻¹ * v ∈ oddCoreOf K ∧ h * v = v * h := by
  classical
  have hh' : h⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hhK
  have hnorm : ∀ x : G, x ∈ K → h * x * h⁻¹ ∈ K := fun x hx => (Subgroup.mem_normalizer_iff.mp
    hhK x).mp hx
  have hnorm' : ∀ x : G, x ∈ K → h⁻¹ * x * h⁻¹⁻¹ ∈ K := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hh' x).mp hx
  let O : Subgroup G := oddCoreOf K
  have hOK : O ≤ K := oddCoreOf_le_self K
  have hfwd : ∀ x : G, x ∈ K → u⁻¹ * x ∈ O → u⁻¹ * (h * x * h⁻¹) ∈ O := by
    intro x hx hux
    have h1 : ⁅h, x⁆ ∈ O := hcomm x hx
    have h2 : u⁻¹ * (h * x * h⁻¹) = (u⁻¹ * ⁅h, x⁆ * u) * (u⁻¹ * x) := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    refine O.mul_mem ?_ hux
    have := mul_mul_inv_mem_oddCoreOf_of_mem (K := K) (K.inv_mem huK) h1
    simpa [mul_assoc] using this
  have hbwd : ∀ x : G, x ∈ K → u⁻¹ * x ∈ O → u⁻¹ * (h⁻¹ * x * h⁻¹⁻¹) ∈ O := by
    intro x hx hux
    have hx' : h⁻¹ * x * h⁻¹⁻¹ ∈ K := hnorm' x hx
    have h1 : ⁅h, h⁻¹ * x * h⁻¹⁻¹⁆ ∈ O := hcomm _ hx'
    have h2 : u⁻¹ * (h⁻¹ * x * h⁻¹⁻¹) = (u⁻¹ * ⁅h, h⁻¹ * x * h⁻¹⁻¹⁆⁻¹ * u) * (u⁻¹ * x) := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    refine O.mul_mem ?_ hux
    have := mul_mul_inv_mem_oddCoreOf_of_mem (K := K) (K.inv_mem huK) (O.inv_mem h1)
    simpa [mul_assoc] using this
  let A : Type _ := {x : G // x ∈ K ∧ u⁻¹ * x ∈ O}
  let σ : Equiv.Perm A :=
    { toFun := fun x => ⟨h * x.1 * h⁻¹, hnorm x.1 x.2.1, hfwd x.1 x.2.1 x.2.2⟩
      invFun := fun x => ⟨h⁻¹ * x.1 * h⁻¹⁻¹, hnorm' x.1 x.2.1, hbwd x.1 x.2.1 x.2.2⟩
      left_inv := fun x => Subtype.ext (by
        change h⁻¹ * (h * x.1 * h⁻¹) * h⁻¹⁻¹ = x.1
        group)
      right_inv := fun x => Subtype.ext (by
        change h * (h⁻¹ * x.1 * h⁻¹⁻¹) * h⁻¹ = x.1
        group) }
  have hσpow : ∀ (n : ℕ) (x : A), ((σ ^ n) x).1 = h ^ n * x.1 * (h ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply]
      have h1 := ih (σ x)
      change ((σ ^ n) (σ x)).1 = _ at h1
      rw [h1]
      change h ^ n * (h * x.1 * h⁻¹) * (h ^ n)⁻¹ = h ^ (n + 1) * x.1 * (h ^ (n + 1))⁻¹
      rw [pow_succ, mul_inv_rev]
      group
  have hσ2 : σ ^ 2 ^ k = 1 := by
    ext x
    rw [hσpow, hh]
    simp
  have hcard : Nat.card A = Nat.card O := by
    refine Nat.card_congr
      { toFun := fun x => ⟨u⁻¹ * x.1, x.2.2⟩
        invFun := fun o => ⟨u * o.1, K.mul_mem huK (hOK o.2), by simp⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun o => Subtype.ext (by simp) }
  have : Finite A := inferInstance
  let := Fintype.ofFinite A
  have hodd : ¬ 2 ∣ Fintype.card A := by
    rw [← Nat.card_eq_fintype_card, hcard]
    have h2 : Nat.card ↥O % 2 = 1 := Nat.odd_iff.mp (oddCoreOf_odd_natCard K)
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxσ⟩ := Equiv.Perm.exists_fixed_point_of_prime hodd hσ2
  refine ⟨x.1, x.2.1, x.2.2, ?_⟩
  have := congrArg Subtype.val hxσ
  change h * x.1 * h⁻¹ = x.1 at this
  calc h * x.1 = (h * x.1 * h⁻¹) * h := by group
    _ = x.1 * h := by rw [this]

theorem exists_order_four_commute_of_comm_mod_odd {K : Subgroup G} {h u : G} {k : ℕ}
    (hh : h ^ 2 ^ k = 1) (hhK : h ∈ Subgroup.normalizer (K : Set G))
    (hcomm : ∀ l ∈ K, ⁅h, l⁆ ∈ oddCoreOf K) (huK : u ∈ K) (hu4 : orderOf u = 4) :
    ∃ y ∈ K, orderOf y = 4 ∧ h * y = y * h := by
  classical
  obtain ⟨v, hvK, hvu, hhv⟩ := exists_commute_of_comm_mod_odd hh hhK hcomm huK
  let O' : Subgroup ↥K := classicalInvolutionOddCore ↥K
  let φ : ↥K →* ↥K ⧸ O' := QuotientGroup.mk' O'
  let uK : ↥K := ⟨u, huK⟩
  let vK : ↥K := ⟨v, hvK⟩
  have hφ : φ vK = φ uK := by
    change (QuotientGroup.mk vK : ↥K ⧸ O') = QuotientGroup.mk uK
    symm
    rw [QuotientGroup.eq]
    obtain ⟨_, h2⟩ := mem_oddCoreOf_iff.mp hvu
    exact h2
  have hker : ∀ x : ↥K, φ x = 1 → (x : G) ∈ oddCoreOf K := by
    intro x hx
    refine mem_oddCoreOf_iff.mpr ⟨x.2, ?_⟩
    exact (QuotientGroup.eq_one_iff x).mp hx
  have hu4K : uK ^ 4 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hu4]
    exact pow_orderOf_eq_one u
  have h2u : ¬ (φ uK) ^ 2 = 1 := by
    intro h2
    have h3 : φ (uK ^ 2) = 1 := by rw [map_pow]; exact h2
    have h4 := hker _ h3
    have h5 : u ^ 2 ∈ oddCoreOf K := h4
    have hpg : IsPGroup 2 (Subgroup.zpowers (u ^ 2)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num) (by rw [hu4]; norm_num), hu4]
      norm_num
    have := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h5 hpg
    have h6 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one this
    rw [hu4] at h6
    omega
  have hord : orderOf (φ uK) = 4 := by
    have h4 : (φ uK) ^ 4 = 1 := by rw [← map_pow, hu4K, map_one]
    exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h2u) (by simpa using h4)
  have hord0 : orderOf v ≠ 0 := (orderOf_pos v).ne'
  obtain ⟨j, m, hm, hjm⟩ := Nat.exists_eq_two_pow_mul_odd hord0
  have hvm : orderOf (v ^ m) = 2 ^ j := by
    have h1 : m ∣ orderOf v := ⟨2 ^ j, by rw [hjm, mul_comm]⟩
    rw [orderOf_pow_of_dvd hm.pos.ne' h1, hjm, Nat.mul_div_cancel _ hm.pos]
  have hmodd : m % 2 = 1 := Nat.odd_iff.mp hm
  have hφvm : ∀ n : ℕ, φ ((vK ^ m) ^ n) = (φ uK) ^ (m * n) := by
    intro n
    rw [map_pow, map_pow, hφ, ← pow_mul]
  have hcoe : ∀ n : ℕ, (((vK ^ m) ^ n : ↥K) : G) = (v ^ m) ^ n := by
    intro n
    rw [Subgroup.coe_pow, Subgroup.coe_pow]
  have hy4 : (v ^ m) ^ 4 = 1 := by
    have h1 : (φ uK) ^ (m * 4) = 1 := by
      rw [mul_comm, pow_mul, ← hord, pow_orderOf_eq_one, one_pow]
    have h2 : (v ^ m) ^ 4 ∈ oddCoreOf K := by
      rw [← hcoe]
      exact hker _ (by rw [hφvm]; exact h1)
    have hpg : IsPGroup 2 (Subgroup.zpowers ((v ^ m) ^ 4)) := by
      have hd : orderOf ((v ^ m) ^ 4) ∣ 2 ^ j := by
        rw [← hvm]
        exact orderOf_pow_dvd _
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    exact eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h2 hpg
  have hy2 : ¬ (v ^ m) ^ 2 = 1 := by
    intro h2
    have h3 : (φ uK) ^ (m * 2) = 1 := by
      rw [← hφvm]
      have : (vK ^ m) ^ 2 = 1 := by
        apply Subtype.ext
        rw [hcoe]
        exact h2
      rw [this, map_one]
    have h4 : 4 ∣ m * 2 := hord ▸ orderOf_dvd_of_pow_eq_one h3
    omega
  refine ⟨v ^ m, K.pow_mem hvK m, ?_, (Commute.pow_right (show Commute h v from hhv) m).eq⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hy2) (by simpa using hy4)

end Lift

end CFSG.ClassicalInvolution.Asc77.C25V
