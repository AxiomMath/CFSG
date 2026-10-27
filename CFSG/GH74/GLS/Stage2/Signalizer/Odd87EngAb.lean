module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem exists_central_commutator_ne_one {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (hnc : ¬ ∀ a b : G, a * b = b * a) :
    ∃ x y : G, x * y * x⁻¹ * y⁻¹ ≠ 1 ∧
      ∀ g : G, g * (x * y * x⁻¹ * y⁻¹) = (x * y * x⁻¹ * y⁻¹) * g := by
  classical
  have hQ : Nontrivial (G ⧸ Subgroup.center G) := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    apply hnc
    intro a b
    have h1 : ((a : G) : G ⧸ Subgroup.center G) = 1 := Subsingleton.elim _ _
    rw [QuotientGroup.eq_one_iff] at h1
    exact ((Subgroup.mem_center_iff.mp h1) b).symm
  have hQp : IsPGroup p (G ⧸ Subgroup.center G) := hG.to_quotient _
  have := hQp.center_nontrivial
  obtain ⟨⟨c, hc⟩, hc1⟩ := exists_ne (1 : Subgroup.center (G ⧸ Subgroup.center G))
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
  have hy : y ∉ Subgroup.center G := by
    intro hy
    apply hc1
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff y).mpr hy
  have hex : ∃ x : G, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    exact hy (Subgroup.mem_center_iff.mpr hcon)
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, y, ?_, ?_⟩
  · intro h
    apply hx
    have h2 : x * y * x⁻¹ * y⁻¹ * (y * x) = 1 * (y * x) := by rw [h]
    simpa [mul_assoc] using h2
  · have hz : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center G := by
      rw [← QuotientGroup.eq_one_iff]
      have h := Subgroup.mem_center_iff.mp hc (x : G ⧸ Subgroup.center G)
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [h]
      group
    exact Subgroup.mem_center_iff.mp hz

theorem exists_eigenspace_dvd_finrank
    {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0) {k : ℕ}
    (x y z : Module.End K V) (hx : IsUnit x) (hy : IsUnit y)
    (hz : z ^ p ^ k = 1) (hz1 : z ≠ 1)
    (hxz : Commute x z) (hyz : Commute y z) (hxy : x * y = z * (y * x)) :
    ∃ μ : K, μ ≠ 1 ∧ μ ^ p ^ k = 1 ∧ Module.End.eigenspace z μ ≠ ⊥ ∧
      p ∣ Module.finrank K (Module.End.eigenspace z μ) := by
  classical
  have hm : ((p ^ k : ℕ) : K) ≠ 0 := by
    rw [Nat.cast_pow]; exact pow_ne_zero _ hpK
  have hsq : Squarefree (Polynomial.X ^ (p ^ k) - 1 : Polynomial K) := by
    have := (Polynomial.separable_X_pow_sub_C (1 : K) hm one_ne_zero).squarefree
    simpa using this
  have hss : z.IsSemisimple := by
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq ?_
    simp [hz]
  have htop : ⨆ μ, Module.End.eigenspace z μ = ⊤ := by
    have := Module.End.iSup_maxGenEigenspace_eq_top z
    simpa [hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] using this
  have hex : ∃ μ : K, μ ≠ 1 ∧ Module.End.eigenspace z μ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hz1
    ext v
    have hv : v ∈ ⨆ μ, Module.End.eigenspace z μ := by rw [htop]; trivial
    have hle : ⨆ μ, Module.End.eigenspace z μ ≤ Module.End.eigenspace z 1 := by
      refine iSup_le fun μ => ?_
      by_cases h1 : μ = 1
      · rw [h1]
      · rw [hcon μ h1]; exact bot_le
    have := hle hv
    simpa using this
  obtain ⟨μ, hμ1, hμE⟩ := hex
  have hμpow : μ ^ p ^ k = 1 := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hμE
    have h1 := (Module.End.HasEigenvector.pow_apply ⟨hv, hv0⟩ (p ^ k))
    rw [hz] at h1
    have h2 : (1 : K) • v = μ ^ p ^ k • v := by simpa using h1
    exact (smul_left_injective K hv0 h2).symm
  set E := Module.End.eigenspace z μ with hE
  have hxE : ∀ v ∈ E, x v ∈ E := by
    intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    calc z (x v) = (z * x) v := rfl
      _ = (x * z) v := by rw [hxz.eq]
      _ = x (z v) := rfl
      _ = μ • x v := by rw [hv, map_smul]
  have hyE : ∀ v ∈ E, y v ∈ E := by
    intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    calc z (y v) = (z * y) v := rfl
      _ = (y * z) v := by rw [hyz.eq]
      _ = y (z v) := rfl
      _ = μ • y v := by rw [hv, map_smul]
  let X : E →ₗ[K] E := x.restrict hxE
  let Y : E →ₗ[K] E := y.restrict hyE
  have hXY : X * Y = μ • (Y * X) := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    show x (y v) = μ • y (x v)
    have h1 : x (y v) = z (y (x v)) := by
      have := congrArg (fun T : Module.End K V => T (v : V)) hxy
      simpa using this
    rw [h1]
    exact Module.End.mem_eigenspace_iff.mp (hyE _ (hxE _ v.2))
  have hdetne : ∀ {w : Module.End K V} (hw : IsUnit w) (hwE : ∀ v ∈ E, w v ∈ E),
      LinearMap.det (w.restrict hwE) ≠ 0 := by
    intro w hw hwE h0
    have h1 := LinearMap.det_eq_zero_iff_ker_ne_bot.mp h0
    apply h1
    rw [LinearMap.ker_eq_bot]
    intro a b hab
    have : w (a : V) = w (b : V) := congrArg Subtype.val hab
    exact Subtype.ext (((Module.End.isUnit_iff w).mp hw).1 this)
  have hdX := hdetne hx hxE
  have hdY := hdetne hy hyE
  have hdet := congrArg LinearMap.det hXY
  rw [LinearMap.det_smul, map_mul, map_mul] at hdet
  have hμd : μ ^ Module.finrank K E = 1 := by
    have hne : LinearMap.det X * LinearMap.det Y ≠ 0 := mul_ne_zero hdX hdY
    refine mul_right_cancel₀ hne ?_
    calc μ ^ Module.finrank K E * (LinearMap.det X * LinearMap.det Y)
        = μ ^ Module.finrank K E * (LinearMap.det Y * LinearMap.det X) := by
          rw [mul_comm (LinearMap.det X) (LinearMap.det Y)]
      _ = LinearMap.det X * LinearMap.det Y := hdet.symm
      _ = 1 * (LinearMap.det X * LinearMap.det Y) := (one_mul _).symm
  refine ⟨μ, hμ1, hμpow, hμE, ?_⟩
  have hord1 : orderOf μ ∣ p ^ k := orderOf_dvd_of_pow_eq_one hμpow
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hord1
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hμ1 (orderOf_eq_one_iff.mp (by simpa using hj))
  have hdvd : orderOf μ ∣ Module.finrank K E := orderOf_dvd_of_pow_eq_one hμd
  rw [hj] at hdvd
  exact (dvd_pow_self p hj0).trans hdvd

theorem exists_weight_space_of_noncomm
    {K V G : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (hpK : (p : K) ≠ 0)
    (ρ : G →* (Module.End K V)ˣ) (hρ : Function.Injective ρ)
    (hnc : ¬ ∀ a b : G, a * b = b * a) :
    ∃ (g : G) (μ : K) (E : Submodule K V), E ≠ ⊥ ∧ p ∣ Module.finrank K E ∧ μ ≠ 1 ∧
      (∃ k : ℕ, μ ^ p ^ k = 1) ∧ ∀ v ∈ E, (ρ g : Module.End K V) v = μ • v := by
  obtain ⟨a, b, hne, hcent⟩ := exists_central_commutator_ne_one hG hnc
  obtain ⟨k, hk⟩ := hG (a * b * a⁻¹ * b⁻¹)
  have hz1 : (ρ (a * b * a⁻¹ * b⁻¹) : Module.End K V) ≠ 1 := by
    intro h
    apply hne
    apply hρ
    rw [map_one]
    exact Units.val_eq_one.mp h
  have hzk : ((ρ (a * b * a⁻¹ * b⁻¹) : Module.End K V)) ^ p ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hk, map_one, Units.val_one]
  have hcomm : ∀ g : G,
      Commute (ρ g : Module.End K V) (ρ (a * b * a⁻¹ * b⁻¹) : Module.End K V) := by
    intro g
    have := hcent g
    show (ρ g : Module.End K V) * _ = _ * (ρ g : Module.End K V)
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, this]
  have hrel : (ρ a : Module.End K V) * (ρ b : Module.End K V) =
      (ρ (a * b * a⁻¹ * b⁻¹) : Module.End K V) *
        ((ρ b : Module.End K V) * (ρ a : Module.End K V)) := by
    rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    group
  obtain ⟨μ, hμ1, hμk, hE, hdvd⟩ := exists_eigenspace_dvd_finrank (Fact.out : p.Prime) hpK
      (ρ a : Module.End K V) (ρ b) (ρ (a * b * a⁻¹ * b⁻¹)) (Units.isUnit _) (Units.isUnit _) hzk hz1
      (hcomm a) (hcomm b) hrel
  exact ⟨a * b * a⁻¹ * b⁻¹, μ, _, hE, hdvd, hμ1, ⟨k, hμk⟩,
    fun v hv => Module.End.mem_eigenspace_iff.mp hv⟩

theorem commute_of_pGroup_of_bilin
    {K V G : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hG : IsPGroup p G)
    (hpK : (p : K) ≠ 0) (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (hdim : Module.finrank K V < 2 * p)
    (ρ : G →* (Module.End K V)ˣ) (hρ : Function.Injective ρ)
    (hinv : ∀ (g : G) (u v : V),
      B ((ρ g : Module.End K V) u) ((ρ g : Module.End K V) v) = B u v) :
    ∀ a b : G, a * b = b * a := by
  by_contra hnc
  obtain ⟨g, μ, E, hE, hdvd, hμ1, ⟨k, hk⟩, hgE⟩ := exists_weight_space_of_noncomm hG hpK ρ hρ hnc
  have hμ2 : μ ^ 2 ≠ 1 := by
    intro h
    have hcop : Nat.Coprime 2 (p ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two (Fact.out)).mpr (Ne.symm hp2))
    have := (pow_gcd_eq_one (a := μ)).mpr ⟨h, hk⟩
    rw [hcop.gcd_eq_one, pow_one] at this
    exact hμ1 this
  have hiso : ∀ u ∈ E, ∀ v ∈ E, B u v = 0 := by
    intro u hu v hv
    have h1 := hinv g u v
    rw [hgE u hu, hgE v hv] at h1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    have h2 : (μ ^ 2 - 1) * B u v = 0 := by
      rw [sub_mul, one_mul, pow_two, mul_assoc, h1, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hμ2)
  have hle : E ≤ B.orthogonal E := fun u hu v hv => hiso v hv u hu
  have h1 : Module.finrank K E ≤ Module.finrank K (B.orthogonal E) := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hB] at h1
  have h2 : 1 ≤ Module.finrank K E := Submodule.one_le_finrank_iff.mpr hE
  have h3 : p ≤ Module.finrank K E := Nat.le_of_dvd h2 hdvd
  omega

section Matrices

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

@[expose] noncomputable def matrixToEnd (K : Type) [Field K] [Algebra F K] :
    Matrix ι ι F →+* Module.End K (ι → K) :=
  (Matrix.toLinAlgEquiv' : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K)).toAlgHom.toRingHom.comp
    (algebraMap F K).mapMatrix

theorem matrixToEnd_injective (K : Type) [Field K] [Algebra F K] :
    Function.Injective (matrixToEnd (ι := ι) (F := F) K) := by
  intro a b hab
  have h1 := Matrix.toLinAlgEquiv'.injective hab
  exact Matrix.map_injective (algebraMap F K).injective h1

@[expose] noncomputable def glToEndUnits (K : Type) [Field K] [Algebra F K] :
    GL ι F →* (Module.End K (ι → K))ˣ :=
  Units.map (matrixToEnd (ι := ι) (F := F) K : Matrix ι ι F →* Module.End K (ι → K))

theorem glToEndUnits_injective (K : Type) [Field K] [Algebra F K] :
    Function.Injective (glToEndUnits (ι := ι) (F := F) K) :=
  Units.map_injective (matrixToEnd_injective K)

theorem glToEndUnits_apply (K : Type) [Field K] [Algebra F K] (g : GL ι F) (v : ι → K) :
    ((glToEndUnits K g : (Module.End K (ι → K))ˣ) : Module.End K (ι → K)) v =
      ((g : Matrix ι ι F).map (algebraMap F K)) *ᵥ v := rfl

theorem natCast_algebraicClosure_ne_zero [Finite F] {p : ℕ} (hp : p.Prime)
    (hpℓ : ringChar F ≠ p) : ((p : ℕ) : AlgebraicClosure F) ≠ 0 := by
  intro h0
  have h1 : ((p : ℕ) : F) = 0 := by
    apply (algebraMap F (AlgebraicClosure F)).injective
    rw [map_natCast, map_zero]
    exact h0
  have h2 : ringChar F ∣ p := (ringChar.spec F _).mp h1
  rcases (Nat.dvd_prime hp).mp h2 with h3 | h3
  · exact CharP.ringChar_ne_one h3
  · exact hpℓ h3

theorem abelian_of_pGroup_of_card_lt [Finite F]
    {p : ℕ} [Fact p.Prime] (hpℓ : ringChar F ≠ p) (hι : Fintype.card ι < p)
    (H : Subgroup (GL ι F)) (hH : IsPGroup p ↥H) :
    ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := by
  classical
  have hpK : ((p : ℕ) : AlgebraicClosure F) ≠ 0 :=
    natCast_algebraicClosure_ne_zero (Fact.out : p.Prime) hpℓ
  let ρ : ↥H →* (Module.End (AlgebraicClosure F) (ι → AlgebraicClosure F))ˣ :=
    (glToEndUnits (ι := ι) (F := F) (AlgebraicClosure F)).comp H.subtype
  have hρ : Function.Injective ρ :=
    (glToEndUnits_injective (AlgebraicClosure F)).comp Subtype.coe_injective
  have hab : ∀ a b : ↥H, a * b = b * a := by
    by_contra hnc
    obtain ⟨g, μ, E, hE, hdvd, -⟩ := exists_weight_space_of_noncomm hH hpK ρ hρ hnc
    have h1 : p ≤ Module.finrank (AlgebraicClosure F) E :=
      Nat.le_of_dvd (Submodule.one_le_finrank_iff.mpr hE) hdvd
    have h2 : Module.finrank (AlgebraicClosure F) E ≤
        Module.finrank (AlgebraicClosure F) (ι → AlgebraicClosure F) := Submodule.finrank_le E
    have h3 : Module.finrank (AlgebraicClosure F) (ι → AlgebraicClosure F) = Fintype.card ι :=
      Module.finrank_fintype_fun_eq_card _
    omega
  intro x hx y hy
  exact congrArg Subtype.val (hab ⟨x, hx⟩ ⟨y, hy⟩)

theorem closure_isometry_mul_eq (J : Matrix ι ι F) {g : GL ι F}
    (hg : g ∈ Subgroup.closure {A : GL ι F | (A : Matrix ι ι F)ᵀ * J * (A : Matrix ι ι F) = J}) :
    (g : Matrix ι ι F)ᵀ * J * (g : Matrix ι ι F) = J := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => simp
  | mul x y _ _ hx hy =>
    simp only [Units.val_mul, Matrix.transpose_mul]
    calc ((y : Matrix ι ι F)ᵀ * (x : Matrix ι ι F)ᵀ) * J * ((x : Matrix ι ι F) * (y : Matrix ι ι F))
        = (y : Matrix ι ι F)ᵀ * ((x : Matrix ι ι F)ᵀ * J * (x : Matrix ι ι F)) *
          (y : Matrix ι ι F) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hx, hy]
  | inv x _ hx =>
    have h1 : (x : Matrix ι ι F) * ((x⁻¹ : GL ι F) : Matrix ι ι F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((x⁻¹ : GL ι F) : Matrix ι ι F)ᵀ * J * ((x⁻¹ : GL ι F) : Matrix ι ι F)
        = ((x⁻¹ : GL ι F) : Matrix ι ι F)ᵀ * ((x : Matrix ι ι F)ᵀ * J * (x : Matrix ι ι F)) *
          ((x⁻¹ : GL ι F) : Matrix ι ι F) := by rw [hx]
      _ = ((x : Matrix ι ι F) * ((x⁻¹ : GL ι F) : Matrix ι ι F))ᵀ * J *
          ((x : Matrix ι ι F) * ((x⁻¹ : GL ι F) : Matrix ι ι F)) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = J := by rw [h1]; simp

theorem glToEndUnits_isometry (K : Type) [Field K] [Algebra F K] (J : Matrix ι ι F) (g : GL ι F)
    (hg : (g : Matrix ι ι F)ᵀ * J * (g : Matrix ι ι F) = J) (u v : ι → K) :
    Matrix.toBilin' (J.map (algebraMap F K))
        ((glToEndUnits K g : Module.End K (ι → K)) u) ((glToEndUnits K g : Module.End K (ι → K)) v) =
      Matrix.toBilin' (J.map (algebraMap F K)) u v := by
  have h1 : ((g : Matrix ι ι F).map (algebraMap F K))ᵀ * J.map (algebraMap F K) *
      (g : Matrix ι ι F).map (algebraMap F K) = J.map (algebraMap F K) := by
    have := congrArg (fun M : Matrix ι ι F => M.map (algebraMap F K)) hg
    simpa [Matrix.map_mul, Matrix.transpose_map] using this
  have h2 := Matrix.toBilin'_comp (J.map (algebraMap F K))
    ((g : Matrix ι ι F).map (algebraMap F K)) ((g : Matrix ι ι F).map (algebraMap F K))
  rw [h1] at h2
  have h3 := LinearMap.congr_fun₂ h2 u v
  simpa [Matrix.toLin'_apply, glToEndUnits_apply] using h3

end Matrices

section Symplectic

open Matrix CFSG.Assembly.LowTwoRank

abbrev symplForm4 (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks 0 1 (-1) 0

theorem det_symplForm4_ne_zero (K : Type) [Field K] : (symplForm4 K).det ≠ 0 := by
  have hJ : symplForm4 K * symplForm4 K = -1 := by
    simp only [symplForm4]
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have h := congrArg Matrix.det hJ
  rw [Matrix.det_mul, Matrix.det_neg, Matrix.det_one] at h
  have h' : (symplForm4 K).det * (symplForm4 K).det = 1 := by
    rw [h]
    simp only [Fintype.card_sum, Fintype.card_fin]
    norm_num
  exact left_ne_zero_of_mul_eq_one h'

theorem symplForm4_map {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] :
    (symplForm4 F).map (algebraMap F K) = symplForm4 K := by
  have h : ((-1 : Matrix (Fin 2) (Fin 2) F)).map (algebraMap F K) = -1 := by
    rw [← RingHom.mapMatrix_apply, map_neg, map_one]
  simp [symplForm4, Matrix.fromBlocks_map, h]

theorem pGroup_sp4_abelian
    {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpℓ : ringChar F ≠ p)
    (H : Subgroup (CFSG.Assembly.LowTwoRank.StatedSp 2 F)) (hH : IsPGroup p ↥H) :
    ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := by
  classical
  have _ := hodd
  have hpK : ((p : ℕ) : AlgebraicClosure F) ≠ 0 :=
    natCast_algebraicClosure_ne_zero (Fact.out : p.Prime) hpℓ
  let ρ : ↥H →* (Module.End (AlgebraicClosure F) (Fin 2 ⊕ Fin 2 → AlgebraicClosure F))ˣ :=
    (glToEndUnits (ι := Fin 2 ⊕ Fin 2) (F := F) (AlgebraicClosure F)).comp
      ((StatedSp 2 F).subtype.comp H.subtype)
  have hρ : Function.Injective ρ :=
    (glToEndUnits_injective (AlgebraicClosure F)).comp
      (Subtype.coe_injective.comp Subtype.coe_injective)
  have hB : (Matrix.toBilin' (symplForm4 (AlgebraicClosure F))).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _ (det_symplForm4_ne_zero _)
  have hdim :
      Module.finrank (AlgebraicClosure F) (Fin 2 ⊕ Fin 2 → AlgebraicClosure F) < 2 * p := by
    rw [Module.finrank_fintype_fun_eq_card]
    have := (Fact.out : p.Prime).two_le
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hinv : ∀ (g : ↥H) (u v : Fin 2 ⊕ Fin 2 → AlgebraicClosure F),
      Matrix.toBilin' (symplForm4 (AlgebraicClosure F))
        ((ρ g : Module.End (AlgebraicClosure F) _) u)
        ((ρ g : Module.End (AlgebraicClosure F) _) v) =
      Matrix.toBilin' (symplForm4 (AlgebraicClosure F)) u v := by
    intro g u v
    have h := glToEndUnits_isometry (AlgebraicClosure F) (symplForm4 F)
      ((g : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F)
      (closure_isometry_mul_eq _ (g : ↥(StatedSp 2 F)).2) u v
    rwa [symplForm4_map] at h
  have hab := commute_of_pGroup_of_bilin hp2 hH hpK _ hB hdim ρ hρ hinv
  intro x hx y hy
  exact congrArg Subtype.val (hab ⟨x, hx⟩ ⟨y, hy⟩)

end Symplectic

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
