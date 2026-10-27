module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAutField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent
import CFSG.RankThree.PartOne.S11d.OutUnitary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.PartOne.OutStructure (Inn OutPChain OutPNice.toChain OutPChain.of_mulEquiv)

section Model

variable {ℓ f n : ℕ} {K : Type} [Field K]

private noncomputable def suProjEquiv (h : UnitaryFieldData ℓ f K) (hn : 1 ≤ n) :
    StatedProj (StatedSU n (ℓ ^ f) K) ≃*
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  (unitaryPSUEquiv h hn).symm.trans
    (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)) (by
      ext z
      constructor
      · rintro ⟨y, ⟨c, hcN, hcn, hy⟩, rfl⟩
        exact ⟨c, hcN, hcn, hy⟩
      · rintro ⟨c, hcN, hcn, hz⟩
        exact ⟨(MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)).symm z, ⟨c, hcN, hcn, hz⟩,
          MulEquiv.apply_symm_apply _ _⟩))

theorem not_dvd_card_suScalars (h : UnitaryFieldData ℓ f K) (hn : 1 ≤ n) {p : ℕ}
    (hdiag : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) :
    ¬ p ∣ Nat.card ↥((StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)) := by
  rw [← unitaryScalars_eq h hn, card_unitaryScalars h hn]
  exact hdiag

theorem unitForm_mulVec_mulVec (h : UnitaryFieldData ℓ f K) (N : Matrix (Fin n) (Fin n) K)
    (x y : Fin n → K) :
    Cls.unitForm h.bar (N *ᵥ x) (N *ᵥ y) = x ⬝ᵥ ((Nᵀ * N.map h.bar) *ᵥ (h.bar ∘ y)) := by
  rw [Cls.unitForm_apply]
  have hσy : h.bar ∘ (N *ᵥ y) = N.map h.bar *ᵥ (h.bar ∘ y) := by
    funext i
    exact RingHom.map_mulVec h.bar N y i
  rw [hσy, ← Matrix.vecMul_transpose N x, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

theorem transpose_mul_map_bar (h : UnitaryFieldData ℓ f K) {N : Matrix (Fin n) (Fin n) K}
    (hN : (N.map h.bar)ᵀ * N = 1) : Nᵀ * N.map h.bar = 1 := by
  have h3 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M.map h.bar) hN
  simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h3
  have hid : N.map (⇑h.bar ∘ ⇑h.bar) = N := by
    ext i j
    simp [h.bar_bar]
  rwa [hid, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)] at h3

theorem unitForm_mulVec_of_mem (h : UnitaryFieldData ℓ f K) {N : GL (Fin n) K}
    (hN : N ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (x y : Fin n → K) :
    Cls.unitForm h.bar ((N : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((N : Matrix (Fin n) (Fin n) K) *ᵥ y) = Cls.unitForm h.bar x y := by
  have h1 : ((N : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * N = 1 := by
    have := mem_primeFormUnitary.1 hN
    rwa [Units.val_one, Matrix.mul_one] at this
  rw [unitForm_mulVec_mulVec, transpose_mul_map_bar h h1, Matrix.one_mulVec, Cls.unitForm_apply]

theorem unitForm_map (h : UnitaryFieldData ℓ f K) (σ : K ≃+* K) (x y : Fin n → K) :
    Cls.unitForm h.bar (fun i => σ (x i)) (fun i => σ (y i)) = σ (Cls.unitForm h.bar x y) := by
  rw [Cls.unitForm_apply, Cls.unitForm_apply]
  simp only [dotProduct, Function.comp_apply, map_sum, map_mul, map_bar_comm]

theorem statedSU_le_isomGL (h : UnitaryFieldData ℓ f K) :
    StatedSU n (ℓ ^ f) K ≤ Cls.isomGL (Cls.unitForm (ι := Fin n) h.bar) := by
  intro g hg
  rw [Cls.mem_isomGL]
  have h1 := ((mem_unitarySU_iff h).1 hg).2
  intro x y
  rw [unitForm_mulVec_mulVec, transpose_mul_map_bar h h1, Matrix.one_mulVec, Cls.unitForm_apply]

theorem map_bar_transpose_mul_of_mem_isomGL (h : UnitaryFieldData ℓ f K) {g : GL (Fin n) K}
    (hg : g ∈ Cls.isomGL (Cls.unitForm (ι := Fin n) h.bar)) :
    ((g : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * g = 1 := by
  have hT : (g : Matrix (Fin n) (Fin n) K)ᵀ * (g : Matrix (Fin n) (Fin n) K).map h.bar = 1 := by
    rw [Matrix.ext_iff_mulVec]
    intro w
    have hw : w = h.bar ∘ (h.bar ∘ w) := by
      funext i
      simp [h.bar_bar]
    rw [Matrix.one_mulVec]
    apply dotProduct_eq
    intro x
    rw [dotProduct_comm, dotProduct_comm w]
    have := Cls.mem_isomGL.1 hg x (h.bar ∘ w)
    rw [unitForm_mulVec_mulVec, Cls.unitForm_apply] at this
    rw [hw]
    exact this
  have h3 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M.map h.bar) hT
  simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h3
  have hid : (g : Matrix (Fin n) (Fin n) K).map (⇑h.bar ∘ ⇑h.bar) = g := by
    ext i j
    simp [h.bar_bar]
  rwa [hid, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)] at h3

theorem exists_scalar_mul_mem_statedSU (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hdiag : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) {g : GL (Fin n) K}
    (hg : g ∈ Cls.isomGL (Cls.unitForm (ι := Fin n) h.bar)) (hgp : g ^ p = 1) :
    ∃ c : Kˣ, c ^ p = 1 ∧
      Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ Cls.isomGL (Cls.unitForm (ι := Fin n) h.bar) ∧
      Matrix.GeneralLinearGroup.scalar (Fin n) c * g ∈ StatedSU n (ℓ ^ f) K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hgg := map_bar_transpose_mul_of_mem_isomGL h hg
  set d : Kˣ := (Matrix.GeneralLinearGroup.det g)⁻¹ with hd
  have hdp : d ^ p = 1 := by rw [hd, inv_pow, ← map_pow, hgp, map_one, inv_one]
  have hN : h.bar (g : Matrix (Fin n) (Fin n) K).det * (g : Matrix (Fin n) (Fin n) K).det = 1 := by
    have h1 := congrArg Matrix.det hgg
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
    change (h.bar.mapMatrix (g : Matrix (Fin n) (Fin n) K)).det * _ = 1 at h1
    rwa [← RingHom.map_det] at h1
  have hdq : d ^ (ℓ ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hd, Units.val_inv_eq_inv_val,
      Matrix.GeneralLinearGroup.val_det_apply, inv_pow, pow_succ, ← h.bar_apply, hN, inv_one,
      Units.val_one]
  have hscal : ∀ c : Kˣ, c ^ (ℓ ^ f + 1) = 1 →
      Matrix.GeneralLinearGroup.scalar (Fin n) c ∈
        Cls.isomGL (Cls.unitForm (ι := Fin n) h.bar) := by
    intro c hc
    rw [Cls.mem_isomGL]
    intro x y
    have hv : ∀ v : Fin n → K,
        (Matrix.scalar (Fin n) (c : K)) *ᵥ v = fun i => (c : K) * v i := fun v => by
      funext i
      rw [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    rw [Matrix.GeneralLinearGroup.coe_scalar, hv, hv, Cls.unitForm_apply, Cls.unitForm_apply]
    have hcc : (c : K) * h.bar (c : K) = 1 := by
      rw [h.bar_apply, ← pow_succ', ← Units.val_pow_eq_pow_val, hc, Units.val_one]
    simp only [dotProduct, Function.comp_apply, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    calc (c : K) * x i * (h.bar (c : K) * h.bar (y i))
        = ((c : K) * h.bar (c : K)) * (x i * h.bar (y i)) := by ring
      _ = x i * h.bar (y i) := by rw [hcc, one_mul]
  have hmem : ∀ c : Kˣ, c ^ (ℓ ^ f + 1) = 1 → c ^ n = d →
      Matrix.GeneralLinearGroup.scalar (Fin n) c * g ∈ StatedSU n (ℓ ^ f) K := by
    intro c hc hcn
    refine (mem_unitarySU_iff h).2 ⟨?_, ?_⟩
    · rw [Units.val_mul, Matrix.det_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← Units.val_pow_eq_pow_val, hcn, hd]
      change (((Matrix.GeneralLinearGroup.det g)⁻¹ : Kˣ) : K) *
        ((Matrix.GeneralLinearGroup.det g : Kˣ) : K) = 1
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    · have hcc : h.bar (c : K) * (c : K) = 1 := by
        rw [h.bar_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, hc, Units.val_one]
      rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
        Matrix.map_smul' _ _ _ (map_mul h.bar), Matrix.transpose_smul, Matrix.smul_mul,
        Matrix.mul_smul, hgg, smul_smul, hcc, one_smul]
  by_cases hd1 : d = 1
  · refine ⟨1, one_pow p, hscal 1 (one_pow _), hmem 1 (one_pow _) ?_⟩
    rw [one_pow, hd1]
  · have hdo : orderOf d = p := orderOf_eq_prime hdp hd1
    have hpq : p ∣ ℓ ^ f + 1 := hdo ▸ orderOf_dvd_of_pow_eq_one hdq
    have hpn : ¬ p ∣ n := fun hpn => hdiag (Nat.dvd_gcd hpn hpq)
    have hcop : Nat.Coprime n p := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn))
    obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have hdu : (d ^ u) ^ (ℓ ^ f + 1) = 1 := by
      obtain ⟨k, hk⟩ := hpq
      rw [← pow_mul, hk, show u * (p * k) = p * (u * k) by ring, pow_mul, hdp, one_pow]
    refine ⟨d ^ u, by rw [← pow_mul, mul_comm, pow_mul, hdp, one_pow], hscal _ hdu,
      hmem _ hdu ?_⟩
    rw [← pow_mul, mul_comm, ← pow_mod_orderOf, hdo, hu, pow_one]

end Model

section Field

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} [S.Normal]
variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem outPChain_uni (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hp : p.Prime) (hdiag : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    (e : ↥S ≃* StatedProj (StatedSU n (ℓ ^ f) K)) : OutPChain p ↥S :=
  (CFSG.RankThree.PartOne.OutStructure.outPNice_primeFormP h hn hq hp hdiag).toChain.of_mulEquiv
    (e.trans (suProjEquiv h (by omega)))

theorem exists_fieldAct_uni (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) (hpℓ : p ≠ ℓ)
    (hdiag : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) (φ : ↥(StatedSU n (ℓ ^ f) K) →* Ω)
    (hφS : φ.range = S)
    (hφk : φ.ker = (StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)) {b : Ω}
    (hbp : b ^ p = 1) (hbN : b ∉ S ⊔ Subgroup.centralizer (S : Set Ω)) :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K),
      A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      FieldAct p φ b A σ ∧ FormRel (Cls.unitForm (ι := Fin n) h.bar) A σ := by
  haveI : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  set e : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≃* ↥S :=
    (suProjEquiv h (by omega)).symm.trans (coverProjEquiv φ hφS hφk) with he
  set γ := transAut e b with hγ
  have hγo : orderOf γ = p := orderOf_transAut_eq e hp hbp hbN
  have hγp : γ ^ p = 1 := by rw [← hγo]; exact pow_orderOf_eq_one γ
  obtain ⟨-, -, -, -, -, -, -, hFker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order h hn hq
  set σ := primeFormFieldFactor h hC hn hq γ with hσ
  have hσp : σ ^ p = 1 := by rw [hσ, ← map_pow, hγp, map_one]
  have hσ1 : σ ≠ 1 := by
    intro hσ1
    have hγD : γ ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← hFker, MonoidHom.mem_ker]
      exact hσ1
    have hcop : Nat.Coprime ((Inn (primeFormP h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K))).relIndex
        (primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) p := by
      rw [Subgroup.relIndex, Subgroup.index_eq_card, hcard]
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hdiag)
    exact hbN ((transAut_mem_inner_iff e b).1 (mem_of_pow_mem_of_coprime _ hγD
      (by rw [hγp]; exact one_mem _) hcop))
  have hσo : orderOf σ = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hσp hσ1
  obtain ⟨hpf, hcardK0, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hq hp hp2 hpℓ γ
      hγo σ rfl hσo
  have hγeq : γ =
      primeFormConjHom h _ M * primeFormFieldHom h hC σ * (primeFormConjHom h _ M)⁻¹ := by
    rw [← hM]
    group
  refine ⟨M, σ, M.2, ⟨hσo, ?_, fun k => ?_⟩, ⟨1, fun u v => ?_⟩⟩
  ·
    rw [hcardK0, h.card, ← pow_mul, ← pow_mul]
    congr 1
    obtain ⟨m, rfl⟩ := hpf
    rw [Nat.mul_div_cancel_left m hp.pos]
    ring
  ·
    set kg : ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n) k with hkg
    set g' : ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      primeFormConjSU h _ M (primeFormFieldSU h hC σ (primeFormConjSU h _ M⁻¹ kg)) with hg'
    refine ⟨(MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)).symm g', ?_, ?_⟩
    · rw [semiConj_apply]
      change (M : GL (Fin n) K) * glAut σ (((M⁻¹ : primeFormUnitary h _) : GL (Fin n) K) *
        (k : GL (Fin n) K) * ((M⁻¹ : primeFormUnitary h _) : GL (Fin n) K)⁻¹) *
        (M : GL (Fin n) K)⁻¹ = _
      rw [Subgroup.coe_inv, inv_inv]
      rfl
    · have h1 : γ (QuotientGroup.mk kg) = QuotientGroup.mk g' := by
        rw [hγeq, MulAut.mul_apply, MulAut.mul_apply, ← map_inv, primeFormConjHom_mk]
        rfl
      have h2 := transAut_spec e b (QuotientGroup.mk kg)
      rw [← hγ, h1] at h2
      exact h2
  ·
    rw [Units.val_one, one_mul, one_mul, semiMap_apply, semiMap_apply, unitForm_mulVec_of_mem h M.2,
      unitForm_map, unitForm_mulVec_of_mem h (inv_mem M.2)]

theorem exists_clsData_uni (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hZ : Subgroup.center ↥S = ⊥) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) (hpℓ : p ≠ ℓ) (hdiag : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    (e : PSimple p S ≃* StatedProj (StatedSU n (ℓ ^ f) K)) {B : Subgroup Ω}
    (hB : IsElemAbelian p B) :
    ∃ φ : ↥(StatedSU n (ℓ ^ f) K) →* Ω, φ.range = S ∧
      φ.ker = (StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K) ∧
      ¬ p ∣ Nat.card φ.ker ∧
      ∃ θ : ↥(B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω))) →* ↥(StatedSU n (ℓ ^ f) K),
        (∀ x, (φ (θ x))⁻¹ * (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        IsElemAbelian p θ.range ∧ θ.range ⊓ φ.ker = ⊥ ∧
        (∀ x, θ x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        (B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = B ∨
          ∃ b ∈ B, b ∉ S ⊔ Subgroup.centralizer (S : Set Ω) ∧
            B = B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) ⊔ Subgroup.zpowers b ∧
            Subgroup.zpowers b ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = ⊥ ∧
            ∃ (A : GL (Fin n) K) (σ : K ≃+* K),
              A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
              FieldAct p φ b A σ ∧ FormRel (Cls.unitForm (ι := Fin n) h.bar) A σ ∧
              ∀ x, semiConj A σ ((θ x : ↥(StatedSU n (ℓ ^ f) K)) : GL (Fin n) K) = θ x) := by
  haveI : Finite K := h.finite
  obtain ⟨φ, hφS, hφk⟩ := exists_cover_of_center_eq_bot hcore hZ e
  have hker : φ.ker ≤ Subgroup.center ↥(StatedSU n (ℓ ^ f) K) :=
    hφk ▸ CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  have hC : ¬ p ∣ Nat.card φ.ker := hφk ▸ not_dvd_card_suScalars h (by omega) hdiag
  obtain ⟨θ, hθ, hθel, hθk, hθ1⟩ := exists_inner_lift hp hB hZ φ hφS hker hC
  have hOut : OutPChain p ↥S :=
    outPChain_uni h hn hq hp hdiag (coverProjEquiv φ hφS hφk).symm
  refine ⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, ?_⟩
  rcases inner_split' hp hB hOut with h' | ⟨b, hb, hbN, hBb, hbinf⟩
  · exact Or.inl h'
  · right
    obtain ⟨A, σ, hA, hact, hform⟩ :=
      exists_fieldAct_uni h hp hp2 hn hq hpℓ hdiag φ hφS hφk (hB.2 b hb) hbN
    exact ⟨b, hb, hbN, hBb, hbinf, A, σ, hA, hact, hform, semiConj_eq_of_fieldAct hp hZ φ hφS
      hker hC hB inf_le_left θ hθ (fun x => hθel.2 _ ⟨x, rfl⟩) hb hact⟩

end Field

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
