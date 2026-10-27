module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLSU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open scoped IsMulCommutative

section Family

variable {K : Type} [Field K] {ℓ f : ℕ}

theorem blkFacts_unitForm (h : UnitaryFieldData ℓ f K) (hℓ2 : ℓ ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {n : ℕ} [Nonempty (Fin n)] :
    ∀ U W : Submodule K (Fin n → K), IsCompl U W →
      (∀ u ∈ U, ∀ w ∈ W, unitForm (ι := Fin n) h.bar u w = 0 ∧ unitForm h.bar w u = 0) →
      (unitForm (ι := Fin n) h.bar = 0 ∨ ∀ u ∈ U, (∀ u' ∈ U, unitForm h.bar u u' = 0) → u = 0) →
      (3 ≤ Module.finrank K U ∨ (Module.finrank K U = 2 ∧ ℓ ^ f ≠ 3)) →
      blkI (unitForm (ι := Fin n) h.bar) U W ≤ StatedSU n (ℓ ^ f) K ∧
      CFSG.Open.IsQuasisimple ↥(blkI (unitForm (ι := Fin n) h.bar) U W) ∧
      (∀ x ∈ blkSub (unitForm (ι := Fin n) h.bar) U W, orderOf x = p →
        p ∣ Nat.card ↥(blkI (unitForm (ι := Fin n) h.bar) U W)) ∧
      (∀ y : GL (Fin n) K, (∀ u ∈ U, glEquiv y u ∈ U) →
        (∀ j ∈ blkI (unitForm (ι := Fin n) h.bar) U W, y * j = j * y) →
        ∃ c : K, ∀ u ∈ U, glEquiv y u = c • u) ∧
      (∀ (A : GL (Fin n) K) (σ : K ≃+* K), orderOf σ = p →
        (∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) →
        ∀ y : GL (Fin n) K, (∀ u ∈ U, glEquiv y u ∈ U) → ∀ k : ℕ, 0 < k → k < p →
          ¬ ∀ j ∈ blkI (unitForm (ι := Fin n) h.bar) U W,
            y * (ModelGen.semiConj A σ ^ k) j * y⁻¹ = j) := by
  intro U W hUW horth hnd hdim
  have hnd' := hnd.resolve_left (unitForm_ne_zero h.bar)
  have hSU : CFSG.ClassicalGroups.UnitaryFlag.gramSU h (1 : Matrix (Fin n) (Fin n) K) =
      StatedSU n (ℓ ^ f) K := (CFSG.ClassicalGroups.UnitaryFlag.unitarySU_eq_gramSU h n).symm
  exact ⟨hSU ▸ blkI_le_gramSU h U W, isQuasisimple_blkI_unitForm h hℓ2 hUW horth hnd' hdim,
    fun x hx hxp => dvd_card_blkI_unitForm h hℓ2 hUW horth hnd' hdim hp hx hxp,
    fun y hyU hy => exists_smul_of_commute_blkI_unitForm h hℓ2 hUW horth hnd' hdim hyU hy,
    fun A σ hσ hU y hyU k hk0 hkp =>
      not_forall_semiConj_pow_unitForm h hℓ2 hUW horth hnd' hdim hp hp2 hσ hU hyU hk0 hkp⟩

theorem finrank_weightSpace_eq_one_unitForm (h : UnitaryFieldData ℓ f K) (h2K : (2 : K) ≠ 0)
    {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0) {n : ℕ} [NeZero n] :
    ∀ (Aε : Subgroup (GL (Fin n) K)) [IsMulCommutative Aε], (∀ a : ↥Aε, a ^ p = 1) →
      Aε ≤ isomGL (unitForm (ι := Fin n) h.bar) →
      IsMaxElem (unitForm (ι := Fin n) h.bar) (glRep Aε) p ∅ →
      (∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧ Matrix.GeneralLinearGroup.scalar (Fin n) c ∈
        isomGL (unitForm (ι := Fin n) h.bar)) →
      ∀ H' : Hyperplane ↥Aε p, weightSpace (glRep Aε) H'.1 ≠ ⊥ →
        Module.finrank K (weightSpace (glRep Aε) H'.1) = 1 := by
  classical
  intro Aε _ hA hAεβ hmax ⟨c, hc1, hcp, hcβ⟩ H' hH'
  haveI : Finite K := h.finite
  haveI : Fintype K := Fintype.ofFinite K
  haveI := Fact.mk hp
  have hd : p ∣ ℓ ^ f + 1 := by
    rw [← orderOf_eq_prime hcp hc1]
    exact orderOf_dvd_of_pow_eq_one (pow_succ_eq_one_of_scalar_mem h hcβ)
  have hσp : ∀ c' : K, c' ^ p = 1 → c' * h.bar c' = 1 := by
    intro c' hc'
    rw [UnitaryFieldData.bar_apply, ← pow_succ']
    obtain ⟨k, hk⟩ := hd
    rw [hk, pow_mul, hc', one_pow]
  have hq : p ∣ Fintype.card K - 1 := by
    rw [← Nat.card_eq_fintype_card, h.card, pow_mul', sq]
    have h1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
    have : ℓ ^ f * ℓ ^ f - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
      zify [h1, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega) :
        ℓ ^ f * ℓ ^ f ≠ 0)]
      ring
    rw [this]
    exact Dvd.dvd.mul_right hd _
  exact finrank_weightSpace_eq_one_uni (unitForm (ι := Fin n) h.bar) (glRep Aε) hp hA hpK
    (isIsomRep_glRep hAεβ) (fun u v => (unitForm_swap h.bar_bar u v).symm) hσp h2K
    (unitForm_separatingLeft h.bar) hmax hq H' hH'

end Family

section CaseL

abbrev ConcACaseLLUStatement : Prop :=
  ∀ {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} {n : ℕ}, 5 ≤ n →
    ∀ {K : Type} [Field K] [Finite K] {τ : K →+* K}, p.Prime → ∀ [S.Normal],
    IsElemAbelian p B → p ^ 4 ≤ Nat.card B → Nat.card ↥(B ⊓ centModSubgroup p S) = p →
    GLAPPrimeCore p ↥S = ⊥ → (2 : K) ≠ 0 → (p : K) ≠ 0 →
    ∀ {H : Subgroup (GL (Fin n) K)} {β : (Fin n → K) →ₗ[K] (Fin n → K) →ₛₗ[τ] K},
    H ≤ isomGL β → (β = 0 ∨ β.SeparatingLeft) →
    (∀ g ∈ isomGL β, (g : Matrix (Fin n) (Fin n) K).det = 1 → g ∈ H) →
    (∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧ Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ isomGL β) →
    ∀ {Qbig : Prop}, Qbig →
    (∀ U W : Submodule K (Fin n → K), IsCompl U W →
      (∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0) →
      (β = 0 ∨ ∀ u ∈ U, (∀ u' ∈ U, β u u' = 0) → u = 0) →
      (3 ≤ Module.finrank K U ∨ (Module.finrank K U = 2 ∧ Qbig)) →
      blkI β U W ≤ H ∧ CFSG.Open.IsQuasisimple ↥(blkI β U W) ∧
      (∀ x ∈ blkSub β U W, orderOf x = p → p ∣ Nat.card ↥(blkI β U W)) ∧
      (∀ y : GL (Fin n) K, (∀ u ∈ U, glEquiv y u ∈ U) → (∀ j ∈ blkI β U W, y * j = j * y) →
        ∃ c : K, ∀ u ∈ U, glEquiv y u = c • u) ∧
      (∀ (A : GL (Fin n) K) (σ : K ≃+* K), orderOf σ = p →
        (∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) →
        ∀ y : GL (Fin n) K, (∀ u ∈ U, glEquiv y u ∈ U) → ∀ k : ℕ, 0 < k → k < p →
          ¬ ∀ j ∈ blkI β U W, y * (ModelGen.semiConj A σ ^ k) j * y⁻¹ = j)) →
    (∀ (Aε : Subgroup (GL (Fin n) K)) [IsMulCommutative Aε], (∀ a : ↥Aε, a ^ p = 1) →
      Aε ≤ isomGL β → IsMaxElem β (glRep Aε) p ∅ →
      (∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧ Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ isomGL β) →
      ∀ H' : Hyperplane ↥Aε p, weightSpace (glRep Aε) H'.1 ≠ ⊥ →
        Module.finrank K (weightSpace (glRep Aε) H'.1) = 1) →
    ∀ (φ : ↥H →* Ω), φ.range = S → φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf H →
    ∀ {B₁ : Subgroup Ω} (θ : ↥B₁ →* GL (Fin n) K), B₁ ≤ B →
    B ⊓ Subgroup.centralizer (S : Set Ω) ≤ B₁ → θ.range ≤ isomGL β →
    IsElemAbelian p θ.range → θ.range ⊓ StatedScalars (Fin n) K = ⊥ →
    (∀ x : ↥B₁, θ x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) →
    (∀ (x : ↥B₁) (k : ↥H), ∃ k' : ↥H,
      (k' : GL (Fin n) K) = θ x * k * (θ x)⁻¹ ∧ φ k' = x * φ k * x⁻¹) →
    p ^ (n - 2) ≤ Nat.card θ.range →
    (B₁ = B ∨ ∃ b ∈ B, b ∉ B₁ ∧ B = B₁ ⊔ Subgroup.zpowers b ∧
      Subgroup.zpowers b ⊓ B₁ = ⊥ ∧ ∃ (A : GL (Fin n) K) (σ : K ≃+* K),
        ModelGen.FieldAct p φ b A σ ∧ ModelGen.FormRel β A σ ∧
        ∀ x : ↥B₁, ModelGen.semiConj A σ (θ x) * (θ x)⁻¹ ∈ StatedScalars (Fin n) K) →
    S267ConcA p S B

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_caseL_uni (hLU : ConcACaseLLUStatement)
    (hp : p.Prime) (hp2 : p ≠ 2)
    [hSn : S.Normal] (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B)
    (h4 : p ^ 4 ≤ Nat.card B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    (hp3B : ¬ (p = 3 ∧ Nat.card B = 3 ^ 4)) {n : ℕ} (hn : 3 ≤ n) {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hℓ2 : ℓ ≠ 2) (hdiag : p ∣ Nat.gcd n (ℓ ^ f + 1))
    (e : PSimple p S ≃* StatedProj (StatedSU n (ℓ ^ f) K)) : S267ConcA p S B := by
  classical
  haveI : Finite K := h.finite
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI : CharP K ℓ := h.charP
  haveI : Fact p.Prime := ⟨hp⟩
  have hℓ := h.prime
  have hpq : p ∣ ℓ ^ f + 1 := hdiag.trans (Nat.gcd_dvd_right _ _)
  have hpn : p ∣ n := hdiag.trans (Nat.gcd_dvd_left _ _)
  have hp4 : ¬ p ∣ 4 := fun hd4 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
    (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from hd4)))
  have hpℓ : p ≠ ℓ := by
    rintro rfl
    have h1 : p ∣ p ^ f := dvd_pow_self p (by have := h.one_le; omega)
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 hpq))
  have hcharne : ∀ m : ℕ, m.Prime → m ≠ ℓ → (m : K) ≠ 0 := by
    intro m hm hmℓ h0
    exact hmℓ ((Nat.prime_dvd_prime_iff_eq hℓ hm).1 ((CharP.cast_eq_zero_iff K ℓ m).1 h0)).symm
  have h2K : (2 : K) ≠ 0 := by exact_mod_cast hcharne 2 Nat.prime_two (Ne.symm hℓ2)
  have hpK : (p : K) ≠ 0 := hcharne p hp hpℓ
  rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | hn4
  ·
    exfalso
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpn
    have hle := ModelGen.card_le_of_caseL_uni hp hp2 hperf hcore le_rfl h hℓ2 hdiag e hB hBC
    subst hp3
    exact hp3B ⟨rfl, le_antisymm hle h4⟩
  · have hn5 : 5 ≤ n := by
      by_contra h5
      exact hp4 (by rwa [show n = 4 by omega] at hpn)
    obtain ⟨φ, hφS, hφk, B₁, θ, hB₁B, hB₀B₁, hθβ, hθel, hθZ, hθ1, hθact, hθc, hsplit⟩ :=
      ModelGen.exists_caseLData_uni hp hp2 hperf hcore hn4 h hℓ2 hdiag e hB hBC hrank
    have hsc : ∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧
        Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ isomGL (unitForm (ι := Fin n) h.bar) := by
      have hpK' : p ∣ Nat.card Kˣ := by
        rw [Nat.card_units, h.card, mul_comm 2 f, pow_mul]
        have h1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
        have : (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
          zify [h1, Nat.one_le_pow 2 (ℓ ^ f) h1]
          ring
        rw [this]
        exact Dvd.dvd.mul_right hpq _
      obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hpK'
      have hcp : c ^ p = 1 := hc ▸ pow_orderOf_eq_one c
      refine ⟨c, fun h1 => ?_, hcp, ModelGen.unitaryI_le_isomGL h
        (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.scalar_mem_primeFormUnitary_one h ?_)⟩
      · rw [h1, orderOf_one] at hc
        exact hp.one_lt.ne hc
      · obtain ⟨k, hk⟩ := hpq
        rw [UnitaryFieldData.norm, h.bar_apply, ← pow_succ', hk, pow_mul,
          ← Units.val_pow_eq_pow_val, hcp, Units.val_one, one_pow]
    have hQ : ℓ ^ f ≠ 3 := fun h3 => hp4 (by rw [h3] at hpq; exact hpq)
    exact hLU hn5 hp hB h4 hBC hcore h2K hpK (ModelGen.statedSU_le_isomGL h)
      (Or.inr (unitForm_separatingLeft h.bar))
      (fun g hg hdet => (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).2
        ⟨hdet, ModelGen.map_bar_transpose_mul_of_mem_isomGL h hg⟩)
      hsc hQ (blkFacts_unitForm h hℓ2 hp hp2) (finrank_weightSpace_eq_one_unitForm h h2K hp hpK)
      φ hφS hφk θ hB₁B hB₀B₁ hθβ hθel hθZ hθ1 hθact hθc hsplit

end CaseL

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls

end
