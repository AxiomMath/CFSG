module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc7b

public section

namespace CFSG.LocalAnalysis.Gross82.OrderThree

open Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7.LinearPSL
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7.UnitaryPSU

private theorem conjAut_mem_inner_of_fix_Rproj {F : Type} [Field F] [Finite F]
    {p m L' : ℕ} [Fact p.Prime] (hm : ¬ p ∣ m) (hL : Even L') (hL1 : 1 ≤ L')
    (hn : 3 ≤ m * (L' + 1)) {ζ : Fˣ} (hζ1 : ζ ≠ 1) (hζ2 : ζ ^ 2 ≠ 1) :
    ∀ A : GL (Fin (m * (L' + 1))) F,
      (∃ K : ℕ, conjAut _ F A ^ p ^ K = 1) →
      (∀ x ∈ Rproj ζ (cyc m (L' + 1)), conjAut _ F A x = x) →
      conjAut _ F A ∈ inner (projectiveSL (m * (L' + 1)) F) := by
  intro A hA hfixR
  obtain ⟨z, hz⟩ := det_eq_pow_of_fix hL hL1 hm hn hζ1 hζ2 A
    (fun i j _ => hfixR _ (proj_diagSL_mem_Rproj ζ _ _ _ (dij_mem_zpowers ζ i j)))
    (hfixR _ (proj_permSL_mem_Rproj ζ _ (sign_cyc m L' hL))) hA
  exact conjAut_mem_inner_of_det hz

theorem conjAut_mem_inner_of_fix_sylow
    {F : Type} [Field F] [Finite F] {n p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hn : 3 ≤ n) (hpn : p ∣ n) (hpq : p ∣ Nat.card F - 1)
    (P : Sylow p (projectiveSL n F)) (A : GL (Fin n) F)
    (hpow : ∃ k : ℕ, conjAut n F A ^ (p ^ k) = 1)
    (hfix : ∀ x ∈ (P : Subgroup (projectiveSL n F)), conjAut n F A x = x) :
    conjAut n F A ∈ inner (projectiveSL n F) := by
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p
    (by rw [Nat.card_units]; exact hpq)
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hζ
    exact hp.out.one_lt.ne hζ
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h2
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hζ] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h3)
  obtain ⟨m, L', v, rfl, hm, hL, hL1, hLv⟩ := exists_decomp hp.out hp2 (by omega) hpn
  have hσpow : cyc m (L' + 1) ^ (p ^ v) = 1 := by rw [← hLv]; exact cyc_pow_card m L'
  have hR := isPGroup_Rproj (F := F) hζp hσpow
  have hcore := conjAut_mem_inner_of_fix_Rproj hm hL hL1 hn hζ1 hζ2
  refine mem_inner_of_fix_sylow_of_hom (conjAut _ F) (fun g => ?_) hR hcore P A hpow hfix
  obtain ⟨g', rfl⟩ := proj_surjective _ F g
  exact ⟨SpecialLinearGroup.toGL g', conjAut_toGL g'⟩

theorem mem_inner_of_mem_range_conjAut_of_fix_sylow
    {F : Type} [Field F] [Finite F] {n p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hn : 3 ≤ n) (hpn : p ∣ n) (hpq : p ∣ Nat.card F - 1)
    (P : Sylow p (projectiveSL n F)) (α : MulAut (projectiveSL n F))
    (hdiag : α ∈ (conjAut n F).range) (hpow : ∃ k : ℕ, α ^ (p ^ k) = 1)
    (hfix : ∀ x ∈ (P : Subgroup (projectiveSL n F)), α x = x) :
    α ∈ inner (projectiveSL n F) := by
  obtain ⟨A, rfl⟩ := hdiag
  exact conjAut_mem_inner_of_fix_sylow hp2 hn hpn hpq P A hpow hfix

private theorem exists_mul_eq_smul_dij {ℓ f : ℕ} {F : Type} [Field F] {n : ℕ}
    (h : UnitaryFieldData ℓ f F) {ζ : Fˣ}
    (hzN : ∀ x ∈ Subgroup.zpowers ζ, h.norm (x : F) = 1) {σ : Equiv.Perm (Fin n)}
    {A : primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)}
    (hfixR : ∀ x ∈ RprojU h ζ σ,
      primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A x = x) :
    ∀ i j : Fin n, i ≠ j → ∃ c₀ : F,
      (((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          diagonal (fun k => (dij ζ i j k : F)) =
        c₀ • (diagonal (fun k => (dij ζ i j k : F)) *
          ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))) := by
  intro i j _
  have hN : ∀ k, h.norm (dij ζ i j k : F) = 1 := fun k => hzN _ (dij_mem_zpowers ζ i j k)
  exact exists_mul_eq_smul_of_fix h
    (hfixR _ (mk_dglHom_mem_RprojU h ζ σ (dij ζ i j) (prod_dij ζ i j) hN
      (dij_mem_zpowers ζ i j)))

private theorem exists_pow_eq_scalar {ℓ f : ℕ} {F : Type} [Field F] {n p : ℕ}
    [Fact p.Prime] (h : UnitaryFieldData ℓ f F) (hn : 3 ≤ n)
    {A : primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)}
    (hA : ∃ K : ℕ,
      primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A ^ p ^ K = 1) :
    ∃ (K : ℕ) (u : F),
      (((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ (p ^ K) = scalar (Fin n) u) := by
  obtain ⟨K, hK⟩ := hA
  have h1 : primeFormConjHom h _ (A ^ p ^ K) = 1 := by rw [map_pow, hK]
  obtain ⟨u, -, hu⟩ := eq_scalar_of_primeFormConjHom_eq_one h isPrimeFormGram_one hn h1
  exact ⟨K, u, by
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hu, GeneralLinearGroup.coe_scalar]⟩

private theorem primeFormConjHom_mem_inner_of_fix_RprojU {ℓ f : ℕ} {F : Type} [Field F]
    {m L' p : ℕ} [Fact p.Prime] (h : UnitaryFieldData ℓ f F)
    (hL : Even L') (hL1 : 1 ≤ L') (hm : ¬ p ∣ m) (hn : 3 ≤ m * (L' + 1))
    {ζ : Fˣ} (hζ1 : ζ ≠ 1) (hζ2 : ζ ^ 2 ≠ 1)
    (hzN : ∀ x ∈ Subgroup.zpowers ζ, h.norm (x : F) = 1) :
    ∀ A : primeFormUnitary h ((1 : GL (Fin (m * (L' + 1))) F) :
        Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F),
      (∃ K : ℕ, primeFormConjHom h ((1 : GL (Fin (m * (L' + 1))) F) :
        Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F) A ^ p ^ K = 1) →
      (∀ x ∈ RprojU h ζ (cyc m (L' + 1)), primeFormConjHom h
        ((1 : GL (Fin (m * (L' + 1))) F) :
        Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F) A x = x) →
      primeFormConjHom h ((1 : GL (Fin (m * (L' + 1))) F) :
        Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F) A ∈
        inner (primeFormP h ((1 : GL (Fin (m * (L' + 1))) F) :
          Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F)) := by
  intro A hA hfixR
  have hdet : (((A : GL (Fin (m * (L' + 1))) F) :
      Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F)).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hP' := exists_mul_eq_smul_of_fix h
    (hfixR _ (mk_permGL_mem_RprojU h ζ (cyc m (L' + 1)) (sign_cyc m L' hL)))
  obtain ⟨π, t, z, hfac, hzH, hz⟩ := det_eq_pow_of_matrix hL hL1 hm hn hζ1 hζ2 _
    hdet (exists_mul_eq_smul_dij h hzN hfixR) hP' (exists_pow_eq_scalar h hn hA)
  have htN : ∀ k, t k ∈ (Units.map h.normHom).ker := fun k =>
    (h.mem_ker_normUnits).2 (norm_eq_one_of_monomial h A.2 hfac k)
  have hzN' : h.norm (z : F) = 1 :=
    (h.mem_ker_normUnits).1 ((Subgroup.closure_le _).2 (Set.range_subset_iff.2 htN) hzH)
  exact primeFormConjHom_mem_inner_of_det h hzN' hz

theorem primeFormConjHom_mem_inner_of_fix_sylow {ℓ f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) {n p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hpn : p ∣ n) (hpq : p ∣ ℓ ^ f + 1)
    (P : Sylow p (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)))
    (A : primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (hpow : ∃ k : ℕ,
      primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A ^ (p ^ k) = 1)
    (hfix : ∀ x ∈ (P : Subgroup (primeFormP h ((1 : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F))),
      primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A x = x) :
    primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A ∈
      inner (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
  haveI := h.finite
  obtain ⟨ζ', hζ'⟩ := exists_prime_orderOf_dvd_card' (G := (Units.map h.normHom).ker) p
    (by rw [(unitary_field_norm h).2.2.1]; exact hpq)
  set ζ : Fˣ := (ζ' : Fˣ) with hζdef
  have hζ : orderOf ζ = p := by rw [hζdef, Subgroup.orderOf_coe, hζ']
  have hzN : ∀ x ∈ Subgroup.zpowers ζ, h.norm (x : F) = 1 := fun x hx =>
    (h.mem_ker_normUnits).1 ((Subgroup.zpowers_le.2 ζ'.2) hx)
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hζ
    exact hp.out.one_lt.ne hζ
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h2
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hζ] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h3)
  obtain ⟨m, L', v, rfl, hm, hL, hL1, hLv⟩ := exists_decomp hp.out hp2 (by omega) hpn
  have hσpow : cyc m (L' + 1) ^ (p ^ v) = 1 := by rw [← hLv]; exact cyc_pow_card m L'
  have hR := isPGroup_RprojU h hζp hσpow
  set c := primeFormConjHom h ((1 : GL (Fin (m * (L' + 1))) F) :
    Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F) with hcdef
  have hconj : ∀ g : primeFormP h ((1 : GL (Fin (m * (L' + 1))) F) :
      Matrix (Fin (m * (L' + 1))) (Fin (m * (L' + 1))) F),
      ∃ u, c u = MulAut.conj g := by
    intro g
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective g
    exact ⟨⟨s, s.2.1⟩, primeFormConjHom_eq_conj h _ s⟩
  exact mem_inner_of_fix_sylow_of_hom c hconj hR
    (primeFormConjHom_mem_inner_of_fix_RprojU h hL hL1 hm hn hζ1 hζ2 hzN) P A hpow hfix

theorem mem_inner_of_mem_primeFormD_of_fix_sylow {ℓ f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) {n p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hpn : p ∣ n) (hpq : p ∣ ℓ ^ f + 1)
    (P : Sylow p (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)))
    (α : MulAut (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)))
    (hdiag : α ∈ primeFormD h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (hpow : ∃ k : ℕ, α ^ (p ^ k) = 1)
    (hfix : ∀ x ∈ (P : Subgroup (primeFormP h ((1 : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F))), α x = x) :
    α ∈ inner (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
  obtain ⟨A, rfl⟩ := hdiag
  exact primeFormConjHom_mem_inner_of_fix_sylow h hp2 hn hpn hpq P A hpow hfix

end CFSG.LocalAnalysis.Gross82.OrderThree
