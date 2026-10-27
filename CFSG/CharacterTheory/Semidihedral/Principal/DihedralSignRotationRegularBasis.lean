module

public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralPrincipalBlockExhaustion
public import CFSG.CharacterTheory.Semidihedral.Principal.LinearTwistBlocks
public import CFSG.CharacterTheory.Wreathed.CentralSylowPowerQuotients

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

theorem rotation_mem_centralInvolutionSection {S : Type*} [Group S] [Finite S] {r s : S}
    {n M : ℕ} (hn : 2 ≤ n) (hM : M = 2 ^ (n - 1)) (hcard : Nat.card S = 2 * M)
    (hgen : Subgroup.closure {r, s} = ⊤) (hr : orderOf r = M) (hs : orderOf s = 2)
    (hrel : s * r * s = r⁻¹) (ht : r ^ (M / 2) ∈ Subgroup.center S) (j : ℕ) (hj1 : 1 ≤ j)
    (hjM : j < M) : r ^ j ∈ centralInvolutionSection (r ^ (M / 2)) := by
  have hD := mem_centralInvolutionSection_iff_retraction (ι := MonoidHom.id S) (R := ⊥)
    (π := MonoidHom.id S) hn hM hcard hgen hr hs hrel (by simp) ht
    (by rw [MonoidHom.ker_id]) (by ext; rfl) (r ^ j)
  simp only [MonoidHom.id_apply] at hD
  rw [hD]
  refine ⟨Subgroup.npow_mem_zpowers r j, ?_⟩
  exact pow_ne_one_of_lt_orderOf (by omega) (by rw [hr]; exact hjM)

@[expose] def dihedralRegularRows (e : ℤ) (h : ℕ) : Matrix (Fin 4 ⊕ Fin h) (Fin 2) ℤ :=
  Matrix.of fun i j => Sum.elim (fun i : Fin 4 => ![![1, 0], ![1, 0], ![-e, e], ![-e, e]] i)
    (fun _ : Fin h => ![0, e]) i j

theorem dihedralRegularRows_gram (e : ℤ) (he : e = 1 ∨ e = -1) (h : ℕ) :
    (dihedralRegularRows e h).transpose * dihedralRegularRows e h =
      !![4, -2; -2, (h : ℤ) + 2] := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dihedralRegularRows, Matrix.of_apply,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_four, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases he with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp <;> ring

open CFSG.Wreathed in
theorem dihedral_sign_and_constant_rotation_character_regular_basis {G : Type} [Group G]
    [Fintype G] (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {n M : ℕ} (hn : 3 ≤ n)
    (hM : M = 2 ^ (n - 1)) (S : Sylow 2 G) (r s : (S : Subgroup G)) (hr : orderOf r = M)
    (hs : orderOf s = 2) (hrel : s * r * s = r⁻¹) (hgen : Subgroup.closure {r, s} = ⊤)
    (hcard : Nat.card (S : Subgroup G) = 2 * M) (basis : FiniteIrreducibleCharacterBasis G)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (lam : G →* ℂˣ) (hlam2 : ∀ g, lam g ^ 2 = 1) (hlamr : (lam (r : G) : ℂ) = -1)
    (β : basis.index)
    (hβ : β ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) (q : ℕ)
    (hq : (basis.representation β).character 1 = q) (hqodd : Odd q) (hq1 : 1 < q) (e : ℤ)
    (he : e = 1 ∨ e = -1)
    (hβr : ∀ j : ℕ, 1 ≤ j → j < M → (basis.representation β).character ((r : G) ^ j) = e)
    (hlamβ : (fun g => (lam g : ℂ) * (basis.representation β).character g) ≠
      (basis.representation β).character)
    (hy₀ : ∃ y₀ : G, Odd (orderOf y₀) ∧ (basis.representation β).character y₀ ≠ q) :
    ∃ (labelLam labelLamβ : basis.index) (ψ : Fin (M / 2 - 1) → basis.index),
      (basis.representation labelLam).character = (fun g => (lam g : ℂ)) ∧
      (basis.representation labelLamβ).character =
        (fun g => (lam g : ℂ) * (basis.representation β).character g) ∧
      Function.Injective ψ ∧
      principal ≠ labelLam ∧ principal ≠ β ∧ principal ≠ labelLamβ ∧ labelLam ≠ β ∧
      labelLam ≠ labelLamβ ∧ β ≠ labelLamβ ∧
      (∀ k, ψ k ≠ principal ∧ ψ k ≠ labelLam ∧ ψ k ≠ β ∧ ψ k ≠ labelLamβ) ∧
      (∀ ℓ, ℓ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔
        ℓ = principal ∨ ℓ = labelLam ∨ ℓ = β ∨ ℓ = labelLamβ ∨ ∃ k, ℓ = ψ k) ∧
      Module.finrank ℂ (basis.representation principal).vector = 1 ∧
      Module.finrank ℂ (basis.representation labelLam).vector = 1 ∧
      Module.finrank ℂ (basis.representation β).vector = q ∧
      Module.finrank ℂ (basis.representation labelLamβ).vector = q ∧
      (∀ k, (Module.finrank ℂ (basis.representation (ψ k)).vector : ℤ) = q + e) ∧
      (∀ k (y : G), Odd (orderOf y) →
        (basis.representation (ψ k)).character y = (basis.representation β).character y + e) ∧
      (∀ ℓ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        Odd (Module.finrank ℂ (basis.representation ℓ).vector) ↔
          ℓ = principal ∨ ℓ = labelLam ∨ ℓ = β ∨ ℓ = labelLamβ) ∧
      LinearIndependent ℤ ![oddRestriction (1 : G → ℂ),
        oddRestriction (1 + (e : ℂ) • (basis.representation β).character)] ∧
      Submodule.span ℤ {oddRestriction (1 : G → ℂ),
          oddRestriction (1 + (e : ℂ) • (basis.representation β).character)} =
        oddRestrictionLattice basis
          (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) ∧
      LinearIndependent ℤ ![oddRestriction (1 : G → ℂ),
        oddRestriction (basis.representation β).character] ∧
      Submodule.span ℤ {oddRestriction (1 : G → ℂ),
          oddRestriction (basis.representation β).character} =
        oddRestrictionLattice basis
          (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) ∧
      (∀ i : Fin 4 ⊕ Fin (M / 2 - 1),
        oddRestriction (basis.representation
            (Sum.elim ![principal, labelLam, β, labelLamβ] ψ i)).character =
          dihedralRegularRows e (M / 2 - 1) i 0 • oddRestriction (1 : G → ℂ) +
            dihedralRegularRows e (M / 2 - 1) i 1 •
              oddRestriction (1 + (e : ℂ) • (basis.representation β).character)) ∧
      (dihedralRegularRows e (M / 2 - 1)).transpose * dihedralRegularRows e (M / 2 - 1) =
        !![4, -2; -2, ((M / 2 + 1 : ℕ) : ℤ)] := by
  have hn2 : 2 ≤ n := by omega
  have hM4 : 4 ≤ M := by
    rw [hM]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hM2 : 2 ≤ M := by omega
  have hhalf : M / 2 = 2 ^ (n - 2) := by
    rw [hM, show n - 1 = (n - 2) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  have hhalfeven : Even (M / 2) := by
    rw [hhalf]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hrM : r ^ M = 1 := hr ▸ pow_orderOf_eq_one r
  have hss : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs, sq] at h
    exact h
  obtain ⟨eS, -, -⟩ := exists_dihedral_mulEquiv hM2 hcard hgen hrM hss hrel
  have hSiso : Nonempty (DihedralGroup M ≃* (S : Subgroup G)) := ⟨eS⟩
  have hstruct := (dihedral_rotation_involution_structure (S := (S : Subgroup G)) hn2
    (hM ▸ hSiso)).2 r s (hM ▸ hr) hs hrel hgen
  have htS : r ^ (M / 2) ∈ Subgroup.center (S : Subgroup G) := by
    rw [hhalf]
    exact hstruct.2.2.2.2.2.1
  set t : G := ((r ^ (M / 2) : (S : Subgroup G)) : G) with htdef
  obtain ⟨⟨R, ⟨hRn, hRodd, hRidx⟩, -⟩, hall⟩ :=
    dihedral_principal_block_exhaustion_and_section_values ideal hn2 hM S hSiso r s hr hs hrel
      hgen t rfl (Subgroup.centralizer {t}) rfl basis principal hprincipal
  obtain ⟨⟨π, ⟨hker, hid⟩, -⟩, hπall⟩ := hall R hRn hRodd hRidx
  obtain ⟨χ₁, χ₂, χ₃, δ₁, δ₂, δ₃, ε, ψ, h12, h13, h23, h1, h2, h3, hδ₁, hδ₂, hδ₃, hε, hψinj,
    hψne, -, -, himage, -, hsecvals, -, -, hχt3, hψt, hodd⟩ := hπall π hker hid
  have hSC : (S : Subgroup G) ≤ Subgroup.centralizer {t} := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff, htdef]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp htS ⟨y, hy⟩)
  have hrotD : ∀ j : ℕ, 1 ≤ j → j < M →
      ((r ^ j : (S : Subgroup G)) : G) ∈ centralInvolutionSection t := by
    intro j hj1 hjM
    have h := rotation_mem_centralInvolutionSection hn2 hM hcard hgen hr hs hrel htS j hj1 hjM
    exact (mem_centralInvolutionSection_subgroup_iff _ _).mp h
  obtain ⟨-, -, -, -, -, -, -, -, hφval, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    dihedral_explicit_character_family hM2 (by rw [hM]; exact Nat.even_pow.mpr ⟨even_two,
      by omega⟩) hcard hgen hr hs hrel
  have hφrot : ∀ (i : Fin 4) (j : ℕ),
      dihedralLinearCharacter r s M i (r ^ j) = dihedralRotationSign i ^ j := by
    intro i j
    have h := (hφval i (j : ℤ)).1
    rwa [zpow_natCast, zpow_natCast] at h
  have hval : ∀ j : ℕ, 1 ≤ j → j < M →
      (χ₁ : G → ℂ) ((r : G) ^ j) = δ₁ ∧ (χ₂ : G → ℂ) ((r : G) ^ j) = -δ₂ * (-1) ^ j ∧
        (χ₃ : G → ℂ) ((r : G) ^ j) = -δ₃ * (-1) ^ j := by
    intro j hj1 hjM
    obtain ⟨hv1, hv2, hv3, -⟩ := hsecvals ⟨((r ^ j : (S : Subgroup G)) : G), hSC (r ^ j).2⟩
      (hrotD j hj1 hjM)
    rw [hid (r ^ j), hφrot] at hv1 hv2 hv3
    simp only [Subgroup.coe_pow] at hv1 hv2 hv3
    refine ⟨?_, ?_, ?_⟩
    · rw [hv1]
      simp [dihedralRotationSign]
    · rw [hv2]
      simp [dihedralRotationSign]
    · rw [hv3]
      simp [dihedralRotationSign]
  have c1χ₁ : (1 : G → ℂ) ≠ χ₁ := fun h => h1 h.symm
  have c12 : (χ₁ : G → ℂ) ≠ χ₂ := fun h => h12 (Subtype.ext h)
  have c13 : (χ₁ : G → ℂ) ≠ χ₃ := fun h => h13 (Subtype.ext h)
  have c23 : (χ₂ : G → ℂ) ≠ χ₃ := fun h => h23 (Subtype.ext h)
  have hpm : ∀ z : ℤ, z = 1 ∨ z = -1 → (z : ℂ) * z = 1 := by
    rintro z (rfl | rfl) <;> norm_num
  have hee : (e : ℂ) * e = 1 := hpm e he
  have hneg1 : ∀ k : ℤ, (-1 : ℂ) ^ k = 1 ∨ (-1 : ℂ) ^ k = -1 := by
    intro k
    rcases Int.even_or_odd k with hk | hk
    · exact Or.inl hk.neg_one_zpow
    · exact Or.inr hk.neg_one_zpow
  have hβr1 : (basis.representation β).character (r : G) = e := by
    simpa using hβr 1 le_rfl (by omega)
  have hβr2 : (basis.representation β).character ((r : G) ^ 2) = e := hβr 2 (by omega) (by omega)
  have htpow : t = (r : G) ^ (M / 2) := by rw [htdef, Subgroup.coe_pow]
  have hβt : (basis.representation β).character t = e := by
    rw [htpow]
    exact hβr (M / 2) (by omega) (by omega)
  have hψtval : ∀ (k : dihedralIndexSet M) (x : ℂ), (x = 1 ∨ x = -1) →
      (ψ k : G → ℂ) t ≠ x := by
    intro k x hx h
    rw [hψt k] at h
    rcases hneg1 (k : ℤ) with h' | h' <;> rw [h'] at h <;> rcases hε with rfl | rfl <;>
      rcases hx with rfl | rfl <;> norm_num at h
  have hdeg1 : ∀ ℓ, (basis.representation ℓ).character 1 =
      (Module.finrank ℂ (basis.representation ℓ).vector : ℂ) :=
    fun ℓ => Representation.char_one _
  have hβimage : (basis.representation β).character ∈
      ({1, (χ₁ : G → ℂ), (χ₂ : G → ℂ), (χ₃ : G → ℂ)} : Set (G → ℂ)) ∪
        Set.range (fun k => (ψ k : G → ℂ)) := by
    rw [← himage]
    exact ⟨β, hβ, rfl⟩
  have hβχ₁ : (basis.representation β).character = χ₁ := by
    rcases hβimage with h | ⟨k, hk⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h | h | h
      · exfalso
        have h' := congrFun h 1
        rw [hq] at h'
        simp only [Pi.one_apply] at h'
        norm_cast at h'
        omega
      · exact h
      · exfalso
        have ha := (hval 1 le_rfl (by omega)).2.1
        have hb := (hval 2 (by omega) (by omega)).2.1
        rw [← h, pow_one] at ha
        rw [← h] at hb
        rw [hβr1] at ha
        rw [hβr2] at hb
        revert ha hb
        rcases hδ₂ with rfl | rfl <;> rcases he with rfl | rfl <;> norm_num
      · exfalso
        have ha := (hval 1 le_rfl (by omega)).2.2
        have hb := (hval 2 (by omega) (by omega)).2.2
        rw [← h, pow_one] at ha
        rw [← h] at hb
        rw [hβr1] at ha
        rw [hβr2] at hb
        revert ha hb
        rcases hδ₃ with rfl | rfl <;> rcases he with rfl | rfl <;> norm_num
    · exfalso
      have h' := congrFun hk t
      rw [hβt] at h'
      exact hψtval k e (by rcases he with rfl | rfl <;> norm_num) h'
  have hδ₁e : δ₁ = e := by
    have ha := (hval 1 le_rfl (by omega)).1
    rw [← hβχ₁, pow_one, hβr1] at ha
    exact_mod_cast ha.symm
  have hlampow : ∀ w, lam w ^ 2 ^ 1 = 1 := fun w => by simpa using hlam2 w
  obtain ⟨htwist, ⟨labelLam, hLchar, hLB0⟩, -⟩ :=
    prime_power_linear_twists_preserve_blocks basis ideal 2 lam 1 hlampow principal hprincipal
  obtain ⟨labelLamβ, hLβchar, hLβblock⟩ := htwist β
  have hLβB0 : labelLamβ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal)
      principal := by
    rw [← coefficientBlock_eq_of_mem basis _ hβ]
    exact hLβblock
  have hLfun : (basis.representation labelLam).character = fun g => (lam g : ℂ) :=
    funext hLchar
  have hLβfun : (basis.representation labelLamβ).character =
      fun g => (lam g : ℂ) * (basis.representation β).character g := funext hLβchar
  have hlam1 : (lam 1 : ℂ) = 1 := by rw [map_one, Units.val_one]
  have hlamt : (lam t : ℂ) = 1 := by
    rw [htpow, map_pow, Units.val_pow_eq_pow_val, hlamr, hhalfeven.neg_one_pow]
  have hlamodd : ∀ y : G, Odd (orderOf y) → (lam y : ℂ) = 1 := by
    intro y hy
    have hsq : (lam y : ℂ) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hlam2 y, Units.val_one]
    have hord : (lam y : ℂ) ^ orderOf y = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
    obtain ⟨m, hm⟩ := hy
    rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul] at hord
    exact hord
  have hLimage : (basis.representation labelLam).character ∈
      ({1, (χ₁ : G → ℂ), (χ₂ : G → ℂ), (χ₃ : G → ℂ)} : Set (G → ℂ)) ∪
        Set.range (fun k => (ψ k : G → ℂ)) := by
    rw [← himage]
    exact ⟨labelLam, hLB0, rfl⟩
  have hLβimage : (basis.representation labelLamβ).character ∈
      ({1, (χ₁ : G → ℂ), (χ₂ : G → ℂ), (χ₃ : G → ℂ)} : Set (G → ℂ)) ∪
        Set.range (fun k => (ψ k : G → ℂ)) := by
    rw [← himage]
    exact ⟨labelLamβ, hLβB0, rfl⟩
  have hq1' : (q : ℂ) ≠ 1 := by
    norm_cast
    omega
  have hL23 : (basis.representation labelLam).character = χ₂ ∨
      (basis.representation labelLam).character = χ₃ := by
    rcases hLimage with h | ⟨k, hk⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h | h | h
      · exfalso
        have h' := congrFun h (r : G)
        rw [hLfun] at h'
        simp only [Pi.one_apply] at h'
        rw [hlamr] at h'
        norm_num at h'
      · exfalso
        have h' := congrFun h 1
        rw [hLfun, ← hβχ₁] at h'
        simp only at h'
        rw [hlam1, hq] at h'
        exact hq1' h'.symm
      · exact Or.inl h
      · exact Or.inr h
    · exfalso
      have h' := congrFun hk t
      rw [hLfun] at h'
      simp only at h'
      rw [hlamt] at h'
      exact hψtval k 1 (Or.inl rfl) h'
  have hLβ23 : (basis.representation labelLamβ).character = χ₂ ∨
      (basis.representation labelLamβ).character = χ₃ := by
    rcases hLβimage with h | ⟨k, hk⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h | h | h
      · exfalso
        have h' := congrFun h 1
        rw [hLβfun] at h'
        simp only [Pi.one_apply] at h'
        rw [hlam1, hq, one_mul] at h'
        exact hq1' h'
      · exfalso
        apply hlamβ
        rw [← hLβfun, h, hβχ₁]
      · exact Or.inl h
      · exact Or.inr h
    · exfalso
      have h' := congrFun hk t
      rw [hLβfun] at h'
      simp only at h'
      rw [hlamt, one_mul, hβt] at h'
      exact hψtval k e (by rcases he with rfl | rfl <;> norm_num) h'
  have hLneLβ : (basis.representation labelLam).character ≠
      (basis.representation labelLamβ).character := by
    intro h
    have h' := congrFun h 1
    rw [hLfun, hLβfun] at h'
    simp only at h'
    rw [hlam1, hq, one_mul] at h'
    exact hq1' h'.symm
  have hχ₂in : (χ₂ : G → ℂ) = (basis.representation labelLam).character ∨
      (χ₂ : G → ℂ) = (basis.representation labelLamβ).character := by
    rcases hL23 with h | h
    · exact Or.inl h.symm
    · rcases hLβ23 with h' | h'
      · exact Or.inr h'.symm
      · exact absurd (h.trans h'.symm) hLneLβ
  have hχ₃in : (χ₃ : G → ℂ) = (basis.representation labelLam).character ∨
      (χ₃ : G → ℂ) = (basis.representation labelLamβ).character := by
    rcases hL23 with h | h
    · rcases hLβ23 with h' | h'
      · exact absurd (h.trans h'.symm) hLneLβ
      · exact Or.inr h'.symm
    · exact Or.inl h.symm
  have hψlabel : ∀ k : dihedralIndexSet M, ∃ ℓ ∈ coefficientBlock basis
      (localizedComplexIntegerRing ideal) principal,
        (basis.representation ℓ).character = ψ k := by
    intro k
    have hk : (ψ k : G → ℂ) ∈ (fun l => (basis.representation l).character) ''
        (coefficientBlock basis (localizedComplexIntegerRing ideal) principal :
          Set basis.index) := by
      rw [himage]
      exact Or.inr ⟨k, rfl⟩
    obtain ⟨ℓ, hℓ, hℓc⟩ := hk
    exact ⟨ℓ, hℓ, hℓc⟩
  choose ψL hψLB0 hψLc using hψlabel
  have hcardI : Fintype.card (dihedralIndexSet M) = M / 2 - 1 := by
    have h := card_option_dihedralIndexSet hM2
    rw [Fintype.card_option] at h
    omega
  have hdeg1 : ∀ ℓ, (basis.representation ℓ).character 1 =
      (Module.finrank ℂ (basis.representation ℓ).vector : ℂ) :=
    fun ℓ => Representation.char_one _
  have hdegpos : ∀ ℓ, 0 < Module.finrank ℂ (basis.representation ℓ).vector := by
    intro ℓ
    have h := irreducible_character_degree_ne_zero (basis.representation ℓ) (basis.irreducible ℓ)
    rw [hdeg1] at h
    exact Nat.pos_of_ne_zero (by exact_mod_cast h)
  have hdegψ : ∀ k : dihedralIndexSet M,
      (Module.finrank ℂ (basis.representation (ψL k)).vector : ℤ) = q + e ∧ ε = -e := by
    intro k
    have h := (hodd 1 (by rw [orderOf_one]; exact odd_one)).2 k
    rw [← hψLc k, ← hβχ₁, hq, hdeg1, hδ₁e] at h
    have hz : 1 + e * (q : ℤ) + ε *
        (Module.finrank ℂ (basis.representation (ψL k)).vector : ℤ) = 0 := by
      exact_mod_cast h
    have hpos := hdegpos (ψL k)
    rcases he with rfl | rfl <;> rcases hε with rfl | rfl <;> omega
  have hk₀ : (1 : ℤ) ∈ dihedralIndexSet M := by
    rw [dihedralIndexSet, Finset.mem_Icc]
    omega
  have hεe : ε = -e := (hdegψ ⟨1, hk₀⟩).2
  have hψodd : ∀ (k : dihedralIndexSet M) (y : G), Odd (orderOf y) →
      (basis.representation (ψL k)).character y = (basis.representation β).character y + e := by
    intro k y hy
    have h := (hodd y hy).2 k
    rw [← hψLc k, ← hβχ₁, hδ₁e, hεe] at h
    push_cast at h
    linear_combination (-(e : ℂ)) * h +
      ((basis.representation β).character y - (basis.representation (ψL k)).character y) * hee
  let eqv : dihedralIndexSet M ≃ Fin (M / 2 - 1) := Fintype.equivFinOfCardEq hcardI
  let ψ' : Fin (M / 2 - 1) → basis.index := fun k => ψL (eqv.symm k)
  have hψ'c : ∀ k, (basis.representation (ψ' k)).character = ψ (eqv.symm k) :=
    fun k => hψLc _
  have hdist : ∀ ℓ ℓ' : basis.index, (basis.representation ℓ).character ≠
      (basis.representation ℓ').character → ℓ ≠ ℓ' := fun ℓ ℓ' h heq => h (heq ▸ rfl)
  have hβval1 : (basis.representation β).character 1 = q := hq
  have hLval1 : (basis.representation labelLam).character 1 = 1 := by rw [hLfun]; exact hlam1
  have hLβval1 : (basis.representation labelLamβ).character 1 = q := by
    rw [hLβfun]
    simp only
    rw [hlam1, hq, one_mul]
  have hP1 : (basis.representation principal).character 1 = 1 := by rw [hprincipal]; rfl
  have hne_at1 : ∀ ℓ ℓ' : basis.index, (basis.representation ℓ).character 1 = 1 →
      (basis.representation ℓ').character 1 = q → ℓ ≠ ℓ' := by
    intro ℓ ℓ' h1' hq' heq
    rw [heq, hq'] at h1'
    exact hq1' h1'
  have hPL : principal ≠ labelLam := by
    apply hdist
    intro h
    have h' := congrFun h (r : G)
    rw [hprincipal, hLfun] at h'
    simp only [Pi.one_apply] at h'
    rw [hlamr] at h'
    norm_num at h'
  have hPβ : principal ≠ β := hne_at1 _ _ hP1 hβval1
  have hPLβ : principal ≠ labelLamβ := hne_at1 _ _ hP1 hLβval1
  have hLβ' : labelLam ≠ β := hne_at1 _ _ hLval1 hβval1
  have hLLβ : labelLam ≠ labelLamβ := hdist _ _ hLneLβ
  have hβLβ : β ≠ labelLamβ := hdist _ _ (fun h => hlamβ (by rw [← hLβfun, ← h]))
  have hψchar : ∀ k, (ψ (eqv.symm k) : G → ℂ) ≠ 1 ∧ (ψ (eqv.symm k) : G → ℂ) ≠ χ₁ ∧
      (ψ (eqv.symm k) : G → ℂ) ≠ χ₂ ∧ (ψ (eqv.symm k) : G → ℂ) ≠ χ₃ := by
    intro k
    obtain ⟨h1', h2', h3', h4'⟩ := hψne (eqv.symm k)
    exact ⟨h1', fun h => h2' (Subtype.ext h), fun h => h3' (Subtype.ext h),
      fun h => h4' (Subtype.ext h)⟩
  have hψ'ne : ∀ k, ψ' k ≠ principal ∧ ψ' k ≠ labelLam ∧ ψ' k ≠ β ∧ ψ' k ≠ labelLamβ := by
    intro k
    obtain ⟨h1', h2', h3', h4'⟩ := hψchar k
    refine ⟨hdist _ _ ?_, hdist _ _ ?_, hdist _ _ ?_, hdist _ _ ?_⟩
    · rw [hψ'c, hprincipal]
      exact h1'
    · rw [hψ'c]
      intro h
      rcases hL23 with h'' | h'' <;> rw [h''] at h
      · exact h3' h
      · exact h4' h
    · rw [hψ'c, hβχ₁]
      exact h2'
    · rw [hψ'c]
      intro h
      rcases hLβ23 with h'' | h'' <;> rw [h''] at h
      · exact h3' h
      · exact h4' h
  have hψ'inj : Function.Injective ψ' := by
    intro k l h
    have hc := congrArg (fun ℓ => (basis.representation ℓ).character) h
    simp only [hψ'c] at hc
    exact eqv.symm.injective (hψinj (Subtype.ext hc))
  have hB0iff : ∀ ℓ, ℓ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔
      ℓ = principal ∨ ℓ = labelLam ∨ ℓ = β ∨ ℓ = labelLamβ ∨ ∃ k, ℓ = ψ' k := by
    intro ℓ
    have himg : ℓ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔
        (basis.representation ℓ).character ∈ (fun l => (basis.representation l).character) ''
          (coefficientBlock basis (localizedComplexIntegerRing ideal) principal :
            Set basis.index) :=
      ⟨fun h => ⟨ℓ, h, rfl⟩, fun ⟨ℓ', h', heq⟩ => basis.distinct heq ▸ h'⟩
    rw [himg, himage]
    constructor
    · rintro (h | ⟨k, hk⟩)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
        rcases h with h | h | h | h
        · exact Or.inl (basis.distinct (h.trans hprincipal.symm))
        · exact Or.inr (Or.inr (Or.inl (basis.distinct (h.trans hβχ₁.symm))))
        · rcases hχ₂in with h' | h'
          · exact Or.inr (Or.inl (basis.distinct (h.trans h')))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (basis.distinct (h.trans h')))))
        · rcases hχ₃in with h' | h'
          · exact Or.inr (Or.inl (basis.distinct (h.trans h')))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (basis.distinct (h.trans h')))))
      · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨eqv k, basis.distinct ?_⟩)))
        change (basis.representation ℓ).character = (basis.representation (ψ' (eqv k))).character
        rw [hψ'c, Equiv.symm_apply_apply]
        exact hk.symm
    · rintro (rfl | rfl | rfl | rfl | ⟨k, rfl⟩)
      · exact Or.inl (by rw [hprincipal]; simp)
      · rcases hL23 with h | h
        · exact Or.inl (by rw [h]; simp)
        · exact Or.inl (by rw [h]; simp)
      · exact Or.inl (by rw [hβχ₁]; simp)
      · rcases hLβ23 with h | h
        · exact Or.inl (by rw [h]; simp)
        · exact Or.inl (by rw [h]; simp)
      · exact Or.inr ⟨eqv.symm k, (hψ'c k).symm⟩
  have hfin : ∀ ℓ (d : ℕ), (basis.representation ℓ).character 1 = d →
      Module.finrank ℂ (basis.representation ℓ).vector = d := by
    intro ℓ d h
    rw [hdeg1] at h
    exact_mod_cast h
  have hfP := hfin principal 1 (by rw [hP1]; simp)
  have hfL := hfin labelLam 1 (by rw [hLval1]; simp)
  have hfβ := hfin β q hβval1
  have hfLβ := hfin labelLamβ q hLβval1
  have hfψ : ∀ k, (Module.finrank ℂ (basis.representation (ψ' k)).vector : ℤ) = q + e :=
    fun k => (hdegψ (eqv.symm k)).1
  have hoddiff : ∀ ℓ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      Odd (Module.finrank ℂ (basis.representation ℓ).vector) ↔
        ℓ = principal ∨ ℓ = labelLam ∨ ℓ = β ∨ ℓ = labelLamβ := by
    intro ℓ hℓ
    constructor
    · intro hodd'
      rcases (hB0iff ℓ).mp hℓ with h | h | h | h | ⟨k, rfl⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exfalso
        have hk := hfψ k
        obtain ⟨m, hm⟩ := hodd'
        obtain ⟨m', hm'⟩ := hqodd
        rw [hm, hm'] at hk
        push_cast at hk
        rcases he with rfl | rfl <;> omega
    · rintro (rfl | rfl | rfl | rfl)
      · rw [hfP]
        exact odd_one
      · rw [hfL]
        exact odd_one
      · rw [hfβ]
        exact hqodd
      · rw [hfLβ]
        exact hqodd
  have hor : ∀ (f : G → ℂ) (y : CFSG.Wreathed.OddElements G),
      CFSG.Wreathed.oddRestriction f y = f y.1 := fun _ _ => rfl
  have hrows : ∀ i : Fin 4 ⊕ Fin (M / 2 - 1),
      oddRestriction (basis.representation
          (Sum.elim ![principal, labelLam, β, labelLamβ] ψ' i)).character =
        dihedralRegularRows e (M / 2 - 1) i 0 • oddRestriction (1 : G → ℂ) +
          dihedralRegularRows e (M / 2 - 1) i 1 •
            oddRestriction (1 + (e : ℂ) • (basis.representation β).character) := by
    intro i
    funext y
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hor, hor, hor]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, zsmul_eq_mul]
    rcases i with i | k
    · fin_cases i
      · simp [dihedralRegularRows, hprincipal]
      · simp [dihedralRegularRows, hLfun, hlamodd y.1 y.2]
      · simp only [dihedralRegularRows, Matrix.of_apply, Sum.elim_inl]
        simp
        linear_combination (-(basis.representation β).character y) * hee
      · simp only [dihedralRegularRows, Matrix.of_apply, Sum.elim_inl]
        simp [hLβfun, hlamodd y.1 y.2]
        linear_combination (-(basis.representation β).character y) * hee
    · simp only [dihedralRegularRows, Matrix.of_apply, Sum.elim_inr]
      simp
      have h := hψodd (eqv.symm k) y.1 y.2
      change (basis.representation (ψ' k)).character y.1 = _ at h
      rw [h]
      linear_combination (-(basis.representation β).character y) * hee
  set b₀ := CFSG.Wreathed.oddRestriction (1 : G → ℂ) with hb₀
  set b₁ := CFSG.Wreathed.oddRestriction (1 + (e : ℂ) • (basis.representation β).character)
    with hb₁
  set bβ := CFSG.Wreathed.oddRestriction (basis.representation β).character with hbβ
  have hb₁eq : b₁ = b₀ + e • bβ := by
    funext y
    rw [Pi.add_apply, Pi.smul_apply, hb₁, hb₀, hbβ, hor, hor, hor]
    simp [zsmul_eq_mul]
  have hbβeq : bβ = (-e) • b₀ + e • b₁ := by
    have h := hrows (Sum.inl 2)
    simpa [dihedralRegularRows] using h
  have hPB0 : principal ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal :=
    coefficientBlock_self_mem basis _ principal
  have hmemL : ∀ ℓ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      CFSG.Wreathed.oddRestriction (basis.representation ℓ).character ∈
        CFSG.Wreathed.oddRestrictionLattice basis
          (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) :=
    fun ℓ hℓ => Submodule.subset_span ⟨ℓ, hℓ, rfl⟩
  have hb₀L : b₀ ∈ CFSG.Wreathed.oddRestrictionLattice basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) := by
    have h := hmemL principal hPB0
    rwa [hprincipal] at h
  have hbβL : bβ ∈ CFSG.Wreathed.oddRestrictionLattice basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) := hmemL β hβ
  have hb₁L : b₁ ∈ CFSG.Wreathed.oddRestrictionLattice basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) := by
    rw [hb₁eq]
    exact add_mem hb₀L (Submodule.smul_mem _ _ hbβL)
  have hrowlabel : ∀ ℓ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∃ i : Fin 4 ⊕ Fin (M / 2 - 1), Sum.elim ![principal, labelLam, β, labelLamβ] ψ' i = ℓ := by
    intro ℓ hℓ
    rcases (hB0iff ℓ).mp hℓ with rfl | rfl | rfl | rfl | ⟨k, rfl⟩
    · exact ⟨Sum.inl 0, rfl⟩
    · exact ⟨Sum.inl 1, rfl⟩
    · exact ⟨Sum.inl 2, rfl⟩
    · exact ⟨Sum.inl 3, rfl⟩
    · exact ⟨Sum.inr k, rfl⟩
  have hspan₁ : Submodule.span ℤ {b₀, b₁} = CFSG.Wreathed.oddRestrictionLattice basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro f hf
      rcases hf with rfl | rfl
      · exact hb₀L
      · exact hb₁L
    · apply Submodule.span_le.mpr
      rintro _ ⟨ℓ, hℓ, rfl⟩
      obtain ⟨i, rfl⟩ := hrowlabel ℓ hℓ
      change CFSG.Wreathed.oddRestriction (basis.representation
        (Sum.elim ![principal, labelLam, β, labelLamβ] ψ' i)).character ∈ _
      rw [hrows i]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hspan₂ : Submodule.span ℤ {b₀, bβ} = CFSG.Wreathed.oddRestrictionLattice basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) := by
    rw [← hspan₁]
    apply le_antisymm
    · rw [Submodule.span_le]
      intro f hf
      rcases hf with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · rw [hbβeq]
        exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [Submodule.span_le]
      intro f hf
      rcases hf with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · rw [hb₁eq]
        exact add_mem (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  obtain ⟨y₀, hy₀odd, hy₀⟩ := hy₀
  let o₁ : CFSG.Wreathed.OddElements G := ⟨1, by rw [orderOf_one]; exact odd_one⟩
  let o₀ : CFSG.Wreathed.OddElements G := ⟨y₀, hy₀odd⟩
  have he0 : (e : ℂ) ≠ 0 := by rcases he with rfl | rfl <;> norm_num
  have hqβ : (q : ℂ) - (basis.representation β).character y₀ ≠ 0 := sub_ne_zero.mpr hy₀.symm
  have hlin₂ : LinearIndependent ℤ ![b₀, bβ] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrFun hab o₁
    have h2 := congrFun hab o₀
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hb₀, hbβ, hor, hor] at h1 h2
    simp only [Pi.one_apply, zsmul_eq_mul, mul_one, Pi.zero_apply] at h1 h2
    change (a : ℂ) + b * (basis.representation β).character 1 = 0 at h1
    rw [hq] at h1
    have hb : (b : ℂ) = 0 := by
      have h3 : (b : ℂ) * ((q : ℂ) - (basis.representation β).character y₀) = 0 := by
        linear_combination h1 - h2
      exact (mul_eq_zero.mp h3).resolve_right hqβ
    have ha : (a : ℂ) = 0 := by
      rw [hb, zero_mul, add_zero] at h1
      exact h1
    exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩
  have hlin₁ : LinearIndependent ℤ ![b₀, b₁] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    rw [hb₁eq, smul_add, ← add_assoc, ← add_smul, smul_smul] at hab
    obtain ⟨ha, hb⟩ := (LinearIndependent.pair_iff.mp hlin₂) (a + b) (b * e) hab
    have hb' : b = 0 := by
      rcases he with rfl | rfl <;> omega
    exact ⟨by omega, hb'⟩
  have hgram := dihedralRegularRows_gram e he (M / 2 - 1)
  have hcastM : ((M / 2 - 1 : ℕ) : ℤ) + 2 = ((M / 2 + 1 : ℕ) : ℤ) := by omega
  rw [hcastM] at hgram
  refine ⟨labelLam, labelLamβ, ψ', hLfun, hLβfun, hψ'inj, hPL, hPβ, hPLβ, hLβ', hLLβ, hβLβ,
    hψ'ne, hB0iff, hfP, hfL, hfβ, hfLβ, hfψ, fun k y hy => hψodd (eqv.symm k) y hy, hoddiff,
    hlin₁, hspan₁, hlin₂, hspan₂, hrows, hgram⟩

end CFSG.Semidihedral.Principal
