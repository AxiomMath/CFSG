module

public import CFSG.CharacterTheory.Semidihedral.Principal.ActualSimpleLayerExhaustionSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.OddFourierFamily
public import CFSG.CharacterTheory.Semidihedral.Principal.ColumnRigidity
public import CFSG.CharacterTheory.Semidihedral.Principal.FourierOddDegreeProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.ActualSimpleLayerInvolutionColumns

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOuterQuotient CFSG.Semidihedral.SemilinearOddExtensions
  CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Wreathed CFSG.Open

theorem actual_simple_layer_principal_block_exhaustion_and_values {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ρ : Gamma t →* coordinateE F),
      Nat.card F = p ^ f ∧ Function.Injective ρ ∧
      (CFSG.generalizedFitting (Gamma t)).map ρ = specialLayer F ∧ linearLayer F ≤ ρ.range ∧
      (let φ : C t → ℂ := fun c =>
        (Nat.card {x : Omega F // ((ρ (kappa t c) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let e : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      φ 1 = Nat.card F ∧ (∃ y : C t, Odd (orderOf y) ∧ φ y ≠ Nat.card F) ∧
      ∃ (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index),
        ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal
          (Nat.card F) e (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν) := by
  obtain ⟨F, hfield, hfinite, ρ, hcard, hρ, hlayer, hD, hcols⟩ :=
    actual_simple_layer_principal_involution_columns n hn S0 f0 hG t ht hnonab hcentral hnc p f
      hp hpodd hf hmodel ideal basis principal hprincipal localBasis localPrincipal
      hlocalPrincipal
  refine ⟨F, hfield, hfinite, ρ, hcard, hρ, hlayer, hD, ?_⟩
  intro φ e
  let k : ℕ := 2 ^ (n - 3)
  let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
  let χ : basis.index → G → ℂ := fun c => (basis.representation c).character
  obtain ⟨hlφ, U, hU, hUU, hUV, hVV, hUp0, hUp1, -, hUodd⟩ := hcols
  let _ := hfield
  let _ := hfinite
  have hqodd : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
  have hq3 : 3 ≤ Nat.card F := by
    rw [hcard]
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      obtain ⟨m, hm⟩ := hpodd
      omega
    exact hp3.trans (Nat.le_self_pow (by omega) p)
  have hφ1 : φ 1 = Nat.card F := by
    let _ : Fintype F := Fintype.ofFinite F
    have hfix : Nat.card {x : Omega F // ((ρ (kappa t 1) : coordinateE F) :
        Equiv.Perm (Omega F)) x = x} = Nat.card (Omega F) :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun x => by
        rw [map_one, map_one]
        rfl)
    simp only [φ]
    rw [hfix, card_omega]
    push_cast
    ring
  have hex : ∃ y : C t, Odd (orderOf y) ∧ φ y ≠ Nat.card F :=
    exists_odd_fixedPoint_character_ne hnonab F ρ hρ
  have he : (e : ℂ) ≠ 0 := by
    simp only [e]
    split_ifs <;> norm_num
  have he1 : Nat.card F % 4 = 1 → e = 1 := fun h => by simp only [e, h, ite_true]
  have he3 : Nat.card F % 4 = 3 → e = -1 := fun h => by
    simp only [e]
    rw [ite_eq_right (by omega)]
  have hpB : principal ∈ B := coefficientBlock_self_mem _ _ _
  obtain ⟨-, S, fS, hzS, hrS⟩ :=
    InvolutionFusion.involution_centered_sylow_existence n hn S0 f0 hG t ht
  obtain ⟨hM4, hkeven, hk2, hhalf⟩ := modulus_eq_four_mul hn
  have hkdef : k = 2 ^ (n - 3) := rfl
  have hMk : modulus n = 4 * k := hM4
  have htr : (fS (r n) : G) ^ (modulus n / 2) = t := by
    have hm2 : modulus n / 2 = 2 ^ (n - 2) := by omega
    rw [hm2, ← hrS]
    rfl
  have htS : t ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [← hzS]
    have h := (Subgroup.mem_center_iff.mp (CFSG.Semidihedral.z_mem_center n hn)) (fS.symm ⟨s, hs⟩)
    have h' := congrArg (fun w => ((fS w : S) : G)) h
    simp only [map_mul, MulEquiv.apply_symm_apply] at h'
    exact h'
  obtain ⟨-, -, hΘapply, hEapply, hΘ1, hE1, -, -, -, -, -, -, -, -, -, -,
    c₁, c₂, c₃, δ₁, δ₂, δ₃, εe, ψ, hc₁, hc₂, hc₃, h12, h13, h23, hc₁p, hc₂p, hc₃p, hδ₁, hδ₂, hδ₃,
    hεe, hψinj, hψmem, hΘeq, hEeq, hθcoef, hηcoef, -, -, hne0, -, hεsign⟩ :=
    even_cyclic_principal_Fourier_family hn fS basis ideal principal hprincipal
  obtain ⟨I, hI⟩ := exists_isOddResidueTransversal (n := n) hn
  obtain ⟨hIcard, -, hfapply, -, hfdeg1, -, -, -, -, hφθ, hφη, εo, ν', dν, hεo, -, hνinj, hνmem,
    hfeq, hφcoef, hνavoid⟩ :=
    odd_cyclic_principal_Fourier_family hn fS basis ideal principal hprincipal I hI
  obtain ⟨hνc₁, -, -⟩ := hνavoid c₁ c₂ c₃ δ₁ δ₂ δ₃ εe ψ hc₁ hc₂ hc₃ h12 h13 h23 hc₁p hc₂p hc₃p
    hδ₁ hδ₂ hδ₃ hεe hψinj hψmem hΘeq hEeq
  obtain ⟨-, -, -, -, -, hcongr⟩ :=
    cyclic_multiplicity_central_involution_congruence hn S fS basis B I hI
  obtain ⟨-, hvodd, hvinv⟩ :=
    cyclic_principal_Fourier_projection_values hn fS basis ideal principal hprincipal
  have hIk : I.card = k := by rw [hIcard]; omega
  obtain ⟨enum, henum0, henuminj, henummem, henumsurj⟩ := exists_enum_of_card I hIk hI.one_mem
  let d : basis.index → ℤ := fun c => (Module.finrank ℂ (basis.representation c).vector : ℤ)
  have hχ1 : ∀ c, χ c 1 = (d c : ℂ) := fun c => by
    simp only [χ, d, (basis_character_one basis c).1, Int.cast_natCast]
  have hdpos : ∀ c ∈ B, 0 < d c := fun c _ => by
    simp only [d]
    exact_mod_cast (basis_character_one basis c).2
  have hdp : d principal = 1 := by
    have h := hχ1 principal
    rw [show χ principal 1 = 1 by
      show (basis.representation principal).character 1 = 1
      rw [hprincipal]
      rfl] at h
    exact_mod_cast h.symm
  have hεe' : εe = -δ₁ := by
    beta_reduce at hεsign hne0
    rw [(basis_character_one basis c₁).1] at hεsign hne0
    rw [hεsign]
    exact neg_sign_one_add_mul_eq hδ₁ (basis_character_one basis c₁).2 hne0
  beta_reduce at hΘeq hEeq hθcoef hηcoef hfeq hφcoef hφθ hφη hvodd hvinv hfdeg1 hE1 hνmem hcongr
  set L := multiplicityColumn basis (fS (r n) : G) (modulus n) with hL
  have hMk4 : modulus n / 4 = k := by omega
  have hMk2 : modulus n / 2 = 2 * k := by omega
  rw [hMk4] at hψinj hψmem hEeq hηcoef hφη hvodd hvinv hE1 hνc₁ hcongr
  let b : ℕ → basis.index := fun i => ν' (enum i)
  have hb0 : b 0 = ν' 1 := by simp only [b, henum0]
  let T : basis.index → ℤ := Pi.single principal 1 + δ₁ • Pi.single c₁ 1 + δ₂ • Pi.single c₂ 1 +
    δ₃ • Pi.single c₃ 1
  let P : ℕ → basis.index → ℤ := fun j =>
    Pi.single principal 1 + δ₁ • Pi.single c₁ 1 - δ₁ • Pi.single (ψ j) 1
  let Fv : ℕ → basis.index → ℤ := fun i => εo • (Pi.single (b i) 1 - Pi.single (b 0) 1)
  have hTθ : ∀ y ∈ B, T y = L 0 y - L ((modulus n / 2 : ℕ) : ℤ) y := fun y hy => by
    rw [hθcoef y hy]
    simp only [T, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  have hPη : ∀ j ∈ Finset.Icc 1 (k - 1), ∀ y ∈ B, P j y = L 0 y - L (2 * (j : ℤ)) y := by
    intro j hj y hy
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    rw [hηcoef j hj1 hj2 y hy, hεe']
    simp only [P, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    ring
  have hFφ : ∀ i ∈ Finset.range k, ∀ y ∈ B, Fv i y = L (enum i).val y - L 1 y := by
    intro i hi y hy
    rw [hφcoef (enum i) (henummem i hi) y hy]
    simp only [Fv, b, henum0, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul]
  have hψB : ∀ j ∈ Finset.Icc 1 (k - 1), ψ j ∈ B := fun j hj =>
    (hψmem j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2).1
  have ha_x : ∀ j ∈ Finset.Icc 1 (k - 1), ψ j ≠ principal ∧ ψ j ≠ c₁ ∧ ψ j ≠ c₂ ∧ ψ j ≠ c₃ :=
    fun j hj => (hψmem j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2).2
  have ha_inj : Set.InjOn ψ (Finset.Icc 1 (k - 1)) := fun j hj l hl hjl =>
    hψinj j l (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 (Finset.mem_Icc.mp hl).1
      (Finset.mem_Icc.mp hl).2 hjl
  have hbB : ∀ i ∈ Finset.range k, b i ∈ B := fun i hi => (hνmem (enum i) (henummem i hi)).1
  have hb_inj : Set.InjOn b (Finset.range k) := fun i hi i' hi' hii' =>
    henuminj hi hi' (hνinj _ (henummem i hi) _ (henummem i' hi') hii')
  have hb_x : ∀ i ∈ Finset.range k, b i ≠ principal ∧ b i ≠ c₁ := fun i hi =>
    ⟨(hνmem (enum i) (henummem i hi)).2.1, (hνc₁ (enum i) (henummem i hi)).1⟩
  have hb_a : ∀ i ∈ Finset.range k, ∀ j ∈ Finset.Icc 1 (k - 1), b i ≠ ψ j := fun i hi j hj =>
    (hνc₁ (enum i) (henummem i hi)).2 j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
  have hΘval : ∀ g, principalCyclicProjection basis B (fS (r n) : G)
      (fun x => 1 - cyclicLinearCharacter (fS (r n) : G) (modulus n)
        ((modulus n / 2 : ℕ) : ℤ) x) g =
      1 + δ₁ * χ c₁ g + δ₂ * χ c₂ g + δ₃ * χ c₃ g := fun g => by
    rw [hΘeq]
    simp [χ]
  have hEval : ∀ j ∈ Finset.Icc 1 (k - 1), ∀ g, principalCyclicProjection basis B (fS (r n) : G)
      (fun x => 1 - cyclicLinearCharacter (fS (r n) : G) (modulus n) (2 * (j : ℤ)) x) g =
      1 + δ₁ * χ c₁ g - δ₁ * χ (ψ j) g := fun j hj g => by
    rw [hEeq j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2, hεe']
    simp [χ]
    ring
  have hfval : ∀ j ∈ I, ∀ g, principalCyclicProjection basis B (fS (r n) : G)
      (fun x => cyclicLinearCharacter (fS (r n) : G) (modulus n) (j.val : ℤ) x -
        cyclicLinearCharacter (fS (r n) : G) (modulus n) 1 x) g =
      εo * (χ (ν' j) g - χ (ν' 1) g) := fun j hj g => by
    rw [hfeq j hj]
    simp [χ]
  have hχp : ∀ g, χ principal g = 1 := fun g => by
    show (basis.representation principal).character g = 1
    rw [hprincipal]
    rfl
  have hcomm : ∀ y : C t, Commute t (y : G) := fun y =>
    (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm
  have hoddc : ∀ y : C t, Odd (orderOf y) → Odd (orderOf (y : G)) := fun y hy => by
    rwa [Subgroup.orderOf_coe]
  have hsec := fun (y : C t) (hy : Odd (orderOf y)) =>
    hvinv (t * y) t y rfl (hcomm y) ht (hoddc y hy)
  have hval : ∀ c ∈ B, ∀ y : C t, Odd (orderOf y) →
      (fun c (y : C t) => χ c (t * (y : G))) c y = (U c 0 : ℂ) + U c 1 * (1 + (e : ℂ) * φ y) :=
    fun c hc y hy => hU c hc y hy
  have hjodd : ∀ j ∈ I, Odd ((j.val : ℕ) : ℤ) := fun j hj => by exact_mod_cast hI.odd j hj
  have hTU := sum_mul_columns_eq_zero B φ (Nat.card F) (e : ℂ) he hφ1 hex U
    (fun c (y : C t) => χ c (t * (y : G))) hval T fun y hy =>
      (sum_cast_four_mul (fun c => χ c (t * y)) hpB hc₁ hc₂ hc₃ δ₁ δ₂ δ₃).trans (by
        have h := (hsec y hy).1
        rw [hΘval] at h
        rw [hχp]
        exact h)
  have hPU : ∀ j ∈ Finset.Icc 1 (k - 1), _ := fun j hj =>
    sum_mul_columns_eq_zero B φ (Nat.card F) (e : ℂ) he hφ1 hex U
      (fun c (y : C t) => χ c (t * (y : G))) hval (P j) fun y hy =>
        (sum_cast_three_mul (fun c => χ c (t * y)) hpB hc₁ (hψB j hj) δ₁).trans (by
          have h := (hsec y hy).2.1 j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
          rw [hEval j hj] at h
          rw [hχp]
          exact h)
  have hFU : ∀ i ∈ Finset.range k, _ := fun i hi =>
    sum_mul_columns_eq_zero B φ (Nat.card F) (e : ℂ) he hφ1 hex U
      (fun c (y : C t) => χ c (t * (y : G))) hval (Fv i) fun y hy =>
        (sum_cast_two_mul (fun c => χ c (t * y)) (hbB i hi) (hbB 0 (by simp; omega)) εo).trans (by
          have h := (hsec y hy).2.2 _ (hjodd _ (henummem i hi))
          rw [hfval _ (henummem i hi)] at h
          rw [hb0]
          exact h)
  have hdeg0 : ∀ w : basis.index → ℤ, ∑ c ∈ B, (w c : ℂ) * χ c 1 = 0 →
      ∑ y ∈ B, d y * w y = 0 := by
    intro w hw
    have h : ((∑ y ∈ B, d y * w y : ℤ) : ℂ) = 0 := by
      rw [← hw]
      push_cast
      exact Finset.sum_congr rfl fun c _ => by rw [hχ1 c]; ring
    exact_mod_cast h
  have hdT : ∑ y ∈ B, d y * T y = 0 := hdeg0 T
    ((sum_cast_four_mul (fun c => χ c 1) hpB hc₁ hc₂ hc₃ δ₁ δ₂ δ₃).trans (by
      have h := hΘ1
      rw [hΘval] at h
      rw [hχp]
      exact h))
  have hdP : ∀ j ∈ Finset.Icc 1 (k - 1), ∑ y ∈ B, d y * P j y = 0 := fun j hj => hdeg0 (P j)
    ((sum_cast_three_mul (fun c => χ c 1) hpB hc₁ (hψB j hj) δ₁).trans (by
      have h := hE1 j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
      rw [hEval j hj] at h
      rw [hχp]
      exact h))
  have h0k : 0 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  have hdF : ∀ i ∈ Finset.range k, ∑ y ∈ B, d y * Fv i y = 0 := fun i hi => hdeg0 (Fv i)
    ((sum_cast_two_mul (fun c => χ c 1) (hbB i hi) (hbB 0 h0k) εo).trans (by
      have h := hfdeg1 _ (henummem i hi)
      rw [hfval _ (henummem i hi)] at h
      rw [hb0]
      exact h))
  have hTF : ∀ i ∈ Finset.range k, ∑ y ∈ B, T y * Fv i y = 0 := fun i hi => by
    rw [← (hφθ (enum i) (henummem i hi)).1]
    exact Finset.sum_congr rfl fun y hy => by rw [hTθ y hy, hFφ i hi y hy, mul_comm]
  have hPF : ∀ j ∈ Finset.Icc 1 (k - 1), ∀ i ∈ Finset.range k, ∑ y ∈ B, P j y * Fv i y = 0 :=
    fun j hj i hi => by
      rw [← (hφη (enum i) (henummem i hi) j (Finset.mem_Icc.mp hj).1
        (Finset.mem_Icc.mp hj).2).1]
      exact Finset.sum_congr rfl fun y hy => by rw [hPη j hj y hy, hFφ i hi y hy, mul_comm]
  have hUd : ∀ i, ∑ y ∈ B, U y i * d y = 0 := fun i => by
    have h := hUodd 1 (by rw [orderOf_one]; exact odd_one) i
    have h' : ((∑ y ∈ B, U y i * d y : ℤ) : ℂ) = 0 := by
      rw [← h]
      push_cast
      refine Finset.sum_congr rfl fun c _ => ?_
      have hc1 : (basis.representation c).character 1 = (d c : ℂ) := hχ1 c
      rw [hc1]
      simp
    exact_mod_cast h'
  obtain ⟨F', hF', hF'fin, A', ρ', hdata⟩ := actual_simple_layer_matrix_data n hn S0 f0 hG t ht
    hnonab hcentral hnc p f hp hpodd hf hmodel
  have h2part : 2 ^ padicValNat 2 (Nat.card F ^ 2 - 1) = modulus n := by
    have h := hdata.two_part
    rw [hdata.field_card, ← hcard, Nat.factorization_def _ Nat.prime_two] at h
    rw [h]
    rfl
  have hXt : ∀ c ∈ B, (basis.representation c).character ((fS (r n) : G) ^ (modulus n / 2)) =
      ((U c 0 + (1 + e * (Nat.card F : ℤ)) * U c 1 : ℤ) : ℂ) := fun c hc => by
    rw [htr]
    have h : χ c (t * ((1 : C t) : G)) = U c 0 + U c 1 * (1 + (e : ℂ) * φ 1) :=
      hU c hc 1 (by rw [orderOf_one]; exact odd_one)
    rw [OneMemClass.coe_one, mul_one, hφ1] at h
    show χ c t = _
    rw [h]
    push_cast
    ring
  have hcong0 := hcongr (Nat.card F) e (fun c => U c 0) (fun c => U c 1) hq3 hqodd h2part he1 he3
    hXt
  have hIimage : (Finset.range k).image enum = I := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact henummem i hi
    · intro hx
      exact henumsurj x hx
  have hmod : ((modulus n / 2 : ℕ) : ℤ) = 2 * (k : ℤ) := by rw [hMk2]; push_cast; ring
  have hcong : ∀ y ∈ B, U y 0 + 2 * U y 1 + T y + 2 * ∑ j ∈ Finset.Icc 1 (k - 1), P j y +
      2 * ∑ i ∈ Finset.range k, Fv i y ≡ 0 [ZMOD 2 * k] := by
    intro y hy
    have h := hcong0 y hy
    simp only [Pi.sub_apply] at h
    have hsP : ∑ j ∈ Finset.Icc 1 (k - 1), P j y =
        ∑ l ∈ Finset.Icc 1 (k - 1), (L 0 y - L (2 * (l : ℤ)) y) :=
      Finset.sum_congr rfl fun j hj => hPη j hj y hy
    have hsF : ∑ i ∈ Finset.range k, Fv i y = ∑ j ∈ I, (L (j.val : ℤ) y - L 1 y) := by
      rw [← hIimage, Finset.sum_image henuminj]
      exact Finset.sum_congr rfl fun i hi => hFφ i hi y hy
    rw [hTθ y hy, hsP, hsF]
    rw [hmod] at h ⊢
    exact h
  have hVV' : ∑ c ∈ B, U c 1 * U c 1 = 2 * (k : ℤ) + 2 := by
    rw [hVV]
    have h : (2 : ℤ) ^ (n - 2) = 2 * (k : ℤ) := by exact_mod_cast hhalf
    rw [h]
  obtain ⟨y₂, y₃, η₂, η₃, hswap, b', ε', hb', x₄, hx₄, δ₄, hδ₄, hdist, -, hb'inj, ha_x', hb'_x,
    hb'_a, hε', hUshape, hVshape, -, -, -, hvanish, -, -⟩ :=
    integral_principal_column_rigidity B k hk2 hkeven d hdpos principal c₁ c₂ c₃ hpB hc₁ hc₂ hc₃
      (Ne.symm hc₁p) (Ne.symm hc₂p) (Ne.symm hc₃p) h12 h13 h23 hdp ψ hψB ha_inj ha_x
      b hbB hb_inj hb_x hb_a δ₁ δ₂ δ₃ εo hδ₁ hδ₂ hδ₃ hεo T rfl P (fun j _ => rfl) Fv
      (fun i _ => rfl) hdT hdP hdF hTF hPF (fun c => U c 0) (fun c => U c 1) (hUd 0)
      (by simpa [mul_comm] using hTU.1) (fun j hj => by simpa [mul_comm] using (hPU j hj).1)
      (fun i hi => by simpa [mul_comm] using (hFU i hi).1) (hUd 1)
      (by simpa [mul_comm] using hTU.2) (fun j hj => by simpa [mul_comm] using (hPU j hj).2)
      (fun i hi => by simpa [mul_comm] using (hFU i hi).2) hUU hUV hVV' hUp0 hUp1 hcong
  obtain ⟨h01, h02, h03, h04, h12', h13', h14, h23', h24, h34⟩ := hdist
  have hy₂B : y₂ ∈ B := by rcases hswap with ⟨rfl, -, -, -⟩ | ⟨rfl, -, -, -⟩ <;> assumption
  have hy₃B : y₃ ∈ B := by rcases hswap with ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩ <;> assumption
  have hη₂ : η₂ = 1 ∨ η₂ = -1 := by
    rcases hswap with ⟨-, rfl, -, -⟩ | ⟨-, rfl, -, -⟩ <;> assumption
  have hη₃ : η₃ = 1 ∨ η₃ = -1 := by
    rcases hswap with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> assumption
  have hb'ν : ∀ i ∈ Finset.range k, ∃ j ∈ I, b' i = ν' j := by
    intro i hi
    rcases hb' with ⟨rfl, -⟩ | ⟨hk2', rfl, -⟩
    · exact ⟨enum i, henummem i hi, rfl⟩
    · have hi' : Equiv.swap 0 1 i ∈ Finset.range k := by
        rw [hk2'] at hi ⊢
        exact ColumnRigidity.swap_mem_range_two hi
      exact ⟨enum (Equiv.swap 0 1 i), henummem _ hi', rfl⟩
  have hb'B : ∀ i ∈ Finset.range k, b' i ∈ B := fun i hi => by
    obtain ⟨j, hj, hji⟩ := hb'ν i hi
    rw [hji]
    exact (hνmem j hj).1
  have hU0 : ∀ c ∈ B, U c 0 = (Pi.single principal 1 - δ₁ • Pi.single c₁ 1 +
      η₂ • Pi.single y₂ 1 - η₃ • Pi.single y₃ 1 + (2 * δ₄) • Pi.single x₄ 1 :
        basis.index → ℤ) c := hUshape
  have hU1 : ∀ c ∈ B, U c 1 = (δ₁ • Pi.single c₁ 1 - η₂ • Pi.single y₂ 1 - δ₄ • Pi.single x₄ 1 +
      δ₁ • ∑ j ∈ Finset.Icc 1 (k - 1), Pi.single (ψ j) 1 -
      δ₁ • ∑ i ∈ Finset.range k, Pi.single (b' i) 1 : basis.index → ℤ) c := hVshape
  have hψne : ∀ c, (∀ j ∈ Finset.Icc 1 (k - 1), c ≠ ψ j) →
      (∑ j ∈ Finset.Icc 1 (k - 1), Pi.single (ψ j) 1 : basis.index → ℤ) c = 0 :=
    fun c h => ColumnRigidity.sum_single_apply_of_forall_ne h
  have hbne : ∀ c, (∀ i ∈ Finset.range k, c ≠ b' i) →
      (∑ i ∈ Finset.range k, Pi.single (b' i) 1 : basis.index → ℤ) c = 0 :=
    fun c h => ColumnRigidity.sum_single_apply_of_forall_ne h
  have hUp : U principal 0 = 1 ∧ U principal 1 = 0 := ⟨hUp0, hUp1⟩
  have hUc₁ : U c₁ 0 = -δ₁ ∧ U c₁ 1 = δ₁ := by
    refine ⟨?_, ?_⟩
    · rw [hU0 c₁ hc₁]
      simp [Ne.symm h01, h12', h13', h14]
    · rw [hU1 c₁ hc₁]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hψne c₁ fun j hj => (ha_x' j hj).2.1.symm, hbne c₁ fun i hi => (hb'_x i hi).2.1.symm]
      simp [h12', h14]
  have hUy₂ : U y₂ 0 = η₂ ∧ U y₂ 1 = -η₂ := by
    refine ⟨?_, ?_⟩
    · rw [hU0 y₂ hy₂B]
      simp [Ne.symm h02, Ne.symm h12', h23', h24]
    · rw [hU1 y₂ hy₂B]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hψne y₂ fun j hj => (ha_x' j hj).2.2.1.symm,
        hbne y₂ fun i hi => (hb'_x i hi).2.2.1.symm]
      simp [Ne.symm h12', h24]
  have hUy₃ : U y₃ 0 = -η₃ ∧ U y₃ 1 = 0 := by
    refine ⟨?_, ?_⟩
    · rw [hU0 y₃ hy₃B]
      simp [Ne.symm h03, Ne.symm h13', Ne.symm h23', h34]
    · rw [hU1 y₃ hy₃B]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hψne y₃ fun j hj => (ha_x' j hj).2.2.2.1.symm,
        hbne y₃ fun i hi => (hb'_x i hi).2.2.2.1.symm]
      simp [Ne.symm h13', Ne.symm h23', h34]
  have hUx₄ : U x₄ 0 = 2 * δ₄ ∧ U x₄ 1 = -δ₄ := by
    refine ⟨?_, ?_⟩
    · rw [hU0 x₄ hx₄]
      simp [Ne.symm h04, Ne.symm h14, Ne.symm h24, Ne.symm h34]
    · rw [hU1 x₄ hx₄]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hψne x₄ fun j hj => (ha_x' j hj).2.2.2.2.symm,
        hbne x₄ fun i hi => (hb'_x i hi).2.2.2.2.symm]
      simp [Ne.symm h14, Ne.symm h24]
  have hUψ : ∀ j ∈ Finset.Icc 1 (k - 1), U (ψ j) 0 = 0 ∧ U (ψ j) 1 = δ₁ := by
    intro j hj
    obtain ⟨hj0, hj1, hj2, hj3, hj4⟩ := ha_x' j hj
    refine ⟨?_, ?_⟩
    · rw [hU0 (ψ j) (hψB j hj)]
      simp [hj0, hj1, hj2, hj3, hj4]
    · rw [hU1 (ψ j) (hψB j hj)]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [ColumnRigidity.sum_single_apply_of_injOn ha_inj hj,
        hbne (ψ j) fun i hi h => hb'_a i hi j hj h.symm]
      simp [hj1, hj2, hj4]
  have hUb : ∀ i ∈ Finset.range k, U (b' i) 0 = 0 ∧ U (b' i) 1 = -δ₁ := by
    intro i hi
    obtain ⟨hi0, hi1, hi2, hi3, hi4⟩ := hb'_x i hi
    refine ⟨?_, ?_⟩
    · rw [hU0 (b' i) (hb'B i hi)]
      simp [hi0, hi1, hi2, hi3, hi4]
    · rw [hU1 (b' i) (hb'B i hi)]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [ColumnRigidity.sum_single_apply_of_injOn hb'inj hi,
        hψne (b' i) fun j hj => hb'_a i hi j hj]
      simp [hi1, hi2, hi4]
  have hXt' : ∀ c ∈ B, χ c t = ((U c 0 + (1 + e * (Nat.card F : ℤ)) * U c 1 : ℤ) : ℂ) :=
    fun c hc => by
      have h := hXt c hc
      rw [htr] at h
      exact h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlist : B = ({principal, c₁, y₂, y₃, x₄} ∪ (Finset.Icc 1 (k - 1)).image ψ ∪
      (Finset.range k).image b' : Finset basis.index) := by
    apply Finset.Subset.antisymm
    · intro ξ hξ
      by_contra hnot
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
        not_or, not_exists, not_and] at hnot
      obtain ⟨⟨⟨h0, h1, h2, h3, h4⟩, ha⟩, hb⟩ := hnot
      obtain ⟨hU0ξ, hU1ξ⟩ := hvanish ξ hξ h0 h1 h2 h3 h4 (fun j hj hξj => ha j hj hξj.symm)
        (fun i hi hξi => hb i hi hξi.symm)
      have hzero := hXt' ξ hξ
      rw [hU0ξ, hU1ξ] at hzero
      exact CFSG.LyonsUnitaryFour.principal_block_character_ne_zero_of_centralizes_sylow basis
        ideal 2 principal hprincipal ξ hξ S t htS (by
          have h : (basis.representation ξ).character t = _ := hzero
          rw [h]
          simp)
    · intro ξ hξ
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image] at hξ
      rcases hξ with ((rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩) | ⟨i, hi, rfl⟩
      exacts [hpB, hc₁, hy₂B, hy₃B, hx₄, hψB j hj, hb'B i hi]
  have hcardB : B.card = 2 * k + 4 := by
    rw [hlist]
    exact card_listed k (by omega) h01 h02 h03 h04 h12' h13' h14 h23' h24 h34 ha_inj hb'inj ha_x'
      hb'_x hb'_a
  have heven1 : (2 : ℤ) ∣ 1 + e * (Nat.card F : ℤ) := by
    obtain ⟨m, hm⟩ := hqodd
    rcases (show e = 1 ∨ e = -1 by simp only [e]; split_ifs <;> simp) with h | h <;>
      rw [h, hm] <;> push_cast
    · exact ⟨m + 1, by ring⟩
    · exact ⟨-m, by ring⟩
  have hpar : ∀ c ∈ B, (Odd (Module.finrank ℂ (basis.representation c).vector) ↔ Odd (U c 0)) := by
    intro c hc
    obtain ⟨kk, hkk, hkkd⟩ := character_involution_parity (basis.representation c)
      (show t ^ 2 = 1 by rw [← ht]; exact pow_orderOf_eq_one t)
    have hkk' : kk = U c 0 + (1 + e * (Nat.card F : ℤ)) * U c 1 := by
      have h := hkk.symm.trans (hXt' c hc)
      exact_mod_cast h
    have hd := hkkd _ (basis_character_one basis c).1
    have h2 : (2 : ℤ) ∣ (1 + e * (Nat.card F : ℤ)) * U c 1 := Dvd.dvd.mul_right heven1 _
    rw [← Int.odd_coe_nat, Int.odd_iff, Int.odd_iff]
    generalize (1 + e * (Nat.card F : ℤ)) * U c 1 = w at hkk' h2
    omega
  have hsumB : ∀ g : basis.index → ℂ, ∑ c ∈ B, g c = g principal + g c₁ + g y₂ + g y₃ + g x₄ +
      ∑ j ∈ Finset.Icc 1 (k - 1), g (ψ j) + ∑ i ∈ Finset.range k, g (b' i) := fun g => by
    rw [hlist]
    exact sum_listed k h01 h02 h03 h04 h12' h13' h14 h23' h24 h34 ha_inj hb'inj ha_x' hb'_x hb'_a g
  have hδ₁sq : (δ₁ : ℂ) ^ 2 = 1 := by rcases hδ₁ with h | h <;> rw [h] <;> norm_num
  have hδ₁0 : (δ₁ : ℂ) ≠ 0 := by rcases hδ₁ with h | h <;> rw [h] <;> norm_num
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hk1 : ((k - 1 : ℕ) : ℂ) = (k : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hoddrel : ∀ x : G, Odd (orderOf x) →
      (∀ j ∈ Finset.Icc 1 (k - 1), χ (ψ j) x = χ c₁ x + δ₁) ∧
      (∀ i ∈ Finset.range k, χ (b' i) x = χ c₁ x + δ₁) ∧
      1 + δ₁ * χ c₁ x + η₂ * χ y₂ x + η₃ * χ y₃ x = 0 ∧
      1 + η₂ * χ y₂ x + δ₄ * χ x₄ x = 0 := by
    intro x hx
    obtain ⟨hΘx, hEx, hFx⟩ := hvodd x hx
    rw [hΘval] at hΘx
    have hΘx' : 1 + δ₁ * χ c₁ x + η₂ * χ y₂ x + η₃ * χ y₃ x = 0 := by
      rcases hswap with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact hΘx
      · linear_combination hΘx
    have hψx : ∀ j ∈ Finset.Icc 1 (k - 1), χ (ψ j) x = χ c₁ x + δ₁ := by
      intro j hj
      have h := hEx j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
      rw [hEval j hj] at h
      linear_combination (-(δ₁ : ℂ)) * h + (χ c₁ x - χ (ψ j) x) * hδ₁sq
    have hνx : ∀ i ∈ Finset.range k, χ (b' i) x = χ (ν' 1) x := by
      intro i hi
      obtain ⟨j, hj, hji⟩ := hb'ν i hi
      have h := hFx _ (hjodd j hj)
      rw [hfval j hj] at h
      rw [hji]
      have hεo0 : (εo : ℂ) ≠ 0 := by rcases hεo with h | h <;> rw [h] <;> norm_num
      have h' := (mul_eq_zero.mp h).resolve_left hεo0
      linear_combination h'
    have horth : ∀ i : Fin 2, ∑ c ∈ B, (U c i : ℂ) * χ c x = 0 := by
      intro i
      have h := congrArg (starRingEnd ℂ) (hUodd x hx i)
      rw [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp [χ]
    have hU0x := horth 0
    rw [hsumB, Finset.sum_eq_zero (fun j hj => by rw [(hUψ j hj).1]; simp),
      Finset.sum_eq_zero (fun i hi => by rw [(hUb i hi).1]; simp), hUp.1, hUc₁.1, hUy₂.1,
      hUy₃.1, hUx₄.1, hχp] at hU0x
    push_cast at hU0x
    have h4 : 1 + η₂ * χ y₂ x + δ₄ * χ x₄ x = 0 := by linear_combination (hΘx' + hU0x) / 2
    have hU1x := horth 1
    have hsψ : ∑ j ∈ Finset.Icc 1 (k - 1), (U (ψ j) 1 : ℂ) * χ (ψ j) x =
        ((k : ℂ) - 1) * (δ₁ * (χ c₁ x + δ₁)) := by
      rw [Finset.sum_congr rfl fun j hj =>
        show (U (ψ j) 1 : ℂ) * χ (ψ j) x = (δ₁ : ℂ) * (χ c₁ x + δ₁) by
          rw [(hUψ j hj).2, hψx j hj], Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
        show k - 1 + 1 - 1 = k - 1 by omega, hk1]
    have hsν : ∑ i ∈ Finset.range k, (U (b' i) 1 : ℂ) * χ (b' i) x =
        (k : ℂ) * (-(δ₁ : ℂ) * χ (ν' 1) x) := by
      rw [Finset.sum_congr rfl fun i hi =>
        show (U (b' i) 1 : ℂ) * χ (b' i) x = -(δ₁ : ℂ) * χ (ν' 1) x by
          rw [(hUb i hi).2, hνx i hi]
          push_cast
          ring, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsumB, hsψ, hsν, hUp.2, hUc₁.2, hUy₂.2, hUy₃.2, hUx₄.2] at hU1x
    push_cast at hU1x
    have hv : χ (ν' 1) x = χ c₁ x + δ₁ := by
      have h : (k : ℂ) * ((δ₁ : ℂ) * (χ c₁ x + δ₁ - χ (ν' 1) x)) = 0 := by
        linear_combination hU1x + h4 + hδ₁sq
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hk0
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' hδ₁0
        · linear_combination -h''
    exact ⟨hψx, fun i hi => (hνx i hi).trans hv, hΘx', h4⟩
  refine ⟨hφ1, hex, δ₁, η₂, η₃, δ₄, c₁, y₂, y₃, x₄, ψ, b', ?_⟩
  unfold ActualPrincipalBlockFamily
  refine ⟨hlφ, hδ₁, hη₂, hη₃, hδ₄, ?_, ha_inj, hb'inj, ha_x', hb'_x, hb'_a, hlist, hcardB, ?_, ?_,
    hoddrel⟩
  · simp [List.nodup_cons, h01, h02, h03, h04, h12', h13', h14, h23', h24, h34]
  · intro c hc
    rw [hpar c hc]
    have hc' : c ∈ ({principal, c₁, y₂, y₃, x₄} ∪ (Finset.Icc 1 (k - 1)).image ψ ∪
        (Finset.range k).image b' : Finset basis.index) := by
      rw [← hlist]
      exact hc
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image] at hc'
    rcases hc' with ((rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩) | ⟨i, hi, rfl⟩
    · rw [hUp.1]
      simp
    · rw [hUc₁.1]
      rcases hδ₁ with h | h <;> rw [h] <;> simp
    · rw [hUy₂.1]
      rcases hη₂ with h | h <;> rw [h] <;> simp
    · rw [hUy₃.1]
      rcases hη₃ with h | h <;> rw [h] <;> simp
    · rw [hUx₄.1]
      simp only [Ne.symm h04, Ne.symm h14, Ne.symm h24, Ne.symm h34, or_self, iff_false,
        Int.not_odd_iff_even]
      exact even_two_mul δ₄
    · rw [(hUψ j hj).1]
      obtain ⟨hj0, hj1, hj2, hj3, -⟩ := ha_x' j hj
      simp [hj0, hj1, hj2, hj3]
    · rw [(hUb i hi).1]
      obtain ⟨hi0, hi1, hi2, hi3, -⟩ := hb'_x i hi
      simp [hi0, hi1, hi2, hi3]
  · intro y hy
    have hval' : ∀ c ∈ B, χ c (t * y) = (U c 0 : ℂ) + U c 1 * (1 + (e : ℂ) * φ y) :=
      fun c hc => hU c hc y hy
    refine ⟨?_, ?_, ?_, ?_, fun j hj => ?_, fun i hi => ?_⟩
    · show χ c₁ (t * y) = _
      rw [hval' c₁ hc₁, hUc₁.1, hUc₁.2]
      push_cast
      ring
    · show χ y₂ (t * y) = _
      rw [hval' y₂ hy₂B, hUy₂.1, hUy₂.2]
      push_cast
      ring
    · show χ y₃ (t * y) = _
      rw [hval' y₃ hy₃B, hUy₃.1, hUy₃.2]
      push_cast
      ring
    · show χ x₄ (t * y) = _
      rw [hval' x₄ hx₄, hUx₄.1, hUx₄.2]
      push_cast
      ring
    · show χ (ψ j) (t * y) = _
      rw [hval' (ψ j) (hψB j hj), (hUψ j hj).1, (hUψ j hj).2]
      push_cast
      ring
    · show χ (b' i) (t * y) = _
      rw [hval' (b' i) (hb'B i hi), (hUb i hi).1, (hUb i hi).2]
      push_cast
      ring

end CFSG.Semidihedral.Principal
