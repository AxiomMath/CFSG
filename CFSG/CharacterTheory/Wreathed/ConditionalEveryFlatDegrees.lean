module

public import CFSG.CharacterTheory.Wreathed.ConditionalEveryFlatWitness

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FlatEvery

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.FullDefectLabels CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.FlatCentralFourier CFSG.Wreathed.AdaptedBaseFusion
  CFSG.Wreathed.ConditionalGeneralBase CFSG.Wreathed.ConditionalExactOrder
  CFSG.Wreathed.LinearLocalTwistMoment

theorem blockFamilies_disjoint {ι : Type*} {p A Bq Dq ω : ι} {M : ℕ} {J : Finset ℕ}
    {χ : ℕ → ι} {γ : ℕ → Fin 4 → ι} {P Q : ℕ → Fin 2 → ι} {m : ℕ} {ψ : ZMod m × ZMod m → ι}
    {V : Finset (ZMod m × ZMod m)} (T : BlockFamilies p A Bq Dq ω M J χ γ P Q ψ V) :
    Disjoint ({p, A, Bq, Dq, ω} : Finset ι) (J.image χ) ∧
    Disjoint (({p, A, Bq, Dq, ω} : Finset ι) ∪ J.image χ)
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => P re.1 re.2) ∧
    Disjoint (({p, A, Bq, Dq, ω} : Finset ι) ∪ J.image χ ∪
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => P re.1 re.2))
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => Q re.1 re.2) ∧
    Disjoint (({p, A, Bq, Dq, ω} : Finset ι) ∪ J.image χ ∪
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => P re.1 re.2) ∪
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => Q re.1 re.2))
      (V.image ψ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_right]
    intro φ hφ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hφ
    obtain ⟨n1, n2, n3, n4, n5⟩ := T.hχcore j hj
    simp [n1, n2, n3, n4, n5]
  · rw [Finset.disjoint_right]
    intro φ hφ
    obtain ⟨⟨r, e⟩, hre, rfl⟩ := Finset.mem_image.mp hφ
    have hr := (Finset.mem_product.mp hre).1
    obtain ⟨n1, n2, n3, n4, n5, n6, -⟩ := T.label_out hr (T.P_eq hr e)
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      not_or]
    exact ⟨⟨n1, n2, n3, n4, n5⟩, fun ⟨j, hj, h⟩ => n6 j hj h.symm⟩
  · rw [Finset.disjoint_right]
    intro φ hφ
    obtain ⟨⟨r, e⟩, hre, rfl⟩ := Finset.mem_image.mp hφ
    have hr := (Finset.mem_product.mp hre).1
    obtain ⟨n1, n2, n3, n4, n5, n6, -⟩ := T.label_out hr (T.Q_eq hr e)
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      not_or]
    refine ⟨⟨⟨n1, n2, n3, n4, n5⟩, fun ⟨j, hj, h⟩ => n6 j hj h.symm⟩, ?_⟩
    rintro ⟨⟨r', e'⟩, hre', h⟩
    exact T.P_ne_Q (Finset.mem_product.mp hre').1 hr e' e h
  · rw [Finset.disjoint_right]
    intro φ hφ
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hφ
    obtain ⟨n1, n2, n3, n4, n5, n6, -⟩ := T.gen I hI
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      not_or]
    refine ⟨⟨⟨⟨n1, n2, n3, n4, n5⟩, fun ⟨j, hj, h⟩ => n6 j hj h.symm⟩, ?_⟩, ?_⟩
    · rintro ⟨⟨r', e'⟩, hre', h⟩
      have hr' := (Finset.mem_product.mp hre').1
      exact (T.label_out hr' (T.P_eq hr' e')).2.2.2.2.2.2 I hI h
    · rintro ⟨⟨r', e'⟩, hre', h⟩
      have hr' := (Finset.mem_product.mp hre').1
      exact (T.label_out hr' (T.Q_eq hr' e')).2.2.2.2.2.2 I hI h

theorem blockFamilies_degree_multiset {ι R : Type*} {p A Bq Dq ω : ι} {M : ℕ} {J : Finset ℕ}
    {χ : ℕ → ι} {γ : ℕ → Fin 4 → ι} {P Q : ℕ → Fin 2 → ι} {m : ℕ} {ψ : ZMod m × ZMod m → ι}
    {V : Finset (ZMod m × ZMod m)} (T : BlockFamilies p A Bq Dq ω M J χ γ P Q ψ V)
    {B : Finset ι}
    (hB : B = ({p, A, Bq, Dq, ω} : Finset ι) ∪ J.image χ ∪
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => P re.1 re.2) ∪
      ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => Q re.1 re.2) ∪
      V.image ψ) (d : ι → R) {δ b d' Δ : R} (hdχ : ∀ j ∈ J, d (χ j) = δ)
    (hdP : ∀ r ∈ Finset.Ico 1 M, ∀ e, d (P r e) = b)
    (hdQ : ∀ r ∈ Finset.Ico 1 M, ∀ e, d (Q r e) = d') (hdψ : ∀ I ∈ V, d (ψ I) = Δ) :
    Multiset.map d B.val = {d p, d A, d Bq, d Dq, d ω} + Multiset.replicate J.card δ +
      Multiset.replicate (2 * (M - 1)) b + Multiset.replicate (2 * (M - 1)) d' +
      Multiset.replicate V.card Δ := by
  obtain ⟨h1, h2, h3, h4⟩ := blockFamilies_disjoint T
  have iP : Set.InjOn (fun re : ℕ × Fin 2 => P re.1 re.2)
      (Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2)) : Finset (ℕ × Fin 2)) := by
    rintro ⟨r, e⟩ hre ⟨r', e'⟩ hre' h
    obtain ⟨h₁, h₂⟩ := T.P_inj (Finset.mem_product.mp hre).1 (Finset.mem_product.mp hre').1 h
    exact Prod.ext h₁ h₂
  have iQ : Set.InjOn (fun re : ℕ × Fin 2 => Q re.1 re.2)
      (Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2)) : Finset (ℕ × Fin 2)) := by
    rintro ⟨r, e⟩ hre ⟨r', e'⟩ hre' h
    obtain ⟨h₁, h₂⟩ := T.Q_inj (Finset.mem_product.mp hre).1 (Finset.mem_product.mp hre').1 h
    exact Prod.ext h₁ h₂
  have hnodup : [p, A, Bq, Dq, ω].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true]
    exact ⟨⟨T.hAp.symm, T.hBp.symm, T.hDp.symm, T.hωp.symm⟩, ⟨T.hBA.symm, T.hDA.symm,
      T.hωA.symm⟩, ⟨T.hDB.symm, T.hωB.symm⟩, T.hωD.symm⟩
  exact (ConditionalCompleteBase.card_and_degree_multiset B d p A Bq Dq ω hnodup χ J T.hχinj P
    Q iP iQ V ψ T.geninj h1 h2 h3 h4 hB hdχ hdP hdQ hdψ).2

theorem degrees_gt_one {q : ℕ} (hq3 : 3 ≤ q) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    1 < (q : ℤ) ^ 3 ∧ 1 < (q : ℤ) ^ 2 + ε * q + 1 ∧ 1 < q * ((q : ℤ) ^ 2 + ε * q + 1) ∧
      1 < q * ((q : ℤ) + ε) ∧ 1 < (q : ℤ) ^ 3 - ε ∧
      1 < ((q : ℤ) + ε) * ((q : ℤ) ^ 2 + ε * q + 1) := by
  have hq' : (3 : ℤ) ≤ q := by exact_mod_cast hq3
  have h27 : (27 : ℤ) ≤ (q : ℤ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 3) hq' 3
    norm_num at this
    exact this
  rcases hε with rfl | rfl <;> refine ⟨by linarith, by nlinarith, by nlinarith, by nlinarith,
    by linarith, by nlinarith⟩

theorem flat_block_degrees
    {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (basis : FiniteIrreducibleCharacterBasis G)
    (B : basis.index) (hflat : FlatWreathedBlock basis ideal S e B)
    (eb : FiniteIrreducibleCharacterBasis (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G)))) (θB : eb.index)
    (nb : FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (θhat : nb.index) (hθ : InflatedLabel (oddCore_le_normalizer S) nb eb θB θhat)
    (hB : brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _)
        le_rfl nb θhat = centralCharacterResidueHom basis ideal B)
    (η : G) (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hord : orderOf ((modelBase S e).normalizerMonoidHom ⟨η, hη⟩) = 3) :
    let m : ℕ := 2 ^ n
    let M : ℕ := m / 2
    let q : ℕ := p ^ f
    let ε : ℤ := if q % 4 = 1 then 1 else -1
    let Qd : ℤ := (q : ℤ) ^ 2 + ε * q + 1
    let BB := coefficientBlock basis (localizedComplexIntegerRing ideal) B
    let deg : basis.index → ℤ := fun χ => (Module.finrank ℂ (basis.representation χ).vector : ℤ)
    (∃! χ, χ ∈ BB ∧ deg χ = 1) ∧
    (∀ χ ∈ BB, deg χ = 1 → (basis.representation χ).character = 1) ∧
    Multiset.map deg BB.val = {1, (q : ℤ) ^ 3, q * (q + ε)} + Multiset.replicate (m - 1) Qd +
      Multiset.replicate (m - 1) (q * Qd) + Multiset.replicate M ((q : ℤ) ^ 3 - ε) +
      Multiset.replicate ((m - 1) * (m - 2) / 6) ((q + ε) * Qd) ∧
    ∀ principal : basis.index, (basis.representation principal).character = 1 →
      BB = coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
      FlatWreathedBlock basis ideal S e principal := by
  intro m M q ε Qd BB deg
  obtain ⟨⟨F, _, _, sg, ρ, hcard, hodd, hρ, hlayer, hrange⟩, ⟨lam, hlam⟩, hA⟩ :=
    flat_witness_cubic hnonab n hn S e hfour p f hp hpodd hf hmodel ideal basis B hflat eb θB
      nb θhat hθ hB η hη hord
  obtain ⟨⟨σ0, υ0, g0, hg0⟩, hA⟩ := hA lam hlam F sg ρ hcard hodd hρ hlayer hrange
  have hm0 : 0 < 2 * 2 ^ n := by positivity
  have hθ0 := Complex.isPrimitiveRoot_exp (2 * 2 ^ n) hm0.ne'
  have hζ0 := hθ0.pow hm0 (show 2 * 2 ^ n = 2 * 2 ^ n from rfl)
  obtain ⟨⟨v, hv⟩, hA⟩ := hA _ hζ0 _ hθ0 rfl
  obtain ⟨⟨lamU, hlamU⟩, hA⟩ := hA v hv ⟨σ0, hg0.left_mem⟩ ⟨υ0, hg0.right_mem⟩ g0 hg0
  obtain ⟨⟨V, hV6, hVrep⟩, hA⟩ := hA lamU hlamU
  obtain ⟨⟨δ₀, δ₁, δ₂, δ₃, δ₄, α, β, γ, χ₀, χ₁, χ₂, χ₃, χ₄, ξ, P, Q, ψ, D, Δ, hcomp⟩, hA⟩ :=
    hA V hV6 hVrep
  obtain ⟨hC, hfb1, -⟩ := hA δ₀ δ₁ δ₂ δ₃ δ₄ α β γ χ₀ χ₁ χ₂ χ₃ χ₄ ξ P Q ψ D Δ hcomp
  obtain ⟨-, hinj, hξinj, hPQinj, hψinj, hξcore, hPQcore, hψcore, -, -, -, -, -, -, -, -,
    -, -, -, hdξ₀, hdPQ₀, hdψ₀, -, -, -, -, -, -, hBB₀, -⟩ := hcomp
  have hBB : BB = {χ₀, χ₁, χ₂, χ₃, χ₄} ∪ ((Finset.Ico 1 m).filter Odd).image ξ ∪
      (((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => P x.1 x.2) ∪
        ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => Q x.1 x.2)) ∪
      V.image ψ := hBB₀
  have hdξ : ∀ h ∈ (Finset.Ico 1 m).filter Odd, deg (ξ h) = D := hdξ₀
  have hdPQ : ∀ r ∈ Finset.Ico 1 M, ∀ er, deg (P r er) = deg χ₂ ∧ deg (Q r er) = deg χ₃ :=
    hdPQ₀
  have hdψ : ∀ I ∈ V, deg (ψ I) = Δ := hdψ₀
  clear hBB₀ hdξ₀ hdPQ₀ hdψ₀
  obtain ⟨⟨d₀, d₂, d₃, d₄⟩, -, dD, -, -, dΔ, -⟩ := hC
  have hfb1' : deg χ₁ = 1 := hfb1
  rw [hcard] at d₀ d₂ d₃ d₄ dD dΔ
  have d₀' : deg χ₀ = (q : ℤ) ^ 3 * deg χ₁ := d₀
  have d₂' : deg χ₂ = Qd * deg χ₁ := d₂
  have d₃' : deg χ₃ = q * Qd * deg χ₁ := d₃
  have d₄' : deg χ₄ = q * (q + ε) * deg χ₁ := d₄
  have dD' : D = ((q : ℤ) ^ 3 - ε) * deg χ₁ := dD
  have dΔ' : Δ = (q + ε) * Qd * deg χ₁ := dΔ
  clear d₀ d₂ d₃ d₄ dD dΔ
  rw [hfb1', mul_one] at d₀' d₂' d₃' d₄' dD' dΔ'
  have T := blockFamilies_of_distinct hinj hξinj hPQinj hψinj hξcore hPQcore hψcore
  have hB' : BB = ({χ₁, χ₀, χ₂, χ₃, χ₄} : Finset basis.index) ∪
      ((Finset.Ico 1 (2 ^ n)).filter Odd).image ξ ∪
      ((Finset.Ico 1 (2 ^ n / 2) ×ˢ (Finset.univ : Finset (Fin 2))).image fun re =>
        P re.1 re.2) ∪
      ((Finset.Ico 1 (2 ^ n / 2) ×ˢ (Finset.univ : Finset (Fin 2))).image fun re =>
        Q re.1 re.2) ∪ V.image ψ := by
    rw [hBB, Finset.insert_comm χ₀ χ₁, ← Finset.union_assoc]
  have hq3 : 3 ≤ q := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    exact le_trans hp3 (Nat.le_self_pow (by omega) p)
  have hε : ε = 1 ∨ ε = -1 := by
    by_cases h : q % 4 = 1
    · exact Or.inl (ite_eq_left h)
    · exact Or.inr (ite_eq_right h)
  obtain ⟨g₀, g₂, g₃, g₄, gξ, gψ⟩ := degrees_gt_one hq3 hε
  have hdP' : ∀ r ∈ Finset.Ico 1 (2 ^ n / 2), ∀ e', deg (P r e') = Qd := fun r hr e' => by
    rw [(hdPQ r hr e').1, d₂']
  have hdQ' : ∀ r ∈ Finset.Ico 1 (2 ^ n / 2), ∀ e', deg (Q r e') = q * Qd := fun r hr e' => by
    rw [(hdPQ r hr e').2, d₃']
  have hdξ' : ∀ h ∈ (Finset.Ico 1 (2 ^ n)).filter Odd, deg (ξ h) = (q : ℤ) ^ 3 - ε :=
    fun h hh => by rw [hdξ h hh, dD']
  have hdψ' : ∀ I ∈ V, deg (ψ I) = (q + ε) * Qd := fun I hI => by rw [hdψ I hI, dΔ']
  have hmul := blockFamilies_degree_multiset T hB' deg hdξ' hdP' hdQ' hdψ'
  have hJ : ((Finset.Ico 1 (2 ^ n)).filter Odd).card = 2 ^ n / 2 := by
    obtain ⟨K, -, -, -, hmK⟩ := modulus_split hn
    rw [hmK, show 4 * K / 2 = 2 * K by omega, show 4 * K = 2 * (2 * K) by ring]
    exact CFSG.Wreathed.ConditionalSquareRoot.card_filter_odd_Ico (2 * K)
  have hVc := ConditionalCompleteBase.card_orbit_representatives_two_pow V hV6 hVrep
  have hm4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hk : 2 * (2 ^ n / 2 - 1) + 1 = 2 ^ n - 1 := by
    have h2 : 2 ^ n = 2 * (2 ^ n / 2) :=
      (Nat.two_mul_div_two_of_even ((Nat.even_pow' (by omega)).mpr even_two)).symm
    omega
  have h1 : Module.finrank ℂ (basis.representation χ₁).vector = 1 := by
    have h' : (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) = 1 := hfb1'
    exact_mod_cast h'
  have hχ1 := character_eq_one_of_finrank_one hnonab (basis.representation χ₁) h1
  obtain ⟨hmemχ, hmemξ, hmemPQ⟩ := FlatRelative.mem_of_eq_union hBB
  have hmemψ := mem_gen_of_eq_union hBB
  have huniq : ∀ φ ∈ BB, deg φ = 1 → φ = χ₁ := by
    intro φ hφ hφ1
    rw [hB'] at hφ
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image]
      at hφ
    rcases hφ with ((((rfl | rfl | rfl | rfl | rfl) | ⟨h, hh, rfl⟩) | ⟨⟨r, e'⟩, hre, rfl⟩) |
      ⟨⟨r, e'⟩, hre, rfl⟩) | ⟨I, hI, rfl⟩
    · rfl
    · rw [d₀'] at hφ1
      exact absurd hφ1 (ne_of_gt g₀)
    · rw [d₂'] at hφ1
      exact absurd hφ1 (ne_of_gt g₂)
    · rw [d₃'] at hφ1
      exact absurd hφ1 (ne_of_gt g₃)
    · rw [d₄'] at hφ1
      exact absurd hφ1 (ne_of_gt g₄)
    · rw [hdξ' h hh] at hφ1
      exact absurd hφ1 (ne_of_gt gξ)
    · rw [hdP' r (Finset.mem_product.mp hre).1 e'] at hφ1
      exact absurd hφ1 (ne_of_gt g₂)
    · rw [hdQ' r (Finset.mem_product.mp hre).1 e'] at hφ1
      exact absurd hφ1 (ne_of_gt g₃)
    · rw [hdψ' I hI] at hφ1
      exact absurd hφ1 (ne_of_gt gψ)
  refine ⟨⟨χ₁, ⟨hmemχ.2.1, hfb1'⟩, fun φ ⟨hφ, hφ1⟩ => huniq φ hφ hφ1⟩,
    fun φ hφ hφ1 => by rw [huniq φ hφ hφ1]; exact hχ1, ?_, fun principal hprincipal => ?_⟩
  · rw [hmul, hJ, hVc, hfb1', d₀', d₂', d₃', d₄', ConditionalGlobalDegrees.multiset_degrees, hk]
  · have hχp : χ₁ = principal := basis.distinct (hχ1.trans hprincipal.symm)
    have hp0 : principal = principalCharacterLabel basis :=
      basis.distinct (hprincipal.trans (principalCharacterLabel_character basis).symm)
    refine ⟨?_, ?_⟩
    · rw [← hχp]
      exact (coefficientBlock_eq_of_mem _ _ hmemχ.2.1).symm
    · obtain ⟨-, -, -, -, -, -, -, hflat₀⟩ := principal_flat basis ideal hn S e
      rw [hp0]
      exact hflat₀

end CFSG.Wreathed.FlatEvery
