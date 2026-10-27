module

public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderModel
public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerSylowWreathed
public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderGroupModel

public section

open scoped Classical

namespace CFSG.Wreathed.BrauerWreathedOrder

open Matrix CFSG.DesarguesianPlanes CFSG.BrauerLinearThree

theorem factorization_two_mul_odd (a : ℕ) {m : ℕ} (hm : Odd m) :
    (2 ^ a * m).factorization 2 = a := by
  rw [Nat.factorization_mul (by positivity) hm.pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hm)
      (even_iff_two_dvd.mpr h)), add_zero]

theorem factorization_sq_sub_one {q n d : ℕ} (hq : q % 4 = 1) (hqd : q - 1 = 2 ^ n * d)
    (hd : Odd d) : 2 ^ (q ^ 2 - 1).factorization 2 = 2 * 2 ^ n := by
  obtain ⟨v, hv⟩ : ∃ v, q + 1 = 2 * (2 * v + 1) := ⟨(q - 1) / 4, by omega⟩
  have hq1 : 1 ≤ q := by omega
  have hsq : q ^ 2 - 1 = 2 ^ (n + 1) * (d * (2 * v + 1)) := by
    have : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      zify [hq1, Nat.one_le_pow 2 q hq1]
      ring
    rw [this, hqd, hv]
    ring
  rw [hsq, factorization_two_mul_odd _ (hd.mul (odd_two_mul_add_one v)), pow_succ, mul_comm]

theorem isSquare_units_iff {F : Type} [Field F] {u : Fˣ} : IsSquare u ↔ IsSquare (u : F) := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, by simp⟩
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
    exact ⟨Units.mk0 r hr0, Units.ext (by simpa using hr)⟩

theorem exists_nonsquare_neg_nonsquare {F : Type} [Field F] [Fintype F]
    (hq : Fintype.card F % 4 = 1) : ∃ b : Fˣ, ¬ IsSquare b ∧ ¬ IsSquare (-b) := by
  have hF : ringChar F ≠ 2 := by
    intro h
    have := FiniteField.even_card_of_char_two h
    omega
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hF
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha ⟨0, by simp⟩
  refine ⟨Units.mk0 a ha0, fun h => ha (by simpa using isSquare_units_iff.mp h), fun h => ?_⟩
  apply ha
  obtain ⟨s, hs⟩ := (FiniteField.isSquare_neg_one_iff (F := F)).mpr (by omega)
  obtain ⟨r, hr⟩ := isSquare_units_iff.mp h
  refine ⟨s * r, ?_⟩
  have hr' : -a = r * r := by simpa using hr
  calc a = (-1) * (-a) := by ring
    _ = (s * s) * (r * r) := by rw [hs, hr']
    _ = s * r * (s * r) := by ring

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
  {Z : Subgroup (GL (Fin 2) F)} [Z.Normal] {J : G}
  (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2) (hq : Nat.card F % 4 = 1)

include hZ hZodd h2 hJ hq in
theorem mem_centerSub_of_commute_sylow (P : Sylow 2 (Subgroup.centralizer ({J} : Set G)))
    {c : Subgroup.centralizer ({J} : Set G)}
    (hcomm : ∀ y ∈ (P : Subgroup (Subgroup.centralizer ({J} : Set G))), c * y = y * c) :
    (c : G) ∈ centerSub φ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, α, -, -, -, ⟨SC, hSC⟩, -, -, hJ₁⟩ := exists_wreathed_sylow φ hZ hZodd h2 hJ hq rfl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Subgroup.centralizer ({J} : Set G)) SC P
  set s := g⁻¹ * c * g with hs
  have hscomm : ∀ y ∈ (SC : Subgroup (Subgroup.centralizer ({J} : Set G))), s * y = y * s := by
    intro y hy
    have hy' : g * y * g⁻¹ ∈ (P : Subgroup (Subgroup.centralizer ({J} : Set G))) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      have := Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) _ hy
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    have h := hcomm _ hy'
    calc s * y = g⁻¹ * (c * (g * y * g⁻¹)) * g := by rw [hs]; group
      _ = g⁻¹ * ((g * y * g⁻¹) * c) * g := by rw [h]
      _ = y * s := by rw [hs]; group
  have hmem : ∀ x ∈ Subgroup.closure {linearCentralizerHom φ (diagGL α 1),
      linearCentralizerHom φ (diagGL 1 α), swapW φ}, (s : G) * x = x * s := by
    intro x hx
    rw [← hSC] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact congrArg Subtype.val (hscomm y hy)
  have hJ₁mem : invJ₁ φ ∈ Subgroup.closure {linearCentralizerHom φ (diagGL α 1),
      linearCentralizerHom φ (diagGL 1 α), swapW φ} := by
    rw [← hJ₁]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
  have hWmem : swapW φ ∈ Subgroup.closure {linearCentralizerHom φ (diagGL α 1),
      linearCentralizerHom φ (diagGL 1 α), swapW φ} :=
    Subgroup.subset_closure (by simp)
  have hsJ : J * (s : G) = s * J := (Subgroup.mem_centralizer_singleton_iff.mp s.2).symm
  obtain ⟨a, b, hab⟩ := exists_diag_of_commute φ hZ hZodd h2 hsJ (hmem _ hJ₁mem).symm
  have hsW := hmem _ hWmem
  rw [hab] at hsW
  have hcom := commute_of_linearCentralizerHom_commute φ hZ hZodd h2 hsW
  rw [swapGL_mul_diagGL] at hcom
  have hab' : a = b := by
    have := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 1) hcom
    exact Units.ext (by simpa [diagGL, swapGL, Matrix.mul_apply, Fin.sum_univ_two] using this)
  have hsC : (s : G) ∈ centerSub φ := by
    rw [mem_centerSub]
    refine ⟨a, ?_⟩
    rw [hab, ← hab']
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagGL, GeneralLinearGroup.scalar]
  have hgJ : J * (g : G) = g * J := (Subgroup.mem_centralizer_singleton_iff.mp g.2).symm
  have hsg := commute_of_mem_centerSub φ hsC hgJ
  have hc : (c : G) = g * s * g⁻¹ := by
    rw [hs]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hc, ← hsg, Subgroup.coe_inv, mul_inv_cancel_right]
  exact hsC

section Wreath

open CFSG.Wreathed.BrauerWong

variable {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
  (φx : Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G) ≃*
    GL (Fin 2) F ⧸ Z)

omit [Finite G] in
include hn in
theorem orderOf_modelHom_x : orderOf (wreathModelHom S e (Original.x (2 ^ n))) = 2 := by
  rw [orderOf_injective _ (wreathModelHom_injective S e)]
  exact (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1

include hn φx hZ hZodd h2 hq in
theorem factorization_card_sub_one : (Nat.card F - 1).factorization 2 = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, α, -, hW, -, ⟨SC, hSC⟩, -⟩ :=
    exists_wreathed_sylow φx hZ hZodd h2 (orderOf_modelHom_x hn) hq rfl
  set k := (Nat.card F - 1).factorization 2
  have hSN : (S : Subgroup G) ≤
      Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G) :=
    sylow_le_involutionCentralizer n hn S e
  have h1 : Nat.card (SC : Subgroup (Subgroup.centralizer
      ({wreathModelHom S e (Original.x (2 ^ n))} : Set G))) = 2 ^ (2 * k + 1) := by
    rw [← hW.card_eq, ← hSC, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have h3 : Nat.card ((S.subtype hSN : Sylow 2 _) : Subgroup (Subgroup.centralizer
      ({wreathModelHom S e (Original.x (2 ^ n))} : Set G))) = 2 ^ (2 * n + 1) := by
    rw [Sylow.coe_subtype, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv,
      card_sylow_model S e]
    ring
  have h4 : Nat.card (SC : Subgroup (Subgroup.centralizer
      ({wreathModelHom S e (Original.x (2 ^ n))} : Set G))) =
      Nat.card ((S.subtype hSN : Sylow 2 _) : Subgroup (Subgroup.centralizer
        ({wreathModelHom S e (Original.x (2 ^ n))} : Set G))) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  rw [h1, h3] at h4
  have := Nat.pow_right_injective (le_refl 2) h4
  omega

include hn hZ hZodd h2 hq in
theorem exists_scalar_eq_modelHom_a :
    ∃ α₀ : Fˣ, linearCentralizerHom φx (GeneralLinearGroup.scalar (Fin 2) α₀) =
      wreathModelHom S e (Original.a (2 ^ n)) := by
  have hSN : (S : Subgroup G) ≤
      Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G) :=
    sylow_le_involutionCentralizer n hn S e
  set a' : Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G) :=
    ⟨wreathModelHom S e (Original.a (2 ^ n)), hSN (wreathModelHom_mem S e _)⟩
  have hcomm : ∀ y ∈ ((S.subtype hSN : Sylow 2 _) : Subgroup _), a' * y = y * a' := by
    intro y hy
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hy
    apply Subtype.ext
    have hc := modelCenter_conj S e hn
      (⟨Original.a (2 ^ n), Subgroup.mem_zpowers _, rfl⟩ :
        wreathModelHom S e (Original.a (2 ^ n)) ∈ modelCenter S e) hy
    change wreathModelHom S e (Original.a (2 ^ n)) * y = y * wreathModelHom S e (Original.a (2 ^ n))
    calc wreathModelHom S e (Original.a (2 ^ n)) * y =
        y * ((y : G)⁻¹ * wreathModelHom S e (Original.a (2 ^ n)) * y) := by group
      _ = y * wreathModelHom S e (Original.a (2 ^ n)) := by rw [hc]
  exact (mem_centerSub φx).mp
    (mem_centerSub_of_commute_sylow φx hZ hZodd h2 (orderOf_modelHom_x hn) hq _ hcomm)

omit [Finite G] in
include hn in
theorem not_isSquare_of_scalar_eq_modelHom_a {d : ℕ} (hqd : Nat.card F - 1 = 2 ^ n * d)
    (hd : Odd d) {α₀ : Fˣ}
    (hα₀ : linearCentralizerHom φx (GeneralLinearGroup.scalar (Fin 2) α₀) =
      wreathModelHom S e (Original.a (2 ^ n))) : ¬ IsSquare α₀ := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card] at hqd
  rintro ⟨r, rfl⟩
  have h2n : 2 * 2 ^ (n - 1) = 2 ^ n := by
    rw [← pow_succ']
    congr 1
    omega
  have hpow : (r * r) ^ (2 ^ n / 2) = r ^ 2 ^ n := by
    rw [← pow_two, ← pow_mul, WreathGenerators.half_eq (by omega), h2n]
  have hx : wreathModelHom S e (Original.x (2 ^ n)) =
      linearCentralizerHom φx (GeneralLinearGroup.scalar (Fin 2) (r ^ 2 ^ n)) :=
    (wreathModelHom_x_eq n S e).trans (by rw [← hα₀, ← map_pow, ← map_pow, hpow])
  have hodd : Odd (orderOf (wreathModelHom S e (Original.x (2 ^ n)))) := by
    rw [hx]
    exact (odd_orderOf_pow_two_pow hqd hd r).of_dvd_nat
      ((orderOf_map_dvd _ _).trans (orderOf_map_dvd _ _))
  rw [orderOf_modelHom_x hn] at hodd
  exact absurd hodd (by decide)

include hn φx hZ hZodd h2 hq in
theorem exists_card_sub_one_eq_two_pow_mul_odd :
    ∃ d : ℕ, Nat.card F - 1 = 2 ^ n * d ∧ Odd d := by
  have hk := factorization_card_sub_one hZ hZodd h2 hq hn φx
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have hq0 : Nat.card F - 1 ≠ 0 := by omega
  refine ⟨(Nat.card F - 1) / 2 ^ n, ?_, ?_⟩
  · have := Nat.ordProj_mul_ordCompl_eq_self (Nat.card F - 1) 2
    rw [hk] at this
    exact this.symm
  · have := Nat.coprime_ordCompl Nat.prime_two hq0
    rw [hk] at this
    exact Nat.coprime_two_left.mp this

include hq in
omit [Finite G] in
theorem five_le_card : 5 ≤ Nat.card F := by
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  omega

include hn φx hZ hZodd h2 hq in
theorem exists_conditionalCompatibleModelData_of_linear (p f : ℕ) (hcard : Nat.card F = p ^ f) :
    ∃ (F' : Type) (_ : Field F') (_ : Finite F') (Sigma : Subgroup (F' ≃+* F')) (b : F'ˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F') = b)
      (ρ : centralizerFullQuotient n hn S e →*
        ComponentClassification.CatalogueSchreierLinearTwo.coordinateE F')
      (Ψ : CyclicCentralSL2Extension.SemilinearExtension F' b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn) Sigma hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F' Sigma b hSigma ρ Ψ := by
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨d, hqd, hd⟩ := exists_card_sub_one_eq_two_pow_mul_odd hZ hZodd h2 hq hn φx
  have hF5 := five_le_card hq
  have hq3 : 3 ≤ Nat.card F := by omega
  obtain ⟨α₀, hα₀⟩ := exists_scalar_eq_modelHom_a hZ hZodd h2 hq hn φx
  have hα₀sq := not_isSquare_of_scalar_eq_modelHom_a hn φx hqd hd hα₀
  have hq' : Fintype.card F % 4 = 1 := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨b, hb, hnb⟩ := exists_nonsquare_neg_nonsquare hq'
  exact ⟨F, inferInstance, inferInstance, ⊥, b, bot_fixes b, modelRho hn φx hZ hZodd h2 hq3 hα₀,
    semilinearEquiv φx hZ hZodd h2 hq3 hqd hd hn b hb hnb,
    conditionalCompatibleModelData hn φx hZ hZodd h2 hq3 hα₀ hqd hd p f hcard hα₀sq hF5 b hb hnb⟩

include hn φx hZ hZodd h2 hq in
theorem exists_sylow_not_isCyclic_of_linear (p f : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f) :
    ∃ U : Sylow 2 (centralizerSimpleLayer n hn S e),
      ¬ IsCyclic (U : Subgroup (centralizerSimpleLayer n hn S e)) := by
  obtain ⟨d, hqd, hd⟩ := exists_card_sub_one_eq_two_pow_mul_odd hZ hZodd h2 hq hn φx
  have hF5 := five_le_card hq
  have hq3 : 3 ≤ Nat.card F := by omega
  obtain ⟨α₀, hα₀⟩ := exists_scalar_eq_modelHom_a hZ hZodd h2 hq hn φx
  have hα₀sq := not_isSquare_of_scalar_eq_modelHom_a hn φx hqd hd hα₀
  let U : Sylow 2 (centralizerSimpleLayer n hn S e) := Classical.choice Sylow.nonempty
  exact ⟨U, centralizerSimpleLayer_sylow_not_isCyclic hn φx hZ hZodd h2 hq3 hα₀ hqd hd hα₀sq p f
    hp hpodd hf hcard hF5 U⟩

include hn φx hZ hZodd h2 hq in
theorem two_pow_factorization_sq_sub_one (p f : ℕ) (hcard : Nat.card F = p ^ f) :
    2 ^ ((p ^ f) ^ 2 - 1).factorization 2 = 2 * 2 ^ n := by
  obtain ⟨d, hqd, hd⟩ := exists_card_sub_one_eq_two_pow_mul_odd hZ hZodd h2 hq hn φx
  rw [← hcard]
  exact factorization_sq_sub_one hq hqd hd

end Wreath

end CFSG.Wreathed.BrauerWreathedOrder
