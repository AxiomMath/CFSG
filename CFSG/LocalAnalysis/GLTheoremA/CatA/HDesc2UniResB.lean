module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2LinResB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2UniRes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDescUniRes

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame
open CFSG.RankThree.PartOne.CTP
open Matrix

section Lifts

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem exists_pow_scalar_of_mem_primeFormD {n p : ℕ} (hn : 3 ≤ n)
    {β : MulAut (primeFormP h (idGram K n))} (hβ : β ∈ primeFormD h (idGram K n))
    (hβp : β ^ p = 1) :
    ∃ (A : primeFormUnitary h (idGram K n)) (c : Kˣ), h.norm (c : K) = 1 ∧
      (A : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) c ∧
        β = primeFormConjHom h (idGram K n) A := by
  obtain ⟨A, rfl⟩ := hβ
  have h1 : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨A ^ p, 1⟩ = 1 := by
    rw [primeFormPsi_apply, map_pow, hβp, map_one, one_mul]
  obtain ⟨-, c, hc1, hc⟩ :=
    (primeFormPsi_eq_one_iff h (isPrimeFormGram_idGram (K := K) (n := n)) hn ⟨A ^ p, 1⟩).1 h1
  exact ⟨A, c, hc1, by rwa [SubgroupClass.coe_pow] at hc, rfl⟩

theorem primeFormConjHom_eq_one_of_coe_eq_scalar {n : ℕ} {X : primeFormUnitary h (idGram K n)}
    {c : Kˣ} (hX : (X : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c) :
    primeFormConjHom h (idGram K n) X = 1 := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk, MulAut.one_apply]
  congr 1
  refine Subtype.ext ?_
  change (X : GL (Fin n) K) * (g : GL (Fin n) K) * (X : GL (Fin n) K)⁻¹ = g
  rw [hX, GeneralLinearGroup.scalar_commute c (g : GL (Fin n) K), mul_inv_cancel_right]

end Lifts

section InnerPart

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem three_dvd_card_sub_one (h : UnitaryFieldData ℓ f K) (h3 : 3 ∣ ℓ ^ f + 1) :
    3 ∣ Nat.card K - 1 := by
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hcard : Nat.card K - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
    rw [h.card, show ℓ ^ (2 * f) = (ℓ ^ f) ^ 2 by rw [← pow_mul, mul_comm]]
    zify [hq1, Nat.one_le_pow 2 (ℓ ^ f) (by omega)]
    ring
  rw [hcard]
  exact Dvd.dvd.mul_right h3 _

theorem card_le_three_of_le_primeFormD (h : UnitaryFieldData ℓ f K) [CharP K 2]
    (h3 : 3 ∣ ℓ ^ f + 1) (hq3 : 3 < ℓ ^ f)
    {E : Subgroup (MulAut (primeFormP h (idGram K 3)))} (hE : IsElemAbelian 3 E)
    (hED : E ≤ primeFormD h (idGram K 3)) {t : primeFormP h (idGram K 3)} (ht : orderOf t = 2)
    (hfix : ∀ e ∈ E, e t = t) : Nat.card E ≤ 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h.finite
  have hne : ¬ (3 = 3 ∧ ℓ ^ f = 2) := fun h' => by omega
  by_contra hlt
  push Not at hlt
  have hpE : IsPGroup 3 E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g g.2)⟩
  obtain ⟨n, hn⟩ := hpE.exists_card_eq
  have h9 : 3 ^ 2 ≤ Nat.card E := by
    rw [hn] at hlt ⊢
    have h1 : 1 < n := by
      by_contra h
      push Not at h
      interval_cases n <;> simp at hlt
    exact Nat.pow_le_pow_right (by norm_num) h1
  obtain ⟨D, hDE, hD9⟩ := CFSG.LocalAnalysis.GLTheoremA.exists_sub_card_pow Nat.prime_three hE h9
  have hD : IsElemAbelian 3 D :=
    ⟨⟨⟨fun x y => Subtype.ext (show (x : MulAut (primeFormP h (idGram K 3))) * y = y * x from
      congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hDE x.2⟩ ⟨y, hDE y.2⟩))⟩⟩,
      fun x hx => hE.2 x (hDE hx)⟩
  have hD1 : D ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hD9
    norm_num at hD9
  obtain ⟨⟨a, haD⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hD1
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  obtain ⟨b, hbD, hba⟩ : ∃ b ∈ D, b ∉ Subgroup.zpowers a := by
    by_contra hc
    push Not at hc
    have hle := Subgroup.card_le_of_le (show D ≤ Subgroup.zpowers a from hc)
    rw [Nat.card_zpowers, hD9] at hle
    have := orderOf_le_of_pow_eq_one (by norm_num) (hD.2 a haD)
    omega
  have hab : a * b = b * a := congrArg Subtype.val (hD.1.is_comm.comm ⟨a, haD⟩ ⟨b, hbD⟩)
  obtain ⟨A, α, hαn, hA3, rfl⟩ :=
    exists_pow_scalar_of_mem_primeFormD (le_refl 3) (hED (hDE haD)) (hD.2 _ haD)
  obtain ⟨B, β, hβn, hB3, rfl⟩ :=
    exists_pow_scalar_of_mem_primeFormD (le_refl 3) (hED (hDE hbD)) (hD.2 _ hbD)
  have ht2 : t ^ 2 = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  obtain ⟨U, rfl, hU2⟩ := exists_lift_sq_eq_one ht2
  set u : GL (Fin 3) K := (U : GL (Fin 3) K) with hu
  have hu1 : u ≠ 1 := by
    intro h1
    have hU : U = 1 := Subtype.ext h1
    rw [hU, QuotientGroup.mk_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hu2 : u * u = 1 := by
    rw [hu, ← Subgroup.coe_mul, ← sq, hU2, Subgroup.coe_one]
  have hAU := mul_comm_of_primeFormConjHom_fix hU2 (hfix _ (hDE haD))
  have hBU := mul_comm_of_primeFormConjHom_fix hU2 (hfix _ (hDE hbD))
  have hz1 : primeFormConjHom h (idGram K 3) (A * B * A⁻¹ * B⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hab]
    group
  obtain ⟨z, -, hz⟩ := (primeFormConjHom_eq_one_iff_of_ne (le_refl 3) hne _).1 hz1
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.coe_inv] at hz
  have hABg := HDescLinRes.commute_of_commutator_eq_scalar hu1 hu2 hAU hBU hz
  obtain ⟨μ, hμ⟩ := HDescLinRes.exists_cube_root_of_commute hA3 hu1 hu2 hAU
  obtain ⟨ν, hν⟩ := HDescLinRes.exists_cube_root_of_commute hB3 hu1 hu2 hBU
  have hμn : h.norm (μ : K) = 1 :=
    norm_eq_one_of_pow_norm Nat.prime_three (by norm_num) h3 (by rw [hμ]; exact hαn)
  have hνn : h.norm (ν : K) = 1 :=
    norm_eq_one_of_pow_norm Nat.prime_three (by norm_num) h3 (by rw [hν]; exact hβn)
  have hμ'n : h.norm ((μ⁻¹ : Kˣ) : K) = 1 := by
    simpa [Units.val_inv_eq_inv_val] using norm_inv_eq_one hμn
  have hν'n : h.norm ((ν⁻¹ : Kˣ) : K) = 1 := by
    simpa [Units.val_inv_eq_inv_val] using norm_inv_eq_one hνn
  set A' := scalarU h 3 μ⁻¹ hμ'n * A with hA'
  set B' := scalarU h 3 ν⁻¹ hν'n * B with hB'
  have hA'c : primeFormConjHom h (idGram K 3) A' = primeFormConjHom h (idGram K 3) A := by
    rw [hA', map_mul, conjHom_scalarU (le_refl 3) hne, one_mul]
  have hB'c : primeFormConjHom h (idGram K 3) B' = primeFormConjHom h (idGram K 3) B := by
    rw [hB', map_mul, conjHom_scalarU (le_refl 3) hne, one_mul]
  have hA'3s : A' ^ 3 = 1 := rescale_pow_eq_one (le_refl 3) hne hμ'n (by rw [hμ]; exact hA3)
  have hB'3s : B' ^ 3 = 1 := rescale_pow_eq_one (le_refl 3) hne hν'n (by rw [hν]; exact hB3)
  set a' : GL (Fin 3) K := (A' : GL (Fin 3) K) with ha'
  set b' : GL (Fin 3) K := (B' : GL (Fin 3) K) with hb'
  have hsc : ∀ (c : Kˣ) (g : GL (Fin 3) K),
      GeneralLinearGroup.scalar (Fin 3) c * g = g * GeneralLinearGroup.scalar (Fin 3) c :=
    fun c g => GeneralLinearGroup.scalar_commute c g
  have ha'e : a' = GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * A := by
    rw [ha', hA', Subgroup.coe_mul, coe_scalarU]
  have hb'e : b' = GeneralLinearGroup.scalar (Fin 3) ν⁻¹ * B := by
    rw [hb', hB', Subgroup.coe_mul, coe_scalarU]
  have hA'3 : a' ^ 3 = 1 := by
    rw [ha', ← Subgroup.coe_pow, hA'3s, Subgroup.coe_one]
  have hB'3 : b' ^ 3 = 1 := by
    rw [hb', ← Subgroup.coe_pow, hB'3s, Subgroup.coe_one]
  have hA'B' : a' * b' = b' * a' := by
    rw [ha'e, hb'e]
    calc GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * (A : GL (Fin 3) K) *
          (GeneralLinearGroup.scalar (Fin 3) ν⁻¹ * B)
        = GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * GeneralLinearGroup.scalar (Fin 3) ν⁻¹ *
            ((A : GL (Fin 3) K) * B) := by
          rw [mul_assoc, ← mul_assoc (A : GL (Fin 3) K), ← hsc ν⁻¹ A]; group
      _ = GeneralLinearGroup.scalar (Fin 3) ν⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ⁻¹ *
            ((B : GL (Fin 3) K) * A) := by rw [hABg, hsc μ⁻¹]
      _ = GeneralLinearGroup.scalar (Fin 3) ν⁻¹ * (B : GL (Fin 3) K) *
            (GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * A) := by
          rw [mul_assoc (GeneralLinearGroup.scalar (Fin 3) ν⁻¹) (B : GL (Fin 3) K),
            ← mul_assoc (B : GL (Fin 3) K), ← hsc μ⁻¹ B]
          group
  have hA'U : a' * u = u * a' := by
    rw [ha'e, mul_assoc, hAU, ← mul_assoc, ← mul_assoc, hsc μ⁻¹ u]
  have hB'U : b' * u = u * b' := by
    rw [hb'e, mul_assoc, hBU, ← mul_assoc, ← mul_assoc, hsc ν⁻¹ u]
  set s : Set (GL (Fin 3) K) := {a', b'} with hs
  have hss : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    intro x hx y hy
    rw [hs, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hA'B'
    · exact hA'B'.symm
    · rfl
  have hcomm : ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, x * y = y * x := by
    intro x hx y hy
    letI := Subgroup.closureCommGroupOfComm (k := s) (fun x hx y hy _ => hss x hx y hy)
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : Subgroup.closure s) ⟨y, hy⟩)
  have hexp : ∀ x ∈ Subgroup.closure s, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rw [hs, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hA'3
      · exact hB'3
    | one => exact one_pow 3
    | mul x y hx hy ihx ihy => rw [(Commute.mul_pow (hcomm x hx y hy) 3), ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd Nat.prime_three (three_dvd_card_sub_one h h3)
  obtain ⟨P, hP⟩ := exists_conj_diagonal_of_exponent_prime (n := 3) (p := 3) ⟨ζ, hζ⟩
    (Subgroup.closure s) hcomm hexp
  have hPA := hP a' (Subgroup.subset_closure (by rw [hs]; exact Set.mem_insert _ _))
  have hPB := hP b' (Subgroup.subset_closure (by rw [hs]; exact Set.mem_insert_of_mem _ rfl))
  set da : Fin 3 → K := fun l => ((P * a' * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) l l
    with hdadef
  set db : Fin 3 → K := fun l => ((P * b' * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) l l
    with hdbdef
  have hda : ((P * a' * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal da :=
    glConj_eq_diagonal hPA
  have hdb : ((P * b' * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal db :=
    glConj_eq_diagonal hPB
  have hda3 := HDescLinRes.diag_pow_three_eq_one hA'3 hda
  have hdb3 := HDescLinRes.diag_pow_three_eq_one hB'3 hdb
  set W := P * u * P⁻¹ with hW
  have hWcomm : ∀ {X : GL (Fin 3) K} {d : Fin 3 → K}, X * u = u * X →
      ((P * X * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d →
      diagonal d * (W : Matrix (Fin 3) (Fin 3) K) = (W : Matrix (Fin 3) (Fin 3) K) * diagonal d := by
    intro X d hXu hd
    rw [← hd, ← Units.val_mul, ← Units.val_mul]
    congr 1
    rw [hW]
    calc P * X * P⁻¹ * (P * u * P⁻¹) = P * (X * u) * P⁻¹ := by group
      _ = P * (u * X) * P⁻¹ := by rw [hXu]
      _ = P * u * P⁻¹ * (P * X * P⁻¹) := by group
  have hW2 : (W : Matrix (Fin 3) (Fin 3) K) * W = 1 := by
    rw [← Units.val_mul]
    have : W * W = 1 := by
      rw [hW]
      calc P * u * P⁻¹ * (P * u * P⁻¹) = P * (u * u) * P⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    rw [this, Units.val_one]
  by_cases hjoint : ∀ i j, i ≠ j → da i ≠ da j ∨ db i ≠ db j
  · apply hu1
    have h1 := HDescLinRes.eq_one_of_commute_two_diagonal_of_mul_self_eq_one hjoint
      (hWcomm hA'U hda) (hWcomm hB'U hdb) hW2
    have h1' : W = 1 := Units.ext h1
    calc u = P⁻¹ * W * P := by rw [hW]; group
      _ = 1 := by rw [h1']; group
  · push Not at hjoint
    obtain ⟨i, j, hij, hai, hbi⟩ := hjoint
    have hnc : ∃ l, da l ≠ da i := by
      by_contra hc
      push Not at hc
      apply ha1'
      have hai0 : da i ≠ 0 := by
        intro h0
        have := hda3 i
        rw [h0] at this
        norm_num at this
      have hsc' : P * a' * P⁻¹ = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (da i) hai0) := by
        apply Units.ext
        rw [hda, GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
        congr 1
        funext l
        exact hc l
      rw [← hA'c]
      exact primeFormConjHom_eq_one_of_coe_eq_scalar (HDescLinRes.eq_scalar_of_conj_eq_scalar hsc')
    obtain ⟨m, c, hc0, hbm⟩ := HDescLinRes.exists_pow_of_diag_eq hij hai hbi hda3 hdb3 hnc
    apply hba
    have hPB' : P * b' * P⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) * (P * a' * P⁻¹) ^ m := by
      apply Units.ext
      rw [hdb, Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val, hda,
        diagonal_pow, Units.val_mk0, Matrix.scalar_apply, diagonal_mul_diagonal]
      congr 1
      funext l
      rw [hbm l]
      rfl
    have hB'eq : b' = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) * a' ^ m := by
      have h1 : P * b' * P⁻¹ = P * (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) * a' ^ m) *
          P⁻¹ := by
        rw [hPB', conj_pow]
        calc GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) * (P * a' ^ m * P⁻¹)
            = (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) * P) * a' ^ m * P⁻¹ := by group
          _ = (P * GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0)) * a' ^ m * P⁻¹ := by
              rw [hsc]
          _ = P * (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) * a' ^ m) * P⁻¹ := by group
      have h2 := congrArg (fun g => P⁻¹ * g * P) h1
      simpa [mul_assoc] using h2
    have hS : ((B' * (A' ^ m)⁻¹ : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, ← ha', ← hb', hB'eq,
        mul_inv_cancel_right]
    have hSc := primeFormConjHom_eq_one_of_coe_eq_scalar hS
    have hBm : primeFormConjHom h (idGram K 3) B' = primeFormConjHom h (idGram K 3) A' ^ m := by
      have e : B' = (B' * (A' ^ m)⁻¹) * A' ^ m := by group
      rw [e, map_mul, hSc, one_mul, map_pow]
    rw [← hB'c, hBm, hA'c]
    exact Subgroup.npow_mem_zpowers _ m

end InnerPart

section FieldPart

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem card_le_three_mul_card_inf_primeFormD (h : UnitaryFieldData ℓ f K)
    (hne : ¬ (3 = 3 ∧ ℓ ^ f = 2)) {B : Subgroup (MulAut (primeFormP h (idGram K 3)))}
    (hB : ∀ b ∈ B, b ^ 3 = 1) :
    Nat.card B ≤ 3 * Nat.card (B ⊓ primeFormD h (idGram K 3) :
      Subgroup (MulAut (primeFormP h (idGram K 3)))) := by
  classical
  have := h.finite
  have hker := ker_primeFormFieldFactor h (isPrimeFormGram_idGram (K := K) (n := 3)) (le_refl 3) hne
  let φ : B →* (K ≃+* K) :=
    (primeFormFieldFactor h (isPrimeFormGram_idGram (K := K) (n := 3)) (le_refl 3) hne).comp
      B.subtype
  have hkerφ : Nat.card φ.ker = Nat.card (B ⊓ primeFormD h (idGram K 3) :
      Subgroup (MulAut (primeFormP h (idGram K 3)))) := by
    have h1 : φ.ker = (primeFormD h (idGram K 3)).subgroupOf B := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hker, MonoidHom.mem_ker]
      rfl
    rw [h1, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  haveI : IsCyclic (K ≃+* K) := by
    obtain ⟨σ₀, -, -, htop, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality h.prime
        (by have := h.one_le; omega) h.card
    exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ₀, htop⟩
  have hrange : Nat.card φ.range ∣ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    obtain ⟨y, hy⟩ := x
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hy
    apply Subtype.ext
    show φ b ^ 3 = 1
    rw [← map_pow, show b ^ 3 = 1 from Subtype.ext (hB b b.2), map_one]
  rw [← Subgroup.card_ker_mul_card_range φ, hkerφ, mul_comm]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd (by norm_num) hrange)

end FieldPart

section TwoByTwo

variable {K : Type} [Field K]

@[expose] def suTwoJ : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

@[expose] def suTwoP (ω : K) : Matrix (Fin 2) (Fin 2) K := !![1, ω; 1, ω ^ 2]

@[expose] def suTwoPInv (ω : K) : Matrix (Fin 2) (Fin 2) K := !![ω ^ 2, ω; 1, 1]

theorem suTwoJ_mul_suTwoJ : (suTwoJ : Matrix (Fin 2) (Fin 2) K) * suTwoJ = 1 := by
  rw [suTwoJ, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp

theorem suTwoJ_mul_suTwoJ_mul (M : Matrix (Fin 2) (Fin 2) K) : suTwoJ * (suTwoJ * M) = M := by
  rw [← Matrix.mul_assoc, suTwoJ_mul_suTwoJ, Matrix.one_mul]

theorem transpose_suTwoJ : (suTwoJ : Matrix (Fin 2) (Fin 2) K)ᵀ = suTwoJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suTwoJ]

theorem suTwoJ_mul_transpose_mul_suTwoJ [CharP K 2] (A : Matrix (Fin 2) (Fin 2) K) :
    suTwoJ * Aᵀ * suTwoJ = adjugate A := by
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suTwoJ, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, CharTwo.neg_eq]

theorem suTwoP_mul_suTwoPInv [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    suTwoP ω * suTwoPInv ω = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [suTwoP, suTwoPInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  have e1 : 1 * ω ^ 2 + ω * 1 = (1 : K) := by linear_combination hω - h2
  have e2 : 1 * ω + ω * 1 = (0 : K) := by linear_combination ω * h2
  have e3 : 1 * ω ^ 2 + ω ^ 2 * 1 = (0 : K) := by linear_combination ω ^ 2 * h2
  have e4 : 1 * ω + ω ^ 2 * 1 = (1 : K) := by linear_combination hω - h2
  rw [e1, e2, e3, e4]

theorem suTwoPInv_mul_suTwoP [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    suTwoPInv ω * suTwoP ω = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [suTwoP, suTwoPInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  have e1 : ω ^ 2 * 1 + ω * 1 = (1 : K) := by linear_combination hω - h2
  have e2 : ω ^ 2 * ω + ω * ω ^ 2 = (0 : K) := by linear_combination ω ^ 3 * h2
  have e3 : 1 * 1 + 1 * 1 = (0 : K) := by linear_combination h2
  have e4 : 1 * ω + 1 * ω ^ 2 = (1 : K) := by linear_combination hω - h2
  rw [e1, e2, e3, e4]

theorem suTwoPInv_mul_suTwoP_mul [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (M : Matrix (Fin 2) (Fin 2) K) : suTwoPInv ω * (suTwoP ω * M) = M := by
  rw [← Matrix.mul_assoc, suTwoPInv_mul_suTwoP hω, Matrix.one_mul]

theorem suTwoP_mul_suTwoPInv_mul [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (M : Matrix (Fin 2) (Fin 2) K) : suTwoP ω * (suTwoPInv ω * M) = M := by
  rw [← Matrix.mul_assoc, suTwoP_mul_suTwoPInv hω, Matrix.one_mul]

theorem map_suTwoP (τ : K →+* K) (ω : K) : (suTwoP ω).map τ = suTwoP (τ ω) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suTwoP, map_pow]

theorem map_suTwoPInv (τ : K →+* K) (ω : K) : (suTwoPInv ω).map τ = suTwoPInv (τ ω) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suTwoPInv, map_pow]

theorem pow_two_pow_two_of_pow_three {ω : K} (hω3 : ω ^ 3 = 1) : (ω ^ 2) ^ 2 = ω := by
  rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hω3, one_mul]

theorem suTwoP_sq {ω : K} (hω3 : ω ^ 3 = 1) : suTwoP (ω ^ 2) = suTwoJ * suTwoP ω := by
  rw [suTwoP, suTwoP, suTwoJ, Matrix.mul_fin_two, pow_two_pow_two_of_pow_three hω3]
  simp

theorem suTwoPInv_sq {ω : K} (hω3 : ω ^ 3 = 1) : suTwoPInv (ω ^ 2) = suTwoPInv ω * suTwoJ := by
  rw [suTwoPInv, suTwoPInv, suTwoJ, Matrix.mul_fin_two, pow_two_pow_two_of_pow_three hω3]
  simp

theorem transpose_map_mul_eq_one [CharP K 2] {τ : K →+* K} {B : Matrix (Fin 2) (Fin 2) K}
    (hB : B.map τ = suTwoJ * B * suTwoJ) (hdet : B.det = 1) : (B.map τ)ᵀ * B = 1 := by
  rw [hB, Matrix.transpose_mul, Matrix.transpose_mul, transpose_suTwoJ,
    ← Matrix.mul_assoc suTwoJ, suTwoJ_mul_transpose_mul_suTwoJ, Matrix.adjugate_mul, hdet,
    one_smul]

theorem map_eq_suTwoJ_mul_mul_suTwoJ [CharP K 2] {τ : K →+* K} {Z : Matrix (Fin 2) (Fin 2) K}
    (hZ : (Z.map τ)ᵀ * Z = 1) (hdet : Z.det = 1) : Z.map τ = suTwoJ * Z * suTwoJ := by
  have h1 : adjugate Z * Z = 1 := by rw [Matrix.adjugate_mul, hdet, one_smul]
  have h2 : Z * (Z.map τ)ᵀ = 1 := mul_eq_one_comm.1 hZ
  have h3 : (Z.map τ)ᵀ = suTwoJ * Zᵀ * suTwoJ := by
    rw [suTwoJ_mul_transpose_mul_suTwoJ]
    calc (Z.map τ)ᵀ = adjugate Z * Z * (Z.map τ)ᵀ := by rw [h1, Matrix.one_mul]
      _ = adjugate Z := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  have h4 := congrArg Matrix.transpose h3
  rwa [Matrix.transpose_transpose, Matrix.transpose_mul, Matrix.transpose_mul, transpose_suTwoJ,
    Matrix.transpose_transpose, ← Matrix.mul_assoc] at h4

end TwoByTwo

section Blocks

variable {K : Type} [Field K]

theorem map_blkMat (τ : K →+* K) (A : Matrix (Fin 2) (Fin 2) K) :
    (HDescLinRes.blkMat A).map τ = HDescLinRes.blkMat (A.map τ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HDescLinRes.blkMat]

theorem transpose_blkMat (A : Matrix (Fin 2) (Fin 2) K) :
    (HDescLinRes.blkMat A)ᵀ = HDescLinRes.blkMat Aᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HDescLinRes.blkMat]

theorem blkMat_apply_castSucc (A : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    HDescLinRes.blkMat A i.castSucc j.castSucc = A i j := by
  fin_cases i <;> fin_cases j <;> simp [HDescLinRes.blkMat]

theorem blkMat_injective : Function.Injective (HDescLinRes.blkMat (R := K)) := by
  intro A B hAB
  ext i j
  rw [← blkMat_apply_castSucc A, hAB, blkMat_apply_castSucc]

theorem map_suTwoMat_of_fix {τ : K →+* K} {ω : K} (hτω : τ ω = ω)
    {g : Matrix (Fin 2) (Fin 2) K} (hτg : g.map τ = g) :
    (HDescLinRes.blkMat (suTwoP ω * g * suTwoPInv ω)).map τ =
      HDescLinRes.blkMat (suTwoP ω * g * suTwoPInv ω) := by
  rw [map_blkMat, Matrix.map_mul, Matrix.map_mul, hτg, map_suTwoP, map_suTwoPInv, hτω]

end Blocks

section SUBlock

variable {ℓ f : ℕ} {K : Type} [Field K] [CharP K 2]

@[expose] def suTwoPGL {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : GL (Fin 3) K :=
  ⟨HDescLinRes.blkMat (suTwoP ω), HDescLinRes.blkMat (suTwoPInv ω), by
    rw [← HDescLinRes.blkMat_mul, suTwoP_mul_suTwoPInv hω, HDescLinRes.blkMat_one], by
    rw [← HDescLinRes.blkMat_mul, suTwoPInv_mul_suTwoP hω, HDescLinRes.blkMat_one]⟩

@[expose] def suTwoBlkGL {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (F₀ : Subfield K) :
    Matrix.SpecialLinearGroup (Fin 2) F₀ →* GL (Fin 3) K :=
  (MulAut.conj (suTwoPGL hω)).toMonoidHom.comp (Matrix.SpecialLinearGroup.toGL.comp
    (HDescLinRes.slBlk.comp (Matrix.SpecialLinearGroup.map F₀.subtype)))

theorem coe_suTwoBlkGL {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {F₀ : Subfield K}
    (g : Matrix.SpecialLinearGroup (Fin 2) F₀) :
    ((suTwoBlkGL hω F₀ g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      HDescLinRes.blkMat (suTwoP ω * (g : Matrix (Fin 2) (Fin 2) F₀).map F₀.subtype *
        suTwoPInv ω) := by
  rw [HDescLinRes.blkMat_mul, HDescLinRes.blkMat_mul]
  rfl

theorem suTwoBlkGL_mem_gramSU (h : UnitaryFieldData ℓ f K) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (hωb : h.bar ω = ω ^ 2) {F₀ : Subfield K} (hF₀ : ∀ c ∈ F₀, h.bar c = c)
    (g : Matrix.SpecialLinearGroup (Fin 2) F₀) :
    suTwoBlkGL hω F₀ g ∈ gramSU h (idGram K 3) := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  set g' := (g : Matrix (Fin 2) (Fin 2) F₀).map F₀.subtype with hg'
  have hg'b : g'.map h.bar = g' := by
    ext i j
    exact hF₀ _ ((g : Matrix (Fin 2) (Fin 2) F₀) i j).2
  have hg'det : g'.det = 1 := by
    rw [hg', ← RingHom.mapMatrix_apply, ← RingHom.map_det, g.2, map_one]
  set B := suTwoP ω * g' * suTwoPInv ω with hB
  have hBb : B.map h.bar = suTwoJ * B * suTwoJ := by
    rw [hB, Matrix.map_mul, Matrix.map_mul, hg'b, map_suTwoP, map_suTwoPInv, hωb, suTwoP_sq hω3,
      suTwoPInv_sq hω3]
    simp only [Matrix.mul_assoc]
  have hBdet : B.det = 1 := by
    rw [hB, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
      suTwoP_mul_suTwoPInv hω, Matrix.det_one, one_mul, hg'det]
  have hBu := transpose_map_mul_eq_one hBb hBdet
  have hI : idGram K 3 = (1 : Matrix (Fin 3) (Fin 3) K) := Units.val_one
  refine ⟨?_, ?_⟩
  · rw [hI, Matrix.mul_one, coe_suTwoBlkGL, ← hg', ← hB, map_blkMat, transpose_blkMat,
      ← HDescLinRes.blkMat_mul, hBu, HDescLinRes.blkMat_one]
  · rw [coe_suTwoBlkGL, ← hg', ← hB, HDescLinRes.det_blkMat, hBdet]

@[expose] noncomputable def suTwoBlk (h : UnitaryFieldData ℓ f K) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (hωb : h.bar ω = ω ^ 2) {F₀ : Subfield K}
    (hF₀ : ∀ c ∈ F₀, h.bar c = c) :
    Matrix.SpecialLinearGroup (Fin 2) F₀ →* primeFormP h (idGram K 3) :=
  (QuotientGroup.mk' _).comp
    ((suTwoBlkGL hω F₀).codRestrict _ (suTwoBlkGL_mem_gramSU h hω hωb hF₀))

theorem exists_suTwoBlkGL_eq (h : UnitaryFieldData ℓ f K) {σ : K ≃+* K} {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (hωσ : σ ω = ω) (hωb : h.bar ω = ω ^ 2) {F₀ : Subfield K}
    (hF₀mem : ∀ c : K, σ c = c → h.bar c = c → c ∈ F₀) {Z : GL (Fin 3) K}
    (hZ : Z ∈ gramSU h (idGram K 3)) (hZσ : (Z : Matrix (Fin 3) (Fin 3) K).map σ = Z)
    (h02 : (Z : Matrix (Fin 3) (Fin 3) K) 0 2 = 0) (h12 : (Z : Matrix (Fin 3) (Fin 3) K) 1 2 = 0)
    (h20 : (Z : Matrix (Fin 3) (Fin 3) K) 2 0 = 0) (h21 : (Z : Matrix (Fin 3) (Fin 3) K) 2 1 = 0)
    (h22 : (Z : Matrix (Fin 3) (Fin 3) K) 2 2 = 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F₀, suTwoBlkGL hω F₀ g = Z := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  set z : Matrix (Fin 3) (Fin 3) K := (Z : Matrix (Fin 3) (Fin 3) K) with hz
  set Z' : Matrix (Fin 2) (Fin 2) K := fun i j => z i.castSucc j.castSucc with hZ'
  have hzb : z = HDescLinRes.blkMat Z' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [HDescLinRes.blkMat, hZ', h02, h12, h20, h21, h22]
  have hI : idGram K 3 = (1 : Matrix (Fin 3) (Fin 3) K) := Units.val_one
  have hZu : (Z'.map h.bar)ᵀ * Z' = 1 := by
    have h1 := hZ.1
    rw [hI, Matrix.mul_one, ← hz, hzb, map_blkMat, transpose_blkMat, ← HDescLinRes.blkMat_mul,
      ← HDescLinRes.blkMat_one] at h1
    exact blkMat_injective h1
  have hZdet : Z'.det = 1 := by
    have h1 := hZ.2
    rwa [← hz, hzb, HDescLinRes.det_blkMat] at h1
  have hZ'σ : Z'.map (σ : K →+* K) = Z' := by
    apply blkMat_injective
    rw [← map_blkMat, ← hzb]
    exact hZσ
  have hZ'b : Z'.map h.bar = suTwoJ * Z' * suTwoJ := map_eq_suTwoJ_mul_mul_suTwoJ hZu hZdet
  set g₁ := suTwoPInv ω * Z' * suTwoP ω with hg₁
  have hg₁σ : g₁.map (σ : K →+* K) = g₁ := by
    rw [hg₁, Matrix.map_mul, Matrix.map_mul, hZ'σ, map_suTwoP, map_suTwoPInv,
      show (σ : K →+* K) ω = ω from hωσ]
  have hg₁b : g₁.map h.bar = g₁ := by
    rw [hg₁, Matrix.map_mul, Matrix.map_mul, hZ'b, map_suTwoP, map_suTwoPInv, hωb, suTwoP_sq hω3,
      suTwoPInv_sq hω3]
    simp only [Matrix.mul_assoc, suTwoJ_mul_suTwoJ_mul]
  have hmem : ∀ i j, g₁ i j ∈ F₀ := by
    intro i j
    apply hF₀mem
    · exact congrFun (congrFun hg₁σ i) j
    · exact congrFun (congrFun hg₁b i) j
  let g₀ : Matrix (Fin 2) (Fin 2) F₀ := fun i j => ⟨g₁ i j, hmem i j⟩
  have hg₀ : g₀.map F₀.subtype = g₁ := by
    ext i j
    rfl
  have hdet : g₀.det = 1 := by
    apply F₀.subtype.injective
    rw [map_one, RingHom.map_det, RingHom.mapMatrix_apply, hg₀, hg₁, Matrix.det_mul,
      Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, suTwoPInv_mul_suTwoP hω, Matrix.det_one,
      one_mul, hZdet]
  refine ⟨⟨g₀, hdet⟩, Units.ext ((coe_suTwoBlkGL hω _).trans ?_)⟩
  show HDescLinRes.blkMat (suTwoP ω * g₀.map F₀.subtype * suTwoPInv ω) = z
  rw [hg₀, hg₁, hzb]
  congr 1
  simp only [Matrix.mul_assoc, suTwoP_mul_suTwoPInv hω, suTwoP_mul_suTwoPInv_mul hω,
    Matrix.mul_one]

end SUBlock

section Core

theorem mul_comm_of_eq_conj_mul_scalar_diag {k : Type} [Field k] [CharP k 2] {X u : GL (Fin 3) k}
    {d : Fin 3 → k} (hX : (X : Matrix (Fin 3) (Fin 3) k) = diagonal d) (hd01 : d 0 = d 1)
    {c : kˣ} (hUWs : u = X * u * X⁻¹ * GeneralLinearGroup.scalar (Fin 3) c) : X * u = u * X := by
  set s := GeneralLinearGroup.scalar (Fin 3) c with hs
  have hsc : ∀ g : GL (Fin 3) k, s * g = g * s := fun g => GeneralLinearGroup.scalar_commute c g
  have hXu : X = u⁻¹ * X * u * s := by
    calc X = u⁻¹ * (u * X) := by group
      _ = u⁻¹ * (X * u * X⁻¹ * s * X) := by rw [← hUWs]
      _ = u⁻¹ * (X * u * (X⁻¹ * (s * X))) := by group
      _ = u⁻¹ * (X * u * (X⁻¹ * (X * s))) := by rw [hsc X]
      _ = u⁻¹ * X * u * s := by group
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have htrX : Matrix.trace (X : Matrix (Fin 3) (Fin 3) k) = d 2 := by
    rw [hX, Matrix.trace_diagonal, Fin.sum_univ_three, ← hd01]
    linear_combination d 0 * h2
  have hd2 : d 2 ≠ 0 := by
    intro h0
    have hdet : (X : Matrix (Fin 3) (Fin 3) k).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 X.isUnit).ne_zero
    apply hdet
    rw [hX, Matrix.det_diagonal, Fin.prod_univ_three, h0, mul_zero]
  have htr := congrArg (fun g : GL (Fin 3) k => Matrix.trace (g : Matrix (Fin 3) (Fin 3) k)) hXu
  simp only [Units.val_mul, hs, GeneralLinearGroup.coe_scalar] at htr
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, Matrix.trace_units_conj', htrX, smul_eq_mul] at htr
  have hc1 : (c : k) = 1 := by
    have : (1 - (c : k)) * d 2 = 0 := by rw [sub_mul, one_mul, ← htr, sub_self]
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hd2)).symm
  have hs1 : s = 1 := by rw [hs, show c = 1 from Units.ext hc1, map_one]
  rw [hs1, mul_one] at hXu
  calc X * u = u * (u⁻¹ * X * u) := by group
    _ = u * X := by rw [← hXu]

variable {ℓ f : ℕ} {K : Type} [Field K] [CharP K 2]

theorem commute_of_primeFormConjHom_fix_diag {h : UnitaryFieldData ℓ f K}
    {X : primeFormUnitary h (idGram K 3)} {d : Fin 3 → K}
    (hX : ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d) (hd01 : d 0 = d 1)
    {Y₁ : gramSU h (idGram K 3)}
    (hfix : primeFormConjHom h (idGram K 3) X (Y₁ : primeFormP h (idGram K 3)) = Y₁) :
    (X : GL (Fin 3) K) * Y₁ = Y₁ * X := by
  rw [primeFormConjHom_mk, QuotientGroup.eq] at hfix
  obtain ⟨c, -, -, hc⟩ := hfix
  have hW : ((⟨(X : GL (Fin 3) K) * Y₁ * (X : GL (Fin 3) K)⁻¹,
      conj_mem_gramSU h (idGram K 3) X.2 Y₁.2⟩ : gramSU h (idGram K 3))⁻¹ * Y₁ :
        gramSU h (idGram K 3)) =
      ((X : GL (Fin 3) K) * Y₁ * (X : GL (Fin 3) K)⁻¹)⁻¹ * (Y₁ : GL (Fin 3) K) := rfl
  rw [hW] at hc
  refine mul_comm_of_eq_conj_mul_scalar_diag hX hd01 (c := c) ?_
  rw [← hc, mul_inv_cancel_left]

theorem glaPLayer_ne_bot_of_unitary_diagonal (h : UnitaryFieldData ℓ f K) {σ : K ≃+* K}
    {F₀ : Subfield K} {e : ℕ} (he : 2 ≤ e) (hF₀ : Nat.card F₀ = 2 ^ e)
    (hF₀σ : ∀ c ∈ F₀, σ c = c) (hF₀b : ∀ c ∈ F₀, h.bar c = c)
    (hF₀mem : ∀ c : K, σ c = c → h.bar c = c → c ∈ F₀)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hωσ : σ ω = ω) (hωb : h.bar ω = ω ^ 2)
    {X : primeFormUnitary h (idGram K 3)} {d : Fin 3 → K}
    (hX : ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d)
    (hd01 : d 0 = d 1) (hd02 : d 0 ≠ d 2) :
    GLAPLayer 3 (fixSubgroup (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ) ⊓
      fixSubgroup (primeFormConjHom h (idGram K 3) X)) ≠ ⊥ := by
  classical
  have := h.finite
  set Y := fixSubgroup (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ) ⊓
      fixSubgroup (primeFormConjHom h (idGram K 3) X) with hYdef
  set φ := suTwoBlk h hω hωb hF₀b with hφdef
  have hφ : ∀ g, φ g = ((⟨suTwoBlkGL hω F₀ g, suTwoBlkGL_mem_gramSU h hω hωb hF₀b g⟩ :
      gramSU h (idGram K 3)) : primeFormP h (idGram K 3)) := fun g => rfl
  have hd12 : d 1 ≠ d 2 := by rwa [← hd01]
  have hσB : ∀ g : Matrix.SpecialLinearGroup (Fin 2) F₀,
      glAut σ (suTwoBlkGL hω F₀ g) = suTwoBlkGL hω F₀ g := by
    intro g
    apply Units.ext
    rw [coe_glAut, coe_suTwoBlkGL]
    exact map_suTwoMat_of_fix (τ := (σ : K →+* K)) hωσ (by
      ext i j
      exact hF₀σ _ ((g : Matrix (Fin 2) (Fin 2) F₀) i j).2)
  have hXB : ∀ g : Matrix.SpecialLinearGroup (Fin 2) F₀,
      (X : GL (Fin 3) K) * suTwoBlkGL hω F₀ g = suTwoBlkGL hω F₀ g * X := by
    intro g
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_suTwoBlkGL, hX]
    exact HDescLinRes.diagonal_mul_blkMat hd01 _
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    rw [hφ, QuotientGroup.eq_one_iff] at hg
    obtain ⟨c, -, -, hc⟩ := hg
    have hc' : ((suTwoBlkGL hω F₀ g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.scalar (Fin 3) (c : K) := by
      have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hc
      simpa only [GeneralLinearGroup.coe_scalar] using this
    rw [coe_suTwoBlkGL] at hc'
    have hc1 : (c : K) = 1 := by
      have := congrFun (congrFun hc' 2) 2
      simp [HDescLinRes.blkMat] at this
      exact this.symm
    rw [hc1, map_one, ← HDescLinRes.blkMat_one] at hc'
    have hB1 := blkMat_injective hc'
    have hg'1 : (g : Matrix (Fin 2) (Fin 2) F₀).map F₀.subtype = 1 := by
      have e1 : suTwoPInv ω * (suTwoP ω * (g : Matrix (Fin 2) (Fin 2) F₀).map F₀.subtype *
          suTwoPInv ω) * suTwoP ω = (g : Matrix (Fin 2) (Fin 2) F₀).map F₀.subtype := by
        simp only [Matrix.mul_assoc, suTwoPInv_mul_suTwoP_mul hω, suTwoPInv_mul_suTwoP hω,
          Matrix.mul_one]
      rw [← e1, hB1, Matrix.mul_one, suTwoPInv_mul_suTwoP hω]
    have hg1 : (g : Matrix (Fin 2) (Fin 2) F₀) = 1 :=
      Matrix.map_injective (f := ((↑) : F₀ → K)) Subtype.val_injective
        (hg'1.trans (Matrix.map_one _ rfl rfl).symm)
    exact Subtype.ext hg1
  have hJY : φ.range ≤ Y := by
    rintro _ ⟨g, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_fixSubgroup, hφ]
      show primeFormFieldAut h (isPrimeFormGram_idGram (K := K) (n := 3)) σ _ = _
      rw [primeFormFieldAut_mk]
      congr 1
      exact Subtype.ext (hσB g)
    · rw [mem_fixSubgroup, hφ, primeFormConjHom_mk]
      congr 1
      apply Subtype.ext
      show (X : GL (Fin 3) K) * suTwoBlkGL hω F₀ g * (X : GL (Fin 3) K)⁻¹ = suTwoBlkGL hω F₀ g
      rw [hXB g, mul_inv_cancel_right]
  have hJn : (φ.range.subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJY]
    rintro _ y ⟨g, rfl⟩ hy
    obtain ⟨Y₁, rfl⟩ := QuotientGroup.mk_surjective y
    have hyσ := (Subgroup.mem_inf.1 hy).1
    have hyX := (Subgroup.mem_inf.1 hy).2
    rw [mem_fixSubgroup] at hyσ hyX
    have hXu := commute_of_primeFormConjHom_fix_diag hX hd01 hyX
    have hyσ' : primeFormFieldAut h (isPrimeFormGram_idGram (K := K) (n := 3)) σ
        (Y₁ : primeFormP h (idGram K 3)) = Y₁ := hyσ
    rw [primeFormFieldAut_mk, QuotientGroup.eq] at hyσ'
    obtain ⟨w, -, -, hw⟩ := hyσ'
    have hw' : (glAut σ (Y₁ : GL (Fin 3) K))⁻¹ * (Y₁ : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) w := hw
    have hσY : glAut σ (Y₁ : GL (Fin 3) K) =
        (Y₁ : GL (Fin 3) K) * (GeneralLinearGroup.scalar (Fin 3) w)⁻¹ := by
      rw [← hw', _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    obtain ⟨u, hu⟩ : ∃ u : GL (Fin 3) K, u = (Y₁ : GL (Fin 3) K) := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : GL (Fin 3) K, B = suTwoBlkGL hω F₀ g := ⟨_, rfl⟩
    rw [← hu] at hXu hσY
    have humem : u ∈ gramSU h (idGram K 3) := hu ▸ Y₁.2
    have hBmem : B ∈ gramSU h (idGram K 3) := hB ▸ suTwoBlkGL_mem_gramSU h hω hωb hF₀b g
    have hσB' : glAut σ B = B := by rw [hB]; exact hσB g
    have hXB' : (X : GL (Fin 3) K) * B = B * X := by rw [hB]; exact hXB g
    have hbm : (B : Matrix (Fin 3) (Fin 3) K) = HDescLinRes.blkMat (suTwoP ω *
        (g : Matrix (Fin 2) (Fin 2) F₀).map F₀.subtype * suTwoPInv ω) := by
      rw [hB]; exact coe_suTwoBlkGL hω g
    have hsB : (GeneralLinearGroup.scalar (Fin 3) w)⁻¹ * B =
        B * (GeneralLinearGroup.scalar (Fin 3) w)⁻¹ :=
      (show Commute (GeneralLinearGroup.scalar (Fin 3) w) B from
        GeneralLinearGroup.scalar_commute w _).inv_left.eq
    obtain ⟨Z, hZ⟩ : ∃ Z : GL (Fin 3) K, Z = u * B * u⁻¹ := ⟨_, rfl⟩
    have hZσ : glAut σ Z = Z := by
      rw [hZ, map_mul, map_mul, map_inv, hσY, hσB']
      calc u * (GeneralLinearGroup.scalar (Fin 3) w)⁻¹ * B *
            (u * (GeneralLinearGroup.scalar (Fin 3) w)⁻¹)⁻¹
          = u * ((GeneralLinearGroup.scalar (Fin 3) w)⁻¹ * B) *
              GeneralLinearGroup.scalar (Fin 3) w * u⁻¹ := by group
        _ = u * (B * (GeneralLinearGroup.scalar (Fin 3) w)⁻¹) *
              GeneralLinearGroup.scalar (Fin 3) w * u⁻¹ := by rw [hsB]
        _ = u * B * u⁻¹ := by group
    have hZmem : Z ∈ gramSU h (idGram K 3) := by
      rw [hZ]
      exact mul_mem (mul_mem humem hBmem) (inv_mem humem)
    have hXZ : (X : GL (Fin 3) K) * Z = Z * X := by
      have h1 : Commute (X : GL (Fin 3) K) u := hXu
      have h2 : Commute (X : GL (Fin 3) K) B := hXB'
      rw [hZ]
      exact ((h1.mul_right h2).mul_right h1.inv_right).eq
    have hXZm : diagonal d * (Z : Matrix (Fin 3) (Fin 3) K) =
        (Z : Matrix (Fin 3) (Fin 3) K) * diagonal d := by
      have := congrArg Units.val hXZ
      rwa [Units.val_mul (X : GL (Fin 3) K) Z, Units.val_mul Z (X : GL (Fin 3) K), hX] at this
    have hum : diagonal d * (u : Matrix (Fin 3) (Fin 3) K) =
        (u : Matrix (Fin 3) (Fin 3) K) * diagonal d := by
      have := congrArg Units.val hXu
      rwa [Units.val_mul (X : GL (Fin 3) K) u, Units.val_mul u (X : GL (Fin 3) K), hX] at this
    have hu20 : (u : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 :=
      HDescLinRes.eq_zero_of_diagonal_commute hum hd02.symm
    have hu21 : (u : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 :=
      HDescLinRes.eq_zero_of_diagonal_commute hum hd12.symm
    have hb20 : (B : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by rw [hbm]; simp [HDescLinRes.blkMat]
    have hb21 : (B : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by rw [hbm]; simp [HDescLinRes.blkMat]
    have hb22 : (B : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by rw [hbm]; simp [HDescLinRes.blkMat]
    have hZ22 : (Z : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
      have e1 : (Z : Matrix (Fin 3) (Fin 3) K) = (u : Matrix (Fin 3) (Fin 3) K) *
          ((B : Matrix (Fin 3) (Fin 3) K) * ((u⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
        rw [hZ, Units.val_mul (u * B) u⁻¹, Units.val_mul u B, Matrix.mul_assoc]
      have e2 : (u : Matrix (Fin 3) (Fin 3) K) 2 2 *
          ((u⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
        have := HDescLinRes.mul_apply_two_two
          (Q := ((u⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hu20 hu21
        rw [Units.mul_inv, Matrix.one_apply_eq] at this
        exact this.symm
      rw [e1, HDescLinRes.mul_apply_two_two hu20 hu21, HDescLinRes.mul_apply_two_two hb20 hb21,
        hb22, one_mul, e2]
    have hZσm : (Z : Matrix (Fin 3) (Fin 3) K).map σ = Z := by
      have := congrArg Units.val hZσ
      rwa [coe_glAut] at this
    obtain ⟨g'', hg''⟩ := exists_suTwoBlkGL_eq h hω hωσ hωb hF₀mem hZmem hZσm
      (HDescLinRes.eq_zero_of_diagonal_commute hXZm hd02)
      (HDescLinRes.eq_zero_of_diagonal_commute hXZm hd12)
      (HDescLinRes.eq_zero_of_diagonal_commute hXZm hd02.symm)
      (HDescLinRes.eq_zero_of_diagonal_commute hXZm hd12.symm) hZ22
    refine ⟨g'', ?_⟩
    rw [hφ g'', hφ g, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    show suTwoBlkGL hω F₀ g'' = (Y₁ : GL (Fin 3) K) * suTwoBlkGL hω F₀ g * (Y₁ : GL (Fin 3) K)⁻¹
    rw [hg'', hZ, hu, hB]
  haveI : Fintype F₀ := Fintype.ofFinite F₀
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F₀) :=
    CFSG.Quasithin.R3c21.isSimpleGroup_sl2_of_card_two_pow he
      (by rw [← Nat.card_eq_fintype_card, hF₀])
  let eJ : Matrix.SpecialLinearGroup (Fin 2) F₀ ≃* φ.range := MonoidHom.ofInjective hφinj
  haveI : IsSimpleGroup φ.range := eJ.symm.isSimpleGroup
  have hnc : ∃ a b : φ.range, a * b ≠ b * a := by
    let t1 : Matrix.SpecialLinearGroup (Fin 2) F₀ := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    let t2 : Matrix.SpecialLinearGroup (Fin 2) F₀ := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    have ht1 : (t1 : Matrix (Fin 2) (Fin 2) F₀) = !![1, 1; 0, 1] := rfl
    have ht2 : (t2 : Matrix (Fin 2) (Fin 2) F₀) = !![1, 0; 1, 1] := rfl
    refine ⟨eJ t1, eJ t2, fun h => ?_⟩
    rw [← map_mul, ← map_mul] at h
    have h' := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F₀ =>
      (A : Matrix (Fin 2) (Fin 2) F₀) 0 0) (eJ.injective h)
    simp only [Matrix.SpecialLinearGroup.coe_mul, ht1, ht2] at h'
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h'
  have h3J : 3 ∣ Nat.card φ.range := by
    rw [← Nat.card_congr eJ.toEquiv]
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h2F : (2 : F₀) = 0 := F₀.subtype.injective (by rw [map_ofNat, map_zero]; exact h2)
    have h11 : (1 : F₀) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2F
    let t3 : Matrix.SpecialLinearGroup (Fin 2) F₀ := ⟨!![0, 1; 1, 1], by
      rw [Matrix.det_fin_two_of]; linear_combination -h2F⟩
    have ht3 : t3 ^ 3 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
      show (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F₀) ^ 3 = 1
      rw [pow_succ, pow_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two]
      simp only [mul_zero, zero_mul, mul_one, one_mul, zero_add, add_zero, h11]
    have ht31 : t3 ≠ 1 := by
      intro h1
      have h1' := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F₀ =>
        (A : Matrix (Fin 2) (Fin 2) F₀) 0 0) h1
      simp [t3] at h1'
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [← orderOf_eq_prime ht3 ht31]
    exact orderOf_dvd_natCard t3
  have hle := le_glaPLayer_of_normal_simple Nat.prime_three hJY hJn hnc h3J
  intro hbot
  rw [hbot] at hle
  obtain ⟨a, b, hab⟩ := hnc
  apply hab
  have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.1 (hle a.2))
  have hb : b = 1 := Subtype.ext (Subgroup.mem_bot.1 (hle b.2))
  rw [ha, hb]

end Core

open CFSG.RankThree.Classical
open CFSG.LieType.Chevalley (fixSubfield)

section Diag

theorem exists_eq_ne_of_diag_of_ne_scalar {k : Type} [Field k] [CharP k 2]
    {P M u : GL (Fin 3) k} {d : Fin 3 → k}
    (hd : ((P * M * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = diagonal d)
    (hu1 : u ≠ 1) (hu2 : u * u = 1) (hMu : M * u = u * M)
    (hM1 : ∀ c : kˣ, M ≠ GeneralLinearGroup.scalar (Fin 3) c) :
    ∃ i j l : Fin 3, i ≠ j ∧ l ≠ i ∧ l ≠ j ∧ d i = d j ∧ d l ≠ d i := by
  classical
  set W := P * u * P⁻¹ with hW
  have hWd : diagonal d * (W : Matrix (Fin 3) (Fin 3) k) =
      (W : Matrix (Fin 3) (Fin 3) k) * diagonal d := by
    rw [← hd, ← Units.val_mul, ← Units.val_mul]
    congr 1
    rw [hW]
    calc P * M * P⁻¹ * (P * u * P⁻¹) = P * (M * u) * P⁻¹ := by group
      _ = P * (u * M) * P⁻¹ := by rw [hMu]
      _ = P * u * P⁻¹ * (P * M * P⁻¹) := by group
  have hW2 : (W : Matrix (Fin 3) (Fin 3) k) * W = 1 := by
    rw [← Units.val_mul]
    have : W * W = 1 := by
      rw [hW]
      calc P * u * P⁻¹ * (P * u * P⁻¹) = P * (u * u) * P⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    rw [this, Units.val_one]
  by_cases hinj : ∀ i j, i ≠ j → d i ≠ d j
  · exfalso
    apply hu1
    have h1 := HDescLinRes.eq_one_of_commute_two_diagonal_of_mul_self_eq_one (a := d) (b := d)
      (fun i j hij => Or.inl (hinj i j hij)) hWd hWd hW2
    have h1' : W = 1 := Units.ext h1
    calc u = P⁻¹ * W * P := by rw [hW]; group
      _ = 1 := by rw [h1']; group
  push Not at hinj
  obtain ⟨i, j, hij, hdij⟩ := hinj
  by_cases hc : ∀ l, d l = d i
  · exfalso
    have hdi0 : d i ≠ 0 := by
      intro h0
      have hdet : ((P * M * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).det ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
      apply hdet
      rw [hd, Matrix.det_diagonal, Fin.prod_univ_three, hc 0, h0, zero_mul, zero_mul]
    have hsc : P * M * P⁻¹ = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (d i) hdi0) := by
      apply Units.ext
      rw [hd, GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
      congr 1
      funext l
      exact hc l
    exact hM1 _ (HDescLinRes.eq_scalar_of_conj_eq_scalar hsc)
  push Not at hc
  obtain ⟨l, hl⟩ := hc
  exact ⟨i, j, l, hij, fun h => hl (by rw [h]), fun h => hl (by rw [h, hdij]), hdij, hl⟩

private theorem injective_vec_three {i j l : Fin 3} (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j) :
    Function.Injective ![i, j, l] := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

variable {ℓ e : ℕ} {k : Type} [Field k]

theorem isOrthonormalFamily_comp {h₀ : UnitaryFieldData ℓ e k} {n : ℕ} {ι : Type*}
    [DecidableEq ι] {b : ι → Fin n → k} (hb : IsOrthonormalFamily h₀ b) {π : ι → ι}
    (hπ : Function.Injective π) : IsOrthonormalFamily h₀ (b ∘ π) := fun i j => by
  rw [Function.comp_apply, Function.comp_apply, hb]
  exact if_congr hπ.eq_iff rfl rfl

theorem exists_unitary_conj_eq_diagonal (h₀ : UnitaryFieldData ℓ e k) {n : ℕ}
    {M : GL (Fin n) k} {b : Fin n → Fin n → k} (hb : IsOrthonormalFamily h₀ b) {μ : Fin n → k}
    (hμ : ∀ i, (M : Matrix (Fin n) (Fin n) k) *ᵥ b i = μ i • b i) :
    ∃ R : GL (Fin n) k, R ∈ primeFormUnitary h₀ (idGram k n) ∧
      ((R * M * R⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = diagonal μ := by
  set B : Matrix (Fin n) (Fin n) k := Matrix.of fun r c => b c r with hB
  have h1 : (B.map h₀.bar)ᵀ * B = 1 := by
    ext c c'
    have := hb c c'
    rw [idForm_eq_dotProduct] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← this]
    simp [hB, dotProduct]
  have h2 : B * (B.map h₀.bar)ᵀ = 1 := mul_eq_one_comm.1 h1
  have hMB : (M : Matrix (Fin n) (Fin n) k) * B = B * diagonal μ := by
    ext r c
    have := congrFun (hμ c) r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [hB, Matrix.of_apply]
    rw [this, mul_comm]
  have hBB : (((B.map h₀.bar)ᵀ).map h₀.bar)ᵀ = B := by
    ext i j
    simp [h₀.bar_bar]
  refine ⟨⟨(B.map h₀.bar)ᵀ, B, h1, h2⟩, ?_, ?_⟩
  · rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    show (((B.map h₀.bar)ᵀ).map h₀.bar)ᵀ * (B.map h₀.bar)ᵀ = 1
    rw [hBB]
    exact h2
  · show (B.map h₀.bar)ᵀ * (M : Matrix (Fin n) (Fin n) k) * B = diagonal μ
    rw [Matrix.mul_assoc, hMB, ← Matrix.mul_assoc, h1, Matrix.one_mul]

end Diag

section Subfield

variable {ℓ f e : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {k : Subfield K}
  {h₀ : UnitaryFieldData ℓ e k} (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c)

include hbar in
private theorem subfieldGL_mem_primeFormUnitary' {n : ℕ} {g : GL (Fin n) k}
    (hg : g ∈ primeFormUnitary h₀ (idGram k n)) :
    subfieldGL k n g ∈ primeFormUnitary h (idGram K n) := by
  rw [mem_primeFormUnitary] at hg ⊢
  simp only [idGram, Units.val_one, Matrix.mul_one] at hg ⊢
  rw [coe_subfieldGL, map_subtype_map_bar h h₀ hbar, ← transpose_map, ← Matrix.map_mul, hg,
    Matrix.map_one _ (map_zero _) (map_one _)]

include hbar in
private theorem mem_primeFormUnitary_of_subfieldGL' {n : ℕ} {g : GL (Fin n) k}
    (hg : subfieldGL k n g ∈ primeFormUnitary h (idGram K n)) :
    g ∈ primeFormUnitary h₀ (idGram k n) := by
  rw [mem_primeFormUnitary] at hg ⊢
  simp only [idGram, Units.val_one, Matrix.mul_one] at hg ⊢
  rw [coe_subfieldGL, map_subtype_map_bar h h₀ hbar, ← transpose_map, ← Matrix.map_mul] at hg
  refine Matrix.map_injective (f := (k.subtype : k → K)) Subtype.val_injective ?_
  change (((g : Matrix (Fin n) (Fin n) k).map h₀.bar)ᵀ * g).map k.subtype =
    (1 : Matrix (Fin n) (Fin n) k).map k.subtype
  rw [hg, Matrix.map_one _ (map_zero _) (map_one _)]

omit h in
private theorem glAut_subfieldGL' (σ : K ≃+* K) (n : ℕ) (g : GL (Fin n) (fixSubfield σ)) :
    glAut σ (subfieldGL (fixSubfield σ) n g) = subfieldGL (fixSubfield σ) n g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact (((g : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j).2

end Subfield

section Reduction

private theorem two_pow_mod_three_of_odd {m : ℕ} (hm : Odd m) : 2 ^ m % 3 = 2 := by
  obtain ⟨t, rfl⟩ := hm
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

variable {f : ℕ} {K : Type} [Field K] [CharP K 2]

theorem glaPLayer_ne_bot_of_fieldHom_conjHom (h : UnitaryFieldData 2 f K) (hf : Odd f)
    (hf3 : f ≠ 3) {σ : K ≃+* K} (hσ : orderOf σ = 3) {M : primeFormUnitary h (idGram K 3)}
    (hM1 : primeFormConjHom h (idGram K 3) M ≠ 1)
    (hM3 : primeFormConjHom h (idGram K 3) M ^ 3 = 1)
    (hcomm : primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ *
        primeFormConjHom h (idGram K 3) M =
      primeFormConjHom h (idGram K 3) M *
        primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ)
    {t : primeFormP h (idGram K 3)} (ht : orderOf t = 2)
    (hfix : primeFormConjHom h (idGram K 3) M t = t) :
    GLAPLayer 3 (fixSubgroup (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ) ⊓
      fixSubgroup (primeFormConjHom h (idGram K 3) M)) ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h.finite
  obtain ⟨h3f, hK₀card⟩ := dvd_and_card_fixSubfield_unitary h Nat.prime_three (by norm_num) hσ
  set e := f / 3 with he
  have hfe : f = 3 * e := (Nat.mul_div_cancel' h3f).symm
  have heodd : Odd e := by
    have : Odd (3 * e) := by rw [← hfe]; exact hf
    exact (Nat.odd_mul.1 this).2
  have he2 : 2 ≤ e := by
    obtain ⟨m, hm⟩ := heodd
    have := h.one_le
    omega
  have hne : ¬ (3 = 3 ∧ 2 ^ f = 2) := by
    rintro ⟨-, h2⟩
    have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [h2] at h4
    norm_num at h4
  have h3 : 3 ∣ 2 ^ f + 1 := by
    have := two_pow_mod_three_of_odd hf
    omega
  have hpq₀ : 3 ∣ 2 ^ e + 1 := by
    have := two_pow_mod_three_of_odd heodd
    omega
  set K₀ := fixSubfield σ with hK₀def
  have hσK₀ : ∀ c ∈ K₀, σ c = c := fun c hc => RingHom.mem_eqLocusField.mp hc
  have h₀ : UnitaryFieldData 2 e K₀ :=
    fixSubfield_unitaryFieldData h Nat.prime_three (by norm_num) hσ
  have hbar₀ : ∀ c : K₀, (h₀.bar c : K) = h.bar c :=
    fixSubfield_unitaryFieldData_bar h Nat.prime_three (by norm_num) hσ
  have h3K₀ : 3 ∣ Nat.card K₀ - 1 := by
    have h4 : 2 ^ (2 * e) % 3 = 1 := by rw [pow_mul, Nat.pow_mod]; norm_num
    rw [hK₀card]
    omega
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd (F := K₀) Nat.prime_three h3K₀
  have hζK : IsPrimitiveRoot (ζ : K) 3 := hζ.map_of_injective K₀.subtype.injective
  set ω : K := (ζ : K) with hωdef
  have hω3 : ω ^ 3 = 1 := hζK.pow_eq_one
  have hωσ : σ ω = ω := hσK₀ _ ζ.2
  have hμ3 : ∀ x : K, x ^ 3 = 1 → σ x = x := by
    intro x hx
    obtain ⟨m, -, rfl⟩ := hζK.eq_pow_of_pow_eq_one hx
    rw [map_pow, hωσ]
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht] at this
  obtain ⟨U, rfl, hU2⟩ := exists_lift_sq_eq_one ht2
  set u : GL (Fin 3) K := (U : GL (Fin 3) K) with hu
  have hu1 : u ≠ 1 := by
    intro h1
    have hU : U = 1 := Subtype.ext h1
    rw [hU, QuotientGroup.mk_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hu2 : u * u = 1 := by
    rw [hu, ← Subgroup.coe_mul, ← sq, hU2, Subgroup.coe_one]
  obtain ⟨A, α, hαn, hA3, hAM⟩ :=
    exists_pow_scalar_of_mem_primeFormD (le_refl 3) ⟨M, rfl⟩ hM3
  rw [hAM] at hM1 hcomm hfix ⊢
  have hAu := mul_comm_of_primeFormConjHom_fix hU2 hfix
  obtain ⟨μ, hμ⟩ := HDescLinRes.exists_cube_root_of_commute hA3 hu1 hu2 hAu
  have hμn : h.norm (μ : K) = 1 :=
    norm_eq_one_of_pow_norm Nat.prime_three (by norm_num) h3 (by rw [hμ]; exact hαn)
  have hμ'n : h.norm ((μ⁻¹ : Kˣ) : K) = 1 := by
    simpa [Units.val_inv_eq_inv_val] using norm_inv_eq_one hμn
  obtain ⟨A', hA'⟩ : ∃ A' : primeFormUnitary h (idGram K 3), A' = scalarU h 3 μ⁻¹ hμ'n * A :=
    ⟨_, rfl⟩
  have hA'c : primeFormConjHom h (idGram K 3) A' = primeFormConjHom h (idGram K 3) A := by
    rw [hA', map_mul, conjHom_scalarU (le_refl 3) hne, one_mul]
  have hA'3 : A' ^ 3 = 1 := by
    rw [hA']
    exact rescale_pow_eq_one (le_refl 3) hne hμ'n (by rw [hμ]; exact hA3)
  have hA'3g : (A' : GL (Fin 3) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hA'3, Subgroup.coe_one]
  have ha'e : (A' : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * A := by
    rw [hA', Subgroup.coe_mul, coe_scalarU]
  have hA'u : (A' : GL (Fin 3) K) * u = u * A' := by
    rw [ha'e, mul_assoc, hAu, ← mul_assoc, ← mul_assoc,
      GeneralLinearGroup.scalar_commute μ⁻¹ u]
  rw [← hA'c] at hM1 hcomm ⊢
  have hA'ns : ∀ c : Kˣ, (A' : GL (Fin 3) K) ≠ GeneralLinearGroup.scalar (Fin 3) c :=
    fun c hc => hM1 (primeFormConjHom_eq_one_of_coe_eq_scalar hc)
  have hσc : primeFormConjHom h (idGram K 3)
      (primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := 3)) σ A') =
      primeFormConjHom h (idGram K 3) A' := by
    have e1 : primeFormConjHom h (idGram K 3)
        (primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := 3)) σ A') =
        primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ *
          primeFormConjHom h (idGram K 3) A' *
          (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ)⁻¹ :=
      (primeFormField_conj_eq h (isPrimeFormGram_idGram (K := K) (n := 3)) σ A').symm
    rw [e1, hcomm, mul_inv_cancel_right]
  have hz : primeFormConjHom h (idGram K 3)
      (A'⁻¹ * primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := 3)) σ A') = 1 := by
    rw [map_mul, map_inv, hσc, inv_mul_cancel]
  obtain ⟨lam, -, hlam⟩ := (primeFormConjHom_eq_one_iff_of_ne (le_refl 3) hne _).1 hz
  have hσA : glAut σ (A' : GL (Fin 3) K) =
      (A' : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) lam := by
    rw [← hlam, Subgroup.coe_mul, Subgroup.coe_inv, coe_primeFormFieldU, mul_inv_cancel_left]
  obtain ⟨P, hP⟩ := HDescLinRes.exists_conj_diagonal_of_pow_three hζK hA'3g
  set d : Fin 3 → K := fun l =>
    ((P * (A' : GL (Fin 3) K) * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) l l with hd
  obtain ⟨i, j, l, hij, hli, hlj, hdij, hdl⟩ :=
    exists_eq_ne_of_diag_of_ne_scalar hP hu1 hu2 hA'u hA'ns
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have htrA : Matrix.trace ((A' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = d l := by
    rw [← Matrix.trace_units_conj P ((A' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      ← Units.val_mul, ← Units.val_mul, hP, Matrix.trace_diagonal, Fin.sum_univ_three,
      HDescLinRes.sum_three_of_ne hij hli hlj, ← hdij]
    linear_combination d i * h2
  have hσtr : σ (Matrix.trace ((A' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      lam * Matrix.trace ((A' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have e1 : Matrix.trace ((glAut σ (A' : GL (Fin 3) K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
        σ (Matrix.trace ((A' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
      rw [coe_glAut, Matrix.trace_fin_three, Matrix.trace_fin_three, map_add, map_add]
      simp only [Matrix.map_apply]
    rw [← e1, hσA, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
      smul_eq_mul]
  have hdl3 := HDescLinRes.diag_pow_three_eq_one hA'3g hP l
  have hdl0 : d l ≠ 0 := by
    intro h0
    rw [h0] at hdl3
    norm_num at hdl3
  have hlam1 : lam = 1 := by
    rw [htrA, hμ3 _ hdl3] at hσtr
    have h0 : ((lam : K) - 1) * d l = 0 := by linear_combination -hσtr
    exact Units.ext (sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hdl0))
  have hσA' : glAut σ (A' : GL (Fin 3) K) = A' := by
    rw [hσA, hlam1, map_one, mul_one]
  obtain ⟨M₀, hM₀⟩ := exists_subfieldGL_eq_of_fixed 3 hσA'
  have hM₀U : M₀ ∈ primeFormUnitary h₀ (idGram K₀ 3) :=
    mem_primeFormUnitary_of_subfieldGL' h hbar₀ (by rw [hM₀]; exact A'.2)
  have hM₀3 : M₀ ^ 3 = 1 :=
    subfieldGL_injective K₀ 3 (by rw [map_pow, hM₀, hA'3g, map_one])
  set A₀ : primeFormUnitary h₀ (idGram K₀ 3) := ⟨M₀, hM₀U⟩ with hA₀
  have hA₀3 : A₀ ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hM₀3)
  obtain ⟨b, ν, -, hb, hν, -⟩ := exists_orthonormal_eigenbasis_pair (h := h₀) Nat.prime_three
    hpq₀ (A := A₀) (B := A₀) rfl hA₀3 hA₀3
  have hν' : ∀ i, (M₀ : Matrix (Fin 3) (Fin 3) K₀) *ᵥ b i = ν i • b i := fun i =>
    (CFSG.RankThree.PartOne.KCUnitaryBlock.toLinU_apply_eq h₀ A₀ (b i)).symm.trans (hν i)
  have hmapdiag : ∀ (R : GL (Fin 3) K₀) (w : Fin 3 → K₀),
      ((R * M₀ * R⁻¹ : GL (Fin 3) K₀) : Matrix (Fin 3) (Fin 3) K₀) = diagonal w →
      ((subfieldGL K₀ 3 R * (A' : GL (Fin 3) K) * (subfieldGL K₀ 3 R)⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = diagonal (fun t => (w t : K)) := by
    intro R w hR
    rw [← hM₀, ← map_inv, ← map_mul, ← map_mul, coe_subfieldGL, hR]
    exact Matrix.diagonal_map (map_zero _)
  obtain ⟨R₀, -, hR₀⟩ := exists_unitary_conj_eq_diagonal h₀ hb hν'
  obtain ⟨i', j', l', hij', hli', hlj', hdij', hdl'⟩ :=
    exists_eq_ne_of_diag_of_ne_scalar (hmapdiag R₀ ν hR₀) hu1 hu2 hA'u hA'ns
  have hπ := injective_vec_three hij' hli' hlj'
  obtain ⟨R₁, hR₁U, hR₁⟩ := exists_unitary_conj_eq_diagonal h₀
    (isOrthonormalFamily_comp hb hπ) (fun c => hν' (![i', j', l'] c))
  set Q : primeFormUnitary h (idGram K 3) :=
    ⟨subfieldGL K₀ 3 R₁, subfieldGL_mem_primeFormUnitary' h hbar₀ hR₁U⟩ with hQ
  have hX : (((Q * A' * Q⁻¹ : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (fun t => (ν (![i', j', l'] t) : K)) :=
    hmapdiag R₁ _ hR₁
  set F₀ : Subfield K := h₀.fixedField.map K₀.subtype with hF₀def
  have hF₀ : Nat.card F₀ = 2 ^ e := by
    have h1 : ((F₀ : Subfield K) : Set K) = K₀.subtype '' (h₀.fixedField : Set K₀) :=
      Subfield.coe_map _ _
    have h2 : Nat.card F₀ = Nat.card ((F₀ : Subfield K) : Set K) := rfl
    rw [h2, h1, Nat.card_image_of_injective K₀.subtype.injective]
    exact h₀.card_fixedField
  have hF₀σ : ∀ c ∈ F₀, σ c = c := by
    intro c hc
    obtain ⟨x, -, rfl⟩ := Subfield.mem_map.1 hc
    exact hσK₀ _ x.2
  have hF₀b : ∀ c ∈ F₀, h.bar c = c := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Subfield.mem_map.1 hc
    show h.bar (x : K) = x
    rw [← hbar₀ x]
    exact congrArg Subtype.val ((UnitaryFieldData.mem_fixedField h₀).1 hx)
  have hF₀mem : ∀ c : K, σ c = c → h.bar c = c → c ∈ F₀ := by
    intro c hσc hbc
    refine Subfield.mem_map.2 ⟨⟨c, RingHom.mem_eqLocusField.2 hσc⟩,
      (UnitaryFieldData.mem_fixedField h₀).2 (Subtype.ext ?_), rfl⟩
    rw [hbar₀]
    exact hbc
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have e1 : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
    rw [hω3, sub_self] at e1
    exact (mul_eq_zero.1 e1).resolve_left (sub_ne_zero.2 (hζK.ne_one (by norm_num)))
  have hωb : h.bar ω = ω ^ 2 := by
    rw [UnitaryFieldData.bar_apply, pow_eq_pow_mod _ hω3, two_pow_mod_three_of_odd hf]
  have hcore := glaPLayer_ne_bot_of_unitary_diagonal h he2 hF₀ hF₀σ hF₀b hF₀mem hω hωσ hωb hX
    (show (ν i' : K) = ν j' from hdij') (show (ν i' : K) ≠ ν l' from fun h => hdl' h.symm)
  have hσQ : primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := 3)) σ Q = Q :=
    Subtype.ext (by rw [coe_primeFormFieldU]; exact glAut_subfieldGL' σ 3 R₁)
  have e2 : primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ *
      primeFormConjHom h (idGram K 3) Q *
      (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ)⁻¹ =
      primeFormConjHom h (idGram K 3) Q := by
    have := primeFormField_conj_eq h (isPrimeFormGram_idGram (K := K) (n := 3)) σ Q
    rwa [hσQ] at this
  have hfconj : primeFormConjHom h (idGram K 3) Q *
      primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ *
      (primeFormConjHom h (idGram K 3) Q)⁻¹ =
      primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ := by
    calc primeFormConjHom h (idGram K 3) Q *
          primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ *
          (primeFormConjHom h (idGram K 3) Q)⁻¹
        = (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ *
            primeFormConjHom h (idGram K 3) Q *
            (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ)⁻¹) *
          primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ *
          (primeFormConjHom h (idGram K 3) Q)⁻¹ := by rw [e2]
      _ = primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ := by group
  have hcX : primeFormConjHom h (idGram K 3) (Q * A' * Q⁻¹) =
      primeFormConjHom h (idGram K 3) Q * primeFormConjHom h (idGram K 3) A' *
        (primeFormConjHom h (idGram K 3) Q)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  apply HDescLinRes.glaPLayer_ne_bot_of_conj Nat.prime_three (primeFormConjHom h (idGram K 3) Q)
  rw [hfconj, ← hcX]
  exact hcore

end Reduction

section Assembly

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem goodSubThree_primeFormP {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K) (hℓ : ℓ = 2) (hf : Odd f)
    (hf1 : f ≠ 1) (hf3 : f ≠ 3) : HDescLinRes.GoodSubThree (primeFormP h (idGram K 3)) := by
  classical
  subst hℓ
  intro A hA hA27 T hT2 hT hAT
  have hA1 : A ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hA27
    norm_num at hA27
  obtain ⟨B, hBA, hBcard, t, -, ht, hBt⟩ :=
    HDescLinRes.exists_hyperplane_fix_involution Nat.prime_three (by norm_num) hA hA1 hT2 hT hAT
  have hB : IsElemAbelian 3 B := isElemAbelian_mono hA hBA
  have h2f := two_pow_mod_three_of_odd hf
  have h3 : 3 ∣ 2 ^ f + 1 := by omega
  have hf5 : 5 ≤ f := by
    obtain ⟨m, hm⟩ := hf
    omega
  have hq3 : 3 < 2 ^ f :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf5 : 2 ^ 5 ≤ 2 ^ f)
  have hne : ¬ (3 = 3 ∧ 2 ^ f = 2) := fun h' => by omega
  have hBD : Nat.card (B ⊓ primeFormD h (idGram K 3) :
      Subgroup (MulAut (primeFormP h (idGram K 3)))) ≤ 3 :=
    card_le_three_of_le_primeFormD h h3 hq3 (isElemAbelian_mono hB inf_le_left) inf_le_right ht
      (fun e he => hBt e (Subgroup.mem_inf.1 he).1)
  have hBf := card_le_three_mul_card_inf_primeFormD h hne (B := B) (fun b hb => hB.2 b hb)
  have h27 : (27 : ℕ) ≤ Nat.card B * 3 := by
    rw [hBcard]
    exact hA27
  have hB9 : Nat.card B = 9 := by omega
  obtain ⟨x, hxB, hxD⟩ : ∃ x ∈ B, x ∉ primeFormD h (idGram K 3) := by
    by_contra hc
    push Not at hc
    have := Subgroup.card_le_of_le (le_inf le_rfl hc : B ≤ B ⊓ primeFormD h (idGram K 3))
    omega
  have hBD1 : (B ⊓ primeFormD h (idGram K 3) :
      Subgroup (MulAut (primeFormP h (idGram K 3)))) ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hBf
    omega
  obtain ⟨⟨c, hcBD⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hBD1
  have hc1' : c ≠ 1 := fun h0 => hc1 (Subtype.ext h0)
  have hcB := (Subgroup.mem_inf.1 hcBD).1
  have hcD := (Subgroup.mem_inf.1 hcBD).2
  have hx3 : x ^ 3 = 1 := hB.2 x hxB
  have hcomm : x * c = c * x := congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hxB⟩ ⟨c, hcB⟩)
  have hcl := HDescLinRes.closure_eq_of_card_nine_not_mem hB9 hxB hcB hx3 hxD hcD hc1'
  refine ⟨Subgroup.closure {x, c}, hcl.le.trans hBA, by rw [hcl, hB9]; norm_num, ?_⟩
  apply HDescLinRes.isGood_closure_pair
  obtain ⟨σ, hσdef⟩ : ∃ σ : K ≃+* K, primeFormFieldFactor h
      (isPrimeFormGram_idGram (K := K) (n := 3)) (le_refl 3) hne x = σ := ⟨_, rfl⟩
  have hker := ker_primeFormFieldFactor h (isPrimeFormGram_idGram (K := K) (n := 3)) (le_refl 3) hne
  have hσ3 : σ ^ 3 = 1 := by rw [← hσdef, ← map_pow, hx3, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hxD
    rw [← hker, MonoidHom.mem_ker, hσdef, h1]
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 (fun h0 => hxD (h0 ▸ Subgroup.one_mem _))
  obtain ⟨-, -, -, -, -, N, hN⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' h (le_refl 3) hne
      Nat.prime_three (by norm_num) x hxo σ hσdef hσo
  have hc3 : c ^ 3 = 1 := hB.2 c hcB
  have hct : c t = t := hBt c hcB
  obtain ⟨M, rfl⟩ := hcD
  obtain ⟨g, hg⟩ : ∃ g : MulAut (primeFormP h (idGram K 3)),
      g = primeFormConjHom h (idGram K 3) N := ⟨_, rfl⟩
  have hcM' : primeFormConjHom h (idGram K 3) (N⁻¹ * M * N) =
      g⁻¹ * primeFormConjHom h (idGram K 3) M * g := by
    rw [hg, map_mul, map_mul, map_inv]
  have hfσ : primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ = g⁻¹ * x * g := by
    rw [hg]
    exact hN.symm
  have hM1 : primeFormConjHom h (idGram K 3) (N⁻¹ * M * N) ≠ 1 := by
    rw [hcM']
    intro h1
    apply hc1'
    calc primeFormConjHom h (idGram K 3) M =
          g * (g⁻¹ * primeFormConjHom h (idGram K 3) M * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hM3 : primeFormConjHom h (idGram K 3) (N⁻¹ * M * N) ^ 3 = 1 := by
    rw [hcM']
    have := conj_pow (a := g⁻¹) (b := primeFormConjHom h (idGram K 3) M) (i := 3)
    rw [inv_inv] at this
    rw [this, hc3]
    group
  have hcomm' : primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ *
      primeFormConjHom h (idGram K 3) (N⁻¹ * M * N) =
      primeFormConjHom h (idGram K 3) (N⁻¹ * M * N) *
        primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ := by
    rw [hfσ, hcM']
    calc g⁻¹ * x * g * (g⁻¹ * primeFormConjHom h (idGram K 3) M * g)
        = g⁻¹ * (x * primeFormConjHom h (idGram K 3) M) * g := by group
      _ = g⁻¹ * (primeFormConjHom h (idGram K 3) M * x) * g := by rw [hcomm]
      _ = g⁻¹ * primeFormConjHom h (idGram K 3) M * g * (g⁻¹ * x * g) := by group
  have ht' : orderOf (g⁻¹ t) = 2 :=
    (orderOf_injective (g⁻¹ : MulAut (primeFormP h (idGram K 3))).toMonoidHom
      (MulEquiv.injective _) t).trans ht
  have hfix' : primeFormConjHom h (idGram K 3) (N⁻¹ * M * N) (g⁻¹ t) = g⁻¹ t := by
    rw [hcM']
    simp only [MulAut.mul_apply, MulAut.apply_inv_self, hct]
  have hred := glaPLayer_ne_bot_of_fieldHom_conjHom h hf hf3 hσo hM1 hM3 hcomm' ht' hfix'
  apply HDescLinRes.glaPLayer_ne_bot_of_conj Nat.prime_three g⁻¹
  rw [show g⁻¹ * x * g⁻¹⁻¹ = primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := 3)) σ by
      rw [hfσ, inv_inv],
    show g⁻¹ * primeFormConjHom h (idGram K 3) M * g⁻¹⁻¹ =
      primeFormConjHom h (idGram K 3) (N⁻¹ * M * N) by rw [hcM', inv_inv]]
  exact hred

end Assembly

theorem goodSubAt_unitary (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hq : q.p = 2) (hodd : Odd q.exponent)
    (h8 : q.card ≠ 8) : HDesc.GoodSubAt 3 ⟨.twistedA 2 q, hv⟩ 2 := by
  intro _ _ A hA hcard T hT2 hT hAT
  obtain ⟨r, q', K, _, hU, -, hdA, hne, ⟨eP⟩⟩ :=
    KD264Lie.exists_primeFormP_mulEquiv_of_isUnitaryIdx (d := ⟨.twistedA 2 q, hv⟩) trivial
  injection hdA with hr hqq
  subst hr hqq
  haveI := hU.charP
  haveI := hU.finite
  haveI : CharP K 2 := CharP.congr q.p hq
  have hcard' := TauCeti.PrimePower.card_def q
  have hf1 : q.exponent ≠ 1 := fun h1 => hne ⟨rfl, by rw [hcard', hq, h1]; norm_num⟩
  have hf3 : q.exponent ≠ 3 := fun h3 => h8 (by rw [hcard', hq, h3]; norm_num)
  exact HDescLinRes.GoodSubThree.of_mulEquiv eP (goodSubThree_primeFormP hU hq hodd hf1 hf3) A hA
    hcard T hT2 hT hAT

theorem unitaryRes_twistedA_two (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hq : q.p = 2) (hodd : Odd q.exponent)
    (h8 : q.card ≠ 8) :
    HDesc.LpEpsNoGoodTwoLocal 3 ⟨.twistedA 2 q, hv⟩ ∧ HDesc.GoodSubAt 3 ⟨.twistedA 2 q, hv⟩ 2 :=
  ⟨lpEpsNoGoodTwoLocal_unitary q hv hq, goodSubAt_unitary q hv hq hodd h8⟩

end CFSG.LocalAnalysis.GLTheoremA.HDescUniRes

end
