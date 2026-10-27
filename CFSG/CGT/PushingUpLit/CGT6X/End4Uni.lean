module

public import CFSG.CGT.PushingUpLit.CGT6X.End4Frame
public import CFSG.CGT.PushingUpLit.CGT6X.End4Cover
public import CFSG.CGT.PushingUpLit.CGT6X.End4Core
public import CFSG.CGT.PushingUpLit.CGT6X.End3Cfg
public import CFSG.CGT.PushingUpLit.CGT6X.K7aBridge
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.ClassicalGroups.UnitaryFlag.WittBasis
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.FourFive
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.CGT.PushingUpLit.CGT6X.K7a
  CFSG.CGT.PushingUpLit.CGT6X.End3 CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6
  CFSG.LieType.Steinberg.CentralExt CFSG.LocalAnalysis CFSG.SL2MinimalFaithful
  CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.Open (StatedClassicalModel)

section Torus

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

include h in
theorem exists_bar_eq_one_add : ∃ s : K, h.bar s = 1 + s := by
  have := h.charP
  obtain ⟨c, hc⟩ := exists_add_bar_eq_neg_one h
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h1 : (-1 : K) = 1 := CharTwo.neg_eq 1
  rw [h1] at hc
  exact ⟨c, by linear_combination hc + (-c) * h2⟩

theorem bar_eq_inv_of_norm {a : Kˣ} (ha : (a : K) * h.bar a = 1) : h.bar a = ((a⁻¹ : Kˣ) : K) := by
  rw [Units.val_inv_eq_inv_val]
  exact eq_inv_of_mul_eq_one_right ha

variable {h} [CharP K 2]

theorem kap_mem_gramSU {s : K} (hs : h.bar s = 1 + s) (t : Kˣ × Kˣ × Kˣ)
    (h1 : (t.1 : K) * h.bar t.1 = 1) (h2 : (t.2.1 : K) * h.bar t.2.1 = 1)
    (h3 : (t.2.2 : K) * h.bar t.2.2 = 1) (ht : t.1 * t.2.1 * t.2.2 = 1) :
    kap s t ∈ gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  refine ⟨?_, ?_⟩
  · rw [kap_coe, tm_map s h.bar hs, tm_transpose, Units.val_one, Matrix.mul_one, tm_mul,
      mul_comm (h.bar _), mul_comm (h.bar _), mul_comm (h.bar _), h1, h2, h3]
    exact tm_one s
  · rw [kap_det]
    simpa using congrArg Units.val ht

theorem wm_map_transpose {s : K} (σ : K →+* K) (hσ : σ s = 1 + s) :
    ((wm s).map σ)ᵀ = wm s := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hs2 : (1 : K) + (1 + s) = s := by linear_combination h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wm, fu, fv, fc, hσ, hs2] <;>
    first | linear_combination h2 | linear_combination (-1 : K) * h2 | ring

theorem wGL_mem_gramSU {s : K} (hs : h.bar s = 1 + s) :
    wGL s ∈ gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  refine ⟨?_, ?_⟩
  · rw [wGL_coe, wm_map_transpose h.bar hs, Units.val_one, Matrix.mul_one]
    exact wm_sq s
  · have h1 := congrArg Matrix.det (wm_sq s)
    rw [det_mul, det_one] at h1
    exact K7a.eq_one_of_sq_eq_one (by rw [pow_two]; exact h1)

omit [CharP K 2] in
theorem mem_range_orthGU {g : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)}
    (hfix : ∀ i j, h.bar (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) : g ∈ (orthGU h).range := by
  set M' : Matrix (Fin 3) (Fin 3) K := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM'
  have hM'barmap : M'.map h.bar = M' := Matrix.ext fun i j => hfix i j
  have hM'det : M'.det = 1 := g.2.2
  have hgram : M'ᵀ * M' = 1 := by
    have h1 := g.2.1
    rw [hM'barmap] at h1
    simpa using h1
  let Ak' : Matrix (Fin 3) (Fin 3) h.fixedField := Matrix.of fun i j => ⟨M' i j, hfix i j⟩
  have hAkmap : Ak'.map h.fixedField.subtype = M' := by
    ext i j
    rfl
  have hdetk : Ak'.det = 1 := by
    apply h.fixedField.subtype.injective
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hAkmap, hM'det, map_one]
  have hAkorth : Ak' * Ak'ᵀ = 1 := by
    apply Matrix.map_injective h.fixedField.subtype.injective
    show (Ak' * Ak'ᵀ).map h.fixedField.subtype = (1 : Matrix (Fin 3) (Fin 3) h.fixedField).map
      h.fixedField.subtype
    rw [Matrix.map_mul, transpose_map, hAkmap, Matrix.map_one _ (map_zero _) (map_one _)]
    exact mul_eq_one_comm.mp hgram
  refine ⟨⟨⟨Ak', hdetk⟩, hAkorth⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hAkmap

theorem tm_comm_orthGU (s x y : K) (A : orthSL h.fixedField) :
    (((orthGU h A : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * tm s x y y =
      tm s x y y * (((orthGU h A : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
        GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have hmat : (((orthGU h A : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (A.1 : Matrix (Fin 3) (Fin 3) h.fixedField).map h.fixedField.subtype := rfl
  have hM : (A.1 : Matrix (Fin 3) (Fin 3) h.fixedField).map h.fixedField.subtype *
      ((A.1 : Matrix (Fin 3) (Fin 3) h.fixedField).map h.fixedField.subtype)ᵀ = 1 := by
    rw [← transpose_map, ← Matrix.map_mul, mem_orthSL.1 A.2,
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hmat]
  exact tm_comm s (row_sum_eq_one hM) (col_sum_eq_one (mul_eq_one_comm.mp hM)) x y

end Torus

section Cover

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

include h in
theorem hsplit_gramSU
    (hf : 2 ≤ f) (E : Type) [Group E] [Finite E]
    (π : E →* gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) →* E, ∀ g, π (σ g) = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.charP
  have := h.finite
  let ι : ↥(unitarySU 2 f K 3) ≃* ↥(gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 3)
  have hq : ((3 : ℕ), 2 ^ f) ≠ ((3 : ℕ), 2) := by
    intro hh
    have h2 : 2 ^ f = 2 := (Prod.mk.inj hh).2
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hπ' : Function.Surjective (ι.symm.toMonoidHom.comp π) := ι.symm.surjective.comp hπ
  have hcen' : (ι.symm.toMonoidHom.comp π).ker ≤ Subgroup.center E := by
    intro x hx
    apply hcen
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : ι.symm (π x) = 1 := hx
    exact ι.symm.injective (by rw [h1, map_one])
  obtain ⟨s, hs⟩ := SUOdd.statedSU_odd_exists_section_of_central (F := K) (p := 2) (f := f)
    h.card_eq_sq (by omega) (n := 3) le_rfl (by decide) hq hπ' hcen'
  refine ⟨s.comp ι.symm.toMonoidHom, fun g => ?_⟩
  have h1 := hs (ι.symm g)
  have h2 : ι.symm (π (s (ι.symm g))) = ι.symm g := h1
  exact ι.symm.injective h2

include h in
theorem isPerfect_gramSU (hf : 2 ≤ f) :
    Group.IsPerfect (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.charP
  have := h.finite
  have hq : ((3 : ℕ), 2 ^ f) ≠ ((3 : ℕ), 2) := by
    intro hh
    have h2 : 2 ^ f = 2 := (Prod.mk.inj hh).2
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hperf := SUOdd.isPerfect_statedSU_odd (F := K) (p := 2) (f := f) h.card_eq_sq (n := 3)
    le_rfl hq
  exact Group.IsPerfect.ofSurjective
    (f := (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 3)).toMonoidHom) (MulEquiv.surjective _)

include h in
theorem exists_norm_one_unit (hf : 2 ≤ f) :
    ∃ a : Kˣ, (a : K) * h.bar a = 1 ∧ a ^ (2 ^ f + 1) = 1 ∧ a ^ 3 ≠ 1 := by
  have := h.finite
  have := h.charP
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hcard : Nat.card Kˣ = (2 ^ f) ^ 2 - 1 := by rw [Nat.card_units, h.card_eq_sq]
  obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ f := ⟨_, rfl⟩
  rw [← hq] at hcard ⊢
  have hq4 : 4 ≤ q := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have key : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have h1 : 1 ≤ q := by omega
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2]
    ring
  have hdvd : q - 1 ∣ orderOf g := by rw [hord, hcard, key]; exact dvd_mul_right _ _
  have hA : orderOf (g ^ (q - 1)) = q + 1 := by
    rw [orderOf_pow_of_dvd (by omega) hdvd, hord, hcard, key]
    exact Nat.mul_div_cancel_left _ (by omega)
  refine ⟨g ^ (q - 1), ?_, ?_, ?_⟩
  · rw [h.bar_apply, ← hq, ← pow_succ', ← Units.val_pow_eq_pow_val, ← hA, pow_orderOf_eq_one,
      Units.val_one]
  · rw [← hA, pow_orderOf_eq_one]
  · intro h3
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [hA] at h4
    have := Nat.le_of_dvd (by norm_num) h4
    omega

end Cover

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem end411_unitary
    (hV : ∀ v : V, v ^ 2 = 1) {L Y : Subgroup (MulAut V)}
    (hYL : Y ≤ L) [Group.IsPerfect ↥L] (hSQ : SimpleQuot Y) (hgen : CommGen Y) {t : MulAut V}
    (htN : t ∈ Subgroup.normalizer (L : Set (MulAut V))) (ht2 : t ^ 2 = 1)
    (htY : ∀ y ∈ Y, t * y = y * t)
    (hτout : ∀ x : ↥L ⧸ Subgroup.center ↥L,
      centerAutHom ↥L (conjOn L t htN) ≠ MulAut.conj x)
    {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ f)
    (hYF : Nonempty (↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    (hmod : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2 f) : False := by
  set Y' : Subgroup ↥L := Y.subgroupOf L with hY'def
  obtain ⟨φ⟩ := hYF
  let φ' : ↥Y' ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (Subgroup.subgroupOfEquivOfLe hYL).trans φ
  have hτ2 : conjOn L t htN ^ 2 = 1 := conjOn_sq L t htN ht2
  have hYτ : ∀ y ∈ Y', conjOn L t htN y = y := fun y hy =>
    conjOn_fixes L t htN y (htY y hy)
  obtain ⟨K, _, _, h, Φ, θ, H, -, -, hΦτ, hΦY⟩ :=
    K7a_unitary (L := ↥L) hf hmod (conjOn L t htN) hτ2 hτout Y' hF ⟨φ'⟩ hYτ
  have hchar : CharP K 2 := h.charP
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Φ' : (↥L ⧸ Subgroup.center ↥L) ≃* PI h := Φ.trans θ.symm
  have hΦ'τ : ∀ y : ↥L, Φ' (QuotientGroup.mk (conjOn L t htN y)) =
      barAut h (Φ' (QuotientGroup.mk y)) := by
    intro y
    have h1 := hΦτ (QuotientGroup.mk y)
    rw [centerAutHom_mk] at h1
    show θ.symm (Φ (QuotientGroup.mk (conjOn L t htN y))) =
      barAut h (θ.symm (Φ (QuotientGroup.mk y)))
    rw [h1]
    simp
  let q : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) →* PI h :=
    QuotientGroup.mk'
      (normOneScalars h (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 3)
  set O : Subgroup (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    (orthGU h).range with hOdef
  have hO : ∀ y ∈ Y', ∃ o ∈ O, Φ' (QuotientGroup.mk y) = q o := by
    intro y hy
    have h1 : Φ (QuotientGroup.mk y) ∈ (orthToP h).range.map θ.toMonoidHom := by
      rw [← hΦY]
      exact ⟨QuotientGroup.mk y, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨x, hx, hxy⟩ := h1
    obtain ⟨A, rfl⟩ := hx
    refine ⟨orthGU h A, ⟨A, rfl⟩, ?_⟩
    show θ.symm (Φ (QuotientGroup.mk y)) = _
    rw [← hxy]
    simp [q, orthToP]
  obtain ⟨ρ, hρ⟩ := exists_cover Φ' q (hsplit_gramSU h hf)
  have hMperf := isPerfect_gramSU h hf
  let γ : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) →*
      gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    (primeFormFieldSU h isPrimeFormGram_one (fieldDataHermitianForm h).conj).toMonoidHom
  have hint := cover_intertwine Φ' q ρ hρ (conjOn L t htN).toMonoidHom (barAut h).toMonoidHom γ
    hΦ'τ (fun m => (primeFormFieldAut_mk h isPrimeFormGram_one _ m).symm)
  have hF4 : ∃ s : Finset F, s.card = 4 := by
    have : Fintype F := Fintype.ofFinite F
    have h4 : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
    exact ⟨s, hs⟩
  have hY'perf : Group.IsPerfect ↥Y' := by
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
      LinearGroups.special_linear_dimension_two_perfect hF4
    exact Group.IsPerfect.ofSurjective (f := φ'.symm.toMonoidHom) φ'.symm.surjective
  have hcardY : Nat.card O ≤ Nat.card ↥Y' := by
    have := h.finite
    calc Nat.card O ≤ Nat.card (orthSL h.fixedField) :=
          Nat.card_le_card_of_surjective _ (orthGU h).rangeRestrict_surjective
      _ ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := card_orthSL_le
      _ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
          rw [card_specialLinearGroup_fin_two, card_specialLinearGroup_fin_two, hF,
            h.card_fixedField]
      _ = Nat.card ↥Y' := (Nat.card_congr φ'.toEquiv).symm
  have hYO' : Y' = O.map ρ :=
    eq_map_of_perfect Φ' q ρ hρ Y' Subgroup.commutator_eq_self O hO hcardY
  set ρ' : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) →* MulAut V :=
    L.subtype.comp ρ with hρ'
  have hYO : Y = O.map ρ' := by
    have h1 : Y'.map L.subtype = Y := Subgroup.map_subgroupOf_eq_of_le hYL
    rw [← h1, hYO', Subgroup.map_map]
  have hγ' : ∀ m, t * ρ' m * t⁻¹ = ρ' (γ m) := by
    intro m
    have h1 := congrArg (fun φ : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) →* ↥L =>
      ((φ m : ↥L) : MulAut V)) hint
    simpa [conjOn_apply, hρ'] using h1
  obtain ⟨s, hs⟩ := exists_bar_eq_one_add h
  obtain ⟨a, hanorm, han, ha3⟩ := exists_norm_one_unit h hf
  have hnodd : Odd (2 ^ f + 1) := (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  have hbar_a : h.bar (a : K) = ((a⁻¹ : Kˣ) : K) := bar_eq_inv_of_norm h hanorm
  have hbar_ainv : h.bar ((a⁻¹ : Kˣ) : K) = (a : K) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hbar_a, Units.val_inv_eq_inv_val, inv_inv]
  have hn1 : ((1 : Kˣ) : K) * h.bar ((1 : Kˣ) : K) = 1 := by simp
  have hn3 : ((a⁻¹ : Kˣ) : K) * h.bar ((a⁻¹ : Kˣ) : K) = 1 := by
    rw [hbar_ainv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hn4 : ((a⁻¹ * a⁻¹ : Kˣ) : K) * h.bar ((a⁻¹ * a⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_mul, map_mul, hbar_ainv]
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  let α : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    ⟨kap s (1, a, a⁻¹), kap_mem_gramSU hs _ hn1 hanorm hn3 (by simp)⟩
  let δ : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    ⟨kap s (a⁻¹ * a⁻¹, a, a), kap_mem_gramSU hs _ hn4 hanorm hanorm (by group)⟩
  let ω : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    ⟨wGL s, wGL_mem_gramSU hs⟩
  obtain ⟨hrel, hαn, hδn⟩ := torus_elements s
    (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).subtype Subtype.val_injective a
    han (α := α) (δ := δ) (ω := ω) rfl rfl rfl
  have hαO : α ∈ O := by
    apply mem_range_orthGU
    intro i j
    have hmap1 : (tm s ((1 : Kˣ) : K) (a : K) ((a⁻¹ : Kˣ) : K)).map h.bar =
        tm s ((1 : Kˣ) : K) (a : K) ((a⁻¹ : Kˣ) : K) := by
      have hbar1 : h.bar ((1 : Kˣ) : K) = ((1 : Kˣ) : K) := by simp
      rw [tm_map s h.bar hs, hbar1, hbar_ainv, hbar_a]
    exact congrFun (congrFun hmap1 i) j
  have hδC : ∀ o ∈ O, δ * o = o * δ := by
    intro o ho
    obtain ⟨A, rfl⟩ := ho
    apply Subtype.ext
    apply Units.ext
    exact (tm_comm_orthGU s _ _ A).symm
  have hγδ : γ δ = δ⁻¹ := by
    apply Subtype.ext
    apply Units.ext
    have hb1 : h.bar ((a⁻¹ * a⁻¹ : Kˣ) : K) = (((a⁻¹ * a⁻¹)⁻¹ : Kˣ) : K) := by
      rw [Units.val_mul, map_mul, hbar_ainv]
      simp
    have e1 : (((γ δ : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
        (tm s ((a⁻¹ * a⁻¹ : Kˣ) : K) (a : K) (a : K)).map h.bar := rfl
    have e2 : ((((δ⁻¹ : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
        tm s (((a⁻¹ * a⁻¹)⁻¹ : Kˣ) : K) ((a⁻¹ : Kˣ) : K) ((a⁻¹ : Kˣ) : K) := rfl
    rw [e1, e2, tm_map s h.bar hs, hb1, hbar_a]
  have hcore := end411_core hV hSQ hgen ht2 htY ρ' (fun m => γ m) O hYO hγ' hnodd hαO hδC hγδ
    hαn hδn hrel
  have h1 : ρ δ = 1 := Subtype.ext (by simpa [hρ'] using hcore)
  have h2 : q δ = 1 := by
    rw [← hρ, h1]
    simp
  have h3 : δ ∈ normOneScalars h (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 3 :=
    (QuotientGroup.eq_one_iff δ).mp h2
  obtain ⟨c, -, -, hc⟩ := h3
  have hc' : tm s ((a⁻¹ * a⁻¹ : Kˣ) : K) (a : K) (a : K) = Matrix.scalar (Fin 3) (c : K) := by
    have h5 : ((δ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hc]
    rw [GeneralLinearGroup.coe_scalar] at h5
    exact h5
  have h4 : ((a⁻¹ * a⁻¹ : Kˣ) : K) = (a : K) := eq_of_tm_scalar s _ _ _ hc'
  have h5 : a⁻¹ * a⁻¹ = a := Units.ext h4
  apply ha3
  calc a ^ 3 = a * a * a := pow_three' a
    _ = a * a * (a⁻¹ * a⁻¹) := by rw [h5]
    _ = 1 := by group

end Main

end CFSG.CGT.PushingUpLit.CGT6X.End4
