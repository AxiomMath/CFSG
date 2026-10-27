module

public import CFSG.GroupTheory.WeirSylow.GL
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.GroupTheory.WeirSylow

open Module Finset
open LinearMap (BilinForm)
open CFSG.Assembly.LowTwoRank (StatedSp)

section Spaces

variable {K : Type} [Field K]

@[expose] def IsSymplecticSpace (S : FormSpace K K) : Prop :=
  ∃ B : BilinForm K S.V, (∀ x y, S.F x y = B x y) ∧ B.IsAlt ∧ B.Nondegenerate

theorem nondegenerate_of_isAlt {V : Type*} [AddCommGroup V] [Module K V] {B : BilinForm K V}
    (hB : B.IsAlt) (h : ∀ x, (∀ y, B x y = 0) → x = 0) : B.Nondegenerate :=
  (LinearMap.IsAlt.isRefl hB).nondegenerate_iff_separatingLeft.2 h

@[expose] def piBilinForm {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module K (V i)] (B : ∀ i, BilinForm K (V i)) : BilinForm K (∀ i, V i) :=
  LinearMap.mk₂ K (fun x y => ∑ i, B i (x i) (y i))
    (fun x x' y => by simp [Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum])
    (fun x y y' => by simp [Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum])

theorem piBilinForm_apply {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module K (V i)] (B : ∀ i, BilinForm K (V i)) (x y : ∀ i, V i) :
    piBilinForm B x y = ∑ i, B i (x i) (y i) :=
  rfl

@[expose] def prodBilinForm {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (B : BilinForm K V) (C : BilinForm K W) : BilinForm K (V × W) :=
  LinearMap.mk₂ K (fun x y => B x.1 y.1 + C x.2 y.2)
    (fun x x' y => by
      simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
      ring)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring)
    (fun x y y' => by
      simp only [Prod.fst_add, Prod.snd_add, map_add]
      ring)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul]
      ring)

theorem prodBilinForm_apply {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (B : BilinForm K V) (C : BilinForm K W) (x y : V × W) :
    prodBilinForm B C x y = B x.1 y.1 + C x.2 y.2 :=
  rfl

theorem isSymplecticSpace_pi {ι : Type} [Fintype ι] (S : ι → FormSpace K K)
    (hS : ∀ i, IsSymplecticSpace (S i)) : IsSymplecticSpace (FormSpace.pi S) := by
  classical
  choose B hBF hBa hBn using hS
  refine ⟨piBilinForm B, fun x y => ?_, fun x => ?_, ?_⟩
  · change ∑ i, (S i).F (x i) (y i) = _
    simp [hBF, piBilinForm_apply]
  · simp [piBilinForm_apply, (hBa _).self_eq_zero]
  · refine nondegenerate_of_isAlt (fun x => by simp [piBilinForm_apply, (hBa _).self_eq_zero])
      fun x hx => ?_
    funext i
    refine (hBn i).1 (x i) fun z => ?_
    have := hx (Pi.single i z)
    rwa [piBilinForm_apply, Finset.sum_eq_single i
      (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero]) (by simp),
      Pi.single_eq_same] at this

theorem isSymplecticSpace_prod (S T : FormSpace K K) (hS : IsSymplecticSpace S)
    (hT : IsSymplecticSpace T) : IsSymplecticSpace (S.prod T) := by
  obtain ⟨B, hBF, hBa, hBn⟩ := hS
  obtain ⟨C, hCF, hCa, hCn⟩ := hT
  refine ⟨prodBilinForm B C, fun x y => ?_, fun x => ?_, ?_⟩
  · change S.F x.1 y.1 + T.F x.2 y.2 = _
    rw [hBF, hCF, prodBilinForm_apply]
  · rw [prodBilinForm_apply, hBa.self_eq_zero, hCa.self_eq_zero, add_zero]
  · refine nondegenerate_of_isAlt (fun x => by
      rw [prodBilinForm_apply, hBa.self_eq_zero, hCa.self_eq_zero, add_zero])
      fun x hx => Prod.ext (hBn.1 x.1 fun z => ?_) (hCn.1 x.2 fun z => ?_)
    · simpa [prodBilinForm_apply] using hx (z, 0)
    · simpa [prodBilinForm_apply] using hx (0, z)

@[expose] def stdSympSpace (K : Type) [Field K] (r : ℕ) : FormSpace K K :=
  ⟨Fin r ⊕ Fin r → K, fun x y => CFSG.LocalAnalysis.ComponentInitial.pairedSympForm K r x y⟩

theorem isSymplecticSpace_stdSympSpace (r : ℕ) : IsSymplecticSpace (stdSympSpace K r) :=
  ⟨CFSG.LocalAnalysis.ComponentInitial.pairedSympForm K r, fun _ _ => rfl,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.pairedSympForm_isAlt,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.pairedSympForm_nondegenerate⟩

theorem finrank_stdSympSpace (r : ℕ) : finrank K (stdSympSpace K r).V = 2 * r :=
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.finrank_standard

theorem exists_injective_isom_statedSp (S : FormSpace K K) (hS : IsSymplecticSpace S) {n : ℕ}
    (hdim : finrank K S.V = 2 * n) : ∃ ψ : S.isom →* StatedSp n K, Function.Injective ψ := by
  obtain ⟨B, hBF, hBa, hBn⟩ := hS
  obtain ⟨ι⟩ := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_form_isometry B
    (CFSG.LocalAnalysis.ComponentInitial.pairedSympForm K n) hBa hBn
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.pairedSympForm_isAlt
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.pairedSympForm_nondegenerate
    (by rw [hdim, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.finrank_standard])
  let e₁ : S.isom ≃* (stdSympSpace K n).isom :=
    formIsometryGroupCongr ι.toLinearEquiv fun x y => by
      rw [hBF]
      exact ι.map_app y x
  let M := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv
    (Pi.basisFun K (Fin n ⊕ Fin n))
  have hmem : ∀ g : (stdSympSpace K n).isom, M g.1 ∈ StatedSp n K := fun g => by
    rw [← CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.map_isometryGroup_eq_statedSp]
    exact Subgroup.mem_map_of_mem _ (TauCeti.BilinForm.mem_isometryGroup_iff.2 g.2)
  let ψ₀ : (stdSympSpace K n).isom →* StatedSp n K :=
    { toFun := fun g => ⟨M g.1, hmem g⟩
      map_one' := Subtype.ext (map_one M)
      map_mul' := fun g h => Subtype.ext (map_mul M g.1 h.1) }
  refine ⟨ψ₀.comp e₁.toMonoidHom, fun g h hgh => e₁.injective (Subtype.ext ?_)⟩
  exact M.injective (congrArg Subtype.val hgh)

end Spaces

section Torus

variable (K : Type) [Field K] (L : Type) [Field L] [Algebra K L]

@[expose] noncomputable def prodUnitsHom : Lˣ →* ((L × L) ≃ₗ[K] (L × L)) where
  toFun u := (DistribMulAction.toModuleAut K L u).prodCongr (DistribMulAction.toModuleAut K L u⁻¹)
  map_one' := LinearEquiv.ext fun x => by
    change ((1 : Lˣ) • x.1, (1 : Lˣ)⁻¹ • x.2) = x
    rw [inv_one, one_smul, one_smul]
  map_mul' u v := LinearEquiv.ext fun x => by
    change ((u * v) • x.1, (u * v)⁻¹ • x.2) = (u • v • x.1, u⁻¹ • v⁻¹ • x.2)
    rw [mul_inv, mul_smul, mul_smul]

theorem prodUnitsHom_apply (u : Lˣ) (x : L × L) :
    prodUnitsHom K L u x = ((u : L) * x.1, ((u⁻¹ : Lˣ) : L) * x.2) :=
  rfl

theorem prodUnitsHom_injective : Function.Injective (prodUnitsHom K L) := fun u v h => by
  have := congrArg Prod.fst (LinearEquiv.congr_fun h (1, 0))
  rw [prodUnitsHom_apply, prodUnitsHom_apply, mul_one, mul_one] at this
  exact Units.ext this

end Torus

section SymplecticTori

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

theorem exists_ne_zero_dual (L : Type) [Field L] [Algebra K L] :
    ∃ lam : L →ₗ[K] K, lam ≠ 0 := by
  obtain ⟨f, hf, -⟩ := Submodule.exists_le_ker_of_lt_top (⊥ : Submodule K L) bot_lt_top
  exact ⟨f, hf⟩

theorem eq_zero_of_forall_mul {lam : L →ₗ[K] K} (hlam : lam ≠ 0) {x : L}
    (hx : ∀ z, lam (x * z) = 0) : x = 0 := by
  by_contra h
  apply hlam
  ext t
  simpa [mul_inv_cancel_left₀ h] using hx (x⁻¹ * t)

@[expose] def hypSympForm (lam : L →ₗ[K] K) : BilinForm K (L × L) :=
  LinearMap.mk₂ K (fun v w => lam (v.1 * w.2) - lam (v.2 * w.1))
    (fun v v' w => by simp only [Prod.fst_add, Prod.snd_add, add_mul, map_add]; ring)
    (fun c v w => by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_mul_assoc, map_smul, smul_eq_mul]; ring)
    (fun v w w' => by simp only [Prod.fst_add, Prod.snd_add, mul_add, map_add]; ring)
    (fun c v w => by
      simp only [Prod.smul_fst, Prod.smul_snd, mul_smul_comm, map_smul, smul_eq_mul]; ring)

theorem hypSympForm_apply (lam : L →ₗ[K] K) (v w : L × L) :
    hypSympForm lam v w = lam (v.1 * w.2) - lam (v.2 * w.1) :=
  rfl

theorem hypSympForm_isAlt (lam : L →ₗ[K] K) : (hypSympForm lam).IsAlt := fun v => by
  rw [hypSympForm_apply, mul_comm, sub_self]

theorem hypSympForm_nondegenerate {lam : L →ₗ[K] K} (hlam : lam ≠ 0) :
    (hypSympForm lam).Nondegenerate :=
  nondegenerate_of_isAlt (hypSympForm_isAlt lam) fun v hv => Prod.ext
    (eq_zero_of_forall_mul hlam fun z => by simpa [hypSympForm_apply] using hv (0, z))
    (eq_zero_of_forall_mul hlam fun z => by simpa [hypSympForm_apply] using hv (z, 0))

theorem prodUnitsHom_mem_isometry (lam : L →ₗ[K] K) (u : Lˣ) (v w : L × L) :
    hypSympForm lam (prodUnitsHom K L u v) (prodUnitsHom K L u w) = hypSympForm lam v w := by
  simp only [hypSympForm_apply, prodUnitsHom_apply]
  congr 2 <;> rw [mul_mul_mul_comm, ← Units.val_mul] <;> simp

@[expose] def twistSympForm (lam : L →ₗ[K] K) (σ : L ≃ₐ[K] L) : BilinForm K L :=
  LinearMap.mk₂ K (fun x y => lam (x * σ y))
    (fun x x' y => by rw [add_mul, map_add])
    (fun c x y => by rw [smul_mul_assoc, map_smul])
    (fun x y y' => by rw [map_add, mul_add, map_add])
    (fun c x y => by rw [map_smul, mul_smul_comm, map_smul])

theorem twistSympForm_apply (lam : L →ₗ[K] K) (σ : L ≃ₐ[K] L) (x y : L) :
    twistSympForm lam σ x y = lam (x * σ y) :=
  rfl

theorem twistSympForm_isAlt {lam : L →ₗ[K] K} {σ : L ≃ₐ[K] L} (hσ : ∀ x, σ (σ x) = x)
    (hlam : ∀ z, σ z = z → lam z = 0) : (twistSympForm lam σ).IsAlt := fun x => by
  rw [twistSympForm_apply]
  refine hlam _ ?_
  rw [map_mul, hσ, mul_comm]

theorem twistSympForm_nondegenerate {lam : L →ₗ[K] K} (hlam : lam ≠ 0) {σ : L ≃ₐ[K] L}
    (hσ : ∀ x, σ (σ x) = x) (halt : (twistSympForm lam σ).IsAlt) :
    (twistSympForm lam σ).Nondegenerate :=
  nondegenerate_of_isAlt halt fun x hx => eq_zero_of_forall_mul hlam fun z => by
    have := hx (σ z)
    rwa [twistSympForm_apply, hσ] at this

theorem toModuleAut_mem_twist (lam : L →ₗ[K] K) (σ : L ≃ₐ[K] L) {u : Lˣ}
    (hu : (u : L) * σ u = 1) (x y : L) :
    twistSympForm lam σ (DistribMulAction.toModuleAut K L u x)
      (DistribMulAction.toModuleAut K L u y) = twistSympForm lam σ x y := by
  change lam (u • x * σ (u • y)) = lam (x * σ y)
  rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, map_mul σ,
    mul_mul_mul_comm, hu, one_mul]

end SymplecticTori

section Frobenius

variable {K : Type} [Field K] [Fintype K] {L : Type} [Field L] [Algebra K L] [Finite L]

theorem pow_natCard_eq (x : L) : x ^ Nat.card L = x := by
  have := Fintype.ofFinite L
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

theorem natCard_eq_pow_finrank : Nat.card L = Fintype.card K ^ finrank K L := by
  have := Fintype.ofFinite L
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K)]

theorem frob_pow_apply (f : ℕ) (x : L) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ f) x = x ^ Fintype.card K ^ f := by
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]

theorem frob_pow_frob_pow {f : ℕ} (hf : finrank K L = 2 * f) (x : L) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ f)
      ((FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ f) x) = x := by
  rw [frob_pow_apply, frob_pow_apply, ← pow_mul, ← pow_add, ← two_mul, ← hf,
    ← natCard_eq_pow_finrank, pow_natCard_eq]

theorem exists_pow_ne_self {f : ℕ} (hf : 0 < f) (hfL : f < finrank K L) :
    ∃ x : L, x ^ Fintype.card K ^ f ≠ x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Lˣ)
  refine ⟨g, fun h => ?_⟩
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have h1 : g ^ (Fintype.card K ^ f - 1) = 1 := by
    have hpos : 1 ≤ Fintype.card K ^ f := Nat.one_le_pow _ _ (by omega)
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have hg0 : (g : L) ≠ 0 := g.ne_zero
    have : (g : L) ^ (Fintype.card K ^ f - 1) * g = 1 * g := by
      rw [← pow_succ, Nat.sub_add_cancel hpos, one_mul, h]
    exact mul_right_cancel₀ hg0 this
  have h2 := Nat.le_of_dvd (Nat.sub_pos_of_lt (Nat.one_lt_pow hf.ne' hq))
    (orderOf_dvd_iff_pow_eq_one.2 h1)
  rw [hg, Nat.card_units, natCard_eq_pow_finrank (K := K)] at h2
  have h3 : Fintype.card K ^ finrank K L ≤ Fintype.card K ^ f := by
    have := Nat.one_le_pow f _ (by omega : 0 < Fintype.card K)
    omega
  exact absurd ((Nat.pow_le_pow_iff_right hq).1 h3) (by omega)

end Frobenius

theorem natCard_statedSp_cast (K : Type) [Field K] [Finite K] (n : ℕ) :
    (Nat.card (StatedSp n K) : ℤ) =
      (Nat.card K : ℤ) ^ (n ^ 2) * ∏ j ∈ Icc 1 n, (((Nat.card K : ℤ) ^ 2) ^ j - 1) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_prod]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Nat.cast_sub (Nat.one_le_pow _ _ Nat.card_pos), Nat.cast_pow, Nat.cast_one, ← pow_mul]

theorem factorization_card_statedSp {p : ℕ} [hp : Fact p.Prime] (hp1 : Odd p) (K : Type)
    [Field K] [Fintype K] (hpK : ¬ p ∣ Fintype.card K) (n : ℕ) :
    (Nat.card (StatedSp n K)).factorization p =
      padicValNat p (Fintype.card K ^ orderOf (Fintype.card K : ZMod p) - 1) *
          ((if Even (orderOf (Fintype.card K : ZMod p)) then 2 * n else n) /
            orderOf (Fintype.card K : ZMod p)) +
        padicValNat p ((if Even (orderOf (Fintype.card K : ZMod p)) then 2 * n else n) /
            orderOf (Fintype.card K : ZMod p)).factorial := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hpZ := Nat.prime_iff_prime_int.mp hp.out
  have hc : ¬ (p : ℤ) ∣ (Fintype.card K : ℤ) ^ 2 := fun h =>
    hpK (by exact_mod_cast hpZ.dvd_of_dvd_pow h)
  have hc2 : 2 ≤ |(Fintype.card K : ℤ) ^ 2| := by
    rw [abs_of_nonneg (by positivity)]
    have : (2 : ℤ) ≤ Fintype.card K := by exact_mod_cast hq
    nlinarith
  have hu : ¬ (p : ℤ) ∣ (Fintype.card K : ℤ) ^ (n ^ 2) := fun h =>
    hpK (by exact_mod_cast hpZ.dvd_of_dvd_pow h)
  rw [factorization_eq_of_cast_eq_mul_prod hp1 hc hc2
    (by rw [natCard_statedSp_cast, Nat.card_eq_fintype_card]) hu,
    padicValInt_sq_pow_ordMod_sub_one hp1, ordMod_sq, ordMod_natCast,
    padicValInt_natCast_pow_sub_one p hq.le]
  split_ifs with he
  · obtain ⟨f, hf⟩ := he
    have hf' : orderOf (Fintype.card K : ZMod p) = 2 * f := by omega
    rw [hf', Nat.mul_div_cancel_left f two_pos, Nat.mul_div_mul_left n f two_pos]
  · rfl

theorem exists_injective_sigmaModel_Sp {p : ℕ} [hp : Fact p.Prime] (K : Type) [Field K]
    [Fintype K] (hpK : ¬ p ∣ Fintype.card K) (n : ℕ) :
    ∃ φ : sigmaModel p (orderOf (Fintype.card K : ZMod p))
        (padicValNat p (Fintype.card K ^ orderOf (Fintype.card K : ZMod p) - 1))
        (if Even (orderOf (Fintype.card K : ZMod p)) then 2 * n else n) →* StatedSp n K,
      Function.Injective φ := by
  set q := Fintype.card K with hqdef
  set e := orderOf (q : ZMod p) with hedef
  set a := padicValNat p (q ^ e - 1) with hadef
  have hq : 1 < q := Fintype.one_lt_card
  have he : 0 < e := by
    rw [hedef, ← ordMod_natCast]
    exact ordMod_pos (c := (q : ℤ)) (by exact_mod_cast hpK)
  have : NeZero e := ⟨he.ne'⟩
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  let L := FiniteField.Extension K (ringChar K) e
  have hLcard : Nat.card L = q ^ e := by
    rw [FiniteField.natCard_extension, Nat.card_eq_fintype_card]
  have hLdim : finrank K L = e := FiniteField.finrank_extension K _ e
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq (L := L) (d := p ^ a)
    (by rw [hLcard]; exact pow_padicValNat_dvd)
  obtain ⟨lam, hlam⟩ := exists_ne_zero_dual (K := K) L
  by_cases hev : Even e
  ·
    rw [ite_eq_left hev]
    obtain ⟨f, hf⟩ := hev
    have hfe : e = 2 * f := by omega
    have hf0 : 0 < f := by omega
    have hnd : ¬ p ∣ q ^ f - 1 := by
      intro h
      have h' : (p : ℤ) ∣ (q : ℤ) ^ f - 1 := by
        have := Int.natCast_dvd_natCast.2 h
        rwa [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one] at this
      rw [dvd_pow_sub_one_iff, ordMod_natCast, ← hedef] at h'
      exact absurd (Nat.le_of_dvd hf0 h') (by omega)
    have hdvd : p ^ a ∣ q ^ f + 1 := by
      have hcop : (p ^ a).Coprime (q ^ f - 1) :=
        Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hnd)
      refine hcop.dvd_of_dvd_mul_left ?_
      have hfac : (q ^ f - 1) * (q ^ f + 1) = q ^ e - 1 := by
        have h1 : 1 ≤ q ^ f := Nat.one_le_pow _ _ (by omega)
        have h2 : 1 ≤ q ^ e := Nat.one_le_pow _ _ (by omega)
        zify [h1, h2]
        rw [hfe, pow_mul']
        ring
      rw [hfac]
      exact pow_padicValNat_dvd
    let σ : L ≃ₐ[K] L := FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ f
    have hσσ : ∀ x, σ (σ x) = x := frob_pow_frob_pow (by rw [hLdim, hfe])
    have hζσ : (ζ : L) * σ ζ = 1 := by
      rw [frob_pow_apply, ← pow_succ']
      have : ζ ^ (q ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ hdvd)
      have h' := congrArg Units.val this
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at h'
    let Fix : Submodule K L := LinearMap.ker ((σ : L →ₗ[K] L) - LinearMap.id)
    have hFix : Fix < ⊤ := by
      obtain ⟨x, hx⟩ := exists_pow_ne_self (K := K) (L := L) hf0 (by rw [hLdim]; omega)
      refine lt_top_iff_ne_top.2 fun htop => hx ?_
      have hmem : x ∈ Fix := htop ▸ Submodule.mem_top
      have : σ x - x = 0 := hmem
      rw [← frob_pow_apply]
      exact sub_eq_zero.1 this
    obtain ⟨mu, hmu, hFixmu⟩ := Submodule.exists_le_ker_of_lt_top Fix hFix
    have hmu0 : ∀ z, σ z = z → mu z = 0 := fun z hz =>
      hFixmu (show σ z - z = 0 from sub_eq_zero.2 hz)
    have halt := twistSympForm_isAlt hσσ hmu0
    let S₀ : FormSpace K K := ⟨L, fun x y => twistSympForm mu σ x y⟩
    have hS₀ : IsSymplecticSpace S₀ :=
      ⟨twistSympForm mu σ, fun _ _ => rfl, halt, twistSympForm_nondegenerate hmu hσσ halt⟩
    have hmem : DistribMulAction.toModuleAut K L ζ ∈ S₀.isom := fun x y =>
      toModuleAut_mem_twist mu σ hζσ x y
    obtain ⟨ρ, hρ⟩ := exists_injective_hom_of_orderOf_eq hmem (by rw [orderOf_toModuleAut, hζ])
    obtain ⟨S, hS, hSdim, φ, hφ⟩ := exists_sigmaModel_rep p IsSymplecticSpace
      (fun ι _ S hS => isSymplecticSpace_pi S hS) S₀ hS₀ (inferInstanceAs (Nontrivial L))
      ρ hρ e (2 * n)
    let T := stdSympSpace K ((2 * n - e * (2 * n / e)) / 2)
    obtain ⟨ψ, hψ⟩ := exists_rep_prod S T φ hφ
    have hdim : finrank K (S.prod T).V = 2 * n := by
      rw [FormSpace.finrank_prod, hSdim, finrank_stdSympSpace]
      change finrank K L * (2 * n / e) + _ = _
      rw [hLdim]
      have h1 := Nat.mul_div_le (2 * n) e
      have h2 : 2 ∣ e * (2 * n / e) := Dvd.dvd.mul_right ⟨f, hfe⟩ _
      omega
    obtain ⟨χ, hχ⟩ := exists_injective_isom_statedSp (S.prod T)
      (isSymplecticSpace_prod S T hS (isSymplecticSpace_stdSympSpace _)) hdim
    exact ⟨χ.comp ψ, hχ.comp hψ⟩
  ·
    rw [ite_eq_right hev]
    let S₀ : FormSpace K K := ⟨L × L, fun v w => hypSympForm lam v w⟩
    have hS₀ : IsSymplecticSpace S₀ :=
      ⟨hypSympForm lam, fun _ _ => rfl, hypSympForm_isAlt lam, hypSympForm_nondegenerate hlam⟩
    have hmem : prodUnitsHom K L ζ ∈ S₀.isom := fun v w => prodUnitsHom_mem_isometry lam ζ v w
    obtain ⟨ρ, hρ⟩ := exists_injective_hom_of_orderOf_eq hmem
      (by rw [orderOf_injective _ (prodUnitsHom_injective K L), hζ])
    obtain ⟨S, hS, hSdim, φ, hφ⟩ := exists_sigmaModel_rep p IsSymplecticSpace
      (fun ι _ S hS => isSymplecticSpace_pi S hS) S₀ hS₀ (inferInstanceAs (Nontrivial (L × L)))
      ρ hρ e n
    let T := stdSympSpace K (n - e * (n / e))
    obtain ⟨ψ, hψ⟩ := exists_rep_prod S T φ hφ
    have hdim : finrank K (S.prod T).V = 2 * n := by
      rw [FormSpace.finrank_prod, hSdim, finrank_stdSympSpace]
      change finrank K (L × L) * (n / e) + _ = _
      rw [Module.finrank_prod, hLdim]
      have h1 := Nat.mul_div_le n e
      zify [h1]
      ring
    obtain ⟨χ, hχ⟩ := exists_injective_isom_statedSp (S.prod T)
      (isSymplecticSpace_prod S T hS (isSymplecticSpace_stdSympSpace _)) hdim
    exact ⟨χ.comp ψ, hχ.comp hψ⟩

theorem sylow_Sp {p : ℕ} [hp : Fact p.Prime] (hp1 : Odd p) (K : Type) [Field K] [Fintype K]
    (hpK : ¬ p ∣ Fintype.card K) (n : ℕ) (P : Sylow p (StatedSp n K)) :
    Nonempty (P ≃* sigmaModel p (orderOf (Fintype.card K : ZMod p))
      (padicValNat p (Fintype.card K ^ orderOf (Fintype.card K : ZMod p) - 1))
      (if Even (orderOf (Fintype.card K : ZMod p)) then 2 * n else n)) := by
  obtain ⟨φ, hφ⟩ := exists_injective_sigmaModel_Sp K hpK n
  exact nonempty_sylow_mulEquiv_sigmaModel φ hφ (factorization_card_statedSp hp1 K hpK n) P

theorem sylow_Sp_mulEquiv_sylow_GL {p : ℕ} [hp : Fact p.Prime] (hp1 : Odd p) (K : Type)
    [Field K] [Fintype K] (hpK : ¬ p ∣ Fintype.card K) (n : ℕ) (P : Sylow p (StatedSp n K))
    (P' : Sylow p (GL (Fin (if Even (orderOf (Fintype.card K : ZMod p)) then 2 * n else n)) K)) :
    Nonempty (P ≃* P') := by
  obtain ⟨e₁⟩ := sylow_Sp hp1 K hpK n P
  obtain ⟨e₂⟩ := sylow_GL hp1 K hpK _ P'
  exact ⟨e₁.trans e₂.symm⟩

end CFSG.GroupTheory.WeirSylow
