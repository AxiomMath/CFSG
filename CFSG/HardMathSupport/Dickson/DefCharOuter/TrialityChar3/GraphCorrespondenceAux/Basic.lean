module

public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientDescent
public import CFSG.LieType.Chevalley.ChevalleyLargeRootCentralizerFaithful
public import CFSG.LieType.Chevalley.OddTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.RankThree.PartOne.KGD.D4T36Core
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.GraphCorrespondence

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Field

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K K₃ : Type} [Field K] [Finite K] [Field K₃] [Algebra K K₃]

theorem frobenius_algebraMap (hK : Nat.card K = ℓ ^ f) (Fr : K₃ ≃+* K₃)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (c : K) : Fr (algebraMap K K₃ c) = algebraMap K K₃ c := by
  have : Fintype K := Fintype.ofFinite K
  rw [hFr, ← map_pow, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

@[expose] noncomputable def fixedEquiv (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) [Finite K₃]
    (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    K ≃+* fixSubfield Fr := by
  have hcard := CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube (Fact.out : ℓ.Prime) hf hK₃ Fr hFr
  let φ : K →+* fixSubfield Fr := (algebraMap K K₃).codRestrict (fixSubfield Fr)
    fun c => (mem_fixSubfield Fr).2 (frobenius_algebraMap hK Fr hFr c)
  have hφ : Function.Injective φ := fun a b h => (algebraMap K K₃).injective
    (congrArg Subtype.val h)
  have : Finite (fixSubfield Fr) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact (pow_pos (Fact.out : ℓ.Prime).pos f).ne')
  exact RingEquiv.ofBijective φ (hφ.bijective_of_nat_card_le (by rw [hcard, hK]))

theorem fixedEquiv_apply (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) [Finite K₃]
    (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (c : K) :
    ((fixedEquiv hf hK hK₃ Fr hFr c : fixSubfield Fr) : K₃) = algebraMap K K₃ c := rfl

theorem exists_ext (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) :
    ∃ (K₃ : Type) (_ : Field K₃) (_ : Finite K₃) (_ : CharP K₃ ℓ) (_ : Algebra K K₃),
      Nat.card K₃ = (ℓ ^ f) ^ 3 ∧ ∃ Fr : K₃ ≃+* K₃, ∀ c, Fr c = c ^ (ℓ ^ f) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  let _ : Algebra (ZMod ℓ) K := ZMod.algebra K ℓ
  have hfin : Module.finrank (ZMod ℓ) K = f := by
    have : Fintype K := Fintype.ofFinite K
    have h1 := Module.card_eq_pow_finrank (K := ZMod ℓ) (V := K)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK] at h1
    exact (Nat.pow_right_injective hℓ.two_le h1).symm
  have hf3 : f * 3 ≠ 0 := by omega
  have hdvd : Module.finrank (ZMod ℓ) K ∣ Module.finrank (ZMod ℓ) (GaloisField ℓ (f * 3)) := by
    rw [hfin, GaloisField.finrank ℓ hf3]
    exact Dvd.intro 3 rfl
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdvd
  let _ : Algebra K (GaloisField ℓ (f * 3)) := φ.toRingHom.toAlgebra
  refine ⟨GaloisField ℓ (f * 3), inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [GaloisField.card ℓ (f * 3) hf3, pow_mul]
  · have hinj : Function.Injective (iterateFrobenius (GaloisField ℓ (f * 3)) ℓ f) :=
      (iterateFrobenius (GaloisField ℓ (f * 3)) ℓ f).injective
    refine ⟨RingEquiv.ofBijective _ ⟨hinj, Finite.surjective_of_injective hinj⟩, fun c => ?_⟩
    exact iterateFrobenius_def ℓ f c

end Field

section Group

variable {G : Type*} [Group G]

theorem commute_of_conj_eq (A B W : G) (h : A * W * A⁻¹ = B * W * B⁻¹) :
    A⁻¹ * B * W = W * (A⁻¹ * B) := by
  calc A⁻¹ * B * W = A⁻¹ * (B * W * B⁻¹) * B := by group
    _ = A⁻¹ * (A * W * A⁻¹) * B := by rw [h]
    _ = W * (A⁻¹ * B) := by group

theorem twisted_fixed (P a b c x : G) (hx : x = a⁻¹ * (P * b * P⁻¹))
    (hF : b⁻¹ * (P * c * P⁻¹) = x) : P * (b * c⁻¹) * P⁻¹ = a * b⁻¹ := by
  have h1 : P * c * P⁻¹ = b * (a⁻¹ * (P * b * P⁻¹)) := by
    rw [← hx, ← hF]; group
  calc P * (b * c⁻¹) * P⁻¹ = (P * b * P⁻¹) * (P * c * P⁻¹)⁻¹ := by group
    _ = (P * b * P⁻¹) * (b * (a⁻¹ * (P * b * P⁻¹)))⁻¹ := by rw [h1]
    _ = a * b⁻¹ := by group

end Group

section Matrix

set_option linter.unusedSectionVars false


theorem baseChange_normalForm {K : Type} [Field K] (L : Type) [Field L] (ι : K →+* L)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (T : K ≃+* K) (ε : ℕ)
    (u : adjointGroup Tag.D4 K) :
    baseChangeGL ι ((MulAut.conj g * (exactNormalAut Tag.D4 K a T 0 * d4Graph K ε)) u :
        ModGL Tag.D4 K) =
      baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) *
        baseChangeGL ι (Subtype.val (twistedEntrywiseAut TwistTag.D4 (ε : ℤ) T u) :
          ModGL Tag.D4 K) *
          (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a))⁻¹ := by
  have hP : Units.map (entrywiseHom (τ := Tag.D4) T.toRingHom) (d4P K ^ ε) = d4P K ^ ε := by
    rw [map_pow]
    exact congrArg (· ^ ε) (units_map_entrywiseHom_diagramMap (t := TwistTag.D4) T.toRingHom)
  have h1 : (Subtype.val (twistedEntrywiseAut TwistTag.D4 (ε : ℤ) T u) : ModGL Tag.D4 K) =
      d4P K ^ ε * Units.map (entrywiseHom T.toRingHom) (u : ModGL Tag.D4 K) * (d4P K ^ ε)⁻¹ := by
    have h := coe_twistedEntrywiseAut TwistTag.D4 (ε : ℤ) T u
    rw [zpow_natCast] at h
    exact h
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_exactNormalAut, exactQ_zero, coe_d4Graph, h1]
  simp only [map_mul, map_inv, hP, mul_one, inv_one]
  group

theorem baseChangeGL_d4P {K L : Type} [Field K] [Field L] (ι : K →+* L) :
    baseChangeGL ι (d4P K) = d4P L := baseChangeGL_diagramMap ι TwistTag.D4

theorem cube_expand {G : Type*} [Group G] (x Q : G) :
    (x * Q) ^ 3 = x * (Q * x * Q⁻¹) * (Q * (Q * x * Q⁻¹) * Q⁻¹) * Q ^ 3 := by
  rw [pow_three']
  group

theorem cube_mem {F : Type} [Field F] (ε : ℕ) {x : ModGL Tag.D4 F}
    (hx : x ∈ adjointGroup Tag.D4 F) :
    (x * d4P F ^ ε) ^ 3 ∈ adjointGroup Tag.D4 F := by
  have hconj : ∀ y ∈ adjointGroup Tag.D4 F, d4P F ^ ε * y *
      (d4P F ^ ε)⁻¹ ∈ adjointGroup Tag.D4 F := fun y hy =>
    conj_mem_adjointGroup_of_map_eq (map_conj_pow_of_map_conj (d4P F)
      (map_conj_diagramMap TwistTag.D4 F (Or.inl rfl)) ε) y hy
  have hP3 : (d4P F ^ ε) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, show d4P F ^ 3 = 1 from
      diagramMap_pow_order TwistTag.D4 F, one_pow]
  rw [cube_expand, hP3, mul_one]
  exact mul_mem (mul_mem hx (hconj _ hx)) (hconj _ (hconj _ hx))

theorem cube_eq_one {K L : Type} [Field K] [Finite K] [Field L] (ι : K →+* L)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ)
    (hx : baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) ∈ adjointGroup Tag.D4 L)
    (hM : ∀ u : adjointGroup Tag.D4 K, baseChangeGL ι (α u : ModGL Tag.D4 K) =
      (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) * d4P L ^ ε) *
        baseChangeGL ι (u : ModGL Tag.D4 K) *
          (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) *
            d4P L ^ ε)⁻¹) :
    (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) *
      d4P L ^ ε) ^ 3 = 1 := by
  classical
  set M := baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) *
    d4P L ^ ε with hMdef
  have hcomm : ∀ w ∈ (adjointGroup Tag.D4 K).map (baseChangeGL ι), M ^ 3 * w = w * M ^ 3 := by
    rintro _ ⟨w', hw', rfl⟩
    set u : adjointGroup Tag.D4 K := ⟨w', hw'⟩ with hu
    have h3 : α (α (α u)) = u := by
      have : (α ^ 3) u = u := by rw [hα3]; rfl
      rwa [pow_three, MulAut.mul_apply, MulAut.mul_apply] at this
    have e' : M * (M * (M * baseChangeGL ι w' * M⁻¹) * M⁻¹) * M⁻¹ = baseChangeGL ι w' := by
      have := congrArg (fun y : adjointGroup Tag.D4 K => baseChangeGL ι (y : ModGL Tag.D4 K)) h3
      rw [hM (α (α u)), hM (α u), hM u] at this
      exact this
    have e'' : (M * M * M) * baseChangeGL ι w' * (M * M * M)⁻¹ = baseChangeGL ι w' := by
      calc (M * M * M) * baseChangeGL ι w' * (M * M * M)⁻¹ =
          M * (M * (M * baseChangeGL ι w' * M⁻¹) * M⁻¹) * M⁻¹ := by group
        _ = baseChangeGL ι w' := e'
    rw [pow_three']
    exact mul_inv_eq_iff_eq_mul.mp e''
  have hNad : M ^ 3 ∈ adjointGroup Tag.D4 L := cube_mem ε hx
  rcases lt_or_ge 2 (Nat.card K) with h2 | h2
  · obtain ⟨-, -, hfaith, -⟩ := Chevalley_large_finite_root_centralizer_faithfulness Tag.D4 K
      (by simpa using h2) L ι
    exact hfaith _ hNad hcomm
  ·
    have hK2 : Nat.card K = 2 := by
      have := Finite.one_lt_card (α := K)
      omega
    have : Fintype K := Fintype.ofFinite K
    have hu1 : ∀ u : Kˣ, u = 1 := by
      have h1 : Fintype.card Kˣ = 1 := by
        rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK2]
      intro u
      exact Fintype.card_le_one_iff.mp (le_of_eq h1) u 1
    have ha : a = 1 := funext fun i => hu1 (a i)
    rw [ha, rootDiagUnit_one, mul_one] at hMdef hx
    set n : ModGL Tag.D4 K := ((g : ModGL Tag.D4 K) * d4P K ^ ε) ^ 3 with hn
    have hMn : M ^ 3 = baseChangeGL ι n := by
      rw [hMdef, hn, map_pow, map_mul, map_pow, baseChangeGL_d4P]
    have hnad : n ∈ adjointGroup Tag.D4 K := cube_mem ε g.2
    have hcen : (⟨n, hnad⟩ : adjointGroup Tag.D4 K) ∈ Subgroup.center (adjointGroup Tag.D4 K) := by
      rw [Subgroup.mem_center_iff]
      intro u
      have := hcomm (baseChangeGL ι (u : ModGL Tag.D4 K)) ⟨u, u.2, rfl⟩
      rw [hMn, ← map_mul, ← map_mul] at this
      exact Subtype.ext (baseChangeGL_injective ι (by simpa using this.symm))
    rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hcen
    have hn1 : n = 1 := congrArg Subtype.val hcen
    rw [hMn, hn1, map_one]

variable {K : Type} [Field K]

theorem coe_normalForm (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ)
    (u : adjointGroup Tag.D4 K) :
    ((MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) u : ModGL Tag.D4 K) =
      ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε) * (u : ModGL Tag.D4 K) *
        ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε)⁻¹ := by
  have h1 : ∀ w : ModGL Tag.D4 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) w = w := by
    intro w
    have e1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
    rw [e1]
    exact Units.ext (entrywise_id (R := K) _)
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_exactNormalAut, exactQ_zero, coe_d4Graph, h1]
  group

theorem baseChange_normalForm_one {L : Type} [Field L] (ι : K →+* L)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ) (u : adjointGroup Tag.D4 K) :
    baseChangeGL ι ((MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) u :
        ModGL Tag.D4 K) =
      (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) * d4P L ^ ε) *
        baseChangeGL ι (u : ModGL Tag.D4 K) *
          (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) * d4P L ^ ε)⁻¹ := by
  rw [coe_normalForm]
  simp only [map_mul, map_inv, map_pow, baseChangeGL_d4P]

theorem inv_normalForm (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) :
    ∃ (g' : adjointGroup Tag.D4 K) (a' : Fin Tag.D4.rank → Kˣ),
      (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 2))⁻¹ =
        MulAut.conj g' * (exactNormalAut Tag.D4 K a' 1 0 * d4Graph K 1) := by
  set a' : Fin Tag.D4.rank → Kˣ := fun i => (a (d4Rho.symm i))⁻¹ with ha'
  set g' : adjointGroup Tag.D4 K := exactNormalAut Tag.D4 K a' 1 0 (d4Graph K 1 g⁻¹) with hg'
  refine ⟨g', a', ?_⟩
  have hP3 : d4P K ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 K
  have hd : rootDiagUnit Tag.D4 a' = d4P K * (rootDiagUnit Tag.D4 a)⁻¹ * (d4P K)⁻¹ := by
    have hinv : rootDiagUnit Tag.D4 a⁻¹ = (rootDiagUnit Tag.D4 a)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← rootDiagUnit_mul, inv_mul_cancel, rootDiagUnit_one])
    have h : d4P K * rootDiagUnit Tag.D4 a⁻¹ = rootDiagUnit Tag.D4 a' * d4P K :=
      diagramMap_mul_rootDiagUnit (t := TwistTag.D4) (K := K) a⁻¹
    rw [hinv] at h
    calc rootDiagUnit Tag.D4 a' = (rootDiagUnit Tag.D4 a' * d4P K) * (d4P K)⁻¹ := by group
      _ = _ := by rw [← h]
  have hg'c : (g' : ModGL Tag.D4 K) =
      rootDiagUnit Tag.D4 a' * (d4P K * (g : ModGL Tag.D4 K)⁻¹ * (d4P K)⁻¹) *
        (rootDiagUnit Tag.D4 a')⁻¹ := by
    have h1 : ∀ w : ModGL Tag.D4 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) w = w := by
      intro w
      have e1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
      rw [e1]
      exact Units.ext (entrywise_id (R := K) _)
    rw [hg', coe_exactNormalAut, exactQ_zero, coe_d4Graph, h1]
    simp only [Subgroup.coe_inv, pow_one, inv_one, mul_one]
  have hprod : ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ 2) *
      ((g' : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a' * d4P K ^ 1) = 1 := by
    rw [hg'c, hd]
    calc _ = (g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ 3 *
          (rootDiagUnit Tag.D4 a)⁻¹ * (g : ModGL Tag.D4 K)⁻¹ := by group
      _ = 1 := by rw [hP3]; group
  refine inv_eq_of_mul_eq_one_right (MulEquiv.ext fun u => Subtype.ext ?_)
  rw [MulAut.mul_apply, coe_normalForm, coe_normalForm, MulAut.one_apply]
  have hinv : ((g' : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a' * d4P K ^ 1) =
      ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ 2)⁻¹ :=
    eq_inv_of_mul_eq_one_right hprod
  rw [hinv]
  group

end Matrix

section FieldActor

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K]

theorem sigma_ne_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) : σ ≠ 1 := by
  intro h
  have hc := CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube hp hf hK σ hσ
  have htop : fixSubfield σ = ⊤ := by
    ext c
    simp [h]
  rw [htop] at hc
  have hc' : Nat.card K = p ^ f := by
    rw [← hc]
    exact (Nat.card_congr Subfield.topEquiv.toEquiv).symm
  have hp1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
  rw [hK] at hc'
  nlinarith [hp1, pow_pos (lt_trans Nat.zero_lt_one hp1) 2]

theorem sigma_cube {p f : ℕ} (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) : σ ^ 3 = 1 := by
  ext c
  exact ringEquiv_cube_apply_eq hK hσ c

theorem fieldActor_cube {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1) :
    fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := by
  have h1 : fieldActor (t := TwistTag.D4) σ (σ ^ 3) = fieldActor σ σ ^ 3 :=
    map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3
  rw [← h1, hσ3, fieldActor_one]

theorem fieldActor_not_inner {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    fieldActor (t := TwistTag.D4) σ σ ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  intro hin
  have h1 : Θ (fieldActor (t := TwistTag.D4) σ σ) = σ :=
    hΘ _ 1 σ (by rw [map_one, one_mul])
  have h2 : fieldActor (t := TwistTag.D4) σ σ ∈ Θ.ker := by rw [hker]; exact hin
  rw [MonoidHom.mem_ker] at h2
  exact sigma_ne_one hp hf hK σ hσ (h1.symm.trans h2)

end FieldActor

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.GraphCorrespondence
