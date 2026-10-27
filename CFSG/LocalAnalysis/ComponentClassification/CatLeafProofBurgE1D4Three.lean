module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1D4Conj
public import CFSG.ClassicalInvolution.AschTight.S19FChartD4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1Residue

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open scoped MatrixGroups

theorem not_forall_pow_eq_self_of_card_eq_pow_three {K : Type*} [Field K] [Finite K] {q : ℕ}
    (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3) : ¬ ∀ c : K, c ^ q = c := by
  intro h
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf γ = q ^ 3 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_units, hK]
  have h1 : γ ^ (q - 1) = 1 := by
    have h2 : γ ^ q = γ := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h γ)
    have h3 : γ ^ q = γ ^ (q - 1) * γ := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [h3] at h2
    exact mul_eq_right.1 h2
  have h4 := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h1)
  rw [hord] at h4
  have h5 : q < q ^ 3 := by
    calc q = q ^ 1 := (pow_one q).symm
      _ < q ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

variable {K : Type} [Field K] [Finite K]

theorem not_fixes_fixedSubgroup_conj_aShort
    {q : ℕ} (σ : K ≃+* K) (hD : D4Data K σ.toRingHom q)
    (t₀ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (ht₀ : (t₀ : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag (aShortTD4 K))
    (δ : K ≃+* K) (hδ : δ = σ ∨ δ = σ⁻¹) :
    ¬ ∀ x ∈ fixedSubgroup (MulAut.conj t₀),
      (MulAut.conj g * fieldActor (t := .D4) σ δ) x = x := by
  intro hfix
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := hD.sigma3
  have hodd : Odd (Nat.card K) := by
    rw [hD.card]
    exact hD.odd.pow
  have hK2 : ringChar K ≠ 2 := CFSG.RankThree.PartOne.ringChar_ne_two_of_odd_card hodd
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  let ι : twistedGroup σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (MonoidHom.ofInjective (twistedIncl_injective σ.toRingHom)).trans
      (MulEquiv.subgroupCongr hD.range)
  have hι : ∀ x, (ι x : ModGL TwistTag.D4.tag K) = twistedIncl σ.toRingHom x := fun _ => rfl
  have htι : ι (slShort σ.toRingHom hσ3 (-1)) = t₀ :=
    Subtype.ext (by rw [hι, twistedIncl_slShort_neg_one hσ3, ht₀])
  have hδι : ∀ A : SL(2, K), fieldActor (t := .D4) σ δ (ι (slShort σ.toRingHom hσ3 A)) =
      ι (slShort σ.toRingHom hσ3 (Matrix.SpecialLinearGroup.map δ.toRingHom A)) := fun A =>
    Subtype.ext (by
      rw [coe_fieldActor, hι, hι]
      exact CFSG.ClassicalInvolution.Disconnected.AschTight.S19F.slShort_entrywise hσ3 δ
        (ringEquiv_comm_of_finite σ δ) A)
  have hmap1 : Matrix.SpecialLinearGroup.map δ.toRingHom (-1 : SL(2, K)) = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_neg]
  have hmem : ∀ A : SL(2, K), ι (slShort σ.toRingHom hσ3 A) ∈ fixedSubgroup (MulAut.conj t₀) := by
    intro A
    change t₀ * ι (slShort σ.toRingHom hσ3 A) * t₀⁻¹ = ι (slShort σ.toRingHom hσ3 A)
    rw [← htι, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
    congr 2
    simp
  obtain ⟨g', rfl⟩ := ι.surjective g
  have hg't : g' * slShort σ.toRingHom hσ3 (-1) = slShort σ.toRingHom hσ3 (-1) * g' := by
    have h1 := hfix t₀ (by change t₀ * t₀ * t₀⁻¹ = t₀; group)
    rw [MulAut.mul_apply, MulAut.conj_apply, ← htι, hδι, hmap1, ← map_inv, ← map_mul,
      ← map_mul] at h1
    have h3 := ι.injective h1
    calc g' * slShort σ.toRingHom hσ3 (-1) =
        g' * slShort σ.toRingHom hσ3 (-1) * g'⁻¹ * g' := by group
      _ = slShort σ.toRingHom hσ3 (-1) * g' := by rw [h3]
  obtain ⟨D, hD'⟩ := linAct_of_centralizes_short hσ3 hD.neg_one h2 hD.hC₀ hD.hgF hg't
  have key : ∀ A : SL(2, K), glConjSL D (Matrix.SpecialLinearGroup.map δ.toRingHom A) = A := by
    intro A
    have h1 := hfix _ (hmem A)
    rw [MulAut.mul_apply, MulAut.conj_apply, hδι, ← map_inv, ← map_mul, ← map_mul] at h1
    have h3 := ι.injective h1
    rw [hD'] at h3
    exact slShort_injective hσ3 h3
  have hδ1 : δ = 1 := by
    refine RingEquiv.ext fun c => ?_
    let A : SL(2, K) := ⟨!![c, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩
    have h1 := congrArg (fun B : SL(2, K) => Matrix.trace (B : Matrix (Fin 2) (Fin 2) K)) (key A)
    simp only [glConjSL_coe, Matrix.trace_units_conj, Matrix.trace_fin_two,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at h1
    simpa [A] using h1
  have hσ1 : σ = 1 := by
    rcases hδ with h | h
    · rw [← h, hδ1]
    · rw [← inv_eq_one, ← h, hδ1]
  exact not_forall_pow_eq_self_of_card_eq_pow_three hD.two_le hD.card fun c => by
    rw [← hD.frob c, hσ1]
    rfl

theorem burgE1D4OrderThreeInput_holds
    : BurgE1D4OrderThreeInput := by
  intro q K _ _ σ hq hK hσ t g δ ht hδ _ _ hfix
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  have hqd : q ∣ ringChar K ^ (n : ℕ) := by
    rw [← hn, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self q (by norm_num)
  obtain ⟨f, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hqd
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      rw [h0, pow_zero, one_pow] at hK
      have := Finite.one_lt_card (α := K)
      omega
    · exact h0
  have hp2 : ringChar K ≠ 2 := fun h2 => by
    rw [h2] at hq
    exact (Nat.not_even_iff_odd.2 hq) ((Nat.even_pow' (by omega)).2 even_two)
  have hD : D4Data K σ.toRingHom (ringChar K ^ f) := ⟨hq, hK, hσ⟩
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := hD.sigma3
  let ι : twistedGroup σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (MonoidHom.ofInjective (twistedIncl_injective σ.toRingHom)).trans
      (MulEquiv.subgroupCongr hD.range)
  have hι : ∀ x, (ι x : ModGL TwistTag.D4.tag K) = twistedIncl σ.toRingHom x := fun _ => rfl
  obtain ⟨c, hc⟩ := exists_conj_eq_aLong hp hp2 hf hK σ hσ t ht
  set c' := (ι (nB σ.toRingHom))⁻¹ * c with hc'def
  have hc' : ((c' * t * c'⁻¹ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag (aShortTD4 K) := by
    have h1 : c * t * c⁻¹ = ι (slLong σ.toRingHom hσ3 (-1)) :=
      Subtype.ext (by rw [hc, hι, twistedIncl_slLong_neg_one hσ3])
    have h2 : slLong σ.toRingHom hσ3 (-1) =
        nB σ.toRingHom * slShort σ.toRingHom hσ3 (-1) * (nB σ.toRingHom)⁻¹ := by
      rw [← slB_neg_one hσ3, slB_apply]
    have h3 : c' * t * c'⁻¹ = ι (slShort σ.toRingHom hσ3 (-1)) := by
      calc c' * t * c'⁻¹ = (ι (nB σ.toRingHom))⁻¹ * (c * t * c⁻¹) * ι (nB σ.toRingHom) := by
            rw [hc'def]
            group
        _ = ι (slShort σ.toRingHom hσ3 (-1)) := by
            rw [h1, h2, map_mul, map_mul, map_inv]
            group
    rw [h3, hι, twistedIncl_slShort_neg_one hσ3]
  refine not_fixes_fixedSubgroup_conj_aShort σ hD (c' * t * c'⁻¹)
    (c' * g * fieldActor (t := .D4) σ δ c'⁻¹) hc' δ hδ fun x hx => ?_
  have hx₀ : c' * t * c'⁻¹ * x * (c' * t * c'⁻¹)⁻¹ = x := hx
  have hx' : c'⁻¹ * x * c' ∈ fixedSubgroup (MulAut.conj t) := by
    change t * (c'⁻¹ * x * c') * t⁻¹ = c'⁻¹ * x * c'
    calc t * (c'⁻¹ * x * c') * t⁻¹ =
        c'⁻¹ * (c' * t * c'⁻¹ * x * (c' * t * c'⁻¹)⁻¹) * c' := by group
      _ = c'⁻¹ * x * c' := by rw [hx₀]
  have h1 := hfix _ hx'
  rw [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
  rw [MulAut.mul_apply, MulAut.conj_apply, map_inv]
  calc c' * g * (fieldActor (t := .D4) σ δ c')⁻¹ * fieldActor (t := .D4) σ δ x *
        (c' * g * (fieldActor (t := .D4) σ δ c')⁻¹)⁻¹ =
      c' * (g * ((fieldActor (t := .D4) σ δ c')⁻¹ * fieldActor (t := .D4) σ δ x *
        fieldActor (t := .D4) σ δ c') * g⁻¹) * c'⁻¹ := by group
    _ = c' * (c'⁻¹ * x * c') * c'⁻¹ := by rw [h1]
    _ = x := by group

end CFSG.ComponentClassification.CatLeafProof
