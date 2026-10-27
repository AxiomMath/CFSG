module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjExp
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjDescent
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjIndex
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjCore
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjFin
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjClass

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Lang.E6Descent CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Lang.AnisoE6
open CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag (delta twE6W0_inv w0_mul_delta_mul_w0_inv)
open scoped Matrix

set_option linter.unusedSectionVars false

section Main


theorem tw_conj_into_graph {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 2)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (p ^ f))
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (v : WeylGroup Tag.E6)
    (hF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {ω : (AlgebraicClosure K)ˣ} (hω : IsPrimitiveRoot (ω : AlgebraicClosure K) 3)
    {x₁ x₂ : twistedE6RootGroup K σ} (k₁ k₂ : Fin Tag.E6.rank → ℕ)
    (ha₁ : rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₁ i) =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x₁ : ModGL TwistTag.E6.tag K) * g0)
    (ha₂ : rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₂ i) =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x₂ : ModGL TwistTag.E6.tag K) * g0)
    (hb₁ : canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v *
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr
          (rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₁ i)) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)⁻¹ =
      rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₁ i))
    (hb₂ : canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v *
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr
          (rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₂ i)) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)⁻¹ =
      rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₂ i))
    (hreg : ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α →
      ¬ ((3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ) ∧ (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ))) :
    ∃ h : ModGL TwistTag.E6.tag (AlgebraicClosure K),
      h ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) ∧
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr h = h ∧
      h⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x₁ : ModGL TwistTag.E6.tag K) * h ∈
        graphCentralizer TwistTag.E6.tag (AlgebraicClosure K)
          (diagramMap TwistTag.E6 (AlgebraicClosure K)) ∧
      h⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x₂ : ModGL TwistTag.E6.tag K) * h ∈
        graphCentralizer TwistTag.E6.tag (AlgebraicClosure K)
          (diagramMap TwistTag.E6 (AlgebraicClosure K)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI hKp : CharP K p :=
    charP_of_card_eq_prime_pow (f := f * 2)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hω3 : ω ^ 3 = 1 := Units.ext (by simpa using hω.pow_eq_one)
  have hFrEq : Fr = iterateFrobenius (AlgebraicClosure K) p f := RingHom.ext fun c => by
    rw [hFr, iterateFrobenius_def]
  have hfixv : ∀ (k : Fin Tag.E6.rank → ℕ),
      canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v *
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr
          (rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k i)) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)⁻¹ =
        rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k i) →
      ∀ t : Fin Tag.E6.rank, (3 : ℤ) ∣
        (∑ i, (k i : ℤ) * ((twE6W0 * v⁻¹) • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i) -
          (k t : ℤ) := by
    intro k hb
    refine tw_torus_exp_fix hFr hq hω v k ?_
    obtain ⟨n, hn⟩ : ∃ n : ModGL TwistTag.E6.tag (AlgebraicClosure K),
        n = canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d : ModGL TwistTag.E6.tag (AlgebraicClosure K),
        d = rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k i) := ⟨_, rfl⟩
    rw [← hn, ← hd] at hb
    show twistHom TwistTag.E6 (AlgebraicClosure K) Fr
        (rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k i)) =
      (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)⁻¹ *
        rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k i) *
          canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v
    rw [← hn, ← hd]
    calc twistHom TwistTag.E6 (AlgebraicClosure K) Fr d =
          n⁻¹ * (n * twistHom TwistTag.E6 (AlgebraicClosure K) Fr d * n⁻¹) * n := by group
      _ = n⁻¹ * d * n := by rw [hb]
  obtain ⟨ωc, hk₁V, hk₂V, hcase⟩ := tw_regular_elliptic_conj (twE6W0 * v⁻¹) k₁ k₂ hreg
    (hfixv k₁ hb₁) (hfixv k₂ hb₂)
  rcases hcase with hinner | ⟨a, b, m, hm, hnot⟩
  swap
  · exact (tw_outer_false hp hf hK σ hσ hq Fr hFr g0 hg0C v hF hω k₁ k₂ ha₁ ha₂ a b m hm
      hnot).elim
  set V : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd ωc with hV
  have hw : dlt (V * v * (dlt V)⁻¹) = V * v * (dlt V)⁻¹ := tw_inner_hw v V hinner
  have hF2 : twistHom TwistTag.E6 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) p f)
      g0 = g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v := by
    rw [← hFrEq]
    exact hF
  obtain ⟨h, hhad, hhF, hhΓ⟩ := exists_fixed_conj_into_graphFixed_tw (L := AlgebraicClosure K)
    p f hf v V g0 hg0C hF2 hw (ι := Bool)
    (fun b => cond b (rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₁ i))
      (rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₂ i)))
    (fun b => by cases b <;> exact rootDiagUnit_mem_torusGroup _)
    (fun b => by
      cases b
      · exact tw_diagramMap_conj_diag ω hω3 V k₂ hk₂V
      · exact tw_diagramMap_conj_diag ω hω3 V k₁ hk₁V)
  refine ⟨h, hhad, by rw [hFrEq]; exact hhF, ?_, ?_⟩
  · have h1 := hhΓ true
    have e1 : g0 * rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₁ i) * g0⁻¹ =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x₁ : ModGL TwistTag.E6.tag K) := by
      rw [ha₁]
      group
    simpa only [cond_true, e1] using h1
  · have h1 := hhΓ false
    have e1 : g0 * rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₂ i) * g0⁻¹ =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x₂ : ModGL TwistTag.E6.tag K) := by
      rw [ha₂]
      group
    simpa only [cond_false, e1] using h1

theorem tw_regular_contained_gen {q : ℕ} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    {k : Type} [Field k] [Finite k] [Algebra k K]
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hkq : Nat.card k = q)
    (hq : q % 3 = 2) (E₀ : Subgroup (twistedE6RootGroup K σ)) (hexp : ∀ x ∈ E₀, x ^ 3 = 1)
    (hcard : Nat.card E₀ = 3 ^ 2)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup TwistTag.E6.tag) (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    (hmem : ∀ x ∈ E₀,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
          (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom)
    (hreg : ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α →
      ¬ TwKills K σ E₀ g0 α) :
    ∃ g : twistedE6RootGroup K σ,
      E₀.map (MulAut.conj g).toMonoidHom ≤
        ((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom).range := by
  classical
  obtain ⟨hp, f, hf, rfl⟩ := exists_pow_ringChar_of_card_sq K q hK (by omega)
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have hp3 : ringChar K ≠ 3 := by
    intro h
    rw [h] at hq
    have h3 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    omega
  haveI : Finite E₀ := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Nontrivial E₀ := Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; norm_num)
  obtain ⟨⟨x₁, hx₁E⟩, hx₁ne⟩ := exists_ne (1 : E₀)
  have hx₁1 : x₁ ≠ 1 := fun h => hx₁ne (Subtype.ext h)
  have hx₁3 : x₁ ^ 3 = 1 := hexp x₁ hx₁E
  obtain ⟨x₂, hx₂E, hx₂not⟩ := exists_mem_not_mem_zpowers E₀ hcard hx₁E hx₁3 hx₁1
  have hgen : Subgroup.closure ({x₁, x₂} : Set (twistedE6RootGroup K σ)) = E₀ :=
    closure_pair_eq_of_not_mem E₀ hcard hx₁E hx₂E hx₁3 hx₁1 hx₂not
  obtain ⟨ω, hω⟩ := exists_primCubeRoot_of_charP (L := AlgebraicClosure K) hp3
  have hω3 : ω ^ 3 = 1 := Units.ext (by simpa using hω.pow_eq_one)
  obtain ⟨k₁, ha₁, hb₁⟩ := tw_diag_exponent hω Fr
    (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v) g0 x₁ hx₁3
    (hmem x₁ hx₁E)
  obtain ⟨k₂, ha₂, hb₂⟩ := tw_diag_exponent hω Fr
    (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v) g0 x₂
    (hexp x₂ hx₂E) (hmem x₂ hx₂E)
  have hreg' : ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α →
      ¬ ((3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ) ∧ (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ)) := fun α hα hh =>
    hreg α hα (tw_kills_of_pair hω3 hgen g0 k₁ k₂ ha₁ ha₂ hh.1 hh.2)
  obtain ⟨h, hhad, hhF, hh₁, hh₂⟩ := tw_conj_into_graph hp hf hK σ hσ hq Fr hFr g0 hg0C v hF hω
    k₁ k₂ ha₁ ha₂ hb₁ hb₂ hreg'
  obtain ⟨ωv, hωv, hvw⟩ := (coxeterSystem Tag.E6).exists_isReduced v
  have hF' : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
        ((coxeterSystem Tag.E6).wordProd ωv) := by
    rw [← hvw]
    exact hF
  obtain ⟨t, htT, htF, htC⟩ := tw_exists_class_element hp hf hK σ hσ hq Fr hFr g0 hg0C hωv hF'
  obtain ⟨t', htT', htF', htC'⟩ : ∃ t' : ModGL TwistTag.E6.tag (AlgebraicClosure K),
      t' ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) ∧
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr t' =
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
          ((coxeterSystem Tag.E6).wordProd ωv))⁻¹ * t' *
          canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
            ((coxeterSystem Tag.E6).wordProd ωv) ∧
      g0 * t' * g0⁻¹ ∉ (twistedE6RootGroup K σ).map
        (baseChangeGL (algebraMap K (AlgebraicClosure K))) := ⟨t, htT, htF, htC⟩
  have ht'ad : t' ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htT'
    rw [ha]
    exact (exceptional_Lang_adjoint_diagonal_lift TwistTag.E6.tag (AlgebraicClosure K) a).1
  have hc0ad : g0 * t' * g0⁻¹ ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    mul_mem (mul_mem hg0C ht'ad) (inv_mem hg0C)
  have hc0R : g0 * t' * g0⁻¹ ∈ twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr := by
    refine ⟨hc0ad, ?_⟩
    show twistHom TwistTag.E6 (AlgebraicClosure K) Fr (g0 * t' * g0⁻¹) = g0 * t' * g0⁻¹
    rw [map_mul, map_mul, map_inv, hF', htF']
    group
  have hhR : h ∈ twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr := ⟨hhad, hhF⟩
  obtain ⟨j, hj⟩ := tw_class_correction hp hf hK σ hσ hq Fr hFr hc0R hhR htC'
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 hj
  have key : ∀ (x : twistedE6RootGroup K σ) (kx : Fin Tag.E6.rank → ℕ)
      (hax : rootDiagUnit TwistTag.E6.tag (fun i => ω ^ kx i) =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) * g0)
      (hΓ : h⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL TwistTag.E6.tag K) * h ∈
        graphCentralizer TwistTag.E6.tag (AlgebraicClosure K)
          (diagramMap TwistTag.E6 (AlgebraicClosure K))),
      (⟨y, hy⟩ : twistedE6RootGroup K σ)⁻¹ * x * ⟨y, hy⟩ ∈ (phiG σ hfix).range := by
    intro x kx hax hΓ
    refine tw_mem_range_phiG σ hσ hfix hkq Fr hFr _ ?_
    have hxL : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) =
        g0 * rootDiagUnit TwistTag.E6.tag (fun i => ω ^ kx i) * g0⁻¹ := by
      rw [hax]
      group
    have hcomm : Commute (g0 * t' * g0⁻¹)
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K)) := by
      have hdt := rootDiagUnit_mul_comm_of_mem_torusGroup (τ := TwistTag.E6.tag)
        (K := AlgebraicClosure K) (fun i => ω ^ kx i) htT'
      show g0 * t' * g0⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) = _
      rw [hxL]
      calc g0 * t' * g0⁻¹ * (g0 * rootDiagUnit TwistTag.E6.tag (fun i => ω ^ kx i) * g0⁻¹)
          = g0 * (t' * rootDiagUnit TwistTag.E6.tag (fun i => ω ^ kx i)) * g0⁻¹ := by group
        _ = g0 * (rootDiagUnit TwistTag.E6.tag (fun i => ω ^ kx i) * t') * g0⁻¹ := by rw [hdt]
        _ = g0 * rootDiagUnit TwistTag.E6.tag (fun i => ω ^ kx i) * g0⁻¹ * (g0 * t' * g0⁻¹) := by
          group
    have hcz := hcomm.zpow_left j
    have e2 : ((g0 * t' * g0⁻¹) ^ j)⁻¹ *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          (g0 * t' * g0⁻¹) ^ j =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) := by
      rw [hcz.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
    have e3 : ((g0 * t' * g0⁻¹) ^ j * h)⁻¹ *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          ((g0 * t' * g0⁻¹) ^ j * h) =
        h⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) * h := by
      rw [mul_inv_rev]
      calc h⁻¹ * ((g0 * t' * g0⁻¹) ^ j)⁻¹ *
            baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
              ((g0 * t' * g0⁻¹) ^ j * h)
          = h⁻¹ * (((g0 * t' * g0⁻¹) ^ j)⁻¹ *
              baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
                (g0 * t' * g0⁻¹) ^ j) * h := by group
        _ = h⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              (x : ModGL TwistTag.E6.tag K) * h := by rw [e2]
    have e1 : baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((⟨y, hy⟩ : twistedE6RootGroup K σ)⁻¹ * x * ⟨y, hy⟩ : twistedE6RootGroup K σ) :
          ModGL TwistTag.E6.tag K) =
        ((g0 * t' * g0⁻¹) ^ j * h)⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
            ((g0 * t' * g0⁻¹) ^ j * h) := by
      rw [← hyeq]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rw [e1, e3]
    exact hΓ
  have hz₁ := key x₁ k₁ ha₁ hh₁
  have hz₂ := key x₂ k₂ ha₂ hh₂
  have hrange : ∀ z, z ∈ (phiG σ hfix).range →
      z ∈ ((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom).range := by
    rintro z ⟨γ, rfl⟩
    exact ⟨e6FixedF4EquivAll k γ, by simp⟩
  refine ⟨(⟨y, hy⟩ : twistedE6RootGroup K σ)⁻¹, ?_⟩
  rw [Subgroup.map_le_iff_le_comap, ← hgen, Subgroup.closure_le]
  intro z hz
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  have e : ∀ w : twistedE6RootGroup K σ,
      (MulAut.conj (⟨y, hy⟩ : twistedE6RootGroup K σ)⁻¹).toMonoidHom w =
        (⟨y, hy⟩ : twistedE6RootGroup K σ)⁻¹ * w * ⟨y, hy⟩ := fun w => by
    simp [MulAut.conj_apply]
  rcases hz with rfl | rfl
  · rw [e]
    exact hrange _ hz₁
  · rw [e]
    exact hrange _ hz₂

theorem twHighRegularContained_two : TwHighRegularContained_two := by
  intro q K _ _ σ k _ _ _ hfix hK hσ hkq hq _hq3 E₀ hexp hcard _hnn Fr hFr v g0 hg0C hF hmem hreg
  exact tw_regular_contained_gen σ hfix hK hσ hkq hq E₀ hexp hcard Fr hFr v g0 hg0C hF hmem hreg

end Main

end CFSG.LieType.SeitzGeneration.ExcHighThree
