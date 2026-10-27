module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIISymplecticField
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIILinearFiveTwo
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer

public section

namespace CFSG.ComponentClassification.RankTwoHypIISymplectic

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.ComponentClassification.RankTwoHypIIY
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.ComponentClassification.SymmetricLocal
  (small_standard_source_even_simple_symplectic_parameters_stated)

variable {K : Type} [Field K]

section Transvection

variable (K) in
@[expose] noncomputable def transvSp : StatedSp 2 K :=
  upperUnipotentSp 2 K (transpose_single_zero_zero (K := K))

theorem transvSp_mul_self [CharP K 2] : transvSp K * transvSp K = 1 := by
  have h : (single (0 : Fin 2) (0 : Fin 2) (1 : K)) + single 0 0 1 = 0 := by
    ext i j
    rw [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  apply Subtype.ext
  apply Units.ext
  change (((transvSp K : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
    (((transvSp K : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1
  rw [transvSp, coe_upperUnipotentSp, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [h, fromBlocks_one]

theorem spInner_transvSp_mem_range [CharP K 2] (k : Subfield K) :
    spInner 2 K (transvSp K) ∈ ((spInner 2 K).comp (subfieldSpHom 2 k)).range := by
  have hent : ∀ i j, spMat (transvSp K) i j ∈ k := by
    intro i j
    rw [spMat, transvSp, coe_upperUnipotentSp]
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
        Matrix.one_apply, Matrix.single_apply, Matrix.zero_apply] <;>
      (try split_ifs) <;> first | exact zero_mem k | exact one_mem k
  have hinv : (transvSp K)⁻¹ = transvSp K := inv_eq_of_mul_eq_one_right transvSp_mul_self
  obtain ⟨g₀, hg₀⟩ := exists_subfieldSpHom_eq_of_mem k hent (by rw [hinv]; exact hent)
  exact ⟨g₀, by rw [MonoidHom.comp_apply, hg₀]⟩

theorem not_commute_transvection [Finite K] [CharP K 2] {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) {s : MulAut (StatedProj (StatedSp 2 K))}
    (hs : s ∉ spSemilinearAutGroup 2 K) :
    s * spInner 2 K (transvSp K) ≠ spInner 2 K (transvSp K) * s := by
  intro hcomm
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
  obtain ⟨-, huniq, -, -, -, -, hEsup, -⟩ :=
    exceptionalAut_structure (by omega) hFr hord hzp
  set γ := exceptionalAut K with hγ
  have hγE : γ ^ 2 ∈ spSemilinearAutGroup 2 K := by
    rw [hEsup]
    exact mem_sup_right (mem_zpowers _)
  obtain ⟨⟨g, j⟩, hgj, -⟩ := huniq s
  simp only at hgj
  have hj : ¬ Even (j : ℕ) := by
    rintro ⟨i, hi⟩
    apply hs
    rw [hgj, hi, ← two_mul, pow_mul]
    exact mul_mem (spInner_mem_spSemilinearAutGroup g) (pow_mem hγE i)
  obtain ⟨i, hi⟩ := Nat.not_even_iff_odd.mp hj
  have heE : s * γ⁻¹ ∈ spSemilinearAutGroup 2 K := by
    have : s * γ⁻¹ = spInner 2 K g * (γ ^ 2) ^ i := by
      rw [hgj, hi, ← pow_mul, pow_succ, mul_assoc, mul_inv_cancel_right]
    rw [this]
    exact mul_mem (spInner_mem_spSemilinearAutGroup g) (pow_mem hγE i)
  obtain ⟨g', φ, he⟩ := exists_eq_spInner_mul_fieldAut (inv_mem heE)
  have hfix : s (proj 2 K (transvSp K)) = proj 2 K (transvSp K) := by
    have h1 : s * MulAut.conj (proj 2 K (transvSp K)) * s⁻¹ =
        MulAut.conj (proj 2 K (transvSp K)) := by
      rw [← spInner_eq_conj, hcomm, mul_inv_cancel_right]
    rw [mulAut_mul_conj_mul_inv] at h1
    exact RankTwoHypIIY.conj_injective_of_center_eq_bot
      (center_eq_bot (r := 2) hK (by norm_num) (Or.inl hf) (by omega)) h1
  have h2' : γ (proj 2 K (transvSp K)) = (s * γ⁻¹)⁻¹ (proj 2 K (transvSp K)) := by
    have : γ (proj 2 K (transvSp K)) = (s * γ⁻¹)⁻¹ (s (proj 2 K (transvSp K))) := by
      rw [← MulAut.mul_apply]
      congr 1
      group
    rw [this, hfix]
  have h2 : proj 2 K (exceptionalSpAut K (transvSp K)) =
      proj 2 K (g' * fieldSp 2 K φ (transvSp K) * g'⁻¹) := by
    rw [← exceptionalAut_proj, ← hγ, h2', he, spInner_mul_fieldAut_proj]
  have h3 := UnitaryHigher.proj_bijective_of_charTwo.1 h2
  have h4 := displacementInLine_conj g' (transvSp K) φ displacementInLine_upperUnipotent
  rw [← h3, transvSp, exceptionalSpAut_upperUnipotent] at h4
  exact not_displacementInLine_upperUnipotent_swap h4

end Transvection

section Field

variable [Finite K]

theorem rigidInvolution_fieldAut_four {f : ℕ} (hf : 4 ≤ f) (hfe : Even f)
    (hK : Nat.card K = 2 ^ f) (σ : K ≃+* K) (hσ : ∀ t, σ t = t ^ 2 ^ (f / 2))
    (hX : fieldAut 2 K σ ∉ inner (StatedProj (StatedSp 2 K)))
    (h2 : fieldAut 2 K σ ^ 2 = 1) :
    RigidInvolution (inner (StatedProj (StatedSp 2 K))) (fieldAut 2 K σ) := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  refine rigidInvolution_fieldAut_sp le_rfl (by omega) hfe hK (Or.inr hf) σ hσ
    (fun s hs hsN => ?_) hX h2
  apply not_commute_transvection (by omega) hK hs
  exact (mem_centralizer_iff.mp hsN _ (spInner_transvSp_mem_range _)).symm

theorem mem_normalizer_commutator {W : Type*} [Group W] {N : Subgroup W} {c : W}
    (hc : c ∈ normalizer (N : Set W)) : c ∈ normalizer ((⁅N, N⁆ : Subgroup W) : Set W) := by
  have hmap : ∀ d ∈ normalizer (N : Set W), N.map (MulAut.conj d).toMonoidHom = N := by
    intro d hd
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.mp hd x).mp hx
    · intro x hx
      refine ⟨d⁻¹ * x * d, ?_, by simp [mul_assoc]⟩
      have := (mem_normalizer_iff.mp (inv_mem hd) x).mp hx
      simpa [mul_assoc] using this
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : (MulAut.conj c).toMonoidHom y ∈ (⁅N, N⁆ : Subgroup W).map (MulAut.conj c).toMonoidHom :=
      mem_map_of_mem _ hy
    rwa [Subgroup.map_commutator, hmap c hc] at this
  · intro hy
    have hy' : (MulAut.conj c⁻¹).toMonoidHom (c * y * c⁻¹) ∈
        (⁅N, N⁆ : Subgroup W).map (MulAut.conj c⁻¹).toMonoidHom := mem_map_of_mem _ hy
    rw [Subgroup.map_commutator, hmap c⁻¹ (inv_mem hc)] at hy'
    simpa [mul_assoc] using hy'

theorem rigidInvolution_fieldAut_four_two (hK : Nat.card K = 2 ^ 2) (σ : K ≃+* K)
    (hσ : ∀ t, σ t = t ^ 2 ^ (2 / 2))
    (hX : fieldAut 2 K σ ∉ inner (StatedProj (StatedSp 2 K)))
    (h2 : fieldAut 2 K σ ^ 2 = 1) :
    RigidInvolution (inner (StatedProj (StatedSp 2 K))) (fieldAut 2 K σ) := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have : Finite (MulAut (StatedProj (StatedSp 2 K))) := Finite.of_injective
    (fun e : MulAut (StatedProj (StatedSp 2 K)) => (e : StatedProj (StatedSp 2 K) →
      StatedProj (StatedSp 2 K))) fun _ _ hab => MulEquiv.ext (congrFun hab)
  set k := descentField σ with hk
  set N := ((spInner 2 K).comp (subfieldSpHom 2 k)).range with hN
  obtain ⟨hNI, -, hιjinj, -, hCEN, -⟩ :=
    even_symplectic_field_centralizers_and_intermediate_odd_cores le_rfl le_rfl even_two hK σ hσ
  have hNeq : N = inner (StatedProj (StatedSp 2 K)) ⊓ centralizer {fieldAut 2 K σ} := by
    rw [hN, hk]
    exact range_eq_inner_inf_centralizer le_rfl le_rfl even_two hK σ hσ
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    exact hX (by rw [map_one]; exact one_mem _)
  obtain ⟨-, -, hkcard, -⟩ := even_symplectic_quadratic_involution_descent (by omega)
    (by omega) hK (a := fieldAut 2 K σ) (by rw [← sq, h2]) 1 σ
    (by rw [show (⟨(1 : StatedSp 2 K), statedSp_le_gsp (1 : StatedSp 2 K).2⟩ : gsp 2 K) = 1 from
      rfl, map_one, one_mul]) hσ1
  have hk2 : Nat.card k = 2 := by rw [hkcard]; rfl
  obtain ⟨-, -, -, -, ⟨eProj⟩⟩ := small_standard_source_even_simple_symplectic_parameters_stated
    (X := StatedSp 2 k) hkcard (by omega) ⟨MulEquiv.refl _⟩
  let e : N ≃* CFSG.ComponentClassification.PresentationLocal.sympFour :=
    ((MonoidHom.ofInjective hιjinj).symm.trans eProj.symm).trans
      (CFSG.RankThree.PartOne.KCSpComm.statedProjEquivSympFour hk2)
  set L : Subgroup (MulAut (StatedProj (StatedSp 2 K))) := ⁅N, N⁆ with hL
  have eL : L ≃* commutator CFSG.ComponentClassification.PresentationLocal.sympFour :=
    RankTwoHypIILinear.commutatorEquivOfMulEquiv e
  have hLsimple : IsSimpleGroup L := by
    have := CFSG.ComponentClassification.PresentationLocal.isSimpleGroup_commutator_sympFour
    exact eL.isSimpleGroup
  have hnc : ¬ ∀ a b : L, a * b = b * a := by
    intro hab
    apply CFSG.ComponentClassification.PresentationLocal.not_isMulCommutative_commutator_sympFour
    refine ⟨⟨fun x y => ?_⟩⟩
    apply eL.symm.injective
    rw [map_mul, map_mul, hab]
  have hLp : ⁅L, L⁆ = L := commutator_eq_self_of_isSimpleGroup hLsimple hnc
  have heven : Even (Nat.card L) := by
    rw [Nat.card_congr (eL.trans
      CFSG.ComponentClassification.PresentationLocal.commutatorEquivAlternating).toEquiv]
    have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
    rw [Nat.card_perm, Nat.card_fin] at h
    have h' : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      have : Nat.factorial 6 = 720 := by decide
      omega
    rw [h']
    decide
  have hLN : L ≤ N := by
    rw [hL, commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hNC : N ≤ centralizer {fieldAut 2 K σ} := by
    rw [hNeq]
    exact inf_le_right
  have hCN : centralizer {fieldAut 2 K σ} ≤
      normalizer (N : Set (MulAut (StatedProj (StatedSp 2 K)))) := by
    intro c hc
    rw [mem_normalizer_iff]
    intro y
    rw [hNeq]
    constructor
    · intro hy
      obtain ⟨hyI, hyC⟩ := mem_inf.mp hy
      exact mem_inf.mpr ⟨(inner_normal _).conj_mem y hyI c, mul_mem (mul_mem hc hyC) (inv_mem hc)⟩
    · intro hy
      obtain ⟨hyI, hyC⟩ := mem_inf.mp hy
      refine mem_inf.mpr ⟨?_, ?_⟩
      · have := (inner_normal _).conj_mem _ hyI c⁻¹
        simpa [mul_assoc] using this
      · have := mul_mem (mul_mem (inv_mem hc) hyC) hc
        simpa [mul_assoc] using this
  refine ⟨L, hLN.trans hNI, hLN.trans hNC, fun c hc => mem_normalizer_commutator (hCN hc), hLp,
    twoNilpotentCentral_of_isSimpleGroup hLsimple hLp heven, ?_⟩
  intro s hs hsL hs2
  have hsN : s ∈ centralizer (N : Set (MulAut (StatedProj (StatedSp 2 K)))) := by
    rw [mem_centralizer_iff]
    intro n hn
    have hsnN : s * n * s⁻¹ ∈ N := (mem_normalizer_iff.mp (hCN hs) n).mp hn
    have hc : n⁻¹ * (s * n * s⁻¹) ∈ centralizer (L : Set (MulAut (StatedProj (StatedSp 2 K)))) := by
      rw [mem_centralizer_iff]
      intro a ha
      have hna : n * a * n⁻¹ ∈ L :=
        (mem_normalizer_iff.mp (mem_normalizer_commutator (le_normalizer hn)) a).mp ha
      have h1 : s * (n * a * n⁻¹) * s⁻¹ = n * a * n⁻¹ := by
        rw [← mem_centralizer_iff.mp hsL _ hna, mul_inv_cancel_right]
      have h2 : s * a * s⁻¹ = a := by
        rw [← mem_centralizer_iff.mp hsL _ ha, mul_inv_cancel_right]
      have h3 : s * (n * a * n⁻¹) * s⁻¹ = (s * n * s⁻¹) * (s * a * s⁻¹) * (s * n * s⁻¹)⁻¹ := by
        group
      rw [h2] at h3
      rw [h3] at h1
      calc a * (n⁻¹ * (s * n * s⁻¹)) = n⁻¹ * (n * a * n⁻¹) * (s * n * s⁻¹) := by group
        _ = n⁻¹ * ((s * n * s⁻¹) * a * (s * n * s⁻¹)⁻¹) * (s * n * s⁻¹) := by rw [h1]
        _ = n⁻¹ * (s * n * s⁻¹) * a := by group
    have h1 := RankTwoHypIILinear.eq_one_of_mem_centralizer_commutator e
      CFSG.ComponentClassification.PresentationLocal.centralizer_commutator_sympFour
      (mul_mem (inv_mem hn) hsnN) hc
    rw [inv_mul_eq_one] at h1
    calc n * s = s * n * s⁻¹ * s := by rw [← h1]
      _ = s * n := by group
  by_cases hsE : s ∈ spSemilinearAutGroup 2 K
  · have hs' : s ∈ spSemilinearAutGroup 2 K ⊓ centralizer (N : Set _) := ⟨hsE, hsN⟩
    rw [hCEN] at hs'
    exact eq_one_or_eq_of_mem_zpowers h2 hs'
  · exact absurd (mem_centralizer_iff.mp hsN _ (spInner_transvSp_mem_range k)).symm
      (not_commute_transvection le_rfl hK hsE)

end Field

section Suzuki

variable [Finite K] [CharP K 2] {m : ℕ}

theorem exists_conj_eta (hK : Nat.card K = 2 ^ (2 * m + 1))
    {a : MulAut (StatedProj (StatedSp 2 K))} (ha : orderOf a = 2)
    (haI : a ∉ inner (StatedProj (StatedSp 2 K))) :
    ∃ b ∈ inner (StatedProj (StatedSp 2 K)), a = b * exceptionalAut K ^ (2 * m + 1) * b⁻¹ := by
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
  obtain ⟨hγord, -, -, -, -, -, -, -, -, hinvol⟩ := exceptionalAut_structure (by omega) hFr hord hzp
  obtain ⟨s, j, hj, hsj⟩ := hinvol a ha
  have hjf : j = 2 * m + 1 := hj.resolve_left fun h => haI (by
    rw [hsj, h, pow_zero, mul_one]
    exact spInner_mem_inner s)
  subst hjf
  set ηG : Subgroup.zpowers (minorAut K ^ (2 * m + 1)) :=
    ⟨minorAut K ^ (2 * m + 1), Subgroup.mem_zpowers _⟩ with hηG
  set u := (antiSpEquiv K).symm s with hu
  set x : etaProduct K m := SemidirectProduct.inl u * SemidirectProduct.inr ηG with hx
  have hΘx : etaProductHom K m x = a := by
    rw [hx, map_mul, etaProductHom_inl, hηG, etaProductHom_inr_eta, hu,
      MulEquiv.apply_symm_apply, hsj]
  have hxr : x.right = ηG := by
    rw [hx, SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.right_inr,
      one_mul]
  have hγ2f : exceptionalAut K ^ (2 * (2 * m + 1)) = 1 := by rw [← hγord, pow_orderOf_eq_one]
  have hu1 : u * (minorAut K ^ (2 * m + 1)) u = 1 := by
    have hsq := pow_orderOf_eq_one a
    rw [ha] at hsq
    have hγ2 : exceptionalAut K ^ (2 * m + 1) * exceptionalAut K ^ (2 * m + 1) = 1 := by
      rw [← pow_add, ← two_mul, hγ2f]
    have key : a * a = spInner 2 K (s * (exceptionalSpAut K ^ (2 * m + 1)) s) :=
      calc a * a = spInner 2 K s * (exceptionalAut K ^ (2 * m + 1) * spInner 2 K s) *
            exceptionalAut K ^ (2 * m + 1) := by rw [hsj]; simp only [mul_assoc]
        _ = spInner 2 K s * spInner 2 K ((exceptionalSpAut K ^ (2 * m + 1)) s) *
            (exceptionalAut K ^ (2 * m + 1) * exceptionalAut K ^ (2 * m + 1)) := by
          rw [exceptionalAut_pow_mul_spInner]
          simp only [mul_assoc]
        _ = spInner 2 K (s * (exceptionalSpAut K ^ (2 * m + 1)) s) := by
          rw [hγ2, mul_one, map_mul]
    have h1 : s * (exceptionalSpAut K ^ (2 * m + 1)) s = 1 :=
      spInner_injective (by rw [← key, ← sq, hsq, map_one])
    have hs : s = antiSpEquiv K u := by rw [hu, MulEquiv.apply_symm_apply]
    rw [hs, exceptionalSpAut_pow_apply, ← map_mul] at h1
    exact (antiSpEquiv K).injective (h1.trans (map_one _).symm)
  have hxl : x.left = u := by
    simp only [hx, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.left_inr, SemidirectProduct.right_inl, map_one, mul_one]
  have hx2 : x ^ 2 = 1 := by
    refine SemidirectProduct.ext ?_ ?_
    · rw [sq, SemidirectProduct.mul_left, hxr, hxl, SemidirectProduct.one_left]
      exact hu1
    · rw [sq, SemidirectProduct.mul_right, hxr, SemidirectProduct.one_right]
      have h := pow_orderOf_eq_one (minorAut K ^ (2 * m + 1))
      rw [orderOf_eta m hK] at h
      exact Subtype.ext (by rw [Subgroup.coe_mul, ← sq, h]; rfl)
  obtain ⟨h, hh⟩ := eta_involution_conj m hK x hxr hx2
  have hconj := congrArg (etaProductHom K m) hh
  rw [map_mul, map_mul, map_inv, hΘx, etaProductHom_inl, etaProductHom_inr_eta] at hconj
  refine ⟨(spInner 2 K (antiSpEquiv K h))⁻¹, inv_mem (spInner_mem_inner _), ?_⟩
  rw [← hconj]
  group

theorem rigidInvolution_eta (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    RigidInvolution (inner (StatedProj (StatedSp 2 K))) (exceptionalAut K ^ (2 * m + 1)) := by
  have : Finite (MulAut (StatedProj (StatedSp 2 K))) := Finite.of_injective
    (fun e : MulAut (StatedProj (StatedSp 2 K)) => (e : StatedProj (StatedSp 2 K) →
      StatedProj (StatedSp 2 K))) fun _ _ hab => MulEquiv.ext (congrFun hab)
  obtain ⟨φ, -, hφinj, hord2, hrange, hC, -, hγN, hCN, -⟩ :=
    even_symplectic_two_suzuki_full_centralizer_odd_core hm hK (exceptionalAut K)
      exceptionalAut_proj
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
  obtain ⟨-, -, -, -, -, -, -, -, hpowI, -⟩ := exceptionalAut_structure (by omega) hFr hord hzp
  set η := exceptionalAut K ^ (2 * m + 1) with hη
  set L := φ.range with hL
  have hηX : η ∉ inner (StatedProj (StatedSp 2 K)) := by
    rw [hη, hpowI]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hη2 : η ^ 2 = 1 := by
    have := pow_orderOf_eq_one η
    rwa [hord2] at this
  obtain ⟨-, -, hsimple⟩ := CFSG.LieType.Ree.suzuki_simple hm hK
  have eL : CFSG.Blueprint.suzukiGroup m K ≃* L := MonoidHom.ofInjective hφinj
  have hLsimple : IsSimpleGroup L := eL.symm.isSimpleGroup
  have heven : Even (Nat.card L) := by
    rw [← Nat.card_congr eL.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
    refine Even.mul_right (Even.mul_right ?_ _) _
    exact Even.pow_of_ne_zero (Even.pow_of_ne_zero even_two (by omega)) (by norm_num)
  have hγL : exceptionalAut K ∈ normalizer (L : Set (MulAut (StatedProj (StatedSp 2 K)))) := by
    have hle : L.map (MulAut.conj (exceptionalAut K)).toMonoidHom ≤ L := by
      rintro _ ⟨n, hn, rfl⟩
      exact hγN n hn
    have heq : L.map (MulAut.conj (exceptionalAut K)).toMonoidHom = L :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Subgroup.card_map_of_injective (MulAut.conj (exceptionalAut K)).injective])
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have : (MulAut.conj (exceptionalAut K)).toMonoidHom y ∈
          L.map (MulAut.conj (exceptionalAut K)).toMonoidHom := mem_map_of_mem _ hy
      rwa [heq] at this
    · intro hy
      rw [← heq] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
      have : y = z := by
        have := congrArg (fun w => (exceptionalAut K)⁻¹ * w * exceptionalAut K) hzy
        simpa [mul_assoc] using this.symm
      rwa [this]
  refine RigidInvolution.of_isSimpleGroup_of_le_zpowers hηX hη2 (hrange ▸ inf_le_left)
    (hrange ▸ inf_le_right) ?_ hLsimple heven ?_
  · rw [hC]
    exact sup_le le_normalizer (zpowers_le.mpr hγL)
  · rw [hCN]
    exact inf_le_right

end Suzuki

end CFSG.ComponentClassification.RankTwoHypIISymplectic
