module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthPhase1
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthClifford
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthBig
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthList
public import TauCeti.LinearAlgebra.QuadraticForm.Quaternary.Basic

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

section Frame

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {i : V ≃ₗ[F] V}

theorem plusSp_le_perp (h2 : (2 : F) ≠ 0) (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (fr : Frame Q) (hfr : fr.span = minusSp i) : plusSp i ≤ fr.perp := by
  intro x hx
  rw [Frame.mem_perp_iff_forall_incl]
  intro Y
  have : fr.incl Y ∈ minusSp i := hfr ▸ ⟨Y, rfl⟩
  exact polar_plusSp_minusSp h2 hi hx this

theorem perp_le_plusSp (h2 : (2 : F) ≠ 0) (hii : i * i = 1)
    (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (fr : Frame Q) (hfr : fr.span = minusSp i) :
    fr.perp ≤ plusSp i := by
  intro x hx
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii x
  have hu' : u ∈ fr.perp := plusSp_le_perp h2 hi fr hfr hu
  have hv' : v ∈ fr.perp := by
    have := fr.perp.sub_mem hx hu'
    simpa using this
  have hvs : v ∈ fr.span := hfr ▸ hv
  have hv0 : v = 0 := Submodule.disjoint_def.mp fr.isCompl_span_perp.disjoint v hvs hv'
  rw [hv0, add_zero]
  exact hu

theorem La_neg_one_eq_of_span_eq (h2 : (2 : F) ≠ 0) (hii : i * i = 1)
    (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (fr : Frame Q) (hfr : fr.span = minusSp i) :
    fr.La (-1) = i := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii x
  have hu' : fr.coords u = 0 := (Frame.mem_perp_iff fr).mp (plusSp_le_perp h2 hi fr hfr hu)
  have hvs : v ∈ fr.span := hfr ▸ hv
  have hv' : fr.incl (fr.coords v) = v := ((Frame.mem_span_iff fr).mp hvs).symm
  rw [Frame.La_neg_one_apply, map_add, hu', zero_add, hv', map_add, mem_plusSp.mp hu,
    mem_minusSp.mp hv, two_smul]
  abel

end Frame

section Arith

theorem four_dvd_of_even_of_even_choose {a : ℕ} (ha : Even a) (hc : Even (a.choose 2)) : 4 ∣ a := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' m
  · omega
  · exfalso
    have hm : m + m = 4 * k + 2 := by omega
    rw [hm] at hc
    have h : (4 * k + 2).choose 2 = (2 * k + 1) * (4 * k + 1) := by
      rw [Nat.choose_two_right]
      have h1 : 4 * k + 2 - 1 = 4 * k + 1 := by omega
      have h2 : (4 * k + 2) * (4 * k + 1) = 2 * ((2 * k + 1) * (4 * k + 1)) := by ring
      rw [h1, h2, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [h] at hc
    have hodd : Odd ((2 * k + 1) * (4 * k + 1)) := Odd.mul ⟨k, rfl⟩ ⟨2 * k, by ring⟩
    exact (Nat.not_even_iff_odd.mpr hodd) hc

end Arith

section Main

variable {p f : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p f) V]
  [FiniteDimensional (GaloisField p f) V] {Q : QuadraticForm (GaloisField p f) V}

theorem finite_linearEquiv {F W : Type} [Field F] [Finite F] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] : Finite (W ≃ₗ[F] W) := by
  have : Finite W := Module.finite_of_finite F
  exact Finite.of_injective (fun e : W ≃ₗ[F] W => (e : W → W)) DFunLike.coe_injective

theorem det_eq_one_of_mem_commutator {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    {O : Subgroup (W ≃ₗ[F] W)} {g : W ≃ₗ[F] W} (hg : g ∈ ⁅O, O⁆) : LinearEquiv.det g = 1 := by
  have hker : ⁅O, O⁆ ≤ (LinearEquiv.det : (W ≃ₗ[F] W) →* Fˣ).ker := by
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (mul_comm _ _)
  exact MonoidHom.mem_ker.mp (hker hg)

theorem exists_frame_map_eq_of_isClassicalMember [Finite (spinGroup Q)]
    (hodd : Odd (Nat.card (GaloisField p f))) (h4 : 4 ≤ Nat.card (GaloisField p f))
    (hQ : (polarBilin Q).Nondegenerate)
    (hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q))
    (hker2 : ∀ c ∈ (spinAction Q).ker, c * c = 1)
    (hrange : (spinAction Q).range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    {L : Subgroup (spinGroup Q)} {z : spinGroup Q} (h : IsClassicalMember p f L z)
    (hz : spinAction Q z ≠ 1) :
    ∃ fr : Frame Q, L.map (spinAction Q) = fr.La.range := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card (GaloisField p f) hodd
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have : Finite (V ≃ₗ[GaloisField p f] V) := finite_linearEquiv
  have hfacts := imageFacts_of_isClassicalMember (spinAction Q) h2 hker hker2 hrange hodd h hz
  set θ := spinAction Q with hθ
  set i := θ z with hi_def
  have hiO := hfacts.mem_orthogonalGroup
  have hii : i * i = 1 := hfacts.mul_self
  have hi2 : orderOf i = 2 := hfacts.orderOf_eq_two
  have hdet : LinearEquiv.det i = 1 := by
    have hmem : i ∈ θ.range := ⟨z, rfl⟩
    rw [hrange] at hmem
    exact det_eq_one_of_mem_commutator hmem
  have hW : PolarNondegOn Q (minusSp i) := polarNondegOn_minusSp h2 hQ hiO hii
  have hQ' : (polarBilin (Q.restrict (minusSp i))).Nondegenerate :=
    nondegenerate_polarBilin_restrict hW
  have hQ'' : (Q.restrict (minusSp i)).Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ'
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  have heven : Even (Module.finrank (GaloisField p f) (minusSp i)) :=
    even_finrank_minusSp h2 hii hdet
  obtain ⟨l, hlen, hlorth, hlne, hlspan, hldisc⟩ :=
    exists_orthogonal_list_restrict Q (minusSp i) hQ''
  obtain ⟨c, hc, hzz⟩ := spinLift_sq_and_norm hQnd hiO hii rfl hlorth (hlen ▸ heven) hlspan hlne
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, pow_two] at this
  have hz2' : (z : CliffordAlgebra Q) * z = 1 := by
    have := congrArg (fun x : spinGroup Q => (x : CliffordAlgebra Q)) hz2
    simpa using this
  have hsign : ((-1 : GaloisField p f) ^ l.length.choose 2) = 1 := by
    apply algebraMap_injective' Q
    rw [← hzz, hz2', map_one]
  have hchoose : Even (l.length.choose 2) :=
    (neg_one_pow_eq_one_iff_even (neg_one_ne_one h2)).mp hsign
  have h4a : 4 ∣ Module.finrank (GaloisField p f) (minusSp i) := by
    rw [← hlen]
    exact four_dvd_of_even_of_even_choose (hlen ▸ heven) hchoose
  have ha0 : Module.finrank (GaloisField p f) (minusSp i) ≠ 0 := by
    intro h0
    have hbot : minusSp i = ⊥ := Submodule.finrank_eq_zero.mp h0
    refine hz (LinearEquiv.ext fun x => ?_)
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii x
    have hv0 : v = 0 := by
      have : v ∈ (⊥ : Submodule (GaloisField p f) V) := hbot ▸ hv
      exact (Submodule.mem_bot _).mp this
    rw [hv0, add_zero]
    exact mem_plusSp.mp hu
  have hcase : Module.finrank (GaloisField p f) (minusSp i) = 4 ∨
      8 ≤ Module.finrank (GaloisField p f) (minusSp i) := by
    obtain ⟨k, hk⟩ := h4a
    omega
  rcases hcase with hdim | hdim
  swap
  ·
    exact (false_of_finrank_minus_ge_eight hodd hQ hiO hii hdim hfacts.subnormal hfacts.perfect
      hfacts.le_nM hfacts.mem hi2
      (fun N hNO hNC hNp => hfacts.le_map_centralizer hNO hNC hNp) hfacts.unique).elim
  ·
    have hiso : ¬ (Q.restrict (minusSp i)).Anisotropic := by
      rw [QuadraticMap.not_anisotropic_iff_exists]
      obtain ⟨v, hv0, hvQ⟩ := exists_isotropic_of_finrank_ge_three hodd (Q.restrict (minusSp i)) hQ'
        (by omega)
      exact ⟨v, hv0, hvQ⟩
    have hP0 : (l.map Q).prod ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hc
      exact zero_ne_one hc
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_mul, zero_mul] at hc
      exact zero_ne_one hc
    have hdisc : TauCeti.RegularFormClass.discr (TauCeti.formClass (Q.restrict (minusSp i)) hQ'') =
        0 := by
      rw [hldisc (Units.mk0 _ hP0) rfl, TauCeti.squareClass_eq_zero_iff]
      refine ⟨Units.mk0 c⁻¹ (inv_ne_zero hc0), Units.ext ?_⟩
      simp only [Units.val_mk0, Units.val_mul]
      field_simp
      linear_combination hc
    obtain ⟨φ⟩ := hQ''.equivalent_hyperbolicPlane_prod_self hdim hdisc hiso
    obtain ⟨fr, hfr⟩ := Frame4.exists_frame_of_isometryEquiv (minusSp i) φ
    have hfri : fr.La (-1) = i := La_neg_one_eq_of_span_eq h2 hii hiO fr hfr
    have hperp : fr.perp = plusSp i :=
      le_antisymm (perp_le_plusSp h2 hii hiO fr hfr) (plusSp_le_perp h2 hiO fr hfr)
    have hR : ∀ R : Subgroup (V ≃ₗ[GaloisField p f] V), IsFundamental Q R (fr.La (-1)) →
        R ≤ (Subgroup.centralizer ({z} : Set (spinGroup Q))).map θ := by
      intro R hR
      have hc := hR.le_centralizer
      rw [hfri] at hc
      exact hfacts.le_map_centralizer
        (hR.le_elementaryGroup.trans (elementaryGroup_le_orthogonalGroup Q)) hc
        (IsFundamental.commutator_eq h4 hR)
    have hiA : fr.La (-1) ∈ L.map θ := by rw [hfri]; exact hfacts.mem
    have hfix : ∀ a ∈ L.map θ, ∀ x ∈ fr.perp, a x = x := by
      intro a ha x hx
      rw [hperp] at hx
      exact (hfacts.le_nM ha).2.2 x hx
    have hAc : ∀ a ∈ L.map θ, a * fr.La (-1) = fr.La (-1) * a := by
      intro a ha
      rw [hfri]
      exact (hfacts.le_nM ha).2.1
    have hAO : L.map θ ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun a ha => (hfacts.le_nM ha).1
    have hdec := Frame4.exists_mul_of_isPerfect_fix (F := fr) h2 hfacts.perfect hAO hAc hfix
    rcases Frame4.eq_La_range_or_eq_swap hodd h4 fr hfacts.subnormal hfacts.perfect
      (hR _ (IsFundamental.of_frame fr)) (hR _ (IsFundamental.of_frame_swap fr)) hdec hiA
      hfacts.unique with hA | hA
    · exact ⟨fr, hA⟩
    · exact ⟨fr.swap, hA⟩

end Main

end CFSG.ClassicalInvolution.ModelFacts
