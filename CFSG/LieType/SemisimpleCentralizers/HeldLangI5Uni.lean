module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5Inn
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5Torus
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5Aux
public import CFSG.LieType.SemisimpleCentralizers.HeldLangPSU
public import CFSG.ClassicalInvolution.Phan.CenterScalars

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open CFSG.Open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
  CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.HardMathSupport.Foote.ModuleExclusions

theorem suFixEmb_injective {K : Type} [Field K] {d : ℕ} {bar σ : K ≃+* K}
    (hcomm : ∀ x, σ (bar x) = bar (σ x)) (hbb : ∀ x, bar (bar x) = x) (u : GL (Fin d) K) (hu : IsIso bar u) :
    Function.Injective (suFixEmb hcomm hbb u hu) := by
  intro x y hxy
  have h1 : u⁻¹ * glFixEmb σ (x : GL (Fin d) (fixField σ)) * u =
      u⁻¹ * glFixEmb σ (y : GL (Fin d) (fixField σ)) * u :=
    congrArg (fun z : SUid bar d => (z : GL (Fin d) K)) hxy
  have h2 : glFixEmb σ (x : GL (Fin d) (fixField σ)) = glFixEmb σ (y : GL (Fin d) (fixField σ)) := by
    simpa using h1
  exact Subtype.ext (glFixEmb_injective σ h2)

theorem exists_phi_of_outer_three {K : Type} [Field K] {p f N : ℕ} (hdat : UnitaryFieldData p f K)
    (hN : 3 ≤ N) (hNq : ¬(N = 3 ∧ p ^ f = 2))
    (β' : MulAut (StatedProj (StatedSU N (p ^ f) K))) (hβ'3 : β' ^ 3 = 1)
    (hout : β' ∉ innAutDerived (StatedProj (StatedSU N (p ^ f) K))) :
    ∃ (A : uU hdat N) (φ : K ≃+* K),
      β' = uConjAut hdat (by omega) A * uFieldAut hdat (by omega) φ ∧ orderOf φ = 3 := by
  have hn1 : 1 ≤ N := by omega
  haveI : Finite K := hdat.finite
  haveI : Fact p.Prime := ⟨hdat.prime⟩
  haveI : CharP K p := hdat.charP
  obtain ⟨A, φ, hβ'eq⟩ := exists_uConjAut_mul_uFieldAut hdat hN hNq β'
  have hφ3 : φ ^ 3 = 1 := by
    have := congrArg (uFactor hdat hN hNq) hβ'3
    rw [map_pow, hβ'eq, uFactor_apply, map_one] at this
    exact this
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hφ3) with h1 | h1
  · exfalso
    apply hout
    have hφ1 : φ = 1 := orderOf_eq_one_iff.1 h1
    have hβ'A : β' = uConjAut hdat hn1 A := by rw [hβ'eq, hφ1, map_one, mul_one]
    rw [hβ'A]
    exact uConjAut_mem_innAutDerived hdat hN A (by rw [← hβ'A]; exact hβ'3)
  · exact ⟨A, φ, hβ'eq, h1⟩

theorem kd264I5_SU {K : Type} [Field K] [Finite K] {p f N : ℕ} (hdat : UnitaryFieldData p f K)
    (hN : 3 ≤ N) (hNq : ¬(N = 3 ∧ p ^ f = 2)) (h3q : 3 ∣ p ^ f + 1)
    (β : MulAut ↥(StatedSU N (p ^ f) K)) (hβ3 : β ^ 3 = 1)
    (hout : onCenterQuotient β ∉ innAutDerived
      (↥(StatedSU N (p ^ f) K) ⧸ Subgroup.center ↥(StatedSU N (p ^ f) K))) :
    ∃ E : Subgroup ↥(StatedSU N (p ^ f) K), E ≤ MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id _) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ (N - 1) := by
  have hn1 : 1 ≤ N := by omega
  haveI : NeZero N := ⟨by omega⟩
  haveI : Fact p.Prime := ⟨hdat.prime⟩
  haveI : CharP K p := hdat.charP
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [hdat.card, ← pow_mul, Nat.mul_comm]
  have hKe : Nat.card K = p ^ (2 * f) := hdat.card
  have hnq : (N, p ^ f) ≠ (3, 2) := fun h => hNq ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
  set bar : K ≃+* K := unitaryInvolution K p f with hbardef
  have hbar : IsUnitaryInvolution bar := isUnitaryInvolution_unitaryInvolution hK
  have hbarapp : ∀ x, bar x = x ^ p ^ f := fun x => unitaryInvolution_apply K p f x
  have hbb : ∀ x, bar (bar x) = x := hbar.invol
  have hS : StatedSU N (p ^ f) K = SUid bar N := (SUid_eq_statedSU hK N).symm
  have hperf : Group.IsPerfect ↥(StatedSU N (p ^ f) K) := isPerfect_statedSU hK hN hnq
  have hc : Subgroup.center ↥(StatedSU N (p ^ f) K) =
      (StatedScalars (Fin N) K).subgroupOf (StatedSU N (p ^ f) K) := by
    rw [hS]
    exact CFSG.ClassicalInvolution.Phan.center_SUid_eq hbar hN
  let e₀ : ↥(StatedSU N (p ^ f) K) ⧸ Subgroup.center ↥(StatedSU N (p ^ f) K) ≃*
      StatedProj (StatedSU N (p ^ f) K) := QuotientGroup.quotientMulEquivOfEq hc
  let β' : MulAut (StatedProj (StatedSU N (p ^ f) K)) := MulAut.congr e₀ (onCenterQuotient β)
  have hβ'mk : ∀ x : ↥(StatedSU N (p ^ f) K), β' (QuotientGroup.mk x) = QuotientGroup.mk (β x) := by
    intro x
    show e₀ (onCenterQuotient β (e₀.symm (QuotientGroup.mk x))) = _
    have h1 : e₀.symm (QuotientGroup.mk x) = QuotientGroup.mk x :=
      QuotientGroup.quotientMulEquivOfEq_mk hc.symm x
    rw [h1]
    have h2 : onCenterQuotient β (QuotientGroup.mk x) = QuotientGroup.mk (β x) :=
      onCenterQuotient_apply_mk β x
    rw [h2]
    exact QuotientGroup.quotientMulEquivOfEq_mk hc (β x)
  have hβ'3 : β' ^ 3 = 1 := by
    have h1 : (onCenterQuotient β) ^ 3 = 1 := by
      have := congrArg (centerQuotientHom ↥(StatedSU N (p ^ f) K)) hβ3
      rwa [map_pow, map_one] at this
    show (MulAut.congr e₀ (onCenterQuotient β)) ^ 3 = 1
    rw [← map_pow, h1, map_one]
  have hout' : β' ∉ innAutDerived (StatedProj (StatedSU N (p ^ f) K)) := by
    intro hmem
    apply hout
    have h2 : onCenterQuotient β = MulAut.congr e₀.symm β' := by
      refine MulEquiv.ext fun y => ?_
      simp [β', MulAut.congr_apply]
    rw [h2]
    exact (mem_innAutDerived_congr e₀.symm).2 hmem
  obtain ⟨A, φ, hβ'eq, hφord⟩ := exists_phi_of_outer_three hdat hN hNq β' hβ'3 hout'
  have hφ3 : φ ^ 3 = 1 := by rw [← hφord]; exact pow_orderOf_eq_one φ
  haveI := hperf
  have hβlift : β.toMonoidHom = uLift hdat A φ := by
    refine eq_of_central_displacement β.toMonoidHom (uLift hdat A φ) fun x => ?_
    have h1 : (QuotientGroup.mk (uLift hdat A φ x) : StatedProj (StatedSU N (p ^ f) K)) =
        QuotientGroup.mk (β x) := by
      rw [← hβ'mk x, hβ'eq]
      exact (uLift_proj hdat hn1 A φ x).symm
    rw [hc]
    exact QuotientGroup.eq.1 h1
  have hβ_coe : ∀ x : ↥(StatedSU N (p ^ f) K), ((β x : ↥(StatedSU N (p ^ f) K)) : GL (Fin N) K) =
      (A : GL (Fin N) K) * glMap φ (x : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹ := fun x =>
    congrArg (fun m : ↥(StatedSU N (p ^ f) K) →* ↥(StatedSU N (p ^ f) K) =>
      ((m x : ↥(StatedSU N (p ^ f) K)) : GL (Fin N) K)) hβlift
  have hodd : Odd (orderOf φ) := by rw [hφord]; decide
  have hcomm : ∀ x, φ (bar x) = bar (φ x) := fun x => by rw [hbarapp, hbarapp, map_pow]
  have hIso : IsIso bar (A : GL (Fin N) K) := isIso_of_mem_uU hdat hbb A.2
  have hcube : ∀ x : ↥(StatedSU N (p ^ f) K), (x : GL (Fin N) K) =
      normProd φ (A : GL (Fin N) K) 3 * (x : GL (Fin N) K) * (normProd φ (A : GL (Fin N) K) 3)⁻¹ := by
    intro x
    have h3 : (β ^ 3) x = x := by rw [hβ3]; rfl
    have h4 : ((β ^ 3) x : ↥(StatedSU N (p ^ f) K)) = β (β (β x)) := by
      simp [pow_succ, MulAut.mul_apply]
    have h5 : (((β (β (β x)) : ↥(StatedSU N (p ^ f) K))) : GL (Fin N) K) =
        (fun z : GL (Fin N) K => (A : GL (Fin N) K) * glMap φ z * (A : GL (Fin N) K)⁻¹)^[3]
          (x : GL (Fin N) K) := by
      rw [hβ_coe (β (β x)), hβ_coe (β x), hβ_coe x]
      rfl
    rw [iterate_twist_formula, hφ3, glMap_one] at h5
    rw [← h5, h4.symm, h3]
  have hNmem : normProd φ (A : GL (Fin N) K) 3 ∈ uU hdat N :=
    mem_uU_of_isIso hdat (hIso.normProd hcomm 3)
  have hone : uConjAut hdat hn1 ⟨normProd φ (A : GL (Fin N) K) 3, hNmem⟩ = 1 := by
    refine MulEquiv.ext fun z => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    have e : uConjAut hdat hn1 ⟨normProd φ (A : GL (Fin N) K) 3, hNmem⟩ (QuotientGroup.mk g) =
        QuotientGroup.mk ⟨_, uConjSU_mem hdat ⟨normProd φ (A : GL (Fin N) K) 3, hNmem⟩ g⟩ :=
      uConjAut_proj hdat hn1 _ g
    rw [e]
    show _ = QuotientGroup.mk g
    congr 1
    exact Subtype.ext (hcube g).symm
  obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff hdat hN ⟨normProd φ (A : GL (Fin N) K) 3, hNmem⟩).1 hone
  have hcs : Ai φ ((A : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) (orderOf φ) =
      ((c : Kˣ) : K) • (1 : Matrix (Fin N) (Fin N) K) := by
    rw [hφord, ← coe_normProd]
    have : (normProd φ (A : GL (Fin N) K) 3 : GL (Fin N) K) =
        Matrix.GeneralLinearGroup.scalar (Fin N) c := hc
    rw [this, Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  obtain ⟨u, hu, hfix⟩ := exists_fix_of_eq (p := p) (e := 2 * f) hdat.prime (by have := hdat.one_le; omega)
    hKe hbar hcomm hodd (StatedSU N (p ^ f) K) hS (A : GL (Fin N) K) hIso hcs β.toMonoidHom hβ_coe
  obtain ⟨j, hj2, hjcard, hform⟩ := exists_barFix_eq (p := p) (e := 2 * f) hdat.prime
    (by have := hdat.one_le; omega) hKe hbar hcomm hodd
  have hdvd := orderOf_dvd_of_card (p := p) (e := 2 * f) hdat.prime (by have := hdat.one_le; omega) hKe φ
  rw [hφord] at hj2 hdvd
  have hf3 : f = 3 * j := by omega
  have h3j : 3 ∣ p ^ j + 1 := by
    have h1 : p ^ f = (p ^ j) ^ 3 := by rw [hf3, ← pow_mul, mul_comm]
    rw [h1] at h3q
    have hx : (p ^ j) ^ 3 % 3 = (p ^ j) % 3 := by
      have := Nat.mod_lt (p ^ j) (by norm_num : 3 > 0)
      interval_cases hm : (p ^ j) % 3 <;> simp [Nat.pow_mod, hm]
    omega
  have hF0 := card_fixField (p := p) (e := 2 * f) hdat.prime (by have := hdat.one_le; omega) hKe φ
  haveI : Finite (fixField φ) :=
    CFSG.Semidihedral.FixedFieldData.finite_of_prime_power_card _ hdat.prime hF0
  have hbar0 : ∀ t : fixField φ, t ^ 3 = 1 → barFix φ bar hcomm hbar.invol t * t = 1 := by
    intro t ht
    rw [hform t, ← pow_succ]
    obtain ⟨m, hm⟩ := h3j
    rw [hm, pow_mul, ht, one_pow]
  have h3F : 3 ∣ Nat.card (fixField φ) - 1 := by
    rw [hjcard, sq_sub_one_eq _ (Nat.one_le_pow _ _ hdat.prime.pos)]
    exact Dvd.dvd.mul_right h3j _
  obtain ⟨D, hDabel, hDcard⟩ := exists_torus3 hbar0 h3F hn1
  let Φ : SUid (barFix φ bar hcomm hbar.invol) N →* ↥(StatedSU N (p ^ f) K) :=
    (MulEquiv.subgroupCongr hS.symm).toMonoidHom.comp (suFixEmb hcomm hbar.invol u hu)
  have hΦinj : Function.Injective Φ :=
    (MulEquiv.subgroupCongr hS.symm).injective.comp (suFixEmb_injective hcomm hbar.invol u hu)
  refine ⟨D.map Φ, ?_, isElemAbelian_map_of_injective Φ hDabel, ?_⟩
  · rintro _ ⟨x₀, hx₀, rfl⟩
    exact (hfix (Φ x₀)).2 ⟨x₀, rfl⟩
  · rw [Subgroup.card_map_of_injective hΦinj, hDcard]

end CFSG.LieType.SemisimpleCentralizers.HeldLang
