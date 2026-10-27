module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpBasic
public import CFSG.LieType.Steinberg.CentralExt.SymplecticPerfect
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAutU
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveKBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.RankOne (normal_of_isComponent_of_twoSmall
  quotientCenterAutHom quotientCenterAutHom_injective card_le_of_isPGroup_of_card_dvd
  card_eq_card_inf_centralizer_mul_card_range)

theorem card_le_sixteen_of_twoFree {J : Type} [Group J] [Finite J] {τ : MulAut J}
    {D : Subgroup (fixedSubgroup τ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 1) (h2 : F4Pilot.FixedCentralizerTwoFree τ D)
    {Q : Subgroup (fixedSubgroup τ)} (hQ : IsPGroup 2 Q) : Nat.card Q ≤ 16 := by
  have hN : D.Normal :=
    normal_of_isComponent_of_twoSmall hD (fixedCentralizerTwoSmall_of_twoFree' h2)
  have hQN : Q ≤ normalizer (D : Set (fixedSubgroup τ)) := by
    rw [normalizer_eq_top_iff.mpr hN]
    exact le_top
  have hcard := card_eq_card_inf_centralizer_mul_card_range hQN
  have h1 : Nat.card (Q ⊓ centralizer (D : Set (fixedSubgroup τ)) : Subgroup _) = 1 := by
    set U : Subgroup (fixedSubgroup τ) := Q ⊓ centralizer (D : Set (fixedSubgroup τ)) with hU
    have hUb := h2 (U.map (fixedSubgroup τ).subtype) ((hQ.to_le inf_le_left).map _) ?_
      (map_subtype_le U)
    · have hc : Nat.card (U.map (fixedSubgroup τ).subtype) = Nat.card U :=
        card_map_of_injective (fixedSubgroup τ).subtype_injective
      rw [hUb, card_bot] at hc
      exact hc.symm
    · rintro _ ⟨u, hu, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨d, hd, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.mp (mem_inf.mp hu).2 d hd)
  set R := (D.normalizerMonoidHom.comp (inclusion hQN)).range with hR
  have hRp : IsPGroup 2 R := hQ.of_surjective _
    (D.normalizerMonoidHom.comp (inclusion hQN)).rangeRestrict_surjective
  have : Group.IsPerfect D := hD.1.1
  have hA := card_mulAut_of_lieModel_PSL_three_two hDm
  have : Finite (MulAut (D ⧸ center D)) := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  have h3 : Nat.card (R.map (quotientCenterAutHom D)) ≤ 16 :=
    card_le_of_isPGroup_of_card_dvd (hRp.map _) (u := 21) (by decide) (by norm_num)
      (by rw [hA])
  rw [card_map_of_injective quotientCenterAutHom_injective] at h3
  rw [hcard, h1, one_mul]
  exact h3

theorem not_thirtyTwo_dvd_of_twoFree {J : Type} [Group J] [Finite J] {τ : MulAut J}
    {D : Subgroup (fixedSubgroup τ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 1) (h2 : F4Pilot.FixedCentralizerTwoFree τ D) :
    ¬ 32 ∣ Nat.card (fixedSubgroup τ) := by
  intro h32
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := fixedSubgroup τ) 2 (n := 5)
    (by norm_num; exact h32)
  have h1 := card_le_sixteen_of_twoFree hD hDm h2 (IsPGroup.of_card hQ)
  rw [hQ] at h1
  norm_num at h1

namespace SevenList

theorem mulAut_congr_mem_range_conj {J J' : Type} [Group J] [Group J'] (e : J ≃* J')
    {τ : MulAut J} (hτ : τ ∈ (MulAut.conj : J →* MulAut J).range) :
    MulAut.congr e τ ∈ (MulAut.conj : J' →* MulAut J').range := by
  obtain ⟨s, rfl⟩ := hτ
  exact ⟨e s, (mulAut_congr_conj e s).symm⟩

open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient in
theorem card_fixed_onQuotient_eq {X : Type*} [Group X] [Finite X] (Z : Subgroup X) [Z.Normal]
    (hZ : Z ≤ center X) (hZ2 : Nat.card Z = 2) (ψ : MulAut X) (hinv : Z.map ψ.toMonoidHom = Z)
    {h : X} (hhZ : h⁻¹ * ψ h ∈ Z) (hh : ψ h ≠ h) :
    Nat.card (fixedSubgroup (onQuotient Z ψ hinv)) = Nat.card (fixedSubgroup ψ) := by
  have hhN : h ∈ fixedPreimage Z ψ hinv := (mem_fixedPreimage_iff Z ψ hinv h).mpr hhZ
  have hrange : (displacement Z ψ hinv hZ).range = ⊤ := by
    have hne : (displacement Z ψ hinv hZ).range ≠ ⊥ := by
      intro hbot
      have h1 : displacement Z ψ hinv hZ ⟨h, hhN⟩ ∈ (displacement Z ψ hinv hZ).range :=
        ⟨_, rfl⟩
      rw [hbot, mem_bot] at h1
      exact hh ((displacement_eq_one_iff Z ψ hinv hZ ⟨h, hhN⟩).mp h1)
    have hdvd : Nat.card (displacement Z ψ hinv hZ).range ∣ 2 :=
      hZ2 ▸ card_subgroup_dvd_card _
    have h2 : Nat.card (displacement Z ψ hinv hZ).range = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact absurd (card_eq_one.mp h1) hne
      · exact h1
    exact eq_top_of_card_eq _ (h2.trans hZ2.symm)
  have hN1 : Nat.card (fixedPreimage Z ψ hinv) = Nat.card (fixedSubgroup ψ) * 2 := by
    rw [← Subgroup.card_ker_mul_card_range (displacement Z ψ hinv hZ), hrange, card_top, hZ2,
      displacement_kernel]
    congr 1
    exact Nat.card_congr (subgroupOfEquivOfLe (fixed_le_fixedPreimage Z ψ hinv)).toEquiv
  have hker : (preimageProjection Z ψ hinv).ker = Z.subgroupOf (fixedPreimage Z ψ hinv) := by
    ext x
    change preimageProjection Z ψ hinv x = 1 ↔ (x : X) ∈ Z
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
    · intro hx
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hx)
  have hN2 : Nat.card (fixedPreimage Z ψ hinv) =
      2 * Nat.card (fixedSubgroup (onQuotient Z ψ hinv)) := by
    rw [← Subgroup.card_ker_mul_card_range (preimageProjection Z ψ hinv),
      MonoidHom.range_eq_top.mpr (preimageProjection_surjective Z ψ hinv), card_top, hker,
      ← hZ2]
    congr 1
    exact Nat.card_congr (subgroupOfEquivOfLe (central_le_fixedPreimage Z ψ hinv)).toEquiv
  omega

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher in
theorem card_fixed_conjAut_eq {r : ℕ} {K : Type} [Field K] [Finite K] (A : gsp r K)
    {h : StatedSp r K} (hhZ : h⁻¹ * conjSp r K A h ∈ spScalars r K)
    (hne : conjSp r K A h ≠ h) :
    Nat.card (fixedSubgroup (conjAut r K A)) = Nat.card (fixedSubgroup (conjSp r K A)) := by
  have hinv := map_eq_of_forall_mem (conjSp r K) (spScalars r K)
    (fun A _ hz => conjSp_mem_spScalars A hz) A
  have hZ2 : Nat.card (spScalars r K) = 2 := by
    have hle : Nat.card (spScalars r K) ≤ 2 :=
      LieType.Steinberg.card_statedScalars_subgroupOf_statedSp_le_two r K
    have hne1 : Nat.card (spScalars r K) ≠ 1 := by
      intro h1
      have h2 : h⁻¹ * conjSp r K A h ∈ (⊥ : Subgroup (StatedSp r K)) := card_eq_one.mp h1 ▸ hhZ
      rw [mem_bot, inv_mul_eq_one] at h2
      exact hne h2.symm
    have hpos : 0 < Nat.card (spScalars r K) := Nat.card_pos
    omega
  exact card_fixed_onQuotient_eq (spScalars r K) spScalars_le_center hZ2 (conjSp r K A) hinv
    hhZ hne

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag in
theorem conj_proj_eq_conjAut {r : ℕ} {K : Type} [Field K] (g : StatedSp r K) :
    MulAut.conj (proj r K g) =
      conjAut r K ⟨(g : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp g.2⟩ := by
  refine MulEquiv.ext fun t => ?_
  obtain ⟨y, rfl⟩ := proj_surjective (r := r) (K := K) t
  rw [MulAut.conj_apply]
  change _ = proj r K (conjSp r K _ y)
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag in
theorem conjAut_not_mem_range_conj {r : ℕ} [NeZero r] {K : Type} [Field K] [Finite K]
    (A : gsp r K) (hsq : ∀ m : K, m ^ 2 ≠ (multiplierUnit A : K)) :
    conjAut r K A ∉ (MulAut.conj : StatedProj (StatedSp r K) →* _).range := by
  rintro ⟨x, hx⟩
  obtain ⟨g, rfl⟩ := proj_surjective (r := r) (K := K) x
  rw [conj_proj_eq_conjAut] at hx
  have h1 : conjAut r K ((⟨g, statedSp_le_gsp g.2⟩ : gsp r K)⁻¹ * A) = 1 := by
    rw [map_mul, map_inv, hx, inv_mul_cancel]
  obtain ⟨c, hc⟩ := (ComponentClassification.Burgoyne.Sp.conjAut_eq_one_iff
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)) _).mp h1
  apply hsq c
  have hA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((c : K) • 1) := by
    have h2 : (A : GL (Fin r ⊕ Fin r) K) = (g : GL (Fin r ⊕ Fin r) K) *
        Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
      rw [← hc]
      simp
    rw [h2, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
    rfl
  have hμ := multiplierUnit_spec A
  rw [hA] at hμ
  have hg : Matrix.transpose
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      formJ r K * ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      formJ r K :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp g.2
  have h3 : ((c : K) ^ 2) • formJ r K = (multiplierUnit A : K) • formJ r K := by
    rw [sq, ← hμ, Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
    rw [hg]
  exact smul_formJ_injective r h3

theorem not_isSquare_neg_one {K : Type} [Field K] [Finite K] (hK : Nat.card K = 7) :
    ¬ IsSquare (-1 : K) := by
  have : Fintype K := Fintype.ofFinite K
  rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hK]
  decide

theorem sq_ne_neg_sq {K : Type} [Field K] [Finite K] (hK : Nat.card K = 7) {l : K} (hl : l ≠ 0)
    (m : K) : m ^ 2 ≠ -(l ^ 2) := by
  intro h
  apply not_isSquare_neg_one hK
  refine ⟨m / l, ?_⟩
  rw [div_mul_div_comm, ← sq, ← sq, h, neg_div, div_self (pow_ne_zero 2 hl)]

theorem ringEquiv_eq_one {K : Type} [Field K] [Finite K] (hK : Nat.card K = 7) (σ : K ≃+* K) :
    σ = 1 := by
  have : Fintype K := Fintype.ofFinite K
  let e := ZMod.ringEquivOfPrime K (by norm_num : (7 : ℕ).Prime)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have h1 : (σ : K →+* K).comp (e : ZMod 7 →+* K) = (e : ZMod 7 →+* K) := Subsingleton.elim _ _
  refine RingEquiv.ext fun x => ?_
  have h2 := congrArg (fun φ : ZMod 7 →+* K => φ (e.symm x)) h1
  simpa using h2

end SevenList

end CFSG.SeitzReduction.LinearPilot
