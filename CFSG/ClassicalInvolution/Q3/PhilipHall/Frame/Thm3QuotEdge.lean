module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3QuotBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent2Quot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecQuot

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3Quot

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Map

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {X : Subgroup Y} [X.Normal]

theorem mem_normalizer_of_normal (X : Subgroup Y) [X.Normal] (g : Y) :
    g ∈ Subgroup.normalizer (X : Set Y) := by
  rw [Subgroup.normalizer_eq_top]
  exact Subgroup.mem_top g

theorem natCard_map_of_isPGroup (hX : Odd (Nat.card X)) {A : Subgroup Y} (hA : IsPGroup 2 A) :
    Nat.card ↥(A.map (QuotientGroup.mk' X)) = Nat.card A := by
  have hAX : A ⊓ X = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd X hA le_rfl (odd_natCard_inf hX A)
  exact (Nat.card_congr (AscQuot.quotRestrictEquiv hAX).toEquiv).symm

theorem mem_RSet_map (hX : Odd (Nat.card X)) {R : Subgroup Y} (hR : R ∈ RSet Φ) :
    R.map (QuotientGroup.mk' X) ∈ RSet (quotFamily Φ X) := by
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  exact mem_RSet_of_isSylow2In (map_mem_quotFamily hJ) (isSylow2In_map_mk hX hRJ)

theorem mem_USet_map (hX : Odd (Nat.card X)) {U : Subgroup Y} (hU : U ∈ USet Φ) :
    U.map (QuotientGroup.mk' X) ∈ USet (quotFamily Φ X) := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨J, -, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have hR2 : IsPGroup 2 R := hRJ.2.1
  refine ⟨R.map (QuotientGroup.mk' X), mem_RSet_map hX hR, Subgroup.map_mono hUR, ?_, ?_⟩
  · let φ : ↥U →* ↥(U.map (QuotientGroup.mk' X)) :=
      ((QuotientGroup.mk' X).comp U.subtype).codRestrict (U.map (QuotientGroup.mk' X))
        fun x => ⟨x, x.2, rfl⟩
    have hφ : Function.Surjective φ := by
      rintro ⟨_, u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
    exact isCyclic_of_surjective φ hφ
  · have h1 := Subgroup.relIndex_mul_card U R
    rw [inf_eq_left.mpr hUR] at h1
    have h2 := Subgroup.relIndex_mul_card (U.map (QuotientGroup.mk' X))
      (R.map (QuotientGroup.mk' X))
    rw [inf_eq_left.mpr (Subgroup.map_mono hUR)] at h2
    have cU := natCard_map_of_isPGroup hX (hR2.to_le hUR)
    have cR := natCard_map_of_isPGroup hX hR2
    rw [cU, cR, ← h1] at h2
    have hU0 : 0 < Nat.card U := Nat.card_pos
    rw [Nat.eq_of_mul_eq_mul_right hU0 h2, hidx]

theorem exists_conj_normalizes_of_map (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X))
    {M P : Subgroup Y} (hM : M ∈ Φ) (hP : IsPGroup 2 P)
    (hPM : P.map (QuotientGroup.mk' X) ≤ Subgroup.normalizer
      ((M.map (QuotientGroup.mk' X) : Subgroup (Y ⧸ X)) : Set (Y ⧸ X))) :
    ∃ n ∈ X, P ≤ Subgroup.normalizer ((conjSub n M : Subgroup Y) : Set Y) :=
  TwinADescent2.exists_conj_normalizer_gen hΦ hX hM hP fun u hu => hPM ⟨u, hu, rfl⟩

theorem omegaNbr_map_iff (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X)) {L M : Subgroup Y}
    (hL : L ∈ Φ) (hM : M ∈ Φ)
    (hne : L.map (QuotientGroup.mk' X) ≠ M.map (QuotientGroup.mk' X)) :
    L.map (QuotientGroup.mk' X) ∈ omegaNbr (quotFamily Φ X) (M.map (QuotientGroup.mk' X)) ↔
      ∃ n ∈ X, L ∈ omegaNbr Φ (conjSub n M) := by
  have hΦ' : HypOmegaGen (quotFamily Φ X) := TwinEdge.hypOmegaGen_quotFamily_odd hΦ hX
  constructor
  · rintro ⟨-, -, Rb, hRb, hRbL, hRbN⟩
    have hRbsyl : IsSylow2In Rb (L.map (QuotientGroup.mk' X)) :=
      Sec6Gen.isSylow2In_of_mem_RSet_of_le hΦ' (map_mem_quotFamily hL) hRb hRbL
    obtain ⟨V, hVL, hV2, hVmap⟩ := TwinEdge.Quot.exists_lift_isPGroup hX hRbsyl.2.1 hRbL
    obtain ⟨R, hR, hVR⟩ := IsSylow2In.exists_ge hV2 hVL
    have hRmap : R.map (QuotientGroup.mk' X) = Rb := by
      refine hRbsyl.eq_of_le (hR.2.1.map _) (Subgroup.map_mono hR.1) ?_
      rw [← hVmap]
      exact Subgroup.map_mono hVR
    obtain ⟨n, hn, hRn⟩ := exists_conj_normalizes_of_map hΦ hX hM hR.2.1
      (by rw [hRmap]; exact hRbN)
    refine ⟨n, hn, hL, ?_, R, mem_RSet_of_isSylow2In hL hR, hR.1, hRn⟩
    intro h
    apply hne
    rw [h, OddQuot.map_conjSub_of_mem hn M]
  · rintro ⟨n, hn, -, -, R, hR, hRL, hRN⟩
    have hRs : IsSylow2In R L := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΦ hL hR hRL
    refine ⟨map_mem_quotFamily hL, hne, R.map (QuotientGroup.mk' X),
      mem_RSet_of_isSylow2In (map_mem_quotFamily hL) (isSylow2In_map_mk hX hRs),
      Subgroup.map_mono hRL, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    have := mk_mem_normalizer_map (N := X) (hRN hr)
    rwa [OddQuot.map_conjSub_of_mem hn M] at this

theorem omegaStarNbr_map_iff (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X)) {L M : Subgroup Y}
    (hL : L ∈ Φ) (hM : M ∈ Φ)
    (hne : L.map (QuotientGroup.mk' X) ≠ M.map (QuotientGroup.mk' X)) :
    L.map (QuotientGroup.mk' X) ∈ omegaStarNbr (quotFamily Φ X) (M.map (QuotientGroup.mk' X)) ↔
      ∃ n ∈ X, L ∈ omegaStarNbr Φ (conjSub n M) := by
  have hΦ' : HypOmegaGen (quotFamily Φ X) := TwinEdge.hypOmegaGen_quotFamily_odd hΦ hX
  constructor
  · intro h
    exact E187C.exists_conj_omegaStarNbr_of
      (fun hJ hUb hUbJ => TwinADescent2.exists_lift_USet_gen hΦ' hX hJ hUb hUbJ)
      (fun hU => Sec6Gen.isPGroup_of_mem_USet hΦ hU)
      (fun hK hU2 hUN => TwinADescent2.exists_conj_normalizer_gen hΦ hX hK hU2 hUN) hM hL h
  · rintro ⟨n, hn, -, -, U, hU, hUL, hUN⟩
    refine ⟨map_mem_quotFamily hL, hne, U.map (QuotientGroup.mk' X), mem_USet_map hX hU,
      Subgroup.map_mono hUL, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have := mk_mem_normalizer_map (N := X) (hUN hu)
    rwa [OddQuot.map_conjSub_of_mem hn M] at this

end Map

section Viol

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}

theorem mem_normalizer_of_mem_omegaStarNbr_gen (hΦ : HypOmegaGen Φ) {M J : Subgroup Y}
    (hJ : J ∈ omegaStarNbr Φ M) {j : Y} (hj : IsUniqueInvolution J j) :
    j ∈ Subgroup.normalizer (M : Set Y) := by
  obtain ⟨-, -, U, hU, hUJ, hUN⟩ := hJ
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΦ hU
  exact hUN (mem_of_isPGroup hj hUJ (Sec6Gen.isPGroup_of_mem_USet hΦ hU) (by omega))

theorem aViol_involution_ne (hΦ : HypOmegaGen Φ) {M J : Subgroup Y} {z j : Y} (hM : M ∈ Φ)
    (hv : AViol Φ M J z j) : z ≠ j := by
  rintro rfl
  exact hv.not_nbr (Q3CL.T3.twin_mem_omegaNbr hΦ hM hv.mem hv.ne hv.hzK hv.hzJ)

theorem aViol_involution_comm (hΦ : HypOmegaGen Φ) {M J : Subgroup Y} {z j : Y}
    (hv : AViol Φ M J z j) : z * j = j * z := by
  have h1 := hv.hzK.conj_eq (mem_normalizer_iff_conjSub_eq.mp
    (mem_normalizer_of_mem_omegaStarNbr_gen hΦ hv.star hv.hzJ))
  calc z * j = (j * z * j⁻¹) * j := by rw [h1]
    _ = j * z := by group

theorem aViol_mem_normalizer (hΦ : HypOmegaGen Φ) {M J : Subgroup Y} {z j : Y} (hM : M ∈ Φ)
    (hv : AViol Φ M J z j) : z ∈ Subgroup.normalizer (J : Set Y) :=
  mem_normalizer_of_mem_omegaStarNbr_gen hΦ (Q3T6.Mu.omegaStarNbr_symm hΦ hM hv.mem hv.star) hv.hzK

theorem map_ne_of_aViol (hΦ : HypOmegaGen Φ) {X : Subgroup Y} [X.Normal] (hX : Odd (Nat.card X))
    {M J : Subgroup Y} {z j : Y} (hM : M ∈ Φ) (hv : AViol Φ M J z j) :
    QuotientGroup.mk' X z ≠ QuotientGroup.mk' X j ∧
      J.map (QuotientGroup.mk' X) ≠ M.map (QuotientGroup.mk' X) := by
  have hzj := involution_map_ne hX hv.hzK.sq hv.hzJ.sq (aViol_involution_comm hΦ hv)
    (aViol_involution_ne hΦ hM hv)
  refine ⟨hzj, fun h => hzj ?_⟩
  have hzb := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hX M) hv.hzK
  have hjb := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hX J) hv.hzJ
  rw [h] at hjb
  exact hzb.eq hjb

end Viol

section NotNbr

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {X : Subgroup Y} [X.Normal]

theorem not_omegaNbr_map_of_aSet (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X)) {M J : Subgroup Y}
    (hM : M ∈ Φ) (hJ : J ∈ aSet Φ M) :
    J.map (QuotientGroup.mk' X) ∉ omegaNbr (quotFamily Φ X) (M.map (QuotientGroup.mk' X)) := by
  obtain ⟨z, j, hv⟩ := hJ
  intro hJb
  have hJΦ : J ∈ Φ := hv.mem
  obtain ⟨-, hne⟩ := map_ne_of_aViol hΦ hX hM hv
  obtain ⟨n, hn, hJn⟩ := (omegaNbr_map_iff hΦ hX hJΦ hM hne).mp hJb
  set J' : Subgroup Y := conjSub n⁻¹ J with hJ'def
  have hJ'Φ : J' ∈ Φ := hΦ.conjInvariant _ _ hJΦ
  have hJJ' : conjSub n J' = J := conjSub_conjSub_inv n J
  have hJ' : J' ∈ omegaNbr Φ M := by
    have := omegaNbr_conj hΦ.conjInvariant hJn n⁻¹
    rwa [conjSub_inv_conjSub, ← hJ'def] at this
  have hzJ' : z ∈ Subgroup.normalizer (J' : Set Y) := by
    obtain ⟨-, -, R, hR, hRM, hRN⟩ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ hM hJ'Φ hJ'
    exact hRN (Sec6Gen.mem_of_isSylow2In hv.hzK
      (Sec6Gen.isSylow2In_of_mem_RSet_of_le hΦ hM hR hRM))
  have hzJ : z ∈ Subgroup.normalizer (J : Set Y) := aViol_mem_normalizer hΦ hM hv
  set H : Subgroup Y := X ⊓ Subgroup.normalizer (J' : Set Y) with hHdef
  have hHodd : Odd (Nat.card H) := hX.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hU2 : IsPGroup 2 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_mul_self_eq_one hv.hzK.sq hv.hzK.ne_one
  have hzH : z ∈ Subgroup.normalizer (H : Set Y) :=
    Sec6Gen.mem_normalizer_inf' (mem_normalizer_of_normal X z)
      (Subgroup.le_normalizer hzJ')
  have hUJ : Subgroup.zpowers z ≤ Subgroup.normalizer (J : Set Y) :=
    Subgroup.zpowers_le.mpr hzJ
  have hUJ' : Subgroup.zpowers z ≤ Subgroup.normalizer (J' : Set Y) :=
    Subgroup.zpowers_le.mpr hzJ'
  have hUm : ∀ u ∈ Subgroup.zpowers z, n⁻¹ * (u * n * u⁻¹) ∈ H := by
    intro u hu
    refine Subgroup.mem_inf.mpr ⟨X.mul_mem (X.inv_mem hn) (‹X.Normal›.conj_mem n hn u), ?_⟩
    rw [mem_normalizer_iff_conjSub_eq]
    have h1 : conjSub u⁻¹ J' = J' :=
      mem_normalizer_iff_conjSub_eq.mp ((Subgroup.normalizer _).inv_mem (hUJ' hu))
    have h2 : conjSub u J = J := mem_normalizer_iff_conjSub_eq.mp (hUJ hu)
    rw [conjSub_mul, conjSub_mul, conjSub_mul, h1, hJJ', h2, hJ'def]
  obtain ⟨h, hh, hzc⟩ := exists_fixed_mem_coset hHodd hU2 (Subgroup.zpowers_le.mpr hzH) hUm
  have hcX : n * h ∈ X := X.mul_mem hn hh.1
  have hcJ : conjSub (n * h) J' = J := by
    rw [conjSub_mul, mem_normalizer_iff_conjSub_eq.mp hh.2, hJJ']
  have hcz : n * h ∈ Subgroup.centralizer ({z} : Set Y) := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hzc (Subgroup.mem_zpowers z))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact this.symm
  have hcM : conjSub (n * h) M = M := mem_normalizer_iff_conjSub_eq.mp
    (le_normalizer_of_le_centralizer hΦ hX hM hv.hzK ⟨hcX, hcz⟩)
  have := omegaNbr_conj hΦ.conjInvariant hJ' (n * h)
  rw [hcJ, hcM] at this
  exact hv.not_nbr this

end NotNbr

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3Quot
