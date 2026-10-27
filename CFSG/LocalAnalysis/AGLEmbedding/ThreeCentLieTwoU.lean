module

public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoUBlocks
import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSmall
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBasic

public section

namespace CFSG.AGLEmbedding

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {n : ℕ}

theorem pow_three_eq_one_of_mem_normOneScalars (hK : UnitaryFieldData 2 1 K)
    {z : gramSU hK (idGram K n)} (hz : z ∈ normOneScalars hK (gramSU hK (idGram K n)) n) :
    z ^ 3 = 1 := by
  obtain ⟨c, -, -, hc⟩ := hz
  have hc3 : c ^ 3 = 1 := Units.ext (by
    simpa using pow_three_eq_one_of_card_eq_four (by rw [hK.card]; norm_num) c.ne_zero)
  apply Subtype.ext
  rw [Subgroup.coe_pow, hc, ← map_pow, hc3, map_one, Subgroup.coe_one]

theorem commute_of_mem_normOneScalars (hK : UnitaryFieldData 2 1 K)
    {z : gramSU hK (idGram K n)} (hz : z ∈ normOneScalars hK (gramSU hK (idGram K n)) n)
    (g : gramSU hK (idGram K n)) : Commute z g := by
  obtain ⟨c, -, -, hc⟩ := hz
  exact Subtype.ext (by
    change (z : GL (Fin n) K) * g = g * z
    rw [hc]
    exact (commute_scalar c (g : GL (Fin n) K)).eq.symm)

theorem exists_perfect_fixed_of_quasisimple (hK : UnitaryFieldData 2 1 K)
    (A : primeFormUnitary hK (idGram K n))
    {L : Subgroup (LinearMap.GeneralLinearGroup K (Fin n → K))} (hL : CFSG.IsQuasisimple L)
    (hLC : L ≤ unitaryCentralizer (idForm hK n) (toLinU hK n A))
    (hdet : ∀ g ∈ L, LinearMap.det (g : Module.End K (Fin n → K)) = 1) :
    ∃ Q : Subgroup (primeFormP hK (idGram K n)), ⁅Q, Q⁆ = Q ∧
      (∀ y ∈ Q, primeFormConjHom hK (idGram K n) A y = y) ∧ Q ≠ ⊥ := by
  set ι : gramSU hK (idGram K n) →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
    (Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃*
      LinearMap.GeneralLinearGroup K (Fin n → K)).toMonoidHom.comp
      (gramSU hK (idGram K n)).subtype
  have hι : Function.Injective ι := fun _ _ e =>
    Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective e)
  have hLι : L ≤ ι.range := fun g hg => by
    have hgU : g ∈ sesqSpecialUnitaryGroup (idForm hK n) :=
      mem_sesqSpecialUnitaryGroup.mpr ⟨(mem_unitaryCentralizer.mp (hLC hg)).1, hdet g hg⟩
    refine ⟨⟨Matrix.GeneralLinearGroup.toLin.symm g, ?_⟩, ?_⟩
    · rw [← toLin_mem_sesqSpecialUnitaryGroup_iff, MulEquiv.apply_symm_apply]
      exact hgU
    · exact MulEquiv.apply_symm_apply (Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃*
        LinearMap.GeneralLinearGroup K (Fin n → K)) g
  set L' := L.comap ι
  have hL'map : L'.map ι = L := Subgroup.map_comap_eq_self hLι
  have hL' : CFSG.IsQuasisimple L' := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((Subgroup.equivMapOfInjective L' ι hι).trans (MulEquiv.subgroupCongr hL'map)).symm hL
  set Z := normOneScalars hK (gramSU hK (idGram K n)) n
  refine ⟨L'.map (QuotientGroup.mk' Z), by
    rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hL'.1], ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [QuotientGroup.mk'_apply, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    have hc := (mem_unitaryCentralizer.mp (hLC hs)).2
    have h1 : ι s * toLinU hK n A = toLinU hK n A * ι s := Units.ext hc.eq
    have h2 : (s : GL (Fin n) K) * A = A * s := Matrix.GeneralLinearGroup.toLin.injective (by
      rw [map_mul, map_mul]
      exact h1)
    change (A : GL (Fin n) K) * s * (A : GL (Fin n) K)⁻¹ = s
    rw [← h2, mul_inv_cancel_right]
  · intro hQ
    have hle : L' ≤ Z := by
      intro s hs
      have h1 : (QuotientGroup.mk' Z) s ∈ (⊥ : Subgroup (primeFormP hK (idGram K n))) :=
        hQ ▸ Subgroup.mem_map_of_mem _ hs
      rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hcomm : ⁅L', L'⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro u hu v _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (commute_of_mem_normOneScalars hK (hle hu) v).eq
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hL'
    rw [Subgroup.isPerfect_iff.mp hL'.1] at hcomm
    rw [hcomm] at hnt
    exact not_nontrivial _ hnt

theorem exists_primeFormConjHom_eq (hK : UnitaryFieldData 2 1 K) (hn : 4 ≤ n)
    {α : MulAut (primeFormP hK (idGram K n))} (hα3 : α ^ 3 = 1) :
    ∃ A : primeFormUnitary hK (idGram K n), primeFormConjHom hK (idGram K n) A = α := by
  have hC := isPrimeFormGram_idGram (K := K) (n := n)
  have hq : ¬(n = 3 ∧ 2 ^ 1 = 2) := fun h => by omega
  have : Finite K := hK.finite
  set φ := primeFormFieldFactor hK hC (by omega) hq α
  have hφ3 : φ ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hcard := (card_ringAut_and_isCyclic hK.prime K hK.card).1
  have hφ : φ = 1 := by
    have h1 : orderOf φ ∣ 3 := orderOf_dvd_of_pow_eq_one hφ3
    have h2 : orderOf φ ∣ 2 * 1 := hcard ▸ orderOf_dvd_natCard φ
    have h3 : orderOf φ = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num) h1 h2
    exact orderOf_eq_one_iff.mp h3
  have hαD : α ∈ primeFormD hK (idGram K n) := by
    rw [← ker_primeFormFieldFactor hK hC (by omega) hq]
    exact hφ
  exact hαD

theorem exists_scalar_of_primeFormConjHom_pow (hK : UnitaryFieldData 2 1 K) (hn : 4 ≤ n)
    {A : primeFormUnitary hK (idGram K n)} (hA : primeFormConjHom hK (idGram K n) (A ^ 3) = 1) :
    ∃ c : Kˣ, ((A ^ 3 : primeFormUnitary hK (idGram K n)) : GL (Fin n) K) =
      Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  have hq : ¬(n = 3 ∧ 2 ^ 1 = 2) := fun h => by omega
  have key := (unitary_prime_form_full_semilinear_realization hK
    (isPrimeFormGram_idGram (K := K) (n := n)) (by omega) hq).2.2.1 ⟨A ^ 3, 1⟩
  rw [primeFormPsi_apply, map_one, mul_one, hA] at key
  obtain ⟨-, c, -, hc⟩ := key.mp rfl
  exact ⟨c, hc⟩

theorem threeAutFixedTwoThree_primeFormP_two (hK : UnitaryFieldData 2 1 K) (hn : 4 ≤ n) :
    ThreeAutFixedTwoThree (primeFormP hK (idGram K n)) := by
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ 1 = 2) := fun h => by omega
  obtain ⟨⟨eT⟩, -⟩ := unitary_full_diagonal_outer_order hK hn3 hq
  let e : primeFormP hK (idGram K n) ≃* StatedProj (StatedSU n (2 ^ 1) K) :=
    eT.trans (unitaryPSUEquiv hK (by omega))
  have : Finite K := hK.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK.card]; norm_num
  have hnq : (n, 2 ^ 1) ≠ (3, 2) := fun h => by
    have := congrArg Prod.fst h
    simp only at this
    omega
  have : IsSimpleGroup (StatedProj (StatedSU n (2 ^ 1) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 1 hK4 n hn3 hnq
  have : Group.IsPerfect (StatedSU n (2 ^ 1) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK4 hn3 hnq
  have : Group.IsPerfect (StatedProj (StatedSU n (2 ^ 1) K)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have : IsSimpleGroup (primeFormP hK (idGram K n)) := e.isSimpleGroup
  have : Group.IsPerfect (primeFormP hK (idGram K n)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine threeAutFixedTwoThree_of_fixed_prime center_eq_bot_of_simple_of_perfect ?_
  intro α hα3 hfree y hαy p hp hp5 hyp
  by_contra hy1
  obtain ⟨A, rfl⟩ := exists_primeFormConjHom_eq hK hn hα3
  obtain ⟨c, hc⟩ := exists_scalar_of_primeFormConjHom_pow hK hn (by rw [map_pow, hα3])
  have hx := toLinU_mem (h := hK) A
  have hxA : ((toLinU hK n A) ^ 3 : LinearMap.GeneralLinearGroup K (Fin n → K)) =
      Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.scalar (Fin n) c) := by
    rw [← map_pow, toLinU_apply, hc]
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)
  by_cases hc1 : c = 1
  · have hx3 : toLinU hK n A ^ 3 = 1 := by rw [hxA, hc1, map_one, map_one]
    obtain ⟨Y, hY, hYp⟩ := exists_lift_cube_of_pow_eq_one
      (fun z hz => pow_three_eq_one_of_mem_normOneScalars hK hz) hyp
    have hy3 : y ^ 3 ≠ 1 := fun h3 => hy1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      hcop (orderOf_dvd_of_pow_eq_one hyp) (orderOf_dvd_of_pow_eq_one h3)))
    have hY1 : Y ≠ 1 := fun h => hy3 (by rw [← hY, h, QuotientGroup.mk_one])
    have h1 : primeFormConjHom hK (idGram K n) A (Y : primeFormP hK (idGram K n)) = Y := by
      rw [hY, map_pow, hαy]
    rw [primeFormConjHom_mk, QuotientGroup.eq] at h1
    set W : gramSU hK (idGram K n) :=
      ⟨A * Y * (A : GL (Fin n) K)⁻¹, conj_mem_gramSU hK (idGram K n) A.2 Y.2⟩ with hWdef
    have hWp : W ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      change ((A : GL (Fin n) K) * Y * (A : GL (Fin n) K)⁻¹) ^ p = 1
      rw [conj_pow, ← Subgroup.coe_pow, hYp, Subgroup.coe_one, mul_one, mul_inv_cancel])
    have hYW : Y = W * (W⁻¹ * Y) := by group
    have hzp : (W⁻¹ * Y) ^ p = 1 := by
      have h2 : Y ^ p = (W * (W⁻¹ * Y)) ^ p := by rw [← hYW]
      rw [(commute_of_mem_normOneScalars hK h1 W).symm.mul_pow, hWp, one_mul, hYp] at h2
      exact h2.symm
    have hz1 : W⁻¹ * Y = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hzp)
      (orderOf_dvd_of_pow_eq_one (pow_three_eq_one_of_mem_normOneScalars hK h1)))
    have hAY : (A : GL (Fin n) K) * Y = Y * A := by
      have h3 : (W : GL (Fin n) K) = Y := congrArg Subtype.val (inv_mul_eq_one.mp hz1)
      change (A : GL (Fin n) K) * Y * (A : GL (Fin n) K)⁻¹ = Y at h3
      calc (A : GL (Fin n) K) * Y = A * Y * (A : GL (Fin n) K)⁻¹ * A := by group
        _ = Y * A := by rw [h3]
    set yL := Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K)
    have hyL : yL ∈ unitaryCentralizer (idForm hK n) (toLinU hK n A) := by
      refine mem_unitaryCentralizer.mpr ⟨sesqSpecialUnitaryGroup_le _
        ((toLin_mem_sesqSpecialUnitaryGroup_iff hK (idGram K n) Y).mpr Y.2), ?_⟩
      have h4 : yL * toLinU hK n A = toLinU hK n A * yL := by
        rw [toLinU_apply, ← map_mul, ← map_mul, hAY]
      exact congrArg Units.val h4
    have hyLp : yL ^ p = 1 := by rw [← map_pow, ← Subgroup.coe_pow, hYp, Subgroup.coe_one, map_one]
    have hyL1 : yL ≠ 1 := fun h => hY1 (Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective
      (h.trans (map_one _).symm)))
    obtain ⟨L, hL, hLC, hdet⟩ := exists_quasisimple_of_cube_eq_one hK hx hx3 hyL hp hp5 hyLp hyL1
    obtain ⟨Q, hQ, hQfix, hQ1⟩ := exists_perfect_fixed_of_quasisimple hK A hL hLC hdet
    exact hQ1 (hfree Q hQ hQfix)
  · have hx3 : ((toLinU hK n A : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) ^ 3 = algebraMap K _ (c : K) := by
      rw [← Units.val_pow_eq_pow_val, hxA]
      ext v i
      simp [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVec, dotProduct,
        Matrix.diagonal_apply]
    obtain ⟨L, hL, hLC, hdet⟩ := exists_quasisimple_of_cube_eq_scalar hK hn hx c.ne_zero
      (fun h => hc1 (Units.ext h)) hx3
    obtain ⟨Q, hQ, hQfix, hQ1⟩ := exists_perfect_fixed_of_quasisimple hK A hL hLC hdet
    exact hQ1 (hfree Q hQ hQfix)

theorem threeAutFixedTwoThree_of_model_psu_two {X : Type} [Group X]
    (h : StatedClassicalModel X .PSU n 2 1) : ThreeAutFixedTwoThree X := by
  obtain ⟨⟨hpp, hf, hn, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hn4 : 4 ≤ n := by
    by_contra h4
    exact hne (by rw [show n = 3 by omega]; rfl)
  have hU : UnitaryFieldData 2 1 K := ⟨hpp, hf, by rw [hK]; ring⟩
  obtain ⟨⟨eT⟩, -⟩ := unitary_full_diagonal_outer_order hU (by omega)
    (fun h => by omega : ¬(n = 3 ∧ 2 ^ 1 = 2))
  exact ThreeAutFixedTwoThree.of_mulEquiv
    (e.trans ((unitaryPSUEquiv hU (by omega)).symm.trans eT.symm))
    (threeAutFixedTwoThree_primeFormP_two hU hn4)

theorem threeAutFixedTwoThree_lie_twistedA_two (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ (r : ℕ) (q : TauCeti.PrimePower), q.card = 2 ∧ d.1 = .twistedA r q) :
    ThreeAutFixedTwoThree (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  obtain ⟨r, q, hq, hd⟩ := hd
  simp only at hd
  subst hd
  obtain ⟨hp2, hf⟩ := ParabHub.primePower_eq_of_card_eq Nat.prime_two hq
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _)
  rw [hp2, hf] at h
  exact threeAutFixedTwoThree_of_model_psu_two h

end CFSG.AGLEmbedding
