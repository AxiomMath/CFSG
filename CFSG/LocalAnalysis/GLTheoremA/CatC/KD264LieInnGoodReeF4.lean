module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodInner
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.Main
public import CFSG.Mathlib.Arithmetic.PowFourSubOne
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4ThreeAux.Faithful
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.LieType.Ree CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.LargeReeOrder
open CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4ThreeAux
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.KLR
open CFSG.RankThree.PartOne.K1214
open CFSG.LieType.SteinbergBR

section ExistsSylow


theorem exists_sylowShape_and_reePlane {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] {a : ℕ} (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hdvd : p ∣ (2 ^ (2 * a + 1)) ^ 4 - 1) :
    (∃ e, SylowShape p 2 e (ReeTag.F4.reeGamma K a)) ∧ Nonempty (ReePlane K a p) := by
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three (by omega) (by omega)
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have hle : 2 ^ (a + 1) ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases dvd_cases_of_dvd_pow_four_sub_one hp hdvd with h | h | h
  · have hmM : (p : ℤ) ∣ 2 ^ (2 * a + 1) - 1 := by
      exact_mod_cast int_dvd_sub_one' hq1 h
    exact ⟨⟨_, sylowShape_ree_phi1 hK hp hp5 h⟩, exists_plane_phi1 hK hp hp3 hmM⟩
  · have hmM : (p : ℤ) ∣ 2 ^ (2 * a + 1) + 1 := by
      exact_mod_cast Int.natCast_dvd_natCast.2 h
    exact ⟨⟨_, sylowShape_ree_phi2 hK hp hp5 h⟩, exists_plane_phi2 hK hp hp3 hmM⟩
  · rcases dvd_phi4_cases hp hp3 h with ⟨h1, -⟩ | ⟨h1, -⟩
    · have hmM : (p : ℤ) ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1 := by
        exact_mod_cast Int.natCast_dvd_natCast.2 h1
      exact ⟨⟨_, sylowShape_ree_phi4 hK hp hp5 h⟩, exists_plane_phi4p hK hp hp3 hmM⟩
    · have hmM : (p : ℤ) ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 := by
        exact_mod_cast int_dvd_sub_add_one' hle h1
      exact ⟨⟨_, sylowShape_ree_phi4 hK hp hp5 h⟩, exists_plane_phi4m hK hp hp3 hmM⟩

private theorem exists_good_of_reePlane_reeGamma_F4 {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : 3 < p)
    (hsh : ∃ e, SylowShape p 2 e (ReeTag.F4.reeGamma K a)) (P : ReePlane K a p)
    {E : Subgroup (ReeTag.F4.reeGamma K a)} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) :
    ∃ x ∈ E, x ≠ 1 ∧ ∃ P' : Subgroup (ReeTag.F4.reeGamma K a),
      P' ≤ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧ ⁅P', P'⁆ = P' ∧
        p ∣ Nat.card P' := by
  classical
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨γ, hγ⟩ := exists_conj_plane hp hp2 hsh P E (fun x hx => hE.2 x hx) hcard
  have hroot : (rootFinset ReeTag.F4.tag).Nonempty := by
    refine Finset.card_pos.mp ?_
    rw [card_rootFinset]
    decide
  obtain ⟨β, hβ⟩ := hroot
  obtain ⟨z, hz1, hzker⟩ := exists_planeElt_kernel hp hp2 P hβ
  have hne : rootCharKernel (expTuple (z.1 : (AlgebraicClosure K)ˣ)
      (z.2 : (AlgebraicClosure K)ˣ) P.U) ≠ ∅ :=
    Set.nonempty_iff_ne_empty.1 ⟨β, hzker⟩
  obtain ⟨A, Sg, hd⟩ := plane_layer hK hp hp3 P hz1 hne
  have hquasi : CFSG.IsQuasisimple Sg := (layerType_props ha hK hd.2.2.2.2.2).1
  have hpdvd : p ∣ Nat.card Sg := by
    by_contra h
    exact plane_layer_dvd ha hK hp hp3 P hne hd ((hp.coprime_iff_not_dvd).2 h)
  have hpsi1 : P.Ψ z ≠ 1 := fun h => hz1 (P.Ψinj (by simpa using h))
  refine ⟨γ * P.Ψ z * γ⁻¹, ?_, ?_, Sg.map (MulAut.conj γ).toMonoidHom, ?_, ?_, ?_⟩
  · rw [hγ]
    exact Subgroup.mem_map_of_mem (MulAut.conj γ).toMonoidHom ⟨z, rfl⟩
  · intro h1
    apply hpsi1
    calc P.Ψ z = γ⁻¹ * (γ * P.Ψ z * γ⁻¹) * γ := by group
      _ = γ⁻¹ * 1 * γ := by rw [h1]
      _ = 1 := by group
  · rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hsC : s ∈ Subgroup.centralizer ({P.Ψ z} : Set (ReeTag.F4.reeGamma K a)) := by
      rw [← hd.2.2.2.1]
      exact (le_sup_right : Sg ≤ A ⊔ Sg) hs
    have hcomm := Subgroup.mem_centralizer_singleton_iff.1 hsC
    calc (γ * s * γ⁻¹) * (γ * P.Ψ z * γ⁻¹)
        = γ * (s * P.Ψ z) * γ⁻¹ := by group
      _ = γ * (P.Ψ z * s) * γ⁻¹ := by rw [hcomm]
      _ = (γ * P.Ψ z * γ⁻¹) * (γ * s * γ⁻¹) := by group
  · have hquasiMap : CFSG.IsQuasisimple (Sg.map (MulAut.conj γ).toMonoidHom) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Sg.equivMapOfInjective (MulAut.conj γ).toMonoidHom (MulAut.conj γ).injective) hquasi
    haveI : Group.IsPerfect ↥(Sg.map (MulAut.conj γ).toMonoidHom) := hquasiMap.1
    exact Subgroup.commutator_eq_self
  · rw [Subgroup.card_map_of_injective (MulAut.conj γ).injective]
    exact hpdvd

end ExistsSylow


theorem false_of_isElemAbelian_reeGamma_F4_of_not_dvd {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] {a p : ℕ} (hK : Nat.card K = 2 ^ (2 * a + 1)) (hp : p.Prime)
    (hp3 : 3 < p) (hndvd : ¬ p ∣ (2 ^ (2 * a + 1)) ^ 4 - 1)
    (E : Subgroup (ReeTag.F4.reeGamma K a)) (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) : False := by
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three (by omega) (by omega)
  have hdvd : p ∣ Nat.card (ReeTag.F4.reeGamma K a) := by
    have h0 := Subgroup.card_subgroup_dvd_card E
    rw [hcard] at h0
    exact (dvd_pow_self p two_ne_zero).trans h0
  have hrank := le_pRank_of_card hp.one_lt E hE.isElementaryAbelian hcard
  rcases (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).2 p hp hp3 hdvd with
    h1 | h2 | h3 | h4 | h5
  · exact hndvd (dvd_pow_four_sub_one_of_dvd_factor (Or.inl h1))
  · exact hndvd (dvd_pow_four_sub_one_of_dvd_factor (Or.inr (Or.inl h2)))
  · exact hndvd (dvd_pow_four_sub_one_of_dvd_factor (Or.inr (Or.inr h3)))
  · have := pRank_le_one_ree_phi6 hK hp hp5 h4
    omega
  · have := pRank_le_one_ree_phi12 hK hp hp5 h5
    omega

private theorem exists_good_of_reeGamma_F4_three {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {E : Subgroup (ReeTag.F4.reeGamma K a)} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) :
    ∃ x ∈ E, x ≠ 1 ∧ ∃ P : Subgroup (ReeTag.F4.reeGamma K a),
      P ≤ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧ ⁅P, P⁆ = P ∧
        3 ∣ Nat.card P := by
  classical
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hne : ∃ x ∈ E, x ≠ 1 := by
    have h1 : 1 < Nat.card E := by rw [hcard]; norm_num
    haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp h1
    obtain ⟨x, hx1⟩ := exists_ne (1 : E)
    exact ⟨x, x.2, fun h => hx1 (Subtype.ext h)⟩
  obtain ⟨x, hxE, hx1⟩ := hne
  have hx3 : x ^ 3 = 1 := by simpa using hE.2 x hxE
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨e⟩ := reeGamma_centralizer_su3 hK hord
  have hquasi : CFSG.IsQuasisimple (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (su3_isQuasisimple (by omega) (card_galoisField_su3 a))
  refine ⟨x, hxE, hx1, Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)), le_rfl, ?_, ?_⟩
  · haveI : Group.IsPerfect ↥(Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) :=
      hquasi.1
    exact Subgroup.commutator_eq_self
  · rw [show Nat.card (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) =
        Nat.card (unitarySU 2 (2 * a + 1) (GaloisField 2 (2 * (2 * a + 1))) 3) from
      Nat.card_congr e.toEquiv]
    exact three_dvd_card_su3 rfl (card_galoisField_su3 a)

theorem perfectCentralizerPlanes_reeGamma_F4 {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : PerfectCentralizerPlanes p (ReeTag.F4.reeGamma K a) := by
  intro E hE hcard
  rcases eq_or_ne p 3 with rfl | hp3ne
  · exact exists_good_of_reeGamma_F4_three ha hK hE hcard
  · have hp3 : 3 < p := by
      have := hp.two_le
      omega
    by_cases hdvd : p ∣ (2 ^ (2 * a + 1)) ^ 4 - 1
    · obtain ⟨hsh, ⟨P⟩⟩ := exists_sylowShape_and_reePlane hK hp hp3 hdvd
      exact exists_good_of_reePlane_reeGamma_F4 ha hK hp hp2 hp3 hsh P hE hcard
    · exact (false_of_isElemAbelian_reeGamma_F4_of_not_dvd hK hp hp3 hdvd E hE hcard).elim

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
