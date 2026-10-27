module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2Neighbour
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionLevi
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionPerfect

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.EvenSmallLie RootOps


variable {K : Type} [Field K]

theorem commutator_centralizer_e7Rep_zero_two [CharP K 2] (hK : Nat.card K = 2) :
    ⁅centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K)),
        centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K))⁆ =
      centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K)) := by
  obtain ⟨n, hn⟩ := E8Pilot.exists_conj_pinnedElt_highRoot_eq (K := K) (Or.inr (Or.inl rfl))
    (e7RepFrames_isRoot 0 _ List.mem_cons_self)
  rw [e7Rep_zero_eq_pinnedElt, ← hn, ← map_conj_centralizer_singleton_E7, ← map_commutator,
    E8Pilot.commutator_centralizer_pinnedElt_highRoot_two (Or.inr (Or.inl rfl)) hK]

theorem commutator_centralizer_e7Rep_zero_of_one_le {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    ⁅centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K)),
        centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K))⁆ =
      centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K)) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  rcases Nat.lt_or_ge f 2 with h | h
  · obtain rfl : f = 1 := by omega
    exact commutator_centralizer_e7Rep_zero_two (by simpa using hK)
  · refine commutator_centralizer_e7Rep_zero ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h

theorem forall_normal_isPGroup_eq_bot_perpLevi_of_finite [Finite K] [CharP K 2] :
    ∀ N : Subgroup (EPilot.perpLevi .E7 K), N.Normal → IsPGroup 2 N → N = ⊥ := by
  intro N hN hNp
  have hs := isSimpleGroup_perpLevi_E7 (K := K)
  rcases hs.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hDp : IsPGroup 2 (EPilot.perpLevi .E7 K) := by
      rw [h] at hNp
      exact hNp.of_equiv Subgroup.topEquiv
    have : Finite (EPilot.perpLevi .E7 K) := by
      have := finite_modGL (τ := .E7) (K := K)
      infer_instance
    have : Nontrivial (EPilot.perpLevi .E7 K) := hs.toNontrivial
    have hnt := hDp.center_nontrivial
    rw [center_perpLevi_E7_eq_bot] at hnt
    exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt rfl

theorem factO2E7_of_finite [Finite K] [CharP K 2] : FactO2E7 K :=
  EPilot.forall_normal_isPGroup_eq_bot_of_mulEquiv (perpLeviEquivXLevi K)
    forall_normal_isPGroup_eq_bot_perpLevi_of_finite

theorem not_isPGroup_SL2_of_finite [Finite K] [CharP K 2] : ¬ IsPGroup 2 (SL2 K) := by
  intro hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA⟩ := F4Pilot.exists_orderOf_eq_natCard_add_one (K := K)
  obtain ⟨k, hk⟩ := hp A
  have hdvd : Nat.card K + 1 ∣ 2 ^ k := hA ▸ orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hKc : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hf1 : 1 ≤ (f : ℕ) := f.2
  rw [hKc] at hj
  rcases j with _ | j
  · have : 0 < 2 ^ (f : ℕ) := by positivity
    simp at hj
  · have h1 : Even (2 ^ (j + 1)) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
    have h2 : Odd (2 ^ (f : ℕ) + 1) := (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
    rw [← hj] at h1
    exact (Nat.not_even_iff_odd.2 h2) h1

theorem not_isPGroup_rootSL2_highRootD [Finite K] [CharP K 2] :
    ¬ IsPGroup 2 (rootSubgroup .E7 K highRootD ⊔ rootSubgroup .E7 K (-highRootD) :
      Subgroup (ModGL .E7 K)) := by
  obtain ⟨-, -, ⟨e, -⟩, -⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps (τ := .E7) K
      (e7RepPreHigh_isRoot 0)
  rw [← highRootD_eq] at e
  intro hp
  exact not_isPGroup_SL2_of_finite (hp.of_equiv e.symm)

theorem exists_map_highRootDJ_eq_of_finite [Finite K] [CharP K 2]
    (ι : EPilot.perpLevi .E7 K ≃* EPilot.perpLevi .E7 K) :
    ∃ c ∈ adjointGroup .E7 K, ((highRootDJ K).map ι.toMonoidHom).map (perpLeviHom K) =
      (EPilot.highRootSL2 .E7 K).map (MulAut.conj c).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_perpLevi_eq (K := K)
  obtain ⟨d, hd⟩ := exists_map_inf_centralizer_eq S ι
  rw [sylow_inf_centralizer_eq_highRootDU S hS] at hd
  obtain ⟨nD, hJ⟩ := exists_highRootDJ_eq_sup (K := K)
  have h := map_mulEquiv_sup_map_conj_eq (perpLeviHom K) ι (highRootDU K) nD d hd
  rw [← hJ, map_perpLeviHom_highRootDU, rootSubgroup_highRootD_eq_map, map_conj_map_conj,
    map_conj_map_conj] at h
  have hmemC : ∀ x : EPilot.perpLevi .E7 K, perpLeviHom K x ∈ adjointGroup .E7 K := fun x =>
    (x : adjointGroup .E7 K).2
  have hn₀ : ((e7RepConj K 0 : adjointGroup .E7 K) : ModGL .E7 K)⁻¹ ∈ adjointGroup .E7 K :=
    inv_mem (e7RepConj K 0).2
  rcases isPGroup_or_eq_conj_of_conj_highRoot 2 (mul_mem (hmemC d) hn₀)
      (mul_mem (hmemC (ι nD * d)) hn₀) with hp | ⟨c, hc, heq⟩
  · exfalso
    rw [← h] at hp
    refine not_isPGroup_rootSL2_highRootD (K := K) ((hp.of_equiv
      ((((highRootDJ K).map ι.toMonoidHom).equivMapOfInjective _
        perpLeviHom_injective).symm.trans ((highRootDJ K).equivMapOfInjective _
          ι.injective).symm)).of_equiv highRootDJEquiv)
  · exact ⟨c, hc, h.trans heq⟩

theorem factF5E7_of_finite [Finite K] [CharP K 2] : FactF5E7 K := by
  intro ι
  obtain ⟨c, hc, h⟩ := exists_map_highRootDJ_eq_of_finite
    (((perpLeviEquivXLevi K).trans ι).trans (perpLeviEquivXLevi K).symm)
  refine ⟨e7RepConj K 0 * ⟨c, hc⟩, ?_⟩
  apply map_injective (adjointGroup .E7 K).subtype_injective
  have h2 := map_xLeviHom_map_perpLeviEquivXLevi ((highRootDJ K).map
    (((perpLeviEquivXLevi K).trans ι).trans (perpLeviEquivXLevi K).symm).toMonoidHom)
  rw [h, map_conj_map_conj, ← map_map_mulEquiv_conj, ← posJE7_subgroupOf_eq_map] at h2
  have hsub : (adjointGroup .E7 K).subtype (e7RepConj K 0 * ⟨c, hc⟩) =
      (e7RepConj K 0 : ModGL .E7 K) * c := by
    simp only [map_mul, Subgroup.coe_subtype]
  rw [Subgroup.map_map]
  refine h2.trans ?_
  rw [map_map_conj_eq, posJE7, subgroupOf_map_subtype,
    inf_eq_left.2 EPilot.highRootSL2_le_adjointGroup, hsub]

theorem nonempty_centralizer_map_conj_posJE7_mulEquiv_of_finite [Finite K] [CharP K 2]
    (c : adjointGroup .E7 K) :
    Nonempty (centralizer (((posJE7 K).map (MulAut.conj c).toMonoidHom :
      Subgroup (adjointGroup .E7 K)) : Set (adjointGroup .E7 K)) ≃* EPilot.perpLevi .E7 K) := by
  have hcen : centralizer (((posJE7 K).map (MulAut.conj c).toMonoidHom :
      Subgroup (adjointGroup .E7 K)) : Set (adjointGroup .E7 K)) =
        (EPilot.perpLevi .E7 K).map (MulAut.conj c).toMonoidHom := by
    rw [← F4Pilot.map_centralizer_mulEquiv (MulAut.conj c) (posJE7 K), posJE7,
      centralizer_highRootSL2_subgroupOf_E7_of_charTwo]
  exact ⟨(MulEquiv.subgroupCongr hcen).trans
    ((EPilot.perpLevi .E7 K).equivMapOfInjective _ (MulAut.conj c).injective).symm⟩

theorem factF56E7_of_factF5E7_of_finite [Finite K] [CharP K 2] (h : FactF5E7 K) :
    FactF56E7 K := by
  intro ι
  obtain ⟨c, hc⟩ := h ι
  rw [hc]
  exact nonempty_centralizer_map_conj_posJE7_mulEquiv_of_finite c

theorem factF56E7_of_finite [Finite K] [CharP K 2] : FactF56E7 K :=
  factF56E7_of_factF5E7_of_finite factF5E7_of_finite

end CFSG.SeitzReduction.E7Pilot
