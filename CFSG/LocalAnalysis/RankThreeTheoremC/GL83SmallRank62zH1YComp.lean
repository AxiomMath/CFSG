module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1Quot
import CFSG.Walter.AStar.Subnormal
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xLift
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.AGLEmbedding

variable {B : Type} [Group B] [Finite B] {f : ℕ} {Q : Subgroup B}

theorem k631a_subnormal_bot [Fact f.Prime] (hcore : GLAPPrimeCore f B = ⊥) {K : Subgroup B}
    (hK : K.IsSubnormal) (hc : ¬ f ∣ Nat.card K) : K = ⊥ := by
  let π : Set Nat.Primes := {q | q.val ≠ f}
  have h1 := CFSG.LocalCores.prime_set_core_subnormal_intersection π hK
  have h2 : piCore π K = ⊤ := by
    refine top_le_iff.mp (CFSG.LocalCores.le_piCore_of_normal Subgroup.normal_top ?_)
    intro q hq hqf
    rw [Subgroup.card_top] at hq
    exact hc (hqf ▸ hq)
  have h3 : piCore π B = ⊥ := by
    rw [← pPrimeCore_eq_piCore (G := B) (p := f)]
    exact hcore
  rw [h2, h3, inf_bot_eq, Subgroup.map_top, Subgroup.range_subtype] at h1
  exact h1

theorem k631a_comp_dvd (h : k631aBHyp f Q) {J : Subgroup B} (hJ : IsComponent J) :
    f ∣ Nat.card J := by
  have := Fact.mk h.prime
  by_contra hc
  have hbot := k631a_subnormal_bot h.core hJ.2 hc
  have := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
  rw [hbot] at this
  exact (not_nontrivial_iff_subsingleton.mpr inferInstance) this

theorem k631a_sylow_inf (h : k631aBHyp f Q) {J : Subgroup B} (hJ : J.IsSubnormal) :
    ∃ P : Sylow f J, (P : Subgroup J).map J.subtype = Q ⊓ J := by
  have := Fact.mk h.prime
  obtain ⟨P, hP⟩ :=
    CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal (h.pgroup.toSylow h.sylow) hJ
  exact ⟨P, by simpa using hP⟩

theorem k631a_inf_ne_bot (h : k631aBHyp f Q) {J : Subgroup B} (hJ : IsComponent J) :
    Q ⊓ J ≠ ⊥ := by
  have := Fact.mk h.prime
  have h1 := CFSG.Walter.sylow_inf_ne_bot_of_isSubnormal (h.pgroup.toSylow h.sylow) hJ.2
    (k631a_comp_dvd h hJ)
  simpa using h1

omit [Finite B] in
theorem k631a_mem_sylow_iff {J : Subgroup B} {P : Subgroup J} (hP : P.map J.subtype = Q ⊓ J)
    (k : J) : k ∈ P ↔ (k : B) ∈ Q := by
  constructor
  · intro hk
    have : (k : B) ∈ P.map J.subtype := Subgroup.mem_map_of_mem _ hk
    rw [hP] at this
    exact this.1
  · intro hk
    have : (k : B) ∈ Q ⊓ J := ⟨hk, k.2⟩
    rw [← hP] at this
    obtain ⟨k', hk', hkk'⟩ := this
    rwa [← Subtype.ext hkk']

theorem k631a_simple_of_center_bot {J : Type} [Group J] (hq : IsQuasisimple J)
    (hZ : Subgroup.center J = ⊥) : IsSimpleGroup J ∧ ∃ a b : J, a * b ≠ b * a := by
  let e : J ≃* J ⧸ Subgroup.center J :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  obtain ⟨-, hs, a, b, hab⟩ := hq
  have := hs
  refine ⟨e.isSimpleGroup, e.symm a, e.symm b, fun hba => hab ?_⟩
  simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba

theorem k631a_center_bot (h : k631aBHyp f Q) {J : Subgroup B} (hJ : IsComponent J) :
    Subgroup.center ↥J = ⊥ := by
  have := Fact.mk h.prime
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  by_contra hz1
  have hord : orderOf z ≠ 1 := fun h1 => hz1 (orderOf_eq_one_iff.mp h1)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hord
  have hfin : orderOf z ≠ 0 := (orderOf_pos z).ne'
  have hwo : orderOf (z ^ (orderOf z / r)) = r := orderOf_pow_orderOf_div hfin hrd
  have hwc : z ^ (orderOf z / r) ∈ Subgroup.center ↥J := Subgroup.pow_mem _ hz _
  set w := z ^ (orderOf z / r) with hw
  by_cases hrf : r = f
  · obtain ⟨P, hP⟩ := k631a_sylow_inf h hJ.2
    have hPc : IsMulCommutative (P : Subgroup J) := by
      refine IsMulCommutative.of_comm ?_
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      refine Subtype.ext (Subtype.ext ?_)
      have ha' := (k631a_mem_sylow_iff hP a).mp ha
      have hb' := (k631a_mem_sylow_iff hP b).mp hb
      have hab := h.comm.is_comm.comm (⟨(a : B), ha'⟩ : ↥Q) ⟨(b : B), hb'⟩
      have hab' : (a : B) * b = b * a := congrArg Subtype.val hab
      exact hab'
    have hwf : w ^ f = 1 := by
      have := pow_orderOf_eq_one w
      rwa [hwo, hrf] at this
    have hw1 := lift62x_center_eq_one hJ.1.1.commutator_eq_top h.prime P.isPGroup'
      P.not_dvd_index hPc hwc hwf
    rw [hw1, orderOf_one] at hwo
    exact hr.one_lt.ne hwo
  · have hnorm : (Subgroup.zpowers w).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hwc)
    have hsn : ((Subgroup.zpowers w).map J.subtype).IsSubnormal :=
      hnorm.isSubnormal.trans' hJ.2
    have hcard : Nat.card ((Subgroup.zpowers w).map J.subtype) = r := by
      rw [Subgroup.card_map_of_injective J.subtype_injective, Nat.card_zpowers, hwo]
    have hnd : ¬ f ∣ Nat.card ((Subgroup.zpowers w).map J.subtype) := by
      rw [hcard]
      intro hd
      exact hrf ((Nat.prime_dvd_prime_iff_eq h.prime hr).mp hd).symm
    have hbot := k631a_subnormal_bot h.core hsn hnd
    rw [hbot, Subgroup.card_bot] at hcard
    exact hr.one_lt.ne hcard

theorem k631a_eq_one_of_central (h : k631aBHyp f Q) {J : Subgroup B} (hJ : IsComponent J)
    {j : B} (hj : j ∈ J) (hc : ∀ k ∈ J, j * k = k * j) : j = 1 := by
  have hz : (⟨j, hj⟩ : ↥J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hc k k.2).symm
  rw [k631a_center_bot h hJ, Subgroup.mem_bot] at hz
  exact congrArg Subtype.val hz

theorem k631a_normalizes (h : k631aBHyp f Q) {J : Subgroup B} (hJ : IsComponent J) :
    Q ≤ normalizer (J : Set B) := by
  intro q hq
  obtain ⟨⟨x, hxQJ⟩, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (k631a_inf_ne_bot h hJ)
  obtain ⟨hxQ, hxJ⟩ := hxQJ
  have hx1 : x ≠ 1 := fun h1 => hx1' (Subtype.ext h1)
  have hJ' : IsComponent (J.map (MulAut.conj q).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj q) hJ
  rcases CFSG.LocalCores.distinct_components_commute hJ hJ' with heq | hcomm
  · exact mem_normalizer_iff_map_conj_eq.mpr heq.symm
  · exfalso
    have hqx : q * x * q⁻¹ = x := by
      have := h.comm.is_comm.comm (⟨q, hq⟩ : ↥Q) ⟨x, hxQ⟩
      have h2 : q * x = x * q := congrArg Subtype.val this
      rw [h2]
      group
    have hxJ' : x ∈ J.map (MulAut.conj q).toMonoidHom := ⟨x, hxJ, by simpa using hqx⟩
    refine hx1 (k631a_eq_one_of_central h hJ hxJ fun k hk => ?_)
    have h3 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hk
    exact Subgroup.mem_centralizer_iff.mp h3 x hxJ'

theorem k631a_inner (hInn : KFactInnerAction) (h : k631aBHyp f Q) {J : Subgroup B}
    (hJ : IsComponent J) {q : B} (hq : q ∈ Q) :
    ∃ s ∈ Q ⊓ J, ∀ j ∈ J, q * j * q⁻¹ = s * j * s⁻¹ := by
  have := Fact.mk h.prime
  have hZ := k631a_center_bot h hJ
  obtain ⟨hsimple, hnab⟩ := k631a_simple_of_center_bot hJ.1 hZ
  have hcat : IsCatalogGroup ↥J := h.catalog.simple_subgroup J hsimple hnab
  obtain ⟨P, hP⟩ := k631a_sylow_inf h hJ.2
  have hmem := k631a_mem_sylow_iff hP
  have hqN : q ∈ normalizer (J : Set B) := k631a_normalizes h hJ hq
  set φ : MulAut J := J.normalizerMonoidHom ⟨q, hqN⟩ with hφdef
  have hφ : ∀ k : J, ((φ k : J) : B) = q * k * q⁻¹ := fun _ => rfl
  obtain ⟨n, hn⟩ := h.pgroup ⟨q, hq⟩
  have hφp : φ ^ (f ^ n) = 1 := by
    have h1 : (⟨q, hqN⟩ : normalizer (J : Set B)) ^ (f ^ n) = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hn)
    rw [hφdef, ← map_pow, h1, map_one]
  have hPne : (P : Subgroup J) ≠ ⊥ := by
    intro hbot
    have h1 := k631a_inf_ne_bot h hJ
    rw [← hP, hbot, Subgroup.map_bot] at h1
    exact h1 rfl
  have hPc : IsMulCommutative (P : Subgroup J) := by
    refine IsMulCommutative.of_comm ?_
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    refine Subtype.ext (Subtype.ext ?_)
    have hab := h.comm.is_comm.comm (⟨(a : B), (hmem a).mp ha⟩ : ↥Q) ⟨(b : B), (hmem b).mp hb⟩
    have hab' : (a : B) * b = b * a := congrArg Subtype.val hab
    exact hab'
  obtain ⟨g, hgP, hg⟩ := hInn f h.prime h.ne_two J hsimple hnab hcat P hPne hPc φ ⟨n, hφp⟩
    (fun g hg => by
      have hsg : q * (g : B) = g * q :=
        congrArg Subtype.val (h.comm.is_comm.comm (⟨q, hq⟩ : ↥Q) ⟨(g : B), (hmem g).mp hg⟩)
      ext m
      change q * ((g : B) * m * (g : B)⁻¹) * q⁻¹ = (g : B) * (q * m * q⁻¹) * (g : B)⁻¹
      calc q * ((g : B) * m * (g : B)⁻¹) * q⁻¹ = (q * g) * m * (q * g)⁻¹ := by group
        _ = (g * q) * m * (g * q)⁻¹ := by rw [hsg]
        _ = (g : B) * (q * m * q⁻¹) * (g : B)⁻¹ := by group)
  refine ⟨(g : B), ⟨(hmem g).mp hgP, g.2⟩, fun k hk => ?_⟩
  have h1 := congrArg (fun ψ : MulAut J => ((ψ ⟨k, hk⟩ : J) : B)) hg
  simpa [hφ] using h1

end CFSG.LocalAnalysis.RankThreeTheoremC
