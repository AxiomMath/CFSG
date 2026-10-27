module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Defs
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup Equiv

theorem ths_le_pCore_of_isSubnormal {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {S : Subgroup X} (hS : S.IsSubnormal) (hp : IsPGroup p S) :
    S ≤ CFSG.pCore p X := by
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection {q : Nat.Primes | q.val = p} hS
  rw [← CFSG.pCore_eq_piCore ↥S p, ← CFSG.pCore_eq_piCore X p] at h
  have htop : CFSG.pCore p ↥S = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, hp.of_equiv Subgroup.topEquiv.symm⟩)
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h.le.trans inf_le_right

theorem ths_le_pPrimeCore_of_isSubnormal {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {S : Subgroup X} (hS : S.IsSubnormal) (hp : p.Coprime (Nat.card S)) :
    S ≤ CFSG.pPrimeCore p X := by
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection {q : Nat.Primes | q.val ≠ p} hS
  rw [← CFSG.pPrimeCore_eq_piCore ↥S p, ← CFSG.pPrimeCore_eq_piCore X p] at h
  have htop : CFSG.pPrimeCore p ↥S = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩)
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h.le.trans inf_le_right

theorem ths_center_eq_bot {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (h3 : CFSG.pCore p X = ⊥) (h3' : CFSG.pPrimeCore p X = ⊥) {J : Subgroup X}
    (hJ : CFSG.IsComponent J) : Subgroup.center J = ⊥ := by
  by_contra hne
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (Subgroup.center J) ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hcard
  have hfact : Fact q.Prime := ⟨hq⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center J) q hqd
  set zJ : J := (z : J) with hzJ
  have hzc : ∀ g : J, g * zJ = zJ * g := fun g => (Subgroup.mem_center_iff.mp z.2 g)
  set Zq : Subgroup J := Subgroup.zpowers zJ with hZq
  have hZqN : Zq.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have : g * zJ ^ k * g⁻¹ = zJ ^ k := by
      have hc : Commute g (zJ ^ k) := (Commute.zpow_right (hzc g) k)
      rw [hc.eq]; group
    rw [this]
    exact Subgroup.zpow_mem_zpowers _ _
  set W : Subgroup X := Zq.map J.subtype with hW
  have hWsub : W.IsSubnormal := by
    refine Subgroup.IsSubnormal.step W J (Subgroup.map_subtype_le _) hJ.2 ?_
    have : W.subgroupOf J = Zq := Subgroup.comap_map_eq_self_of_injective J.subtype_injective Zq
    rw [this]
    exact hZqN
  have hWcard : Nat.card W = q := by
    rw [hW, Subgroup.card_map_of_injective J.subtype_injective, hZq, Nat.card_zpowers]
    rw [hzJ]
    exact (Subgroup.orderOf_coe z).trans hz
  have hW1 : W = ⊥ := by
    by_cases hqp : q = p
    · subst hqp
      refine le_bot_iff.mp (h3 ▸ ths_le_pCore_of_isSubnormal hWsub ?_)
      exact IsPGroup.of_card (n := 1) (by rw [hWcard]; simp)
    · refine le_bot_iff.mp (h3' ▸ ths_le_pPrimeCore_of_isSubnormal hWsub ?_)
      rw [hWcard]
      exact (Nat.coprime_primes hp hq).mpr (fun h => hqp h.symm)
  rw [hW1, Subgroup.card_bot] at hWcard
  exact hq.one_lt.ne hWcard

theorem ThompsonFrame.exists_alt_normal {p : ℕ} {X : Type} [Group X] [Finite X] {D : Subgroup X}
    (hF : ThompsonFrame p D) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (huniq : ∀ L' : Subgroup X, CFSG.IsComponent L' → L' = L) {n : ℕ}
    (e : L ⧸ center L ≃* alternatingGroup (Fin n)) :
    L.Normal ∧ D ≤ L ∧ 5 ≤ n ∧ Nonempty (L ≃* alternatingGroup (Fin n)) := by
  classical
  have hp := hF.prime
  have : Fact p.Prime := ⟨hp⟩
  have hZ := ths_center_eq_bot hp hF.pCore_eq_bot hF.pPrimeCore_eq_bot hL
  let q1 : L ⧸ Subgroup.center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let e' : L ≃* alternatingGroup (Fin n) := q1.symm.trans e
  have hlayer : CFSG.layer X = L := by
    simp only [CFSG.layer.eq_sSup]
    have : {K : Subgroup X | CFSG.IsComponent K} = {L} :=
      Set.ext fun K => ⟨fun hK => huniq K hK, fun hK => hK ▸ hL⟩
    rw [this, sSup_singleton]
  have hLn : L.Normal := by
    rw [← hlayer]
    have := CFSG.LocalCores.layer_characteristic (G := X)
    infer_instance
  have hF0 : CFSG.fittingSubgroup X = ⊥ := by
    rw [CFSG.Fitting_eq_pcore X p hF.pPrimeCore_eq_bot, hF.pCore_eq_bot]
  have hgf : CFSG.generalizedFitting X = L := by
    rw [CFSG.generalizedFitting, hF0, hlayer, bot_sup_eq]
  have hCle : Subgroup.centralizer (L : Set X) ≤ L := by
    have := CFSG.centralizer_generalizedFitting_le X
    rwa [hgf] at this
  have h5 : 5 ≤ n := by
    by_contra hlt
    have hsol : Group.IsSolvable (alternatingGroup (Fin n)) :=
      alternatingGroup.isSolvable (by simpa using (show n ≤ 4 by omega))
    have hsolL : Group.IsSolvable L :=
      Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective
    have : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
    have : Group.IsPerfect L := hL.1.1
    exact Group.IsPerfect.not_isSolvable L inferInstance
  refine ⟨hLn, ?_, h5, ⟨e'⟩⟩
  let c : X →* MulAut L := MulAut.conjNormal
  let ρ : X →* CFSG.ComponentClassification.OuterAutomorphisms.Outer L :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner L)).comp c
  have hker : ∀ x, ρ x = 1 → x ∈ L := by
    intro x hx
    have hxin : c x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner L :=
      (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨l, hl⟩ := hxin
    have hxC : (l : X)⁻¹ * x ∈ Subgroup.centralizer (L : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have h1 := congrArg (fun φ : MulAut L => ((φ ⟨m, hm⟩ : L) : X)) hl
      simp only [c, MulAut.conjNormal_apply, MulAut.conj_apply] at h1
      have h1' : (l : X) * m * (l : X)⁻¹ = x * m * x⁻¹ := h1
      calc m * ((l : X)⁻¹ * x) = (l : X)⁻¹ * ((l : X) * m * (l : X)⁻¹) * x := by group
        _ = (l : X)⁻¹ * (x * m * x⁻¹) * x := by rw [h1']
        _ = (l : X)⁻¹ * x * m := by group
    have hx' : x = (l : X) * ((l : X)⁻¹ * x) := by group
    rw [hx']
    exact mul_mem l.2 (hCle hxC)
  intro d hd
  by_contra hdL
  have hρ : ρ d ≠ 1 := fun h => hdL (hker d h)
  have hdp : (ρ d) ^ p = 1 := by rw [← map_pow, hF.elem.2 d hd, map_one]
  have hord : orderOf (ρ d) = p :=
    ((Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hdp)).resolve_left
      (fun h => hρ (orderOf_eq_one_iff.mp h))
  have hdvd : p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) :=
    hord ▸ orderOf_dvd_natCard (ρ d)
  have hcard : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (alternatingGroup (Fin n))) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv
  exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n h5 p hp hF.odd (hcard ▸ hdvd)

end CFSG.LocalAnalysis.RankThreeTheoremC
