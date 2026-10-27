module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporCentKit
public import CFSG.RankThree.PartOne.KS.HeKit
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHeGenE
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveKit
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.PartOne CFSG.Sporadic.HeldB

theorem gLAPPrimeCoreOf_eq_bot_of_simple {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P : Subgroup G} (hs : IsSimpleGroup ↥P) (hpP : p ∣ Nat.card P) : GLAPPrimeCoreOf p P = ⊥ := by
  have hn : (GLAPPrimeCore p ↥P).Normal := GLAPPrimeCore.normal p ↥P
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p ↥P) with h | h
  · unfold GLAPPrimeCoreOf
    rw [h, Subgroup.map_bot]
  · exfalso
    have hcop := coprime_card_GLAPPrimeCoreOf hp P
    unfold GLAPPrimeCoreOf at hcop
    rw [h, Subgroup.card_map_of_injective P.subtype_injective, Subgroup.card_top] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hpP

theorem le_of_relIndex_two_of_odd {G : Type*} [Group G] [Finite G] {C D O : Subgroup G}
    (hOC : O ≤ C) (hD : D.relIndex C = 2) (hO : Odd (Nat.card O)) : O ≤ D := by
  intro o ho
  have hi : (D.subgroupOf C).index = 2 := hD
  have hsq : (⟨o, hOC ho⟩ : ↥C) ^ 2 ∈ D.subgroupOf C := Subgroup.sq_mem_of_index_two hi _
  have hsq' : o ^ 2 ∈ D := by
    rw [Subgroup.mem_subgroupOf] at hsq
    simpa using hsq
  obtain ⟨k, hk⟩ := hO
  have hm : orderOf o ∣ 2 * k + 1 := by
    rw [← hk]
    exact Subgroup.orderOf_dvd_natCard O ho
  have hpow : o ^ (2 * k + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 hm
  have : o = (o ^ 2) ^ (k + 1) := by
    calc o = o ^ (2 * k + 1) * o := by rw [hpow, one_mul]
      _ = (o ^ 2) ^ (k + 1) := by rw [← pow_mul, ← pow_succ]; ring_nf
  rw [this]
  exact D.pow_mem hsq' _


theorem isCyclic_gLAPPrimeCoreOf_heOuterC : IsCyclic ↥(GLAPPrimeCoreOf 2 heOuterC) := by
  obtain ⟨hDeq, hDq, hDi⟩ := ctbh_outer_centralizer_derived_quasisimple
  set O := GLAPPrimeCoreOf 2 heOuterC with hO
  set D := heOuterD with hDdef
  have hOC : O ≤ heOuterC := GLAPPrimeCoreOf_le _
  have hOodd : Odd (Nat.card O) :=
    Nat.coprime_two_left.1 (coprime_card_GLAPPrimeCoreOf Nat.prime_two heOuterC)
  have hOD : O ≤ D := le_of_relIndex_two_of_odd hOC hDi hOodd
  have hDC : D ≤ heOuterC := hDeq ▸ commutator_self_le' heOuterC
  set Z : Subgroup (Equiv.Perm (Fin 8330)) := (Subgroup.center ↥D).map D.subtype with hZ
  have hOZ : O ≤ Z := by
    have hle : O.subgroupOf D ≤ CFSG.pPrimeCore 2 ↥D := by
      refine le_sSup ⟨⟨fun x hx g => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact GLAPPrimeCoreOf_conj_mem (g : Equiv.Perm (Fin 8330)) (hDC g.2) _ hx
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOD).toEquiv]
        exact coprime_card_GLAPPrimeCoreOf Nat.prime_two heOuterC
    rw [CFSG.ComponentClassification.SolMax.HeGen.pPrimeCore_heOuterD] at hle
    intro o ho
    exact ⟨⟨o, hOD ho⟩, hle (Subgroup.mem_subgroupOf.2 ho), rfl⟩
  have hZcard : Nat.card Z = 3 := by
    rw [hZ, Subgroup.card_map_of_injective D.subtype_injective]
    exact card_center_heOuterD
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZcyc : IsCyclic ↥Z := isCyclic_of_prime_card hZcard
  have hsub : IsCyclic ↥(O.subgroupOf Z) := Subgroup.isCyclic _
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hOZ).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hOZ).surjective

theorem b3Phi_two_heAutGroup :
    ∀ r ∈ heAutGroup, r ^ 2 = 1 →
      B3Phi 2 (Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 8330))) ⊓ heP) := by
  intro r hrR hr2
  by_cases hr1 : r = 1
  · subst hr1
    have htop : Subgroup.centralizer ({(1 : Equiv.Perm (Fin 8330))} : Set _) = ⊤ := by
      ext x
      simp [Subgroup.mem_centralizer_singleton_iff]
    rw [htop, top_inf_eq]
    refine b3Phi_of_oPrime (gLAPPrimeCoreOf_eq_bot_of_simple Nat.prime_two heP_simple ?_)
    rw [card_heP]
    norm_num
  have hro : orderOf r = 2 := orderOf_eq_prime hr2 hr1
  by_cases hrP : r ∈ heP
  ·
    have hcore := ctbhi_held_inner_involution_centralizers_odd_core.2 ⟨r, hrP⟩
      (by rw [Subgroup.orderOf_mk]; exact hro)
    have hB : B3Phi 2 (Subgroup.centralizer ({(⟨r, hrP⟩ : ↥heP)} : Set ↥heP)) := by
      refine b3Phi_of_oPrime ?_
      unfold GLAPPrimeCoreOf GLAPPrimeCore
      rw [hcore, Subgroup.map_bot]
    rw [← b3Phi_map_iff Nat.prime_two heP.subtype heP.subtype_injective,
      map_centralizer_subtype] at hB
    exact hB
  ·
    obtain ⟨-, hcl, -⟩ := ctbh_outer_involution_class_exhaustion
    have hmem : r ∈ {x : Equiv.Perm (Fin 8330) | x ∈ heAutGroup ∧ x ∉ heP ∧ orderOf x = 2} :=
      ⟨hrR, hrP, hro⟩
    rw [hcl] at hmem
    obtain ⟨g, hgP, rfl⟩ := hmem
    refine b3Phi_conj_of_normalizes Nat.prime_two
      (fun a ha q hq => heP.mul_mem (heP.mul_mem ha hq) (heP.inv_mem ha)) hgP ?_
    have hC : Subgroup.centralizer ({heAutU} : Set (Equiv.Perm (Fin 8330))) ⊓ heP = heOuterC := by
      rw [heOuterC_eq, inf_comm]
    rw [hC]
    exact b3Phi_of_isCyclic isCyclic_gLAPPrimeCoreOf_heOuterC

theorem b3SporPair_He_two (hbr : SporadicBridges) : B3SporPair .He 2 :=
  b3SporPair_of_autModel Nat.prime_two heAutModel ⟨heEquivP.symm.trans (hbr .He).some⟩
    b3Phi_two_heAutGroup

end CFSG.HardMathSupport.Solomon.Coordinator
