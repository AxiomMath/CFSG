module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L618
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L618OmegaPGroup
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lines

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

namespace L618Om

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem exists_pSubgroup_containing (hS : Situation G p P M) {Q : Subgroup G}
    (hQp : IsPGroup p Q) (hQM : Q ≤ M) :
    ∃ R : Subgroup G, Q ≤ R ∧ R ≤ M ∧ IsPGroup p R ∧
      ∃ A : Subgroup G, A ≤ R ∧ CFSG.IsElementaryAbelian p A ∧ Nat.card A = p ^ 3 := by
  have : Fact p.Prime := ⟨hS.prime⟩
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup p hS.prime P M hS.sylow_le Q
    hQp hQM
  obtain ⟨A₀, hA₀P, hA₀e, hA₀c⟩ := hS.exists_elemAbelian_cube
  have hinj : Function.Injective (MulAut.conj ((m : G)⁻¹)).toMonoidHom :=
    (MulAut.conj ((m : G)⁻¹)).injective
  refine ⟨(P : Subgroup G).map (MulAut.conj ((m : G)⁻¹)).toMonoidHom, ?_, ?_, ?_,
    A₀.map (MulAut.conj ((m : G)⁻¹)).toMonoidHom, Subgroup.map_mono hA₀P, ?_, ?_⟩
  · intro q hq
    have h1 := hm (Subgroup.mem_map_of_mem (MulAut.conj (m : G)).toMonoidHom hq)
    refine ⟨(m : G) * q * (m : G)⁻¹, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro _ ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem (M.inv_mem m.2) (hS.sylow_le hy)) (M.inv_mem (M.inv_mem m.2))
  · obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := n) (by rw [Subgroup.card_map_of_injective hinj, hn])
  · have : CFSG.IsElementaryAbelian p A₀ := hA₀e
    exact CFSG.IsElementaryAbelian.map _
  · rw [Subgroup.card_map_of_injective hinj, hA₀c]

theorem exists_plane_centralizer_three (hS : Situation G p P M) {Q E : Subgroup G}
    (hQp : IsPGroup p Q) (hQM : Q ≤ M) (hEQ : E ≤ Q) (hEe : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) {q : G} (hqQ : q ∈ Q) (hq1 : q ^ p = 1) (hqE : q ∉ E) :
    ∃ U : Subgroup G, U ≤ Q ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2 ∧
      ∀ u ∈ U, u ≠ 1 → 3 ≤ Open.pRank p (M ⊓ centralizer ({u} : Set G)) := by
  have hprime := hS.prime
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨R, hQR, hRM, hRp, A, hAR, hAe, hAc⟩ := exists_pSubgroup_containing hS hQp hQM
  have hER : E ≤ R := hEQ.trans hQR
  have : CFSG.IsElementaryAbelian p A := hAe
  have : CFSG.IsElementaryAbelian p E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).2 hEe
  have hA' : CFSG.IsElementaryAbelian p (A.subgroupOf R) :=
    CFSG.IsElementaryAbelian.subgroupOf hAR
  have hAc' : Nat.card (A.subgroupOf R) = p ^ 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv).trans hAc
  have hE' : CFSG.IsElementaryAbelian p (E.subgroupOf R) :=
    CFSG.IsElementaryAbelian.subgroupOf hER
  have hEc' : Nat.card (E.subgroupOf R) = p ^ 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hER).toEquiv).trans hEc
  have hEQ' : E.subgroupOf R ≤ Q.subgroupOf R := fun b hb => hEQ hb
  obtain ⟨U', hU'Q, hU'e, hU'c, hU'W⟩ := exists_plane_of_omega hS.ne_two hRp hA' hAc' hEQ' hE'
    hEc' (q := ⟨q, hQR hqQ⟩) hqQ (Subtype.ext (by simpa using hq1))
    (fun h => hqE (Subgroup.mem_subgroupOf.mp h))
  have : CFSG.IsElementaryAbelian p U' := hU'e
  refine ⟨U'.map R.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact hU'Q hu
  · exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1
      CFSG.IsElementaryAbelian.map_subtype
  · rw [Subgroup.card_map_of_injective R.subtype_injective, hU'c]
  · rintro _ ⟨u, hu, rfl⟩ hu1
    have hu1' : u ≠ 1 := fun h => hu1 (by rw [h, map_one])
    obtain ⟨W, hWc, hWe, hW3⟩ := hU'W u hu hu1'
    have : CFSG.IsElementaryAbelian p W := hWe
    have hW'e : IsElemAbelian p (W.map R.subtype) :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1
        CFSG.IsElementaryAbelian.map_subtype
    have hW'le : W.map R.subtype ≤ M ⊓ centralizer ({R.subtype u} : Set G) := by
      rintro _ ⟨w, hw, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨hRM w.2, mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hWc hw))
    have hW'p : IsPGroup p (W.map R.subtype) :=
      fun y => ⟨1, Subtype.ext (by simpa using hW'e.2 y y.2)⟩
    obtain ⟨n, hn⟩ := hW'p.exists_card_eq
    have hcard : p ^ 3 ≤ Nat.card (W.map R.subtype) := by
      rw [Subgroup.card_map_of_injective R.subtype_injective]
      exact hW3
    rw [hn] at hcard
    have h3n : 3 ≤ n := (Nat.pow_le_pow_iff_right hprime.one_lt).mp hcard
    exact h3n.trans (CFSG.SectionRank.le_pRank hprime.one_lt hW'le hW'e hn)

end L618Om

theorem stepOmegaU_holds : StepOmegaU := by
  intro G _ _ p P M x z hS hx hz H S hopt hO Q hQH hQp hBQ hq
  obtain ⟨q, hqQ, hq1, hqB⟩ := hq
  have hpl := plane_of_central hS hx hz
  exact L618Om.exists_plane_centralizer_three hS hQp (hopt.sylow_le Q hQp hQH hBQ) hBQ
    hpl.isElemAbelian hpl.card_eq hqQ hq1 hqB

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
