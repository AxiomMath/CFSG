module

public import CFSG.GH74.Generic.BProg.B3.SolvP101Orbit
public import CFSG.GH74.Generic.BProg.B3.SolvLift
public import CFSG.GH74.Generic.BProg.B3.SolvStab
public import CFSG.GH74.Generic.BProg.B3.Obs
public import CFSG.GH74.GLS.Bg.Pu5.BalB0
public import CFSG.GH74.Generic.BProg.B1.PilotS5Facts

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace SolvP101

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic CFSG.GH74.Generic.BProg
  CFSG.ClassicalInvolution.Balance.LocalBalance CFSG.GH74.GLS.Th2.Bal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_two_comps {x e : G} {I0 V : Subgroup G} (hx : orderOf x = 2)
    (hxe : x ∈ centralizer ({e} : Set G))
    (hV : Balance.IsSolvTwoCompSL23In (centralizer ({x} : Set G) ⊓ centralizer ({e} : Set G)) V ∨
      IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({e} : Set G)) V)
    (hI0V : I0 ≤ oPrimeResidualOf 2 V)
    (hnot : ¬ I0 ≤ (pPrimePCore 2 ↥(centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype) :
    ∃ A B : Subgroup (CentralizerBar e), IsComponent A ∧ IsComponent B ∧
      (I0.subgroupOf (centralizer ({e} : Set G))).map (piBar e) ≤ A ⊔ B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({e} : Set G) with hC
  set x' : ↥C := ⟨x, hxe⟩ with hx'
  have hx'2 : orderOf x' = 2 := TwoThin.orderOf_mk_centralizer hxe hx
  have hVW : V ≤ centralizer ({x} : Set G) ⊓ C := by
    rcases hV with h | h
    · exact h.1
    · exact h.1
  have hVC : V ≤ C := hVW.trans inf_le_right
  have hI0V' : I0 ≤ V := hI0V.trans (Balance.oPrimeResidualOf_le_self V)
  have hres : I0.subgroupOf C ≤ oPrimeResidualOf 2 (V.subgroupOf C) := by
    intro i hi
    have hle : oPrimeResidualOf 2 V ≤ (oPrimeResidualOf 2 (V.subgroupOf C)).map C.subtype := by
      refine Balance.oPrimeResidualOf_le_of_two_elements fun v hv h2 => ?_
      refine ⟨⟨v, hVC hv⟩, Balance.mem_oPrimeResidualOf_of_two_element (mem_subgroupOf.2 hv) ?_, rfl⟩
      obtain ⟨k, hk⟩ := h2
      exact ⟨k, Subtype.ext hk⟩
    obtain ⟨j, hj, hji⟩ := hle (hI0V (mem_subgroupOf.1 hi))
    have : j = i := Subtype.ext hji
    rw [← this]
    exact hj
  rcases hV with hVs | hVp
  ·
    have hV' := Bg.Pu5.isSolvTwoCompSL23In_subgroupOf hxe hVs
    rcases Balance.solvableL2PrimeBalance_proved ↥C x' hx'2 _ hV' with h22 | ⟨L, hL, -, hVL⟩
    · exfalso
      apply hnot
      intro i hi
      exact ⟨⟨i, hVC (hI0V' hi)⟩, h22 (hres (mem_subgroupOf.2 hi)), rfl⟩
    · have hLc :=
        ((CFSG.ComponentClassification.PrimeComponentLift.prime_component_minimal_perfect_lift 2).2
          L hL).2.2
      refine ⟨L.map (piBar e), L.map (piBar e), hLc, hLc, ?_⟩
      rw [sup_idem]
      exact Subgroup.map_mono (hres.trans hVL)
  ·
    obtain ⟨-, -, L, hL, hcases, -⟩ := TwoThin.pumpupY_structure hx'2
      (TwoThin.le_centralizer_mk hVp.1 hxe) (TwoThin.isTwoComponent_centralizer_mk hVp hxe)
    refine ⟨L, CFSG.LocalAnalysis.ComponentInitial.conjSub (TwoThin.barMk ↥C x')⁻¹ L, hL,
      CFSG.LocalAnalysis.ComponentInitial.isComponent_conjSub hL _, ?_⟩
    have hAT : (V.subgroupOf C).map (TwoThin.barMk ↥C) ≤
        L ⊔ CFSG.LocalAnalysis.ComponentInitial.conjSub (TwoThin.barMk ↥C x')⁻¹ L := by
      rcases hcases with ⟨-, hAL⟩ | ⟨-, hAB, hAD⟩
      · exact hAL.trans le_sup_left
      · refine hAD.trans ?_
        rintro _ ⟨z, rfl⟩
        exact CFSG.LocalAnalysis.ComponentInitial.swapDiag_mem_sup hAB z
    refine (Subgroup.map_mono ?_).trans hAT
    intro i hi
    exact mem_subgroupOf.2 (hI0V' (mem_subgroupOf.1 hi))

omit [Finite G] in
theorem basic_facts {x y : G} {K E : Subgroup G} {Lb Ib : Subgroup (CentralizerBar x)} {I0 I1 : Subgroup G}
    (hx : orderOf x = 2) (h : SolvAdm x y K E Lb Ib) (hI : SolvLift x y E Lb I0 I1) {d e : G}
    (hd : d ∈ closure ({x, y} : Set G)) (hd1 : d ≠ 1) (he : e ∈ E) (he1 : e ≠ 1) :
    d * d = 1 ∧ orderOf d = 2 ∧ orderOf e = 2 ∧ x ∈ centralizer ({e} : Set G) ∧
      d ∈ centralizer ({e} : Set G) ∧ I1 ≤ centralizer ({d} : Set G) ⊓ centralizer ({e} : Set G) ∧
      I0 ≤ I1 := by
  have hset := h.setup
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hy2 : y ^ 2 = 1 := by rw [← hset.y_ord]; exact pow_orderOf_eq_one y
  have hxy : x * y = y * x := (mem_centralizer_singleton_iff.1 hset.y_mem).symm
  have hD := B1.isElementaryAbelian_closure_pair hxy hx2 hy2
  have hdd : d * d = 1 := (C3.Layer1.Back.forall_of_isElementaryAbelian hD).2 d hd
  have hdord : orderOf d = 2 := orderOf_eq_prime (by rw [sq]; exact hdd) hd1
  have hee : e * e = 1 := (C3.Layer1.Back.forall_of_isElementaryAbelian hset.E_ea).2 e he
  have heord : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact hee) he1
  have hex : e ∈ centralizer ({x} : Set G) := hset.E_le he
  have hxe : x ∈ centralizer ({e} : Set G) := TwoThin.mem_centralizer_symm hex
  have hey : e * y = y * e := h.centE e he
  have hde : d ∈ centralizer ({e} : Set G) := by
    have hcen : e ∈ centralizer ((closure ({x, y} : Set G) : Subgroup G) : Set G) := by
      rw [B1.centralizer_closure_pair]
      refine mem_inf.2 ⟨hex, ?_⟩
      rw [mem_centralizer_singleton_iff]
      exact hey
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.1 hcen d hd
  have hI1 : I1 ≤ centralizer ({d} : Set G) ⊓ centralizer ({e} : Set G) := by
    intro i hi
    have hc := hI.le_cent hi
    refine mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.1 hc d (mem_sup_left hd)).symm
    · rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.1 hc e (mem_sup_right he)).symm
  have hI01 : I0 ≤ I1 := by
    rw [← hI.res_I1]
    exact Balance.oPrimeResidualOf_le_self I1
  exact ⟨hdd, hdord, heord, hxe, hde, hI1, hI01⟩

theorem exists_comp_of_unstable' {x y : G} {K E : Subgroup G} {Lb Ib : Subgroup (CentralizerBar x)}
    {I0 I1 : Subgroup G} (hx : orderOf x = 2) (h : SolvAdm x y K E Lb Ib) (hI : SolvLift x y E Lb I0 I1)
    {d e : G} (hd : d ∈ closure ({x, y} : Set G)) (hd1 : d ≠ 1) (he : e ∈ E) (he1 : e ≠ 1)
    (hn : ¬ ⁅I0, pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ centralizer ({e} : Set G)⁆ ≤
      pPrimeCoreOf 2 (centralizer ({e} : Set G))) :
    ∃ J : Subgroup G, IsPCompIn 2 (centralizer ({e} : Set G)) J ∧ d ∈ normalizer (J : Set G) ∧
      d ∉ centralizerSection J (pPrimeCoreOf 2 J) ∧
      pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ centralizer ({e} : Set G) ≤ normalizer (J : Set G) ∧
      I1 ≤ normalizer (J : Set G) ∧
      ¬ ∀ n ∈ (⁅I0, pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ centralizer ({e} : Set G)⁆.subgroupOf
          (centralizer ({e} : Set G))).map (piBar e),
        ∀ z ∈ (J.subgroupOf (centralizer ({e} : Set G))).map (piBar e), n * z = z * n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({e} : Set G) with hC
  set Xe : Subgroup G := pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ C with hXe
  set X0 : Subgroup G := ⁅I0, Xe⁆ with hX0
  obtain ⟨hdd, hdord, -, hxe, hde, hI1, hI01⟩ := basic_facts hx h hI hd hd1 he he1
  have hI0 : I0 ≤ centralizer ({d} : Set G) ⊓ C := hI01.trans hI1
  have hXe_norm : I1 ≤ normalizer (Xe : Set G) := fun i hi =>
    inf_normalizer_le_normalizer_inf ⟨TwoThin.mem_normalizer_pPrimeCoreOf (le_normalizer (hI1 hi).1),
      le_normalizer (hI1 hi).2⟩
  have hX0Xe : X0 ≤ Xe := by
    rw [hX0, commutator_comm]
    exact Balance.SL23.comm_le_of_le_normalizer (hI01.trans hXe_norm)
  have hX0C : X0 ≤ C := hX0Xe.trans inf_le_right
  set N : Subgroup (CentralizerBar e) := (X0.subgroupOf C).map (piBar e) with hN
  have hN1 : N ≠ ⊥ := by
    intro hbot
    apply hn
    intro z hz
    have hzC : z ∈ C := hX0C hz
    have hmem : piBar e ⟨z, hzC⟩ ∈ N := ⟨⟨z, hzC⟩, mem_subgroupOf.2 hz, rfl⟩
    rw [hbot, mem_bot] at hmem
    exact ⟨⟨z, hzC⟩, (QuotientGroup.eq_one_iff _).1 hmem, rfl⟩
  have hNY : N ≤ (Xe.subgroupOf C).map (piBar e) :=
    Subgroup.map_mono fun z hz => mem_subgroupOf.2 (hX0Xe (mem_subgroupOf.1 hz))
  have hDd : ∀ b ∈ zpowers d, b ≠ 1 → b = d := fun b hb hb1 =>
    (B1.PilotS5.mem_zpowers_of_two hdord hb).resolve_left hb1
  have hDH : zpowers d ≤ C := (zpowers_le).2 hde
  have hDk : 2 ^ 1 ≤ Nat.card ↥(zpowers d) := by rw [Nat.card_zpowers, hdord]; norm_num
  have hD2 : ∀ b ∈ zpowers d, b * b = 1 := fun b hb => by
    rcases B1.PilotS5.mem_zpowers_of_two hdord hb with rfl | rfl
    · simp
    · exact hdd
  have hY : ∀ b ∈ zpowers d, b ≠ 1 → Xe ≤ pPrimeCoreOf 2 (centralizer ({b} : Set G)) :=
    fun b hb hb1 => by rw [hDd b hb hb1]; exact inf_le_left
  obtain ⟨J, hJ, hDJ, hfaith, hnc⟩ := Obs.exists_J (k := 1) le_rfl hDH hDk hD2 hY hNY hN1
  have hdJ : d ∈ normalizer (J : Set G) := hDJ (mem_zpowers d)
  have hXeJ : Xe ≤ normalizer (J : Set G) := by
    refine le_trans ?_ (Obs.inf_AG_le_normalizer hDH hD2 hJ hDJ (mem_zpowers d) hd1)
    refine le_inf ?_ inf_le_right
    refine le_iInf₂ fun b hb => ?_
    rw [hDd b hb.1 hb.2]
    exact inf_le_left
  have hnormiff : ∀ g' : ↥C, g' ∈ normalizer ((J.subgroupOf C : Subgroup ↥C) : Set ↥C) ↔
      (g' : G) ∈ normalizer (J : Set G) := by
    intro g'
    rw [← Subgroup.subgroupOf_normalizer_eq hJ.1]
    rfl
  obtain ⟨V, hV, hI0V⟩ := hI.quasi_e e he he1
  have hnot := not_le_O22_of_unstable hI0 hn
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_two_comps hx hxe hV hI0V hnot
  set Jb : Subgroup (CentralizerBar e) := (J.subgroupOf C).map (piBar e) with hJb
  have hJbc : IsComponent Jb :=
    ((CFSG.ComponentClassification.PrimeComponentLift.prime_component_minimal_perfect_lift 2).2 _
      hJ.2).2.2
  set R : Subgroup (CentralizerBar e) := (I0.subgroupOf C).map (piBar e) with hR
  set S : Subgroup (CentralizerBar e) := (I1.subgroupOf C).map (piBar e) with hS
  have hI1I0 : ∀ g ∈ I1, ∀ i ∈ I0, g * i * g⁻¹ ∈ I0 := by
    intro g hg i hi
    rw [← hI.res_I1] at hi ⊢
    have key : oPrimeResidualOf 2 I1 ≤ (oPrimeResidualOf 2 I1).comap (MulAut.conj g).toMonoidHom := by
      refine Balance.oPrimeResidualOf_le_of_two_elements fun v hv h2 => ?_
      obtain ⟨k, hk⟩ := h2
      show (MulAut.conj g) v ∈ oPrimeResidualOf 2 I1
      rw [MulAut.conj_apply]
      refine Balance.mem_oPrimeResidualOf_of_two_element (I1.mul_mem (I1.mul_mem hg hv) (I1.inv_mem hg))
        ⟨k, ?_⟩
      rw [conj_pow, hk, mul_one, mul_inv_cancel]
    exact key hi
  have hconjR : ∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨i, hi, rfl⟩
    refine ⟨g * i * g⁻¹, mem_subgroupOf.2 (hI1I0 _ (mem_subgroupOf.1 hg) _ (mem_subgroupOf.1 hi)), ?_⟩
    simp
  have hSR : S ≤ normalizer (R : Set (CentralizerBar e)) := fun s hs =>
    Balance.mem_normalizer_of_conj (fun r hr => hconjR s hs r hr)
      (fun r hr => hconjR s⁻¹ (S.inv_mem hs) r hr)
  have h2 : ∀ s ∈ S, ∃ m : ℕ, Odd m ∧ s ^ m ∈ R := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
    refine ⟨m, hm, ⟨g ^ m, mem_subgroupOf.2 ?_, map_pow _ _ _⟩⟩
    rw [← hI.res_I1]
    refine Balance.mem_oPrimeResidualOf_of_two_element (I1.pow_mem (mem_subgroupOf.1 hg) m) ⟨k, ?_⟩
    have h1 : (g ^ m) ^ (2 ^ k) = 1 := by
      rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
    simpa using congrArg Subtype.val h1
  have hLnc : ¬ ∀ r ∈ R, ∀ z ∈ Jb, r * z = z * r := by
    intro hall
    apply hnc
    have hle : X0 ≤ ((centralizer (Jb : Set (CentralizerBar e))).comap (piBar e)).map C.subtype := by
      rw [hX0, Subgroup.commutator_le]
      intro i hi w hw
      have hiC : i ∈ C := (hI0 hi).2
      have hwC : w ∈ C := hw.2
      refine ⟨⁅(⟨i, hiC⟩ : ↥C), ⟨w, hwC⟩⁆, ?_, rfl⟩
      show piBar e ⁅(⟨i, hiC⟩ : ↥C), ⟨w, hwC⟩⁆ ∈ centralizer (Jb : Set (CentralizerBar e))
      rw [map_commutatorElement, mem_centralizer_iff]
      have hiJ : ∀ z ∈ Jb, piBar e ⟨i, hiC⟩ * z = z * piBar e ⟨i, hiC⟩ :=
        hall _ ⟨⟨i, hiC⟩, mem_subgroupOf.2 hi, rfl⟩
      have hwJ : piBar e ⟨w, hwC⟩ ∈ normalizer (Jb : Set (CentralizerBar e)) :=
        Subgroup.le_normalizer_map (piBar e) ⟨⟨w, hwC⟩, (hnormiff _).2 (hXeJ hw), rfl⟩
      intro z hz
      exact (commutatorElement_commute hiJ hwJ z hz).symm
    rintro _ ⟨x0, hx0, rfl⟩ z hz
    obtain ⟨c, hc, hcx⟩ := hle (mem_subgroupOf.1 hx0)
    have : c = x0 := Subtype.ext hcx
    rw [← this]
    exact (mem_centralizer_iff.1 hc z hz).symm
  have hconj := conjSub_eq_of_two_comps hA hB hJbc hAB hSR h2 hLnc
  have hI1J : I1 ≤ normalizer (J : Set G) := by
    intro g hg
    have hgC : g ∈ C := (hI1 hg).2
    have h1 := hconj (piBar e ⟨g, hgC⟩) ⟨⟨g, hgC⟩, mem_subgroupOf.2 hg, rfl⟩
    have hn1 := mem_normalizer_of_conjSub_eq h1
    have hn2 := CFSG.ComponentClassification.UnbalancedLayer.mem_normalizer_of_map hJ.2 hn1
    exact (hnormiff ⟨g, hgC⟩).1 hn2
  exact ⟨J, hJ, hdJ, hfaith d (mem_zpowers d) hd1, hXeJ, hI1J, hnc⟩

end SolvP101

end CFSG.GH74.Generic.BProg.B3
