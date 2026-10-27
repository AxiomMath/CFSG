module

public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicBender
public import CFSG.LocalAnalysis.EvenBN.GMSK.SporadicONOuter
public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22
public import CFSG.Sporadic.HNOddCore.OuterFix
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseBabySchreier
public import CFSG.Monster.B.CTIB.ComponentsSeventeen

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

namespace SporadicBender

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy IsoInvariant
  isoInvariant_card_quotient_center)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

section Unitary

open CFSG.GH74.Uniqueness.Bender CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups

variable {X : Type} [Group X] {n : ℕ}

theorem benderType_of_lieModel_PSU3 (h : LieModel X .PSU 3 2 n) :
    BenderType X n 3 ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) := by
  obtain ⟨e⟩ := exists_mulEquiv_psu3_of_lieModel_PSU3 h
  have hmodel : PSU3Model n = CFSG.Open.PSU3 2 n := CFSG.Models.benderPSU3Model_eq_psu3 n
  exact .unitary n (two_le_of_lieModel_PSU3 h) (e.trans (MulEquiv.subgroupCongr hmodel.symm))

theorem card_outer_of_lieModel_PSU3 (h : LieModel X .PSU 3 2 n) :
    Nat.card (Outer X) = 2 * n * Nat.gcd 3 (2 ^ n + 1) := by
  obtain ⟨Dd, _, -, hDd, -, hQ⟩ := (benderType_of_lieModel_PSU3 h).outer_unitary
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Dd, hDd, hQ]

theorem card_centralizer_of_lieModel_PSU3
    (h : LieModel X .PSU 3 2 n) {z : X} (hz : orderOf z = 2) :
    Nat.card (centralizer ({z} : Set X)) =
      (2 ^ n) ^ 3 * ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) := by
  have := finite_of_lieModel_PSU3 h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨t, ht⟩ := (benderType_of_lieModel_PSU3 h).exists_benderCore Q
  have hzQ : z ∈ (Q : Subgroup X) := hQ (mem_zpowers z)
  have hzZ := ht.center_of_involution z (le_borel _ hzQ) hz
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    omega
  exact ht.card_centralizer hzZ hz1

end Unitary

open CFSG.ONSchreier CFSG.Sporadic.ONOddCore in
theorem on_outer_fixed_centralizer
    {D : Type} [Group D] (hON : NativeSporadic.IsSporadic D .ONan) {α : MulAut D}
    (hα : orderOf α = 2) (hout : α ∉ inner D) {t : D} (ht : orderOf t = 2) (hαt : α t = t) :
    CFSG.oddCore ↥(α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer ({t} : Set D)) = ⊥ ∧
      ∃ x ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer ({t} : Set D),
        orderOf x = 5 ∨ orderOf x = 7 := by
  obtain ⟨e⟩ := hON
  set θ : D ≃* Pv := e.trans onEquivPv
  have ha : orderOf ((θ t : Pv) : Equiv.Perm (Fin N)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  obtain ⟨g, hg, hga⟩ := cti_on_all_involutions_conjugate _ (θ t).2 ha
  set gP : Pv := ⟨g, hg⟩
  set Θ : D ≃* Pv := θ.trans (MulAut.conj gP⁻¹)
  have hΘt : Θ t = zP := by
    apply Subtype.ext
    change g⁻¹ * ((θ t : Pv) : Equiv.Perm (Fin N)) * g⁻¹⁻¹ = onz
    rw [hga]
    group
  set γ := MulAut.congr Θ α
  have hγ2 : orderOf γ = 2 := (Sporadic.orderOf_congr Θ α).trans hα
  have hγout : γ ∉ (MulAut.conj : Pv →* MulAut Pv).range :=
    fun hb => hout ((Sporadic.congr_mem_inner_iff Θ α).1 hb)
  have hγγ : γ * γ = 1 := Sporadic.mul_self_eq_one_of_orderOf_eq_two hγ2
  have hz : γ zP = zP := by
    rw [← hΘt]
    change Θ (α (Θ.symm (Θ t))) = Θ t
    rw [MulEquiv.symm_apply_apply, hαt]
  refine ⟨?_, ?_⟩
  · have h1 := oddCore_fixed_centralizer hγout hγγ (a := zP)
      (by rw [← hΘt, MulEquiv.orderOf_eq, ht]) hz
    have e1 := fixedCentCongr Θ α t
    rw [hΘt] at e1
    exact CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.oddCore_eq_bot_of_mulEquiv
      e1.symm h1
  · obtain ⟨-, hLm, -, A, hA⟩ := ctuc_on_outer_local_quotient_is_graph_or_field.2.2 γ hγout hz
    rcases hA with hc | hc
    · obtain ⟨-, w, -, -, hw, hw5⟩ := Sporadic.exists_fixed_three_five_of_graph A
        (by rw [sq]; exact induced_sq hγγ hLm hc)
      obtain ⟨x, hx, hxr⟩ := Sporadic.on_outer_exists_fixed_of_quotient Θ hΘt hz hc hw
        (by norm_num) (by norm_num) hw5
      exact ⟨x, hx, Or.inl hxr⟩
    · obtain ⟨-, w, -, -, hw, hw7⟩ := Sporadic.exists_fixed_three_seven_of_field A
        (by rw [sq]; exact induced_sq hγγ hLm hc)
      obtain ⟨x, hx, hxr⟩ := Sporadic.on_outer_exists_fixed_of_quotient Θ hΘt hz hc hw
        (by norm_num) (by norm_num) hw7
      exact ⟨x, hx, Or.inr hxr⟩

theorem on_outer_U3_false
    {D : Type} [Group D] [Finite D] (hON : NativeSporadic.IsSporadic D .ONan) {n : ℕ}
    {α : MulAut D} {S : Subgroup D} (d : FixedRootDatumOf T_U3 D n α S) (hout : α ∉ inner D) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSs, hnab⟩ := simple_of_T_U3 d.type
  have hU : LieModel S .PSU 3 2 n := d.type.2
  have hn := d.type.1
  have hSD : Nat.card S ∣ 460815505920 := by
    obtain ⟨e⟩ := hON
    rw [← CFSG.Sporadic.ON.card_ON]
    change Nat.card S ∣ Nat.card (NativeSporadic.Carrier .ONan)
    rw [← Nat.card_congr e.toEquiv]
    exact Subgroup.card_subgroup_dvd_card S
  have h3 : 3 * n ≤ 9 := le_of_two_pow_dvd (h := 900030285) (by decide)
    ((two_pow_dvd_card_of_T_U3 d.type).trans (hSD.trans (by norm_num)))
  have hn3 : n = 3 := by
    have : n ≤ 3 := by omega
    interval_cases n
    · rw [card_eq_u3Order d.type] at hSD
      revert hSD
      decide
    · rfl
  subst hn3
  obtain ⟨s, hs2⟩ : ∃ s : S, orderOf s = 2 := exists_prime_orderOf_dvd_card' 2
    ((dvd_pow_self 2 (by norm_num : 3 * 3 ≠ 0)).trans (two_pow_dvd_card_of_T_U3 d.type))
  have htS : (s : D) ∈ S := s.2
  have ht : orderOf (s : D) = 2 := by rw [Subgroup.orderOf_coe, hs2]
  obtain ⟨hcore, x, hx, hxr⟩ := on_outer_fixed_centralizer hON d.orderOf_eq hout ht
    (d.le_fixed htS)
  have hO : Nat.card (Outer S) = 18 := by
    rw [card_outer_of_lieModel_PSU3 hU]
    norm_num
  have hcent : Nat.card (centralizer ({s} : Set S)) = 1536 := by
    rw [card_centralizer_of_lieModel_PSU3 hU hs2]
    norm_num
  obtain ⟨r, hr, hxr, hr18, hr1536⟩ : ∃ r : ℕ, r.Prime ∧ orderOf x = r ∧ ¬ r ∣ 18 ∧
      ¬ r ∣ 1536 := by
    rcases hxr with h | h
    · exact ⟨5, by norm_num, h, by norm_num, by norm_num⟩
    · exact ⟨7, by norm_num, h, by norm_num, by norm_num⟩
  have hxS := d.mem_of_prime_of_outer hSs hnab hout htS hcore hx hr hxr (hO ▸ hr18)
  have hxc : (⟨x, hxS⟩ : S) ∈ centralizer ({s} : Set S) := by
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 hx).2)
  have hdvd := orderOf_dvd_natCard (⟨⟨x, hxS⟩, hxc⟩ : centralizer ({s} : Set S))
  rw [hcent, Subgroup.orderOf_mk, Subgroup.orderOf_mk, hxr] at hdvd
  exact hr1536 hdvd

open CFSG.Sporadic.ONOddCore
  (cti_on_involution_local_components_projective_linear_quotient_order) in
theorem on_benderFree :
    BenderFixedRootFree .ONan := by
  refine ⟨fun D _ _ hD hs n α S d => ?_, sporadicFixedRootFreeOf_of_card CFSG.Sporadic.ON.card_ON
    fun _ _ _ hX => not_dvd_of_check_Sz hX (e := 9) (h := 900030285) (by norm_num) (by decide)
      (by decide)⟩
  obtain ⟨hSs, hnab⟩ := simple_of_T_U3 d.type
  by_cases hα : α ∈ inner D
  · refine d.false_of_inner_comps hD hSs hnab hα (isoInvariant_card_quotient_center {20160}) ?_
      fun t ht B hB => Set.mem_singleton_iff.2
        (cti_on_involution_local_components_projective_linear_quotient_order hs t ht B hB)
    rw [Set.mem_singleton_iff, card_quotient_center_eq hSs hnab]
    exact ne_of_check_U3 d.type (e := 6) (h := 315) (by norm_num) (by decide) (by decide)
  · exact on_outer_U3_false hs d hα

theorem not_mem_singleton_of_ne {x a : ℕ} (h : x ≠ a) : x ∉ ({a} : Set ℕ) :=
  fun h' => h (Set.mem_singleton_iff.1 h')

theorem not_mem_pair_of_ne {x a b : ℕ} (ha : x ≠ a) (hb : x ≠ b) : x ∉ ({a, b} : Set ℕ) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨ha, hb⟩

theorem sporadicFixedRootFreeOf_of_card_quotient_center {T : StdType}
    {s : TauCeti.SporadicName} {Ni No : Set ℕ}
    (hT : ∀ (n : ℕ) (X : Type) [Group X] [Finite X], T n X →
      IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧ Nat.card X ∉ Ni ∧ Nat.card X ∉ No)
    (hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G)) fun Y _ => Nat.card (Y ⧸ center Y) ∈ Ni)
    (hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ β : MulAut G, orderOf β = 2 → β ∉ inner G →
        CompsSatisfy (CFSG.Sporadic.Schreier.fixSub β) fun Y _ => Nat.card (Y ⧸ center Y) ∈ No) :
    SporadicFixedRootFreeOf T s :=
  sporadicFixedRootFreeOf_of_comps (isoInvariant_card_quotient_center Ni)
    (isoInvariant_card_quotient_center No)
    (fun n X _ _ hX => by
      obtain ⟨hs, hnab, hi, ho⟩ := hT n X hX
      exact ⟨hs, hnab, by rwa [card_quotient_center_eq hs hnab],
        by rwa [card_quotient_center_eq hs hnab]⟩)
    hin hout

open CFSG.ComponentClassification.RestrictedStd.Spor (co1LocalComponentsInput_holds) in
theorem co1_benderFree :
    BenderFixedRootFree .Co1 := by
  have hinner : ∀ β : MulAut (NativeSporadic.Carrier .Co1),
      β ∈ inner (NativeSporadic.Carrier .Co1) := fun β => by
    obtain ⟨g, hg⟩ := CFSG.Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
      CFSG.Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner β
    exact ⟨g, hg.symm⟩
  have hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .Co1) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G))
          fun Y _ => Nat.card (Y ⧸ center Y) ∈ ({251596800} : Set ℕ) :=
    fun G _ _ _ ⟨e⟩ t ht B hB =>
      Set.mem_singleton_iff.2 (co1LocalComponentsInput_holds G e t ht B hB).1
  refine ⟨sporadicFixedRootFreeOf_of_card_quotient_center (No := ∅) (fun _ _ _ _ hX =>
      ⟨(simple_of_T_U3 hX).1, (simple_of_T_U3 hX).2, ?_, Set.notMem_empty _⟩) hin
      (Sporadic.outer_comps_of_forall_inner hinner _),
    sporadicFixedRootFreeOf_of_card_quotient_center (No := ∅) (fun _ _ _ _ hX =>
      ⟨(simple_of_T_Sz hX).1, (simple_of_T_Sz hX).2, ?_, Set.notMem_empty _⟩) hin
      (Sporadic.outer_comps_of_forall_inner hinner _)⟩
  all_goals first
    | exact not_mem_singleton_of_ne
        (ne_of_check_U3 hX (e := 12) (h := 61425) (by norm_num) (by decide) (by decide))
    | exact not_mem_singleton_of_ne
        (ne_of_check_Sz hX (e := 12) (h := 61425) (by norm_num) (by decide) (by decide))

open CFSG.Sporadic.FischerOddCore in
theorem fi22_benderFree :
    BenderFixedRootFree .Fi22 := by
  have hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .Fi22) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G))
          fun Y _ => Nat.card (Y ⧸ center Y) ∈ ({9196830720} : Set ℕ) :=
    fun G _ _ _ ⟨e⟩ t ht B hB => Set.mem_singleton_iff.2
      (CTI_Fi22_involution_local_components_unitary_quotient_order e t ht B hB)
  have hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .Fi22) → ∀ β : MulAut G, orderOf β = 2 →
        β ∉ inner G → CompsSatisfy (CFSG.Sporadic.Schreier.fixSub β)
          fun Y _ => Nat.card (Y ⧸ center Y) ∈ ({174182400, 1451520} : Set ℕ) := by
    intro G _ _ hG hGs β hβ2 hβ B hB
    rcases fi22OuterComponentsInput_holds G hGs β
        (Sporadic.mul_self_eq_one_of_orderOf_eq_two hβ2) hβ B hB with h | h <;> simp [h]
  refine ⟨sporadicFixedRootFreeOf_of_card_quotient_center (fun _ _ _ _ hX =>
      ⟨(simple_of_T_U3 hX).1, (simple_of_T_U3 hX).2, ?_, ?_⟩) hin hout,
    sporadicFixedRootFreeOf_of_card_quotient_center (fun _ _ _ _ hX =>
      ⟨(simple_of_T_Sz hX).1, (simple_of_T_Sz hX).2, ?_, ?_⟩) hin hout⟩
  · exact not_mem_singleton_of_ne
      (ne_of_check_U3 hX (e := 15) (h := 280665) (by norm_num) (by decide) (by decide))
  · exact not_mem_pair_of_ne
      (ne_of_check_U3 hX (e := 12) (h := 42525) (by norm_num) (by decide) (by decide))
      (ne_of_check_U3 hX (e := 9) (h := 2835) (by norm_num) (by decide) (by decide))
  · exact not_mem_singleton_of_ne
      (ne_of_check_Sz hX (e := 15) (h := 280665) (by norm_num) (by decide) (by decide))
  · exact not_mem_pair_of_ne
      (ne_of_check_Sz hX (e := 12) (h := 42525) (by norm_num) (by decide) (by decide))
      (ne_of_check_Sz hX (e := 9) (h := 2835) (by norm_num) (by decide) (by decide))

open CFSG.ComponentClassification.RestrictedStd.Spor (fi23_inner_comps) in
theorem fi23_benderFree :
    BenderFixedRootFree .Fi23 := by
  have hinner : ∀ β : MulAut (NativeSporadic.Carrier .Fi23),
      β ∈ inner (NativeSporadic.Carrier .Fi23) := fun β => by
    change β ∈ inner NativeSporadic.Fi23
    rw [CFSG.Sporadic.FischerOddCore.CTUC_Fi23_all_automorphisms_inner.1]
    trivial
  have hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .Fi23) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G)) fun Y _ =>
          Nat.card (Y ⧸ center Y) ∈ ({64561751654400, 9196830720} : Set ℕ) :=
    fun G _ _ _ ⟨e⟩ t ht => fi23_inner_comps e t ht
  refine ⟨sporadicFixedRootFreeOf_of_card_quotient_center (No := ∅) (fun _ _ _ _ hX =>
      ⟨(simple_of_T_U3 hX).1, (simple_of_T_U3 hX).2, ?_, Set.notMem_empty _⟩) hin
      (Sporadic.outer_comps_of_forall_inner hinner _),
    sporadicFixedRootFreeOf_of_card_quotient_center (No := ∅) (fun _ _ _ _ hX =>
      ⟨(simple_of_T_Sz hX).1, (simple_of_T_Sz hX).2, ?_, Set.notMem_empty _⟩) hin
      (Sporadic.outer_comps_of_forall_inner hinner _)⟩
  all_goals first
    | exact not_mem_pair_of_ne
        (ne_of_check_U3 hX (e := 17) (h := 492567075) (by norm_num) (by decide) (by decide))
        (ne_of_check_U3 hX (e := 15) (h := 280665) (by norm_num) (by decide) (by decide))
    | exact not_mem_pair_of_ne
        (ne_of_check_Sz hX (e := 17) (h := 492567075) (by norm_num) (by decide) (by decide))
        (ne_of_check_Sz hX (e := 15) (h := 280665) (by norm_num) (by decide) (by decide))

open CFSG.Sporadic.FischerOddCore in
theorem fi24prime_benderFree :
    BenderFixedRootFree .Fi24Prime := by
  have hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .Fi24Prime) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G))
          fun Y _ => Nat.card (Y ⧸ center Y) ∈ ({64561751654400} : Set ℕ) :=
    fun G _ _ _ ⟨e⟩ t ht B hB => Set.mem_singleton_iff.2
      (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven
        e t ht B hB).1
  have hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .Fi24Prime) → ∀ β : MulAut G, orderOf β = 2 →
        β ∉ inner G → CompsSatisfy (CFSG.Sporadic.Schreier.fixSub β) fun Y _ =>
          Nat.card (Y ⧸ center Y) ∈ ({4089470473293004800, 9196830720} : Set ℕ) := by
    intro G _ _ hG hGs β hβ2 hβ B hB
    rcases fi24primeOuterComponentsInput_holds G hGs β
        (Sporadic.mul_self_eq_one_of_orderOf_eq_two hβ2) hβ B hB with h | h <;> simp [h]
  refine ⟨sporadicFixedRootFreeOf_of_card_quotient_center (fun _ _ _ _ hX =>
      ⟨(simple_of_T_U3 hX).1, (simple_of_T_U3 hX).2, ?_, ?_⟩) hin hout,
    sporadicFixedRootFreeOf_of_card_quotient_center (fun _ _ _ _ hX =>
      ⟨(simple_of_T_Sz hX).1, (simple_of_T_Sz hX).2, ?_, ?_⟩) hin hout⟩
  · exact not_mem_singleton_of_ne
      (ne_of_check_U3 hX (e := 17) (h := 492567075) (by norm_num) (by decide) (by decide))
  · exact not_mem_pair_of_ne
      (ne_of_check_U3 hX (e := 18) (h := 15600091832325) (by norm_num) (by decide) (by decide))
      (ne_of_check_U3 hX (e := 15) (h := 280665) (by norm_num) (by decide) (by decide))
  · exact not_mem_singleton_of_ne
      (ne_of_check_Sz hX (e := 17) (h := 492567075) (by norm_num) (by decide) (by decide))
  · exact not_mem_pair_of_ne
      (ne_of_check_Sz hX (e := 18) (h := 15600091832325) (by norm_num) (by decide) (by decide))
      (ne_of_check_Sz hX (e := 15) (h := 280665) (by norm_num) (by decide) (by decide))

open CFSG.ComponentClassification.RestrictedStd.Spor (hnLocalComponentsInput_holds
  compsSatisfy_perm_ten) in
theorem hn_benderFree :
    BenderFixedRootFree .HN := by
  have hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .HN) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G))
          fun Y _ => Nat.card (Y ⧸ center Y) ∈ ({44352000} : Set ℕ) :=
    fun G _ _ _ ⟨e⟩ t ht B hB =>
      Set.mem_singleton_iff.2 (hnLocalComponentsInput_holds G e t ht B hB)
  have hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .HN) → ∀ β : MulAut G, orderOf β = 2 →
        β ∉ inner G → CompsSatisfy (CFSG.Sporadic.Schreier.fixSub β)
          fun Y _ => Nat.card (Y ⧸ center Y) ∈ ({1814400} : Set ℕ) := by
    intro G _ _ _ ⟨e⟩ β hβ2 hβ
    obtain ⟨eS⟩ := CFSG.Sporadic.HNOddCore.hn_outer_involution_fixSub e β hβ2 hβ
    exact CompsSatisfy.of_mulEquiv (isoInvariant_card_quotient_center _) eS
      compsSatisfy_perm_ten
  refine ⟨sporadicFixedRootFreeOf_of_card_quotient_center (fun _ _ _ _ hX =>
      ⟨(simple_of_T_U3 hX).1, (simple_of_T_U3 hX).2, ?_, ?_⟩) hin hout,
    sporadicFixedRootFreeOf_of_card_quotient_center (fun _ _ _ _ hX =>
      ⟨(simple_of_T_Sz hX).1, (simple_of_T_Sz hX).2, ?_, ?_⟩) hin hout⟩
  · exact not_mem_singleton_of_ne
      (ne_of_check_U3 hX (e := 9) (h := 86625) (by norm_num) (by decide) (by decide))
  · exact not_mem_singleton_of_ne
      (ne_of_check_U3 hX (e := 7) (h := 14175) (by norm_num) (by decide) (by decide))
  · exact not_mem_singleton_of_ne
      (ne_of_check_Sz hX (e := 9) (h := 86625) (by norm_num) (by decide) (by decide))
  · exact not_mem_singleton_of_ne
      (ne_of_check_Sz hX (e := 7) (h := 14175) (by norm_num) (by decide) (by decide))

open CFSG.ComponentClassification.RestrictedStd.Spor (compsSatisfy_of_charP) in
theorem th_benderFree :
    BenderFixedRootFree .Th := by
  have hinner : ∀ β : MulAut (NativeSporadic.Carrier .Th),
      β ∈ inner (NativeSporadic.Carrier .Th) := fun β => by
    have h : inner (NativeSporadic.Carrier .Th) = ⊤ := CFSG.Sporadic.ThSchreier.inner_Th
    rw [h]
    trivial
  have hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .Th) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G)) fun _ _ => False :=
    fun G _ _ _ hG t ht => compsSatisfy_of_charP
      ((CFSG.Sporadic.ThSchreier.ctuc_Th_inner_involution_centralizers_characteristic_two.2.2
        G hG).1 t ht).1 _
  exact ⟨sporadicFixedRootFreeOf_of_comps (Qi := fun _ _ => False) (Qo := fun _ _ => False)
      (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
      (fun _ _ _ _ hX => ⟨(simple_of_T_U3 hX).1, (simple_of_T_U3 hX).2, id, id⟩) hin
      (Sporadic.outer_comps_of_forall_inner hinner _),
    sporadicFixedRootFreeOf_of_comps (Qi := fun _ _ => False) (Qo := fun _ _ => False)
      (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
      (fun _ _ _ _ hX => ⟨(simple_of_T_Sz hX).1, (simple_of_T_Sz hX).2, id, id⟩) hin
      (Sporadic.outer_comps_of_forall_inner hinner _)⟩

theorem b_benderFree :
    BenderFixedRootFree .B := by
  have hinner : ∀ β : MulAut (NativeSporadic.Carrier .B),
      β ∈ inner (NativeSporadic.Carrier .B) :=
    CFSG.ComponentClassification.BMCase.inner_of_mulEquiv_pinnedB NativeSporadic.B
      ⟨MulEquiv.refl NativeSporadic.B⟩
  have hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .B) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G)) fun Y _ => Nat.card (Y ⧸ center Y) ∈
          ({76532479683774853939200, 3311126603366400} : Set ℕ) := by
    intro G _ _ _ ⟨e⟩ t ht K hK
    obtain ⟨-, hiso, -⟩ :=
      CFSG.Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen
        ⟨e⟩ t ht K hK
    rcases hiso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · left
      rw [Nat.card_congr φ.toEquiv, CFSG.LieType.Chevalley.C2E6Std.card_stdGroup]
    · right
      obtain ⟨ψ⟩ := CFSG.Monster.B.E6.StdF4Radical.nonempty_groupJ_mulEquiv_F4
      rw [Set.mem_singleton_iff, Nat.card_congr φ.toEquiv, ← Nat.card_congr ψ.toEquiv,
        CFSG.Monster.B.E6.FieldInvF4.card_groupJ]
  refine ⟨sporadicFixedRootFreeOf_of_card_quotient_center (No := ∅) (fun _ _ _ _ hX =>
      ⟨(simple_of_T_U3 hX).1, (simple_of_T_U3 hX).2, ?_, Set.notMem_empty _⟩) hin
      (Sporadic.outer_comps_of_forall_inner hinner _),
    sporadicFixedRootFreeOf_of_card_quotient_center (No := ∅) (fun _ _ _ _ hX =>
      ⟨(simple_of_T_Sz hX).1, (simple_of_T_Sz hX).2, ?_, Set.notMem_empty _⟩) hin
      (Sporadic.outer_comps_of_forall_inner hinner _)⟩
  all_goals first
    | exact not_mem_pair_of_ne
        (ne_of_check_U3 hX (e := 36) (h := 1113694156575) (by norm_num) (by decide) (by decide))
        (ne_of_check_U3 hX (e := 24) (h := 197358525) (by norm_num) (by decide) (by decide))
    | exact not_mem_pair_of_ne
        (ne_of_check_Sz hX (e := 36) (h := 1113694156575) (by norm_num) (by decide) (by decide))
        (ne_of_check_Sz hX (e := 24) (h := 197358525) (by norm_num) (by decide) (by decide))

theorem m_fixedRootFreeOf
    {T : StdType}
    (hT : ∀ (n : ℕ) (X : Type) [Group X] [Finite X], T n X → IsSimpleGroup X ∧
      (∃ a b : X, a * b ≠ b * a) ∧ ¬ (2 ^ 41 ∣ Nat.card X ∧ ¬ 2 ^ 42 ∣ Nat.card X)) :
    SporadicFixedRootFreeOf T .M := by
  intro D _ _ hD hs n α S d
  obtain ⟨hSs, hnab, h41⟩ := hT n S d.type
  have hα : α ∈ inner D := CFSG.ComponentClassification.CatLeafProof.monsterInnerInput D hD hs α
  refine d.false_of_inner_comps hD hSs hnab hα
    (isoInvariant_card_quotient_center {N | 2 ^ 41 ∣ N ∧ ¬ 2 ^ 42 ∣ N}) ?_
    fun t ht B hB =>
      CFSG.ComponentClassification.CatLeafProof.monsterLocalComponentsInput D hD hs t ht B hB
  rw [Set.mem_ofPred_eq, card_quotient_center_eq hSs hnab]
  exact h41

theorem not_two_part_forty_one {N c n : ℕ} (hN : N ≠ 0) (h2 : N.factorization 2 = c * n)
    (hc : c * n ≠ 41) : ¬ (2 ^ 41 ∣ N ∧ ¬ 2 ^ 42 ∣ N) := by
  rintro ⟨h41, h42⟩
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hN, h2] at h41 h42
  omega

theorem m_benderFree
    :
    BenderFixedRootFree .M :=
  ⟨m_fixedRootFreeOf fun _ _ _ _ hX => ⟨(simple_of_T_U3 hX).1, (simple_of_T_U3 hX).2,
      not_two_part_forty_one Nat.card_pos.ne' (factorization_two_card_of_lieModel_PSU3 hX.2)
        (by omega)⟩,
    m_fixedRootFreeOf fun _ _ _ _ hX => ⟨(simple_of_T_Sz hX).1, (simple_of_T_Sz hX).2,
      not_two_part_forty_one Nat.card_pos.ne' (factorization_two_card_of_lieModel_twistedB2 hX)
        (by omega)⟩⟩

theorem benderFixedRootFree
    (s : TauCeti.SporadicName) :
    BenderFixedRootFree s := by
  cases s with
  | M11 => exact m11_benderFree
  | M12 => exact m12_benderFree
  | M22 => exact m22_benderFree
  | M23 => exact m23_benderFree
  | M24 => exact m24_benderFree
  | J1 => exact j1_benderFree
  | J2 => exact j2_benderFree
  | J3 => exact j3_benderFree
  | J4 => exact j4_benderFree
  | HS => exact hs_benderFree
  | McL => exact mcl_benderFree
  | He => exact he_benderFree
  | Ru => exact ru_benderFree
  | Suz => exact suz_benderFree
  | ONan => exact on_benderFree
  | Co1 => exact co1_benderFree
  | Co2 => exact co2_benderFree
  | Co3 => exact co3_benderFree
  | Fi22 => exact fi22_benderFree
  | Fi23 => exact fi23_benderFree
  | Fi24Prime => exact fi24prime_benderFree
  | HN => exact hn_benderFree
  | Ly => exact ly_benderFree
  | Th => exact th_benderFree
  | B => exact b_benderFree
  | M => exact m_benderFree

end SporadicBender

open CFSG.Blueprint SporadicBender

theorem fixedRootSelectorOf_sporadicRep_U3 :
    FixedRootSelectorOf T_U3 SurvU3 fun D _ => NativeSporadic.SporadicRep D :=
  fun D _ _ hD ⟨s, hs⟩ n α S d => ((benderFixedRootFree s).1 D hD hs n α S d).elim

theorem fixedRootSelectorOf_sporadicRep_Sz :
    FixedRootSelectorOf T_Sz SurvSz fun D _ => NativeSporadic.SporadicRep D :=
  fun D _ _ hD ⟨s, hs⟩ n α S d => ((benderFixedRootFree s).2 D hD hs n α S d).elim

end CFSG.LocalAnalysis.EvenBN.GMSK
