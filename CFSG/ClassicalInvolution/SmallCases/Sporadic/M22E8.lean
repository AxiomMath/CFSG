module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22
public import CFSG.GroupTheory.NonabelianOrderSixCore
public import Certificates.Certificate9316

public section


namespace CFSG.ClassicalInvolution

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native
open scoped commutatorElement

theorem m22E8_check : m22E8Check = true :=
  Certificates.certificate9316

theorem m22E8_facts : M22E8Facts :=
  m22E8Facts_of_check m22E8_check

abbrev m22E8K : Subgroup (Equiv.Perm (Fin 22)) := m22CentQ1.originalSubgroup

theorem m22E8UL_data :
    (1 : Equiv.Perm (Fin 22)) ∈ m22E8UL ∧
      (∀ x ∈ m22E8UL, ∀ y ∈ m22E8UL, x * y ∈ m22E8UL) ∧
      (∀ x ∈ m22E8UL, x⁻¹ ∈ m22E8UL) ∧
      (∀ u ∈ m22E8UL, u ∈ m22E8KL) ∧
      (∀ u ∈ m22E8UL, u ^ 2 ^ 6 = 1) ∧
      (∀ g ∈ m22E8KL, ∀ u ∈ m22E8UL, g * u * g⁻¹ ∈ m22E8UL) ∧
      (∀ g ∈ m22E8KL, (∀ u ∈ m22E8UL, g * u = u * g) → g ∈ m22E8UL) := by
  have h := m22_U1_check
  simp only [twoConstrainedCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, hmul⟩, hinv⟩, hUK⟩, hpow⟩, hnorm⟩, hself⟩ := h
  refine ⟨by simpa [m22E8UL] using h1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    simpa [m22E8UL] using hmul x (by simpa [m22E8UL] using hx) y (by simpa [m22E8UL] using hy)
  · intro x hx
    simpa [m22E8UL] using hinv x (by simpa [m22E8UL] using hx)
  · intro u hu
    simpa [m22E8UL, m22E8KL] using hUK u (by simpa [m22E8UL] using hu)
  · intro u hu
    simpa [m22E8UL] using hpow u (by simpa [m22E8UL] using hu)
  · intro g hg u hu
    simpa [m22E8UL, m22E8KL] using hnorm g (by simpa [m22E8KL] using hg) u (by simpa [m22E8UL] using hu)
  · intro g hg hc
    rcases hself g (by simpa [m22E8KL] using hg) with hfalse | hmem
    · have htrue : (m22E8UL.all fun u => decide (g * u = u * g)) = true :=
        List.all_eq_true.2 fun u hu => decide_eq_true (hc u hu)
      have hfalseUL : (m22E8UL.all fun u => decide (g * u = u * g)) = false := by
        simpa [m22E8UL] using hfalse
      rw [htrue] at hfalseUL
      exact Bool.noConfusion hfalseUL
    · simpa [m22E8UL] using hmem

noncomputable abbrev m22E8U : Subgroup (Equiv.Perm (Fin 22)) :=
  subgroupOfList m22E8UL (m22E8UL_data.1) (m22E8UL_data.2.1) (m22E8UL_data.2.2.1)

private theorem permClosureList_subset_closure {n : ℕ}
    (gens : List (Equiv.Perm (Fin n))) (fuel : ℕ) :
    ∀ x ∈ permClosureList gens fuel, x ∈ Subgroup.closure {g | g ∈ gens} := by
  induction fuel with
  | zero =>
      intro x hx
      have hx1 : x = 1 := by simpa [permClosureList] using hx
      exact hx1 ▸ Subgroup.one_mem _
  | succ fuel ih =>
      intro x hx
      rw [permClosureList, List.range_succ, List.foldl_append] at hx
      simp only [List.foldl_cons, List.foldl_nil, List.mem_eraseDups, List.mem_append,
        List.mem_flatMap, List.mem_map] at hx
      rcases hx with hx | ⟨y, hy, g, hg, rfl⟩
      · exact ih x hx
      · simpa [tab_eq] using
          (Subgroup.closure {g | g ∈ gens}).mul_mem (ih y hy) (Subgroup.subset_closure hg)

theorem m22E8U_eq_closure :
    m22E8U = Subgroup.closure {g | g ∈ m22UGens1} := by
  let U := m22E8U
  have hUmem : ∀ x, x ∈ U ↔ x ∈ m22E8UL := fun x => mem_subgroupOfList
  have hgenU : ∀ g ∈ m22UGens1, g ∈ U := fun g hg =>
    (hUmem g).2 ((m22E8_facts).ugens_mem g hg)
  apply le_antisymm
  · intro x hx
    exact permClosureList_subset_closure m22UGens1 20 x ((hUmem x).1 hx)
  · refine (Subgroup.closure_le U).mpr ?_
    exact hgenU

theorem m22E8U_card :
    Nat.card m22E8U = 64 := by
  classical
  let U := m22E8U
  have hUmem : ∀ x, x ∈ U ↔ x ∈ m22E8UL := fun x => mem_subgroupOfList
  rw [show Nat.card U = Nat.card (↥(m22E8UL.toFinset)) from ?_,
    Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup (m22E8_facts).ul_nodup, (m22E8_facts).ul_length]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    simp [U, mem_subgroupOfList])

theorem m22E8U_le_K :
    m22E8U ≤ m22E8K := by
  intro u hu
  exact (mem_enumerationTab_iff m22CentQ1 (m22_oddcore_cent1).1 u).1
    (m22E8UL_data.2.2.2.1 u hu)

theorem m22E8K_le_normalizer_U :
    m22E8K ≤ Subgroup.normalizer (m22E8U : Set _) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro u
  have hgL : g ∈ m22E8KL :=
    (mem_enumerationTab_iff m22CentQ1 (m22_oddcore_cent1).1 g).2 hg
  change (u ∈ m22E8UL ↔ g * u * g⁻¹ ∈ m22E8UL)
  refine ⟨fun huu => m22E8UL_data.2.2.2.2.2.1 g hgL u huu, fun huu => ?_⟩
  have hgi : g⁻¹ ∈ m22E8KL :=
    (mem_enumerationTab_iff m22CentQ1 (m22_oddcore_cent1).1 g⁻¹).2 (m22E8K.inv_mem hg)
  have hconj := m22E8UL_data.2.2.2.2.2.1 g⁻¹ hgi (g * u * g⁻¹) huu
  have heq : g⁻¹ * (g * u * g⁻¹) * (g⁻¹)⁻¹ = u := by group
  rwa [heq] at hconj

theorem m22E8U_isPGroup : IsPGroup 2 m22E8U := by
  intro u
  refine ⟨6, ?_⟩
  exact Subtype.ext (by
    have hu : (u : Equiv.Perm (Fin 22)) ∈ m22E8UL := (mem_subgroupOfList).1 u.2
    simpa using m22E8UL_data.2.2.2.2.1 u.1 hu)

instance m22E8U_subgroupOf_normal :
    (m22E8U.subgroupOf m22E8K).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer m22E8U_le_K).2 m22E8K_le_normalizer_U

theorem m22E8K_card : Nat.card m22E8K = 384 :=
  (m22_rep_data1).2.2.2.1

theorem m22E8U_subgroupOf_K_card :
    Nat.card (m22E8U.subgroupOf m22E8K) = 64 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe m22E8U_le_K).toEquiv, m22E8U_card]

theorem m22E8_quotient_card :
    Nat.card (m22E8K ⧸ m22E8U.subgroupOf m22E8K) = 6 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (m22E8U.subgroupOf m22E8K)
  rw [m22E8K_card, m22E8U_subgroupOf_K_card] at h
  omega

theorem m22E8X_mem_K : m22E8X ∈ m22E8K :=
  (mem_enumerationTab_iff m22CentQ1 (m22_oddcore_cent1).1 m22E8X).1
    (m22E8_facts).x_mem

theorem m22E8Y_mem_K : m22E8Y ∈ m22E8K :=
  (mem_enumerationTab_iff m22CentQ1 (m22_oddcore_cent1).1 m22E8Y).1
    (m22E8_facts).y_mem

theorem m22E8_quotient_noncomm :
    ¬ IsMulCommutative (m22E8K ⧸ m22E8U.subgroupOf m22E8K) := by
  intro hcomm
  let x : m22E8K := ⟨m22E8X, m22E8X_mem_K⟩
  let y : m22E8K := ⟨m22E8Y, m22E8Y_mem_K⟩
  have hq : QuotientGroup.mk' (m22E8U.subgroupOf m22E8K) ⁅x, y⁆ = 1 := by
    rw [map_commutatorElement]
    exact (commutatorElement_eq_one_iff_mul_comm).2 (isMulCommutative_iff.mp hcomm _ _)
  have hmem : ⁅x, y⁆ ∈ m22E8U.subgroupOf m22E8K := (QuotientGroup.eq_one_iff _).mp hq
  have hcoe : ((⁅x, y⁆ : m22E8K) : Equiv.Perm (Fin 22)) = ⁅m22E8X, m22E8Y⁆ := rfl
  have hmemU : (⁅m22E8X, m22E8Y⁆ : Equiv.Perm (Fin 22)) ∈ m22E8U := by
    have h := Subgroup.mem_subgroupOf.mp hmem
    rwa [hcoe] at h
  exact (m22E8_facts).xy_not_mem hmemU

theorem m22E8_quotient_pCore_eq_bot :
    CFSG.pCore 2 (m22E8K ⧸ m22E8U.subgroupOf m22E8K) = ⊥ := by
  exact pCore_two_eq_bot_of_card_six_of_not_comm _
    m22E8_quotient_card m22E8_quotient_noncomm

theorem m22E8U_eq_pCoreOf :
    m22E8U = CFSG.Open.pCoreOf 2 m22E8K := by
  apply le_antisymm
  · exact CFSG.LieType.BorelTits.le_pCoreOf 2 m22E8U_le_K
      (m22E8U_subgroupOf_normal) m22E8U_isPGroup
  · have hmap := CFSG.LieType.BorelTits.map_pCore_le (r := 2)
      (QuotientGroup.mk' (m22E8U.subgroupOf m22E8K))
      (QuotientGroup.mk'_surjective (m22E8U.subgroupOf m22E8K))
    rw [m22E8_quotient_pCore_eq_bot, le_bot_iff] at hmap
    have hleker : CFSG.pCore 2 m22E8K ≤
        (QuotientGroup.mk' (m22E8U.subgroupOf m22E8K)).ker :=
      (Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 m22E8K)).mp hmap
    rw [QuotientGroup.ker_mk'] at hleker
    calc
      CFSG.Open.pCoreOf 2 m22E8K
          = (CFSG.pCore 2 m22E8K).map m22E8K.subtype := rfl
      _ ≤ (m22E8U.subgroupOf m22E8K).map m22E8K.subtype := Subgroup.map_mono hleker
      _ = m22E8U := Subgroup.map_subgroupOf_eq_of_le m22E8U_le_K

theorem m22E8U_subgroupOf_eq_pCore :
    m22E8U.subgroupOf m22E8K = CFSG.pCore 2 m22E8K := by
  ext x
  constructor
  · intro hx
    have hx' : (x : Equiv.Perm (Fin 22)) ∈ CFSG.Open.pCoreOf 2 m22E8K := by
      rw [← m22E8U_eq_pCoreOf]
      exact hx
    rw [CFSG.Open.pCoreOf] at hx'
    rcases (Subgroup.mem_map.mp hx') with ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    simpa [hyx'] using hy
  · intro hx
    have hx' : (x : Equiv.Perm (Fin 22)) ∈ CFSG.Open.pCoreOf 2 m22E8K := by
      rw [CFSG.Open.pCoreOf]
      exact Subgroup.mem_map_of_mem _ hx
    rwa [← m22E8U_eq_pCoreOf] at hx'

noncomputable abbrev m22E8E :
    Subgroup (Equiv.Perm (Fin 22)) :=
  subgroupOfList m22E8EL (m22E8_facts).el_one (m22E8_facts).el_mul (m22E8_facts).el_inv

theorem m22E8E_mem {x : Equiv.Perm (Fin 22)} :
    x ∈ m22E8E ↔ x ∈ m22E8EL := Iff.rfl

theorem m22E8E_eq_closure :
    m22E8E = Subgroup.closure {x | x ∈ m22E8CommGens} := by
  let E := m22E8E
  have hEmem : ∀ x, x ∈ E ↔ x ∈ m22E8EL := fun x => mem_subgroupOfList
  have hgenE : ∀ g ∈ m22E8CommGens, g ∈ E := fun g hg =>
    (hEmem g).2 ((m22E8_facts).commgens_mem g hg)
  apply le_antisymm
  · intro x hx
    exact permClosureList_subset_closure m22E8CommGens 20 x ((hEmem x).1 hx)
  · refine (Subgroup.closure_le E).mpr ?_
    exact hgenE

theorem m22E8E_card : Nat.card m22E8E = 8 := by
  classical
  let E := m22E8E
  have hEmem : ∀ x, x ∈ E ↔ x ∈ m22E8EL := fun x => mem_subgroupOfList
  rw [show Nat.card E = Nat.card (↥(m22E8EL.toFinset)) from ?_,
    Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup (m22E8_facts).el_nodup, (m22E8_facts).el_length]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    simp [E, mem_subgroupOfList])

theorem m22E8E_le_U : m22E8E ≤ m22E8U := by
  intro x hx
  exact (m22E8_facts).el_le_ul x ((m22E8E_mem).1 hx)

instance m22E8E_isMulCommutative :
    IsMulCommutative m22E8E :=
  IsMulCommutative.of_comm fun a b => Subtype.ext <| by
    exact (m22E8_facts).el_comm a.1 ((m22E8E_mem).1 a.2) b.1 ((m22E8E_mem).1 b.2)

instance m22E8E_isElementaryAbelian :
    IsElementaryAbelian 2 m22E8E where
  exponent_dvd_p := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    exact Subtype.ext <| by
      have hx : (x : Equiv.Perm (Fin 22)) ∈ m22E8EL := (m22E8E_mem).1 x.2
      simpa using (m22E8_facts).el_sq x.1 hx

theorem m22E8E_le_commutator :
    m22E8E ≤ ⁅m22E8U, m22E8U⁆ := by
  have hU0 : m22E8U0 ∈ m22E8U :=
    (mem_subgroupOfList).2 (m22E8_facts).u0_mem
  have hU1 : m22E8U1 ∈ m22E8U :=
    (mem_subgroupOfList).2 (m22E8_facts).u1_mem
  have hU2 : m22E8U2 ∈ m22E8U :=
    (mem_subgroupOfList).2 (m22E8_facts).u2_mem
  have h0 : ⁅m22E8U0, m22E8U1⁆ ∈ ⁅m22E8U, m22E8U⁆ :=
    Subgroup.commutator_mem_commutator hU0 hU1
  have h1 : ⁅m22E8U0, m22E8U2⁆ ∈ ⁅m22E8U, m22E8U⁆ :=
    Subgroup.commutator_mem_commutator hU0 hU2
  have h2 : ⁅m22E8U1, m22E8U2⁆ ∈ ⁅m22E8U, m22E8U⁆ :=
    Subgroup.commutator_mem_commutator hU1 hU2
  rw [m22E8E_eq_closure]
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  simp only [m22E8CommGens, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

theorem m22E8_commutator_le_E :
    ⁅m22E8U, m22E8U⁆ ≤ m22E8E := by
  refine (Subgroup.commutator_le).mpr ?_
  intro x hx y hy
  exact (m22E8E_mem).2 ((m22E8_facts).ul_comm_mem x hx y hy)

theorem m22E8E_eq_commutator :
    m22E8E = ⁅m22E8U, m22E8U⁆ :=
  le_antisymm m22E8E_le_commutator m22E8_commutator_le_E

theorem m22E8E_le_K :
    m22E8E ≤ m22E8K :=
  m22E8E_le_U.trans m22E8U_le_K

theorem m22E8E_subgroupOf_eq_commutator :
    m22E8E.subgroupOf m22E8K =
      ⁅m22E8U.subgroupOf m22E8K, m22E8U.subgroupOf m22E8K⁆ := by
  apply (Subgroup.map_subtype_inj (H := m22E8K)).mp
  calc
    (m22E8E.subgroupOf m22E8K).map m22E8K.subtype
        = m22E8E := by
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr m22E8E_le_K]
    _ = ⁅m22E8U, m22E8U⁆ := m22E8E_eq_commutator
    _ = (⁅m22E8U.subgroupOf m22E8K, m22E8U.subgroupOf m22E8K⁆).map m22E8K.subtype := by
          simp [Subgroup.map_commutator,
            Subgroup.map_subgroupOf_eq_of_le m22E8U_le_K]

theorem m22E8E_characteristic :
    (m22E8E.subgroupOf m22E8K).Characteristic := by
  have hUchar : (m22E8U.subgroupOf m22E8K).Characteristic := by
    rw [m22E8U_subgroupOf_eq_pCore]
    exact CFSG.pCore_characteristic
  rw [m22E8E_subgroupOf_eq_commutator]
  let : (m22E8U.subgroupOf m22E8K).Characteristic := hUchar
  exact Subgroup.commutator_characteristic (H₁ := m22E8U.subgroupOf m22E8K) (H₂ := m22E8U.subgroupOf m22E8K)


theorem m22E8_full_data :
    m22E8U = Subgroup.closure {g | g ∈ m22UGens1} ∧
    Nat.card m22E8U = 64 ∧
    (m22E8U.subgroupOf m22E8K).Normal ∧
    Nat.card (m22E8K ⧸ m22E8U.subgroupOf m22E8K) = 6 ∧
    ¬ IsMulCommutative (m22E8K ⧸ m22E8U.subgroupOf m22E8K) ∧
    m22E8U = CFSG.Open.pCoreOf 2 m22E8K ∧
    m22E8E = ⁅CFSG.Open.pCoreOf 2 m22E8K, CFSG.Open.pCoreOf 2 m22E8K⁆ ∧
    (m22E8E.subgroupOf m22E8K).Characteristic ∧
    IsElementaryAbelian 2 m22E8E ∧
    Nat.card m22E8E = 8 := by
  refine ⟨m22E8U_eq_closure, m22E8U_card, m22E8U_subgroupOf_normal, m22E8_quotient_card,
    m22E8_quotient_noncomm, m22E8U_eq_pCoreOf, ?_, m22E8E_characteristic,
    m22E8E_isElementaryAbelian, m22E8E_card⟩
  rw [m22E8E_eq_commutator, m22E8U_eq_pCoreOf]

theorem m22E8_O2_derived_characteristic :
    m22E8U = Subgroup.closure {g | g ∈ m22UGens1} ∧
    m22E8U = CFSG.Open.pCoreOf 2 m22E8K ∧
    m22E8E = ⁅CFSG.Open.pCoreOf 2 m22E8K, CFSG.Open.pCoreOf 2 m22E8K⁆ ∧
    (m22E8E.subgroupOf m22E8K).Characteristic ∧
    IsElementaryAbelian 2 m22E8E ∧
    Nat.card m22E8E = 8 := by
  refine ⟨m22E8U_eq_closure, m22E8U_eq_pCoreOf, ?_, m22E8E_characteristic,
    m22E8E_isElementaryAbelian, m22E8E_card⟩
  rw [m22E8E_eq_commutator, m22E8U_eq_pCoreOf]

end CFSG.ClassicalInvolution
