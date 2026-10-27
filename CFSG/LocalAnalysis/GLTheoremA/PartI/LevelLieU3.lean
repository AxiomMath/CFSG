module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU2
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLie
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
import CFSG.HardMathSupport.Timmesfeld.Proving.OmegaPiGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieU

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer CFSG.Fischer
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

@[expose] def decompSub (K : Subgroup M5) (y : M5) (hK : ∀ k ∈ K, k * y = y * k) :
    Subgroup M5 where
  carrier := {x | ∃ k ∈ K, ∃ n : ℤ, x = k * y ^ n}
  mul_mem' := by
    rintro _ _ ⟨k, hk, n, rfl⟩ ⟨k', hk', m, rfl⟩
    have hc : k' * y ^ n = y ^ n * k' := ((show Commute k' y from hK k' hk').zpow_right n).eq
    refine ⟨k * k', K.mul_mem hk hk', n + m, ?_⟩
    calc k * y ^ n * (k' * y ^ m) = k * (y ^ n * k') * y ^ m := by group
      _ = k * (k' * y ^ n) * y ^ m := by rw [← hc]
      _ = k * k' * (y ^ n * y ^ m) := by group
      _ = k * k' * y ^ (n + m) := by rw [zpow_add]
  one_mem' := ⟨1, K.one_mem, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨k, hk, n, rfl⟩
    refine ⟨k⁻¹, K.inv_mem hk, -n, ?_⟩
    have hc : k⁻¹ * y ^ (-n) = y ^ (-n) * k⁻¹ :=
      ((show Commute k⁻¹ y from (show Commute k y from hK k hk).inv_left).zpow_right (-n)).eq
    rw [mul_inv_rev, ← zpow_neg]
    exact hc.symm

theorem commutator_centralizer_le (Kb : Subgroup M5) (hKbC : Kb ≤ Subgroup.centralizer {yM5})
    (hsup : Subgroup.centralizer {yM5} = Kb ⊔ Subgroup.zpowers yM5) :
    ⁅Subgroup.centralizer {yM5}, Subgroup.centralizer {yM5}⁆ ≤ Kb := by
  have hK : ∀ k ∈ Kb, k * yM5 = yM5 * k :=
    fun k hk => Subgroup.mem_centralizer_singleton_iff.1 (hKbC hk)
  have hle : Subgroup.centralizer {yM5} ≤ decompSub Kb yM5 hK := by
    rw [hsup]
    apply sup_le
    · intro k hk
      exact ⟨k, hk, 0, by simp⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨1, Kb.one_mem, 1, by simp⟩
  rw [Subgroup.commutator_le]
  intro x hx x' hx'
  obtain ⟨k, hk, n, rfl⟩ := hle hx
  obtain ⟨k', hk', m, rfl⟩ := hle hx'
  have h1b : Commute (yM5 ^ n) k' := ((show Commute k' yM5 from hK k' hk').zpow_right n).symm
  have h12 : Commute (yM5 ^ n) (yM5 ^ m) := (Commute.refl yM5).zpow_zpow n m
  have h2a : Commute (yM5 ^ m) k := ((show Commute k yM5 from hK k hk).zpow_right m).symm
  rw [CFSG.HardMathSupport.Solomon.Coordinator.commutatorElement_mul_mul' h1b h12 h2a,
    commutatorElement_def]
  exact Kb.mul_mem (Kb.mul_mem (Kb.mul_mem hk hk') (Kb.inv_mem hk)) (Kb.inv_mem hk')

theorem pSimple_equiv_of_simple (K : Subgroup M5) [IsSimpleGroup K]
    (hnc : ¬ IsMulCommutative K) (h3 : 3 ∣ Nat.card K) : Nonempty (PSimple 3 K ≃* K) := by
  have hO : GLAPPrimeCore 3 K = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Proving.glaPPrimeCore_eq_bot_of_isSimpleGroup
      Nat.prime_three h3
  let pq0 : PQuot 3 K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hZK : Subgroup.center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
    · exact h
    · exfalso
      apply hnc
      refine ⟨⟨fun a b => ?_⟩⟩
      have ha : a ∈ Subgroup.center K := by
        rw [h]
        exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 ha b).symm
  have hZP : Subgroup.center (PQuot 3 K) = ⊥ := by
    have h1 := Subgroup.map_center_eq pq0
    rw [hZK] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ pq0.injective).1 h1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZP).trans (QuotientGroup.quotientBot.trans pq0)⟩

theorem caseA_components (I : Subgroup M5) (hI : GLAPComponent 3 (Subgroup.centralizer {yM5}) I) :
    kLevel 3 (PSimple 3 I) ≤ 2 := by
  obtain ⟨Kb, hKbC, hsup, -, hsimp, hnc, h3, hcat⟩ := m5_u4_layer
  have hcomm := commutator_centralizer_le Kb hKbC hsup
  have hIKb : I ≤ Kb := by
    calc I = ⁅I, I⁆ := (glaPComponent_perfect hI).symm
      _ ≤ ⁅Subgroup.centralizer {yM5}, Subgroup.centralizer {yM5}⁆ :=
          Subgroup.commutator_mono hI.1 hI.1
      _ ≤ Kb := hcomm
  have hsub : CFSG.Open.IsSubnormal I Kb := by
    have h := hI.2.1.inf_of_le hKbC
    rwa [inf_eq_left.2 hIKb] at h
  rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub hsimp with h | h
  · exact absurd h (glaPComponent_ne_bot' hI)
  · rw [h]
    haveI := hsimp
    obtain ⟨e⟩ := pSimple_equiv_of_simple Kb hnc h3
    rw [kLevel_congr 3 e]
    exact kLevel_le_two_of_chev (Or.inr (catalog_ambiguous_of_u4two hcat))

theorem not_comp_of_solvable {X I : Subgroup M5} (hsolv : Group.IsSolvable ↥X)
    (hI : GLAPComponent 3 X I) : False := by
  haveI := hsolv
  have hJX : I ≤ X := hI.1
  have hperf : ⁅I, I⁆ = I := glaPComponent_perfect hI
  have hne : I ≠ ⊥ := glaPComponent_ne_bot' hI
  have hJ'ne : I.subgroupOf X ≠ ⊥ := by
    intro h0
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hJX, h0, Subgroup.map_bot]
  have hlt : ⁅I.subgroupOf X, I.subgroupOf X⁆ < I.subgroupOf X :=
    Group.IsSolvable.commutator_lt_of_ne_bot hJ'ne
  have heq : ⁅I.subgroupOf X, I.subgroupOf X⁆ = I.subgroupOf X := by
    apply Subgroup.map_injective (f := X.subtype) X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJX]
    exact hperf
  rw [heq] at hlt
  exact lt_irrefl _ hlt

theorem isSolvable_centralizer_of_equiv (τ : M5 ≃* M5) (s : M5)
    (h : Group.IsSolvable ↥(Subgroup.centralizer {τ s})) :
    Group.IsSolvable ↥(Subgroup.centralizer {s}) := by
  have h' : Group.IsSolvable ↥((Subgroup.centralizer {s}).map τ.toMonoidHom) := by
    rw [map_centralizer_equiv]
    exact h
  haveI := h'
  let e := (Subgroup.centralizer {s}).equivMapOfInjective τ.toMonoidHom τ.injective
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem isSimpleGroup_M5 : IsSimpleGroup M5 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (StatedProj (StatedSU 5 (2 ^ 1) F4)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F4 2 1 hF4card 5
      (by norm_num) (by norm_num)
  let projM5 : StatedProj (StatedSU 5 (2 ^ 1) F4) ≃* M5 :=
    (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_eq_bot hF4card)).trans
      QuotientGroup.quotientBot
  exact projM5.symm.isSimpleGroup

theorem kLevel_le_two_of_k2 {p : ℕ} {S : Type} [Group S] (h : catalogIs S (k2 p)) :
    kLevel p S ≤ 2 := by
  unfold kLevel
  by_cases h1 : IsChevSimple p S
  · rw [if_pos h1]
    norm_num
  · rw [if_neg h1, if_pos h]

theorem downLe_M5_of (hk : kLevel 3 M5 ≤ 2) : DownLe 3 2 M5 := by
  haveI := isSimpleGroup_M5
  intro α hα I hI
  obtain ⟨s, rfl⟩ := exists_conj_of_pow_three α hα
  rw [fixSubgroup_conj_eq] at hI
  have hs3 : s ^ 3 = 1 := by
    apply eq_one_of_conj_eq_one
    rw [map_pow]
    exact hα
  rcases normal_form s hs3 with rfl | ⟨τ, hτ⟩ | ⟨τ, d, hd, hcnt⟩
  ·
    have htop : Subgroup.centralizer ({1} : Set M5) = ⊤ := by
      ext x
      simp [Subgroup.mem_centralizer_singleton_iff]
    rw [htop] at hI
    have hIt : I = ⊤ := by
      rcases CFSG.Open.IsSubnormal.eq_bot_or_top hI.2.1 with h | h
      · exact absurd h (glaPComponent_ne_bot' hI)
      · exact h
    rw [hIt]
    haveI : IsSimpleGroup (⊤ : Subgroup M5) := Subgroup.topEquiv.isSimpleGroup
    have hnc : ¬ IsMulCommutative (⊤ : Subgroup M5) := by
      intro h
      apply su_ne_us
      exact congrArg Subtype.val
        (h.is_comm.comm ⟨sM5, Subgroup.mem_top _⟩ ⟨uM5, Subgroup.mem_top _⟩)
    have h3 : 3 ∣ Nat.card (⊤ : Subgroup M5) := by
      rw [Subgroup.card_top]
      obtain ⟨Kb, -, -, -, -, -, h3Kb, -⟩ := m5_u4_layer
      exact h3Kb.trans (Subgroup.card_subgroup_dvd_card Kb)
    obtain ⟨e⟩ := pSimple_equiv_of_simple ⊤ hnc h3
    rw [kLevel_congr 3 e, kLevel_congr 3 Subgroup.topEquiv]
    exact hk
  ·
    have hI' := glaPComponent_map_centralizer τ s I hI
    have hk' : kLevel 3 (PSimple 3 (I.map τ.toMonoidHom)) ≤ 2 := by
      rcases hτ with h | h
      · rw [h] at hI'
        exact caseA_components _ hI'
      · rw [h, centralizer_inv_eq] at hI'
        exact caseA_components _ hI'
    obtain ⟨e⟩ := pSimple_map_equiv 3 τ I
    rw [kLevel_congr 3 e] at hk'
    exact hk'
  ·
    exact (not_comp_of_solvable
      (isSolvable_centralizer_of_equiv τ s (centralizer_diag_solvable (τ s) d hd hcnt)) hI).elim

end CFSG.LocalAnalysis.GLTheoremA.LevelLieU

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer

theorem kdLieRowU5Two_holds : KDLieRowU5Two := by
  intro q hv hq
  have hcat : catalogIs (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 4 q, hv⟩).Group
      CFSG.LocalAnalysis.GLTheoremA.S9.isU5two :=
    ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 4 q, hv⟩,
      (show q.card = 2 from hq), ⟨MulEquiv.refl _⟩⟩
  obtain ⟨e⟩ := bridge_u5two_stated hcat
  have hk2 : catalogIs (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 4 q, hv⟩).Group
      (k2 3) :=
    ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 4 q, hv⟩,
      (show (3 : ℕ) = 3 ∧ q.card = 2 from ⟨rfl, hq⟩), ⟨MulEquiv.refl _⟩⟩
  have hk : kLevel 3 M5 ≤ 2 := by
    rw [← kLevel_congr 3 e]
    exact LevelLieU.kLevel_le_two_of_k2 hk2
  exact downLe_of_mulEquiv e.symm (LevelLieU.downLe_M5_of hk)

end CFSG.LocalAnalysis.GLTheoremA
