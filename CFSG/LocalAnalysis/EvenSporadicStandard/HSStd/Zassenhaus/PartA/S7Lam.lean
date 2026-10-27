module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S2Odd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Toolbox
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect1
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

local notation "A6" => alternatingGroup (Fin 6)

section AutA6

theorem isSimple_alt6 : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)

theorem alt6_nonabelian : ∃ a b : A6, a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    fun h => ?_⟩
  have := congrArg Subtype.val h
  revert this
  decide

abbrev innA6 : Subgroup (MulAut A6) := (MulAut.conj : A6 →* MulAut A6).range

instance innA6_normal : innA6.Normal where
  conj_mem := by
    rintro _ ⟨a, rfl⟩ g
    exact ⟨g a, (mul_conj_mul_inv g a).symm⟩

theorem innA6_le_commutator : innA6 ≤ _root_.commutator (MulAut A6) := by
  have hperf : _root_.commutator A6 = ⊤ := commutator_alternatingGroup_eq_top (by simp)
  have h1 : innA6 = (⊤ : Subgroup A6).map (MulAut.conj : A6 →* MulAut A6) :=
    MonoidHom.range_eq_map _
  have hII : innA6 = ⁅innA6, innA6⁆ := by
    have h2 : ⁅innA6, innA6⁆ = ((_root_.commutator A6).map (MulAut.conj : A6 →* MulAut A6)) := by
      rw [_root_.commutator_def, Subgroup.map_commutator, ← h1]
    rw [h2, hperf, ← h1]
  rw [hII, _root_.commutator_def]
  exact Subgroup.commutator_mono le_top le_top

theorem card_innA6 : Nat.card innA6 = 360 := by
  have h1 := Subgroup.card_mul_index innA6
  rw [CFSG.QuasithinUnique.Setup.X3Aut.index_inner_alt6,
    CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6] at h1
  omega

theorem s7_commutator_mulAut_alt6 : _root_.commutator (MulAut A6) = innA6 := by
  apply le_antisymm _ innA6_le_commutator
  have hcard : Nat.card (MulAut A6 ⧸ innA6) = 2 ^ 2 := by
    have h1 := Subgroup.card_mul_index innA6
    rw [CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6, card_innA6] at h1
    have : innA6.index = 4 := CFSG.QuasithinUnique.Setup.X3Aut.index_inner_alt6
    rw [← Subgroup.index_eq_card, this]
    norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : IsMulCommutative (MulAut A6 ⧸ innA6) := by
    haveI : Finite (MulAut A6 ⧸ innA6) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
  rw [_root_.commutator_def]
  rw [Subgroup.commutator_le]
  intro a _ b _
  have hc : (QuotientGroup.mk a : MulAut A6 ⧸ innA6) * QuotientGroup.mk b =
      QuotientGroup.mk b * QuotientGroup.mk a := hcomm.is_comm.comm _ _
  have h : (QuotientGroup.mk (⁅a, b⁆ : MulAut A6) : MulAut A6 ⧸ innA6) = 1 := by
    rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv]
    exact (commutatorElement_eq_one_iff_mul_comm.2 hc :)
  exact (QuotientGroup.eq_one_iff _).1 h

theorem innA6_perfect : ⁅innA6, innA6⁆ = innA6 := by
  have hperf : _root_.commutator A6 = ⊤ := commutator_alternatingGroup_eq_top (by simp)
  have h1 : innA6 = (⊤ : Subgroup A6).map (MulAut.conj : A6 →* MulAut A6) :=
    MonoidHom.range_eq_map _
  have h2 : ⁅innA6, innA6⁆ = ((_root_.commutator A6).map (MulAut.conj : A6 →* MulAut A6)) := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← h1]
  rw [h2, hperf, ← h1]

theorem commutator_prod_alt6 :
    _root_.commutator (Multiplicative (ZMod 2) × MulAut A6) =
      innA6.map (MonoidHom.inr (Multiplicative (ZMod 2)) (MulAut A6)) := by
  apply le_antisymm
  · rw [_root_.commutator_def, Subgroup.commutator_le]
    rintro ⟨a, m⟩ _ ⟨b, n⟩ _
    refine ⟨⁅m, n⁆, ?_, ?_⟩
    · rw [← s7_commutator_mulAut_alt6]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    · have hab : ⁅a, b⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact mul_comm a b
      refine Prod.ext ?_ rfl
      simpa [commutatorElement_def] using hab.symm
  · rintro _ ⟨m, hm, rfl⟩
    have h0 : m ∈ ⁅(⊤ : Subgroup (MulAut A6)), (⊤ : Subgroup (MulAut A6))⁆ := by
      rw [← _root_.commutator_def]; exact innA6_le_commutator hm
    have h2 := Subgroup.mem_map_of_mem
      (MonoidHom.inr (Multiplicative (ZMod 2)) (MulAut A6)) h0
    rw [Subgroup.map_commutator] at h2
    exact Subgroup.commutator_mono le_top le_top h2

end AutA6


section Lam

variable {X : Type} [Group X] [Finite X] {t : X}

theorem e_symm_mem_commutator
    (e : ↥(centralizer ({t} : Set X)) ≃* Multiplicative (ZMod 2) × MulAut A6) {m : MulAut A6}
    (hm : m ∈ innA6) : e.symm (1, m) ∈ _root_.commutator ↥(centralizer ({t} : Set X)) := by
  have h0 : m ∈ ⁅(⊤ : Subgroup (MulAut A6)), (⊤ : Subgroup (MulAut A6))⁆ := by
    rw [← _root_.commutator_def]; exact innA6_le_commutator hm
  have h2 := Subgroup.mem_map_of_mem
    (MonoidHom.inr (Multiplicative (ZMod 2)) (MulAut A6)) h0
  rw [Subgroup.map_commutator] at h2
  have h3 : ((1 : Multiplicative (ZMod 2)), m) ∈
      ⁅(⊤ : Subgroup (Multiplicative (ZMod 2) × MulAut A6)),
        (⊤ : Subgroup (Multiplicative (ZMod 2) × MulAut A6))⁆ :=
    Subgroup.commutator_mono le_top le_top h2
  have h4 : ((1 : Multiplicative (ZMod 2)), m) ∈
      (⁅(⊤ : Subgroup ↥(centralizer ({t} : Set X))),
        (⊤ : Subgroup ↥(centralizer ({t} : Set X)))⁆).map e.toMonoidHom := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    exact h3
  obtain ⟨l, hl, hle⟩ := h4
  have : l = e.symm (1, m) := by
    apply e.injective
    simpa using hle
  rw [this] at hl
  exact hl

theorem snd_eq_one_of_commute
    (e : ↥(centralizer ({t} : Set X)) ≃* Multiplicative (ZMod 2) × MulAut A6)
    (g : ↥(centralizer ({t} : Set X)))
    (h : ∀ m ∈ innA6, g * e.symm (1, m) = e.symm (1, m) * g) : (e g).2 = 1 := by
  haveI := isSimple_alt6
  refine eq_one_of_commute_conj alt6_nonabelian _ fun s => ?_
  have h1 := congrArg e (h (MulAut.conj s) ⟨s, rfl⟩)
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
  have h2 := congrArg Prod.snd h1
  simpa using h2

theorem e_t_eq (ht : orderOf t = 2)
    (e : ↥(centralizer ({t} : Set X)) ≃* Multiplicative (ZMod 2) × MulAut A6) :
    (e ⟨t, mem_centralizer_singleton_iff.2 rfl⟩).2 = 1 ∧
      (e ⟨t, mem_centralizer_singleton_iff.2 rfl⟩).1 ≠ 1 := by
  haveI := isSimple_alt6
  set t' : ↥(centralizer ({t} : Set X)) := ⟨t, mem_centralizer_singleton_iff.2 rfl⟩ with ht'
  have hcen : ∀ x : ↥(centralizer ({t} : Set X)), x * t' = t' * x := fun x =>
    Subtype.ext (mem_centralizer_singleton_iff.1 x.2)
  have hnt : t' ≠ 1 := by
    intro h
    have : t = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at ht
    omega
  refine ⟨?_, ?_⟩
  · have hz : (e t').2 ∈ center (MulAut A6) := by
      rw [mem_center_iff]
      intro m
      have h1 := congrArg e (hcen (e.symm (1, m)))
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
      have h2 := congrArg Prod.snd h1
      simpa using h2
    rw [center_mulAut_eq_bot alt6_nonabelian] at hz
    simpa using hz
  · intro h
    apply hnt
    apply e.injective
    refine Prod.ext (by simpa using h) ?_
    have hz : (e t').2 ∈ center (MulAut A6) := by
      rw [mem_center_iff]
      intro m
      have h1 := congrArg e (hcen (e.symm (1, m)))
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
      have h2 := congrArg Prod.snd h1
      simpa using h2
    rw [center_mulAut_eq_bot alt6_nonabelian] at hz
    simpa using hz

theorem mem_zpowers_of_commute_derived (ht : orderOf t = 2)
    (e : ↥(centralizer ({t} : Set X)) ≃* Multiplicative (ZMod 2) × MulAut A6) {g : X}
    (hg : g ∈ centralizer ({t} : Set X)) (hc : ∀ l ∈ centralizerDerived t, g * l = l * g) :
    g ∈ zpowers t := by
  set g' : ↥(centralizer ({t} : Set X)) := ⟨g, hg⟩ with hg'
  have h2 : (e g').2 = 1 := by
    apply snd_eq_one_of_commute e g'
    intro m hm
    have hl := e_symm_mem_commutator e hm
    apply Subtype.ext
    exact hc _ ⟨_, hl, rfl⟩
  obtain ⟨hs, hne⟩ := e_t_eq ht e
  set t' : ↥(centralizer ({t} : Set X)) := ⟨t, mem_centralizer_singleton_iff.2 rfl⟩ with ht'
  have hZ2 : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a = b := by decide
  by_cases h1 : (e g').1 = 1
  · have : g' = 1 := by
      apply e.injective
      exact Prod.ext (by simpa using h1) (by simpa using h2)
    have : g = 1 := congrArg Subtype.val this
    rw [this]
    exact one_mem _
  · have : g' = t' := by
      apply e.injective
      exact Prod.ext (hZ2 _ _ h1 hne) (by rw [h2]; exact hs.symm)
    have : g = t := congrArg Subtype.val this
    rw [this]
    exact mem_zpowers t

omit [Finite X] in
theorem mul_self_of_orderOf_two (ht : orderOf t = 2) : t * t = 1 := by
  have := pow_orderOf_eq_one t
  rwa [ht, pow_two] at this

theorem cent_normal_dichotomy (hO : Open.fusionOddCore X = ⊥) (ht : orderOf t = 2)
    (e : ↥(centralizer ({t} : Set X)) ≃* Multiplicative (ZMod 2) × MulAut A6)
    {N : Subgroup X} [N.Normal] (hN : centralizerDerived t ≤ N) :
    t ∈ centralizer (N : Set X) ∨ centralizer (N : Set X) = ⊥ := by
  by_cases htB : t ∈ centralizer (N : Set X)
  · exact Or.inl htB
  right
  have ht2 : t * t = 1 := mul_self_of_orderOf_two ht
  set B : Subgroup X := centralizer (N : Set X) with hB
  have hBn : B.Normal := inferInstance
  have hcomm : ∀ b ∈ B, ∀ n ∈ N, b * n = n * b := fun b hb n hn =>
    (mem_centralizer_iff.1 hb n hn).symm
  have hfix : ∀ o ∈ B, t * o = o * t → o = 1 := by
    intro o ho hto
    have hoc : o ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.2 hto.symm
    have hz := mem_zpowers_of_commute_derived ht e hoc (fun l hl => hcomm o ho l (hN hl))
    obtain ⟨n, rfl⟩ := hz
    have h2 : t ^ n = 1 ∨ t ^ n = t := by
      have hmod : t ^ n = t ^ (n % 2) := by
        conv_lhs => rw [← Int.emod_add_mul_ediv n 2, zpow_add, zpow_mul]
        have : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht2
        rw [this, one_zpow, mul_one]
      have : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases this with h | h
      · left; rw [hmod, h]; simp
      · right; rw [hmod, h]; simp
    rcases h2 with h2 | h2
    · exact h2
    · exfalso; apply htB; rw [← h2]; exact ho
  obtain ⟨hinv, -⟩ := inv_of_centralizer_eq_bot (O := B) ht2
    (fun o ho => hBn.conj_mem o ho t) hfix
  have hodd : Odd (Nat.card B) := by
    by_contra hev
    have h2 : 2 ∣ Nat.card B := by
      rw [Nat.not_odd_iff_even] at hev
      exact even_iff_two_dvd.1 hev
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 2 h2
    have hb2 : b * b = 1 := mul_self_of_orderOf_two hb
    have h3 := hinv b b.2
    have h4 : t * (b : X) * t⁻¹ = (b : X) := by
      rw [h3]
      have : (b : X) * (b : X) = 1 := congrArg Subtype.val hb2
      exact (eq_inv_of_mul_eq_one_left this).symm
    have h5 : (b : X) = 1 := hfix b b.2 (by
      have := h4
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this)
    have : b = 1 := Subtype.ext h5
    rw [this, orderOf_one] at hb
    omega
  have hle := le_fusionOddCore_of_odd' (N := B) hodd
  rw [hO] at hle
  exact le_bot_iff.1 hle

end Lam

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
