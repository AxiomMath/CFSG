module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmBase
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafGLR

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SP1

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

set_option linter.unusedSectionVars false

theorem perfect_card_dvd_84_subsingleton {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (h : Nat.card H ∣ 84) : Subsingleton H := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 7 H))
  haveI : Finite (Sylow 7 H) := Sylow.finite_of_finiteIndex P
  have hn : Nat.card (Sylow 7 H) ∣ 84 :=
    (Sylow.card_dvd_index P).trans ((Subgroup.index_dvd_card _).trans h)
  have hn1 : Nat.card (Sylow 7 H) = 1 := by
    have hmod := card_sylow_modEq_one 7 H
    unfold Nat.ModEq at hmod
    have hle : Nat.card (Sylow 7 H) ≤ 84 := Nat.le_of_dvd (by norm_num) hn
    generalize Nat.card (Sylow 7 H) = k at hn hmod hle ⊢
    interval_cases k <;> omega
  haveI : Subsingleton (Sylow 7 H) := (Nat.card_eq_one_iff_unique.1 hn1).1
  haveI : P.toSubgroup.Normal := Sylow.normal_of_subsingleton P
  haveI : Group.IsNilpotent P.toSubgroup := IsPGroup.isNilpotent P.isPGroup'
  have hidx : P.toSubgroup.index ∣ 84 := (Subgroup.index_dvd_card _).trans h
  have hidx7 : ¬ 7 ∣ P.toSubgroup.index := Sylow.not_dvd_index P
  have hcop : Nat.Coprime P.toSubgroup.index 7 :=
    (Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hidx7)
  have h12 : P.toSubgroup.index ∣ 12 :=
    Nat.Coprime.dvd_of_dvd_mul_right hcop (by simpa using hidx)
  have hquot : Group.IsSolvable (H ⧸ P.toSubgroup) := by
    apply CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    rw [← Subgroup.index_eq_card]
    have hsub : P.toSubgroup.index.primeFactors ⊆ (12 : ℕ).primeFactors :=
      Nat.primeFactors_mono h12 (by norm_num)
    have h12card : ((12 : ℕ).primeFactors).card ≤ 2 := by
      have : (12 : ℕ).primeFactors = {2, 3} := by
        rw [show (12 : ℕ) = 2 * (2 * 3) by norm_num, Nat.primeFactors_mul (by norm_num)
          (by norm_num), Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors (by norm_num)]
        decide
      rw [this]
      exact Finset.card_le_two
    exact (Finset.card_le_card hsub).trans h12card
  have hsolv : Group.IsSolvable H := Group.isSolvable_of_subgroup_quotient P.toSubgroup
  by_contra hnot
  haveI : Nontrivial H := not_subsingleton_iff_nontrivial.1 hnot
  exact Group.IsPerfect.not_isSolvable H hsolv

theorem perfect_card_2688_false {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (hcard : Nat.card G = 2688) (D : Subgroup G) [D.Normal] (hD2 : IsPGroup 2 ↥D)
    (hD32 : 32 ∣ Nat.card D) : False := by
  have hidx : D.index ∣ 84 := by
    have h1 : D.index * 32 ∣ 84 * 32 := by
      rw [show (84 : ℕ) * 32 = 2688 by norm_num, ← hcard, ← Subgroup.index_mul_card]
      exact Nat.mul_dvd_mul_left _ hD32
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h1
  have hDtop : D = ⊤ := by
    have hsub : Subsingleton (G ⧸ D) :=
      perfect_card_dvd_84_subsingleton (by rw [← Subgroup.index_eq_card]; exact hidx)
    exact QuotientGroup.subgroup_eq_top_of_subsingleton D hsub
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG2 : IsPGroup 2 G := by
    have h1 : IsPGroup 2 ↥(⊤ : Subgroup G) := hDtop ▸ hD2
    exact h1.of_equiv Subgroup.topEquiv
  haveI : Group.IsNilpotent G := IsPGroup.isNilpotent hG2
  have hsub : Subsingleton G := by
    by_contra hnot
    haveI : Nontrivial G := not_subsingleton_iff_nontrivial.1 hnot
    exact Group.IsPerfect.not_isSolvable G inferInstance
  have h1 : Nat.card G = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
  omega

theorem isTwoPrimeTwo_of_isPGroup {Y : Type} [Group Y] {K : Subgroup Y} (h : IsPGroup 2 ↥K) :
    IsTwoPrimeTwo K := by
  refine ⟨⊥, bot_le, ?_, ?_, ?_⟩
  · rw [Subgroup.bot_subgroupOf]
    infer_instance
  · rw [Subgroup.card_bot]
    exact odd_one
  · intro g hg
    obtain ⟨k, hk⟩ := h ⟨g, hg⟩
    refine ⟨k, ?_⟩
    rw [Subgroup.mem_bot]
    simpa using congrArg Subtype.val hk

theorem oTwoPrime_eq_bot {Y : Type} [Group Y] [Finite Y] {H : Subgroup Y}
    (h : CFSG.oddCore ↥H = ⊥) : oTwoPrime H = ⊥ := by
  have hle : pPrimeCore 2 ↥H ≤ CFSG.oddCore ↥H := by
    unfold pPrimeCore CFSG.oddCore
    apply sSup_le
    rintro K ⟨hn, hc⟩
    exact le_sSup ⟨hn, Nat.coprime_two_left.mp hc⟩
  rw [h, le_bot_iff] at hle
  rw [oTwoPrime, hle, Subgroup.map_bot]

theorem isPGroup_oTwoPrimeTwo {Y : Type} [Group Y] [Finite Y] {H : Subgroup Y}
    (h : oTwoPrime H = ⊥) : IsPGroup 2 ↥(oTwoPrimeTwo H) := by
  rintro ⟨g, hg⟩
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoPrime H hg
  rw [h, Subgroup.mem_bot] at hk
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem thirtytwo_le_card {Y : Type} [Group Y] [Finite Y] {D K K' : Subgroup Y} (hK : K ≤ D)
    (hK' : K' ≤ D) (h8 : Nat.card K = 8) (h8' : Nat.card K' = 8)
    (h2 : Nat.card ↥(K ⊓ K') = 2) : 32 ≤ Nat.card D := by
  have ha := Subgroup.relIndex_mul_card K D
  have ha' := Subgroup.relIndex_mul_card K' D
  have hb := Subgroup.relIndex_mul_card (K ⊓ K') D
  rw [inf_of_le_left hK, h8] at ha
  rw [inf_of_le_left hK', h8'] at ha'
  rw [inf_of_le_left (inf_le_left.trans hK), h2] at hb
  have hle : (K ⊓ K').relIndex D ≤ K.relIndex D * K'.relIndex D := Subgroup.relIndex_inf_le
  have hpos : 0 < Nat.card D := Nat.card_pos
  generalize K.relIndex D = a at ha hle
  generalize K'.relIndex D = a' at ha' hle
  generalize (K ⊓ K').relIndex D = b at hb hle
  have haa : a' = a := by omega
  subst haa
  have hb4 : b = 4 * a' := by omega
  subst hb4
  have ha0 : 0 < a' := by omega
  have h4 : 4 ≤ a' := by nlinarith
  omega

theorem thirtytwo_dvd_card {M : Type} [Group M] [Finite M] (hM : IsPGroup 2 M)
    (h : 32 ≤ Nat.card M) : 32 ∣ Nat.card M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hM
  rw [hm] at h ⊢
  have h5 : 5 ≤ m := by
    by_contra hlt
    have hlt' : m < 5 := by omega
    interval_cases m <;> norm_num at h
  simpa using Nat.pow_dvd_pow 2 h5


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem isPGroup_core_of_oddCore (h : PerpHypS n Y R S t)
    (hO : CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥) :
    IsPGroup 2 ↥(tightCore R) := by
  refine isPGroup_core_of_oddCore_centralizer h ?_
  have e : Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) =
      (CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set Y))).map
        (Subgroup.centralizer ({t} : Set Y)).subtype := rfl
  rw [e, hO, Subgroup.map_bot]

theorem card_core_eq_eight (h : PerpHypS n Y R S t) (hK2 : IsPGroup 2 ↥(tightCore R)) :
    Nat.card ↥(tightCore R) = 8 := by
  have hsyl := h.core.datum.sylow_core
  have heq : tightCore R = (S : Subgroup R).map R.subtype := hsyl.2.2 _ le_rfl hK2 hsyl.1
  rw [heq, Subgroup.card_map_of_injective R.subtype_injective]
  obtain ⟨e⟩ := h.core.q8
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem card_conjSub_eq (g : Y) (K : Subgroup Y) : Nat.card ↥(conjSub g K) = Nat.card ↥K :=
  Nat.card_congr (Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.toEquiv

theorem thirtytwo_le_card_oTwoPrimeTwo (h : PerpHypS n Y R S t) (hK2 : IsPGroup 2 ↥(tightCore R))
    {g : Y} (hg : g ∈ Subgroup.centralizer ({t} : Set Y))
    (hne : conjSub g (tightCore R) ≠ tightCore R) :
    tightCore R ≤ oTwoPrimeTwo (Subgroup.centralizer ({t} : Set Y)) ∧
      conjSub g (tightCore R) ≤ oTwoPrimeTwo (Subgroup.centralizer ({t} : Set Y)) ∧
      32 ≤ Nat.card ↥(oTwoPrimeTwo (Subgroup.centralizer ({t} : Set Y))) := by
  have hct : g * t * g⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    rw [hg]; group
  have hz' : IsUniqueInvolution (conjSub g (tightCore R)) t := by
    have := (uniqueInv_core h).conj g
    rwa [hct] at this
  have hsub' : CFSG.Open.IsSubnormal (conjSub g (tightCore R))
      (Subgroup.centralizer ({t} : Set Y)) :=
    isSubnormal_of_hypOmegaGen h.core.hyp ⟨g, rfl⟩ hz'
  have hKD := le_oTwoPrimeTwo_of_isSubnormal (isSubnormal_core h) (isTwoPrimeTwo_of_isPGroup hK2)
  have hK'D := le_oTwoPrimeTwo_of_isSubnormal hsub'
    (isTwoPrimeTwo_of_isPGroup (isPGroup_conjSub hK2 g))
  have h8 := card_core_eq_eight h hK2
  have h8' : Nat.card ↥(conjSub g (tightCore R)) = 8 := by rw [card_conjSub_eq, h8]
  have hinf := (twin_facts h hK2 hg hne).2
  have h2 : Nat.card ↥(tightCore R ⊓ conjSub g (tightCore R)) = 2 := by
    rw [hinf, Nat.card_zpowers, h.core.datum.order]
  exact ⟨hKD, hK'D, thirtytwo_le_card hKD hK'D h8 h8' h2⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SP1
