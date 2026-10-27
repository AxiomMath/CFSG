module

public import CFSG.Open.LocalVocabulary
import CFSG.Quasithin.Vol2.Ch11SKFIto
import CFSG.Quasithin.H13.U3S1348J

public section

namespace CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G]

theorem pRank_add_one_le_of_commutator_le_pCoreOf {q : ℕ} [hqp : Fact q.Prime] (hq : q ≠ 2)
    {M L X : Subgroup G} (hLM : L ≤ M) (hXM : X ≤ M)
    (hcomm : ⁅L, X⁆ ≤ CFSG.Open.pCoreOf 2 M) (hX : ⁅X, X⁆ = X) (hqX : q ∣ Nat.card X) :
    CFSG.Open.pRank q L + 1 ≤ CFSG.Open.pRank q M := by
  classical
  have hqprime : q.Prime := hqp.out
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup ↥M := CFSG.pCore 2 ↥M with hK
  haveI hKn : K.Normal := hK ▸ CFSG.pCore_normal
  set π : ↥M →* (↥M ⧸ K) := QuotientGroup.mk' K with hπ
  set l : Subgroup ↥M := L.subgroupOf M with hl
  set x : Subgroup ↥M := X.subgroupOf M with hx
  have hlmap : l.map M.subtype = L := by rw [hl, Subgroup.map_subgroupOf_eq_of_le hLM]
  have hxmap : x.map M.subtype = X := by rw [hx, Subgroup.map_subgroupOf_eq_of_le hXM]
  have hK2 : IsPGroup 2 K := by
    rw [hK]
    exact CFSG.pCore_isPGroup
  have hqK : ¬ q ∣ Nat.card K := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK2
    rw [hn]
    intro hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp (hqprime.dvd_of_dvd_pow hdvd) with h | h
    · exact hqprime.ne_one h
    · exact hq h
  have hcommH : ⁅l, x⁆ ≤ K := by
    have h := hcomm
    rw [← hlmap, ← hxmap, ← Subgroup.map_commutator] at h
    rw [← (show K.map M.subtype = CFSG.Open.pCoreOf 2 M from rfl)] at h
    exact (Subgroup.map_le_map_iff_of_injective M.subtype_injective).mp h
  have hxx : ⁅x, x⁆ = x := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, hxmap, hX]
  have hperf_x : Group.IsPerfect ↥x := Subgroup.isPerfect_iff.mpr hxx
  have hq_x : q ∣ Nat.card x := by
    rw [show Nat.card x = Nat.card X from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv]
    exact hqX
  haveI : Group.IsPerfect ↥x := hperf_x
  have hxRperf : Group.IsPerfect ↥(x.map π) := Group.IsPerfect.map (H := x) π
  have hq_xR : q ∣ Nat.card (x.map π) := by
    have hcard := CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker π x
    rw [show π.ker = K from QuotientGroup.ker_mk' K] at hcard
    have hxK2 : IsPGroup 2 ↥(x ⊓ K) := hK2.to_le inf_le_right
    have hq_not : ¬ q ∣ Nat.card ↥(x ⊓ K) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hxK2
      rw [hn]
      intro hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp (hqprime.dvd_of_dvd_pow hdvd) with h | h
      · exact hqprime.ne_one h
      · exact hq h
    have hqprod : q ∣ Nat.card (x.map π) * Nat.card ↥(x ⊓ K) := hcard ▸ hq_x
    rcases hqprime.dvd_mul.mp hqprod with h | h
    · exact h
    · exact absurd h hq_not
  obtain ⟨E, hEL, hEabel, hEcard⟩ := CFSG.SectionRank.exists_pRank hqprime.one_lt L
  set EM : Subgroup ↥M := E.subgroupOf M with hEM
  have hEM_le_l : EM ≤ l := by
    intro y hy
    exact hEL hy
  have hEMabel : CFSG.Open.IsElemAbelian q EM := by
    rw [hEM]
    exact hEabel.subgroupOf M
  have hEMcard : Nat.card EM = q ^ CFSG.Open.pRank q L := by
    rw [hEM]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEL.trans hLM)).toEquiv).trans hEcard
  have hEMdisj : Disjoint EM K :=
    IsPGroup.disjoint_of_ne q 2 hq EM K hEMabel.isPGroup hK2
  set ER : Subgroup (↥M ⧸ K) := EM.map π with hER
  have hER_le_lR : ER ≤ l.map π := by
    rw [hER]
    exact Subgroup.map_mono hEM_le_l
  have hERabel : CFSG.Open.IsElemAbelian q ER := by
    rw [hER]
    exact hEMabel.map π
  have hERcard : Nat.card ER = q ^ CFSG.Open.pRank q L := by
    have hcard := CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker π EM
    rw [show π.ker = K from QuotientGroup.ker_mk' K, hEMdisj.eq_bot, Subgroup.card_bot,
      mul_one] at hcard
    rw [hER, ← hcard]
    exact hEMcard
  have hcommR : ⁅l.map π, x.map π⁆ = ⊥ := by
    have hmapcomm : ⁅l.map π, x.map π⁆ = (⁅l, x⁆).map π :=
      (Subgroup.map_commutator l x π).symm
    rw [hmapcomm, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hcommH
  obtain ⟨y, hyq, hyZ⟩ := CFSG.Quasithin.Vol2.Ch11.SecS.KF.exists_pow_eq_one_not_mem_center
    (p := q) (L := ↥(x.map π)) hq hq_xR
  have hyxR : (y : ↥M ⧸ K) ∈ x.map π := y.2
  have hyLp : (y : ↥M ⧸ K) ∈ l.map π → False := by
    intro hyL
    apply hyZ
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    have hmem := Subgroup.commutator_mem_commutator hyL z.2
    rw [hcommR] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)).symm
  have hy_notin : (y : ↥M ⧸ K) ∉ ER := fun hyER => hyLp (hER_le_lR hyER)
  have hyq' : (y : ↥M ⧸ K) ^ q = 1 := by
    have := congrArg (fun t : ↥(x.map π) => (t : ↥M ⧸ K)) hyq
    simpa using this
  have hy_comm : ∀ a ∈ ER, a * (y : ↥M ⧸ K) = (y : ↥M ⧸ K) * a := by
    intro a ha
    have haL : a ∈ l.map π := hER_le_lR ha
    have hmem := Subgroup.commutator_mem_commutator haL hyxR
    rw [hcommR] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
  obtain ⟨hAabel, hAcard⟩ := CFSG.Quasithin.H13.U3.elemAbelian_sup_zpowers
    (p := q) (A := ER) hERabel hy_notin hyq' hy_comm
  have hrankR : CFSG.Open.pRank q L + 1 ≤
      CFSG.Open.pRank q (⊤ : Subgroup (↥M ⧸ K)) := by
    refine CFSG.SectionRank.le_pRank hqprime.one_lt le_top hAabel ?_
    rw [hAcard, hERcard, pow_succ]
  have hEq : CFSG.Open.pRank q (⊤ : Subgroup (↥M ⧸ K)) = CFSG.Open.pRank q M := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top q (↥M ⧸ K),
      CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd (p := q) hqprime K hqK,
      CFSG.SectionRank.pRank_eq_open_pRank_top q ↥M,
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup M]
  exact hEq ▸ hrankR

end CFSG.GroupTheory
