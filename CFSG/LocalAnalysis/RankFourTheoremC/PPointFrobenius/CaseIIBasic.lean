module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.CaseDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.LemmaQ
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

open Subgroup
open scoped MatrixGroups commutatorElement

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding

theorem isPerfect_of_isSimpleGroup_of_nonabelian {H : Type*} [Group H] [IsSimpleGroup H]
    (hab : ∃ a b : H, a * b ≠ b * a) : Group.IsPerfect H := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator H) with h | h
  · obtain ⟨a, b, hab⟩ := hab
    have hmem : ⁅a, b⁆ ∈ commutator H := by
      rw [_root_.commutator_def]
      exact commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact absurd hmem hab
  · exact h

namespace FrobCaseIIHyp

variable {p n : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {L U : Subgroup Y} {x : Y}

theorem prime (_h : FrobCaseIIHyp p n L U x) : p.Prime := Fact.out

theorem isSimpleGroup (h : FrobCaseIIHyp p n L U x) : IsSimpleGroup L := by
  obtain ⟨e⟩ := h.equiv
  have : IsSimpleGroup (CFSG.AGLEmbedding.PSL2GF p n) :=
    CFSG.AGLEmbedding.isSimpleGroup_psl2GF_of_two_le (by have := h.three_le; omega)
  exact e.isSimpleGroup

theorem eq_one_of_mem_centralizer (h : FrobCaseIIHyp p n L U x) {l : Y} (hl : l ∈ L)
    (hc : l ∈ centralizer (L : Set Y)) : l = 1 := by
  obtain ⟨e⟩ := h.equiv
  have hc1 : (⟨l, hl⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (mem_centralizer_iff.mp hc k k.2)
  have hc2 : e ⟨l, hl⟩ ∈ Subgroup.center (CFSG.AGLEmbedding.PSL2GF p n) := by
    rw [Subgroup.mem_center_iff]
    intro z'
    obtain ⟨k, rfl⟩ := e.surjective z'
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (mem_centralizer_iff.mp hc k k.2))
  rw [CFSG.GorensteinWalter.psl2_center_eq_bot, Subgroup.mem_bot] at hc2
  have h3 : (⟨l, hl⟩ : L) = 1 := e.injective (hc2.trans (map_one e).symm)
  exact congrArg Subtype.val h3

theorem card_eq (h : FrobCaseIIHyp p n L U x) : Nat.card U = p ^ n := by
  obtain ⟨e⟩ := h.equiv
  have hp : p.Prime := Fact.out
  have hfac : (Nat.card L).factorization p = n := by
    obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow p (CFSG.AGLEmbedding.PSL2GF p n)))
    have h1 := (CFSG.AGLEmbedding.psl2GF_sylow p n (by have := h.three_le; omega) T).2
    have h2 := Sylow.card_eq_multiplicity T
    have h3 : (Nat.card (CFSG.AGLEmbedding.PSL2GF p n)).factorization p = n :=
      Nat.pow_right_injective hp.two_le (h2.symm.trans h1)
    rw [Nat.card_congr e.toEquiv]
    exact h3
  rw [h.sylow.card_eq, hfac]

theorem isElemAbelian (h : FrobCaseIIHyp p n L U x) : CFSG.Open.IsElemAbelian p U := by
  obtain ⟨e⟩ := h.equiv
  refine ⟨?_, ?_⟩
  · obtain ⟨Q, hQ⟩ := h.sylow.isPGroup.exists_le_sylow
    have hab := h.abelian Q
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have h1 := hab.is_comm.comm ⟨a, hQ a.2⟩ ⟨b, hQ b.2⟩
    have h2 := congrArg Subtype.val h1
    exact h2
  · intro u hu
    obtain ⟨Q, hQ⟩ := h.sylow
    rw [← hQ] at hu
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hu
    have hes : Function.Surjective (e : L →* CFSG.AGLEmbedding.PSL2GF p n) := e.surjective
    set T : Sylow p (CFSG.AGLEmbedding.PSL2GF p n) := Q.mapSurjective hes with hTdef
    have hT := (CFSG.AGLEmbedding.psl2GF_sylow p n (by have := h.three_le; omega) T).1
    have hmem : e q ∈ (T : Subgroup (CFSG.AGLEmbedding.PSL2GF p n)) := by
      rw [hTdef, Sylow.coe_mapSurjective]
      exact Subgroup.mem_map.2 ⟨q, hq, rfl⟩
    have h1 : (e q) ^ p = 1 := hT.2 _ hmem
    have h2 : q ^ p = 1 := by
      apply e.injective
      rw [map_pow, h1, map_one]
    show (q : Y) ^ p = 1
    rw [← Subgroup.coe_pow, h2]
    rfl

theorem commute_of_mem (h : FrobCaseIIHyp p n L U x) {a b : Y} (ha : a ∈ U) (hb : b ∈ U) :
    a * b = b * a :=
  congrArg Subtype.val ((isMulCommutative_iff.mp h.isElemAbelian.1) ⟨a, ha⟩ ⟨b, hb⟩)

theorem ne_bot (h : FrobCaseIIHyp p n L U x) : U ≠ ⊥ := by
  intro hU
  have := h.card_eq
  rw [hU, card_bot] at this
  have h1 : 1 < p ^ n := Nat.one_lt_pow (by have := h.three_le; omega) h.prime.one_lt
  omega

theorem disjoint_centralizer (h : FrobCaseIIHyp p n L U x) :
    Disjoint U (centralizer (L : Set Y)) :=
  disjoint_def.mpr fun hu hc => h.eq_one_of_mem_centralizer (h.sylow.le hu) hc

theorem nonabelian (h : FrobCaseIIHyp p n L U x) : ∃ a b : L, a * b ≠ b * a := by
  obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h.ne_bot
  by_contra hall
  push Not at hall
  apply hu1
  apply Subtype.ext
  refine h.eq_one_of_mem_centralizer (h.sylow.le u.2) (mem_centralizer_iff.mpr fun l hl => ?_)
  exact congrArg Subtype.val (hall ⟨l, hl⟩ ⟨u, h.sylow.le u.2⟩)

theorem isPerfect (h : FrobCaseIIHyp p n L U x) : Group.IsPerfect L := by
  have := h.isSimpleGroup
  exact isPerfect_of_isSimpleGroup_of_nonabelian h.nonabelian

theorem commutator_eq (h : FrobCaseIIHyp p n L U x) : ⁅L, L⁆ = L := by
  have := h.isPerfect
  exact Subgroup.commutator_eq_self

theorem orderOf_eq (h : FrobCaseIIHyp p n L U x) : orderOf x = p :=
  orderOf_eq_prime h.pow_eq_one h.ne_one

theorem commute_of_mem_sylow (h : FrobCaseIIHyp p n L U x) (Q : Sylow p Y) {a b : Y}
    (ha : a ∈ (Q : Subgroup Y)) (hb : b ∈ (Q : Subgroup Y)) : a * b = b * a :=
  congrArg Subtype.val ((isMulCommutative_iff.mp (h.abelian Q)) ⟨a, ha⟩ ⟨b, hb⟩)

theorem exists_sylow_mem (h : FrobCaseIIHyp p n L U x) :
    ∃ Q : Sylow p Y, x ∈ (Q : Subgroup Y) := by
  have hxp : IsPGroup p (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_eq, pow_one])
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  exact ⟨Q, hQ (mem_zpowers x)⟩

theorem sylow_le_centralizer (h : FrobCaseIIHyp p n L U x) {Q : Sylow p Y}
    (hxQ : x ∈ (Q : Subgroup Y)) : (Q : Subgroup Y) ≤ centralizer ({x} : Set Y) := fun _ hq =>
  mem_centralizer_singleton_iff.mpr (h.commute_of_mem_sylow Q hq hxQ)

theorem mem_zpowers_of_mem_centralizer (h : FrobCaseIIHyp p n L U x) {g : Y}
    (hg : g ∈ centralizer (L : Set Y)) (hgp : g ^ p = 1) (hgx : g * x = x * g) :
    g ∈ zpowers x := by
  by_contra hgx'
  have hxC : zpowers x ≤ centralizer ((zpowers g : Subgroup Y) : Set Y) :=
    zpowers_le.mpr (mem_centralizer_iff.mpr fun c hc => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
      exact (Commute.zpow_left hgx k).eq)
  have hBe : CFSG.Open.IsElemAbelian p (zpowers x ⊔ zpowers g) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p
      (CFSG.Open.isElemAbelian_zpowers h.pow_eq_one) (CFSG.Open.isElemAbelian_zpowers hgp) hxC
  have hBc : Nat.card (zpowers x ⊔ zpowers g : Subgroup Y) = p ^ 2 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers h.prime (zpowers x) hgp hgx' ?_,
      Nat.card_zpowers, h.orderOf_eq, sq]
    intro e he
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
    exact (Commute.zpow_left (Commute.symm hgx) k).eq
  have hBL : zpowers x ⊔ zpowers g ≤ centralizer (L : Set Y) :=
    sup_le (zpowers_le.mpr h.mem_centralizer) (zpowers_le.mpr hg)
  have h4 := CFSG.LocalAnalysis.RankThreeTheoremC.add_le_pRank_of_commute (P := ⊤)
    h.isElemAbelian hBe h.card_eq hBc
    (fun a ha b hb => mem_centralizer_iff.mp (hBL hb) a (h.sylow.le ha))
    (h.disjoint_centralizer.mono_right hBL) le_top le_top
  have := h.pRank_le
  omega

theorem map_conj_eq_of_map_conj_zpowers_eq (h : FrobCaseIIHyp p n L U x) {g : Y}
    (hg : (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x) :
    L.map (MulAut.conj g).toMonoidHom = L := by
  have hxmem : x ∈ (zpowers x).map (MulAut.conj g).toMonoidHom := by
    rw [hg]
    exact mem_zpowers x
  obtain ⟨z, hz, hzx⟩ := hxmem
  have hzL : z ∈ centralizer (L : Set Y) := zpowers_le.mpr h.mem_centralizer hz
  have hle : L.map (MulAut.conj g).toMonoidHom ≤ centralizer ({x} : Set Y) := by
    rintro _ ⟨l, hl, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hzx]
    have hzl : l * z = z * l := mem_centralizer_iff.mp hzL l hl
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * l * g⁻¹ * (g * z * g⁻¹) = g * (l * z) * g⁻¹ := by group
      _ = g * (z * l) * g⁻¹ := by rw [hzl]
      _ = g * z * g⁻¹ * (g * l * g⁻¹) := by group
  have hperf : ⁅L.map (MulAut.conj g).toMonoidHom, L.map (MulAut.conj g).toMonoidHom⁆ =
      L.map (MulAut.conj g).toMonoidHom := by
    rw [← map_commutator, h.commutator_eq]
  exact eq_of_le_of_card_ge (h.perfect_le _ hle hperf)
    (by rw [card_map_of_injective (MulAut.conj g).injective])

theorem le_centralizer_of_normal (h : FrobCaseIIHyp p n L U x)
    (hL : ∀ g : Y, L.map (MulAut.conj g).toMonoidHom = L) {W : Subgroup Y}
    (hcop : Nat.Coprime p (Nat.card W)) (hN : U ≤ normalizer (W : Set Y)) :
    W ≤ centralizer (L : Set Y) := by
  obtain ⟨e⟩ := h.equiv
  exact le_centralizer_of_coprime_of_psl2GF (by have := h.five_le; omega)
    (by have := h.three_le; omega) e h.sylow.le h.sylow.isPGroup h.card_eq
    (fun g _ => mem_normalizer_iff_map_conj_eq.mpr (hL g)) hN hcop

theorem map_conj_eq_of_pCore_ne_bot (h : FrobCaseIIHyp p n L U x)
    (hR : CFSG.pCore p Y ≠ ⊥) (g : Y) : L.map (MulAut.conj g).toMonoidHom = L := by
  obtain ⟨Q, hxQ⟩ := h.exists_sylow_mem
  have hRn : (CFSG.pCore p Y).Normal := CFSG.pCore_normal
  have hRQ : CFSG.pCore p Y ≤ Q := CFSG.pCore_isPGroup.le_sylow_of_normal Q
  have hRN : CFSG.pCore p Y ≤ normalizer (L : Set Y) :=
    hRQ.trans ((h.sylow_le_centralizer hxQ).trans h.centralizer_le)
  have hRL : CFSG.pCore p Y ⊓ L = ⊥ := by
    have := h.isSimpleGroup
    have : ((CFSG.pCore p Y).subgroupOf L).Normal := hRn.subgroupOf L
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore p Y).subgroupOf L) with h1 | h1
    · rw [← subgroupOf_map_subtype, h1, Subgroup.map_bot]
    · exfalso
      have hLR : L ≤ CFSG.pCore p Y := subgroupOf_eq_top.mp h1
      obtain ⟨a, b, hab⟩ := h.nonabelian
      exact hab (Subtype.ext (h.commute_of_mem_sylow Q (hRQ (hLR a.2)) (hRQ (hLR b.2))))
  have hRC : CFSG.pCore p Y ≤ centralizer (L : Set Y) := by
    intro r hr
    rw [mem_centralizer_iff]
    intro l hl
    have h1 : r * l * r⁻¹ * l⁻¹ ∈ CFSG.pCore p Y ⊓ L := by
      refine ⟨?_, L.mul_mem ((mem_normalizer_iff.mp (hRN hr) l).mp hl) (L.inv_mem hl)⟩
      have : l * r⁻¹ * l⁻¹ ∈ CFSG.pCore p Y := hRn.conj_mem _ (inv_mem hr) l
      simpa [mul_assoc] using mul_mem hr this
    rw [hRL, mem_bot] at h1
    calc l * r = (r * l * r⁻¹ * l⁻¹)⁻¹ * (r * l) := by group
      _ = r * l := by rw [h1, inv_one, one_mul]
  have hdvd : p ∣ Nat.card (CFSG.pCore p Y) := by
    have : Nontrivial (CFSG.pCore p Y) := (nontrivial_iff_ne_bot _).2 hR
    obtain ⟨n, hn, hcard⟩ := (CFSG.pCore_isPGroup (p := p) (G := Y)).nontrivial_iff_card.1 this
    rw [hcard]
    exact dvd_pow_self p hn.ne'
  obtain ⟨⟨r, hrR⟩, hr⟩ := exists_prime_orderOf_dvd_card' (G := CFSG.pCore p Y) p hdvd
  have hr' : orderOf r = p := by rw [← Subgroup.orderOf_mk r hrR, hr]
  have hrx : r ∈ zpowers x := h.mem_zpowers_of_mem_centralizer (hRC hrR)
    (hr' ▸ pow_orderOf_eq_one r) (h.commute_of_mem_sylow Q (hRQ hrR) hxQ)
  have hxR : x ∈ CFSG.pCore p Y := by
    have heq : zpowers r = zpowers x := eq_of_le_of_card_ge (zpowers_le.mpr hrx)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, h.orderOf_eq, hr'])
    exact zpowers_le.mpr hrR (heq ▸ mem_zpowers x)
  have hmap : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ Q := by
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr (hRQ (hRn.conj_mem x hxR g))
  exact h.map_conj_eq_of_map_conj_zpowers_eq (h.weakClosed Q hxQ g hmap)

end FrobCaseIIHyp

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
