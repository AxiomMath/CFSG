module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BFiveHS
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentA

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Blueprint CFSG.RankThree.Native Subgroup

section Generic

variable {K : Type*} [Group K] [Finite K]

private theorem conj_mem_of_relIndex_le {E L : Subgroup K} (hsimple : IsSimpleGroup E)
    (hEL : E ≤ L) (hidx : E.relIndex L ≤ 14) (hbig : ¬ Nat.card E ∣ Nat.factorial 14) {c : K}
    (hc : c ∈ L) {e : K} (he : e ∈ E) : c * e * c⁻¹ ∈ E := by
  haveI := hsimple
  have hIL : E.map (MulAut.conj c).toMonoidHom ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    exact L.mul_mem (L.mul_mem hc (hEL hy)) (L.inv_mem hc)
  have hcard : Nat.card (E.map (MulAut.conj c).toMonoidHom) = Nat.card E :=
    card_map_of_injective (MulAut.conj c).injective
  have h1 : E.relIndex (E.map (MulAut.conj c).toMonoidHom) ≤ 14 :=
    (relIndex_le_of_le_right hIL (by rw [relIndex]; exact index_ne_zero_of_finite)).trans hidx
  have h2 := relIndex_mul_card E (E.map (MulAut.conj c).toMonoidHom)
  have h3 := relIndex_mul_card (E.map (MulAut.conj c).toMonoidHom) E
  rw [inf_comm] at h3
  have hpos : 0 < Nat.card ↥(E ⊓ E.map (MulAut.conj c).toMonoidHom) := Nat.card_pos
  have h4 : (E.map (MulAut.conj c).toMonoidHom).relIndex E =
      E.relIndex (E.map (MulAut.conj c).toMonoidHom) := by
    rw [hcard] at h2
    exact Nat.eq_of_mul_eq_mul_right hpos (h3.trans h2.symm)
  have hJ : (E.map (MulAut.conj c).toMonoidHom).subgroupOf E = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((E.map (MulAut.conj c).toMonoidHom).subgroupOf E).normalCore with hb | ht
    · refine absurd ?_ hbig
      have hd := index_normalCore_dvd_factorial_index
        ((E.map (MulAut.conj c).toMonoidHom).subgroupOf E)
      rw [hb, index_bot] at hd
      refine hd.trans ?_
      rw [← relIndex, h4]
      exact Nat.factorial_dvd_factorial h1
    · exact eq_top_iff.2 (ht ▸ ((E.map (MulAut.conj c).toMonoidHom).subgroupOf E).normalCore_le)
  have heq : E.map (MulAut.conj c).toMonoidHom = E :=
    (eq_of_le_of_card_ge (subgroupOf_eq_top.1 hJ) hcard.le).symm
  have hm : (MulAut.conj c).toMonoidHom e ∈ E.map (MulAut.conj c).toMonoidHom :=
    mem_map_of_mem _ he
  rw [heq] at hm
  simpa [MulAut.conj_apply] using hm

private theorem not_mem_of_simple_le_centralizer {E : Subgroup K} (hsimple : IsSimpleGroup E)
    {s : K} (hEs : E ≤ centralizer ({s} : Set K)) (hs : s ≠ 1) (hcard : orderOf s < Nat.card E) :
    s ∉ E := by
  intro hsE
  haveI := hsimple
  have hZ : ((zpowers s).subgroupOf E).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hn
    have hc : Commute (g : K) s := mem_centralizer_singleton_iff.1 (hEs g.2)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hk, (hc.zpow_right k).eq,
      mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers s) k
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((zpowers s).subgroupOf E) with hb | ht
  · have hmem : (⟨s, hsE⟩ : E) ∈ (zpowers s).subgroupOf E := mem_subgroupOf.2 (mem_zpowers s)
    rw [hb, mem_bot] at hmem
    exact hs (congrArg Subtype.val hmem)
  · have hle := card_le_of_le (subgroupOf_eq_top.1 ht)
    rw [Nat.card_zpowers] at hle
    omega

private theorem card_mul_five_dvd {E : Subgroup K} {s w : K} (hs5 : orderOf s = 5) (hsE : s ∉ E)
    (hEs : E ≤ centralizer ({s} : Set K)) (hEw : E ≤ centralizer ({w} : Set K))
    (hsw : s ∈ centralizer ({w} : Set K)) :
    Nat.card E * 5 ∣ Nat.card (centralizer ({w} : Set K)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hconj : ∀ g ∈ E, s⁻¹ * g * s ∈ E := fun g hg => by
    rwa [mul_assoc, mem_centralizer_singleton_iff.1 (hEs hg), inv_mul_cancel_left]
  rw [← CFSG.Monster.B.Pinned.card_sup_zpowers hs5 hsE hconj]
  exact card_dvd_of_le (sup_le hEw (zpowers_le.2 hsw))

end Generic

section HSCopy


private theorem false_of_hs_le_centralizer {Q : Type*} [Group Q] [Finite Q] {s : Q}
    (hs5 : orderOf s = 5) {E : Subgroup Q} (hEC : E ≤ centralizer ({s} : Set Q))
    (φ : ↥E ≃* NativeSporadic.HS) (hC : Nat.card ↥(centralizer ({s} : Set Q)) < 665280000)
    (hinv : ∀ w : Q, orderOf w = 2 → ¬ 44352000 * 5 ∣ Nat.card ↥(centralizer ({w} : Set Q)))
    {F W : Subgroup Q} (hF : IsElemAbelian 5 F) (hFc : Nat.card F = 5 ^ 2) (hsF : s ∈ F)
    (hW : IsElemAbelian 2 W) (hWc : Nat.card W = 2 ^ 4) (hFW : F ≤ centralizer (W : Set Q)) :
    False := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimpleHS : IsSimpleGroup NativeSporadic.HS := CFSG.Sporadic.HS.isSimpleGroup_HS
  have hsimple : IsSimpleGroup ↥E := @MulEquiv.isSimpleGroup _ _ NativeSporadic.HS _ hsimpleHS φ
  have hEcard : Nat.card ↥E = 44352000 := by
    rw [Nat.card_congr φ.toEquiv]
    exact CFSG.Sporadic.HS.card_HS
  have hidx : E.relIndex (centralizer ({s} : Set Q)) ≤ 14 := by
    have h1 := relIndex_mul_card E (centralizer ({s} : Set Q))
    rw [inf_of_le_left hEC, hEcard] at h1
    omega
  have hbig : ¬ Nat.card ↥E ∣ Nat.factorial 14 := by
    rw [hEcard]
    norm_num [Nat.factorial]
  have hFC : F ≤ centralizer ({s} : Set Q) := fun f hf => by
    have := hF.1
    exact mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (mul_comm' (⟨f, hf⟩ : F) ⟨s, hsF⟩))
  obtain ⟨e, heE, heF, he1⟩ : ∃ e ∈ E, e ∈ F ∧ e ≠ 1 := by
    have h1 : E.relIndex F ≤ 14 := (relIndex_le_of_le_right hFC
      (by rw [relIndex]; exact index_ne_zero_of_finite)).trans hidx
    have h2 := relIndex_mul_card E F
    rw [hFc, show (5 : ℕ) ^ 2 = 25 by norm_num] at h2
    have h3 : E ⊓ F ≠ ⊥ := fun hb => by
      rw [hb, card_bot, mul_one] at h2
      omega
    obtain ⟨⟨e, he⟩, he1⟩ := ne_bot_iff_exists_ne_one.1 h3
    exact ⟨e, (mem_inf.1 he).1, (mem_inf.1 he).2, fun h => he1 (Subtype.ext h)⟩
  have hWC : W ≤ centralizer ({s} : Set Q) := fun w hw =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hFW hsF) w hw)
  have hCN : centralizer ({s} : Set Q) ≤ normalizer (E : Set Q) :=
    le_normalizer_iff.2 fun c hc x hx => conj_mem_of_relIndex_le hsimple hEC hidx hbig hc hx
  have hs1 : s ≠ 1 := fun h => by
    rw [h, orderOf_one] at hs5
    exact absurd hs5 (by norm_num)
  have hsE : s ∉ E :=
    not_mem_of_simple_le_centralizer hsimple hEC hs1 (by rw [hs5, hEcard]; norm_num)
  have hfaith : ∀ w ∈ W, w ≠ 1 → ∃ x ∈ E, w * x ≠ x * w := by
    intro w hw hw1
    by_contra hall
    push Not at hall
    have hd := card_mul_five_dvd hs5 hsE hEC
      (fun x hx => mem_centralizer_singleton_iff.2 (hall x hx).symm)
      (mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hFW hsF) w hw).symm)
    rw [hEcard] at hd
    exact hinv w (orderOf_eq_prime (hW.2 w hw) hw1) hd
  refine false_of_autModel CFSG.RankThree.PartOne.hs_autModel (fun x hx hx5 => ?_)
    (φ.trans hs100Equiv) hWc (hWC.trans hCN) hfaith heE (orderOf_eq_prime (hF.2 e heF) he1)
    fun w hw => mem_centralizer_iff.1 (hFW heF) w hw
  rcases card_centralizer_hs100R_of_five hx hx5 with h | h | h <;> rw [h] <;> decide

end HSCopy

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (sFiveA orderOf_sFiveA)


theorem false_of_fiveA_B
    {F W : Subgroup NativeSporadic.B} (hF : IsElemAbelian 5 F)
    (hFc : Nat.card F = 5 ^ 2) (hsF : sFiveA ∈ F) (hW : IsElemAbelian 2 W)
    (hWc : Nat.card W = 2 ^ 4) (hFW : F ≤ centralizer (W : Set NativeSporadic.B)) : False := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨E, hEC, ⟨φ⟩⟩ := CFSG.HardMathSupport.Dickson.I271.tabBFiveAHS_of_cert
  refine false_of_hs_le_centralizer orderOf_sFiveA hEC φ
    CFSG.HardMathSupport.Dickson.I271.TabBFiveCent.tabBFiveACard_holds (fun w hw => ?_) hF hFc
    hsF hW hWc hFW
  obtain ⟨k, -, hk⟩ := CFSG.Monster.Existence.babyTableIII.1 w hw
  rw [hk]
  fin_cases k <;> decide

end CFSG.LocalAnalysis.GLTheoremA.H1017
