module

public import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.RankThree.PartOne.S9.Planes.Transfer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup CFSG.RankThree.PartOne.Planes

variable {G : Type*} [Group G]

@[expose] def IsIsolatedPlane (p : ℕ) (P V : Subgroup G) : Prop :=
  V ≤ P ∧ CFSG.IsElementaryAbelian p V ∧ Nat.card V = p ^ 2 ∧
    ∀ E : Subgroup G, E ≤ P → CFSG.IsElementaryAbelian p E → V ≤ E → Nat.card E ≤ p ^ 2

theorem mem_of_isIsolatedPlane [Finite G] {p : ℕ} (hp : p.Prime) {P V : Subgroup G}
    (hV : IsIsolatedPlane p P V) {y : G} (hyP : y ∈ P) (hyc : y ∈ centralizer (P : Set G))
    (hyp : y ^ p = 1) : y ∈ V := by
  by_contra hyV
  obtain ⟨hVP, hVe, hVc, hiso⟩ := hV
  have hcomm : ∀ e ∈ V, e * y = y * e := fun e he => mem_centralizer_iff.1 hyc e (hVP he)
  have hcard := card_sup_zpowers hp V hyp hyV hcomm
  have hle : zpowers y ≤ centralizer (V : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun e he => hcomm e he
  have : CFSG.IsElementaryAbelian p V := hVe
  have : CFSG.IsElementaryAbelian p (zpowers y) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hyp
  have hE : CFSG.IsElementaryAbelian p ↥(V ⊔ zpowers y) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer hle
  have hEP : V ⊔ zpowers y ≤ P := sup_le hVP ((zpowers_le).2 hyP)
  have hbound := hiso _ hEP hE le_sup_left
  rw [hcard, hVc] at hbound
  have hp1 := hp.one_lt
  have : p ^ 2 * p ≤ p ^ 2 * 1 := by simpa using hbound
  have := Nat.le_of_mul_le_mul_left this (by positivity)
  omega

theorem isolatedPlane_structure [Finite G] {p : ℕ} (hp : p.Prime)
    {P V A : Subgroup G} (hP : IsPGroup p P) (hV : IsIsolatedPlane p P V) (hAP : A ≤ P)
    (hA : CFSG.IsElementaryAbelian p A) (hAc : Nat.card A = p ^ 3) :
    ¬ P ≤ normalizer (V : Set G) ∧
      ∃ z ∈ V, z ≠ 1 ∧ z ∈ centralizer (P : Set G) ∧ z ^ p = 1 ∧
        ∀ y ∈ P, y ∈ centralizer (P : Set G) → y ^ p = 1 → y ∈ zpowers z := by
  classical
  have hp1 := hp.one_lt
  have hfact : Fact p.Prime := ⟨hp⟩
  obtain ⟨hVP, hVe, hVc, hiso⟩ := hV
  have hVi : IsIsolatedPlane p P V := ⟨hVP, hVe, hVc, hiso⟩
  have hnotnormal : ¬ P ≤ normalizer (V : Set G) := by
    intro hVn
    obtain ⟨-, hbig⟩ := normalPlane_concrete hp hP hVP hVn hVe hVc hAP hA hAc
    have : CFSG.IsElementaryAbelian p V := hVe
    have : CFSG.IsElementaryAbelian p ↥(A ⊓ centralizer (V : Set G)) :=
      isElementaryAbelian_of_le inf_le_left hA
    have hle : V ≤ centralizer ((A ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
      intro v hv
      exact mem_centralizer_iff.2 fun x hx => (mem_centralizer_iff.1 hx.2 v hv).symm
    have hE : CFSG.IsElementaryAbelian p ↥((A ⊓ centralizer (V : Set G)) ⊔ V) :=
      CFSG.IsElementaryAbelian.sup_of_le_centralizer hle
    have hEP : (A ⊓ centralizer (V : Set G)) ⊔ V ≤ P := sup_le (inf_le_left.trans hAP) hVP
    have hbound := hiso _ hEP hE le_sup_right
    have : p ^ 3 ≤ p ^ 2 := hbig.trans hbound
    have := (Nat.pow_le_pow_iff_right hp1).1 this
    omega
  refine ⟨hnotnormal, ?_⟩
  have hPnt : Nontrivial P := by
    have hA1 : 1 < Nat.card A := by
      rw [hAc]
      exact Nat.one_lt_pow (by norm_num) hp1
    have hAbot : A ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot A).1 hA1
    have hPbot : P ≠ ⊥ := fun h => hAbot (le_bot_iff.1 (h ▸ hAP))
    exact Finite.one_lt_card_iff_nontrivial.1 ((Subgroup.one_lt_card_iff_ne_bot P).2 hPbot)
  have hZnt : Nontrivial (center P) := hP.center_nontrivial
  have hZp : IsPGroup p (center P) := hP.to_subgroup (center P)
  obtain ⟨n, hn, hcard⟩ := hZp.nontrivial_iff_card.1 hZnt
  have hdvd : p ∣ Nat.card (center P) := by
    rw [hcard]
    exact dvd_pow_self p (Nat.pos_iff_ne_zero.1 hn)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := center P) p hdvd
  set z : G := ((w : P) : G) with hz
  have hzP : z ∈ P := (w : P).2
  have hzc : z ∈ centralizer (P : Set G) := by
    refine mem_centralizer_iff.2 fun g hg => ?_
    have := mem_center_iff.1 w.2 ⟨g, hg⟩
    exact (congrArg Subtype.val this)
  have hzord : orderOf z = p := by
    rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hw
  have hzp : z ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzord
    omega
  have hzV : z ∈ V := mem_of_isIsolatedPlane hp hVi hzP hzc hzp
  refine ⟨z, hzV, hz1, hzc, hzp, ?_⟩
  intro y hyP hyc hyp
  by_contra hyz
  have hyV : y ∈ V := mem_of_isIsolatedPlane hp hVi hyP hyc hyp
  apply hnotnormal
  have hcommzy : ∀ e ∈ zpowers z, e * y = y * e := by
    intro e he
    have heP : e ∈ P := (zpowers_le.2 hzP) he
    exact mem_centralizer_iff.1 hyc e heP
  have hcard2 := card_sup_zpowers hp (zpowers z) hyp hyz hcommzy
  have hcardz : Nat.card (zpowers z) = p := by rw [Nat.card_zpowers, hzord]
  have hle : zpowers z ⊔ zpowers y ≤ V := sup_le (zpowers_le.2 hzV) (zpowers_le.2 hyV)
  have heq : zpowers z ⊔ zpowers y = V := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hcard2, hcardz, hVc, pow_two]
  have hVcent : V ≤ centralizer (P : Set G) := by
    rw [← heq]
    exact sup_le (zpowers_le.2 hzc) (zpowers_le.2 hyc)
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  have hcomm : g * h = h * g → (h ∈ V ↔ g * h * g⁻¹ ∈ V) := by
    intro hgh
    rw [hgh, mul_inv_cancel_right]
  constructor
  · intro hh
    have hgh : g * h = h * g := (mem_centralizer_iff.1 (hVcent hh) g hg)
    exact (hcomm hgh).1 hh
  · intro hh
    have hh' : g * h * g⁻¹ ∈ centralizer (P : Set G) := hVcent hh
    have hgh : g * h = h * g := by
      have h1 := mem_centralizer_iff.1 hh' g hg
      have : g * (g * h * g⁻¹) * g⁻¹ = g * h * g⁻¹ := by
        rw [h1, mul_assoc, mul_inv_cancel, mul_one]
      have h2 : g * h * g⁻¹ = h := by
        have := congrArg (fun x => g⁻¹ * x * g) this
        simpa [mul_assoc] using this
      calc g * h = (g * h * g⁻¹) * g := by group
        _ = h * g := by rw [h2]
    exact (hcomm hgh).2 hh

theorem not_elemAbelian_cube_le_normalizer_of_isIsolatedPlane [Finite G] {p : ℕ} (hp : p.Prime)
    {P V E : Subgroup G} (hP : IsPGroup p P) (hV : IsIsolatedPlane p P V)
    (hEN : E ≤ P ⊓ normalizer (V : Set G)) (hE : CFSG.IsElementaryAbelian p E)
    (hEc : Nat.card E = p ^ 3) : False := by
  obtain ⟨hVP, hVe, hVc, hiso⟩ := hV
  have hp1 := hp.one_lt
  have hNp : IsPGroup p ↥(P ⊓ normalizer (V : Set G)) := hP.to_le inf_le_left
  have hVN : V ≤ P ⊓ normalizer (V : Set G) := le_inf hVP le_normalizer
  obtain ⟨-, hbig⟩ := normalPlane_concrete hp hNp hVN inf_le_right hVe hVc hEN hE hEc
  have : CFSG.IsElementaryAbelian p V := hVe
  have : CFSG.IsElementaryAbelian p ↥(E ⊓ centralizer (V : Set G)) :=
    isElementaryAbelian_of_le inf_le_left hE
  have hle : V ≤ centralizer ((E ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
    intro v hv
    exact mem_centralizer_iff.2 fun x hx => (mem_centralizer_iff.1 hx.2 v hv).symm
  have hF : CFSG.IsElementaryAbelian p ↥((E ⊓ centralizer (V : Set G)) ⊔ V) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer hle
  have hFP : (E ⊓ centralizer (V : Set G)) ⊔ V ≤ P :=
    sup_le (inf_le_left.trans (hEN.trans inf_le_left)) hVP
  have hbound := hiso _ hFP hF le_sup_right
  have : p ^ 3 ≤ p ^ 2 := hbig.trans hbound
  have := (Nat.pow_le_pow_iff_right hp1).1 this
  omega

theorem isIsolatedPlane_of_pRank_le_two [Finite G] {p : ℕ} (hp : p.Prime) {P D : Subgroup G}
    (hDP : D ≤ P) (hD : CFSG.Open.IsElemAbelian p D) (hDc : Nat.card D = p ^ 2)
    (hrank : CFSG.Open.pRank p (D ⊔ (P ⊓ centralizer (D : Set G))) ≤ 2) :
    IsIsolatedPlane p P D := by
  refine ⟨hDP, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p D).2 hD, hDc, ?_⟩
  intro E hEP hE hDE
  have hE' : CFSG.Open.IsElemAbelian p E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).1 hE
  have hEc : E ≤ D ⊔ (P ⊓ centralizer (D : Set G)) := by
    refine le_sup_of_le_right (le_inf hEP ?_)
    intro x hx
    refine mem_centralizer_iff.2 fun d hd => ?_
    have := hE'.1.is_comm.comm ⟨d, hDE hd⟩ ⟨x, hx⟩
    exact congrArg Subtype.val this
  have hfact : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ :=
    (CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p E hE').exists_card_eq
  have hkle : k ≤ CFSG.Open.pRank p (D ⊔ (P ⊓ centralizer (D : Set G))) := by
    unfold CFSG.Open.pRank
    exact le_csSup (CFSG.RankThreeCoreUniqueness.Helpers.pRank_set_bddAbove p hp.one_lt _)
      ⟨E, hEc, hE', hk⟩
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos (hkle.trans hrank)

end CFSG.LocalAnalysis.RankThreeTheoremC
