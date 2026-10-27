module

public import CFSG.Goldschmidt.Steps.Sec82a
import CFSG.Goldschmidt.Steps.Sec82c
import CFSG.Goldschmidt.Steps.Sec82d
import CFSG.Goldschmidt.Steps.Sec82Tools
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec84b
import CFSG.Goldschmidt.Steps.Sec81b
import CFSG.Walter.Bender1970.S3.CoreExchangeTools
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom

public section

namespace CFSG.Goldschmidt.Sec82

open CFSG.Open CFSG.GorensteinWalter

section Join

variable {G : Type*} [Group G]

theorem isElemAbelian_sup_zpowers {q : ℕ} (hq : q.Prime) {E : Subgroup G}
    (hEc : Nat.card E = q ^ 2) (hEq : ∀ e ∈ E, e ^ q = 1) {z : G} (hzq : z ^ q = 1)
    (hzE : z ∉ E) (hz : ∀ e ∈ E, e * z = z * e) :
    IsElemAbelian q (E ⊔ Subgroup.zpowers z) ∧
      Nat.card (E ⊔ Subgroup.zpowers z : Subgroup G) = q ^ 3 := by
  have : Fact q.Prime := ⟨hq⟩
  have hz1 : z ≠ 1 := fun h => hzE (h ▸ E.one_mem)
  have hord : orderOf z = q := orderOf_eq_prime hzq hz1
  have hcardz : Nat.card (Subgroup.zpowers z) = q := by rw [Nat.card_zpowers, hord]
  have hnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer (E : Set G) (Subgroup.mem_centralizer_iff.mpr hz)
  have hdisj : Disjoint E (Subgroup.zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro x hxE hxz
    have : Fact (Nat.card (Subgroup.zpowers z)).Prime := ⟨by rw [hcardz]; exact hq⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (E.subgroupOf (Subgroup.zpowers z)) with h | h
    · have hx : (⟨x, hxz⟩ : Subgroup.zpowers z) ∈ E.subgroupOf (Subgroup.zpowers z) := hxE
      rw [h] at hx
      exact congrArg Subtype.val (Subgroup.mem_bot.1 hx)
    · exfalso
      have hf : (⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) ∈
          E.subgroupOf (Subgroup.zpowers z) := by
        rw [h]
        trivial
      exact hzE hf
  have hcard := card_sup_eq_mul_of_disjoint_of_le_normalizer E (Subgroup.zpowers z) hnorm hdisj
  have hEab := IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := E) hEc
  have hdec : ∀ x ∈ E ⊔ Subgroup.zpowers z, ∃ e ∈ E, ∃ k : ℤ, x = e * z ^ k := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left E _ hnorm] at hx
    obtain ⟨e, he, y, hy, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨e, he, k, rfl⟩
  have hcomm : ∀ e ∈ E, ∀ k : ℤ, Commute e (z ^ k) := fun e he k =>
    Commute.zpow_right (hz e he) k
  refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, by rw [hcard, hEc, hcardz]; ring⟩
  · obtain ⟨e₁, he₁, k₁, h₁⟩ := hdec x x.2
    obtain ⟨e₂, he₂, k₂, h₂⟩ := hdec y y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [h₁, h₂]
    have h12 : e₁ * e₂ = e₂ * e₁ :=
      congrArg Subtype.val (hEab.is_comm.comm (⟨e₁, he₁⟩ : E) ⟨e₂, he₂⟩)
    calc e₁ * z ^ k₁ * (e₂ * z ^ k₂) = e₁ * (z ^ k₁ * e₂) * z ^ k₂ := by group
      _ = e₁ * (e₂ * z ^ k₁) * z ^ k₂ := by rw [(hcomm e₂ he₂ k₁).eq]
      _ = (e₁ * e₂) * (z ^ k₁ * z ^ k₂) := by group
      _ = (e₂ * e₁) * (z ^ k₂ * z ^ k₁) := by rw [h12, ← zpow_add, ← zpow_add, add_comm]
      _ = e₂ * (e₁ * z ^ k₂) * z ^ k₁ := by group
      _ = e₂ * (z ^ k₂ * e₁) * z ^ k₁ := by rw [(hcomm e₁ he₁ k₂).eq]
      _ = e₂ * z ^ k₂ * (e₁ * z ^ k₁) := by group
  · obtain ⟨e, he, k, rfl⟩ := hdec x hx
    rw [(hcomm e he k).mul_pow, hEq e he, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hzq, one_zpow]

end Join

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G} {a : G}
  {H : Subgroup G} {p : ℕ} {M L : Subgroup G}

theorem qCoreOf_le_oddCoreOf (c : Ctx S A a H p M L) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    qCoreOf M q ≤ oddCoreOf H := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨-, hQH, hMQ, -⟩ := qCoreOf_facts c hq
  have hQodd : Odd (Nat.card (qCoreOf M q)) := by
    obtain ⟨k, hk⟩ := (qCoreOf_isPGroup M q).exists_card_eq
    rw [hk]
    exact (hq.odd_of_ne_two hq2).pow
  have hQON : qCoreOf M q ≤ Subgroup.normalizer (oddCoreOf H : Set G) :=
    hQH.trans (Sec8.le_normalizer_oddCoreOf H)
  have hodd := odd_card_sup_of_le_normalizer hQON hQodd (Sec8.odd_card_oddCoreOf H)
  have hNH : qCoreOf M q ⊔ oddCoreOf H ≤ H := sup_le hQH (Sec8.oddCoreOf_le H)
  have hHN : H ≤ Subgroup.normalizer ((qCoreOf M q ⊔ oddCoreOf H : Subgroup G) : Set G) := by
    refine c.hHO.le.trans (sup_le (le_sup_right.trans Subgroup.le_normalizer) fun x hx => ?_)
    exact Sec8.mem_normalizer_sup (hMQ (c.hCM hx)) (Sec8.le_normalizer_oddCoreOf H (c.hCH hx))
  exact le_sup_left.trans (Sec8.le_oddCoreOf hNH hHN hodd)

theorem qCoreOf_le_centralizer_qCoreOf (c : Ctx S A a H p M L) {q r : ℕ} (hq : q.Prime)
    (hr : r.Prime) (hrq : r ≠ q) :
    qCoreOf M q ≤ Subgroup.centralizer (qCoreOf H r : Set G) := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hQA, hQH, hMQ, -⟩ := qCoreOf_facts c hq
  by_cases hrp : r = p
  · rw [hrp]
    refine le_centralizer_qCoreOf_of_coprime c hQA hQH hMQ ?_
    obtain ⟨k, hk⟩ := (qCoreOf_isPGroup M q).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.coprime_primes hq c.hp).mpr fun h => hrq (hrp.trans h.symm))
  · exact le_centralizer_qCoreOf_of_ne c hQH hMQ hr hrp
      (IsPGroup.disjoint_of_ne q r (Ne.symm hrq) _ _ (qCoreOf_isPGroup M q)
        (qCoreOf_isPGroup H r)).eq_bot

theorem isCyclic_qCoreOf_of_le_two (h312 : S_G312) (hE : componentLayerOf H = ⊥)
    (c : Ctx S A a H p M L) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hR2 : CFSG.Open.pRank q (qCoreOf H q) ≤ 2) : IsCyclic (qCoreOf M q) := by
  have : Fact q.Prime := ⟨hq⟩
  set Q := qCoreOf M q with hQ
  set R := qCoreOf H q with hR
  obtain ⟨-, hQH, -, hLQ⟩ := qCoreOf_facts c hq
  have hQp : IsPGroup q Q := qCoreOf_isPGroup M q
  have hRp : IsPGroup q R := qCoreOf_isPGroup H q
  have hQres : Q ≤ Subgroup.centralizer
      (pResidualOf (generalizedFittingSubgroupOf H) q : Set G) := by
    have h1 := Walter.pResidualOf_generalizedFitting_le H hq
    rw [hE, sup_bot_eq] at h1
    refine Subgroup.le_centralizer_iff.mp (h1.trans (sSup_le ?_))
    rintro _ ⟨r, hr, hrq, rfl⟩
    exact Subgroup.le_centralizer_iff.mp (qCoreOf_le_centralizer_qCoreOf c hq hr hrq)
  obtain ⟨-, hsyl⟩ := h312 G H A (Sec8.sstar_of_mem_benderM c.hset c.h4 c.ha c.hH) q hq hq2 hR2
  have hQX : Q ≤ (normalClosureIn H A ⊔ oddCoreOf H) ⊓
      Subgroup.centralizer (pResidualOf (generalizedFittingSubgroupOf H) q : Set G) :=
    le_inf ((qCoreOf_le_oddCoreOf c hq hq2).trans le_sup_right) hQres
  have hQR : Q ≤ Subgroup.normalizer (R : Set G) :=
    hQH.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in H q))
  have hQRle : Q ≤ R := by
    have hT : IsPGroup q (Q ⊔ R : Subgroup G) := IsPGroup.to_sup_of_normal_right' hQp hRp hQR
    have heq : Q ⊔ R = R := hsyl.2.2 (Q ⊔ R) (sup_le hQX hsyl.1) hT le_sup_right
    calc Q ≤ Q ⊔ R := le_sup_left
      _ = R := heq
  by_contra hQc
  obtain ⟨E, hEQ, hEq, hEc⟩ := Sec8.exists_plane hq hq2 hQp hQc
  have hEq' : ∀ e ∈ E, e ^ q = 1 := fun e he => by
    simpa using congrArg Subtype.val (hEq ⟨e, he⟩)
  let W : Subgroup G :=
    { carrier := {z | z ∈ R ⊓ Subgroup.centralizer (R : Set G) ∧ z ^ q = 1}
      mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1, by
        rw [Commute.mul_pow (Subgroup.mem_centralizer_iff.mp hx.1.2 y hy.1.1).symm, hx.2, hy.2,
          one_mul]⟩
      one_mem' := ⟨Subgroup.one_mem _, one_pow q⟩
      inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hWE : W ≤ E := by
    intro z hz
    by_contra hzE
    have hzc : ∀ e ∈ E, e * z = z * e := fun e he =>
      Subgroup.mem_centralizer_iff.mp hz.1.2 e (hQRle (hEQ he))
    obtain ⟨hFel, hFc⟩ := isElemAbelian_sup_zpowers hq hEc hEq' hz.2 hzE hzc
    have hFR : E ⊔ Subgroup.zpowers z ≤ R :=
      sup_le (hEQ.trans hQRle) (Subgroup.zpowers_le.mpr hz.1.1)
    have h3 := CFSG.SectionRank.le_pRank hq.one_lt hFR hFel hFc
    omega
  have hQ1 : Q ≠ ⊥ := Sec8.ne_bot_of_not_isCyclic hQc
  have hR1 : R ≠ ⊥ := fun h => hQ1 (le_bot_iff.mp (h ▸ hQRle))
  have hW1 : W ≠ ⊥ := by
    have hZ1 := Sec8.qCoreOf_inf_centralizer_ne_bot hq hR1
    obtain ⟨k, hk⟩ := (hRp.to_le (inf_le_left : R ⊓ Subgroup.centralizer (R : Set G) ≤ R)
      ).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hZ1 (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
    have hdvd : q ∣ Nat.card (R ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) := by
      rw [hk]
      exact dvd_pow_self q hk0
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(R ⊓ Subgroup.centralizer (R : Set G))) q hdvd
    intro hWb
    have hzq : (z : G) ^ q = 1 := by
      rw [← Subgroup.orderOf_coe] at hz
      rw [← hz, pow_orderOf_eq_one]
    have hzW : (z : G) ∈ W := ⟨z.2, hzq⟩
    rw [hWb, Subgroup.mem_bot] at hzW
    have hz1 : z = 1 := Subtype.ext hzW
    rw [hz1, orderOf_one] at hz
    exact hq.one_lt.ne hz
  have hWH : W ≤ H := fun z hz => qCoreOf_le H q hz.1.1
  have hHR := le_normalizer_of_isNormalIn (qCoreOf_normal_in H q)
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := by
    intro h hh
    refine Sec82.mem_normalizer_of_conj_mem fun z hz => ⟨⟨?_, ?_⟩, ?_⟩
    · exact (qCoreOf_normal_in H q).2 h hh z hz.1.1
    · exact (Subgroup.mem_normalizer_iff.mp
        (Sec8.normalizer_le_normalizer_centralizer R (hHR hh)) z).mp hz.1.2
    · rw [conj_pow, hz.2, mul_one, mul_inv_cancel]
  have hNW : Subgroup.normalizer (W : Set G) = H :=
    normalizer_eq_of_nontrivial_normal_in_coatom c.hsimple c.hHco hWH hW1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hWH).mpr hHW)
  exact c.hLH (hNW ▸ (hLQ.trans (Subgroup.centralizer_le (hWE.trans hEQ))).trans
    (Subgroup.centralizer_le_normalizer _))

end CFSG.Goldschmidt.Sec82
