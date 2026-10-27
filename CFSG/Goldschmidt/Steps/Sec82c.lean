module

public import CFSG.Goldschmidt.Steps.Sec82a
import CFSG.Goldschmidt.Steps.Sec82Tools
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.G73Basic
import CFSG.Goldschmidt.Steps.AxB
import CFSG.Walter.Bender1970.S4.ComponentTools
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom

public section

namespace CFSG.Goldschmidt.Sec82

open CFSG.Open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G} {a : G}
  {H : Subgroup G} {p : ℕ} {M L : Subgroup G}

theorem fittingSubgroupOf_le_centralizer (c : Ctx S A a H p M L) :
    CFSG.fittingSubgroupOf M ≤ Subgroup.centralizer (L : Set G) :=
  (Walter.fittingSubgroupOf_le_centralizer_layer M).trans
    (Subgroup.centralizer_le (Walter.le_componentLayerOf_of_isComponentOf c.hL))

theorem fittingSubgroupOf_le_centralizer_A (c : Ctx S A a H p M L) :
    CFSG.fittingSubgroupOf M ≤ Subgroup.centralizer (A : Set G) :=
  (fittingSubgroupOf_le_centralizer c).trans (Subgroup.centralizer_le c.hAL)

theorem le_centralizer_qCoreOf_of_coprime (c : Ctx S A a H p M L) {X : Subgroup G}
    (hXA : X ≤ Subgroup.centralizer (A : Set G)) (hXH : X ≤ H)
    (hMX : M ≤ Subgroup.normalizer (X : Set G)) (hcop : Nat.Coprime (Nat.card X) p) :
    X ≤ Subgroup.centralizer (qCoreOf H p : Set G) := by
  have : Fact p.Prime := ⟨c.hp⟩
  set P := qCoreOf H p ⊓ Subgroup.centralizer (A : Set G) with hP
  have hHO := le_normalizer_of_isNormalIn (qCoreOf_normal_in H p)
  have hXP : X ≤ Subgroup.normalizer (P : Set G) := fun x hx =>
    Sec8.mem_normalizer_inf (hHO (hXH hx)) (Subgroup.le_normalizer (hXA hx))
  set N₀ := qCoreOf H p ⊓ Subgroup.normalizer (P : Set G) with hN₀
  have hXN₀ : X ≤ Subgroup.normalizer (N₀ : Set G) := fun x hx =>
    Sec8.mem_normalizer_inf (hHO (hXH hx)) (Subgroup.le_normalizer (hXP hx))
  have hN₀X : N₀ ≤ Subgroup.normalizer (X : Set G) := (inf_le_right.trans c.hPM).trans hMX
  have hpN₀ : IsPGroup p N₀ := (qCoreOf_isPGroup H p).to_le inf_le_left
  have hdisj : X ⊓ N₀ = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨k, hk⟩ := hpN₀ ⟨x, hx.2⟩
    have h1 : orderOf x ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf x ∣ Nat.card X := by
      have := orderOf_dvd_natCard (⟨x, hx.1⟩ : X)
      rwa [Subgroup.orderOf_mk] at this
    have h3 : Nat.Coprime (p ^ k) (Nat.card X) := Nat.Coprime.pow_left k hcop.symm
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h3 h1 h2))
  have hXC : X ≤ Subgroup.centralizer (N₀ : Set G) :=
    Sec82.le_centralizer_of_inf_eq_bot hXN₀ hN₀X hdisj
  have hPN₀ : P ≤ N₀ := le_inf inf_le_left Subgroup.le_normalizer
  have hfix : qCoreOf H p ⊓ Subgroup.centralizer (P : Set G) ≤
      Subgroup.centralizer (X : Set G) :=
    (le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))).trans
      (Subgroup.le_centralizer_iff.mp hXC)
  have h := N10 G (qCoreOf H p) X P (qCoreOf_isPGroup H p) hcop
    ((qCoreOf_isPGroup H p).to_le inf_le_left) (hXH.trans hHO) (inf_le_left.trans
      Subgroup.le_normalizer) (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hXC.trans (Subgroup.centralizer_le hPN₀))) hfix
  exact Subgroup.le_centralizer_iff.mp h

theorem le_centralizer_qCoreOf_of_ne (c : Ctx S A a H p M L) {X : Subgroup G} (hXH : X ≤ H)
    (hMX : M ≤ Subgroup.normalizer (X : Set G)) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hdisj : X ⊓ qCoreOf H q = ⊥) : X ≤ Subgroup.centralizer (qCoreOf H q : Set G) :=
  Sec82.le_centralizer_of_inf_eq_bot
    (hXH.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in H q)))
    (((qCoreOf_centralizer_of_ne H c.hp hq (Ne.symm hqp)).trans c.hCOM).trans hMX) hdisj

theorem oddCoreOf_le_centralizer_of_qCoreOf (H : Subgroup G) {X : Subgroup G} (hXH : X ≤ H)
    (hX2 : IsPGroup 2 X)
    (hXq : ∀ q : ℕ, q.Prime → q ≠ 2 → X ≤ Subgroup.centralizer (qCoreOf H q : Set G)) :
    oddCoreOf H ≤ Subgroup.centralizer (X : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := oddCoreOf H with hO
  have hodd : Odd (Nat.card O) := Sec8.odd_card_oddCoreOf H
  have hOH : O ≤ H := Sec8.oddCoreOf_le H
  have hOn : (O.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mpr (Sec8.le_normalizer_oddCoreOf H)
  have hFO : CFSG.fittingSubgroupOf O ≤ CFSG.fittingSubgroupOf H :=
    Walter.fittingSubgroupOf_le_of_isSubnormal hOH hOn.isSubnormal
  have hF : CFSG.fittingSubgroupOf O ≤ Subgroup.centralizer (X : Set G) := by
    rw [(show CFSG.fittingSubgroupOf O = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf O)]
    refine iSup_le fun r => ?_
    have hr : r.1.1.Prime := Nat.prime_of_mem_primeFactors r.1.2
    have hr2 : r.1.1 ≠ 2 := by
      rintro h
      have hdvd : 2 ∣ Nat.card O := h ▸ Nat.dvd_of_mem_primeFactors r.1.2
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
    have h1 : qCoreOf O r.1.1 ≤ qCoreOf H r.1.1 :=
      Walter.le_qCoreOf_of_le_fittingSubgroupOf hr
        ((qCoreOf_le_fittingSubgroupOf O r.1.1 hr).trans hFO) (qCoreOf_isPGroup O r.1.1)
    exact h1.trans (Subgroup.le_centralizer_iff.mp (hXq _ hr hr2))
  have hcop : Nat.Coprime (Nat.card X) (Nat.card O) := by
    obtain ⟨k, hk⟩ := hX2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  exact Sec82.le_centralizer_of_coprime_of_fitting (G73.isSolvable_oddCoreOf H)
    (hXH.trans (Sec8.le_normalizer_oddCoreOf H)) hcop hF

theorem qCoreOf_two_eq_bot (c : Ctx S A a H p M L) : qCoreOf M 2 = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := qCoreOf M 2 with hR
  have hRA : R ≤ Subgroup.centralizer (A : Set G) :=
    (qCoreOf_le_fittingSubgroupOf M 2 Nat.prime_two).trans (fittingSubgroupOf_le_centralizer_A c)
  have hRH : R ≤ H := hRA.trans c.hCH
  have hMR : M ≤ Subgroup.normalizer (R : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in M 2)
  have hR2 : IsPGroup 2 R := qCoreOf_isPGroup M 2
  have hRq : ∀ q : ℕ, q.Prime → q ≠ 2 → R ≤ Subgroup.centralizer (qCoreOf H q : Set G) := by
    intro q hq hq2
    by_cases hqp : q = p
    · subst hqp
      obtain ⟨k, hk⟩ := hR2.exists_card_eq
      refine le_centralizer_qCoreOf_of_coprime c hRA hRH hMR ?_
      rw [hk]
      exact Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2))
    · have : Fact q.Prime := ⟨hq⟩
      exact le_centralizer_qCoreOf_of_ne c hRH hMR hq hqp
        (IsPGroup.disjoint_of_ne 2 q (Ne.symm hq2) _ _ hR2 (qCoreOf_isPGroup H q)).eq_bot
  have hOR := oddCoreOf_le_centralizer_of_qCoreOf H hRH hR2 hRq
  by_contra hR1
  have hNR : Subgroup.normalizer (R : Set G) = M :=
    normalizer_eq_of_nontrivial_normal_in_coatom c.hsimple c.hM (qCoreOf_le M 2) hR1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (qCoreOf_le M 2)).mpr hMR)
  have hOM : oddCoreOf H ≤ M := hNR ▸ hOR.trans (Subgroup.centralizer_le_normalizer _)
  have hHM : H ≤ M := c.hHO.le.trans (sup_le hOM c.hCM)
  exact c.hMH ((c.hHco.le_iff.mp hHM).resolve_left c.hM.1)

end CFSG.Goldschmidt.Sec82
