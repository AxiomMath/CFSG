module

public import CFSG.Goldschmidt.StatementsG2
public import CFSG.Walter.Bender1970.S3.CoreExchangeTools
import CFSG.Goldschmidt.Steps.G53Tools
import CFSG.Goldschmidt.Steps.G62Basic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.Walter.Bender1970.S3.CoreExchangeRank
public import CFSG.Goldschmidt.StatementsG

public section

namespace CFSG.Goldschmidt.G63

open CFSG.GorensteinWalter hiding oddCoreOf
open CFSG.Walter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isNormalIn_of_le_normalizer {K H : Subgroup G} (hKH : K ≤ H)
    (hN : H ≤ Subgroup.normalizer (K : Set G)) : IsNormalIn K H :=
  ⟨hKH, fun _ hh k hk => (Subgroup.mem_normalizer_iff.mp (hN hh) k).mp hk⟩

omit [Finite G] in
theorem fstarZero_isNormalIn (H : Subgroup G) : IsNormalIn (fstarZero H) H :=
  isNormalIn_of_le_normalizer ((G62.fstarZero_le H).trans (generalizedFittingSubgroupOf_le H))
    (G62.le_normalizer_fstarZero H)

theorem qCoreOf_fstarZero_isNormalIn (H : Subgroup G) (p : ℕ) :
    IsNormalIn (qCoreOf (fstarZero H) p) H :=
  map_characteristic_isNormalIn_of_isNormalIn (pCore p (fstarZero H)) inferInstance
    (fstarZero_isNormalIn H)

theorem qCoreOf_fstarZero_le (H : Subgroup G) (p : ℕ) :
    qCoreOf (fstarZero H) p ≤ qCoreOf H p :=
  le_qCoreOf_of_normal_isPGroup H _ p (qCoreOf_fstarZero_isNormalIn H p).1
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (qCoreOf_fstarZero_isNormalIn H p).1).mpr
      (le_normalizer_of_isNormalIn (qCoreOf_fstarZero_isNormalIn H p)))
    (qCoreOf_isPGroup _ p)

theorem inf_fstarZero_le_qCoreOf (H : Subgroup G) (p : ℕ) :
    qCoreOf H p ⊓ fstarZero H ≤ qCoreOf (fstarZero H) p := by
  refine le_qCoreOf_of_normal_isPGroup (fstarZero H) _ p inf_le_right
    ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun x hx =>
      mem_normalizer_inf
        (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p) ((fstarZero_isNormalIn H).1 hx))
        (Subgroup.le_normalizer hx)) ((qCoreOf_isPGroup H p).to_le inf_le_left)

@[expose] noncomputable def qCoreCompl (H : Subgroup G) (p : ℕ) : Subgroup G :=
  sSup {R | ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ R = qCoreOf H q}

theorem fitting_le_qCoreOf_sup (H : Subgroup G) (p : ℕ) :
    CFSG.fittingSubgroupOf H ≤ qCoreOf H p ⊔ qCoreCompl H p := by
  rw [(show CFSG.fittingSubgroupOf H = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf H)]
  refine iSup_le fun q => ?_
  by_cases hqp : q.1.1 = p
  · rw [hqp]
    exact le_sup_left
  · exact (le_sSup (s := {R | ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ R = qCoreOf H q})
      ⟨q.1.1, Nat.prime_of_mem_primeFactors q.1.2, hqp, rfl⟩).trans le_sup_right

theorem qCoreCompl_le_centralizer (H : Subgroup G) {p : ℕ} (hp : p.Prime) :
    qCoreCompl H p ≤ Subgroup.centralizer (qCoreOf H p : Set G) := by
  refine sSup_le ?_
  rintro _ ⟨q, hq, hqp, rfl⟩
  exact qCoreOf_centralizer_of_ne H hp hq (Ne.symm hqp)

omit [Finite G] in
theorem commutatorElement_mul_mul_of_commute {u₁ u₂ n₁ n₂ : G} (h₁₁ : Commute u₁ n₁)
    (h₁₂ : Commute u₁ n₂) (h₂₁ : Commute u₂ n₁) (h₂₂ : Commute u₂ n₂) :
    ⁅u₁ * n₁, u₂ * n₂⁆ = ⁅u₁, u₂⁆ * ⁅n₁, n₂⁆ := by
  set z := ⁅n₁, n₂⁆ with hz
  have h3 : Commute u₁ z := by
    rw [hz, commutatorElement_def]
    exact ((h₁₁.mul_right h₁₂).mul_right h₁₁.inv_right).mul_right h₁₂.inv_right
  have h4 : Commute u₂ z := by
    rw [hz, commutatorElement_def]
    exact ((h₂₁.mul_right h₂₂).mul_right h₂₁.inv_right).mul_right h₂₂.inv_right
  have k1 : n₁ * u₂ * n₁⁻¹ = u₂ := by rw [h₂₁.eq.symm]; group
  have k2 : n₁ * n₂ * n₁⁻¹ = z * n₂ := by rw [hz, commutatorElement_def]; group
  have k3 : u₁ * z * u₁⁻¹ = z := by rw [h3.eq]; group
  have k4 : u₁ * n₂ * u₁⁻¹ = n₂ := by rw [h₁₂.eq]; group
  have k5 : z * u₂⁻¹ = u₂⁻¹ * z := (h4.symm.inv_right).eq
  calc ⁅u₁ * n₁, u₂ * n₂⁆
      = u₁ * ((n₁ * u₂ * n₁⁻¹) * (n₁ * n₂ * n₁⁻¹)) * u₁⁻¹ * n₂⁻¹ * u₂⁻¹ := by
        rw [commutatorElement_def]; group
    _ = (u₁ * u₂ * u₁⁻¹) * (u₁ * z * u₁⁻¹) * (u₁ * n₂ * u₁⁻¹) * n₂⁻¹ * u₂⁻¹ := by
        rw [k1, k2]; group
    _ = (u₁ * u₂ * u₁⁻¹) * (z * u₂⁻¹) := by rw [k3, k4]; group
    _ = ⁅u₁, u₂⁆ * z := by rw [k5, commutatorElement_def]; group

theorem commutator_fitting_le_centralizer (H : Subgroup G) {p : ℕ} (hp : p.Prime)
    {X : Subgroup G} (hX : X ≤ qCoreOf H p)
    (hXc : ⁅qCoreOf H p, qCoreOf H p⁆ ≤ Subgroup.centralizer (X : Set G)) :
    ⁅CFSG.fittingSubgroupOf H, CFSG.fittingSubgroupOf H⁆ ≤
      Subgroup.centralizer (X : Set G) := by
  set P := qCoreOf H p with hPdef
  set N := qCoreCompl H p with hNdef
  have hNP : N ≤ Subgroup.centralizer (P : Set G) := qCoreCompl_le_centralizer H hp
  have hPN : P ≤ Subgroup.centralizer (N : Set G) := Subgroup.le_centralizer_iff.mp hNP
  have hNX : N ≤ Subgroup.centralizer (X : Set G) := hNP.trans (Subgroup.centralizer_le hX)
  have hFle := fitting_le_qCoreOf_sup H p
  have hPNN : P ≤ Subgroup.normalizer (N : Set G) :=
    hPN.trans (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.commutator_le]
  intro f₁ hf₁ f₂ hf₂
  obtain ⟨u₁, hu₁, n₁, hn₁, rfl⟩ := mem_sup_of_le_normalizer hPNN (hFle hf₁)
  obtain ⟨u₂, hu₂, n₂, hn₂, rfl⟩ := mem_sup_of_le_normalizer hPNN (hFle hf₂)
  have hc : ∀ u ∈ P, ∀ n ∈ N, Commute u n := fun u hu n hn =>
    (Subgroup.mem_centralizer_iff.mp (hNP hn)) u hu
  rw [commutatorElement_mul_mul_of_commute (hc u₁ hu₁ n₁ hn₁) (hc u₁ hu₁ n₂ hn₂)
    (hc u₂ hu₂ n₁ hn₁) (hc u₂ hu₂ n₂ hn₂)]
  refine Subgroup.mul_mem _ (hXc (Subgroup.commutator_mem_commutator hu₁ hu₂)) (hNX ?_)
  rw [commutatorElement_def]
  exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)

theorem le_qCoreOf_fstarZero (H : Subgroup G) {p : ℕ} (hp : p.Prime) {X : Subgroup G}
    (hX : X ≤ qCoreOf H p)
    (hXc : ⁅qCoreOf H p, qCoreOf H p⁆ ≤ Subgroup.centralizer (X : Set G)) :
    X ≤ qCoreOf (fstarZero H) p := by
  have hXF : X ≤ generalizedFittingSubgroupOf H :=
    hX.trans ((qCoreOf_le_fittingSubgroupOf H p hp).trans le_sup_left)
  have hXC : X ≤ Subgroup.centralizer
      ((⁅CFSG.fittingSubgroupOf H, CFSG.fittingSubgroupOf H⁆ : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp (commutator_fitting_le_centralizer H hp hX hXc)
  exact (le_inf hX ((le_inf hXF hXC).trans le_sup_right)).trans (inf_fstarZero_le_qCoreOf H p)

theorem center_qCoreOf_le_qCoreOf_fstarZero (H : Subgroup G) {p : ℕ} (hp : p.Prime) :
    qCoreOf H p ⊓ Subgroup.centralizer (qCoreOf H p : Set G) ≤ qCoreOf (fstarZero H) p :=
  le_qCoreOf_fstarZero H hp inf_le_left
    ((Bender35.commutator_self_le _).trans (Subgroup.le_centralizer_iff.mp inf_le_right))

theorem le_and_isSubnormal_of_le_qCoreOf {K X : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hX : X ≤ qCoreOf K p) : X ≤ K ∧ (X.subgroupOf K).IsSubnormal := by
  have : Fact p.Prime := ⟨hp⟩
  have hn := qCoreOf_normal_in K p
  refine ⟨hX.trans hn.1, isSubnormal_subgroupOf_trans hX ?_
    (isSubnormal_subgroupOf_of_isNormalIn hn)⟩
  exact isSubnormal_of_nilpotent (qCoreOf_isPGroup K p).isNilpotent _ hX

omit [Finite G] in
theorem isCyclic_of_le {H K : Subgroup G} (hK : IsCyclic K) (hHK : H ≤ K) : IsCyclic H := by
  have : IsCyclic (H.subgroupOf K) := Subgroup.isCyclic _
  exact (Subgroup.subgroupOfEquivOfLe hHK).isCyclic.mp this

theorem isCyclic_of_card_le {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hPp : IsPGroup p P)
    (hcard : Nat.card P ≤ p) : IsCyclic P := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hPp.exists_card_eq
  rcases Nat.lt_or_ge k 2 with h | h
  · interval_cases k
    · rw [pow_zero] at hk
      have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hk).1
      exact isCyclic_of_subsingleton
    · rw [pow_one] at hk
      exact isCyclic_of_prime_card hk
  · have : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos h
    have := hp.one_lt
    nlinarith [hk ▸ hcard]

theorem sup_zpowers_isElemAbelian {x z : G} {p : ℕ} (hp : p.Prime) (hxp : x ^ p = 1)
    (hzp : z ^ p = 1) (hz1 : z ≠ 1) (hxz : x ∉ Subgroup.zpowers z) (hcomm : x * z = z * x) :
    CFSG.Open.IsElemAbelian p (Subgroup.zpowers x ⊔ Subgroup.zpowers z) ∧
      Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers z : Subgroup G) = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hzo : orderOf z = p := orderOf_eq_prime hzp hz1
  have hx1 : x ≠ 1 := fun h => hxz (h ▸ Subgroup.one_mem _)
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxzc : Subgroup.zpowers x ≤
      Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq', Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  refine ⟨isElemAbelian_sup (isElemAbelian_zpowers hxp) (isElemAbelian_zpowers hzp) hxzc, ?_⟩
  have hdisj : Disjoint (Subgroup.zpowers z) (Subgroup.zpowers x) := by
    rw [disjoint_iff]
    set I := Subgroup.zpowers z ⊓ Subgroup.zpowers x with hI
    have hIz : I ≤ Subgroup.zpowers z := inf_le_left
    have hdvd : Nat.card I ∣ p := by
      rw [← hzo, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le hIz
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq I h
    · exfalso
      apply hxz
      have h1 : I = Subgroup.zpowers z :=
        Subgroup.eq_of_le_of_card_ge hIz (by rw [h, Nat.card_zpowers, hzo])
      have h2 : Subgroup.zpowers z ≤ Subgroup.zpowers x := h1 ▸ inf_le_right
      have h3 : Subgroup.zpowers z = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge h2 (by rw [Nat.card_zpowers, Nat.card_zpowers, hzo, hxo])
      rw [h3]
      exact Subgroup.mem_zpowers x
  rw [sup_comm, card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
    (hxzc.trans (Subgroup.centralizer_le_normalizer _)) hdisj, Nat.card_zpowers,
    Nat.card_zpowers, hzo, hxo, pow_two]

theorem exists_isElemAbelian_card_sq {Q : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQp : IsPGroup p Q) (hQ : ¬ IsCyclic Q) :
    ∃ E ≤ Q, CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  obtain ⟨X, hXQ, hXcyc, hXexp, -⟩ := exists_noncyclic_exponent_le hp hp2 hQp hQ
  obtain ⟨z, hzX, x, hxX, hz1, hzX', hxz, -, -, -⟩ :=
    exists_typePP hp hp2 (hQp.to_le hXQ) le_rfl Subgroup.le_normalizer hXexp hXcyc
      (mul_one (1 : G)) (Subgroup.one_mem _) (Subgroup.one_mem _)
  have hcomm : x * z = z * x := (Subgroup.mem_centralizer_iff.mp hzX') x hxX
  exact ⟨_, sup_le (Subgroup.zpowers_le.mpr (hXQ hxX)) (Subgroup.zpowers_le.mpr (hXQ hzX)),
    sup_zpowers_isElemAbelian hp (hXexp x hxX) (hXexp z hzX) hz1 hxz hcomm⟩

theorem two_le_rank_of_not_isCyclic {Q : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQp : IsPGroup p Q) (hQ : ¬ IsCyclic Q) : 2 ≤ rank Q := by
  obtain ⟨E, hEQ, hE, hcard⟩ := exists_isElemAbelian_card_sq hp hp2 hQp hQ
  exact le_rank hp hEQ hE hcard

omit [Finite G] in
theorem eq_of_isCoatom_of_le {H H₁ : Subgroup G} (hH : IsCoatom H) (hH₁ : IsCoatom H₁)
    (hle : H₁ ≤ H) : H₁ = H := by
  by_contra hne
  exact hH.1 (hH₁.2 H (lt_of_le_of_ne hle hne))

theorem normalizer_le_of_mem_goldA (hsimple : IsSimpleGroup G) {a : G} {H Y : Subgroup G}
    (hH : IsCoatom H) (hY : Y ∈ goldA a H)
    (hF : ∀ r : ℕ, r.Prime → ¬ IsPGroup r (generalizedFittingSubgroupOf H)) :
    Subgroup.normalizer (Y : Set G) ≤ H := by
  obtain ⟨B, hB, hNB⟩ := G53.exists_isCoatom_normalizer_le hsimple hH
    (hY.2.1.trans (generalizedFittingSubgroupOf_le H)) hY.1
  rcases hY.2.2.2.2 B hB hNB with rfl | ⟨r, hr, -, hHr⟩
  · exact hNB
  · exact absurd hHr (hF r hr)

theorem normalizer_le_of_uniqueness (hsimple : IsSimpleGroup G) {a : G} {H : Subgroup G}
    (hH : IsCoatom H) (hU : UniquenessA a H)
    (hF : ∀ r : ℕ, r.Prime → ¬ IsPGroup r (generalizedFittingSubgroupOf H)) {p : ℕ}
    (hp : p.Prime) {Y : Subgroup G} (hY : Y ≤ qCoreOf (fstarZero H) p) (hY1 : Y ≠ ⊥)
    (haY : a ∈ Subgroup.normalizer (Y : Set G)) : Subgroup.normalizer (Y : Set G) ≤ H :=
  let h := le_and_isSubnormal_of_le_qCoreOf hp hY
  normalizer_le_of_mem_goldA hsimple hH (hU Y hY1 h.1 h.2 haY) hF

section Setting

variable {S : Sylow 2 G} {A : Subgroup G}

theorem commute_of_mem (hG : GoldSetting G S A) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    a * b = b * a :=
  congrArg Subtype.val (hG.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem le_of_mem_benderM (hG : GoldSetting G S A) {a : G} (ha : a ∈ A) {H : Subgroup G}
    (hH : H ∈ benderM a) : A ≤ H := fun _ hb =>
  centralizer_le_of_mem_benderM hH
    (Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem hG hb ha))

theorem exists_sstar (hG : GoldSetting G S A) {H : Subgroup G} (hH : H ≠ ⊤) :
    ∃ A' : Subgroup G, IsSStarIn H A' ∧ CFSG.Open.IsElemAbelian 2 A' ∧ A ⊓ H ≤ A' := by
  obtain ⟨g, hg, hS⟩ := hG.sstar H hH
  exact ⟨conjSub g A ⊓ H, hS, G53.isElemAbelian_conjSub_inf hG.elem g H,
    le_inf hg inf_le_right⟩

theorem not_isPGroup_fstar (h62 : S_G62) (hG : GoldSetting G S A) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ benderM a) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hQ : qCoreOf H q ≠ ⊥) :
    ∀ r : ℕ, r.Prime → ¬ IsPGroup r (generalizedFittingSubgroupOf H) := by
  intro r hr hFr
  by_cases hr2 : r = 2
  · subst hr2
    have hQF : qCoreOf H q ≤ generalizedFittingSubgroupOf H :=
      (qCoreOf_le_fittingSubgroupOf H q hq).trans le_sup_left
    exact hq2 (eq_of_isPGroup_of_isPGroup hq Nat.prime_two (qCoreOf_isPGroup H q)
      (hFr.to_le hQF) hQ)
  · exact h62 G S A hG a ha ha1 H hH r hr hr2 hFr

theorem commutator_qCoreOf_eq_bot_of_mem_two {H : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {a : G} (ha : a ∈ qCoreOf H 2) :
    ⁅qCoreOf H p, Subgroup.zpowers a⁆ = ⊥ := by
  have haH : a ∈ H := (qCoreOf_normal_in H 2).1 ha
  have h1 : ⁅qCoreOf H p, Subgroup.zpowers a⁆ ≤ qCoreOf H p :=
    commutator_zpowers_le_of_mem_normalizer
      (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p) haH)
  have h2 : ⁅qCoreOf H p, Subgroup.zpowers a⁆ ≤ qCoreOf H 2 := by
    rw [Subgroup.commutator_le]
    intro u hu g hg
    have hg2 : g ∈ qCoreOf H 2 := (Subgroup.zpowers_le.mpr ha) hg
    rw [commutatorElement_def]
    exact (qCoreOf H 2).mul_mem
      ((qCoreOf_normal_in H 2).2 u ((qCoreOf_normal_in H p).1 hu) g hg2)
      ((qCoreOf H 2).inv_mem hg2)
  by_contra hne
  exact hp2 (eq_of_isPGroup_of_isPGroup hp Nat.prime_two ((qCoreOf_isPGroup H p).to_le h1)
    ((qCoreOf_isPGroup H 2).to_le h2) hne)

theorem uniquenessA_of (h51 : S_G51) (hG : GoldSetting G S A) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ benderM a) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hyp : ⁅qCoreOf H p, Subgroup.zpowers a⁆ ≠ ⊥ ∨ 3 ≤ CFSG.Open.pRank p (qCoreOf H p)) :
    UniquenessA a H := by
  rcases h51 G S A hG a ha ha1 H hH with h | ⟨ha2, hle⟩
  · exact h
  · exfalso
    rcases hyp with h | h
    · exact h (commutator_qCoreOf_eq_bot_of_mem_two hp hp2 ha2)
    · have := hle p hp hp2
      omega

theorem not_isCyclic_qCoreOf (h54 : S_G54) (h62 : S_G62) (hG : GoldSetting G S A) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ benderM a) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hyp : ⁅qCoreOf H p, Subgroup.zpowers a⁆ ≠ ⊥ ∨ 3 ≤ CFSG.Open.pRank p (qCoreOf H p)) :
    ¬ IsCyclic (qCoreOf H p) := by
  intro hcyc
  rcases hyp with h | h
  · have hcomm : IsMulCommutative (qCoreOf H p) := IsCyclic.isMulCommutative
    have hPC : qCoreOf H p ≤ Subgroup.centralizer (qCoreOf H p : Set G) := fun x hx => by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hcomm.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
    have heq : qCoreOf H p ⊓ Subgroup.centralizer (qCoreOf H p : Set G) = qCoreOf H p :=
      inf_eq_left.mpr hPC
    refine h62 G S A hG a ha ha1 H hH p hp hp2 (h54 G S A hG a ha ha1 H hH p hp hp2 h ?_ ?_)
    · rw [heq]
      exact inf_le_left
    · rw [heq]
      exact hcyc
  · exact not_isCyclic_of_two_le_rank hp (qCoreOf_isPGroup H p)
      (by rw [rank_eq_pRank_of_isPGroup hp (qCoreOf_isPGroup H p)]; omega) hcyc

end Setting

theorem le_normalClosureIn_sup_of_isPGroup (h37 : S_G37) {H A : Subgroup G}
    (hS : IsSStarIn H A) (hA : CFSG.Open.IsElemAbelian 2 A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G} (hXp : IsPGroup p X) (hXH : X ≤ H)
    (hXN : H ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    X ≤ normalClosureIn H A ⊔ oddCoreOf H := by
  obtain ⟨-, -, h3, -⟩ :=
    h37 G H A hS hA a ha ha1 X hXH hXN (G53.eq_layer_sup_oddFitting_of_isPGroup hp hp2 hXp)
  rwa [G53.oddFitting_eq_of_isPGroup hp hp2 hXp] at h3

omit [Finite G] in
theorem le_of_fusionIsSylowIn {P₁ K X : Subgroup G} {p : ℕ}
    (hS : CFSG.Open.fusionIsSylowIn p P₁ K) (hXK : X ≤ K) (hXp : IsPGroup p X)
    (hXN : X ≤ Subgroup.normalizer (P₁ : Set G)) : X ≤ P₁ :=
  le_sup_left.trans
    (hS.2.2 (X ⊔ P₁) (sup_le hXK hS.1) (hXp.to_sup_of_normal_right' hS.2.1 hXN) le_sup_right).le

theorem commutator_pResidual_eq_bot (M : Subgroup G) {p : ℕ} (hp : p.Prime) {X B : Subgroup G}
    (hBp : IsPGroup p B) (hXB : X ≤ B)
    (hRB : pResidualOf (generalizedFittingSubgroupOf M) p ≤ Subgroup.normalizer (B : Set G))
    (hXR : X ≤ Subgroup.normalizer
      (pResidualOf (generalizedFittingSubgroupOf M) p : Set G)) :
    ⁅pResidualOf (generalizedFittingSubgroupOf M) p, X⁆ = ⊥ := by
  set K := pResidualOf (generalizedFittingSubgroupOf M) p with hKdef
  have hKK : pResidualOf K p = K := pResidualOf_pResidualOf _ p hp
  have hKn : IsNormalIn K M := pResidualOf_generalizedFitting_isNormalIn M p
  have hKQ : K ≤ Subgroup.centralizer (qCoreOf M p : Set G) :=
    pResidualOf_generalizedFitting_le_centralizer M hp
  refine commutator_eq_bot_of_pResidual hp hKK hXR hRB hXB (hBp.to_le inf_le_right) ?_
  have hKBn : ((K ⊓ B).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun k hk =>
      mem_normalizer_inf (Subgroup.le_normalizer hk) (hRB hk)
  have h1 : K ⊓ B ≤ qCoreOf K p :=
    le_qCoreOf_of_normal_isPGroup K (K ⊓ B) p inf_le_left hKBn (hBp.to_le inf_le_right)
  have hOKn : IsNormalIn (qCoreOf K p) M :=
    map_characteristic_isNormalIn_of_isNormalIn (pCore p K) inferInstance hKn
  have h2 : qCoreOf K p ≤ qCoreOf M p :=
    le_qCoreOf_of_normal_isPGroup M (qCoreOf K p) p hOKn.1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hOKn.1).mpr
        (le_normalizer_of_isNormalIn hOKn)) (qCoreOf_isPGroup K p)
  exact (h1.trans h2).trans (Subgroup.le_centralizer_iff.mp hKQ)

end CFSG.Goldschmidt.G63
