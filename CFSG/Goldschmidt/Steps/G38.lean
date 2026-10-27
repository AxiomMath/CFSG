module

public import CFSG.Goldschmidt.Steps.G38Comp
public import CFSG.Goldschmidt.Steps.G37Transport
import CFSG.Goldschmidt.Steps.AxB
import CFSG.Goldschmidt.Steps.Completion

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.GorensteinWalter

namespace G38

variable {G : Type} [Group G] [Finite G]

theorem four_le_card_of_not_isCyclic {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hnc : ¬ IsCyclic B) : 4 ≤ Nat.card B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBp : IsPGroup 2 B := fun x => ⟨1, Subtype.ext (by simpa using hB.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hBp.exists_card_eq
  rcases k with _ | _ | k
  · exfalso
    apply hnc
    have : Subsingleton B := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
    infer_instance
  · exfalso
    exact hnc (isCyclic_of_prime_card (by simpa using hk))
  · rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem commute_of_qCore {H Y V : Subgroup G} {a : G} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hY : IsNormalIn Y H) (hYq : IsPGroup q Y)
    (hV : V ≤ qCoreOf (H ⊓ Subgroup.centralizer ({a} : Set G)) p) :
    Y ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  set Q := qCoreOf (H ⊓ Subgroup.centralizer ({a} : Set G)) p with hQ
  have hQn : IsNormalIn Q (H ⊓ Subgroup.centralizer ({a} : Set G)) := qCoreOf_normal_in _ p
  have hQH : Q ≤ H := hQn.1.trans inf_le_left
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvQ := hV hv
  have hyC : y ∈ H ⊓ Subgroup.centralizer ({a} : Set G) := ⟨hY.1 hy.1, hy.2⟩
  have h1 : y * v * y⁻¹ * v⁻¹ ∈ Q := Q.mul_mem (hQn.2 y hyC v hvQ) (Q.inv_mem hvQ)
  have h2 : y * v * y⁻¹ * v⁻¹ ∈ Y := by
    have : v * y⁻¹ * v⁻¹ ∈ Y := hY.2 v (hQH hvQ) _ (Y.inv_mem hy.1)
    simpa [mul_assoc] using Y.mul_mem hy.1 this
  have hdisj : Disjoint Y Q :=
    IsPGroup.disjoint_of_ne q p hpq.symm Y Q hYq (qCoreOf_isPGroup _ p)
  have h3 : y * v * y⁻¹ * v⁻¹ = 1 := by
    have := Subgroup.disjoint_def.mp hdisj h2 h1
    exact this
  calc v * y = (y * v * y⁻¹ * v⁻¹)⁻¹ * (y * v) := by group
    _ = y * v := by rw [h3, inv_one, one_mul]

theorem eq_bot_of_qCoreOf_eq_bot
    (h37 : S_G37) (h31 : S_G31) {H A A₀ V : Subgroup G}
    (hS : IsSStarIn H A) (hA : IsElemAbelian 2 A) (hA₀A : A₀ ≤ A) (hA₀ : ¬ IsCyclic A₀)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hP : qCoreOf H p = ⊥)
    (hV : ∀ a ∈ A₀, a ≠ 1 → V ≤ qCoreOf (H ⊓ Subgroup.centralizer ({a} : Set G)) p) :
    V = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hA₀el : IsElemAbelian 2 A₀ := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => hA.2 x (hA₀A hx)⟩
    have := hA.1.is_comm.comm (⟨x, hA₀A x.2⟩ : A) ⟨y, hA₀A y.2⟩
    exact congrArg (fun z : A => (z : G)) this
  have h4 := four_le_card_of_not_isCyclic hA₀el hA₀
  have hAH : A ≤ H := hS.1
  obtain ⟨a₀, ha₀, ha₀1⟩ : ∃ a ∈ A₀, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card A₀ = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun x y => Subtype.ext ((hcon x x.2).trans (hcon y y.2).symm)⟩, ⟨1⟩⟩
    omega
  have hVQ := hV a₀ ha₀ ha₀1
  have hVH : V ≤ H := hVQ.trans ((Subgroup.map_subtype_le _).trans inf_le_left)
  have hVp : IsPGroup p V := (qCoreOf_isPGroup _ p).to_le hVQ
  have hVa₀ : V ≤ Subgroup.centralizer ({a₀} : Set G) :=
    hVQ.trans ((Subgroup.map_subtype_le _).trans inf_le_right)
  have hq : ∀ q : ℕ, q.Prime → q ≠ p → qCoreOf H q ≤ Subgroup.centralizer (V : Set G) := by
    intro q hqp hqne
    have : Fact q.Prime := ⟨hqp⟩
    have hYn : IsNormalIn (qCoreOf H q) H := qCoreOf_normal_in H q
    have hYq : IsPGroup q (qCoreOf H q) := qCoreOf_isPGroup H q
    by_cases hq2 : q = 2
    ·
      subst hq2
      have hcop : Nat.Coprime (Nat.card V) 2 := by
        obtain ⟨k, hk⟩ := hVp.exists_card_eq
        rw [hk]
        exact Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
      have hB : IsPGroup 2 (Subgroup.zpowers a₀) := by
        refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, pow_one]
        exact orderOf_eq_prime (hA.2 a₀ (hA₀A ha₀)) ha₀1
      have hYN : H ≤ Subgroup.normalizer (qCoreOf H 2 : Set G) := le_normalizer_of_isNormalIn hYn
      refine N10 G (qCoreOf H 2) V (Subgroup.zpowers a₀) hYq hcop hB (hVH.trans hYN)
        ((Subgroup.zpowers_le.mpr (hAH (hA₀A ha₀))).trans hYN) ?_ ?_
      · rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff,
          Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro v hv
        exact Subgroup.mem_centralizer_singleton_iff.mp (hVa₀ hv)
      · intro y hy
        have hy' : y ∈ qCoreOf H 2 ⊓ Subgroup.centralizer ({a₀} : Set G) := by
          refine ⟨hy.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
          exact (Subgroup.mem_centralizer_iff.mp hy.2 a₀ (Subgroup.mem_zpowers a₀)).symm
        exact commute_of_qCore hp Nat.prime_two hp2 hYn hYq hVQ hy'
    ·
      have hYodd : Odd (Nat.card (qCoreOf H q)) := by
        obtain ⟨k, hk⟩ := hYq.exists_card_eq
        rw [hk]
        exact (hqp.odd_of_ne_two hq2).pow
      refine Completion.le_of_inf_centralizer_le hA₀el h4 hYodd
        ((hA₀A.trans hAH).trans (le_normalizer_of_isNormalIn hYn)) ?_
      intro a ha ha1
      exact commute_of_qCore hp hqp (Ne.symm hqne) hYn hYq (hV a ha ha1)
  have hF : generalizedFittingSubgroupOf H ≤ Subgroup.centralizer (V : Set G) := by
    refine sup_le ?_ ?_
    · rw [fittingSubgroupOf_eq_iSup_qCoreOf H]
      refine iSup_le fun q => ?_
      have hqp : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
      by_cases hqe : q.1.1 = p
      · rw [hqe, hP]
        exact bot_le
      · exact hq q.1.1 hqp hqe
    · refine sSup_le fun L hL => ?_
      exact Subgroup.le_centralizer_iff.mp
        (le_centralizer_of_isComponentOf h37 h31 hS hA hA₀A hA₀ hp hp2 hV hL)
  have hVF : V ≤ Subgroup.centralizer (generalizedFittingSubgroupOf H : Set G) :=
    Subgroup.le_centralizer_iff.mp hF
  have hle := CFSG.Walter.le_qCoreOf_of_centralizes H hp hVH hVp
    (by rw [hP]; intro x _; rw [Subgroup.mem_centralizer_iff]; intro y hy
        rw [SetLike.mem_coe, Subgroup.mem_bot] at hy; rw [hy, one_mul, mul_one])
    (hVF.trans (Subgroup.centralizer_le (pResidualOf_le _ p)))
  rw [hP] at hle
  exact le_bot_iff.mp hle

theorem qCoreOf_top_quotient_eq_bot (H : Subgroup G) {p : ℕ} (hp : p.Prime) :
    qCoreOf (⊤ : Subgroup (H ⧸ CFSG.pCore p H)) p = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set N := CFSG.pCore p H with hN
  set π := QuotientGroup.mk' N with hπ
  set X := qCoreOf (⊤ : Subgroup (H ⧸ N)) p with hX
  have hXn : IsNormalIn X ⊤ := qCoreOf_normal_in _ p
  have hXp : IsPGroup p X := qCoreOf_isPGroup _ p
  have hXN : X.Normal := ⟨fun x hx g => hXn.2 g (Subgroup.mem_top g) x hx⟩
  set M := X.comap π with hM
  have hMn : M.Normal := hXN.comap π
  have hMp : IsPGroup p M := by
    intro m
    obtain ⟨i, hi⟩ := hXp ⟨π m, m.2⟩
    have hi' : (m : H) ^ p ^ i ∈ N := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπ, map_pow]
      simpa using congrArg Subtype.val hi
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := p) (G := H)) ⟨_, hi'⟩
    refine ⟨i + j, Subtype.ext ?_⟩
    have hj' : ((m : H) ^ p ^ i) ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
    rw [Subgroup.coe_pow, pow_add, pow_mul, hj', Subgroup.coe_one]
  have hMN : M ≤ N := le_sSup ⟨hMn, hMp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective N x
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hMN hx

end G38

open G38 in
theorem G38_of
    (h37 : S_G37) (h31 : S_G31) : S_G38 := by
  intro G _ _ H A hS hA A₀ hA₀A hA₀ p hp hp2
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hAH : A ≤ H := hS.1
  have hA₀H : A₀ ≤ H := hA₀A.trans hAH
  set V := ⨅ a : {a : G // a ∈ A₀ ∧ a ≠ 1},
    qCoreOf (H ⊓ Subgroup.centralizer ({a.1} : Set G)) p with hVdef
  have hV : ∀ a ∈ A₀, a ≠ 1 → V ≤ qCoreOf (H ⊓ Subgroup.centralizer ({a} : Set G)) p :=
    fun a ha ha1 => iInf_le (fun a : {a : G // a ∈ A₀ ∧ a ≠ 1} =>
      qCoreOf (H ⊓ Subgroup.centralizer ({a.1} : Set G)) p) ⟨a, ha, ha1⟩
  obtain ⟨a₀, ha₀, ha₀1⟩ : ∃ a ∈ A₀, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hA₀
    refine ⟨⟨1, fun x => ⟨0, Subtype.ext ?_⟩⟩⟩
    simp [hcon x x.2]
  have hVH : V ≤ H := (hV a₀ ha₀ ha₀1).trans ((Subgroup.map_subtype_le _).trans inf_le_left)
  set N : Subgroup H := CFSG.pCore p H with hN
  have hNp : IsPGroup p N := CFSG.pCore_isPGroup
  have hNodd : Odd (Nat.card N) := by
    obtain ⟨k, hk⟩ := hNp.exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  set π := QuotientGroup.mk' N with hπ
  have hS' := SStarTransport.isSStarIn_quotient hS N hNodd
  have hĀ := SStarTransport.isElemAbelian_map (SStarTransport.isElemAbelian_subgroupOf hA H) π
  have hĀ₀A : (A₀.subgroupOf H).map π ≤ (A.subgroupOf H).map π :=
    Subgroup.map_mono fun x hx => hA₀A hx
  have hinj : ∀ x : H, (x : G) ∈ A₀ → π x = 1 → x = 1 := by
    intro x hx hπx
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπx
    obtain ⟨k, hk⟩ := hNp ⟨x, hπx⟩
    have h1 : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : x ^ 2 = 1 := Subtype.ext (by simpa using hA.2 x (hA₀A hx))
    have hcop : Nat.Coprime 2 (p ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1))
  have hĀ₀ : ¬ IsCyclic ((A₀.subgroupOf H).map π) := by
    intro hcyc
    let φ : A₀ →* (A₀.subgroupOf H).map π :=
      (π.comp (Subgroup.inclusion hA₀H)).codRestrict _ fun x => ⟨_, x.2, rfl⟩
    have hφ : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : π (Subgroup.inclusion hA₀H x) = 1 := congrArg Subtype.val hx
      have h2 := hinj _ x.2 h1
      exact Subtype.ext (by simpa using congrArg (fun z : H => (z : G)) h2)
    exact hA₀ (isCyclic_of_injective φ hφ)
  have hPbar := qCoreOf_top_quotient_eq_bot H hp
  have hVbar : ∀ ā ∈ (A₀.subgroupOf H).map π, ā ≠ 1 → (V.subgroupOf H).map π ≤
      qCoreOf ((⊤ : Subgroup (H ⧸ N)) ⊓ Subgroup.centralizer ({ā} : Set (H ⧸ N))) p := by
    rintro _ ⟨a', ha', rfl⟩ hā
    have ha1 : (a' : G) ≠ 1 := fun h => hā (by
      have : a' = 1 := Subtype.ext h
      rw [this, map_one])
    set Q := qCoreOf (H ⊓ Subgroup.centralizer ({(a' : G)} : Set G)) p with hQ
    have hQn : IsNormalIn Q (H ⊓ Subgroup.centralizer ({(a' : G)} : Set G)) :=
      qCoreOf_normal_in _ p
    have hQp : IsPGroup p Q := qCoreOf_isPGroup _ p
    have hQH : Q ≤ H := hQn.1.trans inf_le_left
    have hVQ : V.subgroupOf H ≤ Q.subgroupOf H := fun x hx => hV _ ha' ha1 hx
    refine (Subgroup.map_mono (f := π) hVQ).trans ?_
    refine le_qCoreOf_of_isNormalIn_pGroup (G := H ⧸ N) _ _ p hp ?_ ⟨?_, ?_⟩ ?_
    · rintro _ ⟨q, hq, rfl⟩
      refine ⟨Subgroup.mem_top _, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hqa : (q : G) * a' = a' * q :=
        Subgroup.mem_centralizer_singleton_iff.mp (hQn.1 (Subgroup.mem_subgroupOf.mp hq)).2
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hqa
    · rintro _ ⟨q, hq, rfl⟩
      refine ⟨Subgroup.mem_top _, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hqa : (q : G) * a' = a' * q :=
        Subgroup.mem_centralizer_singleton_iff.mp (hQn.1 (Subgroup.mem_subgroupOf.mp hq)).2
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hqa
    ·
      intro x hx y hy
      have : Fact (IsPGroup 2 (Subgroup.zpowers a')) := ⟨by
        refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, pow_one]
        refine orderOf_eq_prime ?_ (fun h => ha1 (congrArg Subtype.val h))
        exact Subtype.ext (by simpa using hA.2 a' (hA₀A ha'))⟩
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hcen := CFSG.centralizer_map_quotient_eq_map_centralizer 2 (Subgroup.zpowers a') N
        inferInstance (Nat.coprime_two_left.mpr hNodd)
      have hxC : x ∈ Subgroup.centralizer
          (((Subgroup.zpowers a').map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) :
            Set (H ⧸ N)) := by
        rw [MonoidHom.map_zpowers, Subgroup.mem_centralizer_iff]
        intro z hz
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        have hxa := Subgroup.mem_centralizer_singleton_iff.mp hx.2
        exact ((Commute.zpow_left hxa.symm k)).eq
      rw [hcen] at hxC
      obtain ⟨h, hh, rfl⟩ := hxC
      obtain ⟨q, hq, rfl⟩ := hy
      refine ⟨h * q * h⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      have hhC : (h : G) ∈ H ⊓ Subgroup.centralizer ({(a' : G)} : Set G) := by
        refine ⟨h.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have := Subgroup.mem_centralizer_iff.mp hh a' (Subgroup.mem_zpowers a')
        exact (congrArg Subtype.val this).symm
      show h * q * h⁻¹ ∈ Q.subgroupOf H
      rw [Subgroup.mem_subgroupOf]
      simpa using hQn.2 _ hhC _ (Subgroup.mem_subgroupOf.mp hq)
    · exact (hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm).map π
  have hbot := eq_bot_of_qCoreOf_eq_bot h37 h31 hS' hĀ hĀ₀A hĀ₀ hp hp2 hPbar hVbar
  intro v hv
  have hvH := hVH hv
  have hπv : π ⟨v, hvH⟩ = 1 := by
    have : π ⟨v, hvH⟩ ∈ (V.subgroupOf H).map π := ⟨⟨v, hvH⟩, hv, rfl⟩
    rw [hbot] at this
    exact this
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπv
  exact ⟨⟨v, hvH⟩, hπv, rfl⟩

end CFSG.Goldschmidt
