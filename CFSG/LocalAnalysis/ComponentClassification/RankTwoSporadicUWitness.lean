module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPWitness
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCriterion
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement

variable {G W : Type*} [Group G] [Group W]

section Lift

theorem disp_mem_inf_centralizer {A : Subgroup G} {X : Subgroup W}
    {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A X ψ) (t : normalizer (A : Set G))
    {a : G} (ha : a ∈ A) (hc : ψ t * ψ ⟨a, le_normalizer ha⟩ = ψ ⟨a, le_normalizer ha⟩ * ψ t) :
    (t : G) * a * (t : G)⁻¹ * a⁻¹ ∈ A ⊓ centralizer (A : Set G) := by
  have hA' : (t : G) * a * (t : G)⁻¹ ∈ A := (mem_normalizer_iff.mp t.2 a).mp ha
  refine ⟨A.mul_mem hA' (A.inv_mem ha), ?_⟩
  have h1 : ψ (t * ⟨a, le_normalizer ha⟩ * t⁻¹ * (⟨a, le_normalizer ha⟩)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hc]
    group
  simpa using (hψ.eq_one_iff _).mp h1

theorem conj_commutator_eq_of_disp {A : Subgroup G} {t p q : G} (hp : p ∈ A) (hq : q ∈ A)
    (hzp : t * p * t⁻¹ * p⁻¹ ∈ A ⊓ centralizer (A : Set G))
    (hzq : t * q * t⁻¹ * q⁻¹ ∈ A ⊓ centralizer (A : Set G)) :
    t * ⁅p, q⁆ * t⁻¹ = ⁅p, q⁆ := by
  set zp := t * p * t⁻¹ * p⁻¹ with hzp'
  set zq := t * q * t⁻¹ * q⁻¹ with hzq'
  have hcomm : ∀ {z y : G}, z ∈ centralizer (A : Set G) → y ∈ A → Commute z y :=
    fun hz hy => (mem_centralizer_iff.mp hz _ hy).symm
  have e1 : t * p * t⁻¹ = zp * p := by rw [hzp']; group
  have e2 : t * q * t⁻¹ = zq * q := by rw [hzq']; group
  calc t * ⁅p, q⁆ * t⁻¹ = ⁅t * p * t⁻¹, t * q * t⁻¹⁆ := by
        simp only [commutatorElement_def]; group
    _ = ⁅zp * p, zq * q⁆ := by rw [e1, e2]
    _ = ⁅p, q⁆ := commutatorElement_mul_left_central (hcomm hzp.2 hp) (hcomm hzp.2 hq)
        (hcomm hzq.2 hp) (hcomm hzq.2 hq) (hcomm hzp.2 hzq.1)

theorem exists_lift_of_isPGroup [Finite G] [Finite W] {A : Subgroup G} {X : Subgroup W}
    {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A X ψ)
    (hZ : Odd (Nat.card ↥(A ⊓ centralizer (A : Set G)))) (t : normalizer (A : Set G)) {c : W}
    (hcX : c ∈ X) (hct : c * ψ t = ψ t * c) (hc2 : IsPGroup 2 (zpowers c)) :
    ∃ (a : G) (ha : a ∈ A), a * t = t * a ∧ ψ ⟨a, le_normalizer ha⟩ = c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha, rfl⟩ := hψ.exists_eq c hcX
  set z := (t : G) * a * (t : G)⁻¹ * a⁻¹ with hz
  have hzZ := disp_mem_inf_centralizer hψ t ha hct.symm
  have e1 : (t : G) * a * (t : G)⁻¹ = z * a := by rw [hz]; group
  have hpow : ∀ j : ℕ, (t : G) * a ^ j * (t : G)⁻¹ = z ^ j * a ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hza : a ^ j * z = z * a ^ j := mem_centralizer_iff.mp hzZ.2 _ (pow_mem ha j)
      calc (t : G) * a ^ (j + 1) * (t : G)⁻¹
          = ((t : G) * a ^ j * (t : G)⁻¹) * ((t : G) * a * (t : G)⁻¹) := by group
        _ = z ^ j * (a ^ j * z) * a := by rw [ih, e1]; group
        _ = z ^ j * (z * a ^ j) * a := by rw [hza]
        _ = z ^ (j + 1) * a ^ (j + 1) := by group
  have hzodd : Odd (orderOf z) := by
    have h := orderOf_dvd_natCard (⟨z, hzZ⟩ : ↥(A ⊓ centralizer (A : Set G)))
    rw [Subgroup.orderOf_mk] at h
    exact hZ.of_dvd_nat h
  set m := orderOf z
  have ham : a ^ m * t = t * a ^ m := by
    have h := hpow m
    rw [pow_orderOf_eq_one, one_mul] at h
    calc a ^ m * t = (t : G) * a ^ m * (t : G)⁻¹ * t := by rw [h]
      _ = t * a ^ m := by group
  set c := ψ ⟨a, le_normalizer ha⟩
  have hcm : c ∈ zpowers (c ^ m) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hc2) ⟨c, mem_zpowers c⟩
    have hord : orderOf c = 2 ^ k := by
      rw [← hk]
      exact Subgroup.orderOf_coe (⟨c, mem_zpowers c⟩ : zpowers c)
    have hcop : (orderOf c).Coprime m := by
      rw [hord]
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hzodd)
    have hle : zpowers (c ^ m) ≤ zpowers c := zpowers_le.mpr (pow_mem (mem_zpowers _) m)
    have hcard : Nat.card (zpowers (c ^ m)) = Nat.card (zpowers c) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hcop.orderOf_pow]
    rw [eq_of_le_of_card_ge hle hcard.ge]
    exact mem_zpowers c
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hcm
  refine ⟨(a ^ m) ^ j, zpow_mem (pow_mem ha m) j, ?_, ?_⟩
  · exact (Commute.zpow_left ham j).eq
  · have : (⟨(a ^ m) ^ j, le_normalizer (zpow_mem (pow_mem ha m) j)⟩ : normalizer (A : Set G)) =
        (⟨a, le_normalizer ha⟩ ^ m) ^ j := by
      ext
      simp
    rw [this, map_zpow, map_pow]
    exact hj

theorem commutator_centralizer_le_map {A T : Subgroup G} {X : Subgroup W}
    {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A X ψ)
    (hTN : T ≤ normalizer (A : Set G)) :
    ⁅X ⊓ centralizer (((T.subgroupOf (normalizer (A : Set G))).map ψ : Subgroup W) : Set W),
      X ⊓ centralizer (((T.subgroupOf (normalizer (A : Set G))).map ψ : Subgroup W) : Set W)⁆ ≤
      ((A ⊓ centralizer (T : Set G)).subgroupOf (normalizer (A : Set G))).map ψ := by
  set E := (T.subgroupOf (normalizer (A : Set G))).map ψ
  let P : Subgroup (normalizer (A : Set G)) :=
    A.subgroupOf (normalizer (A : Set G)) ⊓ (centralizer (E : Set W)).comap ψ
  have hPmap : P.map ψ = X ⊓ centralizer (E : Set W) := by
    apply le_antisymm
    · rintro _ ⟨p, ⟨hpA, hpC⟩, rfl⟩
      exact ⟨hψ.map_mem (p : G) hpA, hpC⟩
    · rintro x ⟨hxX, hxC⟩
      obtain ⟨a, ha, rfl⟩ := hψ.exists_eq x hxX
      exact ⟨⟨a, le_normalizer ha⟩, ⟨ha, hxC⟩, rfl⟩
  have hPP : ⁅P, P⁆ ≤ (A ⊓ centralizer (T : Set G)).subgroupOf (normalizer (A : Set G)) := by
    rw [commutator_le]
    intro p hp q hq
    have hpA : (p : G) ∈ A := hp.1
    have hqA : (q : G) ∈ A := hq.1
    have hcoe : ((⁅p, q⁆ : normalizer (A : Set G)) : G) = ⁅(p : G), (q : G)⁆ := by
      simp [commutatorElement_def]
    change ((⁅p, q⁆ : normalizer (A : Set G)) : G) ∈ A ⊓ centralizer (T : Set G)
    rw [hcoe]
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem hpA hqA) (A.inv_mem hpA)) (A.inv_mem hqA)
    · refine mem_centralizer_iff.mpr fun t ht => ?_
      let t' : normalizer (A : Set G) := ⟨t, hTN ht⟩
      have htE : ψ t' ∈ E := ⟨t', ht, rfl⟩
      have hpc : ψ t' * ψ ⟨p, le_normalizer hpA⟩ = ψ ⟨p, le_normalizer hpA⟩ * ψ t' :=
        mem_centralizer_iff.mp hp.2 _ htE
      have hqc : ψ t' * ψ ⟨q, le_normalizer hqA⟩ = ψ ⟨q, le_normalizer hqA⟩ * ψ t' :=
        mem_centralizer_iff.mp hq.2 _ htE
      have h := conj_commutator_eq_of_disp hpA hqA (disp_mem_inf_centralizer hψ t' hpA hpc)
        (disp_mem_inf_centralizer hψ t' hqA hqc)
      calc t * ⁅(p : G), (q : G)⁆ = t * ⁅(p : G), (q : G)⁆ * t⁻¹ * t := by group
        _ = ⁅(p : G), (q : G)⁆ * t := by rw [h]
  calc ⁅X ⊓ centralizer (E : Set W), X ⊓ centralizer (E : Set W)⁆ = ⁅P.map ψ, P.map ψ⁆ := by
        rw [hPmap]
    _ = (⁅P, P⁆).map ψ := (map_commutator P P ψ).symm
    _ ≤ _ := map_mono hPP

end Lift

theorem isSolvable_inf_centralizer_of_isSylowOf [Finite G] {K T : Subgroup G}
    (hT : IsSylowOf 2 T K) (hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) :
    Group.IsSolvable ↥(K ⊓ centralizer (T : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := K ⊓ centralizer (T : Set G)
  have hTH : T ≤ H :=
    le_inf hT.le fun x hx => mem_centralizer_iff.mpr fun y hy => hTab y hy x hx
  have hTsyl : IsSylowOf 2 T H := by
    rw [isSylowOf_iff] at hT ⊢
    refine ⟨hTH, hT.2.1, fun h2 => hT.2.2 ?_⟩
    rw [← relIndex_mul_relIndex T H K hTH inf_le_left]
    exact h2.mul_right _
  obtain ⟨Q, hQ⟩ := hTsyl.exists_sylow_eq_subgroupOf
  have hP : normalizer ((Q : Subgroup H) : Set H) ≤ centralizer ((Q : Subgroup H) : Set H) := by
    intro h _
    rw [mem_centralizer_iff]
    intro x hx
    rw [SetLike.mem_coe, hQ, mem_subgroupOf] at hx
    exact Subtype.ext (mem_centralizer_iff.mp h.2.2 _ hx)
  have hker : ¬ 2 ∣ Nat.card (MonoidHom.transferSylow Q hP).ker :=
    MonoidHom.not_dvd_card_ker_transferSylow Q hP
  have : Group.IsSolvable (MonoidHom.transferSylow Q hP).ker :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hker))
  have hQT : ∀ x : H, x ∈ (Q : Subgroup H) → (x : G) ∈ T := fun x hx => by
    rw [hQ, mem_subgroupOf] at hx
    exact hx
  have : Group.IsSolvable Q := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (Subtype.ext (hTab _ (hQT _ a.2) _ (hQT _ b.2)))
  exact Group.isSolvable_of_ker_le_range (MonoidHom.transferSylow Q hP).ker.subtype
    (MonoidHom.transferSylow Q hP) (range_subtype _).ge

section Main

variable [Finite G] [Finite W]

omit [Finite G] [Finite W] in
theorem conj_mem_centralizer_of_mem_normalizer {A' : Subgroup G} {a k : G}
    (ha : a ∈ normalizer (A' : Set G)) (hk : k ∈ centralizer (A' : Set G)) :
    a * k * a⁻¹ ∈ centralizer (A' : Set G) := by
  rw [mem_centralizer_iff]
  intro x hx
  have hx' : a⁻¹ * x * a ∈ A' := by
    have := (mem_normalizer_iff.mp (inv_mem ha) x).mp hx
    simpa using this
  have hc := mem_centralizer_iff.mp hk _ hx'
  calc x * (a * k * a⁻¹) = a * ((a⁻¹ * x * a) * k) * a⁻¹ := by group
    _ = a * (k * (a⁻¹ * x * a)) * a⁻¹ := by rw [hc]
    _ = a * k * a⁻¹ * x := by group

omit [Finite G] [Finite W] in
theorem mem_of_odd_mul {H : Subgroup G} {s z y : G} (hyH : y ∈ H) (hzy : Commute z y)
    (hz : Odd (orderOf z)) (hs : s = z * y) (hs2 : s ^ 2 = 1) : s ∈ H := by
  obtain ⟨j, hj⟩ := hz
  have h1 : s ^ orderOf z = y ^ orderOf z := by
    rw [hs, hzy.mul_pow, pow_orderOf_eq_one, one_mul]
  have h2 : s ^ orderOf z = s := by
    rw [hj, pow_succ, pow_mul, hs2, one_pow, one_mul]
  rw [← h2, h1]
  exact pow_mem hyH _

theorem not_uWitness_map {A A' T : Subgroup G} {X : Subgroup W}
    {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A X ψ)
    {ψ' : normalizer (A' : Set G) →* W} (hψ' : IsActionHom A' X ψ')
    (hWX : ⁅(⊤ : Subgroup W), ⊤⁆ ≤ X) (hTN : T ≤ normalizer (A : Set G))
    (hTsyl : IsSylowOf 2 T (centralizer (A' : Set G))) (hTab : ∀ x ∈ T, x ^ 2 = 1)
    (hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ A, c * t = t * c → c ∈ normalizer (A' : Set G))
    (hKK : Odd (Nat.card ↥(centralizer (A : Set G) ⊓ centralizer (A' : Set G))))
    (hZ : Odd (Nat.card ↥(A ⊓ centralizer (A : Set G))))
    (hZ' : Odd (Nat.card ↥(A' ⊓ centralizer (A' : Set G)))) :
    ¬ UWitness X ((T.subgroupOf (normalizer (A : Set G))).map ψ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTC : T ≤ centralizer (A' : Set G) := hTsyl.le
  rintro ⟨_, ⟨s, hsT, rfl⟩, hs1, ⟨_, ⟨t, htT, rfl⟩, ht1, c, hcX, hct, hc2, _, ⟨v, hvT, rfl⟩,
    hvc⟩, P, hPle, hPperf, hsP⟩
  simp only [SetLike.mem_coe, mem_subgroupOf] at hsT htT hvT
  have hne : ∀ x : normalizer (A : Set G), ψ x ≠ 1 → (x : G) ≠ 1 := fun x hx h =>
    hx (by rw [show x = 1 from Subtype.ext h, map_one])
  have hs1' := hne s hs1
  have ht1' := hne t ht1
  obtain ⟨a, haA, hat, hac⟩ := exists_lift_of_isPGroup hψ hZ t hcX hct hc2
  have haN : a ∈ normalizer (A' : Set G) := hQ t htT ht1' a haA hat
  set y : G := (v : G) * a * (v : G)⁻¹ * a⁻¹ with hy
  have hyA : y ∈ A := A.mul_mem ((mem_normalizer_iff.mp v.2 a).mp haA) (A.inv_mem haA)
  have hyK : y ∈ centralizer (A' : Set G) := by
    have h1 : a * (v : G)⁻¹ * a⁻¹ ∈ centralizer (A' : Set G) :=
      conj_mem_centralizer_of_mem_normalizer haN (inv_mem (hTC hvT))
    rw [hy, show (v : G) * a * (v : G)⁻¹ * a⁻¹ = (v : G) * (a * (v : G)⁻¹ * a⁻¹) by group]
    exact mul_mem (hTC hvT) h1
  have hψy : ψ ⟨y, le_normalizer hyA⟩ = ψ s := by
    have : (⟨y, le_normalizer hyA⟩ : normalizer (A : Set G)) = ⁅v, ⟨a, le_normalizer haA⟩⁆ :=
      Subtype.ext (by simp [hy, commutatorElement_def])
    rw [this, map_commutatorElement, hac, hvc]
  have hk : (s : G) * y⁻¹ ∈ centralizer (A : Set G) ⊓ centralizer (A' : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (hTC hsT) (inv_mem hyK)⟩
    have h1 : ψ (s * (⟨y, le_normalizer hyA⟩ : normalizer (A : Set G))⁻¹) = 1 := by
      rw [map_mul, map_inv, hψy, mul_inv_cancel]
    simpa using (hψ.eq_one_iff _).mp h1
  have hsA : (s : G) ∈ A := by
    have hkodd : Odd (orderOf ((s : G) * y⁻¹)) := by
      have h := orderOf_dvd_natCard
        (⟨(s : G) * y⁻¹, hk⟩ : ↥(centralizer (A : Set G) ⊓ centralizer (A' : Set G)))
      rw [Subgroup.orderOf_mk] at h
      exact hKK.of_dvd_nat h
    exact mem_of_odd_mul hyA (mem_centralizer_iff.mp hk.1 y hyA).symm hkodd (by group)
      (hTab _ hsT)
  have hPQ : P ≤ ((A ⊓ centralizer (T : Set G)).subgroupOf (normalizer (A : Set G))).map ψ :=
    hPle.trans (commutator_centralizer_le_map hψ hTN)
  obtain ⟨P₁, hP₁Q, hP₁perf, hP₁map⟩ := exists_perfect_le_map_eq ψ
    (Q := (A ⊓ centralizer (T : Set G)).subgroupOf (normalizer (A : Set G)) ⊓ P.comap ψ)
    (by
      apply le_antisymm
      · exact (map_mono inf_le_right).trans (map_comap_le _ _)
      · intro x hx
        obtain ⟨q, hq, rfl⟩ := hPQ hx
        exact ⟨q, ⟨hq, hx⟩, rfl⟩) hPperf
  have hP₁A : ∀ q ∈ P₁, (q : G) ∈ A ∧ (q : G) ∈ centralizer (T : Set G) :=
    fun q hq => (hP₁Q hq).1
  have hP₁N : ∀ q ∈ P₁, (q : G) ∈ normalizer (A' : Set G) := fun q hq =>
    hQ s hsT hs1' q (hP₁A q hq).1 (mem_centralizer_iff.mp (hP₁A q hq).2 s hsT).symm
  let PG : Subgroup G := P₁.map (normalizer (A : Set G)).subtype
  have hPGperf : ⁅PG, PG⁆ = PG := by rw [← map_commutator, hP₁perf]
  have hPGN : PG ≤ normalizer (A' : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    exact hP₁N q hq
  have hdec : ∀ q ∈ P₁, ∃ b ∈ A', b⁻¹ * (q : G) ∈ centralizer (A' : Set G) := by
    intro q hq
    have hqG : (q : G) ∈ PG := ⟨q, hq, rfl⟩
    obtain ⟨b, hb, he⟩ := hψ'.exists_eq _ (map_mem_of_mem_perfect hWX hPGN hPGperf hqG)
    refine ⟨b, hb, (hψ'.eq_one_iff (⟨b, le_normalizer hb⟩⁻¹ * ⟨q, hPGN hqG⟩)).mp ?_⟩
    rw [map_mul, map_inv, he, inv_mul_cancel]
  let M : Subgroup G := A' ⊔ centralizer (A' : Set G)
  have hMN : M ≤ normalizer (A' : Set G) := sup_le le_normalizer (centralizer_le_normalizer _)
  have hA'M : (A'.subgroupOf M).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hMN
  have hPM : ∀ q : P₁, ((q : normalizer (A : Set G)) : G) ∈ M := by
    intro q
    obtain ⟨b, hb, hk⟩ := hdec q q.2
    rw [show ((q : normalizer (A : Set G)) : G) = b * (b⁻¹ * q) by group]
    exact mul_mem_sup hb hk
  let φ : P₁ →* M ⧸ A'.subgroupOf M := (QuotientGroup.mk' (A'.subgroupOf M)).comp
    (((normalizer (A : Set G)).subtype.comp P₁.subtype).codRestrict M hPM)
  let H : Subgroup G := centralizer (A' : Set G) ⊓ centralizer (T : Set G)
  have hHsolv : Group.IsSolvable ↥H :=
    isSolvable_inf_centralizer_of_isSylowOf hTsyl fun x hx y hy => commute_of_sq_eq_one hTab hx hy
  have hHM : H ≤ M := inf_le_left.trans le_sup_right
  let χ : ↥H →* M ⧸ A'.subgroupOf M := (QuotientGroup.mk' (A'.subgroupOf M)).comp (inclusion hHM)
  have hφχ : φ.range ≤ χ.range := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨b, hb, hk⟩ := hdec q q.2
    have hkT : b⁻¹ * ((q : normalizer (A : Set G)) : G) ∈ centralizer (T : Set G) := by
      rw [mem_centralizer_iff]
      intro x hx
      have hbx : x * b = b * x := (mem_centralizer_iff.mp (hTC hx) b hb).symm
      have hqx : x * ((q : normalizer (A : Set G)) : G) = ((q : normalizer (A : Set G)) : G) * x :=
        mem_centralizer_iff.mp (hP₁A q q.2).2 x hx
      calc x * (b⁻¹ * ((q : normalizer (A : Set G)) : G))
          = b⁻¹ * (b * x * b⁻¹) * ((q : normalizer (A : Set G)) : G) := by group
        _ = b⁻¹ * (x * b * b⁻¹) * ((q : normalizer (A : Set G)) : G) := by rw [hbx]
        _ = b⁻¹ * (x * ((q : normalizer (A : Set G)) : G)) := by group
        _ = b⁻¹ * ((q : normalizer (A : Set G)) : G) * x := by rw [hqx]; group
    refine ⟨⟨b⁻¹ * q, hk, hkT⟩, ?_⟩
    change QuotientGroup.mk' (A'.subgroupOf M) ⟨b⁻¹ * q, hHM ⟨hk, hkT⟩⟩ =
      QuotientGroup.mk' (A'.subgroupOf M) ⟨_, hPM q⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
    simp only [coe_mul, coe_inv, mul_inv_rev, inv_inv]
    have hqN := hP₁N q q.2
    have := (mem_normalizer_iff.mp (inv_mem hqN) b).mp hb
    simpa [mul_assoc] using this
  have hφ1 : ∀ q : P₁, φ q = 1 := by
    have hperf : Group.IsPerfect P₁ := (Subgroup.isPerfect_iff).mpr hP₁perf
    have hR : Group.IsPerfect φ.range := Group.IsPerfect.range φ
    have hχsolv : Group.IsSolvable χ.range :=
      Group.isSolvable_of_surjective (f := χ.rangeRestrict) χ.rangeRestrict_surjective
    have hsolv : Group.IsSolvable φ.range :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective hφχ)
    have hbot : φ.range = ⊥ := by
      by_contra hne
      have : Nontrivial φ.range := (nontrivial_iff_ne_bot _).mpr hne
      exact Group.IsPerfect.not_isSolvable φ.range hsolv
    intro q
    have : φ q ∈ φ.range := ⟨q, rfl⟩
    rwa [hbot, mem_bot] at this
  have hP₁A' : ∀ q : P₁, ((q : normalizer (A : Set G)) : G) ∈ A' := by
    intro q
    have := hφ1 q
    change QuotientGroup.mk' (A'.subgroupOf M) ⟨_, hPM q⟩ = 1 at this
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at this
  rw [← hP₁map] at hsP
  obtain ⟨p, hp, hps⟩ := hsP
  have hpA := (hP₁A p hp).1
  have hz : (s : G) * (p : G)⁻¹ ∈ A ⊓ centralizer (A : Set G) := by
    refine ⟨A.mul_mem hsA (A.inv_mem hpA), ?_⟩
    have h1 : ψ (s * p⁻¹) = 1 := by rw [map_mul, map_inv, hps, mul_inv_cancel]
    simpa using (hψ.eq_one_iff _).mp h1
  have hzodd : Odd (orderOf ((s : G) * (p : G)⁻¹)) := by
    have h := orderOf_dvd_natCard (⟨(s : G) * (p : G)⁻¹, hz⟩ : ↥(A ⊓ centralizer (A : Set G)))
    rw [Subgroup.orderOf_mk] at h
    exact hZ.of_dvd_nat h
  have hsA' : (s : G) ∈ A' :=
    mem_of_odd_mul (hP₁A' ⟨p, hp⟩) (mem_centralizer_iff.mp hz.2 _ hpA).symm hzodd (by group)
      (hTab _ hsT)
  have hsZ : (s : G) ∈ A' ⊓ centralizer (A' : Set G) := ⟨hsA', hTC hsT⟩
  have hsodd : Odd (orderOf (s : G)) := by
    have h := orderOf_dvd_natCard (⟨(s : G), hsZ⟩ : ↥(A' ⊓ centralizer (A' : Set G)))
    rw [Subgroup.orderOf_mk] at h
    exact hZ'.of_dvd_nat h
  rw [orderOf_eq_prime (hTab _ hsT) hs1'] at hsodd
  exact absurd hsodd (by decide)

end Main

end CFSG.ComponentClassification.RankTwoSporadic
