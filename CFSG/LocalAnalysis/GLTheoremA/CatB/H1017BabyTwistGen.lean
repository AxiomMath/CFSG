module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Twist

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open

variable {K : Type} [Group K] [Finite K]

theorem noTwist_of_hyperplane {r : ℕ} (hr : 1 ≤ r)
    (h : ∀ E D T : Subgroup K, IsElemAbelian 3 E → Nat.card E = 3 ^ r → D ≤ E →
      Nat.card D = 3 ^ (r - 1) → IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set K) →
      T ≤ Subgroup.centralizer (D : Set K) → T ≤ Subgroup.centralizer (E : Set K))
    (E₀ : Subgroup K) (hE₀ : IsElemAbelian 3 E₀) (hcard : 3 ^ r ≤ Nat.card E₀) (T : Subgroup K)
    (hT : IsPGroup 2 T) (hET : E₀ ≤ Subgroup.normalizer (T : Set K)) :
    ∀ e ∈ E₀, ∀ t ∈ T, e * t = t * e := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro e he t ht
  have hE₀p : IsPGroup 3 E₀ := fun g => ⟨1, Subtype.ext (by simpa using hE₀.2 g g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hE₀p
  have hrn : r ≤ n := by
    rw [hn] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard
  have hze : Nat.card (Subgroup.zpowers e) ∣ 3 ^ r := by
    rw [Nat.card_zpowers]
    exact (orderOf_dvd_of_pow_eq_one (hE₀.2 e he)).trans (dvd_pow_self 3 (by omega))
  obtain ⟨E, hEcard, hzE, hEE₀⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three hze
    (show 3 ^ r ∣ Nat.card E₀ from hn ▸ Nat.pow_dvd_pow 3 hrn)
    ((Subgroup.zpowers_le).2 he)
  have heE : e ∈ E := hzE (Subgroup.mem_zpowers e)
  have hE : IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.mono hE₀ hEE₀
  have hEne : E ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hEcard
    have : 3 ≤ 3 ^ r := Nat.le_self_pow (by omega) 3
    omega
  have hT3 : ¬ 3 ∣ Nat.card T := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hT
    rw [hk]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow hd)
    omega
  have hEN : E ≤ Subgroup.normalizer (T : Set K) := hEE₀.trans hET
  have hgen := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1114.gen_by_hyperplanes
    Nat.prime_three hE hEne hEN hT3
  have hcent : ∀ D : Subgroup K, D ≤ E ∧ (D.subgroupOf E).index = 3 →
      T ⊓ Subgroup.centralizer (D : Set K) ≤ Subgroup.centralizer (E : Set K) := by
    rintro D ⟨hDE, hDi⟩
    have hDcard : Nat.card D = 3 ^ (r - 1) := by
      have h1 := (D.subgroupOf E).card_mul_index
      rw [hDi, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDE).toEquiv, hEcard] at h1
      have : 3 ^ r = 3 ^ (r - 1) * 3 := by rw [← pow_succ]; congr 1; omega
      rw [this] at h1
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
    refine h E D _ hE hEcard hDE hDcard (hT.to_le inf_le_left) (fun a ha => ?_) inf_le_right
    have haD : a ∈ Subgroup.centralizer (D : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact comm_of_isElemAbelian' hE (hDE hd) ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hxT := Subgroup.mem_normalizer_iff.1 (hEN ha) x
    simp only [SetLike.mem_coe, Subgroup.mem_inf] at hxT ⊢
    constructor
    · rintro ⟨hx, hxD⟩
      exact ⟨hxT.1 hx, Subgroup.mul_mem _ (Subgroup.mul_mem _ haD hxD) (Subgroup.inv_mem _ haD)⟩
    · rintro ⟨hx, hxD⟩
      refine ⟨hxT.2 hx, ?_⟩
      have e1 : x = a⁻¹ * (a * x * a⁻¹) * a := by group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ haD) hxD) haD
  have hTE : T ≤ Subgroup.centralizer (E : Set K) :=
    hgen.trans (iSup₂_le fun D hD => hcent D hD)
  exact Subgroup.mem_centralizer_iff.1 (hTE ht) e heE

theorem NoTwistRank.comm_of_subgroup {s : TauCeti.SporadicName} {r : ℕ} (hs : NoTwistRank s r)
    {H : Subgroup K} (hH : Nonempty (↥H ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    {E T : Subgroup K} (hEH : E ≤ H) (hTH : T ≤ H) (hE : IsElemAbelian 3 E)
    (hc : 3 ^ r ≤ Nat.card E) (hT : IsPGroup 2 T) (hN : E ≤ Subgroup.normalizer (T : Set K)) :
    ∀ e ∈ E, ∀ t ∈ T, e * t = t * e := by
  intro e he t ht
  have hN' : E.subgroupOf H ≤ Subgroup.normalizer ((T.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := Subgroup.mem_normalizer_iff.1 (hN (Subgroup.mem_subgroupOf.1 hx)) (y : K)
    simpa only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      using this
  have hT' : IsPGroup 2 (T.subgroupOf H) := by
    rw [← Subgroup.comap_subtype]
    exact hT.comap_subtype
  have key := hs ↥H ⟨.sporadic s, rfl, hH⟩ (E.subgroupOf H) (isElemAbelian_subgroupOf hE H)
    (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv]) (T.subgroupOf H) hT' hN'
    ⟨e, hEH he⟩ (Subgroup.mem_subgroupOf.2 he) ⟨t, hTH ht⟩ (Subgroup.mem_subgroupOf.2 ht)
  exact congrArg Subtype.val key

theorem comm_of_pow_mul_index_two {r : ℕ} (hr : 1 ≤ r) {Q H E T : Subgroup K} {s : K}
    (hs3 : s ^ 3 = 1) (hqs : ∀ q ∈ Q, q * s = s * q)
    (hdecomp : ∀ g ∈ Subgroup.centralizer ({s} : Set K), ∃ k : ℕ, ∃ q ∈ Q, g = s ^ k * q)
    (hidx : (H.subgroupOf Q).index = 2)
    (hHtw : ∀ E' T' : Subgroup K, E' ≤ H → T' ≤ H → IsElemAbelian 3 E' →
      3 ^ (r - 1) ≤ Nat.card E' → IsPGroup 2 T' → E' ≤ Subgroup.normalizer (T' : Set K) →
      ∀ e ∈ E', ∀ t ∈ T', e * t = t * e)
    (hE : IsElemAbelian 3 E) (hcard : 3 ^ r ≤ Nat.card E) (hT : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set K)) (hsE : s ∈ E) (hTs : ∀ t ∈ T, t * s = s * t) :
    ∀ e ∈ E, ∀ t ∈ T, e * t = t * e := by
  have hmulH : ∀ a ∈ Q, ∀ b ∈ Q, (a * b ∈ H ↔ (a ∈ H ↔ b ∈ H)) := by
    intro a ha b hb
    have := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using this
  have hEdec : ∀ e ∈ E, ∃ k : ℕ, ∃ q ∈ E ⊓ Q, e = s ^ k * q := by
    intro e he
    obtain ⟨k, q, hq, rfl⟩ := hdecomp e
      (Subgroup.mem_centralizer_singleton_iff.2 (comm_of_isElemAbelian' hE he hsE))
    refine ⟨k, q, Subgroup.mem_inf.2 ⟨?_, hq⟩, rfl⟩
    have e1 : q = (s ^ k)⁻¹ * (s ^ k * q) := by group
    rw [e1]
    exact E.mul_mem (E.inv_mem (E.pow_mem hsE k)) he
  have hEQcard : 3 ^ (r - 1) ≤ Nat.card (E ⊓ Q : Subgroup K) := by
    let f : Fin 3 × ↥(E ⊓ Q) → ↥E := fun p =>
      ⟨s ^ (p.1 : ℕ) * p.2, E.mul_mem (E.pow_mem hsE _) (Subgroup.mem_inf.1 p.2.2).1⟩
    have hf : Function.Surjective f := by
      rintro ⟨e, he⟩
      obtain ⟨k, q, hq, rfl⟩ := hEdec e he
      refine ⟨(⟨k % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨q, hq⟩), Subtype.ext ?_⟩
      show s ^ (k % 3) * q = s ^ k * q
      conv_rhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hs3, one_pow, one_mul]
    have h1 := Nat.card_le_card_of_surjective f hf
    rw [Nat.card_prod, Nat.card_fin] at h1
    have hr' : 3 ^ r = 3 * 3 ^ (r - 1) := by rw [← pow_succ']; congr 1; omega
    rw [hr'] at hcard
    exact Nat.le_of_mul_le_mul_left (hcard.trans h1) (by norm_num)
  have hEQH : E ⊓ Q ≤ H := by
    intro q hq
    obtain ⟨hqE, hqQ⟩ := Subgroup.mem_inf.1 hq
    have hq2 : q * q ∈ H := by
      have := Subgroup.mul_self_mem_of_index_two hidx ⟨q, hqQ⟩
      rwa [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at this
    have hq3 : q ^ 3 = 1 := hE.2 q hqE
    have e1 : q = q * q * (q * q) := by
      calc q = q ^ 3 * q := by rw [hq3, one_mul]
        _ = q * q * (q * q) := by rw [pow_three]; simp only [mul_assoc]
    rw [e1]
    exact H.mul_mem hq2 hq2
  have hTQ : T ≤ Q := by
    intro t ht
    obtain ⟨k, q, hq, hkq⟩ := hdecomp t (Subgroup.mem_centralizer_singleton_iff.2 (hTs t ht))
    have hc : Commute (s ^ k) q := Commute.pow_left (show Commute s q from (hqs q hq).symm) k
    have ht3 : t ^ 3 ∈ Q := by
      rw [hkq, hc.mul_pow, ← pow_mul, mul_comm k 3, pow_mul, hs3, one_pow, one_mul]
      exact Q.pow_mem hq 3
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 hT ⟨t, ht⟩
    have hcop : Nat.Coprime 3 (orderOf t) := by
      rw [← Subgroup.orderOf_mk t ht, hj]
      exact Nat.Coprime.pow_right _ (by norm_num)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact Q.pow_mem ht3 m
  have hEQT : ∀ e ∈ E ⊓ Q, ∀ t ∈ T ⊓ H, e * t = t * e := by
    refine hHtw (E ⊓ Q) (T ⊓ H) hEQH inf_le_right (hE.mono inf_le_left) hEQcard
      (hT.to_le inf_le_left) fun a ha => ?_
    have haH : a ∈ H := hEQH ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hxT := Subgroup.mem_normalizer_iff.1 (hET (Subgroup.mem_inf.1 ha).1) x
    simp only [SetLike.mem_coe, Subgroup.mem_inf] at hxT ⊢
    constructor
    · rintro ⟨hx, hxH⟩
      exact ⟨hxT.1 hx, H.mul_mem (H.mul_mem haH hxH) (H.inv_mem haH)⟩
    · rintro ⟨hx, hxH⟩
      refine ⟨hxT.2 hx, ?_⟩
      have e1 : x = a⁻¹ * (a * x * a⁻¹) * a := by group
      rw [e1]
      exact H.mul_mem (H.mul_mem (H.inv_mem haH) hxH) haH
  have hETH : ∀ e ∈ E, ∀ t ∈ T ⊓ H, e * t = t * e := by
    intro e he t ht
    obtain ⟨k, q, hq, rfl⟩ := hEdec e he
    have hts : Commute (s ^ k) t :=
      Commute.pow_left (show Commute s t from (hTs t (Subgroup.mem_inf.1 ht).1).symm) k
    calc s ^ k * q * t = s ^ k * (q * t) := by rw [mul_assoc]
      _ = s ^ k * (t * q) := by rw [hEQT q hq t ht]
      _ = t * (s ^ k * q) := by rw [← mul_assoc, hts.eq, mul_assoc]
  intro e he t ht
  by_cases htH : t ∈ H
  · exact hETH e he t (Subgroup.mem_inf.2 ⟨ht, htH⟩)
  have hu : e * t * e⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hET he) t).1 ht
  obtain ⟨c, hc⟩ : ∃ c, c = t⁻¹ * (e * t * e⁻¹) := ⟨_, rfl⟩
  have hcT : c ∈ T := by rw [hc]; exact T.mul_mem (T.inv_mem ht) hu
  have hcH : c ∈ H := by
    obtain ⟨k, q, hq, hkq⟩ := hEdec e he
    have hqQ : q ∈ Q := (Subgroup.mem_inf.1 hq).2
    have htQ : t ∈ Q := hTQ ht
    have hqt : q * t * q⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hqQ htQ) (Q.inv_mem hqQ)
    have hsk : Commute (s ^ k) (q * t * q⁻¹) :=
      Commute.pow_left (show Commute s (q * t * q⁻¹) from (hqs _ hqt).symm) k
    have heq : e * t * e⁻¹ = q * t * q⁻¹ := by
      rw [hkq]
      calc s ^ k * q * t * (s ^ k * q)⁻¹ = s ^ k * (q * t * q⁻¹) * (s ^ k)⁻¹ := by group
        _ = q * t * q⁻¹ := by rw [hsk.eq, mul_inv_cancel_right]
    have hqtH : q * t * q⁻¹ ∉ H := by
      rw [hmulH _ (Q.mul_mem hqQ htQ) _ (Q.inv_mem hqQ), hmulH _ hqQ _ htQ, inv_mem_iff]
      tauto
    rw [hc, heq, hmulH _ (Q.inv_mem htQ) _ hqt, inv_mem_iff]
    tauto
  have hce : e * c = c * e := hETH e he c (Subgroup.mem_inf.2 ⟨hcT, hcH⟩)
  have hut : e * t * e⁻¹ = t * c := by rw [hc]; group
  have key : ∀ n : ℕ, e ^ n * t * (e ^ n)⁻¹ = t * c ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcn : e * c ^ n * e⁻¹ = c ^ n := by
        rw [(Commute.pow_right (show Commute e c from hce) n).eq, mul_inv_cancel_right]
      calc e ^ (n + 1) * t * (e ^ (n + 1))⁻¹ = e * (e ^ n * t * (e ^ n)⁻¹) * e⁻¹ := by group
        _ = e * t * e⁻¹ * (e * c ^ n * e⁻¹) := by rw [ih]; group
        _ = t * c ^ (n + 1) := by rw [hut, hcn, pow_succ', mul_assoc]
  have h3 := key 3
  rw [hE.2 e he, inv_one, mul_one, one_mul] at h3
  have hc3 : c ^ 3 ^ 1 = 1 := by
    rw [pow_one]
    exact mul_left_cancel (h3.symm.trans (mul_one t).symm)
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 hT ⟨c, hcT⟩
  have hc2 : c ^ 2 ^ j = 1 := by
    have := pow_orderOf_eq_one (⟨c, hcT⟩ : T)
    rw [hj] at this
    simpa using congrArg Subtype.val this
  rw [eq_one_of_pow_two_pow_p Nat.prime_three (by norm_num) hc3 hc2, mul_one] at hut
  calc e * t = e * t * e⁻¹ * e := by group
    _ = t * e := by rw [hut]

end CFSG.LocalAnalysis.GLTheoremA.H1017
