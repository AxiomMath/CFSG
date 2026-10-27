module

public import CFSG.Open.LocalVocabulary

public section

open Subgroup CFSG.Open


namespace CFSG.HardMathSupport.Solomon.Proving

theorem card_eq_index_mul_card_inf {K : Type*} [Group K] [Finite K] (P R : Subgroup K) [R.Normal]
    (h : P ⊔ R = ⊤) : Nat.card R = P.index * Nat.card (P ⊓ R : Subgroup K) := by
  have h1 := Subgroup.index_mul_card R
  have h2 := Subgroup.index_mul_card P
  have h3 := Subgroup.relIndex_mul_card R P
  have h4 : R.relIndex P = R.index := by
    have := Subgroup.relIndex_sup_right P R
    rw [h, Subgroup.relIndex_top_right] at this
    exact this.symm
  rw [h4, inf_comm] at h3
  have hR : R.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hR)
  rw [h1, ← h2, ← h3]
  ring

theorem relIndex_isPow {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {Q : Subgroup G}
    (hQ : IsPGroup p Q) (N : Subgroup G) : ∃ k : ℕ, N.relIndex Q = p ^ k := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
  have h1 := Subgroup.index_mul_card (N.subgroupOf Q)
  have hdvd : (N.subgroupOf Q).index ∣ p ^ n := ⟨_, by rw [← hn, ← h1]⟩
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  exact ⟨m, hm⟩

theorem eq_one_of_dvd_pow_of_not_dvd {p d n : ℕ} (hp : p.Prime) (h1 : d ∣ p ^ n) (h2 : ¬ p ∣ d) :
    d = 1 := by
  obtain ⟨m, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 h1
  cases m with
  | zero => rfl
  | succ m => exact absurd (dvd_pow_self p (Nat.succ_ne_zero m)) h2

theorem isPGroup_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : ∀ x ∈ E, x ^ p = 1) : IsPGroup p E := by
  have := Fact.mk hp
  rw [IsPGroup.iff_orderOf]
  intro g
  have hg : (g : G) ^ p = 1 := hE _ g.2
  have hd : orderOf (g : G) ∣ p := orderOf_dvd_of_pow_eq_one hg
  rcases (Nat.dvd_prime hp).1 hd with h | h
  · exact ⟨0, by rw [pow_zero, ← Subgroup.orderOf_coe, h]⟩
  · exact ⟨1, by rw [pow_one, ← Subgroup.orderOf_coe, h]⟩

theorem exp_eq_of_mul_eq {p a o i j : ℕ} [hp : Fact p.Prime] (ha : ¬ p ∣ a) (ho : ¬ p ∣ o)
    (h : a * p ^ i = o * p ^ j) : i = j := by
  have ha0 : a ≠ 0 := by rintro rfl; exact ha (dvd_zero p)
  have ho0 : o ≠ 0 := by rintro rfl; exact ho (dvd_zero p)
  have h1 := congrArg (padicValNat p) h
  rw [padicValNat.mul ha0 (pow_ne_zero _ hp.out.ne_zero), padicValNat.mul ho0 (pow_ne_zero _ hp.out.ne_zero),
    padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd ha,
    padicValNat.eq_zero_of_not_dvd ho] at h1
  simpa using h1


theorem exists_sylow_sup_eq_top {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    {Q R : Subgroup K} [R.Normal] (hQ : IsPGroup p Q) (h : Q ⊔ R = ⊤) :
    ∃ P : Subgroup K, Q ≤ P ∧ IsPGroup p P ∧ ¬ p ∣ P.index ∧ P ⊔ R = ⊤ := by
  have := Fact.mk hp
  obtain ⟨S, hQS⟩ := hQ.exists_le_sylow
  have hnd : ¬ p ∣ (S : Subgroup K).index := Sylow.not_dvd_index S
  refine ⟨S, hQS, S.isPGroup', hnd, ?_⟩
  have hRp : ∃ k, R.index = p ^ k := by
    have h1 := Subgroup.relIndex_sup_right Q R
    rw [h, Subgroup.relIndex_top_right] at h1
    obtain ⟨k, hk⟩ := relIndex_isPow hp hQ R
    exact ⟨k, h1.trans hk⟩
  obtain ⟨k, hk⟩ := hRp
  have hXS : ((S : Subgroup K) ⊔ R).index ∣ (S : Subgroup K).index :=
    Subgroup.index_dvd_of_le le_sup_left
  have hXR : ((S : Subgroup K) ⊔ R).index ∣ R.index := Subgroup.index_dvd_of_le le_sup_right
  have hX1 : ((S : Subgroup K) ⊔ R).index = 1 := by
    refine eq_one_of_dvd_pow_of_not_dvd hp (n := k) ?_ ?_
    · rw [← hk]; exact hXR
    · intro hd; exact hnd (hd.trans hXS)
  exact Subgroup.index_eq_one.1 hX1

theorem exists_qr_subgroup {M : Type*} [Group M] (Q R : Subgroup M)
    (hQN : ∀ q ∈ Q, ∀ r ∈ R, q * r * q⁻¹ ∈ R) :
    ∃ H : Subgroup M, Q ≤ H ∧ R ≤ H ∧ ∀ x ∈ H, ∃ q ∈ Q, ∃ r ∈ R, q * r = x := by
  let S : Subgroup M :=
    { carrier := {x | ∃ q ∈ Q, ∃ r ∈ R, q * r = x}
      one_mem' := ⟨1, Q.one_mem, 1, R.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨q1, hq1, r1, hr1, rfl⟩ ⟨q2, hq2, r2, hr2, rfl⟩
        have hc : q2⁻¹ * r1 * q2 ∈ R := by
          have := hQN _ (Q.inv_mem hq2) _ hr1
          simpa using this
        refine ⟨q1 * q2, Q.mul_mem hq1 hq2, (q2⁻¹ * r1 * q2) * r2, R.mul_mem hc hr2, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨q, hq, r, hr, rfl⟩
        refine ⟨q⁻¹, Q.inv_mem hq, q * r⁻¹ * q⁻¹, hQN q hq _ (R.inv_mem hr), ?_⟩
        group }
  refine ⟨S, fun q hq => ⟨q, hq, 1, R.one_mem, mul_one q⟩,
    fun r hr => ⟨1, Q.one_mem, r, hr, one_mul r⟩, ?_⟩
  rintro x ⟨q, hq, r, hr, rfl⟩
  exact ⟨q, hq, r, hr, rfl⟩

theorem card_comap_mk_eq_mul {M : Type*} [Group M] [Finite M] (O : Subgroup M) [O.Normal]
    (Ebar : Subgroup (M ⧸ O)) :
    Nat.card ↥(Ebar.comap (QuotientGroup.mk' O)) = Nat.card O * Nat.card Ebar := by
  have h1 := Subgroup.card_mul_index (Ebar.comap (QuotientGroup.mk' O))
  have h4 : (Ebar.comap (QuotientGroup.mk' O)).index = Ebar.index :=
    Subgroup.index_comap_of_surjective (H := Ebar) (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  rw [h4] at h1
  have h2 := Subgroup.card_mul_index Ebar
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup O
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := Ebar)))
  rw [h1, h3, ← h2]
  ring

theorem exists_elemAbelian_centralizer_lift {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (O : Subgroup M) [O.Normal] (hO : Nat.Coprime p (Nat.card O))
    (Q : Subgroup M) (hQ : IsPGroup p Q) (Ebar : Subgroup (M ⧸ O)) (hE : IsElemAbelian p Ebar)
    (hQE : Ebar ≤ Subgroup.centralizer
      ((Q.map (QuotientGroup.mk' O) : Subgroup (M ⧸ O)) : Set (M ⧸ O))) :
    ∃ E : Subgroup M, IsElemAbelian p E ∧ Nat.card E = Nat.card Ebar ∧
      E ≤ Subgroup.centralizer (Q : Set M) := by
  have := Fact.mk hp
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup M, R = Ebar.comap (QuotientGroup.mk' O) := ⟨_, rfl⟩
  have hRmem : ∀ x : M, x ∈ R ↔ (x : M ⧸ O) ∈ Ebar := by
    intro x; rw [hRdef]; exact Iff.rfl
  have hEbarComm : ∀ a ∈ Ebar, ∀ b ∈ Ebar, a * b = b * a := by
    intro a ha b hb
    have := hE.1.is_comm.comm (⟨a, ha⟩ : Ebar) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hcommQ : ∀ q ∈ Q, ∀ x ∈ R, (QuotientGroup.mk q : M ⧸ O) * (QuotientGroup.mk x : M ⧸ O)
      = (QuotientGroup.mk x : M ⧸ O) * (QuotientGroup.mk q : M ⧸ O) := by
    intro q hq x hx
    have hmem : (QuotientGroup.mk q : M ⧸ O) ∈ Q.map (QuotientGroup.mk' O) :=
      Subgroup.mem_map_of_mem _ hq
    exact Subgroup.mem_centralizer_iff.1 (hQE ((hRmem x).1 hx)) _ hmem
  have hQN : ∀ q ∈ Q, ∀ r ∈ R, q * r * q⁻¹ ∈ R := by
    intro q hq r hr
    rw [hRmem, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hcommQ q hq r hr, mul_inv_cancel_right]
    exact (hRmem r).1 hr
  obtain ⟨H, hQH, hRH, hHdec⟩ := exists_qr_subgroup Q R hQN
  have hRn : (R.subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨q, hq, r, hr, hqr⟩ := hHdec g.1 g.2
    have hn' : (n : M) ∈ R := hn
    show (g : M) * (n : M) * (g : M)⁻¹ ∈ R
    have hconj : (g : M) * (n : M) * (g : M)⁻¹ = q * (r * n * r⁻¹) * q⁻¹ := by
      rw [← hqr]; group
    rw [hconj]
    exact hQN q hq _ (R.mul_mem (R.mul_mem hr hn') (R.inv_mem hr))
  have hQ' : IsPGroup p (Q.subgroupOf H) := hQ.comap_subtype
  have hsup : Q.subgroupOf H ⊔ R.subgroupOf H = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    rw [Subgroup.mem_sup_of_normal_right]
    obtain ⟨q, hq, r, hr, hqr⟩ := hHdec x.1 x.2
    exact ⟨⟨q, hQH hq⟩, hq, ⟨r, hRH hr⟩, hr, Subtype.ext hqr⟩
  obtain ⟨P, hQP, hPp, hPnd, hPtop⟩ := exists_sylow_sup_eq_top hp hQ' hsup
  have hcardR' : Nat.card ↥(R.subgroupOf H) = Nat.card R := by
    have h := Subgroup.card_map_of_injective (f := H.subtype) (K := R.subgroupOf H) Subtype.val_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hRH] at h
    exact h.symm
  have hcardR : Nat.card R = Nat.card O * Nat.card Ebar := by
    rw [hRdef]; exact card_comap_mk_eq_mul O Ebar
  have hsplit : Nat.card ↥(R.subgroupOf H) = P.index * Nat.card ↥(P ⊓ R.subgroupOf H) :=
    card_eq_index_mul_card_inf P (R.subgroupOf H) hPtop
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hPp
  have hdvdT : Nat.card ↥(P ⊓ R.subgroupOf H) ∣ p ^ n := by
    rw [← hn]; exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hdvdT
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (isPGroup_of_pow_eq_one hp (fun x hx => hE.2 x hx))
  have harith : P.index * p ^ i = Nat.card O * p ^ j := by
    rw [← hi, ← hj, ← hsplit, hcardR', hcardR]
  have hij : i = j := exp_eq_of_mul_eq hPnd ((Nat.Prime.coprime_iff_not_dvd hp).1 hO) harith
  obtain ⟨T, hTdef⟩ : ∃ T : Subgroup H, T = P ⊓ R.subgroupOf H := ⟨_, rfl⟩
  have hi' : Nat.card T = p ^ i := by rw [hTdef]; exact hi
  have hTE : Nat.card T = Nat.card Ebar := by rw [hi', hj, hij]
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup M, E = T.map H.subtype := ⟨_, rfl⟩
  have hEmem : ∀ x : M, x ∈ E ↔ ∃ t ∈ T, (t : M) = x := by
    intro x; rw [hEdef]; exact Subgroup.mem_map
  have hcardE : Nat.card E = Nat.card T := by
    rw [hEdef]; exact Subgroup.card_map_of_injective Subtype.val_injective
  have hER : ∀ x ∈ E, x ∈ R := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := (hEmem _).1 hx
    rw [hTdef] at ht
    exact ht.2
  have hmkE : ∀ x ∈ E, (QuotientGroup.mk x : M ⧸ O) ∈ Ebar := fun x hx => (hRmem x).1 (hER x hx)
  have hEbarComm : ∀ a ∈ Ebar, ∀ b ∈ Ebar, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : Ebar) ⟨b, hb⟩)
  have hbot : E ⊓ O = ⊥ := by
    have hd1 : Nat.card ↥(E ⊓ O) ∣ Nat.card ↥O := Subgroup.card_dvd_of_le inf_le_right
    have hd2 : Nat.card ↥(E ⊓ O) ∣ p ^ i := by
      have h := Subgroup.card_dvd_of_le (inf_le_left : E ⊓ O ≤ E)
      rw [hcardE, hi'] at h
      exact h
    have h1 := eq_one_of_dvd_pow_of_not_dvd hp hd2
      (fun h => ((Nat.Prime.coprime_iff_not_dvd hp).1 hO) (h.trans hd1))
    exact Subgroup.eq_bot_of_card_eq _ h1
  have hEO : ∀ x ∈ E, x ∈ O → x = 1 := by
    intro x hx hxO
    have hmem : x ∈ E ⊓ O := ⟨hx, hxO⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    have hc : x * y * x⁻¹ * y⁻¹ ∈ E :=
      E.mul_mem (E.mul_mem (E.mul_mem hx hy) (E.inv_mem hx)) (E.inv_mem hy)
    have hmk : (QuotientGroup.mk (x * y * x⁻¹ * y⁻¹) : M ⧸ O) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv]
      rw [hEbarComm _ (hmkE x hx) _ (hmkE y hy)]
      group
    have hO' : x * y * x⁻¹ * y⁻¹ ∈ O := (QuotientGroup.eq_one_iff _).1 hmk
    have h1 := hEO _ hc hO'
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  have hEexp : ∀ x ∈ E, x ^ p = 1 := by
    intro x hx
    apply hEO _ (E.pow_mem hx p)
    apply (QuotientGroup.eq_one_iff _).1
    rw [QuotientGroup.mk_pow]
    exact hE.2 _ (hmkE x hx)
  have hEcentr : E ≤ Subgroup.centralizer (Q : Set M) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨t, htT, rfl⟩ := (hEmem _).1 hx
    have hqH : q ∈ H := hQH hq
    have hqP : (⟨q, hqH⟩ : H) ∈ P := hQP (Subgroup.mem_subgroupOf.2 hq)
    have htP : t ∈ P := by rw [hTdef] at htT; exact htT.1
    have htR : (t : M) ∈ R := by rw [hTdef] at htT; exact htT.2
    have hcT : (⟨q, hqH⟩ : H) * t * (⟨q, hqH⟩ : H)⁻¹ ∈ T := by
      rw [hTdef]
      exact ⟨P.mul_mem (P.mul_mem hqP htP) (P.inv_mem hqP), hRn.conj_mem _ htR _⟩
    have hd : q * (t : M) * q⁻¹ ∈ E := (hEmem _).2 ⟨_, hcT, rfl⟩
    have htE : (t : M) ∈ E := (hEmem _).2 ⟨t, htT, rfl⟩
    have hmkd : (QuotientGroup.mk (q * (t : M) * q⁻¹) : M ⧸ O) = QuotientGroup.mk (t : M) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        hcommQ q hq (t : M) htR, mul_inv_cancel_right]
    have hz : (q * (t : M) * q⁻¹) * (t : M)⁻¹ ∈ E := E.mul_mem hd (E.inv_mem htE)
    have hzO : (q * (t : M) * q⁻¹) * (t : M)⁻¹ ∈ O := by
      apply (QuotientGroup.eq_one_iff _).1
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmkd, mul_inv_cancel]
    have hz1 := hEO _ hz hzO
    calc q * (t : M) = (q * (t : M) * q⁻¹ * (t : M)⁻¹) * ((t : M) * q) := by group
      _ = (t : M) * q := by rw [hz1, one_mul]
  have hIsComm : IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (hEcomm a.1 a.2 b.1 b.2)⟩⟩
  exact ⟨E, ⟨hIsComm, hEexp⟩, hcardE.trans hTE, hEcentr⟩

end CFSG.HardMathSupport.Solomon.Proving
