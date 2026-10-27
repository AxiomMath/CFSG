module

public import CFSG.GH74.GLS.C3.Layer1.Bk113aFiveW
public import CFSG.GH74.GLS.C3.Layer1.Bk113aFiveOrbit
public import CFSG.GH74.GLS.C3.Layer2.L5C7

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {x : G} {K L M T Q : Subgroup G}

theorem mem_of_index_le_two {R T : Subgroup G} (hRT : R ≤ T)
    (hcard : Nat.card ↥T ≤ 2 * Nat.card ↥R) {t y : G} (ht : t ∈ T) (hy : y ∈ T)
    (htR : t ∉ R) (hyR : y ∉ R) : y⁻¹ * t ∈ R := by
  by_contra hyt
  classical
  let t' : ↥T := ⟨t, ht⟩
  let y' : ↥T := ⟨y, hy⟩
  have hne1 : (QuotientGroup.mk 1 : ↥T ⧸ R.subgroupOf T) ≠ QuotientGroup.mk y' := by
    intro h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    exact hyR (by simpa using h)
  have hne2 : (QuotientGroup.mk 1 : ↥T ⧸ R.subgroupOf T) ≠ QuotientGroup.mk t' := by
    intro h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    exact htR (by simpa using h)
  have hne3 : (QuotientGroup.mk y' : ↥T ⧸ R.subgroupOf T) ≠ QuotientGroup.mk t' := by
    intro h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    exact hyt h
  have h3 : 2 < Nat.card (↥T ⧸ R.subgroupOf T) := by
    have := Fintype.ofFinite (↥T ⧸ R.subgroupOf T)
    rw [Nat.card_eq_fintype_card]
    exact Fintype.two_lt_card_iff.2 ⟨_, _, _, hne1, hne2, hne3⟩
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup (R.subgroupOf T)
  have h5 : Nat.card ↥(R.subgroupOf T) = Nat.card ↥R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRT).toEquiv
  rw [h5] at h4
  have hpos : 0 < Nat.card ↥R := Nat.card_pos
  have h6 : 3 * Nat.card ↥R ≤ Nat.card (↥T ⧸ R.subgroupOf T) * Nat.card ↥R :=
    Nat.mul_le_mul_right _ h3
  omega

omit [Finite G] in
theorem abelian_sup_of_commDisj {P Q : Subgroup G} (hCD : CommDisj P Q)
    (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) :
    ∀ a ∈ P ⊔ Q, ∀ b ∈ P ⊔ Q, a * b = b * a := by
  intro a ha b hb
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_of_commute hCD.comm ha
  obtain ⟨p', hp', q', hq', rfl⟩ := mem_sup_of_commute hCD.comm hb
  calc p * q * (p' * q') = p * (q * p') * q' := by group
    _ = p * (p' * q) * q' := by rw [← hCD.comm p' hp' q hq]
    _ = (p * p') * (q * q') := by group
    _ = (p' * p) * (q' * q) := by rw [hPab p hp p' hp', hQab q hq q' hq']
    _ = p' * (p * q') * q := by group
    _ = p' * (q' * p) * q := by rw [hCD.comm p hp q' hq']
    _ = p' * q' * (p * q) := by group

theorem five_TI_aux (hh : Hyp9A x K L M T Q) (hG : IsKProperSimple G) (h81 : B_iv2_8_1)
    (h92 : B_lemma92)
    (hlistL : HasL2Model (kBar L) Odd ∨ Nonempty (kBar L ≃* alternatingGroup (Fin 7)))
    (hQ4 : Nat.card ↥Q = 4) {R : Subgroup G} (hRT : R ≤ T) (hQR : Q ≤ R) {n : G}
    (hn : n ∈ normalizer (R : Set G)) :
    (n ∈ M → conjugate Q n = Q) ∧ (n ∉ M → conjugate Q n ⊓ Q = ⊥) := by
  have hVR : conjugate Q n ≤ R := fun v hv => by
    have h1 : n * v * n⁻¹ ∈ R := hQR (mem_conjugate_iff'.1 hv)
    have h2 := (Subgroup.mem_normalizer_iff.1 ((normalizer _).inv_mem hn) (n * v * n⁻¹)).1 h1
    have e : n⁻¹ * (n * v * n⁻¹) * n⁻¹⁻¹ = v := by group
    rwa [e] at h2
  have hVT : conjugate Q n ≤ T := hVR.trans hRT
  have hTM : T ≤ M := hh.sylowTM.le
  refine ⟨fun hnM => ?_, fun hnM => ?_⟩
  · have hle : conjugate Q n ≤ Q := by
      intro v hv
      have hu : n * v * n⁻¹ ∈ Q := mem_conjugate_iff'.1 hv
      have h1 := conj_mem_CMK hh.L_normal.2 (M.inv_mem hnM) (hh.sylowQ.le hu)
      rw [inv_inv] at h1
      have e : n⁻¹ * (n * v * n⁻¹) * n = v := by group
      rw [e] at h1
      have h2 : v ∈ T ⊓ CMK M L := ⟨hVT hv, h1⟩
      rwa [T_inf_CMK hh] at h2
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjugate', hQ4])
  · have hV0 : conjugate Q n ≠ ⊥ := by
      intro h0
      have h1 : Nat.card ↥(conjugate Q n) = 4 := by rw [card_conjugate']; exact hQ4
      rw [h0, Subgroup.card_bot] at h1
      omega
    have hV2 : 2 ≤ pRank 2 ↥(conjugate Q n) := by
      rw [pRank_conjugate']; exact hh.rankQ
    have hbot : conjugate Q n ⊓ CMK M L = ⊥ :=
      inf_CMK_eq_bot_of_not_mem hh hG h81 h92 hlistL hnM le_rfl (hVT.trans hTM) hV0 hV2
    refine eq_bot_iff.2 fun y hy => ?_
    have hy' : y ∈ conjugate Q n ⊓ CMK M L := ⟨hy.1, hh.sylowQ.le hy.2⟩
    rw [hbot] at hy'
    exact hy'

theorem five_weak_closure (hh : Hyp9A x K L M T Q)
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hsL : IsSimpleGroup (kBar L)) (hnL : ∃ a b : kBar L, a * b ≠ b * a)
    (e5 : kBar K ≃* alternatingGroup (Fin 5)) (hP4 : Nat.card ↥(T ⊓ K) = 4)
    (hQ4 : Nat.card ↥Q = 4) (hR16 : Nat.card ↥((T ⊓ K) ⊔ Q) = 16)
    (hRab : ∀ a ∈ (T ⊓ K) ⊔ Q, ∀ b ∈ (T ⊓ K) ⊔ Q, a * b = b * a)
    (hCD : CommDisj (T ⊓ K) Q)
    (hPn : ∀ t ∈ T, ∀ p ∈ T ⊓ K, t * p * t⁻¹ ∈ T ⊓ K)
    (hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q) (hT32 : Nat.card ↥T ≤ 32)
    (hL112 : (∀ q ∈ Q, ∀ t ∈ closure {u : G | u ∈ T ∧ u * u = 1}, q * t = t * q) →
      (T ⊓ K) ⊔ Q = T) (g : G)
    (hg : ((T ⊓ K) ⊔ Q).map (MulAut.conj g).toMonoidHom ≤ T) :
    ((T ⊓ K) ⊔ Q).map (MulAut.conj g).toMonoidHom = (T ⊓ K) ⊔ Q := by
  classical
  set R : Subgroup G := (T ⊓ K) ⊔ Q with hRdef
  set B : Subgroup G := R.map (MulAut.conj g).toMonoidHom with hBdef
  have hQT : Q ≤ T := Setup91.Q_le_T hh
  have hQR : Q ≤ R := le_sup_right
  have hRT : R ≤ T := sup_le inf_le_left hQT
  have hBcard : Nat.card ↥B = 16 := by
    rw [hBdef, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hR16
  by_cases hTR : T = R
  · exact Subgroup.eq_of_le_of_card_ge (hTR ▸ hg) (by rw [hBcard, hR16])
  · by_contra hBR
    have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
      intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      rw [← map_mul, ← map_mul, hRab a' ha' b' hb']
    obtain ⟨y, hyB, hyR⟩ : ∃ y ∈ B, y ∉ R := by
      by_contra hcon
      push Not at hcon
      exact hBR (Subgroup.eq_of_le_of_card_ge (fun y hy => hcon y hy) (by rw [hBcard, hR16]))
    have hyT : y ∈ T := hg hyB
    have hBR8 : 8 ≤ Nat.card ↥(B ⊓ R) := by
      have h := CFSG.GH74.GLS.C3.Layer1.P34.card_mul_inf B R
      have hsub : ((B : Set G) * (R : Set G)) ⊆ (T : Set G) := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        exact T.mul_mem (hg ha) (hRT hb)
      have hle : Nat.card ↥((B : Set G) * (R : Set G)) ≤ Nat.card ↥(T : Set G) :=
        Nat.card_mono (Set.toFinite _) hsub
      have hT' : Nat.card ↥(T : Set G) = Nat.card ↥T := rfl
      rw [hBcard, hR16] at h
      by_contra hlt
      push Not at hlt
      have h1 : Nat.card ↥((B : Set G) * (R : Set G)) * Nat.card ↥(B ⊓ R) ≤ 32 * 7 :=
        Nat.mul_le_mul (hle.trans (hT'.le.trans hT32)) (by omega)
      omega
    have hCsub : B ⊓ R ≤ R ⊓ centralizer ({y} : Set G) := fun z hz =>
      ⟨hz.2, mem_centralizer_singleton_iff.2 (hBab z hz.1 y hyB)⟩
    have hC8 : 8 ≤ Nat.card ↥(R ⊓ centralizer ({y} : Set G)) :=
      hBR8.trans (Subgroup.card_le_of_le hCsub)
    have hdec : ∀ r ∈ R ⊓ centralizer ({y} : Set G), ∃ p ∈ (T ⊓ K) ⊓ centralizer ({y} : Set G),
        ∃ q ∈ Q ⊓ centralizer ({y} : Set G), p * q = r := by
      intro r hr
      obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_of_commute hCD.comm hr.1
      have hyc : (p * q) * y = y * (p * q) := mem_centralizer_singleton_iff.1 hr.2
      have hp' := hPn y hyT p hp
      have hq' := hQn y hyT q hq
      have e1 : (y * p * y⁻¹) * (y * q * y⁻¹) = p * q := by
        have : y * (p * q) * y⁻¹ = p * q := by rw [← hyc]; group
        rw [← this]; group
      have h2 : p⁻¹ * (y * p * y⁻¹) = q * (y * q * y⁻¹)⁻¹ := by
        have e2 : y * p * y⁻¹ = p * q * (y * q * y⁻¹)⁻¹ := by
          rw [← e1]; group
        rw [e2]; group
      have h3 : p⁻¹ * (y * p * y⁻¹) ∈ (T ⊓ K) ⊓ Q :=
        ⟨(T ⊓ K).mul_mem ((T ⊓ K).inv_mem hp) hp', by rw [h2]; exact Q.mul_mem hq (Q.inv_mem hq')⟩
      rw [hCD.inf, Subgroup.mem_bot] at h3
      have hpy : y * p * y⁻¹ = p := by
        have : y * p * y⁻¹ = p * (p⁻¹ * (y * p * y⁻¹)) := by group
        rw [this, h3, mul_one]
      have hqy : y * q * y⁻¹ = q := by
        have h4 : p * q = p * (y * q * y⁻¹) := by
          rw [hpy] at e1; exact e1.symm
        exact (mul_left_cancel h4).symm
      refine ⟨p, ⟨hp, mem_centralizer_singleton_iff.2 ?_⟩, q, ⟨hq, mem_centralizer_singleton_iff.2 ?_⟩, rfl⟩
      · calc p * y = (y * p * y⁻¹) * y := by rw [hpy]
          _ = y * p := by group
      · calc q * y = (y * q * y⁻¹) * y := by rw [hqy]
          _ = y * q := by group
    have hCP : Nat.card ↥((T ⊓ K) ⊓ centralizer ({y} : Set G)) ≤ 2 := by
      obtain ⟨p, hp, hpy⟩ := not_centralizes_PL hh hKN hsL hnL e5 hyT hyR
      refine card_le_two_of_lt_four hP4 inf_le_left (fun h => hpy ?_)
      have hpc : p ∈ (T ⊓ K) ⊓ centralizer ({y} : Set G) := by rw [h]; exact hp
      have := mem_centralizer_singleton_iff.1 hpc.2
      calc y * p * y⁻¹ = (p * y) * y⁻¹ := by rw [← this]
        _ = p := by group
    have hprod : Nat.card ↥(R ⊓ centralizer ({y} : Set G)) ≤
        Nat.card ↥((T ⊓ K) ⊓ centralizer ({y} : Set G)) * Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) := by
      let f : ↥((T ⊓ K) ⊓ centralizer ({y} : Set G)) × ↥(Q ⊓ centralizer ({y} : Set G)) →
          ↥(R ⊓ centralizer ({y} : Set G)) := fun pq =>
        ⟨(pq.1 : G) * (pq.2 : G), ⟨Subgroup.mul_mem_sup pq.1.2.1 (pq.2.2.1), by
          have h1 := mem_centralizer_singleton_iff.1 pq.1.2.2
          have h2 := mem_centralizer_singleton_iff.1 pq.2.2.2
          refine mem_centralizer_singleton_iff.2 ?_
          calc (pq.1 : G) * pq.2 * y = pq.1 * (y * pq.2) := by rw [← h2, mul_assoc]
            _ = (y * pq.1) * pq.2 := by rw [← h1, mul_assoc]
            _ = y * (pq.1 * pq.2) := by rw [mul_assoc]⟩⟩
      have hf : Function.Surjective f := by
        rintro ⟨r, hr⟩
        obtain ⟨p, hp, q, hq, hpq⟩ := hdec r hr
        exact ⟨⟨⟨p, hp⟩, ⟨q, hq⟩⟩, Subtype.ext hpq⟩
      have := Nat.card_le_card_of_surjective f hf
      rwa [Nat.card_prod] at this
    have hCQ : Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) = 4 := by
      have h1 : 4 ≤ Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) := by
        by_contra hlt
        push Not at hlt
        have : Nat.card ↥(R ⊓ centralizer ({y} : Set G)) ≤ 2 * 3 :=
          hprod.trans (Nat.mul_le_mul hCP (by omega))
        omega
      have h2 : Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) ≤ 4 := hQ4 ▸ Subgroup.card_le_of_le inf_le_left
      omega
    have hQy : Q ⊓ centralizer ({y} : Set G) = Q :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hCQ, hQ4])
    have hyQ : ∀ q ∈ Q, y * q = q * y := fun q hq => by
      have : q ∈ Q ⊓ centralizer ({y} : Set G) := by rw [hQy]; exact hq
      exact (mem_centralizer_singleton_iff.1 this.2).symm
    have hTQc : ∀ t ∈ T, ∀ q ∈ Q, t * q = q * t := by
      intro t ht q hq
      by_cases htR : t ∈ R
      · exact hRab t htR q (hQR hq)
      · have hcos : y⁻¹ * t ∈ R :=
          mem_of_index_le_two hRT (by omega) ht hyT htR hyR
        have e : t = y * (y⁻¹ * t) := by group
        calc t * q = y * (y⁻¹ * t) * q := by rw [← e]
          _ = y * (q * (y⁻¹ * t)) := by rw [mul_assoc, hRab _ hcos q (hQR hq)]
          _ = (y * q) * (y⁻¹ * t) := by rw [mul_assoc]
          _ = (q * y) * (y⁻¹ * t) := by rw [hyQ q hq]
          _ = q * t := by rw [mul_assoc]; congr 1; group
    have hQZ : ∀ q ∈ Q, ∀ t ∈ closure {u : G | u ∈ T ∧ u * u = 1}, q * t = t * q := by
      intro q hq t ht
      have hle : closure {u : G | u ∈ T ∧ u * u = 1} ≤ centralizer ({q} : Set G) := by
        rw [Subgroup.closure_le]
        intro u hu
        exact mem_centralizer_singleton_iff.2 (hTQc u hu.1 q hq)
      exact (mem_centralizer_singleton_iff.1 (hle ht)).symm
    exact hTR (hL112 hQZ).symm

theorem lemma113a_five
    (h81 : B_iv2_8_1) (h92 : B_lemma92) (hG : C3Hyp G)
    (hh : Hyp9A x K L M T Q) (p91 : Prop91Concl K M T Q)
    (e5 : kBar K ≃* alternatingGroup (Fin 5)) (hT : IsSylowOf 2 T ⊤) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 ↥T := hh.sylowT.isPGroup
  have hQT : Q ≤ T := Setup91.Q_le_T hh
  have hTC : T ≤ centralizer ({x} : Set G) := hh.sylowT.le
  have hcases := kBar_cases p91
  have hlist := hlist_of_cases hcases
  have hs : IsSimpleGroup (kBar K) := by
    rcases hlist with h | h
    · exact isSimpleGroup_of_hasL2Model h
    · exact isSimpleGroup_of_alt7 h
  have hn : ∃ a b : kBar K, a * b ≠ b * a :=
    nonab_of_quasisimple (TwoThin.isQuasisimple_hat hh.twoTerminal.1.2.2)
  obtain ⟨eKL⟩ := hh.kBar_equiv
  have hsL : IsSimpleGroup (kBar L) := by
    have := hs
    exact eKL.symm.isSimpleGroup
  have hnL : ∃ a b : kBar L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hn
    exact ⟨eKL a, eKL b, fun h => hab (eKL.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hlistL : HasL2Model (kBar L) Odd ∨ Nonempty (kBar L ≃* alternatingGroup (Fin 7)) := by
    rcases hlist with h | h
    · exact Or.inl (TwoThin.hasL2Model_of_mulEquiv eKL h)
    · obtain ⟨e7⟩ := h
      exact Or.inr ⟨eKL.symm.trans e7⟩
  have heven : 2 ∣ Nat.card ↥K := by
    obtain ⟨a, ha⟩ := exists_involution_of_model hlist
    have hd : 2 ∣ Nat.card (kBar K) := by
      have := orderOf_dvd_natCard a
      rwa [ha] at this
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)]
    exact Dvd.dvd.mul_right hd _
  have hKN := hh.K_normal hsL hnL heven
  have p91' := p91
  obtain ⟨hQe, ⟨g, hgM, hgR, hgQ⟩, -, -⟩ := p91'
  obtain ⟨hR, hcomm, hPQ⟩ := hh.R_eq hsL hnL
  have hCD : CommDisj (T ⊓ K) Q := ⟨hcomm, hPQ⟩
  have hP4 : Nat.card ↥(T ⊓ K) = 4 := card_P_five hh e5
  have hQ4 : Nat.card ↥Q = 4 := hQe.2
  obtain ⟨hQab, hQsq⟩ := forall_of_isElementaryAbelian hQe.1
  have hPsq : ∀ p ∈ T ⊓ K, p * p = 1 := by
    intro p hp
    have hp4 : p ^ 4 = 1 := by
      have h1 : (⟨p, hp⟩ : ↥(T ⊓ K)) ^ Nat.card ↥(T ⊓ K) = 1 := pow_card_eq_one'
      rw [hP4] at h1
      have h2 := congrArg (fun y : ↥(T ⊓ K) => (y : G)) h1
      simpa using h2
    have hpK : p ∈ K := hp.2
    have h3 : (QuotientGroup.mk (⟨p, hpK⟩ : ↥K) : kBar K) ^ 4 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨p, hpK⟩ : ↥K) ^ 4 = 1 := Subtype.ext (by simpa using hp4)
      rw [this]; rfl
    have h4 := a5_no_order_four e5 _ h3
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h4
    have hO : p ^ 2 ∈ pPrimeCoreOf 2 K := by
      refine Setup91.mem_pPrimeCoreOf_iff.2 ⟨K.pow_mem hpK 2, ?_⟩
      exact h4
    have hmem : p ^ 2 ∈ T ⊓ pPrimeCoreOf 2 K := ⟨T.pow_mem hp.1 2, hO⟩
    rw [Setup91.inf_pPrimeCoreOf_eq_bot K hTp, Subgroup.mem_bot] at hmem
    rw [← sq]; exact hmem
  have hPab : ∀ a ∈ T ⊓ K, ∀ b ∈ T ⊓ K, a * b = b * a := by
    intro a ha b hb
    have hab := hPsq (a * b) ((T ⊓ K).mul_mem ha hb)
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hPsq a ha)
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hPsq b hb)
    have habinv : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
    calc a * b = (a * b)⁻¹ := habinv.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hainv, hbinv]
  have hR16 : Nat.card ↥((T ⊓ K) ⊔ Q) = 16 := by
    rw [Setup91.card_sup_Q hh hsL hnL, hP4, hQ4]
  have hRT : (T ⊓ K) ⊔ Q ≤ T := sup_le inf_le_left hQT
  have hQR : Q ≤ (T ⊓ K) ⊔ Q := le_sup_right
  have hRab := abelian_sup_of_commDisj hCD hPab hQab
  have hPn : ∀ t ∈ T, ∀ p ∈ T ⊓ K, t * p * t⁻¹ ∈ T ⊓ K := fun t ht p hp =>
    ⟨T.mul_mem (T.mul_mem ht hp.1) (T.inv_mem ht), hKN t (hTC ht) p hp.2⟩
  have hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := fun t ht q hq => by
    have h1 : t * q * t⁻¹ ∈ T ⊓ CxK x K :=
      ⟨T.mul_mem (T.mul_mem ht (hQT hq)) (T.inv_mem ht),
        conj_mem_CMK hKN (hTC ht) (mem_CxK_of_mem_Q hh hq)⟩
    rwa [← hh.hQ] at h1
  have hTN : T ≤ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) := fun t ht =>
    mem_normalizer_of_conj_le (fun r hr => by
      obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_of_commute hcomm hr
      have e : t * (p * q) * t⁻¹ = (t * p * t⁻¹) * (t * q * t⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hPn t ht p hp))
        (Subgroup.mem_sup_right (hQn t ht q hq)))
  have hT32 : Nat.card ↥T ≤ 32 := by
    obtain ⟨ψ, hψ⟩ := lemma113d_ne6 (K := K) (M := centralizer ({x} : Set G))
      hh.K_le_centralizer hKN (n := 5) (by norm_num) (by norm_num) e5
    have := card_T_leL hh ψ hψ
    rw [hQ4] at this
    omega
  have hL112 : (∀ q ∈ Q, ∀ t ∈ closure {u : G | u ∈ T ∧ u * u = 1}, q * t = t * q) →
      (T ⊓ K) ⊔ Q = T := fun hQZ => (lemma112L h81 h92 hG hh p91 hQZ).2
  have hweak := fun g' hg' => five_weak_closure hh hKN hsL hnL e5 hP4 hQ4 hR16 hRab hCD hPn hQn
    hT32 hL112 g' hg'
  have hux : g⁻¹ * x * g ∈ conjugate Q g := by
    rw [mem_conjugate_iff']
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e]; exact hh.x_mem_Q
  have huxR : g⁻¹ * x * g ∈ (T ⊓ K) ⊔ Q := hgR hux
  have hxR : x ∈ (T ⊓ K) ⊔ Q := hQR hh.x_mem_Q
  have hweak' : ∀ g' : G, ((T ⊓ K) ⊔ Q).map (MulAut.conj g').toMonoidHom ≤ T →
      ((T ⊓ K) ⊔ Q).map (MulAut.conj g').toMonoidHom = (T ⊓ K) ⊔ Q := hweak
  obtain ⟨n, hnN, hn'⟩ := CFSG.GH74.GLS.C3.Layer2.L5.burnside_weak T ((T ⊓ K) ⊔ Q) hTp (isSylowOf_iff.1 hT)
    hRT hRab hweak' (g⁻¹ * x * g) huxR g⁻¹ (by
      have e : (g⁻¹)⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [e]; exact hxR)
  have hnM : n ∉ M := by
    intro hnM
    apply hgM
    have e : (g⁻¹)⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e] at hn'
    have hgnC : g * n ∈ centralizer ({x} : Set G) := by
      refine mem_centralizer_singleton_iff.2 ?_
      calc g * n * x = g * n * (n⁻¹ * (g⁻¹ * x * g) * n) := by rw [hn']
        _ = x * (g * n) := by
          have : g * n * (n⁻¹ * (g⁻¹ * x * g) * n) = x * g * n := by group
          rw [this]; group
    have hgnM : g * n ∈ M := hh.centralizer_le hgnC
    have : g = (g * n) * n⁻¹ := by group
    rw [this]
    exact M.mul_mem hgnM (M.inv_mem hnM)
  have hTIaux := fun n' (hn'' : n' ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G)) =>
    five_TI_aux hh hG.kproper h81 h92 hlistL hQ4 hRT hQR hn''
  have hTI : ∀ n' ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G), conjugate Q n' ≠ Q →
      conjugate Q n' ⊓ Q = ⊥ := fun n' hn'' hne => by
    by_cases hn'M : n' ∈ M
    · exact absurd ((hTIaux n' hn'').1 hn'M) hne
    · exact (hTIaux n' hn'').2 hn'M
  have hex : ∃ n' ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G), conjugate Q n' ≠ Q := by
    refine ⟨n, hnN, fun hcon => ?_⟩
    have h1 : conjugate Q n ⊓ Q = ⊥ := (hTIaux n hnN).2 hnM
    rw [hcon, inf_idem] at h1
    have h2 : Nat.card ↥Q = 1 := by rw [h1, Subgroup.card_bot]
    omega
  have hR2 : IsPGroup 2 ↥((T ⊓ K) ⊔ Q) := IsPGroup.of_card (n := 4) (by rw [hR16]; norm_num)
  obtain ⟨w, hwK, hw3, hwR, hwQ, hwfpf⟩ := five_w hh hKN e5 hCD hR2
  have hwP : ∀ p ∈ T ⊓ K, w * p * w⁻¹ ∈ T ⊓ K := by
    intro p hp
    have h1 : w * p * w⁻¹ ∈ (T ⊓ K) ⊔ Q :=
      (Subgroup.mem_normalizer_iff.1 hwR p).1 (Subgroup.mem_sup_left hp)
    exact ⟨hRT h1, K.mul_mem (K.mul_mem hwK hp.2) (K.inv_mem hwK)⟩
  exact five_orbit_false hCD hP4 hQ4 hPab hQab hR16 hT hTN hQn hT32 hTI hex hwR hwP hwQ hwfpf hw3

end CFSG.GH74.GLS.C3.Layer1.Bk
