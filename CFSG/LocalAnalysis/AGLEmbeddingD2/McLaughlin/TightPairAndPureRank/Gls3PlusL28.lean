module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusLieOffCharAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L28AutThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SeitzSurvivor
public import CFSG.Dihedral.Glauberman.DicksonMaxExist
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneData

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.L28Local CFSG.RankThree.PartOne.Census3
  CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

section Abstract

variable {G : Type*} [Group G] [Finite G] {T : Subgroup G}

theorem l28_exists_inverter (h : L28Data G T) :
    ∃ w : G, w ∈ Subgroup.normalizer (T : Set G) ∧ w ∉ T ∧ w * w = 1 ∧
      ∀ c ∈ T, w * c * w⁻¹ = c⁻¹ := by
  obtain ⟨s, hsN, hs⟩ := h.inv
  set N := Subgroup.normalizer (T : Set G) with hN
  have hTN : T ≤ N := Subgroup.le_normalizer
  have hidx : (T.subgroupOf N).index = 2 := by
    have hcard : Nat.card (T.subgroupOf N) = 9 := by
      rw [← h.card_eq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
    have := (T.subgroupOf N).index_mul_card
    rw [hcard, h.card_normalizer] at this
    omega
  have hs2 : s ^ 2 ∈ T := by
    have := Subgroup.mul_self_mem_of_index_two hidx (⟨s, hsN⟩ : N)
    rw [pow_two]
    exact Subgroup.mem_subgroupOf.mp this
  have hσT : ∀ y ∈ T, s * y * s⁻¹ ∈ T := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hsN y).mp hy
  have hinv : ∀ x ∈ T, s * x * s⁻¹ = x⁻¹ := by
    intro x hx
    have hσ : ∀ y ∈ T, s * (s * y * s⁻¹) * s⁻¹ = y := by
      intro y hy
      have hc : s ^ 2 * y = y * s ^ 2 := h.commute _ hs2 y hy
      calc s * (s * y * s⁻¹) * s⁻¹ = s ^ 2 * y * (s ^ 2)⁻¹ := by simp only [pow_two]; group
        _ = y := by rw [hc]; group
    have hfix : s * (x * (s * x * s⁻¹)) * s⁻¹ = x * (s * x * s⁻¹) := by
      calc s * (x * (s * x * s⁻¹)) * s⁻¹
          = (s * x * s⁻¹) * (s * (s * x * s⁻¹) * s⁻¹) := by group
        _ = (s * x * s⁻¹) * x := by rw [hσ x hx]
        _ = x * (s * x * s⁻¹) := h.commute _ (hσT x hx) x hx
    have h1 : x * (s * x * s⁻¹) = 1 := hs _ (mul_mem hx (hσT x hx)) hfix
    exact eq_inv_of_mul_eq_one_right h1
  have hs9 : s ^ 9 = s * (s ^ 2) ^ 4 := by group
  refine ⟨s ^ 9, ?_, ?_, ?_, ?_⟩
  · rw [hs9]
    exact mul_mem hsN (pow_mem (hTN hs2) 4)
  · intro hw
    rw [hs9] at hw
    have hsT : s ∈ T := by
      have h4 : (s ^ 2) ^ 4 ∈ T := pow_mem hs2 4
      have := mul_mem hw (inv_mem h4)
      simpa using this
    obtain ⟨t, ht, ht1⟩ := h.exists_ne_one
    refine ht1 (hs t ht ?_)
    calc s * t * s⁻¹ = t * s * s⁻¹ := by rw [h.commute s hsT t ht]
      _ = t := by group
  · have h9 : (s ^ 2) ^ 9 = 1 := h.pow_nine_eq_one hs2
    calc s ^ 9 * s ^ 9 = (s ^ 2) ^ 9 := by group
      _ = 1 := h9
  · intro c hc
    have h4 : (s ^ 2) ^ 4 ∈ T := pow_mem hs2 4
    have hcomm : (s ^ 2) ^ 4 * c = c * (s ^ 2) ^ 4 := h.commute _ h4 c hc
    rw [hs9]
    calc s * (s ^ 2) ^ 4 * c * (s * (s ^ 2) ^ 4)⁻¹
        = s * ((s ^ 2) ^ 4 * c) * ((s ^ 2) ^ 4)⁻¹ * s⁻¹ := by group
      _ = s * (c * (s ^ 2) ^ 4) * ((s ^ 2) ^ 4)⁻¹ * s⁻¹ := by rw [hcomm]
      _ = s * c * s⁻¹ := by group
      _ = c⁻¹ := hinv c hc

theorem l28_isCyclic (h : L28Data G T)
    (hrk : ∀ E : Subgroup G, CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 3) : IsCyclic T := by
  by_contra hnc
  have hall : ∀ x ∈ T, x ^ 3 = 1 := by
    intro x hx
    by_contra hx3
    apply hnc
    have h9 : orderOf (⟨x, hx⟩ : T) ∣ 9 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact Subtype.ext (by simpa using h.pow_nine_eq_one hx)
    have hnot3 : ¬ orderOf (⟨x, hx⟩ : T) ∣ 3 := by
      intro h3
      rw [orderOf_dvd_iff_pow_eq_one] at h3
      exact hx3 (by simpa using congrArg Subtype.val h3)
    have : orderOf (⟨x, hx⟩ : T) = 9 := by
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
        (show orderOf (⟨x, hx⟩ : T) ∣ 3 ^ 2 from h9)
      interval_cases k
      · exact absurd (by rw [hk']; norm_num) hnot3
      · exact absurd (by rw [hk']; norm_num) hnot3
      · simpa using hk'
    exact isCyclic_of_orderOf_eq_card (⟨x, hx⟩ : T) (by rw [this, h.card_eq])
  have hel : CFSG.Open.IsElemAbelian 3 T :=
    ⟨⟨⟨fun a b => Subtype.ext (h.commute a a.2 b b.2)⟩⟩, hall⟩
  have := hrk T hel
  rw [h.card_eq] at this
  omega

end Abstract

section XLevel

variable {X : Type} [Group X] [Finite X] {K : Subgroup X}

theorem l28_gammaCore_eq (T : Subgroup K) (hd : L28Data K T) :
    gammaCore 3 1 K (T.map K.subtype) = (Subgroup.normalizer (T : Set K)).map K.subtype := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  · rw [gammaCore, Subgroup.closure_le]
    rintro x ⟨hxK, R, hRQ, hrk, hxR⟩
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    have hR : R ≠ ⊥ := ne_bot_of_one_le_pRank' (by norm_num) hrk
    obtain ⟨r, hr⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR
    obtain ⟨t, ht, htr⟩ := hRQ r.2
    have hxr : x * (r : X) * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hxR r).mp r.2
    obtain ⟨t', ht', ht'r⟩ := hRQ hxr
    have ht1 : t ≠ 1 := by
      rintro rfl
      exact hr (Subtype.ext (by simpa using htr.symm))
    have hconj : (⟨x, hxK⟩ : K) * t * (⟨x, hxK⟩ : K)⁻¹ = t' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show (t : X) = r from htr, show (t' : X) = x * r * x⁻¹ from ht'r]
    have hmem : ((⟨x, hxK⟩ : K)⁻¹)⁻¹ * t * (⟨x, hxK⟩ : K)⁻¹ ∈ T := by
      rw [inv_inv, hconj]; exact ht'
    have := hd.mem_normalizer_of_conj_mem ht ht1 hmem
    simpa using Subgroup.inv_mem _ this
  · rintro _ ⟨k, hk, rfl⟩
    refine Subgroup.subset_closure ⟨k.2, T.map K.subtype, le_rfl, ?_, ?_⟩
    · have h1 := KFactProofs.GLBCoreNormalizer.one_le_pRank_of_dvd Nat.prime_three
        (T := T) (by rw [hd.card_eq]; norm_num)
      exact h1.trans (pRank_le_pRank_map (by norm_num) K.subtype K.subtype_injective T)
    · rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨t, ht, rfl⟩
        have := (Subgroup.mem_normalizer_iff.mp hk t).mp ht
        exact ⟨k * t * k⁻¹, this, rfl⟩
      · rintro ⟨t', ht', hh⟩
        have hk' : k⁻¹ ∈ Subgroup.normalizer (T : Set K) := Subgroup.inv_mem _ hk
        have := (Subgroup.mem_normalizer_iff.mp hk' t').mp ht'
        refine ⟨k⁻¹ * t' * k, ?_, ?_⟩
        · simpa using this
        · have h1 : (t' : X) = (k : X) * h * (k : X)⁻¹ := by
            exact hh
          calc ((k⁻¹ * t' * k : K) : X) = (k : X)⁻¹ * (t' : X) * (k : X) := rfl
            _ = h := by rw [h1]; group

end XLevel

section Main

theorem isoLie_A1_two_three (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower)
    (hq2 : q.p = 2) (hq3 : q.exponent = 3) (hd : d.1 = .A 1 q) {Y : Type} [Group Y]
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) :
    IsoLie Y (.A 1 ⟨2, 3, Nat.prime_two, by norm_num⟩) := by
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  rcases q with ⟨p, k, hp, hk⟩
  simp only at hq2 hq3
  subst hq2 hq3
  exact ⟨hv, ⟨e⟩⟩

theorem gls3ConclusionPlus_lie_L28 (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower)
    (hq2 : q.p = 2) (hq3 : q.exponent = 3) (hd : d.1 = .A 1 q) {X : Type} [Group X] [Finite X]
    {K : Subgroup X} (hKn : K.Normal) (hiso : Nonempty (↥K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hKc : Subgroup.centralizer (K : Set X) = ⊥) (P : Sylow 3 X)
    (hP : 2 ≤ CFSG.Open.pRank 3 (P : Subgroup X)) : Gls3ConclusionPlus X K (P : Subgroup X) := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hiso
  have hK2 : IsCaseTwoGroup 3 ↥K := ⟨d, Or.inl ⟨rfl, q, hq2, hq3, hd⟩, ⟨e⟩⟩
  obtain ⟨ε₀⟩ := nonempty_equiv_G8 hK2
  have hdata : ∀ T : Sylow 3 ↥K, L28Data ↥K (T : Subgroup ↥K) := fun T => l28Data_of_equiv ε₀ T
  have hrk1 : ∀ E : Subgroup ↥K, CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 3 := by
    have := (CFSG.AGLEmbeddingD2.linTwoEight_data d q hq2 hq3 hd e).2
    exact fun E hE => this E ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).2 hE)
  have hKcard : Nat.card ↥K = 504 := by rw [Nat.card_congr ε₀.toEquiv, CFSG.Quasithin.F6.L28Res.card_G8]
  have hAut : Nat.card (MulAut ↥K) = 1512 := card_mulAut_of_isCaseTwoGroup_three hK2
  have hψ : Function.Injective (MulAut.conjNormal : X →* MulAut ↥K) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := congrArg (fun f : MulAut ↥K => (f ⟨k, hk⟩ : X)) hx
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      have h2 : x * k * x⁻¹ = k := this
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    rw [hKc] at hxc
    exact Subgroup.mem_bot.mp hxc
  have hmemK : ∀ (x : X) (k : ↥K), (MulAut.conjNormal : X →* MulAut ↥K) x = MulAut.conj k →
      x ∈ K := by
    intro x k hk
    have : (MulAut.conjNormal : X →* MulAut ↥K) x =
        (MulAut.conjNormal : X →* MulAut ↥K) (k : X) := by
      rw [hk]
      ext y
      simp [MulAut.conjNormal_apply, MulAut.conj_apply]
    rw [hψ this]
    exact k.2
  have hXdvd : Nat.card X ∣ 1512 := by
    rw [← hAut]
    exact Subgroup.card_dvd_of_injective _ hψ
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal (G := X) (p := 3) P (N := K)
  have hmapT : (T : Subgroup ↥K).map K.subtype = (P : Subgroup X) ⊓ K := by
    rw [hT, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr inf_le_right
  set Q : Subgroup X := (P : Subgroup X) ⊓ K with hQ
  have hTd := hdata T
  have hTcard : Nat.card (T : Subgroup ↥K) = 9 := hTd.card_eq
  have hQcard : Nat.card Q = 9 := by
    rw [← hmapT, Subgroup.card_map_of_injective K.subtype_injective, hTcard]
  obtain ⟨E₀, hE₀P, hE₀el, hE₀c⟩ := exists_elemAbelian_card_sq Nat.prime_three hP
  have hnotK : ¬ E₀ ≤ K := by
    intro hle
    set F : Subgroup ↥K := E₀.subgroupOf K with hF
    have hFel : CFSG.Open.IsElemAbelian 3 F := by
      refine ⟨⟨⟨?_⟩⟩, ?_⟩
      · rintro ⟨x, hx⟩ ⟨y, hy⟩
        apply Subtype.ext
        apply Subtype.ext
        have := congrArg Subtype.val (hE₀el.1.is_comm.comm ⟨(x : X), hx⟩ ⟨(y : X), hy⟩)
        exact this
      · intro x hx
        exact Subtype.ext (by simpa using hE₀el.2 (x : X) hx)
    have hFc : Nat.card F = 3 ^ 2 := by
      rw [← hE₀c]
      have hm : F.map K.subtype = E₀ := by
        rw [hF, Subgroup.subgroupOf_map_subtype]; exact inf_eq_left.mpr hle
      rw [← hm, Subgroup.card_map_of_injective K.subtype_injective]
    have := hrk1 F hFel
    rw [hFc] at this
    omega
  have hidx : K.index = 3 := by
    have hmul := K.index_mul_card
    rw [hKcard] at hmul
    have hdvd : K.index ∣ 3 := by
      have : K.index * 504 ∣ 1512 := hmul ▸ hXdvd
      have h3 : K.index * 504 ∣ 3 * 504 := by simpa using this
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h3
    have hne : K.index ≠ 1 := by
      intro h1
      exact hnotK (by rw [Subgroup.index_eq_one.mp h1]; exact le_top)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  have hXcard : Nat.card X = 1512 := by
    have hmul := K.index_mul_card
    rw [hKcard, hidx] at hmul
    omega
  have hPcard : Nat.card (P : Subgroup X) = 27 := by
    rw [Sylow.card_eq_multiplicity, hXcard]
    have : (1512 : ℕ).factorization 3 = 3 := by
      rw [show (1512 : ℕ) = 3 ^ 3 * 56 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [this]; norm_num
  have hTcyc : IsCyclic (T : Subgroup ↥K) := l28_isCyclic hTd hrk1
  have hQcyc : IsCyclic Q := by
    let eQ : (T : Subgroup ↥K) ≃* Q :=
      (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).trans
        (MulEquiv.subgroupCongr hmapT)
    exact isCyclic_of_surjective eQ.toMonoidHom eQ.surjective
  have hQmem : ∀ k : ↥K, (k : X) ∈ Q ↔ k ∈ (T : Subgroup ↥K) := fun k => by
    rw [← hmapT]
    exact Subgroup.mem_map_iff_mem K.subtype_injective
  have hnormiff : ∀ k : ↥K, (k : X) ∈ Subgroup.normalizer (Q : Set X) ↔
      k ∈ Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) := by
    intro k
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro hk t
      exact (hQmem t).symm.trans ((hk (t : X)).trans (hQmem (k * t * k⁻¹)))
    · intro hk h
      by_cases hhK : h ∈ K
      · exact (hQmem ⟨h, hhK⟩).trans ((hk ⟨h, hhK⟩).trans (hQmem (k * ⟨h, hhK⟩ * k⁻¹)).symm)
      · have h1 : h ∉ Q := fun hh => hhK (Subgroup.mem_inf.mp hh).2
        have h2 : (k : X) * h * (k : X)⁻¹ ∉ Q := by
          intro hh
          have hh' : (k : X) * h * (k : X)⁻¹ ∈ K := (Subgroup.mem_inf.mp hh).2
          apply hhK
          have := hKn.conj_mem _ hh' (k : X)⁻¹
          have e : (k : X)⁻¹ * ((k : X) * h * (k : X)⁻¹) * ((k : X)⁻¹)⁻¹ = h := by group
          rwa [e] at this
        exact ⟨fun hh => absurd hh h1, fun hh => absurd hh h2⟩
  set Γ : Subgroup X := (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)).map K.subtype with hΓdef
  have hΓeq : gammaCore 3 1 K Q = Γ := by
    have := l28_gammaCore_eq (K := K) (T : Subgroup ↥K) hTd
    rwa [hmapT] at this
  have hΓK : K ⊓ Subgroup.normalizer (Q : Set X) = Γ := by
    ext x
    constructor
    · rintro ⟨hxK, hxN⟩
      exact ⟨⟨x, hxK⟩, (hnormiff ⟨x, hxK⟩).mp hxN, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, (hnormiff k).mpr hk⟩
  have hΓcard : Nat.card Γ = 18 := by
    rw [hΓdef, Subgroup.card_map_of_injective K.subtype_injective, hTd.card_normalizer]
  have hΓK_le : Γ ≤ K := Subgroup.map_subtype_le _
  obtain ⟨w, hwN, hwT, hw2, hwinv⟩ := l28_exists_inverter hTd
  have hwQ : (w : X) ∉ Q := fun hh => hwT ((hQmem w).mp hh)
  have hw2X : (w : X) * (w : X) = 1 := congrArg Subtype.val hw2
  have hwinvX : ∀ c ∈ Q, (w : X) * c * (w : X)⁻¹ = c⁻¹ := by
    intro c hc
    rw [← hmapT] at hc
    obtain ⟨t', ht', rfl⟩ := hc
    have := congrArg Subtype.val (hwinv t' ht')
    simpa using this
  obtain ⟨φ⟩ := CFSG.Glauberman.Dickson.nonempty_sup_zpowers_mulEquiv_dihedral Q hQcyc (w : X) hwQ hw2X hwinvX
  have hQΓ : Q ≤ Γ := by
    rw [← hmapT]
    exact Subgroup.map_mono Subgroup.le_normalizer
  have hwΓ : Subgroup.zpowers (w : X) ≤ Γ := by
    rw [Subgroup.zpowers_le]
    exact ⟨w, hwN, rfl⟩
  have hsupcard : Nat.card (Q ⊔ Subgroup.zpowers (w : X) : Subgroup X) = 18 := by
    rw [Nat.card_congr φ.toEquiv, hQcard]
    rw [Nat.card_eq_fintype_card, DihedralGroup.card]
  have hsup : Q ⊔ Subgroup.zpowers (w : X) = Γ :=
    Subgroup.eq_of_le_of_card_ge (sup_le hQΓ hwΓ) (by rw [hΓcard, hsupcard])
  have hD : Nonempty (↥(gammaCore 3 1 K Q) ≃* DihedralGroup (Nat.card Q)) :=
    ⟨(MulEquiv.subgroupCongr (hΓeq.trans hsup.symm)).trans φ⟩
  rw [hQcard] at hD
  have hnonab : ¬ (∀ a ∈ (P : Subgroup X), ∀ b ∈ (P : Subgroup X), a * b = b * a) := by
    intro hab
    obtain ⟨y, hyE, hyK⟩ := IsConcreteLE.not_le_iff_exists.mp hnotK
    have hyP : y ∈ (P : Subgroup X) := hE₀P hyE
    obtain ⟨t₀, -, hf⟩ := hTd.aut ((MulAut.conjNormal : X →* MulAut ↥K) y) (by
      intro x hx
      have hxP : (x : X) ∈ (P : Subgroup X) := (inf_le_left : Q ≤ P) ((hQmem x).mpr hx)
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have := hab y hyP x hxP
      calc y * (x : X) * y⁻¹ = (x : X) * y * y⁻¹ := by rw [this]
        _ = x := by group)
    exact hyK (hmemK y t₀ hf)
  have hIso := isoLie_A1_two_three d q hq2 hq3 hd e
  have hlt : gammaCore 3 1 K Q < K := by
    rw [hΓeq]
    refine lt_of_le_of_ne hΓK_le ?_
    intro h
    have h2 : Nat.card Γ = Nat.card K := by rw [h]
    rw [hΓcard, hKcard] at h2
    omega
  have hmax : ∀ H : Subgroup X, gammaCore 3 1 K Q < H → H ≤ K → H = K := by
    intro H hΓH hHK
    rw [hΓeq] at hΓH
    have hNY : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ H.subgroupOf K := by
      intro k hk
      exact hΓH.le ⟨k, hk, rfl⟩
    rcases hTd.maximal hNY with h | h
    · exfalso
      have : H = Γ := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hHK, h]
      exact (ne_of_lt hΓH) this.symm
    · refine le_antisymm hHK ?_
      intro x hx
      have : (⟨x, hx⟩ : ↥K) ∈ H.subgroupOf K := h ▸ Subgroup.mem_top _
      exact this
  refine ⟨hlt, hmax, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
  refine ⟨hIso, hidx, hQcyc, hQcard, ?_, hD, hPcard, hnonab⟩
  rw [hΓeq, ← hΓK]

theorem gls3PlusCase_lie_L28 (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower)
    (hq2 : q.p = 2) (hq3 : q.exponent = 3) (hd : d.1 = .A 1 q) : Gls3PlusCase (.lie d) := by
  unfold Gls3PlusCase
  intro X _ _ _ K hKn _ _ hiso hKc P hP _
  exact gls3ConclusionPlus_lie_L28 d q hq2 hq3 hd hKn hiso hKc P hP

end Main

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
