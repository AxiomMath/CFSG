module

public import CFSG.GH74.GLS.C3.Layer1.Th2P617D
public import CFSG.GH74.GLS.C3.Layer1.Th2P617E
public import CFSG.GroupTheory.PRankCommutingSup
public import CFSG.GH74.GLS.C3.Layer1.Th2L84
public import CFSG.GH74.GLS.C3.Layer1.BkA7Facts
public import CFSG.GH74.GLS.Bg.Pu5.L299Abs2

public section

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs
open scoped commutatorElement

namespace CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem Th2Std.T_le_normalizer (hG : C3Hyp G) (hs : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) : T ≤ normalizer (K : Set G) := by
  have hKN := hs.K_normal_A7 hG h7
  intro t ht
  refine C3.Layer1.P34.mem_normalizer_of_conj_le (fun a ha => ?_)
  have := hKN t⁻¹ ((centralizer ({x} : Set G)).inv_mem (hs.T_le_C ht)) a ha
  simpa using this

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.Th2.Obs

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

omit [Finite G] in
theorem actOn_T_eq_one_iff (hs : Th2Std x y K T S) (e : kBar K ≃* alternatingGroup (Fin 7))
    (hTN : T ≤ normalizer (K : Set G)) {t : G} (ht : t ∈ T) :
    actOn e hTN ⟨t, ht⟩ = 1 ↔ t ∈ T ⊓ CxK x K := by
  rw [actOn_eq_one_iff]
  exact ⟨fun h => ⟨ht, hs.T_le_C ht, h⟩, fun h => h.2.2⟩

omit [Finite G] in
theorem card_T_eq_card_Q_mul_range (hs : Th2Std x y K T S) (e : kBar K ≃* alternatingGroup (Fin 7))
    (hTN : T ≤ normalizer (K : Set G)) :
    Nat.card ↥T = Nat.card ↥(T ⊓ CxK x K) * Nat.card ↥(actOn e hTN).range := by
  have hker : (actOn e hTN).ker = (T ⊓ CxK x K).subgroupOf T := by
    ext ⟨t, ht⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, actOn_T_eq_one_iff hs e hTN ht]
  have hk : Nat.card ↥((T ⊓ CxK x K).subgroupOf T) = Nat.card ↥(T ⊓ CxK x K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : T ⊓ CxK x K ≤ T)).toEquiv
  have hcard := Subgroup.card_ker_mul_card_range (actOn e hTN)
  rw [hker, hk] at hcard
  exact hcard.symm

omit [Finite G] in
theorem card_range_le_sixteen (hT2 : IsPGroup 2 ↥T) {J : Subgroup G}
    (e : kBar J ≃* alternatingGroup (Fin 7)) (hTN : T ≤ normalizer (J : Set G)) :
    IsPGroup 2 ↥(actOn e hTN).range ∧ Nat.card ↥(actOn e hTN).range ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := actOn e hTN with hφ
  have hR : IsPGroup 2 ↥φ.range := IsPGroup.of_surjective hT2 φ.rangeRestrict φ.rangeRestrict_surjective
  refine ⟨hR, ?_⟩
  have := Th2.L627.card_le_twoPartCard hR (le_top : φ.range ≤ ⊤)
  have h5 : twoPartCard (⊤ : Subgroup (Perm (Fin 7))) = 16 := by
    unfold twoPartCard
    rw [Subgroup.card_top, show (Nat.card (Perm (Fin 7))).factorization 2 = 4 from
      A7.factorization_S7]
    norm_num
  omega


omit [Finite G] in
theorem actOn_P_apply (e : kBar K ≃* alternatingGroup (Fin 7)) (hTN : T ≤ normalizer (K : Set G))
    {p : G} (hp : p ∈ T ⊓ K) :
    actOn e hTN ⟨p, hp.1⟩ = ((e (QuotientGroup.mk (⟨p, hp.2⟩ : ↥K))) : Perm (Fin 7)) :=
  a7Act_of_mem e hp.2

omit [Finite G] in
theorem actOn_P_injective (hs : Th2Std x y K T S) (hcd : Th2.CommDisj (T ⊓ K) (T ⊓ CxK x K))
    (e : kBar K ≃* alternatingGroup (Fin 7)) (hTN : T ≤ normalizer (K : Set G)) :
    Function.Injective ((actOn e hTN).comp (Subgroup.inclusion (inf_le_left : T ⊓ K ≤ T))) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro p hp
  have hp1 : actOn e hTN ⟨(p : G), p.2.1⟩ = 1 := hp
  have hpQ : (p : G) ∈ T ⊓ CxK x K := (actOn_T_eq_one_iff hs e hTN p.2.1).1 hp1
  have : (p : G) = 1 := hcd.eq_one_of_mem p.2 hpQ
  exact Subgroup.mem_bot.2 (Subtype.ext this)

theorem card_alt7 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]


omit [Finite G] in
theorem actOn_even_of_mem_R (hcd : Th2.CommDisj (T ⊓ K) (T ⊓ CxK x K)) (hs : Th2Std x y K T S)
    (e : kBar K ≃* alternatingGroup (Fin 7)) (hTN : T ≤ normalizer (K : Set G)) {r : G}
    (hr : r ∈ (T ⊓ K) ⊔ (T ⊓ CxK x K)) (hrT : r ∈ T) :
    actOn e hTN ⟨r, hrT⟩ ∈ alternatingGroup (Fin 7) := by
  obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute hcd.comm hr
  have h1 : (⟨p * q, hrT⟩ : ↥T) = ⟨p, hp.1⟩ * ⟨q, hq.1⟩ := rfl
  rw [h1, map_mul, (actOn_T_eq_one_iff hs e hTN hq.1).2 hq, mul_one, actOn_P_apply e hTN hp]
  exact (e _).2

theorem range_inf_alt_eq (hs : Th2Std x y K T S) (hcd : Th2.CommDisj (T ⊓ K) (T ⊓ CxK x K))
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) (e : kBar K ≃* alternatingGroup (Fin 7))
    (hTN : T ≤ normalizer (K : Set G)) :
    ((actOn e hTN).comp (Subgroup.inclusion (inf_le_left : T ⊓ K ≤ T))).range =
        (actOn e hTN).range ⊓ alternatingGroup (Fin 7) ∧
      Nat.card ↥((actOn e hTN).range ⊓ alternatingGroup (Fin 7)) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := actOn e hTN with hψ
  set ψP := ψ.comp (Subgroup.inclusion (inf_le_left : T ⊓ K ≤ T)) with hψP
  have hinj : Function.Injective ψP := actOn_P_injective hs hcd e hTN
  have hcardP : Nat.card ↥ψP.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Th2.card_sylow_A7 hs.sylow_P h7
  have hle : ψP.range ≤ ψ.range ⊓ alternatingGroup (Fin 7) := by
    rintro _ ⟨p, rfl⟩
    refine ⟨⟨⟨p, p.2.1⟩, rfl⟩, ?_⟩
    show actOn e hTN ⟨(p : G), p.2.1⟩ ∈ alternatingGroup (Fin 7)
    rw [actOn_P_apply e hTN p.2]
    exact (e _).2
  have hR2 : IsPGroup 2 ↥ψ.range := (card_range_le_sixteen hs.T_pGroup e hTN).1
  have hI2 : IsPGroup 2 ↥(ψ.range ⊓ alternatingGroup (Fin 7)) := hR2.to_inf_left
  have hcardle : Nat.card ↥(ψ.range ⊓ alternatingGroup (Fin 7)) ≤ 8 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hI2
    have hdvd : Nat.card ↥(ψ.range ⊓ alternatingGroup (Fin 7)) ∣ 2520 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : ψ.range ⊓ alternatingGroup (Fin 7) ≤ alternatingGroup (Fin 7))
      rwa [card_alt7] at this
    rw [hn] at hdvd ⊢
    by_contra hcon
    push Not at hcon
    have h4 : 4 ≤ n := by
      by_contra h4
      push Not at h4
      interval_cases n <;> omega
    have : 2 ^ 4 ∣ 2 ^ n := Nat.pow_dvd_pow 2 h4
    have := this.trans hdvd
    norm_num at this
  have heq : ψP.range = ψ.range ⊓ alternatingGroup (Fin 7) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardP]; exact hcardle)
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact hcardP

theorem mem_R_of_actOn_even (hs : Th2Std x y K T S) (hcd : Th2.CommDisj (T ⊓ K) (T ⊓ CxK x K))
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) (e : kBar K ≃* alternatingGroup (Fin 7))
    (hTN : T ≤ normalizer (K : Set G)) {t : G} (ht : t ∈ T)
    (hev : actOn e hTN ⟨t, ht⟩ ∈ alternatingGroup (Fin 7)) :
    t ∈ (T ⊓ K) ⊔ (T ⊓ CxK x K) := by
  set ψ := actOn e hTN with hψ
  set ψP := ψ.comp (Subgroup.inclusion (inf_le_left : T ⊓ K ≤ T)) with hψP
  have heq := (range_inf_alt_eq hs hcd h7 e hTN).1
  have hmem : ψ ⟨t, ht⟩ ∈ ψP.range := by
    rw [heq]
    exact ⟨⟨⟨t, ht⟩, rfl⟩, hev⟩
  obtain ⟨p, hp⟩ := hmem
  have hptT : (p : G)⁻¹ * t ∈ T := T.mul_mem (T.inv_mem p.2.1) ht
  have h1 : ψ ⟨(p : G)⁻¹ * t, hptT⟩ = 1 := by
    have h2 : (⟨(p : G)⁻¹ * t, hptT⟩ : ↥T) = (⟨(p : G), p.2.1⟩ : ↥T)⁻¹ * ⟨t, ht⟩ := rfl
    rw [h2, map_mul, map_inv]
    have h3 : ψ ⟨(p : G), p.2.1⟩ = ψ ⟨t, ht⟩ := hp
    rw [h3]
    group
  have hq : (p : G)⁻¹ * t ∈ T ⊓ CxK x K := (actOn_T_eq_one_iff hs e hTN hptT).1 h1
  have : t = (p : G) * ((p : G)⁻¹ * t) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left p.2) (Subgroup.mem_sup_right hq)

omit [Finite G] in
theorem barAct_not_inn_of_odd {J : Subgroup G} (e : kBar J ≃* alternatingGroup (Fin 7))
    (m : ↥(normalizer (J : Set G))) (hodd : a7Act J e m ∉ alternatingGroup (Fin 7)) :
    barAct J m ∉ innAut (kBar J) := by
  intro hin
  obtain ⟨k, hk⟩ := hin
  have h2 : a7Act J e m = ((e k : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by
    show (Th2.Bal.a7Theta e).symm (barAct J m) = _
    rw [← hk]
    refine (Th2.Bal.a7Theta e).symm_apply_eq.2 ?_
    rw [Th2.Bal.a7Theta_even, e.symm_apply_apply]
  exact hodd (h2 ▸ (e k).2)

omit [Finite G] in
theorem inducesFAut_of_odd {J : Subgroup G} (e : kBar J ≃* alternatingGroup (Fin 7)) {f : G}
    (hf : f ∈ normalizer (J : Set G)) (hodd : a7Act J e ⟨f, hf⟩ ∉ alternatingGroup (Fin 7)) :
    C3.Layer1.P34.InducesFAutL2A7 f J := by
  have hα := barAct_not_inn_of_odd e ⟨f, hf⟩ hodd
  refine ⟨hf, ?_, Or.inr ⟨⟨e⟩, hα⟩⟩
  intro h1
  exact hα (by rw [show barAct J ⟨f, hf⟩ = 1 from h1]; exact one_mem _)


theorem isCentralInvolution_x_of_eq (hs : Th2Std x y K T S) (hTS : T = S) :
    IsCentralInvolution x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ↥T = 2 ^ (Nat.card G).factorization 2 := by
    have h1 := hs.sylowS.card_eq
    rw [Subgroup.card_top] at h1
    rw [hTS]
    exact h1
  exact isCentralInvolution_of_card hs.orderOf_x hs.x_mem_T
    (fun s hs' => mem_centralizer_singleton_iff.1 (hs.T_le_C hs')) hcard

theorem isMaximalClassTwoGroup_of_dihedral_four {Q : Type} [Group Q] [Finite Q]
    (hQ8 : Q ≃* DihedralGroup 4) : C3.Layer1.P34.IsMaximalClassTwoGroup Q := by
  have h := CFSG.GH74.GLS.Bg.Pu5.isNonabelianMaximalClass_dihedral (m := 2) (by norm_num)
  obtain ⟨hp, -, hnil, hcard⟩ := h
  have hD : C3.Layer1.P34.IsMaximalClassTwoGroup (DihedralGroup 4) := ⟨hp, hnil, hcard.symm⟩
  exact C3.Layer1.Thm1.isMaximalClassTwoGroup_of_equiv hQ8.symm hD

theorem mem_R_of_involution_local
    (hs : Th2Std x y K T S) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (e : kBar K ≃* alternatingGroup (Fin 7))
    (hTN : T ≤ normalizer (K : Set G))
    (hKn : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hSimple : IsSimpleGroup G) (hNonab : ∃ a b : G, a * b ≠ b * a)
    (hxCentral : IsCentralInvolution x)
    (hQ8 : Nonempty (↥(T ⊓ CxK x K) ≃* DihedralGroup 4))
    (hTS : T = S) {s : G} (hsT : s ∈ T) (hs2 : orderOf s = 2) :
    s ∈ (T ⊓ K) ⊔ (T ⊓ CxK x K) := by
  by_contra hR
  have hcen := centerlessBar_of_A7 h7
  have hcd := hs.commDisj hcen
  have hodd : a7Act K e ⟨s, hTN hsT⟩ ∉ alternatingGroup (Fin 7) := fun hev =>
    hR (mem_R_of_actOn_even hs hcd h7 e hTN hsT hev)
  have hind := inducesFAut_of_odd e (hTN hsT) hodd
  obtain ⟨e8⟩ := hQ8
  have hQmax : C3.Layer1.P34.IsMaximalClassTwoGroup ↥(T ⊓ CxK x K) :=
    isMaximalClassTwoGroup_of_dihedral_four e8
  have hyp : C3.Layer1.Bk.Prop34HypN G x K :=
    { simple := hSimple
      nonab := hNonab
      central := hxCentral
      comp := hs.comp
      normal := hKn
      shape := Or.inr h7
      sylowQ := ⟨T ⊓ CxK x K, hs.sylow_Q, Or.inr hQmax⟩ }
  exact C3.Layer1.Bk.prop34N_false hyp (hs.T_le_C hsT) hs2 hind

theorem T_le_normalizer_of_KN (hs : Th2Std x y K T S)
    (hKn : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) :
    T ≤ normalizer (K : Set G) := by
  intro t ht
  exact mem_normalizer_K_of_KN hKn (hs.T_le_C ht)

theorem mem_R_of_involution_of_KN
    (hs : Th2Std x y K T S) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (e : kBar K ≃* alternatingGroup (Fin 7))
    (hKn : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hSimple : IsSimpleGroup G) (hNonab : ∃ a b : G, a * b ≠ b * a)
    (hxCentral : IsCentralInvolution x)
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) ≤ 4) (hTS : T = S)
    {s : G} (hsT : s ∈ T) (hs2 : orderOf s = 2) :
    s ∈ (T ⊓ K) ⊔ (T ⊓ CxK x K) := by
  by_contra hR
  have hcen := centerlessBar_of_A7 h7
  have hcd := hs.commDisj hcen
  have hTN := T_le_normalizer_of_KN hs hKn
  have hodd : a7Act K e ⟨s, hTN hsT⟩ ∉ alternatingGroup (Fin 7) := fun hev =>
    hR (mem_R_of_actOn_even hs hcd h7 e hTN hsT hev)
  have hind := inducesFAut_of_odd e (hTN hsT) hodd
  have hyp : C3.Layer1.Bk.Prop34HypN G x K :=
    { simple := hSimple
      nonab := hNonab
      central := hxCentral
      comp := hs.comp
      normal := hKn
      shape := Or.inr h7
      sylowQ := ⟨T ⊓ CxK x K, hs.sylow_Q,
        isCyclic_or_isMaximalClass_of_card_le_four hs.sylow_Q.isPGroup hQ4⟩ }
  exact C3.Layer1.Bk.prop34N_false hyp (hs.T_le_C hsT) hs2 hind

theorem mem_R_of_involution
    (hG : C3Hyp G) (hs : Th2Std x y K T S) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (e : kBar K ≃* alternatingGroup (Fin 7)) (hQ4 : Nat.card ↥(T ⊓ CxK x K) ≤ 4) (hTS : T = S)
    {s : G} (hsT : s ∈ T) (hs2 : orderOf s = 2) : s ∈ (T ⊓ K) ⊔ (T ⊓ CxK x K) :=
  mem_R_of_involution_of_KN hs h7 e (hs.K_normal_A7 hG h7)
    hG.kproper.1 hG.kproper.2.1 (isCentralInvolution_x_of_eq hs hTS) hQ4 hTS hsT hs2


omit [Finite G] in
theorem Q_normal_in_T (hs : Th2Std x y K T S) (e : kBar K ≃* alternatingGroup (Fin 7))
    (hTN : T ≤ normalizer (K : Set G)) {t : G} (ht : t ∈ T) {q : G} (hq : q ∈ T ⊓ CxK x K) :
    t * q * t⁻¹ ∈ T ⊓ CxK x K := by
  have hT : t * q * t⁻¹ ∈ T := T.mul_mem (T.mul_mem ht hq.1) (T.inv_mem ht)
  refine (actOn_T_eq_one_iff hs e hTN hT).1 ?_
  have h1 : (⟨t * q * t⁻¹, hT⟩ : ↥T) = ⟨t, ht⟩ * ⟨q, hq.1⟩ * ⟨t, ht⟩⁻¹ := rfl
  rw [h1, map_mul, map_mul, map_inv, (actOn_T_eq_one_iff hs e hTN hq.1).2 hq, mul_one]
  group

theorem sign_eq_neg_one_of_not_mem_alt {σ : Perm (Fin 7)} (h : σ ∉ alternatingGroup (Fin 7)) :
    Equiv.Perm.sign σ = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h1) h
  · exact h1

theorem exists_odd_involution_coset (hs : Th2Std x y K T S)
    (hcd : Th2.CommDisj (T ⊓ K) (T ⊓ CxK x K)) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (e : kBar K ≃* alternatingGroup (Fin 7)) (hTN : T ≤ normalizer (K : Set G)) {s₀ : G}
    (hs₀T : s₀ ∈ T) (hs₀R : s₀ ∉ (T ⊓ K) ⊔ (T ⊓ CxK x K)) :
    ∃ t ∈ T, t ∉ (T ⊓ K) ⊔ (T ⊓ CxK x K) ∧ t * t ∈ T ⊓ CxK x K ∧
      (∀ s ∈ T, s ∉ (T ⊓ K) ⊔ (T ⊓ CxK x K) → s * t⁻¹ ∈ (T ⊓ K) ⊔ (T ⊓ CxK x K)) ∧
      ∀ p ∈ T ⊓ K, t * p = p * t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := actOn e hTN with hψ
  obtain ⟨hpg, hle16⟩ := card_range_le_sixteen hs.T_pGroup e hTN
  obtain ⟨-, hcard8⟩ := range_inf_alt_eq hs hcd h7 e hTN
  have hodd0 : ψ ⟨s₀, hs₀T⟩ ∉ alternatingGroup (Fin 7) := fun hev =>
    hs₀R (mem_R_of_actOn_even hs hcd h7 e hTN hs₀T hev)
  have hcard16 : Nat.card ↥ψ.range = 16 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hpg
    have hlt : Nat.card ↥(ψ.range ⊓ alternatingGroup (Fin 7)) < Nat.card ↥ψ.range := by
      by_contra hge
      push Not at hge
      have heq : ψ.range ⊓ alternatingGroup (Fin 7) = ψ.range :=
        Subgroup.eq_of_le_of_card_ge inf_le_left hge
      have hmem : ψ ⟨s₀, hs₀T⟩ ∈ ψ.range ⊓ alternatingGroup (Fin 7) := by
        rw [heq]; exact ⟨_, rfl⟩
      exact hodd0 hmem.2
    rw [hcard8, hn] at hlt
    rw [hn] at hle16 ⊢
    have hn4 : n = 4 := by
      have h3 : 3 < n := by
        by_contra h3
        push Not at h3
        interval_cases n <;> omega
      have h5 : n ≤ 4 := by
        by_contra h5
        push Not at h5
        have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h5
        omega
      omega
    rw [hn4]
    norm_num
  have hcardS : Nat.card ↥ψ.range = 2 ^ (Nat.card (Perm (Fin 7))).factorization 2 := by
    rw [hcard16, show (Nat.card (Perm (Fin 7))).factorization 2 = 4 from A7.factorization_S7]
    norm_num
  obtain ⟨f, hf2, hfcyc, hfmem, -, hfcomm, -⟩ := IVK.ivk_1_1T (Sylow.ofCard ψ.range hcardS)
  simp only [Sylow.coe_ofCard] at hfmem hfcomm
  have hfsign : Equiv.Perm.sign f = -1 := by
    rw [Equiv.Perm.sign_of_cycleType, hfcyc]
    simp
    decide
  have hff : f * f = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf2, sq] at this
  obtain ⟨⟨t, htT⟩, hft⟩ := hfmem
  have hft' : ψ ⟨t, htT⟩ = f := hft
  have htR : t ∉ (T ⊓ K) ⊔ (T ⊓ CxK x K) := by
    intro htR
    have := actOn_even_of_mem_R hcd hs e hTN htR htT
    rw [hft'] at this
    have h1 := Equiv.Perm.mem_alternatingGroup.1 this
    rw [hfsign] at h1
    exact absurd h1 (by decide)
  refine ⟨t, htT, htR, ?_, ?_, ?_⟩
  · refine (actOn_T_eq_one_iff hs e hTN (T.mul_mem htT htT)).1 ?_
    have h1 : (⟨t * t, T.mul_mem htT htT⟩ : ↥T) = ⟨t, htT⟩ * ⟨t, htT⟩ := rfl
    rw [h1, map_mul, hft', hff]
  · intro s hsT hsR
    have hodd : ψ ⟨s, hsT⟩ ∉ alternatingGroup (Fin 7) := fun hev =>
      hsR (mem_R_of_actOn_even hs hcd h7 e hTN hsT hev)
    have hsign := sign_eq_neg_one_of_not_mem_alt hodd
    have hstT : s * t⁻¹ ∈ T := T.mul_mem hsT (T.inv_mem htT)
    refine mem_R_of_actOn_even hs hcd h7 e hTN hstT ?_
    have h1 : (⟨s * t⁻¹, hstT⟩ : ↥T) = ⟨s, hsT⟩ * ⟨t, htT⟩⁻¹ := rfl
    rw [h1, map_mul, map_inv, hft', Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hsign,
      hfsign]
    decide
  · intro p hp
    have hpT : p ∈ T := hp.1
    have hψp : ψ ⟨p, hpT⟩ ∈ ψ.range ⊓ alternatingGroup (Fin 7) := by
      refine ⟨⟨_, rfl⟩, ?_⟩
      show actOn e hTN ⟨p, hp.1⟩ ∈ alternatingGroup (Fin 7)
      rw [actOn_P_apply e hTN hp]
      exact (e _).2
    have hcomm : ψ ⟨p, hpT⟩ * f = f * ψ ⟨p, hpT⟩ := hfcomm _ hψp
    have hctT : t * p * t⁻¹ * p⁻¹ ∈ T :=
      T.mul_mem (T.mul_mem (T.mul_mem htT hpT) (T.inv_mem htT)) (T.inv_mem hpT)
    have hψc : ψ ⟨t * p * t⁻¹ * p⁻¹, hctT⟩ = 1 := by
      have h1 : (⟨t * p * t⁻¹ * p⁻¹, hctT⟩ : ↥T) = ⟨t, htT⟩ * ⟨p, hpT⟩ * ⟨t, htT⟩⁻¹ * ⟨p, hpT⟩⁻¹ := rfl
      rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv, hft']
      calc f * ψ ⟨p, hpT⟩ * f⁻¹ * (ψ ⟨p, hpT⟩)⁻¹ = (f * ψ ⟨p, hpT⟩) * f⁻¹ * (ψ ⟨p, hpT⟩)⁻¹ := rfl
        _ = (ψ ⟨p, hpT⟩ * f) * f⁻¹ * (ψ ⟨p, hpT⟩)⁻¹ := by rw [hcomm]
        _ = 1 := by group
    have hcQ : t * p * t⁻¹ * p⁻¹ ∈ T ⊓ CxK x K := (actOn_T_eq_one_iff hs e hTN hctT).1 hψc
    have htpK : t * p * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hTN htT) p).1 hp.2
    have htpT : t * p * t⁻¹ ∈ T := T.mul_mem (T.mul_mem htT hpT) (T.inv_mem htT)
    have hcP : t * p * t⁻¹ * p⁻¹ ∈ T ⊓ K :=
      (T ⊓ K).mul_mem ⟨htpT, htpK⟩ ((T ⊓ K).inv_mem hp)
    have hc1 : t * p * t⁻¹ * p⁻¹ = 1 := hcd.eq_one_of_mem hcP hcQ
    calc t * p = (t * p * t⁻¹ * p⁻¹) * (p * t) := by group
      _ = p * t := by rw [hc1, one_mul]


private theorem open_pRank_eq_pRank (H : Subgroup G) :
    CFSG.Open.pRank 2 H = CFSG.pRank 2 ↥H := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup H,
    ← CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥H]

private theorem pRank_two_le_of_isD8 {P : Subgroup G} (hP : C3.Layer1.Bk.IsD8 P) :
    CFSG.Open.pRank 2 P ≤ 2 := by
  refine CFSG.SectionRank.pRank_le (p := 2) (H := P) (k := 2) (by norm_num) ?_
  intro E hEP hE
  have hE' : CFSG.IsElementaryAbelian 2 ↥E :=
    (CFSG.Open.isElemAbelian_iff_isElementaryAbelian (p := 2) (E := E)).mp hE
  calc Nat.card ↥E ≤ 4 := hP.card_le_four hEP hE'
    _ = 2 ^ 2 := by norm_num

theorem pRank_le_four_of_Q4_TS
    (hs : Th2Std x y K T S) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) (hTS : T = S)
    (hSimple : IsSimpleGroup G) (hNonab : ∃ a b : G, a * b ≠ b * a) :
    CFSG.pRank 2 G ≤ 4 := by
  classical
  let e7 : kBar K ≃* alternatingGroup (Fin 7) := Classical.choice h7
  have hKn := (Th2Std.K_normal_of_A7_card_Q_four hs e7 hQ4).2
  have hxCentral := isCentralInvolution_x_of_eq hs hTS
  have hD8 : C3.Layer1.Bk.IsD8 (T ⊓ K) :=
    C3.Layer1.Bk.isD8_of_inf_alt7 hs.T_pGroup hs.sylow_P e7
  have hPrank : CFSG.Open.pRank 2 (T ⊓ K) ≤ 2 := pRank_two_le_of_isD8 hD8
  have hQrank : CFSG.Open.pRank 2 (T ⊓ CxK x K) ≤ 2 := by
    refine CFSG.SectionRank.pRank_le (p := 2) (H := T ⊓ CxK x K) (k := 2) (by norm_num) ?_
    intro E hEQ hE
    have hE' : CFSG.IsElementaryAbelian 2 ↥E :=
      (CFSG.Open.isElemAbelian_iff_isElementaryAbelian (p := 2) (E := E)).mp hE
    calc Nat.card ↥E ≤ Nat.card ↥(T ⊓ CxK x K) := Subgroup.card_le_of_le hEQ
      _ = 4 := hQ4
      _ = 2 ^ 2 := by norm_num
  have hcdis := hs.commDisj (centerlessBar_of_A7 h7)
  have hRrank : CFSG.Open.pRank 2 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) =
      CFSG.Open.pRank 2 (T ⊓ K) + CFSG.Open.pRank 2 (T ⊓ CxK x K) := by
    refine CFSG.GroupTheory.pRank_sup_eq_add_of_commute_of_not_dvd Nat.prime_two ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      exact hcdis.comm p hp q hq
    · rw [hcdis.inf, Subgroup.card_bot]
      norm_num
  have hRle : CFSG.Open.pRank 2 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) ≤ 4 := by
    rw [hRrank]
    omega
  have hSrank : CFSG.Open.pRank 2 S ≤ 4 := by
    refine CFSG.SectionRank.pRank_le (p := 2) (H := S) (k := 4) (by norm_num) ?_
    intro E hES hEopen
    have hEel : CFSG.IsElementaryAbelian 2 ↥E :=
      (CFSG.Open.isElemAbelian_iff_isElementaryAbelian (p := 2) (E := E)).mp hEopen
    have hER : E ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) := by
      intro s hsE
      by_cases hs1 : s = 1
      · subst hs1
        exact (Subgroup.one_mem _)
      · have hsq : s * s = 1 := by
          have h := CFSG.elemPow_eq_one_of_isElementaryAbelian
            (p := 2) (A := E) s hsE
          simpa [pow_two] using h
        have hs2 : orderOf s = 2 :=
          orderOf_eq_prime (by simpa [pow_two] using hsq) hs1
        have hsT : s ∈ T := by
          rw [hTS]
          exact hES hsE
        exact mem_R_of_involution_of_KN hs h7 e7 hKn hSimple hNonab hxCentral
          hQ4.le hTS hsT hs2
    have hErank : CFSG.Open.pRank 2 E ≤ CFSG.Open.pRank 2 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) := by
      have h := C3.Layer1.Back.pRank_mono' hER
      rwa [← open_pRank_eq_pRank E, ← open_pRank_eq_pRank ((T ⊓ K) ⊔ (T ⊓ CxK x K))] at h
    have hcardE : Nat.card ↥E = 2 ^ CFSG.Open.pRank 2 E := by
      rw [C3.Layer1.Back.card_eq_two_pow_pRank hEel, ← open_pRank_eq_pRank E]
    rw [hcardE]
    calc 2 ^ CFSG.Open.pRank 2 E ≤ 2 ^ 4 :=
          Nat.pow_le_pow_right (by norm_num) (hErank.trans hRle)
      _ = 2 ^ 4 := rfl
  have hSyl : CFSG.pRank 2 (S : Subgroup G) = CFSG.pRank 2 G := by
    let Ssyl : Sylow 2 G := Sylow.ofCard S (by
      rw [hs.sylowS.card_eq, Subgroup.card_top])
    have h := (CFSG.SectionRank.pRank_sylow Ssyl).2
    have hcoe : (Ssyl : Subgroup G) = S := Sylow.coe_ofCard S _
    rwa [hcoe] at h
  have hSrank_group : CFSG.pRank 2 ↥S ≤ 4 := by
    rw [← open_pRank_eq_pRank S]
    exact hSrank
  rw [← hSyl]
  exact hSrank_group

theorem central_decomposition_of_smallQ
    (hs : Th2Std x y K T S) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (e : kBar K ≃* alternatingGroup (Fin 7)) (hTS : T = S)
    (hSimple : IsSimpleGroup G) (hNonab : ∃ a b : G, a * b ≠ b * a)
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) (hQel : CFSG.IsElementaryAbelian 2 ↥(T ⊓ CxK x K)) :
    ∀ s ∈ T, ∃ π ∈ T ⊓ K, ∃ c ∈ T, (∀ g ∈ T, g * c = c * g) ∧ s = π * c := by
  classical
  have hcen := centerlessBar_of_A7 h7
  have hcd := hs.commDisj hcen
  have hKn := (Th2Std.K_normal_of_A7_card_Q_four hs e hQ4).2
  have hTN := T_le_normalizer_of_KN hs hKn
  have hxCentral := isCentralInvolution_x_of_eq hs hTS
  have hInvR : ∀ s ∈ T, orderOf s = 2 → s ∈ (T ⊓ K) ⊔ (T ⊓ CxK x K) :=
    fun s hsT hs2 => mem_R_of_involution_of_KN hs h7 e hKn hSimple hNonab hxCentral
      hQ4.le hTS hsT hs2
  obtain ⟨hQc, hQsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hQel
  have hRQ : ∀ r ∈ (T ⊓ K) ⊔ (T ⊓ CxK x K), ∀ q ∈ T ⊓ CxK x K, r * q = q * r := by
    intro r hr q hq
    obtain ⟨p, hp, q', hq', rfl⟩ := exists_mul_of_mem_sup_of_commute hcd.comm hr
    calc p * q' * q = p * (q' * q) := by group
      _ = p * (q * q') := by rw [hQc q' hq' q hq]
      _ = (p * q) * q' := by group
      _ = (q * p) * q' := by rw [hcd.comm p hp q hq]
      _ = q * (p * q') := by group
  by_cases hTR : ∀ s ∈ T, s ∈ (T ⊓ K) ⊔ (T ⊓ CxK x K)
  · intro s hsT
    obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute hcd.comm (hTR s hsT)
    exact ⟨p, hp, q, hq.1, fun g hg => hRQ g (hTR g hg) q hq, rfl⟩
  · push Not at hTR
    obtain ⟨s₀, hs₀T, hs₀R⟩ := hTR
    obtain ⟨t, htT, htR, ht2, hcoset, htP⟩ :=
      exists_odd_involution_coset hs hcd h7 e hTN hs₀T hs₀R
    have hx1 : x ≠ 1 := by
      intro h1
      have := hs.orderOf_x
      rw [h1, orderOf_one] at this
      omega
    have hinv := hInvR
    have htQ : ∀ q ∈ T ⊓ CxK x K, t * q = q * t :=
      centralizes_of_no_involution_outside inf_le_left le_sup_right
        (fun t' ht' q hq => Q_normal_in_T hs e hTN ht' hq) hQ4 hQel
        ⟨hs.x_mem_T, hs.x_mem_CxK⟩ hx1
        (fun s hsT => (mem_centralizer_singleton_iff.1 (hs.T_le_C hsT))) hinv htT htR ht2
    have htRc : ∀ r ∈ (T ⊓ K) ⊔ (T ⊓ CxK x K), r * t = t * r := by
      intro r hr
      obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute hcd.comm hr
      calc p * q * t = p * (q * t) := by group
        _ = p * (t * q) := by rw [htQ q hq |>.symm]
        _ = (p * t) * q := by group
        _ = (t * p) * q := by rw [htP p hp |>.symm]
        _ = t * (p * q) := by group
    have htc : ∀ g ∈ T, g * t = t * g := by
      intro g hg
      by_cases hgR : g ∈ (T ⊓ K) ⊔ (T ⊓ CxK x K)
      · exact htRc g hgR
      · have hr := hcoset g hg hgR
        have hrt := htRc _ hr
        have hg' : g = (g * t⁻¹) * t := by group
        calc g * t = ((g * t⁻¹) * t) * t := by rw [← hg']
          _ = (g * t⁻¹) * (t * t) := by group
          _ = ((g * t⁻¹) * t) * t := by group
          _ = (t * (g * t⁻¹)) * t := by rw [hrt]
          _ = t * ((g * t⁻¹) * t) := by group
          _ = t * g := by rw [← hg']
    have hQcT : ∀ q ∈ T ⊓ CxK x K, ∀ g ∈ T, g * q = q * g := by
      intro q hq g hg
      by_cases hgR : g ∈ (T ⊓ K) ⊔ (T ⊓ CxK x K)
      · exact hRQ g hgR q hq
      · have hr := hcoset g hg hgR
        have hrq := hRQ _ hr q hq
        calc g * q = ((g * t⁻¹) * t) * q := by group
          _ = (g * t⁻¹) * (t * q) := by group
          _ = (g * t⁻¹) * (q * t) := by rw [htQ q hq]
          _ = ((g * t⁻¹) * q) * t := by group
          _ = (q * (g * t⁻¹)) * t := by rw [hrq]
          _ = q * ((g * t⁻¹) * t) := by group
          _ = q * g := by group
    intro s hsT
    by_cases hsR : s ∈ (T ⊓ K) ⊔ (T ⊓ CxK x K)
    · obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute hcd.comm hsR
      exact ⟨p, hp, q, hq.1, fun g hg => hQcT q hq g hg, rfl⟩
    · have hr := hcoset s hsT hsR
      obtain ⟨p, hp, q, hq, hpq⟩ := exists_mul_of_mem_sup_of_commute hcd.comm hr
      refine ⟨p, hp, q * t, T.mul_mem hq.1 htT, fun g hg => ?_, ?_⟩
      · calc g * (q * t) = (g * q) * t := by group
          _ = (q * g) * t := by rw [hQcT q hq g hg]
          _ = q * (g * t) := by group
          _ = q * (t * g) := by rw [htc g hg]
          _ = (q * t) * g := by group
      · calc s = (s * t⁻¹) * t := by group
          _ = (p * q) * t := by rw [hpq]
          _ = p * (q * t) := by group


theorem central_decomposition
    (hG : C3Hyp G) (hs : Th2Std x y K T S) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (e : kBar K ≃* alternatingGroup (Fin 7)) (hTS : T = S)
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) (hQel : CFSG.IsElementaryAbelian 2 ↥(T ⊓ CxK x K)) :
    ∀ s ∈ T, ∃ π ∈ T ⊓ K, ∃ c ∈ T, (∀ g ∈ T, g * c = c * g) ∧ s = π * c :=
  central_decomposition_of_smallQ hs h7 e hTS hG.kproper.1 hG.kproper.2.1 hQ4 hQel

theorem exists_d8Central_of_smallQ
    (hs : Th2Std x y K T S) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (e : kBar K ≃* alternatingGroup (Fin 7)) (hTS : T = S)
    (hSimple : IsSimpleGroup G) (hNonab : ∃ a b : G, a * b ≠ b * a)
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) (hQel : CFSG.IsElementaryAbelian 2 ↥(T ⊓ CxK x K)) :
    ∃ z : G, D8Central T (T ⊓ K) z := by
  have hD8 : C3.Layer1.Bk.IsD8 (T ⊓ K) := C3.Layer1.Bk.isD8_of_inf_alt7 hs.T_pGroup hs.sylow_P e
  obtain ⟨z, hzP, hz1, hzz, hzc, hzu⟩ := hD8.exists_z
  exact ⟨z, ⟨hD8.card_eq, inf_le_left, hzP, hz1, hzz, hzc, hzu,
    central_decomposition_of_smallQ hs h7 e hTS hSimple hNonab hQ4 hQel⟩⟩

theorem exists_d8Central
    (hG : C3Hyp G) (hs : Th2Std x y K T S) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (e : kBar K ≃* alternatingGroup (Fin 7)) (hTS : T = S)
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) (hQel : CFSG.IsElementaryAbelian 2 ↥(T ⊓ CxK x K)) :
    ∃ z : G, D8Central T (T ⊓ K) z :=
  exists_d8Central_of_smallQ hs h7 e hTS hG.kproper.1 hG.kproper.2.1 hQ4 hQel

theorem false_of_Q4_TS_of_smallQ
    (hs : Th2Std x y K T S) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) (hTS : T = S) {B : Subgroup G}
    (hB : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B) {b : G} {J : Subgroup G}
    (hobs : Obstr52 B b J) (hSimple : IsSimpleGroup G)
    (hNonab : ∃ a b : G, a * b ≠ b * a) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eK : kBar K ≃* alternatingGroup (Fin 7) := Classical.choice h7
  have hG4 : pRank 2 G ≤ 4 :=
    pRank_le_four_of_Q4_TS hs h7 hQ4 hTS hSimple hNonab
  have hE : IsE 4 ⊤ B := isE_of_isSn le_top hB le_rfl
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := hE.2.1
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  obtain ⟨eJ⟩ := hobs.nonempty_A7_of_rank_four hG4 hBel
  have hcen := centerlessBar_of_A7 ⟨eK⟩
  have hcd := hs.commDisj hcen
  have hP : RankTwoShape (T ⊓ K) := rankTwoShape_sylow_A7 hs.sylow_P ⟨eK⟩
  have hKn := (Th2Std.K_normal_of_A7_card_Q_four hs eK hQ4).2
  have hTN := T_le_normalizer_of_KN hs hKn
  obtain ⟨U, hU, E₁, hE₁S, hE₁2, hBdef⟩ := (isS_sup_iff hcd hP B).1 hB
  have hQel : CFSG.IsElementaryAbelian 2 ↥(T ⊓ CxK x K) := by
    have hEQ : E₁ ≤ T ⊓ CxK x K := hE₁S.1
    have hcardE : Nat.card ↥E₁ = 2 ^ pRank 2 ↥E₁ :=
      C3.Layer1.Back.card_eq_two_pow_pRank hE₁S.2.1
    have h4 : 4 ≤ Nat.card ↥E₁ := by
      rw [hcardE]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ pRank 2 ↥E₁ := Nat.pow_le_pow_right (by norm_num) hE₁2
    have hEQ' : E₁ = T ⊓ CxK x K := Subgroup.eq_of_le_of_card_ge hEQ (by rw [hQ4]; exact h4)
    rw [← hEQ']
    exact hE₁S.2.1
  obtain ⟨z, hD⟩ := exists_d8Central_of_smallQ hs h7 eK hTS hSimple hNonab hQ4 hQel
  have hBR : B ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) := hB.1.1
  have hBT : B ≤ T := hBR.trans (sup_le inf_le_left inf_le_left)
  have hbB : b ∈ B := hobs.mem
  have hbT : b ∈ T := hBT hbB
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq b hbB) hobs.ne_one
  have hTcard : Nat.card ↥T = twoPartCard (⊤ : Subgroup G) := by
    have h1 := hs.sylowS.card_eq
    unfold twoPartCard
    rw [← hTS] at h1
    exact h1
  have hT64 : Nat.card ↥T ≤ 64 := by
    have h1 := card_T_eq_card_Q_mul_range hs eK hTN
    have h2 := (card_range_le_sixteen hs.T_pGroup eK hTN).2
    rw [hQ4] at h1
    omega
  set A : Subgroup G := T ⊓ centralizer ({b} : Set G) with hA
  have hBA : B ≤ A := fun g hg => ⟨hBT hg, hobs.B_le_centralizer hBel hg⟩
  have hA2 : IsPGroup 2 ↥A := hs.T_pGroup.to_inf_left
  obtain ⟨T₁, hAT₁, hsyl₁, hT₁card⟩ :=
    hobs.exists_sylow hG4 hBel eJ (inf_le_right : A ≤ centralizer ({b} : Set G)) hA2
  have hT₁2 : IsPGroup 2 ↥T₁ := hsyl₁.isPGroup
  have hT₁le : Nat.card ↥T₁ ≤ Nat.card ↥T := by
    rw [hTcard]
    exact Th2.L627.card_le_twoPartCard hT₁2 le_top
  have hq2 : 2 ≤ twoPartCard (CxK b J) := by
    have hz2 : IsPGroup 2 ↥(zpowers b) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
    have hzle : zpowers b ≤ CxK b J := (zpowers_le).2 (mem_CxK_self' hobs.comp.1)
    have := Th2.L627.card_le_twoPartCard hz2 hzle
    rwa [Nat.card_zpowers, hb2] at this
  have hbT₁ : b ∈ T₁ := hAT₁ ⟨hbT, mem_centralizer_singleton_iff.2 rfl⟩
  by_cases hα : Nat.card ↥T₁ = Nat.card ↥T
  ·
    have hq4 : twoPartCard (CxK b J) ≤ 4 := by omega
    have hT₁G : Nat.card ↥T₁ = 2 ^ (Nat.card G).factorization 2 := by
      rw [hα, hTcard]
      unfold twoPartCard
      rw [Subgroup.card_top]
    have hc : IsCentralInvolution b :=
      isCentralInvolution_of_card hb2 hbT₁
        (fun s hs' => mem_centralizer_singleton_iff.1 (hsyl₁.le hs')) hT₁G
    exact hobs.false_of_isCentralInvolution_of_le_four hG4 hSimple hNonab hBel ⟨eJ⟩ hq4 hc
  ·
    have hlt : Nat.card ↥T₁ < Nat.card ↥T := lt_of_le_of_ne hT₁le hα
    obtain ⟨k, hk⟩ : ∃ k, twoPartCard (CxK b J) = 2 ^ k := ⟨_, rfl⟩
    have hq1 : twoPartCard (CxK b J) = 2 := by
      have hk1 : 1 ≤ k := by
        by_contra hk0
        push Not at hk0
        interval_cases k
        omega
      have hk2 : k ≤ 1 := by
        by_contra hk2
        push Not at hk2
        have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
        omega
      have : k = 1 := by omega
      rw [hk, this]
      norm_num
    have hT₁32 : Nat.card ↥T₁ = 32 := by omega
    have hT64' : Nat.card ↥T = 64 := by
      obtain ⟨j, hj⟩ : ∃ j, Nat.card ↥T = 2 ^ j := ⟨_, hTcard⟩
      have hj6 : j = 6 := by
        have hj5 : 5 < j := by
          by_contra hj5
          push Not at hj5
          have : 2 ^ j ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hj5
          omega
        have hj7 : j ≤ 6 := by
          by_contra hj7
          push Not at hj7
          have : 2 ^ 7 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj7
          omega
        omega
      rw [hj, hj6]
      norm_num
    have hAcard : Nat.card ↥T ≤ 2 * Nat.card ↥A := hD.card_le_two_mul_centralizer hbT
    have hAT₁eq : A = T₁ := by
      refine Subgroup.eq_of_le_of_card_ge hAT₁ ?_
      omega
    have hA32 : Nat.card ↥A = 32 := by rw [hAT₁eq]; exact hT₁32
    have hBT₁ : B ≤ T₁ := hBA.trans hAT₁
    have hBne : B ≠ T₁ := by
      intro h1
      have hBcard : Nat.card ↥B = 2 ^ pRank 2 ↥B := C3.Layer1.Back.card_eq_two_pow_pRank hBel
      have hBr : pRank 2 ↥B ≤ 4 := (pRank_le_top' B).trans hG4
      have : Nat.card ↥B ≤ 2 ^ 4 := by
        rw [hBcard]; exact Nat.pow_le_pow_right (by norm_num) hBr
      rw [h1] at this
      omega
    obtain ⟨-, u, hu, v, hv, huv⟩ := hobs.V_structure hG4 hBel ⟨eJ⟩ hq1
      (hsyl₁.le) hT₁2 hBT₁ hBne
    have hnc : ∃ g ∈ T, g * b ≠ b * g := by
      by_contra hcon
      push Not at hcon
      have hAT : T ≤ A := fun g hg => ⟨hg, mem_centralizer_singleton_iff.2 (hcon g hg)⟩
      have := Subgroup.card_le_of_le hAT
      omega
    have hcomm := hD.commutative_centralizer hbT hnc
    have huA : u ∈ T ⊓ centralizer ({b} : Set G) := by rw [← hA, hAT₁eq]; exact hu
    have hvA : v ∈ T ⊓ centralizer ({b} : Set G) := by rw [← hA, hAT₁eq]; exact hv
    exact huv (hcomm u huA v hvA)

theorem false_of_Q4_TS
    (hG : C3Hyp G) (hs : Th2Std x y K T S) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) (hTS : T = S) {B : Subgroup G}
    (hB : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B) {b : G} {J : Subgroup G}
    (hobs : Obstr52 B b J) : False :=
  false_of_Q4_TS_of_smallQ hs h7 hQ4 hTS hB hobs hG.kproper.1 hG.kproper.2.1

end CFSG.GH74.GLS.Th2.Obs
