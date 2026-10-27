module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018CoreField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporL3DownBM
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018OddHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFBU38Char2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFBU38Alt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018U38Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQ

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158Inn

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def isD4Eight : TauCeti.CFSGIndex → Prop :=
  onLie fun | .D 4 q => q.p = 2 ∧ q.exponent = 3 | _ => False

@[expose] def isTD4Eight : TauCeti.CFSGIndex → Prop :=
  onLie fun | .trialityD4 q => q.p = 2 ∧ q.exponent = 3 | _ => False

@[expose] def T158FieldCoreU : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω) (x₁ x₂ : Ω) (L₁ L₂ : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore 3 ↥S = ⊥ →
    x₁ ^ 3 = 1 → x₂ ^ 3 = 1 → x₁ * x₂ = x₂ * x₁ → x₁ ∈ Subgroup.normalizer (S : Set Ω) →
    GLAMarking (PQuot 3 S) (fun lab _ _ I F θ => lab = ⟨.twA, 2, 9⟩ ∧
      GLAPrimeField 3 lab I F (GLAInduces θ (indRel 3 S x₁))) →
    GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x₁} : Set Ω)) L₁ → catalogIs (PSimple 3 L₁) S9.isU3eight →
    GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x₂} : Set Ω)) L₂ → catalogIs (PSimple 3 L₂) S9.isU3eight →
    FieldOn 3 x₁ L₂ → FieldOn 3 x₂ L₁ → False

@[expose] def T158TriCore : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω) (x₁ x₂ : Ω) (L₁ L₂ : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore 3 ↥S = ⊥ →
    (catalogIs (PSimple 3 S) isD4Eight ∨ catalogIs (PSimple 3 S) isTD4Eight) →
    x₁ ^ 3 = 1 → x₂ ^ 3 = 1 → x₁ * x₂ = x₂ * x₁ → NonInnDiag 3 x₁ S → ¬ FieldOn 3 x₁ S →
    GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x₁} : Set Ω)) L₁ → catalogIs (PSimple 3 L₁) S9.isU3eight →
    GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x₂} : Set Ω)) L₂ → catalogIs (PSimple 3 L₂) S9.isU3eight →
    FieldOn 3 x₁ L₂ → FieldOn 3 x₂ L₁ → False

private theorem t158Inn_prime_eq_two_of_card_eight (q : TauCeti.PrimePower) (h : q.card = 8) : q.p = 2 := by
  have hdvd : q.p ∣ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact dvd_pow_self q.p q.exponent_pos.ne'
  rw [h] at hdvd
  have h2 : q.p ∣ 2 := q.prime_p.dvd_of_dvd_pow (n := 3) (by norm_num; exact hdvd)
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h2

theorem t158Inn_isChevTwo_of_isU3eight {T : Type} [Group T] (h : catalogIs T S9.isU3eight) : IsChevSimple 2 T := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  refine Or.inl ⟨i, ?_, ⟨e⟩⟩
  cases i with
  | cyclic p hp => simp [S9.isU3eight, onLie] at hi
  | alternating n hn => simp [S9.isU3eight, onLie] at hi
  | sporadic s => simp [S9.isU3eight, onLie] at hi
  | lie j =>
    obtain ⟨d, hv⟩ := j
    simp only [S9.isU3eight, onLie] at hi
    simp only [onLie]
    change d.characteristic = 2
    split at hi
    · rename_i q
      rw [TauCeti.LieTypeIndex.characteristic_twistedA]
      exact t158Inn_prime_eq_two_of_card_eight q hi
    · exact absurd hi id

theorem t158Inn_twoPart_card_u38 : twoPart 5515776 = 2 ^ 9 := by
  have h : (5515776 : ℕ) = 2 ^ 9 * 10773 := by norm_num
  rw [h]
  exact FQ.twoPart_two_pow_mul_odd (by decide)

private theorem t158Inn_d4_index {i : TauCeti.CFSGIndex} (hi : isD4any i) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid),
      i = TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩ ∧ q.p = 2 := by
  rcases i with ⟨n, hn⟩ | ⟨p, hp⟩ | ⟨d, hv⟩ | s
  all_goals try (simp [isD4any, onLie] at hi; done)
  cases d with
  | D r q =>
    rcases r with _ | _ | _ | _ | _ | r
    all_goals try (simp [isD4any, onLie] at hi; done)
    exact ⟨q, hv, rfl, by simpa [isD4any, onLie] using hi⟩
  | _ => simp [isD4any, onLie] at hi

private theorem t158Inn_td4_index {i : TauCeti.CFSGIndex}
    (hi : onLie (fun | .trialityD4 _ => True | _ => False) i) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      i = TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩ := by
  rcases i with ⟨n, hn⟩ | ⟨p, hp⟩ | ⟨d, hv⟩ | s
  all_goals try (simp [onLie] at hi; done)
  cases d with
  | trialityD4 q => exact ⟨q, hv, rfl⟩
  | _ => simp [onLie] at hi

private theorem t158Inn_two_pow_dvd_orderD {e : ℕ} (he : 1 ≤ e) : 2 ^ 12 ∣ orderD 4 (2 ^ e) := by
  have hev : Even ((2 ^ e) ^ 4) := by
    rw [← pow_mul]
    exact Nat.even_pow.2 ⟨even_two, by omega⟩
  have hpos : 1 ≤ (2 ^ e) ^ 4 := Nat.one_le_pow _ _ (by positivity)
  have hodd : Odd ((2 ^ e) ^ 4 - 1) := by
    obtain ⟨k, hk⟩ := hev
    exact ⟨k - 1, by omega⟩
  have hcop : Nat.Coprime 2 ((2 ^ e) ^ 4 - 1) := (Nat.coprime_two_left).2 hodd
  have hg : Nat.gcd 4 ((2 ^ e) ^ 4 - 1) = 1 := by
    have h4 : Nat.Coprime (2 ^ 2) ((2 ^ e) ^ 4 - 1) := Nat.Coprime.pow_left 2 hcop
    simpa using h4
  unfold orderD
  rw [hg, Nat.div_one]
  have h12 : 2 ^ 12 ∣ (2 ^ e) ^ (4 * (4 - 1)) := by
    rw [show 4 * (4 - 1) = 12 by norm_num]
    exact pow_dvd_pow_of_dvd (dvd_pow_self 2 (by omega)) 12
  exact (h12.mul_right _).mul_right _

private theorem t158Inn_two_pow_dvd_orderTrialityD4 {e : ℕ} (he : 1 ≤ e) :
    2 ^ 12 ∣ orderTrialityD4 (2 ^ e) := by
  unfold orderTrialityD4
  have h12 : 2 ^ 12 ∣ (2 ^ e) ^ 12 := pow_dvd_pow_of_dvd (dvd_pow_self 2 (by omega)) 12
  exact ((h12.mul_right _).mul_right _).mul_right _


section Sec_t158Inn_nineteen_dvd


theorem t158Inn_nineteen_dvd {T : Type} [Group T] [Finite T] {J : Subgroup T}
    (hU : catalogIs (PSimple 3 J) S9.isU3eight) : 19 ∣ Nat.card T := by
  have h1 : Nat.card (PSimple 3 J) = 5515776 :=
    CatSingle.card_isU3eight CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hU
  have h2 : Nat.card (PSimple 3 J) ∣ Nat.card (PQuot 3 J) := Subgroup.card_quotient_dvd_card _
  have h3 : Nat.card (PQuot 3 J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
  have h4 : Nat.card J ∣ Nat.card T := Subgroup.card_subgroup_dvd_card J
  have h19 : 19 ∣ Nat.card (PSimple 3 J) := by rw [h1]; norm_num
  exact h19.trans (h2.trans (h3.trans h4))

end Sec_t158Inn_nineteen_dvd

section Sec_t158Inn_prime_eq_three


theorem t158Inn_prime_eq_three {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X L : Subgroup Ω} {g : Ω} (hL : GLAPComponent p X L) (hU : catalogIs (PSimple p L) S9.isU3eight)
    (hgp : g ^ p = 1) (hF : FieldOn p g L) : p = 3 := by
  have hst := FP.i91CentPartAt_of_stOrder (G := Ω) hp hp2 (FQ.s10StOrderAt hp hp2)
  have h := hst X L g hL (t158Inn_isChevTwo_of_isU3eight hU) hgp hF
  rw [FP.card2_eq_twoPart_card_pSimple hp hp2,
    CatSingle.card_isU3eight CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hU,
    t158Inn_twoPart_card_u38] at h
  unfold centCard2 twoPart at h
  rw [← pow_mul] at h
  have h9 := Nat.pow_right_injective le_rfl h
  have hdvd : p ∣ 3 ^ 2 := ⟨_, by rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9, mul_comm]⟩
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hdvd)

end Sec_t158Inn_prime_eq_three

section Sec_t158Inn_char_eq_two


theorem t158Inn_char_eq_two {Ω : Type} [Group Ω] [Finite Ω] {X K J : Subgroup Ω} {x : Ω}
    (hK : GLAPComponent 3 X K) (hxN : x ∈ Subgroup.normalizer (K : Set Ω)) (hx3 : x ^ 3 = 1)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hU : catalogIs (PSimple 3 J) S9.isU3eight) (d : TauCeti.ValidLieTypeIndex)
    (e : PSimple 3 K ≃* (TauCeti.CFSGIndex.lie d).Group) : d.1.characteristic = 2 := by
  obtain ⟨hsimple, hna⟩ := chev_pSimple_simple_nonabelian Nat.prime_three hK
  haveI := hsimple
  by_contra h2
  have hr : d.1.characteristic.Prime := up7a8_char_prime d.1
  have hχ : IsChevSimple d.1.characteristic (PSimple 3 K) :=
    Or.inl ⟨TauCeti.CFSGIndex.lie d, rfl, ⟨e⟩⟩
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hx3
  have hα3 : (chevAut 3 K ⟨x, hxN⟩) ^ 3 = 1 := chevAut_pow_eq_one 3 K hxN hx3
  have hJ' := glaPComponent_chevTransfer Nat.prime_three hxN hxp hJ
  obtain ⟨eJ⟩ := nonempty_pSimple_equiv_chevTransfer Nat.prime_three hxN hxp hJ
  have hU' : catalogIs (PSimple 3 (chevTransfer 3 K J)) S9.isU3eight := I2018.catalogIs_congr' eJ hU
  have hJχ : IsChevSimple d.1.characteristic (PSimple 3 (chevTransfer 3 K J)) :=
    I2018.i2018OddB3_holds _ hr h2 (PSimple 3 K) hsimple hna hχ _ hα3 _ hJ'
  exact h2 (I2018.I2018U38Char2_holds _ hU' _ hJχ)

end Sec_t158Inn_char_eq_two

section Sec_t158Inn_char2_index


theorem t158Inn_char2_index
    {Ω : Type} [Group Ω] [Finite Ω] {X K J : Subgroup Ω} {x : Ω}
    (hK : GLAPComponent 3 X K) (hcat : IsCatalogGroup (PSimple 3 K))
    (hxN : x ∈ Subgroup.normalizer (K : Set Ω)) (hx3 : x ^ 3 = 1)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hU : catalogIs (PSimple 3 J) S9.isU3eight) :
    ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 ∧
      Nonempty (PSimple 3 K ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨hsimple, hna⟩ := chev_pSimple_simple_nonabelian Nat.prime_three hK
  haveI := hsimple
  obtain ⟨i, ⟨eS⟩⟩ := hcat
  cases i with
  | cyclic r hr =>
    exfalso
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    apply eS.injective
    simp only [map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    exact (I2018.i2018_alt_absurd hK hxN hx3 hJ hU I2018.I2018U38NotAlt_holds hn eS).elim
  | sporadic s =>
    exact (I2018.i2018_spor_absurd hK hxN hx3 hJ hU I2018.i2018U38Cover_holds
      (I2018.sporL3Down_all_of_BM sporL3Down_B_holds sporL3Down_M_holds s) eS).elim
  | lie dl => exact ⟨dl, t158Inn_char_eq_two hK hxN hx3 hJ hU dl eS, ⟨eS⟩⟩

end Sec_t158Inn_char2_index

section Sec_t158Inn_chev2


theorem t158Inn_chev2
    {Ω : Type} [Group Ω] [Finite Ω] {X K J : Subgroup Ω} {x : Ω}
    (hK : GLAPComponent 3 X K) (hcat : IsCatalogGroup (PSimple 3 K))
    (hxN : x ∈ Subgroup.normalizer (K : Set Ω)) (hx3 : x ^ 3 = 1)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hU : catalogIs (PSimple 3 J) S9.isU3eight) : IsChevSimple 2 (PSimple 3 K) := by
  obtain ⟨d, hd, ⟨e⟩⟩ := t158Inn_char2_index hK hcat hxN hx3 hJ hU
  exact Or.inl ⟨TauCeti.CFSGIndex.lie d, hd, ⟨e⟩⟩

end Sec_t158Inn_chev2

section Sec_t158Inn_tri_eight


theorem t158Inn_tri_eight {Ω : Type} [Group Ω] [Finite Ω] {S L : Subgroup Ω} {x : Ω}
    (hSc : GLAPComponent 3 S S) (hD : catalogIs (PSimple 3 S) isD4any ∨ IsTD4 3 S)
    (hxN : x ∈ Subgroup.normalizer (S : Set Ω)) (hx3 : x ^ 3 = 1)
    (hL : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x} : Set Ω)) L)
    (hU : catalogIs (PSimple 3 L) S9.isU3eight) :
    catalogIs (PSimple 3 S) isD4Eight ∨ catalogIs (PSimple 3 S) isTD4Eight := by
  obtain ⟨hsimple, hna⟩ := chev_pSimple_simple_nonabelian Nat.prime_three hSc
  haveI := hsimple
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hx3
  have hα3 : (chevAut 3 S ⟨x, hxN⟩) ^ 3 = 1 := chevAut_pow_eq_one 3 S hxN hx3
  have hJ' := glaPComponent_chevTransfer Nat.prime_three hxN hxp hL
  obtain ⟨eJ⟩ := nonempty_pSimple_equiv_chevTransfer Nat.prime_three hxN hxp hL
  have hU' : catalogIs (PSimple 3 (chevTransfer 3 S L)) S9.isU3eight := I2018.catalogIs_congr' eJ hU
  have h19 : 19 ∣ Nat.card (PSimple 3 S) := t158Inn_nineteen_dvd hU'
  have hα1 : (2 ^ 12 ∣ Nat.card (PSimple 3 S)) → chevAut 3 S ⟨x, hxN⟩ ≠ 1 := by
    intro h12 h1
    have hJ'' := hJ'
    rw [h1, I2018.fixSubgroup_one_eq_top] at hJ''
    obtain ⟨eT⟩ := chevQ_pSimple_top_equiv Nat.prime_three hna hJ''
    have hcard : Nat.card (PSimple 3 S) = 5515776 :=
      CatSingle.card_isU3eight CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
        (I2018.catalogIs_congr' eT hU')
    rw [hcard] at h12
    norm_num at h12
  rcases hD with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  ·
    obtain ⟨q, hv, rfl, hq2⟩ := t158Inn_d4_index hi
    have hord : Nat.card (PSimple 3 S) = orderD 4 q.card :=
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.D 4 q, hv⟩ _ ⟨e⟩
    have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
    have h12 : 2 ^ 12 ∣ Nat.card (PSimple 3 S) := by
      rw [hord, hqc]
      exact t158Inn_two_pow_dvd_orderD q.exponent_pos
    obtain ⟨lab, -, -, -, hf⟩ := I2018Core.field_bound hsimple hna ⟨.D 4 q, hv⟩
      (by simpa using hq2) e hα3 (hα1 h12) hJ' hU'
    have hf' : q.exponent ∣ 3 := by
      rcases hf with h | ⟨h, -⟩
      · exact h
      · simp [I2018Core.specOf] at h
    rcases (Nat.dvd_prime Nat.prime_three).1 hf' with h1 | h3
    · exfalso
      rw [hord, hqc, h1] at h19
      exact absurd h19 (by decide)
    · exact Or.inl ⟨TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩, ⟨hq2, h3⟩, ⟨e⟩⟩
  ·
    obtain ⟨q, hv, rfl⟩ := t158Inn_td4_index hi
    have hq2 : q.p = 2 := by
      have h := t158Inn_char_eq_two hSc hxN hx3 hL hU ⟨.trialityD4 q, hv⟩ e
      simpa using h
    have hord : Nat.card (PSimple 3 S) = orderTrialityD4 q.card :=
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.trialityD4 q, hv⟩ _ ⟨e⟩
    have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
    have h12 : 2 ^ 12 ∣ Nat.card (PSimple 3 S) := by
      rw [hord, hqc]
      exact t158Inn_two_pow_dvd_orderTrialityD4 q.exponent_pos
    obtain ⟨lab, -, -, -, hf⟩ := I2018Core.field_bound hsimple hna ⟨.trialityD4 q, hv⟩
      (by simpa using hq2) e hα3 (hα1 h12) hJ' hU'
    have hf' : q.exponent ∣ 3 := by
      rcases hf with h | ⟨h, -⟩
      · exact h
      · simp [I2018Core.specOf] at h
    rcases (Nat.dvd_prime Nat.prime_three).1 hf' with h1 | h3
    · exfalso
      rw [hord, hqc, h1] at h19
      exact absurd h19 (by decide)
    · exact Or.inr ⟨TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩, ⟨hq2, h3⟩, ⟨e⟩⟩

end Sec_t158Inn_tri_eight

end CFSG.LocalAnalysis.GLTheoremA.T158Inn

end
