module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110n
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110m2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256p2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110n

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup PerfectInLayer LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (autCenterQuot)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (fieldSize compRelC compRel subRelC subRel sameShape)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

section Indices

@[expose] def D4UpE8TwoIdx (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d = .E8 q ∧ q.card = 2

@[expose] def D4UpRestBigIdx (d : TauCeti.LieTypeIndex) : Prop :=
  Claims1110m.D4UpRestIdx d ∧ ¬ D4UpE8TwoIdx d

theorem four_le_two_pow_of_ne_d4n {a : ℕ} (ha : 1 ≤ a) (h : 2 ^ a ≠ 2) : 4 ≤ 2 ^ a := by
  have ha2 : 2 ≤ a := by
    by_contra hlt
    exact h (by rw [show a = 1 by omega, pow_one])
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha2

theorem restBig_facts_d4n {d : TauCeti.LieTypeIndex} (hv : d.Valid) (hd : D4UpRestBigIdx d) :
    d.characteristic = 2 ∧ 4 ≤ fieldSize d ∧ (∃ a : ℕ, fieldSize d = 2 ^ a) ∧
      (CFSG.Yardstones.Md42047359a2a.lieFamily d = .exceptional ∨
        CFSG.Yardstones.Md42047359a2a.lieFamily d = .suzukiReeTits) ∧ d ≠ .suzuki 2 := by
  have hs := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  obtain ⟨hd1, hd2⟩ := hd
  have hq : ∀ q : TauCeti.PrimePower, q.p = 2 → q.card ≠ 2 → 4 ≤ q.card := fun q hp hc => by
    rw [TauCeti.PrimePower.card_def, hp] at hc ⊢
    exact four_le_two_pow_of_ne_d4n q.exponent_pos hc
  have hq' : ∀ q : TauCeti.PrimePower, q.p = 2 → q.card = 2 ^ q.exponent := fun q hp => by
    rw [TauCeti.PrimePower.card_def, hp]
  cases d with
  | G2 q =>
    have hp : q.p = 2 := hd1
    refine ⟨by simpa using hp, hq q hp fun h => by simp only at hs; omega, ⟨_, hq' q hp⟩,
      Or.inl rfl, by simp⟩
  | E8 q =>
    have hp : q.p = 2 := hd1
    exact ⟨by simpa using hp, hq q hp fun h => hd2 ⟨q, rfl, h⟩, ⟨_, hq' q hp⟩, Or.inl rfl, by simp⟩
  | trialityD4 q =>
    obtain ⟨hp, hc⟩ : q.p = 2 ∧ q.card ≠ 2 := hd1
    exact ⟨by simpa using hp, hq q hp hc, ⟨_, hq' q hp⟩, Or.inl rfl, by simp⟩
  | F4 q =>
    obtain ⟨hp, hc⟩ : q.p = 2 ∧ q.card ≠ 2 := hd1
    exact ⟨by simpa using hp, hq q hp hc, ⟨_, hq' q hp⟩, Or.inl rfl, by simp⟩
  | E6 q =>
    obtain ⟨hp, hc⟩ : q.p = 2 ∧ q.card ≠ 2 := hd1
    exact ⟨by simpa using hp, hq q hp hc, ⟨_, hq' q hp⟩, Or.inl rfl, by simp⟩
  | twistedE6 q =>
    obtain ⟨hp, hc⟩ : q.p = 2 ∧ q.card ≠ 2 := hd1
    exact ⟨by simpa using hp, hq q hp hc, ⟨_, hq' q hp⟩, Or.inl rfl, by simp⟩
  | E7 q =>
    obtain ⟨hp, hc⟩ : q.p = 2 ∧ q.card ≠ 2 := hd1
    exact ⟨by simpa using hp, hq q hp hc, ⟨_, hq' q hp⟩, Or.inl rfl, by simp⟩
  | reeF4 m =>
    refine ⟨by simp, ?_, ⟨_, rfl⟩, Or.inr rfl, by simp⟩
    show 4 ≤ 2 ^ (2 * m + 1)
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  | A _ _ => exact (hd1 : False).elim
  | twistedA _ _ => exact (hd1 : False).elim
  | B _ _ => exact (hd1 : False).elim
  | C _ _ => exact (hd1 : False).elim
  | D _ _ => exact (hd1 : False).elim
  | twistedD _ _ => exact (hd1 : False).elim
  | suzuki _ => exact (hd1 : False).elim
  | reeG2 _ => exact (hd1 : False).elim
  | tits => exact (hd1 : False).elim

end Indices

section Arith

theorem card_ne_of_compRelC_d4n (hb : LieOrderBridge) {d : TauCeti.LieTypeIndex}
    (hd4 : 4 ≤ fieldSize d) {i : TauCeti.CFSGIndex} (hi : compRelC d i) {G : Type} [Group G]
    [Finite G] (φ : G ≃* i.Group) : Nat.card G ≠ 174182400 := by
  cases i with
  | cyclic p hp => exact (hi : False).elim
  | sporadic s => exact (hi : False).elim
  | alternating n hn =>
    have hn8 : n ≤ 8 := by
      rcases (hi : (n = 5 ∧ _) ∨ (n = 6 ∧ _) ∨ (n = 8 ∧ _)) with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
        norm_num
    rw [Nat.card_congr φ.toEquiv]
    show Nat.card (alternatingGroup (Fin n)) ≠ 174182400
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [nat_card_alternatingGroup, Nat.card_fin]
    interval_cases n <;> decide
  | lie e =>
    intro hcard
    have h1 : lieOrderFormula e.1 = 174182400 := (hb e G ⟨φ⟩).symm.trans hcard
    obtain ⟨q, hq, hq2⟩ := eq_D4_two_of_lieOrderFormula_d4n e.2 h1
    have hi' : compRel d e.1 := hi
    rcases hi' with ⟨-, ⟨j, hj, hfs⟩, -⟩ | ⟨hfd, -⟩ | ⟨hfd, -⟩
    · rw [hq] at hfs
      have hfs' : q.card = fieldSize d ^ j := hfs
      have : fieldSize d ≤ fieldSize d ^ j := Nat.le_self_pow (by omega) _
      omega
    · omega
    · omega

theorem subRelC_five_facts_d4n (hb : LieOrderBridge) {d : TauCeti.LieTypeIndex}
    (hd : D4UpRestBigIdx d) {i : TauCeti.CFSGIndex} (hi : subRelC 5 d i) {G : Type} [Group G]
    [Finite G] (φ : G ≃* i.Group) :
    Nat.card G ≠ 174182400 ∧ ¬ 174182400 * Nat.card G ∣ lieOrderFormula d := by
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have h3 : ∀ {a Q : ℕ}, Q ^ 5 = 2 ^ a → ¬ 3 ∣ Q := fun {a Q} h h3 =>
    absurd (Nat.prime_three.dvd_of_dvd_pow (h ▸ dvd_pow h3 (by norm_num) : 3 ∣ 2 ^ a))
      (by norm_num)
  have hfin : ∀ {M Q N : ℕ} (f : ℕ → ℕ), M ≠ 0 → ¬ 3 ∣ Q →
      (∃ R, f (Q ^ 5) = f Q * R ∧ ¬ 3 ∣ R) → M = f Q → N = f (Q ^ 5) → ¬ 174182400 * M ∣ N :=
    fun {M Q N} f hM _ ⟨R, hR, hR3⟩ hMQ hNQ h =>
      false_of_dvd_of_eq_mul_d4n hM (by rw [hNQ, hR, hMQ]) hR3 h
  cases i with
  | cyclic p hp => exact (hi : False).elim
  | sporadic s => exact (hi : False).elim
  | alternating n hn =>
    exfalso
    obtain ⟨hd1, -⟩ := hd
    rcases (hi : (n = 5 ∧ _) ∨ (n = 6 ∧ _) ∨ (n = 8 ∧ _)) with
      ⟨-, ⟨q, rfl⟩, -⟩ | ⟨-, ⟨⟨q, rfl⟩, -⟩ | ⟨⟨q, rfl⟩, -⟩⟩ | ⟨-, ⟨q, rfl⟩, -⟩ <;>
      exact (hd1 : False)
  | lie e =>
    obtain ⟨e, hev⟩ := e
    have hcard : Nat.card G = lieOrderFormula e := hb ⟨e, hev⟩ G ⟨φ⟩
    have hi' : subRel 5 d e := hi
    obtain ⟨hd1, hd2⟩ := hd
    rcases hi' with ⟨hs, hf⟩ | ⟨⟨q, rfl⟩, -⟩ | ⟨-, ⟨q, rfl⟩, -⟩ | ⟨⟨q', rfl, hq'⟩, ⟨q, rfl⟩, hf⟩ |
        ⟨-, ⟨q, rfl⟩, -⟩ | ⟨rfl, ⟨k, rfl⟩, hf⟩ | ⟨-, ⟨k, rfl⟩, -⟩
    ·
      have hne : lieOrderFormula e ≠ 174182400 := fun h => by
        obtain ⟨q, rfl, -⟩ := eq_D4_two_of_lieOrderFormula_d4n hev h
        cases d <;> first | exact (hs : False) | exact (hd1 : False)
      refine ⟨hcard ▸ hne, ?_⟩
      have hM : lieOrderFormula e ≠ 0 := hcard ▸ hG0
      rw [hcard]
      have hq2 : ∀ q : TauCeti.PrimePower, q.p = 2 → q.card = 2 ^ q.exponent := fun q hp => by
        rw [TauCeti.PrimePower.card_def, hp]
      cases d with
      | G2 q =>
        cases e with
        | G2 q' =>
          have hf' : q'.card ^ 5 = q.card := hf
          have hQ := h3 (hf'.trans (hq2 q hd1))
          exact hfin orderG2 hM hQ (orderG2_pow_five_d4n hQ) rfl (by rw [hf']; rfl)
        | _ => exact (hs : False).elim
      | E8 q =>
        cases e with
        | E8 q' =>
          have hf' : q'.card ^ 5 = q.card := hf
          have hQ := h3 (hf'.trans (hq2 q hd1))
          exact hfin orderE8 hM hQ (orderE8_pow_five_d4n hQ) rfl (by rw [hf']; rfl)
        | _ => exact (hs : False).elim
      | trialityD4 q =>
        cases e with
        | trialityD4 q' =>
          have hf' : q'.card ^ 5 = q.card := hf
          have hQ := h3 (hf'.trans (hq2 q (hd1 : q.p = 2 ∧ q.card ≠ 2).1))
          exact hfin orderTrialityD4 hM hQ (orderTrialityD4_pow_five_d4n hQ) rfl (by rw [hf']; rfl)
        | _ => exact (hs : False).elim
      | F4 q =>
        cases e with
        | F4 q' =>
          have hf' : q'.card ^ 5 = q.card := hf
          have hQ := h3 (hf'.trans (hq2 q (hd1 : q.p = 2 ∧ q.card ≠ 2).1))
          exact hfin orderF4 hM hQ (orderF4_pow_five_d4n hQ) rfl (by rw [hf']; rfl)
        | _ => exact (hs : False).elim
      | E6 q =>
        cases e with
        | E6 q' =>
          have hf' : q'.card ^ 5 = q.card := hf
          have hQ := h3 (hf'.trans (hq2 q (hd1 : q.p = 2 ∧ q.card ≠ 2).1))
          exact hfin orderE6 hM hQ (orderE6_pow_five_d4n hQ) rfl (by rw [hf']; rfl)
        | _ => exact (hs : False).elim
      | twistedE6 q =>
        cases e with
        | twistedE6 q' =>
          have hf' : q'.card ^ 5 = q.card := hf
          have hQ := h3 (hf'.trans (hq2 q (hd1 : q.p = 2 ∧ q.card ≠ 2).1))
          exact hfin orderTwistedE6 hM hQ (orderTwistedE6_pow_five_d4n hQ) rfl (by rw [hf']; rfl)
        | _ => exact (hs : False).elim
      | E7 q =>
        cases e with
        | E7 q' =>
          have hf' : q'.card ^ 5 = q.card := hf
          have hQ := h3 (hf'.trans (hq2 q (hd1 : q.p = 2 ∧ q.card ≠ 2).1))
          exact hfin orderE7 hM hQ (orderE7_pow_five_d4n hQ) rfl (by rw [hf']; rfl)
        | _ => exact (hs : False).elim
      | reeF4 k =>
        cases e with
        | reeF4 k' =>
          have hf' : (2 ^ (2 * k' + 1)) ^ 5 = 2 ^ (2 * k + 1) := hf
          have hQ := h3 hf'
          exact hfin orderTwistedF4 hM hQ (orderTwistedF4_pow_five_d4n hQ) rfl (by rw [hf']; rfl)
        | _ => exact (hs : False).elim
      | _ => exact (hd1 : False).elim
    · exact (hd1 : False).elim
    · exact (hd1 : False).elim
    ·
      have hU : lieOrderFormula (.twistedA 2 q') = 6048 := by
        show orderTwistedA 2 q'.card = 6048
        rw [hq']
        decide
      have hG : lieOrderFormula (.G2 q) = orderG2 32 := by
        show orderG2 q.card = orderG2 32
        rw [show q.card = 32 from hf]
      rw [hcard, hU, hG]
      exact ⟨by norm_num, by decide⟩
    · exact (hd1 : False).elim
    ·
      have hk : 2 * k + 1 = 5 := Nat.pow_right_injective (le_refl 2) hf
      have hT : lieOrderFormula .tits = orderTits := rfl
      have hR : lieOrderFormula (.reeF4 k) = orderTwistedF4 32 := by
        show orderTwistedF4 (2 ^ (2 * k + 1)) = orderTwistedF4 32
        rw [hk]
        norm_num
      rw [hcard, hT, hR]
      exact ⟨by unfold orderTits; norm_num, by unfold orderTits; decide⟩
    · exact (hd1 : False).elim

end Arith

section Components

variable {Γ : Type*} [Group Γ]

theorem isComponent_subgroupOf_d4n {Q H : Subgroup Γ} (hQ : CFSG.Open.IsComponentOf Q H) :
    CFSG.IsComponent (Q.subgroupOf H) :=
  (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hQ.1).1
    (CFSG.Assembly.isComponentOf_iff_open.2 hQ)

theorem eq_or_commute_of_isComponentOf_d4n [Finite Γ] {Q₁ Q₂ H : Subgroup Γ}
    (h₁ : CFSG.Open.IsComponentOf Q₁ H) (h₂ : CFSG.Open.IsComponentOf Q₂ H) :
    Q₁ = Q₂ ∨ ⁅Q₁, Q₂⁆ = ⊥ := by
  rcases CFSG.LocalCores.distinct_components_commute (isComponent_subgroupOf_d4n h₁)
    (isComponent_subgroupOf_d4n h₂) with he | hc
  · left
    rw [Subgroup.subgroupOf_inj, inf_eq_left.2 h₁.1, inf_eq_left.2 h₂.1] at he
    exact he
  · right
    have := congrArg (Subgroup.map H.subtype) hc
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h₁.1,
      Subgroup.map_subgroupOf_eq_of_le h₂.1, Subgroup.map_bot] at this

theorem card_centerQuot_mul_dvd_of_commute_d4n [Finite Γ] {T J : Subgroup Γ} (hc : ⁅T, J⁆ = ⊥) :
    Nat.card (↥T ⧸ Subgroup.center ↥T) * Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card Γ := by
  have hle : T ≤ Subgroup.centralizer J := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have hcomm : ∀ t ∈ T, ∀ j ∈ J, t * j = j * t := fun t ht j hj =>
    ((Subgroup.mem_centralizer_iff.mp (hle ht)) j hj).symm
  let φ : ↥T × ↥J →* Γ := MonoidHom.noncommCoprod T.subtype J.subtype
    (fun t j => hcomm t t.2 j j.2)
  have hφ : ∀ p : ↥T × ↥J, φ p = (p.1 : Γ) * (p.2 : Γ) := fun _ => rfl
  have h1 : Nat.card (↥T × ↥J) = Nat.card φ.range * Nat.card φ.ker := by
    rw [φ.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  let ψ : ↥φ.ker →* ↥T := (MonoidHom.fst ↥T ↥J).comp φ.ker.subtype
  have hker : ∀ p : ↥φ.ker, ((p : ↥T × ↥J).1 : Γ) * ((p : ↥T × ↥J).2 : Γ) = 1 := fun p => by
    rw [← hφ]
    exact p.2
  have hψinj : Function.Injective ψ := by
    intro p p' h
    have h1 : (p : ↥T × ↥J).1 = (p' : ↥T × ↥J).1 := h
    have h2 : ((p : ↥T × ↥J).2 : Γ) = ((p' : ↥T × ↥J).2 : Γ) := by
      have e1 := hker p
      have e2 := hker p'
      rw [h1] at e1
      exact mul_left_cancel (e1.trans e2.symm)
    exact Subtype.ext (Prod.ext h1 (Subtype.ext h2))
  have hψc : ψ.range ≤ Subgroup.center ↥T := by
    rintro _ ⟨p, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro t
    have hpJ : ((p : ↥T × ↥J).1 : Γ) ∈ J := by
      have e1 : ((p : ↥T × ↥J).1 : Γ) = ((p : ↥T × ↥J).2 : Γ)⁻¹ := eq_inv_of_mul_eq_one_left (hker p)
      rw [e1]
      exact J.inv_mem (p : ↥T × ↥J).2.2
    exact Subtype.ext (hcomm t t.2 _ hpJ)
  have h2 : Nat.card φ.ker ∣ Nat.card (Subgroup.center ↥T) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv]
    exact Subgroup.card_dvd_of_le hψc
  obtain ⟨m, hm⟩ := h2
  have hT := (Subgroup.center ↥T).card_eq_card_quotient_mul_card_subgroup
  have hJ := (Subgroup.center ↥J).card_eq_card_quotient_mul_card_subgroup
  have h3 : Nat.card φ.range * Nat.card φ.ker =
      Nat.card (↥T ⧸ Subgroup.center ↥T) * Nat.card (↥J ⧸ Subgroup.center ↥J) *
        (m * Nat.card (Subgroup.center ↥J)) * Nat.card φ.ker := by
    rw [← h1, Nat.card_prod, hT, hJ, hm]
    ring
  have h4 : Nat.card φ.range = Nat.card (↥T ⧸ Subgroup.center ↥T) *
      Nat.card (↥J ⧸ Subgroup.center ↥J) * (m * Nat.card (Subgroup.center ↥J)) :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos h3
  exact (Dvd.intro _ h4.symm).trans (Subgroup.card_subgroup_dvd_card φ.range)

end Components

section Main

set_option linter.unusedSectionVars false

theorem perfectInLayer_restBig_d4n {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {d : TauCeti.ValidLieTypeIndex} (hd : D4UpRestBigIdx d.1)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)) {β : MulAut S} (hβ5 : β ^ 5 = 1)
    (hβ1 : β ≠ 1) : PerfectInLayer β := by
  obtain ⟨hchar, -, -, hfam, -⟩ := restBig_facts_d4n d.2 hd
  have h5 : (5 : ℕ) ≠ d.1.characteristic := by rw [hchar]; norm_num
  rcases hfam with hF | hF
  · exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCentExceptional S hs
      hna d hF he 5 Nat.prime_five (by norm_num) h5 β hβ5 hβ1
  · exact CFSG.HardMathSupport.Dickson.SuzukiReeB.lieSemisimpleCentSuzukiReeTits S hs hna d hF he 5
      Nat.prime_five (by norm_num) h5 β hβ5 hβ1

theorem false_of_pumpup_restBig_d4n (hX : Inputs256p.ExcCompFieldIdx) {K : Type} [Group K]
    [Finite K] (hK : CFSG.LocalAnalysis.GLTheoremA.IsKHat K) {d : TauCeti.ValidLieTypeIndex}
    (hd : D4UpRestBigIdx d.1) (e : (K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group)
    {D : Type} [Group D] (hD : CFSG.Models.LieModel D .POmegaPlus 4 2 1) {x : MulAut K}
    (hx : Lemma1314.PumpupVia 5 D K x) : False := by
  have hb : LieOrderBridge := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  obtain ⟨hβ5, hβ1⟩ := Claims1110m.autCenterQuot_facts_d4cls hK.1 hx.1
  have hna := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.1
  have hs : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.1.2
  obtain ⟨hchar, hd4, -, -, hsz⟩ := restBig_facts_d4n d.2 hd
  have h5 : (5 : ℕ) ≠ d.1.characteristic := by rw [hchar]; norm_num
  have hlay : PerfectInLayer (autCenterQuot K x) :=
    perfectInLayer_restBig_d4n hs hna hd ⟨e⟩ hβ5 hβ1
  obtain ⟨T, hT, hTc⟩ := Claims1110m.exists_d4_component_d4cls hD hK.1 hx hlay
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ e.toEquiv
  have hS : Nat.card (K ⧸ Subgroup.center K) = lieOrderFormula d.1 := hb d _ ⟨e⟩
  by_cases hmem : autCenterQuot K x ∈ innAutDerived (K ⧸ Subgroup.center K)
  ·
    obtain ⟨i, ⟨φ⟩, hi⟩ := Inputs256p.compIdxAt_of_excCompFieldIdx hX e Nat.prime_five
      (by norm_num) h5 _ hmem hβ5 hβ1 T hT
    exact card_ne_of_compRelC_d4n hb hd4 hi φ hTc
  ·
    have h5S : 5 ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group := by
      rw [← Nat.card_congr e.toEquiv]
      exact ((show 5 ∣ 174182400 by norm_num).trans
        (hTc ▸ Subgroup.card_quotient_dvd_card _)).trans (Subgroup.card_subgroup_dvd_card T)
    have hout : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OuterIdxAt 5 d.1 (K ⧸ Subgroup.center K) :=
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.outerIdxAt_of_mulEquiv Nat.prime_five e.symm
        (GLTheoremA.KD264Lie.kd264OuterIdx_of_families GLTheoremA.KD264Lie.lieOuterIdx_linear
            GLTheoremA.KD264Lie.lieOuterIdx_unitary GLTheoremA.KD264Lie.lieOuterIdx_classicalBCD
            GLTheoremA.KD264Lie.lieOuterIdx_triality GLTheoremA.KD264Lie.lieOuterIdx_excUntwisted
            GLTheoremA.KD264Lie.lieOuterIdx_excTwisted d 5 Nat.prime_five (by norm_num)
          h5 h5S (fun h => absurd h.1 (by norm_num)) (fun h => hsz h.2))
    obtain ⟨J, hJ, -, i, ⟨φ⟩, hi⟩ := hout _ hβ5 hmem
    have hJc : CFSG.Open.IsComponentOf J (fixSubgroup (autCenterQuot K x)) :=
      (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJ
        (hlay J hJ.1 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ))).1
    obtain ⟨hne, hndvd⟩ := subRelC_five_facts_d4n hb hd hi φ
    rcases eq_or_commute_of_isComponentOf_d4n hT hJc with rfl | hc
    · exact hne hTc
    · apply hndvd
      rw [← hS, ← hTc]
      exact card_centerQuot_mul_dvd_of_commute_d4n hc

theorem noD4UpOn_restBig_of_exc_d4n (hX : Inputs256p.ExcCompFieldIdx) :
    Claims1110m.NoD4UpOn D4UpRestBigIdx := by
  intro K _ _ hK _ d hd ⟨e⟩ D _ hD x hx
  exact false_of_pumpup_restBig_d4n hX hK hd e hD hx

theorem noD4UpOn_rest_of_exc_d4n (hX : Inputs256p.ExcCompFieldIdx)
    (hE8 : Claims1110m.NoD4UpOn D4UpE8TwoIdx) : Claims1110m.NoD4UpOn Claims1110m.D4UpRestIdx := by
  intro K _ _ hK hO d hd he D _ hD x hx
  by_cases h8 : D4UpE8TwoIdx d.1
  · exact hE8 K hK hO d h8 he D hD x hx
  · exact noD4UpOn_restBig_of_exc_d4n hX K hK hO d ⟨hd, h8⟩ he D hD x hx

end Main

section E8Two

@[expose] def E8TwoNoD4Comp : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, D4UpE8TwoIdx d.1 →
    ∀ β : MulAut (TauCeti.CFSGIndex.lie d).Group, β ^ 5 = 1 → β ≠ 1 →
      ∀ T : Subgroup (TauCeti.CFSGIndex.lie d).Group, CFSG.Open.IsComponentOf T (fixSubgroup β) →
        Nat.card (↥T ⧸ Subgroup.center ↥T) ≠ 174182400

set_option linter.unusedSectionVars false

theorem noD4UpOn_e8Two_of_noD4Comp_d4n (h : E8TwoNoD4Comp) :
    Claims1110m.NoD4UpOn D4UpE8TwoIdx := by
  intro K _ _ hK _ d hd ⟨e⟩ D _ hD x hx
  obtain ⟨hβ5, hβ1⟩ := Claims1110m.autCenterQuot_facts_d4cls hK.1 hx.1
  have hna := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.1
  have hs : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.1.2
  obtain ⟨q, hdq, hq2⟩ := hd
  have hp : q.p = 2 := by
    have h1 : q.p ∣ q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact dvd_pow_self _ q.exponent_pos.ne'
    rw [hq2] at h1
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h1
  have hF : CFSG.Yardstones.Md42047359a2a.lieFamily d.1 = .exceptional := by rw [hdq]; rfl
  have h5 : (5 : ℕ) ≠ d.1.characteristic := by
    rw [hdq, TauCeti.LieTypeIndex.characteristic_E8, hp]
    norm_num
  have hlay : PerfectInLayer (autCenterQuot K x) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCentExceptional
      (K ⧸ Subgroup.center K) hs hna d hF ⟨e⟩ 5 Nat.prime_five (by norm_num) h5 _ hβ5 hβ1
  obtain ⟨T, hT, hTc⟩ := Claims1110m.exists_d4_component_d4cls hD hK.1 hx hlay
  refine h d ⟨q, hdq, hq2⟩ (MulAut.congr e (autCenterQuot K x)) ?_ ?_ _
    (InputsL33.isComponentOf_map_congr e hT) (Claims1110m.card_centerQuot_map_d4cls e hTc)
  · rw [← map_pow, hβ5, map_one]
  · intro h1
    exact hβ1 ((MulAut.congr e).injective (h1.trans (map_one _).symm))

theorem noD4UpOn_rest_of_exc_of_e8_d4n (hX : Inputs256p.ExcCompFieldIdx) (hE8 : E8TwoNoD4Comp) :
    Claims1110m.NoD4UpOn Claims1110m.D4UpRestIdx :=
  noD4UpOn_rest_of_exc_d4n hX (noD4UpOn_e8Two_of_noD4Comp_d4n hE8)

end E8Two

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110n
