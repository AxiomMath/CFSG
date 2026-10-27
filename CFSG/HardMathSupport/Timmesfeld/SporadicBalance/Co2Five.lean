module

public import CFSG.RankThree.Native.Co2FiveCentralizers
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OuterTrivial

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.RankThree.Native
  CFSG.Sporadic.Co2Cert CFSG.Blueprint

section Generic

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem eq_bot_of_normal_simple {p : ℕ} (hp : p.Prime) {C D M : Subgroup G} (hDC : D ≤ C)
    (hDn : ∀ g ∈ C, ∀ d ∈ D, g * d * g⁻¹ ∈ D) (hDs : IsSimpleGroup D) (hpD : p ∣ Nat.card D)
    (hcent : IsPGroup p ↥(Subgroup.centralizer (D : Set G) ⊓ C)) (hMC : M ≤ C)
    (hMn : ∀ g ∈ C, ∀ m ∈ M, g * m * g⁻¹ ∈ M) (hM : Nat.Coprime p (Nat.card M)) : M = ⊥ := by
  have hnorm : ((M ⊓ D).subgroupOf D).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨hMn g (hDC g.2) x hx.1, hDn g (hDC g.2) x hx.2⟩
  have hMD : M ⊓ D = ⊥ := by
    have := hDs
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((M ⊓ D).subgroupOf D) with h | h
    · rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hx.2⟩ : ↥D) ∈ (M ⊓ D).subgroupOf D := Subgroup.mem_subgroupOf.2 hx
      rw [h, Subgroup.mem_bot] at hx'
      exact (Subgroup.mem_bot).2 (congrArg Subtype.val hx')
    · exfalso
      have hDM : D ≤ M := fun d hd => by
        have : (⟨d, hd⟩ : ↥D) ∈ (M ⊓ D).subgroupOf D := by rw [h]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.1 this).1
      have hpM : p ∣ Nat.card M := hpD.trans (Subgroup.card_dvd_of_le hDM)
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hM hpM
  rw [eq_bot_iff]
  intro m hm
  rw [Subgroup.mem_bot]
  have hmc : m ∈ Subgroup.centralizer (D : Set G) ⊓ C := by
    refine Subgroup.mem_inf.2 ⟨?_, hMC hm⟩
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h1 : m * d * m⁻¹ * d⁻¹ ∈ M := by
      have h2 : d * m⁻¹ * d⁻¹ ∈ M := hMn d (hDC hd) m⁻¹ (M.inv_mem hm)
      have := M.mul_mem hm h2
      simpa [mul_assoc] using this
    have h2 : m * d * m⁻¹ * d⁻¹ ∈ D := D.mul_mem (hDn m (hMC hm) d hd) (D.inv_mem hd)
    have h3 : m * d * m⁻¹ * d⁻¹ = 1 := by
      have : m * d * m⁻¹ * d⁻¹ ∈ M ⊓ D := ⟨h1, h2⟩
      rw [hMD] at this
      exact this
    calc d * m = (m * d * m⁻¹ * d⁻¹)⁻¹ * (m * d) := by group
      _ = m * d := by rw [h3, inv_one, one_mul]
  obtain ⟨k, hk⟩ := hcent ⟨m, hmc⟩
  have hmk : m ^ p ^ k = 1 := congrArg Subtype.val hk
  have hord : orderOf (⟨m, hm⟩ : ↥M) ∣ Nat.card M := orderOf_dvd_natCard _
  have hordp : orderOf (⟨m, hm⟩ : ↥M) ∣ p ^ k := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_dvd_of_pow_eq_one hmk
  have h1 : orderOf (⟨m, hm⟩ : ↥M) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hordp (Nat.Coprime.pow_left k hM)) hord
  rw [orderOf_eq_one_iff] at h1
  exact congrArg Subtype.val h1

omit [Finite G] in
theorem gLAPPrimeCoreOf_eq_bot_of_ambient [Finite G] {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (s : ↥H)
    (h : ∀ M : Subgroup G, M ≤ Subgroup.centralizer ({(s : G)} : Set G) ⊓ H →
      (∀ g ∈ Subgroup.centralizer ({(s : G)} : Set G) ⊓ H, ∀ m ∈ M, g * m * g⁻¹ ∈ M) →
      Nat.Coprime p (Nat.card M) → M = ⊥) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set ↥H)) = ⊥ := by
  set N := GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set ↥H)) with hN
  have hNC : N ≤ Subgroup.centralizer ({s} : Set ↥H) := GLAPPrimeCoreOf_le _
  refine (Subgroup.map_eq_bot_iff_of_injective N H.subtype_injective).1 (h _ ?_ ?_ ?_)
  · rintro _ ⟨n, hn, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, n.2⟩
    show (n : G) ∈ Subgroup.centralizer ({(s : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 (hNC hn))
  · rintro g ⟨hgs, hgH⟩ _ ⟨n, hn, rfl⟩
    have hgs' : (⟨g, hgH⟩ : ↥H) ∈ Subgroup.centralizer ({s} : Set ↥H) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hgs)
    exact ⟨_, GLAPPrimeCoreOf_conj_mem _ hgs' n hn, rfl⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact coprime_card_GLAPPrimeCoreOf hp _

omit [Finite G] in
theorem centralizer_eq_of_zpowers_eq {a b : G} (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  have e : ∀ c : G, Subgroup.centralizer ({c} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers c : Set G) := fun c => by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [e a, e b, h]

end Generic

section Co2Five


theorem factorization_card_co2P_five : (Nat.card co2P).factorization 5 = 3 := by
  rw [card_co2P, show (42305421312000 : ℕ) = 5 ^ 3 * 338443370496 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem eq_bot_of_le_co2FiveC0 {M : Subgroup (Equiv.Perm (Fin 2300))} (hMC : M ≤ co2FiveC0)
    (hMn : ∀ g ∈ co2FiveC0, ∀ m ∈ M, g * m * g⁻¹ ∈ M) (hM : Nat.Coprime 5 (Nat.card M)) :
    M = ⊥ := by
  obtain ⟨-, -, -, -, -, -, hAC, hAn, hAcard, -, -, hAcent, -⟩ :=
    R3E_Co2_full_five_centralizer_structures
  have hAp : IsPGroup 5 co2FiveA := IsPGroup.of_card (n := 3) (by rw [hAcard]; norm_num)
  have hAn' : ∀ g ∈ co2FiveC0, ∀ a ∈ co2FiveA, g * a * g⁻¹ ∈ co2FiveA := by
    intro g hg a ha
    have := hAn.conj_mem ⟨a, hAC ha⟩ (Subgroup.mem_subgroupOf.2 ha) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hcore := gLAPPrimeCoreOf_eq_bot_of_pConstrained Nat.prime_five hAC hAn' hAp
    (by rw [inf_comm]; exact hAcent)
  have hle := le_GLAPPrimeCoreOf_of_normal hMC hMn hM
  rw [hcore] at hle
  exact le_bot_iff.1 hle

theorem eq_bot_of_le_co2FiveC1 {M : Subgroup (Equiv.Perm (Fin 2300))} (hMC : M ≤ co2FiveC1)
    (hMn : ∀ g ∈ co2FiveC1, ∀ m ∈ M, g * m * g⁻¹ ∈ M) (hM : Nat.Coprime 5 (Nat.card M)) :
    M = ⊥ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hDs, -, hDcard, -, hDcent5⟩ :=
    R3E_Co2_full_five_centralizer_structures
  have hDC : co2FiveD ≤ co2FiveC1 := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact co2FiveC1.mul_mem (co2FiveC1.mul_mem (co2FiveC1.mul_mem ha hb) (co2FiveC1.inv_mem ha))
      (co2FiveC1.inv_mem hb)
  have hDn : ∀ g ∈ co2FiveC1, ∀ d ∈ co2FiveD, g * d * g⁻¹ ∈ co2FiveD := by
    intro g hg d hd
    have hmap : co2FiveD.map (MulAut.conj g).toMonoidHom = co2FiveD := by
      have hC : co2FiveC1.map (MulAut.conj g).toMonoidHom = co2FiveC1 := by
        ext y
        constructor
        · rintro ⟨c, hc, rfl⟩
          exact co2FiveC1.mul_mem (co2FiveC1.mul_mem hg hc) (co2FiveC1.inv_mem hg)
        · intro hy
          refine ⟨g⁻¹ * y * g, co2FiveC1.mul_mem (co2FiveC1.mul_mem (co2FiveC1.inv_mem hg) hy) hg,
            ?_⟩
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
      rw [co2FiveD, Subgroup.map_commutator, hC]
    rw [← hmap]
    exact ⟨d, hd, rfl⟩
  exact eq_bot_of_normal_simple Nat.prime_five hDC hDn hDs (by rw [hDcard]; norm_num)
    (IsPGroup.of_card (n := 1) (by rw [hDcent5, pow_one])) hMC hMn hM

theorem oPrimeCoreTrivialAt_co2P_five : OPrimeCoreTrivialAt 5 ↥co2P := by
  obtain ⟨⟨hQP, -, hQcard, -⟩, ⟨hlines, -⟩, htrans, -, hC0, -, -, -, -, -, -, -, hC1, -⟩ :=
    R3E_Co2_full_five_centralizer_structures
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hbase : ∀ i : Fin 2, ∀ r : ↥co2P, (r : Equiv.Perm (Fin 2300)) =
      co2FiveLine (co2FiveRepLine i) →
      GLAPPrimeCoreOf 5 (Subgroup.centralizer ({r} : Set ↥co2P)) = ⊥ := by
    intro i r hr
    refine gLAPPrimeCoreOf_eq_bot_of_ambient Nat.prime_five r fun M hM hMn hMc => ?_
    rw [hr] at hM hMn
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · have e : co2FiveLine (co2FiveRepLine 0) = co2FiveLine 0 := rfl
      rw [e, ← hC0] at hM hMn
      exact eq_bot_of_le_co2FiveC0 hM hMn hMc
    · have e : co2FiveLine (co2FiveRepLine 1) = co2FiveLine 1 := rfl
      rw [e, ← hC1] at hM hMn
      exact eq_bot_of_le_co2FiveC1 hM hMn hMc
  intro s hs
  have hso : orderOf (s : Equiv.Perm (Fin 2300)) = 5 := by rw [Subgroup.orderOf_coe]; exact hs
  obtain ⟨g, hgP, hgQ⟩ := Co3T.exists_conj_mem_of_full hQP
    (by rw [hQcard, factorization_card_co2P_five]; norm_num) s.2 hso
  set t := g⁻¹ * (s : Equiv.Perm (Fin 2300)) * g with htdef
  have htP : t ∈ co2P := co2P.mul_mem (co2P.mul_mem (co2P.inv_mem hgP) s.2) hgP
  have hto : orderOf t = 5 := by
    have := (MulAut.conj g⁻¹ : Equiv.Perm (Fin 2300) ≃* Equiv.Perm (Fin 2300)).orderOf_eq
      (s : Equiv.Perm (Fin 2300))
    simpa [MulAut.conj_apply, htdef, hso] using this
  have hmem : Subgroup.zpowers t ∈
      {H : Subgroup (Equiv.Perm (Fin 2300)) | H ≤ co2FiveQ ∧ Nat.card H = 5} :=
    ⟨(Subgroup.zpowers_le).2 hgQ, by rw [Nat.card_zpowers, hto]⟩
  rw [hlines] at hmem
  obtain ⟨j, hj⟩ := hmem
  obtain ⟨hhP, hconj⟩ := htrans j
  set h := co2FiveTransporter j with hhdef
  set r := co2FiveLine (co2FiveRepLine (co2FiveRecordOf j)) with hrdef
  have hlP : co2FiveLine j ∈ co2P := by
    have : co2FiveLine j ∈ Subgroup.zpowers t := by
      rw [← hj]
      exact Subgroup.mem_zpowers _
    exact (Subgroup.zpowers_le.2 htP) this
  have hrP : r ∈ co2P := by
    have e : r = h⁻¹ * co2FiveLine j * h := by rw [← hconj]; group
    rw [e]
    exact co2P.mul_mem (co2P.mul_mem (co2P.inv_mem hhP) hlP) hhP
  set g' : ↥co2P := ⟨g, hgP⟩
  set t' : ↥co2P := ⟨t, htP⟩
  set h' : ↥co2P := ⟨h, hhP⟩
  set r' : ↥co2P := ⟨r, hrP⟩
  set l' : ↥co2P := ⟨co2FiveLine j, hlP⟩
  have hs' : s = g' * t' * g'⁻¹ := Subtype.ext (by
    show (s : Equiv.Perm (Fin 2300)) = g * (g⁻¹ * (s : Equiv.Perm (Fin 2300)) * g) * g⁻¹
    group)
  have hl' : l' = h' * r' * h'⁻¹ := Subtype.ext hconj.symm
  have hcent : Subgroup.centralizer ({t'} : Set ↥co2P) =
      Subgroup.centralizer ({l'} : Set ↥co2P) := by
    have e := centralizer_eq_of_zpowers_eq hj
    ext c
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hc
      apply Subtype.ext
      have h1 : (c : Equiv.Perm (Fin 2300)) ∈ Subgroup.centralizer ({t} : Set _) :=
        Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hc)
      rw [← e] at h1
      exact Subgroup.mem_centralizer_singleton_iff.1 h1
    · intro hc
      apply Subtype.ext
      have h1 : (c : Equiv.Perm (Fin 2300)) ∈ Subgroup.centralizer ({co2FiveLine j} : Set _) :=
        Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hc)
      rw [e] at h1
      exact Subgroup.mem_centralizer_singleton_iff.1 h1
  rw [hs', gLAPPrimeCoreOf_centralizer_conj, hcent, hl', gLAPPrimeCoreOf_centralizer_conj]
  exact hbase _ r' rfl


theorem oPrimeCoreTrivialAt_Co2_five : OPrimeCoreTrivialAt 5 NativeSporadic.Co2 :=
  OPrimeCoreTrivialAt.of_mulEquiv co2PermEquiv oPrimeCoreTrivialAt_co2P_five

theorem sporadicOPrimeHolds_Co2_five : SporadicOPrimeHolds .Co2 5 := by
  intro S _ _ _ ⟨e⟩
  have e0 : S ≃* NativeSporadic.Co2 := e
  exact OPrimeCoreTrivialAt.of_mulEquiv (e0.trans co2PermEquiv) oPrimeCoreTrivialAt_co2P_five

theorem sporadicOnePairHolds_Co2_five :
    SporadicOnePairHolds .Co2 5 :=
  ⟨sporadicOPrimeHolds_Co2_five, sporadicOuterHolds_Co2 5⟩

end Co2Five

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
