module

public import CFSG.LocalAnalysis.GL83PartI.I_33
public import CFSG.LocalAnalysis.GLTheoremB.Lemma23Proof
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type*} [Group G]

theorem mem_gLAPPrimeCore_of_mem_oPrimeP {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Type*}
    [Group H] {c : H} (hc : c ∈ oPrimeP p H) {n : ℕ} (hn : orderOf c = 2 ^ n) :
    c ∈ GLAPPrimeCore p H := by
  have : Fact p.Prime := ⟨hp⟩
  have hc' : QuotientGroup.mk' (GLAPPrimeCore p H) c ∈ CFSG.pCore p (H ⧸ GLAPPrimeCore p H) := hc
  have hpg : IsPGroup p (CFSG.pCore p (H ⧸ GLAPPrimeCore p H)) := CFSG.pCore_isPGroup
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.1 hpg ⟨_, hc'⟩
  have h1 : orderOf (QuotientGroup.mk' (GLAPPrimeCore p H) c) = p ^ m := by
    have := Subgroup.orderOf_coe (⟨_, hc'⟩ : CFSG.pCore p (H ⧸ GLAPPrimeCore p H))
    rw [hm] at this
    exact this
  have h2 : p ^ m ∣ 2 ^ n := by
    rw [← h1, ← hn]
    exact orderOf_map_dvd _ c
  have hm0 : m = 0 := by
    by_contra hm0
    have h3 : p ∣ 2 ^ n := (dvd_pow_self p hm0).trans h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3))
  rw [hm0, pow_zero, orderOf_eq_one_iff] at h1
  exact (QuotientGroup.eq_one_iff c).1 h1

theorem comm_mem_gLAPPrimeCoreOf_of_mem_oPrimePOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {C S : Subgroup G} (hS2 : IsPGroup 2 S) (hSC : S ≤ C) {y : G} (hy : y ∈ oPrimePOf p C)
    (hyS : y ∈ Subgroup.normalizer (S : Set G)) {s : G} (hs : s ∈ S) :
    s * y * s⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf p C := by
  obtain ⟨y', hy', rfl⟩ := hy
  set s' : C := ⟨s, hSC hs⟩ with hs'
  have hc1 : s' * y' * s'⁻¹ * y'⁻¹ ∈ oPrimeP p C := by
    have h1 : s' * y' * s'⁻¹ ∈ oPrimeP p C := (oPrimeP.normal p C).conj_mem y' hy' s'
    exact mul_mem h1 (inv_mem hy')
  have hval : ((s' * y' * s'⁻¹ * y'⁻¹ : C) : G) = s * (y' : G) * s⁻¹ * (y' : G)⁻¹ := by
    simp [hs']
  have hcS : s * (y' : G) * s⁻¹ * (y' : G)⁻¹ ∈ S := by
    have h1 : (y' : G) * s⁻¹ * (y' : G)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.1 hyS s⁻¹).1 (S.inv_mem hs)
    have := S.mul_mem hs h1
    simpa [mul_assoc] using this
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.1 hS2 ⟨_, hcS⟩
  have hn' : orderOf (s' * y' * s'⁻¹ * y'⁻¹ : C) = 2 ^ n := by
    rw [← Subgroup.orderOf_coe, hval, ← hn]
    exact (Subgroup.orderOf_coe (⟨_, hcS⟩ : S)).symm ▸ rfl
  exact ⟨_, mem_gLAPPrimeCore_of_mem_oPrimeP hp hp2 hc1 hn', hval⟩

theorem mem_normalizer_inf_centralizer {T E : Subgroup G} {b : G}
    (hbT : b ∈ Subgroup.normalizer (T : Set G)) (hcomm : ∀ a ∈ E, Commute a b) :
    b ∈ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hbT' := Subgroup.mem_normalizer_iff.1 hbT h
  constructor
  · rintro ⟨hhT, hhC⟩
    exact ⟨hbT'.1 hhT, GL83.mul_mul_inv_mem_centralizer_of_commute hcomm hhC⟩
  · rintro ⟨hhT, hhC⟩
    refine ⟨hbT'.2 hhT, ?_⟩
    have := GL83.mul_mul_inv_mem_centralizer_of_commute (A := E) (b := b⁻¹) (h := b * h * b⁻¹)
      (fun a ha => (hcomm a ha).inv_right) hhC
    simpa [mul_assoc] using this

theorem lemma28_isBZeroMax {G : Type} [Group G] [Finite G] {m : ℕ} (hS : GLStanding G m 3)
    {B : Subgroup G} (hB : IsElemAbelian 3 B) (hrank : GLATwoLocalRank 3 G ≤ CFSG.Open.pRank 3 B)
    {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) {A : Subgroup G} {k : ℕ} (hk : 3 ≤ k)
    (hA : IsEkIn 3 k B A)
    (hT : ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ A ≤ Subgroup.normalizer (T : Set G))
    (hbA : b ∈ A)
    (hcore : ∀ a ∈ A, a ≠ 1 → b ∈ oPrimePOf 3 (Subgroup.centralizer ({a} : Set G))) :
    IsBZeroMax 3 B := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAB, hAe, hAcard⟩ := hA
  obtain ⟨T₀, hT₀ne, hT₀2, hAT₀⟩ := hT
  let S0 : Set (Subgroup G) :=
    {T' | IsPGroup 2 T' ∧ A ≤ Subgroup.normalizer (T' : Set G) ∧ T₀ ≤ T'}
  obtain ⟨T, hTS, hTmax⟩ := (Set.toFinite S0).exists_maximalFor id S0 ⟨T₀, hT₀2, hAT₀, le_rfl⟩
  obtain ⟨hT2, hAT, hT₀T⟩ := hTS
  have hTne : T ≠ ⊥ := fun h => hT₀ne (le_bot_iff.1 (h ▸ hT₀T))
  have hmax : ∀ T' : Subgroup G, IsPGroup 2 T' → A ≤ Subgroup.normalizer (T' : Set G) →
      T ≤ T' → T' = T := fun T' h2 hN hle =>
    le_antisymm (hTmax ⟨h2, hN, hT₀T.trans hle⟩ hle) hle
  have hAne : A ≠ ⊥ := fun h => hb1 (Subgroup.mem_bot.1 (h ▸ hbA))
  obtain ⟨A₁, hA₁A, hA₁i, hne⟩ :=
    (GL83.I_33_1_proved G hS.charTwo 3 hp3 (by norm_num) A T hAne hAe hT2 hAT
      (Or.inl ⟨hTne, hmax⟩)).1 b hbA hb1
  have hA₁e : IsElemAbelian 3 A₁ := isElemAbelian_mono hAe hA₁A
  have hcardA₁ : Nat.card A₁ = 3 ^ (k - 1) := by
    have h1 : Nat.card A = Nat.card (A₁.subgroupOf A) * (A₁.subgroupOf A).index :=
      (Subgroup.card_mul_index _).symm
    have h2 : Nat.card (A₁.subgroupOf A) = Nat.card A₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁A).toEquiv
    rw [h2, hA₁i, hAcard] at h1
    have h3 : 3 ^ k = 3 ^ (k - 1) * 3 := by
      rw [← pow_succ]; congr 1; omega
    rw [h3] at h1
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h1).symm
  obtain ⟨E, hEA₁, hEe, hEcard⟩ := exists_le_isElemAbelian_card (p := 3) hA₁e (n := 2)
    (by rw [hcardA₁]; exact pow_dvd_pow 3 (by omega))
  have hEA : E ≤ A := hEA₁.trans hA₁A
  have hEB : E ≤ B := hEA.trans hAB
  have hE0 : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hEcard
    omega
  set X : Subgroup G := T ⊓ Subgroup.centralizer (E : Set G) with hXdef
  have hbT : b ∈ Subgroup.normalizer (T : Set G) := hAT hbA
  have hbX : b ∈ Subgroup.normalizer (X : Set G) :=
    mem_normalizer_inf_centralizer hbT fun a ha => elemAbelian_comm hAe (hEA ha) hbA
  have hbdn : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    Subgroup.le_normalizer
  have hPX : Subgroup.zpowers b ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.zpowers_le.2 hbX
  have hX2 : IsPGroup 2 X := hT2.to_le inf_le_left
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers b)) (Nat.card X) := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hAe.2 b hbA) hb1]
    obtain ⟨j, hj⟩ := hX2.exists_card_eq
    rw [hj]
    exact Nat.Coprime.pow_right j (by norm_num)
  have hsolv : Group.IsSolvable X := by
    have := IsPGroup.isNilpotent hX2
    infer_instance
  have hdouble : ⁅⁅X, Subgroup.zpowers b⁆, Subgroup.zpowers b⁆ = ⁅X, Subgroup.zpowers b⁆ :=
    GL83.commutator_double_eq_self (Subgroup.zpowers b) X hPX hcop hsolv
  set S : Subgroup G := ⁅X, Subgroup.zpowers b⁆ with hSdef
  have hSne : S ≠ ⊥ := by
    intro h
    apply hne
    have h' : ⁅Subgroup.zpowers b, X⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h
    refine eq_bot_iff.2 ((Subgroup.commutator_mono le_rfl ?_).trans h'.le)
    exact inf_le_inf_left _ (Subgroup.centralizer_le fun x hx => hEA₁ hx)
  have hSle : S ≤ X := GL83.commutator_le_of_le_normalizer hPX
  have hS2 : IsPGroup 2 S := hT2.to_le (hSle.trans inf_le_left)
  have hSN : Subgroup.zpowers b ≤ Subgroup.normalizer (S : Set G) :=
    CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer _ X _ hPX hbdn
  have hSC : ∀ e ∈ E, S ≤ Subgroup.centralizer ({e} : Set G) := fun e he =>
    hSle.trans (inf_le_right.trans (Subgroup.centralizer_le fun x hx => by
      rw [Set.mem_singleton_iff.1 hx]; exact he))
  have hSΔ : S ≤ GLADelta 3 E := by
    refine le_iInf fun e => le_iInf fun he => le_iInf fun he1 => ?_
    calc S = ⁅S, Subgroup.zpowers b⁆ := hdouble.symm
      _ ≤ _ := by
        rw [Subgroup.commutator_le]
        intro s hs y hy
        have hyo : y ∈ oPrimePOf 3 (Subgroup.centralizer ({e} : Set G)) :=
          Subgroup.zpowers_le.2 (hcore e (hEA he) he1) hy
        rw [commutatorElement_def]
        exact comm_mem_gLAPPrimeCoreOf_of_mem_oPrimePOf hp3 (by norm_num) hS2 (hSC e he) hyo
          (hSN hy) hs
  have hSeven : 2 ∣ Nat.card S := by
    obtain ⟨n, hn⟩ := hS2.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hSne (Subgroup.card_eq_one.1 (by simpa using hn))
    rw [hn]
    exact dvd_pow_self 2 hn0
  have hSB : S ≤ ⁅GLADelta 3 E, B⁆ := by
    calc S = ⁅S, Subgroup.zpowers b⁆ := hdouble.symm
      _ ≤ ⁅GLADelta 3 E, B⁆ := Subgroup.commutator_mono hSΔ (Subgroup.zpowers_le.2 hb)
  have hΔeven : 2 ∣ Nat.card (GLADelta 3 E) := hSeven.trans (Subgroup.card_dvd_of_le hSΔ)
  have hWcop : Nat.Coprime 3 (Nat.card (GLADelta 3 E)) :=
    CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLADelta hp3 hE0
  have hconj : ∀ e ∈ B, ∀ w ∈ GLADelta 3 E, e * w * e⁻¹ ∈ GLADelta 3 E := by
    intro e he w hw
    simp only [GLADelta, Subgroup.mem_iInf] at hw ⊢
    intro d hd hd1
    have hec : e ∈ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact elemAbelian_comm hB (hEB hd) he
    exact mem_gLAPPrimeCoreOf_conj (hw d hd hd1) hec
  have hBΔ : B ≤ Subgroup.normalizer (GLADelta 3 E : Set G) := fun e he =>
    Subgroup.mem_normalizer_fintype fun n hn => hconj e he n hn
  obtain ⟨Q, -, hQ2, hQc, hBQ⟩ := exists_sylow_normalized_of_not_dvd (q := 2) (GLADelta 3 E) B
    (GL83.isPGroup_of_isElemAbelian hB) hBΔ (hp3.coprime_iff_not_dvd.1 hWcop)
  have hQ1 : Q ≠ ⊥ := by
    intro h
    have h1 := hQc 1 (by simpa using hΔeven)
    rw [h, Subgroup.card_bot] at h1
    simp at h1
  have hloc : IsTwoLocal (Subgroup.normalizer (Q : Set G)) := ⟨Q, hQ1, hQ2, rfl⟩
  obtain ⟨j, hj⟩ := exists_card_eq_pow (GL83.isPGroup_of_isElemAbelian hB)
  have h1 : j ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (Q : Set G)) :=
    CFSG.SectionRank.le_pRank hp3.one_lt hBQ hB hj
  have h2 : CFSG.Open.pRank 3 (Subgroup.normalizer (Q : Set G)) ≤ GLATwoLocalRank 3 G :=
    le_csSup ⟨CFSG.Open.pRank 3 (⊤ : Subgroup G), by
      rintro i ⟨H, -, rfl⟩
      exact CFSG.SectionRank.pRank_mono hp3.one_lt le_top⟩ ⟨_, hloc, rfl⟩
  have h3 : CFSG.Open.pRank 3 B ≤ j := by
    unfold CFSG.Open.pRank
    refine csSup_le' ?_
    rintro i ⟨E', hE'B, -, hE'c⟩
    have := Subgroup.card_dvd_of_le hE'B
    rw [hE'c, hj] at this
    exact (Nat.pow_dvd_pow_iff_le_right hp3.one_lt).1 this
  have hjeq : j = GLATwoLocalRank 3 G := le_antisymm (h1.trans h2) (hrank.trans h3)
  have hBmax : GLAIsBmax 3 B := ⟨hB, hj.trans (by rw [hjeq]), Q, hQ1, hQ2, hBQ⟩
  refine ⟨hBmax, E, hEB, ⟨hEe, hEcard⟩, fun h => absurd h (by norm_num), fun _ => ?_⟩
  exact even_iff_two_dvd.2 (hSeven.trans (Subgroup.card_dvd_of_le hSB))

end CFSG.HardMathSupport.Solomon.LocalBalance
