module

public import CFSG.LocalAnalysis.GLTheoremB.BaseCase
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.Section2.CoprimeTools
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace GL83

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] def I_33_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsCharTwoType G → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ D B : Subgroup G, D ≠ ⊥ → D ≤ B → IsElemAbelian p B →
      (∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G)) →
      ∃ A S : Subgroup G, A ≤ D ∧ (A.subgroupOf D).index = p ∧ S ≤ Subgroup.centralizer (A : Set G) ∧
        IsPGroup 2 S ∧ S = ⁅S, D⁆ ∧ S = ⁅S, B⁆ ∧ S ≠ ⊥

@[expose] def I_33_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsCharTwoType G → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ N B I : Subgroup G, IsTwoLocal N → B ≠ ⊥ → IsElemAbelian p B → B ≤ N →
      I ≤ N ⊓ Subgroup.centralizer (B : Set G) → ¬ IsPGroup 2 I →
      ∃ A : Subgroup G, A ≤ B ∧ (A.subgroupOf B).index = p ∧
        ⁅I, pCoreOf 2 N ⊓ Subgroup.centralizer (A : Set G)⁆ ≠ ⊥

section Proofs

variable {G : Type*} [Group G]

theorem eq_one_of_pow_prime_of_pGroup_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T : Subgroup G}
    (hT : IsPGroup 2 T) {x : G} (hxT : x ∈ T) (hx : x ^ p = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hT) ⟨x, hxT⟩
  have h1 : orderOf x = 2 ^ k := by
    rw [← hk]; exact (Subgroup.orderOf_coe ⟨x, hxT⟩)
  have h2 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hx
  rw [h1] at h2
  rcases (Nat.dvd_prime hp).1 h2 with h | h
  · have : orderOf x = 1 := by rw [h1, h]
    exact orderOf_eq_one_iff.1 this
  · exfalso
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      simp at h
      exact hp.one_lt.ne h
    · have : 2 ∣ p := h ▸ dvd_pow_self 2 hk0.ne'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm

theorem inf_eq_bot_of_elemAbelian_of_pGroup_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B T : Subgroup G} (hB : IsElemAbelian p B) (hT : IsPGroup 2 T) : B ⊓ T = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  exact eq_one_of_pow_prime_of_pGroup_two hp hp2 hT hx.2 (hB.2 x hx.1)

variable [Finite G]

theorem inf_centralizer_eq_bot_of_pCoreOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hchar : IsCharTwoType G) {N B : Subgroup G} (hN : IsTwoLocal N) (hBN : B ≤ N)
    (hB : IsElemAbelian p B) :
    B ⊓ Subgroup.centralizer (pCoreOf 2 N : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (pCoreOf 2 N) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxN : x ∈ N ⊓ Subgroup.centralizer (pCoreOf 2 N : Set G) := ⟨hBN hx.1, hx.2⟩
  exact eq_one_of_pow_prime_of_pGroup_two hp hp2 h2 (hchar N hN hxN) (hB.2 x hx.1)

theorem inf_centralizer_eq_bot_of_maximal {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hchar : IsCharTwoType G) {B T : Subgroup G} (hB : IsElemAbelian p B) (hT2 : IsPGroup 2 T)
    (hBT : B ≤ Subgroup.normalizer (T : Set G)) (hTne : T ≠ ⊥)
    (hmax : ∀ T' : Subgroup G, IsPGroup 2 T' → B ≤ Subgroup.normalizer (T' : Set G) → T ≤ T' →
      T' = T) :
    B ⊓ Subgroup.centralizer (T : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (T : Set G) with hNdef
  have hN : IsTwoLocal N := ⟨T, hTne, hT2, rfl⟩
  have hTN : T ≤ pCoreOf 2 N :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hT2
  have hcore : IsPGroup 2 (pCoreOf 2 N) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  have hBc : B ≤ Subgroup.normalizer (pCoreOf 2 N : Set G) :=
    hBT.trans (le_normalizer_pCoreOf 2 N)
  have hEq : pCoreOf 2 N = T := hmax _ hcore hBc hTN
  rw [← hEq]
  exact inf_centralizer_eq_bot_of_pCoreOf hp hp2 hchar hN hBT hB

theorem le_iSup_hyperplane {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D T : Subgroup G}
    (hDne : D ≠ ⊥) (hD : IsElemAbelian p D) (hT : IsPGroup 2 T)
    (hDT : D ≤ Subgroup.normalizer (T : Set G)) :
    T ≤ ⨆ (A : Subgroup G) (_ : A ≤ D ∧ (A.subgroupOf D).index = p),
      T ⊓ Subgroup.centralizer (A : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).2 hDne
  refine le_iSup_inf_centralizer_hyperplane hD hDT ?_
  intro hdvd
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  rw [hn] at hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))

omit [Finite G] in
theorem comm_zpowers_eq_bot_iff {b : G} {X : Subgroup G} :
    ⁅Subgroup.zpowers b, X⁆ = ⊥ ↔ X ≤ Subgroup.centralizer ({b} : Set G) := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le]
  constructor
  · intro h x hx
    rw [Subgroup.mem_centralizer_iff] at h ⊢
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact (h x hx).symm
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := Subgroup.mem_centralizer_iff.1 (h hx) b rfl
    exact this.symm

omit [Finite G] in
theorem eq_of_le_of_relIndex_eq {A₁ A₂ D : Subgroup G} (h1 : A₁ ≤ A₂) (hA₂ : A₂ ≤ D)
    (hi : (A₁.subgroupOf D).index = (A₂.subgroupOf D).index)
    (hne : (A₂.subgroupOf D).index ≠ 0) : A₁ = A₂ := by
  have h := Subgroup.relIndex_mul_relIndex A₁ A₂ D h1 hA₂
  have h' : A₁.relIndex A₂ * A₂.relIndex D = 1 * A₂.relIndex D := by
    rw [one_mul]; exact h.trans hi
  have h2 : A₁.relIndex A₂ = 1 := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) h'
  exact le_antisymm h1 (Subgroup.relIndex_eq_one.1 h2)

theorem I_33_1_proved :
    ∀ (G : Type) [Group G] [Finite G], IsCharTwoType G → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ B T : Subgroup G, B ≠ ⊥ → IsElemAbelian p B → IsPGroup 2 T →
        B ≤ Subgroup.normalizer (T : Set G) →
        ((T ≠ ⊥ ∧ ∀ T' : Subgroup G, IsPGroup 2 T' → B ≤ Subgroup.normalizer (T' : Set G) →
            T ≤ T' → T' = T) ∨
          (∃ N : Subgroup G, IsTwoLocal N ∧ B ≤ N ∧ T = pCoreOf 2 N) ∨
          B ⊓ Subgroup.centralizer (T : Set G) = ⊥) →
        (∀ b ∈ B, b ≠ 1 → ∃ A : Subgroup G, A ≤ B ∧ (A.subgroupOf B).index = p ∧
            ⁅Subgroup.zpowers b, T ⊓ Subgroup.centralizer (A : Set G)⁆ ≠ ⊥) ∧
        ∀ D : Subgroup G, D ≠ ⊥ → D ≤ B → ¬ IsCyclic D →
          (∃ A₁ A₂ : Subgroup G, A₁ ≠ A₂ ∧ A₁ ≤ D ∧ A₂ ≤ D ∧ (A₁.subgroupOf D).index = p ∧
              (A₂.subgroupOf D).index = p ∧
              ⁅D, T ⊓ Subgroup.centralizer (A₁ : Set G)⁆ ≠ ⊥ ∧
              ⁅D, T ⊓ Subgroup.centralizer (A₂ : Set G)⁆ ≠ ⊥) ∧
          ∃ d₁ d₂ : G, d₁ ∈ D ∧ d₂ ∈ D ∧ d₁ ≠ 1 ∧ d₂ ∉ Subgroup.zpowers d₁ ∧
            ⁅D, T ⊓ Subgroup.centralizer ({d₁} : Set G)⁆ ≠ ⊥ ∧
            ⁅D, T ⊓ Subgroup.centralizer ({d₂} : Set G)⁆ ≠ ⊥ := by
  intro G _ _ hchar p hp hp2 B T hBne hB hT hBT hhyp
  have hc : B ⊓ Subgroup.centralizer (T : Set G) = ⊥ := by
    rcases hhyp with ⟨hTne, hmax⟩ | ⟨N, hN, hBN, hTN⟩ | hc
    · exact inf_centralizer_eq_bot_of_maximal hp hp2 hchar hB hT hBT hTne hmax
    · subst hTN; exact inf_centralizer_eq_bot_of_pCoreOf hp hp2 hchar hN hBN hB
    · exact hc
  constructor
  · intro b hb hb1
    by_contra hcon
    push Not at hcon
    have hle : T ≤ Subgroup.centralizer ({b} : Set G) := by
      refine (le_iSup_hyperplane hp hp2 hBne hB hT hBT).trans (iSup₂_le fun A hA => ?_)
      exact comm_zpowers_eq_bot_iff.1 (hcon A hA.1 hA.2)
    have hbT : b ∈ B ⊓ Subgroup.centralizer (T : Set G) := by
      refine ⟨hb, Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩
      exact (Subgroup.mem_centralizer_iff.1 (hle ht) b rfl).symm
    rw [hc] at hbT
    exact hb1 (Subgroup.mem_bot.1 hbT)
  · intro D hDne hDB hDcyc
    have hDel : IsElemAbelian p D := isElemAbelian_mono hB hDB
    have hDT : D ≤ Subgroup.normalizer (T : Set G) := hDB.trans hBT
    have hgen := le_iSup_hyperplane hp hp2 hDne hDel hT hDT
    have hDc : D ⊓ Subgroup.centralizer (T : Set G) = ⊥ :=
      eq_bot_iff.2 (hc ▸ inf_le_inf_right _ hDB)
    have hcomm : ∀ A : Subgroup G, ⁅D, T ⊓ Subgroup.centralizer (A : Set G)⁆ = ⊥ →
        T ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (D : Set G) := fun A h =>
      Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h)
    have hex : ∃ A : Subgroup G, A ≤ D ∧ (A.subgroupOf D).index = p ∧
        ⁅D, T ⊓ Subgroup.centralizer (A : Set G)⁆ ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      have hle : T ≤ Subgroup.centralizer (D : Set G) :=
        hgen.trans (iSup₂_le fun A hA => hcomm A (hcon A hA.1 hA.2))
      have hD1 : D ≤ Subgroup.centralizer (T : Set G) := Subgroup.le_centralizer_iff.1 hle
      exact hDne (eq_bot_iff.2 (hDc ▸ le_inf le_rfl hD1))
    obtain ⟨A₀, hA₀D, hA₀i, hA₀c⟩ := hex
    have hex2 : ∃ A₁ : Subgroup G, A₁ ≤ D ∧ (A₁.subgroupOf D).index = p ∧
        ⁅D, T ⊓ Subgroup.centralizer (A₁ : Set G)⁆ ≠ ⊥ ∧ A₁ ≠ A₀ := by
      by_contra hcon
      push Not at hcon
      have hle : T ≤ Subgroup.centralizer (A₀ : Set G) := by
        refine hgen.trans (iSup₂_le fun A hA => ?_)
        by_cases hAA : A = A₀
        · subst hAA; exact inf_le_right
        · have hbot : ⁅D, T ⊓ Subgroup.centralizer (A : Set G)⁆ = ⊥ := by
            by_contra h
            exact hAA (hcon A hA.1 hA.2 h)
          exact (hcomm A hbot).trans (Subgroup.centralizer_le fun x hx => hA₀D hx)
      have hA₀c' : A₀ ≤ Subgroup.centralizer (T : Set G) := Subgroup.le_centralizer_iff.1 hle
      have hA₀bot : A₀ = ⊥ := eq_bot_iff.2 (hDc ▸ le_inf hA₀D hA₀c')
      subst hA₀bot
      rw [Subgroup.bot_subgroupOf, Subgroup.index_bot] at hA₀i
      have : Fact p.Prime := ⟨hp⟩
      exact hDcyc (isCyclic_of_prime_card hA₀i)
    obtain ⟨A₁, hA₁D, hA₁i, hA₁c, hA₁ne⟩ := hex2
    have hne0 : (A₀.subgroupOf D).index ≠ 0 := by rw [hA₀i]; exact hp.ne_zero
    have hn10 : ¬ A₁ ≤ A₀ := fun h =>
      hA₁ne (eq_of_le_of_relIndex_eq h hA₀D (hA₁i.trans hA₀i.symm) hne0)
    have hn01 : ¬ A₀ ≤ A₁ := fun h =>
      hA₁ne (eq_of_le_of_relIndex_eq h hA₁D (hA₀i.trans hA₁i.symm)
        (by rw [hA₁i]; exact hp.ne_zero)).symm
    refine ⟨⟨A₁, A₀, hA₁ne, hA₁D, hA₀D, hA₁i, hA₀i, hA₁c, hA₀c⟩, ?_⟩
    obtain ⟨d₁, hd₁A₁, hd₁A₀⟩ := IsConcreteLE.not_le_iff_exists.1 hn10
    obtain ⟨d₂, hd₂A₀, hd₂A₁⟩ := IsConcreteLE.not_le_iff_exists.1 hn01
    refine ⟨d₁, d₂, hA₁D hd₁A₁, hA₀D hd₂A₀, ?_, ?_, ?_, ?_⟩
    · rintro rfl; exact hd₁A₀ (one_mem _)
    · intro h
      exact hd₂A₁ ((Subgroup.zpowers_le.2 hd₁A₁) h)
    · refine fun h => hA₁c (eq_bot_iff.2 ((Subgroup.commutator_mono le_rfl ?_).trans h.le))
      exact inf_le_inf_left _ (Subgroup.centralizer_le (by simpa using hd₁A₁))
    · refine fun h => hA₀c (eq_bot_iff.2 ((Subgroup.commutator_mono le_rfl ?_).trans h.le))
      exact inf_le_inf_left _ (Subgroup.centralizer_le (by simpa using hd₂A₀))

omit [Finite G] in
theorem isPGroup_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

omit [Finite G] in
theorem commutator_le_of_le_normalizer {S B' : Subgroup G}
    (h : B' ≤ Subgroup.normalizer (S : Set G)) : ⁅S, B'⁆ ≤ S := by
  rw [Subgroup.commutator_le]
  intro s hs b hb
  have h1 : b * s⁻¹ * b⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (h hb) s⁻¹).1 (S.inv_mem hs)
  simpa [commutatorElement_def, mul_assoc] using S.mul_mem hs h1

omit [Finite G] in
theorem mul_mul_inv_mem_centralizer_of_commute {A : Subgroup G} {b h : G}
    (hcomm : ∀ a ∈ A, Commute a b) (hh : h ∈ Subgroup.centralizer (A : Set G)) :
    b * h * b⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hh ⊢
  intro a ha
  have h1 : Commute a b := hcomm a ha
  have h2 : a * h = h * a := hh a ha
  calc a * (b * h * b⁻¹) = (a * b) * h * b⁻¹ := by simp [mul_assoc]
    _ = (b * a) * h * b⁻¹ := by rw [h1.eq]
    _ = b * (a * h) * b⁻¹ := by simp [mul_assoc]
    _ = b * (h * a) * b⁻¹ := by rw [h2]
    _ = b * h * (a * b⁻¹) := by simp [mul_assoc]
    _ = b * h * (b⁻¹ * a) := by rw [h1.inv_right.eq]
    _ = (b * h * b⁻¹) * a := by simp [mul_assoc]

theorem I_33_2_proved : I_33_2 := by
  intro G _ _ hchar p hp hp2 D B hDne hDB hB ⟨T₀, hT₀ne, hT₀2, hBT₀⟩
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hBne : B ≠ ⊥ := fun h => hDne (le_bot_iff.1 (h ▸ hDB))
  let S : Set (Subgroup G) :=
    {T' | IsPGroup 2 T' ∧ B ≤ Subgroup.normalizer (T' : Set G) ∧ T₀ ≤ T'}
  obtain ⟨T, hTS, hTmax⟩ := (Set.toFinite S).exists_maximalFor id S ⟨T₀, hT₀2, hBT₀, le_rfl⟩
  obtain ⟨hT2, hBT, hT₀T⟩ := hTS
  have hTne : T ≠ ⊥ := fun h => hT₀ne (le_bot_iff.1 (h ▸ hT₀T))
  have hmax : ∀ T' : Subgroup G, IsPGroup 2 T' → B ≤ Subgroup.normalizer (T' : Set G) →
      T ≤ T' → T' = T := fun T' h2 hN hle =>
    le_antisymm (hTmax ⟨h2, hN, hT₀T.trans hle⟩ hle) hle
  obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hDne (Subgroup.eq_bot_iff_forall _ |>.2 hcon)
  obtain ⟨A₀, hA₀B, hA₀i, hne⟩ :=
    ((I_33_1_proved G hchar p hp hp2 B T hBne hB hT2 hBT (Or.inl ⟨hTne, hmax⟩)).1 d (hDB hdD) hd1)
  set X : Subgroup G := T ⊓ Subgroup.centralizer (A₀ : Set G) with hXdef
  have hBcomm : ∀ b ∈ B, ∀ a ∈ A₀, Commute a b := fun b hb a ha =>
    elemAbelian_comm hB (hA₀B ha) hb
  have hdA₀ : d ∉ A₀ := by
    intro hd
    apply hne
    rw [comm_zpowers_eq_bot_iff]
    intro x hx
    exact Subgroup.mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]
      exact Subgroup.mem_centralizer_iff.1 hx.2 d hd
  have hBX : B ≤ Subgroup.normalizer (X : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hbT := Subgroup.mem_normalizer_iff.1 (hBT hb) h
    constructor
    · rintro ⟨hhT, hhC⟩
      exact ⟨hbT.1 hhT, mul_mul_inv_mem_centralizer_of_commute (hBcomm b hb) hhC⟩
    · rintro ⟨hhT, hhC⟩
      refine ⟨hbT.2 hhT, ?_⟩
      have := mul_mul_inv_mem_centralizer_of_commute (A := A₀) (b := b⁻¹) (h := b * h * b⁻¹)
        (fun a ha => (hBcomm b hb a ha).inv_right) hhC
      simpa [mul_assoc] using this
  have hBd : B ≤ Subgroup.centralizer (Subgroup.zpowers d : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    have h : Commute d b := elemAbelian_comm hB (hDB hdD) hb
    exact (Commute.zpow_left h n).eq
  have hBdn : B ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    hBd.trans (Subgroup.centralizer_le_normalizer _)
  have hdB : Subgroup.zpowers d ≤ B := Subgroup.zpowers_le.2 (hDB hdD)
  have hPX : Subgroup.zpowers d ≤ Subgroup.normalizer (X : Set G) := hdB.trans hBX
  have hX2 : IsPGroup 2 X := hT2.to_le inf_le_left
  have hDel : IsElemAbelian p D := isElemAbelian_mono hB hDB
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers d)) (Nat.card X) := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hB.2 d (hDB hdD)) hd1]
    obtain ⟨k, hk⟩ := hX2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hsolv : Group.IsSolvable X := by
    have := IsPGroup.isNilpotent hX2
    infer_instance
  have hdouble : ⁅⁅X, Subgroup.zpowers d⁆, Subgroup.zpowers d⁆ = ⁅X, Subgroup.zpowers d⁆ :=
    commutator_double_eq_self (Subgroup.zpowers d) X hPX hcop hsolv
  set Ssub : Subgroup G := ⁅X, Subgroup.zpowers d⁆ with hSdef
  have hSne : Ssub ≠ ⊥ := by rwa [hSdef, Subgroup.commutator_comm]
  have hSle : Ssub ≤ X := commutator_le_of_le_normalizer hPX
  have hBS : B ≤ Subgroup.normalizer (Ssub : Set G) :=
    CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer B X (Subgroup.zpowers d) hBX hBdn
  have hcomB : ∀ B' : Subgroup G, Subgroup.zpowers d ≤ B' → B' ≤ B → Ssub = ⁅Ssub, B'⁆ := by
    intro B' h1 h2
    apply le_antisymm
    · calc Ssub = ⁅Ssub, Subgroup.zpowers d⁆ := hdouble.symm
        _ ≤ ⁅Ssub, B'⁆ := Subgroup.commutator_mono le_rfl h1
    · exact commutator_le_of_le_normalizer (h2.trans hBS)
  have hidx : ((A₀ ⊓ D).subgroupOf D).index = p := by
    have h1 : (A₀ ⊓ D).relIndex D = A₀.relIndex D := Subgroup.inf_relIndex_right _ _
    change (A₀ ⊓ D).relIndex D = p
    rw [h1]
    have hle : A₀.relIndex D ≤ A₀.relIndex B :=
      Subgroup.relIndex_le_of_le_right hDB (by change (A₀.subgroupOf B).index ≠ 0; rw [hA₀i]; exact hp.ne_zero)
    have hB' : A₀.relIndex B = p := hA₀i
    have hle' : A₀.relIndex D ≤ p := hB' ▸ hle
    have h2 : A₀.relIndex D ≠ 1 := fun h => hdA₀ ((Subgroup.relIndex_eq_one.1 h) hdD)
    have h3 : A₀.relIndex D ∣ Nat.card D := Subgroup.relIndex_dvd_card _ _
    obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian hDel).exists_card_eq
    rw [hn] at h3
    obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow hp).1 h3
    rcases j with _ | _ | j
    · rw [pow_zero] at hjeq; exact absurd hjeq h2
    · simpa using hjeq
    · exfalso
      have : p < p ^ (j + 2) := by
        calc p = p ^ 1 := (pow_one p).symm
          _ < p ^ (j + 2) := Nat.pow_lt_pow_right hp.one_lt (by omega)
      rw [hjeq] at hle'
      exact absurd hle' (not_le.2 this)
  refine ⟨A₀ ⊓ D, Ssub, inf_le_right, hidx, ?_, hT2.to_le (hSle.trans inf_le_left),
    hcomB D (Subgroup.zpowers_le.2 hdD) hDB, hcomB B hdB le_rfl, hSne⟩
  exact hSle.trans (inf_le_right.trans (Subgroup.centralizer_le (fun x hx => hx.1)))

theorem I_33_3_proved : I_33_3 := by
  intro G _ _ hchar p hp hp2 N B I hN hBne hB hBN hI hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hO : IsPGroup 2 (pCoreOf 2 N) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  have hBO : B ≤ Subgroup.normalizer (pCoreOf 2 N : Set G) := hBN.trans (le_normalizer_pCoreOf 2 N)
  have hle : pCoreOf 2 N ≤ Subgroup.centralizer (I : Set G) := by
    refine (le_iSup_hyperplane hp hp2 hBne hB hO hBO).trans (iSup₂_le fun A hA => ?_)
    exact Subgroup.le_centralizer_iff.1
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcon A hA.1 hA.2))
  have hIO : I ≤ Subgroup.centralizer (pCoreOf 2 N : Set G) := Subgroup.le_centralizer_iff.1 hle
  have hIle : I ≤ pCoreOf 2 N := fun x hx => hchar N hN ⟨(hI hx).1, hIO hx⟩
  exact hnot (hO.to_le hIle)

end Proofs

end GL83
