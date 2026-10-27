module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GAmb
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bDesc
public import CFSG.LocalAnalysis.GLTheoremA.P55.I336.Main
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSetup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def T263HasB0 (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B B₀ : Subgroup Ω) : Prop :=
  B₀ ≤ B ∧ InnDiagOn p B₀ S ∧ Nat.card B ≤ p * Nat.card B₀ ∧
    (∀ a ∈ B, InnDiagOn p (Subgroup.zpowers a) S → a ∈ B₀) ∧
    B ⊓ Subgroup.centralizer (S : Set Ω) ≤ B₀

@[expose] def T263Dich (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B : Subgroup Ω) : Prop :=
  ∀ c ∈ B, NonInnDiag p c S → FieldOn p c S ∨ (p = 3 ∧ IsTD4 3 S)

@[expose] def T263Out : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
    IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S) → S ⊔ B = ⊤ → GLAIsBmax p B →
    (∃ T : Subgroup Ω, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ S ∧ B ≤ Subgroup.normalizer (T : Set Ω)) →
    ∃ B₀ : Subgroup Ω, T263HasB0 p S B B₀ ∧ T263Dich p S B

@[expose] def T263CaseIx (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω → ∀ (S B : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
    IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S) → catalogIs (↥S ⧸ Subgroup.center ↥S) Q →
    (p = 3 → ¬ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1)) →
    S ⊔ B = ⊤ → GLAPPrimeCore p Ω = ⊥ → GLAIsBmax p B → 4 ≤ GLATwoLocalRank p Ω →
    (∃ T : Subgroup Ω, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ S ∧ B ≤ Subgroup.normalizer (T : Set Ω)) →
    ∀ B₀ : Subgroup Ω, T263HasB0 p S B B₀ → T263Dich p S B →
    Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) = p ^ 2 → Nat.card ↥B₀ = p ^ 3 → Nat.card ↥B = p ^ 4 →
    ∀ b ∈ B, b ∉ B₀ → FieldOn p b S →
    GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) = ⊥ → T263GConcl p S B

@[expose] def T263CaseIxTD4 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω → ∀ (S B : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
    IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S) → p = 3 → IsTD4 3 S →
    (p = 3 → ¬ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1)) →
    S ⊔ B = ⊤ → GLAPPrimeCore p Ω = ⊥ → GLAIsBmax p B → 4 ≤ GLATwoLocalRank p Ω →
    (∃ T : Subgroup Ω, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ S ∧ B ≤ Subgroup.normalizer (T : Set Ω)) →
    ∀ B₀ : Subgroup Ω, T263HasB0 p S B B₀ → T263Dich p S B →
    Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) = p ^ 2 → Nat.card ↥B₀ = p ^ 3 → Nat.card ↥B = p ^ 4 →
    ∀ b ∈ B, b ∉ B₀ →
    GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) = ⊥ → T263GConcl p S B

@[expose] def T263BT (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
    IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S) → catalogIs (↥S ⧸ Subgroup.center ↥S) Q →
    CFSG.Open.IsElemAbelian p B →
    (∃ T : Subgroup Ω, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ S ∧ B ≤ Subgroup.normalizer (T : Set Ω)) →
    ∃ T' : Subgroup Ω, T' ≠ ⊥ ∧ IsPGroup 2 T' ∧ T' ≤ S ∧ B ≤ Subgroup.normalizer (T' : Set Ω) ∧
      B ⊓ Subgroup.centralizer (T' : Set Ω) ≤ Subgroup.centralizer (S : Set Ω)

@[expose] def T263Desc (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω → ∀ (S B : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
    IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S) → catalogIs (↥S ⧸ Subgroup.center ↥S) Q →
    (p = 3 → ¬ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1)) →
    S ⊔ B = ⊤ → GLAPPrimeCore p Ω = ⊥ → GLAIsBmax p B → 4 ≤ GLATwoLocalRank p Ω →
    (∃ T : Subgroup Ω, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ S ∧ B ≤ Subgroup.normalizer (T : Set Ω)) →
    Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < p ^ 3 →
    ∀ B₀ : Subgroup Ω, T263HasB0 p S B B₀ → T263Dich p S B →
    p * Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < Nat.card ↥B₀ →
    ∀ T' : Subgroup Ω, T' ≠ ⊥ → IsPGroup 2 T' → T' ≤ S → B ≤ Subgroup.normalizer (T' : Set Ω) →
    B ⊓ Subgroup.centralizer (T' : Set Ω) ≤ Subgroup.centralizer (S : Set Ω) →
    ∀ x : Ω, x ∈ B₀ → x ∉ Subgroup.centralizer (S : Set Ω) →
    (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≠ ⊥ →
    T263GConcl p S B ∨
      ∃ D I : Subgroup Ω, D ≤ B ∧ GLAPComponent p (S ⊓ Subgroup.centralizer (D : Set Ω)) I ∧
        B ≤ Subgroup.normalizer (I : Set Ω) ∧
        CFSG.Open.IsQuasisimple (PQuot p I) ∧ IsChevSimple 2 (PSimple p I) ∧
        Nat.card (PQuot p I) < Nat.card ↥S ∧
        (∃ T'' : Subgroup Ω, T'' ≤ I ∧ IsPGroup 2 T'' ∧ B ≤ Subgroup.normalizer (T'' : Set Ω) ∧
          ¬ T'' ≤ GLAPPrimeCoreOf p I) ∧
        (p = 3 → ¬ GLAMarking (PQuot 3 I) (fun lab _ _ _ _ _ => lab.n = 1))

section Generic

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω]

theorem t263_card_eq_pow (hp : p.Prime) {H : Subgroup Ω} (hH : CFSG.Open.IsElemAbelian p H) :
    ∃ k : ℕ, Nat.card ↥H = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact (isPGroup_of_isElemAbelian hH).exists_card_eq

theorem t263_caseI_numerics (hp : p.Prime) {B B₀ C : Subgroup Ω} {m : ℕ}
    (hBc : Nat.card ↥B = p ^ m) (hm : 4 ≤ m) (hC : ∃ c : ℕ, Nat.card ↥C = p ^ c)
    (hB₀ : ∃ a : ℕ, Nat.card ↥B₀ = p ^ a) (hC3 : Nat.card ↥C < p ^ 3)
    (hBB₀ : Nat.card ↥B ≤ p * Nat.card ↥B₀) (hB₀C : Nat.card ↥B₀ ≤ p * Nat.card ↥C) :
    Nat.card ↥C = p ^ 2 ∧ Nat.card ↥B₀ = p ^ 3 ∧ Nat.card ↥B = p ^ 4 := by
  obtain ⟨c, hc⟩ := hC
  obtain ⟨a, ha⟩ := hB₀
  have h1 : p ^ m ≤ p ^ (a + 1) := by rw [pow_succ, mul_comm]; rw [← hBc, ← ha]; exact hBB₀
  have h2 : p ^ a ≤ p ^ (c + 1) := by rw [pow_succ, mul_comm]; rw [← hc, ← ha]; exact hB₀C
  have h3 : p ^ c < p ^ 3 := by rw [← hc]; exact hC3
  have e1 : m ≤ a + 1 := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
  have e2 : a ≤ c + 1 := (Nat.pow_le_pow_iff_right hp.one_lt).1 h2
  have e3 : c < 3 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 h3
  have hc2 : c = 2 := by omega
  have ha3 : a = 3 := by omega
  have hm4 : m = 4 := by omega
  subst hc2 ha3 hm4
  exact ⟨hc, ha, hBc⟩

theorem t263_caseI_layer (hp : p.Prime) {S B : Subgroup Ω} (hBel : CFSG.Open.IsElemAbelian p B)
    (hCc : Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) = p ^ 2) {b : Ω} (hb : b ∈ B)
    (hbC : b ∉ B ⊓ Subgroup.centralizer (S : Set Ω))
    (hlay : GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) ≠ ⊥) : T263GConcl p S B := by
  classical
  left
  set C : Subgroup Ω := B ⊓ Subgroup.centralizer (S : Set Ω) with hCdef
  have hCB : C ≤ B := inf_le_left
  have hCel : CFSG.Open.IsElemAbelian p C := isElemAbelian_mono hBel hCB
  have hbp : b ^ p = 1 := hBel.2 b hb
  have hcomm : ∀ e ∈ C, e * b = b * e := fun e he => CFSG.Open.IsElemAbelian.comm hBel (hCB he) hb
  obtain ⟨hEel, hEcard⟩ := isElemAbelian_sup_zpowers_of_card hp hCel hCc hbp hbC hcomm
  refine ⟨C ⊔ Subgroup.zpowers b, sup_le hCB (Subgroup.zpowers_le.2 hb), hEel, hEcard, ?_⟩
  have hEq : S ⊓ Subgroup.centralizer ((C ⊔ Subgroup.zpowers b : Subgroup Ω) : Set Ω) =
      S ⊓ Subgroup.centralizer ({b} : Set Ω) := by
    ext s
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hsS, hsE⟩
      refine ⟨hsS, ?_⟩
      apply Subgroup.centralizer_le (s := ({b} : Set Ω)) (t := (↑(C ⊔ Subgroup.zpowers b) : Set Ω))
      · intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (le_sup_right : Subgroup.zpowers y ≤ C ⊔ Subgroup.zpowers y) (Subgroup.mem_zpowers y)
      · exact hsE
    · rintro ⟨hsS, hsb⟩
      refine ⟨hsS, ?_⟩
      have hle : C ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer ({s} : Set Ω) := by
        refine sup_le ?_ ?_
        · intro c hc
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 s hsS).symm
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.1 hsb).symm
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle he)
  rw [hEq]
  exact hlay

theorem t263_exists_x (hp : p.Prime) (hp2 : p ≠ 2) {S B B₀ T' : Subgroup Ω} (hB₀B : B₀ ≤ B)
    (hB₀el : CFSG.Open.IsElemAbelian p B₀) (hT'2 : IsPGroup 2 T')
    (hBT' : B ≤ Subgroup.normalizer (T' : Set Ω))
    (hker : B ⊓ Subgroup.centralizer (T' : Set Ω) ≤ Subgroup.centralizer (S : Set Ω))
    (hcard : p * Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < Nat.card ↥B₀) :
    ∃ x : Ω, x ∈ B₀ ∧ x ∉ Subgroup.centralizer (S : Set Ω) ∧
      (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≠ ⊥ := by
  classical
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup Ω, C = B ⊓ Subgroup.centralizer (S : Set Ω) := ⟨_, rfl⟩
  rw [← hCdef] at hcard
  have hCpos : 0 < Nat.card ↥C := Nat.card_pos
  have hB₀ne : B₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    have : 0 < p * Nat.card ↥C := Nat.mul_pos hp.pos hCpos
    omega
  have hTD : (⁅T', B₀⁆ : Subgroup Ω) ≠ ⊥ := by
    intro h
    have h1 : B₀ ≤ Subgroup.centralizer (T' : Set Ω) := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      exact h
    have h2 : B₀ ≤ C := by
      rw [hCdef]
      exact fun y hy => ⟨hB₀B hy, hker ⟨hB₀B hy, h1 hy⟩⟩
    have h3 := Subgroup.card_le_of_le h2
    have h4 : Nat.card ↥C ≤ p * Nat.card ↥C := Nat.le_mul_of_pos_left _ hp.pos
    omega
  obtain ⟨D₀, hD₀B₀, hD₀card, hD₀comm⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.P55.I336.exists_hyperplane_comm_ne_bot hp hp2 hT'2 hB₀el hB₀ne
      (hB₀B.trans hBT') hTD
  have hD₀C : ¬ D₀ ≤ C := by
    intro h
    have h1 := Subgroup.card_le_of_le h
    have h2 : p * Nat.card ↥D₀ = Nat.card ↥B₀ := by rw [mul_comm]; exact hD₀card
    have h3 : p * Nat.card ↥D₀ ≤ p * Nat.card ↥C := Nat.mul_le_mul_left p h1
    omega
  obtain ⟨x, hxD₀, hxC⟩ := Set.not_subset.1 hD₀C
  have hxB₀ : x ∈ B₀ := hD₀B₀ hxD₀
  refine ⟨x, hxB₀, fun hx => hxC (by rw [hCdef]; exact ⟨hB₀B hxB₀, hx⟩), ?_⟩
  intro h
  apply hD₀comm
  have hle : T' ⊓ Subgroup.centralizer (D₀ : Set Ω) ≤ T' ⊓ Subgroup.centralizer ({x} : Set Ω) :=
    inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxD₀))
  have h2 : (⁅T' ⊓ Subgroup.centralizer (D₀ : Set Ω), B₀⁆ : Subgroup Ω) ≤
      ⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl hle
  exact le_bot_iff.1 (h ▸ h2)

theorem t263Desc_mono {Q Q' : TauCeti.CFSGIndex → Prop} (hsub : ∀ i, Q i → Q' i) (h : T263Desc Q') :
    T263Desc Q :=
  fun p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hQ =>
    h p hp hp2 Ω hK S B hSn hSq hSp hSc (S10.catalogIs_imp hsub hQ)

theorem t263GenOn_of_cases {Q : TauCeti.CFSGIndex → Prop}
    (hLB : ∀ p : ℕ, p.Prime → ∀ (Y : Type) [Group Y] [Finite Y], LBalanceAt Y p)
    (hOut : T263Out) (hI : T263CaseIx Q) (hITD : T263CaseIxTD4) (hBT : T263BT Q) (hD : T263Desc Q) :
    T263GenOn t263KGroup Q := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hQ hIH hSB hΩ hB h4 hT hC
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hmk : p = 3 ∧ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1)
  · exact Or.inr hmk
  have hF2 : p = 3 → ¬ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1) := fun h3 hm => hmk ⟨h3, hm⟩
  obtain ⟨hBel, hBcard, -, -, -⟩ :
      CFSG.Open.IsElemAbelian p B ∧ Nat.card ↥B = p ^ GLATwoLocalRank p Ω ∧
        ∃ U : Subgroup Ω, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set Ω) := id hB
  obtain ⟨B₀, hB₀, hdich⟩ := hOut p hp hp2 Ω S B hSn hSq hSp hSc hSB hB hT
  have hB₀' := hB₀
  obtain ⟨hB₀B, -, hB₀idx, hB₀max, hCB₀⟩ := hB₀'
  by_cases hcase : Nat.card ↥B₀ ≤ p * Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω))
  ·
    have hB₀el : CFSG.Open.IsElemAbelian p B₀ := isElemAbelian_mono hBel hB₀B
    have hCel : CFSG.Open.IsElemAbelian p (B ⊓ Subgroup.centralizer (S : Set Ω)) :=
      isElemAbelian_mono hBel inf_le_left
    obtain ⟨hCc, hB₀c, hBc⟩ := t263_caseI_numerics hp hBcard h4 (t263_card_eq_pow hp hCel)
      (t263_card_eq_pow hp hB₀el) hC hB₀idx hcase
    obtain ⟨b, hb, hbB₀⟩ : ∃ b ∈ B, b ∉ B₀ := by
      by_contra hcon
      push Not at hcon
      have hle : B ≤ B₀ := hcon
      have h1 := Subgroup.card_le_of_le hle
      rw [hB₀c, hBc] at h1
      have h2 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      omega
    have hbN : b ∈ Subgroup.normalizer (S : Set Ω) := by
      rw [Subgroup.normalizer_eq_top_iff.2 hSn]
      exact Subgroup.mem_top b
    have hnon : NonInnDiag p b S := ⟨hbN, fun hin => hbB₀ (hB₀max b hb hin)⟩
    have hfield := hdich b hb hnon
    by_cases hlay : GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) = ⊥
    · rcases hfield with hF | ⟨hp3, hTD⟩
      · exact hI p hp hp2 Ω hK S B hSn hSq hSp hSc hQ hF2 hSB hΩ hB h4 hT B₀ hB₀ hdich hCc hB₀c hBc b hb hbB₀
          hF hlay
      · exact hITD p hp hp2 Ω hK S B hSn hSq hSp hSc hp3 hTD hF2 hSB hΩ hB h4 hT B₀ hB₀ hdich hCc hB₀c hBc b hb
          hbB₀ hlay
    · exact t263_caseI_layer hp hBel hCc hb (fun hbC => hbB₀ (hCB₀ hbC)) hlay
  ·
    have hcase' : p * Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < Nat.card ↥B₀ := not_le.1 hcase
    obtain ⟨T', hT'ne, hT'2, hT'S, hBT', hker⟩ := hBT p hp hp2 Ω S B hSn hSq hSp hSc hQ hBel hT
    obtain ⟨x, hxB₀, hxC, hxcomm⟩ := t263_exists_x hp hp2 hB₀B (isElemAbelian_mono hBel hB₀B) hT'2 hBT'
      hker hcase'
    rcases hD p hp hp2 Ω hK S B hSn hSq hSp hSc hQ hF2 hSB hΩ hB h4 hT hC B₀ hB₀ hdich hcase' T' hT'ne hT'2
        hT'S hBT' hker x hxB₀ hxC hxcomm with
      hdone | ⟨D, I, hDB, hIcomp, hBI, hIq, hIc, hIlt, hIT, hIGF⟩
    · exact hdone
    · rcases t263Amb_of_genLt hIH hp hp2 h4 hB hBI hIq hIc hIlt hIT
          (fun N' _ => t263_sections_of_kGroup (hK.subgroup (I ⊔ B)) N') with
        ⟨E, hEB, hEel, hEcard, hElay⟩ | ⟨hp3, hmk⟩
      · rw [closureIn_eq_self_of_le hBI] at hElay
        have hlayer := layer_ne_bot_of_desc hp hSn hBel hDB hIcomp hEB hElay
        have hcardE : p ^ 3 ≤ Nat.card ↥(E ⊔ D) := by
          have := Subgroup.card_le_of_le (le_sup_left : E ≤ E ⊔ D)
          rw [hEcard] at this
          exact this
        exact Or.inl (kConcl_of_ge hp (hLB p hp Ω) hK hSn hBel (sup_le hEB hDB) hcardE hlayer)
      · exact absurd hmk (hIGF hp3)

theorem t263FactGenK_of_cases
    (hLB : ∀ p : ℕ, p.Prime → ∀ (Y : Type) [Group Y] [Finite Y], LBalanceAt Y p)
    (hOut : T263Out) (hI : T263Families T263CaseIx) (hITD : T263CaseIxTD4) (hBT : T263Families T263BT)
    (hD : T263Families T263Desc) : T263FactGenK :=
  t263FactGenK_of_families
    (T263Families.of_apply fun f => t263GenOn_of_cases hLB hOut (hI.apply f) hITD (hBT.apply f) (hD.apply f))

end Generic

end CFSG.LocalAnalysis.GLTheoremA.T263

end
