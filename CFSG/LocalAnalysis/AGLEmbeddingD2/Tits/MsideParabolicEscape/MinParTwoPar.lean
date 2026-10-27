module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParC4Wit

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Open
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

structure TwoPar (S : Type) [Group S] (T P₁ P₂ : Subgroup S) : Prop where
  sylow : IsSylowTwoOf T ⊤
  lt₁ : Subgroup.normalizer (T : Set S) < P₁
  lt₂ : Subgroup.normalizer (T : Set S) < P₂
  atom₁ : ∀ Q : Subgroup S, Subgroup.normalizer (T : Set S) ≤ Q → Q ≤ P₁ →
    Q = Subgroup.normalizer (T : Set S) ∨ Q = P₁
  atom₂ : ∀ Q : Subgroup S, Subgroup.normalizer (T : Set S) ≤ Q → Q ≤ P₂ →
    Q = Subgroup.normalizer (T : Set S) ∨ Q = P₂
  ne : P₁ ≠ P₂
  top₁ : P₁ ≠ ⊤
  top₂ : P₂ ≠ ⊤
  hover : ∀ Y : Subgroup S, Subgroup.normalizer (T : Set S) ≤ Y →
    Y = Subgroup.normalizer (T : Set S) ∨ Y = P₁ ∨ Y = P₂ ∨ Y = ⊤
  cover : ∀ X : Subgroup S, T ≤ X → X ≠ ⊤ → X ≤ P₁ ∨ X ≤ P₂
  ov₁ : ∀ X : Subgroup S, T ≤ X → X ≤ P₁ → ¬ X ≤ Subgroup.normalizer (T : Set S) →
    pElementSubgroup 2 P₁ ≤ X
  ov₂ : ∀ X : Subgroup S, T ≤ X → X ≤ P₂ → ¬ X ≤ Subgroup.normalizer (T : Set S) →
    pElementSubgroup 2 P₂ ≤ X
  gen₁ : P₁ ≤ Subgroup.normalizer (T : Set S) ⊔ pElementSubgroup 2 P₁
  gen₂ : P₂ ≤ Subgroup.normalizer (T : Set S) ⊔ pElementSubgroup 2 P₂
  ct₁ : CharTwo P₁
  ct₂ : CharTwo P₂

section

variable {S : Type} [Group S] {T P₁ P₂ : Subgroup S}

@[expose] def TwoPar.node (_h : TwoPar S T P₁ P₂) : Bool → Subgroup S
  | true => P₁
  | false => P₂

theorem TwoPar.le_node (h : TwoPar S T P₁ P₂) (b : Bool) :
    Subgroup.normalizer (T : Set S) < h.node b := by
  cases b
  · exact h.lt₂
  · exact h.lt₁

theorem TwoPar.atom (h : TwoPar S T P₁ P₂) (b : Bool) :
    ∀ Q : Subgroup S, Subgroup.normalizer (T : Set S) ≤ Q → Q ≤ h.node b →
      Q = Subgroup.normalizer (T : Set S) ∨ Q = h.node b := by
  cases b
  · exact h.atom₂
  · exact h.atom₁

theorem TwoPar.gen (h : TwoPar S T P₁ P₂) (b : Bool) :
    h.node b ≤ Subgroup.normalizer (T : Set S) ⊔ pElementSubgroup 2 (h.node b) := by
  cases b
  · exact h.gen₂
  · exact h.gen₁

theorem TwoPar.ov (h : TwoPar S T P₁ P₂) (b : Bool) :
    ∀ X : Subgroup S, T ≤ X → X ≤ h.node b → ¬ X ≤ Subgroup.normalizer (T : Set S) →
      pElementSubgroup 2 (h.node b) ≤ X := by
  cases b
  · exact h.ov₂
  · exact h.ov₁

theorem TwoPar.ct (h : TwoPar S T P₁ P₂) (b : Bool) : CharTwo (h.node b) := by
  cases b
  · exact h.ct₂
  · exact h.ct₁

theorem TwoPar.node_ne (h : TwoPar S T P₁ P₂) {b b' : Bool} (hb : b ≠ b') :
    h.node b ≠ h.node b' := by
  cases b <;> cases b' <;> simp at hb
  · exact h.ne.symm
  · exact h.ne

theorem TwoPar.nonnorm (h : TwoPar S T P₁ P₂) (b : Bool) :
    ¬ pElementSubgroup 2 (h.node b) ≤ Subgroup.normalizer (T : Set S) := fun hle =>
  (h.le_node b).ne' (le_antisymm ((h.gen b).trans (sup_le le_rfl hle)) (h.le_node b).le)

theorem TwoPar.eq_of_pElement_le (h : TwoPar S T P₁ P₂) {j k : Bool}
    (hle : pElementSubgroup 2 (h.node k) ≤ h.node j) : k = j := by
  by_contra hkj
  have h1 : h.node k ≤ h.node j :=
    (h.gen k).trans (sup_le (h.le_node j).le hle)
  rcases h.atom j (h.node k) (h.le_node k).le h1 with e | e
  · exact (h.le_node k).ne' e
  · exact h.node_ne hkj e

theorem TwoPar.pElement_top (h : TwoPar S T P₁ P₂) :
    pElementSubgroup 2 P₁ ⊔ pElementSubgroup 2 P₂ = ⊤ := by
  by_contra hne
  have hTW : T ≤ pElementSubgroup 2 P₁ ⊔ pElementSubgroup 2 P₂ :=
    le_sup_of_le_left (le_pElementSubgroup_of_isPGroup
      (Subgroup.le_normalizer.trans h.lt₁.le) h.sylow.2.1)
  rcases h.cover _ hTW hne with hW | hW
  · have : pElementSubgroup 2 (h.node false) ≤ h.node true := le_sup_right.trans hW
    exact absurd (h.eq_of_pElement_le this) (by decide)
  · have : pElementSubgroup 2 (h.node true) ≤ h.node false := le_sup_left.trans hW
    exact absurd (h.eq_of_pElement_le this) (by decide)

@[expose] noncomputable def minParData_of_twoPar (h : TwoPar S T P₁ P₂) :
    MinParData (⊤ : Subgroup S) T where
  ι := Bool
  P := h.node
  P_min := fun b => by
    refine ⟨le_top, ?_, fun Q hQ1 hQ2 => ?_⟩
    · rw [top_inf_eq]; exact h.le_node b
    · rw [top_inf_eq] at hQ1 ⊢
      exact h.atom b Q hQ1 hQ2
  P_all := fun A hA => by
    obtain ⟨-, h1, h2⟩ := hA
    rw [top_inf_eq] at h1 h2
    rcases h.hover A h1.le with e | e | e | e
    · exact absurd e h1.ne'
    · exact ⟨true, e⟩
    · exact ⟨false, e⟩
    · exfalso
      rcases h2 P₁ h.lt₁.le (e ▸ le_top) with e1 | e1
      · exact h.lt₁.ne' e1
      · exact h.top₁ (e1.trans e)
  P_inj := fun b b' hbb => by
    by_contra hne
    exact h.node_ne hne hbb
  OV := fun X hTX _ hX => by
    by_cases hXt : X = ⊤
    · exact ⟨true, (pElementSubgroup_le _).trans (hXt ▸ le_top)⟩
    · rcases h.cover X hTX hXt with e | e
      · exact ⟨true, h.ov true X hTX e hX⟩
      · exact ⟨false, h.ov false X hTX e hX⟩
  sub := fun J k hJ hle => by
    by_contra hk
    obtain ⟨j, hj⟩ := hJ
    have hjk : j ≠ k := fun e => hk (e ▸ hj)
    have hJle : (⨆ j' ∈ J, h.node j') ≤ h.node j := by
      refine iSup₂_le fun j' hj' => ?_
      have : j' = j := by
        by_contra hne
        apply hk
        cases j' <;> cases j <;> cases k <;> simp_all
      exact this ▸ le_rfl
    exact hjk (h.eq_of_pElement_le (hle.trans hJle)).symm
  two := fun J a hJ ha h2 => by
    obtain ⟨j, hj⟩ := hJ
    obtain ⟨m, hm⟩ := h2
    have hmem : ∀ b, a ∈ h.node b → a ∈ pElementSubgroup 2 (h.node b) := fun b hb =>
      Subgroup.subset_closure ⟨hb, m, hm⟩
    by_cases hall : ∀ b, b ∈ J
    · have htop := h.pElement_top
      have : pElementSubgroup 2 P₁ ⊔ pElementSubgroup 2 P₂ ≤
          ⨆ j ∈ J, pElementSubgroup 2 (h.node j) :=
        sup_le (le_iSup₂_of_le (f := fun j (_ : j ∈ J) => pElementSubgroup 2 (h.node j)) true
          (hall true) le_rfl) (le_iSup₂_of_le
            (f := fun j (_ : j ∈ J) => pElementSubgroup 2 (h.node j)) false (hall false) le_rfl)
      rw [htop] at this
      exact this (Subgroup.mem_top a)
    · push Not at hall
      obtain ⟨b0, hb0⟩ := hall
      have hJb : ∀ j' ∈ J, j' = j := by
        intro j' hj'
        by_contra hne
        apply hb0
        cases j' <;> cases j <;> cases b0 <;> simp_all
      have hle : (⨆ j' ∈ J, h.node j') ≤ h.node j :=
        iSup₂_le fun j' hj' => (hJb j' hj') ▸ le_rfl
      exact le_iSup₂_of_le (f := fun j (_ : j ∈ J) => pElementSubgroup 2 (h.node j)) j hj le_rfl
        (hmem j (hle ha))
  nonnorm := h.nonnorm

end

section Witness

variable {S : Type} [Group S] [Finite S]

theorem oddWitness_of_charTwo {T P : Subgroup S} (hT : IsSylowTwoOf T ⊤) (hTP : T ≤ P)
    (hct : CharTwo P) (hnt : ¬ pElementSubgroup 2 P ≤ T) : OddWitness P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pElementSubgroup 2 P with hO
  have hTO : T ≤ O := le_pElementSubgroup_of_isPGroup hTP hT.2.1
  have hOP : O ≤ P := pElementSubgroup_le P
  have hnot : ¬ IsPGroup 2 O := by
    intro hO2
    apply hnt
    have hcardT : Nat.card T ∣ Nat.card O := Subgroup.card_dvd_of_le hTO
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 hT.2.1)
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card.1 hO2)
    have hSidx : Nat.card T * (T.subgroupOf ⊤).index = Nat.card S := by
      have := Subgroup.card_mul_index (T.subgroupOf ⊤)
      rwa [show Nat.card (T.subgroupOf ⊤ : Subgroup (⊤ : Subgroup S)) = Nat.card T from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv, Subgroup.card_top] at this
    have hOdvd : Nat.card O ∣ Nat.card S := Subgroup.card_subgroup_dvd_card O
    rw [← hSidx, hm, hk] at hOdvd
    have hcop : Nat.Coprime (2 ^ m) ((T.subgroupOf ⊤).index) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hT.2.2)
    have hdvd : 2 ^ m ∣ 2 ^ k := by
      have := hcop.dvd_of_dvd_mul_right hOdvd
      exact this
    have hmk : m ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
    have hle : Nat.card O ≤ Nat.card T := by
      rw [hm, hk]; exact Nat.pow_le_pow_right (by norm_num) hmk
    have heq : T = O := Subgroup.eq_of_le_of_card_ge hTO hle
    exact heq ▸ le_rfl
  obtain ⟨p, hp, hpO, hp2⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card O ∧ p ≠ 2 := by
    by_contra hcon
    push Not at hcon
    apply hnot
    rw [IsPGroup.iff_card]
    have hpos : 0 < Nat.card O := Nat.card_pos
    exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hpos.ne' fun {q} hq hqd =>
      hcon q hq hqd⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := O) p hpO
  set N := pCoreOf 2 P with hN
  have hNP : N ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hN2 : IsPGroup 2 ↥N := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  have hPN : P ≤ Subgroup.normalizer (N : Set S) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hyo : orderOf (y : S) = p := by rw [Subgroup.orderOf_coe]; exact hy
  have hyO : (y : S) ∈ O := y.2
  obtain ⟨c, hcN, hcne⟩ : ∃ c ∈ N, (y : S) * c * (y : S)⁻¹ ≠ c := by
    by_contra h'
    push Not at h'
    have hyC : (y : S) ∈ Subgroup.centralizer (N : Set S) := Subgroup.mem_centralizer_iff.2
      fun c hc => (mul_inv_eq_iff_eq_mul.1 (h' c hc)).symm
    have hyN : (y : S) ∈ N := hct ⟨hOP hyO, hyC⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hN2) ⟨(y : S), hyN⟩
    have hk' : orderOf (y : S) = 2 ^ k := by
      rw [← hk, ← Subgroup.orderOf_coe]
    rw [hyo] at hk'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow (dvd_of_eq hk')))
  exact ⟨N, hNP, hN2, hPN, p, y, c, hp, hp2, hyO, ⟨1, by rw [hyo, pow_one]⟩, hcN, hcne⟩

end Witness

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
