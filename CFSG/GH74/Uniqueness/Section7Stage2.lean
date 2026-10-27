module

public import CFSG.GH74.Uniqueness.Section7Stage2Defs
public import CFSG.GH74.Uniqueness.Section6Lemma61
public import CFSG.GH74.Uniqueness.Section6Lemma62

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Generic

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem stage2_exists_isSylowOf_ge {p : ℕ} [Fact p.Prime] {P K : Subgroup X} (hPK : P ≤ K)
    (hP : IsPGroup p P) : ∃ R : Subgroup X, ABGLocalTools.IsSylowOf p R K ∧ P ≤ R := by
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hPK hx⟩, hQ (show (⟨x, hPK hx⟩ : K) ∈ P.subgroupOf K from hx), rfl⟩

theorem stage2_factorization_lt_card_inf_normalizer {p : ℕ} (hp : p.Prime) {P D : Subgroup X}
    (hPp : IsPGroup p P) (hPD : P ≤ D) (hnot : ¬ ABGLocalTools.IsSylowOf p P D) :
    (Nat.card P).factorization p <
      (Nat.card ↥(D ⊓ normalizer (P : Set X))).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS, hPS⟩ := stage2_exists_isSylowOf_ge hPD hPp
  have hlt : P < S := lt_of_le_of_ne hPS (fun heq => hnot (heq ▸ hS))
  obtain ⟨R₁, hR₁p, hPR₁, hR₁S, hR₁N⟩ :=
    CFSG.BenderSuzuki.exists_larger_normalizer_pSubgroup hp hS.isPGroup hlt
  have hR₁ND : R₁ ≤ D ⊓ normalizer (P : Set X) := le_inf (hR₁S.trans hS.le) hR₁N
  obtain ⟨a, ha⟩ := hPp.exists_card_eq
  obtain ⟨b, hb⟩ := hR₁p.exists_card_eq
  have hab : a < b := by
    have hcard : Nat.card P < Nat.card R₁ := Subgroup.card_lt_of_lt hPR₁
    rw [ha, hb] at hcard
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hcard
  have hdvd : p ^ b ∣ Nat.card ↥(D ⊓ normalizer (P : Set X)) := by
    rw [← hb]
    exact Subgroup.card_dvd_of_le hR₁ND
  have hbf : b ≤ (Nat.card ↥(D ⊓ normalizer (P : Set X))).factorization p :=
    (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
  rw [ha, hp.factorization_pow, Finsupp.single_eq_same]
  exact lt_of_lt_of_le hab hbf

end Generic

section Stage2

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem exists_maximal_stage2Adm {z : X} {p : ℕ} {β : Subgroup X}
    (hne : ∃ Q : Subgroup X, Stage2Adm Z M z p β Q) :
    ∃ Q : Subgroup X, Stage2Adm Z M z p β Q ∧
      ∀ Q' : Subgroup X, Stage2Adm Z M z p β Q' → stage2NDExp p M β Q' ≤ stage2NDExp p M β Q := by
  obtain ⟨P, hP⟩ := hne
  obtain ⟨Q, hQ, hmax⟩ := Set.exists_max_image {Q : Subgroup X | Stage2Adm Z M z p β Q}
    (stage2NDExp p M β) (Set.toFinite _) ⟨P, hP⟩
  exact ⟨Q, hQ, fun Q' hQ' => hmax Q' hQ'⟩

theorem IsProductDisconnected.exists_stage2R (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z) {β Q P₁ : Subgroup X} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hβM : β ≠ M) (htβ : conjugate M t = β)
    (htQ : t ∈ normalizer (Q : Set X)) (hP₁Q : P₁ ≤ normalizer (Q : Set X))
    (hP₁D : P₁ ≤ M ⊓ β) (hP₁p : IsPGroup p P₁) (htP₁ : t ∈ normalizer (P₁ : Set X)) :
    ∃ R : Subgroup X, ABGLocalTools.IsSylowOf p R (M ⊓ β ⊓ normalizer (Q : Set X)) ∧ P₁ ≤ R ∧
      t ∈ normalizer (R : Set X) := by
  have htM : t ∉ M := fun htM =>
    hβM (htβ.symm.trans ((h.conjugate_eq_iff_mem (self_mem_omega M)).mpr htM))
  have htD : t ∈ normalizer ((M ⊓ conjugate M t : Subgroup X) : Set X) :=
    mem_normalizer_inf_conjugate (hZ.mul_self_eq_one ht)
  rw [htβ] at htD
  have htN : t ∈ normalizer ((normalizer (Q : Set X) : Subgroup X) : Set X) :=
    Subgroup.le_normalizer htQ
  have htW : t ∈ normalizer ((M ⊓ β ⊓ normalizer (Q : Set X) : Subgroup X) : Set X) :=
    mem_normalizer_inf htD htN
  have hWD : M ⊓ β ⊓ normalizer (Q : Set X) ≤ M ⊓ conjugate M t := by
    rw [htβ]
    exact inf_le_left
  exact h.prop37a hZ ht htM hp hp2 hWD htW (le_inf hP₁D hP₁Q) hP₁p htP₁

theorem ZDSetup.stage2Exists (S : ZDSetup X Z M) (h72 : Prop72Stmt Z M) (h78 : Prop78Stmt Z M)
    (h79 : Prop79Stmt Z M) (h73 : Lemma73Stmt Z M) (h7D : SevenDStmt Z M) :
    Stage2ExistsStmt Z M := by
  intro z p W hW
  have hZ := S.invariant
  have h := S.prodDisc
  have hcand := hW.cand
  have hp := hcand.prime
  have hp2 := hcand.ne_two
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨β, hβ, hβM, hθ⟩ := h72 z p W hW
  have hdt : DoublyTransitive M := h78 z p W hW
  have hcard_lt := h79 z p W hW
  have hsevenD := h7D z p W hcand β hβ hβM
  have hzbot : z ∈ normalizer ((⊥ : Subgroup X) : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top z
  obtain ⟨hinv, hswap⟩ := h73 z p W hW β hβ hβM
  obtain ⟨P, hP, -, hzP⟩ := hinv ⊥ IsPGroup.of_bot bot_le hzbot
  obtain ⟨t₀, ht₀, ht₀P, ht₀β⟩ := hswap P hP hzP
  have hPne : P ≠ ⊥ := by
    intro hbot
    have hd := hsevenD P hP
    rw [hbot, Subgroup.commutator_bot_right, Subgroup.card_bot] at hd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hd)
  have hPadm : Stage2Adm Z M z p β P :=
    { ne_bot := hPne
      pgroup := hP.isPGroup
      le_E := hP.le
      z_norm := hzP
      exists_t := ⟨t₀, ht₀, ht₀P, ht₀β, P, hP, Subgroup.le_normalizer, ht₀P⟩ }
  obtain ⟨Q, hQ, hQmax⟩ := exists_maximal_stage2Adm ⟨P, hPadm⟩
  obtain ⟨t, ht, htQ, htβ, P₁, hP₁, hP₁Q, htP₁⟩ := hQ.exists_t
  have hP₁D : P₁ ≤ M ⊓ β := hP₁.le.trans inf_le_left
  obtain ⟨R, hR, hP₁R, htR⟩ :=
    h.exists_stage2R hZ ht hp hp2 hβM htβ htQ hP₁Q hP₁D hP₁.isPGroup htP₁
  have hPnotD : ¬ ABGLocalTools.IsSylowOf p P (M ⊓ β) := by
    intro hPD
    have heq := (S.lemma62 z p W hW β hβ hβM).mp ⟨P, hPD, hzP⟩
    rw [heq] at hcard_lt
    exact lt_irrefl _ hcard_lt
  have hgrowth := stage2_factorization_lt_card_inf_normalizer hp hP.isPGroup
    (hP.le.trans inf_le_left : P ≤ M ⊓ β) hPnotD
  obtain ⟨n, hn⟩ := hP.isPGroup.exists_card_eq
  rw [hn, hp.factorization_pow, Finsupp.single_eq_same] at hgrowth
  have hPQ : stage2NDExp p M β P ≤ stage2NDExp p M β Q := hQmax P hPadm
  have hP₁card : Nat.card P₁ = p ^ n := by
    have h1 : Nat.card P₁ = p ^ (Nat.card ↥(M ⊓ β ⊓ conjugate β z)).factorization p :=
      hP₁.card_eq
    have h2 : Nat.card P = p ^ (Nat.card ↥(M ⊓ β ⊓ conjugate β z)).factorization p :=
      hP.card_eq
    rw [h1, ← h2, hn]
  have hRcard : Nat.card R = p ^ stage2NDExp p M β Q := hR.card_eq
  refine ⟨β, Q, t, R, P₁, ?_⟩
  exact
    { tmax := hW
      beta_mem := hβ
      beta_ne := hβM
      theta := hθ
      dt := hdt
      transS := S.lemma61a hdt
      card_lt := hcard_lt
      sevenD := hsevenD
      adm := hQ
      maxQ := hQmax
      t_mem := ht
      t_norm_Q := htQ
      t_swap := htβ
      P₁_syl := hP₁
      P₁_le_N := hP₁Q
      t_norm_P₁ := htP₁
      R_syl := hR
      P₁_le_R := hP₁R
      t_norm_R := htR
      card_P₁_lt := by
        rw [hP₁card, hRcard]
        exact lt_of_lt_of_le (Nat.pow_lt_pow_right hp.one_lt hgrowth)
          (Nat.pow_le_pow_right hp.pos hPQ) }

end Stage2

end CFSG.GH74.Uniqueness
