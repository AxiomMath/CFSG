module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_20Cases
import CFSG.Walter.TwoRank
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
  Subgroup

section Main

variable {K : Type} [Group K]

theorem i1020_rank_one {X : Type} [Group X] [Finite X] {q : ℕ} (hq : q.Prime) (loc : Prop)
    {S₀ : Subgroup K} (hS₀ : IsPGroup 2 S₀) (hS₀loc : loc → S₀ ≠ ⊥)
    (hqS₀ : q ∣ Nat.card (normalizer (S₀ : Set K))) (ψ : X →* K) (hψ : Function.Surjective ψ) :
    ∃ S : Subgroup X, IsPGroup 2 S ∧ (loc → S ≠ ⊥) ∧ ∃ E : Subgroup X,
      E ≤ normalizer (S : Set X) ∧ IsElemAbelian q E ∧ Nat.card E = q ^ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨S, hS, hSmap, hN⟩ := i1020_frattini_lift ψ hψ hS₀
  have hdvd : q ∣ Nat.card (normalizer (S : Set X)) :=
    hqS₀.trans ((card_dvd_of_le hN).trans (card_map_dvd _ _))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := normalizer (S : Set X)) q hdvd
  have hxo : orderOf (x : X) = q := by rw [orderOf_coe, hx]
  refine ⟨S, hS, fun hl hbot => hS₀loc hl (by rw [← hSmap, hbot, Subgroup.map_bot]),
    zpowers (x : X), zpowers_le.2 x.2, i1020_isElemAbelian_zpowers (hxo ▸ pow_orderOf_eq_one _),
    by rw [Nat.card_zpowers, hxo, pow_one]⟩

theorem i1020_quotient_witness {X : Type} [Group X] [Finite X] {q r : ℕ} (hq : q.Prime)
    (N : Subgroup X) [N.Normal] (hN : ¬ q ∣ Nat.card N) (loc : Prop)
    (h : ∃ S : Subgroup (X ⧸ N), IsPGroup 2 S ∧ (loc → S ≠ ⊥) ∧ ∃ E : Subgroup (X ⧸ N),
      E ≤ normalizer (S : Set (X ⧸ N)) ∧ IsElemAbelian q E ∧ Nat.card E = q ^ r) :
    ∃ S : Subgroup X, IsPGroup 2 S ∧ (loc → S ≠ ⊥) ∧ ∃ E : Subgroup X,
      E ≤ normalizer (S : Set X) ∧ IsElemAbelian q E ∧ Nat.card E = q ^ r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨S', hS', hS'loc, E', hE'S', hE', hE'c⟩ := h
  obtain ⟨S, hS, hSmap, hNS⟩ :=
    i1020_frattini_lift (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hS'
  have hA : ¬ q ∣ Nat.card (normalizer (S : Set X) ⊓ (QuotientGroup.mk' N).ker : Subgroup X) := by
    rw [QuotientGroup.ker_mk']
    exact fun h => hN (h.trans (card_dvd_of_le inf_le_right))
  obtain ⟨E, hEA, hE, hEc⟩ :=
    i1020_coprime_lift (QuotientGroup.mk' N) (normalizer (S : Set X)) hA (hE'S'.trans hNS) hE' hE'c
  exact ⟨S, hS, fun hl hbot => hS'loc hl (by rw [← hSmap, hbot, Subgroup.map_bot]), E, hEA, hE,
    hEc⟩

theorem i1020_exists_prime_ne {X : Type} [Group X] [Finite X] {q : ℕ} {Y : Subgroup X}
    (hY : ¬ IsPGroup q Y) : ∃ p : ℕ, p.Prime ∧ p ≠ q ∧ p ∣ Nat.card Y := by
  by_contra hno
  push Not at hno
  apply hY
  refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
  intro d hd hdd
  by_contra hne
  exact hno d hd hne hdd

theorem i1020_main [IsSimpleGroup K] (hnc : ∃ a b : K, a * b ≠ b * a) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {k : ℕ} (hk : 2 ≤ k) {V : Subgroup K} (hV : IsElemAbelian 2 V)
    (hVc : Nat.card V = 2 ^ k) (loc : Prop) {S₀ : Subgroup K} (hS₀ : IsPGroup 2 S₀)
    (hS₀loc : loc → S₀ ≠ ⊥) (hqS₀ : q ∣ Nat.card (normalizer (S₀ : Set K))) (n : ℕ) :
    ∀ (X : Type) [Group X] [Finite X], Nat.card X ≤ n → ∀ (r : ℕ) (φ : X →* (Fin r → K)),
      Function.Surjective φ → (loc → 1 ≤ r) →
      ∃ S : Subgroup X, IsPGroup 2 S ∧ (loc → S ≠ ⊥) ∧ ∃ E : Subgroup X,
        E ≤ normalizer (S : Set X) ∧ IsElemAbelian q E ∧ Nat.card E = q ^ r := by
  have hqK : q ∣ Nat.card K := hqS₀.trans (card_subgroup_dvd_card _)
  induction n with
  | zero =>
    intro X _ _ hX
    have := Nat.card_pos (α := X)
    omega
  | succ n ih =>
    intro X _ _ hX r φ hφ hr
    rcases Nat.lt_or_ge r 2 with hr2 | hr2
    ·
      interval_cases r
      · exact ⟨⊥, IsPGroup.of_bot, fun hl => absurd (hr hl) (by norm_num), ⊥, bot_le,
          CFSG.SectionRank.isElemAbelian_bot q, by simp⟩
      · refine i1020_rank_one hq loc hS₀ hS₀loc hqS₀
          ((Pi.evalMonoidHom (fun _ : Fin 1 => K) 0).comp φ) fun a => ?_
        obtain ⟨x, hx⟩ := hφ fun _ => a
        exact ⟨x, by simp [hx]⟩
    by_cases hYq : IsPGroup q φ.ker
    · by_cases hC : centralizer (φ.ker : Set X) ≤ φ.ker
      ·
        have hYne : φ.ker ≠ ⊥ := by
          intro hbot
          obtain ⟨a, ha⟩ := exists_ne (1 : K)
          obtain ⟨x, hx⟩ := hφ (Pi.mulSingle ⟨0, by omega⟩ a)
          have hx1 : x ∈ φ.ker := hC (by
            rw [hbot, mem_centralizer_iff]
            intro h hh
            rw [SetLike.mem_coe, mem_bot] at hh
            rw [hh, one_mul, mul_one])
          rw [MonoidHom.mem_ker, hx] at hx1
          exact ha (by simpa using congrFun hx1 ⟨0, by omega⟩)
        obtain ⟨S, hS, hSne, E, hES, hE, hEc⟩ :=
          i1020_caseA hq hq2 hk hV hVc (by omega) φ hφ hYq hYne hC
        exact ⟨S, hS, fun _ => hSne, E, hES, hE, hEc⟩
      ·
        obtain ⟨i, x, hxo, hxi, hxc⟩ := i1020_caseB hnc hq hq2 hqK φ hφ hC
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        set H : Subgroup X := ((Pi.evalMonoidHom (fun _ : Fin (r' + 1) => K) i).comp φ).ker
          with hHdef
        have hmemH : ∀ h : X, h ∈ H ↔ φ h i = 1 := fun h => by simp [hHdef]
        set φ' : H →* (Fin r' → K) :=
          (MonoidHom.pi fun j => Pi.evalMonoidHom (fun _ : Fin (r' + 1) => K) (i.succAbove j)).comp
            (φ.comp H.subtype) with hφ'def
        have hφ' : Function.Surjective φ' := by
          intro g
          obtain ⟨y, hy⟩ := hφ (i.insertNth 1 g)
          have hyH : y ∈ H := by rw [hmemH, hy, Fin.insertNth_apply_same]
          refine ⟨⟨y, hyH⟩, ?_⟩
          funext j
          simp [hφ'def, hy, Fin.insertNth_apply_succAbove]
        have hxH : x ∉ H := fun h => hxi ((hmemH x).1 h)
        have hHlt : Nat.card H < Nat.card X := by
          rw [← card_top (G := X)]
          refine card_lt_of_lt (lt_top_iff_ne_top.2 fun h => hxH ?_)
          rw [h]; exact mem_top x
        obtain ⟨S₁, hS₁, hS₁loc, E₁, hE₁S₁, hE₁, hE₁c⟩ :=
          ih H (by omega) r' φ' hφ' (fun _ => by omega)
        obtain ⟨hS, hSloc, hES, hE₀, hE₀c⟩ :=
          i1020_map_witness H.subtype H.subtype_injective hS₁ hE₁S₁ hE₁ hE₁c
        have hE₀H : E₁.map H.subtype ≤ H := map_subtype_le _
        have hSH : S₁.map H.subtype ≤ H := map_subtype_le _
        obtain ⟨hE, hEc⟩ := i1020_adjoin hq hE₀ hE₀c hxo (fun h => hxH (hE₀H h))
          (fun e he => (hxc e ((hmemH e).1 (hE₀H he))).symm)
        refine ⟨S₁.map H.subtype, hS, fun hl => hSloc (hS₁loc hl), _, sup_le hES ?_, hE, hEc⟩
        refine zpowers_le.2 (centralizer_le_normalizer _ ?_)
        rw [mem_centralizer_iff]
        intro s hs
        exact (hxc s ((hmemH s).1 (hSH hs))).symm
    ·
      obtain ⟨p, hp, hpq, hpY⟩ := i1020_exists_prime_ne hYq
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p φ.ker))
      set P' : Subgroup X := (P : Subgroup φ.ker).map φ.ker.subtype
      have hfr : normalizer (P' : Set X) ⊔ φ.ker = ⊤ := Sylow.normalizer_sup_eq_top P
      have hP'Y : P' ≤ φ.ker := map_subtype_le _
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (P.isPGroup'.map φ.ker.subtype)
      have hP'q : ¬ q ∣ Nat.card P' := by
        rw [hm]
        intro h
        exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)).symm
      by_cases htop : normalizer (P' : Set X) = ⊤
      ·
        have hP'n : P'.Normal := normalizer_eq_top_iff.1 htop
        have hP'ne : P' ≠ ⊥ :=
          (map_eq_bot_iff_of_injective _ φ.ker.subtype_injective).not.2 (P.ne_bot_of_dvd_card hpY)
        have hlt : Nat.card (X ⧸ P') < Nat.card X := by
          rw [card_eq_card_quotient_mul_card_subgroup P']
          have h1 : 1 < Nat.card P' := (one_lt_card_iff_ne_bot P').2 hP'ne
          have h2 : 0 < Nat.card (X ⧸ P') := Nat.card_pos
          nlinarith
        refine i1020_quotient_witness hq P' hP'q loc
          (ih (X ⧸ P') (by omega) r (QuotientGroup.lift P' φ hP'Y) ?_ hr)
        intro f
        obtain ⟨x, rfl⟩ := hφ f
        exact ⟨x, rfl⟩
      ·
        set X₀ : Subgroup X := normalizer (P' : Set X)
        have hφ₀ : Function.Surjective (φ.comp X₀.subtype) := by
          intro f
          obtain ⟨x, rfl⟩ := hφ f
          have hx : x ∈ X₀ ⊔ φ.ker := hfr ▸ mem_top x
          obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_right.1 hx
          refine ⟨⟨a, ha⟩, ?_⟩
          simp [MonoidHom.mem_ker.1 hb]
        have hlt : Nat.card X₀ < Nat.card X := by
          rw [← card_top (G := X)]
          exact card_lt_of_lt (lt_top_iff_ne_top.2 htop)
        obtain ⟨S₁, hS₁, hS₁loc, E₁, hE₁S₁, hE₁, hE₁c⟩ :=
          ih X₀ (by omega) r (φ.comp X₀.subtype) hφ₀ hr
        obtain ⟨hS, hSloc, hES, hE, hEc⟩ :=
          i1020_map_witness X₀.subtype X₀.subtype_injective hS₁ hE₁S₁ hE₁ hE₁c
        exact ⟨_, hS, fun hl => hSloc (hS₁loc hl), _, hES, hE, hEc⟩

end Main

section Final

variable {K : Type} [Group K] [Finite K]

theorem i1020_exists_elemAbelian_two [IsSimpleGroup K] (hnc : ∃ a b : K, a * b ≠ b * a) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ V : Subgroup K, IsElemAbelian 2 V ∧ Nat.card V = 2 ^ k := by
  have heven : Even (Nat.card K) := by
    by_contra hodd
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard (G := K) (Nat.not_even_iff_odd.1 hodd)
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (IsSimpleGroup.comm_iff_isSolvable.2 hsolv a b)
  have h2 := CFSG.Walter.two_le_twoRank K hnc heven
  have hbdd : BddAbove
      {k | ∃ E : Subgroup K, E ≤ ⊤ ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} :=
    ⟨Nat.card K, fun k ⟨E, _, _, hk⟩ => (Nat.lt_two_pow_self).le.trans
      (hk ▸ Subgroup.card_le_card_group E)⟩
  have hne : ({k | ∃ E : Subgroup K, E ≤ ⊤ ∧ CFSG.Assembly.IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k} : Set ℕ).Nonempty :=
    ⟨0, ⊥, le_top, CFSG.SectionRank.isElemAbelian_bot 2, by simp⟩
  obtain ⟨V, -, hV, hVc⟩ := Nat.sSup_mem hne hbdd
  exact ⟨_, h2, V, hV, hVc⟩

theorem i1020_exists_twoLocal {q : ℕ} (hq : q.Prime) (h : 1 ≤ GLATwoLocalRank q K) :
    ∃ S₀ : Subgroup K, S₀ ≠ ⊥ ∧ IsPGroup 2 S₀ ∧ q ∣ Nat.card (normalizer (S₀ : Set K)) := by
  obtain ⟨H, hH, hH1⟩ : ∃ H : Subgroup K, IsTwoLocal H ∧ 1 ≤ pRank q H := by
    by_contra hno
    push Not at hno
    have : GLATwoLocalRank q K ≤ 0 := by
      refine csSup_le' ?_
      rintro k ⟨H, hH, rfl⟩
      have := hno H hH
      change pRank q H ≤ 0
      omega
    omega
  obtain ⟨E, hEH, -, hEc⟩ := CFSG.SectionRank.exists_pRank hq.one_lt H
  obtain ⟨P, hP, hPp, rfl⟩ := hH
  refine ⟨P, hP, hPp, ?_⟩
  have hne : pRank q (normalizer (P : Set K)) ≠ 0 := by omega
  refine (dvd_pow_self q hne).trans ?_
  rw [← hEc]
  exact card_dvd_of_le hEH

theorem i1020_le_glaTwoLocalRank {X : Type} [Group X] [Finite X] {q r : ℕ} (hq : q.Prime)
    {S E : Subgroup X} (hS : IsPGroup 2 S) (hSne : S ≠ ⊥) (hES : E ≤ normalizer (S : Set X))
    (hE : IsElemAbelian q E) (hEc : Nat.card E = q ^ r) : r ≤ GLATwoLocalRank q X := by
  refine (CFSG.SectionRank.le_pRank hq.one_lt hES hE hEc).trans (le_csSup ?_ ⟨_, ⟨S, hSne, hS,
    rfl⟩, rfl⟩)
  refine ⟨pRank q (⊤ : Subgroup X), ?_⟩
  rintro k ⟨H', -, rfl⟩
  exact CFSG.SectionRank.pRank_mono hq.one_lt le_top

end Final

theorem input10_20_3_proved : Input10_20_3 := by
  intro X _ _ Y _ K _ _ r hsimple hnc ⟨e⟩ q hq hq2
  set φ : X →* (Fin r → K) := e.toMonoidHom.comp (QuotientGroup.mk' Y)
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective Y)
  obtain ⟨k, hk, V, hV, hVc⟩ := i1020_exists_elemAbelian_two hnc
  constructor
  · intro h1
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · rw [hr0]; exact Nat.zero_le _
    obtain ⟨S₀, hS₀ne, hS₀, hqS₀⟩ := i1020_exists_twoLocal hq h1
    obtain ⟨S, hS, hSne, E, hES, hE, hEc⟩ :=
      i1020_main hnc hq hq2 hk hV hVc True hS₀ (fun _ => hS₀ne) hqS₀ (Nat.card X) X le_rfl r φ
        hφ (fun _ => hr0)
    exact i1020_le_glaTwoLocalRank hq hS (hSne trivial) hES hE hEc
  · intro h1
    have hqK : q ∣ Nat.card K := by
      obtain ⟨E, -, -, hEc⟩ := CFSG.SectionRank.exists_pRank hq.one_lt (⊤ : Subgroup K)
      refine (dvd_pow_self q (by omega : pRank q (⊤ : Subgroup K) ≠ 0)).trans ?_
      rw [← hEc]
      exact card_subgroup_dvd_card E
    have hbot : q ∣ Nat.card (normalizer ((⊥ : Subgroup K) : Set K)) := by
      rw [normalizer_eq_top_iff.2 (inferInstance : (⊥ : Subgroup K).Normal), card_top]
      exact hqK
    obtain ⟨S, -, -, E, -, hE, hEc⟩ :=
      i1020_main hnc hq hq2 hk hV hVc False IsPGroup.of_bot (fun h => h.elim) hbot (Nat.card X) X
        le_rfl r φ hφ (fun h => h.elim)
    exact CFSG.SectionRank.le_pRank hq.one_lt le_top hE hEc

end CFSG.HardMathSupport.Solomon.Coordinator
