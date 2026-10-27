module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPermCycle
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Defs

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup

section Pairs

variable {Ω : Type*}

@[expose] def MovedCyc (σ : Perm Ω) : Set (CycleSet σ) := Quotient.mk _ '' {x | σ x ≠ x}

abbrev PairSet (σ : Perm Ω) : Type _ := ↥(MovedCyc σ)

noncomputable instance [Fintype Ω] (σ : Perm Ω) : Fintype (PairSet σ) :=
  have : Finite (PairSet σ) := inferInstance
  Fintype.ofFinite _

noncomputable instance (σ : Perm Ω) : DecidableEq (PairSet σ) := Classical.decEq _

theorem mk_mem_MovedCyc_iff {σ : Perm Ω} (x : Ω) :
    (Quotient.mk _ x : CycleSet σ) ∈ MovedCyc σ ↔ σ x ≠ x := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hs : SameCycle σ y x := Quotient.exact hyx
    exact (not_congr hs.apply_eq_self_iff).1 hy
  · exact fun hx => ⟨x, hx, rfl⟩

theorem cycEquiv_mem_MovedCyc_iff {σ g : Perm Ω} (hg : g * σ = σ * g) (q : CycleSet σ) :
    cycEquiv σ g hg q ∈ MovedCyc σ ↔ q ∈ MovedCyc σ := by
  induction q using Quotient.inductionOn with
  | _ x =>
    rw [cycEquiv_mk, mk_mem_MovedCyc_iff, mk_mem_MovedCyc_iff]
    have key : σ (g x) = g (σ x) := (congrArg (fun e : Perm Ω => e x) hg).symm
    rw [key]
    exact not_congr (EmbeddingLike.apply_eq_iff_eq g)

@[expose] noncomputable def pairActPerm {σ : Perm Ω} (g : Perm Ω) (hg : g * σ = σ * g) :
    Perm (PairSet σ) :=
  (cycEquiv σ g hg).subtypePerm (fun q => cycEquiv_mem_MovedCyc_iff hg q)

theorem pairActPerm_mul {σ : Perm Ω} (g g' : Perm Ω) (hg : g * σ = σ * g)
    (hg' : g' * σ = σ * g') :
    pairActPerm (σ := σ) (g * g') (by rw [mul_assoc, hg', ← mul_assoc, hg, mul_assoc]) =
      pairActPerm g hg * pairActPerm g' hg' := by
  ext ⟨q, hq⟩
  induction q using Quotient.inductionOn with
  | _ x => rfl

theorem pairActPerm_one {σ : Perm Ω} :
    pairActPerm (σ := σ) 1 (by rw [one_mul, mul_one]) = 1 := by
  ext ⟨q, hq⟩
  induction q using Quotient.inductionOn with
  | _ x => rfl

theorem pairActPerm_congr {σ : Perm Ω} {g g' : Perm Ω} (h : g = g') (hg : g * σ = σ * g)
    (hg' : g' * σ = σ * g') : pairActPerm g hg = pairActPerm g' hg' := by
  subst h
  rfl

@[expose] noncomputable def pairAct {σ : Perm Ω} {H : Type*} [Group H] (ι : H →* Perm Ω)
    (hι : ∀ h, ι h * σ = σ * ι h) : H →* Perm (PairSet σ) where
  toFun h := pairActPerm (ι h) (hι h)
  map_one' := by
    suffices ∀ (g : Perm Ω) (hg : g * σ = σ * g), g = 1 → pairActPerm g hg = 1 from
      this _ _ (map_one ι)
    rintro g hg rfl
    exact pairActPerm_one
  map_mul' h h' := by
    suffices ∀ (g : Perm Ω) (hg : g * σ = σ * g), g = ι h * ι h' →
        pairActPerm g hg = pairActPerm (ι h) (hι h) * pairActPerm (ι h') (hι h') from
      this _ _ (map_mul ι h h')
    rintro g hg rfl
    exact pairActPerm_mul (ι h) (ι h') (hι h) (hι h')

theorem mk_apply_eq_mk (σ : Perm Ω) (x : Ω) :
    (Quotient.mk _ (σ x) : CycleSet σ) = Quotient.mk _ x :=
  Quotient.sound (sameCycle_apply_left.2 (SameCycle.refl σ x))

theorem eq_or_eq_apply_of_sameCycle {σ : Perm Ω} (hσ : σ * σ = 1) {x y : Ω}
    (h : SameCycle σ x y) : y = x ∨ y = σ x := by
  obtain ⟨i, rfl⟩ := h
  have h2 : σ ^ (2 : ℤ) = 1 := by rw [zpow_two, hσ]
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' i
  · left
    rw [zpow_mul, h2, one_zpow]
    rfl
  · right
    rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

noncomputable def pairSetRep {σ : Perm Ω} (q : PairSet σ) : Ω := Quotient.out q.1

theorem mk_pairSetRep {σ : Perm Ω} (q : PairSet σ) :
    (Quotient.mk _ (pairSetRep q) : CycleSet σ) = q.1 := Quotient.out_eq q.1

theorem pairSetRep_ne {σ : Perm Ω} (q : PairSet σ) : σ (pairSetRep q) ≠ pairSetRep q :=
  (mk_mem_MovedCyc_iff _).1 (by rw [mk_pairSetRep]; exact q.2)

theorem pairSetRep_injective {σ : Perm Ω} : Function.Injective (pairSetRep (σ := σ)) := by
  intro q q' h
  apply Subtype.ext
  rw [← mk_pairSetRep q, ← mk_pairSetRep q', h]

theorem pairSetRep_ne_apply {σ : Perm Ω} (q q' : PairSet σ) : pairSetRep q ≠ σ (pairSetRep q') := by
  intro h
  have hq : q = q' := by
    apply Subtype.ext
    rw [← mk_pairSetRep q, ← mk_pairSetRep q', h, mk_apply_eq_mk]
  subst hq
  exact pairSetRep_ne q h.symm

theorem card_support_eq_two_mul_card_pairSet [Fintype Ω] [DecidableEq Ω] {σ : Perm Ω}
    (hσ : σ * σ = 1) : σ.support.card = 2 * Fintype.card (PairSet σ) := by
  have hsupp : σ.support = Finset.univ.image (pairSetRep (σ := σ)) ∪
      Finset.univ.image fun q : PairSet σ => σ (pairSetRep q) := by
    ext y
    simp only [Perm.mem_support, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hy
      have hq : (Quotient.mk _ y : CycleSet σ) ∈ MovedCyc σ := (mk_mem_MovedCyc_iff y).2 hy
      have hsc : SameCycle σ (pairSetRep ⟨_, hq⟩) y := Quotient.exact (mk_pairSetRep ⟨_, hq⟩)
      rcases eq_or_eq_apply_of_sameCycle hσ hsc with h | h
      · exact Or.inl ⟨⟨_, hq⟩, h.symm⟩
      · exact Or.inr ⟨⟨_, hq⟩, h.symm⟩
    · rintro (⟨q, rfl⟩ | ⟨q, rfl⟩)
      · exact pairSetRep_ne q
      · exact fun h => pairSetRep_ne q (σ.injective h)
  have hdisj : Disjoint (Finset.univ.image (pairSetRep (σ := σ)))
      (Finset.univ.image fun q : PairSet σ => σ (pairSetRep q)) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy hy'
    obtain ⟨q, rfl⟩ := hy
    obtain ⟨q', hq'⟩ := hy'
    exact pairSetRep_ne_apply q q' hq'.symm
  have hinj : Function.Injective fun q : PairSet σ => σ (pairSetRep q) := fun q q' h =>
    pairSetRep_injective (σ.injective h)
  rw [hsupp, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ pairSetRep_injective,
    Finset.card_image_of_injective _ hinj, Finset.card_univ]
  ring

theorem card_pairSet {n : ℕ} {σ : Perm (Fin n)} (hσ : σ * σ = 1) :
    Fintype.card (PairSet σ) = transCount σ := by
  rw [transCount, card_support_eq_two_mul_card_pairSet hσ]
  omega

theorem pairActPerm_self (σ : Perm Ω) : pairActPerm σ (rfl : σ * σ = σ * σ) = 1 := by
  ext ⟨q, hq⟩
  induction q using Quotient.inductionOn with
  | _ x => exact mk_apply_eq_mk σ x

theorem pairActPerm_apply_ne {σ : Perm Ω} (hσ : σ * σ = 1) {g : Perm Ω} (hg : g * σ = σ * g)
    (hgg : g * g = σ) (q : PairSet σ) : pairActPerm g hg q ≠ q := by
  obtain ⟨q, hq⟩ := q
  induction q using Quotient.inductionOn with
  | _ x =>
    intro h
    have hx : σ x ≠ x := (mk_mem_MovedCyc_iff x).1 hq
    have h1 : (Quotient.mk _ (g x) : CycleSet σ) = Quotient.mk _ x := congrArg Subtype.val h
    have h2 : SameCycle σ (g x) x := Quotient.exact h1
    have hgg' : g (g x) = σ x := congrArg (fun e : Perm Ω => e x) hgg
    rcases eq_or_eq_apply_of_sameCycle hσ h2.symm with h3 | h3
    · exact hx (hgg'.symm.trans ((congrArg g h3).trans h3))
    · have h4 : g (σ x) = σ x := (congrArg g h3).symm.trans hgg'
      exact hx (g.injective (h4.trans h3.symm))

theorem coe_pairActPerm_rep {σ : Perm Ω} (g : Perm Ω) (hg : g * σ = σ * g) (q : PairSet σ) :
    ((pairActPerm g hg q : PairSet σ) : CycleSet σ) = Quotient.mk _ (g (pairSetRep q)) :=
  (congrArg (cycEquiv σ g hg) (mk_pairSetRep q).symm).trans (cycEquiv_mk σ g hg _)

theorem exists_lift_threeCycle [Fintype Ω] [DecidableEq Ω] {σ : Perm Ω} (hσ : σ * σ = 1)
    {c : Perm (PairSet σ)} (hc : c.IsThreeCycle) :
    ∃ (ĉ : Perm Ω) (hĉ : ĉ * σ = σ * ĉ), ĉ ^ 3 = 1 ∧ sign ĉ = 1 ∧ pairActPerm ĉ hĉ = c := by
  have hσ' : ∀ x, σ (σ x) = x := fun x => congrArg (fun e : Perm Ω => e x) hσ
  have hf : Function.Injective
      (Sum.elim (pairSetRep (σ := σ)) fun q : PairSet σ => σ (pairSetRep q)) := by
    rintro (q | q) (q' | q') h
    · exact congrArg Sum.inl (pairSetRep_injective h)
    · exact absurd h (pairSetRep_ne_apply q q')
    · exact absurd h.symm (pairSetRep_ne_apply q' q)
    · exact congrArg Sum.inr (pairSetRep_injective (σ.injective h))
  obtain ⟨e, he1, he2⟩ : ∃ e : PairSet σ ⊕ PairSet σ ↪ Ω,
      (∀ q, e (Sum.inl q) = pairSetRep q) ∧ ∀ q, e (Sum.inr q) = σ (pairSetRep q) :=
    ⟨⟨_, hf⟩, fun _ => rfl, fun _ => rfl⟩
  obtain ⟨ĉ, h1, h2, h3, hcube⟩ : ∃ ĉ : Perm Ω, (∀ q, ĉ (pairSetRep q) = pairSetRep (c q)) ∧
      (∀ q, ĉ (σ (pairSetRep q)) = σ (pairSetRep (c q))) ∧
      (∀ y, y ∉ Set.range e → ĉ y = y) ∧ ĉ ^ 3 = 1 := by
    refine ⟨(Perm.sumCongr c c).viaEmbedding e, fun q => ?_, fun q => ?_, fun y hy => ?_, ?_⟩
    · simpa [he1] using Perm.viaEmbedding_apply (Perm.sumCongr c c) e (Sum.inl q)
    · simpa [he1, he2] using Perm.viaEmbedding_apply (Perm.sumCongr c c) e (Sum.inr q)
    · exact Perm.viaEmbedding_apply_of_notMem _ e y hy
    · have hc3 : c ^ 3 = 1 := by
        have := pow_orderOf_eq_one c
        rwa [hc.orderOf] at this
      have hpow : ∀ n : ℕ, Perm.sumCongr c c ^ n = Perm.sumCongr (c ^ n) (c ^ n) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, ih, pow_succ, Perm.sumCongr_mul]
      have := map_pow (Perm.viaEmbeddingHom e) (Perm.sumCongr c c) 3
      rw [hpow, hc3, Perm.sumCongr_one, map_one] at this
      exact this.symm
  have hcomm : ĉ * σ = σ * ĉ := by
    ext y
    show ĉ (σ y) = σ (ĉ y)
    by_cases hy : y ∈ Set.range e
    · obtain ⟨(q | q), rfl⟩ := hy
      · rw [he1, h2, h1]
      · rw [he2, hσ', h1, h2, hσ']
    · have hy' : σ y ∉ Set.range e := by
        rintro ⟨(q | q), hq⟩
        · rw [he1] at hq
          exact hy ⟨Sum.inr q, by rw [he2, hq, hσ']⟩
        · rw [he2] at hq
          exact hy ⟨Sum.inl q, by rw [he1]; exact σ.injective hq⟩
      rw [h3 y hy, h3 (σ y) hy']
  have hsign : sign ĉ = 1 := by
    have h3' : sign ĉ ^ 3 = 1 := by rw [← map_pow, hcube, map_one]
    rcases Int.units_eq_one_or (sign ĉ) with h | h
    · exact h
    · rw [h] at h3'
      exact absurd h3' (by decide)
  refine ⟨ĉ, hcomm, hcube, hsign, ?_⟩
  ext q
  rw [coe_pairActPerm_rep, h1, mk_pairSetRep]

end Pairs

end CFSG.OddStandard.Solomon75
