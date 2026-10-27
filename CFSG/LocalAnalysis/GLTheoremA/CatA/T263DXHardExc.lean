module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXHard
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXSelQ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXEasyInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

@[expose] def t263GExcHard4 (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E7 q | .E8 q | .F4 q | .G2 q => q.p = 2 ∧ 4 ≤ q.card ∧ ¬ p ∣ q.card ^ 2 - 1
    | _ => False

@[expose] def t263GExcHard2 (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E7 q | .E8 q | .F4 q | .G2 q => q.card = 2 ∧ ¬ p ∣ q.card ^ 2 - 1
    | _ => False

@[expose] def t263GE6UHard4 (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E6 q => q.p = 2 ∧ 4 ≤ q.card ∧ ¬ p ∣ q.card ^ 2 - 1
    | _ => False

@[expose] def t263GE6THard4 (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .twistedE6 q => q.p = 2 ∧ 4 ≤ q.card ∧ ¬ p ∣ q.card ^ 2 - 1
    | _ => False

@[expose] def t263GE6Hard2 (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E6 q | .twistedE6 q => q.card = 2 ∧ ¬ p ∣ q.card ^ 2 - 1
    | _ => False

theorem T263SelWP.of_cover {Q Q₁ Q₂ : ℕ → TauCeti.CFSGIndex → Prop}
    (hcov : ∀ p i, Q p i → Q₁ p i ∨ Q₂ p i) (h₁ : T263SelWP Q₁) (h₂ : T263SelWP Q₂) :
    T263SelWP Q := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hcat
  obtain ⟨i, hi, e⟩ := hcat
  rcases hcov p i hi with h | h
  · exact h₁ p hp hp2 Ω hK S B hSn hSq hSp hSc ⟨i, h, e⟩
  · exact h₂ p hp hp2 Ω hK S B hSn hSq hSp hSc ⟨i, h, e⟩

private theorem cover_hard {p : ℕ} {q : TauCeti.PrimePower} (h : q.p = 2 ∧ ¬ p ∣ q.card ^ 2 - 1) :
    (q.p = 2 ∧ 4 ≤ q.card ∧ ¬ p ∣ q.card ^ 2 - 1) ∨ (q.card = 2 ∧ ¬ p ∣ q.card ^ 2 - 1) := by
  rcases card_eq_two_or_four_le h.1 with h2 | h4
  · exact Or.inr ⟨h2, h.2⟩
  · exact Or.inl ⟨h.1, h4, h.2⟩

theorem t263SelWP_excHard_of (h4 : T263SelWP t263GExcHard4) (h2 : T263SelWP t263GExcHard2) :
    T263SelWP t263GExcHard := by
  refine T263SelWP.of_cover ?_ h4 h2
  intro p i hi
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d <;> simp only [t263GExcHard, t263GExcHard4, t263GExcHard2, onLie] at hi ⊢ <;>
      first | exact hi.elim | exact cover_hard hi
  | cyclic r hr => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim

theorem t263SelWP_e6Hard_of (hu : T263SelWP t263GE6UHard4) (ht : T263SelWP t263GE6THard4)
    (h2 : T263SelWP t263GE6Hard2) : T263SelWP t263GE6Hard := by
  refine T263SelWP.of_cover ?_ (hu.or ht) h2
  intro p i hi
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d <;>
      simp only [t263GE6Hard, t263GE6UHard4, t263GE6THard4, t263GE6Hard2, onLie] at hi ⊢ <;>
      first
        | exact hi.elim
        | exact (cover_hard hi).imp_left Or.inl
        | exact (cover_hard hi).imp_left Or.inr
        | tauto
  | cyclic r hr => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim

theorem three_dvd_card_sq_sub_one {q : TauCeti.PrimePower} (h : q.p = 2) :
    3 ∣ q.card ^ 2 - 1 := by
  rw [TauCeti.PrimePower.card_def, h, ← pow_mul, mul_comm, pow_mul]
  have := Nat.sub_one_dvd_pow_sub_one (2 ^ 2) q.exponent
  simpa using this

@[expose] def AdjCompTriv : Prop :=
  ∀ {τ : Tag}, (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
    ∀ (K : Type) [Field K] [Finite K], ringChar K = 2 → 4 ≤ Nat.card K →
      ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card K ^ 2 - 1 → CompTriv p ↥(adjointGroup τ K)


theorem modelSelQ_adjointGroup {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) (hK4 : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ModelSelQ p ↥(adjointGroup τ K) := by
  intro r hrp hr1 P hPr hP2 hP1
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj r
  have hβp : (MulAut.conj r) ^ p = 1 := by rw [← map_pow, hrp, map_one]
  have hβ1 : MulAut.conj r ≠ 1 := by
    intro h
    refine hr1 (Subgroup.mem_bot.1 ?_)
    rw [← center_adjointGroup_eq_bot (τ := τ) (K := K), Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun f : MulAut ↥(adjointGroup τ K) => f g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    rwa [mul_inv_eq_iff_eq_mul, eq_comm] at h1
  have hβmem : MulAut.conj r ∈ innAutDerived ↥(adjointGroup τ K) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived _ ⟨r, rfl⟩
  have := exists_comp_of_adjointGroup_q hτ hK2 hK4 hp hp2 (MulAut.conj r) hβmem hβp hβ1 P
    (hfix ▸ hPr) hP2 hP1
  rwa [hfix] at this

private theorem exists_modelSelH_untw_cat (hA : AdjCompTriv) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (q : TauCeti.PrimePower)
    (hv : (c q).Valid) (hq2 : q.p = 2) (hq4 : 4 ≤ q.card) (hpq : ¬ p ∣ q.card ^ 2 - 1)
    {X : Type} [Group X] (e : X ≃* (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group) :
    ∃ (T : Type) (_ : Group T) (_ : Finite T), Nonempty (X ≃* T) ∧ ModelSelH p T := by
  obtain ⟨K, _, _, hK, hKc, ⟨φ⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  have hK2 : ringChar K = 2 := by rw [ringChar.eq K q.p, hq2]
  exact ⟨↥(adjointGroup τ K), inferInstance, inferInstance, ⟨e.trans φ⟩,
    modelSelH_of_triv (modelSelQ_adjointGroup hτ hK2 (hK ▸ hq4) hp hp2)
      (hA hτ K hK2 (hK ▸ hq4) p hp hp2 (hK ▸ hpq))⟩

theorem t263SelWP_excHard4_of (hA : AdjCompTriv) : T263SelWP t263GExcHard4 := by
  refine t263SelWP_of_modelH (fun p hp hp2 X _ h => ?_)
    (fun p hp hp2 Ω _ _ S x hSn hSq hSp hcat hxp hInn => ?_)
  · obtain ⟨i, hi, ⟨e⟩⟩ := h
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | E7 q =>
        obtain ⟨hq2, hq4, hpq⟩ := hi
        exact exists_modelSelH_untw_cat hA hp hp2 (by simp)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv hq2 hq4 hpq e
      | E8 q =>
        obtain ⟨hq2, hq4, hpq⟩ := hi
        exact exists_modelSelH_untw_cat hA hp hp2 (by simp)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv hq2 hq4 hpq e
      | F4 q =>
        obtain ⟨hq2, hq4, hpq⟩ := hi
        exact exists_modelSelH_untw_cat hA hp hp2 (by simp)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv hq2 hq4 hpq e
      | G2 q =>
        obtain ⟨hq2, hq4, hpq⟩ := hi
        exact exists_modelSelH_untw_cat hA hp hp2 (by simp)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv hq2 hq4 hpq e
      | _ => exact hi.elim
    | cyclic r hr => exact hi.elim
    | alternating n hn => exact hi.elim
    | sporadic s => exact hi.elim
  · refine inducesInnerMod_excInner hp hp2 hSn hSq hSp (S10.catalogIs_imp ?_ hcat) hxp hInn
    intro i hi
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d <;> simp only [t263GExcHard4, t263GExcInner, onLie] at hi ⊢ <;>
        first | exact hi.elim | exact hi.1
    | cyclic r hr => exact hi.elim
    | alternating n hn => exact hi.elim
    | sporadic s => exact hi.elim

theorem t263SelWP_e6UHard4_of (hA : AdjCompTriv) : T263SelWP t263GE6UHard4 := by
  refine t263SelWP_of_modelH (fun p hp hp2 X _ h => ?_)
    (fun p hp hp2 Ω _ _ S x hSn hSq hSp hcat hxp hInn => ?_)
  · obtain ⟨i, hi, ⟨e⟩⟩ := h
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | E6 q =>
        obtain ⟨hq2, hq4, hpq⟩ := hi
        exact exists_modelSelH_untw_cat hA hp hp2 (by simp)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv hq2 hq4 hpq e
      | _ => exact hi.elim
    | cyclic r hr => exact hi.elim
    | alternating n hn => exact hi.elim
    | sporadic s => exact hi.elim
  · refine inducesInnerMod_e6Inner hp hp2 hSn hSq hSp (S10.catalogIs_imp ?_ hcat) hxp hInn
    intro i hi
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d <;> simp only [t263GE6UHard4, t263GE6Inner, onLie] at hi ⊢ <;>
        first
          | exact hi.elim
          | exact ⟨hi.1, fun h3 => hi.2.2 (h3.1 ▸ three_dvd_card_sq_sub_one hi.1)⟩
    | cyclic r hr => exact hi.elim
    | alternating n hn => exact hi.elim
    | sporadic s => exact hi.elim

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
