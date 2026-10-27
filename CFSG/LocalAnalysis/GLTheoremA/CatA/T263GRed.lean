module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

@[expose] def T263GConcl (p : ℕ) {Ω : Type} [Group Ω] (S B : Subgroup Ω) : Prop :=
  (∃ E : Subgroup Ω, E ≤ B ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      GLAPLayer p (S ⊓ Subgroup.centralizer (E : Set Ω)) ≠ ⊥) ∨
    (p = 3 ∧ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1))

abbrev T263AmbPred : Type 1 := ∀ (Ω : Type) [Group Ω] [Finite Ω], Prop

@[expose] def t263KGroup : T263AmbPred := fun Ω _ _ => CFSG.Open.IsKGroup Ω

@[expose] def T263GenLt (κ : T263AmbPred) (N : ℕ) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω], κ Ω → ∀ (S B : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
    IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S) → Nat.card ↥S < N → S ⊔ B = ⊤ → GLAPPrimeCore p Ω = ⊥ →
    GLAIsBmax p B → 4 ≤ GLATwoLocalRank p Ω →
    (∃ T : Subgroup Ω, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ S ∧ B ≤ Subgroup.normalizer (T : Set Ω)) →
    Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < p ^ 3 → T263GConcl p S B

@[expose] def T263GenOn (κ : T263AmbPred) (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω], κ Ω → ∀ (S B : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
    IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S) → catalogIs (↥S ⧸ Subgroup.center ↥S) Q →
    T263GenLt κ (Nat.card ↥S) → S ⊔ B = ⊤ → GLAPPrimeCore p Ω = ⊥ →
    GLAIsBmax p B → 4 ≤ GLATwoLocalRank p Ω →
    (∃ T : Subgroup Ω, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ S ∧ B ≤ Subgroup.normalizer (T : Set Ω)) →
    Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < p ^ 3 → T263GConcl p S B

@[expose] def T263FactGenK : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω → ∀ (S B : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
    IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S) → S ⊔ B = ⊤ → GLAPPrimeCore p Ω = ⊥ →
    GLAIsBmax p B → 4 ≤ GLATwoLocalRank p Ω →
    (∃ T : Subgroup Ω, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ S ∧ B ≤ Subgroup.normalizer (T : Set Ω)) →
    Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < p ^ 3 → T263GConcl p S B

theorem t263FactGenK_iff : T263FactGenK ↔ ∀ N : ℕ, T263GenLt t263KGroup N := by
  constructor
  · intro h N p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc _ hSB hΩ hB h4 hT hC
    exact h p hp hp2 Ω hK S B hSn hSq hSp hSc hSB hΩ hB h4 hT hC
  · intro h p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hSB hΩ hB h4 hT hC
    exact h (Nat.card ↥S + 1) p hp hp2 Ω hK S B hSn hSq hSp hSc (Nat.lt_succ_self _) hSB hΩ hB h4 hT hC

theorem t263FactGen_of_K (h : T263FactGenK) : T263FactGen := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hSB hΩ hB h4 hT hC
  exact h p hp hp2 Ω hK S B hSn hSq hSp hSc hSB hΩ hB h4 hT hC

@[expose] def t263GLinAll : TauCeti.CFSGIndex → Prop :=
  onLie fun | .A _ q => q.p = 2 | _ => False

@[expose] def t263GL28 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .A 1 q => q.card = 8 | _ => False

@[expose] def t263GLin (i : TauCeti.CFSGIndex) : Prop :=
  t263GLinAll i ∧ ¬ t263GL28 i

@[expose] def t263GUniAll : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA _ q => q.p = 2 | _ => False

@[expose] def t263GU38 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA 2 q => q.card = 8 | _ => False

@[expose] def t263GUni (i : TauCeti.CFSGIndex) : Prop :=
  t263GUniAll i ∧ ¬ t263GU38 i

@[expose] def t263GSymp : TauCeti.CFSGIndex → Prop :=
  onLie fun | .B _ q => q.p = 2 | .C _ q => q.p = 2 | _ => False

@[expose] def t263GOrth : TauCeti.CFSGIndex → Prop :=
  onLie fun | .D _ q => q.p = 2 | _ => False

@[expose] def t263GTwOrth : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedD _ q => q.p = 2 | _ => False

@[expose] def t263GE6 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .E6 q => q.p = 2 | .twistedE6 q => q.p = 2 | _ => False

@[expose] def t263GExc : TauCeti.CFSGIndex → Prop :=
  onLie fun | .E7 q => q.p = 2 | .E8 q => q.p = 2 | .F4 q => q.p = 2 | .G2 q => q.p = 2 | _ => False

@[expose] def t263GTD4 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .trialityD4 q => q.p = 2 | _ => False

@[expose] def t263GSzAll : TauCeti.CFSGIndex → Prop :=
  onLie fun | .suzuki _ => True | _ => False

@[expose] def t263GSz32 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .suzuki 2 => True | _ => False

@[expose] def t263GSz (i : TauCeti.CFSGIndex) : Prop :=
  t263GSzAll i ∧ ¬ t263GSz32 i

@[expose] def t263GRee : TauCeti.CFSGIndex → Prop :=
  onLie fun | .reeF4 _ => True | _ => False

@[expose] def t263GTits : TauCeti.CFSGIndex → Prop :=
  onLie fun | .tits => True | _ => False

@[expose] def t263GAmbU33 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA 2 q => q.card = 3 | _ => False

@[expose] def t263GAmbAlt (i : TauCeti.CFSGIndex) : Prop :=
  ambiguousChev 2 i ∧ ¬ t263GAmbU33 i

@[expose] def t263GChev2 : TauCeti.CFSGIndex → Prop :=
  fun i => (onLie fun d => d.characteristic = 2) i ∨ ambiguousChev 2 i

theorem catalogIs_t263GChev2 {S : Type} [Group S] (h : IsChevSimple 2 S) : catalogIs S t263GChev2 := by
  rcases h with ⟨i, hi, e⟩ | ⟨i, hi, e⟩
  · exact ⟨i, Or.inl hi, e⟩
  · exact ⟨i, Or.inr hi, e⟩

inductive T263Fam : Type
  | lin | uni | symp | orth | twOrth | e6 | exc | td4 | sz | ree | tits | ambAlt | ambU33 | l28 | u38 | sz32

@[expose] def T263Fam.pred : T263Fam → TauCeti.CFSGIndex → Prop
  | .lin => t263GLin
  | .uni => t263GUni
  | .symp => t263GSymp
  | .orth => t263GOrth
  | .twOrth => t263GTwOrth
  | .e6 => t263GE6
  | .exc => t263GExc
  | .td4 => t263GTD4
  | .sz => t263GSz
  | .ree => t263GRee
  | .tits => t263GTits
  | .ambAlt => t263GAmbAlt
  | .ambU33 => t263GAmbU33
  | .l28 => t263GL28
  | .u38 => t263GU38
  | .sz32 => t263GSz32

theorem t263G_cover13 (i : TauCeti.CFSGIndex) (h : t263GChev2 i) :
    t263GLinAll i ∨ t263GUniAll i ∨ t263GSymp i ∨ t263GOrth i ∨ t263GTwOrth i ∨ t263GE6 i ∨ t263GExc i ∨
      t263GTD4 i ∨ t263GSzAll i ∨ t263GRee i ∨ t263GTits i ∨ t263GAmbAlt i ∨ t263GAmbU33 i := by
  rcases h with h | h
  · cases i with
    | cyclic p hp => simp [onLie] at h
    | alternating n hn => simp [onLie] at h
    | sporadic s => simp [onLie] at h
    | lie d =>
      obtain ⟨t, ht⟩ := d
      cases t <;>
        simp_all [onLie, t263GLinAll, t263GUniAll, t263GSymp, t263GOrth, t263GTwOrth, t263GE6, t263GExc, t263GTD4,
          t263GSzAll, t263GRee, t263GTits]
  · by_cases hu : t263GAmbU33 i
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr hu
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inl ⟨h, hu⟩

theorem t263G_cover (i : TauCeti.CFSGIndex) (h : t263GChev2 i) : ∃ f : T263Fam, f.pred i := by
  rcases t263G_cover13 i h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · by_cases hs : t263GL28 i
    · exact ⟨.l28, hs⟩
    · exact ⟨.lin, h, hs⟩
  · by_cases hs : t263GU38 i
    · exact ⟨.u38, hs⟩
    · exact ⟨.uni, h, hs⟩
  · exact ⟨.symp, h⟩
  · exact ⟨.orth, h⟩
  · exact ⟨.twOrth, h⟩
  · exact ⟨.e6, h⟩
  · exact ⟨.exc, h⟩
  · exact ⟨.td4, h⟩
  · by_cases hs : t263GSz32 i
    · exact ⟨.sz32, hs⟩
    · exact ⟨.sz, h, hs⟩
  · exact ⟨.ree, h⟩
  · exact ⟨.tits, h⟩
  · exact ⟨.ambAlt, h⟩
  · exact ⟨.ambU33, h⟩

theorem t263G_catalogIs_cover {S : Type} [Group S] (h : IsChevSimple 2 S) : ∃ f : T263Fam, catalogIs S f.pred := by
  obtain ⟨i, hi, e⟩ := catalogIs_t263GChev2 h
  obtain ⟨f, hf⟩ := t263G_cover i hi
  exact ⟨f, i, hf, e⟩

structure T263Families (P : (TauCeti.CFSGIndex → Prop) → Prop) : Prop where
  lin : P t263GLin
  uni : P t263GUni
  symp : P t263GSymp
  orth : P t263GOrth
  twOrth : P t263GTwOrth
  e6 : P t263GE6
  exc : P t263GExc
  td4 : P t263GTD4
  sz : P t263GSz
  ree : P t263GRee
  tits : P t263GTits
  ambAlt : P t263GAmbAlt
  ambU33 : P t263GAmbU33
  l28 : P t263GL28
  u38 : P t263GU38
  sz32 : P t263GSz32

theorem T263Families.apply {P : (TauCeti.CFSGIndex → Prop) → Prop} (h : T263Families P) (f : T263Fam) : P f.pred := by
  cases f
  exacts [h.lin, h.uni, h.symp, h.orth, h.twOrth, h.e6, h.exc, h.td4, h.sz, h.ree, h.tits, h.ambAlt, h.ambU33,
    h.l28, h.u38, h.sz32]

theorem T263Families.of_apply {P : (TauCeti.CFSGIndex → Prop) → Prop} (h : ∀ f : T263Fam, P f.pred) :
    T263Families P :=
  ⟨h .lin, h .uni, h .symp, h .orth, h .twOrth, h .e6, h .exc, h .td4, h .sz, h .ree, h .tits, h .ambAlt, h .ambU33,
    h .l28, h .u38, h .sz32⟩

theorem t263GenLt_of_families {κ : T263AmbPred} (h : T263Families (T263GenOn κ)) (N : ℕ) : T263GenLt κ N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro p hp hp2 Ω _ _ hκ S B hSn hSq hSp hSc hlt hSB hΩ hB h4 hT hC
    have hIH : T263GenLt κ (Nat.card ↥S) := ih _ hlt
    obtain ⟨f, hq⟩ := t263G_catalogIs_cover hSc
    exact h.apply f p hp hp2 Ω hκ S B hSn hSq hSp hSc hq hIH hSB hΩ hB h4 hT hC

theorem t263FactGenK_of_families (h : T263Families (T263GenOn t263KGroup)) : T263FactGenK :=
  t263FactGenK_iff.2 (t263GenLt_of_families h)

end CFSG.LocalAnalysis.GLTheoremA.T263

end
