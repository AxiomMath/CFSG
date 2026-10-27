module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bDesc
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt73

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti

@[expose] def fAlt5 : CFSGIndex → Prop
  | .alternating n _ => n = 5
  | _ => False

@[expose] def fAlt6 : CFSGIndex → Prop
  | .alternating n _ => n = 6
  | _ => False

@[expose] def fAlt8 : CFSGIndex → Prop
  | .alternating n _ => n = 8
  | _ => False

@[expose] def fL27 : CFSGIndex → Prop := onLie fun d => match d with
  | .A 1 q => q.card = 7
  | _ => False

@[expose] def fU33 : CFSGIndex → Prop := onLie fun d => match d with
  | .twistedA 2 q => q.card = 3
  | _ => False

@[expose] def fTits : CFSGIndex → Prop := onLie fun d => match d with
  | .tits => True
  | _ => False

@[expose] def fSp62 : CFSGIndex → Prop := onLie fun d => match d with
  | .B 3 q => q.card = 2
  | _ => False

@[expose] def fU42 : CFSGIndex → Prop := onLie fun d => match d with
  | .twistedA 3 q => q.card = 2
  | _ => False

@[expose] def fU52 : CFSGIndex → Prop := onLie fun d => match d with
  | .twistedA 4 q => q.card = 2
  | _ => False

@[expose] def fO8p2 : CFSGIndex → Prop := onLie fun d => match d with
  | .D 4 q => q.card = 2
  | _ => False

@[expose] def fTD42 : CFSGIndex → Prop := onLie fun d => match d with
  | .trialityD4 q => q.card = 2
  | _ => False

@[expose] def fL28 : CFSGIndex → Prop := onLie fun d => match d with
  | .A 1 q => q.card = 8
  | _ => False

@[expose] def fU38 : CFSGIndex → Prop := onLie fun d => match d with
  | .twistedA 2 q => q.card = 8
  | _ => False

@[expose] def fLinear : CFSGIndex → Prop := onLie fun d => match d with
  | .A n q => q.p = 2 ∧ ¬ (n = 1 ∧ q.card = 8)
  | _ => False

@[expose] def fUnitary : CFSGIndex → Prop := onLie fun d => match d with
  | .twistedA n q => q.p = 2 ∧ ¬ (n = 2 ∧ q.card = 8) ∧ ¬ (n = 3 ∧ q.card = 2) ∧ ¬ (n = 4 ∧ q.card = 2)
  | _ => False

@[expose] def fSymplectic : CFSGIndex → Prop := onLie fun d => match d with
  | .B n q => q.p = 2 ∧ ¬ (n = 3 ∧ q.card = 2)
  | _ => False

@[expose] def fOmegaPlus : CFSGIndex → Prop := onLie fun d => match d with
  | .D n q => q.p = 2 ∧ ¬ (n = 4 ∧ q.card = 2)
  | _ => False

@[expose] def fOmegaMinus : CFSGIndex → Prop := onLie fun d => match d with
  | .twistedD _ q => q.p = 2
  | _ => False

@[expose] def fE6 : CFSGIndex → Prop := onLie fun d => match d with
  | .E6 q => q.p = 2
  | _ => False

@[expose] def fE7 : CFSGIndex → Prop := onLie fun d => match d with
  | .E7 q => q.p = 2
  | _ => False

@[expose] def fE8 : CFSGIndex → Prop := onLie fun d => match d with
  | .E8 q => q.p = 2
  | _ => False

@[expose] def fF4 : CFSGIndex → Prop := onLie fun d => match d with
  | .F4 q => q.p = 2
  | _ => False

@[expose] def fG2 : CFSGIndex → Prop := onLie fun d => match d with
  | .G2 q => q.p = 2
  | _ => False

@[expose] def fTwE6 : CFSGIndex → Prop := onLie fun d => match d with
  | .twistedE6 q => q.p = 2
  | _ => False

@[expose] def fTriD4 : CFSGIndex → Prop := onLie fun d => match d with
  | .trialityD4 q => q.p = 2 ∧ ¬ q.card = 2
  | _ => False

@[expose] def fSuzuki : CFSGIndex → Prop := onLie fun d => match d with
  | .suzuki _ => True
  | _ => False

@[expose] def fReeTits : CFSGIndex → Prop := onLie fun d => match d with
  | .reeF4 _ => True
  | _ => False

@[expose] def KDescFam (p : ℕ) (Q : CFSGIndex → Prop) : Prop :=
  p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), KHyp p K B →
    catalogIs (↥K ⧸ Subgroup.center ↥K) Q → Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < p ^ 3 →
    KConcl p K B ∨ ∃ D J : Subgroup Y, DescData p K B D J

structure I264bFacts (p : ℕ) : Prop where
  alt5 : KDescFam p fAlt5
  alt6 : KDescFam p fAlt6
  alt8 : KDescFam p fAlt8
  l27 : KDescFam p fL27
  u33 : KDescFam p fU33
  tits : KDescFam p fTits
  sp62 : KDescFam p fSp62
  u42 : KDescFam p fU42
  u52 : KDescFam p fU52
  o8p2 : KDescFam p fO8p2
  td42 : KDescFam p fTD42
  l28 : KDescFam p fL28
  u38 : KDescFam p fU38
  linear : KDescFam p fLinear
  unitary : KDescFam p fUnitary
  symplectic : KDescFam p fSymplectic
  omegaPlus : KDescFam p fOmegaPlus
  omegaMinus : KDescFam p fOmegaMinus
  e6 : KDescFam p fE6
  e7 : KDescFam p fE7
  e8 : KDescFam p fE8
  f4 : KDescFam p fF4
  g2 : KDescFam p fG2
  twE6 : KDescFam p fTwE6
  triD4 : KDescFam p fTriD4
  suzuki : KDescFam p fSuzuki
  reeTits : KDescFam p fReeTits

theorem kDescOrDirect_of_facts {p : ℕ} (F : I264bFacts p) : KDescOrDirect p := by
  intro hp hp2 Y _ _ K B hK hc
  have hchev := hK.chev
  rcases hchev with ⟨i, hi, e⟩ | ⟨i, hi, e⟩
  ·
    cases i with
    | cyclic q hq => exact hi.elim
    | sporadic s => exact hi.elim
    | alternating n hn => exact hi.elim
    | lie dd =>
      obtain ⟨d, hv⟩ := dd
      change d.characteristic = 2 at hi
      cases d with
      | A n q =>
        simp only [LieTypeIndex.characteristic_A] at hi
        by_cases h8 : n = 1 ∧ q.card = 8
        · obtain ⟨rfl, hq8⟩ := h8
          exact F.l28 hp hp2 Y K B hK ⟨.lie ⟨.A 1 q, hv⟩, hq8, e⟩ hc
        · exact F.linear hp hp2 Y K B hK ⟨.lie ⟨.A n q, hv⟩, ⟨hi, h8⟩, e⟩ hc
      | twistedA n q =>
        simp only [LieTypeIndex.characteristic_twistedA] at hi
        by_cases h38 : n = 2 ∧ q.card = 8
        · obtain ⟨rfl, hq8⟩ := h38
          exact F.u38 hp hp2 Y K B hK ⟨.lie ⟨.twistedA 2 q, hv⟩, hq8, e⟩ hc
        by_cases h42 : n = 3 ∧ q.card = 2
        · obtain ⟨rfl, hq2⟩ := h42
          exact F.u42 hp hp2 Y K B hK ⟨.lie ⟨.twistedA 3 q, hv⟩, hq2, e⟩ hc
        by_cases h52 : n = 4 ∧ q.card = 2
        · obtain ⟨rfl, hq2⟩ := h52
          exact F.u52 hp hp2 Y K B hK ⟨.lie ⟨.twistedA 4 q, hv⟩, hq2, e⟩ hc
        exact F.unitary hp hp2 Y K B hK ⟨.lie ⟨.twistedA n q, hv⟩, ⟨hi, h38, h42, h52⟩, e⟩ hc
      | B n q =>
        simp only [LieTypeIndex.characteristic_B] at hi
        by_cases h62 : n = 3 ∧ q.card = 2
        · obtain ⟨rfl, hq2⟩ := h62
          exact F.sp62 hp hp2 Y K B hK ⟨.lie ⟨.B 3 q, hv⟩, hq2, e⟩ hc
        exact F.symplectic hp hp2 Y K B hK ⟨.lie ⟨.B n q, hv⟩, ⟨hi, h62⟩, e⟩ hc
      | C n q =>
        simp only [LieTypeIndex.characteristic_C] at hi
        exfalso
        have hv1 := ((LieTypeIndex.valid_iff _).1 hv).1
        simp only [LieTypeIndex.inStandardRange_iff] at hv1
        exact hv1.2 hi
      | D n q =>
        simp only [LieTypeIndex.characteristic_D] at hi
        by_cases h82 : n = 4 ∧ q.card = 2
        · obtain ⟨rfl, hq2⟩ := h82
          exact F.o8p2 hp hp2 Y K B hK ⟨.lie ⟨.D 4 q, hv⟩, hq2, e⟩ hc
        exact F.omegaPlus hp hp2 Y K B hK ⟨.lie ⟨.D n q, hv⟩, ⟨hi, h82⟩, e⟩ hc
      | twistedD n q =>
        simp only [LieTypeIndex.characteristic_twistedD] at hi
        exact F.omegaMinus hp hp2 Y K B hK ⟨.lie ⟨.twistedD n q, hv⟩, hi, e⟩ hc
      | E6 q =>
        simp only [LieTypeIndex.characteristic_E6] at hi
        exact F.e6 hp hp2 Y K B hK ⟨.lie ⟨.E6 q, hv⟩, hi, e⟩ hc
      | E7 q =>
        simp only [LieTypeIndex.characteristic_E7] at hi
        exact F.e7 hp hp2 Y K B hK ⟨.lie ⟨.E7 q, hv⟩, hi, e⟩ hc
      | E8 q =>
        simp only [LieTypeIndex.characteristic_E8] at hi
        exact F.e8 hp hp2 Y K B hK ⟨.lie ⟨.E8 q, hv⟩, hi, e⟩ hc
      | F4 q =>
        simp only [LieTypeIndex.characteristic_F4] at hi
        exact F.f4 hp hp2 Y K B hK ⟨.lie ⟨.F4 q, hv⟩, hi, e⟩ hc
      | G2 q =>
        simp only [LieTypeIndex.characteristic_G2] at hi
        exact F.g2 hp hp2 Y K B hK ⟨.lie ⟨.G2 q, hv⟩, hi, e⟩ hc
      | twistedE6 q =>
        simp only [LieTypeIndex.characteristic_twistedE6] at hi
        exact F.twE6 hp hp2 Y K B hK ⟨.lie ⟨.twistedE6 q, hv⟩, hi, e⟩ hc
      | trialityD4 q =>
        simp only [LieTypeIndex.characteristic_trialityD4] at hi
        by_cases h2 : q.card = 2
        · exact F.td42 hp hp2 Y K B hK ⟨.lie ⟨.trialityD4 q, hv⟩, h2, e⟩ hc
        exact F.triD4 hp hp2 Y K B hK ⟨.lie ⟨.trialityD4 q, hv⟩, ⟨hi, h2⟩, e⟩ hc
      | suzuki m =>
        exact F.suzuki hp hp2 Y K B hK ⟨.lie ⟨.suzuki m, hv⟩, trivial, e⟩ hc
      | reeG2 m =>
        simp only [LieTypeIndex.characteristic_reeG2] at hi
        omega
      | reeF4 m =>
        exact F.reeTits hp hp2 Y K B hK ⟨.lie ⟨.reeF4 m, hv⟩, trivial, e⟩ hc
      | tits =>
        exact F.tits hp hp2 Y K B hK ⟨.lie ⟨.tits, hv⟩, trivial, e⟩ hc
  ·
    cases i with
    | cyclic q hq => exact hi.elim
    | sporadic s => exact hi.elim
    | alternating n hn =>
      change (n = 5 ∧ (2 = 2 ∨ 2 = 5)) ∨ (n = 6 ∧ (2 = 2 ∨ 2 = 3)) ∨ (n = 8 ∧ 2 = 2) at hi
      rcases hi with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨h8, -⟩
      · exact F.alt5 hp hp2 Y K B hK ⟨.alternating n hn, h5, e⟩ hc
      · exact F.alt6 hp hp2 Y K B hK ⟨.alternating n hn, h6, e⟩ hc
      · exact F.alt8 hp hp2 Y K B hK ⟨.alternating n hn, h8, e⟩ hc
    | lie dd =>
      obtain ⟨d, hv⟩ := dd
      cases d with
      | A n q =>
        rcases n with _ | _ | n
        · simp [ambiguousChev] at hi
        · simp only [ambiguousChev] at hi
          rcases hi with ⟨h7, -⟩ | ⟨-, h⟩
          · exact F.l27 hp hp2 Y K B hK ⟨.lie ⟨.A 1 q, hv⟩, h7, e⟩ hc
          · omega
        · simp [ambiguousChev] at hi
      | twistedA n q =>
        rcases n with _ | _ | _ | _ | n
        · simp [ambiguousChev] at hi
        · simp [ambiguousChev] at hi
        · simp only [ambiguousChev] at hi
          exact F.u33 hp hp2 Y K B hK ⟨.lie ⟨.twistedA 2 q, hv⟩, hi.1, e⟩ hc
        · simp only [ambiguousChev] at hi
          omega
        · simp [ambiguousChev] at hi
      | _ => simp [ambiguousChev] at hi

theorem i264bAt_of_facts {G : Type} [Group G] [Finite G] {p : ℕ}
    (hLB : p.Prime → ∀ (Y : Type) [Group Y] [Finite Y], LBalanceAt Y p) (F : I264bFacts p) :
    I264bAt G p :=
  i264bAt_of_K (kd264bK_of_descOrDirect hLB (kDescOrDirect_of_facts F))

theorem i264ChevTwoAt_of_facts {G : Type} [Group G] [Finite G] {p : ℕ}
    (hLB : p.Prime → ∀ (Y : Type) [Group Y] [Finite Y], LBalanceAt Y p) (F : I264bFacts p) :
    I264ChevTwoAt G p :=
  i264bAt_of_facts hLB F

end CFSG.LocalAnalysis.GLTheoremA
