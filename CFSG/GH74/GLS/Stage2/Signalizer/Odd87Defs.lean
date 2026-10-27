module

public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt41
public import CFSG.GH74.Generic.Sections

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Families

variable (Y : Type) [Group Y]

@[expose] def FAlt : Prop :=
  ∃ n : ℕ, 7 ≤ n ∧ n ≤ 11 ∧ Nonempty (Y ≃* alternatingGroup (Fin n))

@[expose] def FSpor : Prop :=
  NativeSporadic.IsSporadic Y .M11 ∨ NativeSporadic.IsSporadic Y .M12 ∨ NativeSporadic.IsSporadic Y .M22 ∨
    NativeSporadic.IsSporadic Y .M23 ∨ NativeSporadic.IsSporadic Y .J1 ∨ NativeSporadic.IsSporadic Y .J2 ∨
    NativeSporadic.IsSporadic Y .J3

@[expose] def FMcLy : Prop := NativeSporadic.IsSporadic Y .McL ∨ NativeSporadic.IsSporadic Y .Ly

@[expose] def FTwo : Prop :=
  LieModel Y .PSL 2 2 3 ∨ LieModel Y .PSL 2 2 4 ∨ LieModel Y .PSL 3 2 2 ∨ LieModel Y .PSU 3 2 2 ∨
    LieModel Y .twistedB2 0 2 3

@[expose] def FL2 : Prop := ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ≠ 2 ∧ LieModel Y .PSL 2 p f

@[expose] def FL3 : Prop := ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ≠ 2 ∧ LieModel Y .PSL 3 p f

@[expose] def FU3 : Prop := ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ≠ 2 ∧ LieModel Y .PSU 3 p f

@[expose] def FSp4 : Prop := ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ≠ 2 ∧ LieModel Y .PSp 2 p f

@[expose] def FG2 : Prop := ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ≠ 2 ∧ LieModel Y .G2 0 p f

@[expose] def FD4 : Prop := ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ≠ 2 ∧ LieModel Y .trialityD4 0 p f

@[expose] def FL4 : Prop :=
  ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ≠ 2 ∧ p ^ f % 8 ≠ 1 ∧ LieModel Y .PSL 4 p f

@[expose] def FU4 : Prop :=
  ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ≠ 2 ∧ p ^ f % 8 ≠ 7 ∧ LieModel Y .PSU 4 p f

@[expose] def FL5 : Prop := ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧ LieModel Y .PSL 5 p f

@[expose] def FU5 : Prop := ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧ LieModel Y .PSU 5 p f

@[expose] def FRee : Prop := ∃ f : ℕ, 1 ≤ f ∧ LieModel Y .twistedG2 0 3 f

theorem ghList_cases {Y : Type} [Group Y] (h : GHList Y) :
    FAlt Y ∨ FSpor Y ∨ FMcLy Y ∨ FTwo Y ∨ FL2 Y ∨ FL3 Y ∨ FU3 Y ∨ FSp4 Y ∨ FG2 Y ∨ FD4 Y ∨ FL4 Y ∨
      FU4 Y ∨ FL5 Y ∨ FU5 Y ∨ FRee Y := by
  rcases h with hA | (h | h | h | h | h | h | h | h | h) |
      ⟨p, f, hp, hf, ⟨hp2, h | h | h | h | h | h⟩ | ⟨hp2, hq, h⟩ | ⟨hp2, hq, h⟩ | ⟨hq, h⟩ |
        ⟨hq, h⟩ | h | ⟨hp2, h | h | h | h | h⟩⟩
  · have h' : FAlt Y := hA
    tauto
  · have h' : FSpor Y := Or.inl h
    tauto
  · have h' : FSpor Y := Or.inr (Or.inl h)
    tauto
  · have h' : FSpor Y := Or.inr (Or.inr (Or.inl h))
    tauto
  · have h' : FSpor Y := Or.inr (Or.inr (Or.inr (Or.inl h)))
    tauto
  · have h' : FSpor Y := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    tauto
  · have h' : FSpor Y := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    tauto
  · have h' : FSpor Y := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    tauto
  · have h' : FMcLy Y := Or.inl h
    tauto
  · have h' : FMcLy Y := Or.inr h
    tauto
  · have h' : FL2 Y := ⟨p, f, hp, hf, hp2, h⟩
    tauto
  · have h' : FL3 Y := ⟨p, f, hp, hf, hp2, h⟩
    tauto
  · have h' : FU3 Y := ⟨p, f, hp, hf, hp2, h⟩
    tauto
  · have h' : FSp4 Y := ⟨p, f, hp, hf, hp2, h⟩
    tauto
  · have h' : FG2 Y := ⟨p, f, hp, hf, hp2, h⟩
    tauto
  · have h' : FD4 Y := ⟨p, f, hp, hf, hp2, h⟩
    tauto
  · have h' : FL4 Y := ⟨p, f, hp, hf, hp2, hq, h⟩
    tauto
  · have h' : FU4 Y := ⟨p, f, hp, hf, hp2, hq, h⟩
    tauto
  · have h' : FL5 Y := ⟨p, f, hp, hf, hq, h⟩
    tauto
  · have h' : FU5 Y := ⟨p, f, hp, hf, hq, h⟩
    tauto
  · have h' : FRee Y := ⟨f, hf, h⟩
    tauto
  · have h' : FTwo Y := Or.inl h
    tauto
  · have h' : FTwo Y := Or.inr (Or.inl h)
    tauto
  · have h' : FTwo Y := Or.inr (Or.inr (Or.inl h))
    tauto
  · have h' : FTwo Y := Or.inr (Or.inr (Or.inr (Or.inl h)))
    tauto
  · have h' : FTwo Y := Or.inr (Or.inr (Or.inr (Or.inr h)))
    tauto

end Families

@[expose] def Cell87 (F : (Y : Type) → [Group Y] → Prop) : Prop :=
  Prop4_1a → Prop4_1b →
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal] (hz : z ∈ H₀) (p : ℕ)
      (X : Subgroup (Sec H₀ H₁)), Sig4B G z H₀ H₁ hz p X → Hyp42 (zSec z H₀ hz H₁) X →
      F (↥(layer (Sec H₀ H₁)) ⧸ center ↥(layer (Sec H₀ H₁))) →
      Concl42 k (zSec z H₀ hz H₁) p X

theorem ghList_layerBar {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}
    (hctx : Stage2Ctx G z k S) {H₀ : Subgroup G} {H₁ : Subgroup ↥H₀} [H₁.Normal] {hz : z ∈ H₀}
    {p : ℕ} {X : Subgroup (Sec H₀ H₁)} (hsig : Sig4B G z H₀ H₁ hz p X)
    (hyp : Hyp42 (zSec z H₀ hz H₁) X) :
    GHList (↥(layer (Sec H₀ H₁)) ⧸ center ↥(layer (Sec H₀ H₁))) := by
  set K : Subgroup (Sec H₀ H₁) := layer (Sec H₀ H₁) with hK
  have hq : IsQuasisimple ↥K := hyp.2.1
  let π : ↥H₀ →* Sec H₀ H₁ := QuotientGroup.mk' H₁
  let Kpre : Subgroup ↥H₀ := K.comap π
  let H : Subgroup G := Kpre.map H₀.subtype
  have hHle : H ≤ H₀ := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hH : H ≠ ⊤ := fun h => hsig.proper (top_le_iff.1 (h ▸ hHle))
  let e₁ : ↥Kpre ≃* ↥H := Kpre.equivMapOfInjective H₀.subtype H₀.subtype_injective
  let q : ↥Kpre →* ↥K := (π.comp Kpre.subtype).codRestrict K fun k => k.2
  have hq' : Function.Surjective q := by
    intro k
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective H₁ (k : Sec H₀ H₁)
    exact ⟨⟨c, show π c ∈ K by rw [hc]; exact k.2⟩, Subtype.ext hc⟩
  let f : ↥H →* ↥K ⧸ center ↥K := ((QuotientGroup.mk' (center ↥K)).comp q).comp e₁.symm.toMonoidHom
  have hf : Function.Surjective f :=
    ((QuotientGroup.mk'_surjective _).comp hq').comp e₁.symm.surjective
  exact Generic.ghList_of_surjection hctx.std.kgh hH f hf hq.2.1 hq.2.2

theorem prop4_2_of_cells (hAlt : Cell87 FAlt) (hSpor : Cell87 FSpor) (hMcLy : Cell87 FMcLy)
    (hTwo : Cell87 FTwo) (hL2 : Cell87 FL2) (hL3 : Cell87 FL3) (hU3 : Cell87 FU3)
    (hSp4 : Cell87 FSp4) (hG2 : Cell87 FG2) (hD4 : Cell87 FD4) (hL4 : Cell87 FL4)
    (hU4 : Cell87 FU4) (hL5 : Cell87 FL5) (hU5 : Cell87 FU5) (hRee : Cell87 FRee)
    (h41a : Prop4_1a) (h41b : Prop4_1b) : Prop4_2 := by
  intro G _ _ z k S hctx H₀ H₁ _ hz p X hsig hyp
  rcases ghList_cases (ghList_layerBar hctx hsig hyp) with h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h
  · exact hAlt h41a h41b G z k S hctx H₀ H₁ hz p X hsig hyp h
  · exact hSpor h41a h41b G z k S hctx H₀ H₁ hz p X hsig hyp h
  · exact hMcLy h41a h41b G z k S hctx H₀ H₁ hz p X hsig hyp h
  · exact hTwo h41a h41b G z k S hctx H₀ H₁ hz p X hsig hyp h
  · exact hL2 h41a h41b G z k S hctx H₀ H₁ hz p X hsig hyp h
  · exact hL3 h41a h41b G z k S hctx H₀ H₁ hz p X hsig hyp h
  · exact hU3 h41a h41b G z k S hctx H₀ H₁ hz p X hsig hyp h
  · exact hSp4 h41a h41b G z k S hctx H₀ H₁ hz p X hsig hyp h
  · exact hG2 h41a h41b G z k S hctx H₀ H₁ hz p X hsig hyp h
  · exact hD4 h41a h41b G z k S hctx H₀ H₁ hz p X hsig hyp h
  · exact hL4 h41a h41b G z k S hctx H₀ H₁ hz p X hsig hyp h
  · exact hU4 h41a h41b G z k S hctx H₀ H₁ hz p X hsig hyp h
  · exact hL5 h41a h41b G z k S hctx H₀ H₁ hz p X hsig hyp h
  · exact hU5 h41a h41b G z k S hctx H₀ H₁ hz p X hsig hyp h
  · exact hRee h41a h41b G z k S hctx H₀ H₁ hz p X hsig hyp h

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
