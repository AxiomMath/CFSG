module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265NL

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def tySp8 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .B 4 q => q.card = 2 | _ => False

@[expose] def tyOm10m : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedD 5 q => q.card = 2 | _ => False

@[expose] def tyAlt6 : TauCeti.CFSGIndex → Prop :=
  fun | .alternating 6 _ => True | _ => False

@[expose] def tyUn : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA r q => 3 ≤ r ∧ r ≤ 8 ∧ q.card = 2 | _ => False

@[expose] def tyA : TauCeti.CFSGIndex → Prop :=
  fun i => S9.isD4two i ∨ tyOm10m i ∨ S9.isSp6two i ∨ tySp8 i ∨ tyAlt6 i

@[expose] def tyC : TauCeti.CFSGIndex → Prop :=
  fun i => S9.isTD4two i ∨ S9.isF4two i ∨ S9.isTE6two i ∨ onLie (fun | .tits => True | _ => False) i ∨
    onLie (fun | .twistedA 2 q => q.card = 3 | _ => False) i

@[expose] def tyD : TauCeti.CFSGIndex → Prop :=
  onLie fun | .A 1 q => q.card = 8 | .twistedA 2 q => q.card = 8 | _ => False

@[expose] def tyE : TauCeti.CFSGIndex → Prop :=
  onLie fun | .suzuki 2 => True | .tits => True | _ => False

@[expose] def tyF (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .A r q => r + 1 = p ∧ q.p = 2 ∧ p ∣ q.card - 1
    | .twistedA r q => r + 1 = p ∧ q.p = 2 ∧ p ∣ q.card + 1
    | _ => False

structure QUNL (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x b : Ω) : Prop where
  cfg : QUCfg p S B T x b
  nl : ∀ e ∈ B, e ∉ Dgrp b x → GLAPLayer p (Ipart p S b ⊓ cx e) = ⊥

@[expose] def QUConcl (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B : Subgroup Ω) (x b : Ω) : Prop :=
  (∃ E : Subgroup Ω, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ Dgrp b x ≤ E ∧
      GLAPLayer p (S ⊓ cs E) ≠ ⊥) ∨
    (p = 3 ∧ catalogIs (PSimple 3 S) S9.isU4eight ∧ FieldOn 3 b S)

@[expose] def QUList : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x b : Ω), QUNL p S B T x b →
    (p = 3 ∧ (catalogIs (PSimple p (Ipart p S b)) tyA ∨ catalogIs (PSimple p (Ipart p S b)) tyUn ∨
        catalogIs (PSimple p (Ipart p S b)) tyC ∨ catalogIs (PSimple p (Ipart p S b)) tyD)) ∨
      (p = 5 ∧ catalogIs (PSimple p (Ipart p S b)) tyE) ∨ catalogIs (PSimple p (Ipart p S b)) (tyF p)

@[expose] def QUFamA : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x b : Ω), QUNL p S B T x b → p = 3 →
    catalogIs (PSimple p (Ipart p S b)) tyA → QUConcl p S B x b

@[expose] def QUFamB : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x b : Ω), QUNL p S B T x b → p = 3 →
    catalogIs (PSimple p (Ipart p S b)) tyUn → QUConcl p S B x b

@[expose] def QUFamC : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x b : Ω), QUNL p S B T x b → p = 3 →
    catalogIs (PSimple p (Ipart p S b)) tyC → QUConcl p S B x b

@[expose] def QUFamD : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x b : Ω), QUNL p S B T x b → p = 3 →
    catalogIs (PSimple p (Ipart p S b)) tyD → QUConcl p S B x b

@[expose] def QUFamE : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x b : Ω), QUNL p S B T x b → p = 5 →
    catalogIs (PSimple p (Ipart p S b)) tyE → QUConcl p S B x b

@[expose] def QUFamF3 : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x b : Ω), QUNL p S B T x b → p = 3 →
    catalogIs (PSimple p (Ipart p S b)) (tyF p) → QUConcl p S B x b

@[expose] def QUFamFhi : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x b : Ω), QUNL p S B T x b → p ≠ 3 →
    catalogIs (PSimple p (Ipart p S b)) (tyF p) → QUConcl p S B x b

theorem qFactUNL_of_families (hList : QUList) (hA : QUFamA) (hB : QUFamB) (hC : QUFamC) (hD : QUFamD)
    (hE : QUFamE) (hF3 : QUFamF3) (hFhi : QUFamFhi) : QFactUNL := by
  intro p Ω _ _ S B T x b cfg hnl
  have hN : QUNL p S B T x b := ⟨cfg, hnl⟩
  rcases hList p Ω S B T x b hN with ⟨rfl, h⟩ | ⟨rfl, h⟩ | h
  · rcases h with h | h | h | h
    · exact hA 3 Ω S B T x b hN rfl h
    · exact hB 3 Ω S B T x b hN rfl h
    · exact hC 3 Ω S B T x b hN rfl h
    · exact hD 3 Ω S B T x b hN rfl h
  · exact hE 5 Ω S B T x b hN rfl h
  · rcases eq_or_ne p 3 with rfl | hp3
    · exact hF3 3 Ω S B T x b hN rfl h
    · exact hFhi p Ω S B T x b hN hp3 h

structure QSNL (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω) : Prop where
  cfg : QSCfg p S B T x D K
  nl : ∀ e ∈ B, e ∉ D → GLAPLayer p (K ⊓ cx e) = ⊥

@[expose] def QSConcl (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B D K : Subgroup Ω) : Prop :=
  (∃ E : Subgroup Ω, IsE3 p B E ∧ D ≤ E ∧ GLAPLayer p (S ⊓ cs E) ≠ ⊥) ∨ (p = 3 ∧ SmallType 3 K)

@[expose] def QSList : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω), QSNL p S B T x D K →
    (p = 3 ∧ (catalogIs (PSimple p K) tyA ∨ catalogIs (PSimple p K) tyUn ∨ catalogIs (PSimple p K) tyC ∨
        catalogIs (PSimple p K) tyD)) ∨
      (p = 5 ∧ catalogIs (PSimple p K) tyE) ∨ catalogIs (PSimple p K) (tyF p)

@[expose] def QSFamA : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω), QSNL p S B T x D K → p = 3 →
    catalogIs (PSimple p K) tyA → QSConcl p S B D K

@[expose] def QSFamB : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω), QSNL p S B T x D K → p = 3 →
    catalogIs (PSimple p K) tyUn → QSConcl p S B D K

@[expose] def QSFamC : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω), QSNL p S B T x D K → p = 3 →
    catalogIs (PSimple p K) tyC → QSConcl p S B D K

@[expose] def QSFamD : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω), QSNL p S B T x D K → p = 3 →
    catalogIs (PSimple p K) tyD → QSConcl p S B D K

@[expose] def QSFamE : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω), QSNL p S B T x D K → p = 5 →
    catalogIs (PSimple p K) tyE → QSConcl p S B D K

@[expose] def QSFamF : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω), QSNL p S B T x D K →
    catalogIs (PSimple p K) (tyF p) → QSConcl p S B D K

theorem qFactSNL_of_families (hList : QSList) (hA : QSFamA) (hB : QSFamB) (hC : QSFamC) (hD : QSFamD)
    (hE : QSFamE) (hF : QSFamF) : QFactSNL := by
  intro p Ω _ _ S B T x D K cfg hnl
  have hN : QSNL p S B T x D K := ⟨cfg, hnl⟩
  rcases hList p Ω S B T x D K hN with ⟨rfl, h⟩ | ⟨rfl, h⟩ | h
  · rcases h with h | h | h | h
    · exact hA 3 Ω S B T x D K hN rfl h
    · exact hB 3 Ω S B T x D K hN rfl h
    · exact hC 3 Ω S B T x D K hN rfl h
    · exact hD 3 Ω S B T x D K hN rfl h
  · exact hE 5 Ω S B T x D K hN rfl h
  · exact hF p Ω S B T x D K hN h

end CFSG.LocalAnalysis.GLTheoremA.S265

end
