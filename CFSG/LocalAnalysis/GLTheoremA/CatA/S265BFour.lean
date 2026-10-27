module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def tyUnHigh : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA r q => 4 ≤ r ∧ r ≤ 8 ∧ q.card = 2 | _ => False

@[expose] def QUFamBHigh : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x b : Ω), QUNL p S B T x b →
    p = 3 → catalogIs (PSimple p (Ipart p S b)) tyUnHigh → QUConcl p S B x b

@[expose] def QSFamBHigh : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω),
    QSNL p S B T x D K → p = 3 → catalogIs (PSimple p K) tyUnHigh → QSConcl p S B D K

theorem tyUn_four_or_high {i : TauCeti.CFSGIndex} (h : tyUn i) :
    S9.isU4two i ∨ tyUnHigh i := by
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      obtain ⟨h3, h8, h2⟩ : 3 ≤ r ∧ r ≤ 8 ∧ q.card = 2 := h
      rcases Nat.lt_or_ge r 4 with hr | hr
      · obtain rfl : r = 3 := by omega
        exact Or.inl h2
      · exact Or.inr ⟨hr, h8, h2⟩
    | _ => exact h.elim
  | _ => exact h.elim

section Pumpup


theorem quFour_pumpup {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x b : Ω}
    (h : QUNL 3 S B T x b) (hJT : catalogIs (PSimple 3 (Ipart 3 S b)) S9.isU4two) :
    ∃ hbN : b ∈ Subgroup.normalizer (S : Set Ω),
      I1431C2.U42Pumpup (PSimple 3 S) (chevAut 3 S ⟨b, hbN⟩) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hbN : b ∈ Subgroup.normalizer (S : Set Ω) := by
    rw [Subgroup.normalizer_eq_top_iff.2 h.cfg.normal]
    exact Subgroup.mem_top b
  have hb3 : b ^ 3 = 1 := h.cfg.elem.2 b h.cfg.hb
  have hbp := CFSG.LocalAnalysis.GLTheoremA.isPGroup_zpowers_of_pow_eq_one hb3
  have hJ := (FR.i91CompAt_holds (G := Ω) hp (by norm_num) ⊤ S b h.cfg.comp h.cfg.chev hb3
    h.cfg.prop h.cfg.ipart).1
  obtain ⟨e⟩ := nonempty_pSimple_equiv_chevTransfer hp hbN hbp hJ
  obtain ⟨i, hi, ⟨f⟩⟩ := hJT
  exact ⟨hbN, chevAut_pow_eq_one 3 S hbN hb3, fun h1 => h.cfg.hbx
    ((h.cfg.centB b h.cfg.hb).1 ((chevAut_eq_one_iff hp h.cfg.comp hbN).1 h1)), _,
    glaPComponent_chevTransfer hp hbN hbp hJ, i, hi, ⟨e.symm.trans f⟩⟩

end Pumpup

end CFSG.LocalAnalysis.GLTheoremA.S265

end
