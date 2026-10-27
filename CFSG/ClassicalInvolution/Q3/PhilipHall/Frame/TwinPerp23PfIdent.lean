module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Mem
public import CFSG.ClassicalInvolution.Q3.Q3T7SectA

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL



@[expose] def LieTypeOf {X : Type} [Group X] {Z : Set (Subgroup X)} (D : OmegaLieU 3 1 Z) (d : ℕ)
    (ε : Bool) : Prop :=
  ∀ h : D.card = 1, ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsOrthTag d ε t n ∧
    CompIs 3 1 (D.kind ⟨0, by omega⟩) t n

theorem LieOneComp.of_card_type {X : Type} [Group X] {Z : Set (Subgroup X)} {D : OmegaLieU 3 1 Z}
    {d : ℕ} {ε : Bool} (hc : D.card = 1) (ht : LieTypeOf D d ε) : LieOneComp D d ε :=
  ⟨hc, ht hc⟩

section Card

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem secDecomp_card_one (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h : PerpHypS n Y R S t) {c : Y} (hc : c * c = 1) (hc1 : c ≠ 1)
    (hne : (TwinDisc.secFam (Om R) c).Nonempty) (hno : SecNoExit R c)
    (htr : ∀ K ∈ TwinDisc.secFam (Om R) c, ∀ L ∈ TwinDisc.secFam (Om R) c,
      ∃ g : SecQ R c, conjSub g K = L)
    (D : OmegaLieU 3 1 (liftFam (TwinDisc.secFam (Om R) c))) : D.card = 1 := by
  have hS := p23_q8Section h hc
  obtain ⟨-, hl, -, -⟩ := lieDecomp_of_noExit hcit hP (secQ_card_lt h hc1) hS hne hno
  have hΦ : HypOmegaModU (.sl2 3 1) (liftFam (TwinDisc.secFam (Om R) c)) :=
    hypOmegaModU_liftFam hS.hyp.conjInvariant
  have hgen : omegaGen (liftFam (TwinDisc.secFam (Om R) c)) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hS.gen]
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨L, u, hL⟩ := hl J hJ
    exact hL.le_sat.trans (le_omegaGen (satU_mem_liftFam hJ hL))
  obtain ⟨K₀, hK₀⟩ := hne
  obtain ⟨L₀, u₀, hL₀⟩ := hl K₀ hK₀
  have hM₀ := satU_mem_liftFam hK₀ hL₀
  have ht := liftFam_trans hS.hyp hM₀ hL₀.le_sat (fun J' hJ' => htr K₀ hK₀ J' hJ')
  have htrans : ∀ K ∈ liftFam (TwinDisc.secFam (Om R) c), ∀ L ∈ liftFam (TwinDisc.secFam (Om R) c),
      ∃ g : SecQ R c, conjSub g K = L := by
    intro K hK L hL
    obtain ⟨g₁, h₁⟩ := ht K hK
    obtain ⟨g₂, h₂⟩ := ht L hL
    exact ⟨g₂ * g₁⁻¹, by rw [conjSub_mul, ← h₁, conjSub_inv_conjSub, h₂]⟩
  exact Q3T7.card_eq_one_of_transitive3 D hΦ hgen htrans ⟨_, hM₀⟩

end Card

section Steps

@[expose] def P23E4Trans (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → SecNoExit R e →
      ∀ K ∈ TwinDisc.secFam (Om R) e, ∀ L ∈ TwinDisc.secFam (Om R) e,
        ∃ x : SecQ R e, conjSub x K = L

@[expose] def P23E4Type (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → SecNoExit R e →
      ∀ D : OmegaLieU 3 1 (liftFam (TwinDisc.secFam (Om R) e)), LieTypeOf D 6 (piSign 3 1)

@[expose] def P23Y5Trans (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → SecNoExit R u →
      ∀ K ∈ TwinDisc.secFam (Om R) u, ∀ L ∈ TwinDisc.secFam (Om R) u,
        ∃ x : SecQ R u, conjSub x K = L

@[expose] def P23Y5Type (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → SecNoExit R u →
      ∀ D : OmegaLieU 3 1 (liftFam (TwinDisc.secFam (Om R) u)),
        LieTypeOf D 5 true ∨ LieTypeOf D 6 (!piSign 3 1)

theorem p23E4Ident_of_trans_type {n : ℕ} (htr : P23E4Trans n) (hty : P23E4Type n) :
    P23E4Ident n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno D
  have hne := (p23Members n Y R S t K' W u e g hc).1
  have hcard := secDecomp_card_one hcit hP hc.std.perp hc.data.he2 hc.data.he1 hne hno
    (htr hcit hP Y R S t K' W u e g hc hno) D
  exact LieOneComp.of_card_type hcard (hty hcit hP Y R S t K' W u e g hc hno D)

theorem p23Y5Ident_of_trans_type {n : ℕ} (htr : P23Y5Trans n) (hty : P23Y5Type n) :
    P23Y5Ident n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno D
  have hne := (p23Members n Y R S t K' W u e g hc).2
  have hcard := secDecomp_card_one hcit hP hc.std.perp hc.data.hu2 hc.data.hu1 hne hno
    (htr hcit hP Y R S t K' W u e g hc hno) D
  rcases hty hcit hP Y R S t K' W u e g hc hno D with h | h
  · exact Or.inl (LieOneComp.of_card_type hcard h)
  · exact Or.inr (LieOneComp.of_card_type hcard h)

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
