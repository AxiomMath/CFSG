module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwin

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

theorem admissible_of_localShapeT {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G} {a : ℕ}
    {tY : StatedLieTag} {nY : ℕ} (h : LocalShapeT p f a tY nY Ω x) (hD4 : tY ≠ .trialityD4) :
    IsFundTag tY ∧ StatedLieAdmissible tY nY p f := by
  obtain ⟨D, -, i₁, ht, hr, -⟩ := h
  have hexp : D.exp i₁ = f := by
    rcases D.exp_eq i₁ with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h
      exact absurd h hD4
  have key : ∀ (t : StatedLieTag) (n e : ℕ), t = tY → n = nY → e = f → IsFundTag t →
      StatedLieAdmissible t n p e → IsFundTag tY ∧ StatedLieAdmissible tY nY p f := by
    intro t n e ht hn he h1 h2
    subst ht hn he
    exact ⟨h1, h2⟩
  exact key _ _ _ ht hr hexp (D.isFundTag i₁) (D.admissible i₁)

@[expose] def MFTwin (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ (t : StatedLieTag) (n a : ℕ), IsFundTag t → t ≠ .G2 → t ≠ .trialityD4 →
    StatedLieAdmissible t n p f → ¬ (t = .PSL ∧ n = 2) → 2 ≤ a → ModelTwinClass p t n f a →
    ShapeTable a t n ∨ (t = .POmegaPlus ∧ n = 4 ∧ a ≤ 4)

@[expose] def MFTwinClassical (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ (t : StatedLieTag) (n a : ℕ),
    (t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) →
    StatedLieAdmissible t n p f → ¬ (t = .PSL ∧ n = 2) → 2 ≤ a → ModelTwinClass p t n f a →
    ShapeTable a t n ∨ (t = .POmegaPlus ∧ n = 4 ∧ a ≤ 4)

@[expose] def MFTwinExc (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ (t : StatedLieTag) (n a : ℕ),
    (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) →
    StatedLieAdmissible t n p f → 2 ≤ a → ¬ ModelTwinClass p t n f a

theorem mfTwin_of_parts (h1 : MFTwinClassical p f) (h2 : MFTwinExc p f) : MFTwin p f := by
  intro hp2 hq t n a hfund hG2 hD4 hadm hnA1 ha2 hmt
  by_cases hc : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨
      t = .POmegaMinus
  · exact h1 hp2 hq t n a hc hadm hnA1 ha2 hmt
  · exfalso
    have hexc : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 := by
      cases t <;> simp_all [IsFundTag]
    exact h2 hp2 hq t n a hexc hadm ha2 hmt

@[expose] def ShapeExoticSingle (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  ShapeExotic a t n ∧ a = 1 ∧ t ≠ .G2 ∧ t ≠ .trialityD4

@[expose] def ShapeExoticG2D4 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  ShapeExotic a t n ∧ (t = .G2 ∨ t = .trialityD4)

@[expose] def ShapeExoticD4 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  ShapeExotic a t n ∧ t = .POmegaPlus ∧ n = 4 ∧ 2 ≤ a ∧ a ≤ 4

theorem pieceExotic_of_residuals (hTw : MFTwin p f) (h1 : RowPiece p f ShapeExoticSingle)
    (h2 : RowPiece p f ShapeExoticG2D4) (h3 : RowPiece p f ShapeExoticD4) : PieceExotic p f := by
  intro a t n hex G _ _ _ hnab K z S hshape
  by_cases hG : t = .G2 ∨ t = .trialityD4
  · exact h2 a t n ⟨hex, hG⟩ G hnab K z S hshape
  · push Not at hG
    by_cases ha : a = 1
    · exact h1 a t n ⟨hex, ha, hG.1, hG.2⟩ G hnab K z S hshape
    · have ha2 : 2 ≤ a := by
        have := hex.1
        omega
      obtain ⟨hfund, hadm⟩ := admissible_of_localShapeT hshape hG.2
      have hmt := exotic_modelTwinClass S hex.2.1 hG.1 hG.2 hshape
      rcases hTw S.odd S.five t n a hfund hG.1 hG.2 hadm hex.2.1 ha2 hmt with
          htab | ⟨ht, hn, ha4⟩
      · exact absurd htab hex.2.2
      · subst ht hn
        exact h3 a .POmegaPlus 4 ⟨hex, rfl, rfl, ha2, ha4⟩ G hnab K z S hshape

@[expose] def ShapeSp6 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop := a = 1 ∧ t = .PSp ∧ n = 2

@[expose] def ShapeSingleOrth (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  a = 1 ∧ (t = .POmegaOdd ∨ t = .POmegaMinus ∨ (t = .POmegaPlus ∧ n ≠ 6))

@[expose] def ShapeSingleExc (a : ℕ) (t : StatedLieTag) (_n : ℕ) : Prop :=
  a = 1 ∧ (t = .F4 ∨ t = .E6 ∨ t = .E8 ∨ t = .twistedE6)

omit [Fact p.Prime] in
theorem shapeSingle_cases {a : ℕ} {t : StatedLieTag} {n : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p f) (h : ShapeExoticSingle a t n) :
    ShapeSp6 a t n ∨ ShapeSingleOrth a t n ∨ ShapeSingleExc a t n := by
  obtain ⟨⟨-, hnA, htab⟩, ha, hG2, hD4⟩ := h
  have hadm' := hadm.2.2
  subst ha
  cases t with
  | PSL =>
    exfalso
    have h2 : 2 ≤ n := hadm'.1
    have hn : n ≠ 2 := fun hn => hnA ⟨rfl, hn⟩
    apply htab
    by_cases h7 : 7 ≤ n
    · exact Or.inl ⟨rfl, rfl, h7⟩
    · by_cases h6 : n = 6
      · exact Or.inr (Or.inl ⟨rfl, rfl, h6⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by omega, by omega⟩))
  | PSU =>
    exfalso
    have h3 : 3 ≤ n := hadm'.1
    apply htab
    by_cases h7 : 7 ≤ n
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h7⟩)))
    · by_cases h6 : n = 6
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h6⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by omega, by omega⟩)))))
  | PSp =>
    have h2 : 2 ≤ n := hadm'.1
    by_cases hn2 : n = 2
    · exact Or.inl ⟨rfl, rfl, hn2⟩
    · exfalso
      apply htab
      by_cases h4 : 4 ≤ n
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h4⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨rfl, rfl, by omega⟩)))))))
  | POmegaOdd => exact Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)
  | POmegaMinus => exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩)
  | POmegaPlus =>
    by_cases h6 : n = 6
    · exfalso
      apply htab
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨rfl, rfl, h6⟩))))))))
    · exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr ⟨rfl, h6⟩)⟩)
  | G2 => exact absurd rfl hG2
  | F4 => exact Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)
  | E6 => exact Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl rfl)⟩)
  | E7 =>
    exfalso
    apply htab
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, rfl, hadm'⟩)))))))))
  | E8 => exact Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inl rfl))⟩)
  | twistedE6 => exact Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr rfl))⟩)
  | trialityD4 => exact absurd rfl hD4
  | twistedB2 | twistedG2 | twistedF4 | Tits => exact absurd hfund (by simp [IsFundTag])

theorem pieceExotic_of_parts (hTw : MFTwin p f) (hsp : RowPiece p f ShapeSp6)
    (hor : RowPiece p f ShapeSingleOrth) (hex : RowPiece p f ShapeSingleExc)
    (hg : RowPiece p f ShapeExoticG2D4) (hd : RowPiece p f ShapeExoticD4) : PieceExotic p f := by
  refine pieceExotic_of_residuals hTw ?_ hg hd
  intro a t n h G _ _ _ hnab K z S hshape
  obtain ⟨hfund, hadm⟩ := admissible_of_localShapeT hshape h.2.2.2
  rcases shapeSingle_cases hfund hadm h with h' | h' | h'
  · exact hsp a t n h' G hnab K z S hshape
  · exact hor a t n h' G hnab K z S hshape
  · exact hex a t n h' G hnab K z S hshape

theorem pieceExotic_of_modelFacts (h1 : MFTwinClassical p f) (h2 : MFTwinExc p f)
    (hsp : RowPiece p f ShapeSp6) (hor : RowPiece p f ShapeSingleOrth)
    (hex : RowPiece p f ShapeSingleExc) (hg : RowPiece p f ShapeExoticG2D4)
    (hd : RowPiece p f ShapeExoticD4) : PieceExotic p f :=
  pieceExotic_of_parts (mfTwin_of_parts h1 h2) hsp hor hex hg hd

structure ExoticPieces (p f : ℕ) [Fact p.Prime] : Prop where
  twinClassical : MFTwinClassical p f
  twinExc : MFTwinExc p f
  sp6 : RowPiece p f ShapeSp6
  orth : RowPiece p f ShapeSingleOrth
  exc : RowPiece p f ShapeSingleExc
  g2d4 : RowPiece p f ShapeExoticG2D4
  d4 : RowPiece p f ShapeExoticD4

theorem ExoticPieces.pieceExotic (h : ExoticPieces p f) : PieceExotic p f :=
  pieceExotic_of_modelFacts h.twinClassical h.twinExc h.sp6 h.orth h.exc h.g2d4 h.d4

end CFSG.ClassicalInvolution.RouteD.Exotic
