module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Interface
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.QuasithinUnique.SQTK

open CFSG.Assembly CFSG.Open.SQTKTauCeti TauCeti

@[expose] def IsUntwistedA (d : ValidLieTypeIndex) : Prop :=
  match d.1 with
  | .A _ _ => True
  | _ => False

@[expose] def IsListFree (d : ValidLieTypeIndex) : Prop :=
  match d.1 with
  | .G2 q | .trialityD4 q => q.p = 2
  | .suzuki _ | .reeF4 _ | .tits => True
  | _ => False

@[expose] def IsTypeCorB2 (d : ValidLieTypeIndex) : Prop :=
  match d.1 with
  | .B r _ => r = 2
  | .C _ _ => True
  | _ => False

@[expose] def IsTwistedA (d : ValidLieTypeIndex) : Prop :=
  match d.1 with
  | .twistedA _ _ => True
  | _ => False

@[expose] def IsResidue (d : ValidLieTypeIndex) : Prop :=
  match d.1 with
  | .B r _ => 3 ≤ r
  | .G2 q | .trialityD4 q => q.p ≠ 2
  | .D _ _ | .twistedD _ _ | .E6 _ | .E7 _ | .E8 _ | .F4 _ | .twistedE6 _ | .reeG2 _ => True
  | _ => False

theorem lieIndex_classes_cover (d : ValidLieTypeIndex) :
    IsUntwistedA d ∨ IsListFree d ∨ IsTypeCorB2 d ∨ IsTwistedA d ∨ IsResidue d := by
  obtain ⟨d, hd⟩ := d
  have hv := (LieTypeIndex.valid_iff d).1 hd
  cases d with
  | B r q =>
    have h2 : 2 ≤ r := by
      have := hv.1
      simp only [LieTypeIndex.inStandardRange_iff] at this
      exact this.1
    by_cases hr : r = 2
    · exact Or.inr (Or.inr (Or.inl hr))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (show 3 ≤ r by omega))))
  | G2 q =>
    by_cases hp : q.p = 2
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inr (Or.inr hp)))
  | trialityD4 q =>
    by_cases hp : q.p = 2
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inr (Or.inr hp)))
  | A r q => exact Or.inl trivial
  | twistedA r q => exact Or.inr (Or.inr (Or.inr (Or.inl trivial)))
  | C r q => exact Or.inr (Or.inr (Or.inl trivial))
  | D r q => exact Or.inr (Or.inr (Or.inr (Or.inr trivial)))
  | twistedD r q => exact Or.inr (Or.inr (Or.inr (Or.inr trivial)))
  | E6 q => exact Or.inr (Or.inr (Or.inr (Or.inr trivial)))
  | E7 q => exact Or.inr (Or.inr (Or.inr (Or.inr trivial)))
  | E8 q => exact Or.inr (Or.inr (Or.inr (Or.inr trivial)))
  | F4 q => exact Or.inr (Or.inr (Or.inr (Or.inr trivial)))
  | twistedE6 q => exact Or.inr (Or.inr (Or.inr (Or.inr trivial)))
  | suzuki m => exact Or.inr (Or.inl trivial)
  | reeG2 m => exact Or.inr (Or.inr (Or.inr (Or.inr trivial)))
  | reeF4 m => exact Or.inr (Or.inl trivial)
  | tits => exact Or.inr (Or.inl trivial)

theorem lieIndex_classes_disjoint (d : ValidLieTypeIndex) :
    ¬ (IsUntwistedA d ∧ IsListFree d) ∧ ¬ (IsUntwistedA d ∧ IsTypeCorB2 d) ∧
    ¬ (IsUntwistedA d ∧ IsTwistedA d) ∧ ¬ (IsUntwistedA d ∧ IsResidue d) ∧
    ¬ (IsListFree d ∧ IsTypeCorB2 d) ∧ ¬ (IsListFree d ∧ IsTwistedA d) ∧
    ¬ (IsListFree d ∧ IsResidue d) ∧ ¬ (IsTypeCorB2 d ∧ IsTwistedA d) ∧
    ¬ (IsTypeCorB2 d ∧ IsResidue d) ∧ ¬ (IsTwistedA d ∧ IsResidue d) := by
  obtain ⟨d, hd⟩ := d
  cases d
  case B r q =>
    simp [IsUntwistedA, IsListFree, IsTypeCorB2, IsTwistedA, IsResidue]
    omega
  all_goals simp [IsUntwistedA, IsListFree, IsTypeCorB2, IsTwistedA, IsResidue]

theorem tcLieCase_typeCorB2_of_families
    (hB2 : ∀ (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid), TCLieCase ⟨.B 2 q, hv⟩)
    (hC : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.C r q).Valid),
      TCLieCase ⟨.C r q, hv⟩) :
    ∀ d, IsTypeCorB2 d → TCLieCase d := by
  rintro ⟨d, hv⟩ hd
  cases d with
  | B r q =>
    obtain rfl : r = 2 := hd
    exact hB2 q hv
  | C r q => exact hC r q hv
  | _ => exact hd.elim

theorem tcLieCase_twistedA_of_families
    (h : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedA r q).Valid),
      TCLieCase ⟨.twistedA r q, hv⟩) :
    ∀ d, IsTwistedA d → TCLieCase d := by
  rintro ⟨d, hv⟩ hd
  cases d with
  | twistedA r q => exact h r q hv
  | _ => exact hd.elim

theorem tcLieCase_residue_of_families
    (hB : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid), 3 ≤ r →
      TCLieCase ⟨.B r q, hv⟩)
    (hD : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid),
      TCLieCase ⟨.D r q, hv⟩)
    (hTwD : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedD r q).Valid),
      TCLieCase ⟨.twistedD r q, hv⟩)
    (hE6 : ∀ (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid), TCLieCase ⟨.E6 q, hv⟩)
    (hE7 : ∀ (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid), TCLieCase ⟨.E7 q, hv⟩)
    (hE8 : ∀ (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid), TCLieCase ⟨.E8 q, hv⟩)
    (hF4 : ∀ (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid), TCLieCase ⟨.F4 q, hv⟩)
    (hG2 : ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.p ≠ 2 →
      TCLieCase ⟨.G2 q, hv⟩)
    (hD4 : ∀ (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid), q.p ≠ 2 →
      TCLieCase ⟨.trialityD4 q, hv⟩)
    (hTwE6 : ∀ (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid),
      TCLieCase ⟨.twistedE6 q, hv⟩)
    (hRee : ∀ (m : ℕ) (hv : (LieTypeIndex.reeG2 m).Valid), TCLieCase ⟨.reeG2 m, hv⟩) :
    ∀ d, IsResidue d → TCLieCase d := by
  rintro ⟨d, hv⟩ hd
  cases d with
  | B r q => exact hB r q hv hd
  | D r q => exact hD r q hv
  | twistedD r q => exact hTwD r q hv
  | E6 q => exact hE6 q hv
  | E7 q => exact hE7 q hv
  | E8 q => exact hE8 q hv
  | F4 q => exact hF4 q hv
  | G2 q => exact hG2 q hv hd
  | trialityD4 q => exact hD4 q hv hd
  | twistedE6 q => exact hTwE6 q hv
  | reeG2 m => exact hRee m hv
  | _ => exact hd.elim

theorem inCatalog_of_kGroup {G : Type} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KGroup G) : InCatalog G :=
  KCore.KGroupNonab.catalogue_self CFSG.Assembly.inCatalog_isoInvariant hK hnonab

theorem not_stronglyQuasithin_of_elemAbelian {G H : Type} [Group G] [Finite G] [Group H]
    (e : G ≃* H) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {E : Subgroup H}
    (hE : CFSG.Open.IsElemAbelian ℓ E) (hcard : Nat.card E = ℓ ^ 3) :
    ¬ StronglyQuasithin G := by
  intro hS
  have : Finite H := Finite.of_equiv G e.toEquiv
  have h1 : 3 ≤ CFSG.Open.pRank ℓ (⊤ : Subgroup H) :=
    CFSG.SectionRank.le_pRank hℓ.one_lt le_top hE hcard
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hℓ.one_lt e] at h1
  have h2 : CFSG.Open.pRank ℓ (⊤ : Subgroup G) ≤ 2 := hS ℓ hℓ hℓ2
  omega

end CFSG.QuasithinUnique.SQTK
