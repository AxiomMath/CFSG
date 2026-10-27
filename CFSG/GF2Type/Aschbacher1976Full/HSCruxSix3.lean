module

public import CFSG.GF2Type.Aschbacher1976Full.HSCruxSix2

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.CruxSix

@[expose] def goodSets2 : List (List ℕ) :=
  [[181889],
   [181889, 181840, 181770],
   [181889, 180888, 180363],
   [181889, 169632, 165516],
   [181889, 50856, 18061]]

@[expose] def goodSets4 : List (List ℕ) :=
  [[181441],
   [181441, 105120, 67404],
   [181441, 169184, 165068],
   [181441, 71520, 101004],
   [181441, 47272, 9997],
   [181441, 50408, 17613],
   [181441, 42792, 14477],
   [181441, 178305, 173825],
   [181441, 117377, 83777],
   [181441, 178256, 172299, 169506, 164508],
   [181441, 117328, 82251, 50730, 17053],
   [181441, 172824, 178186, 168099, 165460],
   [181441, 82776, 117258, 49323, 18005],
   [181441, 105120, 67404, 169184, 165068, 71520, 117377, 101004, 83777],
   [181441, 47272, 9997, 50408, 17613, 42792, 178305, 14477, 173825]]

@[expose] def goodSets6 : List (List ℕ) :=
  [[152769],
   [152769, 104994, 8989],
   [152769, 47146, 66396],
   [152769, 69987, 14421],
   [152769, 41259, 100948]]

theorem cert2 : Cert 181889 goodSets2 := by decide +kernel

theorem cert4 : Cert 181441 goodSets4 := by decide +kernel

theorem cert6 : Cert 152769 goodSets6 := by decide +kernel

@[expose] def goodSetsAll : List (List ℕ) := goodSets2 ++ goodSets4 ++ goodSets6

theorem mem_goodSetsAll_of_mem {S : List ℕ}
    (h : S ∈ goodSets2 ∨ S ∈ goodSets4 ∨ S ∈ goodSets6) : S ∈ goodSetsAll := by
  simp only [goodSetsAll, List.mem_append]
  rcases h with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem canon_check : ∀ x ∈ invsN, x ≠ oneN →
    ∃ σ ∈ allN, ∃ a ∈ [181889, 181441, 152769], a ∈ allN ∧ mulN σ x = mulN a σ := by
  decide +kernel

@[expose] def nineN : List ℕ :=
  [178305, 117377, 153217, 178186, 117258, 153098, 178256, 117328, 153168]

@[expose] def CentN (S : List ℕ) (y : ℕ) : Prop := ∀ t ∈ S, mulN y t = mulN t y

@[expose] def NrmN (S : List ℕ) : List ℕ :=
  invsN.filter (fun y => decide (∀ t ∈ S, cjN y t ∈ S))

@[expose] def NoYN (S : List ℕ) : Prop :=
  ∀ y₁ ∈ NrmN S, ∀ y₂ ∈ NrmN S, y₁ ≠ y₂ → mulN y₁ y₂ = mulN y₂ y₁ →
    CentN S y₁ ∨ CentN S y₂ ∨ CentN S (mulN y₁ y₂)

@[expose] def NineN (S : List ℕ) : Prop :=
  ∃ σ ∈ allN, (∀ t ∈ S, ∃ u ∈ nineN, mulN σ t = mulN u σ) ∧
    ∀ u ∈ nineN, ∃ t ∈ S, mulN σ t = mulN u σ

@[expose] def GoodS (S : List ℕ) : Prop :=
  S.Nodup ∧ (S.length = 1 ∨ ((S.length = 3 ∨ S.length = 5) ∧ NoYN S) ∨ (S.length = 9 ∧ NineN S))

instance (S : List ℕ) (y : ℕ) : Decidable (CentN S y) := inferInstanceAs (Decidable (∀ _ ∈ _, _))
instance (S : List ℕ) : Decidable (NoYN S) := inferInstanceAs (Decidable (∀ _ ∈ _, _))
instance (S : List ℕ) : Decidable (NineN S) := inferInstanceAs (Decidable (∃ _ ∈ _, _))
instance (S : List ℕ) : Decidable (GoodS S) := inferInstanceAs (Decidable (_ ∧ _))

theorem goodS_goodSets2 : ∀ S ∈ goodSets2, GoodS S := by decide +kernel

theorem goodS_goodSets4 : ∀ S ∈ goodSets4, GoodS S := by decide +kernel

theorem goodS_goodSets6 : ∀ S ∈ goodSets6, GoodS S := by decide +kernel

theorem goodS_all : ∀ S ∈ goodSetsAll, GoodS S := by
  intro S hS
  simp only [goodSetsAll, List.mem_append] at hS
  rcases hS with (h | h) | h
  · exact goodS_goodSets2 S h
  · exact goodS_goodSets4 S h
  · exact goodS_goodSets6 S h

end CFSG.GF2Type.Aschbacher1976Full.HS.CruxSix
