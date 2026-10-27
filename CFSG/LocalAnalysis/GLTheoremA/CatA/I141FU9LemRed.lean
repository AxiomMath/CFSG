module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def I141U9Fam (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (K J : Subgroup Γ) (x a : Γ),
    catalogIs (PSimple 3 K) Q → x ^ 3 = 1 → a ^ 3 = 1 → x * a = a * x → x ∉ Subgroup.zpowers a →
    S10.InnDiagOn 3 (Subgroup.zpowers x) K → S10.InnDiagOn 3 (Subgroup.zpowers a) K →
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set Γ)) J →
    catalogIs (PSimple 3 J) S9.isU3eight → Subgroup.center (PQuot 3 J) ≠ ⊥ → S10.FieldOn 3 a J →
    catalogIs (PSimple 3 K) isU9two

theorem catalogIs_true_iff {S : Type} [Group S] : catalogIs S (fun _ => True) ↔ IsCatalogGroup S := by
  constructor
  · rintro ⟨i, _, e⟩
    exact ⟨i, e⟩
  · rintro ⟨i, e⟩
    exact ⟨i, trivial, e⟩

theorem i141U9Lemma_iff_fam : I141U9Lemma ↔ I141U9Fam (fun _ => True) := by
  unfold I141U9Lemma I141U9Fam
  constructor
  · intro h Γ _ _ K J x a hQ hx ha hxa hxna hI1 hI2 hJ hJU hZ hF
    exact h Γ K J x a (catalogIs_true_iff.1 hQ) hx ha hxa hxna hI1 hI2 hJ hJU hZ hF
  · intro h Γ _ _ K J x a hC hx ha hxa hxna hI1 hI2 hJ hJU hZ hF
    exact h Γ K J x a (catalogIs_true_iff.2 hC) hx ha hxa hxna hI1 hI2 hJ hJU hZ hF

theorem i141U9Fam_mono {Q Q' : TauCeti.CFSGIndex → Prop} (hsub : ∀ i, Q i → Q' i)
    (h : I141U9Fam Q') : I141U9Fam Q := by
  unfold I141U9Fam at h ⊢
  intro Γ _ _ K J x a hQ hx ha hxa hxna hI1 hI2 hJ hJU hZ hF
  obtain ⟨i, hi, e⟩ := hQ
  exact h Γ K J x a ⟨i, hsub i hi, e⟩ hx ha hxa hxna hI1 hI2 hJ hJU hZ hF

theorem i141U9Fam_or {Q₁ Q₂ : TauCeti.CFSGIndex → Prop} (h₁ : I141U9Fam Q₁) (h₂ : I141U9Fam Q₂) :
    I141U9Fam (fun i => Q₁ i ∨ Q₂ i) := by
  unfold I141U9Fam at h₁ h₂ ⊢
  intro Γ _ _ K J x a hQ hx ha hxa hxna hI1 hI2 hJ hJU hZ hF
  obtain ⟨i, hi, e⟩ := hQ
  rcases hi with h | h
  · exact h₁ Γ K J x a ⟨i, h, e⟩ hx ha hxa hxna hI1 hI2 hJ hJU hZ hF
  · exact h₂ Γ K J x a ⟨i, h, e⟩ hx ha hxa hxna hI1 hI2 hJ hJU hZ hF

theorem i141U9Fam_isU9two : I141U9Fam isU9two := by
  unfold I141U9Fam
  intro Γ _ _ K J x a hQ _ _ _ _ _ _ _ _ _ _
  exact hQ

@[expose] def u9FamUnit : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA r q => ¬ (r = 8 ∧ q.card = 2) | _ => False

@[expose] def u9FamLin : TauCeti.CFSGIndex → Prop :=
  onLie fun | .A _ _ => True | _ => False

@[expose] def u9FamClass : TauCeti.CFSGIndex → Prop :=
  onLie fun | .B _ _ => True | .C _ _ => True | .D _ _ => True | .twistedD _ _ => True | _ => False

@[expose] def u9FamE6 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .E6 _ => True | .twistedE6 _ => True | _ => False

@[expose] def u9FamExc : TauCeti.CFSGIndex → Prop :=
  onLie fun | .E7 _ => True | .E8 _ => True | .F4 _ => True | .G2 _ => True | .trialityD4 _ => True | _ => False

@[expose] def u9FamSmall : TauCeti.CFSGIndex → Prop :=
  onLie fun | .suzuki _ => True | .reeG2 _ => True | .reeF4 _ => True | .tits => True | _ => False

@[expose] def u9FamAlt : TauCeti.CFSGIndex → Prop :=
  fun | .alternating _ _ => True | _ => False

@[expose] def u9FamSpor : TauCeti.CFSGIndex → Prop :=
  fun | .sporadic _ => True | _ => False

@[expose] def u9FamCyc : TauCeti.CFSGIndex → Prop :=
  fun | .cyclic _ _ => True | _ => False

theorem u9_cover (i : TauCeti.CFSGIndex) :
    isU9two i ∨ u9FamUnit i ∨ u9FamLin i ∨ u9FamClass i ∨ u9FamE6 i ∨ u9FamExc i ∨
      u9FamSmall i ∨ u9FamAlt i ∨ u9FamSpor i ∨ u9FamCyc i := by
  cases i with
  | cyclic p hp =>
    simp [isU9two, u9FamUnit, u9FamLin, u9FamClass, u9FamE6, u9FamExc, u9FamSmall, u9FamAlt, u9FamSpor,
      u9FamCyc, onLie]
  | alternating n hn =>
    simp [isU9two, u9FamUnit, u9FamLin, u9FamClass, u9FamE6, u9FamExc, u9FamSmall, u9FamAlt, u9FamSpor,
      u9FamCyc, onLie]
  | sporadic s =>
    simp [isU9two, u9FamUnit, u9FamLin, u9FamClass, u9FamE6, u9FamExc, u9FamSmall, u9FamAlt, u9FamSpor,
      u9FamCyc, onLie]
  | lie d =>
    obtain ⟨t, ht⟩ := d
    cases t with
    | twistedA r q =>
      by_cases h : r = 8 ∧ q.card = 2
      · obtain ⟨rfl, hq⟩ := h
        exact Or.inl hq
      · exact Or.inr (Or.inl h)
    | _ =>
      simp [isU9two, u9FamUnit, u9FamLin, u9FamClass, u9FamE6, u9FamExc, u9FamSmall, onLie]

theorem i141U9Lemma_of_gaps (hUnit : I141U9Fam u9FamUnit) (hLin : I141U9Fam u9FamLin)
    (hClass : I141U9Fam u9FamClass) (hE6 : I141U9Fam u9FamE6) (hExc : I141U9Fam u9FamExc)
    (hSmall : I141U9Fam u9FamSmall) (hAlt : I141U9Fam u9FamAlt) (hSpor : I141U9Fam u9FamSpor)
    (hCyc : I141U9Fam u9FamCyc) : I141U9Lemma := by
  rw [i141U9Lemma_iff_fam]
  have hall :=
    i141U9Fam_or i141U9Fam_isU9two
      (i141U9Fam_or hUnit
        (i141U9Fam_or hLin
          (i141U9Fam_or hClass
            (i141U9Fam_or hE6
              (i141U9Fam_or hExc
                (i141U9Fam_or hSmall (i141U9Fam_or hAlt (i141U9Fam_or hSpor hCyc))))))))
  exact i141U9Fam_mono (fun i _ => u9_cover i) hall

end CFSG.LocalAnalysis.GLTheoremA.I141F
