module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 Matrix

private theorem kd26h_dec_isLnEps_cases {S : Type} [Group S] {n q : ℕ} {lin : Bool}
    (h : IsLnEps S n q lin) :
    ∃ (d : TauCeti.LieTypeIndex) (hv : d.Valid), isLnEps n q lin d ∧
      Nonempty (S ≃* TauCeti.ValidLieTypeIndex.Group ⟨d, hv⟩) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => simp [onLie] at hi
  | alternating _ _ => simp [onLie] at hi
  | sporadic _ => simp [onLie] at hi
  | lie idx => exact ⟨idx.1, idx.2, hi, ⟨e⟩⟩

theorem exists_psl_of_isLnEps {S : Type} [Group S] {n q : ℕ} (h : IsLnEps S n q true) :
    ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Finite F), m + 1 = n ∧ Nat.card F = q ∧
      Nonempty (S ≃* ProjectiveSpecialLinearGroup (Fin (m + 1)) F) := by
  obtain ⟨d, hv, hd, ⟨e⟩⟩ := kd26h_dec_isLnEps_cases h
  cases d <;> simp only [isLnEps] at hd
  rename_i r qq
  obtain ⟨hr, hqq⟩ := hd
  haveI : Fact qq.p.Prime := ⟨qq.prime_p⟩
  refine ⟨r, GaloisField qq.p qq.exponent, inferInstance, inferInstance, hr, ?_,
    ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r qq hv)⟩⟩
  rw [GaloisField.card qq.p qq.exponent (ne_of_gt qq.exponent_pos), ← hqq,
    TauCeti.PrimePower.card_def]

theorem exists_psu_of_isLnEps {S : Type} [Group S] {n q : ℕ} (h : IsLnEps S n q false) :
    ∃ (m ℓ f : ℕ) (F : Type) (_ : Field F),
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f F ∧ m + 1 = n ∧ ℓ ^ f = q ∧
        (m = 2 → 3 ≤ q) ∧ Nonempty (S ≃* StatedProj (StatedSU (m + 1) (ℓ ^ f) F)) := by
  obtain ⟨d, hv, hd, ⟨e⟩⟩ := kd26h_dec_isLnEps_cases h
  cases d <;> simp only [isLnEps] at hd
  rename_i r qq
  obtain ⟨hr, hqq⟩ := hd
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r qq, hv⟩ = qq.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA r qq
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r qq, hv⟩ = qq.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA r qq
  have hpow : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r qq, hv⟩ ^
      TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r qq, hv⟩ = q := by
    rw [hc, hf, ← hqq, TauCeti.PrimePower.card_def]
  have hfpos := TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA r qq, hv⟩
  haveI : Fact (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r qq, hv⟩).Prime :=
    ⟨TauCeti.ValidLieTypeIndex.characteristic_prime _⟩
  refine ⟨r, TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r qq, hv⟩,
    TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r qq, hv⟩,
    GaloisField (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r qq, hv⟩)
      (2 * TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r qq, hv⟩), inferInstance,
    ⟨TauCeti.ValidLieTypeIndex.characteristic_prime _,
      TauCeti.ValidLieTypeIndex.fieldExponent_pos _, ?_⟩, hr, hpow, ?_,
    ⟨e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r qq hv)⟩⟩
  · exact GaloisField.card _ _ (by omega)
  · intro hr2
    rw [← hqq]
    exact hrange.2 hr2

end CFSG.LocalAnalysis.GLTheoremA
