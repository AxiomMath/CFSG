module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCatalogDihedral
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSSMathieuJankoExclusion
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Blueprint Blueprint.NativeSporadic

@[expose] def FourSporadicQuaternionEight : Prop :=
  ∀ (T : Type) [Group T] [Finite T],
    (IsSporadic T .J2 ∨ IsSporadic T .J3 ∨ IsSporadic T .McL ∨ IsSporadic T .He) →
      ∃ R : Subgroup T, Nonempty (R ≃* QuaternionGroup 2)

@[expose] def SixBinarySporadicDihedralExclusion : Prop :=
  ∀ (T : Type) [Group T] [Finite T],
    (IsSporadic T .Co1 ∨ IsSporadic T .Co2 ∨ IsSporadic T .Co3 ∨ IsSporadic T .HS ∨
        IsSporadic T .Ru ∨ IsSporadic T .Th) →
      ∀ s : ℕ, 2 ≤ s →
        ∀ P : Sylow 2 T, ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1)))

@[expose] def EightPermutationSporadicDihedralExclusion : Prop :=
  ∀ (T : Type) [Group T] [Finite T],
    (IsSporadic T .M12 ∨ IsSporadic T .M22 ∨ IsSporadic T .M23 ∨ IsSporadic T .M24 ∨
        IsSporadic T .Fi22 ∨ IsSporadic T .Fi23 ∨ IsSporadic T .Fi24Prime ∨
        IsSporadic T .Suz) →
      ∀ s : ℕ, 2 ≤ s →
        ∀ P : Sylow 2 T, ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1)))

@[expose] def SixSporadicElementaryEight : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [Nontrivial T],
    (IsSporadic T .ONan ∨ IsSporadic T .Ly ∨ IsSporadic T .J4 ∨ IsSporadic T .HN ∨
        IsSporadic T .B ∨ IsSporadic T .M) →
      ∃ E : Subgroup T, IsElementaryAbelian 2 E ∧ Nat.card E = 8

theorem three_le_pRank_of_eight {X : Type*} [Group X] [Finite X] {E : Subgroup X}
    (hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = 8) : 3 ≤ pRank 2 X := by
  apply le_csSup
  · refine ⟨Nat.card X, ?_⟩
    rintro r ⟨B, -, hB⟩
    have h1 : r < 2 ^ r := Nat.lt_two_pow_self
    have h2 : Nat.card B ≤ Nat.card X := Subgroup.card_le_card_group B
    omega
  · exact ⟨E, hE, by rw [hcard]; norm_num⟩

theorem dihedral_sylow_sporadic_model_exclusion_of_inputs (hQ8 : FourSporadicQuaternionEight)
    (hBin : SixBinarySporadicDihedralExclusion)
    (hPerm : EightPermutationSporadicDihedralExclusion) (hE8 : SixSporadicElementaryEight)
    {T : Type} [Group T] [Finite T] [Nontrivial T] (hT : SporadicRep T) (s : ℕ) (hs : 2 ≤ s)
    (P : Sylow 2 T) : ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1))) := by
  intro hP
  obtain ⟨hrank, hQ⟩ := SmallLocal.dihedral_sylow_rank_and_quaternion_obstructions hs ⟨P, hP⟩
  have hq : ∀ {t : TauCeti.SporadicName}, IsSporadic T t →
      (IsSporadic T .J2 ∨ IsSporadic T .J3 ∨ IsSporadic T .McL ∨ IsSporadic T .He) → False :=
    fun _ h => hQ (hQ8 T h)
  have he : (IsSporadic T .ONan ∨ IsSporadic T .Ly ∨ IsSporadic T .J4 ∨ IsSporadic T .HN ∨
      IsSporadic T .B ∨ IsSporadic T .M) → False := fun h => by
    obtain ⟨E, hE, hcard⟩ := hE8 T h
    have := three_le_pRank_of_eight hE hcard
    omega
  obtain ⟨t, ht⟩ := hT
  have ht' : IsSporadic T t := ht
  cases t with
  | M11 =>
    obtain ⟨e⟩ := ht
    have e' : T ≃* CFSG.Open.StatedM11 :=
      e.trans (MulEquiv.subgroupCongr Semidihedral.GL2Recognition.statedM11_eq_nativeM11.symm)
    exact UnbalancedGS.dihedral_sylow_M11_J1_involution_count_exclusion
      (.inl ⟨e'⟩) s hs P hP
  | J1 =>
    exact UnbalancedGS.dihedral_sylow_M11_J1_involution_count_exclusion
      (.inr ht) s hs P hP
  | J2 => exact hq ht' (.inl ht')
  | J3 => exact hq ht' (.inr (.inl ht'))
  | McL => exact hq ht' (.inr (.inr (.inl ht')))
  | He => exact hq ht' (.inr (.inr (.inr ht')))
  | Co1 => exact hBin T (.inl ht') s hs P hP
  | Co2 => exact hBin T (.inr (.inl ht')) s hs P hP
  | Co3 => exact hBin T (.inr (.inr (.inl ht'))) s hs P hP
  | HS => exact hBin T (.inr (.inr (.inr (.inl ht')))) s hs P hP
  | Ru => exact hBin T (.inr (.inr (.inr (.inr (.inl ht'))))) s hs P hP
  | Th => exact hBin T (.inr (.inr (.inr (.inr (.inr ht'))))) s hs P hP
  | M12 => exact hPerm T (.inl ht') s hs P hP
  | M22 => exact hPerm T (.inr (.inl ht')) s hs P hP
  | M23 => exact hPerm T (.inr (.inr (.inl ht'))) s hs P hP
  | M24 => exact hPerm T (.inr (.inr (.inr (.inl ht')))) s hs P hP
  | Fi22 => exact hPerm T (.inr (.inr (.inr (.inr (.inl ht'))))) s hs P hP
  | Fi23 => exact hPerm T (.inr (.inr (.inr (.inr (.inr (.inl ht')))))) s hs P hP
  | Fi24Prime => exact hPerm T (.inr (.inr (.inr (.inr (.inr (.inr (.inl ht'))))))) s hs P hP
  | Suz => exact hPerm T (.inr (.inr (.inr (.inr (.inr (.inr (.inr ht'))))))) s hs P hP
  | ONan => exact he (.inl ht')
  | Ly => exact he (.inr (.inl ht'))
  | J4 => exact he (.inr (.inr (.inl ht')))
  | HN => exact he (.inr (.inr (.inr (.inl ht'))))
  | B => exact he (.inr (.inr (.inr (.inr (.inl ht')))))
  | M => exact he (.inr (.inr (.inr (.inr (.inr ht')))))

theorem dihedralSylowSporadicExclusion_of_inputs (hQ8 : FourSporadicQuaternionEight)
    (hBin : SixBinarySporadicDihedralExclusion)
    (hPerm : EightPermutationSporadicDihedralExclusion) (hE8 : SixSporadicElementaryEight) :
    DihedralSylowSporadicExclusion :=
  fun _ _ _ _ hT s hs P =>
    dihedral_sylow_sporadic_model_exclusion_of_inputs hQ8 hBin hPerm hE8 hT s hs P

end CFSG.ComponentClassification.UnbalancedCorr
