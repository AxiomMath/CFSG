module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiTwoSylowFinkelstein
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Open
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSONModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic Cover CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
  CFSG.ComponentClassification.PerfectAutomorphisms

theorem outTwo_of_quotient {X : Type} [Group X] (hX : Group.IsPerfect X)
    (h : OutTwo (X ⧸ center X)) : OutTwo X := by
  have := hX
  have inner : ∀ γ : MulAut X, (∃ y : X ⧸ center X, centerQuotientHom X γ = MulAut.conj y) →
      ∃ g : X, γ = MulAut.conj g := by
    rintro γ ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨g, centerQuotientHom_injective X ?_⟩
    rw [hy, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj]
    rfl
  intro α β
  rcases h (centerQuotientHom X α) (centerQuotientHom X β) with h1 | h1 | h1
  · exact Or.inl (inner α h1)
  · exact Or.inr (Or.inl (inner β h1))
  · refine Or.inr (Or.inr ?_)
    obtain ⟨y, hy⟩ := h1
    have : centerQuotientHom X (α⁻¹ * β) = MulAut.conj y := by
      rw [map_mul, map_inv]
      exact hy
    exact inner _ ⟨y, this⟩

theorem IsLS.isoInv (S : List TauCeti.SporadicName) : GroupClass.IsoInv (IsLS S) := by
  intro X Y _ _ e ⟨s, hs, hq, hodd, hY⟩
  have hc : (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y := Subgroup.map_center_eq e
  refine ⟨s, hs, CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_, ?_⟩
  · rw [← hc, Subgroup.card_map_of_injective e.injective]
    exact hodd
  · obtain ⟨f⟩ := hY
    exact ⟨(QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e hc).symm.trans f⟩

theorem center_eq_oddCore_of_even {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (hodd : Odd (Nat.card (center X))) (heven : Even (Nat.card (X ⧸ center X))) :
    center X = CFSG.oddCore X := by
  have hs : IsSimpleGroup (X ⧸ center X) := hq.2.1
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, hodd⟩
  · refine sSup_le ?_
    rintro N ⟨hN, hNodd⟩
    have hmapN : (N.map (QuotientGroup.mk' (center X))).Normal :=
      hN.map _ (QuotientGroup.mk'_surjective _)
    have := hmapN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (center X))) with
      h | h
    · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact h
    · exfalso
      have h1 : Nat.card (⊤ : Subgroup (X ⧸ center X)) ∣ Nat.card N := by
        rw [← h]
        exact Subgroup.card_map_dvd _ _
      rw [Subgroup.card_top] at h1
      exact (Nat.not_even_iff_odd.2 (hNodd.of_dvd_nat h1)) heven

theorem twoSylowStd_of_lemma25 {s : TauCeti.SporadicName}
    (h25 : CFSG.EvenSporadicStandard.Finkelstein77.Asc76Lemma25)
    (hr : ∀ (X : Type) [Group X], IsLS [s] X → 3 ≤ CFSG.pRank 2 X)
    (hI : ∀ (Y : Type) [Group Y], IsSporadic Y s → HypothesisOne Y) : TwoSylowStd [s] := by
  intro s' hs' H _ _ N M hN hidx hkp hcov hstd hcyc P
  rcases List.mem_singleton.1 hs' with rfl
  obtain ⟨t, ht2, hcomp⟩ := hstd.2
  have htC : t ∈ centralizer (M : Set H) := by
    rw [mem_centralizer_iff]
    intro x hx
    exact mem_centralizer_singleton_iff.1 (hcomp.1 hx)
  exact card_sylow_eq_two_of_finkelstein_of_lemma25_of_pRank h25 hN hidx hstd hcov.1 hcov.2.1
    hcyc (hI _ hcov.2.2) (hr _ (isLS_iff.2 ⟨_, List.mem_singleton_self _, hcov⟩)) htC ht2 P

theorem mem_of_quotient_involution {H : Type} [Group H] {L K : Subgroup H} [Finite ↥L] {u : H}
    (hodd : Odd (Nat.card (center ↥L))) (hu : u ∈ L) (hu2 : orderOf u = 2)
    (h : q ↥L ⟨u, hu⟩ ∈ (K.subgroupOf L).map (q ↥L)) : u ∈ K := by
  have hu'2 : (⟨u, hu⟩ : ↥L) * ⟨u, hu⟩ = 1 := Subtype.ext (mul_self_eq_one_of_orderOf hu2)
  obtain ⟨k, hk, hk2, hkq⟩ := exists_involution_lift hodd h (by rw [← map_mul, hu'2, map_one])
  have hku : k = ⟨u, hu⟩ := Closing.eq_of_mk_eq_of_sq hodd hk2 hu'2 hkq
  have h1 := Subgroup.mem_subgroupOf.1 hk
  rwa [hku] at h1

@[expose] def IsOddCentralExt (D : Type) [Group D] : GroupClass := fun X _ =>
  CFSG.IsQuasisimple X ∧ ∃ π : X →* D, Function.Surjective π ∧ π.ker ≤ center X ∧
    Odd (Nat.card π.ker)

theorem IsOddCentralExt.isoInv (D : Type) [Group D] : GroupClass.IsoInv (IsOddCentralExt D) := by
  intro X Y _ _ e ⟨hq, π, hπs, hπc, hπo⟩
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq,
    π.comp e.symm.toMonoidHom, hπs.comp e.symm.surjective, ?_, ?_⟩
  · intro y hy
    have hy' : π (e.symm y) = 1 := MonoidHom.mem_ker.1 hy
    have h1 : e.symm y ∈ center X := hπc (MonoidHom.mem_ker.2 hy')
    have := (mem_center_iff_of_equiv e (e.symm y)).1 h1
    rwa [MulEquiv.apply_symm_apply] at this
  · have hker : (π.comp e.symm.toMonoidHom).ker = π.ker.map e.toMonoidHom := by
      ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_map]
      constructor
      · intro h
        exact ⟨e.symm y, MonoidHom.mem_ker.2 h, by simp⟩
      · rintro ⟨x, hx, rfl⟩
        show π (e.symm (e x)) = 1
        rw [MulEquiv.symm_apply_apply]
        exact MonoidHom.mem_ker.1 hx
    rw [hker, Subgroup.card_map_of_injective e.injective]
    exact hπo

theorem IsLS.center_eq_oddCore {S : List TauCeti.SporadicName}
    (hfe : ∀ s ∈ S, ∀ (Y : Type) [Group Y], IsSporadic Y s → Finite Y ∧ Even (Nat.card Y))
    {X : Type} [Group X] (hX : IsLS S X) : center X = CFSG.oddCore X := by
  obtain ⟨s, hs, hq, hodd, hY⟩ := hX
  obtain ⟨hfin, heven⟩ := hfe s hs _ hY
  have hZfin : Finite (center X) := Nat.finite_of_card_ne_zero (Nat.pos_of_ne_zero fun h => by
    rw [h] at hodd; exact absurd hodd (by decide)).ne'
  have hXfin : Finite X := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center X)
    refine Nat.finite_of_card_ne_zero ?_
    rw [h1]
    exact Nat.mul_ne_zero (Nat.card_pos (α := X ⧸ center X)).ne' (Nat.card_pos (α := center X)).ne'
  exact center_eq_oddCore_of_even hq hodd heven

structure RowAtlasFacts (S : List TauCeti.SporadicName)
    (Q : TauCeti.SporadicName → PairClass) (IsK : GroupClass) : Prop where
  pRank_K : ∀ (X : Type) [Group X], IsK X → 3 ≤ CFSG.pRank 2 X
  pRank_L : ∀ (X : Type) [Group X], IsLS S X → 3 ≤ CFSG.pRank 2 X
  rowExists : ∀ s ∈ S, ∀ (H : Type) [Group H] [Finite H] (L : Subgroup H), OddCover s L →
    ∃ (K : Subgroup H) (u : H), Q s H L K u
  rowFit : ∀ s ∈ S, ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H), OddCover s L → K ≤ L →
    CFSG.IsQuasisimple ↥K → IsK (↥K ⧸ CFSG.oddCore ↥K) → SolStd (K.subgroupOf L) →
      twoAdic (autCentralizer L K) ≤ 2 → ∃ u : H, Q s H L K u

def stage3Row_of_parts {S : List TauCeti.SporadicName} {Q : TauCeti.SporadicName → PairClass}
    {IsK : GroupClass} {m : TauCeti.SporadicName → ℕ} (hF : RowAtlasFacts S Q IsK)
    (hexc : ∀ (X : Type) [Group X], IsK X →
      ¬ Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin 7)) ∧
        ¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel (X ⧸ center X) .PSL 2 p f)
    (hneL : ∀ (X Y : Type) [Group X] [Group Y], IsLS S X → IsK (Y ⧸ CFSG.oddCore Y) →
      ¬ Nonempty ((X ⧸ center X) ≃* (Y ⧸ center Y)))
    (hinv : GroupClass.IsoInv IsK) (hKq : ∀ (X : Type) [Group X], IsK X → CFSG.IsQuasisimple X)
    (hfe : ∀ s ∈ S, ∀ (Y : Type) [Group Y], IsSporadic Y s → Finite Y ∧ Even (Nat.card Y))
    (hrec : ∀ s ∈ S, Rec36 S s (Q s) (m s)) (hout : OutTwoCovers S)
    (hrowIsK : ∀ s ∈ S, ∀ (H : Type) [Group H] (L K : Subgroup H) (u : H), OddCover s L →
      Q s H L K u → IsK ↥K)
    (hsyl : (∀ s ∈ S, ∀ (H : Type) [Group H] (L K : Subgroup H) (u : H), OddCover s L →
      Q s H L K u → u ∈ K) ∨ TwoSylowStd S) : Stage3Row S Q where
  IsK := IsK
  m := m
  rec36 := hrec
  outTwo := hout
  hyp31Row :=
    { isK_inv := hinv
      isL_inv := IsLS.isoInv S
      quasi_K := fun X _ hX => ⟨hKq X hX, hF.pRank_K X hX⟩
      quasi_L := fun X _ hX => ⟨(by obtain ⟨s, hs, hq, -⟩ := hX; exact hq),
        IsLS.center_eq_oddCore hfe hX, hF.pRank_L X hX⟩
      K_not_exc := hexc
      K_ne_L := hneL }
  rowIsK := hrowIsK
  rowExists := hF.rowExists
  rowFit := hF.rowFit
  inOrTwoSylow := hsyl

end CFSG.EvenSporadicStandard.Induction
