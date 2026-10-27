module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151ExcDefs
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint.Chevalley


private theorem shapeModelDiagAt_adjoint_of {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hG2 : τ = .G2 → 4 ≤ Nat.card K)
    (hE6 : τ = .E6 → p = 3 → ¬ 3 ∣ Nat.card K - 1)
    (hA : T171Sh.ExcAdjCompInnAut) (hD4 : ExcAdjD4Inner)
    (hL : CatLayer) (hC : CatChevComps) (hG : DiagOfCompAction)
    (hcat2 : catalogIs ↥(adjointGroup τ K) (onLie fun d => d.characteristic = 2)) :
    ShapeModelDiagAt ↥(adjointGroup τ K) p := by
  haveI : Finite (ModGL τ K) := CFSG.LieType.Chevalley.finite_modGL (τ := τ)
  haveI : Finite ↥(adjointGroup τ K) := Subtype.finite
  refine hG ↥(adjointGroup τ K) p hp hp2 ?_ ?_ ?_ ?_
  · intro x hx hxp
    exact hL ↥(adjointGroup τ K) p hp hp2 hcat2 x hx hxp
  · intro x hx hxp J hJ
    exact hC ↥(adjointGroup τ K) p hp hp2 hcat2 x hx hxp J hJ
  · intro x w hx hxp hwp hxw
    exact hA hτ K p hp hp2 hG2 hE6 x w hx hxp hwp hxw
  · intro x w hx hxp hwp hxw
    exact hD4 hτ K p hp hp2 hE6 x w hx hxp hwp hxw

private theorem four_le_card_of_g2 {q : TauCeti.PrimePower} {K : Type} [Field K]
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hq2 : q.p = 2)
    (hKcard : Nat.card K = q.card) :
    4 ≤ Nat.card K := by
  rw [hKcard, TauCeti.PrimePower.card_def, hq2]
  have h2 : 2 ≤ q.exponent := by
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hr
    rw [TauCeti.PrimePower.card_def, hq2] at hr
    by_contra h
    have h1 : q.exponent ≤ 1 := by omega
    have hle : 2 ^ q.exponent ≤ 2 := by
      simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h1
    omega
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h2

theorem excUDiag_of (hA : T171Sh.ExcAdjCompInnAut) (hD4 : ExcAdjD4Inner) (hL : CatLayer)
    (hC : CatChevComps) (hG : DiagOfCompAction) (hT : MarkTransport) (hI : ShapeModelDiagIso) :
    SimpleDiagModel (CharTwoOf KD264Lie.isExcUntwistedIdx) := by
  intro S _ _ p hp hp2 hcat hshape
  obtain ⟨i, hi, ⟨eS⟩⟩ := hcat
  cases i with
  | cyclic n r => exact absurd hi (by simp [onLie])
  | alternating n r => exact absurd hi (by simp [onLie])
  | sporadic s => exact absurd hi (by simp [onLie])
  | lie dd =>
    obtain ⟨idx, hv⟩ := dd
    obtain ⟨hPexc, hPchar⟩ := hi
    cases idx with
    | G2 q =>
      obtain ⟨K, hKf, hKfin, hKcard, hKchar, ⟨eAd⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
      letI := hKf
      letI := hKfin
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_G2]
        exact hPchar
      haveI : CharP K 2 := by rw [← hq2]; exact hKchar
      have hcat2 : catalogIs ↥(adjointGroup .G2 K) (onLie fun d => d.characteristic = 2) :=
        ⟨.lie ⟨.G2 q, hv⟩, hPchar, ⟨eAd.symm⟩⟩
      have hdiag := shapeModelDiagAt_adjoint_of (Or.inl rfl) K p hp hp2
        (fun _ => four_le_card_of_g2 hv hq2 hKcard) (fun h _ => absurd h (by decide)) hA hD4 hL hC
        hG hcat2
      haveI : Finite (ModGL .G2 K) := CFSG.LieType.Chevalley.finite_modGL (τ := .G2)
      haveI : Finite ↥(adjointGroup .G2 K) := Subtype.finite
      exact hI hT ↥(adjointGroup .G2 K) S (eAd.symm.trans eS.symm) p hdiag
    | F4 q =>
      obtain ⟨K, hKf, hKfin, hKcard, hKchar, ⟨eAd⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
      letI := hKf
      letI := hKfin
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_F4]
        exact hPchar
      haveI : CharP K 2 := by rw [← hq2]; exact hKchar
      have hcat2 : catalogIs ↥(adjointGroup .F4 K) (onLie fun d => d.characteristic = 2) :=
        ⟨.lie ⟨.F4 q, hv⟩, hPchar, ⟨eAd.symm⟩⟩
      have hdiag := shapeModelDiagAt_adjoint_of (Or.inr (Or.inl rfl)) K p hp hp2
        (fun h => absurd h (by decide)) (fun h _ => absurd h (by decide)) hA hD4 hL hC hG hcat2
      haveI : Finite (ModGL .F4 K) := CFSG.LieType.Chevalley.finite_modGL (τ := .F4)
      haveI : Finite ↥(adjointGroup .F4 K) := Subtype.finite
      exact hI hT ↥(adjointGroup .F4 K) S (eAd.symm.trans eS.symm) p hdiag
    | E6 q =>
      obtain ⟨K, hKf, hKfin, hKcard, hKchar, ⟨eAd⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
      letI := hKf
      letI := hKfin
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_E6]
        exact hPchar
      haveI : CharP K 2 := by rw [← hq2]; exact hKchar
      have hcat2 : catalogIs ↥(adjointGroup .E6 K) (onLie fun d => d.characteristic = 2) :=
        ⟨.lie ⟨.E6 q, hv⟩, hPchar, ⟨eAd.symm⟩⟩
      have hE6 : (.E6 : Tag) = .E6 → p = 3 → ¬ 3 ∣ Nat.card K - 1 := by
        intro _ hp3 h3
        rw [hKcard] at h3
        exact hshape ⟨.lie ⟨.E6 q, hv⟩, ⟨hp3, hq2, h3⟩, ⟨eS⟩⟩
      have hdiag := shapeModelDiagAt_adjoint_of (Or.inr (Or.inr (Or.inl rfl))) K p hp hp2
        (fun h => absurd h (by decide)) hE6 hA hD4 hL hC hG hcat2
      haveI : Finite (ModGL .E6 K) := CFSG.LieType.Chevalley.finite_modGL (τ := .E6)
      haveI : Finite ↥(adjointGroup .E6 K) := Subtype.finite
      exact hI hT ↥(adjointGroup .E6 K) S (eAd.symm.trans eS.symm) p hdiag
    | E7 q =>
      obtain ⟨K, hKf, hKfin, hKcard, hKchar, ⟨eAd⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
      letI := hKf
      letI := hKfin
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_E7]
        exact hPchar
      haveI : CharP K 2 := by rw [← hq2]; exact hKchar
      have hcat2 : catalogIs ↥(adjointGroup .E7 K) (onLie fun d => d.characteristic = 2) :=
        ⟨.lie ⟨.E7 q, hv⟩, hPchar, ⟨eAd.symm⟩⟩
      have hdiag := shapeModelDiagAt_adjoint_of (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) K p hp
        hp2 (fun h => absurd h (by decide)) (fun h _ => absurd h (by decide)) hA hD4 hL hC hG
        hcat2
      haveI : Finite (ModGL .E7 K) := CFSG.LieType.Chevalley.finite_modGL (τ := .E7)
      haveI : Finite ↥(adjointGroup .E7 K) := Subtype.finite
      exact hI hT ↥(adjointGroup .E7 K) S (eAd.symm.trans eS.symm) p hdiag
    | E8 q =>
      obtain ⟨K, hKf, hKfin, hKcard, hKchar, ⟨eAd⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
      letI := hKf
      letI := hKfin
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_E8]
        exact hPchar
      haveI : CharP K 2 := by rw [← hq2]; exact hKchar
      have hcat2 : catalogIs ↥(adjointGroup .E8 K) (onLie fun d => d.characteristic = 2) :=
        ⟨.lie ⟨.E8 q, hv⟩, hPchar, ⟨eAd.symm⟩⟩
      have hdiag := shapeModelDiagAt_adjoint_of (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) K p hp
        hp2 (fun h => absurd h (by decide)) (fun h _ => absurd h (by decide)) hA hD4 hL hC hG
        hcat2
      haveI : Finite (ModGL .E8 K) := CFSG.LieType.Chevalley.finite_modGL (τ := .E8)
      haveI : Finite ↥(adjointGroup .E8 K) := Subtype.finite
      exact hI hT ↥(adjointGroup .E8 K) S (eAd.symm.trans eS.symm) p hdiag
    | _ => exact hPexc.elim

end CFSG.LocalAnalysis.GLTheoremA.F151

end
