module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158Fg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcOmega

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X

@[expose] def CompTwoPart3 (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω) (x y : Ω) (J : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore 3 ↥S = ⊥ → IsChevSimple 2 (PSimple 3 S) →
    catalogIs (PSimple 3 S) Q →
    x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x → x ∉ Subgroup.zpowers y → y ∉ Subgroup.zpowers x →
    InnDiagOn 3 (Subgroup.zpowers x) S → FieldOn 3 y S →
    GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J → y ∈ Subgroup.normalizer (J : Set Ω) →
    centCard2 3 J y ^ 3 = card2 3 J

theorem isChevSimple_comp_of_kd {p : ℕ} (hp : p.Prime) (hD : KDChevDownQ p 2) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {x : Ω} {J : Subgroup Ω} (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hSc : IsChevSimple 2 (PSimple p S)) (hxN : x ∈ Subgroup.normalizer (S : Set Ω)) (hxp : x ^ p = 1)
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J) : IsChevSimple 2 (PSimple p J) :=
  chevQ_step hp hD (glaPComponent_self_p hSq hSp) hSc hxN hxp hJ

section Certs


theorem t158FgFldOn_of_omegaNID {Q : TauCeti.CFSGIndex → Prop} {p : ℕ} (hD : KDChevDownQ p 2)
    (hN : L154OmegaNID Q) (hT : L154OmegaTD4 Q) (h2 : CompTwoPart3 Q) : T158FgFldOn p Q := by
  intro hp hp2 Ω _ _ S x y J hSn hSq hSp hSc hQ hxp hyp hxy hxny hynx hInn hF hJ hJy
  have hnid : NonInnDiag p y J := hN p hp hp2 Ω S x y J hSn hSq hSp hSc hQ hxp hyp hxy hInn hF hJ hJy
  have htd4 : ¬ (p = 3 ∧ IsTD4 3 J) :=
    hT p hp hp2 Ω S x y J hSn hSq hSp hSc hQ hxp hyp hxy hInn hF hJ hJy
  have hcJ : IsChevSimple 2 (PSimple p J) :=
    isChevSimple_comp_of_kd hp hD hSq hSp hSc (hInn.1 (Subgroup.mem_zpowers x)) hxp hJ
  rcases i91_holds Ω p hp hp2 _ J y hJ hcJ hJy hyp hnid with hFJ | ⟨hp3, - | hTD⟩
  · exact Or.inl hFJ
  · subst hp3
    exact Or.inr ⟨hnid, htd4,
      h2 Ω S x y J hSn hSq hSp hSc hQ hxp hyp hxy hxny hynx hInn hF hJ hJy⟩
  · exact absurd ⟨hp3, hTD⟩ htd4

end Certs

section KD


theorem kdChevDownQ_two_holds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : KDChevDownQ p 2 := by
  by_cases hp3 : p = 3
  · subst hp3
    exact kdChevDownQ_three_of_lieComp lieComp_holds 2
  · have hp4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    have hp5 : 5 ≤ p := by
      have := hp.two_le
      omega
    have hAmbSolv : KDAmbSolv p := kdAmbSolv_holds hp hp2 u42_fixSubgroup_solvable
    have hInner : KDChevInner p := kdChevInner_of hp hp2
      (kdCharP_of_lieQConstrainedInner hp
        (CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.lieQConstrainedInner_odd hp hp2)) hAmbSolv
    exact kdChevDownQ_of_lieComps hp (lieCompsOn_holds hp hp5) (fun _ => hInner)
      (kdAmbDownQ_holds hp hp2 hInner hAmbSolv)

theorem t158FgFldOn_of_omegaNID' {Q : TauCeti.CFSGIndex → Prop} (hN : L154OmegaNID Q) (hT : L154OmegaTD4 Q)
    (h2 : CompTwoPart3 Q) (p : ℕ) : T158FgFldOn p Q :=
  fun hp hp2 => t158FgFldOn_of_omegaNID (kdChevDownQ_two_holds hp hp2) hN hT h2 hp hp2

end KD

end CFSG.LocalAnalysis.GLTheoremA.T158

end
