module

public import CFSG.ClassicalInvolution.Q3.TL3T12_6Dual
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfLift
public import CFSG.ClassicalInvolution.Q3.E64Ker.Main

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

theorem e64_ker_le_threeClosure {X : Type} [Group X]
    [Finite X] (φ : X →* AE.AEQ 7) (hφ : φ.range = AE.e64Sub)
    (hker : φ.ker ≤ Subgroup.center X) (hker2 : IsPGroup 2 φ.ker)
    (Q : Set (Subgroup X)) (hgen : pSpan Q = ⊤)
    (hconj : ∀ L ∈ Q, ∀ x : X, conjSub x L ∈ Q) (hord : ∀ L ∈ Q, Nat.card L = 8)
    (hlab : ∀ L ∈ Q, ∃ α ∈ AE.e64Sets, ∃ (h : α.card = 4) (b : Bool),
      L.map φ = AE.memBar α h b)
    (hsurj : ∀ α ∈ AE.e64Sets, ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ Q,
      L.map φ = AE.memBar α h b)
    (hinj : ∀ L ∈ Q, ∀ L' ∈ Q, L.map φ = L'.map φ → L = L')
    {K : Subgroup X} (hK : K ∈ Q) {z : X} (hz : IsUniqueInvolution K z) :
    φ.ker ≤ Subgroup.closure {w : X | w * z = z * w ∧ ∃ a : ℕ, w ^ 3 ^ a = 1} :=
  E64Ker.e64_ker_le_threeClosure' φ hφ hker hker2 Q hgen hconj hord hlab hsurj hinj hK hz

variable {G : Type} [Group G] [Finite G]

theorem AEIdentOn.ker_le_threeClosure_e64 {P : Set (Subgroup G)}
    (I : AEIdentOn P 7 AE.e64Sets AE.e64Sub)
    (hO : classicalInvolutionOddCore ↥(pSpan P) = ⊥) (hc8 : ∀ L ∈ P, Nat.card L = 8)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hinj : ∀ L ∈ P, ∀ L' ∈ P, (L.subgroupOf (pSpan P)).map I.φ =
      (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    {K : Subgroup G} (hK : K ∈ P) {z : G} (hz : IsUniqueInvolution K z) :
    ∀ k ∈ I.φ.ker, k ∈ Subgroup.closure
      (TwinThinPf.threeGens P (⟨z, le_pSpan hK hz.mem⟩ : ↥(pSpan P))) := by
  have hLX : ∀ L ∈ P, L ≤ pSpan P := fun L hL => le_pSpan hL
  have hk2 : IsPGroup 2 I.φ.ker := I.toLabel.isPGroup_ker hO
  refine e64_ker_le_threeClosure (X := ↥(pSpan P)) I.φ I.range_eq I.ker_le hk2
    (restrictFamily P (pSpan P)) (pSpan_restrictFamily_eq_top P) ?_ ?_ ?_ ?_ ?_
    (K := K.subgroupOf (pSpan P)) ⟨K, hK, hLX K hK, rfl⟩
    (z := (⟨z, le_pSpan hK hz.mem⟩ : ↥(pSpan P))) (isUniqueInvolution_subgroupOf hz (hLX K hK))
  · rintro _ ⟨L, hL, hLX', rfl⟩ x
    refine ⟨conjSub (x : G) L, hinv L hL x x.2, hLX _ (hinv L hL x x.2), ?_⟩
    rw [conjSub_subgroupOf]
  · rintro _ ⟨L, hL, hLX', rfl⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX').toEquiv]
    exact hc8 L hL
  · rintro _ ⟨L, hL, hLX', rfl⟩
    obtain ⟨α, hα, h, b, hlab⟩ := I.label L hL
    exact ⟨α, hα, h, b, hlab⟩
  · intro α hα h b
    obtain ⟨L, hL, hlab⟩ := I.label_surj α hα h b
    exact ⟨L.subgroupOf (pSpan P), ⟨L, hL, hLX L hL, rfl⟩, hlab⟩
  · rintro _ ⟨L, hL, hLX', rfl⟩ _ ⟨L', hL', hLX'', rfl⟩ he
    rw [hinj L hL L' hL' he]

end CFSG.ClassicalInvolution.Q3.TC.Thin
