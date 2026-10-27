module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOModel
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOSec
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOJ
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOMin
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOSign

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL)

theorem oCore_of
    (hpc : ∀ {K : Type} [Field K] [Finite K], ringChar K ≠ 2 → ∀ {ℓ e : ℕ}, ℓ.Prime →
      Nat.card K = ℓ ^ e → ∀ {d : ℕ}, 7 ≤ d → ∀ {R : GL (Fin d) K},
      (R : Matrix (Fin d) (Fin d) K)ᵀ = R → ∀ {T : GL (Fin d) K}
      (hT : T ∈ matrixDerived (oQ R)), (T : Matrix (Fin d) (Fin d) K) * T = -1 →
      ∀ {J : Subgroup (StatedProj (matrixDerived (oQ R)))},
      J ≤ centralizer ({projH _ ⟨T, hT⟩} : Set _) →
      IsPComponent 2 (J.subgroupOf (centralizer ({projH _ ⟨T, hT⟩} : Set _))) →
      (∀ u ∈ J, ∀ v ∈ J, ∀ w ∈ J, ¬ X10Orth.E8Triple u v w) → False)
    (hord : ∀ {K : Type} [Field K] [Finite K], ringChar K ≠ 2 → ∀ {p f₀ f : ℕ}, p.Prime →
      Nat.card K = p ^ f₀ → f = 2 * f₀ → ∀ {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
      {C : Finset (Fin d)}, Cᶜ.Nonempty → (3 ≤ C.card → BlockNF w C) →
      ∀ {L : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))},
      L ≤ Burgoyne.C.blockP K hw C → IsPComponent 2 (L.subgroupOf (Burgoyne.C.blockP K hw C)) →
      Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSp 2 p f → False)
    (hord4 : ∀ {K : Type} [Field K] [Finite K], ringChar K ≠ 2 → ∀ {p f₀ f : ℕ}, p.Prime →
      Nat.card K = p ^ f₀ → ∀ {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
      {I : Finset (Fin d)}, Iᶜ.Nonempty → I.card = 4 → BlockNF w I →
      IsQuasisimple (Burgoyne.C.blockP K hw I) →
      Blueprint.LieModel (↥(Burgoyne.C.blockP K hw I) ⧸ pPrimeCore 2 ↥(Burgoyne.C.blockP K hw I))
        .PSL 2 p f → f = 2 * f₀)
    (hcomm : ∀ {K : Type} [Field K] [Finite K], ringChar K ≠ 2 → ∀ {d : ℕ} {w : Fin d → K}
      (hw : ∀ i, w i ≠ 0), OKer (oQ (diagGL hw)) → ∀ {J I : Finset (Fin d)}
      (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))), (I = J ∨ I = Jᶜ) → Iᶜ.Nonempty →
      BlockNF w I → IsQuasisimple (Burgoyne.C.blockP K hw I) →
      ∀ {g : similarityPairs (oQ (diagGL hw))}, (∀ x ∈ Burgoyne.C.blockP K hw I, oκ _ g x = x) →
      oκ _ g (projH _ ⟨signGL K J, hJ⟩) = projH _ ⟨signGL K J, hJ⟩ →
      g.val.right = 1 ∧ ∃ c : Kˣ, ∀ i ∈ I, ∀ j : Fin d,
        (g.val.left : Matrix (Fin d) (Fin d) K) i j = (if i = j then (c : K) else 0) ∧
        (g.val.left : Matrix (Fin d) (Fin d) K) j i = (if i = j then (c : K) else 0)) :
    OCore := by
  intro K _ _ p f₀ f d R hK hp hKc hf h5 hd hR hker hsimp E L t J J₀ h hκ
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hp2 : p ≠ 2 := by
    have : Fintype K := Fintype.ofFinite K
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    rw [← ringChar.eq K p]
    exact hK
  have hE1 := h.exists_ne_one
  obtain ⟨T, hT, rfl, hT2 | hT2⟩ := exists_lift_sq h2 (by omega) hR h.ht2
  swap
  · exact hpc hK hp hKc hd hR hT hT2 h.hJt h.hJc (h.noE8 hp2)
  obtain ⟨w, hw, Js, hJs, θ, hker', hJne, hJcne, hNF, hθt, hκθ⟩ :=
    exists_sign_model hK hR hker hT hT2 h.ht1
  have hd' := h.map θ
  rw [hθt] at hd'
  have hκ' : ∀ e' ∈ E.map (MulAut.congr θ).toMonoidHom,
      ∃ g' : similarityPairs (oQ (diagGL hw)), e' = oκ _ g' := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨g, rfl⟩ := hκ e he
    obtain ⟨g', hg'⟩ := hκθ g
    exact ⟨g', hg'⟩
  have hE1' : ∃ e' ∈ E.map (MulAut.congr θ).toMonoidHom, e' ≠ 1 := by
    obtain ⟨e, he, he1⟩ := hE1
    exact ⟨_, ⟨e, he, rfl⟩, fun h1 =>
      he1 ((MulAut.congr θ).injective (h1.trans (map_one _).symm))⟩
  obtain ⟨I, hI, hI3, hI4, hJe, hq, hIL⟩ :=
    eq_blockP_of_barData hK hd hw hJs hJne hJcne hNF hp2 hd'
  rw [hJe] at hd'
  have hIc : Iᶜ.Nonempty := by
    rcases hI with rfl | rfl
    · exact hJcne
    · rwa [compl_compl]
  have hIne : I.Nonempty := Finset.card_pos.1 (by omega)
  have hNFI := hNF I hI hI3
  obtain ⟨h4, hrep, M, hMH, hMp, hML, hMD⟩ := card_eq_four_of_scalar hw hK hJs hI hI3 hI4 hIc
    hNFI hq hd' hIL hκ' hE1' fun g hfix ht => hcomm hK hw hker' hJs hI hIc hNFI hq hfix ht
  have hf2 := hord4 hK hp hKc hw hIc h4 hNFI hq hd'.hJm
  obtain ⟨w', hw', C, θ₂, hCc, hNFC, hLC, hLc⟩ := exists_second_model hw hK hker' hIne hd'.hE
    hE1' hrep hd'.hLE hd'.hLc hMH hMp hML hMD
  exact hord hK hp hKc hf2 hw' hCc hNFC hLC hLc (lieModel_map_equiv θ₂ hd'.hLm)

end CFSG.ComponentClassification.GSThmB.QPUCl
