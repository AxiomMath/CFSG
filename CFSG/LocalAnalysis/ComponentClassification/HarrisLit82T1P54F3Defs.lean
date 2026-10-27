module

public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3Frame
public import CFSG.LocalAnalysis.ComponentClassification.TBLitSwap

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.F3

open CFSG Subgroup Assembly.LowTwoRank

@[expose] def HatFor3 (R : StatedLieTag → ℕ → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → IsPGroup 2 (center Y) →
    ∀ (τ : StatedLieTag) (n : ℕ), R τ n → Blueprint.LieModel (Y ⧸ center Y) τ n 3 1 →
    (∀ m r : ℕ, 0 < m → 0 < r →
      (Blueprint.LieModel (Y ⧸ center Y) .PSL (2 * m) 3 r ∨
        Blueprint.LieModel (Y ⧸ center Y) .PSU (2 * m) 3 r) →
      Nat.card (center Y) = ordProj[2] (Nat.card (Open.griessHopfMultiplier (Y ⧸ center Y)))) →
    ∀ t : Y, orderOf t = 2 → t ∈ center Y → Concl3 Y t

@[expose] def RowOddThree : Prop := HatFor3 oddR

@[expose] def RowBThree : Prop := HatFor3 fun τ _ => τ = .POmegaOdd

@[expose] def RowSpThree : Prop := HatFor3 fun τ _ => τ = .PSp

@[expose] def RowSLThree : Prop := HatFor3 fun τ n => τ = .PSL ∧ Even n

@[expose] def RowSUThree : Prop := HatFor3 fun τ n => τ = .PSU ∧ Even n

@[expose] def RowDThree : Prop := HatFor3 fun τ _ => τ = .POmegaPlus ∨ τ = .POmegaMinus

@[expose] def RowE7Three : Prop := HatFor3 fun τ _ => τ = .E7

theorem hatFor3_of_rows (hO : RowOddThree) (hB : RowBThree) (hSp : RowSpThree)
    (hSL : RowSLThree) (hSU : RowSUThree) (hD : RowDThree) (hE7 : RowE7Three) :
    HatFor3 fun _ _ => True := by
  intro Y _ _ hq hZ τ n _ hlie hc t ht htZ
  have key : ∀ R : StatedLieTag → ℕ → Prop, HatFor3 R → R τ n → Concl3 Y t :=
    fun R hR hRτ => hR Y hq hZ τ n hRτ hlie hc t ht htZ
  rcases Nat.even_or_odd n with hn | hn <;> cases τ
  all_goals first
    | exact key _ hB rfl
    | exact key _ hSp rfl
    | exact key _ hSL ⟨rfl, hn⟩
    | exact key _ hSU ⟨rfl, hn⟩
    | exact key _ hD (.inl rfl)
    | exact key _ hD (.inr rfl)
    | exact key _ hE7 rfl
    | exact key _ hO (.inl ⟨.inl rfl, hn⟩)
    | exact key _ hO (.inl ⟨.inr rfl, hn⟩)
    | exact key _ hO (by unfold oddR; simp)

theorem harris82Lemma54Three_of_hatFor3 (h : HatFor3 fun _ _ => True) :
    Harris82Lemma54Three := by
  intro X _ _ hX hM τ n hlie t ht htZ
  have hk := GSThmB.OddQuot.not_two_dvd_card_ker (H := X)
  have hπs := QuotientGroup.mk'_surjective (pPrimeCore 2 X)
  set e := TBLit.coreQuotientCenterEquiv X with he
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htZ' : QuotientGroup.mk' (pPrimeCore 2 X) t ∈ center (X ⧸ pPrimeCore 2 X) := by
    rw [TBLit.fusionZStar_eq_centralPreimage] at htZ
    exact htZ
  have hc : ∀ m r : ℕ, 0 < m → 0 < r →
      (Blueprint.LieModel ((X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) .PSL (2 * m) 3 r ∨
        Blueprint.LieModel ((X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) .PSU (2 * m) 3
          r) →
      Nat.card (center (X ⧸ pPrimeCore 2 X)) = ordProj[2] (Nat.card
        (Open.griessHopfMultiplier ((X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)))) := by
    rcases hM with ⟨-, -, -, hc⟩ | ⟨-, ⟨e'⟩⟩
    · intro m r hm hr hl
      have h1 := hc m r hm hr (hl.imp (GSThmB.OddQuot.lieModel_of_equiv e)
        (GSThmB.OddQuot.lieModel_of_equiv e))
      rw [Frame.ordProj_card_fusionZStar] at h1
      rw [h1, Nat.card_congr (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv]
    · exfalso
      have : Group.IsPerfect (X ⧸ pPrimeCore 2 X) := hX.2.1
      exact TBLit.not_isPerfect_sl2Three
        (Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective)
  exact Concl3.of_map hπs hk htt htZ' (h (X ⧸ pPrimeCore 2 X) hX.2 Frame.isPGroup_center_bar τ n
    trivial (GSThmB.OddQuot.lieModel_of_equiv e.symm hlie) hc _ (Frame.orderOf_map_eq_two hk ht)
    htZ')

end CFSG.ComponentClassification.HarrisLit.T1.P54.F3
