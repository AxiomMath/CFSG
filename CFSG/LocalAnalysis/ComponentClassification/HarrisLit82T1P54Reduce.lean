module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Defs
public import CFSG.LocalAnalysis.ComponentClassification.TBLitSwap
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C4Props

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54

open CFSG Subgroup Assembly.LowTwoRank

theorem harris82Lemma54_of_hatFor (h : HatFor fun _ _ => True) : Harris82Lemma54 := by
  intro X _ _ hX p hp hp2 hM τ n f hlie h5 hpsl t ht htZ
  have hk := GSThmB.OddQuot.not_two_dvd_card_ker (H := X)
  have hπs := QuotientGroup.mk'_surjective (pPrimeCore 2 X)
  set e := TBLit.coreQuotientCenterEquiv X with he
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htZ' : QuotientGroup.mk' (pPrimeCore 2 X) t ∈ center (X ⧸ pPrimeCore 2 X) := by
    rw [TBLit.fusionZStar_eq_centralPreimage] at htZ
    exact htZ
  have hc : ∀ m r : ℕ, 0 < m → 0 < r →
      (Blueprint.LieModel ((X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) .PSL (2 * m) p r ∨
        Blueprint.LieModel ((X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) .PSU (2 * m) p
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
  exact Concl.of_map hπs hk htt htZ' (h (X ⧸ pPrimeCore 2 X) hX.2 Frame.isPGroup_center_bar p hp
    hp2 τ n f trivial (GSThmB.OddQuot.lieModel_of_equiv e.symm hlie) h5
    (fun h1 => hpsl (GSThmB.OddQuot.lieModel_of_equiv e h1)) hc _
    (Frame.orderOf_map_eq_two hk ht) htZ')

end CFSG.ComponentClassification.HarrisLit.T1.P54
