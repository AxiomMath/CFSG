module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpVanish
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OConj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpine

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
open CFSG.LocalAnalysis.GLTheoremA.T173X

theorem modelFactSpSplit_holds :
    ∀ (F : Type) [Field F] [Finite F] (ℓ n p : ℕ), 3 ≤ ℓ → Nat.card F = 2 ^ n →
      p.Prime → p ≠ 2 → p ∣ 2 ^ n - 1 → ModelFactV p ↥(StatedSp ℓ F) := by
  intro F hF hFin l n p hl hn hp hp2 hpq
  letI : Field F := hF
  letI : Finite F := hFin
  haveI : CharP F 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hn
  refine modelFactV_of_frame (G₀ := ↥(StatedSp l F)) (p := p)
    (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) p) ?_ ?_
  · intro A hA
    exact exists_conj_eq_symplecticQTorus_of_isBmax (by omega) hn hp hp2 hpq hA
  · intro d hd
    exact stdVanishes_symplecticQTorus (F := F) (ℓ := l) (n := n) (p := p) hl hn hp hp2 hpq hd

theorem i173OOn_famSpSplit
    : I173OOn famSpSplit := by
  intro p Om _ _ S B N D K x lab hcfg hlab hfam hmark
  obtain ⟨htag, hrank, hpq⟩ := hfam
  obtain ⟨F, hF, hFin, hcard, hZ, ⟨M⟩⟩ := exists_model_sp hcfg hlab htag hrank hmark
  letI : Field F := hF
  letI : Finite F := hFin
  exact concl_of_modelFactO hcfg M hZ (ModelFactV.modelFactO
    (modelFactSpSplit_holds F lab.rank lab.n p hrank hcard hcfg.prime hcfg.odd hpq))

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
