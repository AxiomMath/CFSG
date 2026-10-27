module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5G8Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PKMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPFin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPHypOf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5LADefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PE8Odd

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.ClassicalInvolution.Disconnected.AschTight

theorem asc82P510TR_of
    (hB3 : GoldschmidtB3Tmp) (hSH8 : Sec5SH8Statement) (hy : Sec5B59Hyp) (h55 : Asc82Lemma55)
    (h58d : Asc82Lemma58d) (hFB : Asc82Sec5FactB5z) (h4 : Asc82FactReflCentQ6)
    (hU : Asc82FactPocketsUniq6) (hSq : Asc82FactSqReflQ6) (hLA : Asc82Sec5LemmaA)
    (hD : Asc82FactQCentOrd6) (hK : Asc82FactQCentTwo6)
    (hO3 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      IsPGroup 3 (oddCoreIn L))
    (hTE : Asc82P510TE) : Asc82P510TR := by
  intro G _ _ t L S z r ρ B A φ K₁ K₂ a b h hs hTR
  by_cases hTE' : sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) =
      sec5p510_E t a b
  · exact hTE G t L S z r ρ B A φ K₁ K₂ a b h hs hTE'
  · obtain ⟨X, hXgrp, π, hhyp⟩ := sec5op_exists_hyp_gen h hs
    letI : Group X := hXgrp
    haveI : Finite X := Finite.of_surjective π hhyp.surj
    have hout : Sec5G8Outcome (sec5op_Tb z
        (sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))) π) :=
      sec5g8_main hB3 hSH8 hy h55 h58d hFB h4 hU hSq h hs hTE' π hhyp.surj hhyp.ker
    obtain ⟨K', hK'p, -, hK'R, -, -, hK'gen⟩ :=
      sec5op_lemmaK hy hD hK (hO3 G L h.toSec5Setting.isOm6Z2) h hs (Or.inl rfl)
    refine ⟨K', hK'p,
      sec5op_final_of_odd hhyp (fun x hx => (hK'p.2.1 hx).2) hK'gen ?_⟩
    intro k hkK hkodd
    have hkH : k ∈ centralizer ({z} : Set G) := (hK'p.2.1 hkK).2
    have hkL : k ∈ L := (hK'p.2.1 hkK).1
    have hkT : ∀ x ∈ sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)),
        x * k = k * x := by
      intro x hx
      exact Subgroup.mem_centralizer_iff.mp (hK'R hkK) x (hTR.le hx)
    have htT : ∀ x ∈ sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)),
        x * t = t * x := by
      intro x hx
      have hxR : x ∈ sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂) := hTR.le hx
      have hxS : x ∈ S := (Subgroup.mem_inf.mp hxR).1
      exact Subgroup.mem_centralizer_singleton_iff.mp (h.toSec5Ctx.sylow.1 hxS)
    have hLA' : ∀ w ∈ sec5op_Y t z, w * t = t * w → Nat.Coprime (orderOf w) 6 →
        w ∈ centralizer (L : Set G) := by
      intro w hwY hwt hw6
      exact hLA hy.h36 G t L S z h.toSec5Ctx w
        (Subgroup.mem_centralizer_singleton_iff.mpr hwt)
        (sec5op_Y_le hhyp.tH hwY) hw6
    exact sec5pe8m_odd_mem_kerG hhyp hout hkH hkL hkodd hkT htT hLA'

end CFSG.OddStandard.SmallF3.Omega
