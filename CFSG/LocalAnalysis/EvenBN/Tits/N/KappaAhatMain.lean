module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaAhat
public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaY
public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaLemmaA
public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaSplit

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits N.KappaA

namespace KappaAhat

theorem beta_v10_v9 : betaT (kapTc 0 1) ![0, 1, 0, 0] ![0, 0, 1, 0] = ![1, 1, 0, 0] := by
  decide

end KappaAhat

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem Hyp.kappaY_hc (h49 : d.Thm49Statement) (hd : d.Hyp)
    {q : G} (hqJ : q ∈ d.s56J) (hq9 : q * d.pv 9 * q⁻¹ = d.pv 9 * d.z)
    (hq8 : q * d.pv 8 = d.pv 8 * q) (hq10 : q * d.pv 10 = d.pv 10 * q)
    (hq11 : q * d.pv 11 = d.pv 11 * q) {x : G} (hxV : x ∈ d.s56V) (hxε : d.s56Eps x = d.pv 10)
    (hτ : x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ = d.pv 11) :
    x * q * x⁻¹ * q⁻¹ * (d.pv 11 * d.pv 10) ∈ zpowers d.z := by
  obtain ⟨z₀, hz⟩ := hd.s56_exists_S56Z0 h49
  obtain ⟨μ, hμ⟩ := hd.kappaForm h49 hz
  have hv10E : d.pv 10 ∈ d.E := hd.s56_pv10_mem_E
  have hv11E : d.pv 11 ∈ d.E := s56_pv11_mem_E d
  have hw10 : wcoord d (d.pv 10) = ![0, 1, 0, 0] := by
    have h := wcoord_crdE hd (Pi.single (2 : Fin 5) (1 : ZMod 2))
    rw [crdE_single, show basisV 2 = 10 from rfl] at h
    rw [h]; funext i; fin_cases i <;> rfl
  have hw11 : wcoord d (d.pv 11) = ![1, 0, 0, 0] := by
    have h := wcoord_crdE hd (Pi.single (1 : Fin 5) (1 : ZMod 2))
    rw [crdE_single, show basisV 1 = 11 from rfl] at h
    rw [h]; funext i; fin_cases i <;> rfl
  have hebx : eb d x = ![0, 1, 0, 0] := by
    unfold eb; rw [hxε, hw10]
  have hphi0 : ∀ {e : G}, q * e = e * q → phi d q e = 0 := fun {e} h => by
    unfold phi
    rw [show q * e * q⁻¹ * e⁻¹ = 1 by rw [h]; group]
    exact zc_one
  have hphi9 : phi d q (d.pv 9) = 1 := by
    unfold phi
    have hzc : d.pv 9 * d.z * (d.pv 9)⁻¹ = d.z := by
      rw [hd.s56_E_comm (N.node09K_pv9_mem_E d) hd.s56_z_mem_E]; group
    rw [hq9, hzc]
    exact zc_z hd
  have hfbq : fb d q = ![0, 0, 1, 0] := by
    funext i
    fin_cases i
    · exact hphi0 hq11
    · exact hphi0 hq10
    · exact hphi9
    · exact hphi0 hq8
  obtain ⟨u₇, -, hu₇, hw₇⟩ := hμ x hxV (d.pv 7) (s56_pv_mem_J d (by simp))
  have hκ7 : kk d x (d.pv 7) = 0 := by
    unfold kk; rw [hebx, fb_pv7 hd]; decide
  rw [hκ7, ZMod.val_zero, pow_zero, mul_one, hτ] at hu₇
  rw [← hu₇, hw11, fb_pv7 hd, hebx, kapA_table0 μ ![0, 1, 0, 0] rfl] at hw₇
  have hμ1 : μ = 1 := by
    have h0 := congrFun hw₇ 0
    simpa using h0.symm
  obtain ⟨u, huE, hu, hwu⟩ := hμ x hxV q hqJ
  have hκq : kk d x q = 0 := by
    unfold kk; rw [hebx, hfbq]; decide
  rw [hκq, ZMod.val_zero, pow_zero, mul_one] at hu
  rw [hebx, hfbq, hμ1, KappaAhat.beta_v10_v9] at hwu
  have h1110 : d.pv 11 * d.pv 10 ∈ d.E := mul_mem hv11E hv10E
  rw [hu]
  refine (wcoord_eq_zero_iff hd (mul_mem huE h1110)).1 ?_
  rw [wcoord_mul hd huE h1110, wcoord_mul hd hv11E hv10E, hwu, hw11, hw10]
  decide

end Data

namespace N



theorem stepKappaBitAhat_holds : StepKappaBitAhat := by
  intro G _ _ d h49 hd hR
  by_contra hκ
  obtain ⟨z₀, hz⟩ := hd.s56_exists_S56Z0 h49
  have hsq : z₀ * z₀ = 1 := KappaA.z0_sq_eq_one h49 hd hz
  obtain ⟨x, hxV, hxε, hτ⟩ := hd.kappaAhat_exists_x h49 hz hκ
  have hx2 : x * x = d.z := hd.kappaAhat_sq h49 hR hz hsq hxV hxε hτ
  obtain ⟨-, h9, h8, h10, h11, -, -⟩ := Data.kJ_conj d
  exact hd.kappaY h49 hxV hxε hτ
    (hd.kappaY_hc h49 (Data.kJ_mem_J d) h9 h8 h10 h11 hxV hxε hτ) hx2

end N

end CFSG.LocalAnalysis.EvenBN.Tits
