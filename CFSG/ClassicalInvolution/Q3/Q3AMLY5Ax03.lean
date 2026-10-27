module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY5Ax02
public import CFSG.ClassicalInvolution.Q3.Q3AMLY5Stmt
public import CFSG.ClassicalInvolution.Q3.Q3T8B13

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8W
  CFSG.ClassicalInvolution.Q3.Q3NL
open scoped commutatorElement

section Frame


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
  {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem layer_commute_of_mem_two_subgroup [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    (hint : Uniform.IsIntrinsicU (.sl2 3 1) K z) {P : Subgroup G} (hP : IsPGroup 2 ↥P) {k x : G}
    (hk : k ∈ K) (hx : x ∈ nbrLayer Ω K z) (hkP : k ∈ P) (hxP : x ∈ P) : k * x = x * k := by
  have h1 := commutator_mem_oddCoreOf_nbrLayer' h hint h.std.stand.mem h.std.hz hk hx
  have hmemP : ⁅k, x⁆ ∈ P := by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hkP hxP) (P.inv_mem hkP)) (P.inv_mem hxP)
  have hpg : IsPGroup 2 ↥(Subgroup.zpowers ⁅k, x⁆) := hP.to_le (Subgroup.zpowers_le.mpr hmemP)
  have h2 : ⁅k, x⁆ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) h1 hpg
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

theorem not_mem_layer_of_center_eq_bot (hs : Std8 Ω K J S R T W z t)
    (hcen : Subgroup.center (↥(nbrLayer Ω K z) ⧸
      classicalInvolutionOddCore ↥(nbrLayer Ω K z)) = ⊥) : z ∉ nbrLayer Ω K z := by
  intro hz
  set Y : Subgroup G := nbrLayer Ω K z with hYdef
  have hcz : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨z, hz⟩ ∈
      Subgroup.center (↥Y ⧸ classicalInvolutionOddCore ↥Y) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hyz : (y : G) * z = z * (y : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (nbrLayer_le_centralizer Ω K z y.2)
    show QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) y *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨z, hz⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨z, hz⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyz
  rw [hcen, Subgroup.mem_bot] at hcz
  have h2 : (⟨z, hz⟩ : ↥Y) ∈ classicalInvolutionOddCore ↥Y := (QuotientGroup.eq_one_iff _).mp hcz
  have h3 : z ∈ oddCoreOf Y := mem_oddCoreOf_iff.mpr ⟨hz, h2⟩
  exact hs.hz.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard Y) h3
    (isPGroup_zpowers_of_mul_self_eq_one hs.hz.sq hs.hz.ne_one))

theorem e1Y_of_center_eq_bot [IsSimpleGroup G] (hset : E4SettingY Ω K J S R T W z t)
    (hcen : Subgroup.center (↥(nbrLayer Ω K z) ⧸
      classicalInvolutionOddCore ↥(nbrLayer Ω K z)) = ⊥) :
    ∃ s : G, E4Axis Ω K J R z t s := by
  classical
  have h : BadStd8 Ω K J S R T W z t := hset.bad
  have hs : Std8 Ω K J S R T W z t := h.std
  have hE : MuIsoE4 Ω W := hset.mu
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hntJ : ∀ M' ∈ twinSet Ω J, M' = J :=
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hJΩ
  have hzY : z ∉ nbrLayer Ω K z := not_mem_layer_of_center_eq_bot hs hcen
  set Y : Subgroup G := nbrLayer Ω K z with hYdef
  obtain ⟨S₂, hRS₂, hTS₂, hS₂Y⟩ := layer_exists_sylow_RT hs
  obtain ⟨g, hgY, hgS, hgne⟩ := layer_exists_zStar_conj hs hE hRS₂ hTS₂ hS₂Y hcen
  have htT : t ∈ T := mem_T_of_std8 hs
  have hTY : T ≤ Y := (layerT_le_exactCore hs).trans (exactCore3_le_nbrLayer hs.hJ)
  have htY : t ∈ Y := hTY htT
  have hgiY : g⁻¹ ∈ Y := Y.inv_mem hgY
  have hsY : g⁻¹ * t * g ∈ Y := Y.mul_mem (Y.mul_mem hgiY htY) hgY
  have hct : g⁻¹ * t * g * t * (g⁻¹ * t * g)⁻¹ = t :=
    layer_sY_centralizes_t hs hE hRS₂ hTS₂ hgS hsY
  have htt1 : t * (g⁻¹ * t * g) = g⁻¹ * t * g * t := by
    calc t * (g⁻¹ * t * g) = (g⁻¹ * t * g * t * (g⁻¹ * t * g)⁻¹) * (g⁻¹ * t * g) := by
          rw [hct]
      _ = g⁻¹ * t * g * t := by group
  have hS₂2 : IsPGroup 2 ↥(S₂ : Subgroup G) := S₂.isPGroup'
  have hcommR : ∀ r ∈ R, r * (g⁻¹ * t * g) = g⁻¹ * t * g * r := fun r hr =>
    layer_commute_of_mem_two_subgroup h hset.hint hS₂2 (hs.hR.2.1 hr) hsY (hRS₂ hr) hgS
  have hcommRt : ∀ r ∈ R, r * t = t * r := fun r hr =>
    layer_commute_of_mem_two_subgroup h hset.hint hS₂2 (hs.hR.2.1 hr) htY (hRS₂ hr)
      (hTS₂ htT)
  have hRts : ∀ r ∈ R, r * (t * (g⁻¹ * t * g)) = t * (g⁻¹ * t * g) * r := fun r hr => by
    rw [← mul_assoc, hcommRt r hr, mul_assoc, hcommR r hr, ← mul_assoc]
  have hRsyl : IsSylow2In R K :=
    Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hs.hR.1 hs.hR.2.1
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hs.hR.2.1 hRsyl.2.1
    (by have := hΩ.eight_le_of_mem_RSet hs.hR.1; omega)
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have hzs : z * (g⁻¹ * t * g) = g⁻¹ * t * g * z := hcommR z hzR
  have ht1sq : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [hs.ht.sq]; group
  have ht1ne : g⁻¹ * t * g ≠ 1 := by
    intro h1
    apply hs.ht.ne_one
    have := congrArg (fun y => g * y * g⁻¹) h1
    simpa [mul_assoc] using this
  have hztY : z * t ∉ Y := fun hmem => hzY (by
    simpa using Y.mul_mem hmem (Y.inv_mem htY))
  have hind : g⁻¹ * t * g ∉ Subgroup.closure ({z, t} : Set G) := by
    intro hmem
    rcases Thompson.eq_of_mem_closure_pair hs.hz.sq hs.ht.sq hzt hmem with h1 | h1 | h1 | h1
    · exact ht1ne h1
    · exact hzY (h1 ▸ hsY)
    · exact hgne h1
    · exact hztY (h1 ▸ hsY)
  have hCK : ∀ y ∈ Y, conjSub y K = K := fun y hy =>
    conjSub_eq_of_mem_centralizer_std8 hs (nbrLayer_le_centralizer Ω K z hy)
  have hJ₁ : conjSub g⁻¹ J ∈ omegaNbr Ω K :=
    conjSub_mem_omegaNbr_of_conjSub_eq hΩ (hCK g⁻¹ hgiY) hs.hJ
  have hb : IsUniqueInvolution (conjSub g⁻¹ J) (g⁻¹ * t * g) := by
    have := hs.ht.conj g⁻¹
    rwa [inv_inv] at this
  have hAE := hs.stand.aEmpty J hJΩ
  have hconj : IsConj t (t * (g⁻¹ * t * g)) := by
    rcases isConj_or_mem_omegaNbr_gen hΩ hJΩ hAE hntJ hs.ht hgne htt1 with hc | hnbr
    · exact hc
    · exact absurd hnbr (hset.noTri _ hJ₁)
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hJ₂Ω : conjSub c J ∈ Ω := hΩ.conjInvariant c J hJΩ
  have hJ₂t : IsUniqueInvolution (conjSub c J) (t * (g⁻¹ * t * g)) := by
    have := hs.ht.conj c
    rwa [hc] at this
  have hJ₂K : conjSub c J ≠ K := by
    intro hEq
    rw [hEq] at hJ₂t
    rcases hs.hz.unique _ hJ₂t.mem hJ₂t.sq with h1 | h1
    · exact hJ₂t.ne_one h1
    · exact hzY (h1 ▸ Y.mul_mem htY hsY)
  have hJ₂ : conjSub c J ∈ omegaNbr Ω K :=
    mem_omegaNbr_of_centralizes hΩ hK hJ₂Ω hJ₂K hJ₂t hs.hR.1 hs.hR.2.1 hRts
  exact ⟨g⁻¹ * t * g, E4Axis.ofNbr ht1sq ht1ne hzs htt1 hind hcommR
    (layer_sY_normalizes_J hs hE hRS₂ hTS₂ hgS hsY) ⟨conjSub g⁻¹ J, hJ₁, hb⟩
    ⟨conjSub c J, hJ₂, hJ₂t⟩⟩

end Frame

end CFSG.ClassicalInvolution.Q3.Q3AM
