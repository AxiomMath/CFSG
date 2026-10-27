module

import CFSG.ClassicalInvolution.Asc77.AscT8V5Eng
public import CFSG.ClassicalInvolution.Asc77.AscT8Y3

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace T8V

section Layer

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem z_mem_layerJoin (hs : Std8 p f Ω K J S R T W z t) : z ∈ T8.layerJoin Ω (z * t) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hK := T8.xMem_zt hs
  have hRK : IsSylow2In R K :=
    T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.stand.mem hs.hR.1 hs.hR.2.1
  have hRa : R ≤ T8.cenZ (z * t) := by
    rw [T8.cenZ_eq_centralizer]
    exact T8.le_centralizer_mul hs
  have hL := hK.isSylow2In_layerRes_of_le hp hq hΩ hx hRK hRa
  have h8 := hΩ.eight_le_of_mem_RSet hp hs.hR.1
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hs.hR.2.1 hRK.2.1 (by omega)
  exact T8.le_layerJoin ⟨K, hK, rfl⟩ (hL.1 hzR)

theorem T_le_cenZ (hs : Std8 p f Ω K J S R T W z t) : T ≤ T8.cenZ (z * t) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hn21 : K ∈ omegaNbr Ω J :=
    T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hs.stand.mem hs.hJ.1 hs.hJ
  exact T_le_cenZE
    (T8.rep_le_centralizer c (T8.stdRepJ hs) (T8.stdRepK hs) (Or.inr hn21) hs.hz)
    (T8.rep_le_centralizer c (T8.stdRepJ hs) (T8.stdRepJ hs) (Or.inl rfl) hs.ht)

theorem xMem_J (hs : Std8 p f Ω K J S R T W z t) : T8.XMem Ω (z * t) J := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hc := T8.mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht
  exact xMem_JE hΩ.conjInvariant hnt hs.hJ.1 hs.ht hc
    (T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1) (T_le_cenZ hs)

theorem t_mem_layerJoin (hs : Std8 p f Ω K J S R T W z t) : t ∈ T8.layerJoin Ω (z * t) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hJ := xMem_J hs
  have hTJ : IsSylow2In T J :=
    T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1
  have hL := hJ.isSylow2In_layerRes_of_le hp hq hΩ hx hTJ (T_le_cenZ hs)
  have h8 := hΩ.eight_le_of_mem_RSet hp hs.hT.1
  have htT : t ∈ T := T3.mem_of_isPGroup hs.ht hs.hT.2.1 hTJ.2.1 (by omega)
  exact T8.le_layerJoin ⟨J, hJ, rfl⟩ (hL.1 htT)

@[expose] noncomputable def layerMk (x g : G) (hg : g ∈ T8.layerJoin Ω x) : T8.LayerQuot Ω x :=
  QuotientGroup.mk' (classicalInvolutionOddCore ↥(T8.layerJoin Ω x)) ⟨g, hg⟩

end Layer

end T8V

end CFSG.ClassicalInvolution.Asc77
