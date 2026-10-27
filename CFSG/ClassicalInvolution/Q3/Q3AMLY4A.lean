module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadNbhd

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.LY4

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3AM (nbrLayer exactCore3_le_nbrLayer nbrLayer_le_centralizer
  conj_mem_nbrLayer conj_mem_oddCoreOf_of_mem_self)
open scoped commutatorElement

section Thin


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem centralizer_conjSub_eq (hs : Std8 Ω K J S R T W z t) {M : Subgroup G} {a : G}
    (hM : M ∈ Ω) (ha : IsUniqueInvolution M a) :
    ∀ g ∈ Subgroup.centralizer ({a} : Set G), conjSub g M = M := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  exact fun g hg => mem_normalizer_iff_conjSub_eq.mp
    (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hM (hnt M hM) ha hg)

theorem centralizer_le_normalizer_layer (hs : Std8 Ω K J S R T W z t) {M : Subgroup G} {a : G}
    (hM : M ∈ Ω) (ha : IsUniqueInvolution M a) :
    Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer ((nbrLayer Ω M a : Subgroup G) : Set G) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hCM := centralizer_conjSub_eq hs hM ha
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_nbrLayer hΩ hCM hg hy, fun hy => ?_⟩
  have := conj_mem_nbrLayer hΩ hCM (Subgroup.inv_mem _ hg) hy
  simpa [mul_assoc] using this

theorem T_le_centralizer (hs : Std8 Ω K J S R T W z t) :
    T ≤ Subgroup.centralizer ({z} : Set G) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.stand.mem hRΩ hRK
  have h8R := hΩ.eight_le_of_mem_RSet hRΩ
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
  have hcomm : Commutes T R :=
    l6_7_proved G Ω hΩ S T hTΩ R hRΩ hTS hRS (Ne.symm (T8R.R_ne_T hs))
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hcomm x hx z hzR

theorem T_le_exactCore (hs : Std8 Ω K J S R T W z t) : T ≤ exactCore3 z J :=
  le_inf hs.hT.2.1 (T_le_centralizer hs)

theorem isSylow2In_T_layer (hs : Std8 Ω K J S R T W z t)
    (hY : nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z)) :
    IsSylow2In T (nbrLayer Ω K z) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hTΩ hTJ
  have hTsyl' : IsSylow2In T (exactCore3 z J) :=
    ⟨T_le_exactCore hs, hTsyl.2.1, fun V hVQ hV2 hTV =>
      hTsyl.2.2 V (hVQ.trans (exactCore3_le_left z J)) hV2 hTV⟩
  exact T8R.isSylow2In_of_eq_sup_oddCoreOf (exactCore3_le_nbrLayer hs.hJ) hY hTsyl'

theorem sylow_inf_layer (hs : Std8 Ω K J S R T W z t)
    (hY : nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z)) :
    (S : Subgroup G) ⊓ nbrLayer Ω K z = T := by
  have hTX := isSylow2In_T_layer hs hY
  exact hTX.eq_of_le S.isPGroup'.to_inf_left inf_le_right (le_inf hs.hT.2.2 hTX.1)

theorem exists_conj_of_nbr_thin (hΩ : HypOmegaMod Ω) {K N₀ N : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hN₀ : N₀ ∈ omegaNbr Ω K) (hN : N ∈ omegaNbr Ω K)
    (hY : nbrLayer Ω K z = exactCore3 z N₀ ⊔ oddCoreOf (nbrLayer Ω K z)) :
    ∃ y ∈ nbrLayer Ω K z, conjSub y N₀ = N := by
  obtain ⟨hN₀Ω, -, R₀, hR₀, hR₀N₀, hR₀N⟩ := id hN₀
  obtain ⟨hNΩ, -, R₁, hR₁, hR₁N, hR₁N'⟩ := id hN
  have hR₀syl : IsSylow2In R₀ N₀ := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hN₀Ω hR₀ hR₀N₀
  have hR₁syl : IsSylow2In R₁ N := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hNΩ hR₁ hR₁N
  have hR₀c : R₀ ≤ exactCore3 z N₀ :=
    le_inf hR₀N₀ (T3.le_centralizer_of_le_normalizer' hz hR₀N)
  have hR₁c : R₁ ≤ exactCore3 z N :=
    le_inf hR₁N (T3.le_centralizer_of_le_normalizer' hz hR₁N')
  have hR₀syl' : IsSylow2In R₀ (exactCore3 z N₀) :=
    ⟨hR₀c, hR₀syl.2.1, fun V hVQ hV2 hTV =>
      hR₀syl.2.2 V (hVQ.trans (exactCore3_le_left z N₀)) hV2 hTV⟩
  have hR₀Y : IsSylow2In R₀ (nbrLayer Ω K z) :=
    T8R.isSylow2In_of_eq_sup_oddCoreOf (exactCore3_le_nbrLayer hN₀) hY hR₀syl'
  have hcard : Nat.card R₀ = Nat.card R₁ :=
    Disconnected.AschTight.Sec6Gen.natCard_isSylow2In_eq hΩ hN₀Ω hNΩ hR₀syl hR₁syl
  have hR₁Y : IsSylow2In R₁ (nbrLayer Ω K z) :=
    hR₀Y.of_natCard_le hR₁syl.2.1 (hR₁c.trans (exactCore3_le_nbrLayer hN)) hcard.le
  obtain ⟨x, hxY, hxR⟩ := Thompson.exists_conj_of_isSylow2In hR₀Y hR₁Y
  have h8 := hΩ.eight_le_of_mem_RSet hR₀
  exact ⟨x, hxY, hΩ.eq_of_le_of_le (hΩ.conjInvariant x N₀ hN₀Ω) hNΩ hR₁syl.2.1 (by omega)
    (hxR ▸ conjSub_mono (n := x) hR₀N₀) hR₁N⟩

end Thin

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.LY4
