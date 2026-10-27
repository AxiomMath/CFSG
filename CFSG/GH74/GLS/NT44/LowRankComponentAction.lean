module

public import CFSG.GH74.GLS.C3.Layer1.Th2BalGlobal

import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGold
import CFSG.GH74.GLS.NT44.FaithfulContainment
import CFSG.GH74.GLS.NT44.StronglyClosedComponent
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalTransfer
public import CFSG.Goldschmidt.Basic

public section

namespace CFSG.GH74.GLS.NT44

set_option autoImplicit false

theorem original_low_rank_component_action_of_faithful_image
    {G : Type} [Group G] [Finite G]
    {T W : Subgroup G} {x a : G}
    {L : Subgroup (CFSG.GH74.CentralizerBar a)}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (hWT : W ≤ T)
    (hWH : W ≤ Subgroup.centralizer ({a} : Set G))
    (hL : CFSG.IsComponent L) :
    let Z : Subgroup G := Subgroup.closure {z : G | z ∈ T ∧ IsConj x z}
    let H : Subgroup G := Subgroup.centralizer ({a} : Set G)
    let π := CFSG.GH74.GLS.Th2.Bal.piBar a
    let j : ↥W →* CFSG.GH74.CentralizerBar a :=
      π.comp (Subgroup.inclusion hWH)
    let V : Subgroup (CFSG.GH74.CentralizerBar a) :=
      (Z.subgroupOf H).map π
    ∀ (_hZomega : Z = CFSG.GH74.GLS.omega1 W)
      (_hZcl : ∀ z ∈ Z, ∀ g : G, g⁻¹ * z * g ∈ T → g⁻¹ * z * g ∈ Z)
      (_hj : Function.Injective j)
      (_hV4 : Nat.card ↥V = 4)
      (_hVElem : CFSG.IsElementaryAbelian 2 ↥V)
      (_hfaith : ∀ v ∈ V, v ≠ 1 → ¬ ∀ l ∈ L, v * l = l * v),
      ∃ (S : Sylow 2 ↥H) (hLn : L.Normal),
        let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        let Sbar : Sylow 2 (CFSG.GH74.CentralizerBar a) :=
          S.mapSurjective (CFSG.GH74.GLS.TwoThin.barMk_surjective (Y := ↥H))
        let α : ↥W →* MulAut (↥L ⧸ Subgroup.center ↥L) :=
          (@CFSG.GH74.GLS.Prop27.actQuot
            (CFSG.GH74.CentralizerBar a) inferInstance L hLn).comp j
        (W.subgroupOf H) ≤ (S : Subgroup ↥H) ∧
          V ≤ (Sbar : Subgroup (CFSG.GH74.CentralizerBar a)) ∧
          CFSG.Open.fusionStronglyClosed
            (V : Set (CFSG.GH74.CentralizerBar a))
            (Sbar : Subgroup (CFSG.GH74.CentralizerBar a)) ∧
          L ≤ Subgroup.normalClosure (V : Set (CFSG.GH74.CentralizerBar a)) ∧
          V ≤ L ∧
          CFSG.Open.goldschmidtSimpleType (↥L ⧸ Subgroup.center ↥L) ∧
          CFSG.Goldschmidt.InducesOmega1 V L
            (Sbar : Subgroup (CFSG.GH74.CentralizerBar a)) ∧
          (∀ v ∈ V, ∃ t ∈ V ⊓ L, ∀ l ∈ L,
            v⁻¹ * l * v = t⁻¹ * l * t) ∧
          Function.Injective α
 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  dsimp only
  intro hZomega hZcl hj hV4 hVElem hfaith
  let Z : Subgroup G := Subgroup.closure {z : G | z ∈ T ∧ IsConj x z}
  let H : Subgroup G := Subgroup.centralizer ({a} : Set G)
  let π : ↥H →* CFSG.GH74.CentralizerBar a := CFSG.GH74.GLS.Th2.Bal.piBar a
  let j : ↥W →* CFSG.GH74.CentralizerBar a := π.comp (Subgroup.inclusion hWH)
  let V : Subgroup (CFSG.GH74.CentralizerBar a) := (Z.subgroupOf H).map π
  have hZleW : Z ≤ W := by
    change Subgroup.closure {z : G | z ∈ T ∧ IsConj x z} ≤ W
    rw [hZomega]
    change Subgroup.closure {u : G | u ∈ W ∧ u * u = 1} ≤ W
    exact (Subgroup.closure_le W).2 (fun u hu => hu.1)
  have hZH : Z ≤ H := hZleW.trans hWH
  have hW2 : IsPGroup 2 ↥W := hT.isPGroup.to_le hWT
  have hW2H : IsPGroup 2 ↥(W.subgroupOf H) := hW2.comap_subtype (K := H)
  obtain ⟨S, hWS⟩ := hW2H.exists_le_sylow
  have hTiff := (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := T) (K := ⊤)).1 hT
  have hidx : ¬ 2 ∣ T.index := by
    have h := hTiff.2.2
    rwa [Subgroup.relIndex_top_right] at h
  let P : Sylow 2 G := hTiff.2.1.toSylow hidx
  have hPcoe : (P : Subgroup G) = T := by
    dsimp [P]
  have hZclP : CFSG.Open.fusionStronglyClosed (Z : Set G) (P : Subgroup G) := by
    rw [hPcoe]
    exact hZcl
  have hZS : Z.subgroupOf H ≤ (S : Subgroup ↥H) :=
    (Subgroup.subgroupOf_mono H hZleW).trans hWS
  have hclH : CFSG.Open.fusionStronglyClosed
      ((Z.subgroupOf H : Subgroup ↥H) : Set ↥H) (S : Subgroup ↥H) :=
    CFSG.Goldschmidt.stronglyClosed_subgroupOf (p := 2) P hZclP
      (H := H) hZH S hZS
  let Sbar : Sylow 2 (CFSG.GH74.CentralizerBar a) :=
    S.mapSurjective (CFSG.GH74.GLS.TwoThin.barMk_surjective (Y := ↥H))
  have hSbarCoe : (Sbar : Subgroup (CFSG.GH74.CentralizerBar a)) =
      Subgroup.map (CFSG.GH74.GLS.TwoThin.barMk ↥H) (S : Subgroup ↥H) := by
    dsimp [Sbar]
  have hVSbar : V ≤ (Sbar : Subgroup (CFSG.GH74.CentralizerBar a)) := by
    rw [hSbarCoe]
    exact Subgroup.map_mono hZS
  have hclSbar : CFSG.Open.fusionStronglyClosed
      (V : Set (CFSG.GH74.CentralizerBar a))
      (Sbar : Subgroup (CFSG.GH74.CentralizerBar a)) := by
    have h := CFSG.ShultStronglyClosedTI.stronglyClosed_map_surjective
      (p := 2) (G := ↥H) (Y := CFSG.GH74.CentralizerBar a)
      (CFSG.GH74.GLS.TwoThin.barMk ↥H)
      (CFSG.GH74.GLS.TwoThin.barMk_surjective (Y := ↥H))
      S (Z.subgroupOf H) hZS hclH
    simpa [V, Sbar, π, CFSG.GH74.GLS.Th2.Bal.piBar] using h
  have hO : CFSG.Open.goldschmidtOddCore (CFSG.GH74.CentralizerBar a) = ⊥ := by
    have h := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (p := 2) (G := ↥H)
    rw [CFSG.Goldschmidt.goldschmidtOddCore_eq_pPrimeCore (CFSG.GH74.CentralizerBar a)]
    exact h
  have hVne : V ≠ ⊥ := by
    intro hbot
    have hV4' : Nat.card ↥V = 4 := hV4
    rw [hbot, Subgroup.card_bot] at hV4'
    omega
  have hnot : ¬ V ≤ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) := by
    intro hle
    obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := V)).1 hVne
    exact hfaith (v : CFSG.GH74.CentralizerBar a) v.2 (fun h => hv1 (Subtype.ext h))
      (fun l hl => (Subgroup.mem_centralizer_iff.mp (hle v.2) l hl).symm)
  have hLnc : L ≤ Subgroup.normalClosure (V : Set (CFSG.GH74.CentralizerBar a)) :=
    (CFSG.ComponentClassification.GMS78.component_le_normalClosure_or_le_centralizer hL V).resolve_right hnot
  have hVab : IsMulCommutative ↥V := hVElem.toIsMulCommutative
  obtain ⟨hconc, -⟩ :=
    CFSG.ComponentClassification.GMS78.stronglyClosed_components_or_normal
      (H := CFSG.GH74.CentralizerBar a) hO Sbar hVSbar hVab hclSbar
  obtain ⟨htype, hind, hsame⟩ := hconc L hL hLnc
  have hVL : V ≤ L := CFSG.GH74.GLS.NT44.le_of_same_conj_of_faithful hfaith hsame
  have hLn : L.Normal :=
    CFSG.GH74.GLS.NT44.normal_of_isComponent_of_stronglyClosed_le_of_not_le_centralizer
      Sbar hL hVSbar hVL hclSbar hnot
  let α : ↥W →* MulAut (↥L ⧸ Subgroup.center ↥L) :=
    (@CFSG.GH74.GLS.Prop27.actQuot
      (CFSG.GH74.CentralizerBar a) inferInstance L hLn).comp j
  have hinv : ∀ z ∈ α.ker, z ^ 2 = 1 → z = 1 := by
    intro z hz hz2
    have hz2G : (z : G) * (z : G) = 1 := by
      have := congrArg (fun t : ↥W => (t : G)) hz2
      simpa [pow_two] using this
    have hzomega : (z : G) ∈ CFSG.GH74.GLS.omega1 W :=
      Subgroup.subset_closure ⟨z.2, hz2G⟩
    have hzZ : (z : G) ∈ Z := by
      change (z : G) ∈ Subgroup.closure {z : G | z ∈ T ∧ IsConj x z}
      rw [hZomega]
      exact hzomega
    have hjzV : j z ∈ V := by
      dsimp [V, j, π]
      exact Subgroup.mem_map.mpr
        ⟨⟨(z : G), hWH z.2⟩, Subgroup.mem_subgroupOf.mpr hzZ, rfl⟩
    have hzα : CFSG.GH74.GLS.Prop27.actQuot L (j z) = 1 := by
      have := MonoidHom.mem_ker.mp hz
      simpa [α] using this
    have hcomm : ∀ l ∈ L, (j z : CFSG.GH74.CentralizerBar a) * l = l * (j z) :=
      @CFSG.GH74.GLS.Prop27.mul_comm_of_actQuot_eq_one
        (CFSG.GH74.CentralizerBar a) inferInstance L hLn hL.1.1 (j z) hzα
    have hjz : j z = 1 := by
      by_contra h1
      exact hfaith (j z) hjzV h1 hcomm
    exact hj (by simpa only [map_one] using hjz)
  have hX : IsPGroup 2 ↥(⊤ : Subgroup ↥W) :=
    hW2.of_equiv (Subgroup.topEquiv (G := ↥W)).symm
  have hker_top : α.ker ⊓ (⊤ : Subgroup ↥W) = ⊥ :=
    CFSG.StandardType.GGOppRad.ker_inf_eq_bot α hinv hX
  have hker : α.ker = ⊥ := by simpa using hker_top
  have hinj : Function.Injective α := (MonoidHom.ker_eq_bot_iff α).mp hker
  exact ⟨S, hLn, hWS, hVSbar, hclSbar, hLnc, hVL, htype, hind, hsame, hinj⟩

end CFSG.GH74.GLS.NT44

end
