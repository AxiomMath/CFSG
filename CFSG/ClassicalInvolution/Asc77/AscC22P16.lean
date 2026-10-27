module

public import CFSG.ClassicalInvolution.Asc77.AscC22P15
public import CFSG.ClassicalInvolution.Asc77.AscIHSectF
public import CFSG.ClassicalInvolution.Asc77.AscT7JLayer

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected AscE184Sect
open CFSG.ClassicalInvolution.Asc77.T7H

namespace C22P

set_option linter.unusedSectionVars false

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exactImg_conjSub_layer {K : Subgroup G} {y : ↥(exactLayer Ω c)} :
    exactImg Ω c (conjSub (y : G) K) =
      conjSub (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω c)) y)
        (exactImg Ω c K) := by
  have hnc : (y : G) * c * (y : G)⁻¹ = c := mem_centralizer_of_mem_exactLayer
  have h1 : exactCore c (conjSub (y : G) K) = conjSub (y : G) (exactCore c K) := by
    have := exactCore_conjSub (y : G) c K
    rwa [hnc] at this
  unfold exactImg
  rw [h1, ← conjSub_subgroupOf, AscQuot.map_conjSub]

theorem le_sup_oddCoreOf_of_map_eq_top {E S : Subgroup G}
    (htop : (S.subgroupOf E).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥E)) = ⊤) :
    E ≤ S ⊔ oddCoreOf E := by
  intro x hx
  have hx' : QuotientGroup.mk' (classicalInvolutionOddCore ↥E) ⟨x, hx⟩ ∈
      (S.subgroupOf E).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥E)) := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp hx'
  have hmem : s⁻¹ * ⟨x, hx⟩ ∈ classicalInvolutionOddCore ↥E := QuotientGroup.eq.mp hsx
  have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
  have hoc : (s : G)⁻¹ * x ∈ oddCoreOf E := ⟨s⁻¹ * ⟨x, hx⟩, hmem, rfl⟩
  have e : x = (s : G) * ((s : G)⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hsS hoc

end Lift

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}


theorem layer_gen (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : c * c = 1) (hLay : LayerOrthType p f Ω c 6 true)
    {K K' L L' : Subgroup G} {z t b b' y : G}
    (hK : K ∈ tqMembers Ω c) (hK' : K' ∈ tqMembers Ω c) (hL : L ∈ tqMembers Ω c)
    (hL' : L' ∈ tqMembers Ω c)
    (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (hperp : ∀ J ∈ tqMembers Ω c, J ∈ KPerp Ω K → J = K ∨ J = K')
    (htL : IsUniqueInvolution L t) (htL' : IsUniqueInvolution L' t)
    (hzt : z * t = t * z) (htz : t ≠ z)
    {R R' : Subgroup G} (hR : IsSylow2In R (exactCore c K)) (hR' : IsSylow2In R' (exactCore c K'))
    (hRR' : Commutes R R')
    (hb : b ∈ exactCore c K) (hb' : b' ∈ exactCore c K') (ob : b * b = z)
    (hrel : t = b * b' * c) (hy : y ∈ exactLayer Ω c) (hLy : L = conjSub y K)
    (hL'y : L' = conjSub y K') :
    exactLayer Ω c ≤ (L' ⊔ K ⊔ L) ⊔ oddCoreOf (exactLayer Ω c) := by
  classical
  have hcpg := isPGroup_zpowers_of_sq_eq_one hc2
  set E := exactLayer Ω c with hE
  set N₀ := classicalInvolutionOddCore ↥E with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥E
  have hΛ : HypOmegaMod p f (exactPair Ω c) := hypOmegaMod_exactPair hp hq hΩ hcpg
  have hΦ : HypOmegaMod p f (oddQuotientFamily (exactPair Ω c)) :=
    oddQuotHyp p f hp hq ↥E (exactPair Ω c) hΛ N₀ hN₀odd
  have hzK : z ∈ exactCore c K := (isUniqueInvolution_exactCore hp hΩ hcpg hK hz).mem
  have hzE : z ∈ E := exactCore_le_exactLayer hK hzK
  have htL₀ : t ∈ exactCore c L := (isUniqueInvolution_exactCore hp hΩ hcpg hL htL).mem
  have htE : t ∈ E := exactCore_le_exactLayer hL htL₀
  have hbE : b ∈ E := exactCore_le_exactLayer hK hb
  have hb'E : b' ∈ E := exactCore_le_exactLayer hK' hb'
  have hcE : c ∈ E := by
    have : c = (b * b')⁻¹ * t := by rw [hrel]; group
    rw [this]
    exact E.mul_mem (E.inv_mem (E.mul_mem hbE hb'E)) htE
  have hz2 : z * z = 1 := hz.sq
  have ht2 : t * t = 1 := htL.sq
  have hA : exactImg Ω c K ∈ oddQuotientFamily (exactPair Ω c) := exactImg_mem hK
  have hA' : exactImg Ω c K' ∈ oddQuotientFamily (exactPair Ω c) := exactImg_mem hK'
  have hB : exactImg Ω c L ∈ oddQuotientFamily (exactPair Ω c) := exactImg_mem hL
  have hB' : exactImg Ω c L' ∈ oddQuotientFamily (exactPair Ω c) := exactImg_mem hL'
  have hzA := exactImg_isUnique hp hΩ hcpg hK hz hzE
  have hzA' := exactImg_isUnique hp hΩ hcpg hK' hz' hzE
  have htB := exactImg_isUnique hp hΩ hcpg hL htL htE
  have htB' := exactImg_isUnique hp hΩ hcpg hL' htL' htE
  have hne : exactImg Ω c K ≠ exactImg Ω c K' := by
    refine map_ne_of_commutes_sylow (N := N₀) hp hΦ hN₀odd
      (M₁ := (exactCore c K).subgroupOf E) (M₂ := (exactCore c K').subgroupOf E)
      (V₁ := R.subgroupOf E) (V₂ := R'.subgroupOf E)
      ⟨_, exactCore_mem_exactFamily hK, exactCore_le_exactLayer hK, rfl⟩
      (hR.subgroupOf (exactCore_le_exactLayer hK)) (hR'.subgroupOf (exactCore_le_exactLayer hK'))
      ?_
    intro x hx y hy
    exact Subtype.ext (hRR' x (Subgroup.mem_subgroupOf.mp hx) y (Subgroup.mem_subgroupOf.mp hy))
  have hnbA : ∀ M ∈ oddQuotientFamily (exactPair Ω c),
      M ∈ omegaNbr (oddQuotientFamily (exactPair Ω c)) (exactImg Ω c K) → M = exactImg Ω c K' := by
    intro M hM hMn
    obtain ⟨J, hJ, rfl⟩ := exists_exactImg_of_mem hM
    exact T7J.exactImg_nbr_eq_weak hp hq hΩ hcpg hK hperp hJ hMn
  have hbarne : toBar Ω c t htE ≠ toBar Ω c z hzE := fun h =>
    htz (eq_of_toBar_eq htE hzE ht2 hz2 hzt.symm h)
  have hBA : exactImg Ω c L ≠ exactImg Ω c K := by
    intro h
    rw [h] at htB
    exact hbarne (htB.eq hzA)
  have hBA' : exactImg Ω c L ≠ exactImg Ω c K' := by
    intro h
    rw [h] at htB
    exact hbarne (htB.eq hzA')
  have hBB : exactImg Ω c L' ≠ exactImg Ω c K := by
    intro h
    rw [h] at htB'
    exact hbarne (htB'.eq hzA)
  have hBB' : exactImg Ω c L' ≠ exactImg Ω c K' := by
    intro h
    rw [h] at htB'
    exact hbarne (htB'.eq hzA')
  have hBn : exactImg Ω c L ∉ omegaNbr (oddQuotientFamily (exactPair Ω c)) (exactImg Ω c K) :=
    fun h => hBA' (hnbA _ hB h)
  have hBn' : exactImg Ω c L' ∉ omegaNbr (oddQuotientFamily (exactPair Ω c)) (exactImg Ω c K) :=
    fun h => hBB' (hnbA _ hB' h)
  have hgen : omegaGen (oddQuotientFamily (exactPair Ω c)) = ⊤ :=
    omegaGen_quotFamily_eq_top (exactPair Ω c) N₀
      (omegaGen_restrictFamily_eq_top (exactFamily Ω c) E (exactLayer_eq_iSup Ω c).symm)
  obtain ⟨t', n', ht', D, hcard, i, hit, hir⟩ := hLay
  have htn : t' = .PSL ∧ n' = 4 := by
    rcases ht' with h | h | h | h | h | h <;> simp_all
  have hie : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · exact absurd (hit.symm.trans h) (by rw [htn.1]; decide)
  obtain ⟨P⟩ := nonempty_pslLayer_of_lieSystemData D hcard i (hit.trans htn.1)
    (hir.trans htn.2) hie hgen
  obtain ⟨RK, hRK, hKR⟩ := P.fund _ hA
  obtain ⟨RK', hRK', hKR'⟩ := P.fund _ hA'
  obtain ⟨RL, hRL, hLR⟩ := P.fund _ hB
  obtain ⟨RL', hRL', hL'R⟩ := P.fund _ hB'
  have hOK : oddCoreOf (exactImg Ω c K) = ⊥ := PSLLayer.oddCoreOf_fund hp hq P hRK hKR
  have hcomm : Commutes (exactImg Ω c K) (exactImg Ω c K') :=
    commutes_of_twins_bot hΦ hA hA' hne hzA hzA' hOK
  have hcomm' : Commutes (exactImg Ω c L) (exactImg Ω c L') := by
    have h1 : exactImg Ω c L = conjSub (QuotientGroup.mk' N₀ ⟨y, hy⟩) (exactImg Ω c K) := by
      rw [hLy]
      exact exactImg_conjSub_layer (y := ⟨y, hy⟩)
    have h2 : exactImg Ω c L' = conjSub (QuotientGroup.mk' N₀ ⟨y, hy⟩) (exactImg Ω c K') := by
      rw [hL'y]
      exact exactImg_conjSub_layer (y := ⟨y, hy⟩)
    rw [h1, h2]
    exact hcomm.conjSub _
  have heC : toBar Ω c c hcE ∈ Subgroup.center (↥E ⧸ N₀) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective N₀ y
    show QuotientGroup.mk' N₀ y' * QuotientGroup.mk' N₀ ⟨c, hcE⟩ =
      QuotientGroup.mk' N₀ ⟨c, hcE⟩ * QuotientGroup.mk' N₀ y'
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (exactLayer_le_centralizer Ω c y'.2)
  have hrel' : toBar Ω c t htE = toBar Ω c b hbE * toBar Ω c b' hb'E * toBar Ω c c hcE := by
    have h1 : (⟨t, htE⟩ : ↥E) = ⟨b, hbE⟩ * ⟨b', hb'E⟩ * ⟨c, hcE⟩ := Subtype.ext hrel
    unfold toBar
    rw [h1, map_mul, map_mul]
  have ob₁ : toBar Ω c b hbE * toBar Ω c b hbE = toBar Ω c z hzE := by
    have h1 : (⟨b, hbE⟩ : ↥E) * ⟨b, hbE⟩ = ⟨z, hzE⟩ := Subtype.ext ob
    unfold toBar
    rw [← map_mul, h1]
  have hne₁ : exactImg Ω c K ≠ exactImg Ω c L := hBA.symm
  have hnc₁ : ¬ Commutes (exactImg Ω c K) (exactImg Ω c L) := fun h =>
    hBn (MuTab.mem_omegaNbr_of_commutes hB hBA h)
  have hne₂ : exactImg Ω c K ≠ exactImg Ω c L' := hBB.symm
  have hnc₂ : ¬ Commutes (exactImg Ω c K) (exactImg Ω c L') := fun h =>
    hBn' (MuTab.mem_omegaNbr_of_commutes hB' hBB h)
  have hsup := sup_eq_of_chain hp hq P hRK hRL hRL' hKR hKR' hLR hL'R hzA htB htB'
    (mem_exactImg hb hbE) (mem_exactImg hb' hb'E) ob₁ hcomm hcomm' (by rw [hgen]; trivial)
    (fun y _ => (Subgroup.mem_center_iff.mp heC y).symm) hrel' hne₁ hnc₁ hne₂ hnc₂
  rw [hgen] at hsup
  set S : Subgroup G := exactCore c L' ⊔ exactCore c K ⊔ exactCore c L with hS
  have hLS : exactCore c L ≤ S := le_sup_right
  have hKS : exactCore c K ≤ S := le_sup_right.trans le_sup_left
  have hL'S : exactCore c L' ≤ S := le_sup_left.trans le_sup_left
  have hmono : ∀ {M : Subgroup G}, M ≤ S → M.subgroupOf E ≤ S.subgroupOf E := fun hM x hx =>
    Subgroup.mem_subgroupOf.mpr (hM (Subgroup.mem_subgroupOf.mp hx))
  have m₁ : exactImg Ω c L' ≤ (S.subgroupOf E).map (QuotientGroup.mk' N₀) := by
    unfold exactImg
    exact Subgroup.map_mono (hmono hL'S)
  have m₂ : exactImg Ω c K ≤ (S.subgroupOf E).map (QuotientGroup.mk' N₀) := by
    unfold exactImg
    exact Subgroup.map_mono (hmono hKS)
  have m₃ : exactImg Ω c L ≤ (S.subgroupOf E).map (QuotientGroup.mk' N₀) := by
    unfold exactImg
    exact Subgroup.map_mono (hmono hLS)
  have htop : (S.subgroupOf E).map (QuotientGroup.mk' N₀) = ⊤ := by
    rw [eq_top_iff, ← hsup]
    exact sup_le (sup_le m₁ m₂) m₃
  have hlift := le_sup_oddCoreOf_of_map_eq_top htop
  refine hlift.trans (sup_le_sup_right ?_ _)
  exact sup_le_sup (sup_le_sup (exactCore_le_left c L') (exactCore_le_left c K))
    (exactCore_le_left c L)

end Main

end C22P

end CFSG.ClassicalInvolution.Asc77
