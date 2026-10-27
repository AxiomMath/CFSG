module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFOTwo
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFBest
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem L34FF.Core.cover_omegaOneCenterOf (hFF : CitedFFL34BestOffender)
    (hd : L34FF.Core H R Rbar K) (hL : IsLinThreeFour K) (hne : H ≠ ⊤)
    (hK : Open.IsKProper G) {V : Subgroup G} {D₀ : Subgroup G} (hD₀H : D₀ ≤ H)
    (hV : IsSylowTwoOf V D₀) (hΩ : omegaOneCenterOf V ≤ omegaOneCenterOf (pCoreOf 2 H))
    (hS : pCoreOf 2 H ≤ V)
    (hpc : ∀ {W Z : Subgroup G},
      L34FF.threeComp H R K ⊔ V ≤ Subgroup.normalizer (W : Set G) →
      V ≤ Subgroup.centralizer (Z : Set G) →
      (∀ D : Subgroup G, L34FF.threeComp H R K ⊔ V ≤ Subgroup.normalizer (D : Set G) →
        D ≤ Subgroup.centralizer (Z : Set G) → D ≤ Subgroup.centralizer (W : Set G)) →
      Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (Z : Set G) →
      L34FF.threeComp H R K ⊓ Subgroup.centralizer (W : Set G) ≤ L34FF.threeCompCore H R K →
      CFSG.pCore 2 (autOn (L34FF.threeComp H R K ⊔ V) W) = ⊥)
    {A : Subgroup G} (hA : IsMaxElemAbelian V A)
    {a : G} (haA : a ∈ A) (haC : ∀ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ ∉
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3))) :
    ∀ k ∈ K, ∃ x ∈ H ⊓ Subgroup.normalizer (omegaOneCenterOf V : Set G), ∃ hx : x ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨x, hx⟩ = k := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set L := L34FF.threeComp H R K with hLdef
  set Y := L34FF.threeCompCore H R K with hYdef
  set X := L ⊔ V with hXdef
  set Z := omegaOneCenterOf V with hZdef
  set W := nclIn X Z with hWdef
  have hLH : L ≤ H := L34FF.threeComp_le
  have hVH : V ≤ H := hV.1.trans hD₀H
  have hXH : X ≤ H := sup_le hLH hVH
  have hXtop : X ≠ ⊤ := fun h => hne (top_le_iff.mp (h ▸ hXH))
  have hLX : L ≤ X := le_sup_left
  have hAX : A ≤ X := hA.1.trans le_sup_right
  have hZV : Z ≤ V := Setup.omegaOneCenterOf_le V
  have hZW : Z ≤ W := le_nclIn (hZV.trans le_sup_right)
  have hXW : X ≤ Subgroup.normalizer (W : Set G) := le_normalizer_nclIn X Z
  have hWΩ : W ≤ omegaOneCenterOf (pCoreOf 2 H) :=
    L34FF.nclIn_le_of_le_normalizer hΩ
      (hXH.trans (L34FF.le_normalizer_omegaOneCenterOf_pCoreOf_two H))
  have hWe : IsElemAbelian 2 W :=
    L34FF.isElemAbelian_mono_two hWΩ (B2F.isElemAbelian_omegaOneCenterOf _)
  have hWV : W ≤ V :=
    hWΩ.trans ((Setup.omegaOneCenterOf_le _).trans hS)
  have hVZ : V ≤ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨⟨-, hxC⟩, -⟩
    exact hxC
  have hLLC : L ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) :=
    L34FF.le_normalizer_inf_of_normalizes_both (hLH.trans L34FF.le_normalizer_threeComp)
      (hLX.trans (L34FF.le_normalizer_centralizer_of_normalizes hXW))
  have hcovL : ∀ k ∈ K, ∃ l ∈ L, ∃ hl : l ∈ H, π ⟨l, hl⟩ = k := by
    intro k hk
    have hk' : k ∈ (L.subgroupOf H).map π := by rw [hd.map_threeComp]; exact hk
    obtain ⟨⟨l, hlH⟩, hl, rfl⟩ := hk'
    exact ⟨l, hl, hlH, rfl⟩
  rcases hd.threeComp_dichotomy (N := L ⊓ Subgroup.centralizer (W : Set G)) inf_le_left hLLC
    with hβ | hβ
  · exfalso
    let _ : CommGroup W := commGroupOfElemAbelian hWe
    let _ : Module (ZMod 2) (Additive W) := L34FF.moduleOfSq fun w => Subtype.ext (hWe.2 w w.2)
    set f := L34FF.conjOnto W X hXW with hf
    have hLn : ((L.subgroupOf X).map f).Normal :=
      Subgroup.Normal.map (Subgroup.normal_subgroupOf_of_le_normalizer
        (hXH.trans L34FF.le_normalizer_threeComp)) f (L34FF.conjOnto_surjective hXW)
    have hLperf : ⁅(L.subgroupOf X).map f, (L.subgroupOf X).map f⁆ = (L.subgroupOf X).map f := by
      rw [← Subgroup.map_commutator]
      congr 1
      apply Subgroup.map_injective X.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLX]
      exact hd.commutator_threeComp
    have hcen := hFF (autOn X W) (Additive W) ((L34FF.autFTwoRep W).comp (autOn X W).subtype)
      (L34FF.autFTwoRep_comp_injective hWe)
      (L34FF.isKGroup_autOn hXW hK hXtop)
      (hpc hXW hVZ (fun D hD hDZ => L34FF.le_centralizer_nclIn hD hDZ)
        (Subgroup.centralizer_le hZW) hβ)
      ((L.subgroupOf X).map f) hLn hLperf (hd.isLinThreeFour_map_conjOnto hL hXW hLX hβ)
      ((A.subgroupOf X).map f) (L34FF.isElementaryAbelian_map_conjOnto hXW hA.2.1)
      (L34FF.isBestOffender_map_conjOnto hXW hWe hWV hA hAX)
    have haH : a ∈ H := hVH (hA.1 haA)
    apply haC haH
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨l, hl, hlH, rfl⟩ := hcovL k hk
    have h1 := Subgroup.mem_centralizer_iff.mp (hcen ⟨⟨a, hAX haA⟩, haA, rfl⟩) _
      ⟨⟨l, hLX hl⟩, hl, rfl⟩
    have h1' : f ⟨l, hLX hl⟩ * f ⟨a, hAX haA⟩ = f ⟨a, hAX haA⟩ * f ⟨l, hLX hl⟩ := h1
    have hmemX : a * l * a⁻¹ * l⁻¹ ∈ X :=
      X.mul_mem (X.mul_mem (X.mul_mem (hAX haA) (hLX hl)) (X.inv_mem (hAX haA)))
        (X.inv_mem (hLX hl))
    have h2 : f ⟨a * l * a⁻¹ * l⁻¹, hmemX⟩ = 1 := by
      have e : (⟨a * l * a⁻¹ * l⁻¹, hmemX⟩ : X) =
          ⟨a, hAX haA⟩ * ⟨l, hLX hl⟩ * (⟨a, hAX haA⟩ : X)⁻¹ * (⟨l, hLX hl⟩ : X)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← h1', mul_inv_cancel_right,
        mul_inv_cancel]
    have h3 : a * l * a⁻¹ * l⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp (L34FF.le_normalizer_threeComp haH) l).mp hl)
        (L.inv_mem hl)
    have h4 := (hβ ⟨h3, (L34FF.conjOnto_eq_one_iff hXW _).mp h2⟩).2
    have hmem : a * l * a⁻¹ * l⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem haH hlH) (H.inv_mem haH)) (H.inv_mem hlH)
    have h5 := (mk'_primeComplementCore_eq_one_iff 3 ⟨_, hmem⟩).mpr h4
    have e : (⟨a * l * a⁻¹ * l⁻¹, hmem⟩ : H) =
        ⟨a, haH⟩ * ⟨l, hlH⟩ * (⟨a, haH⟩ : H)⁻¹ * (⟨l, hlH⟩ : H)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h5
    have h6 := mul_inv_eq_one.mp h5
    rw [mul_inv_eq_iff_eq_mul] at h6
    exact h6.symm
  · intro k hk
    obtain ⟨l, hl, hlH, rfl⟩ := hcovL k hk
    refine ⟨l, ⟨hlH, ?_⟩, hlH, rfl⟩
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hZW (hβ hl).2)

theorem D1OneSmallData.cover_omegaOneCenterOf (hFF : CitedFFL34BestOffender)
    (hd : D1OneSmallData 3 P M H R Rbar K) (hL : IsLinThreeFour K) {V : Subgroup G}
    (hV : IsSylowTwoOf V (GLBPrimeCore 3 (H ⊓ M))) {A : Subgroup G} (hA : IsMaxElemAbelian V A)
    {a : G} (haA : a ∈ A) (haC : ∀ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ ∉
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3))) :
    ∀ k ∈ K, ∃ x ∈ H ⊓ Subgroup.normalizer (omegaOneCenterOf V : Set G), ∃ hx : x ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨x, hx⟩ = k :=
  hd.toL34FFCore.cover_omegaOneCenterOf hFF hL hd.cfg.ext.toD1Escape.ne_top hd.cfg.glob.kProper
    ((glbPrimeCore_le 3 _).trans inf_le_left) hV (hd.omegaOneCenterOf_le_twoCore hV)
    (hd.twoCore_le_of_isSylowTwoOf hV)
    (fun hXW hVZ hW hZW hβ => hd.pCore_two_autOn_eq_bot hL hV hXW hVZ hW hZW hβ) hA haA haC

end CFSG.AGLEmbedding
