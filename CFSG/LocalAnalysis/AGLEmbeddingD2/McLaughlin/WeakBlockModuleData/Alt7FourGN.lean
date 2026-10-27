module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Alt7FourStepA
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Alt7FourDict
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SylowBaum
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FiveThreeBridge
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.NaturalOn

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules CFSG.AGLEmbedding
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs CFSG.AGLEmbeddingD2.GN
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem exists_nine_le_normalizer_baum_of_four (hX : GNSetting X T) {C₁ : Subgroup X}
    (h1 : C₁ ≤ omegaOneCenterOf T) {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤)
    (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L)
    (hC₁ : ¬ L ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)))
    (eL : ↥L ≃* alternatingGroup (Fin 7)) (HA : Alt7Hyp (alternatingGroup (Fin 7)))
    (hT : gnImg T T ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)))
    {W U : Subgroup X} (hWV : W ≤ gnV T) (hZW : omegaOneCenterOf T ≤ W)
    (hWK : ∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)), ∀ w ∈ W, k * w * k⁻¹ ∈ W)
    (hWU : ⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ ≤ U) (hUV : U ≤ gnV T)
    (hUK : ∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)), ∀ u ∈ U, k * u * k⁻¹ ∈ U)
    (hU16 : Nat.card U = 2 ^ 4) :
    ∃ E : Subgroup (X ⧸ gnC T), E ≤ L ∧ Nat.card E = 9 ∧
      E ≤ gnImg T (Subgroup.normalizer (baum T : Set X)) := by
  classical
  have hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T := CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV_of_le hX.charTwo hQT
  let _ : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  have hVT : gnV T ≤ T := gnV_le_of_le hX.charTwo hQT
  set mk := QuotientGroup.mk' (gnC T) with hmk
  set ρ := gnRep hV with hρ
  have hinj : Function.Injective ρ := gnRep_injective hV
  have hU'16 : Nat.card (modOf hV U) = 16 := by
    rw [card_modOf hV hUV, hU16]; norm_num
  have hU'inv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (modOf hV U) := isInvariant_modOf_of_conj hV L hUK
  have hnt : ∃ l ∈ L, ∃ u ∈ modOf hV U, ρ l u ≠ u := by
    by_contra hno
    push Not at hno
    have hquad : ∀ l₁ ∈ L, ∀ l₂ ∈ L, ∀ w ∈ modOf hV W,
        ρ l₁ (ρ l₂ w - w) = ρ l₂ w - w := fun l₁ hl₁ l₂ hl₂ w hw =>
      hno l₁ hl₁ _ (sub_mem_modOf_of_commutator_le hV L hWV hWU hl₂ hw)
    have htriv := trivial_of_quad ρ eL (modOf hV W) hquad
    apply hC₁
    intro l hl
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective l
    refine ⟨x, ?_, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
    obtain ⟨w, rfl⟩ := exists_elt hV (hWV (hZW (h1 hc)))
    have hw : w ∈ modOf hV W := hZW (h1 hc)
    have := congrArg (elt hV) (htriv _ hl w hw)
    rw [elt_gnRep] at this
    calc elt hV w * x = x * elt hV w * x⁻¹ * x := by rw [this]
      _ = x * elt hV w := by group
  obtain ⟨A₀, hA₀, hAN₀, hLA₀⟩ := exists_offender_of_le hV hVT L hL hJ
  have hfaith : ∀ a ∈ (⊤ : Subgroup (X ⧸ gnC T)), (∀ v, ρ a v = v) → a = 1 :=
    fun a _ h => hinj (by rw [map_one]; exact LinearMap.ext h)
  have hT₁ : IsSylowTwoOf (gnImg T T) (Subgroup.normalizer (L : Set (X ⧸ gnC T))) :=
    CFSG.QuasithinUnique.isSylowTwoOf_of_le
      (CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.isSylowTwoOf_gnImg_top hX) hT
  have hFam : ∀ B ∈ {B : Subgroup (X ⧸ gnC T) |
      ∃ A, IsMaxElemAbelian T A ∧ B = A.map mk}, B ≤ gnImg T T ∧ IsElementaryAbelian 2 ↥B ∧
        IsBestOffenderOn ρ B ⊤ := by
    rintro _ ⟨A, hA, rfl⟩
    have hA2 := isElementaryAbelian_map_mk hA
    refine ⟨Subgroup.map_mono hA.1, hA2, ?_⟩
    have hb := isBestOffender_gnRep_of_le hV hVT hA
    exact (isBestOffender_iff_on ρ _ (fun a _ ha => hfaith a (Subgroup.mem_top a) ha)).mp ⟨hA2, hb⟩
  obtain ⟨-, ℓ, hℓU, hℓfix, E, hEL, hE9, hE⟩ := rep4_of_sixteen ρ hinj eL HA hU'16 hU'inv hnt hT₁ hFam
    ⟨A₀.map mk, ⟨A₀, hA₀, rfl⟩, hLA₀⟩
  set ℓX := subOf hV ℓ with hℓX
  have hℓA : ∀ A, IsMaxElemAbelian T A → ℓX ≤ A := by
    intro A hA v hv
    obtain ⟨w, hw, rfl⟩ := hv
    have hvV := elt_mem hV w
    have hcomm : elt hV w ∈ T ⊓ Subgroup.centralizer (A : Set X) := by
      refine ⟨hVT hvV, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      have h := congrArg (elt hV) (hℓfix (A.map mk) ⟨A, hA, rfl⟩ (mk a) ⟨a, ha, rfl⟩ w hw)
      change elt hV (gnRep hV (QuotientGroup.mk a) w) = elt hV w at h
      rw [elt_gnRep] at h
      calc a * elt hV w = a * elt hV w * a⁻¹ * a := by group
        _ = elt hV w * a := by rw [h]
    rw [eq_omegaOneOf_centralizer hA]
    exact Subgroup.subset_closure ⟨hcomm, hV.2 _ hvV⟩
  have hℓJ : ℓX ≤ omegaOneCenterOf (thompsonJ T) := by
    rw [(omegaOne_centralizer_thompsonJ T).2]
    exact le_iInf₂ fun A hA => hℓA A hA
  set S : Subgroup (X ⧸ gnC T) := gnImg T (T ⊓ Subgroup.centralizer (ℓX : Set X)) with hS
  have hbS : gnImg T (baum T) ≤ S :=
    Subgroup.map_mono (inf_le_inf_left T (Subgroup.centralizer_le hℓJ))
  have hST : S ≤ gnImg T T := Subgroup.map_mono inf_le_left
  have hEN : E ≤ Subgroup.normalizer (S : Set (X ⧸ gnC T)) := by
    have key : ∀ e ∈ E, ∀ s ∈ S, e * s * e⁻¹ ∈ S := by
      intro e he s hs
      obtain ⟨hsT, hsfix⟩ := (mem_gnImg_inf_centralizer_iff hV ℓ s).mp hs
      obtain ⟨h1', h2'⟩ := hE e he s hsT hsfix
      exact (mem_gnImg_inf_centralizer_iff hV ℓ _).mpr ⟨h1', h2'⟩
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨fun hs => key e he s hs, fun hs => ?_⟩
    have := key e⁻¹ (E.inv_mem he) _ hs
    simpa [mul_assoc] using this
  have hEB := (normalizer_le_normalizer_gnImg_baum_of_le hX hbS hST) |>.trans' hEN
  refine ⟨E, hEL, hE9, ?_⟩
  rw [← normalizer_gnImg_baum hX]
  exact hEB

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
