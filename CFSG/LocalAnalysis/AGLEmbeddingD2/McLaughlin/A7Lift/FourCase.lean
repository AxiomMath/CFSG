module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Lift.BaumNormal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Lift.FourPermData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Lift.StepNonsolv
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7FourNorm
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FiveThreeBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Alt7FourDict
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Alt7FourRep
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Alt7FourU
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Lift

open Module CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  CFSG.AGLEmbeddingD2.GN CFSG.AGLEmbeddingD2.McLaughlin.A7Six Equiv Equiv.Perm
open scoped commutatorElement Pointwise

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}

private theorem four_nontrivial (hX : GNSetting X T) (hV : IsElemAbelian 2 (gnV T))
    [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]
    {C₁ : Subgroup X} (h1 : C₁ ≤ omegaOneCenterOf T)
    (eL : ↥L ≃* alternatingGroup (Fin 7))
    {W U : Subgroup X} (hWV : W ≤ gnV T) (hZW : omegaOneCenterOf T ≤ W)
    (hWU : ⁅W, lT T L⁆ ≤ U)
    (hC₁ : ¬ L ≤ gnImg T (Subgroup.centralizer (C₁ : Set X))) :
    ∃ l ∈ L, ∃ u ∈ FiveThreeAlt.modOf hV U, gnRep hV l u ≠ u := by
  classical
  by_contra hno
  push Not at hno
  have hquad : ∀ l₁ ∈ L, ∀ l₂ ∈ L, ∀ w ∈ FiveThreeAlt.modOf hV W,
      gnRep hV l₁ (gnRep hV l₂ w - w) = gnRep hV l₂ w - w := fun l₁ hl₁ l₂ hl₂ w hw =>
    hno l₁ hl₁ _ (sub_mem_modOf_of_commutator_le hV L hWV hWU hl₂ hw)
  have htriv := trivial_of_quad (gnRep hV) eL (FiveThreeAlt.modOf hV W) hquad
  apply hC₁
  intro l hl
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective l
  refine ⟨x, ?_, rfl⟩
  refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
  obtain ⟨w, rfl⟩ := exists_elt hV (hWV (hZW (h1 hc)))
  have hw : w ∈ FiveThreeAlt.modOf hV W := hZW (h1 hc)
  have := congrArg (elt hV) (htriv _ hl w hw)
  rw [elt_gnRep] at this
  calc elt hV w * x = x * elt hV w * x⁻¹ * x := by rw [this]
    _ = x * elt hV w := by group

private theorem four_comm (hX : GNSetting X T) (hV : IsElemAbelian 2 (gnV T))
    [Module (ZMod 2) (Additive (IntMod (gnV T) hV))] (hL : IsComponentOf L ⊤)
    (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) (eL : ↥L ≃* alternatingGroup (Fin 7))
    {U : Subgroup X} (hUV : U ≤ gnV T)
    (hUK : ∀ k ∈ lT T L, ∀ u ∈ U, k * u * k⁻¹ ∈ U) (hU16 : Nat.card U = 2 ^ 4)
    (hnt : ∃ l ∈ L, ∃ u ∈ FiveThreeAlt.modOf hV U, gnRep hV l u ≠ u) :
    commOn (gnRep hV) L ⊤ = FiveThreeAlt.modOf hV U ∧
      fixOn (gnRep hV) L (FiveThreeAlt.modOf hV U) = ⊥ := by
  classical
  have hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hX.sylow
  have hVT : gnV T ≤ T := gnV_le_of_le hX.charTwo hQT
  have hU'16 : Nat.card (FiveThreeAlt.modOf hV U) = 16 := by
    rw [FiveThreeAlt.card_modOf hV hUV, hU16]
    norm_num
  have hU'inv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (gnRep hV) L (FiveThreeAlt.modOf hV U) :=
    isInvariant_modOf_of_conj hV L hUK
  obtain ⟨A₀, hA₀, hAN₀, hLA₀⟩ := exists_offender_of_le (hV := hV) hVT L hL hJ
  have hinj : Function.Injective (gnRep hV) := gnRep_injective hV
  have hfaith : ∀ a ∈ (⊤ : Subgroup (X ⧸ gnC T)), (∀ v, gnRep hV a v = v) → a = 1 :=
    fun a _ h => hinj (by rw [map_one]; exact LinearMap.ext h)
  have hA₀b : IsBestOffenderOn (gnRep hV) (A₀.map (QuotientGroup.mk' (gnC T))) ⊤ :=
    (isBestOffender_iff_on (gnRep hV) _ (fun a _ ha => hfaith a (Subgroup.mem_top a) ha)).mp
      ⟨isElementaryAbelian_map_mk hA₀, isBestOffender_gnRep_of_le (hV := hV) hVT hA₀⟩
  exact commOn_eq_of_card_sixteen (gnRep hV) hinj eL (isElementaryAbelian_map_mk hA₀) hAN₀
    hLA₀ hA₀b hU'16 hU'inv hnt

private theorem four_nV (hV : IsElemAbelian 2 (gnV T))
    [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]
    {U : Subgroup X} (hUV : U ≤ gnV T) (hU16 : Nat.card U = 2 ^ 4)
    (hcomm : commOn (gnRep hV) L ⊤ = FiveThreeAlt.modOf hV U)
    (hfix : fixOn (gnRep hV) L (FiveThreeAlt.modOf hV U) = ⊥) :
    nV T L = U ∧ nV T L ≠ ⊥ ∧
      nV T L ⊓ Subgroup.centralizer (lT T L : Set X) = ⊥ := by
  classical
  have hNV : nV T L = U := by
    have h1 : subOf hV (commOn (gnRep hV) L ⊤) = nV T L := subOf_commOn (hV := hV) L
    rw [hcomm, subOf_modOf hV hUV] at h1
    exact h1.symm
  have hne : nV T L ≠ ⊥ := by
    rw [hNV]
    intro h
    have hcard := hU16
    rw [h, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hC : nV T L ⊓ Subgroup.centralizer (lT T L : Set X) = ⊥ := by
    rw [hNV]
    have hbot : subOf hV (⊥ : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))) = ⊥ := by
      ext g
      rw [mem_subOf]
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [Submodule.mem_bot] at hw
        rw [Subgroup.mem_bot, hw, elt_zero]
      · intro hg
        rw [Subgroup.mem_bot] at hg
        exact ⟨0, Submodule.zero_mem _, by rw [hg, elt_zero]⟩
    have hf := subOf_fixOn (hV := hV) L (FiveThreeAlt.modOf hV U)
    rw [hfix, hbot, subOf_modOf hV hUV] at hf
    exact hf.symm
  exact ⟨hNV, hne, hC⟩

private theorem submodule_irreducible_of_commOn {Γ W : Type} [Group Γ] [Finite Γ]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) Γ W)
    (hρ : Function.Injective ρ) {L : Subgroup Γ} (eL : ↥L ≃* alternatingGroup (Fin 7))
    {A : Subgroup Γ} (hA2 : CFSG.IsElementaryAbelian 2 A)
    (hAN : A ≤ Subgroup.normalizer (L : Set Γ)) (hLA : ⁅L, A⁆ = L)
    (hb : IsBestOffenderOn ρ A ⊤) {Q : Submodule (ZMod 2) W}
    (hcomm : commOn ρ L ⊤ = Q) (hfix : fixOn ρ L Q = ⊥)
    (ρN : Representation (ZMod 2) ↥(Subgroup.normalizer (L : Set Γ)) ↥Q)
    (hρN : ∀ (s : ↥(Subgroup.normalizer (L : Set Γ))) (u : ↥Q),
      ((ρN s u : ↥Q) : W) = ρ (s : Γ) (u : W)) :
    ∀ M : Submodule (ZMod 2) ↥Q,
      (∀ l ∈ L.subgroupOf (Subgroup.normalizer (L : Set Γ)), ∀ q ∈ M, ρN l q ∈ M) →
      M = ⊥ ∨ M = ⊤ := by
  classical
  obtain ⟨hirr0, -⟩ := a7_commOn_quot ρ hρ eL hA2 hAN hLA hb
  rw [hcomm, hfix] at hirr0
  intro M hM
  set Z : Submodule (ZMod 2) W := M.map Q.subtype with hZ
  have hZinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Z := by
    rintro l hl _ ⟨q, hq, rfl⟩
    have hln : l ∈ Subgroup.normalizer (L : Set Γ) := Subgroup.le_normalizer hl
    exact ⟨ρN ⟨l, hln⟩ q, hM ⟨l, hln⟩ (Subgroup.mem_subgroupOf.2 hl) q hq,
      hρN ⟨l, hln⟩ q⟩
  have hZU : Z ≤ Q := by rintro _ ⟨q, -, rfl⟩; exact q.2
  rcases hirr0 Z hZinv bot_le hZU with hZbot | hZtop
  · left
    refine eq_bot_iff.2 fun q hq => ?_
    have hmem : (q : W) ∈ Z := ⟨q, hq, rfl⟩
    rw [hZbot, Submodule.mem_bot] at hmem
    rw [Submodule.mem_bot]
    exact Subtype.ext hmem
  · right
    refine eq_top_iff.2 fun q _ => ?_
    have hmem : (q : W) ∈ Z := by rw [hZtop]; exact q.2
    obtain ⟨q', hq', hqq⟩ := hmem
    have : q' = q := Subtype.ext hqq
    rwa [← this]

private theorem four_normalizer_decomp
    {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q] [Finite Q]
    (ρN : Representation (ZMod 2) ↥(nLs T L) Q)
    (eL : ↥L ≃* alternatingGroup (Fin 7)) (hdim : finrank (ZMod 2) Q = 4)
    (hirr : ∀ M : Submodule (ZMod 2) Q,
      (∀ l ∈ L.subgroupOf (nLs T L), ∀ q ∈ M, ρN l q ∈ M) → M = ⊥ ∨ M = ⊤) :
    ∀ y ∈ nLs T L, ∃ l ∈ L, ∀ m ∈ L, (l⁻¹ * y) * m = m * (l⁻¹ * y) := by
  classical
  intro y hy
  let N : Subgroup (X ⧸ gnC T) := nLs T L
  have hyN : y ∈ N := hy
  let L' : Subgroup ↥N := L.subgroupOf N
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hnorm : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).2 le_rfl
  let eL' : ↥L' ≃* alternatingGroup (Fin 7) := (Subgroup.subgroupOfEquivOfLe hLN).trans eL
  obtain ⟨l', hl', hall⟩ := a7_four_normalizer ρN eL' hdim hirr (g := ⟨y, hyN⟩)
    (by rw [Subgroup.normalizer_eq_top_iff.mpr hnorm]; trivial)
  refine ⟨((l' : ↥N) : X ⧸ gnC T), Subgroup.mem_subgroupOf.1 hl', fun m hm => ?_⟩
  have hm' : (⟨m, hLN hm⟩ : ↥N) ∈ L' := Subgroup.mem_subgroupOf.2 hm
  have h := hall ⟨m, hLN hm⟩ hm'
  simpa using congrArg (fun z : ↥N => (z : X ⧸ gnC T)) h

private theorem four_centralizer_action (hV : IsElemAbelian 2 (gnV T))
    [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]
    {Q : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))}
    (ρN : Representation (ZMod 2) ↥(nLs T L) ↥Q)
    (hρN : ∀ (s : ↥(nLs T L)) (u : ↥Q),
      ((ρN s u : ↥Q) : Additive (IntMod (gnV T) hV)) =
        gnRep hV (s : X ⧸ gnC T) (u : Additive (IntMod (gnV T) hV)))
    (eL : ↥L ≃* alternatingGroup (Fin 7)) (hdim : finrank (ZMod 2) ↥Q = 4)
    (hirr : ∀ M : Submodule (ZMod 2) ↥Q,
      (∀ l ∈ L.subgroupOf (nLs T L), ∀ q ∈ M, ρN l q ∈ M) → M = ⊥ ∨ M = ⊤)
    (hsub : subOf hV Q = nV T L) (g : X)
    (hg : ∀ l ∈ L, QuotientGroup.mk' (gnC T) g * l = l * QuotientGroup.mk' (gnC T) g) :
    ∀ u ∈ nV T L, g * u * g⁻¹ = u := by
  classical
  let N : Subgroup (X ⧸ gnC T) := nLs T L
  have hgN : QuotientGroup.mk' (gnC T) g ∈ N := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change (QuotientGroup.mk' (gnC T) g) * x * (QuotientGroup.mk' (gnC T) g)⁻¹ ∈ L
      have hx' : (QuotientGroup.mk' (gnC T) g) * x * (QuotientGroup.mk' (gnC T) g)⁻¹ = x := by
        rw [hg x hx]
        group
      rw [hx']
      exact hx
    · intro x hx
      refine ⟨x, hx, ?_⟩
      change (QuotientGroup.mk' (gnC T) g) * x * (QuotientGroup.mk' (gnC T) g)⁻¹ = x
      rw [hg x hx]
      group
  let L' : Subgroup ↥N := L.subgroupOf N
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hnorm : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).2 le_rfl
  let eL' : ↥L' ≃* alternatingGroup (Fin 7) := (Subgroup.subgroupOfEquivOfLe hLN).trans eL
  have hc' : ∀ l ∈ L', (⟨QuotientGroup.mk' (gnC T) g, hgN⟩ : ↥N) * l =
      l * ⟨QuotientGroup.mk' (gnC T) g, hgN⟩ := by
    intro l hl
    apply Subtype.ext
    exact hg ((l : ↥N) : X ⧸ gnC T) (Subgroup.mem_subgroupOf.1 hl)
  have h1 : ρN ⟨QuotientGroup.mk' (gnC T) g, hgN⟩ = 1 :=
    a7_four_centralizer_trivial ρN eL' hdim hirr hc'
  intro u hu
  have hu' : u ∈ subOf hV Q := by
    rw [hsub]
    exact hu
  obtain ⟨w, hw, hwu⟩ := (mem_subOf (hV := hV)).1 hu'
  have h2 : ρN ⟨QuotientGroup.mk' (gnC T) g, hgN⟩ ⟨w, hw⟩ = ⟨w, hw⟩ := by
    rw [h1]
    rfl
  have h3 : gnRep hV (QuotientGroup.mk' (gnC T) g) w = w := by
    have hval := hρN ⟨QuotientGroup.mk' (gnC T) g, hgN⟩ ⟨w, hw⟩
    rw [h2] at hval
    exact hval.symm
  rw [← hwu]
  calc g * elt hV w * g⁻¹ = elt hV (gnRep hV (QuotientGroup.mk' (gnC T) g) w) :=
        (elt_gnRep hV g w).symm
    _ = elt hV w := congrArg (elt hV) h3

theorem four_facts (hX : GNSetting X T) {C₁ : Subgroup X} (h1 : C₁ ≤ omegaOneCenterOf T)
    (hL : IsComponentOf L ⊤) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L)
    (hC₁ : ¬ L ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)))
    (eL : ↥L ≃* alternatingGroup (Fin 7))
    {W U : Subgroup X} (hWV : W ≤ gnV T) (hZW : omegaOneCenterOf T ≤ W)
    (hWK : ∀ k ∈ lT T L, ∀ w ∈ W, k * w * k⁻¹ ∈ W) (hWU : ⁅W, lT T L⁆ ≤ U) (hUV : U ≤ gnV T)
    (hUK : ∀ k ∈ lT T L, ∀ u ∈ U, k * u * k⁻¹ ∈ U) (hU16 : Nat.card U = 2 ^ 4) :
    nV T L ≠ ⊥ ∧ nV T L ⊓ Subgroup.centralizer (lT T L : Set X) = ⊥ ∧
      (∀ g : X, (∀ l ∈ L, QuotientGroup.mk' (gnC T) g * l = l * QuotientGroup.mk' (gnC T) g) →
        ∀ u ∈ nV T L, g * u * g⁻¹ = u) ∧
      ∀ y ∈ nLs T L, ∃ l ∈ L, ∀ m ∈ L, (l⁻¹ * y) * m = m * (l⁻¹ * y) := by
  classical
  have hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hX.sylow
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV_of_le hX.charTwo hQT
  let _ : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  have hVT : gnV T ≤ T := gnV_le_of_le hX.charTwo hQT
  set ρ := gnRep hV with hρ
  have hinj : Function.Injective ρ := gnRep_injective hV
  have hnt := four_nontrivial (hX := hX) (hV := hV) (L := L) h1 eL hWV hZW hWU hC₁
  obtain ⟨hcomm, hfix⟩ := four_comm (hX := hX) (hV := hV) (L := L) hL hJ eL hUV hUK hU16 hnt
  obtain ⟨hNV, hne, hC⟩ := four_nV (hV := hV) (L := L) hUV hU16 hcomm hfix
  obtain ⟨A₀, hA₀, hAN₀, hLA₀⟩ := exists_offender_of_le (hV := hV) hVT L hL hJ
  have hfaith : ∀ a ∈ (⊤ : Subgroup (X ⧸ gnC T)), (∀ v, ρ a v = v) → a = 1 :=
    fun a _ h => hinj (by rw [map_one]; exact LinearMap.ext h)
  have hA₀b : IsBestOffenderOn ρ (A₀.map (QuotientGroup.mk' (gnC T))) ⊤ :=
    (isBestOffender_iff_on ρ _ (fun a _ ha => hfaith a (Subgroup.mem_top a) ha)).mp
      ⟨isElementaryAbelian_map_mk hA₀, isBestOffender_gnRep_of_le (hV := hV) hVT hA₀⟩
  have hQ16 : Nat.card (FiveThreeAlt.modOf hV U) = 16 := by
    rw [FiveThreeAlt.card_modOf hV hUV, hU16]
    norm_num
  have hUN : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (nLs T L) (FiveThreeAlt.modOf hV U) := by
    rw [← hcomm]
    exact CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isInvariant_commOn_top ρ le_rfl
  let N : Subgroup (X ⧸ gnC T) := nLs T L
  let L' : Subgroup ↥N := L.subgroupOf N
  let eL' : ↥L' ≃* alternatingGroup (Fin 7) :=
    (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := L))).trans eL
  let ρN : Representation (ZMod 2) ↥N ↥(FiveThreeAlt.modOf hV U) :=
    restRep ρ (FiveThreeAlt.modOf hV U) N hUN
  have hρN : ∀ (s : ↥N) (u : ↥(FiveThreeAlt.modOf hV U)),
      ((ρN s u : ↥(FiveThreeAlt.modOf hV U)) : Additive (IntMod (gnV T) hV)) =
        ρ (s : X ⧸ gnC T) (u : Additive (IntMod (gnV T) hV)) := fun _ _ => rfl
  have hirr := submodule_irreducible_of_commOn (Q := FiveThreeAlt.modOf hV U) ρ hinj eL
    (isElementaryAbelian_map_mk hA₀) hAN₀ hLA₀ hA₀b hcomm hfix ρN hρN
  have hdim : finrank (ZMod 2) ↥(FiveThreeAlt.modOf hV U) = 4 :=
    finrank_eq_four_of_card_sixteen hQ16
  have hsub : subOf hV (FiveThreeAlt.modOf hV U) = nV T L := by
    rw [← hcomm, subOf_commOn (hV := hV)]
  exact ⟨hne, hC, fun g hg => four_centralizer_action hV ρN hρN eL hdim hirr hsub g hg,
    four_normalizer_decomp ρN eL hdim hirr⟩


namespace SevenCtx0

private theorem θs_mem_alternating (c : SevenCtx0 T L)
    (hinner : ∀ y ∈ nLs T L, ∃ l ∈ L, ∀ m ∈ L, (l⁻¹ * y) * m = m * (l⁻¹ * y))
    {y : X ⧸ gnC T} (hy : y ∈ nLs T L) : c.θs ⟨y, hy⟩ ∈ alternatingGroup (Fin 7) := by
  obtain ⟨l, hlL, hcent⟩ := hinner y hy
  have hln : l ∈ nLs T L := Subgroup.le_normalizer hlL
  have hkn : l⁻¹ * y ∈ nLs T L := (nLs T L).mul_mem ((nLs T L).inv_mem hln) hy
  have hθk : c.θs ⟨l⁻¹ * y, hkn⟩ = 1 := by
    rw [c.hθs1]
    intro m hm
    change (l⁻¹ * y) * m * (l⁻¹ * y)⁻¹ = m
    rw [hcent m hm]
    group
  have hprod : (⟨y, hy⟩ : ↥(nLs T L)) = ⟨l, hln⟩ * ⟨l⁻¹ * y, hkn⟩ := by
    ext
    simp [mul_assoc]
  rw [hprod, map_mul, hθk, mul_one, c.θs_of_mem_L hlL]
  exact (c.eL ⟨l, hlL⟩).2

private theorem img_le_alternating (c : SevenCtx0 T L)
    (hinner : ∀ y ∈ nLs T L, ∃ l ∈ L, ∀ m ∈ L, (l⁻¹ * y) * m = m * (l⁻¹ * y))
    {R : Subgroup X} (hRL : R ≤ nL T L) : c.img R ≤ alternatingGroup (Fin 7) := by
  have hRs : R.map (QuotientGroup.mk' (gnC T)) ≤ nLs T L := by
    rintro _ ⟨r, hr, rfl⟩
    exact hRL hr
  rw [← c.imgS_map R hRL]
  rintro σ ⟨y, hy, rfl⟩
  exact θs_mem_alternating c hinner (hRs hy)

private theorem card_img_eq_eight (c : SevenCtx0 T L) (hX : GNSetting X T)
    (hL : IsComponentOf L ⊤)
    (hinner : ∀ y ∈ nLs T L, ∃ l ∈ L, ∀ m ∈ L, (l⁻¹ * y) * m = m * (l⁻¹ * y)) :
    Nat.card (c.img (T ⊓ nL T L)) = 8 ∧
      c.img (T ⊓ nL T L) = c.img (T ⊓ lT T L) := by
  have hRL : T ⊓ nL T L ≤ nL T L := inf_le_right
  have hRT : T ⊓ nL T L ≤ T := inf_le_left
  obtain ⟨hcardS, hSA⟩ := c.card_img_inf_lT hX hL
  have hAnL : T ⊓ lT T L ≤ nL T L := fun x hx =>
    Subgroup.mem_comap.2 (Subgroup.le_normalizer hx.2)
  have hTR : T ⊓ lT T L ≤ T ⊓ nL T L := le_inf inf_le_left hAnL
  have hSle : c.img (T ⊓ lT T L) ≤ c.img (T ⊓ nL T L) := by
    intro σ hσ
    obtain ⟨t, ht, htθ⟩ := (c.mem_img hAnL).1 hσ
    exact (c.mem_img hRL).2 ⟨t, hTR ht, by
      rw [show (⟨t, hRL (hTR ht)⟩ : ↥(nL T L)) = ⟨t, hAnL ht⟩ from Subtype.ext rfl]
      exact htθ⟩
  have hP2 : IsPGroup 2 (c.img (T ⊓ nL T L)) :=
    ((hX.sylow.2.1.to_le hRT).of_equiv (Subgroup.subgroupOfEquivOfLe hRL).symm).map c.θ
  have hA : c.img (T ⊓ nL T L) ≤ alternatingGroup (Fin 7) := c.img_le_alternating hinner hRL
  have htwo : twoPart (alternatingGroup (Fin 7)) = 8 := by
    unfold twoPart
    rw [card_alt7, show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 315 by norm_num)]
  have hbound : Nat.card (c.img (T ⊓ nL T L)) ≤ 8 := htwo ▸ card_le_twoPart hA hP2
  have hge : 8 ≤ Nat.card (c.img (T ⊓ nL T L)) := by
    rw [← hcardS]
    exact Subgroup.card_le_of_le hSle
  have hcardR : Nat.card (c.img (T ⊓ nL T L)) = 8 := le_antisymm hbound hge
  exact ⟨hcardR, (Subgroup.eq_of_le_of_card_ge hSle (by rw [hcardR, hcardS])).symm⟩

private theorem exists_conj_img_eq_fourD (c : SevenCtx0 T L) (hX : GNSetting X T)
    (hL : IsComponentOf L ⊤)
    (hinner : ∀ y ∈ nLs T L, ∃ l ∈ L, ∀ m ∈ L, (l⁻¹ * y) * m = m * (l⁻¹ * y)) :
    ∃ σ : Perm (Fin 7), (c.conj σ).img (T ⊓ nL T L) = fourD := by
  obtain ⟨hcardR, hReq⟩ := c.card_img_eq_eight hX hL hinner
  obtain ⟨hcardS, hSA⟩ := c.card_img_inf_lT hX hL
  have hSylS : IsSylowTwoOf (c.img (T ⊓ lT T L)) (alternatingGroup (Fin 7)) := by
    refine ⟨hSA, ?_, ?_⟩
    · exact IsPGroup.of_card (n := 3) (by rw [hcardS]; rfl)
    · have h1 := Subgroup.card_mul_index ((c.img (T ⊓ lT T L)).subgroupOf
        (alternatingGroup (Fin 7)))
      have hcardSub : Nat.card ((c.img (T ⊓ lT T L)).subgroupOf
          (alternatingGroup (Fin 7))) = 8 :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSA).toEquiv).trans hcardS
      have hidx : ((c.img (T ⊓ lT T L)).subgroupOf (alternatingGroup (Fin 7))).index = 315 := by
        have hthis := h1
        rw [hcardSub, card_alt7] at hthis
        omega
      rw [hidx]
      norm_num
  have hDA : fourD ≤ alternatingGroup (Fin 7) := fourD_le_fourPb.trans fourPb_le_alt
  have hD2 : IsPGroup 2 fourD := IsPGroup.of_card (n := 3) (by rw [card_fourD]; rfl)
  have hSylD : IsSylowTwoOf fourD (alternatingGroup (Fin 7)) := by
    refine ⟨hDA, hD2, ?_⟩
    have h1 := Subgroup.card_mul_index (fourD.subgroupOf (alternatingGroup (Fin 7)))
    have hcardSub : Nat.card (fourD.subgroupOf (alternatingGroup (Fin 7))) = 8 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA).toEquiv).trans card_fourD
    have hidx : (fourD.subgroupOf (alternatingGroup (Fin 7))).index = 315 := by
      have hthis := h1
      rw [hcardSub, card_alt7] at hthis
      omega
    rw [hidx]
    norm_num
  obtain ⟨g, -, hconj⟩ := B6.isSylowTwoOf_exists_conj hSylS hSylD
  refine ⟨g, ?_⟩
  rw [SevenCtx0.img_conj, hReq]
  exact hconj.symm

private theorem exists_lift_of_mem_img (c : SevenCtx0 T L)
    (hRL : T ⊓ nL T L ≤ nL T L)
    (hReq : c.img (T ⊓ nL T L) = c.img (T ⊓ lT T L)) {σ : Perm (Fin 7)}
    (hσ : σ ∈ c.img (T ⊓ nL T L)) :
    ∃ (t : X) (ht : t ∈ T ⊓ nL T L), QuotientGroup.mk' (gnC T) t ∈ L ∧
      c.θ ⟨t, hRL ht⟩ = σ := by
  have hAnL : T ⊓ lT T L ≤ nL T L := fun x hx =>
    Subgroup.mem_comap.2 (Subgroup.le_normalizer hx.2)
  have hσ' : σ ∈ c.img (T ⊓ lT T L) := hReq ▸ hσ
  obtain ⟨t, ht, htθ⟩ := (c.mem_img hAnL).1 hσ'
  have htR : t ∈ T ⊓ nL T L := Subgroup.mem_inf.mpr ⟨ht.1, hAnL ht⟩
  refine ⟨t, htR, ht.2, ?_⟩
  rw [show (⟨t, hRL htR⟩ : ↥(nL T L)) = ⟨t, hAnL ht⟩ from Subtype.ext rfl]
  exact htθ

end SevenCtx0

private theorem four_steps (hX : GNSetting X T)
    {C₁ C₂ : Subgroup X} (hP : IsC118Pair T C₁ C₂) (hDL : gnD T ⊓ lT T L ≤ gnC T)
    {c' : SevenCtx0 T L} (himgR : c'.img (T ⊓ nL T L) = fourD)
    (hCR : T ⊓ gnC T ≤ T ⊓ nL T L)
    (hQR : pCoreOf 2 (⊤ : Subgroup X) ≤ T ⊓ nL T L)
    (hbReq : baum (T ⊓ nL T L) = baum T)
    (h1R : C₁ ≤ omegaOneCenterOf (T ⊓ nL T L))
    (hR0 : T ⊓ nL T L ≤ nL T L)
    (hQLb : ∀ σ ∈ c'.img (T ⊓ nL T L) ⊓ alternatingGroup (Fin 7),
      ∃ (t : X) (ht : t ∈ T ⊓ nL T L), QuotientGroup.mk' (gnC T) t ∈ L ∧
        c'.θ ⟨t, hR0 ht⟩ = σ)
    (hQLS : ∀ σ ∈ c'.img (T ⊓ nL T L),
      ∃ (t : X) (ht : t ∈ T ⊓ nL T L), QuotientGroup.mk' (gnC T) t ∈ L ∧
        c'.θ ⟨t, hR0 ht⟩ = σ) :
    (c'.wP fourPb ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      c'.wP fourPb ≤ gnImg T (Subgroup.normalizer (C₂ : Set X))) ∧
    (c'.wP fourPc ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      c'.wP fourPc ≤ gnImg T (Subgroup.normalizer (C₂ : Set X))) ∧
    (c'.wP fourPS ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      c'.wP fourPS ≤ gnImg T (Subgroup.normalizer (C₂ : Set X))) := by
  classical
  have hnnb : ∃ g ∈ fourPb ⊓ alternatingGroup (Fin 7), ∃ e ∈ c'.img (T ⊓ nL T L),
      g * e * g⁻¹ ∉ c'.img (T ⊓ nL T L) := by
    obtain ⟨g, hg, e, he, hge⟩ := fourPb_notNormal
    refine ⟨g, hg, e, ?_, ?_⟩
    · rw [himgR]; exact he
    · rw [himgR]; exact hge
  have hnc : ∃ g ∈ fourPc ⊓ alternatingGroup (Fin 7), ∃ e ∈ c'.img (T ⊓ nL T L),
      g * e * g⁻¹ ∉ c'.img (T ⊓ nL T L) := by
    obtain ⟨g, hg, e, he, hge⟩ := fourPc_notNormal
    refine ⟨g, hg, e, ?_, ?_⟩
    · rw [himgR]; exact he
    · rw [himgR]; exact hge
  have hbR' : baum (T ⊓ nL T L) = baum T := hbReq
  have hbRle : baum T ≤ T ⊓ nL T L := by
    rw [← hbReq]
    exact inf_le_left
  refine ⟨?_, ?_, ?_⟩
  · exact c'.step hX hP hDL hR0 inf_le_left hCR hQR hbR' h1R
      (by rw [himgR]; exact fourD_le_fourPb)
      (by rw [himgR, card_fourPb, card_fourD]) (Or.inl fourPb_le_alt) hnnb hQLb
      isSolvable_fourPb
  · exact c'.step hX hP hDL hR0 inf_le_left hCR hQR hbR' h1R
      (by rw [himgR]; exact fourD_le_fourPc)
      (by rw [himgR, card_fourPc, card_fourD]) (Or.inl fourPc_le_alt) hnc hQLb
      isSolvable_fourPc
  · exact c'.step_nonsolv hX hP hDL hR0 inf_le_left hCR hQR hbRle
      (by rw [himgR]; exact minParabolic_fourPS) fourPS_le_alt nonempty_fourA5_equiv
      (by rw [himgR, fourPS_eq]) (by rw [himgR]; exact fourD_le_normalizer_fourA5) hQLS

private theorem four_contradiction {C₁ C₂ : Subgroup X} (hY : GNYComponent T C₁ C₂ L)
    {c' : SevenCtx0 T L}
    (hstepb : c'.wP fourPb ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      c'.wP fourPb ≤ gnImg T (Subgroup.normalizer (C₂ : Set X)))
    (hstepc : c'.wP fourPc ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      c'.wP fourPc ≤ gnImg T (Subgroup.normalizer (C₂ : Set X)))
    (hstepS : c'.wP fourPS ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      c'.wP fourPS ≤ gnImg T (Subgroup.normalizer (C₂ : Set X))) : False := by
  classical
  set CC : Subgroup (X ⧸ gnC T) := gnImg T (Subgroup.centralizer (C₁ : Set X)) with hCC
  set NN : Subgroup (X ⧸ gnC T) := gnImg T (Subgroup.normalizer (C₂ : Set X)) with hNN
  have hbc : ∀ K : Subgroup (X ⧸ gnC T), c'.wP fourPb ≤ K → c'.wP fourPc ≤ K → L ≤ K := by
    intro K hb hc
    refine c'.le_of_closure (K := K) gen_bc ?_
    intro δ hδ
    rcases hδ with hδ | hδ
    · exact c'.mem_of_wP_le hb ⟨hδ, fourPb_le_alt hδ⟩
    · exact c'.mem_of_wP_le hc ⟨hδ, fourPc_le_alt hδ⟩
  have hbS : ∀ K : Subgroup (X ⧸ gnC T), c'.wP fourPb ≤ K → c'.wP fourPS ≤ K → L ≤ K := by
    intro K hb hS
    refine c'.le_of_closure (K := K) gen_bS ?_
    intro δ hδ
    rcases hδ with hδ | hδ
    · exact c'.mem_of_wP_le hb ⟨hδ, fourPb_le_alt hδ⟩
    · exact c'.mem_of_wP_le hS ⟨hδ, fourPS_le_alt hδ⟩
  have hcS : ∀ K : Subgroup (X ⧸ gnC T), c'.wP fourPc ≤ K → c'.wP fourPS ≤ K → L ≤ K := by
    intro K hc hS
    refine c'.le_of_closure (K := K) gen_cS ?_
    intro δ hδ
    rcases hδ with hδ | hδ
    · exact c'.mem_of_wP_le hc ⟨hδ, fourPc_le_alt hδ⟩
    · exact c'.mem_of_wP_le hS ⟨hδ, fourPS_le_alt hδ⟩
  rcases hstepb with hbC | hbN
  · rcases hstepc with hcC | hcN
    · exact hY.2.1 (hbc CC hbC hcC)
    · rcases hstepS with hSC | hSN
      · exact hY.2.1 (hbS CC hbC hSC)
      · exact hY.2.2 (hcS NN hcN hSN)
  · rcases hstepc with hcC | hcN
    · rcases hstepS with hSC | hSN
      · exact hY.2.1 (hcS CC hcC hSC)
      · exact hY.2.2 (hbS NN hbN hSN)
    · exact hY.2.2 (hbc NN hbN hcN)

theorem false_of_alt7_four (hX : GNSetting X T)
    {C₁ C₂ : Subgroup X} (hP : IsC118Pair T C₁ C₂) (hY : GNYComponent T C₁ C₂ L)
    (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) (eL : ↥L ≃* alternatingGroup (Fin 7))
    (hDL : gnD T ⊓ lT T L ≤ gnC T)
    {W U : Subgroup X} (hWV : W ≤ gnV T) (hZW : omegaOneCenterOf T ≤ W)
    (hWK : ∀ k ∈ lT T L, ∀ w ∈ W, k * w * k⁻¹ ∈ W) (hWU : ⁅W, lT T L⁆ ≤ U) (hUV : U ≤ gnV T)
    (hUK : ∀ k ∈ lT T L, ∀ u ∈ U, k * u * k⁻¹ ∈ U) (hU16 : Nat.card U = 2 ^ 4) : False := by
  classical
  obtain ⟨-, h1Z, -, -, -, -, -⟩ := id hP
  obtain ⟨hne, hC, hcent, hinner⟩ :=
    four_facts hX h1Z hY.1 hJ hY.2.1 eL hWV hZW hWK hWU hUV hUK hU16
  have hbL : baum T ≤ nL T L := baum_le_nL hX hY.1 hne hC hcent
  obtain ⟨-, hCR, hQR, hbReq, h1R, -⟩ := nT_facts hX hbL
  obtain ⟨c, rfl⟩ := SevenCtx0.exists_eL T L eL
  obtain ⟨σ, hσ⟩ := c.exists_conj_img_eq_fourD hX hY.1 hinner
  set c' : SevenCtx0 T L := c.conj σ with hc'def
  have himgR : c'.img (T ⊓ nL T L) = fourD := by
    rw [hc'def]
    exact hσ
  have hReq : c.img (T ⊓ nL T L) = c.img (T ⊓ lT T L) :=
    (c.card_img_eq_eight hX hY.1 hinner).2
  have hReq' : c'.img (T ⊓ nL T L) = c'.img (T ⊓ lT T L) := by
    rw [hc'def, SevenCtx0.img_conj, SevenCtx0.img_conj, hReq]
  have hR0 : T ⊓ nL T L ≤ nL T L := inf_le_right
  have hQLb : ∀ σ ∈ c'.img (T ⊓ nL T L) ⊓ alternatingGroup (Fin 7),
      ∃ (t : X) (ht : t ∈ T ⊓ nL T L), QuotientGroup.mk' (gnC T) t ∈ L ∧
        c'.θ ⟨t, hR0 ht⟩ = σ := fun σ hσ =>
    c'.exists_lift_of_mem_img hR0 hReq' hσ.1
  have hQLS : ∀ σ ∈ c'.img (T ⊓ nL T L),
      ∃ (t : X) (ht : t ∈ T ⊓ nL T L), QuotientGroup.mk' (gnC T) t ∈ L ∧
        c'.θ ⟨t, hR0 ht⟩ = σ := fun σ hσ =>
    c'.exists_lift_of_mem_img hR0 hReq' hσ
  obtain ⟨hstepb, hstepc, hstepS⟩ :=
    four_steps hX hP hDL himgR hCR hQR hbReq (h1Z.trans h1R) hR0 hQLb hQLS
  exact four_contradiction hY hstepb hstepc hstepS

end CFSG.AGLEmbeddingD2.McLaughlin.A7Lift
