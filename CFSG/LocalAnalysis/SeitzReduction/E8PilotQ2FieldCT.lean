module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2FieldAlign
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotUniqueFieldStep3
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionFusion
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotFieldNormalizeUnique

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

local instance e8PilotQ2FieldCTNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

section Family

variable {K : Type} [Field K] {K₂ : Type} [Field K₂] {ι : K →+* K₂} {G : Type} [Group G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E8 K} {EN : E8Neighbour → Subgroup G}

@[expose] def TwoFieldAligned (Φ : ∀ N : E8Neighbour, TwoFieldParam ι e N (EN N)) : Prop :=
  ∀ (N N' : E8Neighbour) {J : Finset (Fin (Tag.rank .E8))}, J ⊆ N.nodes → J ⊆ N'.nodes →
    ∀ (x : N.levi K₂) (x' : N'.levi K₂), (x : adjointGroup .E8 K₂) = x' →
      x ∈ leviPiece K₂ N J → (((Φ N).Φ x : EN N) : G) = (Φ N').Φ x'

@[expose] def twoFieldOfTriple {E₁ E₂ E₃ : Subgroup G} (hX : TwoFieldParam ι e .high E₁)
    (hY : TwoFieldParam ι e .two E₂) (hZ : TwoFieldParam ι e .six E₃) :
    ∀ N : E8Neighbour, TwoFieldParam ι e N (E8Neighbour.rec E₁ E₂ E₃ N)
  | .high => hX
  | .two => hY
  | .six => hZ

@[expose] noncomputable def twoAlignedFamily (Φ : ∀ N : E8Neighbour, TwoFieldParam ι e N (EN N))
    (J : {J : Finset (Fin (adjDatumE8 K₂).rank) // J.card ≤ 2}) :
    (adjDatumE8 K₂).leviAmalgam J →* G :=
  (EN (amalgamPlacement J.1)).subtype.comp
    ((Φ (amalgamPlacement J.1)).Φ.toMonoidHom.comp
      (Subgroup.inclusion (leviAmalgam_le_placementLevi J)))

theorem twoAlignedFamily_apply (Φ : ∀ N : E8Neighbour, TwoFieldParam ι e N (EN N))
    (J : {J : Finset (Fin (adjDatumE8 K₂).rank) // J.card ≤ 2})
    (x : (adjDatumE8 K₂).leviAmalgam J) :
    twoAlignedFamily Φ J x =
      (((Φ (amalgamPlacement J.1)).Φ ⟨x, leviAmalgam_le_placementLevi J x.2⟩ :
        EN (amalgamPlacement J.1)) : G) :=
  rfl

theorem isCompatible_twoAlignedFamily {Φ : ∀ N : E8Neighbour, TwoFieldParam ι e N (EN N)}
    (hΦ : TwoFieldAligned Φ) : IsCompatible (adjDatumE8 K₂).leviAmalgam (twoAlignedFamily Φ) := by
  intro i j hij x y hxy
  have hsub : (i.1 : Finset (Fin (Tag.rank .E8))) ⊆ j.1 := hij
  rw [twoAlignedFamily_apply, twoAlignedFamily_apply]
  exact hΦ _ _ (subset_nodes_amalgamPlacement i.2)
    (hsub.trans (subset_nodes_amalgamPlacement j.2)) _ _ hxy
    (mem_leviPiece_of_mem_leviAmalgam (N := amalgamPlacement i.1) x.2)

theorem twoAlignedFamily_fix (Φ : ∀ N : E8Neighbour, TwoFieldParam ι e N (EN N))
    (J : {J : Finset (Fin (adjDatumE8 K₂).rank) // J.card ≤ 2}) (x : adjointGroup .E8 K)
    (hx : x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J.1)
    (y : (adjDatumE8 K₂).leviAmalgam J)
    (hxy : ((y : adjointGroup .E8 K₂) : ModGL .E8 K₂) = baseChangeGL ι (x : ModGL .E8 K)) :
    twoAlignedFamily Φ J y = ((e.symm x : L) : G) := by
  rw [twoAlignedFamily_apply]
  have hxN : x ∈ (amalgamPlacement J.1).levi K :=
    levi_le_neighbourLevi (subset_nodes_amalgamPlacement J.2) hx
  have h1 : (⟨y, leviAmalgam_le_placementLevi J y.2⟩ : (amalgamPlacement J.1).levi K₂) =
      leviBaseChange ι _ ⟨x, hxN⟩ :=
    Subtype.ext (Subtype.ext (by rw [coe_leviBaseChange]; exact hxy))
  rw [h1]
  exact (Φ (amalgamPlacement J.1)).fix ⟨x, hxN⟩

end Family

section CT

@[expose] noncomputable def adjointBaseChangeE8 {K K₂ : Type} [Field K] [Field K₂]
    (ι : K →+* K₂) : adjointGroup .E8 K →* adjointGroup .E8 K₂ :=
  ((baseChangeGL ι).comp (adjointGroup .E8 K).subtype).codRestrict _ fun g =>
    baseChangeGL_mem_adjointGroup_E8 ι g

variable {K : Type} [Field K] {K₂ : Type} [Field K₂] {ι : K →+* K₂} {G : Type} [Group G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E8 K} {EN : E8Neighbour → Subgroup G}

@[expose] noncomputable def twoFieldSup (Φ : ∀ N : E8Neighbour, TwoFieldParam ι e N (EN N)) :
    Subgroup G :=
  ⨆ J, (twoAlignedFamily Φ J).range

theorem exists_injective_of_twoFieldAligned {Φ : ∀ N : E8Neighbour, TwoFieldParam ι e N (EN N)}
    (hΦ : TwoFieldAligned Φ) :
    ∃ ψ : adjointGroup .E8 K₂ →* G, Function.Injective ψ ∧ ψ.range = twoFieldSup Φ ∧
      (∀ J (x : (adjDatumE8 K₂).leviAmalgam J), ψ x = twoAlignedFamily Φ J x) ∧
      ∀ x : adjointGroup .E8 K, ψ (adjointBaseChangeE8 ι x) = ((e.symm x : L) : G) := by
  have hcard : ∀ i : Fin (Tag.rank .E8), ({i} : Finset (Fin (Tag.rank .E8))).card ≤ 2 :=
    fun i => by simp
  set φ := twoAlignedFamily Φ with hφdef
  set G₀ : Subgroup G := twoFieldSup Φ with hG₀
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x =>
    le_iSup (fun J => (twoAlignedFamily Φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, (adjDatumE8 K₂).leviAmalgam J →* G₀ := fun J => (φ J).codRestrict G₀ (hle J)
    with hφ'def
  have hφ' : IsCompatible (adjDatumE8 K₂).leviAmalgam φ' := fun i j hij x y hxy =>
    Subtype.ext (isCompatible_twoAlignedFamily hΦ i j hij x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [← MonoidHom.range_comp]
    rfl
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_levi_adjDatumE8 (k := K) 0
    obtain ⟨y, hy⟩ := exists_levi_adjDatumE8_baseChangeGL (K := K₂) ι hu
    refine ⟨⟨{0}, hcard 0⟩, y, fun h => hu1 ?_⟩
    have h1 : φ ⟨{0}, hcard 0⟩ y = 1 := congrArg Subtype.val h
    rw [hφdef, twoAlignedFamily_fix Φ ⟨{0}, hcard 0⟩ u hu y hy] at h1
    have h2 : e.symm u = 1 := Subtype.ext h1
    rw [← map_one e.symm] at h2
    exact e.symm.injective h2
  obtain ⟨ψ₀, hψ₀, hsurj, hker⟩ := exists_surjective_of_isCompatible_e8 K₂ φ' hφ' hgen' hnt
  have hinj₀ : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (center_adjointGroup_eq_bot_field .E8 K₂).le
  have hψφ : ∀ J (x : (adjDatumE8 K₂).leviAmalgam J), (G₀.subtype.comp ψ₀) x = φ J x :=
    fun J x => congrArg Subtype.val (hψ₀ J x)
  refine ⟨G₀.subtype.comp ψ₀, G₀.subtype_injective.comp hinj₀, ?_, hψφ, fun x => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · have key : ∀ (i : Fin (Tag.rank .E8)) (x : adjointGroup .E8 K),
        x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup {i} →
        (G₀.subtype.comp ψ₀) (adjointBaseChangeE8 ι x) = ((e.symm x : L) : G) := by
      intro i x hx
      obtain ⟨y, hy⟩ := exists_levi_adjDatumE8_baseChangeGL (K := K₂) ι hx
      have hyx : (y : adjointGroup .E8 K₂) = adjointBaseChangeE8 ι x := Subtype.ext hy
      rw [← hyx]
      exact (hψφ ⟨{i}, hcard i⟩ y).trans (twoAlignedFamily_fix Φ ⟨{i}, hcard i⟩ x hx y hy)
    have h := CFSG.LieType.Ree.adjointGroup_hom_ext
      (f := (G₀.subtype.comp ψ₀).comp (adjointBaseChangeE8 ι))
      (g := L.subtype.comp e.symm.toMonoidHom)
      (fun i c => key i _ (xElement_mem_levi_adjDatumE8 i c))
      (fun i c => key i _ (yElement_mem_levi_adjDatumE8 i c))
    exact DFunLike.congr_fun h x

theorem le_twoFieldSup {Φ : ∀ N : E8Neighbour, TwoFieldParam ι e N (EN N)}
    (hΦ : TwoFieldAligned Φ) : L ≤ twoFieldSup Φ := by
  obtain ⟨ψ, -, hrange, -, hfix⟩ := exists_injective_of_twoFieldAligned hΦ
  intro g hg
  rw [← hrange]
  refine ⟨adjointBaseChangeE8 ι (e ⟨g, hg⟩), ?_⟩
  rw [hfix, MulEquiv.symm_apply_apply]

theorem nonempty_mulEquiv_twoFieldSup {Φ : ∀ N : E8Neighbour, TwoFieldParam ι e N (EN N)}
    (hΦ : TwoFieldAligned Φ) : Nonempty (twoFieldSup Φ ≃* adjointGroup .E8 K₂) := by
  obtain ⟨ψ, hinj, hrange, -, -⟩ := exists_injective_of_twoFieldAligned hΦ
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

end CT

section Normalizer

variable {K : Type} [Field K] [Finite K] [CharP K 2] {K₂ : Type} [Field K₂] [Finite K₂]
  [CharP K₂ 2] {ι : K →+* K₂} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E8 K} {EN : E8Neighbour → Subgroup G}

omit [Finite K] [CharP K 2] [Finite K₂] [CharP K₂ 2] in
theorem leviEntrywiseEquiv_mem_leviPiece [Finite K₂] (ρ : K₂ ≃+* K₂) {N : E8Neighbour}
    {J : Finset (Fin (Tag.rank .E8))} {x : N.levi K₂} (hx : x ∈ leviPiece K₂ N J) :
    leviEntrywiseEquiv ρ N x ∈ leviPiece K₂ N J := by
  rw [mem_leviPiece, coe_leviEntrywiseEquiv]
  exact F4Pilot.map_rootSpan_baseChangeGL_le (ρ : K₂ →+* K₂) _ ⟨_, mem_leviPiece.1 hx, rfl⟩

theorem eq_one_or_eq_leviEntrywiseEquiv_of_forall (ι : K →+* K₂) {σ : K₂ ≃+* K₂}
    (hσ : orderOf σ = 2) (hfix : ∀ x : K₂, σ x = x ↔ x ∈ Set.range ι) (N : E8Neighbour)
    {β : MulAut (N.levi K₂)}
    (hβ : ∀ y : N.levi K, β (leviBaseChange ι N y) = leviBaseChange ι N y) :
    β = 1 ∨ ∀ x, β x = leviEntrywiseEquiv σ N x := by
  set lam := neighbourLeviEquiv K₂ N with hlam
  set θ : MulAut (e7Levi K₂) := (lam.trans β).trans lam.symm with hθdef
  have hθapp : ∀ g, θ g = lam.symm (β (lam g)) := fun _ => rfl
  have hθ : ∀ g, θ (e7LeviBaseChange ι g) = e7LeviBaseChange ι g := by
    intro g
    rw [hθapp, hlam, ← leviBaseChange_neighbourLeviEquiv, hβ, leviBaseChange_neighbourLeviEquiv,
      MulEquiv.symm_apply_apply]
  rcases eq_one_or_eq_e7LeviBaseChange_of_forall ι hσ hfix hθ with h1 | h1
  · left
    refine MulEquiv.ext fun x => ?_
    obtain ⟨g, rfl⟩ := lam.surjective x
    have h2 := DFunLike.congr_fun h1 g
    rw [hθapp, MulAut.one_apply, MulEquiv.symm_apply_eq] at h2
    exact h2
  · right
    intro x
    obtain ⟨g, rfl⟩ := lam.surjective x
    have h2 := h1 g
    rw [hθapp, MulEquiv.symm_apply_eq] at h2
    rw [h2]
    exact (leviBaseChange_neighbourLeviEquiv (σ : K₂ →+* K₂) N g).symm

theorem conj_mem_map_leviPiece_of_mem_centralizer {σ : K₂ ≃+* K₂} (hσ : orderOf σ = 2)
    (hfix : ∀ x : K₂, σ x = x ↔ x ∈ Set.range ι) {N : E8Neighbour} {E : Subgroup G}
    (h : TwoFieldParam ι e N E) {c : G} (hcL : c ∈ centralizer (L : Set G))
    (hcE : c ∈ normalizer (E : Set G)) {J : Finset (Fin (Tag.rank .E8))} {x : N.levi K₂}
    (hx : x ∈ leviPiece K₂ N J) :
    c * (h.Φ x : G) * c⁻¹ ∈ ((leviPiece K₂ N J).map h.Φ.toMonoidHom).map E.subtype := by
  set α : MulAut E := E.normalizerMonoidHom ⟨c, hcE⟩ with hαdef
  have hα : ∀ y : E, ((α y : E) : G) = c * y * c⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe E ⟨c, hcE⟩ y
  set β : MulAut (N.levi K₂) := (h.Φ.trans α).trans h.Φ.symm with hβdef
  have hβapp : ∀ z, h.Φ (β z) = α (h.Φ z) := fun z => by
    rw [hβdef, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  have hβ : ∀ y : N.levi K, β (leviBaseChange ι N y) = leviBaseChange ι N y := by
    intro y
    apply h.Φ.injective
    rw [hβapp]
    apply Subtype.ext
    rw [hα, h.fix y, ← mem_centralizer_iff.1 hcL _ (e.symm y).2, mul_inv_cancel_right]
  have hcx : c * (h.Φ x : G) * c⁻¹ = (h.Φ (β x) : G) := by rw [hβapp, hα]
  rw [hcx]
  rcases eq_one_or_eq_leviEntrywiseEquiv_of_forall ι hσ hfix N hβ with h1 | h1
  · rw [h1, MulAut.one_apply]
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  · rw [h1 x]
    exact ⟨_, ⟨_, leviEntrywiseEquiv_mem_leviPiece σ hx, rfl⟩, rfl⟩

omit [Finite K] [CharP K 2] [Finite K₂] [CharP K₂ 2] in
theorem range_twoAlignedFamily (Φ : ∀ N : E8Neighbour, TwoFieldParam ι e N (EN N))
    (J : {J : Finset (Fin (adjDatumE8 K₂).rank) // J.card ≤ 2}) :
    (twoAlignedFamily Φ J).range =
      ((leviPiece K₂ (amalgamPlacement J.1) J.1).map
        (Φ (amalgamPlacement J.1)).Φ.toMonoidHom).map (EN (amalgamPlacement J.1)).subtype := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨_, mem_leviPiece_of_mem_leviAmalgam x.2, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hy' : (y : adjointGroup .E8 K₂) ∈ (adjDatumE8 K₂).leviAmalgam J := by
      change (y : adjointGroup .E8 K₂) ∈
        CFSG.LieType.CurtisTits.levi (adjDatumE8 K₂).rootGroup J.1
      rw [levi_adjDatumE8_eq, mem_subgroupOf]
      exact mem_leviPiece.1 hy
    exact ⟨⟨y, hy'⟩, rfl⟩

theorem mem_normalizer_twoFieldSup_of_mem_centralizer {σ : K₂ ≃+* K₂} (hσ : orderOf σ = 2)
    (hfix : ∀ x : K₂, σ x = x ↔ x ∈ Set.range ι)
    (Φ : ∀ N : E8Neighbour, TwoFieldParam ι e N (EN N)) {c : G}
    (hcL : c ∈ centralizer (L : Set G)) (hcE : ∀ N, c ∈ normalizer (EN N : Set G)) :
    c ∈ normalizer (twoFieldSup Φ : Set G) := by
  have hcL' : c⁻¹ ∈ centralizer (L : Set G) := inv_mem hcL
  have hcE' : ∀ N, c⁻¹ ∈ normalizer (EN N : Set G) := fun N => inv_mem (hcE N)
  refine F4Pilot.mem_normalizer_iSup fun J => ?_
  rw [mem_normalizer_iff]
  intro g
  rw [range_twoAlignedFamily]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact conj_mem_map_leviPiece_of_mem_centralizer hσ hfix (Φ (amalgamPlacement J.1)) hcL
      (hcE _) hx
  · rintro ⟨_, ⟨x, hx, rfl⟩, hxg⟩
    have h1 := conj_mem_map_leviPiece_of_mem_centralizer hσ hfix (Φ (amalgamPlacement J.1)) hcL'
      (hcE' _) hx
    have h2 : c⁻¹ * ((Φ (amalgamPlacement J.1)).Φ x : G) * c⁻¹⁻¹ = g := by
      have h3 : ((Φ (amalgamPlacement J.1)).Φ x : G) = c * g * c⁻¹ := hxg
      rw [h3]
      group
    rw [← h2]
    exact h1

end Normalizer

section Endgame

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {t : G}

theorem false_of_E8_two_of_fieldRow_subgroup (hw : E8Work L K t 1) (e : L ≃* adjointGroup .E8 K)
    {G₀ : Subgroup G} {K₂ : Type} [Field K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * 1))
    (e₀ : G₀ ≃* adjointGroup .E8 K₂) (hLG : L ≤ G₀)
    (hCN : centralizer (L : Set G) ≤ normalizer (G₀ : Set G)) : False := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have : Finite K₂ := F4Pilot.finite_of_natCard_eq_two_pow hK₂
  have : CharP K₂ 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hK₂
  have hKt := hw.inf_eq e
  have hNL : normalizer (L : Set G) ≤ normalizer (G₀ : Set G) := by
    intro n hn
    obtain ⟨l, hl⟩ := forall_mem_range_conj_of_mulEquiv_E8_two hK2 e
      (L.normalizerMonoidHom ⟨n, hn⟩)
    have hc : (l : G)⁻¹ * n ∈ centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      have h1 := congrArg (fun β : MulAut L => ((β ⟨y, hy⟩ : L) : G)) hl
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
      calc y * ((l : G)⁻¹ * n) = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * n := by group
        _ = (l : G)⁻¹ * (n * y * n⁻¹) * n := by rw [h1]
        _ = (l : G)⁻¹ * n * y := by group
    have hnl : n = (l : G) * ((l : G)⁻¹ * n) := by group
    rw [hnl]
    exact mul_mem (le_normalizer (hLG l.2)) (hCN hc)
  have htN : t ∈ normalizer (G₀ : Set G) := hCN hw.mem_centralizer
  have htG : t ∉ G₀ := not_mem_E8_field hw.standard hw.card_eq e hw.orderOf_eq hKt hK₂ e₀
  have htC : t ∉ centralizer (G₀ : Set G) :=
    not_mem_centralizer_E8_field hw.standard hw.card_eq e hw.orderOf_eq hKt hK₂ e₀
  have hZ := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt hLG hw.orderOf_eq htN htC
  have huniq := unique_of_step3_E8_field hw.standard hw.card_eq e hw.orderOf_eq hKt hK₂ e₀
    (eq_of_conjugate_E8_field hw.standard hw.card_eq e hw.orderOf_eq hKt hK₂ e₀ htN hNL)
  have := hw.seitz.1
  exact false_of_simple_of_E8_odd hZ hK₂ e₀ htN hw.orderOf_eq htG huniq

end Endgame

end CFSG.SeitzReduction.E8Pilot
