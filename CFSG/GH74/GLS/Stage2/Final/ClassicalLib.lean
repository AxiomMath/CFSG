module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Defs
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm3.Sec7

variable {G Gs : Type} [Group G] [Group Gs]

theorem compatIso_of_compat7 {z : G} {S X : Subgroup G} {z' : Gs} {S' : Subgroup Gs}
    (hL : layerTimesSylow z S = X) (hN : X ⊓ OddCore z = ⊥)
    (hC : Compat7 z X S (IVK.Ez z') S') :
    ∃ ψ : ↥(layerTimesSylow z S) ≃* ↥(layerTimesSylow z' S'),
      (∀ x : ↥(layerTimesSylow z S), (x : G) ∈ S ↔ (ψ x : Gs) ∈ S') ∧
      (∀ x y : ↥(layerTimesSylow z S), (x : G) ∈ S → (y : G) ∈ S → orderOf (x : G) = 2 →
        orderOf (y : G) = 2 → (IsConj (x : G) (y : G) ↔ IsConj (ψ x : Gs) (ψ y : Gs))) := by
  obtain ⟨hnorm, ψ, h1, h2, h3⟩ := hC
  have hbot : (Oz z).subgroupOf X = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have ha' : (a : G) ∈ X ⊓ OddCore z := ⟨a.2, ha⟩
    rw [hN, Subgroup.mem_bot] at ha'
    exact Subtype.ext (by simpa using ha')
  have hinj : Function.Injective (QuotientGroup.mk' ((Oz z).subgroupOf X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hbot]
  let e₁ : ↥X ≃* (↥X ⧸ (Oz z).subgroupOf X) :=
    MulEquiv.ofBijective (QuotientGroup.mk' ((Oz z).subgroupOf X))
      ⟨hinj, QuotientGroup.mk'_surjective _⟩
  let e₂ : ↥(layerTimesSylow z S) ≃* ↥X := MulEquiv.subgroupCongr hL
  refine ⟨(e₂.trans (e₁.trans ψ) : ↥(layerTimesSylow z S) ≃* ↥(IVK.Ez z' ⊔ S')), ?_, ?_⟩
  · intro x
    have hx : ((e₂ x : ↥X) : G) = (x : G) := rfl
    constructor
    · intro hS
      exact h1 (e₂ x) (by rw [hx]; exact hS)
    · intro hS
      obtain ⟨s, hsS, hs⟩ := h2 (e₁ (e₂ x)) hS
      have hs' : QuotientGroup.mk' ((Oz z).subgroupOf X) s =
          QuotientGroup.mk' ((Oz z).subgroupOf X) (e₂ x) := hs
      have := hinj hs'
      rw [← hx, ← this]
      exact hsS
  · intro x y hx hy hox hoy
    exact h3 (e₂ x) (e₂ y) hx hy hox hoy


theorem center_eq_zpowers_of_equiv [Finite G] [Finite Gs] {z : G} {S A : Subgroup G} {z' : Gs}
    {S' A' : Subgroup Gs} (hSA : S ≤ A) (hSA' : S' ≤ A') (ψ : ↥A ≃* ↥A')
    (hψ : ∀ x : ↥A, (x : G) ∈ S ↔ (ψ x : Gs) ∈ S') (hz : z ∈ S) (hzc : ∀ s ∈ S, s * z = z * s)
    (hzo : orderOf z = 2) (hz'o : orderOf z' = 2)
    (hcen : (center ↥S').map S'.subtype = zpowers z') :
    (center ↥S).map S.subtype = zpowers z := by
  let φ₀ : ↥S →* ↥S' :=
    (A'.subtype.comp (ψ.toMonoidHom.comp (Subgroup.inclusion hSA))).codRestrict S'
      (fun s => (hψ ⟨s, hSA s.2⟩).mp s.2)
  have hφinj : Function.Injective φ₀ := by
    intro a b hab
    have h1 : ((φ₀ a : ↥S') : Gs) = ((φ₀ b : ↥S') : Gs) := congrArg Subtype.val hab
    have h1' : (ψ (Subgroup.inclusion hSA a) : Gs) = (ψ (Subgroup.inclusion hSA b) : Gs) := h1
    have h2 : ψ (Subgroup.inclusion hSA a) = ψ (Subgroup.inclusion hSA b) := Subtype.ext h1'
    exact Subgroup.inclusion_injective hSA (ψ.injective h2)
  have hφsurj : Function.Surjective φ₀ := by
    intro y
    have hyA : (y : Gs) ∈ A' := hSA' y.2
    have hy' : ((ψ (ψ.symm ⟨(y : Gs), hyA⟩) : ↥A') : Gs) = (y : Gs) := by
      rw [MulEquiv.apply_symm_apply]
    refine ⟨⟨(ψ.symm ⟨(y : Gs), hyA⟩ : G), (hψ _).mpr (by rw [hy']; exact y.2)⟩, ?_⟩
    apply Subtype.ext
    exact hy'
  let φ : ↥S ≃* ↥S' := MulEquiv.ofBijective φ₀ ⟨hφinj, hφsurj⟩
  have hc1 : Nat.card ↥(center ↥S) = Nat.card ↥(center ↥S') :=
    Nat.card_congr (Subgroup.centerCongr φ).toEquiv
  have hc2 : Nat.card ↥(center ↥S') = 2 := by
    rw [← Subgroup.card_map_of_injective S'.subtype_injective, hcen, Nat.card_zpowers, hz'o]
  have hc3 : Nat.card ↥((center ↥S).map S.subtype) = 2 := by
    rw [Subgroup.card_map_of_injective S.subtype_injective, hc1, hc2]
  have hle : zpowers z ≤ (center ↥S).map S.subtype := by
    rw [Subgroup.zpowers_le]
    refine ⟨⟨z, hz⟩, ?_, rfl⟩
    show (⟨z, hz⟩ : ↥S) ∈ center ↥S
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g.1 g.2)
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hc3, Nat.card_zpowers, hzo]


@[expose] noncomputable def barHom (z : G) (A : Subgroup G) (hAC : A ≤ Cen z) : ↥A →* CentralizerBar z :=
  (toBar z).comp (Subgroup.inclusion hAC)

theorem barHom_apply (z : G) (A : Subgroup G) (hAC : A ≤ Cen z) (a : ↥A) :
    barHom z A hAC a = toBar z ⟨a, hAC a.2⟩ := rfl

theorem barHom_injective (z : G) (A : Subgroup G) (hAC : A ≤ Cen z) (hAN : A ⊓ OddCore z = ⊥) :
    Function.Injective (barHom z A hAC) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  have h1 : toBar z ⟨a, hAC a.2⟩ = 1 := ha
  have h2 : (⟨a, hAC a.2⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := by
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥(Cen z))]
    exact h1
  have h3 : (a : G) ∈ OddCore z := ⟨⟨a, hAC a.2⟩, h2, rfl⟩
  have h4 : (a : G) ∈ A ⊓ OddCore z := ⟨a.2, h3⟩
  rw [hAN, Subgroup.mem_bot] at h4
  exact Subtype.ext h4

theorem barHom_range (z : G) (A : Subgroup G) (hAC : A ≤ Cen z) :
    (barHom z A hAC).range = barOf z A := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a, hAC a.2⟩, a.2, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c, hc⟩, rfl⟩

@[expose] noncomputable def barEquiv (z : G) (A : Subgroup G) (hAC : A ≤ Cen z) (hAN : A ⊓ OddCore z = ⊥) :
    ↥A ≃* ↥(barOf z A) :=
  (MonoidHom.ofInjective (barHom_injective z A hAC hAN)).trans
    (MulEquiv.subgroupCongr (barHom_range z A hAC))

theorem barEquiv_apply (z : G) (A : Subgroup G) (hAC : A ≤ Cen z) (hAN : A ⊓ OddCore z = ⊥)
    (a : ↥A) : ((barEquiv z A hAC hAN a : ↥(barOf z A)) : CentralizerBar z) =
      toBar z ⟨a, hAC a.2⟩ := rfl

theorem mem_iff_barOf (z : G) (A S : Subgroup G) (hAC : A ≤ Cen z) (hAN : A ⊓ OddCore z = ⊥)
    (hSA : S ≤ A) (a : ↥A) :
    (a : G) ∈ S ↔ ((barEquiv z A hAC hAN a : ↥(barOf z A)) : CentralizerBar z) ∈ barOf z S := by
  constructor
  · intro h
    exact ⟨⟨a, hAC a.2⟩, h, rfl⟩
  · rintro ⟨c, hc, hca⟩
    have hcA : (c : G) ∈ A := hSA hc
    have h1 : barHom z A hAC a = barHom z A hAC ⟨c, hcA⟩ := by
      rw [barHom_apply, barHom_apply]
      exact hca.symm
    have h2 := barHom_injective z A hAC hAN h1
    have h3 : (a : G) = (c : G) := congrArg Subtype.val h2
    rw [h3]
    exact hc


theorem isSylowOf_barOf [Finite G] {z : G} {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z)) :
    CFSG.ABGLocalTools.IsSylowOf 2 (barOf z S) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hS.exists_sylow_eq_subgroupOf
  have hsurj : Function.Surjective (toBar z) := QuotientGroup.mk'_surjective _
  let Q' : Sylow 2 (CentralizerBar z) := Sylow.mapSurjective hsurj Q
  have hQ' : (Q' : Subgroup (CentralizerBar z)) = barOf z S := by
    have h1 := Sylow.coe_mapSurjective hsurj Q
    have h2 : (Q' : Subgroup (CentralizerBar z)) = (Q : Subgroup ↥(Cen z)).map (toBar z) := h1
    rw [h2, hQ]
    rfl
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, ?_, ?_⟩
  · rw [← hQ']; exact Q'.isPGroup'
  · rw [Subgroup.relIndex_top_right, ← hQ']
    exact Q'.not_dvd_index

theorem barOf_le_oPrimeResidual {z : G} {S : Subgroup G} (hS : IsPGroup 2 ↥S) :
    barOf z S ≤ oPrimeResidual 2 (CentralizerBar z) := by
  rintro _ ⟨c, hc, rfl⟩
  apply Subgroup.subset_closure
  obtain ⟨k, hk⟩ := hS ⟨(c : G), hc⟩
  refine ⟨k, ?_⟩
  rw [← map_pow]
  have : c ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  rw [this, map_one]

theorem exists_equiv_sylow {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (φ₀ : X ≃* Y)
    (PX : Sylow 2 X) (PY : Sylow 2 Y) :
    ∃ φ : X ≃* Y, ∀ x : X, x ∈ (PX : Subgroup X) ↔ φ x ∈ (PY : Subgroup Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : Function.Surjective φ₀.toMonoidHom := φ₀.surjective
  let P' : Sylow 2 Y := Sylow.mapSurjective hs PX
  have hP' : (P' : Subgroup Y) = (PX : Subgroup X).map φ₀.toMonoidHom := Sylow.coe_mapSurjective hs PX
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P' PY
  refine ⟨φ₀.trans (MulAut.conj g), fun x => ?_⟩
  have h1 : (↑(g • P') : Subgroup Y) = (PY : Subgroup Y) := by rw [hg]
  rw [Sylow.coe_subgroup_smul, hP'] at h1
  rw [← h1]
  constructor
  · intro hx
    rw [Subgroup.pointwise_smul_def]
    exact ⟨φ₀ x, ⟨x, hx, rfl⟩, rfl⟩
  · intro hx
    rw [Subgroup.pointwise_smul_def] at hx
    obtain ⟨y, ⟨x', hx', rfl⟩, hy⟩ := hx
    have : φ₀ x' = φ₀ x := (MulAut.conj g).injective hy
    have := φ₀.injective this
    rw [← this]
    exact hx'


theorem layerTimesSylow_le_Cen {z : G} {S : Subgroup G} (hSC : S ≤ Cen z) :
    layerTimesSylow z S ≤ Cen z :=
  sup_le (Subgroup.map_subtype_le _) hSC

theorem compatIso_of_bar {z : G} {S : Subgroup G} {z' : Gs} {S' : Subgroup Gs}
    {Y : Subgroup (CentralizerBar z)} {Y' : Subgroup (CentralizerBar z')}
    (hSC : S ≤ Cen z) (hSC' : S' ≤ Cen z')
    (hN : layerTimesSylow z S ⊓ OddCore z = ⊥)
    (hB : barOf z (layerTimesSylow z S) = Y)
    (hN' : layerTimesSylow z' S' ⊓ OddCore z' = ⊥)
    (hB' : barOf z' (layerTimesSylow z' S') = Y')
    (φ : ↥Y ≃* ↥Y')
    (hφ : ∀ y : ↥Y,
      (y : CentralizerBar z) ∈ barOf z S ↔ (φ y : CentralizerBar z') ∈ barOf z' S')
    (hone : ∀ u v : G, u ∈ S → v ∈ S → orderOf u = 2 → orderOf v = 2 → IsConj u v)
    (hone' : ∀ u v : Gs, u ∈ S' → v ∈ S' → orderOf u = 2 → orderOf v = 2 → IsConj u v) :
    ∃ ψ : ↥(layerTimesSylow z S) ≃* ↥(layerTimesSylow z' S'),
      (∀ x : ↥(layerTimesSylow z S), (x : G) ∈ S ↔ (ψ x : Gs) ∈ S') ∧
      (∀ x y : ↥(layerTimesSylow z S), (x : G) ∈ S → (y : G) ∈ S → orderOf (x : G) = 2 →
        orderOf (y : G) = 2 → (IsConj (x : G) (y : G) ↔ IsConj (ψ x : Gs) (ψ y : Gs))) := by
  have hAC := layerTimesSylow_le_Cen hSC
  have hAC' := layerTimesSylow_le_Cen hSC'
  have hSA : S ≤ layerTimesSylow z S := le_sup_right
  have hSA' : S' ≤ layerTimesSylow z' S' := le_sup_right
  let e := barEquiv z (layerTimesSylow z S) hAC hN
  let e' := barEquiv z' (layerTimesSylow z' S') hAC' hN'
  let ψ : ↥(layerTimesSylow z S) ≃* ↥(layerTimesSylow z' S') :=
    e.trans ((MulEquiv.subgroupCongr hB).trans
      (φ.trans ((MulEquiv.subgroupCongr hB').symm.trans e'.symm)))
  have hmem : ∀ x : ↥(layerTimesSylow z S), (x : G) ∈ S ↔ (ψ x : Gs) ∈ S' := by
    intro x
    have h1 := mem_iff_barOf z (layerTimesSylow z S) S hAC hN hSA x
    have h2 := mem_iff_barOf z' (layerTimesSylow z' S') S' hAC' hN' hSA' (ψ x)
    have hy : (((MulEquiv.subgroupCongr hB) (e x) : ↥Y) :
        CentralizerBar z) = ((e x : ↥(barOf z (layerTimesSylow z S))) : CentralizerBar z) := rfl
    have h3 := hφ ((MulEquiv.subgroupCongr hB) (e x))
    have hz : (e' (ψ x) : ↥(barOf z' (layerTimesSylow z' S'))) =
        (MulEquiv.subgroupCongr hB').symm (φ ((MulEquiv.subgroupCongr hB) (e x))) := by
      show e' (e'.symm _) = _
      exact e'.apply_symm_apply _
    have hz' : ((e' (ψ x) : ↥(barOf z' (layerTimesSylow z' S'))) : CentralizerBar z') =
        ((φ ((MulEquiv.subgroupCongr hB) (e x)) : ↥Y') :
          CentralizerBar z') := by
      rw [hz]; rfl
    rw [h1, h2, hz', ← hy]
    exact h3
  refine ⟨ψ, hmem, ?_⟩
  intro x y hx hy hox hoy
  have hox' : orderOf (ψ x : Gs) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]; exact hox
  have hoy' : orderOf (ψ y : Gs) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]; exact hoy
  exact ⟨fun _ => hone' _ _ ((hmem x).1 hx) ((hmem y).1 hy) hox' hoy',
    fun _ => hone _ _ hx hy hox hoy⟩

end CFSG.GH74.GLS.Stage2.Final
