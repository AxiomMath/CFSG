module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78InputsGen
public import CFSG.LocalAnalysis.ComponentClassification.SolvablePrimeCoreLayerLift

public section

namespace CFSG.ComponentClassification.SolMax.HeGen

open CFSG Subgroup

@[expose] def GenAt (G : Type) [Group G] (s : MulAut G) : Prop :=
  ∀ m : ℕ, (Nonempty (Sol78.layerOfFixed s ≃* alternatingGroup (Fin m)) ∨
      Sol78.IsTripleCoverAltSeven (Sol78.layerOfFixed s)) →
    ∀ (e : Sol78.layerOfFixed s ⧸ pPrimeCore 2 (Sol78.layerOfFixed s) ≃*
        alternatingGroup (Fin m)) (F : Subgroup G), F ≤ Sol78.layerOfFixed s →
      Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
      (∃ D : Finset (Fin m), D.card = 4 ∧ ∀ x : Sol78.layerOfFixed s, (x : G) ∈ F → ∀ ω ∉ D,
        ((e (x : Sol78.layerOfFixed s ⧸ pPrimeCore 2 (Sol78.layerOfFixed s)) :
          alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) ω = ω) →
      Sol78.layerOfFixed s ⊔ normalizer (F : Set G) = ⊤

@[expose] def layerIn {X : Type*} [Group X] (C : Subgroup X) : Subgroup X :=
  (pLayer C 2).map C.subtype

theorem layerIn_le {X : Type*} [Group X] (C : Subgroup X) : layerIn C ≤ C := by
  intro y hy
  rw [layerIn, Subgroup.mem_map] at hy
  obtain ⟨x, -, rfl⟩ := hy
  exact x.2

theorem pLayer_two_commutator_eq (Y : Type*) [Group Y] :
    ⁅pLayer Y 2, pLayer Y 2⁆ = pLayer Y 2 := by
  apply le_antisymm (Subgroup.commutator_le_self _)
  apply sSup_le
  intro M hM
  have : Group.IsPerfect M := CatalogueBAlternating.pComponent_perfect hM
  rw [← Subgroup.commutator_eq_self (H := M)]
  exact Subgroup.commutator_mono (le_sSup hM) (le_sSup hM)

theorem layerIn_perfect {X : Type*} [Group X] (C : Subgroup X) :
    ⁅layerIn C, layerIn C⁆ = layerIn C := by
  rw [layerIn, ← Subgroup.map_commutator, pLayer_two_commutator_eq]

theorem conj_mem_layerIn {X : Type*} [Group X] [Finite X] (C : Subgroup X) {g : X} (hg : g ∈ C)
    {k : X} (hk : k ∈ layerIn C) : g * k * g⁻¹ ∈ layerIn C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := CatalogueBPrimeJoin.pLayer_characteristic (G := ↥C) (p := 2)
  have hn : (pLayer ↥C 2).Normal := inferInstance
  rw [layerIn, Subgroup.mem_map] at hk ⊢
  obtain ⟨k', hk', rfl⟩ := hk
  exact ⟨⟨g, hg⟩ * k' * ⟨g, hg⟩⁻¹, hn.conj_mem k' hk' _, rfl⟩

theorem pLayer_map_mulEquiv {H K : Type*} [Group H] [Group K] [Finite H] [Finite K] (p : ℕ)
    (hp : p.Prime) (ψ : H ≃* K) : (pLayer H p).map ψ.toMonoidHom = pLayer K p := by
  have hT := LocalAnalysis.ComponentInitial.p_component_isomorphism_transport p hp ψ
  have hT' := LocalAnalysis.ComponentInitial.p_component_isomorphism_transport p hp ψ.symm
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup ((hT.1 L).1 hL)
  · refine sSup_le fun L hL => ?_
    have h1 : (L.map ψ.symm.toMonoidHom).map ψ.toMonoidHom = L := by
      rw [Subgroup.map_map]
      convert L.map_id
      ext x
      simp
    rw [← h1]
    exact Subgroup.map_mono (le_sSup ((hT'.1 L).1 hL))

theorem map_layerIn_eq {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y] {ρ : X →* Y}
    (hρ : Function.Injective ρ) {H : Subgroup X} {K : Subgroup Y} (hHK : H.map ρ = K) :
    (layerIn H).map ρ = layerIn K := by
  set ψ : H ≃* K := (H.equivMapOfInjective ρ hρ).trans (MulEquiv.subgroupCongr hHK)
  have hcomp : ρ.comp H.subtype = K.subtype.comp ψ.toMonoidHom := by
    ext x
    rfl
  rw [layerIn, layerIn, Subgroup.map_map, hcomp, ← Subgroup.map_map,
    pLayer_map_mulEquiv 2 Nat.prime_two ψ]

theorem map_signalizerFixedSubgroup_congr {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G')
    (s : MulAut G) :
    (Open.signalizerFixedSubgroup s).map φ.toMonoidHom =
      Open.signalizerFixedSubgroup (MulAut.congr φ s) := by
  ext t
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change φ (s (φ.symm (φ x))) = φ x
    rw [MulEquiv.symm_apply_apply]
    exact congrArg φ (show s x = x from hx)
  · intro ht
    refine ⟨φ.symm t, ?_, φ.apply_symm_apply t⟩
    change s (φ.symm t) = φ.symm t
    apply φ.injective
    rw [MulEquiv.apply_symm_apply]
    exact ht

theorem layerOfFixed_eq_layerIn {G : Type*} [Group G] (s : MulAut G) :
    Sol78.layerOfFixed s = layerIn (Open.signalizerFixedSubgroup s) := rfl

theorem layerOfFixed_congr {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (φ : G ≃* G') (s : MulAut G) :
    Sol78.layerOfFixed (MulAut.congr φ s) = (Sol78.layerOfFixed s).map φ.toMonoidHom := by
  rw [layerOfFixed_eq_layerIn, layerOfFixed_eq_layerIn,
    map_layerIn_eq φ.injective (map_signalizerFixedSubgroup_congr φ s)]

theorem isTripleCoverAltSeven_of_map {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G')
    {L : Subgroup G} {L' : Subgroup G'} (hLL : L' = L.map φ.toMonoidHom) (ψ : L ≃* L')
    (h : Sol78.IsTripleCoverAltSeven L) : Sol78.IsTripleCoverAltSeven L' := by
  unfold Sol78.IsTripleCoverAltSeven at h ⊢
  obtain ⟨h1, h2, ⟨q⟩⟩ := h
  refine ⟨by rw [hLL, ← Subgroup.map_commutator, h1], ?_, ⟨?_⟩⟩
  · rw [← h2]
    exact (Nat.card_congr (Subgroup.centerCongr ψ).toEquiv).symm
  · exact (QuotientGroup.congr (center L) (center L') ψ (Subgroup.map_center_eq ψ)).symm.trans q

theorem genAt_of_congr {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] (φ : G ≃* G')
    (s : MulAut G) (h : GenAt G' (MulAut.congr φ s)) : GenAt G s := by
  intro m hL e F hFL hF hD
  have hLL := layerOfFixed_congr φ s
  set L := Sol78.layerOfFixed s with hLdef
  set L' := Sol78.layerOfFixed (MulAut.congr φ s) with hL'def
  let ψ : L ≃* L' :=
    (L.equivMapOfInjective φ.toMonoidHom φ.injective).trans (MulEquiv.subgroupCongr hLL.symm)
  have hψ : ∀ x : L, ((ψ x : L') : G') = φ x := fun x => rfl
  have hO : (pPrimeCore 2 L).map ψ.toMonoidHom = pPrimeCore 2 L' := pPrimeCore_map_iso 2 ψ
  let q : L ⧸ pPrimeCore 2 L ≃* L' ⧸ pPrimeCore 2 L' := QuotientGroup.congr _ _ ψ hO
  have hq : ∀ x : L, q.symm ((ψ x : L') : L' ⧸ pPrimeCore 2 L') = (x : L ⧸ pPrimeCore 2 L) :=
    fun x => q.symm_apply_eq.2 rfl
  have hL' : Nonempty (L' ≃* alternatingGroup (Fin m)) ∨ Sol78.IsTripleCoverAltSeven L' := by
    rcases hL with he₀ | hT
    · exact Or.inl ⟨ψ.symm.trans he₀.some⟩
    · exact Or.inr (isTripleCoverAltSeven_of_map φ hLL ψ hT)
  have hFL' : F.map φ.toMonoidHom ≤ L' := by
    rw [hLL]
    exact Subgroup.map_mono hFL
  have hF' : Nonempty (F.map φ.toMonoidHom ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    ⟨(F.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans hF.some⟩
  have hD' : ∃ D : Finset (Fin m), D.card = 4 ∧ ∀ x : L', (x : G') ∈ F.map φ.toMonoidHom →
      ∀ ω ∉ D, ((q.symm.trans e (x : L' ⧸ pPrimeCore 2 L') : alternatingGroup (Fin m)) :
        Equiv.Perm (Fin m)) ω = ω := by
    obtain ⟨D, hD4, hDfix⟩ := hD
    refine ⟨D, hD4, fun x' hx' ω hω => ?_⟩
    have hx : x' = ψ (ψ.symm x') := (ψ.apply_symm_apply x').symm
    have hmem : ((ψ.symm x' : L) : G) ∈ F := by
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'
      have : φ y = φ (ψ.symm x') := by
        rw [MulEquiv.coe_toMonoidHom] at hyx
        rw [hyx, ← hψ, ← hx]
      rwa [φ.injective this] at hy
    rw [hx, MulEquiv.trans_apply, hq]
    exact hDfix _ hmem ω hω
  have hgen := h m hL' (q.symm.trans e) (F.map φ.toMonoidHom) hFL' hF' hD'
  apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
  rw [Subgroup.map_sup, ← hLL, Subgroup.map_equiv_normalizer_eq, hgen,
    Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective]

end CFSG.ComponentClassification.SolMax.HeGen
