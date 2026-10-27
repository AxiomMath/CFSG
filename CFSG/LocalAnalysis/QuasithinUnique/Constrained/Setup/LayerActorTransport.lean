module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
public import CFSG.LocalAnalysis.QuasithinUnique.BenderInterfaces
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.QuasithinUnique.Setup.Layer.Actor

open CFSG.LocalCores CFSG.QuasithinUnique
open scoped commutatorElement

section Sub

variable {G G' : Type*} [Group G] [Group G']

theorem mem_map_equiv_iff (ψ : G ≃* G') {x : G} {X : Subgroup G} :
    ψ x ∈ X.map ψ.toMonoidHom ↔ x ∈ X :=
  Subgroup.mem_map_iff_mem (f := ψ.toMonoidHom) ψ.injective

@[expose] def mapEquiv (ψ : G ≃* G') (H : Subgroup G) : ↥H ≃* ↥(H.map ψ.toMonoidHom) :=
  ψ.subgroupMap H

theorem mapEquiv_coe (ψ : G ≃* G') (H : Subgroup G) (x : ↥H) :
    ((mapEquiv ψ H x : ↥(H.map ψ.toMonoidHom)) : G') = ψ (x : G) := rfl

theorem subtype_comp_mapEquiv (ψ : G ≃* G') (H : Subgroup G) :
    (H.map ψ.toMonoidHom).subtype.comp (mapEquiv ψ H).toMonoidHom =
      ψ.toMonoidHom.comp H.subtype :=
  MonoidHom.ext fun _ => rfl

theorem map_subtype_map (ψ : G ≃* G') (H : Subgroup G) (X : Subgroup ↥H) :
    (X.map (mapEquiv ψ H).toMonoidHom).map (H.map ψ.toMonoidHom).subtype =
      (X.map H.subtype).map ψ.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map, subtype_comp_mapEquiv]

theorem map_subgroupOf (ψ : G ≃* G') (H X : Subgroup G) :
    (X.subgroupOf H).map (mapEquiv ψ H).toMonoidHom =
      (X.map ψ.toMonoidHom).subgroupOf (H.map ψ.toMonoidHom) := by
  ext ⟨y, hy⟩
  obtain ⟨h, hh, rfl⟩ := id hy
  have e1 : (⟨ψ.toMonoidHom h, hy⟩ : ↥(H.map ψ.toMonoidHom)) = mapEquiv ψ H ⟨h, hh⟩ := rfl
  rw [e1, mem_map_equiv_iff (mapEquiv ψ H), Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact (mem_map_equiv_iff ψ).symm

end Sub

section Char

variable {A B : Type*} [Group A] [Group B]

theorem isNilpotent_map_mulEquiv_iff (e : A ≃* B) {N : Subgroup A} :
    Group.IsNilpotent ↥(N.map e.toMonoidHom) ↔ Group.IsNilpotent ↥N := by
  have eN : ↥N ≃* ↥(N.map e.toMonoidHom) := N.equivMapOfInjective e.toMonoidHom e.injective
  constructor
  · intro h
    have := h
    exact Group.nilpotent_of_mulEquiv eN.symm
  · intro h
    have := h
    exact Group.nilpotent_of_mulEquiv eN

theorem map_sSup_normal (e : A ≃* B) (PA : Subgroup A → Prop) (PB : Subgroup B → Prop)
    (h1 : ∀ N, PA N → PB (N.map e.toMonoidHom))
    (h2 : ∀ N', PB N' → PA (N'.map e.symm.toMonoidHom)) :
    (sSup {N : Subgroup A | N.Normal ∧ PA N}).map e.toMonoidHom =
      sSup {N : Subgroup B | N.Normal ∧ PB N} := by
  change MulEquiv.mapSubgroup e (sSup {N : Subgroup A | N.Normal ∧ PA N}) =
    sSup {N : Subgroup B | N.Normal ∧ PB N}
  rw [OrderIso.map_sSup, ← sSup_image]
  refine congrArg sSup (Set.ext fun N' => ⟨?_, fun hN' => ?_⟩)
  · rintro ⟨N, ⟨hn, hs⟩, rfl⟩
    exact ⟨hn.map _ e.surjective, h1 N hs⟩
  · refine ⟨N'.map e.symm.toMonoidHom, ⟨hN'.1.map _ e.symm.surjective, h2 N' hN'.2⟩, ?_⟩
    exact CFSG.LocalCores.map_map_symm e.symm N' |> fun h => by simpa using h

theorem solvableRadical_map (e : A ≃* B) :
    (CFSG.solvableRadical A).map e.toMonoidHom = CFSG.solvableRadical B :=
  map_sSup_normal e (fun N => Group.IsSolvable ↥N) (fun N => Group.IsSolvable ↥N)
    (fun _ h => (solvable_map_mulEquiv_iff e).2 h)
    (fun _ h => (solvable_map_mulEquiv_iff e.symm).2 h)

theorem fittingSubgroup_map (e : A ≃* B) :
    (CFSG.fittingSubgroup A).map e.toMonoidHom = CFSG.fittingSubgroup B :=
  map_sSup_normal e (fun N => Group.IsNilpotent ↥N) (fun N => Group.IsNilpotent ↥N)
    (fun _ h => (isNilpotent_map_mulEquiv_iff e).2 h)
    (fun _ h => (isNilpotent_map_mulEquiv_iff e.symm).2 h)

theorem isComponent_map_mulEquiv_iff (e : A ≃* B) {K : Subgroup A} :
    CFSG.IsComponent (K.map e.toMonoidHom) ↔ CFSG.IsComponent K := by
  constructor
  · intro h
    have := CFSG.LocalCores.isComponent_map_mulEquiv e.symm h
    rwa [CFSG.LocalCores.map_map_symm] at this
  · exact CFSG.LocalCores.isComponent_map_mulEquiv e

theorem layer_map (e : A ≃* B) :
    (CFSG.layer A).map e.toMonoidHom = CFSG.layer B := by
  change MulEquiv.mapSubgroup e (sSup {K : Subgroup A | CFSG.IsComponent K}) =
    sSup {K : Subgroup B | CFSG.IsComponent K}
  rw [OrderIso.map_sSup, ← sSup_image]
  refine congrArg sSup (Set.ext fun K' => ⟨?_, fun hK' => ?_⟩)
  · rintro ⟨K, hK, rfl⟩
    exact CFSG.LocalCores.isComponent_map_mulEquiv e hK
  · refine ⟨K'.map e.symm.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv e.symm hK', ?_⟩
    exact CFSG.LocalCores.map_map_symm e.symm K' |> fun h => by simpa using h

theorem generalizedFitting_map (e : A ≃* B) :
    (CFSG.generalizedFitting A).map e.toMonoidHom = CFSG.generalizedFitting B := by
  simp only [CFSG.generalizedFitting.eq_sup]
  rw [Subgroup.map_sup, fittingSubgroup_map, layer_map]

end Char

section Ambient

theorem map_ambient {G G' : Type} [Group G] [Group G'] (F : ∀ (K : Type) [Group K], Subgroup K)
    (hF : ∀ {A B : Type} [Group A] [Group B] (e : A ≃* B), (F A).map e.toMonoidHom = F B)
    (ψ : G ≃* G') (H : Subgroup G) :
    (F ↥(H.map ψ.toMonoidHom)).map (H.map ψ.toMonoidHom).subtype =
      ((F ↥H).map H.subtype).map ψ.toMonoidHom := by
  rw [← hF (mapEquiv ψ H), map_subtype_map]

variable {G G' : Type*} [Group G] [Group G']

theorem normalCore_map (ψ : G ≃* G') (S : Subgroup G) :
    S.normalCore.map ψ.toMonoidHom = (S.map ψ.toMonoidHom).normalCore := by
  ext y
  obtain ⟨x, rfl⟩ := ψ.surjective y
  rw [mem_map_equiv_iff ψ]
  show (∀ g : G, g * x * g⁻¹ ∈ S) ↔ ∀ g' : G', g' * ψ x * g'⁻¹ ∈ S.map ψ.toMonoidHom
  constructor
  · intro h g'
    obtain ⟨g, rfl⟩ := ψ.surjective g'
    have : ψ (g * x * g⁻¹) ∈ S.map ψ.toMonoidHom := ⟨_, h g, rfl⟩
    simpa using this
  · intro h g
    have := h (ψ g)
    rw [← map_inv, ← map_mul, ← map_mul] at this
    exact (mem_map_equiv_iff ψ).1 this

theorem map_normalCore_subgroupOf (ψ : G ≃* G') (H M : Subgroup G) :
    ((M.map ψ.toMonoidHom).subgroupOf (H.map ψ.toMonoidHom)).normalCore.map
        (H.map ψ.toMonoidHom).subtype =
      ((M.subgroupOf H).normalCore.map H.subtype).map ψ.toMonoidHom := by
  rw [← map_subgroupOf, ← normalCore_map, map_subtype_map]

theorem map_closure_odd (ψ : G ≃* G') (H : Subgroup G) :
    (Subgroup.closure {x | x ∈ H ∧ Odd (orderOf x)}).map ψ.toMonoidHom =
      Subgroup.closure {y | y ∈ H.map ψ.toMonoidHom ∧ Odd (orderOf y)} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, ho⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rwa [orderOf_injective ψ.toMonoidHom ψ.injective]⟩
  · rintro ⟨⟨x, hx, rfl⟩, ho⟩
    exact ⟨x, ⟨hx, by rwa [orderOf_injective ψ.toMonoidHom ψ.injective] at ho⟩, rfl⟩

theorem map_inf_centralizer (ψ : G ≃* G') (K : Subgroup G) :
    (K ⊓ Subgroup.centralizer (K : Set G)).map ψ.toMonoidHom =
      K.map ψ.toMonoidHom ⊓ Subgroup.centralizer ((K.map ψ.toMonoidHom : Subgroup G') : Set G') :=
          by
  ext y
  obtain ⟨x, rfl⟩ := ψ.surjective y
  rw [mem_map_equiv_iff ψ, Subgroup.mem_inf, Subgroup.mem_inf,
    mem_map_equiv_iff ψ]
  refine and_congr_right fun _ => ?_
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h z hz
    obtain ⟨k, hk, rfl⟩ := hz
    show ψ k * ψ x = ψ x * ψ k
    rw [← map_mul, ← map_mul, h k hk]
  · intro h k hk
    have := h (ψ k) ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact ψ.injective this

theorem isComponentIn_map_iff (ψ : G ≃* G') {L H : Subgroup G} :
    IsComponentIn (L.map ψ.toMonoidHom) (H.map ψ.toMonoidHom) ↔ IsComponentIn L H := by
  unfold IsComponentIn
  rw [Subgroup.map_le_map_iff_of_injective ψ.injective, ← map_subgroupOf ψ H L]
  exact and_congr_right fun _ => isComponent_map_mulEquiv_iff (mapEquiv ψ H)

end Ambient

section Nested

variable {X : Type*} [Group X]

theorem normal_subgroupOf_subgroupOf_iff {L K H : Subgroup X} (hLK : L ≤ K) (hKH : K ≤ H) :
    (L.subgroupOf K).Normal ↔ ((L.subgroupOf H).subgroupOf (K.subgroupOf H)).Normal := by
  have hLK' : L.subgroupOf H ≤ K.subgroupOf H := fun x hx => hLK hx
  rw [Subgroup.normal_subgroupOf_iff hLK, Subgroup.normal_subgroupOf_iff hLK']
  constructor
  · intro h l k hl hk
    exact h l k hl hk
  · intro h l k hl hk
    exact h ⟨l, hKH (hLK hl)⟩ ⟨k, hKH hk⟩ hl hk

theorem map_center_subgroupOf {K H : Subgroup X} (hKH : K ≤ H) :
    ((Subgroup.center ↥(K.subgroupOf H)).map (K.subgroupOf H).subtype).map H.subtype =
      K ⊓ Subgroup.centralizer (K : Set X) := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨z.2, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
    have := Subgroup.mem_center_iff.1 hz ⟨⟨k, hKH hk⟩, hk⟩
    have h2 := congrArg (fun y : ↥(K.subgroupOf H) => ((y : ↥H) : X)) this
    exact h2
  · rintro ⟨hxK, hxc⟩
    refine ⟨((⟨x, hKH hxK⟩ : ↥H)), ⟨⟨⟨x, hKH hxK⟩, hxK⟩, Subgroup.mem_center_iff.2 fun y => ?_,
        rfl⟩, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    show ((y : ↥H) : X) * x = x * ((y : ↥H) : X)
    exact Subgroup.mem_centralizer_iff.1 hxc _ y.2

theorem map_conj_subtype {H : Subgroup X} (L : Subgroup ↥H) (t : ↥H) :
    (L.map (MulAut.conj t).toMonoidHom).map H.subtype =
      (L.map H.subtype).map (MulAut.conj (t : X)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

end Nested

section Ambient2

variable {G G' : Type*} [Group G] [Group G']

theorem map_le_normalizer_iff (ψ : G ≃* G') {A L : Subgroup G} :
    A.map ψ.toMonoidHom ≤ Subgroup.normalizer ((L.map ψ.toMonoidHom : Subgroup G') : Set G') ↔
      A ≤ Subgroup.normalizer (L : Set G) := by
  constructor
  · intro h a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 : ψ a ∈ A.map ψ.toMonoidHom := ⟨a, ha, rfl⟩
    have := Subgroup.mem_normalizer_iff.1 (h h1) (ψ x)
    have e : ψ a * ψ x * (ψ a)⁻¹ = ψ (a * x * a⁻¹) := by simp
    rw [e] at this
    exact ((mem_map_equiv_iff ψ).symm.trans this).trans (mem_map_equiv_iff ψ)
  · intro hA g hg
    obtain ⟨a, ha, rfl⟩ := hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨x, rfl⟩ := ψ.surjective y
    have e : ψ a * ψ x * (ψ a)⁻¹ = ψ (a * x * a⁻¹) := by simp
    have := Subgroup.mem_normalizer_iff.1 (hA ha) x
    show ψ x ∈ L.map ψ.toMonoidHom ↔ ψ a * ψ x * (ψ a)⁻¹ ∈ L.map ψ.toMonoidHom
    rw [e]
    exact ((mem_map_equiv_iff ψ).trans this).trans (mem_map_equiv_iff ψ).symm

theorem map_map_conj (ψ : G ≃* G') (L : Subgroup G) (t : G) :
    (L.map (MulAut.conj t).toMonoidHom).map ψ.toMonoidHom =
      (L.map ψ.toMonoidHom).map (MulAut.conj (ψ t)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem map_commutator_mulEquiv (ψ : G ≃* G') (A B : Subgroup G) :
    ⁅A, B⁆.map ψ.toMonoidHom = ⁅A.map ψ.toMonoidHom, B.map ψ.toMonoidHom⁆ :=
  Subgroup.map_commutator A B ψ.toMonoidHom

theorem layer_map_subtype_eq_iSup (H : Subgroup G) :
    (CFSG.layer ↥H).map H.subtype = ⨆ (L : Subgroup G) (_ : IsComponentIn L H), L := by
  simp only [CFSG.layer.eq_sSup]
  rw [sSup_eq_iSup, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun K => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hK => ?_
    refine le_iSup₂_of_le (K.map H.subtype) ⟨Subgroup.map_subtype_le K, ?_⟩ le_rfl
    have : (K.map H.subtype).subgroupOf H = K :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective K
    rw [this]
    exact hK
  · refine iSup₂_le fun L hL => ?_
    refine le_iSup_of_le (L.subgroupOf H) ?_
    rw [Subgroup.map_iSup]
    refine le_iSup_of_le hL.2 ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hL.1]

end Ambient2

section FiniteComm

variable {X : Type*} [Group X] [Finite X]

theorem commutator_eq_bot_of_isComponentIn_ne' {G Y Z : Subgroup X}
    (hY : IsComponentIn Y G) (hZ : IsComponentIn Z G) (hne : Y ≠ Z) : ⁅Y, Z⁆ = ⊥ := by
  have hne' : Y.subgroupOf G ≠ Z.subgroupOf G := fun h => hne (by
    have h1 := congrArg (Subgroup.map G.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hY.1, Subgroup.map_subgroupOf_eq_of_le hZ.1] at h1)
  rcases CFSG.LocalCores.distinct_components_commute hY.2 hZ.2 with h | h
  · exact absurd h hne'
  · refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun x hx => ?_
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h (show (⟨x, hY.1 hx⟩ : ↥G) ∈
      Y.subgroupOf G from hx)
    have h2 := Subgroup.mem_centralizer_iff.1 h1 ⟨y, hZ.1 hy⟩ (show (⟨y, hZ.1 hy⟩ : ↥G) ∈
      Z.subgroupOf G from hy)
    exact congrArg Subtype.val h2

end FiniteComm

end CFSG.QuasithinUnique.Setup.Layer.Actor
