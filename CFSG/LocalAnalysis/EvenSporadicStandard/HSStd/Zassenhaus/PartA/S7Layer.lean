module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Bridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FS79Lemma15Guarded

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.LocalCores
open scoped commutatorElement

theorem nonabelian_of_simple_s7layer {H : Type} [Group H] [Finite H] (hs : IsSimpleGroup H)
    (hc : ¬ (Nat.card H).Prime) : ∃ a b : H, a * b ≠ b * a := by
  by_contra hno
  push Not at hno
  let _ : CommGroup H := { ‹Group H› with mul_comm := fun a b => hno a b }
  exact hc IsSimpleGroup.prime_card

theorem qs_alt6_s7layer : CFSG.IsQuasisimple (alternatingGroup (Fin 6)) := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have := hs
  refine (isQuasisimple_of_isSimpleGroup (nonabelian_of_simple_s7layer hs ?_)).1
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]
  norm_num

theorem cover_layer_lift {X T : Type*} [Group X] [Group T] (E : Subgroup X) [E.Normal]
    (f : ↥E →* T) (hf : Function.Surjective f) (hker : f.ker ≤ center ↥E)
    (N : Subgroup T) [N.Normal] (hN : CFSG.IsQuasisimple ↥N) :
    ∀ n ∈ N, ∃ k : ↥E, (k : X) ∈ CFSG.layer X ∧ f k = n := by
  classical
  let P : Subgroup ↥E := N.comap f
  have : P.Normal := Subgroup.Normal.comap inferInstance f
  let g : ↥P →* ↥N := (f.comp P.subtype).codRestrict N (fun p => p.2)
  have hg : Function.Surjective g := by
    intro n
    obtain ⟨e, he⟩ := hf n
    exact ⟨⟨e, by show f e ∈ N; rw [he]; exact n.2⟩, Subtype.ext he⟩
  have hgk : g.ker ≤ center ↥P := by
    intro p hp
    have h1 : f p = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hp)
      exact (show f p = ((g p : ↥N) : T) from rfl).trans this
    have hc : (p : E) ∈ center ↥E := hker (MonoidHom.mem_ker.2 h1)
    rw [mem_center_iff]
    intro q
    exact Subtype.ext (mem_center_iff.1 hc q)
  obtain ⟨-, -, hsurj⟩ := central_extension_derived_of_surjective g hg hgk hN.1
  have hqs := quasisimple_central_extension_derived_of_surjective g hg hgk hN
  let ι : ↥P →* X := E.subtype.comp P.subtype
  have hι : Function.Injective ι := E.subtype_injective.comp P.subtype_injective
  let C : Subgroup ↥P := commutator ↥P
  have hCq : CFSG.IsQuasisimple (C.map ι) :=
    isQuasisimple_of_mulEquiv (C.equivMapOfInjective ι hι) hqs
  have hCeq : C.map P.subtype = ⁅P, P⁆ := by
    show (commutator ↥P).map P.subtype = _
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have : (C.map P.subtype).Normal := by rw [hCeq]; infer_instance
  have hmap : C.map ι = (C.map P.subtype).map E.subtype := (Subgroup.map_map _ _ _).symm
  have hsub : (C.map ι).IsSubnormal := by
    have hle : C.map ι ≤ E := by
      rintro _ ⟨c, -, rfl⟩
      exact (c : E).2
    have hsub' : (C.map ι).subgroupOf E = C.map P.subtype := by
      rw [hmap]
      exact Subgroup.comap_map_eq_self_of_injective E.subtype_injective _
    exact Subgroup.IsSubnormal.trans hle (by rw [hsub']; exact Subgroup.Normal.isSubnormal inferInstance)
      (Subgroup.Normal.isSubnormal inferInstance)
  have hlayer : C.map ι ≤ CFSG.layer X := component_le_layer ⟨hCq, hsub⟩
  intro n hn
  obtain ⟨c, hc⟩ := hsurj ⟨n, hn⟩
  refine ⟨(c : P), hlayer ⟨c, c.2, rfl⟩, ?_⟩
  exact congrArg Subtype.val hc

theorem perfect_cover_le_layer {X : Type} [Group X] [Finite X] (E : Subgroup X) [E.Normal]
    (hE : ⁅E, E⁆ = E) (f : ↥E →* alternatingGroup (Fin 6) × alternatingGroup (Fin 6))
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center ↥E) : E ≤ CFSG.layer X := by
  classical
  let N1 : Subgroup (alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) :=
    (MonoidHom.inl (alternatingGroup (Fin 6)) (alternatingGroup (Fin 6))).range
  let N2 : Subgroup (alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) :=
    (MonoidHom.inr (alternatingGroup (Fin 6)) (alternatingGroup (Fin 6))).range
  have : N1.Normal := ⟨by
    rintro _ ⟨a, rfl⟩ g
    exact ⟨g.1 * a * g.1⁻¹, by ext <;> simp⟩⟩
  have : N2.Normal := ⟨by
    rintro _ ⟨a, rfl⟩ g
    exact ⟨g.2 * a * g.2⁻¹, by ext <;> simp⟩⟩
  have hN1 : CFSG.IsQuasisimple ↥N1 :=
    isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (f := MonoidHom.inl (alternatingGroup (Fin 6)) (alternatingGroup (Fin 6)))
      (fun a b h => (Prod.ext_iff.1 h).1)) qs_alt6_s7layer
  have hN2 : CFSG.IsQuasisimple ↥N2 :=
    isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (f := MonoidHom.inr (alternatingGroup (Fin 6)) (alternatingGroup (Fin 6)))
      (fun a b h => (Prod.ext_iff.1 h).2)) qs_alt6_s7layer
  have : (CFSG.layer X).Characteristic := layer_characteristic
  have : ((CFSG.layer X).comap E.subtype).Normal :=
    Subgroup.Normal.comap inferInstance E.subtype
  let Y : Subgroup ↥E := (CFSG.layer X).comap E.subtype
  have hperf : commutator ↥E = ⊤ := by
    rw [_root_.commutator_def]
    have := Subgroup.isPerfect_iff.2 hE
    rw [Group.isPerfect_def, _root_.commutator_def] at this
    exact this
  have hcomm : ⁅(⊤ : Subgroup ↥E), ⊤⁆ ≤ Y := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨k1, hk1, hf1⟩ := cover_layer_lift (X := X) E f hf hker N1 hN1 ((f a).1, 1)
      ⟨(f a).1, rfl⟩
    obtain ⟨k2, hk2, hf2⟩ := cover_layer_lift (X := X) E f hf hker N2 hN2 (1, (f a).2)
      ⟨(f a).2, rfl⟩
    have hk1Y : k1 ∈ Y := hk1
    have hk2Y : k2 ∈ Y := hk2
    have hkY : k1 * k2 ∈ Y := Y.mul_mem hk1Y hk2Y
    have hfk : f (k1 * k2) = f a := by
      rw [map_mul, hf1, hf2]
      ext <;> simp
    have hz : (k1 * k2)⁻¹ * a ∈ center ↥E := by
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfk, inv_mul_cancel]
    set z := (k1 * k2)⁻¹ * a with hzdef
    have ha : a = (k1 * k2) * z := by rw [hzdef]; group
    have hzb : z * b = b * z := (mem_center_iff.1 hz b).symm
    have hcz : ⁅a, b⁆ = ⁅k1 * k2, b⁆ := by
      rw [ha, commutatorElement_def, commutatorElement_def]
      calc k1 * k2 * z * b * (k1 * k2 * z)⁻¹ * b⁻¹
          = k1 * k2 * (z * b) * z⁻¹ * (k1 * k2)⁻¹ * b⁻¹ := by group
        _ = k1 * k2 * (b * z) * z⁻¹ * (k1 * k2)⁻¹ * b⁻¹ := by rw [hzb]
        _ = k1 * k2 * b * (k1 * k2)⁻¹ * b⁻¹ := by group
    rw [hcz, commutatorElement_def]
    have hconj : b * (k1 * k2)⁻¹ * b⁻¹ ∈ Y :=
      (inferInstance : Y.Normal).conj_mem _ (Y.inv_mem hkY) b
    have : (k1 * k2) * b * (k1 * k2)⁻¹ * b⁻¹ = (k1 * k2) * (b * (k1 * k2)⁻¹ * b⁻¹) := by group
    rw [this]
    exact Y.mul_mem hkY hconj
  intro e he
  have : (⟨e, he⟩ : ↥E) ∈ Y := by
    apply hcomm
    rw [← _root_.commutator_def, hperf]
    exact mem_top _
  exact this

theorem layerIn_eq_componentLayerOf {G : Type} [Group G] (H : Subgroup G) :
    CFSG.EvenSporadicStandard.Induction.layerIn H = CFSG.GorensteinWalter.componentLayerOf H := by
  unfold CFSG.EvenSporadicStandard.Induction.layerIn CFSG.GorensteinWalter.componentLayerOf
  congr 1
  ext M
  constructor
  · rintro ⟨h1, h2⟩
    exact (gw_isComponentOf_iff h1).2 h2
  · intro h
    exact ⟨h.1, (gw_isComponentOf_iff h.1).1 h⟩

theorem le_componentLayer_of_balance {G : Type} [Group G] [Finite G]
    (h15 : CFSG.EvenSporadicStandard.Induction.FS79Lemma15Sec G)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hO : CFSG.oddCore G = ⊥) (ub : G) (F0 : Subgroup G) (hF2 : IsPGroup 2 F0) (hub : ub ∈ F0)
    (E1 : Subgroup G) (hE : ⁅E1, E1⁆ = E1) (hEF : E1 ≤ Subgroup.centralizer (F0 : Set G))
    (hn : ∀ x ∈ Subgroup.centralizer (F0 : Set G), ∀ e ∈ E1, x * e * x⁻¹ ∈ E1)
    (f : ↥E1 →* alternatingGroup (Fin 6) × alternatingGroup (Fin 6))
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center ↥E1) :
    E1 ≤ CFSG.GorensteinWalter.componentLayerOf (Subgroup.centralizer ({ub} : Set G)) := by
  classical
  have hU : E1 ≤ CFSG.GorensteinWalter.componentLayerOf (Subgroup.centralizer (F0 : Set G)) := by
    let U : Subgroup G := Subgroup.centralizer (F0 : Set G)
    let e : ↥(E1.subgroupOf U) ≃* ↥E1 := Subgroup.subgroupOfEquivOfLe hEF
    have : (E1.subgroupOf U).Normal := ⟨fun n hn' g => by
      rw [Subgroup.mem_subgroupOf] at hn' ⊢
      exact hn g g.2 n hn'⟩
    have : Group.IsPerfect ↥E1 := Subgroup.isPerfect_iff.2 hE
    have : Group.IsPerfect ↥(E1.subgroupOf U) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hperf : ⁅E1.subgroupOf U, E1.subgroupOf U⁆ = E1.subgroupOf U :=
      Subgroup.isPerfect_iff.1 inferInstance
    have key := perfect_cover_le_layer (X := ↥U) (E1.subgroupOf U) hperf
      (f.comp e.toMonoidHom) (hf.comp e.surjective) (by
        intro x hx
        have hx1 : f (e x) = 1 := hx
        have hc : (e x : ↥E1) ∈ center ↥E1 := hker hx1
        rw [mem_center_iff]
        intro y
        apply e.injective
        rw [map_mul, map_mul]
        exact mem_center_iff.1 hc (e y))
    rw [componentLayerOf_eq]
    intro g hg
    exact ⟨⟨g, hEF hg⟩, key (Subgroup.mem_subgroupOf.2 hg), rfl⟩
  rw [← layerIn_eq_componentLayerOf] at hU ⊢
  have hS : IsPGroup 2 ↥(zpowers ub) := hF2.to_le (zpowers_le.2 hub)
  obtain ⟨hF1, hF2'⟩ := h15.at hkp F0 hF2
  obtain ⟨-, hT2'⟩ := h15.at hkp (zpowers ub) hS
  have e1 := hF2' hO
  have e2 := hT2' hO
  have e3 := hF1 (zpowers ub) (zpowers_le.2 hub)
  have hcz : Subgroup.centralizer ((zpowers ub : Subgroup G) : Set G) =
      Subgroup.centralizer ({ub} : Set G) := by
    refine le_antisymm (Subgroup.centralizer_le ?_) (fun g hg => ?_)
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact mem_zpowers x
    · rw [mem_centralizer_singleton_iff] at hg
      rw [mem_centralizer_iff]
      rintro h ⟨k, rfl⟩
      exact ((Commute.zpow_left (show Commute ub g from hg.symm) k)).eq
  rw [hcz] at e2 e3
  refine hU.trans ?_
  rw [← e1, ← e2]
  exact e3

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
