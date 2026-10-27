module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.I32Basic

public section

namespace CFSG.QuasithinUnique.I32

open CFSG.ComponentClassification

section Orbit

variable {Y : Type*} [Group Y] [Finite Y]

@[expose] def orbitSub (s : Y) (K : Subgroup Y) : Subgroup Y := K ⊔ CFSG.conjugate K s

@[expose] def orbitFamily (s : Y) : Set (Subgroup Y) :=
  {A | ∃ K : Subgroup Y, CFSG.Open.IsComponentOf K ⊤ ∧ A = orbitSub s K}

omit [Finite Y] in
theorem isComponentOf_conjugate {K : Subgroup Y} (hK : CFSG.Open.IsComponentOf K ⊤) (g : Y) :
    CFSG.Open.IsComponentOf (CFSG.conjugate K g) ⊤ :=
  (LocalComponents.equiv_iff (MulAut.conj g⁻¹) K).mpr hK

theorem layer_le_normalizer {K : Subgroup Y} (hK : CFSG.Open.IsComponentOf K ⊤) :
    Layer.subgroup Y ≤ Subgroup.normalizer (K : Set Y) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Layer.component_le hK)).mp
    (Layer.normal_component hK)

theorem commute_of_ne_component {K K' : Subgroup Y} (hK : CFSG.Open.IsComponentOf K ⊤)
    (hK' : CFSG.Open.IsComponentOf K' ⊤) (hne : K ≠ K') : ⁅K, K'⁆ = ⊥ :=
  LocalComponents.commute_of_ne K K' hK hK' hne

omit [Finite Y] in
theorem isSubnormal_of_le_layer {B : Subgroup Y} (hB : B ≤ Layer.subgroup Y)
    (hn : Layer.subgroup Y ≤ Subgroup.normalizer (B : Set Y)) :
    CFSG.Open.IsSubnormal B ⊤ := by
  have : (Layer.subgroup Y).Normal := Layer.normal Y
  exact CFSG.Open.IsSubnormal.step hB ((Subgroup.normal_subgroupOf_iff_le_normalizer hB).mpr hn)
    (CFSG.Open.IsSubnormal.step le_top Subgroup.normal_subgroupOf (CFSG.Open.IsSubnormal.refl ⊤))

omit [Finite Y] in
theorem mem_normalizer_sup {A B : Subgroup Y} {y : Y} (hA : y ∈ Subgroup.normalizer (A : Set Y))
    (hB : y ∈ Subgroup.normalizer (B : Set Y)) :
    y ∈ Subgroup.normalizer ((A ⊔ B : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

omit [Finite Y] in
theorem commutator_sup_sup_eq_bot {A₁ A₂ B₁ B₂ : Subgroup Y} (h11 : ⁅A₁, B₁⁆ = ⊥)
    (h12 : ⁅A₁, B₂⁆ = ⊥) (h21 : ⁅A₂, B₁⁆ = ⊥) (h22 : ⁅A₂, B₂⁆ = ⊥) :
    ⁅A₁ ⊔ A₂, B₁ ⊔ B₂⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  have hA : ∀ A : Subgroup Y, ⁅A, B₁⁆ = ⊥ → ⁅A, B₂⁆ = ⊥ →
      A ≤ Subgroup.centralizer ((B₁ ⊔ B₂ : Subgroup Y) : Set Y) := by
    intro A h1 h2
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [← Subgroup.le_centralizer_iff]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
    · rw [← Subgroup.le_centralizer_iff]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
  exact sup_le (hA _ h11 h12) (hA _ h21 h22)

variable {s : Y}

omit [Finite Y] in
theorem orbitSub_le_layer {K : Subgroup Y} (hK : CFSG.Open.IsComponentOf K ⊤) :
    orbitSub s K ≤ Layer.subgroup Y :=
  sup_le (Layer.component_le hK) (Layer.component_le (isComponentOf_conjugate hK s))

theorem layer_le_normalizer_orbitSub {K : Subgroup Y} (hK : CFSG.Open.IsComponentOf K ⊤) :
    Layer.subgroup Y ≤ Subgroup.normalizer (orbitSub s K : Set Y) := fun _ hy =>
  mem_normalizer_sup (layer_le_normalizer hK hy)
    (layer_le_normalizer (isComponentOf_conjugate hK s) hy)

omit [Finite Y] in
theorem le_layer_of_mem_orbitFamily {A : Subgroup Y} (hA : A ∈ orbitFamily s) :
    A ≤ Layer.subgroup Y := by
  obtain ⟨K, hK, rfl⟩ := hA
  exact orbitSub_le_layer hK

theorem layer_le_normalizer_of_mem_orbitFamily {A : Subgroup Y} (hA : A ∈ orbitFamily s) :
    Layer.subgroup Y ≤ Subgroup.normalizer (A : Set Y) := by
  obtain ⟨K, hK, rfl⟩ := hA
  exact layer_le_normalizer_orbitSub hK

theorem isSubnormal_of_mem_orbitFamily {A : Subgroup Y} (hA : A ∈ orbitFamily s) :
    CFSG.Open.IsSubnormal A ⊤ :=
  isSubnormal_of_le_layer (le_layer_of_mem_orbitFamily hA)
    (layer_le_normalizer_of_mem_orbitFamily hA)

theorem isSubnormal_sSup_orbitFamily {S : Set (Subgroup Y)} (hS : S ⊆ orbitFamily s) :
    CFSG.Open.IsSubnormal (sSup S) ⊤ := by
  refine isSubnormal_of_le_layer (sSup_le fun B hB => le_layer_of_mem_orbitFamily (hS hB)) ?_
  intro y hy
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, sSup_eq_iSup', Subgroup.map_iSup]
  exact iSup_congr fun B => Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (layer_le_normalizer_of_mem_orbitFamily (hS B.2) hy)

omit [Finite Y] in
theorem map_conj_orbitSub (hs : s * s = 1) (K : Subgroup Y) :
    (orbitSub s K).map (MulAut.conj s).toMonoidHom = orbitSub s K := by
  unfold orbitSub
  rw [Subgroup.map_sup, ← conjugate_eq_map_conj hs, ← conjugate_eq_map_conj hs,
    conjugate_conjugate_self hs, sup_comm]

omit [Finite Y] in
theorem map_conj_of_mem_orbitFamily (hs : s * s = 1) {A : Subgroup Y} (hA : A ∈ orbitFamily s) :
    A.map (MulAut.conj s).toMonoidHom = A := by
  obtain ⟨K, -, rfl⟩ := hA
  exact map_conj_orbitSub hs K

theorem commutator_eq_bot_of_ne_orbit (hs : s * s = 1) {A B : Subgroup Y}
    (hA : A ∈ orbitFamily s) (hB : B ∈ orbitFamily s) (hne : A ≠ B) : ⁅A, B⁆ = ⊥ := by
  obtain ⟨K, hK, rfl⟩ := hA
  obtain ⟨K', hK', rfl⟩ := hB
  have hKs : CFSG.Open.IsComponentOf (CFSG.conjugate K s) ⊤ := isComponentOf_conjugate hK s
  have hKs' : CFSG.Open.IsComponentOf (CFSG.conjugate K' s) ⊤ := isComponentOf_conjugate hK' s
  have h1 : K ≠ K' := fun h => hne (by rw [h])
  have h2 : K ≠ CFSG.conjugate K' s := by
    intro h
    apply hne
    unfold orbitSub
    rw [h, conjugate_conjugate_self hs, sup_comm]
  have h3 : CFSG.conjugate K s ≠ K' := by
    intro h
    apply hne
    unfold orbitSub
    rw [← h, conjugate_conjugate_self hs, sup_comm]
  have h4 : CFSG.conjugate K s ≠ CFSG.conjugate K' s := fun h =>
    h1 (BenderBranch.conjugate_inj.mp h)
  exact commutator_sup_sup_eq_bot (commute_of_ne_component hK hK' h1)
    (commute_of_ne_component hK hKs' h2) (commute_of_ne_component hKs hK' h3)
    (commute_of_ne_component hKs hKs' h4)

omit [Finite Y] in
theorem layer_le_sSup_orbitFamily (s : Y) : Layer.subgroup Y ≤ sSup (orbitFamily s) :=
  sSup_le fun K hK => le_trans (le_sup_left : K ≤ orbitSub s K) (le_sSup ⟨K, hK, rfl⟩)

theorem exists_orbitSub_le (hs : s * s = 1) {C : Subgroup Y}
    (hC : C = Subgroup.centralizer ({s} : Set Y)) {Lc : Subgroup C}
    (hLc : TwoComponents.IsTwoComponent Lc) :
    ∀ S : Set (Subgroup Y), S.Finite → S ⊆ orbitFamily s →
      Lc.map C.subtype ≤ sSup S → ∃ A ∈ S, Lc.map C.subtype ≤ A := by
  classical
  have hfixed : FixedCommutingProduct.fixedSubgroup (MulAut.conj s) = C := by
    rw [hC]
    ext member
    change s * member * s⁻¹ = member ↔ member ∈ Subgroup.centralizer ({s} : Set Y)
    constructor
    · intro heq
      apply Subgroup.mem_centralizer_iff.mpr
      intro singleton hsingleton
      rw [Set.mem_singleton_iff.mp hsingleton]
      calc s * member = (s * member * s⁻¹) * s := by group
        _ = member * s := by rw [heq]
    · intro hmem
      have hcommutes := Subgroup.mem_centralizer_iff.mp hmem s (Set.mem_singleton s)
      rw [hcommutes]
      group
  have : Group.IsPerfect Lc := ⟨TwoComponents.perfect hLc⟩
  have : Group.IsPerfect (Lc.map C.subtype) := Group.IsPerfect.map C.subtype
  intro S hS
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    intro _ hle
    exfalso
    rw [sSup_empty, le_bot_iff] at hle
    have hLcBot : Lc = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective Lc C.subtype_injective).mp hle
    have : Nontrivial Lc := TwoComponents.nontrivial hLc
    exact (Lc.nontrivial_iff_ne_bot.mp inferInstance) hLcBot
  | @insert A S' hAS' hS'fin ih =>
    intro hsub hle
    have hA : A ∈ orbitFamily s := hsub (Set.mem_insert A S')
    have hS'sub : S' ⊆ orbitFamily s := fun B hB => hsub (Set.mem_insert_of_mem A hB)
    have hcomm : ⁅A, sSup S'⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
      refine sSup_le fun B hB => ?_
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (commutator_eq_bot_of_ne_orbit hs (hS'sub hB) hA (fun h => hAS' (h ▸ hB)))
    have hainv : A.map (MulAut.conj s).toMonoidHom = A := map_conj_of_mem_orbitFamily hs hA
    have hTinv : (sSup S').map (MulAut.conj s).toMonoidHom = sSup S' := by
      rw [sSup_eq_iSup', Subgroup.map_iSup]
      exact iSup_congr fun B => map_conj_of_mem_orbitFamily hs (hS'sub B.2)
    have hderived := FixedCommutingProduct.derived_fixed A (sSup S') hcomm (MulAut.conj s)
      hainv hTinv
    rw [hfixed] at hderived
    have hle' : Lc.map C.subtype ≤ A ⊔ sSup S' := by rwa [sSup_insert] at hle
    have hle'' : Lc.map C.subtype ≤ (A ⊔ sSup S') ⊓ C := le_inf hle' (Subgroup.map_subtype_le Lc)
    have hprod : Lc.map C.subtype ≤ (A ⊓ C) ⊔ (sSup S' ⊓ C) :=
      calc Lc.map C.subtype = ⁅Lc.map C.subtype, Lc.map C.subtype⁆ :=
            Subgroup.commutator_eq_self.symm
        _ ≤ ⁅(A ⊔ sSup S') ⊓ C, (A ⊔ sSup S') ⊓ C⁆ := Subgroup.commutator_mono hle'' hle''
        _ ≤ (A ⊓ C) ⊔ (sSup S' ⊓ C) := hderived
    have hlocal : Lc ≤ A.subgroupOf C ⊔ (sSup S').subgroupOf C := by
      have hmap : Lc.map C.subtype ≤
          (A.subgroupOf C ⊔ (sSup S').subgroupOf C).map C.subtype := by
        rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
        exact hprod
      have hcomap := Subgroup.map_le_iff_le_comap.mp hmap
      rwa [Subgroup.comap_map_eq_self_of_injective C.subtype_injective] at hcomap
    have hasub : CFSG.Open.IsSubnormal (A.subgroupOf C) ⊤ :=
      Components.chain_of_mathlib_subnormal
        ((Components.mathlib_subnormal_of_chain (isSubnormal_of_mem_orbitFamily hA)
          Subgroup.IsSubnormal.top).subgroupOf)
    have hTlocalsub : CFSG.Open.IsSubnormal ((sSup S').subgroupOf C) ⊤ :=
      Components.chain_of_mathlib_subnormal
        ((Components.mathlib_subnormal_of_chain (isSubnormal_sSup_orbitFamily hS'sub)
          Subgroup.IsSubnormal.top).subgroupOf)
    have hpairJoin : sSup ({A.subgroupOf C, (sSup S').subgroupOf C} : Set (Subgroup C)) =
        A.subgroupOf C ⊔ (sSup S').subgroupOf C := by simp
    have hpairSub : ∀ s' ∈ ({A.subgroupOf C, (sSup S').subgroupOf C} : Set (Subgroup C)),
        CFSG.Open.IsSubnormal s' ⊤ := by
      intro s' hs'
      rcases Set.mem_insert_iff.mp hs' with rfl | hs'
      · exact hasub
      · rw [Set.mem_singleton_iff.mp hs']
        exact hTlocalsub
    obtain ⟨cont, hcont, hcontle⟩ := TwoComponentJoins.exists_le_of_le_sSup Lc hLc
      ({A.subgroupOf C, (sSup S').subgroupOf C} : Set (Subgroup C)) hpairSub
      (by rwa [hpairJoin])
    rcases Set.mem_insert_iff.mp hcont with rfl | hcont
    · refine ⟨A, Set.mem_insert A S', ?_⟩
      calc Lc.map C.subtype ≤ (A.subgroupOf C).map C.subtype := Subgroup.map_mono hcontle
        _ = A ⊓ C := Subgroup.subgroupOf_map_subtype A C
        _ ≤ A := inf_le_left
    · rw [Set.mem_singleton_iff.mp hcont] at hcontle
      have hT : Lc.map C.subtype ≤ sSup S' :=
        calc Lc.map C.subtype ≤ ((sSup S').subgroupOf C).map C.subtype :=
              Subgroup.map_mono hcontle
          _ = sSup S' ⊓ C := Subgroup.subgroupOf_map_subtype _ C
          _ ≤ sSup S' := inf_le_left
      obtain ⟨B, hB, hBle⟩ := ih hS'sub hT
      exact ⟨B, Set.mem_insert_of_mem A hB, hBle⟩

theorem exists_component_orbit_le (hs : s * s = 1) {C : Subgroup Y}
    (hC : C = Subgroup.centralizer ({s} : Set Y)) {Lc : Subgroup C}
    (hLc : TwoComponents.IsTwoComponent Lc) (hle : Lc.map C.subtype ≤ Layer.subgroup Y) :
    ∃ K : Subgroup Y, CFSG.Open.IsComponentOf K ⊤ ∧
      Lc.map C.subtype ≤ K ⊔ CFSG.conjugate K s := by
  obtain ⟨A, hA, hLA⟩ := exists_orbitSub_le hs hC hLc (orbitFamily s) (Set.toFinite _) subset_rfl
    (hle.trans (layer_le_sSup_orbitFamily s))
  obtain ⟨K, hK, rfl⟩ := hA
  exact ⟨K, hK, hLA⟩

end Orbit

end CFSG.QuasithinUnique.I32
