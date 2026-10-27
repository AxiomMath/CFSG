module

public import CFSG.ClassicalInvolution.LBalance

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.ComponentClassification

section Layer

variable {G : Type*} [Group G] [Finite G]

theorem layer_le_normalizer_of_isComponentOf {a : Subgroup G} (ha : IsComponentOf a ⊤) :
    Layer.subgroup G ≤ Subgroup.normalizer (a : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Layer.component_le ha)).mp
    (Layer.normal_component ha)

theorem map_conj_sSup_of_isComponentOf {S : Set (Subgroup G)} (hS : ∀ a ∈ S, IsComponentOf a ⊤)
    {g : G} (hg : g ∈ Layer.subgroup G) :
    (sSup S).map (MulAut.conj g).toMonoidHom = sSup S := by
  rw [sSup_eq_iSup', Subgroup.map_iSup]
  refine iSup_congr fun a => ?_
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (layer_le_normalizer_of_isComponentOf (hS a.1 a.2) hg)

theorem exists_isComponentOf_ge_of_le_sSup {x : G} (hx : x ∈ Layer.subgroup G)
    {C : Subgroup G} (hC : C = Subgroup.centralizer ({x} : Set G)) {Lc : Subgroup C}
    (hLc : TwoComponents.IsTwoComponent Lc) :
    ∀ S : Set (Subgroup G), S.Finite → (∀ a ∈ S, IsComponentOf a ⊤) →
      Lc.map C.subtype ≤ sSup S → ∃ a ∈ S, Lc.map C.subtype ≤ a := by
  classical
  have hfixed : FixedCommutingProduct.fixedSubgroup (MulAut.conj x) = C := by
    rw [hC]
    ext member
    change x * member * x⁻¹ = member ↔ member ∈ Subgroup.centralizer ({x} : Set G)
    constructor
    · intro heq
      apply Subgroup.mem_centralizer_iff.mpr
      intro singleton hsingleton
      rw [Set.mem_singleton_iff.mp hsingleton]
      calc x * member = (x * member * x⁻¹) * x := by group
        _ = member * x := by rw [heq]
    · intro hmem
      have hcommutes := Subgroup.mem_centralizer_iff.mp hmem x (Set.mem_singleton x)
      rw [hcommutes]
      group
  let : Group.IsPerfect Lc := ⟨TwoComponents.perfect hLc⟩
  let : Group.IsPerfect (Lc.map C.subtype) := Group.IsPerfect.map C.subtype
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
  | @insert a S' haS' hS'fin ih =>
    intro hcomp hle
    have ha : IsComponentOf a ⊤ := hcomp a (Set.mem_insert a S')
    have hS'comp : ∀ b ∈ S', IsComponentOf b ⊤ := fun b hb => hcomp b (Set.mem_insert_of_mem a hb)
    have hcomm : ⁅a, sSup S'⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      refine sSup_le fun b hb => ?_
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (LocalComponents.commute_of_ne b a (hS'comp b hb) ha fun h => haS' (h ▸ hb))
    have hainv : a.map (MulAut.conj x).toMonoidHom = a :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (layer_le_normalizer_of_isComponentOf ha hx)
    have hTinv : (sSup S').map (MulAut.conj x).toMonoidHom = sSup S' :=
      map_conj_sSup_of_isComponentOf hS'comp hx
    have hderived := FixedCommutingProduct.derived_fixed a (sSup S') hcomm (MulAut.conj x)
      hainv hTinv
    rw [hfixed] at hderived
    have hle' : Lc.map C.subtype ≤ a ⊔ sSup S' := by rwa [sSup_insert] at hle
    have hle'' : Lc.map C.subtype ≤ (a ⊔ sSup S') ⊓ C := le_inf hle' (Subgroup.map_subtype_le Lc)
    have hprod : Lc.map C.subtype ≤ (a ⊓ C) ⊔ (sSup S' ⊓ C) :=
      calc Lc.map C.subtype = ⁅Lc.map C.subtype, Lc.map C.subtype⁆ :=
            Subgroup.commutator_eq_self.symm
        _ ≤ ⁅(a ⊔ sSup S') ⊓ C, (a ⊔ sSup S') ⊓ C⁆ := Subgroup.commutator_mono hle'' hle''
        _ ≤ (a ⊓ C) ⊔ (sSup S' ⊓ C) := hderived
    have hlocal : Lc ≤ a.subgroupOf C ⊔ (sSup S').subgroupOf C := by
      have hmap : Lc.map C.subtype ≤ (a.subgroupOf C ⊔ (sSup S').subgroupOf C).map C.subtype := by
        rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
        exact hprod
      have hcomap := Subgroup.map_le_iff_le_comap.mp hmap
      rwa [Subgroup.comap_map_eq_self_of_injective C.subtype_injective] at hcomap
    have hasub : IsSubnormal (a.subgroupOf C) ⊤ := Components.chain_of_mathlib_subnormal
      ((Components.mathlib_subnormal_of_chain ha.2.1 Subgroup.IsSubnormal.top).subgroupOf)
    have hTE : sSup S' ≤ Layer.subgroup G :=
      sSup_le fun b hb => Layer.component_le (hS'comp b hb)
    have hTnormal : ((sSup S').subgroupOf (Layer.subgroup G)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTE]
      intro g hg
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (map_conj_sSup_of_isComponentOf hS'comp hg)
    have hTsub : IsSubnormal (sSup S') ⊤ := by
      have : (Layer.subgroup G).Normal := Layer.normal G
      exact IsSubnormal.step hTE hTnormal
        (IsSubnormal.step le_top Subgroup.normal_subgroupOf (IsSubnormal.refl ⊤))
    have hTlocalsub : IsSubnormal ((sSup S').subgroupOf C) ⊤ :=
      Components.chain_of_mathlib_subnormal
        ((Components.mathlib_subnormal_of_chain hTsub Subgroup.IsSubnormal.top).subgroupOf)
    have hpairJoin : sSup ({a.subgroupOf C, (sSup S').subgroupOf C} : Set (Subgroup C)) =
        a.subgroupOf C ⊔ (sSup S').subgroupOf C := by simp
    have hpairSub : ∀ s ∈ ({a.subgroupOf C, (sSup S').subgroupOf C} : Set (Subgroup C)),
        IsSubnormal s ⊤ := by
      intro s hs
      rcases Set.mem_insert_iff.mp hs with rfl | hs
      · exact hasub
      · rw [Set.mem_singleton_iff.mp hs]
        exact hTlocalsub
    obtain ⟨cont, hcont, hcontle⟩ := TwoComponentJoins.exists_le_of_le_sSup Lc hLc
      ({a.subgroupOf C, (sSup S').subgroupOf C} : Set (Subgroup C)) hpairSub
      (by rwa [hpairJoin])
    rcases Set.mem_insert_iff.mp hcont with rfl | hcont
    · refine ⟨a, Set.mem_insert a S', ?_⟩
      calc Lc.map C.subtype ≤ (a.subgroupOf C).map C.subtype := Subgroup.map_mono hcontle
        _ = a ⊓ C := Subgroup.subgroupOf_map_subtype a C
        _ ≤ a := inf_le_left
    · rw [Set.mem_singleton_iff.mp hcont] at hcontle
      have hT : Lc.map C.subtype ≤ sSup S' :=
        calc Lc.map C.subtype ≤ ((sSup S').subgroupOf C).map C.subtype :=
              Subgroup.map_mono hcontle
          _ = sSup S' ⊓ C := Subgroup.subgroupOf_map_subtype _ C
          _ ≤ sSup S' := inf_le_left
      obtain ⟨b, hb, hble⟩ := ih hS'comp hT
      exact ⟨b, Set.mem_insert_of_mem a hb, hble⟩

theorem exists_isComponentOf_ge_of_isTwoComponent {x : G} (hx : x ∈ Layer.subgroup G)
    {C : Subgroup G} (hC : C = Subgroup.centralizer ({x} : Set G)) {Lc : Subgroup C}
    (hLc : TwoComponents.IsTwoComponent Lc) (hle : Lc.map C.subtype ≤ Layer.subgroup G) :
    ∃ L : Subgroup G, IsComponentOf L ⊤ ∧ Lc.map C.subtype ≤ L := by
  obtain ⟨L, hL, hLle⟩ := exists_isComponentOf_ge_of_le_sSup hx hC hLc
    {component : Subgroup G | IsComponentOf component ⊤} (Set.toFinite _) (fun _ h => h) hle
  exact ⟨L, hL, hLle⟩

theorem eq_of_isComponentOf_of_perfect_le {L₁ L₂ K : Subgroup G} (h₁ : IsComponentOf L₁ ⊤)
    (h₂ : IsComponentOf L₂ ⊤) (hperf : ⁅K, K⁆ = K) (hne : K ≠ ⊥) (hK₁ : K ≤ L₁)
    (hK₂ : K ≤ L₂) : L₁ = L₂ := by
  by_contra hne'
  have hcomm := LocalComponents.commute_of_ne L₁ L₂ h₁ h₂ hne'
  apply hne
  rw [← hperf]
  exact le_bot_iff.mp (hcomm ▸ Subgroup.commutator_mono hK₁ hK₂)

end Layer

theorem twoComponent_le_layer_of_l2PrimeBalance (hL : L2PrimeBalance) {G : Type} [Group G]
    [Finite G] (hcore : componentClassificationOddCore G = ⊥) {x : G} (hx : x * x = 1)
    {C : Subgroup G} (hC : C = Subgroup.centralizer ({x} : Set G)) {Lc : Subgroup C}
    (hLc : TwoComponents.IsTwoComponent Lc) : Lc.map C.subtype ≤ Layer.subgroup G := by
  have hA : IsPGroup 2 (Subgroup.zpowers x) := by
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)
  have hCz : C = Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    rw [hC, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  subst hCz
  have h1 := (Subgroup.map_mono (le_sSup
    ((CatalogueBAlternating.pComponent_two_iff Lc).mpr hLc))).trans (hL G _ hA)
  rw [LocalBFailure.pLayer_two_eq_twoLayer,
    TwoLayerTransport.eq_layer_of_corefree hcore] at h1
  exact h1

end CFSG.ClassicalInvolution
