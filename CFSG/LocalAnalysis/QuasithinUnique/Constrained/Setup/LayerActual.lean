module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNonsolv3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerCP8

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6 CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup CFSG.LocalCores CFSG.ABGLocalTools
open scoped commutatorElement

universe v

abbrev Comp (G : Type*) [Group G] : Type _ := {L : Subgroup G // CFSG.IsComponent L}

section Tools

variable {X : Type*} [Group X]

theorem isSylowOf_top_of_isSylowTwoOf [Finite X] {T H : Subgroup X} (hT : IsSylowTwoOf T H) :
    IsSylowOf 2 (T.subgroupOf H) (⊤ : Subgroup ↥H) := by
  have := Fact.mk Nat.prime_two
  rw [isSylowOf_iff]
  refine ⟨le_top, hT.2.1.comap_subtype, ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact hT.2.2

theorem exists_conjSub_le_sylowTwo [Finite X] {P K E : Subgroup X} (hP : IsSylowTwoOf P K)
    (hEK : E ≤ K) (hE : IsPGroup 2 ↥E) : ∃ g ∈ K, conjSub g E ≤ P := by
  have := Fact.mk Nat.prime_two
  have hE' : IsPGroup 2 ↥(E.subgroupOf K) := hE.comap_subtype
  obtain ⟨Q, hQ⟩ := hE'.exists_le_sylow
  have hplus : IsSylowTwoOf ((Q : Subgroup ↥K).map K.subtype) K := by
    refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
    · exact Q.isPGroup'.map K.subtype
    · have e : ((Q : Subgroup ↥K).map K.subtype).subgroupOf K = (Q : Subgroup ↥K) :=
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
      rw [e]
      exact Q.not_dvd_index
  obtain ⟨g, hg, hgP⟩ := isSylowTwoOf_exists_conj hplus hP
  refine ⟨g, hg, ?_⟩
  rw [hgP]
  refine (conjSub g).monotone ?_
  intro x hx
  exact ⟨⟨x, hEK hx⟩, hQ hx, rfl⟩

theorem mem_normalizer_of_map_subtype {H : Subgroup X} {L : Subgroup ↥H} {x : ↥H}
    (hx : (x : X) ∈ Subgroup.normalizer ((L.map H.subtype : Subgroup X) : Set X)) :
    x ∈ Subgroup.normalizer (L : Set ↥H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h := Subgroup.mem_normalizer_iff.1 hx (y : X)
  have e1 : y ∈ L ↔ (y : X) ∈ L.map H.subtype :=
    (Subgroup.mem_map_iff_mem H.subtype_injective).symm
  have e2 : x * y * x⁻¹ ∈ L ↔ ((x * y * x⁻¹ : ↥H) : X) ∈ L.map H.subtype :=
    (Subgroup.mem_map_iff_mem H.subtype_injective).symm
  rw [e1, e2]
  simpa using h

theorem map_subtype_mem_normalizer {H : Subgroup X} {L : Subgroup ↥H} {x : ↥H}
    (hx : x ∈ Subgroup.normalizer (L : Set ↥H)) :
    (x : X) ∈ Subgroup.normalizer ((L.map H.subtype : Subgroup X) : Set X) := by
  have key : ∀ z : ↥H, z ∈ Subgroup.normalizer (L : Set ↥H) → ∀ y ∈ L.map H.subtype,
      (z : X) * y * (z : X)⁻¹ ∈ L.map H.subtype := by
    intro z hz y hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨z * y' * z⁻¹, (Subgroup.mem_normalizer_iff.1 hz y').1 hy', by simp⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key x hx y hy, fun hy => ?_⟩
  have := key x⁻¹ ((Subgroup.normalizer (L : Set ↥H)).inv_mem hx) _ hy
  simpa [mul_assoc] using this

end Tools

section Main

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

structure ActualComponentTransfer (H T M : Subgroup (V ≃ₗ[k] V)) [Finite ↥H] : Prop where
  layer : NonsolvableLayer H T M
  transfer : ∀ c : Comp ↥H, CentralProductTransfer 2 (T.subgroupOf H) (M.subgroupOf H)
    (fun c : Comp ↥H => c.1) c
  offender : ∀ c : Comp ↥H, ∃ A : Subgroup (V ≃ₗ[k] V),
    A ≤ (normT (T.subgroupOf H) c.1).map H.subtype ∧ IsMinOffender H A ∧
      ⁅c.1.map H.subtype, A⁆ = c.1.map H.subtype

variable [CharP k 2] [Finite V]

theorem actual_component_minimal_parabolic (hQ : QuadBestOffendersNormalize k V)
    {H T M E : Subgroup (V ≃ₗ[k] V)} (hns : ¬ Group.IsSolvable ↥H)
    (hO2 : ∀ N : Subgroup (V ≃ₗ[k] V), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N → N = ⊥)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (V ≃ₗ[k] V), T ≤ Y → Y < H → Y ≤ M)
    (hEH : E ≤ H) (hEne : E ≠ ⊥) (hEel : CFSG.IsElementaryAbelian 2 E)
    (hEoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) E) :
    ActualComponentTransfer H T M := by
  classical
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  have hlayer := nonsolvable_layer hQ hns hO2 hT hTn hTM hMH hmax hEH hEne hEel hEoff
  have hT' : IsSylowOf 2 (T.subgroupOf H) (⊤ : Subgroup ↥H) :=
    isSylowOf_top_of_isSylowTwoOf hT
  have hTM' : T.subgroupOf H ≤ M.subgroupOf H := fun x hx => hTM hx
  have hMH' : M.subgroupOf H < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => ?_
    have : H ≤ M := Subgroup.subgroupOf_eq_top.1 h
    exact hMH.not_ge this
  have hmax' : ∀ Y : Subgroup ↥H, T.subgroupOf H ≤ Y → Y < ⊤ → Y ≤ M.subgroupOf H := by
    intro Y hTY hY
    have h1 : T ≤ Y.map H.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hT.1]
      exact Subgroup.map_mono hTY
    have h2 : Y.map H.subtype < H := by
      refine lt_of_le_of_ne (Subgroup.map_subtype_le Y) fun h => ?_
      apply hY.ne
      have : Y.map H.subtype = (⊤ : Subgroup ↥H).map H.subtype := by
        rw [h]
        exact (map_subtype_top H).symm
      exact Subgroup.map_injective H.subtype_injective this
    have h3 := hmax _ h1 h2
    intro x hx
    exact h3 ⟨x, hx, rfl⟩
  have hqs : ∀ c : Comp ↥H, CFSG.IsQuasisimple ↥c.1 := fun c => c.2.1
  have hcomm : ∀ c c' : Comp ↥H, c ≠ c' → ⁅c.1, c'.1⁆ = ⊥ := fun c c' hne =>
    hlayer.comp_comm c.1 c'.1 c.2 c'.2 fun h => hne (Subtype.ext h)
  have hlayer_eq : (⨆ c : Comp ↥H, c.1 : Subgroup ↥H) = CFSG.layer ↥H :=
    (sSup_eq_iSup' _).symm
  have hKn : (⨆ c : Comp ↥H, c.1 : Subgroup ↥H).Normal := by
    rw [hlayer_eq]
    have := layer_characteristic (G := ↥H)
    infer_instance
  have hKT : (⨆ c : Comp ↥H, c.1 : Subgroup ↥H) ⊔ T.subgroupOf H = ⊤ := by
    rw [hlayer_eq, ← hlayer.K_eq_layer]
    have hKH : oddGen H ≤ H := (Subgroup.closure_le H).2 fun h hh => hh.1
    have h1 := hlayer.H_eq_KT
    have h2 : (oddGen H ⊔ T).subgroupOf H = ⊤ := by rw [h1, Subgroup.subgroupOf_self]
    rwa [Subgroup.subgroupOf_sup hKH hT.1] at h2
  have hperm : ∀ t ∈ T.subgroupOf H, ∀ c : Comp ↥H, ∃ c' : Comp ↥H, conjSub t c.1 = c'.1 :=
    fun t _ c => ⟨⟨_, isComponent_map_mulEquiv (MulAut.conj t) c.2⟩, rfl⟩
  have htrans : ∀ c c' : Comp ↥H, ∃ t ∈ T.subgroupOf H, conjSub t c.1 = c'.1 := by
    intro c c'
    obtain ⟨t, ht, h⟩ := hlayer.comp_trans c.1 c'.1 c.2 c'.2
    exact ⟨t, ht, h⟩
  have key : ∀ c : Comp ↥H, ∃ A₀ : Subgroup (V ≃ₗ[k] V), IsMinOffender H A₀ ∧
      ⁅c.1.map H.subtype, A₀⁆ = c.1.map H.subtype ∧
      A₀ ≤ Subgroup.normalizer ((c.1.map H.subtype : Subgroup (V ≃ₗ[k] V)) : Set (V ≃ₗ[k] V)) := by
    intro c
    obtain ⟨A₀, hA₀, hcomm₀⟩ := hlayer.comp_offender c.1 c.2
    have hLc : IsComponentIn (c.1.map H.subtype) H := by
      refine ⟨Subgroup.map_subtype_le c.1, ?_⟩
      have : (c.1.map H.subtype).subgroupOf H = c.1 :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective c.1
      rw [this]
      exact c.2
    exact ⟨A₀, hA₀, hcomm₀, (le_offenderJ hA₀).trans
      (hlayer.parabolic.comps _ hLc).2.1⟩
  have hnormal : ∀ c : Comp ↥H, ∀ A₀ : Subgroup (V ≃ₗ[k] V), IsMinOffender H A₀ →
      A₀ ≤ Subgroup.normalizer ((c.1.map H.subtype : Subgroup (V ≃ₗ[k] V)) : Set (V ≃ₗ[k] V)) →
      A₀.subgroupOf H ≤ normL c.1 := by
    intro c A₀ hA₀ hn x hx
    exact mem_normalizer_of_map_subtype (hn hx)
  have hpgroup : ∀ A₀ : Subgroup (V ≃ₗ[k] V), IsMinOffender H A₀ →
      IsPGroup 2 ↥(A₀.subgroupOf H) := by
    intro A₀ hA₀
    have hel : CFSG.IsElementaryAbelian 2 ↥A₀ := hA₀.2.2.1
    exact (CFSG.IsElementaryAbelian.isPGroup 2 ↥A₀).comap_subtype
  have hE_ne : ∀ c : Comp ↥H, ∀ A₀ : Subgroup (V ≃ₗ[k] V), IsMinOffender H A₀ →
      ⁅c.1.map H.subtype, A₀⁆ = c.1.map H.subtype → ⁅c.1, A₀.subgroupOf H⁆ ≠ ⊥ := by
    intro c A₀ hA₀ hcomm₀ hbot
    have h1 := congrArg (Subgroup.map H.subtype) hbot
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA₀.1, hcomm₀,
      Subgroup.map_bot] at h1
    have hnt := isQuasisimple_nontrivial c.2.1
    have : c.1 = ⊥ := by
      have := Subgroup.map_eq_bot_iff_of_injective c.1 H.subtype_injective
      exact this.1 h1
    exact (Subgroup.nontrivial_iff_ne_bot c.1).1 hnt this
  have htransfer : ∀ c : Comp ↥H, ∀ A₀ : Subgroup (V ≃ₗ[k] V), IsMinOffender H A₀ →
      ⁅c.1.map H.subtype, A₀⁆ = c.1.map H.subtype →
      A₀ ≤ Subgroup.normalizer ((c.1.map H.subtype : Subgroup (V ≃ₗ[k] V)) : Set (V ≃ₗ[k] V)) →
      CentralProductTransfer 2 (T.subgroupOf H) (M.subgroupOf H) (fun c : Comp ↥H => c.1) c := by
    intro c A₀ hA₀ hcomm₀ hn
    exact central_product_transfer Nat.prime_two hT' hTM' hMH' hmax' (fun c : Comp ↥H => c.1)
      Subtype.val_injective hqs hcomm hKn hKT hperm htrans c (hpgroup A₀ hA₀)
      (hnormal c A₀ hA₀ hn) (hE_ne c A₀ hA₀ hcomm₀)
  refine ⟨hlayer, fun c => ?_, fun c => ?_⟩
  · obtain ⟨A₀, hA₀, hcomm₀, hn⟩ := key c
    exact htransfer c A₀ hA₀ hcomm₀ hn
  · obtain ⟨A₀, hA₀, hcomm₀, hn⟩ := key c
    have hTr := htransfer c A₀ hA₀ hcomm₀ hn
    have hsyl : IsSylowTwoOf (normT (T.subgroupOf H) c.1) (normL c.1) := by
      have := Fact.mk Nat.prime_two
      exact isSylowOf_iff.1 hTr.sylow_normL
    obtain ⟨g, hg, hgE⟩ := exists_conjSub_le_sylowTwo hsyl (hnormal c A₀ hA₀ hn)
      (hpgroup A₀ hA₀)
    refine ⟨conjSub (g : V ≃ₗ[k] V) A₀, ?_, hA₀.conj g.2, ?_⟩
    · intro x hx
      have hx' : (g : V ≃ₗ[k] V)⁻¹ * x * (g : V ≃ₗ[k] V) ∈ A₀ := mem_conjSub.1 hx
      have hxH : x ∈ H := by
        have h1 : (g : V ≃ₗ[k] V) * ((g : V ≃ₗ[k] V)⁻¹ * x * (g : V ≃ₗ[k] V)) *
            (g : V ≃ₗ[k] V)⁻¹ ∈ H := H.mul_mem (H.mul_mem g.2 (hA₀.1 hx')) (H.inv_mem g.2)
        simpa [mul_assoc] using h1
      refine ⟨⟨x, hxH⟩, hgE ?_, rfl⟩
      rw [mem_conjSub]
      exact hx'
    · have hgn := map_subtype_mem_normalizer (L := c.1) hg
      rw [commutator_conjSub hgn, hcomm₀]
      exact conjSub_eq_self hgn

end Main

end CFSG.QuasithinUnique.Setup.Layer
