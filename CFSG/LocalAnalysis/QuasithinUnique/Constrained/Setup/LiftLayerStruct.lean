module

public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNonsolv3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftLayerBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftLayerDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenderOthers

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin
open scoped MatrixGroups commutatorElement

universe v

section Centralizer

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {H T M : Subgroup (V ≃ₗ[ZMod 2] V)}

omit [Finite V] in
theorem oddGen_le_self (H : Subgroup (V ≃ₗ[ZMod 2] V)) : oddGen H ≤ H :=
  (Subgroup.closure_le H).2 fun _ hh => hh.1

theorem oddGen_subgroupOf_normal (hnl : NonsolvableLayer H T M) :
    ((oddGen H).subgroupOf H).Normal := by
  rw [hnl.K_eq_layer]
  have := CFSG.LocalCores.layer_characteristic (G := ↥H)
  infer_instance

theorem centralizer_oddGen_eq_bot (hnl : NonsolvableLayer H T M) (hT : IsSylowTwoOf T H)
    (hrad : CFSG.solvableRadical ↥H = ⊥) :
    H ⊓ Subgroup.centralizer (oddGen H : Set (V ≃ₗ[ZMod 2] V)) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK'n := oddGen_subgroupOf_normal hnl
  have hZ : (Subgroup.center ↥((oddGen H).subgroupOf H)).map
      ((oddGen H).subgroupOf H).subtype = ⊥ := by
    rw [hnl.C_eq_center, hnl.C_eq_rad, hrad]
  have hT2 : IsPGroup 2 ↥(T.subgroupOf H) :=
    hT.2.1.of_injective (Subgroup.subgroupOfEquivOfLe hT.1).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hT.1).injective
  have hsup : (oddGen H).subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (oddGen_le_self H) hT.1, hnl.H_eq_KT, Subgroup.subgroupOf_self]
  have hTnorm : T.subgroupOf H ≤
      Subgroup.normalizer (((oddGen H).subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hK'n]
    exact le_top
  have hQ2 : IsPGroup 2 (↥H ⧸ (oddGen H).subgroupOf H) := by
    refine hT2.of_surjective
      ((QuotientGroup.mk' ((oddGen H).subgroupOf H)).comp (T.subgroupOf H).subtype) ?_
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    have hKT' : h ∈ (oddGen H).subgroupOf H ⊔ T.subgroupOf H := by rw [hsup]; trivial
    obtain ⟨k, hk, t, ht, rfl⟩ := mem_sup_mul hTnorm hKT'
    refine ⟨⟨t, ht⟩, ?_⟩
    show (QuotientGroup.mk t : ↥H ⧸ (oddGen H).subgroupOf H) = QuotientGroup.mk (k * t)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff k).2 hk, one_mul]
  have hQsolv : Group.IsSolvable (↥H ⧸ (oddGen H).subgroupOf H) := by
    have := hQ2.isNilpotent
    infer_instance
  let D'' : Subgroup ↥H :=
    Subgroup.centralizer (((oddGen H).subgroupOf H : Subgroup ↥H) : Set ↥H)
  have hDn : D''.Normal := Subgroup.normal_centralizer
  have hDK : D'' ⊓ (oddGen H).subgroupOf H ≤ ⊥ := by
    rintro x ⟨hxD, hxK⟩
    have h1 := (CFSG.LocalCores.mem_map_center_iff ((oddGen H).subgroupOf H)).2 ⟨hxK, hxD⟩
    rw [hZ] at h1
    exact h1
  let φ : ↥D'' →* (↥H ⧸ (oddGen H).subgroupOf H) :=
    (QuotientGroup.mk' ((oddGen H).subgroupOf H)).comp D''.subtype
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxK : (x : ↥H) ∈ (oddGen H).subgroupOf H := (QuotientGroup.eq_one_iff _).1 hx
    have h2 := hDK ⟨x.2, hxK⟩
    rw [Subgroup.mem_bot] at h2 ⊢
    exact Subtype.ext h2
  have hDs : Group.IsSolvable ↥D'' := Group.isSolvable_of_isSolvable_injective hφ
  have hDle : D'' ≤ CFSG.solvableRadical ↥H := le_sSup ⟨hDn, hDs⟩
  rw [hrad] at hDle
  rw [eq_bot_iff]
  intro x hx
  have hxD : (⟨x, hx.1⟩ : ↥H) ∈ D'' := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hx.2 (k : V ≃ₗ[ZMod 2] V) hk)
  have h3 := hDle hxD
  rw [Subgroup.mem_bot] at h3 ⊢
  exact congrArg Subtype.val h3

end Centralizer

section List

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {H T M : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

omit [Finite V] in
theorem IsCompListIn.perm (hLc : IsCompListIn H r Lc) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ H)
    (i : Fin r) : ∃ j, (Lc i).map (MulAut.conj t).toMonoidHom = Lc j := by
  obtain ⟨j, hj⟩ := hLc.complete _ (isComponentIn_conjSub (hLc.isComp i) (Subgroup.le_normalizer ht))
  exact ⟨j, hj.symm⟩

theorem IsCompListIn.trans (hnl : NonsolvableLayer H T M) (hLc : IsCompListIn H r Lc)
    (i j : Fin r) : ∃ t ∈ T, (Lc i).map (MulAut.conj t).toMonoidHom = Lc j := by
  obtain ⟨t, ht, h⟩ := hnl.comp_trans _ _ (hLc.isComp i).2 (hLc.isComp j).2
  refine ⟨(t : V ≃ₗ[ZMod 2] V), ht, ?_⟩
  have e1 : ∀ X : Subgroup ↥H, (X.map (MulAut.conj t).toMonoidHom).map H.subtype =
      (X.map H.subtype).map (MulAut.conj (t : V ≃ₗ[ZMod 2] V)).toMonoidHom := by
    intro X
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have h1 := congrArg (Subgroup.map H.subtype) h
  rw [e1, Subgroup.map_subgroupOf_eq_of_le (hLc.isComp i).1,
    Subgroup.map_subgroupOf_eq_of_le (hLc.isComp j).1] at h1
  exact h1

theorem IsCompListIn.card_pow_two (hnl : NonsolvableLayer H T M) (hT : IsSylowTwoOf T H)
    (hLc : IsCompListIn H r Lc) (i₀ : Fin r) : ∃ k : ℕ, r = 2 ^ k :=
  exists_pow_two_card_conj_family hT.2.1 Lc hLc.injective
    (fun _ ht i => hLc.perm (hT.1 ht) i) (hLc.trans hnl) i₀

theorem IsCompListIn.oddGen_eq (hnl : NonsolvableLayer H T M) (hLc : IsCompListIn H r Lc) :
    oddGen H = ⨆ i, Lc i := by
  apply le_antisymm
  · have h1 : oddGen H = (CFSG.layer ↥H).map H.subtype := by
      rw [← hnl.K_eq_layer, Subgroup.map_subgroupOf_eq_of_le (oddGen_le_self H)]
    rw [h1, Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    obtain ⟨i, hi⟩ := hLc.complete _ (BenderBranch.isComponentIn_of_isComponent hK)
    rw [← hi]
    exact le_iSup Lc i
  · exact iSup_le fun i => comp_le_oddGen (hLc.isComp i)

theorem IsCompListIn.elem_commute (hLc : IsCompListIn H r Lc) {i j : Fin r} (hij : i ≠ j) :
    ∀ x ∈ Lc i, ∀ y ∈ Lc j, x * y = y * x :=
  components_commute (hLc.isComp j) (hLc.isComp i) (fun h => hij (hLc.injective h))

theorem IsCompListIn.commutator_eq_bot (hLc : IsCompListIn H r Lc) {i j : Fin r} (hij : i ≠ j) :
    ⁅Lc i, Lc j⁆ = ⊥ :=
  commutator_eq_bot_of_isComponentIn_ne (hLc.isComp i) (hLc.isComp j)
    (fun h => hij (hLc.injective h))

omit [Finite V] in
theorem IsCompListIn.ne_bot (hLc : IsCompListIn H r Lc) (i : Fin r) : Lc i ≠ ⊥ := by
  intro h
  have hq := isQuasisimple_of_isComponentIn (hLc.isComp i)
  have := CFSG.LocalCores.isQuasisimple_nontrivial hq
  rw [h] at this
  exact (not_nontrivial_iff_subsingleton.2 inferInstance) this

end List

section Offender

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_minOffender_ge {H E : Subgroup (V ≃ₗ[ZMod 2] V)} (hEH : E ≤ H) (hEne : E ≠ ⊥)
    (hEel : CFSG.IsElementaryAbelian 2 E)
    (hEoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E) :
    ∃ A, IsMinOffender H A ∧
      weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E ≤ weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A := by
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).2 hEne
  let ρ : ↥E →* (V ≃ₗ[ZMod 2] V) := (MonoidHom.id (V ≃ₗ[ZMod 2] V)).comp E.subtype
  have e2 := weight_comp_subtype (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E ⊤
  rw [map_subtype_top] at e2
  have hρ : Nat.card V ≤ weight ρ ⊤ := by
    rw [e2]
    exact hEoff
  obtain ⟨B, hBbot, hwB, -, hstrict, hel⟩ := exists_maxWeight_minimalSubgroup ρ hρ
  have e1 := weight_comp_subtype (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E B
  refine ⟨B.map E.subtype, ⟨(Subgroup.map_subtype_le B).trans hEH, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective B E.subtype_injective]
    exact hBbot
  · exact isElementaryAbelian_of_mulEquiv
      (show ↥(B.map E.subtype) ≃* ↥B from
        (B.equivMapOfInjective E.subtype E.subtype_injective).symm)
      (hel 2 hEel)
  · have h1 : Nat.card V ≤ weight ρ B := hρ.trans hwB
    rw [← e1]
    exact h1
  · intro D hD0 hDlt
    have hDE : D ≤ E := hDlt.le.trans (Subgroup.map_subtype_le B)
    have hDeq : (D.subgroupOf E).map E.subtype = D := Subgroup.map_subgroupOf_eq_of_le hDE
    have hD1 : ⊥ < D.subgroupOf E := by
      rw [bot_lt_iff_ne_bot]
      intro h0
      have : D = ⊥ := by rw [← hDeq, h0, Subgroup.map_bot]
      exact (bot_lt_iff_ne_bot.1 hD0) this
    have hD2 : D.subgroupOf E < B := by
      rw [← Subgroup.map_lt_map_iff_of_injective E.subtype_injective, hDeq]
      exact hDlt
    have h3 := hstrict _ hD1 hD2
    have e3 := weight_comp_subtype (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E (D.subgroupOf E)
    rw [hDeq] at e3
    have h4 : weight ρ (D.subgroupOf E) = weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) D := e3
    have h5 : weight ρ B = weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (B.map E.subtype) := e1
    rw [h4, h5] at h3
    exact h3
  · have h5 : weight ρ B = weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (B.map E.subtype) := e1
    rw [← e2, ← h5]
    exact hwB

theorem weight_le_of_offenders {H E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hoff : ∀ A, IsMinOffender H A →
      weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A = Nat.card V)
    (hEH : E ≤ H) (hEne : E ≠ ⊥) (hEel : CFSG.IsElementaryAbelian 2 E) :
    weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E ≤ Nat.card V := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨A, hA, hge⟩ := exists_minOffender_ge hEH hEne hEel hlt.le
  have := hoff A hA
  omega

end Offender

end CFSG.QuasithinUnique.Setup.Lift
