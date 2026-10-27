module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionClassMatch
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotOuter
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassUF5Main
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionB
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionOuter

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Quasithin (perfectCore)

variable {K : Type} [Field K]

section Inner

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem conj_inv_mem_sup_zpowers_of_conj_mem_E7 (hset : StandardSetting G L) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {g : G}
    (hw : g⁻¹ * t * g ∈ L) :
    g * t * g⁻¹ ∈ centralizer ({t} : Set G) ∧ g * t * g⁻¹ ∈ L ⊔ zpowers t := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set s := g * t * g⁻¹ with hsdef
  have hwt : (g⁻¹ * t * g) * t = t * (g⁻¹ * t * g) := mem_centralizer_iff.1 htC _ hw
  have hst : s ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc s * t = g * (t * (g⁻¹ * t * g)) * g⁻¹ := by rw [hsdef]; group
      _ = g * ((g⁻¹ * t * g) * t) * g⁻¹ := by rw [hwt]
      _ = t * s := by rw [hsdef]; group
  refine ⟨hst, ?_⟩
  rcases Nat.even_or_odd' f with ⟨e', rfl | rfl⟩
  ·
    by_contra hsL
    have he' : 1 ≤ e' := by omega
    have hsC' : (g⁻¹)⁻¹ * t * g⁻¹ ∈ centralizer ({t} : Set G) := by
      rw [inv_inv]
      exact hst
    have hsL' : (g⁻¹)⁻¹ * t * g⁻¹ ∉ L ⊔ zpowers t := by
      rw [inv_inv]
      exact hsL
    have h := conj_inv_not_mem_sup_zpowers_E7 hset he' hK e ht hKt hsC' hsL'
    rw [inv_inv] at h
    exact h (mem_sup_left hw)
  ·
    have hodd : Odd (2 * e' + 1) := ⟨e', rfl⟩
    have hss : s * s = 1 := by
      calc s * s = g * (t * t) * g⁻¹ := by rw [hsdef]; group
        _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
    have hN : s ∈ normalizer (L : Set G) :=
      centralizer_le_normalizer_of_standard hset.standard htC ht hst
    set α : MulAut L := L.normalizerMonoidHom ⟨s, hN⟩ with hαdef
    have hα : ∀ l : L, ((α l : L) : G) = s * l * s⁻¹ := fun l =>
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨s, hN⟩ l
    have hα2 : α ^ 2 = 1 := by
      refine MulEquiv.ext fun l => Subtype.ext ?_
      rw [sq, MulAut.mul_apply, MulAut.one_apply, hα, hα]
      calc s * (s * (l : G) * s⁻¹) * s⁻¹ = (s * s) * l * (s * s)⁻¹ := by group
        _ = l := by rw [hss, one_mul, inv_one, mul_one]
    obtain ⟨l, hl⟩ := (F4Pilot.conj_mem_range_conj_iff e α).1
      (E8Pilot.mem_range_conj_of_sq_eq_one_of_odd_E7_E8 (Or.inl rfl) hf hodd K hK
        ((F4Pilot.pow_two_conj_eq_one_iff e α).2 hα2))
    refine F4Pilot.mem_sup_zpowers_of_conj_eq htC ht hKt hst l.2 fun y hy => ?_
    have h := congrArg (fun φ : MulAut L => ((φ ⟨y, hy⟩ : L) : G)) hl
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [h, hα]

theorem forall_inner_of_conj_mem_E7 (hset : StandardSetting G L) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∀ g : G, g⁻¹ * t * g ∈ L →
      ∃ w' ∈ CFSG.conjugate L g, ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹ := by
  intro g hw
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  obtain ⟨-, hsL⟩ := conj_inv_mem_sup_zpowers_of_conj_mem_E7 hset hf hK e ht hKt hw
  set s := g * t * g⁻¹ with hsdef
  obtain ⟨y, hyL, hy⟩ := F4Pilot.exists_eq_or_eq_mul_of_mem_sup_zpowers ht htC hsL
  have hsy : ∀ x ∈ L, s * x * s⁻¹ = y * x * y⁻¹ := by
    intro x hx
    rcases hy with hy | hy
    · rw [hy]
    · rw [hy]
      have hc : (y * x * y⁻¹) * t = t * (y * x * y⁻¹) :=
        mem_centralizer_iff.1 htC _ (L.mul_mem (L.mul_mem hyL hx) (L.inv_mem hyL))
      calc t * y * x * (t * y)⁻¹ = t * (y * x * y⁻¹) * t⁻¹ := by group
        _ = (y * x * y⁻¹) * t * t⁻¹ := by rw [hc]
        _ = y * x * y⁻¹ := by group
  refine ⟨g⁻¹ * y * g, EPilot.conj_mem_conjugate hyL g, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx' : (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := by
    simp
  rw [hx']
  have et : t = g⁻¹ * s * g := by rw [hsdef]; group
  calc t * (g⁻¹ * x * g) * t⁻¹ = g⁻¹ * (s * x * s⁻¹) * g := by rw [et]; group
    _ = g⁻¹ * (y * x * y⁻¹) * g := by rw [hsy x hx]
    _ = g⁻¹ * y * g * (g⁻¹ * x * g) * (g⁻¹ * y * g)⁻¹ := by group

end Inner

section Data

variable [Finite K] [CharP K 2]

variable (K) in
@[expose] noncomputable def e7UVRep : Bool → adjointGroup .E7 K
  | false => e7Rep K 3
  | true => e7Rep K 4

variable (K) in
@[expose] noncomputable def e7UVQ : Bool → Subgroup (adjointGroup .E7 K)
  | false => uCoreRadical K
  | true => vCoreRadical K

variable (K) in
@[expose] noncomputable def e7UVM : Bool → Subgroup (adjointGroup .E7 K)
  | false => uLevi K
  | true => vLevi K

theorem e7UVRep_mem_perpLevi (k : Bool) : e7UVRep K k ∈ EPilot.perpLevi .E7 K := by
  cases k
  · exact e7Rep_mem_perpLevi 3
  · exact e7Rep_mem_perpLevi 4

theorem e7UVRep_ne_one (k : Bool) : e7UVRep K k ≠ 1 := by
  cases k
  · exact e7Rep_ne_one 3
  · exact e7Rep_ne_one 4

theorem exists_conj_eq_e7UVRep_of_not_mem_closure_odd {x : adjointGroup .E7 K}
    (hx2 : orderOf x = 2)
    (hx : x ∉ closure {c : adjointGroup .E7 K |
      c ∈ centralizer ({x} : Set (adjointGroup .E7 K)) ∧ Odd (orderOf c)}) :
    ∃ (k : Bool) (c : adjointGroup .E7 K), c * x * c⁻¹ = e7UVRep K k := by
  obtain ⟨k, c, hk, hc⟩ := exists_conj_eq_e7Rep_of_map_not_mem_closure_odd
    (MonoidHom.id (adjointGroup .E7 K)) Function.injective_id hx2 (fun h => hx (by
      refine Subgroup.closure_mono ?_ h
      intro y hy
      exact ⟨(mem_inf.1 hy.1).2, hy.2⟩))
  have h34 : ∀ k : Fin 5, 3 ≤ k.val → k = 3 ∨ k = 4 := by decide
  rcases h34 k hk with rfl | rfl
  · exact ⟨false, c, hc⟩
  · exact ⟨true, c, hc⟩

theorem perfectCore_centralizer_e7UVRep_eq (k : Bool) :
    perfectCore (centralizer ({e7UVRep K k} : Set (adjointGroup .E7 K))) =
      e7UVQ K k ⊔ e7UVM K k := by
  cases k
  · exact perfectCore_centralizer_e7Rep_three_eq_sup
  · exact perfectCore_centralizer_e7Rep_four_eq_sup

theorem isPGroup_e7UVQ (k : Bool) : IsPGroup 2 (e7UVQ K k) := by
  cases k
  · exact isPGroup_uCoreRadical
  · exact isPGroup_vCoreRadical

theorem e7UVM_le_normalizer (k : Bool) :
    e7UVM K k ≤ normalizer (e7UVQ K k : Set (adjointGroup .E7 K)) := by
  cases k
  · exact uLevi_le_normalizer_uCoreRadical
  · exact vLevi_le_normalizer_vCoreRadical

theorem disjoint_e7UVQ_e7UVM (k : Bool) : Disjoint (e7UVQ K k) (e7UVM K k) := by
  cases k
  · exact disjoint_uCoreRadical_uLevi
  · exact disjoint_vCoreRadical_vLevi

theorem forall_normal_isPGroup_eq_bot_e7UVM (k : Bool) :
    ∀ N : Subgroup (e7UVM K k), N.Normal → IsPGroup 2 N → N = ⊥ := by
  cases k
  · exact forall_normal_isPGroup_eq_bot_uLevi
  · exact forall_normal_isPGroup_eq_bot_vLevi

theorem posJE7_le_e7UVM (k : Bool) : posJE7 K ≤ e7UVM K k := by
  cases k
  · exact highRootSL2_le_uLevi
  · exact highRootSL2_le_vLevi

theorem eq_of_nonempty_mulEquiv_e7UV (k₁ k₂ : Bool)
    (h : Nonempty ((e7UVQ K k₁ ⊔ e7UVM K k₁ : Subgroup (adjointGroup .E7 K)) ≃*
      (e7UVQ K k₂ ⊔ e7UVM K k₂ : Subgroup (adjointGroup .E7 K)))) : k₁ = k₂ := by
  cases k₁ <;> cases k₂
  · rfl
  · exact absurd h not_nonempty_mulEquiv_uCore_vCore
  · exact absurd (h.map MulEquiv.symm) not_nonempty_mulEquiv_uCore_vCore
  · rfl

theorem nonempty_centralizer_leviAutOfAut_e7UV (hq : 4 ≤ Nat.card K) (k : Bool)
    (β : (e7UVQ K k ⊔ e7UVM K k : Subgroup (adjointGroup .E7 K)) ≃*
      (e7UVQ K k ⊔ e7UVM K k : Subgroup (adjointGroup .E7 K)))
    (hβ : ((e7UVQ K k).subgroupOf (e7UVQ K k ⊔ e7UVM K k)).map β.toMonoidHom =
      (e7UVQ K k).subgroupOf (e7UVQ K k ⊔ e7UVM K k)) :
    Nonempty (centralizer (((((posJE7 K).subgroupOf (e7UVM K k)).map
      (EPilot.leviAutOfAut (e7UVQ K k) (e7UVM K k) (disjoint_e7UVQ_e7UVM k)
        (e7UVM_le_normalizer k) β hβ).toMonoidHom).map (e7UVM K k).subtype :
          Subgroup (adjointGroup .E7 K)) : Set (adjointGroup .E7 K)) ≃*
      EPilot.perpLevi .E7 K) := by
  cases k
  · exact nonempty_centralizer_leviAutOfAut_u hq β hβ
  · exact nonempty_centralizer_leviAutOfAut_v hq β hβ

end Data

section U19

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_eq_e7UVRep_le_centralizer_mulEquiv_E7 (hset : StandardSetting G L) {f : ℕ}
    (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {g : G} (hw : g⁻¹ * t * g ∈ L) {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((posJE7 K).map e.symm.toMonoidHom).map L.subtype) :
    ∃ (k : Bool) (g₁ : G), g₁⁻¹ * t * g₁ = (e.symm (e7UVRep K k) : G) ∧
      ∃ P : Subgroup G, P ≤ centralizer (X : Set G) ⊓ centralizer ({g₁⁻¹ * t * g₁} : Set G) ∧
        Nonempty (P ≃* EPilot.perpLevi .E7 K) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact EPilot.exists_conj_le_centralizer_mulEquiv_of_conj_mem_aut hset
    (isCyclic_outer_of_mulEquiv_E7 e) (center_eq_bot_of_mulEquiv_E7 e) e ht hKt hw
    (forall_inner_of_conj_mem_E7 hset (by omega) hK e ht hKt) (e7UVRep K)
    (fun _ hx2 hx => exists_conj_eq_e7UVRep_of_not_mem_closure_odd hx2 hx) (e7UVQ K) (e7UVM K)
    perfectCore_centralizer_e7UVRep_eq isPGroup_e7UVQ e7UVM_le_normalizer disjoint_e7UVQ_e7UVM
    forall_normal_isPGroup_eq_bot_e7UVM posJE7_le_e7UVM eq_of_nonempty_mulEquiv_e7UV
    (nonempty_centralizer_leviAutOfAut_e7UV hq) hXodd hXJ

theorem exists_le_centralizer_mulEquiv_of_conj_mem_E7 (hset : StandardSetting G L) {f : ℕ}
    (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {g : G} (hw : g⁻¹ * t * g ∈ L) {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((posJE7 K).map e.symm.toMonoidHom).map L.subtype) :
    ∃ g₁ : G, ∃ y ∈ ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype, y ≠ 1 ∧
      g₁⁻¹ * t * g₁ = y ∧ ∃ P : Subgroup G,
        P ≤ centralizer (X : Set G) ⊓ centralizer ({g₁⁻¹ * t * g₁} : Set G) ∧
          Nonempty (P ≃* EPilot.perpLevi .E7 K) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  obtain ⟨k, g₁, hg₁, P, hP, hPD⟩ :=
    exists_conj_eq_e7UVRep_le_centralizer_mulEquiv_E7 hset hf hK e ht hKt hw hXodd hXJ
  refine ⟨g₁, (e.symm (e7UVRep K k) : G),
    ⟨e.symm (e7UVRep K k), ⟨e7UVRep K k, e7UVRep_mem_perpLevi k, rfl⟩, rfl⟩, ?_, hg₁, P, hP, hPD⟩
  intro h
  apply e7UVRep_ne_one (K := K) k
  have h' : e.symm (e7UVRep K k) = 1 := Subtype.ext h
  rw [← e.apply_symm_apply (e7UVRep K k), h', map_one]

end U19

end CFSG.SeitzReduction.E7Pilot
