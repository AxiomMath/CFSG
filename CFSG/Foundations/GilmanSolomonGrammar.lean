module

public import CFSG.Foundations.Basic
public meta import Lean.Elab.Term
public meta import Lean.Meta.Tactic.Delta

public section

open Lean Elab Term Meta in
elab "gs_grammar% " t:term : term <= ty => do
  let e ← elabTermEnsuringType t ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let e ← deltaExpand e fun n => (`CFSG.GSGrammar).isPrefixOf n
  Core.betaReduce e

namespace CFSG.GSGrammar

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

@[expose] def Corr (comp : Subgroup G → Subgroup G → Prop) (core : Subgroup G → Subgroup G)
    (layer : Subgroup G → G → Subgroup G) (a : G) (J : Subgroup G) (b : G) (L : Subgroup G) :
    Prop :=
  orderOf a = 2 ∧ orderOf b = 2 ∧ a * b = b * a ∧
    J ≤ centralizer ({a} : Set G) ∧ comp J (centralizer ({a} : Set G)) ∧
    L ≤ centralizer ({b} : Set G) ∧ comp L (centralizer ({b} : Set G)) ∧
    b ∈ normalizer (J : Set G) ∧ (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ core J) ∧
    layer J b = layer (L ⊔ conjugate L a) a

@[expose] def IsoCorr (edge : G → Subgroup G → G → Subgroup G → Prop)
    (core : Subgroup G → Subgroup G) (layer : Subgroup G → G → Subgroup G) (a : G)
    (J : Subgroup G) (b : G) (L : Subgroup G) : Prop :=
  edge a J b L ∧ L ⊔ conjugate L a = L ∧ (layer J b : Set G) * (core L : Set G) = L

@[expose] def UnbalancingTriple (comp : Subgroup G → Subgroup G → Prop)
    (core : Subgroup G → Subgroup G) (a x : G) (J : Subgroup G) : Prop :=
  orderOf a = 2 ∧ orderOf x = 2 ∧ a * x = x * a ∧
    J ≤ centralizer ({a} : Set G) ∧ comp J (centralizer ({a} : Set G)) ∧
    closure {y | ∃ j ∈ J, y = j⁻¹ * x⁻¹ * j * x} = J ∧
    closure {y | ∃ j ∈ J, ∃ d ∈ core (centralizer ({x} : Set G)) ⊓ centralizer ({a} : Set G),
      y = j⁻¹ * d⁻¹ * j * d} = J

@[expose] def InvolutionComponent (comp : Subgroup G → Subgroup G → Prop) (J : Subgroup G) :
    Prop :=
  ∃ a : G, orderOf a = 2 ∧ J ≤ centralizer ({a} : Set G) ∧ comp J (centralizer ({a} : Set G))

@[expose] def Reach (vertex : Subgroup G → Prop) (edge : G → Subgroup G → G → Subgroup G → Prop)
    (J L : Subgroup G) : Prop :=
  vertex J ∧ Relation.ReflTransGen (fun J' L' : Subgroup G => ∃ a b : G, edge a J' b L') J L

@[expose] def MaximalUnbalancingTriple (triple : G → G → Subgroup G → Prop)
    (edge isoEdge : G → Subgroup G → G → Subgroup G → Prop) (a x : G) (J : Subgroup G) : Prop :=
  triple a x J ∧
    ∀ (b : G) (L : Subgroup G), orderOf b = 2 → b ∈ centralizer ({a} : Set G) →
      edge a J b L →
      (∀ y ∈ centralizer ({a} : Set G) ⊓ normalizer (J : Set G),
          triple b y L → isoEdge a J b L) ∧
      ∀ S : Subgroup G, S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) →
        (∃ P : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
          (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) →
        b ∈ S → (∀ s ∈ S, s * b = b * s) →
        S ≤ centralizer ({b} : Set G) ⊓ normalizer (L : Set G) ∧
          ∃ P : Sylow 2 ↥(centralizer ({b} : Set G) ⊓ normalizer (L : Set G)),
            (P : Subgroup _) = S.subgroupOf (centralizer ({b} : Set G) ⊓ normalizer (L : Set G))

@[expose] def MaximalComponent (vertex : Subgroup G → Prop)
    (reach : Subgroup G → Subgroup G → Prop) (zstar : ∀ H : Subgroup G, Subgroup H)
    [∀ H : Subgroup G, (zstar H).Normal] (J : Subgroup G) : Prop :=
  vertex J ∧ ∀ L : Subgroup G, reach J L → Nonempty (J ⧸ zstar J ≃* L ⧸ zstar L)

section Basic

variable {comp : Subgroup G → Subgroup G → Prop} {core : Subgroup G → Subgroup G}
  {layer : Subgroup G → G → Subgroup G} {a b x : G} {J L : Subgroup G}

theorem Corr.involutionComponent_left (h : Corr comp core layer a J b L) :
    InvolutionComponent comp J :=
  ⟨a, h.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem Corr.involutionComponent_right (h : Corr comp core layer a J b L) :
    InvolutionComponent comp L :=
  ⟨b, h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

theorem UnbalancingTriple.involutionComponent (h : UnbalancingTriple comp core a x J) :
    InvolutionComponent comp J :=
  ⟨a, h.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem Corr.layer_eq (h : Corr comp core layer a J b L) (hK : L ⊔ conjugate L a = L) :
    layer J b = layer L a := by
  rw [h.2.2.2.2.2.2.2.2.2, hK]

variable {vertex : Subgroup G → Prop} {edge : G → Subgroup G → G → Subgroup G → Prop}
  {J₀ : Subgroup G}

theorem Reach.refl (hJ : vertex J) : Reach vertex edge J J :=
  ⟨hJ, Relation.ReflTransGen.refl⟩

theorem Reach.single (hJ : vertex J) (h : edge a J b L) : Reach vertex edge J L :=
  ⟨hJ, Relation.ReflTransGen.single ⟨a, b, h⟩⟩

theorem Reach.tail (h : Reach vertex edge J₀ J) (hC : edge a J b L) : Reach vertex edge J₀ L :=
  ⟨h.1, Relation.ReflTransGen.tail h.2 ⟨a, b, hC⟩⟩

theorem Reach.trans (h₁ : Reach vertex edge J₀ J) (h₂ : Reach vertex edge J L) :
    Reach vertex edge J₀ L :=
  ⟨h₁.1, h₁.2.trans h₂.2⟩

end Basic

theorem conjugate_eq_map_conj {a : G} (ha : orderOf a = 2) (L : Subgroup G) :
    conjugate L a = L.map (MulAut.conj a).toMonoidHom := by
  have haa : a * a = 1 := by rw [← sq, ← ha, pow_orderOf_eq_one]
  rw [conjugate, inv_eq_of_mul_eq_one_right haa]

theorem forall_mem_commutator_mem_iff {b : G} (hb : orderOf b = 2) {J K : Subgroup G} :
    (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ K) ↔ ⁅J, zpowers b⁆ ≤ K := by
  have hbb : b * b = 1 := by rw [← sq, ← hb, pow_orderOf_eq_one]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  constructor
  · intro h
    rw [Subgroup.commutator_le]
    intro j hj c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · rw [zpow_mul, zpow_two, hbb, one_zpow, commutatorElement_one_right]
      exact one_mem _
    · rw [zpow_add, zpow_mul, zpow_two, hbb, one_zpow, one_mul, zpow_one]
      have h1 := h j⁻¹ (inv_mem hj)
      rw [inv_inv, hbinv] at h1
      rwa [commutatorElement_def, hbinv]
  · intro h j hj
    have hc := h (Subgroup.commutator_mem_commutator (inv_mem hj) (inv_mem (mem_zpowers b)))
    simpa only [commutatorElement_def, inv_inv] using hc

theorem closure_conj_commutator_eq_commutator (J D : Subgroup G) :
    closure {y | ∃ j ∈ J, ∃ d ∈ D, y = j⁻¹ * d⁻¹ * j * d} = ⁅J, D⁆ := by
  rw [Subgroup.commutator_def]
  congr 1
  ext y
  constructor
  · rintro ⟨j, hj, d, hd, rfl⟩
    exact ⟨j⁻¹, inv_mem hj, d⁻¹, inv_mem hd, by rw [commutatorElement_def, inv_inv, inv_inv]⟩
  · rintro ⟨j, hj, d, hd, rfl⟩
    exact ⟨j⁻¹, inv_mem hj, d⁻¹, inv_mem hd, by rw [commutatorElement_def, inv_inv, inv_inv]⟩

theorem closure_elem_commutator_eq_commutator_zpowers (J : Subgroup G) {x : G}
    (hx : orderOf x = 2) :
    closure {y | ∃ j ∈ J, y = j⁻¹ * x⁻¹ * j * x} = ⁅J, zpowers x⁆ := by
  apply le_antisymm
  · rw [closure_le]
    rintro y ⟨j, hj, rfl⟩
    rw [show j⁻¹ * x⁻¹ * j * x = ⁅j⁻¹, x⁻¹⁆ by rw [commutatorElement_def, inv_inv, inv_inv]]
    exact commutator_mem_commutator (inv_mem hj) (inv_mem (mem_zpowers x))
  · rw [commutator_le]
    intro j hj z hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    have hxinv : x⁻¹ = x :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_two, ← hx, pow_orderOf_eq_one])
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [← zpow_mod_orderOf, hx, show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero,
        commutatorElement_one_right]
      exact one_mem _
    · rw [← zpow_mod_orderOf, hx, show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]
      apply subset_closure
      refine ⟨j⁻¹, inv_mem hj, ?_⟩
      rw [commutatorElement_def, inv_inv, hxinv]

theorem coe_sup_eq_mul {A L O : Subgroup G} (hA : A ≤ L) (hO : L ≤ normalizer (O : Set G)) :
    ((A ⊔ O : Subgroup G) : Set G) = (A : Set G) * (O : Set G) :=
  coe_mul_of_left_le_normalizer_right _ _ (hA.trans hO)

section Conventions

variable {comp : Subgroup G → Subgroup G → Prop} {core : Subgroup G → Subgroup G}
  {layer : Subgroup G → G → Subgroup G} {a b x : G} {J L : Subgroup G}

theorem corr_iff_commutator :
    Corr comp core layer a J b L ↔ orderOf a = 2 ∧ orderOf b = 2 ∧ a * b = b * a ∧
      (J ≤ centralizer ({a} : Set G) ∧ comp J (centralizer ({a} : Set G))) ∧
      (L ≤ centralizer ({b} : Set G) ∧ comp L (centralizer ({b} : Set G))) ∧
      b ∈ normalizer (J : Set G) ∧ ⁅J, zpowers b⁆ ≤ core J ∧
      layer J b = layer (L ⊔ L.map (MulAut.conj a).toMonoidHom) a := by
  constructor
  · rintro ⟨ha, hb, hab, hJa, hJ, hLb, hL, hbN, hJb, hfix⟩
    exact ⟨ha, hb, hab, ⟨hJa, hJ⟩, ⟨hLb, hL⟩, hbN, (forall_mem_commutator_mem_iff hb).1 hJb,
      conjugate_eq_map_conj ha L ▸ hfix⟩
  · rintro ⟨ha, hb, hab, ⟨hJa, hJ⟩, ⟨hLb, hL⟩, hbN, hJb, hfix⟩
    exact ⟨ha, hb, hab, hJa, hJ, hLb, hL, hbN, (forall_mem_commutator_mem_iff hb).2 hJb,
      (conjugate_eq_map_conj ha L).symm ▸ hfix⟩

theorem isoCorr_iff_sup {edge : G → Subgroup G → G → Subgroup G → Prop}
    (hle : edge a J b L → L ⊔ conjugate L a = L → layer J b ≤ L)
    (hcore : L ≤ normalizer (core L : Set G)) :
    IsoCorr edge core layer a J b L ↔ edge a J b L ∧ L ⊔ conjugate L a = L ∧
      layer J b ⊔ core L = L := by
  constructor
  · rintro ⟨h, hK, hmul⟩
    refine ⟨h, hK, SetLike.coe_injective ?_⟩
    rw [coe_sup_eq_mul (hle h hK) hcore, hmul]
  · rintro ⟨h, hK, hsup⟩
    refine ⟨h, hK, ?_⟩
    rw [← coe_sup_eq_mul (hle h hK) hcore, hsup]

theorem Corr.layer_le (hlayer : ∀ N t, layer N t ≤ N) (h : Corr comp core layer a J b L)
    (hK : L ⊔ conjugate L a = L) : layer J b ≤ L :=
  (h.layer_eq hK).le.trans (hlayer L a)

theorem unbalancingTriple_iff_commutator :
    UnbalancingTriple comp core a x J ↔ orderOf a = 2 ∧ orderOf x = 2 ∧ a * x = x * a ∧
      (J ≤ centralizer ({a} : Set G) ∧ comp J (centralizer ({a} : Set G))) ∧
      ⁅J, zpowers x⁆ = J ∧
      ⁅J, core (centralizer ({x} : Set G)) ⊓ centralizer ({a} : Set G)⁆ = J := by
  constructor
  · rintro ⟨ha, hx, hax, hJa, hJ, h1, h2⟩
    refine ⟨ha, hx, hax, ⟨hJa, hJ⟩, ?_, ?_⟩
    · rwa [← closure_elem_commutator_eq_commutator_zpowers J hx]
    · rwa [← closure_conj_commutator_eq_commutator]
  · rintro ⟨ha, hx, hax, ⟨hJa, hJ⟩, h1, h2⟩
    refine ⟨ha, hx, hax, hJa, hJ, ?_, ?_⟩
    · rwa [closure_elem_commutator_eq_commutator_zpowers J hx]
    · rwa [closure_conj_commutator_eq_commutator]

end Conventions

section Congr

variable {comp comp' : Subgroup G → Subgroup G → Prop} {core core' : Subgroup G → Subgroup G}
  {layer layer' : Subgroup G → G → Subgroup G}

theorem corr_congr (hcomp : ∀ J K : Subgroup G, J ≤ K → (comp J K ↔ comp' J K))
    (hcore : core = core') (hlayer : layer = layer') {a b : G} {J L : Subgroup G} :
    Corr comp core layer a J b L ↔ Corr comp' core' layer' a J b L := by
  subst hcore hlayer
  constructor
  · rintro ⟨ha, hb, hab, hJa, hJ, hLb, hL, rest⟩
    exact ⟨ha, hb, hab, hJa, (hcomp _ _ hJa).1 hJ, hLb, (hcomp _ _ hLb).1 hL, rest⟩
  · rintro ⟨ha, hb, hab, hJa, hJ, hLb, hL, rest⟩
    exact ⟨ha, hb, hab, hJa, (hcomp _ _ hJa).2 hJ, hLb, (hcomp _ _ hLb).2 hL, rest⟩

theorem isoCorr_congr {edge edge' : G → Subgroup G → G → Subgroup G → Prop}
    (hedge : ∀ a J b L, edge a J b L ↔ edge' a J b L) (hcore : core = core')
    (hlayer : layer = layer') {a b : G} {J L : Subgroup G} :
    IsoCorr edge core layer a J b L ↔ IsoCorr edge' core' layer' a J b L := by
  subst hcore hlayer
  exact and_congr_left' (hedge a J b L)

theorem unbalancingTriple_congr (hcomp : ∀ J K : Subgroup G, J ≤ K → (comp J K ↔ comp' J K))
    (hcore : core = core') {a x : G} {J : Subgroup G} :
    UnbalancingTriple comp core a x J ↔ UnbalancingTriple comp' core' a x J := by
  subst hcore
  constructor
  · rintro ⟨ha, hx, hax, hJa, hJ, rest⟩
    exact ⟨ha, hx, hax, hJa, (hcomp _ _ hJa).1 hJ, rest⟩
  · rintro ⟨ha, hx, hax, hJa, hJ, rest⟩
    exact ⟨ha, hx, hax, hJa, (hcomp _ _ hJa).2 hJ, rest⟩

theorem involutionComponent_congr
    (hcomp : ∀ J K : Subgroup G, J ≤ K → (comp J K ↔ comp' J K)) {J : Subgroup G} :
    InvolutionComponent comp J ↔ InvolutionComponent comp' J := by
  constructor
  · rintro ⟨a, ha, hJa, hJ⟩
    exact ⟨a, ha, hJa, (hcomp _ _ hJa).1 hJ⟩
  · rintro ⟨a, ha, hJa, hJ⟩
    exact ⟨a, ha, hJa, (hcomp _ _ hJa).2 hJ⟩

theorem reach_congr {vertex vertex' : Subgroup G → Prop}
    {edge edge' : G → Subgroup G → G → Subgroup G → Prop} (hvertex : ∀ J, vertex J ↔ vertex' J)
    (hedge : ∀ a J b L, edge a J b L ↔ edge' a J b L) {J L : Subgroup G} :
    Reach vertex edge J L ↔ Reach vertex' edge' J L := by
  have hrel : (fun J' L' : Subgroup G => ∃ a b : G, edge a J' b L') =
      fun J' L' => ∃ a b : G, edge' a J' b L' := by
    simp only [hedge]
  rw [Reach, Reach, hvertex, hrel]

theorem maximalUnbalancingTriple_congr {triple triple' : G → G → Subgroup G → Prop}
    {edge edge' isoEdge isoEdge' : G → Subgroup G → G → Subgroup G → Prop}
    (htriple : ∀ a x J, triple a x J ↔ triple' a x J)
    (hedge : ∀ a J b L, edge a J b L ↔ edge' a J b L)
    (hiso : ∀ a J b L, isoEdge a J b L ↔ isoEdge' a J b L) {a x : G} {J : Subgroup G} :
    MaximalUnbalancingTriple triple edge isoEdge a x J ↔
      MaximalUnbalancingTriple triple' edge' isoEdge' a x J := by
  simp only [MaximalUnbalancingTriple, htriple, hedge, hiso]

theorem maximalComponent_congr {vertex vertex' : Subgroup G → Prop}
    {reach reach' : Subgroup G → Subgroup G → Prop} {zstar : ∀ H : Subgroup G, Subgroup H}
    [∀ H : Subgroup G, (zstar H).Normal] (hvertex : ∀ J, vertex J ↔ vertex' J)
    (hreach : ∀ J L, reach J L ↔ reach' J L) {J : Subgroup G} :
    MaximalComponent vertex reach zstar J ↔ MaximalComponent vertex' reach' zstar J := by
  simp only [MaximalComponent, hvertex, hreach]

end Congr

end CFSG.GSGrammar
