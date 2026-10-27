module

public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassURankClass
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassURankLevi

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily)
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_normal)
open scoped commutatorElement

local instance e7ClassUF5NeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

section General

variable {G : Type*} [Group G]

theorem commutatorElement_mem_inf {A B : Subgroup G} {a b : G} (ha : a ∈ A) (hb : b ∈ B)
    (haB : a ∈ normalizer (B : Set G)) (hbA : b ∈ normalizer (A : Set G)) : ⁅a, b⁆ ∈ A ⊓ B := by
  rw [commutatorElement_def]
  refine ⟨?_, ?_⟩
  · have h : b * a⁻¹ * b⁻¹ ∈ A := (mem_normalizer_iff.1 hbA _).1 (A.inv_mem ha)
    have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [e]
    exact mul_mem ha h
  · have h : a * b * a⁻¹ ∈ B := (mem_normalizer_iff.1 haB _).1 hb
    exact mul_mem h (B.inv_mem hb)

theorem le_normalizer_perfectCore (H : Subgroup G) :
    H ≤ normalizer (perfectCore H : Set G) :=
  (normal_subgroupOf_iff_le_normalizer (perfectCore_le H)).1 (perfectCore_normal H)

end General

@[expose] noncomputable def nodeWordWeyl : List (Fin Tag.E7.rank) → WeylGroup .E7
  | [] => 1
  | i :: ω => nodeWordWeyl ω * simple .E7 i

theorem nodeWordWeyl_smul (ω : List (Fin Tag.E7.rank)) (v : Fin Tag.E7.rank → ℤ) :
    nodeWordWeyl ω • v = ω.foldl (fun v i => reflect .E7 i v) v := by
  induction ω generalizing v with
  | nil => rw [nodeWordWeyl, one_smul, List.foldl_nil]
  | cons i ω ih => rw [nodeWordWeyl, mul_smul, simple_smul, ih, List.foldl_cons]

theorem nodeWordWeyl_mem_parabolicWeylGroup {J : Set (Fin Tag.E7.rank)}
    {ω : List (Fin Tag.E7.rank)} (hω : ∀ i ∈ ω, i ∈ J) :
    nodeWordWeyl ω ∈ parabolicWeylGroup .E7 J := by
  induction ω with
  | nil => exact one_mem _
  | cons i ω ih =>
    exact mul_mem (ih fun j hj => hω j (List.mem_cons_of_mem _ hj))
      (subset_closure ⟨i, hω i List.mem_cons_self, rfl⟩)

@[expose] def uWord₁ : List (Fin Tag.E7.rank) := [1, 3, 2, 0, 4, 3, 1, 2, 5, 4]

@[expose] def uWord₂ : List (Fin Tag.E7.rank) := [1, 3, 2, 0, 4, 3, 1, 2, 5, 4, 3]

theorem uWords_mem : (∀ i ∈ uWord₁, i ∈ uNodes) ∧ ∀ i ∈ uWord₂, i ∈ uNodes := by
  simp only [uNodes, Set.mem_ofPred_eq]
  decide

theorem uWords_smul :
    nodeWordWeyl uWord₁ • uTopRoot = Pi.single 3 1 ∧
      nodeWordWeyl uWord₂ • uTopRoot = -Pi.single 3 1 := by
  rw [nodeWordWeyl_smul, nodeWordWeyl_smul]
  decide

section RootSubgroups

variable {K : Type} [Field K]


theorem map_conj_e7RepConj_rootSubgroup_alpha4 (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    (rootSubgroup .E7 K (ε • Pi.single 3 1)).map
        (MulAut.conj (e7RepConj K 3 : ModGL .E7 K)).toMonoidHom =
      rootSubgroup .E7 K (ε • highRoot .E7) := by
  have hpre : e7RepPreHigh 3 = Pi.single 3 1 := e7RepPreHigh_three
  have hr : IsRoot .E7 (ε • Pi.single (3 : Fin Tag.E7.rank) 1) := by
    rcases hε with rfl | rfl
    · rw [one_smul]; exact isRoot_single .E7 3
    · rw [neg_one_smul]; exact isRoot_neg_single .E7 3
  rw [map_conj_e7RepConj_rootSubgroup 3 hr, smul_comm, ← hpre, e7RepWeyl_smul_e7RepPreHigh]

theorem rootSubgroup_smul_highRoot_mem_leviURootSubgroups (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    (rootSubgroup .E7 K (ε • highRoot .E7)).subgroupOf (adjointGroup .E7 K) ∈
      leviURootSubgroups K := by
  set v := if ε = 1 then nodeWordWeyl uWord₁ else nodeWordWeyl uWord₂ with hv
  have hvJ : v ∈ parabolicWeylGroup .E7 uNodes := by
    rw [hv]
    split_ifs
    exacts [nodeWordWeyl_mem_parabolicWeylGroup uWords_mem.1,
      nodeWordWeyl_mem_parabolicWeylGroup uWords_mem.2]
  have hvr : v • uTopRoot = ε • Pi.single 3 1 := by
    rw [hv]
    rcases hε with rfl | rfl
    · rw [ite_eq_left rfl, one_smul]; exact uWords_smul.1
    · rw [ite_eq_right (by decide), neg_one_smul]; exact uWords_smul.2
  set n := e7RepConj K 3 with hn
  set m : adjointGroup .E7 K :=
    ⟨canonicalRep (coxeterSystem .E7) K v, canonicalRep_mem_adjointGroup _ K v⟩ with hm
  have hmM : (m : ModGL .E7 K) ∈ parabolicLevi .E7 K uNodes := canonicalRep_mem_parabolicLevi hvJ
  refine ⟨n * m * n⁻¹, ⟨m, mem_subgroupOf.2 hmM, rfl⟩, ?_⟩
  have hU : ((rootSubgroup .E7 K uTopRoot).subgroupOf (adjointGroup .E7 K)).map
      (MulAut.conj m).toMonoidHom =
        (rootSubgroup .E7 K (ε • Pi.single 3 1)).subgroupOf (adjointGroup .E7 K) := by
    rw [CFSG.LieType.Chevalley.map_conj_subgroupOf (rootSubgroup_le_adjointGroup _),
      (canonical_weyl_root_transport .E7 K).2.1 v _ isRoot_uTopRoot, hvr]
  rw [uRootGroup, CFSG.LieType.Chevalley.map_conj_map_conj, show n * m * n⁻¹ * n = n * m by group,
    ← CFSG.LieType.Chevalley.map_conj_map_conj, hU,
    CFSG.LieType.Chevalley.map_conj_subgroupOf (rootSubgroup_le_adjointGroup _),
    map_conj_e7RepConj_rootSubgroup_alpha4 ε hε]

end RootSubgroups

@[expose] def uQ24 : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)) :=
  [(![0, 0, 0, 0, 0, 0, 1], ![-1, 0, -1, -1, -1, -1, 0]),
   (![0, 0, 0, 0, 0, 1, 1], ![0, 0, -1, -1, -1, 0, 0]),
   (![0, 0, 0, 0, 1, 1, 1], ![0, 0, 0, -1, 0, 0, 0]),
   (![0, 0, 0, 1, 1, 1, 1], ![0, -1, 0, 0, 0, 0, 0]),
   (![0, 0, 1, 1, 1, 1, 1], ![0, -1, 0, 0, 0, 0, 0]),
   (![0, 1, 0, 1, 1, 1, 1], ![0, 1, 0, 0, 0, 0, 0]),
   (![0, 1, 1, 1, 1, 1, 1], ![0, 0, 0, -1, 0, 0, 0]),
   (![0, 1, 1, 2, 1, 1, 1], ![0, 0, 0, 1, 0, 0, 0]),
   (![0, 1, 1, 2, 2, 1, 1], ![0, 0, 1, 1, 1, 0, 0]),
   (![1, 0, 1, 1, 1, 1, 1], ![0, -1, 0, 0, 0, 0, 0]),
   (![1, 1, 1, 1, 1, 1, 1], ![0, 0, 0, -1, 0, 0, 0]),
   (![1, 1, 1, 2, 1, 1, 1], ![0, 0, 0, 1, 0, 0, 0]),
   (![1, 1, 1, 2, 2, 2, 1], ![0, 0, -1, -1, -1, 0, 0]),
   (![1, 1, 2, 2, 2, 1, 1], ![0, 0, 0, -1, 0, 0, 0]),
   (![1, 1, 2, 2, 2, 2, 1], ![0, 0, 0, -1, 0, 0, 0]),
   (![1, 1, 2, 3, 2, 1, 1], ![0, -1, 0, 0, 0, 0, 0]),
   (![1, 1, 2, 3, 2, 2, 1], ![0, -1, 0, 0, 0, 0, 0]),
   (![1, 1, 2, 3, 3, 2, 1], ![0, -1, 0, 0, 0, 0, 0]),
   (![1, 2, 2, 3, 2, 1, 1], ![0, 1, 0, 0, 0, 0, 0]),
   (![1, 2, 2, 3, 2, 2, 1], ![0, 1, 0, 0, 0, 0, 0]),
   (![1, 2, 2, 3, 3, 2, 1], ![0, 0, 0, -1, 0, 0, 0]),
   (![1, 2, 2, 4, 3, 2, 1], ![0, 0, 0, 1, 0, 0, 0]),
   (![1, 2, 3, 4, 3, 2, 1], ![0, 0, 1, 1, 1, 0, 0]),
   (![2, 2, 3, 4, 3, 2, 1], ![1, 0, 1, 1, 1, 1, 0])]

theorem uQ24_check : (∀ ρ ∈ uLow ++ uHigh, ρ ∈ uQ24.map Prod.fst) ∧
    ∀ p ∈ uQ24, isRootB .E7 p.2 = true ∧ uLevel p.2 = 0 ∧ p.1 - p.2 ∈ uPsi ∧
      ∀ f ∈ uFrame, isRootB .E7 (p.2 + f) = false ∧ isRootB .E7 (-p.2 + f) = false := by
  decide +kernel

@[expose] def uDiagB : Fin Tag.E7.rank → ℤ := ![1, 1, 1, 2, 1, 1, 1]

@[expose] def uDiagC : Fin Tag.E7.rank → ℤ := ![1, 1, 2, 2, 2, 1, 1]

theorem uDiag_check :
    uDiagB ∈ uPsi ∧ Pi.single 4 1 + uDiagB = uφ ∧ Pi.single 2 1 + uDiagB = uψ ∧
      Pi.single 2 1 + uφ = uDiagC ∧ uDiagC ∈ uLow ++ uHigh ∧
      isRootB .E7 uφ = true ∧ isRootB .E7 uψ = true ∧ isRootB .E7 uDiagC = true ∧
      (∀ f ∈ uFrame, isRootB .E7 (Pi.single 3 1 + f) = false ∧
        isRootB .E7 (-Pi.single 3 1 + f) = false) := by
  decide +kernel

section Large

variable {K : Type} [Field K]


variable (K) in
@[expose] noncomputable def uCoreRadicalAS : Subgroup (ModGL .E7 K) :=
  ((uCoreRadical K).map (MulAut.conj (e7RepConj K 3)⁻¹).toMonoidHom).map
    (adjointGroup .E7 K).subtype

theorem mem_uCoreRadicalAS_of {y : adjointGroup .E7 K}
    (h : e7RepConj K 3 * y * (e7RepConj K 3)⁻¹ ∈ uCoreRadical K) :
    (y : ModGL .E7 K) ∈ uCoreRadicalAS K :=
  ⟨y, ⟨_, h, by simp [mul_assoc]⟩, rfl⟩

theorem conj_mem_uCoreRadical_of {y : adjointGroup .E7 K}
    (h : (y : ModGL .E7 K) ∈ uCoreRadicalAS K) :
    e7RepConj K 3 * y * (e7RepConj K 3)⁻¹ ∈ uCoreRadical K := by
  obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := h
  have e : x = e7RepConj K 3 * y * (e7RepConj K 3)⁻¹ := by
    have h' : (e7RepConj K 3)⁻¹ * x * (e7RepConj K 3)⁻¹⁻¹ = y :=
      Subtype.ext (by simpa [MulAut.conj_apply] using hxy)
    rw [← h']
    group
  rw [← e]
  exact hx

theorem commutator_radicalU_le_uCoreRadical [CharP K 2] {X : Subgroup (adjointGroup .E7 K)}
    (hXΛ : X ≤ perfectCore (centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K))))
    (hXN : X ≤ leviU K) : ⁅radicalU K, X⁆ ≤ uCoreRadical K := by
  rw [commutator_le]
  intro r hr x hx
  have h := commutatorElement_mem_inf hr (hXΛ hx)
    (le_normalizer_perfectCore _ (radicalU_le_centralizer hr))
    (leviU_le_normalizer_radicalU (hXN hx))
  rw [uCoreRadical, inf_comm]
  exact h

theorem rootSL2_le_centralizer_uAS {δ : Fin Tag.E7.rank → ℤ} (hδ : IsRoot .E7 δ)
    (hδ0 : uLevel δ = 0) (hperp : ∀ f ∈ uFrame, ¬IsRoot .E7 (δ + f) ∧ ¬IsRoot .E7 (-δ + f)) :
    rootSubgroup .E7 K δ ⊔ rootSubgroup .E7 K (-δ) ≤
      centralizer ({uAS K} : Set (ModGL .E7 K)) := by
  refine sup_le ((closure_le _).2 ?_) ((closure_le _).2 ?_)
  · rintro _ ⟨t, rfl⟩
    exact mem_centralizer_singleton_iff.2
      (commute_uAS_of_forall hδ hδ0 (fun f hf => (hperp f hf).1) t).eq
  · rintro _ ⟨t, rfl⟩
    exact mem_centralizer_singleton_iff.2
      (commute_uAS_of_forall (IsRoot.neg hδ) (by rw [uLevel_neg, hδ0, neg_zero])
        (fun f hf => (hperp f hf).2) t).eq

theorem mem_parabolicRoots_of_uLevel {δ : Fin Tag.E7.rank → ℤ} (hδ : IsRoot .E7 δ)
    (hδ0 : uLevel δ = 0) : δ ∈ parabolicRoots .E7 uNodes := by
  refine ⟨hδ, fun i hi => ?_⟩
  simp only [uNodes, Set.mem_ofPred_eq, not_not] at hi
  rw [hi]
  exact hδ0

theorem map_rootSL2_le_perfectCore [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    {δ : Fin Tag.E7.rank → ℤ} (hδ : IsRoot .E7 δ) (hδ0 : uLevel δ = 0)
    (hperp : ∀ f ∈ uFrame, ¬IsRoot .E7 (δ + f) ∧ ¬IsRoot .E7 (-δ + f)) :
    ((rootSubgroup .E7 K δ ⊔ rootSubgroup .E7 K (-δ)).subgroupOf (adjointGroup .E7 K)).map
        (MulAut.conj (e7RepConj K 3)).toMonoidHom ≤
      perfectCore (centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K))) ⊓ leviU K := by
  set J := rootSubgroup .E7 K δ ⊔ rootSubgroup .E7 K (-δ) with hJ
  have hJC : J ≤ adjointGroup .E7 K :=
    sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)
  have hperf : ⁅J, J⁆ = J := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h⟩ :=
      CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps (τ := .E7) K hδ
    exact Subgroup.isPerfect_iff.1 (h ‹Finite K› hq).2.1
  have hperf' : ⁅(J.subgroupOf (adjointGroup .E7 K)).map (MulAut.conj (e7RepConj K 3)).toMonoidHom,
      (J.subgroupOf (adjointGroup .E7 K)).map (MulAut.conj (e7RepConj K 3)).toMonoidHom⁆ =
        (J.subgroupOf (adjointGroup .E7 K)).map (MulAut.conj (e7RepConj K 3)).toMonoidHom := by
    rw [← map_commutator, CFSG.SeitzReduction.commutator_subgroupOf_eq_self hJC hperf]
  refine le_inf (le_perfectCore_of_perfect ?_ hperf') ?_
  · rintro _ ⟨j, hj, rfl⟩
    have hju : (j : ModGL .E7 K) * uAS K = uAS K * j :=
      mem_centralizer_singleton_iff.1
        (rootSL2_le_centralizer_uAS hδ hδ0 hperp (mem_subgroupOf.1 hj))
    exact conj_mem_centralizer_e7Rep_three hju
  · refine Subgroup.map_mono fun j hj => mem_subgroupOf.2 ?_
    have hJM : J ≤ parabolicLevi .E7 K uNodes :=
      sup_le (F4Pilot.rootSubgroup_le_parabolicLevi (mem_parabolicRoots_of_uLevel hδ hδ0))
        (F4Pilot.rootSubgroup_le_parabolicLevi (mem_parabolicRoots_of_uLevel (IsRoot.neg hδ)
          (by rw [uLevel_neg, hδ0, neg_zero])))
    exact hJM (mem_subgroupOf.1 hj)

theorem rootSubgroup_uTopRoot_le_parabolicLevi :
    rootSubgroup .E7 K uTopRoot ≤ parabolicLevi .E7 K uNodes :=
  F4Pilot.rootSubgroup_le_parabolicLevi (mem_parabolicRoots_of_uLevel isRoot_uTopRoot
    uTop_check.2.2.2.1)

theorem pinnedX_mem_uCoreRadicalAS [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    {ρ : Fin Tag.E7.rank → ℤ} (hρ : ρ ∈ uLow ++ uHigh) (s : K) :
    pinnedX .E7 K ρ s ∈ uCoreRadicalAS K := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (uQ24_check.1 ρ hρ)
  obtain ⟨hδr, hδ0, hb, hperp⟩ := uQ24_check.2 p hp
  have hδ := isRootB_iff.1 hδr
  have hperp' : ∀ f ∈ uFrame, ¬IsRoot .E7 (p.2 + f) ∧ ¬IsRoot .E7 (-p.2 + f) := fun f hf =>
    ⟨not_isRoot_of_isRootB_false (hperp f hf).1, not_isRoot_of_isRootB_false (hperp f hf).2⟩
  have hsum : p.1 - p.2 + p.2 = p.1 := by abel
  have hρΨ : p.1 ∈ uPsi := by
    rcases List.mem_append.1 hρ with h | h
    exacts [mem_uPsi_of_mem_uLow h, mem_uPsi_of_mem_uHigh h]
  have hne := ne_of_uLevel_zero hδ0 hb
  have hc := CFSG.SeitzReduction.commutatorElement_pinnedX_of_oddDerivLaced (R := K)
    CharTwo.two_eq_zero
    (CFSG.SeitzReduction.oddDerivLacedCheck_of_simplyLaced (Or.inr (Or.inr (Or.inl rfl))))
    (isRoot_of_mem_uPsi hb) hδ (Ne.symm hne.1) (fun h => hne.2 (by rw [h, neg_neg]))
    (by rw [hsum]; exact isRoot_of_mem_uPsi hρΨ) s 1
  rw [hsum, mul_one] at hc
  set n := e7RepConj K 3
  set r : adjointGroup .E7 K := ⟨pinnedX .E7 K (p.1 - p.2) s, pinnedX_mem_adjointGroup _ _⟩
  set j : adjointGroup .E7 K := ⟨pinnedX .E7 K p.2 1, pinnedX_mem_adjointGroup _ _⟩
  have hrR : n * r * n⁻¹ ∈ radicalU K :=
    ⟨r, mem_subgroupOf.2 (pinnedX_mem_rootSpan (mem_parabolicRadicalRoots_of_mem_uPsi hb) s),
      rfl⟩
  have hjJ : n * j * n⁻¹ ∈ ((rootSubgroup .E7 K p.2 ⊔ rootSubgroup .E7 K (-p.2)).subgroupOf
      (adjointGroup .E7 K)).map (MulAut.conj n).toMonoidHom :=
    ⟨j, mem_subgroupOf.2 (mem_sup_left (mem_rootSubgroup.2 ⟨1, rfl⟩)), rfl⟩
  have hmem := commutator_radicalU_le_uCoreRadical
    (fun x hx => (map_rootSL2_le_perfectCore hq hδ hδ0 hperp' hx).1)
    (fun x hx => (map_rootSL2_le_perfectCore hq hδ hδ0 hperp' hx).2)
    (commutator_mem_commutator hrR hjJ)
  have hrj : ⁅r, j⁆ = ⟨pinnedX .E7 K p.1 s, pinnedX_mem_adjointGroup _ _⟩ := by
    apply Subtype.ext
    rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_inv, ← commutatorElement_def]
    exact hc
  refine mem_uCoreRadicalAS_of (y := ⟨pinnedX .E7 K p.1 s, pinnedX_mem_adjointGroup _ _⟩) ?_
  rw [← hrj, ← MulAut.conj_apply, map_commutatorElement, MulAut.conj_apply, MulAut.conj_apply]
  exact hmem

theorem conj_pinnedX_uPsi_of_isRoot [CharP K 2] {a β : Fin Tag.E7.rank → ℤ} (ha : IsRoot .E7 a)
    (ha0 : uLevel a = 0) (hβ : β ∈ uPsi) (hr : IsRoot .E7 (a + β)) (t s : K) :
    pinnedX .E7 K a t * pinnedX .E7 K β s * (pinnedX .E7 K a t)⁻¹ =
      pinnedX .E7 K β s * pinnedX .E7 K (a + β) (t * s) := by
  have hne := ne_of_uLevel_zero ha0 hβ
  have hc := CFSG.SeitzReduction.commutatorElement_pinnedX_of_oddDerivLaced (R := K)
    CharTwo.two_eq_zero
    (CFSG.SeitzReduction.oddDerivLacedCheck_of_simplyLaced (Or.inr (Or.inr (Or.inl rfl))))
    ha (isRoot_of_mem_uPsi hβ) hne.1 hne.2 hr t s
  rw [commutatorElement_def] at hc
  have hρ : a + β ∈ uPsi := mem_uPsi_of_level hr (by
    rw [uLevel_add, ha0, zero_add, level_of_mem_uPsi hβ])
  calc pinnedX .E7 K a t * pinnedX .E7 K β s * (pinnedX .E7 K a t)⁻¹ =
        (pinnedX .E7 K a t * pinnedX .E7 K β s * (pinnedX .E7 K a t)⁻¹ *
          (pinnedX .E7 K β s)⁻¹) * pinnedX .E7 K β s := by group
    _ = pinnedX .E7 K (a + β) (t * s) * pinnedX .E7 K β s := by rw [hc]
    _ = pinnedX .E7 K β s * pinnedX .E7 K (a + β) (t * s) := (uPsi_comm β hβ _ hρ s _).eq.symm

theorem pinnedX_psi_mul_phi_mem_uCoreRadicalAS [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (s : K) : pinnedX .E7 K uψ s * pinnedX .E7 K uφ s ∈ uCoreRadicalAS K := by
  obtain ⟨hb, h5, h3, h3φ, hχ, hφr, hψr, hχr, -⟩ := uDiag_check
  set x3 := pinnedX .E7 K (Pi.single 2 1) (1 : K)
  set x5 := pinnedX .E7 K (Pi.single 4 1) (1 : K)
  have e5 := conj_pinnedX_uPsi_of_isRoot (K := K) (isRoot_single .E7 4)
    (uLevel_single_check 4 (by decide)).1 hb (by rw [h5]; exact isRootB_iff.1 hφr) 1 s
  have e3 := conj_pinnedX_uPsi_of_isRoot (K := K) (isRoot_single .E7 2)
    (uLevel_single_check 2 (by decide)).1 hb (by rw [h3]; exact isRootB_iff.1 hψr) 1 s
  have hφΨ : uφ ∈ uPsi := mem_uPsi_of_mem_uFrame (show uφ ∈ uFrame by rw [uFrame_eq]; simp)
  have hψΨ : uψ ∈ uPsi := mem_uPsi_of_mem_uFrame (show uψ ∈ uFrame by rw [uFrame_eq]; simp)
  have e3' := conj_pinnedX_uPsi_of_isRoot (K := K) (isRoot_single .E7 2)
    (uLevel_single_check 2 (by decide)).1 hφΨ (by rw [h3φ]; exact isRootB_iff.1 hχr) 1 s
  rw [h5, one_mul] at e5
  rw [h3, one_mul] at e3
  rw [h3φ, one_mul] at e3'
  have hχΨ : uDiagC ∈ uPsi := by
    rcases List.mem_append.1 hχ with h | h
    exacts [mem_uPsi_of_mem_uLow h, mem_uPsi_of_mem_uHigh h]
  have hcomm : ⁅x3 * x5, pinnedX .E7 K uDiagB s⁆ =
      pinnedX .E7 K uψ s * pinnedX .E7 K uφ s * pinnedX .E7 K uDiagC s := by
    have hg : (x3 * x5) * pinnedX .E7 K uDiagB s * (x3 * x5)⁻¹ =
        pinnedX .E7 K uDiagB s * pinnedX .E7 K uψ s * (pinnedX .E7 K uφ s *
          pinnedX .E7 K uDiagC s) := by
      calc (x3 * x5) * pinnedX .E7 K uDiagB s * (x3 * x5)⁻¹ =
            x3 * (x5 * pinnedX .E7 K uDiagB s * x5⁻¹) * x3⁻¹ := by group
        _ = (x3 * pinnedX .E7 K uDiagB s * x3⁻¹) * (x3 * pinnedX .E7 K uφ s * x3⁻¹) := by
            rw [e5]; group
        _ = _ := by rw [e3, e3']
    rw [commutatorElement_def, hg]
    have c1 := (uPsi_comm uDiagB hb uψ hψΨ s s).eq
    have c23 := ((uPsi_comm uDiagB hb uφ hφΨ s s).mul_right
      (uPsi_comm uDiagB hb uDiagC hχΨ s s)).eq
    calc pinnedX .E7 K uDiagB s * pinnedX .E7 K uψ s * (pinnedX .E7 K uφ s *
          pinnedX .E7 K uDiagC s) * (pinnedX .E7 K uDiagB s)⁻¹ =
        pinnedX .E7 K uψ s * (pinnedX .E7 K uDiagB s * (pinnedX .E7 K uφ s *
          pinnedX .E7 K uDiagC s)) * (pinnedX .E7 K uDiagB s)⁻¹ := by rw [c1]; group
      _ = pinnedX .E7 K uψ s * ((pinnedX .E7 K uφ s * pinnedX .E7 K uDiagC s) *
          pinnedX .E7 K uDiagB s) * (pinnedX .E7 K uDiagB s)⁻¹ := by rw [c23]
      _ = _ := by group
  set n := e7RepConj K 3
  have hgC : x3 * x5 ∈ adjointGroup .E7 K :=
    mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)
  have hgF : (⟨x3 * x5, hgC⟩ : adjointGroup .E7 K) ∈ uF4AS K := by
    refine subset_closure ⟨2, 1, Or.inl ?_⟩
    exact (uOrbitX_eq (K := K) (1 : K)).2.2.1.symm
  have hgΛ : n * ⟨x3 * x5, hgC⟩ * n⁻¹ ∈ uF4 K := ⟨_, hgF, rfl⟩
  set r : adjointGroup .E7 K := ⟨pinnedX .E7 K uDiagB s, pinnedX_mem_adjointGroup _ _⟩ with hr
  have hrR : n * r * n⁻¹ ∈ radicalU K :=
    ⟨r, mem_subgroupOf.2 (pinnedX_mem_rootSpan (mem_parabolicRadicalRoots_of_mem_uPsi hb) s),
      rfl⟩
  have hmem := commutatorElement_mem_inf (uF4_le_perfectCore_centralizer hgΛ) hrR
    (leviU_le_normalizer_radicalU (uF4_le_leviU hgΛ))
    (le_normalizer_perfectCore _ (radicalU_le_centralizer hrR))
  change _ ∈ uCoreRadical K at hmem
  have hcomm' : ⁅(⟨x3 * x5, hgC⟩ : adjointGroup .E7 K), r⁆ =
        ⟨pinnedX .E7 K uψ s * pinnedX .E7 K uφ s * pinnedX .E7 K uDiagC s,
          mul_mem (mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _))
            (pinnedX_mem_adjointGroup _ _)⟩ := by
    apply Subtype.ext
    rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_inv, ← commutatorElement_def]
    exact hcomm
  have h1 : pinnedX .E7 K uψ s * pinnedX .E7 K uφ s * pinnedX .E7 K uDiagC s ∈
      uCoreRadicalAS K := by
    refine mem_uCoreRadicalAS_of (y := ⟨_, mul_mem (mul_mem (pinnedX_mem_adjointGroup _ _)
      (pinnedX_mem_adjointGroup _ _)) (pinnedX_mem_adjointGroup _ _)⟩) ?_
    rw [← hcomm', ← MulAut.conj_apply, map_commutatorElement, MulAut.conj_apply,
      MulAut.conj_apply]
    exact hmem
  have h2 := pinnedX_mem_uCoreRadicalAS hq hχ s
  have e : pinnedX .E7 K uψ s * pinnedX .E7 K uφ s =
      (pinnedX .E7 K uψ s * pinnedX .E7 K uφ s * pinnedX .E7 K uDiagC s) *
        (pinnedX .E7 K uDiagC s)⁻¹ := by group
  rw [e]
  exact mul_mem h1 (inv_mem h2)

variable (K) in
@[expose] noncomputable def uComplElt (c : K × K) : adjointGroup .E7 K :=
  e7RepConj K 3 * ⟨pinnedX .E7 K uφ c.1 * pinnedX .E7 K uθ c.2,
    mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)⟩ * (e7RepConj K 3)⁻¹

theorem uφ_mem_uPsi : uφ ∈ uPsi := mem_uPsi_of_mem_uFrame (show uφ ∈ uFrame by rw [uFrame_eq]; simp)

theorem uψ_mem_uPsi : uψ ∈ uPsi := mem_uPsi_of_mem_uFrame (show uψ ∈ uFrame by rw [uFrame_eq]; simp)

theorem uθ_mem_uPsi : uθ ∈ uPsi := mem_uPsi_of_mem_uFrame (show uθ ∈ uFrame by rw [uFrame_eq]; simp)

theorem pinnedX_mem_parabolicRadical {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ uPsi) (t : K) :
    pinnedX .E7 K β t ∈ parabolicRadical .E7 K uNodes :=
  pinnedX_mem_rootSpan (mem_parabolicRadicalRoots_of_mem_uPsi hβ) t

theorem uComplElt_mem_radicalU (c : K × K) : uComplElt K c ∈ radicalU K :=
  ⟨⟨pinnedX .E7 K uφ c.1 * pinnedX .E7 K uθ c.2,
      mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)⟩,
    mem_subgroupOf.2 (mul_mem (pinnedX_mem_parabolicRadical uφ_mem_uPsi _)
      (pinnedX_mem_parabolicRadical uθ_mem_uPsi _)), rfl⟩

theorem exists_mem_uCoreRadical_mul_eq [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    {r : adjointGroup .E7 K} (hr : r ∈ radicalU K) :
    ∃ q ∈ uCoreRadical K, ∃ c : K × K, r = q * uComplElt K c := by
  obtain ⟨r₀, hr₀, rfl⟩ := hr
  have hle : parabolicRadical .E7 K uNodes ≤ rootSpan .E7 K {β | β ∈ uPsi} :=
    iSup₂_le fun α hα => le_iSup₂_of_le (f := fun β (_ : β ∈ {β | β ∈ uPsi}) =>
      rootSubgroup .E7 K β) α (mem_uPsi_of_mem_parabolicRadicalRoots hα) le_rfl
  obtain ⟨c, hc⟩ := exists_rootProd_eq_of_mem_rootSpan uPsi_nodup uPsi_comm
    (hle (mem_subgroupOf.1 hr₀))
  have hcomm : ∀ a ∈ parabolicRadical .E7 K uNodes, ∀ b ∈ parabolicRadical .E7 K uNodes,
      a * b = b * a := fun a ha b hb => parabolicRadical_comm ha hb
  have hmemQ : ∀ (l : List (Fin Tag.E7.rank → ℤ)), (∀ β ∈ l, β ∈ uPsi) →
      rootProd .E7 K l c ∈ parabolicRadical .E7 K uNodes := fun l hl =>
    list_prod_mem fun x hx => by
      obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
      exact pinnedX_mem_parabolicRadical (hl β hβ) _
  set X := pinnedX .E7 K uφ (c uφ) with hX
  set Y := pinnedX .E7 K uψ (c uψ) with hY
  set Z := pinnedX .E7 K uθ (c uθ) with hZ
  set L := rootProd .E7 K uLow c with hL
  set H := rootProd .E7 K uHigh c with hH
  set t₀ := pinnedX .E7 K uφ (c uφ - c uψ) * Z with ht₀
  set q₀ := Y * pinnedX .E7 K uφ (c uψ) * L * H with hq₀
  have hframe : rootProd .E7 K uFrame c = X * Y * Z := by
    rw [uFrame_eq, E6Pilot.rootProd_cons, E6Pilot.rootProd_cons, E6Pilot.rootProd_cons,
      E6Pilot.rootProd_nil, mul_one, mul_assoc]
  have hsplit : rootProd .E7 K uPsi c = X * Y * Z * L * H := by
    rw [uPsi, E6Pilot.rootProd_append, E6Pilot.rootProd_append, hframe]
  have hXs : X = pinnedX .E7 K uφ (c uψ) * pinnedX .E7 K uφ (c uφ - c uψ) := by
    rw [hX, ← pinnedX_add]
    congr 1
    ring
  have mφ : ∀ t : K, pinnedX .E7 K uφ t ∈ parabolicRadical .E7 K uNodes :=
    pinnedX_mem_parabolicRadical uφ_mem_uPsi
  have mY : Y ∈ parabolicRadical .E7 K uNodes := pinnedX_mem_parabolicRadical uψ_mem_uPsi _
  have mZ : Z ∈ parabolicRadical .E7 K uNodes := pinnedX_mem_parabolicRadical uθ_mem_uPsi _
  have mL : L ∈ parabolicRadical .E7 K uNodes := hmemQ uLow fun β hβ => mem_uPsi_of_mem_uLow hβ
  have mH : H ∈ parabolicRadical .E7 K uNodes := hmemQ uHigh fun β hβ => mem_uPsi_of_mem_uHigh hβ
  have key : rootProd .E7 K uPsi c = q₀ * t₀ := by
    rw [hsplit, hXs, hq₀, ht₀]
    set A := pinnedX .E7 K uφ (c uψ)
    set B := pinnedX .E7 K uφ (c uφ - c uψ)
    have mB : B ∈ parabolicRadical .E7 K uNodes := mφ _
    calc A * B * Y * Z * L * H = A * Y * B * Z * L * H := by
          rw [mul_assoc A B Y, hcomm B mB Y mY, ← mul_assoc]
      _ = Y * A * (B * Z) * L * H := by
          rw [hcomm A (mφ _) Y mY]; group
      _ = Y * A * L * H * (B * Z) := by
          have h1 := hcomm (B * Z) (mul_mem mB mZ) (L * H) (mul_mem mL mH)
          calc Y * A * (B * Z) * L * H = Y * A * ((B * Z) * (L * H)) := by group
            _ = Y * A * ((L * H) * (B * Z)) := by rw [h1]
            _ = Y * A * L * H * (B * Z) := by group
  have hq₀Q : q₀ ∈ uCoreRadicalAS K := by
    refine mul_mem (mul_mem (pinnedX_psi_mul_phi_mem_uCoreRadicalAS hq _)
      (list_prod_mem fun x hx => ?_)) (list_prod_mem fun x hx => ?_)
    · obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
      exact pinnedX_mem_uCoreRadicalAS hq (List.mem_append_left _ hβ) _
    · obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
      exact pinnedX_mem_uCoreRadicalAS hq (List.mem_append_right _ hβ) _
  have hq₀C : q₀ ∈ adjointGroup .E7 K :=
    (parabolicRadical_le_posUnipotent _).trans posUnipotent_le_adjointGroup
      (mul_mem (mul_mem (mul_mem mY (mφ _)) mL) mH)
  have hQ : e7RepConj K 3 * (⟨q₀, hq₀C⟩ : adjointGroup .E7 K) * (e7RepConj K 3)⁻¹ ∈
      uCoreRadical K := conj_mem_uCoreRadical_of hq₀Q
  refine ⟨_, hQ, (c uφ - c uψ, c uθ), ?_⟩
  have hr₀' : r₀ = ⟨q₀, hq₀C⟩ * ⟨t₀, mul_mem (pinnedX_mem_adjointGroup _ _)
      (pinnedX_mem_adjointGroup _ _)⟩ := Subtype.ext (by rw [Subgroup.coe_mul, ← key, hc])
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, uComplElt, hr₀']
  group
  rfl

theorem commutator_radicalU_zpowers_eq_of_commute [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    {a : adjointGroup .E7 K} (ha : a ∈ leviU K) (ha2 : a ^ 2 = 1)
    (hcomm : ∀ c : K × K, uComplElt K c * a = a * uComplElt K c) :
    ⁅radicalU K, zpowers a⁆ = ⁅uCoreRadical K, zpowers a⁆ := by
  refine le_antisymm (fun x hx => ?_) (commutator_mono inf_le_right le_rfl)
  have hR : ∀ x ∈ radicalU K, ∀ y ∈ radicalU K, x * y = y * x := fun x hx y hy =>
    radicalU_comm hx hy
  have haR := leviU_le_normalizer_radicalU ha
  obtain ⟨r, hr, rfl⟩ := (mem_commutator_zpowers_iff hR haR ha2).1 hx
  obtain ⟨q, hqQ, c, rfl⟩ := exists_mem_uCoreRadical_mul_eq hq hr
  have hmul := (commMap (radicalU K) hR a haR).map_mul ⟨q, (mem_inf.1 hqQ).2⟩
    ⟨uComplElt K c, uComplElt_mem_radicalU c⟩
  simp only [commMap_apply, MulMemClass.mk_mul_mk] at hmul
  have h1 : ⁅uComplElt K c, a⁆ = 1 := by rw [commutatorElement_eq_one_iff_mul_comm, hcomm c]
  rw [hmul, h1, mul_one]
  exact commutator_mem_commutator hqQ (mem_zpowers a)

theorem uComplElt_mul_comm_of_mem_rootSubgroup (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    {a : adjointGroup .E7 K} (ha : (a : ModGL .E7 K) ∈ rootSubgroup .E7 K (ε • highRoot .E7))
    (c : K × K) : uComplElt K c * a = a * uComplElt K c := by
  rw [← map_conj_e7RepConj_rootSubgroup_alpha4 ε hε] at ha
  obtain ⟨y, hy, hya⟩ := ha
  obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hy
  have hperp := uDiag_check.2.2.2.2.2.2.2.2
  have hα : IsRoot .E7 (ε • Pi.single (3 : Fin Tag.E7.rank) 1) ∧
      uLevel (ε • Pi.single (3 : Fin Tag.E7.rank) 1) = 0 ∧
      ∀ f ∈ uFrame, ¬IsRoot .E7 (ε • Pi.single (3 : Fin Tag.E7.rank) 1 + f) := by
    rcases hε with rfl | rfl
    · rw [one_smul]
      exact ⟨isRoot_single .E7 3, (uLevel_single_check 3 (by decide)).1,
        fun f hf => not_isRoot_of_isRootB_false (hperp f hf).1⟩
    · rw [neg_one_smul]
      exact ⟨isRoot_neg_single .E7 3, (uLevel_single_check 3 (by decide)).2,
        fun f hf => not_isRoot_of_isRootB_false (hperp f hf).2⟩
  obtain ⟨hαr, hα0, hαf⟩ := hα
  have hcf : ∀ f ∈ uFrame, ∀ s : K, Commute (pinnedX .E7 K f s)
      (pinnedX .E7 K (ε • Pi.single 3 1) t) := fun f hf s =>
    CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv (isRoot_of_mem_uPsi (mem_uPsi_of_mem_uFrame hf))
      hαr (fun h => (ne_of_uLevel_zero hα0 (mem_uPsi_of_mem_uFrame hf)).2
        (by rw [h, neg_neg]))
      (by rw [add_comm]; exact hαf f hf) s t
  have hT : Commute (pinnedX .E7 K uφ c.1 * pinnedX .E7 K uθ c.2)
      (pinnedX .E7 K (ε • Pi.single 3 1) t) :=
    (hcf uφ (by rw [uFrame_eq]; simp) c.1).mul_left (hcf uθ (by rw [uFrame_eq]; simp) c.2)
  apply Subtype.ext
  simp only [uComplElt, Subgroup.coe_mul, Subgroup.coe_inv, ← hya, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  calc (e7RepConj K 3 : ModGL .E7 K) * (pinnedX .E7 K uφ c.1 * pinnedX .E7 K uθ c.2) *
        (e7RepConj K 3 : ModGL .E7 K)⁻¹ * ((e7RepConj K 3 : ModGL .E7 K) *
          pinnedX .E7 K (ε • Pi.single 3 1) t * (e7RepConj K 3 : ModGL .E7 K)⁻¹) =
      (e7RepConj K 3 : ModGL .E7 K) * ((pinnedX .E7 K uφ c.1 * pinnedX .E7 K uθ c.2) *
        pinnedX .E7 K (ε • Pi.single 3 1) t) * (e7RepConj K 3 : ModGL .E7 K)⁻¹ := by group
    _ = (e7RepConj K 3 : ModGL .E7 K) * (pinnedX .E7 K (ε • Pi.single 3 1) t *
        (pinnedX .E7 K uφ c.1 * pinnedX .E7 K uθ c.2)) * (e7RepConj K 3 : ModGL .E7 K)⁻¹ := by
        rw [hT.eq]
    _ = _ := by group

theorem commutator_radicalU_zpowers_eq_uCoreRadical [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) {a : adjointGroup .E7 K}
    (ha : a ∈ (rootSubgroup .E7 K (ε • highRoot .E7)).subgroupOf (adjointGroup .E7 K)) :
    ⁅radicalU K, zpowers a⁆ = ⁅uCoreRadical K, zpowers a⁆ := by
  obtain ⟨d, hd, hX⟩ := rootSubgroup_smul_highRoot_mem_leviURootSubgroups (K := K) ε hε
  have haN : a ∈ leviU K := by
    rw [hX] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hx
    exact mul_mem (mul_mem hd ⟨y, mem_subgroupOf.2 ((rootSubgroup_uTopRoot_le_parabolicLevi
      (mem_subgroupOf.1 hy))), rfl⟩) (inv_mem hd)
  have ha2 : a ^ 2 = 1 := by
    obtain ⟨t, ht⟩ := mem_rootSubgroup.1 (mem_subgroupOf.1 ha)
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← ht, pow_two, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
    rfl
  exact commutator_radicalU_zpowers_eq_of_commute hq haN ha2
    (uComplElt_mul_comm_of_mem_rootSubgroup ε hε (mem_subgroupOf.1 ha))

theorem card_commutator_radicalU_leviURootSubgroup [CharP K 2] {X : Subgroup (adjointGroup .E7 K)}
    (hX : X ∈ leviURootSubgroups K) :
    Nat.card (⁅radicalU K, X⁆ : Subgroup (adjointGroup .E7 K)) = Nat.card (uTopGroup K) := by
  obtain ⟨c, hc, rfl⟩ := hX
  rw [commutator_radicalU_leviURootSubgroup hc, card_map_of_injective (MulAut.conj _).injective]
  exact Nat.card_congr (subgroupOfEquivOfLe uTopGroup_le_adjointGroup).toEquiv

end Large

end CFSG.SeitzReduction.E7Pilot
