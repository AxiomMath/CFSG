module

public import CFSG.GH74.GLS.C3.Layer2.L5C12
public import CFSG.GH74.GLS.C3.Layer2.L5C13
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Stage1.Thm6
  CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

section Iota

variable {h : IsAConfig 5 x K T Q S a} (c : Coord5 h)

@[expose] noncomputable def Coord5.iotaT : ↥T5 →* G :=
  (centralizer ({x} : Set G)).subtype.comp
    (c.ι.symm.toMonoidHom.comp (Subgroup.inclusion T5_le_Fgrp))

theorem Coord5.iotaT_mem_C (t : ↥T5) : c.iotaT t ∈ centralizer ({x} : Set G) :=
  (c.ι.symm ⟨(t : Amb 5), T5_le_Fgrp t.2⟩).2

theorem Coord5.rco_iotaT (t : ↥T5) : c.rco (c.iotaT t) = (t : Amb 5) := by
  rw [Coord5.rco_of_mem c (c.iotaT_mem_C t)]
  have : (⟨c.iotaT t, c.iotaT_mem_C t⟩ : ↥(centralizer ({x} : Set G))) =
      c.ι.symm ⟨(t : Amb 5), T5_le_Fgrp t.2⟩ := Subtype.ext rfl
  rw [this]
  show ((c.ι (c.ι.symm ⟨(t : Amb 5), T5_le_Fgrp t.2⟩) : Fgrp 5) : Amb 5) = _
  rw [MulEquiv.apply_symm_apply]

theorem Coord5.iotaT_mem_T (t : ↥T5) : c.iotaT t ∈ T := by
  refine (c.hιT ⟨c.iotaT t, c.iotaT_mem_C t⟩).2 ?_
  have h2 := c.rco_iotaT t
  rw [Coord5.rco_of_mem c (c.iotaT_mem_C t)] at h2
  have h3 : ((c.ι ⟨c.iotaT t, c.iotaT_mem_C t⟩ : Fgrp 5) : Amb 5) = (t : Amb 5) := h2
  rw [h3]
  exact t.2

theorem Coord5.iotaT_injective : Function.Injective c.iotaT := by
  intro s t hst
  apply Subtype.ext
  have := congrArg c.rco hst
  rwa [c.rco_iotaT, c.rco_iotaT] at this

theorem Coord5.iotaT_elT
    (i : Fin 16) : c.iotaT (elT i) = c.liftEl i := by
  apply Coord5.rco_inj c (c.iotaT_mem_C _) (c.liftEl_mem_C i)
  rw [c.rco_iotaT, c.rco_liftEl]
  rfl

theorem Coord5.iotaT_x0 : c.iotaT x0T5 = x := by
  have hxC : x ∈ centralizer ({x} : Set G) := h.T_le_C h.x_mem_T
  have hx : c.rco x = f1 := by
    rw [Coord5.rco_of_mem c hxC]
    exact Coord5.x_co (c := c)
  apply Coord5.rco_inj c (c.iotaT_mem_C _) hxC
  rw [c.rco_iotaT, hx]
  rfl

theorem Coord5.iotaT_conj {g : Amb 5} (hg : g ∈ Fgrp 5) {t s : ↥T5}
    (hts : g * (t : Amb 5) * g⁻¹ = (s : Amb 5)) : IsConj (c.iotaT t) (c.iotaT s) := by
  set g' : ↥(centralizer ({x} : Set G)) := c.ι.symm ⟨g, hg⟩ with hg'
  rw [isConj_iff]
  refine ⟨(g' : G), ?_⟩
  have hg'C : (g' : G) ∈ centralizer ({x} : Set G) := g'.2
  have hco : c.rco (g' : G) = g := by
    rw [Coord5.rco_of_mem c hg'C]
    show ((c.ι (c.ι.symm ⟨g, hg⟩) : Fgrp 5) : Amb 5) = g
    rw [MulEquiv.apply_symm_apply]
  apply Coord5.rco_inj c (mul_mem (mul_mem hg'C (c.iotaT_mem_C t)) (inv_mem hg'C))
    (c.iotaT_mem_C s)
  rw [Coord5.rco_mul c (mul_mem hg'C (c.iotaT_mem_C t)) (inv_mem hg'C),
    Coord5.rco_mul c hg'C (c.iotaT_mem_C t), Coord5.rco_inv c hg'C, hco, c.rco_iotaT,
    c.rco_iotaT]
  exact hts

end Iota

section PGroups

theorem exists_normalizer_gt {S' P : Subgroup G} (hS' : IsPGroup 2 ↥S') (hP : P ≤ S')
    (hne : P ≠ S') : ∃ b ∈ S', b ∈ normalizer (P : Set G) ∧ b ∉ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥S' := hS'.isNilpotent
  have hlt : P.subgroupOf S' < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    apply le_antisymm hP
    intro y hy
    have : (⟨y, hy⟩ : ↥S') ∈ P.subgroupOf S' := by rw [htop]; exact Subgroup.mem_top _
    exact this
  have hnc : NormalizerCondition ↥S' := Group.normalizerCondition_of_isNilpotent
  have hlt2 : P.subgroupOf S' < normalizer ((P.subgroupOf S' : Subgroup ↥S') : Set ↥S') :=
    hnc _ hlt
  obtain ⟨b, hbN, hbP⟩ := (IsConcreteLE.lt_iff_le_and_exists.1 hlt2).2
  refine ⟨(b : G), b.2, ?_, fun hb => hbP (Subgroup.mem_subgroupOf.2 hb)⟩
  have hbsub : b ∈ (normalizer (P : Set G)).subgroupOf S' := by
    rw [Subgroup.subgroupOf_normalizer_eq hP]
    exact hbN
  exact Subgroup.mem_subgroupOf.1 hbsub

theorem exists_S2 {S' S₁ : Subgroup G} (hS' : IsPGroup 2 ↥S') (h1 : S₁ ≤ S') (hne : S₁ ≠ S')
    (hcard : Nat.card S₁ = 128) :
    ∃ S₂ : Subgroup G, S₁ ≤ S₂ ∧ S₂ ≤ S' ∧ Nat.card S₂ = 256 := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hS'
  have hlt : Nat.card S₁ < Nat.card S' := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le h1) fun hh => hne ?_
    exact Subgroup.eq_of_le_of_card_ge h1 (le_of_eq hh.symm)
  rw [hcard, hm] at hlt
  have hm8 : 8 ≤ m := by
    by_contra hm7
    have : 2 ^ m ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨K, hK, hS₁K, hKS'⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (n := 8) (H := S₁) (L := S') (by rw [hcard]; norm_num)
    (by rw [hm]; exact pow_dvd_pow 2 hm8) h1
  exact ⟨K, hS₁K, hKS', by rw [hK]; norm_num⟩

end PGroups

section S1G

variable {h : IsAConfig 5 x K T Q S a}

structure Coord5.Red
    (c : Coord5 h) : Prop where
  fam : ∀ V, V ∈ fam0G ↔ ∃ W ∈ FamQ (c.lift Rm) Q, c.planeOf W = V
  pres : ∀ n : ↥c.N, PplG.image (c.rhoG n) = PplG
  nbar : ∀ A ∈ n24L, ∃ n : ↥c.N, c.rhoG n = A

theorem exists_red
    (hF : C1Facts) (c : Coord5 h) (hG4 : pRank 2 G ≤ 4)
    (hP : ∀ V ∈ FamQ (c.lift Rm) Q, V ⊓ (T ⊓ K) = ⊥) (hncard : (FamQ (c.lift Rm) Q).ncard = 4) :
    ∃ c' : Coord5 h, c'.Red := by
  obtain ⟨c', -, F, -, hF0, hmem, hpres, hnbar⟩ := exists_nbar0 hF c hG4 hP hncard
  subst hF0
  exact ⟨c', ⟨hmem, hpres, hnbar⟩⟩

variable {c : Coord5 h}

theorem Coord5.rho_stable
    (hRed : c.Red) (n : ↥c.N) :
    IsLinG (c.rhoG n) ∧ ∀ V ∈ fam0G, V.image (c.rhoG n) ∈ fam0G :=
  ⟨fun i j => Coord5.rhoG_xor c n i j, fun V hV => Coord5.fam_stable hRed.fam n.2 V hV⟩

theorem Coord5.R_le_S1
    {S₁ : Subgroup G} (hS : c.S1Data S₁) : c.lift Rm ≤ S₁ :=
  (Coord5.Rg_le_T (c := c)).trans hS.hT

theorem Coord5.mem_S1_of_rho
    {S₁ : Subgroup G} (hS : c.S1Data S₁) {u : G} (hu : u ∈ c.N)
    (hρ : c.rhoG ⟨u, hu⟩ ∈ d8L) : u ∈ S₁ := by
  obtain ⟨s, hs, hsρ⟩ := hS.surj _ hρ
  have hsN : s ∈ c.N := hS.hN hs
  rw [Coord5.rhoT_of_mem hsN] at hsρ
  have hmem : s⁻¹ * u ∈ c.N := mul_mem (inv_mem hsN) hu
  have hk : c.rhoG ⟨s⁻¹ * u, hmem⟩ = 1 := by
    have : (⟨s⁻¹ * u, hmem⟩ : ↥c.N) = (⟨s, hsN⟩ : ↥c.N)⁻¹ * ⟨u, hu⟩ := rfl
    rw [this, map_mul, map_inv, hsρ, inv_mul_cancel]
  have hR : s⁻¹ * u ∈ c.lift Rm := by
    have := SetLike.ext_iff.1 (Coord5.rhoG_ker (c := c)) ⟨s⁻¹ * u, hmem⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf] at this
    exact this.1 hk
  have h3 : s * (s⁻¹ * u) ∈ S₁ := S₁.mul_mem hs (Coord5.R_le_S1 hS hR)
  simpa using h3

theorem Coord5.S1_sylow
    (hF : C1Facts2) (hRed : c.Red) {S₁ : Subgroup G} (hS : c.S1Data S₁) :
    IsSylow2In S₁ c.N := by
  have hp : IsPGroup 2 ↥S₁ := IsPGroup.of_card (n := 7) (by rw [hS.card]; norm_num)
  refine ⟨hS.hN, hp, ?_⟩
  have hdvd : Nat.card c.rhoG.range ∣ 72 := by
    apply hF.g72_dvd
    rintro m ⟨n, rfl⟩
    exact Coord5.rho_stable hRed n
  have h16 : Nat.card ((c.lift Rm).subgroupOf c.N) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Coord5.R_le_N c)).toEquiv]
    exact Coord5.card_lift_Rm (c := c)
  have hker : 16 * Nat.card c.rhoG.range = Nat.card ↥c.N := by
    have h0 := Subgroup.card_ker_mul_card_range c.rhoG
    rw [Coord5.rhoG_ker, h16] at h0
    exact h0
  have h128 : Nat.card ((S₁.subgroupOf c.N)) = 128 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.hN).toEquiv]
    exact hS.card
  have e1 := Subgroup.card_mul_index (S₁.subgroupOf c.N)
  rw [h128] at e1
  rintro ⟨k, hk⟩
  have hk' : (S₁.subgroupOf c.N).index = 2 * k := hk
  rw [hk'] at e1
  obtain ⟨m, hm⟩ := hdvd
  have hr : Nat.card c.rhoG.range = 16 * k := by omega
  rw [hr] at hm
  have h72 : 72 = 16 * (k * m) := by rw [hm]; ring
  generalize k * m = z at h72
  omega

end S1G

end CFSG.GH74.GLS.C3.Layer2.L5
