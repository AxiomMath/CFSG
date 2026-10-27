module

public import CFSG.ClassicalInvolution.Q3.Sec13PerpA
public import CFSG.ClassicalInvolution.Q3.TL4AECover
import CFSG.ClassicalInvolution.Q3.TL3T35
import CFSG.ClassicalInvolution.Q3.TL3T38

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

private theorem pc_mem_RSet (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) {R : Subgroup G} (hR : R ∈ Ω) :
    R ∈ RSet Ω :=
  mem_RSet_iff.mpr ⟨R, hR, le_rfl, h2 R hR, fun R' hR'R _ hle => le_antisymm hR'R hle⟩

private theorem pc_commutes_of_two_group (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J)
    {T : Subgroup G} (hT : IsPGroup 2 ↥T) {R R' : Subgroup G} (hR : R ∈ Ω) (hR' : R' ∈ Ω)
    (hRT : R ≤ T) (hR'T : R' ≤ T) (hne : R ≠ R') : Commutes R R' := by
  obtain ⟨S, hS⟩ := hT.exists_le_sylow
  exact Q3CP.l67Gen G Ω hΩ S R (pc_mem_RSet h2 hR) R' (pc_mem_RSet h2 hR')
    (hRT.trans hS) (hR'T.trans hS) hne

section AELayer

variable {P : Set (Subgroup G)} (I : AEIdent P 5)

private theorem pc_not_disjoint {α β : Finset (Fin 5)} (hα : α.card = 4) (hβ : β.card = 4) :
    ¬ Disjoint α β := by
  intro hd
  have h1 := Finset.card_union_of_disjoint hd
  have h2 := Finset.card_le_univ (α ∪ β)
  simp only [Fintype.card_fin] at h2
  omega

private theorem pc_same_set {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P)
    {α β : Finset (Fin 5)} {hα : α.card = 4} {hβ : β.card = 4} {b c : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b)
    (hlab' : (L'.subgroupOf (pSpan P)).map I.φ = AE.memBar β hβ c)
    (hc : Commutes L L') : α = β := by
  by_contra hne
  apply pc_not_disjoint hα hβ
  refine AE.disjoint_of_zBar_comm (h := hα) (h' := hβ) hne (c := c) fun y hy => ?_
  have hz : AE.zBar α hα ∈ (L.subgroupOf (pSpan P)).map I.φ := by
    rw [hlab]
    exact AE.zBar_mem_memBar α hα b
  have hy' : y ∈ (L'.subgroupOf (pSpan P)).map I.φ := by
    rw [hlab']
    exact hy
  obtain ⟨l, hl, hlz⟩ := I.exists_of_mem_map hL hz
  obtain ⟨l', hl', hly⟩ := I.exists_of_mem_map hL' hy'
  rw [← hlz, ← hly, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc l hl l' hl')

private theorem pc_label_inj (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J)
    (hPΩ : ∀ L ∈ P, L ∈ Ω) (hk : IsPGroup 2 ↥I.φ.ker) :
    ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L' := by
  intro L hL L' hL' hEq
  by_contra hne
  obtain ⟨α, hα, b, hlab⟩ := I.label L hL
  have hS2 : IsPGroup 2 ↥(AE.memBar α hα b) :=
    IsPGroup.of_card (n := 3) (by rw [AE.natCard_memBar (by norm_num) α hα b]; norm_num)
  have hT : IsPGroup 2 ↥(((AE.memBar α hα b).comap I.φ).map (pSpan P).subtype) :=
    ((hS2.comap_of_ker_isPGroup I.φ hk).map _)
  have hLT : L ≤ ((AE.memBar α hα b).comap I.φ).map (pSpan P).subtype := by
    intro l hl
    refine ⟨⟨l, le_pSpan hL hl⟩, ?_, rfl⟩
    have hm := I.mem_map hL hl
    rw [hlab] at hm
    exact hm
  have hL'T : L' ≤ ((AE.memBar α hα b).comap I.φ).map (pSpan P).subtype := by
    intro l hl
    refine ⟨⟨l, le_pSpan hL' hl⟩, ?_, rfl⟩
    have hm := I.mem_map hL' hl
    rw [← hEq, hlab] at hm
    exact hm
  have hc := pc_commutes_of_two_group hΩ h2 hT (hPΩ L hL) (hPΩ L' hL') hLT hL'T hne
  obtain ⟨x, hx, x', hx', hxx⟩ := AE.exists_not_comm_memBar (by norm_num) α hα b
  have hx1 : x ∈ (L.subgroupOf (pSpan P)).map I.φ := by rw [hlab]; exact hx
  have hx2 : x' ∈ (L'.subgroupOf (pSpan P)).map I.φ := by rw [← hEq, hlab]; exact hx'
  obtain ⟨l, hl, hlx⟩ := I.exists_of_mem_map hL hx1
  obtain ⟨l', hl', hl'x⟩ := I.exists_of_mem_map hL' hx2
  apply hxx
  rw [← hlx, ← hl'x, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc l hl l' hl')

private theorem pc_memBar_ne (α : Finset (Fin 5)) (hα : α.card = 4) (b : Bool) :
    AE.memBar α hα b ≠ AE.memBar α hα (!b) := by
  cases b
  · exact fun h => AE.memBar_true_ne_false (by norm_num) α hα h.symm
  · exact AE.memBar_true_ne_false (by norm_num) α hα

private theorem pc_twin_comm (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J)
    (hPΩ : ∀ L ∈ P, L ∈ Ω) (hk : IsPGroup 2 ↥I.φ.ker)
    {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P) {α : Finset (Fin 5)} {hα : α.card = 4}
    {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b)
    (hlab' : (L'.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα (!b)) : Commutes L L' := by
  set S' : Set (Subgroup (AE.AEQ 5)) := {AE.memBar α hα b, AE.memBar α hα (!b)} with hS'
  have hS'2 : ∀ X ∈ S', IsPGroup 2 ↥X := by
    intro X hX
    rcases hX with rfl | rfl <;>
      exact IsPGroup.of_card (n := 3) (by rw [AE.natCard_memBar (by norm_num) α hα _]; norm_num)
  have hS'c : ∀ X ∈ S', ∀ Y ∈ S', X ≠ Y → Commutes X Y := by
    intro X hX Y hY hXY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact absurd rfl hXY
    · exact TC.Thin.memBar_twin_comm α hα b
    · have := TC.Thin.memBar_twin_comm α hα (!b)
      simp only [Bool.not_not] at this
      exact this
    · exact absurd rfl hXY
  have hp : IsPGroup 2 ↥(pSpan S') := isPGroup_pSpan_of_comm hS'2 hS'c
  have hT : IsPGroup 2 ↥(((pSpan S').comap I.φ).map (pSpan P).subtype) :=
    ((hp.comap_of_ker_isPGroup I.φ hk).map _)
  have hX1 : AE.memBar α hα b ≤ pSpan S' :=
    le_iSup₂ (f := fun (X : Subgroup (AE.AEQ 5)) (_ : X ∈ S') => X) (AE.memBar α hα b)
      (Set.mem_insert _ _)
  have hX2 : AE.memBar α hα (!b) ≤ pSpan S' :=
    le_iSup₂ (f := fun (X : Subgroup (AE.AEQ 5)) (_ : X ∈ S') => X) (AE.memBar α hα (!b))
      (Set.mem_insert_of_mem _ rfl)
  have hLT : L ≤ ((pSpan S').comap I.φ).map (pSpan P).subtype := by
    intro l hl
    refine ⟨⟨l, le_pSpan hL hl⟩, ?_, rfl⟩
    have hm := I.mem_map hL hl
    rw [hlab] at hm
    exact hX1 hm
  have hL'T : L' ≤ ((pSpan S').comap I.φ).map (pSpan P).subtype := by
    intro l hl
    refine ⟨⟨l, le_pSpan hL' hl⟩, ?_, rfl⟩
    have hm := I.mem_map hL' hl
    rw [hlab'] at hm
    exact hX2 hm
  have hne : L ≠ L' := by
    rintro rfl
    exact pc_memBar_ne α hα b (hlab.symm.trans hlab')
  exact pc_commutes_of_two_group hΩ h2 hT (hPΩ L hL) (hPΩ L' hL') hLT hL'T hne

private theorem pc_bit (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P) (hne : L ≠ L')
    {α : Finset (Fin 5)} {hα : α.card = 4} {b c : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b)
    (hlab' : (L'.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα c) : c = !b := by
  cases b <;> cases c
  · exact absurd (hinj L hL L' hL' (hlab.trans hlab'.symm)) hne
  · rfl
  · rfl
  · exact absurd (hinj L hL L' hL' (hlab.trans hlab'.symm)) hne

private theorem pc_twin_labels (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P) (hne : L ≠ L') (hc : Commutes L L')
    {α : Finset (Fin 5)} {hα : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b) :
    (L'.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα (!b) := by
  obtain ⟨β, hβ, c, hlab'⟩ := I.label L' hL'
  have hαβ : α = β := pc_same_set I hL hL' hlab hlab' hc
  subst hαβ
  have hcb := pc_bit I hinj hL hL' hne hlab hlab'
  rw [hcb] at hlab'
  exact hlab'

private theorem pc_no_three (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    {L₁ L₂ L₃ : Subgroup G} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P) (h₃ : L₃ ∈ P)
    (n₁₂ : L₁ ≠ L₂) (n₁₃ : L₁ ≠ L₃) (n₂₃ : L₂ ≠ L₃)
    (c₁₂ : Commutes L₁ L₂) (c₁₃ : Commutes L₁ L₃) : False := by
  obtain ⟨α, hα, b, hlab⟩ := I.label L₁ h₁
  have e₂ := pc_twin_labels I hinj h₁ h₂ n₁₂ c₁₂ hlab
  have e₃ := pc_twin_labels I hinj h₁ h₃ n₁₃ c₁₃ hlab
  exact n₂₃ (hinj L₂ h₂ L₃ h₃ (e₂.trans e₃.symm))

private theorem pc_ncard_le_two (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    {S : Set (Subgroup G)} (hS : S ⊆ P) (hc : ∀ L ∈ S, ∀ L' ∈ S, L ≠ L' → Commutes L L') :
    S.ncard ≤ 2 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a, b, c, ha, hb, hc', hab, hac, hbc⟩ := (Set.two_lt_ncard_iff (Set.toFinite S)).mp hlt
  exact pc_no_three I hinj (hS ha) (hS hb) (hS hc') hab hac hbc (hc a ha b hb hab)
    (hc a ha c hc' hac)

end AELayer

private theorem pc_commutes_conj (n : G) {A B : Subgroup G} (hAB : Commutes A B) :
    Commutes (conjSub n A) (conjSub n B) := by
  intro x hx y hy
  have hx' : x = n * (n⁻¹ * x * n) * n⁻¹ := by group
  have hy' : y = n * (n⁻¹ * y * n) * n⁻¹ := by group
  have ha : n⁻¹ * x * n ∈ A := mem_conjSub_iff.mp hx
  have hb : n⁻¹ * y * n ∈ B := mem_conjSub_iff.mp hy
  have hc := hAB _ ha _ hb
  rw [hx', hy']
  calc n * (n⁻¹ * x * n) * n⁻¹ * (n * (n⁻¹ * y * n) * n⁻¹)
      = n * ((n⁻¹ * x * n) * (n⁻¹ * y * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * y * n) * (n⁻¹ * x * n)) * n⁻¹ := by rw [hc]
    _ = n * (n⁻¹ * y * n) * n⁻¹ * (n * (n⁻¹ * x * n) * n⁻¹) := by group

private theorem pc_normalizer_conj (n : G) {A B : Subgroup G}
    (hAB : B ≤ Subgroup.normalizer (A : Set G)) :
    conjSub n B ≤ Subgroup.normalizer ((conjSub n A : Subgroup G) : Set G) := by
  intro x hx
  have hb : n⁻¹ * x * n ∈ B := mem_conjSub_iff.mp hx
  have hbN : n⁻¹ * x * n ∈ Subgroup.normalizer (A : Set G) := hAB hb
  rw [Subgroup.mem_normalizer_iff] at hbN ⊢
  intro m
  rw [mem_conjSub_iff, mem_conjSub_iff]
  have key : n⁻¹ * (x * m * x⁻¹) * n = (n⁻¹ * x * n) * (n⁻¹ * m * n) * (n⁻¹ * x * n)⁻¹ := by
    group
  rw [key]
  exact hbN (n⁻¹ * m * n)

private theorem pc_conj_fix {M : Subgroup G} {x : G} (hc : ∀ a ∈ M, a * x = x * a) :
    conjSub x M = M := by
  ext m
  rw [mem_conjSub_iff]
  constructor
  · intro hm
    have hcm := hc _ hm
    have h3 : x⁻¹ * m * x = m := by
      calc x⁻¹ * m * x = (x⁻¹ * m * x * x) * x⁻¹ := by group
        _ = (x * (x⁻¹ * m * x)) * x⁻¹ := by rw [hcm]
        _ = m := by group
    rw [h3] at hm
    exact hm
  · intro hm
    have hmx := hc m hm
    have h3 : x⁻¹ * m * x = m := by
      calc x⁻¹ * m * x = x⁻¹ * (m * x) := by group
        _ = x⁻¹ * (x * m) := by rw [hmx]
        _ = m := by group
    rw [h3]
    exact hm

private theorem pc_omegaNbr_of_comm (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) (hΩ : HypOmegaGen Ω)
    {M X : Subgroup G} (hX : X ∈ Ω) (hne : X ≠ M) (hc : Commutes M X) :
    X ∈ omegaNbr Ω M := by
  refine (TC.mem_omegaNbr_iff hΩ h2).mpr ⟨hX, hne, ?_⟩
  intro x hx
  rw [mem_normalizer_iff_conjSub_eq]
  exact pc_conj_fix (fun a ha => hc a ha x hx)

private theorem pc_comm_of_omegaNbr (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) (hΩ : HypOmegaGen Ω)
    {M X : Subgroup G} (hM : M ∈ Ω) (hX : X ∈ omegaNbr Ω M) : Commutes M X :=
  TC.Thin.comm_of_mem_omegaNbr hΩ h2 hM hX

private theorem pc_omegaNbr_conj (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) (hΩ : HypOmegaGen Ω) (n : G)
    {M X : Subgroup G} (hX : X ∈ omegaNbr Ω M) : conjSub n X ∈ omegaNbr Ω (conjSub n M) := by
  obtain ⟨hXΩ, hne, hle⟩ := (TC.mem_omegaNbr_iff hΩ h2).mp hX
  refine (TC.mem_omegaNbr_iff hΩ h2).mpr ⟨hΩ.conjInvariant n X hXΩ, ?_, ?_⟩
  · exact fun heq => hne (conjSub_injective n heq)
  · exact pc_normalizer_conj n hle

private theorem pc_rtg_conj (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) (hΩ : HypOmegaGen Ω) (n : G)
    {M X : Subgroup G}
    (hX : Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N) M X) :
    Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N)
      (conjSub n M) (conjSub n X) := by
  induction hX with
  | refl => exact Relation.ReflTransGen.refl
  | @tail Y Z _ hstep ih =>
    obtain ⟨hZ, hd⟩ := hstep
    refine Relation.ReflTransGen.tail ih ⟨hΩ.conjInvariant n Z hZ, ?_⟩
    rcases hd with h | h
    · exact Or.inl (pc_omegaNbr_conj h2 hΩ n h)
    · exact Or.inr (pc_omegaNbr_conj h2 hΩ n h)

private theorem pc_dComp_conj (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) (hΩ : HypOmegaGen Ω) (n : G)
    {M X : Subgroup G} (hX : X ∈ dComp Ω M) : conjSub n X ∈ dComp Ω (conjSub n M) :=
  pc_rtg_conj h2 hΩ n hX

private theorem pc_mem_RSet_iff (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) {R : Subgroup G} :
    R ∈ RSet Ω ↔ R ∈ Ω := by
  constructor
  · intro hR
    obtain ⟨J, hJ, hRJ, _, hmax⟩ := mem_RSet_iff.mp hR
    have hJR : J = R := hmax J le_rfl (h2 J hJ) hRJ
    rw [← hJR]
    exact hJ
  · exact pc_mem_RSet h2

private theorem pc_mem_DSet_iff (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) {R W : Subgroup G} :
    R ∈ DSet Ω W ↔ R ∈ Ω ∧ R ≤ Subgroup.normalizer (W : Set G) := by
  constructor
  · rintro ⟨hR, hN⟩
    exact ⟨(pc_mem_RSet_iff h2).mp hR, hN⟩
  · rintro ⟨hR, hN⟩
    exact ⟨(pc_mem_RSet_iff h2).mpr hR, hN⟩

private theorem pc_dSet_conj (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) (hΩ : HypOmegaGen Ω) (n : G)
    {R W : Subgroup G} (hR : R ∈ DSet Ω W) : conjSub n R ∈ DSet Ω (conjSub n W) := by
  obtain ⟨hRΩ, hN⟩ := (pc_mem_DSet_iff h2).mp hR
  exact (pc_mem_DSet_iff h2).mpr ⟨hΩ.conjInvariant n R hRΩ, pc_normalizer_conj n hN⟩

private theorem pc_mem_kperp_iff (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) (hΩ : HypOmegaGen Ω)
    {M X : Subgroup G} (hM : M ∈ Ω) (hX : X ∈ Ω) :
    X ∈ KPerp Ω M ↔ X = M ∨ Commutes M X := by
  constructor
  · intro h
    rcases Set.mem_insert_iff.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (pc_comm_of_omegaNbr h2 hΩ hM h)
  · rintro (h | h)
    · rw [h]
      exact Set.mem_insert _ _
    · by_cases hXM : X = M
      · rw [hXM]
        exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (pc_omegaNbr_of_comm h2 hΩ hX hXM h)

private theorem pc_kperp_conj (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) (hΩ : HypOmegaGen Ω) (n : G)
    {M X : Subgroup G} (hX : X ∈ KPerp Ω M) : conjSub n X ∈ KPerp Ω (conjSub n M) := by
  rcases Set.mem_insert_iff.mp hX with h | h
  · rw [h]
    exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (pc_omegaNbr_conj h2 hΩ n h)

private theorem pc_kperp_dset_image (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J) (hΩ : HypOmegaGen Ω) (n : G)
    {M W : Subgroup G} (hM : M ∈ Ω) :
    conjSub n '' (KPerp Ω M ∩ DSet Ω W) = KPerp Ω (conjSub n M) ∩ DSet Ω (conjSub n W) := by
  ext Y
  constructor
  · rintro ⟨X, ⟨hXK, hXD⟩, rfl⟩
    exact ⟨pc_kperp_conj h2 hΩ n hXK, pc_dSet_conj h2 hΩ n hXD⟩
  · rintro ⟨hYK, hYD⟩
    have hMn : conjSub n M ∈ Ω := hΩ.conjInvariant n M hM
    have hK' := pc_kperp_conj h2 hΩ n⁻¹ hYK
    have hD' := pc_dSet_conj h2 hΩ n⁻¹ hYD
    rw [conjSub_inv_conjSub] at hK' hD'
    exact ⟨conjSub n⁻¹ Y, ⟨hK', hD'⟩, conjSub_conjSub_inv n Y⟩

private theorem pc_dComp_subset {M X : Subgroup G} (hM : M ∈ Ω) (hX : X ∈ dComp Ω M) :
    X ∈ Ω := by
  have hX' : Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N)
      M X := hX
  clear hX
  induction hX' with
  | refl => exact hM
  | @tail _ Z _ hstep _ => exact hstep.1

private theorem pc_dComp_of_omegaNbr {M X : Subgroup G} (hX : X ∈ omegaNbr Ω M) (hXΩ : X ∈ Ω) :
    X ∈ dComp Ω M :=
  (Relation.ReflTransGen.single ⟨hXΩ, Or.inl hX⟩ :
    Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N) M X)

private theorem pc_dComp_trans {M X Y : Subgroup G} (hX : X ∈ dComp Ω M)
    (hY : Y ∈ dComp Ω X) : Y ∈ dComp Ω M :=
  (Relation.ReflTransGen.trans hX hY :
    Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N) M Y)

private structure TCSetup (Ω : Set (Subgroup G)) (P₁ P₂ : Set (Subgroup G)) (K : Subgroup G)
    (g : G) : Type where
  h : EndHyp Ω
  hKΩ : K ∈ Ω
  hK : K ∈ P₁
  hdc : dComp Ω K = P₁ ∪ P₂
  hdisj : Disjoint P₁ P₂
  hcomm : ∀ L ∈ P₁, ∀ L' ∈ P₂, Commutes L L'
  hgP : ∀ L : Subgroup G, L ∈ P₂ ↔ conjSub g⁻¹ L ∈ P₁
  hinv : ∀ L ∈ P₁, ∀ x ∈ pSpan P₁, conjSub x L ∈ P₁
  htr : ∀ L ∈ P₁, ∀ L' ∈ P₁, ∃ x ∈ pSpan P₁, conjSub x L = L'
  hodd : classicalInvolutionOddCore ↥(pSpan P₁) = ⊥
  I : AEIdent P₁ 5

section Setup

variable {P₁ P₂ : Set (Subgroup G)} {K : Subgroup G} {g : G}

private theorem pc_P₁_mem_dComp (T : TCSetup Ω P₁ P₂ K g) {L : Subgroup G} (hL : L ∈ P₁) :
    L ∈ dComp Ω K := by
  rw [T.hdc]
  exact Or.inl hL

private theorem pc_P₂_mem_dComp (T : TCSetup Ω P₁ P₂ K g) {N : Subgroup G} (hN : N ∈ P₂) :
    N ∈ dComp Ω K := by
  rw [T.hdc]
  exact Or.inr hN

private theorem pc_P₁_Ω (T : TCSetup Ω P₁ P₂ K g) {L : Subgroup G} (hL : L ∈ P₁) : L ∈ Ω :=
  pc_dComp_subset T.hKΩ (pc_P₁_mem_dComp T hL)

private theorem pc_comm_mem (T : TCSetup Ω P₁ P₂ K g) {L X : Subgroup G} (hL : L ∈ P₁)
    (hX : X ∈ Ω) (hc : Commutes L X) : X ∈ P₁ ∪ P₂ := by
  by_cases hXL : X = L
  · exact Or.inl (hXL ▸ hL)
  · have h1 : X ∈ dComp Ω L :=
      pc_dComp_of_omegaNbr (pc_omegaNbr_of_comm T.h.thmD.two T.h.thmD.hyp hX hXL hc) hX
    have h2' : X ∈ dComp Ω K := pc_dComp_trans (pc_P₁_mem_dComp T hL) h1
    rw [T.hdc] at h2'
    exact h2'

private theorem pc_hinj (T : TCSetup Ω P₁ P₂ K g) :
    ∀ L ∈ P₁, ∀ L' ∈ P₁,
      (L.subgroupOf (pSpan P₁)).map T.I.φ = (L'.subgroupOf (pSpan P₁)).map T.I.φ → L = L' :=
  pc_label_inj T.I T.h.thmD.hyp T.h.thmD.two (fun L hL => pc_P₁_Ω T hL)
    (AEIdent.isPGroup_ker T.I T.hodd)

private theorem pc_twin_ex (T : TCSetup Ω P₁ P₂ K g) {L : Subgroup G} (hL : L ∈ P₁) :
    ∃ L' ∈ P₁, L' ≠ L ∧ Commutes L L' := by
  obtain ⟨α, hα, b, hlab⟩ := T.I.label L hL
  obtain ⟨L', hL', hlab'⟩ := T.I.label_surj α hα (!b)
  refine ⟨L', hL', ?_, pc_twin_comm T.I T.h.thmD.hyp T.h.thmD.two (fun L hL => pc_P₁_Ω T hL)
    (AEIdent.isPGroup_ker T.I T.hodd) hL hL' hlab hlab'⟩
  rintro rfl
  exact pc_memBar_ne α hα b (hlab.symm.trans hlab')

private theorem pc_twin_unique (T : TCSetup Ω P₁ P₂ K g) {L L₁ L₂ : Subgroup G} (hL : L ∈ P₁)
    (hL₁ : L₁ ∈ P₁) (hL₂ : L₂ ∈ P₁) (h₁ : L₁ ≠ L) (h₂ : L₂ ≠ L)
    (c₁ : Commutes L L₁) (c₂ : Commutes L L₂) : L₁ = L₂ := by
  obtain ⟨α, hα, b, hlab⟩ := T.I.label L hL
  have e₁ := pc_twin_labels T.I (pc_hinj T) hL hL₁ h₁.symm c₁ hlab
  have e₂ := pc_twin_labels T.I (pc_hinj T) hL hL₂ h₂.symm c₂ hlab
  exact pc_hinj T L₁ hL₁ L₂ hL₂ (e₁.trans e₂.symm)

private theorem pc_P₂_ncard_le (T : TCSetup Ω P₁ P₂ K g) {S : Set (Subgroup G)}
    (hS : S ⊆ P₂) (hc : ∀ L ∈ S, ∀ L' ∈ S, L ≠ L' → Commutes L L') : S.ncard ≤ 2 := by
  have hS' : conjSub g⁻¹ '' S ⊆ P₁ := by
    rintro _ ⟨N, hN, rfl⟩
    exact (T.hgP N).mp (hS hN)
  have hinj : Set.InjOn (conjSub g⁻¹) S := fun A _ B _ hAB => conjSub_injective g⁻¹ hAB
  have hc' : ∀ L ∈ conjSub g⁻¹ '' S, ∀ L' ∈ conjSub g⁻¹ '' S, L ≠ L' → Commutes L L' := by
    rintro _ ⟨N, hN, rfl⟩ _ ⟨N', hN', rfl⟩ hne
    exact pc_commutes_conj g⁻¹ (hc N hN N' hN' (fun e => hne (by rw [e])))
  have := pc_ncard_le_two T.I (pc_hinj T) hS' hc'
  rwa [Set.ncard_image_of_injective S (conjSub_injective g⁻¹)] at this

end Setup

private theorem pc_clique_wSet (h : EndHyp Ω) {C : Set (Subgroup G)} (hC : C ⊆ Ω)
    (hc : ∀ L ∈ C, ∀ L' ∈ C, L ≠ L' → Commutes L L') :
    ∃ W ∈ WSet Ω, ∀ R ∈ C, R ∈ DSet Ω W := by
  have h2 := h.thmD.two
  have hΩ := h.thmD.hyp
  have hp : IsPGroup 2 ↥(pSpan C) := isPGroup_pSpan_of_comm (fun L hL => h2 L (hC hL)) hc
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  obtain ⟨η, hηS, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  have hηG : η ∈ etaG Ω := ⟨S, hηS, hinv⟩
  have hηle : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hηS.1 hV).2
  have hWmem : (⨆ V ∈ η, V) ∈ WSet Ω := ⟨η, hηG, rfl⟩
  refine ⟨⨆ V ∈ η, V, hWmem, fun R hR => ?_⟩
  have hRΩ : R ∈ Ω := hC hR
  have hRS : R ≤ (S : Subgroup G) :=
    (le_iSup₂ (f := fun (L : Subgroup G) (_ : L ∈ C) => L) R hR).trans hS
  have hcard8 : Nat.card ↥R = 8 := h.card_eq_eight hRΩ
  have hRW : R ⊓ (⨆ V ∈ η, V) ∈ η :=
    Sec6Gen.l6_11Gen G Ω hΩ S η hηG hηle R hRΩ
      (by rw [inf_eq_left.mpr hRS, hcard8]; norm_num)
  obtain ⟨R', hR'R, hUR', _, hrel⟩ := (hηS.1 hRW).1
  have hR'Ω : R' ∈ Ω := (pc_mem_RSet_iff h2).mp hR'R
  have h1 := Subgroup.relIndex_mul_card (R ⊓ (⨆ V ∈ η, V)) R'
  rw [inf_eq_left.mpr hUR', hrel, h.card_eq_eight hR'Ω] at h1
  have hU4 : Nat.card ↥(R ⊓ (⨆ V ∈ η, V)) = 4 := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(R ⊓ (⨆ V ∈ η, V))) 2
    (by rw [hU4]; norm_num)
  have hy2 : y ^ 2 = 1 := by
    rw [← hy]
    exact pow_orderOf_eq_one y
  have hx2 : (y : G) ^ 2 = 1 := by
    have := congrArg Subtype.val hy2
    simpa using this
  have hxx : (y : G) * (y : G) = 1 := by rw [← pow_two]; exact hx2
  have hx1 : (y : G) ≠ 1 := by
    intro e
    have : y = 1 := Subtype.ext e
    rw [this, orderOf_one] at hy
    norm_num at hy
  obtain ⟨z, hz⟩ := (hΩ.omega1 R hRΩ).1
  have hyR : (y : G) ∈ R := (inf_le_left : R ⊓ (⨆ V ∈ η, V) ≤ R) y.2
  have hzx : (y : G) = z := (hz.unique _ hyR hxx).resolve_left hx1
  have hzW : z ∈ (⨆ V ∈ η, V) := by
    rw [← hzx]
    exact (inf_le_right : R ⊓ (⨆ V ∈ η, V) ≤ ⨆ V ∈ η, V) y.2
  exact h.mem_dSet_of_mem hWmem hRΩ hz hzW

private theorem pc_mtrans (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω) {A B : Subgroup G}
    (hA : A ∈ DSet Ω W) (hB : B ∈ DSet Ω W) : ∃ m ∈ MGrp Ω W, conjSub m A = B := by
  have h2 := h.thmD.two
  have hΩ := h.thmD.hyp
  have hAΩ := ((pc_mem_DSet_iff h2).mp hA).1
  have hBΩ := ((pc_mem_DSet_iff h2).mp hB).1
  have hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J →
      T ≤ R ⊔ W ⊔ OCW W := by
    intro R hR T hT J hJ hRJ hTJ
    have hRc : 8 ≤ Nat.card ↥R := hΩ.eight_le_of_mem_RSet hR.1
    have hTc : 8 ≤ Nat.card ↥T := hΩ.eight_le_of_mem_RSet hT.1
    have hJc : Nat.card ↥J = 8 := h.card_eq_eight hJ
    have hRJ' : R = J := Subgroup.eq_of_le_of_card_ge hRJ (by omega)
    have hTJ' : T = J := Subgroup.eq_of_le_of_card_ge hTJ (by omega)
    rw [hTJ', ← hRJ']
    exact le_sup_of_le_left le_sup_left
  have hA' : ∀ K ∈ Ω, AEmpty Ω K := h.thmD.aEmpty
  let c : Q3CL.Thompson.Ctx Ω W := Q3CL.Thompson.Ctx.mk hΩ hW hkey hA'
  have hex : ∃ r ∈ A, r ∉ W := by
    by_contra hcon
    push Not at hcon
    obtain ⟨P, hP, hPnc⟩ := (hΩ.omega1 A hAΩ).2
    apply hPnc
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    exact Q3CL.Thompson.Ctx.comm_W c _ (hcon _ (hP.1 a.2)) _ (hcon _ (hP.1 b.2))
  have hexB : ∃ r ∈ B, r ∉ W := by
    by_contra hcon
    push Not at hcon
    obtain ⟨P, hP, hPnc⟩ := (hΩ.omega1 B hBΩ).2
    apply hPnc
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    exact Q3CL.Thompson.Ctx.comm_W c _ (hcon _ (hP.1 a.2)) _ (hcon _ (hP.1 b.2))
  obtain ⟨r, hrA, hrW⟩ := hex
  obtain ⟨r', hr'B, hr'W⟩ := hexB
  have hsyl : ∀ X : Subgroup G, IsPGroup 2 ↥X → IsSylow2In X X := fun X hX =>
    ⟨le_rfl, hX, fun V' hV' _ hle => le_antisymm hV' hle⟩
  let ρ : Asc77.Thompson.Rep Ω W :=
    Asc77.Thompson.Rep.mk A A r hAΩ hA (hsyl A (h2 A hAΩ)) hrA hrW
  let σ : Asc77.Thompson.Rep Ω W :=
    Asc77.Thompson.Rep.mk B B r' hBΩ hB (hsyl B (h2 B hBΩ)) hr'B hr'W
  obtain ⟨m, hm, hmAB⟩ :=
    Q3CL.Thompson.Ctx.exists_conj_of_rep c h.cls (h.not_dbarConnected hW) ρ σ
  exact ⟨m, hm, hmAB⟩

private theorem pc_comm_symm {A B : Subgroup G} (h : Commutes A B) : Commutes B A :=
  fun x hx y hy => (h y hy x hx).symm

section Classes

variable {P₁ P₂ : Set (Subgroup G)} {K : Subgroup G} {g : G}

private theorem pc_clique4 (T : TCSetup Ω P₁ P₂ K g) {Ks : Subgroup G} (hKs : Ks ∈ P₁)
    (hKsc : Commutes K Ks) :
    ∃ W₀ ∈ WSet Ω, K ∈ DSet Ω W₀ ∧ Ks ∈ DSet Ω W₀ ∧
      conjSub g K ∈ DSet Ω W₀ ∧ conjSub g Ks ∈ DSet Ω W₀ := by
  have hN : conjSub g K ∈ P₂ := (T.hgP _).mpr (by rw [conjSub_inv_conjSub]; exact T.hK)
  have hNs : conjSub g Ks ∈ P₂ := (T.hgP _).mpr (by rw [conjSub_inv_conjSub]; exact hKs)
  have hKΩ : K ∈ Ω := T.hKΩ
  have hKsΩ : Ks ∈ Ω := pc_P₁_Ω T hKs
  have hNΩ : conjSub g K ∈ Ω := T.h.thmD.hyp.conjInvariant g K hKΩ
  have hNsΩ : conjSub g Ks ∈ Ω := T.h.thmD.hyp.conjInvariant g Ks hKsΩ
  have hcl : ∀ L ∈ ({K, Ks, conjSub g K, conjSub g Ks} : Set (Subgroup G)),
      ∀ L' ∈ ({K, Ks, conjSub g K, conjSub g Ks} : Set (Subgroup G)), L ≠ L' → Commutes L L' := by
    intro L hL L' hL' hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL hL'
    rcases hL with h1 | h1 | h1 | h1 <;> rcases hL' with h2 | h2 | h2 | h2 <;> rw [h1, h2] <;>
      first
      | exact absurd (h1.trans h2.symm) hne
      | exact hKsc
      | exact pc_comm_symm hKsc
      | exact T.hcomm _ T.hK _ hN
      | exact pc_comm_symm (T.hcomm _ T.hK _ hN)
      | exact T.hcomm _ T.hK _ hNs
      | exact pc_comm_symm (T.hcomm _ T.hK _ hNs)
      | exact T.hcomm _ hKs _ hN
      | exact pc_comm_symm (T.hcomm _ hKs _ hN)
      | exact T.hcomm _ hKs _ hNs
      | exact pc_comm_symm (T.hcomm _ hKs _ hNs)
      | exact pc_commutes_conj g hKsc
      | exact pc_comm_symm (pc_commutes_conj g hKsc)
  have hsub : ({K, Ks, conjSub g K, conjSub g Ks} : Set (Subgroup G)) ⊆ Ω := by
    intro L hL
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL
    rcases hL with h1 | h1 | h1 | h1 <;> rw [h1] <;> assumption
  obtain ⟨W₀, hW₀, hsubD⟩ := pc_clique_wSet T.h hsub hcl
  exact ⟨W₀, hW₀, hsubD K (by simp), hsubD Ks (by simp), hsubD _ (by simp),
    hsubD _ (by simp)⟩

private theorem pc_wyl_exists (T : TCSetup Ω P₁ P₂ K g) {Ks : Subgroup G} (hKs : Ks ∈ P₁)
    (hKsne : Ks ≠ K) (hKsc : Commutes K Ks) :
    ∃ W₀ ∈ WSet Ω, ∀ R ∈ DSet Ω W₀, (KPerp Ω R ∩ DSet Ω W₀).ncard = 4 := by
  obtain ⟨W₀, hW₀, hK, hKs', hN, -⟩ := pc_clique4 T hKs hKsc
  refine ⟨W₀, hW₀, ?_⟩
  have hKΩ : K ∈ Ω := T.hKΩ
  have hKsΩ : Ks ∈ Ω := pc_P₁_Ω T hKs
  have hNP : conjSub g K ∈ P₂ := (T.hgP _).mpr (by rw [conjSub_inv_conjSub]; exact T.hK)
  have hNΩ : conjSub g K ∈ Ω := T.h.thmD.hyp.conjInvariant g K hKΩ
  have h3 : 2 < (KPerp Ω K ∩ DSet Ω W₀).ncard := by
    refine (Set.two_lt_ncard_iff (Set.toFinite _)).mpr
      ⟨K, Ks, conjSub g K, ⟨Set.mem_insert _ _, hK⟩, ⟨?_, hKs'⟩, ⟨?_, hN⟩, hKsne.symm,
        fun e => Set.disjoint_left.mp T.hdisj T.hK (e ▸ hNP),
        fun e => Set.disjoint_left.mp T.hdisj hKs (e ▸ hNP)⟩
    · exact (pc_mem_kperp_iff T.h.thmD.two T.h.thmD.hyp hKΩ hKsΩ).mpr (Or.inr hKsc)
    · exact (pc_mem_kperp_iff T.h.thmD.two T.h.thmD.hyp hKΩ hNΩ).mpr
        (Or.inr (T.hcomm K T.hK _ hNP))
  intro R hR
  rcases (T.h.mu W₀ hW₀) with hS3 | hS4 | hWyl
  · have := ((dSet_class_ncard T.h hW₀ hK).1 hS3)
    omega
  · have := ((dSet_class_ncard T.h hW₀ hK).2.1 hS4)
    omega
  · exact (dSet_class_ncard T.h hW₀ hR).2.2 hWyl

private theorem pc_class_card (T : TCSetup Ω P₁ P₂ K g) {Ks : Subgroup G} (hKs : Ks ∈ P₁)
    (hKsne : Ks ≠ K) (hKsc : Commutes K Ks) {W : Subgroup G} (hW : W ∈ WSet Ω) {R : Subgroup G}
    (hR : R ∈ DSet Ω W) : (KPerp Ω R ∩ DSet Ω W).ncard = 4 := by
  obtain ⟨W₀, hW₀, hcard⟩ := pc_wyl_exists T hKs hKsne hKsc
  obtain ⟨n, rfl⟩ := wSet_conj T.h hW₀ hW
  have hR' : conjSub n⁻¹ R ∈ DSet Ω W₀ := by
    have := pc_dSet_conj T.h.thmD.two T.h.thmD.hyp n⁻¹ hR
    rwa [conjSub_inv_conjSub] at this
  have hRΩ : conjSub n⁻¹ R ∈ Ω := ((pc_mem_DSet_iff T.h.thmD.two).mp hR').1
  have key := pc_kperp_dset_image T.h.thmD.two T.h.thmD.hyp n (W := W₀) hRΩ
  rw [conjSub_conjSub_inv] at key
  rw [← key, Set.ncard_image_of_injective _ (conjSub_injective n)]
  exact hcard _ hR'

private theorem pc_twin_mem (T : TCSetup Ω P₁ P₂ K g) {Ks : Subgroup G} (hKs : Ks ∈ P₁)
    (hKsne : Ks ≠ K) (hKsc : Commutes K Ks) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hK : K ∈ DSet Ω W) : Ks ∈ DSet Ω W := by
  by_contra hnot
  have hΩ := T.h.thmD.hyp
  have h2 := T.h.thmD.two
  have hcard := pc_class_card T hKs hKsne hKsc hW hK
  have hCΩ : ∀ X ∈ KPerp Ω K ∩ DSet Ω W, X ∈ Ω := fun X hX =>
    ((pc_mem_DSet_iff h2).mp hX.2).1
  have hCP : ∀ X ∈ KPerp Ω K ∩ DSet Ω W, X ∈ P₁ ∪ P₂ := by
    intro X hX
    rcases (pc_mem_kperp_iff h2 hΩ T.hKΩ (hCΩ X hX)).mp hX.1 with h | h
    · rw [h]
      exact Or.inl T.hK
    · exact pc_comm_mem T T.hK (hCΩ X hX) h
  have hC1 : ∀ X ∈ KPerp Ω K ∩ DSet Ω W, X ∈ P₁ → X = K := by
    intro X hX hXP
    rcases (pc_mem_kperp_iff h2 hΩ T.hKΩ (hCΩ X hX)).mp hX.1 with h | h
    · exact h
    · by_cases hXK : X = K
      · exact hXK
      · have := pc_twin_unique T T.hK hXP hKs hXK hKsne h hKsc
        exact absurd (this ▸ hX.2) hnot
  have hC2 : ∀ X ∈ (KPerp Ω K ∩ DSet Ω W) ∩ P₂, ∀ Y ∈ (KPerp Ω K ∩ DSet Ω W) ∩ P₂,
      X ≠ Y → Commutes X Y := by
    intro X hX Y hY hXY
    have hXK : X ≠ K := fun e => Set.disjoint_left.mp T.hdisj T.hK (e ▸ hX.2)
    have hYK : Y ≠ K := fun e => Set.disjoint_left.mp T.hdisj T.hK (e ▸ hY.2)
    have hKX : K ∈ KPerp Ω X := by
      rw [pc_mem_kperp_iff h2 hΩ (hCΩ X hX.1) T.hKΩ]
      exact Or.inr (pc_comm_symm ((pc_mem_kperp_iff h2 hΩ T.hKΩ (hCΩ X hX.1)).mp hX.1.1
        |>.resolve_left hXK))
    have hYK' : Y ∈ KPerp Ω K := hY.1.1
    have hYX := dSet_comm_trans T.h hW hX.1.2 hK hY.1.2 hKX hYK'
    rcases (pc_mem_kperp_iff h2 hΩ (hCΩ X hX.1) (hCΩ Y hY.1)).mp hYX with h | h
    · exact absurd h.symm hXY
    · exact h
  have hsplit : KPerp Ω K ∩ DSet Ω W ⊆ (KPerp Ω K ∩ DSet Ω W ∩ P₁) ∪
      (KPerp Ω K ∩ DSet Ω W ∩ P₂) := fun X hX => by
    rcases hCP X hX with h | h
    · exact Or.inl ⟨hX, h⟩
    · exact Or.inr ⟨hX, h⟩
  have h1 : (KPerp Ω K ∩ DSet Ω W ∩ P₁).ncard ≤ 1 := by
    calc (KPerp Ω K ∩ DSet Ω W ∩ P₁).ncard ≤ ({K} : Set (Subgroup G)).ncard :=
          Set.ncard_le_ncard (fun X hX => by
            rw [Set.mem_singleton_iff]
            exact hC1 X hX.1 hX.2) (Set.finite_singleton K)
      _ = 1 := Set.ncard_singleton K
  have h2' : (KPerp Ω K ∩ DSet Ω W ∩ P₂).ncard ≤ 2 :=
    pc_P₂_ncard_le T (fun X hX => hX.2) (fun L hL L' hL' hne => hC2 L hL L' hL' hne)
  have h3 : (KPerp Ω K ∩ DSet Ω W).ncard ≤ (KPerp Ω K ∩ DSet Ω W ∩ P₁).ncard +
      (KPerp Ω K ∩ DSet Ω W ∩ P₂).ncard :=
    (Set.ncard_le_ncard hsplit (Set.toFinite _)).trans (Set.ncard_union_le _ _)
  omega

end Classes

section Star

variable {P₁ P₂ : Set (Subgroup G)} {K : Subgroup G} {g : G}

private theorem pc_P₁_stable (T : TCSetup Ω P₁ P₂ K g) {x : G} (hx : x ∈ pSpan (P₁ ∪ P₂))
    {M : Subgroup G} (hM : M ∈ P₁) : conjSub x M ∈ P₁ := by
  let T₀ : Subgroup G :=
    { carrier := {x | ∀ M ∈ P₁, conjSub x M ∈ P₁ ∧ conjSub x⁻¹ M ∈ P₁}
      mul_mem' := by
        intro a b ha hb M hM
        constructor
        · rw [conjSub_mul]
          exact (ha _ (hb M hM).1).1
        · rw [mul_inv_rev, conjSub_mul]
          exact (hb _ (ha M hM).2).2
      one_mem' := by
        intro M hM
        rw [inv_one, conjSub_one]
        exact ⟨hM, hM⟩
      inv_mem' := by
        intro a ha M hM
        exact ⟨(ha M hM).2, by rw [inv_inv]; exact (ha M hM).1⟩ }
  have hle : pSpan (P₁ ∪ P₂) ≤ T₀ := by
    refine iSup₂_le fun L hL => ?_
    intro y hy
    rcases hL with hL | hL
    · intro M hM
      have hyX : y ∈ pSpan P₁ := le_pSpan hL hy
      exact ⟨T.hinv M hM y hyX, T.hinv M hM y⁻¹ (inv_mem hyX)⟩
    · intro M hM
      have hc : ∀ a ∈ M, a * y = y * a := fun a ha => T.hcomm M hM L hL a ha y hy
      have hc' : ∀ a ∈ M, a * y⁻¹ = y⁻¹ * a := fun a ha => T.hcomm M hM L hL a ha y⁻¹
        (inv_mem hy)
      refine ⟨?_, ?_⟩
      · rw [pc_conj_fix hc]
        exact hM
      · rw [pc_conj_fix hc']
        exact hM
  exact (hle hx M hM).1

private theorem pc_conj_pSpan (T : TCSetup Ω P₁ P₂ K g) {n : G} (hn : conjSub n K = K)
    {x : G} (hx : x ∈ pSpan (P₁ ∪ P₂)) : n * x * n⁻¹ ∈ pSpan (P₁ ∪ P₂) := by
  let S : Subgroup G := (pSpan (P₁ ∪ P₂)).comap (MulAut.conj n).toMonoidHom
  have hle : pSpan (P₁ ∪ P₂) ≤ S := by
    refine iSup₂_le fun L hL => ?_
    intro y hy
    have hLd : L ∈ dComp Ω K := by
      rw [T.hdc]
      exact hL
    have hcd := pc_dComp_conj T.h.thmD.two T.h.thmD.hyp n hLd
    rw [hn] at hcd
    have hmem : n * y * n⁻¹ ∈ conjSub n L := conj_mem_conjSub hy
    have hsub : conjSub n L ≤ pSpan (P₁ ∪ P₂) := by
      have : conjSub n L ∈ P₁ ∪ P₂ := by
        rw [← T.hdc]
        exact hcd
      exact le_iSup₂ (f := fun (L' : Subgroup G) (_ : L' ∈ P₁ ∪ P₂) => L') (conjSub n L) this
    exact hsub hmem
  exact hle hx

private theorem pc_fix_twin (T : TCSetup Ω P₁ P₂ K g) {Ks : Subgroup G} (hKs : Ks ∈ P₁)
    (hKsne : Ks ≠ K) (hKsc : Commutes K Ks) {n : G} (hn : conjSub n K = K) :
    conjSub n Ks = Ks := by
  have hn' : conjSub n⁻¹ K = K := by
    have := conjSub_inv_conjSub n K
    rwa [hn] at this
  obtain ⟨x, hxP, hxK⟩ := T.htr K T.hK Ks hKs
  have hy : conjSub (n * x * n⁻¹) K = conjSub n Ks := by
    calc conjSub (n * x * n⁻¹) K = conjSub (n * x) (conjSub n⁻¹ K) := conjSub_mul _ _ _
      _ = conjSub (n * x) K := by rw [hn']
      _ = conjSub n (conjSub x K) := conjSub_mul _ _ _
      _ = conjSub n Ks := by rw [hxK]
  have hsubP : pSpan P₁ ≤ pSpan (P₁ ∪ P₂) :=
    iSup₂_le fun L hL => le_iSup₂ (f := fun (L' : Subgroup G) (_ : L' ∈ P₁ ∪ P₂) => L') L
      (Or.inl hL)
  have hyP : conjSub (n * x * n⁻¹) K ∈ P₁ :=
    pc_P₁_stable T (pc_conj_pSpan T hn (hsubP hxP)) T.hK
  rw [hy] at hyP
  have hc : Commutes K (conjSub n Ks) := by
    have := pc_commutes_conj n hKsc
    rwa [hn] at this
  have hne : conjSub n Ks ≠ K := by
    intro e
    apply hKsne
    calc Ks = conjSub n⁻¹ (conjSub n Ks) := (conjSub_inv_conjSub n Ks).symm
      _ = conjSub n⁻¹ K := by rw [e]
      _ = K := hn'
  exact pc_twin_unique T T.hK hyP hKs hne hKsne hc hKsc

end Star

open Classical in
private noncomputable def pcStar (K Ks A : Subgroup G) : Subgroup G :=
  if h : ∃ x : G, conjSub x K = A then conjSub (Classical.choose h) Ks else Ks

private theorem pcStar_eq {K Ks : Subgroup G}
    (hfix : ∀ n : G, conjSub n K = K → conjSub n Ks = Ks) {A : Subgroup G} {x : G}
    (hx : conjSub x K = A) : pcStar K Ks A = conjSub x Ks := by
  have hA : ∃ x' : G, conjSub x' K = A := ⟨x, hx⟩
  unfold pcStar
  rw [dif_pos hA]
  have hx₀ : conjSub (Classical.choose hA) K = A := Classical.choose_spec hA
  set x₀ := Classical.choose hA with hx₀def
  have hn : conjSub (x₀⁻¹ * x) K = K := by
    rw [conjSub_mul, hx, ← hx₀, conjSub_inv_conjSub]
  have h1 := hfix _ hn
  calc conjSub x₀ Ks = conjSub x₀ (conjSub (x₀⁻¹ * x) Ks) := by rw [h1]
    _ = conjSub (x₀ * (x₀⁻¹ * x)) Ks := (conjSub_mul _ _ _).symm
    _ = conjSub x Ks := by rw [mul_inv_cancel_left]

private theorem pcStar_K {K Ks : Subgroup G}
    (hfix : ∀ n : G, conjSub n K = K → conjSub n Ks = Ks) : pcStar K Ks K = Ks := by
  rw [pcStar_eq hfix (x := 1) (conjSub_one K), conjSub_one]

private theorem pcStar_conj {K Ks : Subgroup G}
    (hfix : ∀ n : G, conjSub n K = K → conjSub n Ks = Ks) (m : G) {A : Subgroup G} {x : G}
    (hx : conjSub x K = A) : pcStar K Ks (conjSub m A) = conjSub m (pcStar K Ks A) := by
  rw [pcStar_eq hfix (x := m * x) (by rw [conjSub_mul, hx]), pcStar_eq hfix hx, conjSub_mul]

section StarProps

variable {P₁ P₂ : Set (Subgroup G)} {K : Subgroup G} {g : G}

private theorem pc_star_props (T : TCSetup Ω P₁ P₂ K g) {Ks : Subgroup G} (hKs : Ks ∈ P₁)
    (hKsne : Ks ≠ K) (hKsc : Commutes K Ks) :
    (∀ n : G, conjSub n K = K → conjSub n Ks = Ks) := fun n hn =>
  pc_fix_twin T hKs hKsne hKsc hn

private theorem pc_star_Ω (T : TCSetup Ω P₁ P₂ K g) {Ks : Subgroup G} (hKs : Ks ∈ P₁)
    (hKsne : Ks ≠ K) (hKsc : Commutes K Ks) {A : Subgroup G} (hA : A ∈ Ω) :
    pcStar K Ks A ∈ Ω := by
  obtain ⟨x, hx⟩ := T.h.thmD.trans K T.hKΩ A hA
  rw [pcStar_eq (pc_star_props T hKs hKsne hKsc) hx]
  exact T.h.thmD.hyp.conjInvariant x Ks (pc_P₁_Ω T hKs)

private theorem pc_star_comm (T : TCSetup Ω P₁ P₂ K g) {Ks : Subgroup G} (hKs : Ks ∈ P₁)
    (hKsne : Ks ≠ K) (hKsc : Commutes K Ks) {A : Subgroup G} (hA : A ∈ Ω) :
    Commutes A (pcStar K Ks A) := by
  obtain ⟨x, hx⟩ := T.h.thmD.trans K T.hKΩ A hA
  rw [pcStar_eq (pc_star_props T hKs hKsne hKsc) hx, ← hx]
  exact pc_commutes_conj x hKsc

private theorem pc_star_mem_DSet (T : TCSetup Ω P₁ P₂ K g) {Ks : Subgroup G} (hKs : Ks ∈ P₁)
    (hKsne : Ks ≠ K) (hKsc : Commutes K Ks) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {A : Subgroup G} (hA : A ∈ DSet Ω W) : pcStar K Ks A ∈ DSet Ω W := by
  have hAΩ := ((pc_mem_DSet_iff T.h.thmD.two).mp hA).1
  obtain ⟨x, hx⟩ := T.h.thmD.trans K T.hKΩ A hAΩ
  have hA' : conjSub x⁻¹ A ∈ DSet Ω (conjSub x⁻¹ W) := pc_dSet_conj T.h.thmD.two T.h.thmD.hyp x⁻¹ hA
  rw [← hx, conjSub_inv_conjSub] at hA'
  have hW' : conjSub x⁻¹ W ∈ WSet Ω := Asc77.WSet.conj T.h.thmD.hyp.conjInvariant hW x⁻¹
  have hKs' := pc_twin_mem T hKs hKsne hKsc hW' hA'
  have := pc_dSet_conj T.h.thmD.two T.h.thmD.hyp x hKs'
  rw [conjSub_conjSub_inv] at this
  rw [pcStar_eq (pc_star_props T hKs hKsne hKsc) hx]
  exact this

end StarProps

section Invariant

variable {P₁ P₂ : Set (Subgroup G)} {K : Subgroup G} {g : G}

private theorem pc_vW_mem (h : EndHyp Ω) {W : Subgroup G} {A A' : Subgroup G}
    (hA : A ∈ DSet Ω W) (hA' : A' ∈ DSet Ω W) (hc : A' ∈ KPerp Ω A) {zA zs : G}
    (hzA : IsUniqueInvolution A zA) (hzs : IsUniqueInvolution A' zs) :
    zA * zs ∈ vW Ω W :=
  Subgroup.subset_closure ⟨A, hA, A', hA', hc, zA, zs, hzA, hzs, rfl⟩

private theorem pc_MGrp_cent (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω) :
    MGrp Ω W ≤ Subgroup.centralizer (vW Ω W : Set G) := by
  unfold MGrp
  exact iSup₂_le fun R hR => dSet_le_centralizer_vW h hW hR

private theorem pc_const (T : TCSetup Ω P₁ P₂ K g) {Ks : Subgroup G} (hKs : Ks ∈ P₁)
    (hKsne : Ks ≠ K) (hKsc : Commutes K Ks) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {A B : Subgroup G} (hA : A ∈ DSet Ω W) (hB : B ∈ DSet Ω W) {zA zs zB zs' : G}
    (hzA : IsUniqueInvolution A zA) (hzs : IsUniqueInvolution (pcStar K Ks A) zs)
    (hzB : IsUniqueInvolution B zB) (hzs' : IsUniqueInvolution (pcStar K Ks B) zs') :
    zA * zs = zB * zs' := by
  have h2 := T.h.thmD.two
  have hΩ := T.h.thmD.hyp
  obtain ⟨m, hm, hmAB⟩ := pc_mtrans T.h hW hA hB
  have hAΩ := ((pc_mem_DSet_iff h2).mp hA).1
  obtain ⟨x, hx⟩ := T.h.thmD.trans K T.hKΩ A hAΩ
  have hstar : pcStar K Ks B = conjSub m (pcStar K Ks A) := by
    rw [← hmAB]
    exact pcStar_conj (pc_star_props T hKs hKsne hKsc) m hx
  have hA'Ω := pc_star_Ω T hKs hKsne hKsc hAΩ
  have hA'D : pcStar K Ks A ∈ DSet Ω W := pc_star_mem_DSet T hKs hKsne hKsc hW hA
  have hcomm := pc_star_comm T hKs hKsne hKsc hAΩ
  have hvW := pc_vW_mem T.h hA hA'D (by
    rw [pc_mem_kperp_iff h2 hΩ hAΩ hA'Ω]
    exact Or.inr hcomm) hzA hzs
  have hcent := pc_MGrp_cent T.h hW hm
  have hmc : (zA * zs) * m = m * (zA * zs) := Subgroup.mem_centralizer_iff.mp hcent _ hvW
  have hzB' : zB = m * zA * m⁻¹ := by
    rw [← hmAB] at hzB
    exact hzB.eq (hzA.conj m)
  have hzs'' : zs' = m * zs * m⁻¹ := by
    have := hzs.conj m
    rw [← hstar] at this
    exact hzs'.eq this
  have key : m * (zA * zs) * m⁻¹ = zA * zs := by
    rw [← hmc]
    group
  rw [hzB', hzs'']
  have e : m * zA * m⁻¹ * (m * zs * m⁻¹) = m * (zA * zs) * m⁻¹ := by group
  rw [e, key]

end Invariant

section Global

variable {P₁ P₂ : Set (Subgroup G)} {K : Subgroup G} {g : G}

private theorem pc_adj_W (h : EndHyp Ω) {M N : Subgroup G} (hM : M ∈ Ω)
    (hadj : dstarAdj Ω M N) : ∃ W ∈ WSet Ω, M ∈ DSet Ω W ∧ N ∈ DSet Ω W := by
  obtain ⟨hNΩ, hstar⟩ := hadj
  by_cases hc : Commutes M N
  · have hC : ({M, N} : Set (Subgroup G)) ⊆ Ω := by
      intro L hL
      rcases hL with h1 | h1
      · rw [h1]
        exact hM
      · rw [h1]
        exact hNΩ
    have hc' : ∀ L ∈ ({M, N} : Set (Subgroup G)), ∀ L' ∈ ({M, N} : Set (Subgroup G)),
        L ≠ L' → Commutes L L' := by
      intro L hL L' hL' hne
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL hL'
      rcases hL with h1 | h1 <;> rcases hL' with h2 | h2 <;> rw [h1, h2]
      all_goals first
        | exact absurd (h1.trans h2.symm) hne
        | exact hc
        | exact pc_comm_symm hc
    obtain ⟨W, hW, hWD⟩ := pc_clique_wSet h hC hc'
    exact ⟨W, hW, hWD M (by simp), hWD N (by simp)⟩
  · have hMN : ¬ Commutes N M := fun e => hc (pc_comm_symm e)
    rcases hstar with hstar | hstar
    · have hJn : N ∉ omegaNbr Ω M := fun hJ => hc (pc_comm_of_omegaNbr h.thmD.two h.thmD.hyp hM hJ)
      obtain ⟨W, hW, hMD, hND, -⟩ := exists_wSet_of_omegaStar h hM hstar hJn
      exact ⟨W, hW, hMD, hND⟩
    · have hJn : M ∉ omegaNbr Ω N := fun hJ =>
        hMN (pc_comm_of_omegaNbr h.thmD.two h.thmD.hyp hNΩ hJ)
      obtain ⟨W, hW, hND, hMD, -⟩ := exists_wSet_of_omegaStar h hNΩ hstar hJn
      exact ⟨W, hW, hMD, hND⟩

private theorem pc_global (T : TCSetup Ω P₁ P₂ K g) {Ks : Subgroup G} (hKs : Ks ∈ P₁)
    (hKsne : Ks ≠ K) (hKsc : Commutes K Ks) {zK zKs : G} (hzK : IsUniqueInvolution K zK)
    (hzKs : IsUniqueInvolution Ks zKs) :
    ∀ X ∈ Ω, ∀ zX zs : G, IsUniqueInvolution X zX →
      IsUniqueInvolution (pcStar K Ks X) zs → zX * zs = zK * zKs := by
  have key : ∀ X, Relation.ReflTransGen (dstarAdj Ω) K X → X ∈ Ω ∧ ∀ zX zs : G,
      IsUniqueInvolution X zX → IsUniqueInvolution (pcStar K Ks X) zs → zX * zs = zK * zKs := by
    intro X hX
    induction hX with
    | refl =>
      refine ⟨T.hKΩ, fun zX zs hzX hzs => ?_⟩
      rw [pcStar_K (pc_star_props T hKs hKsne hKsc)] at hzs
      rw [← hzK.eq hzX, ← hzKs.eq hzs]
    | @tail M N _ hadj ih =>
      obtain ⟨hMΩ, hP⟩ := ih
      refine ⟨hadj.1, fun zN zs hzN hzs => ?_⟩
      obtain ⟨W, hW, hMD, hND⟩ := pc_adj_W T.h hMΩ hadj
      obtain ⟨zM, hzM⟩ := (T.h.thmD.hyp.omega1 M hMΩ).1
      obtain ⟨zsM, hzsM⟩ :=
        (T.h.thmD.hyp.omega1 (pcStar K Ks M) (pc_star_Ω T hKs hKsne hKsc hMΩ)).1
      have h1 := hP zM zsM hzM hzsM
      rw [← h1]
      exact (pc_const T hKs hKsne hKsc hW hMD hND hzM hzsM hzN hzs).symm
  intro X hX zX zs hzX hzs
  exact (key X (T.h.star K T.hKΩ X hX)).2 zX zs hzX hzs

private theorem pc_c0_one (T : TCSetup Ω P₁ P₂ K g) {Ks : Subgroup G} (hKs : Ks ∈ P₁)
    (hKsne : Ks ≠ K) (hKsc : Commutes K Ks) {zK zKs : G} (hzK : IsUniqueInvolution K zK)
    (hzKs : IsUniqueInvolution Ks zKs) : zK * zKs = 1 := by
  have hglob := pc_global T hKs hKsne hKsc hzK hzKs
  have hcen : ∀ X ∈ Ω, ∀ x ∈ X, (zK * zKs) * x = x * (zK * zKs) := by
    intro X hX x hx
    obtain ⟨W, hW, hXD⟩ := pc_clique_wSet T.h (C := {X}) (by simpa using hX)
      (by
        intro L hL L' hL' hne
        simp only [Set.mem_singleton_iff] at hL hL'
        exact absurd (hL.trans hL'.symm) hne)
    have hXD' : X ∈ DSet Ω W := hXD X (by simp)
    obtain ⟨zX, hzX⟩ := (T.h.thmD.hyp.omega1 X hX).1
    obtain ⟨zs, hzs⟩ :=
      (T.h.thmD.hyp.omega1 (pcStar K Ks X) (pc_star_Ω T hKs hKsne hKsc hX)).1
    have hstarD := pc_star_mem_DSet T hKs hKsne hKsc hW hXD'
    have hvW := pc_vW_mem T.h hXD' hstarD
      ((pc_mem_kperp_iff T.h.thmD.two T.h.thmD.hyp hX (pc_star_Ω T hKs hKsne hKsc hX)).mpr
        (Or.inr (pc_star_comm T hKs hKsne hKsc hX))) hzX hzs
    rw [hglob X hX zX zs hzX hzs] at hvW
    have hcx := dSet_le_centralizer_vW T.h hW hXD' hx
    exact Subgroup.mem_centralizer_iff.mp hcx _ hvW
  have hcenter : ∀ x : G, (zK * zKs) * x = x * (zK * zKs) := by
    intro x
    have hx : x ∈ pSpan Ω := by
      rw [T.h.thmD.gen]
      exact Subgroup.mem_top x
    have hle : pSpan Ω ≤ Subgroup.centralizer ({zK * zKs} : Set G) := by
      refine iSup₂_le fun X hX => ?_
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff.mp hs]
      exact hcen X hX y hy
    have := Subgroup.mem_centralizer_iff.mp (hle hx) _ (Set.mem_singleton _)
    exact this
  have hc0 : zK * zKs ∈ Subgroup.center G :=
    Subgroup.mem_center_iff.mpr fun x => (hcenter x).symm
  rw [T.h.center] at hc0
  exact Subgroup.mem_bot.mp hc0

private theorem pc_twin_prod (T : TCSetup Ω P₁ P₂ K g) {Ks : Subgroup G} (hKs : Ks ∈ P₁)
    (hKsne : Ks ≠ K) (hKsc : Commutes K Ks) {zK zKs : G} (hzK : IsUniqueInvolution K zK)
    (hzKs : IsUniqueInvolution Ks zKs) {L L' : Subgroup G} (hL : L ∈ P₁) (hL' : L' ∈ P₁)
    (hne : L ≠ L') (hc : Commutes L L') {zL zL' : G} (hzL : IsUniqueInvolution L zL)
    (hzL' : IsUniqueInvolution L' zL') : zL * zL' = 1 := by
  have hc1 := pc_c0_one T hKs hKsne hKsc hzK hzKs
  obtain ⟨x, hxP, hxK⟩ := T.htr K T.hK L hL
  have hKsx : conjSub x Ks ∈ P₁ := T.hinv Ks hKs x hxP
  have hcx : Commutes L (conjSub x Ks) := by
    rw [← hxK]
    exact pc_commutes_conj x hKsc
  have hne1 : conjSub x Ks ≠ L := by
    rw [← hxK]
    intro e
    exact hKsne (conjSub_injective x e)
  have hL'eq : L' = conjSub x Ks :=
    pc_twin_unique T hL hL' hKsx hne.symm hne1 hc hcx
  have hzLeq : zL = x * zK * x⁻¹ := by
    rw [← hxK] at hzL
    exact hzL.eq (hzK.conj x)
  have hzL'eq : zL' = x * zKs * x⁻¹ := by
    rw [hL'eq] at hzL'
    exact hzL'.eq (hzKs.conj x)
  rw [hzLeq, hzL'eq]
  calc x * zK * x⁻¹ * (x * zKs * x⁻¹) = x * (zK * zKs) * x⁻¹ := by group
    _ = 1 := by rw [hc1]; group

end Global

theorem caseB_aeCoverHyp (h : EndHyp Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ omegaNbr Ω K) (hne : KPerp Ω J ≠ KPerp Ω K) {P₁ P₂ : Set (Subgroup G)}
    (hP₁ : K ∈ P₁) (hdc : dComp Ω K = P₁ ∪ P₂) (hdisj : Disjoint P₁ P₂)
    (hcomm : ∀ L ∈ P₁, ∀ L' ∈ P₂, ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hg : ∃ g : G, conjSub g K ∈ P₂ ∧ ∀ L : Subgroup G, L ∈ P₂ ↔ conjSub g⁻¹ L ∈ P₁)
    (hinv : ∀ L ∈ P₁, ∀ x ∈ pSpan P₁, conjSub x L ∈ P₁)
    (htr : ∀ L ∈ P₁, ∀ L' ∈ P₁, ∃ x ∈ pSpan P₁, conjSub x L = L')
    (hodd : classicalInvolutionOddCore ↥(pSpan P₁) = ⊥)
    (I : AEIdent P₁ 5) : TL4.AECoverHyp I := by
  obtain ⟨g, -, hgP⟩ := hg
  let T : TCSetup Ω P₁ P₂ K g :=
    ⟨h, hK, hP₁, hdc, hdisj, hcomm, hgP, hinv, htr, hodd, I⟩
  obtain ⟨Ks, hKs, hKsne, hKsc⟩ := pc_twin_ex T hP₁
  obtain ⟨zK, hzK⟩ := (h.thmD.hyp.omega1 K hK).1
  obtain ⟨zKs, hzKs⟩ := (h.thmD.hyp.omega1 Ks (pc_P₁_Ω T hKs)).1
  have hΩ := h.thmD.hyp
  have h2 := h.thmD.two
  have hPΩ : ∀ L ∈ P₁, L ∈ Ω := fun L hL => pc_P₁_Ω T hL
  have hk : IsPGroup 2 ↥I.φ.ker := AEIdent.isPGroup_ker I hodd
  exact
    { ker_two := hk
      card := fun L hL => h.card_eq_eight (hPΩ L hL)
      conj_mem := hinv
      label_inj := pc_hinj T
      twin_comm := fun α hα L hL L' hL' hlab hlab' x hx y hy =>
        pc_twin_comm I hΩ h2 hPΩ hk hL hL' hlab hlab' x hx y hy
      twin_z := fun α hα L hL L' hL' hlab hlab' u u' hu hu' => by
        have hne' : L ≠ L' := by
          rintro rfl
          rw [hlab] at hlab'
          exact AE.memBar_true_ne_false (by norm_num) α hα hlab'
        have hc : Commutes L L' := pc_twin_comm I hΩ h2 hPΩ hk hL hL' hlab hlab'
        have h1 := pc_twin_prod T hKs hKsne hKsc hzK hzKs hL hL' hne' hc hu hu'
        have e1 : u' = u⁻¹ := eq_inv_of_mul_eq_one_right h1
        have e2 : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu.sq
        exact (e1.trans e2).symm }

end CFSG.ClassicalInvolution.Q3.Sec13
