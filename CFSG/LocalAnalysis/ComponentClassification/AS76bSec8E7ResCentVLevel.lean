module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7ResCentU
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassVBruhat

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.E7Pilot
open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily conjCoeff)
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)

local instance e7ResCentVLevelNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

@[expose] def vL1 : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 0, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 1], ![0, 1, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 1], ![0, 1, 0, 1, 1, 0, 0], ![0, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 1, 1],
    ![0, 1, 0, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 0, 0], ![1, 1, 1, 1, 0, 0, 0], ![0, 0, 1, 1, 1, 1, 1],
    ![0, 1, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 0, 0], ![1, 1, 1, 1, 1, 0, 0], ![0, 1, 1, 2, 1, 1, 0],
    ![1, 0, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 0], ![1, 1, 1, 2, 1, 0, 0], ![0, 1, 1, 2, 2, 1, 0],
    ![1, 1, 1, 2, 1, 1, 0], ![1, 1, 2, 2, 1, 0, 0], ![1, 1, 1, 2, 2, 1, 0], ![1, 1, 2, 2, 1, 1, 0],
    ![1, 1, 2, 2, 2, 1, 0], ![1, 1, 2, 3, 2, 1, 0]]

theorem vL1_check : vL1.Nodup ∧ (vL1 ++ vPsi).Nodup ∧
    ∀ β ∈ vL1, isRootB .E7 β = true ∧ 0 < height β ∧ vLevel β = 1 := by
  decide +kernel

theorem vL1_complete_check : ∀ k < Tag.E7.rootCertificate.roots.length,
    vLevel (Tag.E7.rootCertificate.root k) = 1 → Tag.E7.rootCertificate.root k ∈ vL1 := by
  decide +kernel

@[expose] def vLongGen : Fin 6 → Fin Tag.E7.rank → ℤ :=
  ![![1, 0, 1, 1, 1, 1, 0], ![-1, 0, -1, -1, -1, -1, 0], ![0, 0, 1, 1, 1, 0, 0],
    ![0, 0, -1, -1, -1, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0]]

theorem vLongGen_check :
    ∀ i : Fin 6, isRootB .E7 (vLongGen i) = true ∧ vLevel (vLongGen i) = 0 := by
  decide +kernel

theorem vLevel_nsmul' (a : ℕ) (β : Fin Tag.E7.rank → ℤ) : vLevel (a • β) = a * vLevel β := by
  simp only [vLevel, Pi.smul_apply, nsmul_eq_mul]
  ring

theorem level_of_mem_vL1 {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ vL1) : vLevel β = 1 :=
  (vL1_check.2.2 β hβ).2.2

theorem conj_comm_aux {G : Type*} [Group G] {q g w : G} (h : g * q = q * g) :
    q * (g * w * g⁻¹) * q⁻¹ = g * (q * w * q⁻¹) * g⁻¹ := by
  calc q * (g * w * g⁻¹) * q⁻¹ = (q * g) * w * (q * g)⁻¹ := by group
    _ = (g * q) * w * (g * q)⁻¹ := by rw [h]
    _ = g * (q * w * q⁻¹) * g⁻¹ := by group

section Roots


theorem mem_parabolicRadicalRoots_vNodes_iff {β : Fin Tag.E7.rank → ℤ} :
    β ∈ parabolicRadicalRoots .E7 vNodes ↔ (IsRoot .E7 β ∧ 0 < height β) ∧ 1 ≤ vLevel β := by
  constructor
  · rintro ⟨hpos, hnot⟩
    refine ⟨hpos, ?_⟩
    have hnn := (IsRoot.height_pos_iff hpos.1).1 hpos.2
    by_contra hlt
    have h1 : β 1 = 0 := by have := hnn 1; have := hnn 6; simp only [vLevel] at hlt; omega
    have h6 : β 6 = 0 := by have := hnn 1; have := hnn 6; simp only [vLevel] at hlt; omega
    refine hnot ⟨⟨hpos.1, fun i hi => ?_⟩, hpos⟩
    simp only [vNodes, Set.mem_ofPred_eq, not_and_or, not_not] at hi
    rcases hi with rfl | rfl
    · exact h1
    · exact h6
  · rintro ⟨hpos, h1⟩
    refine ⟨hpos, fun h => ?_⟩
    have e1 : β 1 = 0 := h.1.2 1 (by simp [vNodes])
    have e6 : β 6 = 0 := h.1.2 6 (by simp [vNodes])
    simp only [vLevel] at h1
    omega

theorem isRoot_of_mem_vL1 {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ vL1) : IsRoot .E7 β :=
  isRootB_iff.1 (vL1_check.2.2 β hβ).1

theorem mem_vL1_of_level {ρ : Fin Tag.E7.rank → ℤ} (hρ : IsRoot .E7 ρ) (h : vLevel ρ = 1) :
    ρ ∈ vL1 := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hρ
  exact vL1_complete_check k hk h

theorem setOf_mem_vL1_append_vPsi :
    {x | x ∈ vL1 ++ vPsi} = parabolicRadicalRoots .E7 vNodes := by
  ext β
  simp only [Set.mem_ofPred_eq, List.mem_append, mem_parabolicRadicalRoots_vNodes_iff]
  constructor
  · rintro (h | h)
    · exact ⟨⟨isRoot_of_mem_vL1 h, (vL1_check.2.2 β h).2.1⟩, (level_of_mem_vL1 h).ge⟩
    · exact ⟨pos_of_mem_vPsi h, le_trans (by norm_num) (level_of_mem_vPsi h)⟩
  · rintro ⟨hpos, h1⟩
    rcases eq_or_lt_of_le h1 with h | h
    · exact Or.inl (mem_vL1_of_level hpos.1 h.symm)
    · exact Or.inr (mem_vPsi_of_level hpos.1 (by omega))

theorem vRadical_closed : ∀ α ∈ parabolicRadicalRoots .E7 vNodes,
    ∀ β ∈ parabolicRadicalRoots .E7 vNodes, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot .E7 (a • α + b • β) → a • α + b • β ∈ parabolicRadicalRoots .E7 vNodes := by
  intro α hα β hβ a b ha hb hr
  rw [mem_parabolicRadicalRoots_vNodes_iff] at hα hβ ⊢
  refine ⟨CFSG.LieType.Ree.posRoots_nsmul_add_nsmul_mem α hα.1 β hβ.1 a b ha hb hr, ?_⟩
  · rw [vLevel_add, vLevel_nsmul', vLevel_nsmul']
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith [hα.2, hβ.2]

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def vL1Prod (c : (Fin Tag.E7.rank → ℤ) → K) : ModGL .E7 K :=
  (vL1.map fun β => pinnedX .E7 K β (c β)).prod

theorem vL1Prod_eq_one {c : (Fin Tag.E7.rank → ℤ) → K} (hc : ∀ β ∈ vL1, c β = 0) :
    vL1Prod K c = 1 := by
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
  rw [hc β hβ, pinnedX_zero]

end Roots

section Main

variable {K : Type} [Field K]


theorem exists_vL1Prod_mul_rootProd_vPsi {q : ModGL .E7 K}
    (hq : q ∈ parabolicRadical .E7 K vNodes) :
    ∃ c : (Fin Tag.E7.rank → ℤ) → K, q = vL1Prod K c * rootProd .E7 K vPsi c := by
  obtain ⟨-, hsurj, -⟩ := CFSG.LieType.Ree.list_prod_pinnedX_bijective (K := K)
    (S := parabolicRadicalRoots .E7 vNodes) (fun _ hα => hα.1) vRadical_closed vL1_check.2.1
    setOf_mem_vL1_append_vPsi
  obtain ⟨c, hc⟩ := hsurj q hq
  refine ⟨c, ?_⟩
  rw [← hc, List.map_append, List.prod_append]
  rfl

theorem conjCoeff_vPsi_apply {α : Fin Tag.E7.rank → ℤ} (hα1 : vLevel α ≤ 1) (t : K)
    (c : (Fin Tag.E7.rank → ℤ) → K) {ρ : Fin Tag.E7.rank → ℤ} (hρ : ρ ∈ vPsi) :
    conjCoeff α t vPsi c ρ = c ρ + if ρ - α ∈ vPsi then t * c (ρ - α) else 0 := by
  rw [conjCoeff_apply_ite vPsi_nodup (fun _ h => isRoot_of_mem_vPsi h) α t c hρ]
  by_cases h : ρ - α ∈ vPsi
  · have hne : α ≠ ρ - α := fun e => by
      have := level_of_mem_vPsi h
      rw [← e] at this
      omega
    rw [ite_eq_left ⟨h, hne⟩, ite_eq_left h]
  · rw [ite_eq_right fun h' => h h'.1, ite_eq_right h]

variable (K) in
@[expose] noncomputable def vFold (l : List (Fin Tag.E7.rank → ℤ))
    (c e : (Fin Tag.E7.rank → ℤ) → K) : (Fin Tag.E7.rank → ℤ) → K :=
  l.foldr (fun β e' => conjCoeff β (c β) vPsi e') e

theorem conj_listProd_rootProd_vPsi [CharP K 2] {l : List (Fin Tag.E7.rank → ℤ)}
    (hl : ∀ β ∈ l, IsRoot .E7 β ∧ 0 ≤ vLevel β) (c e : (Fin Tag.E7.rank → ℤ) → K) :
    (l.map fun β => pinnedX .E7 K β (c β)).prod * rootProd .E7 K vPsi e *
        ((l.map fun β => pinnedX .E7 K β (c β)).prod)⁻¹ =
      rootProd .E7 K vPsi (vFold K l c e) := by
  induction l with
  | nil => simp [vFold]
  | cons β l ih =>
    have hβ := hl β List.mem_cons_self
    rw [List.map_cons, List.prod_cons, vFold, List.foldr_cons, ← vFold,
      ← conj_rootProd_vPsi hβ.1 hβ.2, ← ih fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ)]
    group

theorem vFold_single_apply {l : List (Fin Tag.E7.rank → ℤ)} (hnd : l.Nodup)
    (hl : ∀ β ∈ l, vLevel β = 1) (c : (Fin Tag.E7.rank → ℤ) → K) {x : Fin Tag.E7.rank → ℤ}
    (hx : x ∈ vPsi) (hx2 : vLevel x = 2) {ρ : Fin Tag.E7.rank → ℤ} (hρ : ρ ∈ vPsi) :
    vFold K l c (Pi.single x 1) ρ =
      (Pi.single x (1 : K) : (Fin Tag.E7.rank → ℤ) → K) ρ +
        if vLevel ρ = 3 ∧ ρ - x ∈ l then c (ρ - x) else 0 := by
  induction l generalizing ρ with
  | nil => simp [vFold]
  | cons β l ih =>
    rw [List.nodup_cons] at hnd
    have hβ1 := hl β List.mem_cons_self
    have hl' : ∀ γ ∈ l, vLevel γ = 1 := fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ)
    rw [vFold, List.foldr_cons, ← vFold, conjCoeff_vPsi_apply hβ1.le _ _ hρ, ih hnd.2 hl' hρ]
    by_cases hb : ρ - β ∈ vPsi
    · rw [ite_eq_left hb, ih hnd.2 hl' hb]
      have hlev : vLevel (ρ - β) = vLevel ρ - 1 := by
        rw [sub_eq_add_neg, vLevel_add, vLevel_neg, hβ1]
        ring
      have hρβ3 : ¬(vLevel (ρ - β) = 3 ∧ ρ - β - x ∈ l) := by
        rintro ⟨h3, -⟩
        have := level_of_mem_vPsi hρ
        have h3' : vLevel ρ ≤ 3 := by
          have := vPsi_level_check ρ hρ
          omega
        omega
      rw [ite_eq_right hρβ3, add_zero]
      by_cases hx' : ρ - β = x
      ·
        have hβx : ρ - x = β := by rw [← hx']; abel
        have h3 : vLevel ρ = 3 := by
          have : vLevel x = vLevel ρ - 1 := by rw [← hx', hlev]
          omega
        rw [hx', Pi.single_eq_same, mul_one, hβx, ite_eq_right fun h => hnd.1 h.2,
          ite_eq_left ⟨h3, List.mem_cons_self⟩]
        ring
      · rw [Pi.single_eq_of_ne hx', mul_zero, add_zero]
        congr 1
        have hne : ρ - x ≠ β := fun h => hx' (by rw [← h]; abel)
        by_cases h3 : vLevel ρ = 3 ∧ ρ - x ∈ l
        · rw [ite_eq_left h3, ite_eq_left ⟨h3.1, List.mem_cons_of_mem _ h3.2⟩]
        · rw [ite_eq_right h3, ite_eq_right]
          rintro ⟨h3', hm⟩
          rcases List.mem_cons.1 hm with h | h
          · exact hne h
          · exact h3 ⟨h3', h⟩
    · rw [ite_eq_right hb, add_zero]
      congr 1
      have hne : ρ - x ≠ β := fun h => hb (by rw [← h, sub_sub_cancel]; exact hx)
      by_cases h3 : vLevel ρ = 3 ∧ ρ - x ∈ l
      · rw [ite_eq_left h3, ite_eq_left ⟨h3.1, List.mem_cons_of_mem _ h3.2⟩]
      · rw [ite_eq_right h3, ite_eq_right]
        rintro ⟨h3', hm⟩
        rcases List.mem_cons.1 hm with h | h
        · exact hne h
        · exact h3 ⟨h3', h⟩

theorem conj_vL1Prod_rootProd_vPsi [CharP K 2] (c e : (Fin Tag.E7.rank → ℤ) → K) :
    vL1Prod K c * rootProd .E7 K vPsi e * (vL1Prod K c)⁻¹ =
      rootProd .E7 K vPsi (vFold K vL1 c e) :=
  conj_listProd_rootProd_vPsi (fun β hβ => ⟨isRoot_of_mem_vL1 hβ, by
    have := level_of_mem_vL1 hβ
    omega⟩) c e

theorem conj_normalForm_rootProd_vPsi [CharP K 2] (c c₂ e : (Fin Tag.E7.rank → ℤ) → K) :
    vL1Prod K c * rootProd .E7 K vPsi c₂ * rootProd .E7 K vPsi e *
        (vL1Prod K c * rootProd .E7 K vPsi c₂)⁻¹ =
      rootProd .E7 K vPsi (vFold K vL1 c e) := by
  have hcomm : rootProd .E7 K vPsi c₂ * rootProd .E7 K vPsi e =
      rootProd .E7 K vPsi e * rootProd .E7 K vPsi c₂ := by
    rw [← E6Pilot.rootProd_add vPsi_comm, ← E6Pilot.rootProd_add vPsi_comm, add_comm]
  rw [← conj_vL1Prod_rootProd_vPsi]
  calc vL1Prod K c * rootProd .E7 K vPsi c₂ * rootProd .E7 K vPsi e *
        (vL1Prod K c * rootProd .E7 K vPsi c₂)⁻¹ =
      vL1Prod K c * (rootProd .E7 K vPsi c₂ * rootProd .E7 K vPsi e) *
        (rootProd .E7 K vPsi c₂)⁻¹ * (vL1Prod K c)⁻¹ := by group
    _ = vL1Prod K c * rootProd .E7 K vPsi e * (vL1Prod K c)⁻¹ := by rw [hcomm]; group

@[expose] def vKillAB (α δ ρ β : Fin Tag.E7.rank → ℤ) : Bool :=
  decide (δ ∈ vPsi) && decide (vLevel δ = 2) && decide (ρ ∈ vPsi) && decide (vLevel ρ = 3) &&
    commB α δ && decide (ρ - α ∉ vPsi) && decide (ρ - (α + δ) = β) && decide (β ∈ vL1)

@[expose] def vKillBB (α δ ρ β : Fin Tag.E7.rank → ℤ) : Bool :=
  decide (δ ∈ vPsi) && decide (vLevel δ = 2) && decide (ρ ∈ vPsi) && decide (vLevel ρ = 3) &&
    commuteB α δ && decide (ρ - α ∈ vPsi) && decide (ρ - α - δ = β) && decide (β ∈ vL1)

theorem vKillA [CharP K 2] {α : Fin Tag.E7.rank → ℤ} {c c₂ : (Fin Tag.E7.rank → ℤ) → K}
    (h : IsRoot .E7 α ∧ vLevel α = 0 ∧ pinnedX .E7 K α 1 * (vL1Prod K c * rootProd .E7 K vPsi c₂) =
      vL1Prod K c * rootProd .E7 K vPsi c₂ * pinnedX .E7 K α 1)
    {δ ρ β : Fin Tag.E7.rank → ℤ} (hb : vKillAB α δ ρ β = true) : c β = 0 := by
  obtain ⟨hα, hα0, hq⟩ := h
  simp only [vKillAB, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨hδ, hδ2⟩, hρ⟩, hρ3⟩, hαδ⟩, hρα⟩, hβe⟩, hβ⟩ := hb
  set q := vL1Prod K c * rootProd .E7 K vPsi c₂ with hqdef
  set g := pinnedX .E7 K α 1
  have hαδr : IsRoot .E7 (α + δ) := by
    have h' := hαδ
    simp only [commB, Bool.and_eq_true, bne_iff_ne] at h'
    exact isRootB_iff.1 h'.1.1.2
  have hαδ2 : vLevel (α + δ) = 2 := by rw [vLevel_add, hα0, hδ2, zero_add]
  have hαδΨ : α + δ ∈ vPsi := mem_vPsi_of_level hαδr hαδ2.ge
  have hg : g * rootProd .E7 K vPsi (Pi.single δ 1) * g⁻¹ =
      rootProd .E7 K vPsi (Pi.single δ 1) * rootProd .E7 K vPsi (Pi.single (α + δ) 1) := by
    rw [E6Pilot.rootProd_single vPsi_nodup hδ, E6Pilot.rootProd_single vPsi_nodup hαδΨ]
    have hc := commutator_pinnedX_of_commB (K := K) hαδ 1 1
    rw [commutatorElement_def, mul_one] at hc
    have hcm : Commute (pinnedX .E7 K δ 1) (pinnedX .E7 K (α + δ) 1) :=
      vPsi_comm δ hδ (α + δ) hαδΨ 1 1
    calc g * pinnedX .E7 K δ 1 * g⁻¹ =
        g * pinnedX .E7 K δ 1 * g⁻¹ * (pinnedX .E7 K δ 1)⁻¹ * pinnedX .E7 K δ 1 := by group
      _ = pinnedX .E7 K (α + δ) 1 * pinnedX .E7 K δ 1 := by rw [hc]
      _ = pinnedX .E7 K δ 1 * pinnedX .E7 K (α + δ) 1 := hcm.eq.symm
  have e := conj_comm_aux (w := rootProd .E7 K vPsi (Pi.single δ 1)) hq
  rw [hg, conj_normalForm_rootProd_vPsi, conj_rootProd_vPsi hα hα0.ge] at e
  have e' : q * (rootProd .E7 K vPsi (Pi.single δ 1) * rootProd .E7 K vPsi (Pi.single (α + δ) 1)) *
      q⁻¹ = rootProd .E7 K vPsi (vFold K vL1 c (Pi.single δ 1) +
        vFold K vL1 c (Pi.single (α + δ) 1)) := by
    rw [E6Pilot.rootProd_add vPsi_comm, ← conj_normalForm_rootProd_vPsi c c₂,
      ← conj_normalForm_rootProd_vPsi c c₂, hqdef]
    group
  rw [e'] at e
  have hρv := E6Pilot.rootProd_injective vPsi_nodup (fun _ h => pos_of_mem_vPsi h) e ρ hρ
  have hnd := vL1_check.1
  have hl : ∀ γ ∈ vL1, vLevel γ = 1 := fun γ hγ => level_of_mem_vL1 hγ
  rw [Pi.add_apply, vFold_single_apply hnd hl c hδ hδ2 hρ,
    vFold_single_apply hnd hl c hαδΨ hαδ2 hρ, conjCoeff_vPsi_apply (by rw [hα0]; norm_num) _ _ hρ,
    ite_eq_right hρα, add_zero, vFold_single_apply hnd hl c hδ hδ2 hρ] at hρv
  have hne1 : ρ ≠ δ := fun h => by rw [h] at hρ3; omega
  have hne2 : ρ ≠ α + δ := fun h => by rw [h] at hρ3; omega
  rw [Pi.single_eq_of_ne hne1, Pi.single_eq_of_ne hne2, zero_add, zero_add, hβe,
    ite_eq_left (show vLevel ρ = 3 ∧ β ∈ vL1 from ⟨hρ3, hβ⟩), add_eq_left] at hρv
  exact hρv

theorem vKillB [CharP K 2] {α : Fin Tag.E7.rank → ℤ} {c c₂ : (Fin Tag.E7.rank → ℤ) → K}
    (h : IsRoot .E7 α ∧ vLevel α = 0 ∧ pinnedX .E7 K α 1 * (vL1Prod K c * rootProd .E7 K vPsi c₂) =
      vL1Prod K c * rootProd .E7 K vPsi c₂ * pinnedX .E7 K α 1)
    {δ ρ β : Fin Tag.E7.rank → ℤ} (hb : vKillBB α δ ρ β = true) : c β = 0 := by
  obtain ⟨hα, hα0, hq⟩ := h
  simp only [vKillBB, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨hδ, hδ2⟩, hρ⟩, hρ3⟩, hαδ⟩, hρα⟩, hβe⟩, hβ⟩ := hb
  set g := pinnedX .E7 K α 1
  have hg : g * rootProd .E7 K vPsi (Pi.single δ 1) * g⁻¹ =
      rootProd .E7 K vPsi (Pi.single δ 1) := by
    rw [E6Pilot.rootProd_single vPsi_nodup hδ, (commute_pinnedX_of_commuteB hαδ 1 1).eq,
      mul_inv_cancel_right]
  have e := conj_comm_aux (w := rootProd .E7 K vPsi (Pi.single δ 1)) hq
  rw [hg, conj_normalForm_rootProd_vPsi, conj_rootProd_vPsi hα hα0.ge] at e
  have hρv := E6Pilot.rootProd_injective vPsi_nodup (fun _ h => pos_of_mem_vPsi h) e ρ hρ
  have hnd := vL1_check.1
  have hl : ∀ γ ∈ vL1, vLevel γ = 1 := fun γ hγ => level_of_mem_vL1 hγ
  have hρα3 : vLevel (ρ - α) = 3 := by
    rw [sub_eq_add_neg, vLevel_add, vLevel_neg, hα0, neg_zero, add_zero, hρ3]
  rw [conjCoeff_vPsi_apply (by rw [hα0]; norm_num) _ _ hρ, ite_eq_left hρα, one_mul,
    vFold_single_apply hnd hl c hδ hδ2 hρα] at hρv
  have hne : ρ - α ≠ δ := fun h => by rw [h] at hρα3; omega
  rw [Pi.single_eq_of_ne hne, zero_add, hβe,
    ite_eq_left (show vLevel (ρ - α) = 3 ∧ β ∈ vL1 from ⟨hρα3, hβ⟩)] at hρv
  linear_combination -hρv

theorem exists_rootProd_vPsi_of_commute [CharP K 2] {q : ModGL .E7 K}
    (hq : q ∈ parabolicRadical .E7 K vNodes)
    (hcomm : ∀ i : Fin 6, pinnedX .E7 K (vLongGen i) 1 * q = q * pinnedX .E7 K (vLongGen i) 1) :
    ∃ e, q = rootProd .E7 K vPsi e := by
  obtain ⟨c, rfl⟩ := exists_vL1Prod_mul_rootProd_vPsi hq
  have hg : ∀ i : Fin 6, IsRoot .E7 (vLongGen i) ∧ vLevel (vLongGen i) = 0 ∧
      pinnedX .E7 K (vLongGen i) 1 * (vL1Prod K c * rootProd .E7 K vPsi c) =
        vL1Prod K c * rootProd .E7 K vPsi c * pinnedX .E7 K (vLongGen i) 1 := fun i =>
    ⟨isRootB_iff.1 (vLongGen_check i).1, (vLongGen_check i).2, hcomm i⟩
  have h05 := hg 0
  have h50 := hg 1
  have h14 := hg 2
  have h41 := hg 3
  have h23 := hg 4
  have h32 := hg 5
  have k0000001 : c ![0, 0, 0, 0, 0, 0, 1] = 0 := vKillB h05 (δ := ![1, 2, 2, 3, 2, 1, 0])
    (ρ := ![2, 2, 3, 4, 3, 2, 1]) (by decide +kernel)
  have k0100000 : c ![0, 1, 0, 0, 0, 0, 0] = 0 := vKillA h05 (δ := ![0, 1, 1, 2, 1, 1, 1])
    (ρ := ![1, 2, 2, 3, 2, 2, 1]) (by decide +kernel)
  have k0000011 : c ![0, 0, 0, 0, 0, 1, 1] = 0 := vKillB h14 (δ := ![1, 2, 2, 3, 2, 1, 0])
    (ρ := ![1, 2, 3, 4, 3, 2, 1]) (by decide +kernel)
  have k0101000 : c ![0, 1, 0, 1, 0, 0, 0] = 0 := vKillA h05 (δ := ![0, 1, 1, 1, 1, 1, 1])
    (ρ := ![1, 2, 2, 3, 2, 2, 1]) (by decide +kernel)
  have k0000111 : c ![0, 0, 0, 0, 1, 1, 1] = 0 := vKillB h23 (δ := ![1, 2, 2, 3, 2, 1, 0])
    (ρ := ![1, 2, 2, 4, 3, 2, 1]) (by decide +kernel)
  have k0101100 : c ![0, 1, 0, 1, 1, 0, 0] = 0 := vKillA h05 (δ := ![0, 1, 1, 1, 1, 1, 1])
    (ρ := ![1, 2, 2, 3, 3, 2, 1]) (by decide +kernel)
  have k0111000 : c ![0, 1, 1, 1, 0, 0, 0] = 0 := vKillA h05 (δ := ![0, 1, 0, 1, 1, 1, 1])
    (ρ := ![1, 2, 2, 3, 2, 2, 1]) (by decide +kernel)
  have k0001111 : c ![0, 0, 0, 1, 1, 1, 1] = 0 := vKillB h32 (δ := ![1, 2, 2, 3, 2, 1, 0])
    (ρ := ![1, 2, 2, 3, 3, 2, 1]) (by decide +kernel)
  have k0101110 : c ![0, 1, 0, 1, 1, 1, 0] = 0 := vKillA h14 (δ := ![1, 1, 1, 1, 1, 1, 1])
    (ρ := ![1, 2, 2, 3, 3, 2, 1]) (by decide +kernel)
  have k0111100 : c ![0, 1, 1, 1, 1, 0, 0] = 0 := vKillA h05 (δ := ![0, 1, 0, 1, 1, 1, 1])
    (ρ := ![1, 2, 2, 3, 3, 2, 1]) (by decide +kernel)
  have k1111000 : c ![1, 1, 1, 1, 0, 0, 0] = 0 := vKillA h14 (δ := ![0, 1, 0, 1, 1, 1, 1])
    (ρ := ![1, 2, 2, 3, 2, 1, 1]) (by decide +kernel)
  have k0011111 : c ![0, 0, 1, 1, 1, 1, 1] = 0 := vKillB h41 (δ := ![1, 2, 2, 3, 2, 1, 0])
    (ρ := ![1, 2, 2, 3, 2, 2, 1]) (by decide +kernel)
  have k0111110 : c ![0, 1, 1, 1, 1, 1, 0] = 0 := vKillA h23 (δ := ![1, 1, 1, 1, 1, 1, 1])
    (ρ := ![1, 2, 2, 3, 2, 2, 1]) (by decide +kernel)
  have k0112100 : c ![0, 1, 1, 2, 1, 0, 0] = 0 := vKillA h05 (δ := ![0, 1, 0, 1, 1, 1, 1])
    (ρ := ![1, 2, 2, 4, 3, 2, 1]) (by decide +kernel)
  have k1111100 : c ![1, 1, 1, 1, 1, 0, 0] = 0 := vKillA h23 (δ := ![0, 1, 1, 1, 1, 1, 1])
    (ρ := ![1, 2, 2, 3, 2, 1, 1]) (by decide +kernel)
  have k0112110 : c ![0, 1, 1, 2, 1, 1, 0] = 0 := vKillA h32 (δ := ![1, 1, 1, 2, 1, 1, 1])
    (ρ := ![1, 2, 2, 3, 2, 2, 1]) (by decide +kernel)
  have k1011111 : c ![1, 0, 1, 1, 1, 1, 1] = 0 := vKillB h50 (δ := ![1, 2, 2, 3, 2, 1, 0])
    (ρ := ![1, 2, 2, 3, 2, 1, 1]) (by decide +kernel)
  have k1111110 : c ![1, 1, 1, 1, 1, 1, 0] = 0 := vKillB h50 (δ := ![1, 1, 2, 3, 2, 1, 1])
    (ρ := ![1, 2, 2, 3, 2, 1, 1]) (by decide +kernel)
  have k1112100 : c ![1, 1, 1, 2, 1, 0, 0] = 0 := vKillA h32 (δ := ![0, 1, 1, 2, 1, 1, 1])
    (ρ := ![1, 2, 2, 3, 2, 1, 1]) (by decide +kernel)
  have k0112210 : c ![0, 1, 1, 2, 2, 1, 0] = 0 := vKillB h41 (δ := ![1, 1, 2, 2, 1, 1, 1])
    (ρ := ![1, 2, 2, 3, 2, 2, 1]) (by decide +kernel)
  have k1112110 : c ![1, 1, 1, 2, 1, 1, 0] = 0 := vKillB h50 (δ := ![1, 1, 2, 2, 2, 1, 1])
    (ρ := ![1, 2, 2, 3, 2, 1, 1]) (by decide +kernel)
  have k1122100 : c ![1, 1, 2, 2, 1, 0, 0] = 0 := vKillA h41 (δ := ![0, 1, 1, 2, 2, 1, 1])
    (ρ := ![1, 2, 2, 3, 2, 1, 1]) (by decide +kernel)
  have k1112210 : c ![1, 1, 1, 2, 2, 1, 0] = 0 := vKillB h50 (δ := ![1, 1, 2, 2, 1, 1, 1])
    (ρ := ![1, 2, 2, 3, 2, 1, 1]) (by decide +kernel)
  have k1122110 : c ![1, 1, 2, 2, 1, 1, 0] = 0 := vKillB h50 (δ := ![1, 1, 1, 2, 2, 1, 1])
    (ρ := ![1, 2, 2, 3, 2, 1, 1]) (by decide +kernel)
  have k1122210 : c ![1, 1, 2, 2, 2, 1, 0] = 0 := vKillB h50 (δ := ![1, 1, 1, 2, 1, 1, 1])
    (ρ := ![1, 2, 2, 3, 2, 1, 1]) (by decide +kernel)
  have k1123210 : c ![1, 1, 2, 3, 2, 1, 0] = 0 := vKillB h50 (δ := ![1, 1, 1, 1, 1, 1, 1])
    (ρ := ![1, 2, 2, 3, 2, 1, 1]) (by decide +kernel)
  have hc : ∀ β ∈ vL1, c β = 0 := by
    intro β hβ
    iterate 25 (rcases List.mem_cons.1 hβ with rfl | hβ <;> try assumption)
    rcases List.mem_singleton.1 hβ with rfl
    assumption
  exact ⟨c, by rw [vL1Prod_eq_one hc, one_mul]⟩

end Main

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
