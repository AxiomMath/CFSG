module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Levi
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootPerfectness

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction


section Line

variable (K : Type) [Field K]

@[expose] noncomputable def e7FrameElt (F : List (Fin Tag.E7.rank → ℤ)) (d : K) :
    adjointGroup .E7 K :=
  ⟨(F.map fun σ => pinnedX .E7 K σ d).prod, list_prod_mem fun _ hx => by
    obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hx
    exact pinnedX_mem_adjointGroup _ _⟩

@[expose] noncomputable def e7FrameLine (F : List (Fin Tag.E7.rank → ℤ)) :
    Subgroup (adjointGroup .E7 K) :=
  closure (Set.range (e7FrameElt K F))

variable {K}

theorem coe_e7FrameElt (F : List (Fin Tag.E7.rank → ℤ)) (d : K) :
    (e7FrameElt K F d : ModGL .E7 K) = (F.map fun σ => pinnedX .E7 K σ d).prod :=
  rfl

theorem e7FrameElt_one (F : List (Fin Tag.E7.rank → ℤ)) : e7FrameElt K F 1 = e7FramePt K F :=
  rfl

theorem e7FrameElt_zero (F : List (Fin Tag.E7.rank → ℤ)) : e7FrameElt K F 0 = 1 := by
  apply Subtype.ext
  rw [coe_e7FrameElt, OneMemClass.coe_one]
  simp only [pinnedX_zero, List.map_const', List.prod_replicate, one_pow]

theorem e7FrameElt_mem_e7FrameLine (F : List (Fin Tag.E7.rank → ℤ)) (d : K) :
    e7FrameElt K F d ∈ e7FrameLine K F :=
  subset_closure ⟨d, rfl⟩

end Line

section LineFacts


variable {K : Type} [Field K]

theorem commute_pinnedX_of_iform_eq_zero_e7 {R : Type} [CommRing R]
    {σ σ' : Fin Tag.E7.rank → ℤ} (hσ : IsRoot .E7 σ) (hσ' : IsRoot .E7 σ')
    (h : iform σ σ' = 0) (c e : R) : Commute (pinnedX .E7 R σ c) (pinnedX .E7 R σ' e) :=
  classD4_commute_pinnedX (Or.inr (Or.inr (Or.inl rfl))) hσ hσ' h.ge c e

theorem e7FrameElt_add {F : List (Fin Tag.E7.rank → ℤ)} (hr : ∀ σ ∈ F, IsRoot .E7 σ)
    (ho : F.Pairwise fun σ σ' => iform σ σ' = 0) (d d' : K) :
    e7FrameElt K F (d + d') = e7FrameElt K F d * e7FrameElt K F d' := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_e7FrameElt]
  induction F with
  | nil => simp
  | cons a F ih =>
    rw [List.pairwise_cons] at ho
    have ha := hr a List.mem_cons_self
    have hr' : ∀ σ ∈ F, IsRoot .E7 σ := fun σ hσ => hr σ (List.mem_cons_of_mem _ hσ)
    have hcomm : Commute (pinnedX .E7 K a d') (F.map fun σ => pinnedX .E7 K σ d).prod :=
      Commute.list_prod_right _ _ fun y hy => by
        obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hy
        exact commute_pinnedX_of_iform_eq_zero_e7 ha (hr' σ hσ) (ho.1 σ hσ) d' d
    simp only [List.map_cons, List.prod_cons]
    rw [pinnedX_add, ih hr' ho.2]
    calc pinnedX .E7 K a d * pinnedX .E7 K a d' *
          ((F.map fun σ => pinnedX .E7 K σ d).prod * (F.map fun σ => pinnedX .E7 K σ d').prod)
        = pinnedX .E7 K a d * (pinnedX .E7 K a d' * (F.map fun σ => pinnedX .E7 K σ d).prod) *
          (F.map fun σ => pinnedX .E7 K σ d').prod := by group
      _ = pinnedX .E7 K a d * ((F.map fun σ => pinnedX .E7 K σ d).prod * pinnedX .E7 K a d') *
          (F.map fun σ => pinnedX .E7 K σ d').prod := by rw [hcomm.eq]
      _ = _ := by group

theorem e7FrameElt_mul_self [CharP K 2] {F : List (Fin Tag.E7.rank → ℤ)}
    (hr : ∀ σ ∈ F, IsRoot .E7 σ) (ho : F.Pairwise fun σ σ' => iform σ σ' = 0) (d : K) :
    e7FrameElt K F d * e7FrameElt K F d = 1 := by
  rw [← e7FrameElt_add hr ho, CharTwo.add_self_eq_zero, e7FrameElt_zero]

theorem mem_e7FrameLine [CharP K 2] {F : List (Fin Tag.E7.rank → ℤ)}
    (hr : ∀ σ ∈ F, IsRoot .E7 σ) (ho : F.Pairwise fun σ σ' => iform σ σ' = 0)
    {w : adjointGroup .E7 K} : w ∈ e7FrameLine K F ↔ ∃ d, e7FrameElt K F d = w := by
  constructor
  · intro hw
    induction hw using closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨0, e7FrameElt_zero F⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact ⟨c + d, e7FrameElt_add hr ho c d⟩
    | inv x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨c, (inv_eq_of_mul_eq_one_right (e7FrameElt_mul_self hr ho c)).symm⟩
  · rintro ⟨d, rfl⟩
    exact e7FrameElt_mem_e7FrameLine F d

theorem isElemAbelian_e7FrameLine [CharP K 2] {F : List (Fin Tag.E7.rank → ℤ)}
    (hr : ∀ σ ∈ F, IsRoot .E7 σ) (ho : F.Pairwise fun σ σ' => iform σ σ' = 0) :
    CFSG.Open.IsElemAbelian 2 (e7FrameLine K F) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨d, hd⟩ := (mem_e7FrameLine hr ho).1 a.2
    obtain ⟨d', hd'⟩ := (mem_e7FrameLine hr ho).1 b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hd, ← hd', ← e7FrameElt_add hr ho,
      ← e7FrameElt_add hr ho, add_comm]
  · obtain ⟨d, rfl⟩ := (mem_e7FrameLine hr ho).1 hx
    rw [sq, e7FrameElt_mul_self hr ho]

theorem e7FrameLine_le_cent {F : List (Fin Tag.E7.rank → ℤ)} (hr : ∀ σ ∈ F, IsRoot .E7 σ)
    (ho : F.Pairwise fun σ σ' => iform σ σ' = 0) :
    e7FrameLine K F ≤ Exc.cent (e7FramePt K F) := by
  rw [e7FrameLine, closure_le]
  rintro _ ⟨d, rfl⟩
  rw [SetLike.mem_coe, Exc.cent, mem_centralizer_singleton_iff, ← e7FrameElt_one,
    ← e7FrameElt_add hr ho, ← e7FrameElt_add hr ho, add_comm]

theorem e7FrameElt_injective {F : List (Fin Tag.E7.rank → ℤ)} (hne : F ≠ []) (hnd : F.Nodup)
    (hF : ∀ σ ∈ F, IsRoot .E7 σ ∧ 0 < height σ) : Function.Injective (e7FrameElt K F) := by
  intro d d' h
  have h' : (F.map fun σ => pinnedX .E7 K σ ((fun _ => d) σ)).prod =
      (F.map fun σ => pinnedX .E7 K σ ((fun _ => d') σ)).prod :=
    congrArg Subtype.val h
  obtain ⟨σ, hσ⟩ := List.exists_mem_of_ne_nil F hne
  exact pinnedX_list_prod_injective F hnd hF _ _ h' σ hσ

theorem e7FrameElt_eq_one_iff {F : List (Fin Tag.E7.rank → ℤ)} (hne : F ≠ []) (hnd : F.Nodup)
    (hF : ∀ σ ∈ F, IsRoot .E7 σ ∧ 0 < height σ) {d : K} : e7FrameElt K F d = 1 ↔ d = 0 :=
  ⟨fun h => e7FrameElt_injective hne hnd hF (h.trans (e7FrameElt_zero F).symm),
    fun h => h ▸ e7FrameElt_zero F⟩

theorem card_e7FrameLine [CharP K 2] {F : List (Fin Tag.E7.rank → ℤ)} (hne : F ≠ [])
    (hnd : F.Nodup) (hF : ∀ σ ∈ F, IsRoot .E7 σ ∧ 0 < height σ)
    (ho : F.Pairwise fun σ σ' => iform σ σ' = 0) : Nat.card (e7FrameLine K F) = Nat.card K := by
  have hr : ∀ σ ∈ F, IsRoot .E7 σ := fun σ hσ => (hF σ hσ).1
  let f : K → e7FrameLine K F := fun d => ⟨e7FrameElt K F d, e7FrameElt_mem_e7FrameLine F d⟩
  have hf : Function.Bijective f := by
    refine ⟨fun d d' h => e7FrameElt_injective hne hnd hF (congrArg Subtype.val h), fun w => ?_⟩
    obtain ⟨d, hd⟩ := (mem_e7FrameLine hr ho).1 w.2
    exact ⟨d, Subtype.ext hd⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

end LineFacts

section Scale


variable (K : Type) [Field K]

@[expose] noncomputable def e7FrameScale (F : List (Fin Tag.E7.rank → ℤ)) (s : Kˣ) :
    adjointGroup .E7 K :=
  ⟨(F.map fun σ => rootTorusSL2 .E7 K σ s).prod, list_prod_mem fun _ hx => by
    obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hx
    exact ((exceptional_Lang_root_rank_one_data .E7 K σ).2.2.2.2.2.2.1 s).1⟩

variable {K}

theorem coe_e7FrameScale (F : List (Fin Tag.E7.rank → ℤ)) (s : Kˣ) :
    (e7FrameScale K F s : ModGL .E7 K) = (F.map fun σ => rootTorusSL2 .E7 K σ s).prod :=
  rfl

theorem prod_zpow_iform_frame {F : List (Fin Tag.E7.rank → ℤ)} (hr : ∀ σ ∈ F, IsRoot .E7 σ)
    (ho : F.Pairwise fun σ σ' => iform σ σ' = 0) {α : Fin Tag.E7.rank → ℤ} (hα : α ∈ F)
    (s : Kˣ) : (F.map fun σ => s ^ (2 * iform σ α / iform σ σ)).prod = s ^ 2 := by
  induction F with
  | nil => simp at hα
  | cons a F ih =>
    rw [List.pairwise_cons] at ho
    have hr' : ∀ σ ∈ F, IsRoot .E7 σ := fun σ hσ => hr σ (List.mem_cons_of_mem _ hσ)
    have haa : iform a a = 2 :=
      EvenOddRadical.iform_self_eq_two (Or.inr (Or.inr (Or.inl rfl))) (hr a List.mem_cons_self)
    simp only [List.map_cons, List.prod_cons]
    rcases List.mem_cons.1 hα with h | hα'
    · rw [h]
      have hrest : (F.map fun σ => s ^ (2 * iform σ a / iform σ σ)).prod = 1 := by
        refine List.prod_eq_one fun x hx => ?_
        obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
        rw [iform_comm, ho.1 σ hσ, mul_zero, Int.zero_ediv, zpow_zero]
      rw [hrest, mul_one, haa]
      norm_num
    · rw [ho.1 α hα', mul_zero, Int.zero_ediv, zpow_zero, one_mul]
      exact ih hr' ho.2 hα'

theorem e7FrameScale_conj {F : List (Fin Tag.E7.rank → ℤ)} (hr : ∀ σ ∈ F, IsRoot .E7 σ)
    (ho : F.Pairwise fun σ σ' => iform σ σ' = 0) (s : Kˣ) (d : K) :
    e7FrameScale K F s * e7FrameElt K F d * (e7FrameScale K F s)⁻¹ =
      e7FrameElt K F ((s : K) ^ 2 * d) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_e7FrameScale, coe_e7FrameElt]
  set H := (F.map fun σ => rootTorusSL2 .E7 K σ s).prod with hH
  have hl : ∀ p ∈ F.map (fun σ => (σ, s)), IsRoot .E7 p.1 := by
    intro p hp
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hp
    exact hr σ hσ
  have h1 : ∀ α ∈ F, H * pinnedX .E7 K α d * H⁻¹ = pinnedX .E7 K α ((s : K) ^ 2 * d) := by
    intro α hα
    have h := list_prod_rootTorusSL2_conj_pinnedX (hr α hα) (F.map fun σ => (σ, s)) hl d
    simp only [List.map_map, Function.comp_def] at h
    rw [hH, h, prod_zpow_iform_frame hr ho hα s, Units.val_pow_eq_pow_val]
  have key : ∀ L : List (Fin Tag.E7.rank → ℤ), (∀ α ∈ L, α ∈ F) →
      H * (L.map fun α => pinnedX .E7 K α d).prod * H⁻¹ =
        (L.map fun α => pinnedX .E7 K α ((s : K) ^ 2 * d)).prod := by
    intro L hL
    induction L with
    | nil => simp
    | cons α L ih =>
      simp only [List.map_cons, List.prod_cons]
      calc H * (pinnedX .E7 K α d * (L.map fun α => pinnedX .E7 K α d).prod) * H⁻¹
          = (H * pinnedX .E7 K α d * H⁻¹) *
              (H * (L.map fun α => pinnedX .E7 K α d).prod * H⁻¹) := by group
        _ = _ := by
          rw [h1 α (hL α List.mem_cons_self), ih fun β hβ => hL β (List.mem_cons_of_mem _ hβ)]
  exact key F fun α hα => hα

theorem e7FrameScale_mem_torusGroup {F : List (Fin Tag.E7.rank → ℤ)}
    (hr : ∀ σ ∈ F, IsRoot .E7 σ) (s : Kˣ) :
    (e7FrameScale K F s : ModGL .E7 K) ∈ torusGroup .E7 K :=
  list_prod_mem fun _ hx => by
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
    exact (exceptional_Lang_root_rank_one_torus_transport .E7 K (hr σ hσ)).2.1 s

theorem odd_orderOf_e7FrameScale [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    {F : List (Fin Tag.E7.rank → ℤ)} (hr : ∀ σ ∈ F, IsRoot .E7 σ) (s : Kˣ) :
    Odd (orderOf (e7FrameScale K F s)) := by
  have h1 : e7FrameScale K F s ^ Nat.card Kˣ = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    exact pow_card_units_eq_one_of_mem_torusGroup_e7 (e7FrameScale_mem_torusGroup hr s)
  have hodd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units, hK]
    have h2 : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
    have h3 : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
    exact ⟨2 ^ (m - 1) - 1, by omega⟩
  exact hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)

end Scale

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
