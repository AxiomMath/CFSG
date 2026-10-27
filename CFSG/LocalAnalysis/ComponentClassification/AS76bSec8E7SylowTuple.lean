module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7FrameLine
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7TwoBasic
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClasses

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction

variable {K : Type} [Field K]

section Light


theorem prod_zpow_iform_frame_vec {F : List (Fin Tag.E7.rank → ℤ)} (hr : ∀ σ ∈ F, IsRoot .E7 σ)
    (ho : F.Pairwise fun σ σ' => iform σ σ' = 0) {α : Fin Tag.E7.rank → ℤ} (hα : α ∈ F)
    (s : (Fin Tag.E7.rank → ℤ) → Kˣ) :
    (F.map fun σ => s σ ^ (2 * iform σ α / iform σ σ)).prod = s α ^ 2 := by
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
      have hrest : (F.map fun σ => s σ ^ (2 * iform σ a / iform σ σ)).prod = 1 := by
        refine List.prod_eq_one fun x hx => ?_
        obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
        rw [iform_comm, ho.1 σ hσ, mul_zero, Int.zero_ediv, zpow_zero]
      rw [hrest, mul_one, haa]
      norm_num
    · rw [ho.1 α hα', mul_zero, Int.zero_ediv, zpow_zero, one_mul]
      exact ih hr' ho.2 hα'

theorem list_prod_pinnedX_single {L : List (Fin Tag.E7.rank → ℤ)} (hL : L.Nodup)
    {σ₀ : Fin Tag.E7.rank → ℤ} (hσ₀ : σ₀ ∈ L) (φ : (Fin Tag.E7.rank → ℤ) → Fin Tag.E7.rank → ℤ)
    {g : (Fin Tag.E7.rank → ℤ) → K} (hg : ∀ σ, σ ≠ σ₀ → g σ = 0) :
    (L.map fun σ => pinnedX .E7 K (φ σ) (g σ)).prod = pinnedX .E7 K (φ σ₀) (g σ₀) := by
  have hzero : ∀ L' : List (Fin Tag.E7.rank → ℤ), σ₀ ∉ L' →
      (L'.map fun σ => pinnedX .E7 K (φ σ) (g σ)).prod = 1 := by
    intro L' hL'
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
    rw [hg σ fun h => hL' (h ▸ hσ), pinnedX_zero]
  induction L with
  | nil => simp at hσ₀
  | cons a L ih =>
    rw [List.nodup_cons] at hL
    simp only [List.map_cons, List.prod_cons]
    rcases List.mem_cons.1 hσ₀ with h | h
    · rw [← h, hzero L (h ▸ hL.1), mul_one]
    · have ha : a ≠ σ₀ := fun h' => hL.1 (h' ▸ h)
      rw [hg a ha, pinnedX_zero, one_mul, ih hL.2 h]

end Light

section Tuple


theorem list_prod_pinnedX_add_vec {F : List (Fin Tag.E7.rank → ℤ)} (hr : ∀ σ ∈ F, IsRoot .E7 σ)
    (ho : F.Pairwise fun σ σ' => iform σ σ' = 0) (f g : (Fin Tag.E7.rank → ℤ) → K) :
    (F.map fun σ => pinnedX .E7 K σ (f σ + g σ)).prod =
      (F.map fun σ => pinnedX .E7 K σ (f σ)).prod *
        (F.map fun σ => pinnedX .E7 K σ (g σ)).prod := by
  induction F with
  | nil => simp
  | cons a F ih =>
    rw [List.pairwise_cons] at ho
    have ha := hr a List.mem_cons_self
    have hr' : ∀ σ ∈ F, IsRoot .E7 σ := fun σ hσ => hr σ (List.mem_cons_of_mem _ hσ)
    have hcomm : Commute (pinnedX .E7 K a (g a)) (F.map fun σ => pinnedX .E7 K σ (f σ)).prod :=
      Commute.list_prod_right _ _ fun y hy => by
        obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hy
        exact commute_pinnedX_of_iform_eq_zero_e7 ha (hr' σ hσ) (ho.1 σ hσ) (g a) (f σ)
    simp only [List.map_cons, List.prod_cons]
    rw [pinnedX_add, ih hr' ho.2]
    calc pinnedX .E7 K a (f a) * pinnedX .E7 K a (g a) *
          ((F.map fun σ => pinnedX .E7 K σ (f σ)).prod *
            (F.map fun σ => pinnedX .E7 K σ (g σ)).prod)
        = pinnedX .E7 K a (f a) *
            (pinnedX .E7 K a (g a) * (F.map fun σ => pinnedX .E7 K σ (f σ)).prod) *
          (F.map fun σ => pinnedX .E7 K σ (g σ)).prod := by group
      _ = pinnedX .E7 K a (f a) *
            ((F.map fun σ => pinnedX .E7 K σ (f σ)).prod * pinnedX .E7 K a (g a)) *
          (F.map fun σ => pinnedX .E7 K σ (g σ)).prod := by rw [hcomm.eq]
      _ = _ := by group

theorem exists_conj_e7FramePt_eq_vec [Finite K] [CharP K 2] {F : List (Fin Tag.E7.rank → ℤ)}
    (hr : ∀ σ ∈ F, IsRoot .E7 σ) (ho : F.Pairwise fun σ σ' => iform σ σ' = 0)
    {a : (Fin Tag.E7.rank → ℤ) → K} (ha : ∀ σ ∈ F, a σ ≠ 0) :
    ∃ h : adjointGroup .E7 K, ((h * e7FramePt K F * h⁻¹ : adjointGroup .E7 K) : ModGL .E7 K) =
      (F.map fun σ => pinnedX .E7 K σ (a σ)).prod := by
  have hsq : ∀ σ, ∃ r : Kˣ, a σ ≠ 0 → (r : K) ^ 2 = a σ := fun σ => by
    by_cases h0 : a σ = 0
    · exact ⟨1, fun h => absurd h0 h⟩
    · obtain ⟨r, hr2⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (a σ)
      have hr0 : r ≠ 0 := by
        rintro rfl
        exact h0 (by rw [hr2, mul_zero])
      exact ⟨Units.mk0 r hr0, fun _ => by rw [Units.val_mk0, sq, ← hr2]⟩
  choose s hs using hsq
  set H := (F.map fun σ => rootTorusSL2 .E7 K σ (s σ)).prod with hH
  have hHmem : H ∈ adjointGroup .E7 K := list_prod_mem fun _ hx => by
    obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hx
    exact ((exceptional_Lang_root_rank_one_data .E7 K σ).2.2.2.2.2.2.1 (s σ)).1
  have hl : ∀ p ∈ F.map (fun σ => (σ, s σ)), IsRoot .E7 p.1 := by
    intro p hp
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hp
    exact hr σ hσ
  have h1 : ∀ α ∈ F, H * pinnedX .E7 K α 1 * H⁻¹ = pinnedX .E7 K α (a α) := by
    intro α hα
    have h := list_prod_rootTorusSL2_conj_pinnedX (hr α hα) (F.map fun σ => (σ, s σ)) hl 1
    simp only [List.map_map, Function.comp_def] at h
    rw [hH, h, prod_zpow_iform_frame_vec hr ho hα s, Units.val_pow_eq_pow_val, hs α (ha α hα),
      mul_one]
  have key : ∀ L : List (Fin Tag.E7.rank → ℤ), (∀ α ∈ L, α ∈ F) →
      H * (L.map fun α => pinnedX .E7 K α 1).prod * H⁻¹ =
        (L.map fun α => pinnedX .E7 K α (a α)).prod := by
    intro L hL
    induction L with
    | nil => simp
    | cons α L ih =>
      simp only [List.map_cons, List.prod_cons]
      calc H * (pinnedX .E7 K α 1 * (L.map fun α => pinnedX .E7 K α 1).prod) * H⁻¹
          = (H * pinnedX .E7 K α 1 * H⁻¹) *
              (H * (L.map fun α => pinnedX .E7 K α 1).prod * H⁻¹) := by group
        _ = _ := by
          rw [h1 α (hL α List.mem_cons_self), ih fun β hβ => hL β (List.mem_cons_of_mem _ hβ)]
  refine ⟨⟨H, hHmem⟩, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact key F fun α hα => hα

theorem e7FrameElt_single_mem_of_tuple [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K)
    {F : List (Fin Tag.E7.rank → ℤ)} (hFr : ∀ σ ∈ F, IsRoot .E7 σ) (hFnd : F.Nodup)
    (hFo : F.Pairwise fun σ σ' => iform σ σ' = 0) (ω : List (Fin Tag.E7.rank))
    (hTF : ∀ t ∈ F.map (fun σ => ω.foldr (reflect .E7) σ), ∀ s ∈ F,
      t ≠ -s ∧ ¬ IsRoot .E7 (t + s))
    {N : Subgroup (adjointGroup .E7 K)}
    (hN : ∀ b : adjointGroup .E7 K, b * e7FramePt K F * b⁻¹ ∈ Exc.cent (e7FramePt K F) →
      b * e7FramePt K F * b⁻¹ ∈ N)
    {t : Fin Tag.E7.rank → ℤ} (ht : t ∈ F.map (fun σ => ω.foldr (reflect .E7) σ)) (c : K) :
    e7FrameElt K [t] c ∈ N := by
  obtain ⟨σ₀, hσ₀, rfl⟩ := List.mem_map.1 ht
  set w := (coxeterSystem .E7).wordProd ω with hw
  set n : adjointGroup .E7 K :=
    ⟨canonicalRep (coxeterSystem .E7) K w, canonicalRep_mem_adjointGroup _ K w⟩ with hn
  have hfoldr : ∀ σ, ω.foldr (reflect .E7) σ = w • σ := fun σ =>
    (wordProd_smul_eq_foldr ω σ).symm
  have hconj : ∀ a : (Fin Tag.E7.rank → ℤ) → K,
      (n : ModGL .E7 K) * (F.map fun σ => pinnedX .E7 K σ (a σ)).prod * (n : ModGL .E7 K)⁻¹ =
        (F.map fun σ => pinnedX .E7 K (ω.foldr (reflect .E7) σ) (a σ)).prod := by
    intro a
    rw [E6Pilot.canonicalRep_mul_list_prod_mul_inv_of_charTwo (K := K) w hFr a]
    simp only [hfoldr]
  have hmem : ∀ a : (Fin Tag.E7.rank → ℤ) → K, (∀ σ ∈ F, a σ ≠ 0) →
      ∃ y ∈ N, (y : ModGL .E7 K) =
        (n : ModGL .E7 K) * (F.map fun σ => pinnedX .E7 K σ (a σ)).prod * (n : ModGL .E7 K)⁻¹ := by
    intro a ha
    obtain ⟨h, hh⟩ := exists_conj_e7FramePt_eq_vec hFr hFo ha
    have hb : (((n * h) * e7FramePt K F * (n * h)⁻¹ : adjointGroup .E7 K) : ModGL .E7 K) =
        (n : ModGL .E7 K) * (F.map fun σ => pinnedX .E7 K σ (a σ)).prod *
          (n : ModGL .E7 K)⁻¹ := by
      have e1 : (n * h) * e7FramePt K F * (n * h)⁻¹ = n * (h * e7FramePt K F * h⁻¹) * n⁻¹ := by
        group
      rw [e1, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hh]
    refine ⟨_, hN (n * h) ?_, hb⟩
    rw [Exc.cent, mem_centralizer_singleton_iff]
    apply Subtype.ext
    show (((n * h) * e7FramePt K F * (n * h)⁻¹ : adjointGroup .E7 K) : ModGL .E7 K) *
        (e7FramePt K F : ModGL .E7 K) = (e7FramePt K F : ModGL .E7 K) *
          (((n * h) * e7FramePt K F * (n * h)⁻¹ : adjointGroup .E7 K) : ModGL .E7 K)
    rw [hb, hconj a]
    change _ * (F.map fun σ => pinnedX .E7 K σ 1).prod = (F.map fun σ => pinnedX .E7 K σ 1).prod * _
    refine (Commute.list_prod_left _ _ fun x hx => Commute.list_prod_right _ _ fun y hy => ?_).eq
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
    obtain ⟨hne, hnr⟩ := hTF _ (List.mem_map_of_mem hσ) s hs
    have hroot : IsRoot .E7 (ω.foldr (reflect .E7) σ) := by
      rw [hfoldr]
      exact CFSG.LieType.Chevalley.IsRoot.smul (hFr σ hσ) w
    exact commute_pinnedX_of_oddDeriv hroot (hFr s hs) hne hnr (a σ) 1
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [e7FrameElt_zero]
    exact one_mem N
  have hex : ∃ e : K, e ≠ 0 ∧ e ≠ c := by
    by_contra hcon
    push Not at hcon
    have hsurj : Function.Surjective (fun b : Bool => if b then c else (0 : K)) := by
      intro x
      by_cases hx : x = 0
      · exact ⟨false, by simp [hx]⟩
      · exact ⟨true, by simp [hcon x hx]⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    omega
  obtain ⟨e, he0, hec⟩ := hex
  have hce : c + e ≠ 0 := fun h => hec (by
    have h' := eq_neg_of_add_eq_zero_right h
    rwa [CharTwo.neg_eq] at h')
  set a : (Fin Tag.E7.rank → ℤ) → K := fun σ => if σ = σ₀ then c + e else 1 with ha
  set a' : (Fin Tag.E7.rank → ℤ) → K := fun σ => if σ = σ₀ then e else 1 with ha'
  set δ : (Fin Tag.E7.rank → ℤ) → K := fun σ => if σ = σ₀ then c else 0 with hδ
  have hanz : ∀ σ ∈ F, a σ ≠ 0 := fun σ _ => by
    simp only [ha]
    split_ifs
    · exact hce
    · exact one_ne_zero
  have ha'nz : ∀ σ ∈ F, a' σ ≠ 0 := fun σ _ => by
    simp only [ha']
    split_ifs
    · exact he0
    · exact one_ne_zero
  obtain ⟨y, hyN, hy⟩ := hmem a hanz
  obtain ⟨y', hy'N, hy'⟩ := hmem a' ha'nz
  have hsplit : (F.map fun σ => pinnedX .E7 K σ (a σ)).prod =
      (F.map fun σ => pinnedX .E7 K σ (a' σ)).prod *
        (F.map fun σ => pinnedX .E7 K σ (δ σ)).prod := by
    rw [← list_prod_pinnedX_add_vec hFr hFo]
    congr 1
    refine List.map_congr_left fun σ _ => ?_
    simp only [ha, ha', hδ]
    split_ifs
    · rw [add_comm]
    · rw [add_zero]
  have hδprod : (F.map fun σ => pinnedX .E7 K (ω.foldr (reflect .E7) σ) (δ σ)).prod =
      pinnedX .E7 K (ω.foldr (reflect .E7) σ₀) c := by
    rw [list_prod_pinnedX_single hFnd hσ₀ _ fun σ hσ => by simp [hδ, hσ]]
    simp [hδ]
  have hfinal : y'⁻¹ * y = e7FrameElt K [ω.foldr (reflect .E7) σ₀] c := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hy, hy', hsplit, coe_e7FrameElt, List.map_singleton,
      List.prod_singleton, ← hδprod, ← hconj δ]
    group
  rw [← hfinal]
  exact mul_mem (inv_mem hy'N) hyN

end Tuple

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
