module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFlagSplitting
public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open Module Submodule

universe u

variable {p f : ℕ} {K : Type*} [Field K]

section Cons

@[expose] def shiftIdx {r ε : ℕ} : HypIndex r ε → HypIndex (r + 1) ε
  | .inl i => .inl i.succ
  | .inr (.inl l) => .inr (.inl l)
  | .inr (.inr i) => .inr (.inr i.succ)

theorem shiftIdx_injective {r ε : ℕ} : Function.Injective (shiftIdx (r := r) (ε := ε)) := by
  intro x y hxy
  rcases x with i | l | i <;> rcases y with i' | l' | i' <;> simp_all [shiftIdx]

theorem hypPartner_shiftIdx {r ε : ℕ} (x : HypIndex r ε) :
    hypPartner (shiftIdx x) = shiftIdx (hypPartner x) := by
  rcases x with i | l | i <;> rfl

theorem shiftIdx_ne_inl_zero {r ε : ℕ} (x : HypIndex r ε) : shiftIdx x ≠ .inl 0 := by
  rcases x with i | l | i <;> simp [shiftIdx, Fin.succ_ne_zero]

theorem shiftIdx_ne_inr_inr_zero {r ε : ℕ} (x : HypIndex r ε) :
    shiftIdx x ≠ .inr (.inr 0) := by
  rcases x with i | l | i <;> simp [shiftIdx, Fin.succ_ne_zero]

theorem fullPos_shiftIdx {r ε : ℕ} (x : HypIndex r ε) :
    fullPos (shiftIdx x) = fullPos x + 1 := by
  rcases x with ⟨i, hi⟩ | ⟨l, hl⟩ | ⟨i, hi⟩ <;> simp [shiftIdx] <;> omega

theorem hypIndex_cases {r ε : ℕ} (x : HypIndex (r + 1) ε) :
    x = .inl 0 ∨ x = .inr (.inr 0) ∨ ∃ x', x = shiftIdx x' := by
  rcases x with i | l | i
  · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨.inl i', rfl⟩)
  · exact Or.inr (Or.inr ⟨.inr (.inl l), rfl⟩)
  · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨.inr (.inr i'), rfl⟩)

variable {V : Type*}

@[expose] def consHyp {r ε : ℕ} (v w : V) (u : HypIndex r ε → V) : HypIndex (r + 1) ε → V
  | .inl i => Fin.cases v (fun i' => u (.inl i')) i
  | .inr (.inl l) => u (.inr (.inl l))
  | .inr (.inr i) => Fin.cases w (fun i' => u (.inr (.inr i'))) i

theorem consHyp_inl_zero {r ε : ℕ} (v w : V) (u : HypIndex r ε → V) :
    consHyp v w u (.inl 0) = v :=
  rfl

theorem consHyp_inr_inr_zero {r ε : ℕ} (v w : V) (u : HypIndex r ε → V) :
    consHyp v w u (.inr (.inr 0)) = w :=
  rfl

theorem consHyp_shiftIdx {r ε : ℕ} (v w : V) (u : HypIndex r ε → V) (x : HypIndex r ε) :
    consHyp v w u (shiftIdx x) = u x := by
  rcases x with i | l | i <;> rfl

variable [AddCommGroup V] [Module K V]

theorem consHyp_gram {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K} {r ε : ℕ} {v w : V}
    {u : HypIndex r ε → V} (hvv : B v v = 0) (hvw : B v w = 1) (hwv : B w v = 1)
    (hww : B w w = 0) (hu : ∀ x y, B (u x) (u y) = hypGram r ε K x y)
    (hvu : ∀ x, B v (u x) = 0) (hwu : ∀ x, B w (u x) = 0) (huv : ∀ x, B (u x) v = 0)
    (huw : ∀ x, B (u x) w = 0) :
    ∀ x y, B (consHyp v w u x) (consHyp v w u y) = hypGram (r + 1) ε K x y := by
  intro x y
  rw [hypGram_apply]
  rcases hypIndex_cases x with rfl | rfl | ⟨x', rfl⟩ <;>
    rcases hypIndex_cases y with rfl | rfl | ⟨y', rfl⟩
  · simp [consHyp_inl_zero, hvv]
  · simp [consHyp_inl_zero, consHyp_inr_inr_zero, hvw]
  · simp [consHyp_inl_zero, consHyp_shiftIdx, hvu, shiftIdx_ne_inr_inr_zero]
  · simp [consHyp_inl_zero, consHyp_inr_inr_zero, hwv]
  · simp [consHyp_inr_inr_zero, hww]
  · simp [consHyp_inr_inr_zero, consHyp_shiftIdx, hwu, shiftIdx_ne_inl_zero]
  · rw [consHyp_shiftIdx, consHyp_inl_zero, huv, hypPartner_shiftIdx]
    simp [(shiftIdx_ne_inl_zero _).symm]
  · rw [consHyp_shiftIdx, consHyp_inr_inr_zero, huw, hypPartner_shiftIdx]
    simp [(shiftIdx_ne_inr_inr_zero _).symm]
  · rw [consHyp_shiftIdx, consHyp_shiftIdx, hu, hypGram_apply, hypPartner_shiftIdx]
    simp only [shiftIdx_injective.eq_iff]

theorem exists_span_image_sup {ι : Type*} {W : ι → V} {X Y : Submodule K V}
    (hX : ∃ s, X = span K (W '' s)) (hY : ∃ t, Y = span K (W '' t)) :
    ∃ s, X ⊔ Y = span K (W '' s) := by
  obtain ⟨s, rfl⟩ := hX
  obtain ⟨t, rfl⟩ := hY
  exact ⟨s ∪ t, by rw [Set.image_union, span_union]⟩

end Cons

theorem exists_common_witt_basis (h : UnitaryFieldData p f K) (ε : ℕ) (hε : ε ≤ 1) :
    ∀ (r : ℕ) {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      {B : V →ₛₗ[h.bar] V →ₗ[K] K}, B.IsSymm → B.SeparatingLeft →
      finrank K V = 2 * r + ε → ∀ F G : ℕ → Submodule K V,
      IsSelfDualFlag B (2 * r + ε) F → IsSelfDualFlag B (2 * r + ε) G →
      ∃ w : Basis (HypIndex r ε) K V, (∀ x y, B (w x) (w y) = hypGram r ε K x y) ∧
        (∀ i ≤ 2 * r + ε, F i = span K (w '' {x | fullPos x < i})) ∧
        ∀ i ≤ 2 * r + ε, ∃ s : Set (HypIndex r ε), G i = span K (w '' s) := by
  intro r
  induction r with
  | zero =>
    intro V _ _ _ B hB hBl hn F G hF hG
    obtain ⟨w, hw⟩ := exists_hypBasis h hB hBl hn
    have hempty : {x : HypIndex 0 ε | fullPos x < 0} = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx => Nat.not_lt_zero _ hx
    have huniv : {x : HypIndex 0 ε | fullPos x < 2 * 0 + ε} = Set.univ :=
      Set.eq_univ_of_forall fun x => fullPos_lt x
    refine ⟨w, hw, fun i hi => ?_, fun i hi => ?_⟩
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [hF.zero, hempty, Set.image_empty, span_empty]
      · rw [show i = 2 * 0 + ε by omega, hF.top hn, huniv, Set.image_univ, w.span_eq]
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact ⟨∅, by rw [hG.zero, Set.image_empty, span_empty]⟩
      · exact ⟨Set.univ, by rw [show i = 2 * 0 + ε by omega, hG.top hn, Set.image_univ,
          w.span_eq]⟩
  | succ r ih =>
    intro V _ _ _ B hB hBl hn F G hF hG
    classical
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := F 1) fun h0 => by
      have h1 := hF.1 1 (by omega)
      rw [h0, finrank_bot] at h1
      exact zero_ne_one h1
    have hexj : ∃ j, v ∈ G j := ⟨2 * (r + 1) + ε, by rw [hG.top hn]; exact mem_top⟩
    obtain ⟨j, hj, hjmin⟩ : ∃ j, v ∈ G j ∧ ∀ i < j, v ∉ G i :=
      ⟨Nat.find hexj, Nat.find_spec hexj, fun i hi => Nat.find_min hexj hi⟩
    obtain ⟨-, ⟨w, hwk, hvw, hww⟩, hrest⟩ :=
      unitary_two_selfdual_flag_splitting h hB hBl hn (by omega) hF hG hv hv0 hj hjmin
    obtain ⟨-, -, -, -, hsplitF, hsplitG, hHF, hHG, hsep, hdimP, F', G', hF', hG', hEF, hEG⟩ :=
      hrest w hwk hvw hww
    have e2 : 2 * (r + 1) + ε - 2 = 2 * r + ε := by omega
    rw [e2] at hdimP hF' hG'
    obtain ⟨w', hw', hF'w, hG'w⟩ := ih (hB.domRestrict _) hsep hdimP F' G' hF' hG'
    have hvv : B v v = 0 := hF.apply_eq_zero (show 1 + 1 ≤ 2 * (r + 1) + ε by omega) hv hv
    have hwv : B w v = 1 := by rw [← hB.eq v w, hvw, map_one]
    obtain ⟨u, hu_def⟩ : ∃ u : HypIndex r ε → V, u = fun x => (w' x : V) := ⟨_, rfl⟩
    have hux : ∀ x, u x = (w' x : V) := fun x => by rw [hu_def]
    have hvu : ∀ x, B v (u x) = 0 := fun x => by
      rw [hux]
      exact (mem_orthogonalBilin.mp (w' x).2) v (subset_span (by simp))
    have hwu : ∀ x, B w (u x) = 0 := fun x => by
      rw [hux]
      exact (mem_orthogonalBilin.mp (w' x).2) w (subset_span (by simp))
    have hc := consHyp_gram hvv hvw hwv hww (u := u) (fun x y => by rw [hux, hux]; exact hw' x y)
      hvu hwu (fun x => by rw [← hB.eq v, hvu, map_zero])
      (fun x => by rw [← hB.eq w, hwu, map_zero])
    refine ⟨basisOfHypGram (consHyp v w u) hc hn, fun x y => by rw [coe_basisOfHypGram, hc],
      fun i hi => ?_, fun i hi => ?_⟩
    ·
      have hd : dedupIdx 1 (2 * (r + 1) + ε) i ≤ 2 * r + ε := by
        unfold dedupIdx
        split_ifs <;> omega
      rw [coe_basisOfHypGram]
      apply le_antisymm
      · rw [hsplitF i hi, hHF i hi]
        refine sup_le (sup_le ?_ ?_) ?_
        · split_ifs with h1
          · rw [span_singleton_le_iff_mem]
            refine subset_span ⟨.inl 0, ?_, consHyp_inl_zero v w u⟩
            change fullPos (.inl 0 : HypIndex (r + 1) ε) < i
            rw [fullPos_inl, Fin.val_zero]
            omega
          · exact bot_le
        · split_ifs with h1
          · rw [span_singleton_le_iff_mem]
            refine subset_span ⟨.inr (.inr 0), ?_, consHyp_inr_inr_zero v w u⟩
            change fullPos (.inr (.inr 0) : HypIndex (r + 1) ε) < i
            rw [fullPos_inr_inr, Fin.val_zero]
            omega
          · exact bot_le
        · rw [inf_comm, ← map_comap_subtype, hEF i hi, hF'w _ hd, map_span, Set.image_image]
          refine span_mono ?_
          rintro _ ⟨x', hx', rfl⟩
          refine ⟨shiftIdx x', ?_, by simp only [consHyp_shiftIdx, hux, subtype_apply]⟩
          change fullPos (shiftIdx x') < i
          have hx'' : fullPos x' < dedupIdx 1 (2 * (r + 1) + ε) i := hx'
          rw [fullPos_shiftIdx]
          unfold dedupIdx at hx''
          split_ifs at hx'' <;> omega
      · rw [span_le]
        rintro _ ⟨x, hx, rfl⟩
        have hx' : fullPos x < i := hx
        rcases hypIndex_cases x with rfl | rfl | ⟨x', rfl⟩
        · rw [fullPos_inl, Fin.val_zero] at hx'
          rw [SetLike.mem_coe, consHyp_inl_zero]
          exact hF.le (by omega) hi hv
        · rw [fullPos_inr_inr, Fin.val_zero] at hx'
          rw [SetLike.mem_coe, show i = 2 * (r + 1) + ε by omega, hF.top hn]
          exact mem_top
        · rw [fullPos_shiftIdx] at hx'
          rw [SetLike.mem_coe, consHyp_shiftIdx, hux]
          have hmem : w' x' ∈ F' (dedupIdx 1 (2 * (r + 1) + ε) i) := by
            rw [hF'w _ hd]
            refine subset_span ⟨x', ?_, rfl⟩
            change fullPos x' < dedupIdx 1 (2 * (r + 1) + ε) i
            have := fullPos_lt x'
            unfold dedupIdx
            split_ifs <;> omega
          rw [← hEF i hi] at hmem
          exact hmem
    ·
      have hd : dedupIdx j (2 * (r + 1) + ε + 1 - j) i ≤ 2 * r + ε := by
        have hj1 : 1 ≤ j := by
          by_contra hj0
          obtain rfl : j = 0 := by omega
          rw [hG.zero, mem_bot] at hj
          exact hv0 hj
        have hjn : j ≤ 2 * (r + 1) + ε := by
          by_contra hjn
          exact hjmin (2 * (r + 1) + ε) (by omega) (by rw [hG.top hn]; exact mem_top)
        unfold dedupIdx
        split_ifs <;> omega
      obtain ⟨s, hs⟩ := hG'w _ hd
      rw [hsplitG i hi, hHG i hi, coe_basisOfHypGram]
      refine exists_span_image_sup (exists_span_image_sup ?_ ?_) ⟨shiftIdx '' s, ?_⟩
      · split_ifs
        · exact ⟨{.inl 0}, by rw [Set.image_singleton, consHyp_inl_zero]⟩
        · exact ⟨∅, by rw [Set.image_empty, span_empty]⟩
      · split_ifs
        · exact ⟨{.inr (.inr 0)}, by rw [Set.image_singleton, consHyp_inr_inr_zero]⟩
        · exact ⟨∅, by rw [Set.image_empty, span_empty]⟩
      · rw [inf_comm, ← map_comap_subtype, hEG i hi, hs, map_span, Set.image_image,
          Set.image_image]
        congr 1
        exact Set.image_congr fun x _ => by simp only [consHyp_shiftIdx, hux, subtype_apply]

theorem unitary_common_Witt_flag_basis (h : UnitaryFieldData p f K) {V : Type u}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {n : ℕ} (hn : finrank K V = n)
    {F G : ℕ → Submodule K V} (hF : IsSelfDualFlag B n F) (hG : IsSelfDualFlag B n G) :
    ∃ w : Basis (HypIndex (n / 2) (n - 2 * (n / 2))) K V,
      (∀ x y, B (w x) (w y) = hypGram (n / 2) (n - 2 * (n / 2)) K x y) ∧
      (∀ i ≤ n, F i = span K (w '' {x | fullPos x < i})) ∧
      ∀ i ≤ n, ∃ s : Set (HypIndex (n / 2) (n - 2 * (n / 2))), G i = span K (w '' s) := by
  have e : 2 * (n / 2) + (n - 2 * (n / 2)) = n := by omega
  obtain ⟨w, hw, hFw, hGw⟩ := exists_common_witt_basis h (n - 2 * (n / 2)) (by omega) (n / 2)
    hB hBl (by rw [hn, e]) F G (by rw [e]; exact hF) (by rw [e]; exact hG)
  exact ⟨w, hw, fun i hi => hFw i (by omega), fun i hi => hGw i (by omega)⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
