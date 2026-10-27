module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Data.SetLike.Fintype

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem aor_exists_finset_closure_eq_of_isCyclic {G : Type*} [Group G] (H : Subgroup G)
    [IsCyclic H] : ∃ s : Finset G, s.card ≤ 1 ∧ Subgroup.closure (s : Set G) = H := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  refine ⟨{(g : G)}, by simp, le_antisymm ?_ ?_⟩
  · rw [Subgroup.closure_le, Finset.coe_singleton, Set.singleton_subset_iff]
    exact g.2
  · intro h hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨h, hh⟩)
    rw [Finset.coe_singleton]
    have : (h : G) = (g : G) ^ k := by rw [← Subgroup.coe_zpow, hk]
    rw [this]
    exact zpow_mem (Subgroup.subset_closure (Set.mem_singleton _)) k

private theorem aor_exists_finset_closure_eq_of_map {G G' : Type*} [Group G] [Group G']
    (f : G →* G') (H : Subgroup G) {a b : ℕ} {s : Finset G'} (hs : s.card ≤ a)
    (hsH : Subgroup.closure (s : Set G') = H.map f) {r : Finset G} (hr : r.card ≤ b)
    (hrH : Subgroup.closure (r : Set G) = H ⊓ f.ker) :
    ∃ u : Finset G, u.card ≤ a + b ∧ Subgroup.closure (u : Set G) = H := by
  classical
  have hpre : ∀ y : G', y ∈ s → ∃ x : G, x ∈ H ∧ f x = y := by
    intro y hy
    have : y ∈ H.map f := hsH ▸ Subgroup.subset_closure hy
    obtain ⟨x, hx, hxy⟩ := this
    exact ⟨x, hx, hxy⟩
  let g : G' → G := fun y => if hy : y ∈ s then Classical.choose (hpre y hy) else 1
  have hgH : ∀ y (hy : y ∈ s), g y ∈ H := by
    intro y hy
    have : g y = Classical.choose (hpre y hy) := by simp only [g, dif_pos hy]
    rw [this]
    exact (Classical.choose_spec (hpre y hy)).1
  have hgf : ∀ y (hy : y ∈ s), f (g y) = y := by
    intro y hy
    have : g y = Classical.choose (hpre y hy) := by simp only [g, dif_pos hy]
    rw [this]
    exact (Classical.choose_spec (hpre y hy)).2
  have hgle : Subgroup.closure ((s.image g : Finset G) : Set G) ≤ H := by
    rw [Subgroup.closure_le, Finset.coe_image]
    rintro _ ⟨y, hy, rfl⟩
    exact hgH y hy
  refine ⟨s.image g ∪ r, (Finset.card_union_le _ _).trans
    (add_le_add (Finset.card_image_le.trans hs) hr), le_antisymm ?_ ?_⟩
  · rw [Subgroup.closure_le, Finset.coe_union]
    rintro x (hx | hx)
    · exact hgle (Subgroup.subset_closure hx)
    · have : x ∈ H ⊓ f.ker := hrH ▸ Subgroup.subset_closure hx
      exact this.1
  · intro h hh
    have himg : f '' ((s.image g : Finset G) : Set G) = (s : Set G') := by
      rw [Finset.coe_image, ← Set.image_comp]
      ext y
      constructor
      · rintro ⟨y', hy', rfl⟩
        rw [Function.comp_apply, hgf y' hy']
        exact hy'
      · intro hy
        exact ⟨y, hy, hgf y hy⟩
    have h1 : f h ∈ (Subgroup.closure ((s.image g : Finset G) : Set G)).map f := by
      rw [MonoidHom.map_closure, himg, hsH]
      exact ⟨h, hh, rfl⟩
    obtain ⟨w, hw, hwf⟩ := h1
    have hk : w⁻¹ * h ∈ Subgroup.closure (r : Set G) := by
      rw [hrH]
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hgle hw)) hh, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwf, inv_mul_cancel]
    rw [show h = w * (w⁻¹ * h) by group]
    refine mul_mem (Subgroup.closure_mono ?_ hw) (Subgroup.closure_mono ?_ hk)
    · rw [Finset.coe_union]
      exact Set.subset_union_left
    · rw [Finset.coe_union]
      exact Set.subset_union_right

theorem aor_gen_log {S : Type} [Group S] [Finite S] (P : Subgroup S) :
    ∃ s : Finset S, s.card ≤ Nat.log 2 (Nat.card P) ∧ Subgroup.closure (s : Set S) = P := by
  classical
  haveI : Fintype S := Fintype.ofFinite S
  have key : ∀ n : ℕ, ∀ P : Subgroup S, Nat.card P = n →
      ∃ s : Finset S, s.card ≤ Nat.log 2 (Nat.card P) ∧
        Subgroup.closure (s : Set S) = P := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih P hP
    by_cases hbot : P = ⊥
    · subst hbot
      exact ⟨∅, by simp, by simp⟩
    · have hne : (Finset.univ.filter (fun M : Subgroup S => M < P)).Nonempty := by
        refine ⟨⊥, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        exact bot_lt_iff_ne_bot.mpr hbot
      obtain ⟨M, hMmax⟩ := Finset.exists_maximal hne
      have hMlt : M < P := (Finset.mem_filter.mp hMmax.1).2
      have hMle : M ≤ P := hMlt.le
      have hnotle : ¬ P ≤ M := fun hPM => hMlt.ne (le_antisymm hMle hPM)
      obtain ⟨g, hgP, hgM⟩ :=
        Set.not_subset.mp (show ¬ (P : Set S) ⊆ (M : Set S) from hnotle)
      have hle : M ⊔ Subgroup.zpowers g ≤ P :=
        sup_le hMle (Subgroup.zpowers_le.mpr hgP)
      have hnotlt : ¬ M ⊔ Subgroup.zpowers g < P := by
        intro hlt
        have hmem : M ⊔ Subgroup.zpowers g ∈
            Finset.univ.filter (fun M : Subgroup S => M < P) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
        have hle' : M ⊔ Subgroup.zpowers g ≤ M := hMmax.2 hmem le_sup_left
        have heq : M ⊔ Subgroup.zpowers g = M := le_antisymm hle' le_sup_left
        exact hgM (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
      have hsup : M ⊔ Subgroup.zpowers g = P := eq_of_le_of_not_lt hle hnotlt
      have hle_card : Nat.card M ≤ Nat.card P := Subgroup.card_le_of_le hMle
      have hne_card : Nat.card M ≠ Nat.card P := by
        intro hc
        exact hMlt.ne (Subgroup.eq_of_le_of_card_ge hMle (le_of_eq hc.symm))
      have hcardlt : Nat.card M < Nat.card P := lt_of_le_of_ne hle_card hne_card
      rw [hP] at hcardlt
      obtain ⟨t, htcard, htcl⟩ := ih (Nat.card M) hcardlt M rfl
      have hdvd : Nat.card M ∣ Nat.card P := Subgroup.card_dvd_of_le hMle
      obtain ⟨c, hc⟩ := hdvd
      have hc2 : 2 ≤ c := by
        rcases c with _ | _ | c
        · exact absurd (by rw [hc, mul_zero]) (Nat.card_pos (α := P)).ne'
        · exact absurd (by rw [hc, zero_add, mul_one]) hne_card
        · omega
      have h2card : Nat.card M * 2 ≤ Nat.card P := by
        rw [hc]
        exact Nat.mul_le_mul_left _ hc2
      have hlog : Nat.log 2 (Nat.card M) + 1 ≤ Nat.log 2 (Nat.card P) := by
        rw [← Nat.log_mul_base (show 1 < 2 by norm_num) (Nat.card_pos (α := M)).ne']
        exact Nat.log_mono_right h2card
      have hcl : Subgroup.closure ((insert g t : Finset S) : Set S) = P := by
        have hcoe : ((insert g t : Finset S) : Set S) = ({g} : Set S) ∪ (t : Set S) := by
          rw [Finset.coe_insert, Set.insert_eq]
        rw [hcoe, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, htcl, sup_comm, hsup]
      refine ⟨insert g t, ?_, hcl⟩
      have h1 : (insert g t).card ≤ t.card + 1 := Finset.card_insert_le g t
      omega
  exact key (Nat.card P) P rfl

theorem aor_gen_of_card_le {S : Type} [Group S] [Finite S] {k : ℕ} (h : Nat.card S ≤ 2 ^ k)
    (P : Subgroup S) : ∃ s : Finset S, s.card ≤ k ∧ Subgroup.closure (s : Set S) = P := by
  obtain ⟨s, hs, hsP⟩ := aor_gen_log P
  refine ⟨s, hs.trans ?_, hsP⟩
  have hP : Nat.card P ≤ 2 ^ k := (Subgroup.card_le_card_group (H := P)).trans h
  calc Nat.log 2 (Nat.card P) ≤ Nat.log 2 (2 ^ k) := Nat.log_mono_right hP
    _ = k := Nat.log_pow (by norm_num) k

theorem aor_gen_of_quot {S : Type} [Group S] (U : Subgroup S) [U.Normal] [IsCyclic U]
    (hQ : ∀ H : Subgroup (S ⧸ U), ∃ s : Finset (S ⧸ U), s.card ≤ 2 ∧
      Subgroup.closure (s : Set (S ⧸ U)) = H)
    (P : Subgroup S) : ∃ s : Finset S, s.card ≤ 3 ∧ Subgroup.closure (s : Set S) = P := by
  classical
  have hker : (QuotientGroup.mk' U).ker = U := QuotientGroup.ker_mk' U
  obtain ⟨s, hs, hsH⟩ := hQ (P.map (QuotientGroup.mk' U))
  let K : Subgroup S := P ⊓ (QuotientGroup.mk' U).ker
  have hK : K = P ⊓ U := by simp [K, hker]
  haveI : IsCyclic K := by
    rw [hK]
    exact Subgroup.isCyclic_of_le inf_le_right
  obtain ⟨r, hr, hrH⟩ := aor_exists_finset_closure_eq_of_isCyclic K
  obtain ⟨u, hucard, hucl⟩ :=
    aor_exists_finset_closure_eq_of_map (QuotientGroup.mk' U) P hs hsH hr hrH
  exact ⟨u, by omega, hucl⟩

theorem aor_quat_central {n : ℕ} [NeZero n] (x : QuaternionGroup n) (hx : x ^ 2 = 1)
    (y : QuaternionGroup n) : x * y = y * x := by
  induction x with
  | a i =>
    have hii : i + i = 0 := by
      have h := hx
      rw [pow_two, QuaternionGroup.a_mul_a, QuaternionGroup.one_def] at h
      exact QuaternionGroup.a.inj h
    cases y with
    | a j => rw [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_a, add_comm]
    | xa j =>
      rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a]
      congr 1
      rw [sub_eq_add_neg]
      congr 1
      exact neg_eq_of_add_eq_zero_right hii
  | xa i =>
    exfalso
    have h := hx
    rw [QuaternionGroup.xa_sq, QuaternionGroup.one_def] at h
    have h2 : (n : ZMod (2 * n)) = 0 := QuaternionGroup.a.inj h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have hle := Nat.le_of_dvd (NeZero.pos n) h2
    have hn : 0 < n := NeZero.pos n
    omega

end CFSG.OddStandard.SmallF3.Omega
