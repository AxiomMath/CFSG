module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotRootSL2Basic

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

theorem exists_ne_zero_ne_one_of_four_le_card [Finite K] (hq : 4 ≤ Nat.card K) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  classical
  by_contra hcon
  have : Fintype K := Fintype.ofFinite K
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
    by_cases hx : x = 0
    · simp [hx]
    · by_cases hx1 : x = 1
      · simp [hx1]
      · exact absurd ⟨x, hx, hx1⟩ hcon
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hle
  have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
  omega

theorem rootCharKernel_inter_closed {a : Fin τ.rank → Kˣ} {S : Set (Fin τ.rank → ℤ)}
    (hScl : ∀ α ∈ S, ∀ β ∈ S, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → IsRoot τ (m • α + n • β) →
      m • α + n • β ∈ S) :
    ∀ α ∈ rootCharKernel a ∩ S, ∀ β ∈ rootCharKernel a ∩ S, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      IsRoot τ (m • α + n • β) → m • α + n • β ∈ rootCharKernel a ∩ S := by
  intro α hα β hβ m n hm hn hr
  refine ⟨⟨hr, ?_⟩, hScl α hα.2 β hβ.2 m n hm hn hr⟩
  rw [rootChar_add, ← Nat.cast_smul_eq_nsmul ℤ m α, ← Nat.cast_smul_eq_nsmul ℤ n β,
    rootChar_zsmul, rootChar_zsmul, hα.1.2, hβ.1.2, one_zpow, one_zpow, one_mul]

section Fixed


theorem mem_rootSpan_inter_of_mem_centralizer {a : Fin τ.rank → Kˣ}
    {S : Set (Fin τ.rank → ℤ)} (hSpos : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α)
    (hScl : ∀ α ∈ S, ∀ β ∈ S, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → IsRoot τ (m • α + n • β) →
      m • α + n • β ∈ S)
    {x : ModGL τ K} (hx : x ∈ rootSpan τ K S)
    (hxa : x ∈ centralizer ({rootDiagUnit τ a} : Set (ModGL τ K))) :
    x ∈ rootSpan τ K (rootCharKernel a ∩ S) := by
  have hfin : S.Finite := (finite_setOf_isRoot τ).subset fun α hα => (hSpos α hα).1
  refine mem_rootSpan_inter_of_conj_eq a hfin (fun α hα => (hSpos α hα).1)
    (fun α hα hrange => bijOn_prod_pinnedX K hSpos hScl α hα hrange) hx ?_
  rw [Subgroup.mem_centralizer_iff.1 hxa _ (Set.mem_singleton _), mul_inv_cancel_right]

theorem mem_rootSpan_of_forall_mem_centralizer (l : Kˣ) (L : List (Fin τ.rank)) :
    ∀ {S : Set (Fin τ.rank → ℤ)}, (∀ α ∈ S, IsRoot τ α ∧ 0 < height α) →
      (∀ α ∈ S, ∀ β ∈ S, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → IsRoot τ (m • α + n • β) →
        m • α + n • β ∈ S) →
      ∀ {x : ModGL τ K}, x ∈ rootSpan τ K S →
        (∀ j ∈ L, x ∈ centralizer
          ({rootDiagUnit τ (fun k => l ^ τ.cartan j k)} : Set (ModGL τ K))) →
        x ∈ rootSpan τ K {α | α ∈ S ∧ ∀ j ∈ L, rootChar (fun k => l ^ τ.cartan j k) α = 1} := by
  induction L with
  | nil =>
    intro S _ _ x hx _
    refine rootSpan_mono ?_ hx
    intro α hα
    exact ⟨hα, fun j hj => absurd hj List.not_mem_nil⟩
  | cons j L ih =>
    intro S hSpos hScl x hx hcent
    have h1 := mem_rootSpan_inter_of_mem_centralizer hSpos hScl hx (hcent j List.mem_cons_self)
    have h2 := ih (fun α hα => hSpos α hα.2) (rootCharKernel_inter_closed hScl) h1
      fun j' hj' => hcent j' (List.mem_cons_of_mem _ hj')
    refine rootSpan_mono ?_ h2
    rintro α ⟨⟨⟨-, hαj⟩, hαS⟩, hαL⟩
    refine ⟨hαS, fun j' hj' => ?_⟩
    rcases List.mem_cons.1 hj' with rfl | h
    · exact hαj
    · exact hαL j' h

theorem mem_rootSubgroup_highRoot_of_forall [CharP K 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {l : Kˣ} (hl : l ≠ 1) {S : Set (Fin τ.rank → ℤ)}
    (hSpos : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α)
    (hScl : ∀ α ∈ S, ∀ β ∈ S, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → IsRoot τ (m • α + n • β) →
      m • α + n • β ∈ S)
    {x : ModGL τ K} (hx : x ∈ rootSpan τ K S)
    (hcent : ∀ j, j ≠ highNode τ → x ∈ centralizer
      ({rootDiagUnit τ (fun k => l ^ τ.cartan j k)} : Set (ModGL τ K))) :
    x ∈ rootSubgroup τ K (highRoot τ) := by
  have h := mem_rootSpan_of_forall_mem_centralizer l
    ((List.finRange τ.rank).filter (· ≠ highNode τ)) hSpos hScl hx fun j hj =>
      hcent j (by simpa using (List.mem_filter.1 hj).2)
  refine (iSup₂_le fun α hα => ?_ : _ ≤ rootSubgroup τ K (highRoot τ)) h
  obtain ⟨hαS, hαL⟩ := hα
  have hαr := (hSpos α hαS).1
  have h0 : ∀ j, j ≠ highNode τ → coPair τ j α = 0 := fun j hj => by
    have h1 := hαL j (List.mem_filter.2 ⟨List.mem_finRange j, by simpa using hj⟩)
    rw [rootChar_cartan_row] at h1
    exact eq_zero_of_zpow_eq_one_of_charTwo hl (abs_coPair_le_two hτ hαr j) h1
  rcases eq_highRoot_or_neg_of_coPair_eq_zero hτ hαr h0 with rfl | rfl
  · exact le_rfl
  · have hpos := (hSpos _ hαS).2
    rw [height_neg] at hpos
    have := height_highRoot_pos τ
    omega

theorem eq_of_pinnedX_eq_pinnedX_of_pos {δ γ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ)
    (hγ : IsRoot τ γ) (hγp : 0 < height γ) {d e : K} (he : e ≠ 0)
    (h : pinnedX τ K δ d = pinnedX τ K γ e) : δ = γ := by
  by_contra hne
  rcases IsRoot.height_pos_or_neg hδ with hpos | hneg
  · have hL := pinnedX_list_prod_injective (R := K) [δ, γ]
      (by simpa using hne)
      (by
        intro α hα
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
        rcases hα with rfl | rfl
        · exact ⟨hδ, hpos⟩
        · exact ⟨hγ, hγp⟩)
      (fun α => if α = δ then d else 0)
      (fun α => if α = γ then e else 0)
      (by
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hne,
          Ne.symm hne, ↓reduceIte, pinnedX_zero, one_mul]
        exact h)
      γ (by simp)
    simp only [Ne.symm hne, ↓reduceIte] at hL
    exact he hL.symm
  · have hneg' : pinnedX τ K δ d ∈ negUnipotent τ K :=
      pinnedX_mem_rootSpan (S := {α | IsRoot τ α ∧ height α < 0}) ⟨hδ, hneg⟩ d
    have hB : pinnedX τ K δ d ∈ borelGroup τ K := by
      rw [h]
      exact Subgroup.mem_sup_right
        (pinnedX_mem_rootSpan (S := {α | IsRoot τ α ∧ 0 < height α}) ⟨hγ, hγp⟩ e)
    have h0 := Subgroup.mem_inf.2 ⟨hB, hneg'⟩
    rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot, h] at h0
    exact he (pinnedX_injective τ K _ (h0.trans (pinnedX_zero τ K _).symm))

theorem mem_highRootSL2_of_mem_centralizer [CharP K 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    (hgD : g ∈ centralizer (rootSpan τ K (perpRoots τ) : Set (ModGL τ K))) :
    g ∈ highRootSL2 τ K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨c, hc0, hc1⟩ := hK
  set l : Kˣ := Units.mk0 c hc0 with hl
  have hl1 : l ≠ 1 := fun h => hc1 (by simpa [hl] using congrArg Units.val h)
  have hr := isRoot_highRoot τ
  have hJD := highRootSL2_le_centralizer_perpLevi (K := K) hτ
  have hJ : ∀ {x : ModGL τ K}, x ∈ rootSubgroup τ K (highRoot τ) → x ∈ highRootSL2 τ K :=
    fun hx => Subgroup.mem_sup_left hx
  have htor : ∀ j : Fin τ.rank, j ≠ highNode τ →
      g ∈ toralCentralizer τ K (fun k => l ^ τ.cartan j k) := by
    intro j hj
    refine mem_toralCentralizer.2 ⟨hg, ?_⟩
    have ht := torusElt_mem_rootSpan_perpRoots hj l
    rw [torusElt_eq_rootDiagUnit] at ht
    rw [Subgroup.mem_centralizer_iff.1 hgD _ ht, mul_inv_cancel_right]
  have hg1 : g ∈ toralCentralizer τ K 1 := by
    refine mem_toralCentralizer.2 ⟨hg, ?_⟩
    rw [rootDiagUnit_one, one_mul, inv_one, mul_one]
  have hB := Chevalley_toral_centralizer_Bruhat_factors τ K 1
  obtain ⟨w, -, h, hh, u, hu, v, hv, hgdec⟩ := hB.1 g hg1
  have hfac : ∀ j : Fin τ.rank, j ≠ highNode τ →
      u ∈ rootSpan τ K (rootCharKernel (fun k => l ^ τ.cartan j k) ∩
        {α | IsRoot τ α ∧ 0 < height α}) ∧
      v ∈ rootSpan τ K (rootCharKernel (fun k => l ^ τ.cartan j k) ∩ inversionSet w) := by
    intro j hj
    obtain ⟨w', -, h', hh', u', hu', v', hv', hgdec'⟩ :=
      (Chevalley_toral_centralizer_Bruhat_factors τ K (fun k => l ^ τ.cartan j k)).1 g
        (htor j hj)
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hB.2.1 w w' h h' u u' v v' hh hh'
      (rootSpan_mono Set.inter_subset_right hu) (rootSpan_mono Set.inter_subset_right hu')
      (rootSpan_mono Set.inter_subset_right hv) (rootSpan_mono Set.inter_subset_right hv')
      (hgdec.symm.trans hgdec')
    exact ⟨hu', hv'⟩
  have hposcl : ∀ α ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α},
      ∀ β ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}, ∀ m n : ℕ, 1 ≤ m →
        1 ≤ n → IsRoot τ (m • α + n • β) →
          m • α + n • β ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α} := by
    intro α hα β hβ m n hm hn hmn
    refine ⟨hmn, ?_⟩
    rw [height_nsmul_add_nsmul]
    have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
    have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith [hα.2, hβ.2]
  have hcentU : ∀ {x : ModGL τ K} {S : Set (Fin τ.rank → ℤ)},
      (∀ j, j ≠ highNode τ → x ∈ rootSpan τ K (rootCharKernel (fun k => l ^ τ.cartan j k) ∩ S)) →
      ∀ j, j ≠ highNode τ → x ∈ centralizer
        ({rootDiagUnit τ (fun k => l ^ τ.cartan j k)} : Set (ModGL τ K)) := fun hx j hj =>
    rootSpan_le_centralizer _ Set.inter_subset_left (hx j hj)
  have hur : u ∈ rootSubgroup τ K (highRoot τ) :=
    mem_rootSubgroup_highRoot_of_forall hτ hl1 (fun α hα => hα) hposcl
      (rootSpan_mono (Set.inter_subset_right) hu) (hcentU fun j hj => (hfac j hj).1)
  have hvr : v ∈ rootSubgroup τ K (highRoot τ) :=
    mem_rootSubgroup_highRoot_of_forall hτ hl1 (fun α hα => inversionSet_pos hα)
      (inversionSet_closed w) (rootSpan_mono (Set.inter_subset_right) hv)
      (hcentU fun j hj => (hfac j hj).2)
  have hu' : h * u * h⁻¹ ∈ rootSubgroup τ K (highRoot τ) :=
    (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSubgroup hr hh) u).1 hur
  have hgJ : g = (h * u * h⁻¹) * (h * canonicalRep (coxeterSystem τ) K w) * v := by
    rw [hgdec]
    group
  have hm : h * canonicalRep (coxeterSystem τ) K w ∈
      centralizer (rootSpan τ K (perpRoots τ) : Set (ModGL τ K)) := by
    have e : h * canonicalRep (coxeterSystem τ) K w = (h * u * h⁻¹)⁻¹ * g * v⁻¹ := by
      rw [hgJ]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hJD (hJ hu'))) hgD) (inv_mem (hJD (hJ hvr)))
  have hwj : ∀ j : Fin τ.rank, j ≠ highNode τ →
      w • (Pi.single j 1 : Fin τ.rank → ℤ) = Pi.single j 1 := by
    intro j hj
    have hc := Subgroup.mem_centralizer_iff.1 hm _ (pinnedX_single_mem_perpLevi hj (1 : K))
    have hroot := IsRoot.smul (isRoot_single τ j) w
    have e : pinnedX τ K (w • Pi.single j 1) (torusRootChar h (w • Pi.single j 1) * 1) =
        pinnedX τ K (Pi.single j 1) 1 := by
      rw [← conj_pinnedX_of_mem_torusGroup hh hroot,
        ← canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (isRoot_single τ j)]
      calc h * (canonicalRep (coxeterSystem τ) K w * pinnedX τ K (Pi.single j 1) 1 *
            (canonicalRep (coxeterSystem τ) K w)⁻¹) * h⁻¹ =
          pinnedX τ K (Pi.single j 1) 1 * (h * canonicalRep (coxeterSystem τ) K w) *
            (h * canonicalRep (coxeterSystem τ) K w)⁻¹ := by rw [hc]; group
        _ = pinnedX τ K (Pi.single j 1) 1 := mul_inv_cancel_right _ _
    exact eq_of_pinnedX_eq_pinnedX_of_pos hroot (isRoot_single τ j)
      (by rw [height_single]; norm_num) one_ne_zero e
  have hw0 := eq_single_or_sub_highRoot_of_iform_eq hτ
    (IsRoot.smul (isRoot_single τ (highNode τ)) w) fun j hj => by
      calc iform (w • (Pi.single (highNode τ) 1 : Fin τ.rank → ℤ)) (Pi.single j 1) =
          iform (w • (Pi.single (highNode τ) 1 : Fin τ.rank → ℤ))
            (w • (Pi.single j 1 : Fin τ.rank → ℤ)) := by rw [hwj j hj]
        _ = iform (Pi.single (highNode τ) 1 : Fin τ.rank → ℤ) (Pi.single j 1) :=
          iform_smul w _ _
  rcases hw0 with h0 | h0
  ·
    have hw1 : w = 1 := eq_one_of_forall_height_pos fun i => by
      by_cases hi : i = highNode τ
      · subst hi
        rw [h0, height_single]
        norm_num
      · rw [hwj i hi, height_single]
        norm_num
    subst hw1
    rw [canonicalRep_one, mul_one] at hm hgJ
    rw [hgJ]
    exact mul_mem (mul_mem (hJ hu') (mem_highRootSL2_of_mem_torusGroup hτ hh hm)) (hJ hvr)
  ·
    obtain ⟨v', i, hv'⟩ := isRoot_iff_exists_smul_single.1 hr
    set s := v' * simple τ i * v'⁻¹ with hs
    have hsx := smul_conj_simple_eq hτ hv'
    have hsw : s * w = 1 := eq_one_of_forall_height_pos fun j => by
      by_cases hj : j = highNode τ
      · subst hj
        rw [mul_smul, h0, hsx]
        have e : (Pi.single (highNode τ) 1 - highRoot τ : Fin τ.rank → ℤ) -
            (Pi.single (highNode τ) 1 - highRoot τ : Fin τ.rank → ℤ) (highNode τ) • highRoot τ =
            Pi.single (highNode τ) 1 := by
          rw [Pi.sub_apply, Pi.single_eq_same, highRoot_highNode hτ]
          ext k
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [e, height_single]
        norm_num
      · rw [mul_smul, hwj j hj, hsx, Pi.single_eq_of_ne (Ne.symm hj), zero_smul, sub_zero,
          height_single]
        norm_num
    have hw : w * s = 1 := by
      rw [eq_inv_of_mul_eq_one_left hsw, mul_inv_cancel]
    set nθ := canonicalRep (coxeterSystem τ) K v' * weylElt τ K i 1 *
      (canonicalRep (coxeterSystem τ) K v')⁻¹ with hnθ
    have hnθJ : nθ ∈ highRootSL2 τ K := conj_mem_highRootSL2 hv' (weylElt_mem_rootPair i 1)
    have ht : h * canonicalRep (coxeterSystem τ) K w * nθ ∈ torusGroup τ K := by
      refine mem_torusGroup_of_mapsRootLines_one ?_ ?_
      · exact mul_mem (mul_mem (Subgroup.mem_sup_left hh) (canonicalRep_mem_monomialSubgroup K w))
          (mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup K _)
            (weylElt_mem_monomialSubgroup i))
            (inv_mem (canonicalRep_mem_monomialSubgroup K _)))
      · have hmaps := ((mapsRootLines_of_mem_torusGroup hh).mul (mapsRootLines_canonicalRep w)).mul
          (((mapsRootLines_canonicalRep v').mul (mapsRootLines_weylElt i)).mul
            (mapsRootLines_canonicalRep v').inv)
        rwa [one_mul, ← hs, hw] at hmaps
    have htJ := mem_highRootSL2_of_mem_torusGroup hτ ht (mul_mem hm (hJD hnθJ))
    have e : h * canonicalRep (coxeterSystem τ) K w =
        (h * canonicalRep (coxeterSystem τ) K w * nθ) * nθ⁻¹ := by group
    rw [hgJ, e]
    exact mul_mem (mul_mem (hJ hu') (mul_mem htJ (inv_mem hnθJ))) (hJ hvr)

theorem centralizer_perpLevi_eq_of_exists [CharP K 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) :
    adjointGroup τ K ⊓ centralizer (rootSpan τ K (perpRoots τ) : Set (ModGL τ K)) =
      highRootSL2 τ K := by
  refine le_antisymm (fun g hg => ?_)
    (le_inf highRootSL2_le_adjointGroup (highRootSL2_le_centralizer_perpLevi hτ))
  exact mem_highRootSL2_of_mem_centralizer hτ hK (Subgroup.mem_inf.1 hg).1 (Subgroup.mem_inf.1 hg).2

theorem centralizer_perpLevi_eq [Finite K] [CharP K 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hq : 4 ≤ Nat.card K) :
    adjointGroup τ K ⊓ centralizer (rootSpan τ K (perpRoots τ) : Set (ModGL τ K)) =
      highRootSL2 τ K :=
  centralizer_perpLevi_eq_of_exists hτ (exists_ne_zero_ne_one_of_four_le_card hq)

end Fixed

end CFSG.SeitzReduction.EPilot
