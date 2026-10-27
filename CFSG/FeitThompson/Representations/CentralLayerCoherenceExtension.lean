module

public import CFSG.FeitThompson.Representations.AbelianizationLayerUniformCoherent
import CFSG.FeitThompson.Foundations.SibleySqrtExtensionInequality
import CFSG.FeitThompson.Representations.CentralNormalSectionDegreeBound
import CFSG.FeitThompson.Representations.FeitOneCharacterExtension
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open FeitExtension NormalInducedFamily
open scoped ComplexOrder Pointwise

section Bookkeeping

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]

noncomputable def virtToSpanIrr : virtualChars G →+ Submodule.span ℤ (Irr G) :=
  (Submodule.inclusion virtualChars_le_span_Irr).toAddMonoidHom

omit [Fintype L] [Fintype G] in
theorem coe_virtToSpanIrr_comp {M : Type*} [AddCommMonoid M] (φ : M →+ virtualChars G) (f : M) :
    ((virtToSpanIrr.comp φ f : Submodule.span ℤ (Irr G)) : G → ℂ) = (φ f : G → ℂ) := (rfl)

theorem IsCoherent.congr_baseline {S : Set (L → ℂ)}
    {τ τ' : charSpanZero S →+ virtualChars G}
    (h : ∀ f, (τ f : G → ℂ) = (τ' f : G → ℂ)) (hc : IsCoherent S τ) : IsCoherent S τ' := by
  have : τ = τ' := AddMonoidHom.ext fun f => Subtype.ext (h f)
  exact this ▸ hc

theorem isCoherent_restrictBaseline_congr {U S S' : Set (L → ℂ)} (h : S = S')
    (τ : charSpanZero U →+ virtualChars G) (hS : S ⊆ U) (hS' : S' ⊆ U)
    (hc : IsCoherent S (restrictBaseline hS τ)) : IsCoherent S' (restrictBaseline hS' τ) := by
  subst h; exact hc

omit [Fintype L] in
theorem sq_apply_one_nonneg {χ : L → ℂ} (hχ : χ ∈ Irr L) : (0 : ℂ) ≤ χ 1 ^ 2 := by
  obtain ⟨d, -, hd⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr hχ
  rw [hd]
  have h : ((d : ℂ)) ^ 2 = (((d ^ 2 : ℕ) : ℝ) : ℂ) := by push_cast; ring
  rw [h]
  exact Complex.zero_le_real.2 (by positivity)

end Bookkeeping

section FeitStep

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]

theorem isCoherent_insert_range_of_lt_degreeSqSum {U : Set (L → ℂ)} {ι : Type*} [Fintype ι]
    {γ : ι → (L → ℂ)} (hinj : Function.Injective γ)
    (hmem : ∀ k, γ k ∈ Irr L) (h2 : 2 ≤ Fintype.card ι) (k₀ : ι)
    {χ : L → ℂ} (hχIrr : χ ∈ Irr L) (hχS : χ ∉ Set.range γ)
    {d : ℤ} (hd : 0 < d) (hχ1 : χ 1 = (d : ℂ) * γ k₀ 1)
    (hW : 2 * γ k₀ 1 * χ 1 < degreeSqSum γ)
    (τ : charSpanZero U →+ virtualChars G)
    (hτiso : ∀ f g : charSpanZero U,
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτ1 : ∀ f : charSpanZero U, (τ f : G → ℂ) 1 = 0)
    (hU : insert χ (Set.range γ) ⊆ U)
    (hcoh : IsCoherent (Set.range γ)
      (restrictBaseline ((Set.subset_insert χ (Set.range γ)).trans hU) τ)) :
    IsCoherent (insert χ (Set.range γ)) (restrictBaseline hU τ) := by
  classical
  obtain ⟨ν, hν⟩ := isCoherent_iff.1 hcoh
  let E : OneCharExtension G γ χ d k₀ :=
  { injective := hinj
    mem_Irr := hmem
    chi_mem_Irr := hχIrr
    chi_notMem := hχS
    two_le_card := h2
    tau := virtToSpanIrr.comp (restrictBaseline hU τ)
    nu := virtToSpanIrr.comp ν
    tau_isometry := fun f h => by
      rw [coe_virtToSpanIrr_comp, coe_virtToSpanIrr_comp, restrictBaseline_apply,
        restrictBaseline_apply, hτiso]
      rfl
    tau_apply_one := fun f => by
      rw [coe_virtToSpanIrr_comp, restrictBaseline_apply]; exact hτ1 _
    nu_isometry := fun f h => by
      rw [coe_virtToSpanIrr_comp, coe_virtToSpanIrr_comp]; exact hν.inner_eq f h
    nu_eq_tau := fun f => by
      apply Subtype.ext
      rw [coe_virtToSpanIrr_comp, coe_virtToSpanIrr_comp, hν.eq_on_zero f,
        restrictBaseline_apply, restrictBaseline_apply]
      rfl
    chi_apply_one := hχ1
    d_pos := hd }
  refine (E.isCoherent_tauVirt_of_lt_degreeSqSum hW).congr_baseline ?_
  intro f
  rw [OneCharExtension.coe_tauVirt]
  exact coe_virtToSpanIrr_comp _ f

theorem isCoherent_insert_of_lt_sum {U S : Set (L → ℂ)} (hSfin : S.Finite)
    (hSIrr : S ⊆ Irr L) (h2 : 2 ≤ S.ncard) {ψ : L → ℂ} (hψ : ψ ∈ S)
    {χ : L → ℂ} (hχIrr : χ ∈ Irr L) (hχS : χ ∉ S)
    {d : ℤ} (hd : 0 < d) (hχ1 : χ 1 = (d : ℂ) * ψ 1)
    (hW : 2 * ψ 1 * χ 1 < ∑ f ∈ hSfin.toFinset, f 1 ^ 2)
    (τ : charSpanZero U →+ virtualChars G)
    (hτiso : ∀ f g : charSpanZero U,
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτ1 : ∀ f : charSpanZero U, (τ f : G → ℂ) 1 = 0)
    (hU : insert χ S ⊆ U)
    (hcoh : IsCoherent S (restrictBaseline ((Set.subset_insert χ S).trans hU) τ)) :
    IsCoherent (insert χ S) (restrictBaseline hU τ) := by
  classical
  let _ : Fintype ↥S := hSfin.fintype
  have hrange : Set.range (Subtype.val : ↥S → (L → ℂ)) = S := Subtype.range_coe
  have hcard : 2 ≤ Fintype.card ↥S := by
    rwa [Set.ncard_eq_toFinset_card', Set.toFinset_card] at h2
  have hdeg : degreeSqSum (Subtype.val : ↥S → (L → ℂ)) = ∑ f ∈ hSfin.toFinset, f 1 ^ 2 := by
    rw [degreeSqSum_eq, Set.Finite.toFinset_eq_toFinset, ← Finset.sum_set_coe]
  have hUr : insert χ (Set.range (Subtype.val : ↥S → (L → ℂ))) ⊆ U := by rw [hrange]; exact hU
  have hcohr : IsCoherent (Set.range (Subtype.val : ↥S → (L → ℂ)))
      (restrictBaseline ((Set.subset_insert χ _).trans hUr) τ) :=
    isCoherent_restrictBaseline_congr hrange.symm τ _ _ hcoh
  have key := isCoherent_insert_range_of_lt_degreeSqSum (γ := (Subtype.val : ↥S → (L → ℂ)))
    Subtype.val_injective (fun k => hSIrr k.2) hcard ⟨ψ, hψ⟩ hχIrr
    (by rw [hrange]; exact hχS) hd hχ1 (by rw [hdeg]; exact hW) τ hτiso hτ1 hUr hcohr
  exact isCoherent_restrictBaseline_congr (by rw [hrange]) τ _ _ key

theorem isCoherent_union_coe_finset {U S : Set (L → ℂ)} (hSfin : S.Finite) (hSIrr : S ⊆ Irr L)
    (h2 : 2 ≤ S.ncard) {ψ : L → ℂ} (hψ : ψ ∈ S)
    (τ : charSpanZero U →+ virtualChars G)
    (hτiso : ∀ f g : charSpanZero U,
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτ1 : ∀ f : charSpanZero U, (τ f : G → ℂ) 1 = 0)
    (hS : S ⊆ U) (hcoh : IsCoherent S (restrictBaseline hS τ)) :
    ∀ D : Finset (L → ℂ), (↑D ⊆ Irr L) →
      (∀ χ ∈ D, ∃ d : ℤ, 0 < d ∧ χ 1 = (d : ℂ) * ψ 1) →
      (∀ χ ∈ D, 2 * ψ 1 * χ 1 < ∑ f ∈ hSfin.toFinset, f 1 ^ 2) →
      ∀ hU : S ∪ ↑D ⊆ U, IsCoherent (S ∪ ↑D) (restrictBaseline hU τ) := by
  classical
  intro D
  induction D using Finset.induction_on with
  | empty =>
      intro _ _ _ hU
      exact isCoherent_restrictBaseline_congr (by simp) τ hS hU hcoh
  | insert a s ha ih =>
      intro hIrr hdeg hW hU
      have hsub : (S ∪ ↑s) ⊆ U := by
        refine (Set.union_subset_union_right _ ?_).trans hU
        exact_mod_cast Finset.coe_subset.2 (Finset.subset_insert a s)
      have hIrr' : (↑s : Set (L → ℂ)) ⊆ Irr L := fun x hx => hIrr (by
        simp only [Finset.coe_insert, Set.mem_insert_iff]
        exact Or.inr hx)
      have hih := ih hIrr' (fun χ hχ => hdeg χ (Finset.mem_insert_of_mem hχ))
        (fun χ hχ => hW χ (Finset.mem_insert_of_mem hχ)) hsub
      have hcoe : S ∪ (↑(insert a s) : Set (L → ℂ)) = insert a (S ∪ ↑s) := by
        simp [Finset.coe_insert, Set.union_insert]
      by_cases hmem : a ∈ S ∪ (↑s : Set (L → ℂ))
      · refine isCoherent_restrictBaseline_congr ?_ τ hsub hU hih
        rw [hcoe, Set.insert_eq_self.2 hmem]
      · have hVfin : (S ∪ (↑s : Set (L → ℂ))).Finite := hSfin.union s.finite_toSet
        have hVIrr : (S ∪ (↑s : Set (L → ℂ))) ⊆ Irr L := Set.union_subset hSIrr hIrr'
        have hV2 : 2 ≤ (S ∪ (↑s : Set (L → ℂ))).ncard :=
          le_trans h2 (Set.ncard_le_ncard Set.subset_union_left hVfin)
        obtain ⟨d, hd, hd1⟩ := hdeg a (Finset.mem_insert_self a s)
        have haIrr : a ∈ Irr L := hIrr (by simp)
        have hWa : 2 * ψ 1 * a 1 < ∑ f ∈ hVfin.toFinset, f 1 ^ 2 := by
          refine lt_of_lt_of_le (hW a (Finset.mem_insert_self a s)) ?_
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i hi _ => sq_apply_one_nonneg ?_)
          · exact Set.Finite.toFinset_subset_toFinset.2 Set.subset_union_left
          · exact hVIrr (Set.Finite.mem_toFinset _ |>.1 hi)
        have hU' : insert a (S ∪ (↑s : Set (L → ℂ))) ⊆ U := by rw [← hcoe]; exact hU
        have key := isCoherent_insert_of_lt_sum hVfin hVIrr hV2 (Set.mem_union_left _ hψ)
          haIrr hmem hd hd1 hWa τ hτiso hτ1 hU' hih
        exact isCoherent_restrictBaseline_congr hcoe.symm τ hU' hU key

end FeitStep

section Layers

variable {L : Type*} [Group L] [Fintype L] {H A B : Subgroup L}

theorem toFinset_eq_kerLayerIndFinset :
    (finite_kerLayerIndFam (A := A) (K := H)).toFinset = kerLayerIndFinset A H := by
  ext f
  rw [Set.Finite.mem_toFinset, mem_kerLayerIndFinset]

theorem sum_sq_apply_one_kerLayerIndFam [A.Normal] [H.Normal]
    (hIrr : (kerLayerIndFam A H : Set (L → ℂ)) ⊆ Irr L) :
    ∑ f ∈ (finite_kerLayerIndFam (A := A) (K := H)).toFinset, f 1 ^ 2
      = (H.index : ℂ) * ((A.relIndex H : ℂ) - 1) := by
  rw [toFinset_eq_kerLayerIndFinset, ← sum_sq_degree_div_norm_kerLayerIndFinset (A := A) (K := H)]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  rw [cfInner_self_of_mem_Irr (hIrr (mem_kerLayerIndFinset.1 hχ)), div_one]

omit [Fintype L] in
theorem map_mk'_subgroupOf_le_center [B.Normal] (hHA : ⁅H, A⁆ ≤ B) :
    letI : (B.subgroupOf H).Normal := ‹B.Normal›.subgroupOf H
    (A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H))
      ≤ Subgroup.center (↥H ⧸ B.subgroupOf H) := by
  let _ : (B.subgroupOf H).Normal := ‹B.Normal›.subgroupOf H
  refine map_mk'_le_center_iff.2 fun a ha h => ?_
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  push_cast
  exact hHA (by rw [Subgroup.commutator_comm]; exact Subgroup.commutator_mem_commutator ha h.2)

theorem exists_degree_of_mem_kerLayerIndFam [B.Normal]
    (hBA : B ≤ A) (hHA : ⁅H, A⁆ ≤ B) {χ : L → ℂ} (hχ : χ ∈ kerLayerIndFam B H) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ^ 2 ≤ (A.relIndex H : ℝ) ∧ χ 1 = (H.index : ℂ) * (n : ℂ) := by
  let _ : (B.subgroupOf H).Normal := ‹B.Normal›.subgroupOf H
  obtain ⟨θ, hθ, rfl⟩ := mem_kerLayerIndFam.1 hχ
  obtain ⟨hirr, hker, -⟩ := mem_kerLayerIrr.1 hθ
  obtain ⟨n, hn1, hn2⟩ := exists_degree_eq_and_sq_le_index_of_map_le_center
    (B := B.subgroupOf H) (A := A.subgroupOf H)
    (fun _ hx => hBA hx) (map_mk'_subgroupOf_le_center hHA) hirr
    (fun x hx => mem_charValueKernel.2 (hker x (Subgroup.mem_subgroupOf.1 hx)))
  obtain ⟨m, hm, hm1⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr hirr
  have hnm : n = m := by
    have h : ((n : ℂ)) = ((m : ℂ)) := by rw [← hn1, hm1]
    exact_mod_cast h
  refine ⟨n, hnm ▸ hm, ?_, ?_⟩
  · have h : (n : ℝ) ^ 2 ≤ ((A.subgroupOf H).index : ℝ) := by exact_mod_cast hn2
    rwa [Subgroup.relIndex]
  · rw [NormalInducedFamily.indClassFun_one_eq_index_mul, hn1]

end Layers

theorem two_mul_index_mul_lt {e n m : ℕ} (he : 0 < e) (hm : (m : ℝ) ^ 2 ≤ (n : ℝ))
    (hn : 4 * e ^ 2 + 1 < n) :
    2 * (e : ℂ) * ((e : ℂ) * (m : ℂ)) < (e : ℂ) * ((n : ℂ) - 1) := by
  have hmr : (m : ℝ) ≤ Real.sqrt n := (Real.le_sqrt (by positivity) (by positivity)).mpr hm
  have key : 2 * (e : ℝ) * Real.sqrt n < (n : ℝ) - 1 := two_mul_mul_sqrt_lt_sub_one_of_lt hn
  have her : (0 : ℝ) < e := by exact_mod_cast he
  have step1 : 2 * (e : ℝ) * ((e : ℝ) * m) ≤ (e : ℝ) * (2 * (e : ℝ) * Real.sqrt n) := by
    have h : (e : ℝ) * m ≤ (e : ℝ) * Real.sqrt n := mul_le_mul_of_nonneg_left hmr her.le
    nlinarith
  have hreal : 2 * (e : ℝ) * ((e : ℝ) * m) < (e : ℝ) * ((n : ℝ) - 1) :=
    lt_of_le_of_lt step1 (mul_lt_mul_of_pos_left key her)
  have hc1 : ((2 * (e : ℝ) * ((e : ℝ) * m) : ℝ) : ℂ) = 2 * (e : ℂ) * ((e : ℂ) * (m : ℂ)) := by
    push_cast; ring
  have hc2 : (((e : ℝ) * ((n : ℝ) - 1) : ℝ) : ℂ) = (e : ℂ) * ((n : ℂ) - 1) := by push_cast; ring
  rw [← hc1, ← hc2]
  exact Complex.real_lt_real.2 hreal

section Main

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G] {H E A B : Subgroup L}

theorem isCoherent_kerLayerIndFam_of_lt_relIndex [H.Normal] [A.Normal] [B.Normal]
    [Group.IsNilpotent ↥H] (hodd : Odd (Nat.card L)) (hH : H ≠ ⊥)
    (hmul : (H : Set L) * (E : Set L) = Set.univ) (hinf : H ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    (hBA : B ≤ A) (hAH' : A ≤ ⁅H, H⁆) (hHA : ⁅H, A⁆ ≤ B)
    (hidx : 4 * H.index ^ 2 + 1 < A.relIndex H)
    (τ : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H) →+ virtualChars G)
    (hτiso : ∀ f g : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτ1 : ∀ f : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H), (τ f : G → ℂ) 1 = 0)
    (hcohA : IsCoherent (kerLayerIndFam A H)
      (restrictBaseline (kerLayerIndFam_anti_left (K := H) bot_le) τ)) :
    IsCoherent (kerLayerIndFam B H)
      (restrictBaseline (kerLayerIndFam_anti_left (K := H) bot_le) τ) := by
  classical
  have hAB : kerLayerIndFam A H ⊆ kerLayerIndFam B H := kerLayerIndFam_anti_left hBA
  have hAIrr : (kerLayerIndFam A H : Set (L → ℂ)) ⊆ Irr L :=
    kerLayerIndFam_subset_Irr_of_frobenius (E := E) _ hH hmul hinf hC
  have hBIrr : (kerLayerIndFam B H : Set (L → ℂ)) ⊆ Irr L :=
    kerLayerIndFam_subset_Irr_of_frobenius (E := E) _ hH hmul hinf hC
  obtain ⟨ψ, hψH'⟩ := nonempty_kerLayerIndFam_commutator (H := H) hH
  have hψA : ψ ∈ kerLayerIndFam A H := kerLayerIndFam_anti_left hAH' hψH'
  have hψ1 : ψ 1 = (H.index : ℂ) := apply_one_of_mem_kerLayerIndFam_commutator hψH'
  have hA2 : 2 ≤ (kerLayerIndFam A H).ncard :=
    le_trans (two_le_ncard_kerLayerIndFam_commutator (E := E) hodd hH hmul hinf hC)
      (Set.ncard_le_ncard (kerLayerIndFam_anti_left hAH') finite_kerLayerIndFam)
  set D : Finset (L → ℂ) :=
    (finite_kerLayerIndFam (A := B) (K := H)).toFinset \
      (finite_kerLayerIndFam (A := A) (K := H)).toFinset with hD
  have hDmem : ∀ f ∈ D, f ∈ kerLayerIndFam B H := by
    intro f hf
    rw [hD, Finset.mem_sdiff, Set.Finite.mem_toFinset] at hf
    exact hf.1
  have hunion : kerLayerIndFam A H ∪ (↑D : Set (L → ℂ)) = kerLayerIndFam B H := by
    ext f
    rw [hD]
    simp only [Finset.coe_sdiff, Set.mem_union, Set.Finite.coe_toFinset, Set.mem_sdiff]
    refine ⟨fun h => h.elim (fun h => hAB h) (fun h => h.1), fun h => ?_⟩
    by_cases hAf : f ∈ kerLayerIndFam A H
    · exact Or.inl hAf
    · exact Or.inr ⟨h, hAf⟩
  have hUA : kerLayerIndFam A H ⊆ kerLayerIndFam (⊥ : Subgroup L) H :=
    kerLayerIndFam_anti_left bot_le
  have hUU : kerLayerIndFam A H ∪ (↑D : Set (L → ℂ)) ⊆ kerLayerIndFam (⊥ : Subgroup L) H := by
    rw [hunion]; exact kerLayerIndFam_anti_left bot_le
  have he : 0 < H.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hsum : ∑ f ∈ (finite_kerLayerIndFam (A := A) (K := H)).toFinset, f 1 ^ 2
      = (H.index : ℂ) * ((A.relIndex H : ℂ) - 1) := sum_sq_apply_one_kerLayerIndFam hAIrr
  have key := isCoherent_union_coe_finset (finite_kerLayerIndFam (A := A) (K := H))
    hAIrr hA2 hψA τ hτiso hτ1 hUA hcohA D
    (fun f hf => hBIrr (hDmem f hf)) ?_ ?_ hUU
  · exact isCoherent_restrictBaseline_congr hunion τ hUU _ key
  ·
    intro χ hχ
    obtain ⟨n, hn, -, hn1⟩ := exists_degree_of_mem_kerLayerIndFam hBA hHA (hDmem χ hχ)
    exact ⟨(n : ℤ), by exact_mod_cast hn, by rw [hn1, hψ1]; push_cast; ring⟩
  ·
    intro χ hχ
    obtain ⟨n, -, hn2, hn1⟩ := exists_degree_of_mem_kerLayerIndFam hBA hHA (hDmem χ hχ)
    rw [hsum, hψ1, hn1]
    exact two_mul_index_mul_lt he hn2 hidx

end Main

end CFSG.FeitThompson
