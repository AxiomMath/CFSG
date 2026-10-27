module

public import CFSG.FeitThompson.Representations.EqualDegreeFamilyCoherence
public import CFSG.FeitThompson.Definitions.TISubsetWithItsExactNormalizer
public import CFSG.FeitThompson.Representations.DadeIntegerIsometry
public import CFSG.FeitThompson.Representations.OddOrderNonrealCharacters
import CFSG.FeitThompson.Representations.InductionIntegerIsometryTISupport
import CFSG.FeitThompson.Representations.SolvableFrobeniusKernelInducedIndexDegree
import CFSG.FeitThompson.Representations.DegreeZeroNormalInductionsPuncturedSupport
import CFSG.FeitThompson.Representations.ProductCharactersFullBasis

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section Frobenius

variable {X : Type*} [Group X] [Fintype X] {H E : Subgroup X}

theorem inf_centralizer_eq_bot_iff_forall_conj_eq_imp_eq_one :
    (∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥) ↔
      ∀ u ∈ E, u ≠ 1 → ∀ h ∈ H, u * h * u⁻¹ = h → h = 1 := by
  constructor
  · intro hC u hu hu1 h hh hfix
    have hmem : h ∈ H ⊓ Subgroup.centralizer ({u} : Set X) :=
      Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_singleton_iff.2 (by
        calc h * u = (u * h * u⁻¹) * u := by rw [hfix]
          _ = u * h := by group)⟩
    rw [hC u hu hu1, Subgroup.mem_bot] at hmem
    exact hmem
  · intro hfree u hu hu1
    refine (Subgroup.eq_bot_iff_forall _).2 fun h hh => ?_
    obtain ⟨hhH, hhc⟩ := Subgroup.mem_inf.1 hh
    refine hfree u hu hu1 h hhH ?_
    have hc := Subgroup.mem_centralizer_singleton_iff.1 hhc
    rw [← hc]
    group

theorem indClassFun_mem_Irr_of_isComplement' [H.Normal] [Nontrivial ↥H]
    (hHE : H.IsComplement' E)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    {θ : ↥H → ℂ} (hθ : θ ∈ Irr ↥H) (hθ1 : θ ≠ 1) :
    indClassFun H θ ∈ Irr X := by
  have _ : Fintype ↥H := Fintype.ofFinite _
  have _ : Fintype ↥E := Fintype.ofFinite _
  refine mem_Irr_of_comp_mulEquiv (frobeniusMulEquiv hHE) ?_
  rw [indClassFun_comp_frobeniusMulEquiv hHE θ]
  exact indClassFun_kernelClassFun_mem_Irr
    (fun v hv => fixedPointFree_frobeniusConjAut
      (hC (v : X) v.2 (fun h => hv (Subtype.ext h)))) hθ hθ1

theorem indFam_nonprincipalIrr_subset_Irr [H.Normal] (hH : H ≠ ⊥) (hHE : H.IsComplement' E)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥) :
    indFam H (nonprincipalIrr ↥H) ⊆ Irr X := by
  have _ : Nontrivial ↥H := H.nontrivial_iff_ne_bot.2 hH
  intro f hf
  obtain ⟨θ, hθ, rfl⟩ := (mem_indFam H).1 hf
  exact indClassFun_mem_Irr_of_isComplement' hHE hC (mem_nonprincipalIrr.1 hθ).1
    (mem_nonprincipalIrr.1 hθ).2

theorem apply_one_eq_card_of_mem_indFam_nonprincipalIrr [IsMulCommutative ↥H]
    (hHE : H.IsComplement' E) {f : X → ℂ} (hf : f ∈ indFam H (nonprincipalIrr ↥H)) :
    f 1 = (Nat.card ↥E : ℂ) := by
  obtain ⟨θ, hθ, rfl⟩ := (mem_indFam H).1 hf
  exact indClassFun_one_eq_card hHE (apply_one_eq_one_of_mem_Irr (mem_nonprincipalIrr.1 hθ).1)

end Frobenius

variable {G : Type*} [Group G] {L : Subgroup G} {A : Set G} {H E : Subgroup ↥L}

theorem coe_mem_sdiff_map_iff (x : ↥L) :
    (x : G) ∈ ((H.map L.subtype : Subgroup G) : Set G) \ {1} ↔ x ∈ H ∧ x ≠ 1 := by
  constructor
  · rintro ⟨hx, hx1⟩
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    obtain rfl : y = x := Subtype.ext hyx
    exact ⟨hy, fun h => hx1 (by simp [h])⟩
  · rintro ⟨hx, hx1⟩
    exact ⟨Subgroup.mem_map.2 ⟨x, hx, rfl⟩, fun h => hx1 (Subtype.ext (by simpa using h))⟩

theorem sdiff_map_eq_image :
    ((H.map L.subtype : Subgroup G) : Set G) \ {1}
      = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}) := by
  refine Set.eq_of_subset_of_subset (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy.1
    exact ⟨x, ⟨hx, fun h => hy.2 (by simp [Set.mem_singleton_iff.1 h])⟩, rfl⟩
  · obtain ⟨x, ⟨hxH, hx1⟩, rfl⟩ := hy
    exact (coe_mem_sdiff_map_iff x).2 ⟨hxH, by simpa using hx1⟩

theorem sdiff_map_nonempty (hH : H ≠ ⊥) :
    (((H.map L.subtype : Subgroup G) : Set G) \ {1}).Nonempty := by
  have _ : Nontrivial ↥H := H.nontrivial_iff_ne_bot.2 hH
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥H)
  exact ⟨((x : ↥L) : G), (coe_mem_sdiff_map_iff _).2 ⟨x.2, fun h => hx (Subtype.ext h)⟩⟩

theorem one_notMem_sdiff_map :
    (1 : G) ∉ ((H.map L.subtype : Subgroup G) : Set G) \ {1} := by simp

theorem conj_image_eq_or_inter_eq_empty_of_pairwise
    (hpair : ∀ g k : G, (fun x => g⁻¹ * x * g) '' A = (fun x => k⁻¹ * x * k) '' A ∨
      ((fun x => g⁻¹ * x * g) '' A) ∩ ((fun x => k⁻¹ * x * k) '' A) = ∅) (g : G) :
    (fun x => g⁻¹ * x * g) '' A = A ∨ (fun x => g⁻¹ * x * g) '' A ∩ A = ∅ := by
  have hid : (fun x => (1 : G)⁻¹ * x * 1) '' A = A := by simp
  simpa [hid] using hpair g 1

theorem isTIWithNormalizer_of_stabilizer_eq_and_pairwise (hH : H ≠ ⊥)
    (hA : A = ((H.map L.subtype : Subgroup G) : Set G) \ {1})
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' A = A ↔ g ∈ L)
    (hpair : ∀ g k : G, (fun x => g⁻¹ * x * g) '' A = (fun x => k⁻¹ * x * k) '' A ∨
      ((fun x => g⁻¹ * x * g) '' A) ∩ ((fun x => k⁻¹ * x * k) '' A) = ∅) :
    IsTIWithNormalizer A L :=
  isTIWithNormalizer_of_conj_image_eq_or_disjoint (hA ▸ sdiff_map_nonempty hH)
    (hA ▸ one_notMem_sdiff_map) (conj_image_eq_or_inter_eq_empty_of_pairwise hpair) hstab

variable [Fintype ↥L]

theorem charSpanZero_le_dadeZDomain [H.Normal] {S : Set (↥L → ℂ)}
    (hSind : S ⊆ indFam H (Irr ↥H)) (hSIrr : S ⊆ Irr ↥L)
    (hA : A = ((H.map L.subtype : Subgroup G) : Set G) \ {1}) :
    charSpanZero S ≤ dadeZDomain L A := by
  intro f hf
  obtain ⟨hspan, h1⟩ := mem_charSpanZero.1 hf
  refine mem_dadeZDomain.2 ⟨mem_virtualChars_of_mem_span_Irr
    (Submodule.span_le.2 (fun g hg => Submodule.subset_span (hSIrr hg)) hspan), ?_⟩
  intro x hx
  rw [hA, coe_mem_sdiff_map_iff] at hx
  by_cases hxH : x ∈ H
  · have hx1 : x = 1 := by tauto
    rw [hx1]; exact h1
  · exact NormalInducedFamily.eq_zero_of_mem_span_indFam_of_notMem H hSind hspan hxH

section Ind

variable [Fintype G]

theorem charSpanZero_Irr_le_virtualChars : charSpanZero (Irr G) ≤ virtualChars G := by
  rw [virtualChars_eq_span_Irr]; exact charSpanZero_le _

noncomputable def IsTIWithNormalizer.indCharSpanZeroHom (hTI : IsTIWithNormalizer A L)
    {S : Set (↥L → ℂ)} (hS : charSpanZero S ≤ dadeZDomain L A) :
    charSpanZero S →+ virtualChars G :=
  ((Submodule.inclusion charSpanZero_Irr_le_virtualChars).toAddMonoidHom).comp
    (hTI.indZMap.comp (Submodule.inclusion hS).toAddMonoidHom)

theorem IsTIWithNormalizer.coe_indCharSpanZeroHom (hTI : IsTIWithNormalizer A L)
    {S : Set (↥L → ℂ)} (hS : charSpanZero S ≤ dadeZDomain L A) (f : charSpanZero S) :
    ((hTI.indCharSpanZeroHom hS f : virtualChars G) : G → ℂ)
      = indClassFun L (f : ↥L → ℂ) :=
  coe_indZMap hTI _

theorem isCoherent_of_coe_eq_indClassFun [H.Normal] [IsMulCommutative ↥H]
    (hH : H ≠ ⊥) (hHE : H.IsComplement' E)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    (hA : A = ((H.map L.subtype : Subgroup G) : Set G) \ {1})
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' A = A ↔ g ∈ L)
    (hpair : ∀ g k : G, (fun x => g⁻¹ * x * g) '' A = (fun x => k⁻¹ * x * k) '' A ∨
      ((fun x => g⁻¹ * x * g) '' A) ∩ ((fun x => k⁻¹ * x * k) '' A) = ∅)
    (τ : charSpanZero (indFam H (nonprincipalIrr ↥H)) →+ virtualChars G)
    (hτ : ∀ f, (τ f : G → ℂ) = indClassFun L (f : ↥L → ℂ)) :
    IsCoherent (indFam H (nonprincipalIrr ↥H)) τ := by
  have hTI : IsTIWithNormalizer A L :=
    isTIWithNormalizer_of_stabilizer_eq_and_pairwise hH hA hstab hpair
  have hSIrr : indFam H (nonprincipalIrr ↥H) ⊆ Irr ↥L :=
    indFam_nonprincipalIrr_subset_Irr hH hHE hC
  have hle := charSpanZero_le_dadeZDomain (H := H)
    (indFam_mono H nonprincipalIrr_subset_Irr) hSIrr hA
  refine isCoherent_of_forall_apply_one_eq (indFam_finite H finite_nonprincipalIrr) hSIrr
    (d := (Nat.card ↥E : ℂ))
    (fun f hf => apply_one_eq_card_of_mem_indFam_nonprincipalIrr hHE hf) τ ?_ ?_
  · intro f g
    rw [hτ, hτ]
    exact hTI.cfInner_indClassFun (mem_dadeDomain_of_mem_dadeZDomain (hle f.2))
      (mem_dadeDomain_of_mem_dadeZDomain (hle g.2))
  · intro f
    rw [hτ]
    exact hTI.indClassFun_apply_one fun x hx => (mem_dadeZDomain.1 (hle f.2)).2 x hx

theorem isCoherent_indCharSpanZeroHom [H.Normal] [IsMulCommutative ↥H]
    (hH : H ≠ ⊥) (hHE : H.IsComplement' E)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    (hA : A = ((H.map L.subtype : Subgroup G) : Set G) \ {1})
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' A = A ↔ g ∈ L)
    (hpair : ∀ g k : G, (fun x => g⁻¹ * x * g) '' A = (fun x => k⁻¹ * x * k) '' A ∨
      ((fun x => g⁻¹ * x * g) '' A) ∩ ((fun x => k⁻¹ * x * k) '' A) = ∅) :
    IsCoherent (indFam H (nonprincipalIrr ↥H))
      ((isTIWithNormalizer_of_stabilizer_eq_and_pairwise hH hA hstab hpair).indCharSpanZeroHom
        (charSpanZero_le_dadeZDomain (H := H) (indFam_mono H nonprincipalIrr_subset_Irr)
          (indFam_nonprincipalIrr_subset_Irr hH hHE hC) hA)) :=
  isCoherent_of_coe_eq_indClassFun hH hHE hC hA hstab hpair _
    (IsTIWithNormalizer.coe_indCharSpanZeroHom _ _)

end Ind

end CFSG.FeitThompson

end
