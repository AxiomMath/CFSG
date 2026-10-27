module

public import CFSG.FeitThompson.Representations.WeightedFeitInequalityConjugatePairExtension
public import CFSG.FeitThompson.Representations.QuotientFrobeniusLinearLayerCoherence
public import CFSG.FeitThompson.Representations.CentralFrobeniusLayerDegreeSquareSum
import CFSG.FeitThompson.Representations.CentralActionCasesComplementOrderBound
import CFSG.FeitThompson.Representations.CentralSubgroupBoundsDegreeSquare
import CFSG.FeitThompson.Representations.DisjointSupportCoherentFamiliesOrthogonal
import CFSG.FeitThompson.Representations.EqualDegreeBlocksImagesSupportedPairs
import CFSG.FeitThompson.Representations.EqualDegreeDifferenceSaturatesAntirealBlocks
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.SolvableFrobeniusKernelInducedIndexDegree

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace CentralSectionFullExtension

open scoped ComplexOrder Pointwise
open WeightedFeitExtension NormalInducedFamily

section Weights

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
  {S : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}

theorem exists_pos_cfInner_self (hc : IsSubcoherent S tau R) {χ : L → ℂ} (hχ : χ ∈ S) :
    ∃ t : ℝ, 0 < t ∧ cfInner χ χ = (t : ℂ) := by
  have hcard := hc.card_R hχ
  rw [charInner_eq_cfInner] at hcard
  refine ⟨((R χ).card : ℝ) / 2, ?_, ?_⟩
  · have hne : (R χ).card ≠ 0 := by
      intro h0
      rw [h0] at hcard
      have h : cfInner χ χ = 0 := by
        have h2 : (2 : ℂ) * cfInner χ χ = 0 := by exact_mod_cast hcard.symm
        simpa using h2
      exact hc.ne_zero χ hχ (cfInner_self_eq_zero.1 h)
    positivity
  · push_cast
    rw [eq_div_iff (by norm_num)]
    linear_combination -hcard

theorem exists_pos_weight (hc : IsSubcoherent S tau R) {χ : L → ℂ} (hχ : χ ∈ S) :
    ∃ t : ℝ, 0 < t ∧ χ 1 ^ 2 / cfInner χ χ = (t : ℂ) := by
  obtain ⟨c, hc0, hcc⟩ := exists_pos_cfInner_self hc hχ
  obtain ⟨d, hd, hd1⟩ := (hc.isCharacter χ hχ).exists_pos_nat_apply_one (hc.ne_zero χ hχ)
  refine ⟨(d : ℝ) ^ 2 / c, by positivity, ?_⟩
  rw [hd1, hcc]
  push_cast
  ring

theorem weight_nonneg (hc : IsSubcoherent S tau R) {χ : L → ℂ} (hχ : χ ∈ S) :
    (0 : ℂ) ≤ χ 1 ^ 2 / cfInner χ χ := by
  obtain ⟨t, ht, htt⟩ := exists_pos_weight hc hχ
  rw [htt]
  exact_mod_cast ht.le

theorem sum_weight_le_of_subset (hc : IsSubcoherent S tau R) {T₁ T₂ : Finset (L → ℂ)}
    (h₁₂ : T₁ ⊆ T₂) (h₂ : T₂ ⊆ S) :
    ∑ γ ∈ T₁, γ 1 ^ 2 / cfInner γ γ ≤ ∑ γ ∈ T₂, γ 1 ^ 2 / cfInner γ γ :=
  Finset.sum_le_sum_of_subset_of_nonneg h₁₂ fun _ hx _ => weight_nonneg hc (h₂ hx)

end Weights

section Extension

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
  {S : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}

def IsCoherentExtensionOf (tau : (L → ℂ) → (G → ℂ)) {T₀ : Set (L → ℂ)}
    (ν₀ : Submodule.span ℤ T₀ →+ virtualChars G) (T : Set (L → ℂ)) : Prop :=
  ∃ ν : Submodule.span ℤ T →+ virtualChars G,
    (∀ f h : Submodule.span ℤ T,
      cfInner (ν f : G → ℂ) (ν h : G → ℂ) = cfInner (f : L → ℂ) (h : L → ℂ)) ∧
    (∀ f : charSpanZero T,
      (ν (Submodule.inclusion (charSpanZero_le T) f) : G → ℂ) = tau (f : L → ℂ)) ∧
    ∀ (v : L → ℂ) (hv₀ : v ∈ Submodule.span ℤ T₀) (hv : v ∈ Submodule.span ℤ T),
      (ν ⟨v, hv⟩ : G → ℂ) = (ν₀ ⟨v, hv₀⟩ : G → ℂ)

variable {T₀ : Set (L → ℂ)} {ν₀ : Submodule.span ℤ T₀ →+ virtualChars G}

theorem IsCoherentExtensionOf.exists_isCoherentWith {T : Set (L → ℂ)}
    {τT : charSpanZero T →+ virtualChars G} (hτ : ∀ f, (τT f : G → ℂ) = tau (f : L → ℂ))
    (h : IsCoherentExtensionOf tau ν₀ T) :
    ∃ ν : Submodule.span ℤ T →+ virtualChars G, IsCoherentWith T τT ν ∧
      ∀ (v : L → ℂ) (hv₀ : v ∈ Submodule.span ℤ T₀) (hv : v ∈ Submodule.span ℤ T),
        (ν ⟨v, hv⟩ : G → ℂ) = (ν₀ ⟨v, hv₀⟩ : G → ℂ) := by
  obtain ⟨ν, hiso, heq, hext⟩ := h
  exact ⟨ν, ⟨hiso, fun f => Subtype.ext (by rw [heq f, hτ f])⟩, hext⟩

theorem IsCoherentExtensionOf.isCoherent {T : Set (L → ℂ)}
    {τT : charSpanZero T →+ virtualChars G} (hτ : ∀ f, (τT f : G → ℂ) = tau (f : L → ℂ))
    (h : IsCoherentExtensionOf tau ν₀ T) : IsCoherent T τT := by
  obtain ⟨ν, hν, -⟩ := h.exists_isCoherentWith hτ
  exact hν.isCoherent

theorem isCoherentExtensionOf_self {τ₀ : charSpanZero T₀ →+ virtualChars G}
    (hτ₀ : ∀ f, (τ₀ f : G → ℂ) = tau (f : L → ℂ)) (h : IsCoherentWith T₀ τ₀ ν₀) :
    IsCoherentExtensionOf tau ν₀ T₀ :=
  ⟨ν₀, h.inner_eq, fun f => by rw [h.eq_on_zero f, hτ₀ f], fun _ _ _ => by congr 1⟩

theorem coe_insert_insert_star (T : Finset (L → ℂ)) (χ : L → ℂ) :
    ((insert χ (insert (star χ) T) : Finset (L → ℂ)) : Set (L → ℂ)) = insertPair χ T := by
  classical
  ext f
  rw [mem_insertPair_iff]
  simp

theorem isCoherentExtensionOf_insertPair (hc : IsSubcoherent S tau R) {T : Finset (L → ℂ)}
    {χ ψ : L → ℂ} (hTS : T ⊆ S) (hTne : T.Nonempty) (hTstar : ∀ γ ∈ T, star γ ∈ T)
    (hT₀T : T₀ ⊆ (T : Set (L → ℂ)))
    (hν : IsCoherentExtensionOf tau ν₀ (T : Set (L → ℂ)))
    (hψT : ψ ∈ T) (hχS : χ ∈ S) (hχT : χ ∉ T) {d : ℕ} (hd : 1 ≤ d)
    (hdeg : χ 1 = (d : ℂ) * ψ 1)
    (hFeit : 2 * χ 1 * ψ 1 < ∑ γ ∈ T, γ 1 ^ 2 / cfInner γ γ) :
    IsCoherentExtensionOf tau ν₀ (insertPair χ T) := by
  obtain ⟨ν, hνc, hνext⟩ := hν.exists_isCoherentWith (τT := subTauHom hc hTS)
    (fun f => subTauHom_apply hc hTS f)
  obtain ⟨ν', hν'c, hν'restr, -⟩ :=
    exists_isCoherentWith_insertPair hc hTS hTne hTstar hνc
      (fun f => subTauHom_apply hc hTS f) hψT hχS hχT hd hdeg hFeit
  refine ⟨ν', hν'c.inner_eq, ?_, ?_⟩
  · intro f
    rw [hν'c.eq_on_zero f]
    exact subTauHom_apply hc (insertPair_subset hc hTS hχS) f
  · intro v hv₀ hv
    have hvT : v ∈ Submodule.span ℤ (T : Set (L → ℂ)) := Submodule.span_mono hT₀T hv₀
    have h1 := hν'restr ⟨v, hvT⟩
    have h2 : Submodule.inclusion (span_le_span_insertPair (a := χ) (Ta := T))
        ⟨v, hvT⟩ = ⟨v, hv⟩ := Subtype.ext rfl
    rw [h2] at h1
    rw [h1, hνext v hv₀ hvT]

theorem isCoherentExtensionOf_of_forall_threshold (hc : IsSubcoherent S tau R)
    {T₀f : Finset (L → ℂ)} (hT₀S : T₀f ⊆ S) (hT₀star : ∀ γ ∈ T₀f, star γ ∈ T₀f)
    {ν₀ : Submodule.span ℤ (T₀f : Set (L → ℂ)) →+ virtualChars G}
    (hν₀ : IsCoherentWith (T₀f : Set (L → ℂ)) (subTauHom hc hT₀S) ν₀)
    (hthr : ∀ χ ∈ S, ∃ ψ ∈ T₀f, ∃ d : ℕ, 1 ≤ d ∧ χ 1 = (d : ℂ) * ψ 1 ∧
      2 * χ 1 * ψ 1 < ∑ γ ∈ T₀f, γ 1 ^ 2 / cfInner γ γ)
    (hT₀ne : T₀f.Nonempty) :
    IsCoherentExtensionOf tau ν₀ (S : Set (L → ℂ)) := by
  classical
  have hstart : IsCoherentExtensionOf tau ν₀ (T₀f : Set (L → ℂ)) :=
    isCoherentExtensionOf_self (fun f => subTauHom_apply hc hT₀S f) hν₀
  suffices H : ∀ n : ℕ, ∀ T : Finset (L → ℂ), S.card - T.card ≤ n → T₀f ⊆ T → T ⊆ S →
      (∀ γ ∈ T, star γ ∈ T) → IsCoherentExtensionOf tau ν₀ (T : Set (L → ℂ)) →
      IsCoherentExtensionOf tau ν₀ (S : Set (L → ℂ)) from
    H S.card T₀f (by omega) Finset.Subset.rfl hT₀S hT₀star hstart
  intro n
  induction n with
  | zero =>
    intro T hcard _ hTS _ hT
    have hTeq : T = S := Finset.eq_of_subset_of_card_le hTS (by omega)
    exact hTeq ▸ hT
  | succ n ih =>
    intro T hcard hT₀T hTS hTstar hT
    by_cases hTeq : T = S
    · exact hTeq ▸ hT
    obtain ⟨χ, hχS, hχT⟩ : ∃ χ ∈ S, χ ∉ T := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      exact hTeq (Finset.Subset.antisymm hTS fun f hf => hcon f hf)
    obtain ⟨ψ, hψ, d, hd, hdeg, hFeit⟩ := hthr χ hχS
    have hψT : ψ ∈ T := hT₀T hψ
    have hTne : T.Nonempty := ⟨ψ, hψT⟩
    have hFeit' : 2 * χ 1 * ψ 1 < ∑ γ ∈ T, γ 1 ^ 2 / cfInner γ γ :=
      lt_of_lt_of_le hFeit (sum_weight_le_of_subset hc hT₀T hTS)
    have hpair := isCoherentExtensionOf_insertPair hc hTS hTne hTstar
      (fun _ hf => hT₀T hf) hT hψT hχS hχT hd hdeg hFeit'
    set T' : Finset (L → ℂ) := insert χ (insert (star χ) T) with hT'def
    have hTT' : T ⊆ T' := by
      intro f hf; simp only [hT'def, Finset.mem_insert]; exact Or.inr (Or.inr hf)
    have hT'S : T' ⊆ S := by
      intro f hf
      simp only [hT'def, Finset.mem_insert] at hf
      rcases hf with rfl | rfl | hf
      · exact hχS
      · exact hc.star_mem _ hχS
      · exact hTS hf
    have hT'star : ∀ γ ∈ T', star γ ∈ T' := by
      intro γ hγ
      simp only [hT'def, Finset.mem_insert] at hγ ⊢
      rcases hγ with rfl | rfl | hγ
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (star_star _)
      · exact Or.inr (Or.inr (hTstar γ hγ))
    have hcardlt : T.card < T'.card :=
      Finset.card_lt_card ⟨hTT', fun hsub => hχT (hsub (by simp [hT'def]))⟩
    have hScard : T'.card ≤ S.card := Finset.card_le_card hT'S
    exact ih T' (by omega) (hT₀T.trans hTT') hT'S hT'star
      ((coe_insert_insert_star T χ).symm ▸ hpair)

end Extension

section Families

variable {L : Type*} [Group L] [Fintype L] {P Z : Subgroup L} [P.Normal] [Z.Normal]

omit [P.Normal] in
theorem kerLayerIndFam_mono {A A' : Subgroup L} (h : A' ≤ A) :
    kerLayerIndFam A P ⊆ kerLayerIndFam A' P := by
  intro f hf
  obtain ⟨θ, hθ, rfl⟩ := mem_kerLayerIndFam.1 hf
  exact indClassFun_mem_kerLayerIndFam (FrobeniusQuotientLayer.kerLayerIrr_mono h hθ)

theorem disjoint_indFamDetect_kerLayerIndFam {A : Subgroup L} (hZA : Z ≤ A) :
    Disjoint (indFamDetect P (Z.subgroupOf P)) (kerLayerIndFam A P) := by
  rw [Set.disjoint_left]
  intro f hfX hfA
  obtain ⟨θ, hθ, rfl⟩ := (mem_indFamDetect P).1 hfX
  obtain ⟨θ', hθ', hθ'eq⟩ := mem_kerLayerIndFam.1 hfA
  obtain ⟨hθ'irr, hθ'ker, -⟩ := mem_kerLayerIrr.1 hθ'
  have hθirr : θ ∈ Irr ↥P := by rw [Irr_eq_irrChar]; exact (mem_irrDetect.1 hθ).1
  obtain ⟨t, ht⟩ :=
    (NormalInducedFamily.indClassFun_eq_iff_exists_conjClassFun P hθirr hθ'irr).1 hθ'eq.symm
  refine (mem_irrDetect.1 hθ).2 fun x hx => ?_
  have hxZ : (x : L) ∈ Z := Subgroup.mem_subgroupOf.1 hx
  refine mem_charValueKernel.2 ?_
  rw [← ht, NormalInduction.conjClassFun_apply, NormalInducedFamily.conjClassFun_apply_one]
  refine hθ'ker _ ?_
  rw [NormalInduction.coe_conjNormal_inv]
  refine hZA ?_
  simpa [mul_assoc] using ‹Z.Normal›.conj_mem _ hxZ (t : L)⁻¹

theorem disjoint_indFamDetect_kerLayerIndFam_commutator (hZP' : Z ≤ ⁅P, P⁆) :
    Disjoint (indFamDetect P (Z.subgroupOf P)) (kerLayerIndFam ⁅P, P⁆ P) :=
  disjoint_indFamDetect_kerLayerIndFam hZP'

omit [Z.Normal] in
theorem kerLayerIndFam_bot_eq_union :
    kerLayerIndFam (⊥ : Subgroup L) P
      = indFamDetect P (Z.subgroupOf P) ∪ kerLayerIndFam Z P := by
  refine Set.Subset.antisymm (fun f hf => ?_)
    (Set.union_subset (fun f hf => ?_) (kerLayerIndFam_mono bot_le))
  · obtain ⟨θ, hθ, rfl⟩ := mem_kerLayerIndFam.1 hf
    obtain ⟨hirr, -, hne⟩ := mem_kerLayerIrr.1 hθ
    by_cases hker : ((Z.subgroupOf P : Subgroup ↥P) : Set ↥P) ⊆ charValueKernel θ
    · refine Or.inr (indClassFun_mem_kerLayerIndFam (mem_kerLayerIrr.2 ⟨hirr, ?_, hne⟩))
      intro n hn
      exact mem_charValueKernel.1 (hker (Subgroup.mem_subgroupOf.2 hn))
    · refine Or.inl (indClassFun_mem_indFamDetect P (mem_irrDetect.2 ⟨?_, hker⟩))
      rw [← Irr_eq_irrChar]; exact hirr
  · obtain ⟨θ, hθ, rfl⟩ := (mem_indFamDetect P).1 hf
    rw [mem_irrDetect] at hθ
    refine indClassFun_mem_kerLayerIndFam (mem_kerLayerIrr.2 ⟨?_, ?_, ?_⟩)
    · rw [Irr_eq_irrChar]; exact hθ.1
    · intro n hn; rw [show n = 1 from Subtype.ext (Subgroup.mem_bot.1 hn)]
    · intro h; exact hθ.2 (by rw [h]; intro x _; exact mem_charValueKernel.2 rfl)

omit [Z.Normal] in
theorem indFamDetect_subset_kerLayerIndFam_bot :
    indFamDetect P (Z.subgroupOf P) ⊆ kerLayerIndFam (⊥ : Subgroup L) P := by
  rw [kerLayerIndFam_bot_eq_union (Z := Z)]
  exact Set.subset_union_left

omit [P.Normal] [Z.Normal] in
theorem kerLayerIndFam_commutator_subset_kerLayerIndFam_bot :
    kerLayerIndFam ⁅P, P⁆ P ⊆ kerLayerIndFam (⊥ : Subgroup L) P :=
  kerLayerIndFam_mono bot_le

theorem sum_weight_indFamDetectFinset :
    ∑ ξ ∈ indFamDetectFinset P (Z.subgroupOf P), ξ 1 ^ 2 / cfInner ξ ξ
      = (P.index : ℂ) * ((Nat.card ↥P : ℂ) - (Z.relIndex P : ℂ)) := by
  classical
  have hfs : kerLayerIndFinset (⊥ : Subgroup L) P
      = indFamDetectFinset P (Z.subgroupOf P) ∪ kerLayerIndFinset Z P := by
    ext f
    rw [Finset.mem_union, mem_kerLayerIndFinset, mem_indFamDetectFinset,
      mem_kerLayerIndFinset, kerLayerIndFam_bot_eq_union (Z := Z)]
    exact Set.mem_union _ _ _
  have hdisj : Disjoint (indFamDetectFinset P (Z.subgroupOf P)) (kerLayerIndFinset Z P) := by
    rw [Finset.disjoint_left]
    intro f hf hf'
    exact Set.disjoint_left.1 (disjoint_indFamDetect_kerLayerIndFam le_rfl)
      (mem_indFamDetectFinset.1 hf) (mem_kerLayerIndFinset.1 hf')
  have hsplit := Finset.sum_union (f := fun ξ : L → ℂ => ξ 1 ^ 2 / cfInner ξ ξ) hdisj
  rw [← hfs, sum_sq_degree_div_norm_kerLayerIndFinset (A := (⊥ : Subgroup L)) (K := P),
    sum_sq_degree_div_norm_kerLayerIndFinset (A := Z) (K := P),
    Subgroup.relIndex_bot_left] at hsplit
  linear_combination -hsplit

end Families

section Threshold

variable {L : Type*} [Group L] [Fintype L] {P E Z : Subgroup L} [P.Normal] [Z.Normal]

noncomputable abbrev fullFamily (P : Subgroup L) : Finset (L → ℂ) :=
  kerLayerIndFinset (⊥ : Subgroup L) P

noncomputable def joinedFamily (P Z : Subgroup L) : Finset (L → ℂ) :=
  ((finite_indFamDetect P (Z.subgroupOf P)).union
    (finite_kerLayerIndFam (A := ⁅P, P⁆) (K := P))).toFinset

omit [P.Normal] [Z.Normal] in
@[simp] theorem mem_joinedFamily {f : L → ℂ} :
    f ∈ joinedFamily P Z ↔
      f ∈ indFamDetect P (Z.subgroupOf P) ∨ f ∈ kerLayerIndFam ⁅P, P⁆ P := by
  rw [joinedFamily, Set.Finite.mem_toFinset]
  exact Set.mem_union _ _ _

omit [P.Normal] [Z.Normal] in
@[simp] theorem coe_joinedFamily :
    (joinedFamily P Z : Set (L → ℂ))
      = indFamDetect P (Z.subgroupOf P) ∪ kerLayerIndFam ⁅P, P⁆ P := by
  ext f
  simp [mem_joinedFamily]

theorem joinedFamily_subset : joinedFamily P Z ⊆ fullFamily P := by
  intro f hf
  rcases mem_joinedFamily.1 hf with h | h
  · exact mem_kerLayerIndFinset.2 (indFamDetect_subset_kerLayerIndFam_bot h)
  · exact mem_kerLayerIndFinset.2 (kerLayerIndFam_commutator_subset_kerLayerIndFam_bot h)

omit [P.Normal] [Z.Normal] in
theorem joinedFamily_eq_union :
    joinedFamily P Z = indFamDetectFinset P (Z.subgroupOf P) ∪ kerLayerIndFinset ⁅P, P⁆ P := by
  classical
  ext f
  rw [Finset.mem_union, mem_joinedFamily, mem_indFamDetectFinset, mem_kerLayerIndFinset]

omit [Fintype L] [P.Normal] [Z.Normal] in
theorem natCard_mul_relIndex (hZP : Z ≤ P) : Nat.card ↥Z * Z.relIndex P = Nat.card ↥P := by
  rw [Subgroup.relIndex, ← Subgroup.card_mul_index (Z.subgroupOf P)]
  congr 1
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv).symm

omit [Fintype L] [P.Normal] [Z.Normal] in
theorem subgroupOf_le_center (hZcent : Z ≤ Subgroup.centralizer (P : Set L)) :
    Z.subgroupOf P ≤ Subgroup.center ↥P := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have hxZ : (x : L) ∈ Z := Subgroup.mem_subgroupOf.1 hx
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hZcent hxZ) (y : L) y.2)

omit [Z.Normal] in
theorem exists_degree_sq_le_relIndex (hZcent : Z ≤ Subgroup.centralizer (P : Set L))
    {ψ : L → ℂ} (hψ : ψ ∈ kerLayerIndFam (⊥ : Subgroup L) P) :
    ∃ d : ℕ, ψ 1 = (P.index : ℂ) * (d : ℂ) ∧ d ^ 2 ≤ Z.relIndex P := by
  obtain ⟨θ, hθ, rfl⟩ := mem_kerLayerIndFam.1 hψ
  obtain ⟨hθirr, -, -⟩ := mem_kerLayerIrr.1 hθ
  obtain ⟨d, hd1, hdsq⟩ :=
    exists_degree_eq_and_sq_le_index_of_le_center hθirr (subgroupOf_le_center (P := P) hZcent)
  exact ⟨d, by rw [indClassFun_one_eq_index_mul, hd1], hdsq⟩

theorem two_mul_mul_le_of_sq_le_of_threshold (e d r z : ℕ) (hd : d ^ 2 ≤ r)
    (hthr : 4 * e ^ 2 ≤ r * (z - 1) ^ 2) : 2 * (e * (e * d)) ≤ e * (r * z - r) := by
  have hrz : r * z - r = r * (z - 1) := by
    cases z with
    | zero => omega
    | succ k => simp [Nat.mul_succ]
  rw [hrz]
  have key : 2 * (e * d) ≤ r * (z - 1) := by
    have h1 : (2 * (e * d)) ^ 2 ≤ (r * (z - 1)) ^ 2 :=
      calc (2 * (e * d)) ^ 2 = 4 * e ^ 2 * d ^ 2 := by ring
        _ ≤ (r * (z - 1) ^ 2) * r := Nat.mul_le_mul hthr hd
        _ = (r * (z - 1)) ^ 2 := by ring
    exact (Nat.pow_le_pow_iff_left (n := 2) (by norm_num)).1 h1
  calc 2 * (e * (e * d)) = e * (2 * (e * d)) := by ring
    _ ≤ e * (r * (z - 1)) := Nat.mul_le_mul_left e key

theorem two_mul_apply_one_mul_apply_one_lt_sum_weight {p a : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (ha : 1 ≤ a) (hPcard : Nat.card ↥P = p ^ a) (hLodd : Odd (Nat.card L))
    (hcompl : P.IsComplement' E) (hcop : (Nat.card ↥P).Coprime (Nat.card ↥E)) [Nontrivial ↥E]
    (hEcyc : IsCyclic ↥E) (hZbot : ⊥ < Z) (hZP : Z ≤ P) (hZP' : Z < ⁅P, P⁆)
    (hZcent : Z ≤ Subgroup.centralizer (P : Set L))
    (hmul : (P : Set L) * (E : Set L) = Set.univ)
    (hfix : FrobeniusQuotientLayer.FixesOnlyCommutatorCoset P E)
    (hcase : (∀ u ∈ E, u ≠ 1 → Z ⊓ Subgroup.centralizer {u} = ⊥) ∨
      (∀ u ∈ E, u ≠ 1 → P ⊓ Subgroup.centralizer {u} = Z))
    {ψ η : L → ℂ} (hψ : ψ ∈ fullFamily P) (hη : η ∈ kerLayerIndFam ⁅P, P⁆ P) :
    2 * ψ 1 * η 1 < ∑ γ ∈ joinedFamily P Z, γ 1 ^ 2 / cfInner γ γ := by
  classical
  set e := P.index with he
  have hthr : 4 * Nat.card ↥E ^ 2 ≤ Z.relIndex P * (Nat.card ↥Z - 1) ^ 2 :=
    four_mul_sq_natCard_le_relIndex_mul_sq_natCard_sub_one hp hpodd ha hPcard hLodd hcompl
      hcop hEcyc hZbot hZP' hZcent hcase
  have heE : e = Nat.card ↥E := by rw [he]; exact index_eq_card_of_isComplement' hcompl
  rw [← heE] at hthr
  obtain ⟨d, hd1, hdsq⟩ := exists_degree_sq_le_relIndex hZcent (mem_kerLayerIndFinset.1 hψ)
  have hη1 : η 1 = (e : ℂ) :=
    FrobeniusQuotientLayer.apply_one_of_mem_kerLayerIndFam_commutator hη
  have hnat := two_mul_mul_le_of_sq_le_of_threshold e d (Z.relIndex P) (Nat.card ↥Z) hdsq hthr
  have hPZ : Z.relIndex P * Nat.card ↥Z = Nat.card ↥P := by
    rw [Nat.mul_comm]; exact natCard_mul_relIndex hZP
  rw [hPZ] at hnat
  have hlhs : 2 * ψ 1 * η 1 = ((2 * (e * (e * d)) : ℕ) : ℂ) := by
    rw [hd1, hη1]; push_cast; ring
  have hrhs : ((e * (Nat.card ↥P - Z.relIndex P) : ℕ) : ℂ)
      = (e : ℂ) * ((Nat.card ↥P : ℂ) - (Z.relIndex P : ℂ)) := by
    have hle : Z.relIndex P ≤ Nat.card ↥P := by
      rw [← hPZ]; exact Nat.le_mul_of_pos_right _ Nat.card_pos
    push_cast [hle]
    ring
  have hstrict : ∑ ξ ∈ indFamDetectFinset P (Z.subgroupOf P), ξ 1 ^ 2 / cfInner ξ ξ
      < ∑ γ ∈ joinedFamily P Z, γ 1 ^ 2 / cfInner γ γ := by
    have hdisj :
        Disjoint (indFamDetectFinset P (Z.subgroupOf P)) (kerLayerIndFinset ⁅P, P⁆ P) := by
      rw [Finset.disjoint_left]
      intro f hf hf'
      exact Set.disjoint_left.1 (disjoint_indFamDetect_kerLayerIndFam_commutator hZP'.le)
        (mem_indFamDetectFinset.1 hf) (mem_kerLayerIndFinset.1 hf')
    rw [joinedFamily_eq_union, Finset.sum_union hdisj]
    have hepos : 0 < e := Nat.pos_of_ne_zero (by rw [he]; exact Subgroup.index_ne_zero_of_finite)
    have heC : (0 : ℂ) < (e : ℂ) := by exact_mod_cast hepos
    have hYpos : ∀ γ ∈ kerLayerIndFinset (⁅P, P⁆ : Subgroup L) P,
        (0 : ℂ) < γ 1 ^ 2 / cfInner γ γ := by
      intro γ hγ
      have hγ' := mem_kerLayerIndFinset.1 hγ
      rw [cfInner_self_of_mem_Irr
        (FrobeniusQuotientLayer.kerLayerIndFam_commutator_subset_Irr hmul hfix hγ'), div_one,
        FrobeniusQuotientLayer.apply_one_of_mem_kerLayerIndFam_commutator hγ']
      positivity
    have h1 : (0 : ℂ) < ∑ γ ∈ kerLayerIndFinset (⁅P, P⁆ : Subgroup L) P,
        γ 1 ^ 2 / cfInner γ γ :=
      Finset.sum_pos hYpos ⟨η, mem_kerLayerIndFinset.2 hη⟩
    simpa using add_lt_add_left h1
      (∑ ξ ∈ indFamDetectFinset P (Z.subgroupOf P), ξ 1 ^ 2 / cfInner ξ ξ)
  refine lt_of_le_of_lt ?_ hstrict
  rw [sum_weight_indFamDetectFinset, hlhs, ← hrhs]
  exact_mod_cast hnat

end Threshold

section Main

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
  {P E Z : Subgroup L} [P.Normal] [Z.Normal]
  {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}

omit [Group G] [Fintype G] [Z.Normal] in
theorem exists_degree_ratio {ψ η : L → ℂ} (hψ : ψ ∈ kerLayerIndFam (⊥ : Subgroup L) P)
    (hη : η ∈ kerLayerIndFam ⁅P, P⁆ P) :
    ∃ d : ℕ, 1 ≤ d ∧ ψ 1 = (d : ℂ) * η 1 := by
  obtain ⟨d, hd, hdvd, hd1⟩ :=
    NormalInducedFamily.exists_apply_one_eq_of_mem_indFam P (kerLayerIndFam_subset_indFam hψ)
  obtain ⟨m, hm⟩ := hdvd
  have hη1 : η 1 = (P.index : ℂ) :=
    FrobeniusQuotientLayer.apply_one_of_mem_kerLayerIndFam_commutator hη
  refine ⟨m, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm; omega
    · exact h0
  · rw [hd1, hη1, hm]
    push_cast
    ring

omit [Fintype L] [Group G] [Fintype G] [P.Normal] [Z.Normal] in
theorem ne_bot_of_natCard_eq_pow {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hPcard : Nat.card ↥P = p ^ a) : P ≠ ⊥ := by
  intro hbot
  have h1 : Nat.card ↥P = 1 := by rw [hbot]; exact Subgroup.card_bot
  rw [hPcard] at h1
  have := Nat.one_lt_pow (by omega : a ≠ 0) hp.one_lt
  omega

omit [Group G] [Fintype G] [P.Normal] [Z.Normal] in
theorem star_mem_joinedFamily {γ : L → ℂ} (hγ : γ ∈ joinedFamily P Z) :
    star γ ∈ joinedFamily P Z := by
  refine mem_joinedFamily.2 ?_
  rcases mem_joinedFamily.1 hγ with h | h
  · refine Or.inl ?_
    rw [indFamDetect_eq_indFam] at h ⊢
    exact DisjointCoherentFamilies.star_mem_indFam P (fun _ hθ => star_mem_irrDetect hθ) h
  · exact Or.inr (FrobeniusQuotientLayer.conj_mem_kerLayerIndFam_commutator h)

theorem isCoherentExtensionOf_of_joined_eq_full (hc : IsSubcoherent (fullFamily P) tau R)
    {ν₀ : Submodule.span ℤ (joinedFamily P Z : Set (L → ℂ)) →+ virtualChars G}
    (hν₀ : IsCoherentWith (joinedFamily P Z : Set (L → ℂ))
      (subTauHom hc joinedFamily_subset) ν₀)
    (heq : joinedFamily P Z = fullFamily P) :
    IsCoherentExtensionOf tau ν₀ (fullFamily P : Set (L → ℂ)) := by
  have h := isCoherentExtensionOf_self
    (τ₀ := subTauHom hc joinedFamily_subset)
    (fun f => subTauHom_apply hc joinedFamily_subset f) hν₀
  exact (congrArg (fun T : Finset (L → ℂ) => (T : Set (L → ℂ))) heq) ▸ h

theorem isCoherentExtensionOf_fullFamily_of_lt {p a : ℕ}
    (hc : IsSubcoherent (fullFamily P) tau R) (hp : p.Prime) (hpodd : Odd p) (ha : 1 ≤ a)
    (hPcard : Nat.card ↥P = p ^ a) (hLodd : Odd (Nat.card L)) (hcompl : P.IsComplement' E)
    (hcop : (Nat.card ↥P).Coprime (Nat.card ↥E)) [Nontrivial ↥E] (hEcyc : IsCyclic ↥E)
    (hZbot : ⊥ < Z) (hZP : Z ≤ P) (hZP' : Z < ⁅P, P⁆)
    (hZcent : Z ≤ Subgroup.centralizer (P : Set L))
    (hmul : (P : Set L) * (E : Set L) = Set.univ)
    (hfix : FrobeniusQuotientLayer.FixesOnlyCommutatorCoset P E)
    (hcase : (∀ u ∈ E, u ≠ 1 → Z ⊓ Subgroup.centralizer {u} = ⊥) ∨
      (∀ u ∈ E, u ≠ 1 → P ⊓ Subgroup.centralizer {u} = Z))
    {ν₀ : Submodule.span ℤ (joinedFamily P Z : Set (L → ℂ)) →+ virtualChars G}
    (hν₀ : IsCoherentWith (joinedFamily P Z : Set (L → ℂ))
      (subTauHom hc joinedFamily_subset) ν₀) :
    IsCoherentExtensionOf tau ν₀ (fullFamily P : Set (L → ℂ)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hPnil : Group.IsNilpotent ↥P := (IsPGroup.of_card hPcard).isNilpotent
  have hPsolv : Group.IsSolvable ↥P := inferInstance
  obtain ⟨η, hη⟩ := FrobeniusQuotientLayer.kerLayerIndFam_commutator_nonempty (K := P)
    (ne_bot_of_natCard_eq_pow hp ha hPcard)
  have hηJ : η ∈ joinedFamily P Z := mem_joinedFamily.2 (Or.inr hη)
  refine isCoherentExtensionOf_of_forall_threshold hc joinedFamily_subset
    (fun _ hγ => star_mem_joinedFamily hγ) hν₀ (fun χ hχ => ?_) ⟨η, hηJ⟩
  obtain ⟨d, hd, hdeg⟩ := exists_degree_ratio (mem_kerLayerIndFinset.1 hχ) hη
  exact ⟨η, hηJ, d, hd, hdeg,
    two_mul_apply_one_mul_apply_one_lt_sum_weight hp hpodd ha hPcard hLodd hcompl hcop hEcyc
      hZbot hZP hZP' hZcent hmul hfix hcase hχ hη⟩

theorem isCoherentExtensionOf_fullFamily {p a : ℕ} (hc : IsSubcoherent (fullFamily P) tau R)
    (hp : p.Prime) (hpodd : Odd p) (ha : 1 ≤ a) (hPcard : Nat.card ↥P = p ^ a)
    (hLodd : Odd (Nat.card L)) (hcompl : P.IsComplement' E)
    (hcop : (Nat.card ↥P).Coprime (Nat.card ↥E)) [Nontrivial ↥E] (hEcyc : IsCyclic ↥E)
    (hZbot : ⊥ < Z) (hZP : Z ≤ P) (hZP' : Z ≤ ⁅P, P⁆)
    (hZcent : Z ≤ Subgroup.centralizer (P : Set L))
    (hmul : (P : Set L) * (E : Set L) = Set.univ)
    (hfix : FrobeniusQuotientLayer.FixesOnlyCommutatorCoset P E)
    (hcase : (∀ u ∈ E, u ≠ 1 → Z ⊓ Subgroup.centralizer {u} = ⊥) ∨
      (∀ u ∈ E, u ≠ 1 → P ⊓ Subgroup.centralizer {u} = Z))
    {ν₀ : Submodule.span ℤ (joinedFamily P Z : Set (L → ℂ)) →+ virtualChars G}
    (hν₀ : IsCoherentWith (joinedFamily P Z : Set (L → ℂ))
      (subTauHom hc joinedFamily_subset) ν₀) :
    IsCoherentExtensionOf tau ν₀ (fullFamily P : Set (L → ℂ)) := by
  rcases lt_or_eq_of_le hZP' with hlt | rfl
  · exact isCoherentExtensionOf_fullFamily_of_lt hc hp hpodd ha hPcard hLodd hcompl hcop hEcyc
      hZbot hZP hlt hZcent hmul hfix hcase hν₀
  ·
    refine isCoherentExtensionOf_of_joined_eq_full hc hν₀ ?_
    ext f
    rw [mem_joinedFamily, mem_kerLayerIndFinset, kerLayerIndFam_bot_eq_union (Z := ⁅P, P⁆)]
    exact (Set.mem_union _ _ _).symm

theorem isCoherent_fullFamily {p a : ℕ} (hc : IsSubcoherent (fullFamily P) tau R)
    (hp : p.Prime) (hpodd : Odd p) (ha : 1 ≤ a) (hPcard : Nat.card ↥P = p ^ a)
    (hLodd : Odd (Nat.card L)) (hcompl : P.IsComplement' E)
    (hcop : (Nat.card ↥P).Coprime (Nat.card ↥E)) [Nontrivial ↥E] (hEcyc : IsCyclic ↥E)
    (hZbot : ⊥ < Z) (hZP : Z ≤ P) (hZP' : Z ≤ ⁅P, P⁆)
    (hZcent : Z ≤ Subgroup.centralizer (P : Set L))
    (hmul : (P : Set L) * (E : Set L) = Set.univ)
    (hfix : FrobeniusQuotientLayer.FixesOnlyCommutatorCoset P E)
    (hcase : (∀ u ∈ E, u ≠ 1 → Z ⊓ Subgroup.centralizer {u} = ⊥) ∨
      (∀ u ∈ E, u ≠ 1 → P ⊓ Subgroup.centralizer {u} = Z))
    {ν₀ : Submodule.span ℤ (joinedFamily P Z : Set (L → ℂ)) →+ virtualChars G}
    (hν₀ : IsCoherentWith (joinedFamily P Z : Set (L → ℂ))
      (subTauHom hc joinedFamily_subset) ν₀) :
    IsCoherent (fullFamily P : Set (L → ℂ)) (subTauHom hc Finset.Subset.rfl) :=
  (isCoherentExtensionOf_fullFamily hc hp hpodd ha hPcard hLodd hcompl hcop hEcyc hZbot hZP
    hZP' hZcent hmul hfix hcase hν₀).isCoherent
    (fun f => subTauHom_apply hc Finset.Subset.rfl f)

end Main

end CentralSectionFullExtension

end CFSG.FeitThompson
