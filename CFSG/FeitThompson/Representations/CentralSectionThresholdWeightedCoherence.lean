module

public import CFSG.FeitThompson.Representations.WeightedFeitInequalityConjugatePairExtension
public import CFSG.FeitThompson.Representations.NormalKernelLayerWeightedDegreeSum
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Representations.DisjointSupportCoherentFamiliesOrthogonal
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.CoherentNormalIrreducibleConjugation
import CFSG.FeitThompson.Representations.ProperNormalLayerDegreeIndexMember
import CFSG.FeitThompson.Representations.CentralSectionNormalDegreeBound
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
import Mathlib.Combinatorics.Matroid.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace CentralSectionCoherence

open NormalInducedFamily WeightedFeitExtension SolvableNormalLayer
open scoped ComplexOrder commutatorElement

section Layers

variable {L : Type*} [Group L] {A A' K : Subgroup L}

theorem star_mem_kerLayerIrr [Finite L] {θ : ↥K → ℂ} (hθ : θ ∈ kerLayerIrr A K) :
    star θ ∈ kerLayerIrr A K := by
  obtain ⟨hirr, hker, hne⟩ := mem_kerLayerIrr.1 hθ
  refine mem_kerLayerIrr.2 ⟨star_mem_Irr hirr, ?_, ?_⟩
  · intro n hn
    simp [Pi.star_apply, hker n hn]
  · exact fun h => hne (by rw [← star_star θ, h, star_one])

theorem star_mem_kerLayerIndFam [Fintype L] {f : L → ℂ} (hf : f ∈ kerLayerIndFam A K) :
    star f ∈ kerLayerIndFam A K := by
  obtain ⟨θ, hθ, rfl⟩ := mem_kerLayerIndFam.1 hf
  exact mem_kerLayerIndFam.2 ⟨star θ, star_mem_kerLayerIrr hθ,
    DisjointCoherentFamilies.indClassFun_star K θ⟩

theorem kerLayerIrr_mono (h : A' ≤ A) : kerLayerIrr A K ⊆ kerLayerIrr A' K := fun θ hθ => by
  obtain ⟨hirr, hker, hne⟩ := mem_kerLayerIrr.1 hθ
  exact mem_kerLayerIrr.2 ⟨hirr, fun n hn => hker n (h hn), hne⟩

theorem kerLayerIndFam_mono [Fintype L] (h : A' ≤ A) :
    kerLayerIndFam A K ⊆ kerLayerIndFam A' K := fun f hf => by
  obtain ⟨θ, hθ, rfl⟩ := mem_kerLayerIndFam.1 hf
  exact mem_kerLayerIndFam.2 ⟨θ, kerLayerIrr_mono h hθ, rfl⟩

theorem kerLayerIndFam_bot [Fintype L] :
    kerLayerIndFam (⊥ : Subgroup L) K = indFam K (Irr ↥K \ {1}) := by
  have h : kerLayerIrr (⊥ : Subgroup L) K = Irr ↥K \ {1} := by
    ext θ
    rw [mem_kerLayerIrr]
    refine ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ?_, h.2⟩⟩
    intro n hn
    rw [Subgroup.mem_bot] at hn
    rw [(Subtype.ext hn : n = 1)]
  ext f
  rw [mem_kerLayerIndFam, mem_indFam, h]

theorem coe_kerLayerIndFinset [Fintype L] (A K : Subgroup L) :
    (kerLayerIndFinset A K : Set (L → ℂ)) = kerLayerIndFam A K := by
  ext f
  simp only [Finset.mem_coe, mem_kerLayerIndFinset]

end Layers

section Weights

variable {L : Type*} [Group L] [Fintype L] {K : Subgroup L}

theorem exists_nonneg_weight [K.Normal] {f : L → ℂ} (hf : f ∈ indFam K (Irr ↥K)) :
    ∃ t : ℝ, 0 ≤ t ∧ f 1 ^ 2 / cfInner f f = (t : ℂ) := by
  obtain ⟨θ, hθ, rfl⟩ := mem_indFam K |>.1 hf
  obtain ⟨d, -, hd1⟩ := exists_apply_one_eq_of_mem_Irr hθ
  refine ⟨((K.index * d : ℕ) : ℝ) ^ 2 / (K.relIndex (inertiaGroup K θ) : ℝ), by positivity, ?_⟩
  rw [cfInner_self_indClassFun K hθ, indClassFun_one_eq_index_mul, hd1]
  push_cast
  ring

theorem weight_nonneg [K.Normal] {f : L → ℂ} (hf : f ∈ indFam K (Irr ↥K)) :
    (0 : ℂ) ≤ f 1 ^ 2 / cfInner f f := by
  obtain ⟨t, ht, h⟩ := exists_nonneg_weight hf
  rw [h]
  exact Complex.zero_le_real.2 ht

theorem weight_nonneg_of_mem_kerLayerIndFam {A : Subgroup L} [K.Normal] {f : L → ℂ}
    (hf : f ∈ kerLayerIndFam A K) : (0 : ℂ) ≤ f 1 ^ 2 / cfInner f f :=
  weight_nonneg (kerLayerIndFam_subset_indFam hf)

end Weights

section Transport

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
  {S : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}

theorem isCoherent_of_eq {U V : Set (L → ℂ)} (h : U = V)
    {τU : charSpanZero U →+ virtualChars G} {τV : charSpanZero V →+ virtualChars G}
    (hτ : ∀ (f : L → ℂ) (h1 : f ∈ charSpanZero U) (h2 : f ∈ charSpanZero V),
      (τU ⟨f, h1⟩ : G → ℂ) = (τV ⟨f, h2⟩ : G → ℂ))
    (hν : IsCoherent U τU) : IsCoherent V τV := by
  subst h
  have hτeq : τU = τV := AddMonoidHom.ext fun f => Subtype.ext (hτ _ f.2 f.2)
  subst hτeq
  exact hν

theorem subTauHom_congr (hc : IsSubcoherent S tau R) {U V : Set (L → ℂ)}
    (hU : U ⊆ (S : Set (L → ℂ))) (hV : V ⊆ (S : Set (L → ℂ)))
    (f : L → ℂ) (h1 : f ∈ charSpanZero U) (h2 : f ∈ charSpanZero V) :
    (subTauHom hc hU ⟨f, h1⟩ : G → ℂ) = (subTauHom hc hV ⟨f, h2⟩ : G → ℂ) := by
  rw [subTauHom_apply, subTauHom_apply]

theorem isCoherent_of_subset (hc : IsSubcoherent S tau R) {U P : Set (L → ℂ)}
    (hPU : P ⊆ U) (hUS : U ⊆ (S : Set (L → ℂ))) (hPS : P ⊆ (S : Set (L → ℂ)))
    (h : IsCoherent U (subTauHom hc hUS)) : IsCoherent P (subTauHom hc hPS) := by
  obtain ⟨ν, hν⟩ := isCoherent_iff.1 h
  refine isCoherent_iff.2 ⟨spanRestrict hPU ν, ⟨?_, ?_⟩⟩
  · intro f g
    rw [coe_spanRestrict_apply, coe_spanRestrict_apply]
    exact hν.inner_eq _ _
  · intro f
    have hfU : (f : L → ℂ) ∈ charSpanZero U :=
      mem_charSpanZero.2 ⟨Submodule.span_mono hPU (mem_charSpanZero.1 f.2).1,
        (mem_charSpanZero.1 f.2).2⟩
    have hkey : (ν (Submodule.inclusion (charSpanZero_le U) ⟨(f : L → ℂ), hfU⟩) : G → ℂ)
        = tau (f : L → ℂ) := by
      rw [hν.eq_on_zero ⟨(f : L → ℂ), hfU⟩, subTauHom_apply]
    refine Subtype.ext ?_
    rw [coe_spanRestrict_apply, subTauHom_apply]
    exact hkey

theorem isCoherent_of_card_le [DecidableEq (L → ℂ)] (hc : IsSubcoherent S tau R)
    {SA : Finset (L → ℂ)} (hSAS : (SA : Set (L → ℂ)) ⊆ (S : Set (L → ℂ)))
    (hSAstar : ∀ γ ∈ SA, star γ ∈ SA) {ψ₀ : L → ℂ} (hψ₀ : ψ₀ ∈ SA)
    (hcohSA : IsCoherent (SA : Set (L → ℂ)) (subTauHom hc hSAS)) :
    ∀ (n : ℕ) (U : Finset (L → ℂ)) (hUS : (U : Set (L → ℂ)) ⊆ (S : Set (L → ℂ))),
      SA ⊆ U → (∀ γ ∈ U, star γ ∈ U) → (U \ SA).card ≤ n →
      (∀ γ ∈ U, (0 : ℂ) ≤ γ 1 ^ 2 / cfInner γ γ) →
      (∀ χ ∈ U, χ ∉ SA → ∃ d : ℕ, 1 ≤ d ∧ χ 1 = (d : ℂ) * ψ₀ 1 ∧
        2 * χ 1 * ψ₀ 1 < ∑ γ ∈ SA, γ 1 ^ 2 / cfInner γ γ) →
      IsCoherent (U : Set (L → ℂ)) (subTauHom hc hUS) := by
  intro n
  induction n with
  | zero =>
    intro U hUS hSAU _ hcard _ _
    have hUSA : U = SA := Finset.Subset.antisymm (by
      intro x hx
      by_contra hxSA
      have hmem : x ∈ U \ SA := Finset.mem_sdiff.2 ⟨hx, hxSA⟩
      simp [Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)] at hmem) hSAU
    subst hUSA
    exact isCoherent_of_eq rfl (subTauHom_congr hc hSAS hUS) hcohSA
  | succ n ih =>
    intro U hUS hSAU hUstar hcard hnn hFeit
    by_cases hUSA : U ⊆ SA
    · have hUeq : U = SA := Finset.Subset.antisymm hUSA hSAU
      subst hUeq
      exact isCoherent_of_eq rfl (subTauHom_congr hc hSAS hUS) hcohSA
    obtain ⟨χ, hχU, hχSA⟩ := Finset.not_subset.1 hUSA
    have hχS : χ ∈ S := hUS hχU
    have hstarχU : star χ ∈ U := hUstar χ hχU
    have hstarχSA : star χ ∉ SA := fun h => hχSA (by
      have h' := hSAstar _ h; rwa [star_star] at h')
    have hne : star χ ≠ χ := hc.star_ne χ hχS
    set U' : Finset (L → ℂ) := U \ {χ, star χ} with hU'
    have hmemU' : ∀ γ, γ ∈ U' ↔ (γ ∈ U ∧ γ ≠ χ ∧ γ ≠ star χ) := fun γ => by
      simp [hU', Finset.mem_sdiff, Finset.mem_insert, not_or]
    have hSAU' : SA ⊆ U' := fun γ hγ =>
      (hmemU' γ).2 ⟨hSAU hγ, fun h => hχSA (h ▸ hγ), fun h => hstarχSA (h ▸ hγ)⟩
    have hU'S : (U' : Set (L → ℂ)) ⊆ (S : Set (L → ℂ)) := fun γ hγ =>
      hUS ((hmemU' γ).1 (by exact_mod_cast hγ)).1
    have hU'star : ∀ γ ∈ U', star γ ∈ U' := by
      intro γ hγ
      obtain ⟨hγU, h1, h2⟩ := (hmemU' γ).1 hγ
      refine (hmemU' _).2 ⟨hUstar γ hγU, fun h => h2 ?_, fun h => h1 (star_injective h)⟩
      rw [← h, star_star]
    have hpairsub : ({χ, star χ} : Finset (L → ℂ)) ⊆ U \ SA := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Finset.mem_sdiff.2 ⟨hχU, hχSA⟩
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact Finset.mem_sdiff.2 ⟨hstarχU, hstarχSA⟩
    have hcard' : (U' \ SA).card ≤ n := by
      have heq : U' \ SA = (U \ SA) \ {χ, star χ} := by
        ext x
        simp only [hU', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have hpc : ({χ, star χ} : Finset (L → ℂ)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa using Ne.symm hne), Finset.card_singleton]
      have hle : 2 ≤ (U \ SA).card := by
        rw [← hpc]; exact Finset.card_le_card hpairsub
      rw [heq, Finset.card_sdiff, Finset.inter_eq_left.2 hpairsub, hpc]
      omega
    obtain ⟨ν, hν⟩ := isCoherent_iff.1 (ih U' hU'S hSAU' hU'star hcard'
      (fun γ hγ => hnn γ ((hmemU' γ).1 hγ).1)
      (fun γ hγ hγSA => hFeit γ ((hmemU' γ).1 hγ).1 hγSA))
    obtain ⟨d, hd, hdeg, hlt⟩ := hFeit χ hχU hχSA
    have hFeit' : 2 * χ 1 * ψ₀ 1 < ∑ γ ∈ U', γ 1 ^ 2 / cfInner γ γ :=
      lt_of_lt_of_le hlt (Finset.sum_le_sum_of_subset_of_nonneg hSAU'
        (fun i hi _ => hnn i ((hmemU' i).1 hi).1))
    have hχU' : χ ∉ U' := fun h => ((hmemU' χ).1 h).2.1 rfl
    have key := isCoherent_insertPair (χ := χ) (ψ := ψ₀) hc
      (by exact_mod_cast hU'S) ⟨ψ₀, hSAU' hψ₀⟩ hU'star hν
      (fun f => subTauHom_apply hc hU'S f) (hSAU' hψ₀) hχS hχU' hd hdeg hFeit'
    refine isCoherent_of_eq ?_ (subTauHom_congr hc _ hUS) key
    ext x
    rw [mem_insertPair_iff]
    simp only [Finset.mem_coe, hmemU']
    constructor
    · rintro (rfl | rfl | ⟨h, -, -⟩)
      · exact hχU
      · exact hstarχU
      · exact h
    · intro hx
      by_cases h1 : x = χ
      · exact Or.inl h1
      by_cases h2 : x = star χ
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨hx, h1, h2⟩)

end Transport

section Bound

variable {L : Type*} [Group L] {B C D K : Subgroup L}

theorem commutator_subgroupOf_le (hcomm : ⁅D, C⁆ ≤ B) :
    ⁅D.subgroupOf K, C.subgroupOf K⁆ ≤ B.subgroupOf K := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.mem_subgroupOf]
  have h := Subgroup.commutator_le.1 hcomm (x : L) (Subgroup.mem_subgroupOf.1 hx) (y : L)
    (Subgroup.mem_subgroupOf.1 hy)
  simpa [commutatorElement_def] using h

theorem apply_one_le_relIndex_mul_sqrt [Finite L] [B.Normal] (hBD : B ≤ D) (hDC : D ≤ C)
    (hCK : C ≤ K) (hcomm : ⁅D, C⁆ ≤ B) {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K)
    (hker : ∀ n : ↥K, (n : L) ∈ B → θ n = θ 1) :
    ‖θ 1‖ ≤ (C.relIndex K : ℝ) * Real.sqrt (D.relIndex C) := by
  have _ : (B.subgroupOf K).Normal := ‹B.Normal›.subgroupOf K
  have h := apply_one_le_index_mul_sqrt_relIndex_of_commutator_le
    (B := B.subgroupOf K) (D := D.subgroupOf K) (C := C.subgroupOf K)
    (Subgroup.subgroupOf_mono K hBD) (Subgroup.subgroupOf_mono K hDC)
    (commutator_subgroupOf_le hcomm) hθ
    (fun n hn => mem_charValueKernel.2 (hker n (Subgroup.mem_subgroupOf.1 hn)))
  rwa [Subgroup.relIndex_subgroupOf hCK, ← Subgroup.relIndex] at h

theorem exists_degree_le_of_mem_kerLayerIndFam [Fintype L] [B.Normal] (hBD : B ≤ D) (hDC : D ≤ C)
    (hCK : C ≤ K) (hcomm : ⁅D, C⁆ ≤ B) {χ : L → ℂ} (hχ : χ ∈ kerLayerIndFam B K) :
    ∃ d : ℕ, 1 ≤ d ∧ χ 1 = (d : ℂ) * (K.index : ℂ) ∧
      (d : ℝ) ≤ (C.relIndex K : ℝ) * Real.sqrt (D.relIndex C) := by
  obtain ⟨θ, hθ, rfl⟩ := mem_kerLayerIndFam.1 hχ
  obtain ⟨hirr, hker, -⟩ := mem_kerLayerIrr.1 hθ
  obtain ⟨d, hd, hd1⟩ := exists_apply_one_eq_of_mem_Irr hirr
  refine ⟨d, hd, by rw [indClassFun_one_eq_index_mul, hd1]; ring, ?_⟩
  have h := apply_one_le_relIndex_mul_sqrt hBD hDC hCK hcomm hirr hker
  rwa [hd1, Complex.norm_natCast] at h

end Bound

section Main

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
  {S : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}
  {A B C D K : Subgroup L}

theorem isCoherent_kerLayerIndFam_union (hc : IsSubcoherent S tau R)
    [K.Normal] [Group.IsSolvable ↥K] [A.Normal] [B.Normal]
    (hAK : A < K) (hBD : B ≤ D) (hDC : D ≤ C) (hCK : C ≤ K) (hcomm : ⁅D, C⁆ ≤ B)
    (hAS : kerLayerIndFam A K ⊆ (S : Set (L → ℂ)))
    (hUS : kerLayerIndFam A K ∪ kerLayerIndFam B K ⊆ (S : Set (L → ℂ)))
    (hcohA : IsCoherent (kerLayerIndFam A K) (subTauHom hc hAS))
    (hthr : 2 * (C.index : ℝ) * Real.sqrt (D.relIndex C) < (A.relIndex K : ℝ) - 1) :
    IsCoherent (kerLayerIndFam A K ∪ kerLayerIndFam B K) (subTauHom hc hUS) := by
  classical
  have hKpos : (0 : ℝ) < (K.index : ℝ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
  set SA : Finset (L → ℂ) := kerLayerIndFinset A K with hSA
  set SB : Finset (L → ℂ) := kerLayerIndFinset B K with hSB
  have hSAcoe : (SA : Set (L → ℂ)) = kerLayerIndFam A K := coe_kerLayerIndFinset A K
  have hSBcoe : (SB : Set (L → ℂ)) = kerLayerIndFam B K := coe_kerLayerIndFinset B K
  set U : Finset (L → ℂ) := SA ∪ SB with hU
  have hUcoe : (U : Set (L → ℂ)) = kerLayerIndFam A K ∪ kerLayerIndFam B K := by
    rw [hU, Finset.coe_union, hSAcoe, hSBcoe]
  have hSAS' : (SA : Set (L → ℂ)) ⊆ (S : Set (L → ℂ)) := hSAcoe ▸ hAS
  have hUS' : (U : Set (L → ℂ)) ⊆ (S : Set (L → ℂ)) := hUcoe ▸ hUS
  obtain ⟨θ₀, hθ₀, hne₀, hker₀, h1₀, hdeg₀⟩ :=
    exists_mem_Irr_indClassFun_one_eq_index_of_lt (A := A) hAK
  set ψ₀ : L → ℂ := indClassFun K θ₀ with hψ₀def
  have hψ₀A : ψ₀ ∈ kerLayerIndFam A K :=
    indClassFun_mem_kerLayerIndFam (mem_kerLayerIrr.2 ⟨hθ₀,
      fun n hn => mem_charValueKernel.1 (hker₀ (Subgroup.mem_subgroupOf.2 hn)), hne₀⟩)
  have hψ₀ : ψ₀ ∈ SA := mem_kerLayerIndFinset.2 hψ₀A
  have hψ₀deg : ψ₀ 1 = (K.index : ℂ) := hdeg₀
  have hsum : ∑ γ ∈ SA, γ 1 ^ 2 / cfInner γ γ = (K.index : ℂ) * ((A.relIndex K : ℂ) - 1) :=
    sum_sq_degree_div_norm_kerLayerIndFinset
  have hFeit : ∀ χ ∈ U, χ ∉ SA → ∃ d : ℕ, 1 ≤ d ∧ χ 1 = (d : ℂ) * ψ₀ 1 ∧
      2 * χ 1 * ψ₀ 1 < ∑ γ ∈ SA, γ 1 ^ 2 / cfInner γ γ := by
    intro χ hχU hχSA
    have hχB : χ ∈ kerLayerIndFam B K := by
      rcases Finset.mem_union.1 hχU with h | h
      · exact absurd h hχSA
      · exact hSBcoe ▸ (Finset.mem_coe.2 h)
    obtain ⟨d, hd, hdeg, hdle⟩ :=
      exists_degree_le_of_mem_kerLayerIndFam hBD hDC hCK hcomm hχB
    refine ⟨d, hd, by rw [hdeg, hψ₀deg], ?_⟩
    have hidx : (K.index : ℝ) * (C.relIndex K : ℝ) = (C.index : ℝ) := by
      have h : C.relIndex K * K.index = C.index := Subgroup.relIndex_mul_index hCK
      rw [mul_comm]
      exact_mod_cast congrArg (Nat.cast (R := ℝ)) h
    have hkey : 2 * ((d : ℝ) * (K.index : ℝ)) * (K.index : ℝ)
        < (K.index : ℝ) * ((A.relIndex K : ℝ) - 1) := by
      have hstep : 2 * ((d : ℝ) * (K.index : ℝ)) * (K.index : ℝ)
          ≤ 2 * (C.index : ℝ) * Real.sqrt (D.relIndex C) * (K.index : ℝ) := by
        have := mul_le_mul_of_nonneg_left hdle (by positivity : (0 : ℝ) ≤ 2 * (K.index : ℝ))
        calc 2 * ((d : ℝ) * (K.index : ℝ)) * (K.index : ℝ)
            = (2 * (K.index : ℝ) * (d : ℝ)) * (K.index : ℝ) := by ring
          _ ≤ (2 * (K.index : ℝ) * ((C.relIndex K : ℝ) * Real.sqrt (D.relIndex C)))
              * (K.index : ℝ) := by
              refine mul_le_mul_of_nonneg_right ?_ hKpos.le
              calc 2 * (K.index : ℝ) * (d : ℝ)
                  = 2 * (K.index : ℝ) * (d : ℝ) := rfl
                _ ≤ 2 * (K.index : ℝ) * ((C.relIndex K : ℝ) * Real.sqrt (D.relIndex C)) := this
          _ = 2 * (C.index : ℝ) * Real.sqrt (D.relIndex C) * (K.index : ℝ) := by
              rw [← hidx]; ring
      refine lt_of_le_of_lt hstep ?_
      calc 2 * (C.index : ℝ) * Real.sqrt (D.relIndex C) * (K.index : ℝ)
          < ((A.relIndex K : ℝ) - 1) * (K.index : ℝ) := by
            exact mul_lt_mul_of_pos_right hthr hKpos
        _ = (K.index : ℝ) * ((A.relIndex K : ℝ) - 1) := by ring
    rw [hdeg, hψ₀deg, hsum]
    have hleft : 2 * ((d : ℂ) * (K.index : ℂ)) * (K.index : ℂ)
        = ((2 * ((d : ℝ) * (K.index : ℝ)) * (K.index : ℝ) : ℝ) : ℂ) := by push_cast; ring
    have hright : (K.index : ℂ) * ((A.relIndex K : ℂ) - 1)
        = (((K.index : ℝ) * ((A.relIndex K : ℝ) - 1) : ℝ) : ℂ) := by push_cast; ring
    rw [hleft, hright]
    exact Complex.real_lt_real.2 hkey
  refine isCoherent_of_eq hUcoe (subTauHom_congr hc hUS' hUS) ?_
  refine isCoherent_of_card_le hc hSAS' ?_ hψ₀
    (isCoherent_of_eq hSAcoe.symm (subTauHom_congr hc hAS hSAS') hcohA)
    (U \ SA).card U hUS' Finset.subset_union_left ?_ le_rfl ?_ hFeit
  · exact fun γ hγ => mem_kerLayerIndFinset.2 (star_mem_kerLayerIndFam
      (mem_kerLayerIndFinset.1 hγ))
  · intro γ hγ
    rcases Finset.mem_union.1 hγ with h | h
    · exact Finset.mem_union_left _
        (mem_kerLayerIndFinset.2 (star_mem_kerLayerIndFam (mem_kerLayerIndFinset.1 h)))
    · exact Finset.mem_union_right _
        (mem_kerLayerIndFinset.2 (star_mem_kerLayerIndFam (mem_kerLayerIndFinset.1 h)))
  · intro γ hγ
    rcases Finset.mem_union.1 hγ with h | h
    · exact weight_nonneg_of_mem_kerLayerIndFam (mem_kerLayerIndFinset.1 h)
    · exact weight_nonneg_of_mem_kerLayerIndFam (mem_kerLayerIndFinset.1 h)

theorem isCoherent_kerLayerIndFam_of_lt (hc : IsSubcoherent S tau R)
    [K.Normal] [Group.IsSolvable ↥K] [A.Normal] [B.Normal]
    (hAK : A < K) (hBD : B ≤ D) (hDC : D ≤ C) (hCK : C ≤ K) (hcomm : ⁅D, C⁆ ≤ B)
    (hAS : kerLayerIndFam A K ⊆ (S : Set (L → ℂ)))
    (hBS : kerLayerIndFam B K ⊆ (S : Set (L → ℂ)))
    (hUS : kerLayerIndFam A K ∪ kerLayerIndFam B K ⊆ (S : Set (L → ℂ)))
    (hcohA : IsCoherent (kerLayerIndFam A K) (subTauHom hc hAS))
    (hthr : 2 * (C.index : ℝ) * Real.sqrt (D.relIndex C) < (A.relIndex K : ℝ) - 1) :
    IsCoherent (kerLayerIndFam B K) (subTauHom hc hBS) :=
  isCoherent_of_subset hc Set.subset_union_right hUS hBS
    (isCoherent_kerLayerIndFam_union hc hAK hBD hDC hCK hcomm hAS hUS hcohA hthr)

theorem le_two_mul_index_mul_sqrt_of_not_isCoherent (hc : IsSubcoherent S tau R)
    [K.Normal] [Group.IsSolvable ↥K] [A.Normal] [B.Normal]
    (hAK : A < K) (hBD : B ≤ D) (hDC : D ≤ C) (hCK : C ≤ K) (hcomm : ⁅D, C⁆ ≤ B)
    (hAS : kerLayerIndFam A K ⊆ (S : Set (L → ℂ)))
    (hBS : kerLayerIndFam B K ⊆ (S : Set (L → ℂ)))
    (hUS : kerLayerIndFam A K ∪ kerLayerIndFam B K ⊆ (S : Set (L → ℂ)))
    (hcohA : IsCoherent (kerLayerIndFam A K) (subTauHom hc hAS))
    (hnB : ¬ IsCoherent (kerLayerIndFam B K) (subTauHom hc hBS)) :
    (A.relIndex K : ℝ) - 1 ≤ 2 * (C.index : ℝ) * Real.sqrt (D.relIndex C) :=
  le_of_not_gt fun hthr =>
    hnB (isCoherent_kerLayerIndFam_of_lt hc hAK hBD hDC hCK hcomm hAS hBS hUS hcohA hthr)

theorem isCoherent_kerLayerIndFam_union_of_le_center (hc : IsSubcoherent S tau R)
    [K.Normal] [Group.IsSolvable ↥K] [A.Normal] [B.Normal]
    (hAK : A < K) (hBD : B ≤ D) (hDC : D ≤ C) (hCK : C ≤ K)
    (hcen : (D.subgroupOf C).map (QuotientGroup.mk' (B.subgroupOf C)) ≤
      Subgroup.center (C ⧸ B.subgroupOf C))
    (hAS : kerLayerIndFam A K ⊆ (S : Set (L → ℂ)))
    (hUS : kerLayerIndFam A K ∪ kerLayerIndFam B K ⊆ (S : Set (L → ℂ)))
    (hcohA : IsCoherent (kerLayerIndFam A K) (subTauHom hc hAS))
    (hthr : 2 * (C.index : ℝ) * Real.sqrt (D.relIndex C) < (A.relIndex K : ℝ) - 1) :
    IsCoherent (kerLayerIndFam A K ∪ kerLayerIndFam B K) (subTauHom hc hUS) :=
  isCoherent_kerLayerIndFam_union hc hAK hBD hDC hCK
    ((map_mk'_subgroupOf_le_center_iff hDC).1 hcen) hAS hUS hcohA hthr

theorem kerLayerIndFam_subset_of_eq_bot (hS : (S : Set (L → ℂ)) = kerLayerIndFam ⊥ K)
    (A : Subgroup L) : kerLayerIndFam A K ⊆ (S : Set (L → ℂ)) :=
  hS ▸ kerLayerIndFam_mono bot_le

theorem kerLayerIndFam_union_subset_of_eq_bot (hS : (S : Set (L → ℂ)) = kerLayerIndFam ⊥ K)
    (A B : Subgroup L) :
    kerLayerIndFam A K ∪ kerLayerIndFam B K ⊆ (S : Set (L → ℂ)) :=
  Set.union_subset (kerLayerIndFam_subset_of_eq_bot hS A) (kerLayerIndFam_subset_of_eq_bot hS B)

theorem isCoherent_kerLayerIndFam_union_of_eq_bot (hc : IsSubcoherent S tau R)
    [K.Normal] [Group.IsSolvable ↥K] [A.Normal] [B.Normal]
    (hS : (S : Set (L → ℂ)) = kerLayerIndFam ⊥ K)
    (hAK : A < K) (hBD : B ≤ D) (hDC : D ≤ C) (hCK : C ≤ K) (hcomm : ⁅D, C⁆ ≤ B)
    (hcohA : IsCoherent (kerLayerIndFam A K)
      (subTauHom hc (kerLayerIndFam_subset_of_eq_bot hS A)))
    (hthr : 2 * (C.index : ℝ) * Real.sqrt (D.relIndex C) < (A.relIndex K : ℝ) - 1) :
    IsCoherent (kerLayerIndFam A K ∪ kerLayerIndFam B K)
      (subTauHom hc (kerLayerIndFam_union_subset_of_eq_bot hS A B)) :=
  isCoherent_kerLayerIndFam_union hc hAK hBD hDC hCK hcomm _ _ hcohA hthr

theorem isCoherent_kerLayerIndFam_of_eq_bot (hc : IsSubcoherent S tau R)
    [K.Normal] [Group.IsSolvable ↥K] [A.Normal] [B.Normal]
    (hS : (S : Set (L → ℂ)) = kerLayerIndFam ⊥ K)
    (hAK : A < K) (hBD : B ≤ D) (hDC : D ≤ C) (hCK : C ≤ K) (hcomm : ⁅D, C⁆ ≤ B)
    (hcohA : IsCoherent (kerLayerIndFam A K)
      (subTauHom hc (kerLayerIndFam_subset_of_eq_bot hS A)))
    (hthr : 2 * (C.index : ℝ) * Real.sqrt (D.relIndex C) < (A.relIndex K : ℝ) - 1) :
    IsCoherent (kerLayerIndFam B K) (subTauHom hc (kerLayerIndFam_subset_of_eq_bot hS B)) :=
  isCoherent_kerLayerIndFam_of_lt hc hAK hBD hDC hCK hcomm _ _
    (kerLayerIndFam_union_subset_of_eq_bot hS A B) hcohA hthr

theorem le_two_mul_index_mul_sqrt_of_not_isCoherent_of_eq_bot (hc : IsSubcoherent S tau R)
    [K.Normal] [Group.IsSolvable ↥K] [A.Normal] [B.Normal]
    (hS : (S : Set (L → ℂ)) = kerLayerIndFam ⊥ K)
    (hAK : A < K) (hBD : B ≤ D) (hDC : D ≤ C) (hCK : C ≤ K) (hcomm : ⁅D, C⁆ ≤ B)
    (hcohA : IsCoherent (kerLayerIndFam A K)
      (subTauHom hc (kerLayerIndFam_subset_of_eq_bot hS A)))
    (hnB : ¬ IsCoherent (kerLayerIndFam B K)
      (subTauHom hc (kerLayerIndFam_subset_of_eq_bot hS B))) :
    (A.relIndex K : ℝ) - 1 ≤ 2 * (C.index : ℝ) * Real.sqrt (D.relIndex C) :=
  le_two_mul_index_mul_sqrt_of_not_isCoherent hc hAK hBD hDC hCK hcomm _ _
    (kerLayerIndFam_union_subset_of_eq_bot hS A B) hcohA hnB

end Main

end CentralSectionCoherence

end CFSG.FeitThompson
