module

public import CFSG.FeitThompson.Representations.WeightedFeitInequalityConjugatePairExtension
public import CFSG.FeitThompson.Representations.CentralFrobeniusLayerDegreeSquareSum
public import CFSG.FeitThompson.Representations.BlockDifferenceOrthogonalConstantOffCore
public import CFSG.FeitThompson.Representations.FreeCentralSectionInducedLayerIrreducible
import CFSG.FeitThompson.Representations.CentralLayerCoherenceExtension
import CFSG.FeitThompson.Representations.EqualDegreeBlocksImagesSupportedPairs
import CFSG.FeitThompson.Representations.CentralLayerDegreeSquareDivisor
import CFSG.FeitThompson.Representations.SmallerDegreeBlocksStrictFeit
import CFSG.FeitThompson.Representations.EqualDegreeSubcoherenceExtendsToFamily

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open WeightedFeitExtension Subgroup
open scoped ComplexOrder

section Abstract

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
  {S : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}

theorem isCoherent_subTauHom_congr (hc : IsSubcoherent S tau R) {U U' : Set (L → ℂ)}
    (hUU' : U = U') {hUS : U ⊆ (S : Set (L → ℂ))} {hU'S : U' ⊆ (S : Set (L → ℂ))}
    (h : IsCoherent U (subTauHom hc hUS)) : IsCoherent U' (subTauHom hc hU'S) := by
  subst hUU'; exact h

theorem IsSubcoherent.subset {T : Finset (L → ℂ)} (hc : IsSubcoherent S tau R) (hTS : T ⊆ S)
    (hTstar : ∀ χ ∈ T, star χ ∈ T) : IsSubcoherent T tau R := by
  have mono : intSpanZeroAtOne (T : Set (L → ℂ)) ≤ intSpanZeroAtOne (S : Set (L → ℂ)) := by
    intro f hf
    exact mem_intSpanZeroAtOne.2 ⟨Submodule.span_mono (by exact_mod_cast hTS)
      (mem_intSpanZeroAtOne.1 hf).1, (mem_intSpanZeroAtOne.1 hf).2⟩
  exact
  { isCharacter := fun χ hχ => hc.isCharacter χ (hTS hχ)
    ne_zero := fun χ hχ => hc.ne_zero χ (hTS hχ)
    star_mem := hTstar
    star_ne := fun χ hχ => hc.star_ne χ (hTS hχ)
    charInner_eq_zero := fun χ hχ ψ hψ hne => hc.charInner_eq_zero χ (hTS hχ) ψ (hTS hψ) hne
    map_add := fun f hf g hg => hc.map_add f (mono hf) g (mono hg)
    tau_mem := fun f hf => hc.tau_mem f (mono hf)
    charInner_tau_tau := fun f hf g hg => hc.charInner_tau_tau f (mono hf) g (mono hg)
    tau_apply_one := fun f hf => hc.tau_apply_one f (mono hf)
    R_subset := fun χ hχ r hr => hc.R_subset χ (hTS hχ) r hr
    charInner_R_self := fun χ hχ r hr => hc.charInner_R_self χ (hTS hχ) r hr
    charInner_R_of_ne := fun χ hχ r hr s hs hne => hc.charInner_R_of_ne χ (hTS hχ) r hr s hs hne
    tau_sub_star := fun χ hχ => hc.tau_sub_star χ (hTS hχ)
    charInner_R_R := fun χ hχ ψ hψ h1 h2 => hc.charInner_R_R χ (hTS hχ) ψ (hTS hψ) h1 h2 }

theorem isCoherent_of_prime_power_degrees (hc : IsSubcoherent S tau R)
    {X : Finset (L → ℂ)} (hXS : X ⊆ S) (hXne : X.Nonempty)
    (hXstar : ∀ χ ∈ X, star χ ∈ X) (hnorm : ∀ χ ∈ X, cfInner χ χ = 1)
    {p e M : ℕ} (hp : 3 ≤ p) (he : 1 ≤ e)
    (hform : ∀ χ ∈ X, ∃ b : ℕ, χ 1 = ((e * p ^ b : ℕ) : ℂ) ∧ (e * p ^ b) ^ 2 ∣ M)
    (hsum : ∃ t : ℕ, ∑ χ ∈ X, χ 1 ^ 2 = (t : ℂ) * (M : ℂ))
    (τX : charSpanZero (X : Set (L → ℂ)) →+ virtualChars G)
    (hτX : ∀ f, (τX f : G → ℂ) = tau (f : L → ℂ)) :
    IsCoherent (X : Set (L → ℂ)) τX := by
  classical
  have coeS : ∀ {T : Finset (L → ℂ)}, T ⊆ X → (T : Set (L → ℂ)) ⊆ (S : Set (L → ℂ)) :=
    fun hT => Finset.coe_subset.2 (hT.trans hXS)
  refine IsCoherent.congr_baseline (τ := subTauHom hc (coeS (le_refl X)))
    (fun f => by rw [subTauHom_apply, hτX]) ?_
  choose! bb hbb hbbdvd using hform
  set dg : (L → ℂ) → ℕ := fun χ => e * p ^ bb χ with hdgdef
  have hdg : ∀ χ ∈ X, χ 1 = (dg χ : ℂ) := hbb
  have hdvd : ∀ χ ∈ X, dg χ ^ 2 ∣ M := hbbdvd
  have hMsum : M ∣ ∑ χ ∈ X, dg χ ^ 2 := by
    obtain ⟨t, ht⟩ := hsum
    have hcast : ((∑ χ ∈ X, dg χ ^ 2 : ℕ) : ℂ) = ((t * M : ℕ) : ℂ) := by
      push_cast
      rw [← ht]
      exact Finset.sum_congr rfl fun χ hχ => by rw [hdg χ hχ]
    exact Dvd.intro_left t (Nat.cast_injective hcast).symm
  obtain ⟨χ₀, hχ₀X, hχ₀min⟩ := X.exists_min_image dg hXne
  set d₀ := dg χ₀ with hd₀
  set B₀ : Finset (L → ℂ) := X.filter (fun χ => dg χ = d₀) with hB₀
  have hB₀X : B₀ ⊆ X := Finset.filter_subset _ _
  have hstardg : ∀ χ ∈ X, dg (star χ) = dg χ := by
    intro χ hχ
    have h1 : ((dg (star χ) : ℂ)) = ((dg χ : ℂ)) := by
      rw [← hdg _ (hXstar χ hχ), ← hdg χ hχ, Pi.star_apply, hdg χ hχ]
      simp
    exact_mod_cast h1
  have hB₀star : ∀ χ ∈ B₀, star χ ∈ B₀ := by
    intro χ hχ
    rw [hB₀, Finset.mem_filter] at hχ ⊢
    exact ⟨hXstar χ hχ.1, by rw [hstardg χ hχ.1, hχ.2]⟩
  have hcohB₀ : IsCoherent (B₀ : Set (L → ℂ)) (subTauHom hc (coeS hB₀X)) := by
    refine (hc.subset (hB₀X.trans hXS) hB₀star).isCoherent_of_uniform_degree
      (subTauHom hc (coeS hB₀X)) (fun f => subTauHom_apply hc (coeS hB₀X) f) ?_
    intro χ hχ ψ hψ
    rw [hB₀, Finset.mem_filter] at hχ hψ
    rw [hdg χ hχ.1, hdg ψ hψ.1, hχ.2, hψ.2]
  suffices H : ∀ n : ℕ, ∀ T : Finset (L → ℂ), (X \ T).card ≤ n → ∀ hTX : T ⊆ X,
      (∀ χ ∈ T, star χ ∈ T) → B₀ ⊆ T →
      IsCoherent (T : Set (L → ℂ)) (subTauHom hc (coeS hTX)) →
      IsCoherent (X : Set (L → ℂ)) (subTauHom hc (coeS (le_refl X))) by
    exact H (X \ B₀).card B₀ le_rfl hB₀X hB₀star (fun _ h => h) hcohB₀
  intro n
  induction n with
  | zero =>
      intro T hcard hTX _ _ hcoh
      have hXT : X ⊆ T :=
        Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 (Nat.le_zero.1 hcard))
      exact isCoherent_subTauHom_congr hc
        (show (T : Set (L → ℂ)) = (X : Set (L → ℂ)) by
          rw [Finset.Subset.antisymm hTX hXT]) hcoh
  | succ n ih =>
      intro T hcard hTX hTstar hB₀T hcoh
      by_cases hXT : X ⊆ T
      · exact isCoherent_subTauHom_congr hc
          (show (T : Set (L → ℂ)) = (X : Set (L → ℂ)) by
            rw [Finset.Subset.antisymm hTX hXT]) hcoh
      ·
        have hne : (X \ T).Nonempty := by rw [Finset.sdiff_nonempty]; exact hXT
        obtain ⟨γ, hγ, hγmin⟩ := (X \ T).exists_min_image dg hne
        rw [Finset.mem_sdiff] at hγ
        obtain ⟨hγX, hγT⟩ := hγ
        have hd₀lt : d₀ < dg γ := by
          rcases lt_or_eq_of_le (hχ₀min γ hγX) with hlt | heq
          · exact hlt
          · exact absurd (hB₀T (by rw [hB₀, Finset.mem_filter]; exact ⟨hγX, heq.symm⟩)) hγT
        have hd0pos : 0 < d₀ := by
          rw [hd₀, hdgdef]
          exact Nat.mul_pos he (Nat.pow_pos (by omega))
        obtain ⟨k, hk⟩ : d₀ ∣ dg γ :=
          mul_pow_dvd_mul_pow_of_le he (by omega) (le_of_lt hd₀lt)
        have hk1 : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with rfl | hpos
          · simp at hk; omega
          · exact hpos
        have hgap : 2 * d₀ * dg γ < ∑ ξ ∈ X.filter (fun ξ => dg ξ < dg γ), dg ξ ^ 2 := by
          have hI : IsLeast (Set.range (fun i : {x // x ∈ X} => dg (i : L → ℂ))) d₀ := by
            refine ⟨⟨⟨χ₀, hχ₀X⟩, rfl⟩, ?_⟩
            rintro y ⟨i, rfl⟩
            exact hχ₀min _ i.2
          have hsum' : ∑ i : {x // x ∈ X}, dg (i : L → ℂ) ^ 2 = ∑ ξ ∈ X, dg ξ ^ 2 :=
            Finset.sum_coe_sort X (fun ξ => dg ξ ^ 2)
          have key := two_mul_min_mul_lt_sum_sq_filter_lt (p := p) (e := e)
            (b := fun i : {x // x ∈ X} => bb (i : L → ℂ)) (d := fun i => dg (i : L → ℂ))
            (M := M) (dmin := d₀) hp he (fun _ => rfl)
            (fun i => hdvd _ i.2) (by rw [hsum']; exact hMsum) hI (j := ⟨γ, hγX⟩) hd₀lt
          have hconv : ∑ i ∈ Finset.univ.filter (fun i : {x // x ∈ X} => dg (i : L → ℂ) < dg γ),
                dg (i : L → ℂ) ^ 2
              = ∑ ξ ∈ X.filter (fun ξ => dg ξ < dg γ), dg ξ ^ 2 := by
            rw [Finset.sum_filter, Finset.sum_filter]
            exact Finset.sum_coe_sort X (fun ξ => if dg ξ < dg γ then dg ξ ^ 2 else 0)
          rw [← hconv]
          exact key
        have hsubT : X.filter (fun ξ => dg ξ < dg γ) ⊆ T := by
          intro ξ hξ
          rw [Finset.mem_filter] at hξ
          by_contra hξT
          exact absurd (hγmin ξ (Finset.mem_sdiff.2 ⟨hξ.1, hξT⟩)) (by omega)
        have hweight : 2 * d₀ * dg γ < ∑ δ ∈ T, dg δ ^ 2 :=
          lt_of_lt_of_le hgap (Finset.sum_le_sum_of_subset hsubT)
        have hFeit : 2 * γ 1 * χ₀ 1 < ∑ δ ∈ T, δ 1 ^ 2 / cfInner δ δ := by
          have hRs : ∑ δ ∈ T, δ 1 ^ 2 / cfInner δ δ = ((∑ δ ∈ T, dg δ ^ 2 : ℕ) : ℂ) := by
            push_cast
            refine Finset.sum_congr rfl fun δ hδ => ?_
            rw [hnorm δ (hTX hδ), div_one, hdg δ (hTX hδ)]
          have hLs : 2 * γ 1 * χ₀ 1 = ((2 * d₀ * dg γ : ℕ) : ℂ) := by
            rw [hdg γ hγX, hdg χ₀ hχ₀X, hd₀]; push_cast; ring
          rw [hLs, hRs]
          exact_mod_cast hweight
        obtain ⟨ν, hν⟩ := isCoherent_iff.1 hcoh
        have hψT : χ₀ ∈ T := hB₀T (by rw [hB₀, Finset.mem_filter]; exact ⟨hχ₀X, rfl⟩)
        have hdeg : γ 1 = (k : ℂ) * χ₀ 1 := by
          rw [hdg γ hγX, hdg χ₀ hχ₀X, hk, ← hd₀]; push_cast; ring
        have hstep := WeightedFeitExtension.isCoherent_insertPair hc (hTX.trans hXS)
          ⟨χ₀, hψT⟩ hTstar hν (fun f => subTauHom_apply hc (coeS hTX) f)
          hψT (hXS hγX) hγT hk1 hdeg hFeit
        set T' : Finset (L → ℂ) := insert γ (insert (star γ) T) with hT'
        have hcoeT' : (T' : Set (L → ℂ)) = insertPair γ T := by
          ext f
          simp [hT', mem_insertPair_iff]
        have hT'X : T' ⊆ X := by
          intro f hf
          rcases Finset.mem_insert.1 hf with rfl | hf
          · exact hγX
          · rcases Finset.mem_insert.1 hf with rfl | hf
            · exact hXstar γ hγX
            · exact hTX hf
        have hcohT' : IsCoherent (T' : Set (L → ℂ)) (subTauHom hc (coeS hT'X)) :=
          isCoherent_subTauHom_congr hc hcoeT'.symm hstep
        refine ih T' ?_ hT'X ?_ (hB₀T.trans (fun x hx =>
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))) hcohT'
        ·
          have hsub : X \ T' ⊆ X \ T := by
            intro x hx
            rw [Finset.mem_sdiff] at hx ⊢
            exact ⟨hx.1, fun hxT =>
              hx.2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxT))⟩
          have hne' : X \ T' ≠ X \ T := by
            intro hEq
            have hmem : γ ∈ X \ T' := by rw [hEq]; exact Finset.mem_sdiff.2 ⟨hγX, hγT⟩
            exact (Finset.mem_sdiff.1 hmem).2 (Finset.mem_insert_self γ _)
          have hlt : (X \ T').card < (X \ T).card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne'⟩)
          omega
        ·
          intro χ hχ
          rcases Finset.mem_insert.1 hχ with rfl | hχ
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          · rcases Finset.mem_insert.1 hχ with rfl | hχ
            · rw [star_star]; exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hTstar χ hχ))

end Abstract

section Family

variable {L : Type*} [Group L] [Fintype L]

theorem indFamDetect_subset_indFam_nonprincipalIrr (K : Subgroup L) (H : Subgroup K) :
    indFamDetect K H ⊆ indFam K (nonprincipalIrr K) := by
  intro f hf
  obtain ⟨θ, hθ, rfl⟩ := (mem_indFamDetect K).1 hf
  refine (mem_indFam K).2 ⟨θ, mem_nonprincipalIrr.2 ⟨?_, ne_one_of_mem_irrDetect hθ⟩, rfl⟩
  rw [← irrChar_eq_Irr]
  exact irrDetect_subset_irrChar H hθ

theorem indFamDetectFinset_subset_indFamNonprincipalFinset (K : Subgroup L) (H : Subgroup K) :
    indFamDetectFinset K H ⊆ indFamNonprincipalFinset K := fun _ hf =>
  (mem_indFamNonprincipalFinset K).2
    (indFamDetect_subset_indFam_nonprincipalIrr K H (mem_indFamDetectFinset.1 hf))

end Family

namespace IsFreeCentralSection

variable {A : Type*} [Group A] [Finite A] {p a : ℕ} {L P E Z : Subgroup A}
  (h : IsFreeCentralSection p a L P E Z)

include h

omit [Finite A] in
theorem natCard_P_subgroupOf_eq_prime_pow : Nat.card (P.subgroupOf L) = p ^ a := by
  rw [Nat.card_congr (subgroupOfEquivOfLe h.P_le).toEquiv, h.natCard_P]

omit [Finite A] in
theorem three_le_prime : 3 ≤ p := by
  have h2 := h.prime.two_le
  rcases Nat.lt_or_ge p 3 with hlt | hge
  · interval_cases p
    · exact absurd h.odd_prime (by decide)
  · exact hge

section Conclusions

variable [(P.subgroupOf L).Normal] [(Z.subgroupOf L).Normal] [Fintype ↥L]

omit [Finite A] in
theorem star_mem_indFamDetectFinset {χ : ↥L → ℂ}
    (hχ : χ ∈ indFamDetectFinset (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) :
    star χ ∈ indFamDetectFinset (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) :=
  mem_indFamDetectFinset.2 (h.conj_mem_indFamDetect (mem_indFamDetectFinset.1 hχ))

omit [Finite A] in
theorem mem_Irr_of_mem_indFamDetectFinset {χ : ↥L → ℂ}
    (hχ : χ ∈ indFamDetectFinset (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) : χ ∈ Irr ↥L := by
  have hmem := mem_indFamDetectFinset.1 hχ
  rw [h.indFamDetect_eq_irrDetect] at hmem
  exact irrDetect_subset_Irr _ hmem

omit [Finite A] in
theorem cfInner_self_of_mem_indFamDetectFinset {χ : ↥L → ℂ}
    (hχ : χ ∈ indFamDetectFinset (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) :
    cfInner χ χ = 1 := cfInner_self_of_mem_Irr (h.mem_Irr_of_mem_indFamDetectFinset hχ)

omit [(P.subgroupOf L).Normal] [(Z.subgroupOf L).Normal] in
theorem exists_degree_eq_mul_pow_and_sq_dvd {χ : ↥L → ℂ}
    (hχ : χ ∈ indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) :
    ∃ b : ℕ, χ 1 = ((Nat.card E * p ^ b : ℕ) : ℂ) ∧
      (Nat.card E * p ^ b) ^ 2 ∣ Nat.card E ^ 2 * Z.relIndex P := by
  obtain ⟨b, hb1, hb2⟩ :=
    CFSG.FeitThompson.exists_degree_eq_index_mul_pow_and_sq_dvd (a := a) h.prime
      h.natCard_P_subgroupOf_eq_prime_pow
      (le_inf h.Z_subgroupOf_le_P_subgroupOf h.Z_subgroupOf_le_centralizer) hχ
  rw [h.index_subgroupOf_eq] at hb1
  rw [h.index_subgroupOf_eq, Subgroup.relIndex_subgroupOf h.P_le] at hb2
  exact ⟨b, hb1, hb2⟩

theorem exists_sum_sq_degree_eq_mul :
    ∃ t : ℕ, ∑ χ ∈ indFamDetectFinset (P.subgroupOf L)
        ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)), χ 1 ^ 2
      = (t : ℂ) * ((Nat.card E ^ 2 * Z.relIndex P : ℕ) : ℂ) := by
  obtain ⟨t, -, ht⟩ := h.exists_sum_sq_degree_indFamDetect_subgroupOf
  exact ⟨t, by rw [ht]; push_cast; ring⟩

theorem isCoherent_centralLayer {G : Type*} [Group G] [Fintype G]
    {S : Finset (↥L → ℂ)} {tau : (↥L → ℂ) → (G → ℂ)} {R : (↥L → ℂ) → Finset (G → ℂ)}
    (hc : IsSubcoherent S tau R) (hS : S = indFamNonprincipalFinset (P.subgroupOf L))
    (τX : charSpanZero ((indFamDetectFinset (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) : Finset (↥L → ℂ)) : Set (↥L → ℂ))
        →+ virtualChars G)
    (hτX : ∀ f, (τX f : G → ℂ) = tau (f : ↥L → ℂ)) :
    (indFamDetect (P.subgroupOf L)
        ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))).Nonempty ∧
      IsCoherent ((indFamDetectFinset (P.subgroupOf L)
        ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) : Finset (↥L → ℂ)) : Set (↥L → ℂ)) τX := by
  refine ⟨h.indFamDetect_nonempty_subgroupOf, ?_⟩
  have hXne : (indFamDetectFinset (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))).Nonempty := by
    obtain ⟨f, hf⟩ := h.indFamDetect_nonempty_subgroupOf
    exact ⟨f, mem_indFamDetectFinset.2 hf⟩
  have hXS : indFamDetectFinset (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ⊆ S := fun x hx =>
    hS ▸ indFamDetectFinset_subset_indFamNonprincipalFinset _ _ hx
  refine isCoherent_of_prime_power_degrees hc hXS hXne
    (fun _ hχ => h.star_mem_indFamDetectFinset hχ)
    (fun _ hχ => h.cfInner_self_of_mem_indFamDetectFinset hχ)
    (e := Nat.card E) (M := Nat.card E ^ 2 * Z.relIndex P) h.three_le_prime Nat.card_pos
    (fun _ hχ => h.exists_degree_eq_mul_pow_and_sq_dvd (mem_indFamDetectFinset.1 hχ)) ?_ τX hτX
  exact h.exists_sum_sq_degree_eq_mul

end Conclusions

end IsFreeCentralSection

end CFSG.FeitThompson
