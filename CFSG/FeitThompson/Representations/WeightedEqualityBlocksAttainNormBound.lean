module

public import CFSG.FeitThompson.Representations.CoherentImageAntirealBlockSelection
public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
import CFSG.FeitThompson.Representations.IntegralOrthonormalBlockProjection
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.PowerOperationsPreserveVirtualChars
import CFSG.FeitThompson.Representations.DadeAveragingOrthogonalProjection
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace PositiveWeightedBlockSaturation

open ComplexOrder CoherentAntirealBlock IntegralBlockProjection

theorem cfInner_self_add_of_cfInner_eq_zero {α : Type*} [Fintype α] {f g : α → ℂ}
    (hfg : cfInner f g = 0) : cfInner (f + g) (f + g) = cfInner f f + cfInner g g := by
  have hgf : cfInner g f = 0 := by rw [← conj_cfInner, hfg, map_zero]
  rw [cfInner_add_left, cfInner_add_right, cfInner_add_right, hfg, hgf]
  ring

section Block

variable {G : Type*} [Group G] [Fintype G]

theorem exists_int_cfInner_sq_le_and_saturation {R : Finset (G → ℂ)} {u D : G → ℂ} {N m : ℤ}
    (hRmem : ↑R ⊆ (Submodule.span ℤ (Irr G) : Set (G → ℂ)))
    (hone : ∀ v ∈ R, cfInner v v = 1)
    (hzero : ∀ v ∈ R, ∀ w ∈ R, v ≠ w → cfInner v w = 0)
    (humem : u ∈ Submodule.span ℤ (Irr G)) (huone : cfInner u u = 1)
    (hRu : ∀ v ∈ R, cfInner v u = 0)
    (hDmem : D ∈ Submodule.span ℤ (Irr G))
    (hDsum : ∑ v ∈ R, cfInner D v = (N : ℂ))
    (hDnorm : cfInner D D = (N : ℂ) + (m : ℂ) ^ 2) :
    ∃ β : ℤ, cfInner D u = (β : ℂ) ∧ β ^ 2 ≤ m ^ 2 ∧
      (β ^ 2 = m ^ 2 →
        ∃ E ⊆ R, (E.card : ℤ) = N ∧ D = (∑ v ∈ E, v) + (β : ℂ) • u) := by
  classical
  have : Nonempty G := ⟨1⟩
  obtain ⟨cf, hcf⟩ := exists_int_cfInner_forall_mem hRmem hDmem
  obtain ⟨β, hβ⟩ := exists_int_cfInner_of_mem_span_Irr hDmem humem
  obtain ⟨P, hP⟩ : ∃ P : G → ℂ, ∑ v ∈ R, cfInner D v • v = P := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : G → ℂ, D - P - (β : ℂ) • u = Z := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, ∑ v ∈ R, cf v ^ 2 = Q := ⟨_, rfl⟩
  have hNsum : N = ∑ v ∈ R, cf v := by
    have h := sum_cfInner_eq_intCast hcf
    rw [hDsum] at h
    exact_mod_cast h
  have hPP : cfInner P P = (Q : ℂ) := by
    rw [← hP, cfInner_sum_cfInner_smul_self hone hzero hcf, hQ]
  have hPu : cfInner P u = 0 := by
    rw [← hP, cfInner_sum_left]
    exact Finset.sum_eq_zero fun v hv => by rw [cfInner_smul_left, hRu v hv, mul_zero]
  have huP : cfInner u P = 0 := by rw [← conj_cfInner, hPu, map_zero]
  have hDv : ∀ v ∈ R, cfInner (D - P) v = 0 := fun v hv => by
    have h := isOrthogonal_sub_sum_cfInner_smul (f := D) (R := R) hone hzero hv
    rw [isOrthogonal_iff, hP] at h
    exact h
  have hDPP : cfInner (D - P) P = 0 := by
    rw [← hP, cfInner_sum_right]
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [cfInner_smul_right, hP, hDv v hv, mul_zero]
  have hZu : cfInner Z u = 0 := by
    rw [← hZ, cfInner_sub_left, cfInner_sub_left, hPu, cfInner_smul_left, huone, hβ]
    ring
  have hZP : cfInner Z P = 0 := by
    rw [← hZ, cfInner_sub_left, hDPP, cfInner_smul_left, huP]
    ring
  have hPZ : cfInner P Z = 0 := by rw [← conj_cfInner, hZP, map_zero]
  have huZ : cfInner u Z = 0 := by rw [← conj_cfInner, hZu, map_zero]
  have hDeq : D = P + ((β : ℂ) • u + Z) := by rw [← hZ]; abel
  have horth : cfInner P ((β : ℂ) • u + Z) = 0 := by
    rw [cfInner_add_right, cfInner_smul_right, hPu, hPZ]; ring
  have hnorm1 : cfInner D D
      = cfInner P P + cfInner ((β : ℂ) • u + Z) ((β : ℂ) • u + Z) := by
    rw [hDeq]; exact cfInner_self_add_of_cfInner_eq_zero horth
  have horth2 : cfInner ((β : ℂ) • u) Z = 0 := by rw [cfInner_smul_left, huZ, mul_zero]
  have hnorm2 : cfInner ((β : ℂ) • u + Z) ((β : ℂ) • u + Z) = (β : ℂ) ^ 2 + cfInner Z Z := by
    rw [cfInner_self_add_of_cfInner_eq_zero horth2, cfInner_smul_left, cfInner_smul_right, huone,
      map_intCast]
    ring
  have hZnorm : cfInner Z Z = ((N + m ^ 2 - Q - β ^ 2 : ℤ) : ℂ) := by
    push_cast
    linear_combination hDnorm - hnorm1 - hnorm2 - hPP
  have hζ : 0 ≤ N + m ^ 2 - Q - β ^ 2 := by
    have h := cfInner_self_nonneg Z
    rw [hZnorm] at h
    exact_mod_cast h
  have hle : N ≤ Q := by rw [hNsum, ← hQ]; exact sum_le_sum_sq cf R
  refine ⟨β, hβ, by linarith, ?_⟩
  intro hβm
  have hζ0 : N + m ^ 2 - Q - β ^ 2 = 0 := by linarith
  have hsq : ∑ v ∈ R, cf v ^ 2 = ∑ v ∈ R, cf v := by rw [hQ, ← hNsum]; linarith
  have h01 : ∀ v ∈ R, cf v = 0 ∨ cf v = 1 := (sum_sq_eq_sum_iff cf R).1 hsq
  obtain ⟨E, hER, hEcard, hEsum⟩ := exists_subset_sum_cfInner_smul_eq hcf h01
  have hZ0 : Z = 0 := by
    have h : cfInner Z Z = 0 := by rw [hZnorm, hζ0]; simp
    exact cfInner_self_eq_zero.1 h
  refine ⟨E, hER, by rw [hEcard, hNsum], ?_⟩
  rw [hDeq, hZ0, ← hP, hEsum]
  abel

end Block

section VirtualChars

variable {G : Type*} [Group G] [Finite G]

theorem mem_span_Irr_of_mem_virtualCharSpan {f : G → ℂ} (hf : f ∈ virtualCharSpan G) :
    f ∈ Submodule.span ℤ (Irr G) :=
  virtualCharSpan_le (fun V _ => FDRep.character_mem_span_Irr V) hf

end VirtualChars

section SpanZero

variable {L : Type*} [Group L] {S : Finset (L → ℂ)} {e : ℕ} {η : L → ℂ}

theorem sub_smul_mem_intSpanZeroAtOne {χ : L → ℂ} {n : ℤ}
    (hχ : χ ∈ S) (hη : η ∈ S) (hηdeg : η 1 = (e : ℂ)) (hdeg : χ 1 = (n : ℂ) * (e : ℂ)) :
    χ - (n : ℂ) • η ∈ intSpanZeroAtOne (S : Set (L → ℂ)) := by
  refine mem_intSpanZeroAtOne.2 ⟨Submodule.sub_mem _ (Submodule.subset_span hχ) ?_, ?_⟩
  · rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ n (Submodule.subset_span hη)
  · simp [hdeg, hηdeg]

end SpanZero

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
  {S X Y : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}
  {τY : charSpanZero (Y : Set (L → ℂ)) →+ virtualChars G}
  {νY : Submodule.span ℤ (Y : Set (L → ℂ)) →+ virtualChars G} {e : ℕ} {η : L → ℂ}

theorem cfInner_tau_tau (hc : IsSubcoherent S tau R) {f h : L → ℂ}
    (hf : f ∈ intSpanZeroAtOne (S : Set (L → ℂ)))
    (hh : h ∈ intSpanZeroAtOne (S : Set (L → ℂ))) : cfInner (tau f) (tau h) = cfInner f h := by
  rw [← charInner_eq_cfInner, ← charInner_eq_cfInner]
  exact hc.charInner_tau_tau f hf h hh

theorem cfInner_eq_zero_of_ne (hc : IsSubcoherent S tau R) {χ ψ : L → ℂ} (hχ : χ ∈ S)
    (hψ : ψ ∈ S) (hne : χ ≠ ψ) : cfInner χ ψ = 0 := by
  rw [← charInner_eq_cfInner]; exact hc.charInner_eq_zero χ hχ ψ hψ hne

theorem tau_sum_smul_sub (hc : IsSubcoherent S tau R) {ι : Type*} [Fintype ι] {χ : ι → L → ℂ}
    {a : ι → ℤ} (hmem : ∀ i, χ i - (a i : ℂ) • η ∈ intSpanZeroAtOne (S : Set (L → ℂ))) :
    tau (∑ i, (a i : ℂ) • χ i - ((∑ i, a i ^ 2 : ℤ) : ℂ) • η)
      = ∑ i, (a i : ℂ) • tau (χ i - (a i : ℂ) • η) := by
  classical
  set d : ι → intSpanZeroAtOne (S : Set (L → ℂ)) := fun i => ⟨χ i - (a i : ℂ) • η, hmem i⟩
    with hd
  have hcoe : ((∑ i, a i • d i : intSpanZeroAtOne (S : Set (L → ℂ))) : L → ℂ)
      = ∑ i, (a i : ℂ) • χ i - ((∑ i, a i ^ 2 : ℤ) : ℂ) • η := by
    push_cast
    rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hd, ← Int.cast_smul_eq_zsmul ℂ (a i), smul_sub, smul_smul]
    ring_nf
  rw [← hcoe, ← hc.tauHom_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, hc.tauHom_apply, ← Int.cast_smul_eq_zsmul ℂ (a i)]

theorem cfInner_R_nu_eq_zero (hc : IsSubcoherent S tau R) (hXS : X ⊆ S) (hYS : Y ⊆ S)
    (hXY : Disjoint X Y) (hXstar : ∀ ψ ∈ X, star ψ ∈ X) (hYstar : ∀ ψ ∈ Y, star ψ ∈ Y)
    (hν : IsCoherentWith (Y : Set (L → ℂ)) τY νY)
    (hτY : ∀ f : charSpanZero (Y : Set (L → ℂ)), (τY f : G → ℂ) = tau (f : L → ℂ))
    (hYIrr : ∀ ψ ∈ Y, ψ ∈ Irr L)
    {χ ψ : L → ℂ} (hχ : χ ∈ X) (hψ : ψ ∈ Y) {v : G → ℂ} (hv : v ∈ R χ) :
    cfInner v (νY ⟨ψ, mem_span_of_mem hψ⟩ : G → ℂ) = 0 := by
  have hn : cfInner ψ ψ = ((1 : ℕ) : ℂ) := by
    simpa using cfInner_self_of_mem_Irr (hYIrr ψ hψ)
  obtain ⟨E, hER, -, hEsum, -⟩ := exists_subset_card_eq_and_eq_sum hc hYS hYstar hν hτY
    (fun r hr => mem_span_Irr_of_mem_virtualCharSpan (hc.R_subset ψ (hYS hψ) r hr))
    (fun f => coe_mem_span_Irr _) hψ hn
  have hne1 : ψ ≠ χ := fun h => (Finset.disjoint_left.1 hXY hχ) (h ▸ hψ)
  have hne2 : ψ ≠ star χ := fun h => (Finset.disjoint_left.1 hXY (hXstar χ hχ)) (h ▸ hψ)
  rw [hEsum, cfInner_sum_right]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [← charInner_eq_cfInner]
  exact hc.charInner_R_R χ (hXS hχ) ψ (hYS hψ) hne1 hne2 v hv s (hER hs)

section Main

variable (hc : IsSubcoherent S tau R) (hXS : X ⊆ S) (hYS : Y ⊆ S) (hXY : Disjoint X Y)
  (hXstar : ∀ ψ ∈ X, star ψ ∈ X) (hYstar : ∀ ψ ∈ Y, star ψ ∈ Y)
  (hν : IsCoherentWith (Y : Set (L → ℂ)) τY νY)
  (hτY : ∀ f : charSpanZero (Y : Set (L → ℂ)), (τY f : G → ℂ) = tau (f : L → ℂ))
  (hYIrr : ∀ ψ ∈ Y, ψ ∈ Irr L) (hη : η ∈ Y) (hYdeg : ∀ ψ ∈ Y, ψ 1 = (e : ℂ))
  {ι : Type*} {χ : ι → L → ℂ} {a : ι → ℤ}
  (hχX : ∀ i, χ i ∈ X) (hdeg : ∀ i, χ i 1 = (a i : ℂ) * (e : ℂ))

include hc hXS hYS hXY hXstar hYstar hν hτY hYIrr hη hYdeg hχX hdeg in
theorem exists_int_norm_and_coeff (i : ι) :
    ∃ N β : ℤ, ((N : ℂ) = cfInner (χ i) (χ i)) ∧
      cfInner (tau (χ i - (a i : ℂ) • η)) (νY ⟨η, mem_span_of_mem hη⟩ : G → ℂ) = (β : ℂ) ∧
      β ^ 2 ≤ a i ^ 2 ∧ (β ^ 2 = a i ^ 2 →
        ∃ E ⊆ R (χ i), (E.card : ℤ) = N ∧ tau (χ i - (a i : ℂ) • η)
          = (∑ v ∈ E, v) + (β : ℂ) • (νY ⟨η, mem_span_of_mem hη⟩ : G → ℂ)) := by
  classical
  set u := (νY ⟨η, mem_span_of_mem hη⟩ : G → ℂ) with hu
  have hηS : η ∈ S := hYS hη
  have hηdeg : η 1 = (e : ℂ) := hYdeg η hη
  have humem : u ∈ Submodule.span ℤ (Irr G) := coe_mem_span_Irr _
  have hηη : cfInner η η = 1 := cfInner_self_of_mem_Irr (hYIrr η hη)
  have huone : cfInner u u = 1 := by rw [hu, hν.inner_eq]; exact hηη
  have hmem : ∀ i, χ i - (a i : ℂ) • η ∈ intSpanZeroAtOne (S : Set (L → ℂ)) := fun i =>
    sub_smul_mem_intSpanZeroAtOne (hXS (hχX i)) hηS hηdeg (hdeg i)
  set D : G → ℂ := tau (χ i - (a i : ℂ) • η) with hD
  have hηχ : cfInner η (χ i) = 0 :=
    cfInner_eq_zero_of_ne hc hηS (hXS (hχX i)) fun h => (Finset.disjoint_left.1 hXY (h ▸ hχX i)) hη
  have hχη : cfInner (χ i) η = 0 := by rw [← conj_cfInner, hηχ, map_zero]
  have hηstar : cfInner η (star (χ i)) = 0 :=
    cfInner_eq_zero_of_ne hc hηS (hc.star_mem _ (hXS (hχX i)))
      fun h => (Finset.disjoint_left.1 hXY (h ▸ hXstar _ (hχX i))) hη
  have hχstar : cfInner (χ i) (star (χ i)) = 0 :=
    cfInner_eq_zero_of_ne hc (hXS (hχX i)) (hc.star_mem _ (hXS (hχX i)))
      (Ne.symm (hc.star_ne _ (hXS (hχX i))))
  have hRmem : ↑(R (χ i)) ⊆ (Submodule.span ℤ (Irr G) : Set (G → ℂ)) := fun r hr =>
    mem_span_Irr_of_mem_virtualCharSpan (hc.R_subset _ (hXS (hχX i)) r hr)
  have hone : ∀ v ∈ R (χ i), cfInner v v = 1 := fun v hv => by
    rw [← charInner_eq_cfInner]; exact hc.charInner_R_self _ (hXS (hχX i)) v hv
  have hzero : ∀ v ∈ R (χ i), ∀ w ∈ R (χ i), v ≠ w → cfInner v w = 0 := fun v hv w hw hne => by
    rw [← charInner_eq_cfInner]; exact hc.charInner_R_of_ne _ (hXS (hχX i)) v hv w hw hne
  have hRu : ∀ v ∈ R (χ i), cfInner v u = 0 := fun v hv =>
    cfInner_R_nu_eq_zero hc hXS hYS hXY hXstar hYstar hν hτY hYIrr (hχX i) hη hv
  have hDmem : D ∈ Submodule.span ℤ (Irr G) :=
    mem_span_Irr_of_mem_virtualCharSpan (hc.tau_mem _ (hmem i))
  obtain ⟨cf, hcf⟩ := exists_int_cfInner_forall_mem hRmem hDmem
  have hDsum : ∑ v ∈ R (χ i), cfInner D v = ((∑ v ∈ R (χ i), cf v : ℤ) : ℂ) :=
    sum_cfInner_eq_intCast hcf
  have hnormL : cfInner D (∑ v ∈ R (χ i), v) = cfInner (χ i) (χ i) := by
    rw [hD, ← hc.tau_sub_star _ (hXS (hχX i)),
      cfInner_tau_tau hc (hmem i) (hc.sub_star_mem (hXS (hχX i))),
      cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, cfInner_smul_left,
      cfInner_smul_left, hχstar, hηχ, hηstar]
    ring
  have hN : ((∑ v ∈ R (χ i), cf v : ℤ) : ℂ) = cfInner (χ i) (χ i) := by
    rw [← hDsum, ← cfInner_sum_right]; exact hnormL
  have hDnorm : cfInner D D = ((∑ v ∈ R (χ i), cf v : ℤ) : ℂ) + (a i : ℂ) ^ 2 := by
    rw [hD, cfInner_tau_tau hc (hmem i) (hmem i), cfInner_sub_left, cfInner_sub_right,
      cfInner_sub_right, cfInner_smul_left, cfInner_smul_left, cfInner_smul_right,
      cfInner_smul_right, hηη, hχη, hηχ, hN, map_intCast]
    ring
  obtain ⟨β, hβ1, hβ2, hβ3⟩ := exists_int_cfInner_sq_le_and_saturation hRmem hone hzero humem
    huone hRu hDmem hDsum hDnorm
  exact ⟨_, β, hN, hβ1, hβ2, hβ3⟩

include hc hXS hYS hXY hXstar hYstar hν hτY hYIrr hη hYdeg hχX hdeg in
theorem exists_subset_card_eq_and_tau_eq [Fintype ι] {w : L → ℂ} {r : ℤ}
    (hapos : ∀ i, 1 ≤ a i) (hwdef : w = ∑ i, (a i : ℂ) • χ i) (hrdef : r = ∑ i, a i ^ 2)
    (hweq : cfInner (tau (w - (r : ℂ) • η)) (νY ⟨η, mem_span_of_mem hη⟩ : G → ℂ) = -(r : ℂ))
    (i : ι) :
    ∃ E ⊆ R (χ i), (E.card : ℂ) = cfInner (χ i) (χ i) ∧
      tau (χ i - (a i : ℂ) • η)
        = (∑ v ∈ E, v) - (a i : ℂ) • (νY ⟨η, mem_span_of_mem hη⟩ : G → ℂ) ∧
      ∀ (ψ : L → ℂ) (hψ : ψ ∈ Y),
        IsOrthogonal (∑ v ∈ E, v) (νY ⟨ψ, mem_span_of_mem hψ⟩ : G → ℂ) := by
  classical
  choose! N β hN hβ hβle hβsat using
    exists_int_norm_and_coeff hc hXS hYS hXY hXstar hYstar hν hτY hYIrr hη hYdeg hχX hdeg
  have hmem : ∀ i, χ i - (a i : ℂ) • η ∈ intSpanZeroAtOne (S : Set (L → ℂ)) := fun i =>
    sub_smul_mem_intSpanZeroAtOne (hXS (hχX i)) (hYS hη) (hYdeg η hη) (hdeg i)
  have hexp : ((∑ i, a i * β i : ℤ) : ℂ) = -(r : ℂ) := by
    rw [← hweq, hwdef, hrdef, tau_sum_smul_sub hc hmem, cfInner_sum_left]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [cfInner_smul_left, hβ i]
  have hsum : ∑ i, a i * β i = -r := by exact_mod_cast hexp
  have hterm : ∀ i ∈ Finset.univ, 0 ≤ a i * (β i + a i) := fun i _ => by
    have h1 : -a i ≤ β i := by nlinarith [hβle i, hapos i]
    have h2 : 0 < a i := lt_of_lt_of_le zero_lt_one (hapos i)
    nlinarith
  have htotal : ∑ i, a i * (β i + a i) = 0 := by
    rw [Finset.sum_congr rfl fun i _ => mul_add (a i) (β i) (a i), Finset.sum_add_distrib, hsum,
      hrdef]
    simp [sq]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 htotal
  have hβa : β i = -a i := by
    have h := hzero i (Finset.mem_univ i)
    have h2 : (0 : ℤ) < a i := lt_of_lt_of_le zero_lt_one (hapos i)
    rcases mul_eq_zero.1 h with h3 | h3
    · omega
    · omega
  obtain ⟨E, hER, hEcard, hEsum⟩ := hβsat i (by rw [hβa]; ring)
  refine ⟨E, hER, ?_, ?_, ?_⟩
  · rw [← hN i]; exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hEcard
  · rw [hEsum, hβa]
    push_cast
    rw [neg_smul]
    abel
  · intro ψ hψ
    rw [isOrthogonal_iff, cfInner_sum_left]
    exact Finset.sum_eq_zero fun v hv =>
      cfInner_R_nu_eq_zero hc hXS hYS hXY hXstar hYstar hν hτY hYIrr (hχX i) hψ (hER hv)

end Main

end PositiveWeightedBlockSaturation

end CFSG.FeitThompson
