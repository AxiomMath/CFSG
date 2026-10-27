module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PlaneTorus
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Models
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentSplit
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmFrame
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabNorm
import CFSG.Mathlib.GroupTheory.CyclicPrimeExponent

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.Timmesfeld.ClassicalOrders

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

private theorem planeDecomp_bounds [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    {A : Subgroup (normOmega E m)} (hA : CFSG.Open.IsElemAbelian p A)
    (hcard : p ^ m ≤ Nat.card A) :
    ∃ (r : ℕ) (U : Fin r → Submodule F ((F × F) × (Fin m → K))),
      CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.IsPlaneDecomp (normHypForm E m) A ⊤ U ∧
      p ^ m ≤ p ^ r ∧ r ≤ m + 1 ∧ r ≠ m + 1 := by
  have hp : p.Prime := Fact.out
  have hdim : Module.finrank F ((F × F) × (Fin m → K)) = 2 * (m + 1) :=
    finrank_normHypForm E m
  have hQ := normHypForm_polarBilin_nondegenerate E m
  have hreg : CFSG.RankThree.PartOne.K159.RegOn (normHypForm E m) ⊤ := fun u _ h =>
    hQ.1 u fun w => by
      simpa [QuadraticMap.polarBilin_apply_apply] using h w Submodule.mem_top
  obtain ⟨r, U, hU⟩ := CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.exists_planeDecomp
    (Q := normHypForm E m) hQ hp hp2 hpq hA ⊤ hreg fun _ _ _ _ => Submodule.mem_top
  have hle : p ^ m ≤ p ^ r := hcard.trans (hU.card_le_pow hA hp)
  have hrn : r ≤ m + 1 := by
    have h1 := hU.toIsPlaneSystem.finrank_biSup (Finset.univ : Finset (Fin r))
    have h2 := Submodule.finrank_le (⨆ j ∈ (Finset.univ : Finset (Fin r)), U j)
    rw [h1, Finset.card_univ, Fintype.card_fin, hdim] at h2
    omega
  have hrne : r ≠ m + 1 := by
    intro hr
    have hdimr : Module.finrank F ((F × F) × (Fin m → K)) = 2 * r := by
      rw [hr]; exact hdim
    have hev : Even r ↔ Even m :=
      (hU.toIsPlaneSystem.isPlusType_iff_of_finrank hdimr).symm.trans
        (isPlusType_normHypForm_iff E m)
    rcases Nat.even_or_odd m with hm_even | hm_odd
    · have h1 : Even (m + 1) := hr ▸ hev.mpr hm_even
      have h2 : ¬ Odd (m + 1) := Nat.not_odd_iff_even.mpr h1
      rw [Nat.odd_add_one] at h2
      exact (Nat.not_even_iff_odd.mpr (not_not.mp h2)) hm_even
    · have hnr : ¬ Even r := fun her => (Nat.not_even_iff_odd.mpr hm_odd) (hev.mp her)
      have hor : Odd r := Nat.not_even_iff_odd.mp hnr
      rw [hr] at hor
      exact (Nat.odd_add_one.mp hor) hm_odd
  exact ⟨r, U, hU, hle, hrn, hrne⟩

private theorem card_of_le_pow {m p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hF : Nat.card F = 2 ^ f) (hpq : p ∣ 2 ^ f + 1)
    {A : Subgroup (normOmega E m)} (hA : CFSG.Open.IsElemAbelian p A)
    (hcard : p ^ m ≤ Nat.card A) : Nat.card A = p ^ m := by
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have : CharP F 2 := RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  have : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  have hp : p.Prime := Fact.out
  have hpq' : p ∣ Nat.card F + 1 := by rw [hF]; exact hpq
  obtain ⟨r, U, hU, hle, hrn, hrne⟩ := planeDecomp_bounds (E := E) hp2 hpq' hA hcard
  have hmr : m ≤ r := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
  have hr : r = m := by omega
  exact le_antisymm (hr ▸ hU.card_le_pow hA hp) hcard

omit [Finite K] [CharP K 2] in
private theorem nondegOn_of_restrict {m : ℕ}
    {Q : QuadraticForm F ((F × F) × (Fin m → K))} {U : Submodule F ((F × F) × (Fin m → K))}
    (h : (QuadraticMap.polarBilin (Q.comp U.subtype)).Nondegenerate) :
    CFSG.StandardType.SUTB.NondegOn (QuadraticMap.polarBilin Q) U := by
  intro x hx hxx
  have h' := h.2 ⟨x, hx⟩ fun y => by
    rw [QuadraticMap.polarBilin_apply_apply,
      CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polar_comp_subtype_cent,
      ← QuadraticMap.polarBilin_apply_apply]
    exact hxx y y.2
  exact Subtype.ext_iff.mp h'

omit [CharP K 2] in
private theorem exists_frame_in_plane {m : ℕ} [Finite F] [CharP F 2] [FiniteDimensional F K]
    {c₀ : F} (hc₀ : c₀ ∉ (CFSG.StandardType.OrdPNsOm.wp F).range)
    {Q : QuadraticForm F ((F × F) × (Fin m → K))}
    {U : Fin m → Submodule F ((F × F) × (Fin m → K))}
    (hU : CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.IsPlaneSystem Q U) (j : Fin m) :
    ∃ a b : (F × F) × (Fin m → K), a ∈ U j ∧ b ∈ U j ∧
      CFSG.StandardType.OrdPNsOm.IsFrame Q c₀ true (Fin.elim0 : Fin 0 → _) Fin.elim0 a b := by
  classical
  have : Finite ((F × F) × (Fin m → K)) := inferInstance
  have : FiniteDimensional F ((F × F) × (Fin m → K)) := inferInstance
  obtain ⟨τ, a, b, ha, hb, hFr, -⟩ :=
    CFSG.StandardType.OrdPNsOm.exists_frame_plane (Q := Q) hc₀
      (nondegOn_of_restrict (hU.nondeg j)) (hU.finrank_eq j)
  refine ⟨a, b, ha, hb, ?_⟩
  cases hτ : τ
  · exfalso
    have hQa : Q a = 0 := by
      rw [hτ] at hFr
      simpa using hFr.qa
    have ha0 : a ≠ 0 := by
      intro h0
      have hpab : QuadraticMap.polar Q (0 : (F × F) × (Fin m → K)) b = 1 := by
        simpa [h0] using hFr.pab
      rw [QuadraticMap.polar_zero_left] at hpab
      exact zero_ne_one hpab
    have hane : (⟨a, ha⟩ : U j) ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
    refine hU.not_isPlusType j ⟨Submodule.span F {⟨a, ha⟩}, ?_, ?_⟩
    · rw [finrank_span_singleton hane, hU.finrank_eq j]
    · rintro ⟨x, hx⟩ hxW
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxW
      rw [← hc]
      change Q (c • a) = 0
      rw [QuadraticMap.map_smul, hQa, smul_eq_mul, mul_zero]
  · simpa [hτ] using hFr

private theorem exists_coord_frame [Finite F] [CharP F 2] {c₀ : F}
    (hc₀ : c₀ ∉ (CFSG.StandardType.OrdPNsOm.wp F).range) :
    ∃ a₀ b₀ : K, CFSG.StandardType.OrdPNsOm.IsFrame (normQuad E) c₀ true
      (Fin.elim0 : Fin 0 → K) Fin.elim0 a₀ b₀ := by
  classical
  have : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  have haniso : ∀ x : K, normQuad E x = 0 → x = 0 := by
    intro x hx
    have h : x * unitaryInvolution K 2 f x = 0 := by
      rw [← algebraMap_normQuad E, hx, map_zero]
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · have hinv := E.isUnitary.invol x
      rw [h', map_zero] at hinv
      exact hinv.symm
  have hnd : CFSG.StandardType.SUTB.NondegOn (QuadraticMap.polarBilin (normQuad E)) ⊤ :=
    fun x _ hx => (normQuad_polarBilin_nondegenerate E).2 x fun y => hx y Submodule.mem_top
  obtain ⟨τ, a, b, -, -, hFr, -⟩ :=
    CFSG.StandardType.OrdPNsOm.exists_frame_plane (Q := normQuad E) (V := K) hc₀ hnd
      (by rw [finrank_top, E.finrank_eq])
  refine ⟨a, b, ?_⟩
  cases hτ : τ
  · exfalso
    have hQa : normQuad E a = 0 := by
      rw [hτ] at hFr
      simpa using hFr.qa
    have ha0 : a ≠ 0 := by
      intro h0
      have hpab : QuadraticMap.polar (normQuad E) (0 : K) b = 1 := by
        simpa [h0] using hFr.pab
      rw [QuadraticMap.polar_zero_left] at hpab
      exact zero_ne_one hpab
    exact ha0 (haniso a hQa)
  · simpa [hτ] using hFr

private theorem normHypForm_coord_single [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m : ℕ} (j : Fin m) (x : K) :
    normHypForm E m ((0, 0), Pi.single j x) = normQuad E x := by
  rw [normHypForm, hypSum_apply, Qn_apply]
  simp only [mul_zero, zero_add]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij, QuadraticMap.map_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem polar_normHypForm_coord_single [Finite F] [CharP F 2]
    [FiniteDimensional F K] {m : ℕ} (j : Fin m) (x y : K) :
    QuadraticMap.polar (normHypForm E m) ((0, 0), Pi.single j x) ((0, 0), Pi.single j y) =
      QuadraticMap.polar (normQuad E) x y := by
  rw [normHypForm, polar_hypSum, polar_Qn_single]
  simp only [mul_zero, add_zero, zero_add]
  rw [Pi.single_eq_same]

private theorem polar_normHypForm_coord_single_ne [Finite F] [CharP F 2]
    [FiniteDimensional F K] {m : ℕ} {i j : Fin m} (hij : i ≠ j) (x y : K) :
    QuadraticMap.polar (normHypForm E m) ((0, 0), Pi.single i x) ((0, 0), Pi.single j y) = 0 := by
  rw [normHypForm, polar_hypSum]
  simp only [mul_zero, add_zero, zero_add]
  rw [polar_Qn]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hki : k = i
  · subst hki
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hij, QuadraticMap.polar_zero_right]
  · rw [Pi.single_eq_of_ne hki, QuadraticMap.polar_zero_left]

private theorem polar_normHypForm_fst_coord [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m : ℕ} (p : F × F) (j : Fin m) (x : K) :
    QuadraticMap.polar (normHypForm E m) (p, 0) ((0, 0), Pi.single j x) = 0 := by
  rw [normHypForm, polar_hypSum]
  simp

private theorem isFrame_coord_plane [Finite F] [CharP F 2] [FiniteDimensional F K] {m : ℕ}
    {c₀ : F} {a₀ b₀ : K}
    (hFr : CFSG.StandardType.OrdPNsOm.IsFrame (normQuad E) c₀ true
      (Fin.elim0 : Fin 0 → K) Fin.elim0 a₀ b₀) (j : Fin m) :
    CFSG.StandardType.OrdPNsOm.IsFrame (normHypForm E m) c₀ true
      (Fin.elim0 : Fin 0 → (F × F) × (Fin m → K)) Fin.elim0
      ((0, 0), Pi.single j a₀) ((0, 0), Pi.single j b₀) := by
  have hQ := normHypForm_coord_single (E := E) j a₀
  have hQ' := normHypForm_coord_single (E := E) j b₀
  have hp := polar_normHypForm_coord_single (E := E) j a₀ b₀
  exact
    { hyp := ⟨fun k => k.elim0, fun k => k.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0⟩
      pea := fun i => i.elim0
      peb := fun i => i.elim0
      pfa := fun i => i.elim0
      pfb := fun i => i.elim0
      pab := by rw [hp, hFr.pab]
      qa := by rw [hQ, hFr.qa]
      qb := by rw [hQ', hFr.qb] }

omit [Finite K] [CharP K 2] in
private theorem linearIndependent_frames [CharP F 2]
    {m : ℕ} {Q : QuadraticForm F ((F × F) × (Fin m → K))} {c₀ : F}
    {a b : Fin m → (F × F) × (Fin m → K)}
    (hFr : ∀ j, CFSG.StandardType.OrdPNsOm.IsFrame Q c₀ true
      (Fin.elim0 : Fin 0 → _) Fin.elim0 (a j) (b j))
    (horth : ∀ i j, i ≠ j → ∀ u ∈ ({a i, b i} : Set ((F × F) × (Fin m → K))),
      ∀ v ∈ ({a j, b j} : Set ((F × F) × (Fin m → K))), QuadraticMap.polar Q u v = 0) :
    LinearIndependent F (Sum.elim a b) := by
  refine CFSG.StandardType.TableBOrth.linearIndependent_of_polar_dual (QF := Q)
    (d := Sum.elim b a) ?_
  rintro (i | i) (j | j) <;> simp only [Sum.elim_inl, Sum.elim_inr]
  · by_cases hij : i = j
    · subst hij
      rw [(hFr i).pab]
      simp
    · rw [horth i j hij (a i) (by simp) (b j) (by simp)]
      simp [hij]
  · by_cases hij : i = j
    · subst hij
      rw [CFSG.StandardType.OrdPNsOm.polar_self_charTwo]
      simp
    · rw [horth i j hij (a i) (by simp) (a j) (by simp)]
      simp
  · by_cases hij : i = j
    · subst hij
      rw [CFSG.StandardType.OrdPNsOm.polar_self_charTwo]
      simp
    · rw [horth i j hij (b i) (by simp) (b j) (by simp)]
      simp
  · by_cases hij : i = j
    · subst hij
      rw [QuadraticMap.polar_comm, (hFr i).pab]
      simp
    · rw [horth i j hij (b i) (by simp) (a j) (by simp)]
      simp [hij]

omit [Finite K] [CharP K 2] in
private theorem frames_polar_eq [CharP F 2]
    {m : ℕ} {Q : QuadraticForm F ((F × F) × (Fin m → K))} {c₀ : F}
    {a b a' b' : Fin m → (F × F) × (Fin m → K)}
    (hFr : ∀ j, CFSG.StandardType.OrdPNsOm.IsFrame Q c₀ true
      (Fin.elim0 : Fin 0 → _) Fin.elim0 (a j) (b j))
    (hFr' : ∀ j, CFSG.StandardType.OrdPNsOm.IsFrame Q c₀ true
      (Fin.elim0 : Fin 0 → _) Fin.elim0 (a' j) (b' j))
    (horth : ∀ i j, i ≠ j → ∀ u ∈ ({a i, b i} : Set ((F × F) × (Fin m → K))),
      ∀ v ∈ ({a j, b j} : Set ((F × F) × (Fin m → K))), QuadraticMap.polar Q u v = 0)
    (horth' : ∀ i j, i ≠ j → ∀ u ∈ ({a' i, b' i} : Set ((F × F) × (Fin m → K))),
      ∀ v ∈ ({a' j, b' j} : Set ((F × F) × (Fin m → K))), QuadraticMap.polar Q u v = 0) :
    ∀ i j : Fin m ⊕ Fin m,
      QuadraticMap.polar Q (Sum.elim a' b' i) (Sum.elim a' b' j) =
        QuadraticMap.polar Q (Sum.elim a b i) (Sum.elim a b j) := by
  rintro (i | i) (j | j) <;> simp only [Sum.elim_inl, Sum.elim_inr]
  · by_cases hij : i = j
    · subst hij
      rw [CFSG.StandardType.OrdPNsOm.polar_self_charTwo,
        CFSG.StandardType.OrdPNsOm.polar_self_charTwo]
    · rw [horth' i j hij (a' i) (by simp) (a' j) (by simp),
        horth i j hij (a i) (by simp) (a j) (by simp)]
  · by_cases hij : i = j
    · subst hij
      rw [(hFr' i).pab, (hFr i).pab]
    · rw [horth' i j hij (a' i) (by simp) (b' j) (by simp),
        horth i j hij (a i) (by simp) (b j) (by simp)]
  · by_cases hij : i = j
    · subst hij
      rw [show QuadraticMap.polar Q (b' i) (a' i) = 1 by
            rw [QuadraticMap.polar_comm]; exact (hFr' i).pab,
        show QuadraticMap.polar Q (b i) (a i) = 1 by
            rw [QuadraticMap.polar_comm]; exact (hFr i).pab]
    · rw [horth' i j hij (b' i) (by simp) (a' j) (by simp),
        horth i j hij (b i) (by simp) (a j) (by simp)]
  · by_cases hij : i = j
    · subst hij
      rw [CFSG.StandardType.OrdPNsOm.polar_self_charTwo,
        CFSG.StandardType.OrdPNsOm.polar_self_charTwo]
    · rw [horth' i j hij (b' i) (by simp) (b' j) (by simp),
        horth i j hij (b i) (by simp) (b j) (by simp)]

omit [Finite K] [CharP K 2] in
private theorem exists_isometry_of_frames [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m : ℕ} {Q : QuadraticForm F ((F × F) × (Fin m → K))} {c₀ : F}
    {a b a' b' : Fin m → (F × F) × (Fin m → K)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hFr : ∀ j, CFSG.StandardType.OrdPNsOm.IsFrame Q c₀ true
      (Fin.elim0 : Fin 0 → _) Fin.elim0 (a j) (b j))
    (hFr' : ∀ j, CFSG.StandardType.OrdPNsOm.IsFrame Q c₀ true
      (Fin.elim0 : Fin 0 → _) Fin.elim0 (a' j) (b' j))
    (horth : ∀ i j, i ≠ j → ∀ u ∈ ({a i, b i} : Set ((F × F) × (Fin m → K))),
      ∀ v ∈ ({a j, b j} : Set ((F × F) × (Fin m → K))), QuadraticMap.polar Q u v = 0)
    (horth' : ∀ i j, i ≠ j → ∀ u ∈ ({a' i, b' i} : Set ((F × F) × (Fin m → K))),
      ∀ v ∈ ({a' j, b' j} : Set ((F × F) × (Fin m → K))), QuadraticMap.polar Q u v = 0) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ∀ j, g (a j) = a' j ∧ g (b j) = b' j := by
  have hQv : ∀ i : Fin m ⊕ Fin m, Q ((Sum.elim a' b') i) = Q ((Sum.elim a b) i) := by
    rintro (j | j) <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · rw [(hFr' j).qa, (hFr j).qa]
    · rw [(hFr' j).qb, (hFr j).qb]
  obtain ⟨g, hg, hgu⟩ := CFSG.StandardType.TableBOrth.exists_orth_apply_eq (QF := Q) hQ
    (Sum.elim a b) (Sum.elim a' b') (linearIndependent_frames hFr horth)
    (linearIndependent_frames hFr' horth') hQv (frames_polar_eq hFr hFr' horth horth')
  exact ⟨g, hg, fun j => ⟨by simpa using hgu (Sum.inl j), by simpa using hgu (Sum.inr j)⟩⟩

private theorem conj_maps [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m p : ℕ} {U : Fin m → Submodule F ((F × F) × (Fin m → K))}
    {e : Fin m → normOmega E m} {A : Subgroup (normOmega E m)} {j : Fin m}
    (hU : CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.IsPlaneFrame (normHypForm E m) p U e A)
    {g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))}
    {emb : K →ₗ[F] ((F × F) × (Fin m → K))}
    (hP : (U j).map g.toLinearMap = LinearMap.range emb) :
    ∀ x : K, ∃ y : K,
      (g * (e j : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) * g⁻¹) (emb x) =
        emb y := by
  intro x
  have hx : emb x ∈ (U j).map g.toLinearMap := by rw [hP]; exact ⟨x, rfl⟩
  obtain ⟨u, huU, hu⟩ := Submodule.mem_map.mp hx
  have h1 : (e j : ((F × F) × (Fin m → K)) ≃ₗ[F] _) u ∈ U j := hU.maps_to j u huU
  have h2 : g ((e j : _ ≃ₗ[F] _) u) ∈ (U j).map g.toLinearMap :=
    Submodule.mem_map_of_mem h1
  rw [hP] at h2
  obtain ⟨y, hy⟩ := h2
  refine ⟨y, ?_⟩
  show g ((e j : _ ≃ₗ[F] _) (g⁻¹ (emb x))) = emb y
  rw [← hu]
  simpa using hy.symm

private theorem conj_fixes [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m p : ℕ} {U : Fin m → Submodule F ((F × F) × (Fin m → K))}
    {e : Fin m → normOmega E m} {A : Subgroup (normOmega E m)} {j : Fin m}
    (hU : CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.IsPlaneFrame (normHypForm E m) p U e A)
    {g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m))
    {emb : K →ₗ[F] ((F × F) × (Fin m → K))}
    (hP : (U j).map g.toLinearMap = LinearMap.range emb) :
    ∀ v, (∀ x : K, QuadraticMap.polar (normHypForm E m) (emb x) v = 0) →
      (g * (e j : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) * g⁻¹) v = v := by
  intro v hv
  have hperp : g⁻¹ v ∈
      CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp (normHypForm E m) (U j) := by
    rw [CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.mem_polarPerp_iff]
    intro u hu
    have hu' : g u ∈ LinearMap.range emb := by
      have h2 : g u ∈ (U j).map g.toLinearMap := Submodule.mem_map_of_mem hu
      rwa [hP] at h2
    obtain ⟨y, hy⟩ := hu'
    have h2 : QuadraticMap.polar (normHypForm E m) u (g⁻¹ v) =
        QuadraticMap.polar (normHypForm E m) (emb y) v := by
      rw [← CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO u (g⁻¹ v), ← hy]
      congr 1
      exact g.apply_symm_apply v
    rw [h2, hv y]
  have hfixe : (e j : ((F × F) × (Fin m → K)) ≃ₗ[F] _) (g⁻¹ v) = g⁻¹ v :=
    hU.apply_of_perp j (g⁻¹ v) hperp
  show g ((e j : _ ≃ₗ[F] _) (g⁻¹ v)) = v
  rw [hfixe]
  simp

private theorem conj_nofix [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m p : ℕ} {U : Fin m → Submodule F ((F × F) × (Fin m → K))}
    {e : Fin m → normOmega E m} {A : Subgroup (normOmega E m)} {j : Fin m}
    (hU : CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.IsPlaneFrame (normHypForm E m) p U e A)
    {g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))}
    {emb : K →ₗ[F] ((F × F) × (Fin m → K))}
    (hemb : ∀ x : K, emb x = ((0, 0), Pi.single j x))
    (hP : (U j).map g.toLinearMap = LinearMap.range emb) :
    ∀ x : K,
      (g * (e j : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) * g⁻¹) (emb x) =
        emb x → x = 0 := by
  intro x hx
  have hxmem : emb x ∈ (U j).map g.toLinearMap := by rw [hP]; exact ⟨x, rfl⟩
  obtain ⟨u, huU, hu⟩ := Submodule.mem_map.mp hxmem
  have hgu : g⁻¹ (emb x) = u := by
    rw [← hu]
    simp
  have hfixe : (e j : ((F × F) × (Fin m → K)) ≃ₗ[F] _) u = u := by
    have hx' : g ((e j : ((F × F) × (Fin m → K)) ≃ₗ[F] _) (g⁻¹ (emb x))) = emb x := hx
    rw [hgu] at hx'
    have h1 : g ((e j : _ ≃ₗ[F] _) u) = g u := by rw [hx', ← hu]; rfl
    exact g.injective h1
  have hzero : u = 0 := hU.eq_zero_of_apply_eq j u huU hfixe
  have h0 : emb x = 0 := by rw [← hu, hzero, map_zero]
  have h1 : (emb x).2 j = 0 := by rw [h0]; rfl
  simpa [hemb] using h1

private theorem conj_pow [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m p : ℕ} {U : Fin m → Submodule F ((F × F) × (Fin m → K))}
    {e : Fin m → normOmega E m} {A : Subgroup (normOmega E m)} {j : Fin m}
    (hU : CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.IsPlaneFrame (normHypForm E m) p U e A)
    {g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))} :
    (g * (e j : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) * g⁻¹) ^ p = 1 := by
  have hep : ((e j : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))) ^ p = 1 := by
    have h : (e j : normOmega E m) ^ p = 1 := by
      rw [← hU.orderOf_eq j]
      exact pow_orderOf_eq_one (e j)
    simpa using congrArg (fun z : normOmega E m =>
      (z : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))) h
  rw [show g * (e j : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) * g⁻¹ =
    MulAut.conj g (e j : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) by
    rw [MulAut.conj_apply]]
  rw [← map_pow, hep, map_one]

private theorem restriction_normQuad [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m : ℕ} {h : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))} {j : Fin m}
    {r : K →ₗ[F] K} (hr : ∀ x : K, r x = (h ((0, 0), Pi.single j x)).2 j)
    (hhΩ : h ∈ normOmega E m)
    (hmaps : ∀ x : K, ∃ y : K, h ((0, 0), Pi.single j x) = ((0, 0), Pi.single j y)) :
    ∀ x : K, normQuad E (r x) = normQuad E x := by
  intro x
  obtain ⟨y, hy⟩ := hmaps x
  have hiso : normHypForm E m (h ((0, 0), Pi.single j x)) =
      normHypForm E m ((0, 0), Pi.single j x) :=
    CFSG.ClassicalGroups.Orthogonal.map_of_mem
      (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup hhΩ) _
  rw [hy] at hiso
  rw [hr, show (h ((0, 0), Pi.single j x)).2 j = y from by rw [hy]; simp,
    ← normHypForm_coord_single (E := E) (j := j) (x := y), hiso,
    normHypForm_coord_single (E := E) (j := j) (x := x)]

omit [Finite K] [CharP K 2] in
private theorem restriction_pow [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m p : ℕ} [Fact p.Prime]
    {h : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))} {j : Fin m}
    {r : K →ₗ[F] K} (hr : ∀ x : K, r x = (h ((0, 0), Pi.single j x)).2 j)
    (hmaps : ∀ x : K, ∃ y : K, h ((0, 0), Pi.single j x) = ((0, 0), Pi.single j y))
    (hpow : h ^ p = 1) : r ^ p = 1 := by
  classical
  have hiter : ∀ (k : ℕ) (x : K), ∃ z : K,
      (h ^ k) (((0, 0) : F × F), (Pi.single j x : Fin m → K)) =
        (((0, 0) : F × F), (Pi.single j z : Fin m → K)) ∧ (r ^ k) x = z := by
    intro k
    induction k with
    | zero => intro x; exact ⟨x, by simp, by simp⟩
    | succ k ih =>
      intro x
      obtain ⟨z, hz, hrz⟩ := ih x
      obtain ⟨y, hy⟩ := hmaps z
      refine ⟨y, ?_, ?_⟩
      · rw [pow_succ', LinearEquiv.mul_apply, hz, hy]
      · rw [pow_succ', Module.End.mul_apply, hrz, hr]
        simpa using congrArg (fun w => w.2 j) hy
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, hz, hrz⟩ := hiter p x
  have h1 : (((0, 0) : F × F), (Pi.single j z : Fin m → K)) =
      (((0, 0) : F × F), (Pi.single j x : Fin m → K)) := by
    rw [← hz, hpow]
    rfl
  have h2 : z = x := by
    simpa using congrArg (fun w => w.2 j) h1
  rw [hrz, h2]
  simp

omit [Finite K] [CharP K 2] in
private theorem scalar_mul_case [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m p : ℕ} [Fact p.Prime]
    {h : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))} {j : Fin m}
    {u : K} {r : K →ₗ[F] K}
    (hr : ∀ x : K, r x = (h ((0, 0), Pi.single j x)).2 j)
    (hmaps : ∀ x : K, ∃ y : K, h ((0, 0), Pi.single j x) = ((0, 0), Pi.single j y))
    (hnofix : ∀ x : K, h ((0, 0), Pi.single j x) = ((0, 0), Pi.single j x) → x = 0)
    (hrp : r ^ p = 1) (hscalar : ∀ a : K, r a = u * a) :
    u ^ p = 1 ∧ u ≠ 1 ∧
      ∀ x : K, (h ((0, 0), Pi.single j x)).2 j = u * x := by
  refine ⟨?_, ?_, fun x => by rw [← hr x]; exact hscalar x⟩
  · have hu1 : ∀ k : ℕ, (r ^ k) 1 = u ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, hscalar, pow_succ']
    have h1 := hu1 p
    rw [hrp] at h1
    simpa using h1.symm
  · intro hu_eq
    refine one_ne_zero (hnofix 1 ?_)
    obtain ⟨y, hy⟩ := hmaps 1
    have hy1 : y = 1 := by
      have h2 : (h ((0, 0), Pi.single j 1)).2 j = y := by rw [hy]; simp
      rw [← h2, ← hr 1, hscalar 1, show u = 1 from hu_eq]
      simp
    rw [hy, hy1]

private theorem false_of_bar [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {E : QuadExt F K (unitaryInvolution K 2 f)}
    {h : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))} {j : Fin m}
    {u : K} {r : K →ₗ[F] K}
    (hr : ∀ x : K, r x = (h ((0, 0), Pi.single j x)).2 j)
    (hmaps : ∀ x : K, ∃ y : K, h ((0, 0), Pi.single j x) = ((0, 0), Pi.single j y))
    (hnofix : ∀ x : K, h ((0, 0), Pi.single j x) = ((0, 0), Pi.single j x) → x = 0)
    (hrp : r ^ p = 1) (hu : u * unitaryInvolution K 2 f u = 1)
    (hbar : ∀ a : K, r a = u * unitaryInvolution K 2 f a) : False := by
  have hr2 : r ^ 2 = 1 := by
    rw [pow_two]
    refine LinearMap.ext fun x => ?_
    show r (r x) = x
    rw [hbar, hbar, map_mul, E.isUnitary.invol, ← mul_assoc, hu, one_mul]
  obtain ⟨k, hk⟩ := Nat.Prime.odd_of_ne_two (Fact.out : p.Prime) hp2
  have hk2 : p = 2 * k + 1 := by omega
  have hrid : r = 1 := by
    have h1 : r ^ p = r := by
      rw [hk2, pow_add, pow_mul, hr2, one_pow, one_mul, pow_one]
    rw [hrp] at h1
    exact h1.symm
  refine one_ne_zero (hnofix 1 ?_)
  obtain ⟨y, hy⟩ := hmaps 1
  have hy1 : y = 1 := by
    have h2 : (h ((0, 0), Pi.single j 1)).2 j = y := by rw [hy]; simp
    rw [← h2, ← hr 1, hrid]
    simp
  rw [hy, hy1]

private theorem exists_scalar_of_conj [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {h : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))} {j : Fin m}
    (hhΩ : h ∈ normOmega E m)
    (hmaps : ∀ x : K, ∃ y : K, h ((0, 0), Pi.single j x) = ((0, 0), Pi.single j y))
    (hnofix : ∀ x : K, h ((0, 0), Pi.single j x) = ((0, 0), Pi.single j x) → x = 0)
    (hpow : h ^ p = 1) :
    ∃ u : K, u ^ p = 1 ∧ u ≠ 1 ∧
      ∀ x : K, (h ((0, 0), Pi.single j x)).2 j = u * x := by
  classical
  let r : K →ₗ[F] K :=
    { toFun := fun x => (h ((0, 0), Pi.single j x)).2 j
      map_add' := by
        intro x y
        have h1 : (((0, 0) : F × F), (Pi.single j (x + y) : Fin m → K)) =
            (((0, 0) : F × F), Pi.single j x) + (((0, 0) : F × F), Pi.single j y) := by
          simp [Pi.single_add]
        rw [h1, map_add]
        rfl
      map_smul' := by
        intro c x
        have h1 : (((0, 0) : F × F), (Pi.single j (c • x) : Fin m → K)) =
            c • (((0, 0) : F × F), Pi.single j x) := by
          simp [Pi.single_smul]
        rw [h1, map_smul]
        rfl }
  have hr : ∀ x : K, r x = (h ((0, 0), Pi.single j x)).2 j := fun x => rfl
  have hN := restriction_normQuad (E := E) hr hhΩ hmaps
  have hrp := restriction_pow hr hmaps hpow
  obtain ⟨u, hu, hcase⟩ :=
    CFSG.ClassicalInvolution.PhanDn.normQuad_preserver_eq_mul_or_mul_bar E r hN
  rcases hcase with hscalar | hbar
  · exact ⟨u, scalar_mul_case hr hmaps hnofix hrp hscalar⟩
  · exact (false_of_bar (E := E) hp2 hr hmaps hnofix hrp hu hbar).elim

omit [CharP K 2] in
private theorem exists_chi_eq [Finite F] [CharP F 2] [FiniteDimensional F K]
    {p : ℕ} [Fact p.Prime] {χ : Multiplicative (ZMod p) →* Kˣ}
    (hχ : Function.Injective χ) {u : K} (hu : u ^ p = 1) :
    ∃ c : Multiplicative (ZMod p), u = (χ c : K) := by
  classical
  have hp : p.Prime := Fact.out
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hu
    exact zero_ne_one hu
  let uu : Kˣ := Units.mk0 u hu0
  have huuv : (uu : K) = u := rfl
  have huup : uu ^ p = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, huuv, hu, Units.val_one]
  let c₀ : Multiplicative (ZMod p) := Multiplicative.ofAdd (1 : ZMod p)
  have hc01 : c₀ ≠ 1 := by
    show (1 : ZMod p) ≠ 0
    exact one_ne_zero
  have hc0p : c₀ ^ p = 1 := by
    have h : c₀ ^ Nat.card (Multiplicative (ZMod p)) = 1 := pow_card_eq_one'
    rwa [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at h
  have hchip : χ c₀ ^ p = 1 := by rw [← map_pow, hc0p, map_one]
  have hchi1 : χ c₀ ≠ 1 := fun h => hc01 (hχ (h.trans (map_one χ).symm))
  have hmem := CFSG.GroupTheory.mem_zpowers_of_pow_eq_one_of_prime hp hchip hchi1 huup
  have hle : Subgroup.zpowers (χ c₀) ≤ χ.range :=
    Subgroup.zpowers_le.mpr (show χ c₀ ∈ χ.range from ⟨c₀, rfl⟩)
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (hle hmem)
  exact ⟨c, by rw [← huuv, hc]⟩

private theorem coord_action [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m p : ℕ} {χ : Multiplicative (ZMod p) →* Kˣ} {j : Fin m}
    {h : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))}
    {c : Multiplicative (ZMod p)}
    (hmaps : ∀ x : K, ∃ y : K, h ((0, 0), Pi.single j x) = ((0, 0), Pi.single j y))
    (hfix : ∀ v, (∀ x : K,
      QuadraticMap.polar (normHypForm E m) ((0, 0), Pi.single j x) v = 0) → h v = v)
    (hscalar : ∀ x : K, (h ((0, 0), Pi.single j x)).2 j = (χ c : K) * x) :
    ∀ (i : Fin m) (x : K), h ((0, 0), Pi.single i x) =
      ((0, 0), Pi.single i ((Pi.mulSingle j (χ c) : Fin m → Kˣ) i * x)) := by
  intro i x
  by_cases hij : i = j
  · subst hij
    obtain ⟨y, hy⟩ := hmaps x
    have hy' : y = (χ c : K) * x := by
      have h2 : (h ((0, 0), Pi.single i x)).2 i = y := by rw [hy]; simp
      rw [← h2, hscalar x]
    rw [hy, hy', Pi.mulSingle_eq_same]
  · have hfixed : h ((0, 0), Pi.single i x) = ((0, 0), Pi.single i x) := by
      apply hfix
      intro z
      rw [QuadraticMap.polar_comm]
      exact polar_normHypForm_coord_single_ne (E := E) hij x z
    rw [hfixed, Pi.mulSingle_eq_of_ne hij]
    simp

private theorem eq_planeDiag_single [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m p : ℕ} {χ : Multiplicative (ZMod p) →* Kˣ} {j : Fin m}
    {h : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))}
    {c : Multiplicative (ZMod p)}
    (hmaps : ∀ x : K, ∃ y : K, h ((0, 0), Pi.single j x) = ((0, 0), Pi.single j y))
    (hfix : ∀ v, (∀ x : K,
      QuadraticMap.polar (normHypForm E m) ((0, 0), Pi.single j x) v = 0) → h v = v)
    (hscalar : ∀ x : K, (h ((0, 0), Pi.single j x)).2 j = (χ c : K) * x) :
    h = planeDiag m (Pi.mulSingle j (χ c)) := by
  classical
  have hcoord := coord_action (E := E) (h := h) (c := c) hmaps hfix hscalar
  refine LinearEquiv.ext fun v => ?_
  have hv : v = (v.1, (0 : Fin m → K)) + ((0 : F × F), v.2) := by
    ext <;> simp
  have hv2 : ((0 : F × F), v.2) =
      ∑ i, ((0 : F × F), (Pi.single i (v.2 i) : Fin m → K)) := by
    have h := prod_mk_sum (s := Finset.univ) (f := fun _ : Fin m => (0 : F × F))
      (g := fun i : Fin m => (Pi.single i (v.2 i) : Fin m → K))
    simpa [Finset.univ_sum_single] using h
  have hW : h ((v.1, (0 : Fin m → K))) = (v.1, 0) := by
    apply hfix
    intro z
    rw [QuadraticMap.polar_comm]
    exact polar_normHypForm_fst_coord (E := E) v.1 j z
  have hsum : ∑ i : Fin m, h ((0 : F × F), (Pi.single i (v.2 i) : Fin m → K)) =
      ∑ i : Fin m,
        ((0 : F × F), Pi.single i ((Pi.mulSingle j (χ c) : Fin m → Kˣ) i * v.2 i)) :=
    Finset.sum_congr rfl fun i _ => hcoord i (v.2 i)
  calc h v = h ((v.1, (0 : Fin m → K)) + ((0 : F × F), v.2)) := congrArg h hv
    _ = h (v.1, (0 : Fin m → K)) + h ((0 : F × F), v.2) := by rw [map_add]
    _ = (v.1, 0) + h ((0 : F × F), v.2) := by rw [hW]
    _ = (v.1, 0) + h (∑ i,
        ((0 : F × F), (Pi.single i (v.2 i) : Fin m → K))) := by rw [hv2]
    _ = (v.1, 0) + ∑ i, h ((0 : F × F),
        (Pi.single i (v.2 i) : Fin m → K)) := by rw [map_sum]
    _ = (v.1, 0) + ∑ i, ((0 : F × F),
        Pi.single i ((Pi.mulSingle j (χ c) : Fin m → Kˣ) i * v.2 i)) := by rw [hsum]
    _ = planeDiag m (Pi.mulSingle j (χ c)) v := by
      rw [planeDiag_apply]
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.univ_sum_single]

private theorem exists_planeFrame_norm {m p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hF : Nat.card F = 2 ^ f) (hpq : p ∣ 2 ^ f + 1)
    {A : Subgroup (normOmega E m)} (hA : CFSG.Open.IsElemAbelian p A)
    (hcard : Nat.card A = p ^ m) :
    ∃ (U : Fin m → Submodule F ((F × F) × (Fin m → K))) (e : Fin m → normOmega E m),
      CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.IsPlaneFrame (normHypForm E m) p U e A := by
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have : CharP F 2 := RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  have : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  have hp : p.Prime := Fact.out
  have hpq' : p ∣ Nat.card F + 1 := by rw [hF]; exact hpq
  have htype : CFSG.GroupTheory.WeirSylow.IsPlusType (normHypForm E m) ↔ Odd (m + 1) := by
    rw [isPlusType_normHypForm_iff E m]
    exact ⟨fun he => he.add_one, fun ho => Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp ho)⟩
  exact CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.exists_planeFrame (Q := normHypForm E m)
    (normHypForm_polarBilin_nondegenerate E m) (n := m + 1) (finrank_normHypForm E m) hp hp2
    hpq' htype hA (by simpa using hcard)

private theorem exists_plane_frames [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m : ℕ} {U : Fin m → Submodule F ((F × F) × (Fin m → K))}
    (hU : CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.IsPlaneSystem (normHypForm E m) U) :
    ∃ (c₀ : F) (a b : Fin m → (F × F) × (Fin m → K)),
      c₀ ∉ (CFSG.StandardType.OrdPNsOm.wp F).range ∧
      (∀ j, CFSG.StandardType.OrdPNsOm.IsFrame (normHypForm E m) c₀ true
        (Fin.elim0 : Fin 0 → _) Fin.elim0 (a j) (b j)) ∧
      (∀ j, Submodule.span F {a j, b j} = U j) ∧
      (∀ i j, i ≠ j → ∀ u ∈ ({a i, b i} : Set ((F × F) × (Fin m → K))),
        ∀ v ∈ ({a j, b j} : Set ((F × F) × (Fin m → K))),
        QuadraticMap.polar (normHypForm E m) u v = 0) := by
  obtain ⟨c₀, hc₀⟩ := CFSG.StandardType.OrdPNsOm.exists_not_mem_range_wp (K := F)
  choose a b ha hb hFr using fun j => exists_frame_in_plane hc₀ hU j
  refine ⟨c₀, a, b, hc₀, hFr, ?_, ?_⟩
  · intro j
    refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr ?_) ?_
    · rintro _ (rfl | rfl)
      exacts [ha j, hb j]
    · rw [CFSG.StandardType.OrdPNsOm.finrank_span_pair (hFr j).pab, hU.finrank_eq j]
  · intro i j hij u hu v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    exacts [hU.perp i j hij _ (ha i) _ (ha j), hU.perp i j hij _ (ha i) _ (hb j),
      hU.perp i j hij _ (hb i) _ (ha j), hU.perp i j hij _ (hb i) _ (hb j)]

private theorem exists_coord_frames [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m : ℕ} {c₀ : F} (hc₀ : c₀ ∉ (CFSG.StandardType.OrdPNsOm.wp F).range) :
    ∃ a₀ b₀ : K,
      CFSG.StandardType.OrdPNsOm.IsFrame (normQuad E) c₀ true
        (Fin.elim0 : Fin 0 → K) Fin.elim0 a₀ b₀ ∧
      Submodule.span F {a₀, b₀} = ⊤ ∧
      (∀ j, CFSG.StandardType.OrdPNsOm.IsFrame (normHypForm E m) c₀ true
        (Fin.elim0 : Fin 0 → _) Fin.elim0
        ((0, 0), Pi.single j a₀) ((0, 0), Pi.single j b₀)) ∧
      (∀ i j, i ≠ j →
        ∀ u ∈ ({((0, 0), Pi.single i a₀), ((0, 0), Pi.single i b₀)} :
          Set ((F × F) × (Fin m → K))),
        ∀ v ∈ ({((0, 0), Pi.single j a₀), ((0, 0), Pi.single j b₀)} :
          Set ((F × F) × (Fin m → K))),
        QuadraticMap.polar (normHypForm E m) u v = 0) := by
  obtain ⟨a₀, b₀, hFr0⟩ := exists_coord_frame (E := E) hc₀
  refine ⟨a₀, b₀, hFr0, ?_, fun j => isFrame_coord_plane (E := E) hFr0 j, ?_⟩
  · refine Submodule.eq_top_of_finrank_eq ?_
    rw [CFSG.StandardType.OrdPNsOm.finrank_span_pair hFr0.pab, E.finrank_eq]
  · intro i j hij u hu v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    exacts [polar_normHypForm_coord_single_ne (E := E) hij a₀ a₀,
      polar_normHypForm_coord_single_ne (E := E) hij a₀ b₀,
      polar_normHypForm_coord_single_ne (E := E) hij b₀ a₀,
      polar_normHypForm_coord_single_ne (E := E) hij b₀ b₀]

private theorem exists_frame_isometry [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m p : ℕ} {U : Fin m → Submodule F ((F × F) × (Fin m → K))}
    {e : Fin m → normOmega E m} {A : Subgroup (normOmega E m)}
    (hU : CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.IsPlaneFrame (normHypForm E m) p U e A) :
    ∃ (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
      (_hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m))
      (emb : Fin m → K →ₗ[F] ((F × F) × (Fin m → K))),
      (∀ (j : Fin m) (x : K), emb j x = ((0, 0), Pi.single j x)) ∧
      (∀ j, (U j).map g.toLinearMap = LinearMap.range (emb j)) := by
  obtain ⟨c₀, a, b, hc₀, hFr, hspanU, horth⟩ := exists_plane_frames (E := E) hU.toIsPlaneSystem
  obtain ⟨a₀, b₀, hFr0, hspanK, hFr', horth'⟩ := exists_coord_frames (E := E) hc₀
  obtain ⟨g, hgO, hgmap⟩ := exists_isometry_of_frames
    (normHypForm_polarBilin_nondegenerate E m) hFr hFr' horth horth'
  let emb : Fin m → K →ₗ[F] ((F × F) × (Fin m → K)) := fun j =>
    (0 : K →ₗ[F] F × F).prod (LinearMap.single F (fun _ : Fin m => K) j)
  have hemb : ∀ (j : Fin m) (x : K), emb j x = ((0, 0), Pi.single j x) := by
    intro j x
    simp [emb]
    rfl
  refine ⟨g, hgO, emb, hemb, ?_⟩
  intro j
  have hrange : LinearMap.range (emb j) =
      Submodule.span F {((0, 0), Pi.single j a₀), ((0, 0), Pi.single j b₀)} := by
    rw [show ((0, 0), Pi.single j a₀) = emb j a₀ from (hemb j a₀).symm,
      show ((0, 0), Pi.single j b₀) = emb j b₀ from (hemb j b₀).symm,
      LinearMap.range_eq_map, ← hspanK, Submodule.map_span, Set.image_pair]
  rw [hrange, ← hspanU j, Submodule.map_span, Set.image_pair]
  change Submodule.span F {g (a j), g (b j)} =
    Submodule.span F {((0, 0), Pi.single j a₀), ((0, 0), Pi.single j b₀)}
  rw [(hgmap j).1, (hgmap j).2]

private theorem conj_mem_omega [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m : ℕ} {e : Fin m → normOmega E m} {j : Fin m}
    {g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m)) :
    g * (e j : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) * g⁻¹ ∈
      normOmega E m := by
  have h1 : (normOmega E m).map (MulAut.conj g).toMonoidHom = normOmega E m :=
    normOmega_map_conj E hgO
  have h2 : MulAut.conj g (e j) ∈ (normOmega E m).map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem _ (e j).2
  rw [h1] at h2
  simpa [MulAut.conj_apply] using h2

private theorem conj_gen_eq_planeDiag [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    {U : Fin m → Submodule F ((F × F) × (Fin m → K))}
    {e : Fin m → normOmega E m} {A : Subgroup (normOmega E m)}
    (hU : CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.IsPlaneFrame (normHypForm E m) p U e A)
    {g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m))
    {emb : Fin m → K →ₗ[F] ((F × F) × (Fin m → K))}
    (hemb : ∀ (j : Fin m) (x : K), emb j x = ((0, 0), Pi.single j x))
    (hPU : ∀ j, (U j).map g.toLinearMap = LinearMap.range (emb j)) (j : Fin m) :
    ∃ c : Multiplicative (ZMod p),
      (g * (e j : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) * g⁻¹) =
        planeDiag m (Pi.mulSingle j (χ c)) := by
  have hmaps := conj_maps (E := E) hU (j := j) (g := g) (emb := emb j) (hPU j)
  have hfix := conj_fixes (E := E) hU hgO (j := j) (g := g) (emb := emb j) (hPU j)
  have hnofix := conj_nofix (E := E) hU (j := j) (g := g) (emb := emb j) (hemb j) (hPU j)
  have hpow := conj_pow (E := E) hU (j := j) (g := g)
  have hmaps' : ∀ x : K, ∃ y : K,
      (g * (e j : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) * g⁻¹)
        ((0, 0), Pi.single j x) = ((0, 0), Pi.single j y) := by
    intro x
    obtain ⟨y, hy⟩ := hmaps x
    exact ⟨y, by rw [← hemb j x, hy, hemb j y]⟩
  have hfix' : ∀ v, (∀ x : K,
      QuadraticMap.polar (normHypForm E m) ((0, 0), Pi.single j x) v = 0) →
      (g * (e j : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) * g⁻¹) v = v := by
    intro v hv
    apply hfix v
    intro x
    rw [hemb j x]
    exact hv x
  have hnofix' : ∀ x : K,
      (g * (e j : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) * g⁻¹)
        ((0, 0), Pi.single j x) = ((0, 0), Pi.single j x) → x = 0 := by
    intro x hx
    apply hnofix x
    rwa [hemb j x]
  obtain ⟨u, hup, hu1, hscalar⟩ :=
    exists_scalar_of_conj (E := E) hp2 (conj_mem_omega (E := E) hgO) hmaps' hnofix' hpow
  obtain ⟨c, huc⟩ := exists_chi_eq (F := F) hχ hup
  exact ⟨c, eq_planeDiag_single (E := E) hmaps' hfix' (by intro x; rw [hscalar x, huc])⟩

private theorem map_le_planeTorus_range [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m p : ℕ} [Fact p.Prime] {χ : Multiplicative (ZMod p) →* Kˣ}
    {U : Fin m → Submodule F ((F × F) × (Fin m → K))}
    {e : Fin m → normOmega E m} {A : Subgroup (normOmega E m)}
    (hm : 2 ≤ m) (hpq : p ∣ 2 ^ f + 1)
    (hU : CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.IsPlaneFrame (normHypForm E m) p U e A)
    {g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m))
    (hstep : ∀ j : Fin m,
      ∃ c : Multiplicative (ZMod p),
        (g * (e j : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) * g⁻¹) =
          planeDiag m (Pi.mulSingle j (χ c))) :
    A.map (normOmegaConj E hgO).toMonoidHom ≤ (normPlaneTorus E hm hpq χ).range := by
  rw [← hU.closure_eq, MonoidHom.map_closure]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, hj, rfl⟩
  obtain ⟨k, rfl⟩ := hj
  obtain ⟨c, hc⟩ := hstep k
  refine ⟨Pi.mulSingle k c, ?_⟩
  apply Subtype.ext
  show (normPlaneTorus E hm hpq χ (Pi.mulSingle k c) : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) = ((normOmegaConj E hgO (e k) : normOmega E m) :
      ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
  rw [normOmegaConj_apply, hc]
  refine LinearEquiv.ext fun v => ?_
  rw [normPlaneTorus_apply, planeDiag_apply]
  congr 1
  funext i
  congr 1
  by_cases hi : i = k <;> simp [hi]

private theorem card_range_planeTorus [Finite F] [CharP F 2] [FiniteDimensional F K]
    {m p : ℕ} [Fact p.Prime] (hm : 2 ≤ m) (hpq : p ∣ 2 ^ f + 1)
    {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ) :
    Nat.card (normPlaneTorus E hm hpq χ).range = p ^ m := by
  rw [MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (normPlaneTorus_injective E hm hpq hχ), Subgroup.card_top,
    Nat.card_fun, Nat.card_fin, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem exists_normOmegaConj_map_eq_normPlaneTorus_range {m p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hF : Nat.card F = 2 ^ f) (hm : 2 ≤ m) (hpq : p ∣ 2 ^ f + 1)
    {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    (A : Subgroup (normOmega E m)) (hA : CFSG.Open.IsElemAbelian p A)
    (hcard : p ^ m ≤ Nat.card A) :
    ∃ (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
      (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m)),
      A.map (normOmegaConj E hg).toMonoidHom = (normPlaneTorus E hm hpq χ).range := by
  classical
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have : CharP F 2 := RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  have : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  have : FiniteDimensional F ((F × F) × (Fin m → K)) := inferInstance
  have : Finite ((F × F) × (Fin m → K)) := inferInstance
  have hcardA : Nat.card A = p ^ m := card_of_le_pow (E := E) hp2 hF hpq hA hcard
  obtain ⟨U, e, hU⟩ := exists_planeFrame_norm (E := E) hp2 hF hpq hA hcardA
  obtain ⟨g, hgO, emb, hemb, hPU⟩ := exists_frame_isometry (E := E) hU
  have hstep := conj_gen_eq_planeDiag (E := E) hp2 hχ hU hgO hemb hPU
  refine ⟨g, hgO, Subgroup.eq_of_le_of_card_ge
    (map_le_planeTorus_range (E := E) hm hpq hU hgO hstep) ?_⟩
  have hcardmap : Nat.card (A.map (normOmegaConj E hgO).toMonoidHom) = p ^ m := by
    rw [Subgroup.card_map_of_injective (normOmegaConj E hgO).injective, hcardA]
  rw [hcardmap, card_range_planeTorus (E := E) hm hpq hχ]

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

end
