module

public import CFSG.ClassicalGroups.Orthogonal.FramedPlanes.Flag
public import CFSG.ClassicalGroups.Orthogonal.FramedPlanes.Triangulable
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCast
import CFSG.ClassicalGroups.Orthogonal.FramedPlanes.Supported

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open Module QuadraticMap
open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.ClassicalGroups.Orthogonal.FramedPlanes CFSG.LieType.CurtisTits

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

theorem exists_polar_normQuad_one_eq_one : ∃ ω : K, polar (normQuad E) 1 ω = 1 := by
  obtain ⟨y, hy⟩ := CFSG.ClassicalGroups.Orthogonal.exists_polar_ne_zero
    (normQuad_polarBilin_nondegenerate E) (one_ne_zero : (1 : K) ≠ 0)
  exact ⟨(polar (normQuad E) 1 y)⁻¹ • y, by
    rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hy]⟩

theorem normHypForm_zero_single (n : ℕ) (j : Fin n) (x : K) :
    normHypForm E n (0, Pi.single j x) = normQuad E x := by
  rw [normHypForm_apply_coord]
  have h1 : hypPlane F (((0, Pi.single j x) : (F × F) × (Fin n → K)).1) = 0 := by
    simp [hypPlane_apply]
  have h2 : (∑ i, normQuad E (((0, Pi.single j x) : (F × F) × (Fin n → K)).2 i)) =
      normQuad E x := by
    dsimp only
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [Pi.single_eq_of_ne hij, QuadraticMap.map_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [h1, h2, zero_add]

theorem polar_normHypForm_zero_single (n : ℕ) (j : Fin n) (x y : K) :
    polar (normHypForm E n) (0, Pi.single j x) (0, Pi.single j y) = polar (normQuad E) x y := by
  rw [polar_hypSum]
  dsimp only
  rw [polar_Qn_single]
  simp

private theorem polar_normHypForm_single_single_of_ne (E : QuadExt F K (unitaryInvolution K 2 f))
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) (a b : K) :
    polar (normHypForm E n) ((0, Pi.single i a) : (F × F) × (Fin n → K))
      (0, Pi.single j b) = 0 := by
  rw [polar_hypSum]
  dsimp only
  rw [polar_Qn_single, Pi.single_eq_of_ne (Ne.symm hij)]
  simp

private theorem normHypForm_single_add_single (E : QuadExt F K (unitaryInvolution K 2 f))
    {n : ℕ} {a b : Fin n} (hab : a ≠ b) (t : F) (x : K) :
    normHypForm E n (((t, 0), Pi.single a x + Pi.single b x) : (F × F) × (Fin n → K)) = 0 := by
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hsum : (∑ i, normQuad E ((Pi.single a x + Pi.single b x : Fin n → K) i)) =
      normQuad E x + normQuad E x := by
    have hzero : ∀ i ∈ (Finset.univ : Finset (Fin n)), i ∉ ({a, b} : Finset (Fin n)) →
        normQuad E ((Pi.single a x + Pi.single b x : Fin n → K) i) = 0 := by
      intro i _ hi
      have hia : i ≠ a := by rintro rfl; exact hi (by simp)
      have hib : i ≠ b := by rintro rfl; exact hi (by simp)
      rw [Pi.add_apply, Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib, add_zero,
        QuadraticMap.map_zero]
    have ha : (Pi.single a x + Pi.single b x : Fin n → K) a = x := by
      rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab, add_zero]
    have hb : (Pi.single a x + Pi.single b x : Fin n → K) b = x := by
      rw [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hab), Pi.single_eq_same, zero_add]
    rw [← Finset.sum_subset (Finset.subset_univ ({a, b} : Finset (Fin n))) hzero,
      Finset.sum_pair hab, ha, hb]
  rw [normHypForm_apply_coord]
  have h1 : hypPlane F ((((t, 0), Pi.single a x + Pi.single b x) :
      (F × F) × (Fin n → K)).1) = 0 := by
    simp [hypPlane_apply]
  have h3 : (∑ i, normQuad E ((((t, 0), Pi.single a x + Pi.single b x) :
      (F × F) × (Fin n → K)).2 i)) = normQuad E x + normQuad E x := hsum
  rw [h1, h3, ← two_mul, h2, zero_mul, add_zero]

@[expose] noncomputable def normChamber (ω : K) (hω : polar (normQuad E) 1 ω = 1) (n : ℕ)
    (j : Fin n) : FrameVert (normHypForm E n) (normQuad E ω) n where
  typ := j
  u := (0, Pi.single j 1)
  w := (0, Pi.single j ω)
  Q_u := by rw [normHypForm_zero_single, normQuad_one]
  Q_w := normHypForm_zero_single E n j ω
  polar_u_w := by rw [polar_normHypForm_zero_single, hω]

variable (ω : K) (hω : polar (normQuad E) 1 ω = 1)

private theorem smul_normChamber_eq_iff {n : ℕ} {j : Fin n} {g : normOmega E n} :
    g • normChamber E ω hω n j = normChamber E ω hω n j ↔
      ((g : normOmega E n) :
          ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) (0, Pi.single j 1) =
          (0, Pi.single j 1) ∧
        ((g : normOmega E n) :
          ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) (0, Pi.single j ω) =
          (0, Pi.single j ω) := by
  rw [← MulAction.mem_stabilizer_iff, mem_stabilizer_iff]
  exact Iff.rfl

private theorem mem_span_one_omega (E : QuadExt F K (unitaryInvolution K 2 f)) (ω : K)
    (hω : polar (normQuad E) 1 ω = 1) (x : K) :
    x ∈ Submodule.span F ({1, ω} : Set K) := by
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h11 : polar (normQuad E) 1 1 = 0 := by
    rw [CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul, normQuad_one, h2, zero_mul]
  have hli : LinearIndependent F ![(1 : K), ω] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      have h := congrArg (polar (normQuad E) 1) hst
      rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
        QuadraticMap.polar_smul_right, h11, hω] at h
      simpa using h
    have hs : s = 0 := by
      rw [ht, zero_smul, add_zero] at hst
      simpa using hst
    exact ⟨hs, ht⟩
  have hrange : Set.range ![(1 : K), ω] = ({1, ω} : Set K) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      exacts [⟨0, by simp⟩, ⟨1, by simp⟩]
  have htop : Submodule.span F ({1, ω} : Set K) = ⊤ := by
    rw [← hrange]
    exact hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, E.finrank_eq])
  rw [htop]
  trivial

private theorem single_eq_smul_add (ω : K) {n : ℕ} (j : Fin n) (c d : F) :
    ((0, Pi.single j (c • (1 : K) + d • ω)) : (F × F) × (Fin n → K)) =
      c • ((0, Pi.single j 1) : (F × F) × (Fin n → K)) +
        d • ((0, Pi.single j ω) : (F × F) × (Fin n → K)) := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · simp
  · by_cases hi : i = j
    · subst hi
      simp
    · simp [Pi.single_eq_of_ne hi]

private theorem smul_single_eq_of_mem_span (hω : polar (normQuad E) 1 ω = 1) {n : ℕ} {j : Fin n}
    {g : normOmega E n} (x : K)
    (h1 : ((g : normOmega E n) :
        ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) (0, Pi.single j 1) =
      (0, Pi.single j 1))
    (hω' : ((g : normOmega E n) :
        ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) (0, Pi.single j ω) =
      (0, Pi.single j ω)) :
    ((g : normOmega E n) :
        ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) (0, Pi.single j x) =
      (0, Pi.single j x) := by
  obtain ⟨c, d, hcd⟩ :=
    Submodule.mem_span_pair.mp (mem_span_one_omega E ω hω x)
  have hdecomp : ((0, Pi.single j x) : (F × F) × (Fin n → K)) =
      c • ((0, Pi.single j 1) : (F × F) × (Fin n → K)) +
        d • ((0, Pi.single j ω) : (F × F) × (Fin n → K)) := by
    rw [← single_eq_smul_add ω j c d, hcd]
  rw [hdecomp, map_add, map_smul, map_smul, h1, hω', ← hdecomp]

@[simp] theorem normChamber_typ {n : ℕ} (j : Fin n) : (normChamber E ω hω n j).typ = j :=
  rfl

@[simp] theorem normChamber_u {n : ℕ} (j : Fin n) :
    (normChamber E ω hω n j).u = (0, Pi.single j 1) :=
  rfl

@[simp] theorem normChamber_w {n : ℕ} (j : Fin n) :
    (normChamber E ω hω n j).w = (0, Pi.single j ω) :=
  rfl

theorem normChamber_adj {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (frameGraph (normHypForm E n) (normQuad E ω) n).Adj (normChamber E ω hω n i)
      (normChamber E ω hω n j) := by
  refine ⟨hij, ?_, ?_, ?_, ?_⟩
  · exact polar_normHypForm_single_single_of_ne E hij 1 1
  · exact polar_normHypForm_single_single_of_ne E hij 1 ω
  · exact polar_normHypForm_single_single_of_ne E hij ω 1
  · exact polar_normHypForm_single_single_of_ne E hij ω ω

theorem exists_totallySingular_coordSupport {n : ℕ} (S : Finset (Fin n)) (hS : 2 ≤ S.card) :
    ∃ T : Submodule F ((F × F) × (Fin n → K)),
      T ≤ coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S ∧
        finrank F T = 3 ∧ ∀ x ∈ T, normHypForm E n x = 0 := by
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  let ℓ : (F × K) →ₗ[F] ((F × F) × (Fin n → K)) :=
    ((LinearMap.inl F F F).comp (LinearMap.fst F F K)).prod
      ((LinearMap.single F (fun _ : Fin n => K) a +
        LinearMap.single F (fun _ : Fin n => K) b).comp (LinearMap.snd F F K))
  have ℓ_apply : ∀ (t : F) (x : K),
      ℓ (t, x) = (((t, 0), Pi.single a x + Pi.single b x) : (F × F) × (Fin n → K)) := by
    intro t x
    simp [ℓ]
  have hinj : Function.Injective ℓ := by
    rintro ⟨t, x⟩ ⟨t', x'⟩ h
    have h1 : t = t' := by
      have := congrArg (fun v : (F × F) × (Fin n → K) => v.1.1) h
      simpa [ℓ_apply] using this
    have h2 : x = x' := by
      have hval : ∀ y : K, ((Pi.single a y + Pi.single b y : Fin n → K) a) = y := by
        intro y
        rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab, add_zero]
      have := congrArg (fun v : (F × F) × (Fin n → K) => v.2 a) h
      simpa [ℓ_apply, hval] using this
    exact Prod.ext h1 h2
  refine ⟨LinearMap.range ℓ, ?_, ?_, ?_⟩
  · rintro _ ⟨⟨t, x⟩, rfl⟩
    rw [mem_coordSupport_refl_iff E S]
    intro j hj
    have hja : j ≠ a := by rintro rfl; exact hj ha
    have hjb : j ≠ b := by rintro rfl; exact hj hb
    rw [ℓ_apply]
    simp [Pi.single_eq_of_ne hja, Pi.single_eq_of_ne hjb]
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_self,
      E.finrank_eq]
  · rintro _ ⟨⟨t, x⟩, rfl⟩
    rw [ℓ_apply]
    exact normHypForm_single_add_single E hab t x

private theorem eq_sum_single_of_mem_suppPerp_coordSupport {n : ℕ} (S : Finset (Fin n))
    {v : (F × F) × (Fin n → K)}
    (hv : v ∈ suppPerp (normHypForm E n)
      (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S)) :
    v = ∑ j ∈ Sᶜ, ((0, Pi.single j (v.2 j)) : (F × F) × (Fin n → K)) := by
  obtain ⟨hv1, hv2⟩ := (mem_suppPerp_coordSupport_refl_iff E S v).mp hv
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum, hv1]
    simp
  · rw [Prod.snd_sum]
    funext i
    rw [Finset.sum_apply]
    by_cases hi : i ∈ S
    · have hz : ∀ j ∈ Sᶜ, (Pi.single j (v.2 j) : Fin n → K) i = 0 := by
        intro j hj
        exact Pi.single_eq_of_ne (by rintro rfl; exact (Finset.mem_compl.mp hj) hi) _
      rw [Finset.sum_eq_zero hz, hv2 i hi]
    · have hmem : i ∈ Sᶜ := Finset.mem_compl.mpr hi
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        exact Pi.single_eq_of_ne (Ne.symm hji) _
      · intro hcon
        exact absurd hmem hcon

private theorem apply_eq_of_fixes_normChamber {n : ℕ} (S : Finset (Fin n)) {g : normOmega E n}
    (h : ∀ j ∈ (↑Sᶜ : Set (Fin n)), g • normChamber E ω hω n j = normChamber E ω hω n j)
    {v : (F × F) × (Fin n → K)}
    (hv : v ∈ suppPerp (normHypForm E n)
      (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S)) :
    ((g : normOmega E n) :
        ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) v = v := by
  have hfix : ∀ j, j ∉ S →
      ((g : normOmega E n) :
          ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) (0, Pi.single j 1) =
          (0, Pi.single j 1) ∧
        ((g : normOmega E n) :
          ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) (0, Pi.single j ω) =
          (0, Pi.single j ω) := by
    intro j hj
    exact (smul_normChamber_eq_iff E ω hω).mp (h j (by simpa using hj))
  have hstep : ∀ j ∈ Sᶜ,
      ((g : normOmega E n) :
          ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) (0, Pi.single j (v.2 j)) =
        (0, Pi.single j (v.2 j)) := by
    intro j hj
    obtain ⟨h1, h2⟩ := hfix j (Finset.mem_compl.mp hj)
    exact smul_single_eq_of_mem_span E ω hω (v.2 j) h1 h2
  have hcoord := eq_sum_single_of_mem_suppPerp_coordSupport E S hv
  calc ((g : normOmega E n) :
          ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) v
      = ((g : normOmega E n) :
          ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K)))
          (∑ j ∈ Sᶜ, ((0, Pi.single j (v.2 j)) : (F × F) × (Fin n → K))) :=
          congrArg _ hcoord
    _ = ∑ j ∈ Sᶜ, ((0, Pi.single j (v.2 j)) : (F × F) × (Fin n → K)) := by
          rw [map_sum]
          exact Finset.sum_congr rfl hstep
    _ = v := hcoord.symm

private theorem fixes_normChamber_of_apply_eq {n : ℕ} (S : Finset (Fin n)) {g : normOmega E n}
    (h : ∀ v ∈ suppPerp (normHypForm E n)
      (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S),
      ((g : normOmega E n) :
        ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) v = v)
    {j : Fin n} (hj : j ∈ (↑Sᶜ : Set (Fin n))) :
    g • normChamber E ω hω n j = normChamber E ω hω n j := by
  have hj' : j ∉ S := by simpa using hj
  rw [smul_normChamber_eq_iff E ω hω]
  refine ⟨h _ ?_, h _ ?_⟩ <;>
    rw [mem_suppPerp_coordSupport_refl_iff E S] <;>
    exact ⟨rfl, fun i hi => Pi.single_eq_of_ne (by rintro rfl; exact hj' hi) _⟩

theorem parabolic_normChamber_compl {n : ℕ} (S : Finset (Fin n)) (hS : 2 ≤ S.card) :
    parabolic ↥(normOmega E n) (normChamber E ω hω n) (↑(Sᶜ) : Set (Fin n)) =
      normBlock E n S := by
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  ext g
  rw [normBlock, Subgroup.mem_subgroupOf,
    mem_supportedDerived_iff_mem_orthDerived (Q := normHypForm E n)
      (normHypForm_polarBilin_nondegenerate E n)
      (coordSupport_nondegenerate (LinearEquiv.refl F ((F × F) × (Fin n → K)))
        (hψ := normHypForm_apply_coord E n)
        (hQ := normHypForm_polarBilin_nondegenerate E n)
        (hQE := normQuad_polarBilin_nondegenerate E) S)
      (exists_totallySingular_coordSupport E S hS),
    mem_parabolic_iff]
  constructor
  · intro h
    exact ⟨g.2, fun v hv => apply_eq_of_fixes_normChamber E ω hω S h hv⟩
  · rintro ⟨-, hv⟩ j hj
    exact fixes_normChamber_of_apply_eq E ω hω S hv hj

theorem parabolic_normChamber_le_erase {n : ℕ} (hn : 3 ≤ n) {J : Set (Fin n)} {j : Fin n}
    (hj : j ∈ J) :
    parabolic ↥(normOmega E n) (normChamber E ω hω n) J ≤
      normBlock E n (Finset.univ.erase j) := by
  have hS : 2 ≤ (Finset.univ.erase j).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
    omega
  have hset : ((Finset.univ.erase j)ᶜ : Finset (Fin n)) = {j} := by
    rw [Finset.compl_erase, Finset.compl_univ]
    simp
  intro g hg
  rw [← parabolic_normChamber_compl E ω hω (Finset.univ.erase j) hS]
  have hcoe : ((↑((Finset.univ.erase j)ᶜ) : Finset (Fin n)) : Set (Fin n)) = {j} := by
    rw [hset]
    exact Finset.coe_singleton j
  rw [hcoe]
  exact parabolic_antitone (F := normChamber E ω hω n) (G := ↥(normOmega E n)) (by
    intro i hi
    rw [Set.mem_singleton_iff] at hi
    subst hi
    exact hj) hg

theorem parabolic_normChamber_le_erase_erase {n : ℕ} (hn : 4 ≤ n) {J : Set (Fin n)}
    {i j : Fin n} (hi : i ∈ J) (hj : j ∈ J) :
    parabolic ↥(normOmega E n) (normChamber E ω hω n) J ≤
      normBlock E n ((Finset.univ.erase i).erase j) := by
  have hS : 2 ≤ ((Finset.univ.erase i).erase j).card := by
    have h1 : (Finset.univ.erase i).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have h2 := Finset.pred_card_le_card_erase (s := Finset.univ.erase i) (a := j)
    omega
  have hset0 : ((Finset.univ.erase i)ᶜ : Finset (Fin n)) = {i} := by
    rw [Finset.compl_erase, Finset.compl_univ]
    simp
  have hset : (((Finset.univ.erase i).erase j)ᶜ : Finset (Fin n)) = {i, j} := by
    rw [Finset.compl_erase, hset0, Finset.pair_comm i j]
  intro g hg
  rw [← parabolic_normChamber_compl E ω hω ((Finset.univ.erase i).erase j) hS]
  have hcoe : ((↑(((Finset.univ.erase i).erase j)ᶜ) : Finset (Fin n)) : Set (Fin n)) =
      ({i, j} : Set (Fin n)) := by
    rw [hset]
    simp
  rw [hcoe]
  exact parabolic_antitone (F := normChamber E ω hω n) (G := ↥(normOmega E n)) (by
    intro k hk
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl
    · exact hi
    · exact hj) hg

theorem normPerm_mem_parabolic_singleton {n : ℕ} (hn : 3 ≤ n) {σ : Equiv.Perm (Fin n)}
    {j : Fin n} (hσ : σ j = j) :
    normPerm E hn σ ∈ parabolic ↥(normOmega E n) (normChamber E ω hω n) {j} := by
  rw [mem_parabolic_singleton_iff, smul_normChamber_eq_iff E ω hω]
  have hσ' : σ⁻¹ j = j := (Equiv.symm_apply_eq σ).mpr hσ.symm
  have hfix : ∀ i : Fin n,
      (Pi.single j (1 : K) : Fin n → K) (σ⁻¹ i) =
        ((Pi.single j (1 : K) : Fin n → K)) i := by
    intro i
    by_cases hi : i = j
    · subst hi
      rw [hσ', Pi.single_eq_same]
    · have hne : σ⁻¹ i ≠ j := by
        intro hcon
        apply hi
        have h := congrArg σ hcon
        simpa [hσ] using h
      rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hi]
  have hfixω : ∀ i : Fin n,
      (Pi.single j (ω : K) : Fin n → K) (σ⁻¹ i) =
        ((Pi.single j (ω : K) : Fin n → K)) i := by
    intro i
    by_cases hi : i = j
    · subst hi
      rw [hσ', Pi.single_eq_same]
    · have hne : σ⁻¹ i ≠ j := by
        intro hcon
        apply hi
        have h := congrArg σ hcon
        simpa [hσ] using h
      rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hi]
  constructor
  · rw [normPerm_apply E hn σ]
    exact Prod.ext rfl (funext hfix)
  · rw [normPerm_apply E hn σ]
    exact Prod.ext rfl (funext hfixω)

theorem normPerm_mem_normBlock_of_fixing_compl {r : ℕ} (hr : 3 ≤ r)
    (S : Finset (Fin r)) (σ : Equiv.Perm (Fin r))
    (hσ : ∀ i, i ∉ S → σ i = i) :
    normPerm E hr σ ∈ normBlock E r S := by
  classical
  by_cases h1 : σ = 1
  · subst σ
    simpa only [map_one] using (normBlock E r S).one_mem
  have hsupp : σ.support ⊆ S := by
    intro i hi
    by_contra his
    exact (Equiv.Perm.mem_support.mp hi) (hσ i his)
  have hS : 2 ≤ S.card :=
    (Equiv.Perm.two_le_card_support_of_ne_one h1).trans
      (Finset.card_le_card hsupp)
  obtain ⟨ω, hω⟩ := exists_polar_normQuad_one_eq_one E
  rw [← parabolic_normChamber_compl E ω hω S hS, mem_parabolic_iff]
  intro j hj
  exact mem_parabolic_singleton_iff.mp
    (normPerm_mem_parabolic_singleton E ω hω hr (hσ j (by simpa using hj)))

theorem normPerm_swap_mem_normBlock {r : ℕ} (hr : 3 ≤ r) (i j : Fin r) :
    normPerm E hr (Equiv.swap i j) ∈ normBlock E r {i, j} := by
  apply normPerm_mem_normBlock_of_fixing_compl E hr {i, j} (Equiv.swap i j)
  intro k hk
  have hki : k ≠ i := by
    intro h
    exact hk (by simp [h])
  have hkj : k ≠ j := by
    intro h
    exact hk (by simp [h])
  exact Equiv.swap_apply_of_ne_of_ne hki hkj

theorem flagTransitive_normChamber {n : ℕ} (hn : 2 ≤ n) :
    FlagTransitive ↥(normOmega E n) (frameGraph (normHypForm E n) (normQuad E ω) n)
      (normChamber E ω hω n) := by
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  obtain ⟨T, -, hT3, hT0⟩ := exists_totallySingular_coordSupport E (Finset.univ : Finset (Fin n))
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  refine flagTransitive_frameGraph (Q := normHypForm E n) (ν := normQuad E ω)
    (v := (((1, 1), 0) : (F × F) × (Fin n → K)))
    (normHypForm_polarBilin_nondegenerate E n) ⟨T, hT3, hT0⟩ (normChamber E ω hω n)
    (fun j => normChamber_typ E ω hω j) (fun i j hij => normChamber_adj E ω hω hij) ?_ ?_
  · rw [normHypForm_apply_coord]
    simp [hypPlane_apply]
  · intro j
    refine ⟨?_, ?_⟩
    · rw [normChamber_u, polar_hypSum]
      simp
    · rw [normChamber_w, polar_hypSum]
      simp

theorem iSup_stabilizer_normChamber {n : ℕ} (hn : 5 ≤ n) :
    (⨆ i, MulAction.stabilizer ↥(normOmega E n) (normChamber E ω hω n i)) = ⊤ := by
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hV : 12 ≤ Module.finrank F ((F × F) × (Fin n → K)) := by
    rw [finrank_normHypForm E n]
    omega
  exact iSup_stabilizer_eq_top_of_connected (typ := FrameVert.typ)
    (Γ := frameGraph (normHypForm E n) (normQuad E ω) n) (F := normChamber E ω hω n)
    (fun j => normChamber_typ E ω hω j) (fun g x => typ_smul g x)
    (flagTransitive_normChamber E ω hω (by omega))
    (frameGraph_preconnected (normHypForm_polarBilin_nondegenerate E n) hV hn)

theorem triangulable_normFrameGraph {n : ℕ} (hn : 5 ≤ n) :
    CFSG.Monster.B.Recog.Triangulable (frameGraph (normHypForm E n) (normQuad E ω) n) := by
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have hV : 12 ≤ Module.finrank F ((F × F) × (Fin n → K)) := by
    rw [finrank_normHypForm E n]
    omega
  exact triangulable_frameGraph (normHypForm_polarBilin_nondegenerate E n) hV hn

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
