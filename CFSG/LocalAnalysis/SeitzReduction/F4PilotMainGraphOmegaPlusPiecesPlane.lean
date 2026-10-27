module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactBlock
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.SeitzReduction.OmegaPilot (diagOmega)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.SymplecticPilot (planeOf diagSpEntry)
open scoped commutatorElement

section Group

variable {G : Type*} [Group G] {z g h : G} {n n' : ℤ}

theorem conj_mul_eq_zpow_of_conj (hg : g * z * g⁻¹ = z ^ n) (hh : h * z * h⁻¹ = z ^ n') :
    g * h * z * (g * h)⁻¹ = z ^ (n * n') := by
  have e : g * h * z * (g * h)⁻¹ = g * (h * z * h⁻¹) * g⁻¹ := by group
  have hc := map_zpow (MulAut.conj g) z n'
  simp only [MulAut.conj_apply] at hc
  rw [e, hh, hc, hg, ← _root_.zpow_mul]

theorem conj_inv_eq_zpow_of_conj (hn : n * n = 1) (hg : g * z * g⁻¹ = z ^ n) :
    g⁻¹ * z * g⁻¹⁻¹ = z ^ n := by
  have h1 : g⁻¹ * z ^ n * g = z := by rw [← hg]; group
  have hc := map_zpow (MulAut.conj g⁻¹) (z ^ n) n
  simp only [MulAut.conj_apply, inv_inv] at hc
  rw [h1, ← _root_.zpow_mul, hn, zpow_one] at hc
  rw [inv_inv, hc]

theorem commute_commutatorElement_of_conj_zpow (hn : n * n = 1) (hn' : n' * n' = 1)
    (hg : g * z * g⁻¹ = z ^ n) (hh : h * z * h⁻¹ = z ^ n') : Commute ⁅g, h⁆ z := by
  have h1 := conj_mul_eq_zpow_of_conj hg hh
  have h2 := conj_mul_eq_zpow_of_conj (conj_inv_eq_zpow_of_conj hn hg)
    (conj_inv_eq_zpow_of_conj hn' hh)
  have h3 := conj_mul_eq_zpow_of_conj h1 h2
  have hexp : n * n' * (n * n') = 1 := by linear_combination (n' * n') * hn + hn'
  rw [hexp, zpow_one] at h3
  have e : ⁅g, h⁆ = g * h * (g⁻¹ * h⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  show g * h * (g⁻¹ * h⁻¹) * z = z * (g * h * (g⁻¹ * h⁻¹))
  calc g * h * (g⁻¹ * h⁻¹) * z =
        g * h * (g⁻¹ * h⁻¹) * z * (g * h * (g⁻¹ * h⁻¹))⁻¹ * (g * h * (g⁻¹ * h⁻¹)) := by group
    _ = z * (g * h * (g⁻¹ * h⁻¹)) := by rw [h3]

end Group

section Plane

variable {K : Type} [Field K] {m : ℕ} {j : Fin m}

theorem statedQuadPlus_eq_of_inl_eq_zero {w : Fin m ⊕ Fin m → K}
    (hw : ∀ i, i ≠ j → w (Sum.inl i) = 0) :
    StatedQuadPlus m K w = w (Sum.inl j) * w (Sum.inr j) := by
  unfold StatedQuadPlus
  exact Finset.sum_eq_single j (fun i _ hij => by rw [hw i hij, zero_mul])
    (fun h => absurd (Finset.mem_univ j) h)

theorem plane_diag_or_antidiag_of_isometry {M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hiso : ∀ v, StatedQuadPlus m K (M *ᵥ v) = StatedQuadPlus m K v)
    (hcol : ∀ i, i ≠ j → M (Sum.inl i) (Sum.inl j) = 0 ∧ M (Sum.inl i) (Sum.inr j) = 0) :
    (M (Sum.inl j) (Sum.inr j) = 0 ∧ M (Sum.inr j) (Sum.inl j) = 0) ∨
      (M (Sum.inl j) (Sum.inl j) = 0 ∧ M (Sum.inr j) (Sum.inr j) = 0) := by
  have c1 : M *ᵥ Pi.single (Sum.inl j) 1 = fun a => M a (Sum.inl j) := by
    rw [mulVec_single_one]; rfl
  have c2 : M *ᵥ Pi.single (Sum.inr j) 1 = fun a => M a (Sum.inr j) := by
    rw [mulVec_single_one]; rfl
  have e1 : (Pi.single (Sum.inl j) (1 : K) : Fin m ⊕ Fin m → K) (Sum.inr j) = 0 :=
    Pi.single_eq_of_ne Sum.inr_ne_inl _
  have e2 : (Pi.single (Sum.inr j) (1 : K) : Fin m ⊕ Fin m → K) (Sum.inl j) = 0 :=
    Pi.single_eq_of_ne Sum.inl_ne_inr _
  have s1 : ∀ i, i ≠ j → (Pi.single (Sum.inl j) (1 : K) : Fin m ⊕ Fin m → K) (Sum.inl i) = 0 :=
    fun i hi => Pi.single_eq_of_ne (fun h => hi (Sum.inl_injective h)) _
  have s2 : ∀ i, (Pi.single (Sum.inr j) (1 : K) : Fin m ⊕ Fin m → K) (Sum.inl i) = 0 :=
    fun i => Pi.single_eq_of_ne Sum.inl_ne_inr _
  have h1 := hiso (Pi.single (Sum.inl j) 1)
  have h2 := hiso (Pi.single (Sum.inr j) 1)
  have h3 := hiso (Pi.single (Sum.inl j) 1 + Pi.single (Sum.inr j) 1)
  rw [c1, statedQuadPlus_eq_of_inl_eq_zero (j := j) (fun i hi => (hcol i hi).1),
    statedQuadPlus_eq_of_inl_eq_zero (j := j) s1, e1, mul_zero] at h1
  rw [c2, statedQuadPlus_eq_of_inl_eq_zero (j := j) (fun i hi => (hcol i hi).2),
    statedQuadPlus_eq_of_inl_eq_zero (j := j) (fun i _ => s2 i), e2, zero_mul] at h2
  rw [mulVec_add, c1, c2, statedQuadPlus_eq_of_inl_eq_zero (j := j) (fun i hi => by
      simp only [Pi.add_apply, (hcol i hi).1, (hcol i hi).2, add_zero]),
    statedQuadPlus_eq_of_inl_eq_zero (j := j) (fun i hi => by
      simp only [Pi.add_apply, s1 i hi, s2 i, add_zero])] at h3
  simp only [Pi.add_apply, Pi.single_eq_same, e1, e2, add_zero, zero_add, mul_one] at h3
  by_cases hα : M (Sum.inl j) (Sum.inl j) = 0
  · right
    refine ⟨hα, ?_⟩
    have hβγ : M (Sum.inl j) (Sum.inr j) * M (Sum.inr j) (Sum.inl j) = 1 := by
      rw [hα, zero_add] at h3
      linear_combination h3 - h2
    have hβ : M (Sum.inl j) (Sum.inr j) ≠ 0 := by
      intro hβ
      rw [hβ, zero_mul] at hβγ
      exact zero_ne_one hβγ
    exact (mul_eq_zero.1 h2).resolve_left hβ
  · left
    have hγ : M (Sum.inr j) (Sum.inl j) = 0 := (mul_eq_zero.1 h1).resolve_left hα
    have hαδ : M (Sum.inl j) (Sum.inl j) * M (Sum.inr j) (Sum.inr j) = 1 := by
      rw [hγ, zero_add] at h3
      linear_combination h3 - h2
    have hδ : M (Sum.inr j) (Sum.inr j) ≠ 0 := by
      intro hδ
      rw [hδ, mul_zero] at hαδ
      exact zero_ne_one hαδ
    exact ⟨(mul_eq_zero.1 h2).resolve_right hδ, hγ⟩

theorem diagSpEntry_mulSingle_of_planeOf_ne (c : Kˣ) {a : Fin m ⊕ Fin m} (ha : planeOf a ≠ j) :
    diagSpEntry (Pi.mulSingle j c) a = 1 :=
  SymplecticPilot.diagSpEntry_mulSingle_of_not_mem j c
    (fun h => ha (SymplecticPilot.planeOf_eq_of_mem_coords h))

theorem commute_diagOmega_mulSingle_of_plane {x : GL (Fin m ⊕ Fin m) K}
    (hblk : ∀ a b, planeOf a = j → planeOf b ≠ j →
      (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a b = 0 ∧
        (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) b a = 0)
    (hD : (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (Sum.inl j) (Sum.inr j) = 0 ∧
      (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (Sum.inr j) (Sum.inl j) = 0)
    (c : Kˣ) : Commute x (diagOmega K m (Pi.mulSingle j c)) := by
  refine (SymplecticPilot.commute_of_diag_iff
    (fun a b hab => OmegaPilot.diagOmega_apply_ne _ hab) x).2 fun a b hab => ?_
  rw [OmegaPilot.diagOmega_apply_self, OmegaPilot.diagOmega_apply_self] at hab
  by_cases ha : planeOf a = j
  · by_cases hb : planeOf b = j
    · rcases a with i | i <;> rcases b with i' | i' <;>
        simp only [SymplecticPilot.planeOf_inl, SymplecticPilot.planeOf_inr] at ha hb <;>
        subst ha hb
      · exact absurd rfl hab
      · exact hD.1
      · exact hD.2
      · exact absurd rfl hab
    · exact (hblk a b ha hb).1
  · by_cases hb : planeOf b = j
    · exact (hblk b a hb ha).2
    · exact absurd (by rw [diagSpEntry_mulSingle_of_planeOf_ne c ha,
        diagSpEntry_mulSingle_of_planeOf_ne c hb]) hab

theorem mul_diagOmega_mulSingle_of_plane {x : GL (Fin m ⊕ Fin m) K}
    (hblk : ∀ a b, planeOf a = j → planeOf b ≠ j →
      (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a b = 0 ∧
        (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) b a = 0)
    (hA : (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (Sum.inl j) (Sum.inl j) = 0 ∧
      (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (Sum.inr j) (Sum.inr j) = 0)
    (c : Kˣ) :
    x * diagOmega K m (Pi.mulSingle j c) = (diagOmega K m (Pi.mulSingle j c))⁻¹ * x := by
  rw [← map_inv (diagOmega K m), ← Pi.mulSingle_inv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, OmegaPilot.diagOmega_coe, OmegaPilot.diagOmega_coe]
  ext a b
  rw [mul_diagonal, diagonal_mul]
  by_cases ha : planeOf a = j
  · by_cases hb : planeOf b = j
    · rcases a with i | i <;> rcases b with i' | i' <;>
        simp only [SymplecticPilot.planeOf_inl, SymplecticPilot.planeOf_inr] at ha hb <;>
        subst ha hb
      · rw [hA.1, zero_mul, mul_zero]
      · rw [SymplecticPilot.diagSpEntry_mulSingle_inr_self,
          SymplecticPilot.diagSpEntry_mulSingle_inl_self, mul_comm]
      · rw [SymplecticPilot.diagSpEntry_mulSingle_inl_self,
          SymplecticPilot.diagSpEntry_mulSingle_inr_self, inv_inv, mul_comm]
      · rw [hA.2, zero_mul, mul_zero]
    · rw [(hblk a b ha hb).1, zero_mul, mul_zero]
  · by_cases hb : planeOf b = j
    · rw [(hblk b a hb ha).2, zero_mul, mul_zero]
    · rw [diagSpEntry_mulSingle_of_planeOf_ne c hb, diagSpEntry_mulSingle_of_planeOf_ne c⁻¹ ha,
        mul_one, one_mul]

theorem exists_conj_diagOmega_mulSingle_eq_zpow {x : GL (Fin m ⊕ Fin m) K}
    (hiso : ∀ v, StatedQuadPlus m K ((x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v) =
      StatedQuadPlus m K v)
    (hblk : ∀ a b, planeOf a = j → planeOf b ≠ j →
      (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a b = 0 ∧
        (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) b a = 0) :
    ∃ n : ℤ, n * n = 1 ∧ ∀ c : Kˣ,
      x * diagOmega K m (Pi.mulSingle j c) * x⁻¹ = diagOmega K m (Pi.mulSingle j c) ^ n := by
  have hcol : ∀ i, i ≠ j →
      (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (Sum.inl i) (Sum.inl j) = 0 ∧
        (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (Sum.inl i) (Sum.inr j) = 0 :=
    fun i hi => ⟨(hblk (Sum.inl j) (Sum.inl i) rfl hi).2, (hblk (Sum.inr j) (Sum.inl i) rfl hi).2⟩
  rcases plane_diag_or_antidiag_of_isometry hiso hcol with hD | hA
  · refine ⟨1, by norm_num, fun c => ?_⟩
    rw [_root_.zpow_one, (commute_diagOmega_mulSingle_of_plane hblk hD c).eq, mul_inv_cancel_right]
  · refine ⟨-1, by norm_num, fun c => ?_⟩
    rw [_root_.zpow_neg_one, mul_diagOmega_mulSingle_of_plane hblk hA c, mul_inv_cancel_right]

end Plane

section Reduction

variable {K : Type} [Field K] [Finite K] {m : ℕ}

theorem perfectCore_statedOmega_inf_centralizer_eq_of_plane (j : Fin m)
    {D D' : Set (Fin m → Kˣ)} (hDD' : D ⊆ D') (hDj : ∀ s ∈ D, s j = 1)
    (hsep : ∀ a, planeOf a ≠ j → ∃ s ∈ D, diagSpEntry s a ≠ 1)
    (hD' : ∀ t ∈ D', ∃ s ∈ D, ∃ c : Kˣ, t = s * Pi.mulSingle j c) :
    perfectCore (StatedOmega (StatedQuadPlus m K) ⊓ centralizer (diagOmega K m '' D)) =
      perfectCore (StatedOmega (StatedQuadPlus m K) ⊓ centralizer (diagOmega K m '' D')) := by
  set B := StatedOmega (StatedQuadPlus m K) ⊓ centralizer (diagOmega K m '' D) with hB
  have hblk : ∀ x ∈ B, ∀ a b, planeOf a = j → planeOf b ≠ j →
      (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a b = 0 ∧
        (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) b a = 0 := by
    intro x hx a b ha hb
    obtain ⟨s, hs, hne⟩ := hsep b hb
    have hsa : diagSpEntry s a = 1 := by
      rcases a with i | i <;> simp only [SymplecticPilot.planeOf_inl,
        SymplecticPilot.planeOf_inr] at ha <;> subst ha <;> simp [hDj s hs]
    have hc : Commute x (diagOmega K m s) :=
      ((mem_centralizer_iff.1 (mem_inf.1 hx).2) _ ⟨s, hs, rfl⟩).symm
    have hcd := (SymplecticPilot.commute_of_diag_iff
      (fun a b hab => OmegaPilot.diagOmega_apply_ne s hab) x).1 hc
    refine ⟨hcd a b ?_, hcd b a ?_⟩
    · rw [OmegaPilot.diagOmega_apply_self, OmegaPilot.diagOmega_apply_self, hsa]
      exact Ne.symm hne
    · rw [OmegaPilot.diagOmega_apply_self, OmegaPilot.diagOmega_apply_self, hsa]
      exact hne
  have hiso : ∀ x ∈ B, ∀ v, StatedQuadPlus m K
      ((x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v) = StatedQuadPlus m K v :=
    fun x hx => OmegaPilot.isometry_of_mem_isometryClosure
      ((Subgroup.commutator_le_self (OmegaPilot.isometryClosure K m)) (mem_inf.1 hx).1)
  refine LinearPilot.perfectCore_eq_of_le_of_commutator_le
    (inf_le_inf_left _ (centralizer_le (Set.image_mono hDD'))) ?_
  refine le_inf ((Subgroup.commutator_le_self B).trans inf_le_left) ?_
  rw [Subgroup.commutator_le]
  intro g hg h hh
  obtain ⟨n, hn, hgn⟩ := exists_conj_diagOmega_mulSingle_eq_zpow (hiso g hg) (hblk g hg)
  obtain ⟨n', hn', hhn⟩ := exists_conj_diagOmega_mulSingle_eq_zpow (hiso h hh) (hblk h hh)
  have hgh : ⁅g, h⁆ ∈ B :=
    Subgroup.commutator_le_self B (Subgroup.commutator_mem_commutator hg hh)
  rw [mem_centralizer_iff]
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨s, hs, c, rfl⟩ := hD' t ht
  have h1 : Commute ⁅g, h⁆ (diagOmega K m s) :=
    ((mem_centralizer_iff.1 (mem_inf.1 hgh).2) _ ⟨s, hs, rfl⟩).symm
  have h2 : Commute ⁅g, h⁆ (diagOmega K m (Pi.mulSingle j c)) :=
    commute_commutatorElement_of_conj_zpow hn hn' (hgn c) (hhn c)
  rw [map_mul]
  exact (h1.mul_right h2).eq.symm

end Reduction

end CFSG.SeitzReduction.F4Pilot
