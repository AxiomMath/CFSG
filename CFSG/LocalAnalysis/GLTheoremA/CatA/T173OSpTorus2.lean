module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpTorus
public import CFSG.LieType.SeitzGeneration.RootPairSp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open CFSG.RankThree.Classical (spEnd spEnd_apply)
open CFSG.RankThree.PartOne.KCSpFull (spEnd_mul spEnd_one)
open CFSG.LieType.SeitzGeneration.RootPair
open CFSG.StandardType.TableBSymp

variable {F : Type} [Field F] [Finite F] [CharP F 2] {ℓ n p : ℕ}

@[expose] noncomputable def coordSpan (X : Set (Fin ℓ ⊕ Fin ℓ)) : Submodule F (Fin ℓ ⊕ Fin ℓ → F) :=
  Submodule.span F ((fun b => Pi.single b (1 : F)) '' X)

private theorem sum_smul_single (v : Fin ℓ ⊕ Fin ℓ → F) :
    (∑ b, v b • (Pi.single b (1 : F) : Fin ℓ ⊕ Fin ℓ → F)) = v := by
  rw [show (∑ b, v b • (Pi.single b (1 : F) : Fin ℓ ⊕ Fin ℓ → F)) =
      ∑ b, (Pi.single b (v b) : Fin ℓ ⊕ Fin ℓ → F) from by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Pi.single_smul (f := fun _ : Fin ℓ ⊕ Fin ℓ => F), smul_eq_mul, mul_one],
    Finset.univ_sum_single]

theorem mem_coordSpan_iff {X : Set (Fin ℓ ⊕ Fin ℓ)} {v : Fin ℓ ⊕ Fin ℓ → F} :
    v ∈ coordSpan X ↔ ∀ b ∉ X, v b = 0 := by
  let T : Submodule F (Fin ℓ ⊕ Fin ℓ → F) :=
    { carrier := {v | ∀ b ∉ X, v b = 0}
      add_mem' := fun hx hy b hb => by simp [hx b hb, hy b hb]
      zero_mem' := fun b _ => rfl
      smul_mem' := fun a x hx b hb => by simp [hx b hb] }
  constructor
  · intro hv
    have hle : coordSpan X ≤ T := by
      rw [coordSpan, Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩ c hc
      exact Pi.single_eq_of_ne (M := fun _ : Fin ℓ ⊕ Fin ℓ => F) (i := b) (i' := c)
        (fun h => hc (by rw [h]; exact hb)) 1
    exact hle hv
  · intro hv
    have h : v = ∑ b, v b • (Pi.single b (1 : F) : Fin ℓ ⊕ Fin ℓ → F) :=
      (sum_smul_single v).symm
    rw [h]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : b ∈ X
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
    · rw [hv b hb, zero_smul]; exact Submodule.zero_mem _

private theorem coordSpan_mono {X Y : Set (Fin ℓ ⊕ Fin ℓ)} (h : X ⊆ Y) :
    coordSpan (F := F) X ≤ coordSpan (F := F) Y :=
  Submodule.span_mono (Set.image_mono h)

theorem coordSpan_inter (X Y : Set (Fin ℓ ⊕ Fin ℓ)) :
    coordSpan (F := F) (X ∩ Y) = coordSpan (F := F) X ⊓ coordSpan (F := F) Y := by
  refine le_antisymm (le_inf (coordSpan_mono Set.inter_subset_left)
    (coordSpan_mono Set.inter_subset_right)) ?_
  intro v hv
  rw [Submodule.mem_inf] at hv
  rw [mem_coordSpan_iff (F := F), mem_coordSpan_iff (F := F)] at hv
  rw [mem_coordSpan_iff (F := F)]
  intro b hb
  rw [Set.mem_inter_iff, not_and_or] at hb
  rcases hb with hb | hb
  · exact hv.1 b hb
  · exact hv.2 b hb

theorem coordSpan_singleton (b : Fin ℓ ⊕ Fin ℓ) :
    coordSpan (F := F) ({b} : Set (Fin ℓ ⊕ Fin ℓ)) =
      Submodule.span F {Pi.single b (1 : F)} := by
  rw [coordSpan, Set.image_singleton]

theorem coordSpan_pair (i : Fin ℓ) :
    coordSpan (F := F) ({Sum.inl i, Sum.inr i} : Set (Fin ℓ ⊕ Fin ℓ)) = plane F i := by
  unfold coordSpan plane
  rw [Set.image_pair]

@[expose] def coordSupport (W : Submodule F (Fin ℓ ⊕ Fin ℓ → F)) : Set (Fin ℓ ⊕ Fin ℓ) :=
  {b | ∃ w ∈ W, w b ≠ 0}

theorem eq_coordSpan_coordSupport (hn : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) {W : Submodule F (Fin ℓ ⊕ Fin ℓ → F)}
    (hWV : ∀ g ∈ CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p,
      ∀ w ∈ W, spEnd g w ∈ W) :
    W = coordSpan (coordSupport W) := by
  refine le_antisymm ?_ ?_
  · intro w hw
    rw [mem_coordSpan_iff]
    intro b hb
    by_contra h
    exact hb ⟨w, hw, h⟩
  · intro v hv
    rw [mem_coordSpan_iff] at hv
    have h : v = ∑ b, v b • (Pi.single b (1 : F) : Fin ℓ ⊕ Fin ℓ → F) :=
      (sum_smul_single v).symm
    rw [h]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : b ∈ coordSupport W
    · obtain ⟨w, hw, hwb⟩ := hb
      have h1 : (Pi.single b (w b) : Fin ℓ ⊕ Fin ℓ → F) ∈ W :=
        single_mem_of_forall_symplecticQTorus hn hp hp2 hpq hWV hw b
      have h2 : (Pi.single b (w b) : Fin ℓ ⊕ Fin ℓ → F) = w b • Pi.single b (1 : F) := by
        funext c
        by_cases hc : c = b
        · subst hc; simp
        · simp [Pi.single_eq_of_ne hc]
      rw [h2] at h1
      have h3 := W.smul_mem (v b * (w b)⁻¹) h1
      rwa [smul_smul, mul_assoc, inv_mul_cancel₀ (a := w b) hwb, mul_one] at h3
    · rw [hv b hb, zero_smul]; exact Submodule.zero_mem _

open CFSG.LieType.SeitzGeneration.RootPair
open CFSG.StandardType.TableBSymp

@[expose] def IsMonomial (g : ↥(StatedSp ℓ F)) (τ : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)) : Prop :=
  ∀ b, spEnd g (Pi.single b (1 : F)) = Pi.single (τ b) (1 : F)

@[expose] def CommutesPar (τ : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)) : Prop := ∀ a, τ (par a) = par (τ a)

theorem CommutesPar.symm {τ : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)} (hτ : CommutesPar τ) :
    CommutesPar τ.symm := by
  intro a
  have h := congrArg τ.symm (hτ (τ.symm a))
  simpa using h.symm

theorem isMonomial_mul {g h : ↥(StatedSp ℓ F)} {τ σ : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)}
    (hg : IsMonomial g τ) (hh : IsMonomial h σ) : IsMonomial (g * h) (τ * σ) := by
  intro b
  rw [spEnd_mul, Module.End.mul_apply, hh, hg]
  rfl

private theorem coordSpan_map_isMonomial {g : ↥(StatedSp ℓ F)} {τ : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)}
    (hg : IsMonomial g τ) (X : Set (Fin ℓ ⊕ Fin ℓ)) :
    (coordSpan (F := F) X).map (spEnd g) = coordSpan (F := F) (τ '' X) := by
  rw [coordSpan, Submodule.map_span, coordSpan]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨τ b, ⟨b, hb, rfl⟩, (hg b).symm⟩
  · rintro ⟨b, ⟨b', hb', rfl⟩, rfl⟩
    exact ⟨Pi.single b' (1 : F), ⟨b', hb', rfl⟩, hg b'⟩

theorem commutesPar_sumCongr (σ : Equiv.Perm (Fin ℓ)) :
    CommutesPar (Equiv.Perm.sumCongr σ σ) := by
  intro a
  cases a <;> rfl

theorem commutesPar_pairSwap (i : Fin ℓ) : CommutesPar (pairSwap i) := by
  intro a
  rcases a with j | j
  · rw [par_inl]
    unfold pairSwap
    by_cases h : j = i
    · subst h
      rw [Equiv.swap_apply_right, Equiv.swap_apply_left, par_inr]
    · rw [Equiv.swap_apply_of_ne_of_ne (a := Sum.inl i) (b := Sum.inr i) Sum.inr_ne_inl
          (fun h' => h (Sum.inr_injective h')),
        Equiv.swap_apply_of_ne_of_ne (a := Sum.inl i) (b := Sum.inr i)
          (fun h' => h (Sum.inl_injective h')) Sum.inl_ne_inr, par_inl]
  · rw [par_inr]
    unfold pairSwap
    by_cases h : j = i
    · subst h
      rw [Equiv.swap_apply_left, Equiv.swap_apply_right, par_inl]
    · rw [Equiv.swap_apply_of_ne_of_ne (a := Sum.inl i) (b := Sum.inr i)
          (fun h' => h (Sum.inl_injective h')) Sum.inl_ne_inr,
        Equiv.swap_apply_of_ne_of_ne (a := Sum.inl i) (b := Sum.inr i) Sum.inr_ne_inl
          (fun h' => h (Sum.inr_injective h')), par_inr]

theorem isMonomial_permSp (σ : Equiv.Perm (Fin ℓ)) :
    IsMonomial (permSp F σ) (Equiv.Perm.sumCongr σ σ) := by
  intro b
  rw [permSp_spEnd_single]
  rfl

theorem isMonomial_spSwapSp (i : Fin ℓ) :
    IsMonomial (spSwapSp (K := F) i) (pairSwap i) :=
  spSwapSp_spEnd_single i

theorem isMonomial_kfcl_permSp {τ : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)}
    (hτ : τ ∈ CFSG.RankThree.PartOne.KFCL.Sp.Hp ℓ) :
    IsMonomial (CFSG.RankThree.PartOne.KFCL.Sp.permSp (K := F) τ hτ) τ := by
  intro b
  rw [spEnd_apply, ← mat_apply, CFSG.RankThree.PartOne.KFCL.Sp.mat_permSp,
    Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec]
  funext a
  rw [Function.comp_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : a = τ b
  · rw [if_pos h, if_pos (by rw [h]; simp)]
  · rw [if_neg h, if_neg (by intro h'; exact h (by rw [← h']; simp))]

def sAll (ℓ : ℕ) : Equiv.Perm (Fin ℓ ⊕ Fin ℓ) := Equiv.sumComm (Fin ℓ) (Fin ℓ)

theorem sAll_apply (a : Fin ℓ ⊕ Fin ℓ) : sAll ℓ a = par a := by
  cases a <;> rfl

theorem mem_Hp_sAll : sAll ℓ ∈ CFSG.RankThree.PartOne.KFCL.Sp.Hp ℓ := by
  rw [CFSG.RankThree.PartOne.KFCL.Sp.mem_Hp]
  intro a
  rw [sAll_apply, sAll_apply, par_par]

@[expose] noncomputable def sAllSp : ↥(StatedSp ℓ F) :=
  CFSG.RankThree.PartOne.KFCL.Sp.permSp (K := F) (sAll ℓ) mem_Hp_sAll

theorem isMonomial_sAllSp : IsMonomial (sAllSp (F := F) (ℓ := ℓ)) (sAll ℓ) :=
  isMonomial_kfcl_permSp (F := F) mem_Hp_sAll

theorem sAllSp_mem_normalizer (hp0 : p ≠ 0) :
    sAllSp (F := F) (ℓ := ℓ) ∈ Subgroup.normalizer
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
        Set ↥(StatedSp ℓ F)) := by
  rw [symplecticQTorus_eq_spTorus (F := F) (ℓ := ℓ) hp0]
  exact CFSG.RankThree.PartOne.KFCL.Sp.spWeyl_le_normalizer
    (CFSG.RankThree.PartOne.KFCL.Sp.mem_spWeyl_iff.mpr ⟨_, mem_Hp_sAll, rfl⟩)

theorem coordSpan_image_invariant {K : Subgroup ↥(StatedSp ℓ F)}
    {W : Submodule F (Fin ℓ ⊕ Fin ℓ → F)} {S : Set (Fin ℓ ⊕ Fin ℓ)}
    (hWK : ∀ n ∈ Subgroup.normalizer
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
          Set ↥(StatedSp ℓ F)), ∀ k ∈ K, ∀ w ∈ W, spEnd (n * k * n⁻¹) w ∈ W)
    (hW : W = coordSpan (F := F) S) {g : ↥(StatedSp ℓ F)}
    {τ : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)}
    (hgN : g ∈ Subgroup.normalizer
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
        Set ↥(StatedSp ℓ F))) (hg : IsMonomial g τ) :
    ∀ k ∈ K, ∀ w ∈ coordSpan (F := F) (τ '' S),
      spEnd k w ∈ coordSpan (F := F) (τ '' S) := by
  intro k hk w hw
  have hmap : (coordSpan (F := F) S).map (spEnd g) = coordSpan (F := F) (τ '' S) :=
    coordSpan_map_isMonomial hg S
  rw [← hmap] at hw
  rw [← hmap]
  rw [Submodule.mem_map] at hw
  rw [Submodule.mem_map]
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  refine ⟨spEnd (g⁻¹ * k * g) w₀, ?_, ?_⟩
  · have hw₀' : w₀ ∈ W := by rwa [hW]
    simpa [inv_inv, hW] using hWK g⁻¹ (inv_mem hgN) k hk w₀ hw₀' 
  · calc spEnd g (spEnd (g⁻¹ * k * g) w₀)
        = spEnd (g * (g⁻¹ * k * g)) w₀ := by rw [← Module.End.mul_apply, ← spEnd_mul]
      _ = spEnd (k * g) w₀ := by rw [show g * (g⁻¹ * k * g) = k * g by group]
      _ = spEnd k (spEnd g w₀) := by rw [spEnd_mul, Module.End.mul_apply]

theorem CommutesPar.mul {τ σ : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)} (hτ : CommutesPar τ)
    (hσ : CommutesPar σ) : CommutesPar (τ * σ) := by
  intro a
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hσ, hτ]

theorem exists_isMonomial_map_inl (hp : p.Prime) (hp2 : p ≠ 2) (hn : Nat.card F = 2 ^ n)
    (hpq : p ∣ 2 ^ n - 1) (i : Fin ℓ) (b : Fin ℓ ⊕ Fin ℓ) :
    ∃ (g : ↥(StatedSp ℓ F)) (τ : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)),
      g ∈ Subgroup.normalizer
          (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
            Set ↥(StatedSp ℓ F)) ∧
        IsMonomial g τ ∧ CommutesPar τ ∧ τ (Sum.inl i) = b := by
  rcases b with k | k
  · refine ⟨permSp F (Equiv.swap i k),
      Equiv.Perm.sumCongr (Equiv.swap i k) (Equiv.swap i k),
      permSp_mem_normalizer_symplecticQTorus hp hp2 hn hpq _, isMonomial_permSp _,
      commutesPar_sumCongr _, ?_⟩
    show Equiv.Perm.sumCongr (Equiv.swap i k) (Equiv.swap i k) (Sum.inl i) = Sum.inl k
    simp
  · refine ⟨spSwapSp (K := F) k * permSp F (Equiv.swap i k),
      pairSwap k * Equiv.Perm.sumCongr (Equiv.swap i k) (Equiv.swap i k),
      Subgroup.mul_mem _ (spSwapSp_mem_normalizer_symplecticQTorus hp hp2 hn hpq k)
        (permSp_mem_normalizer_symplecticQTorus hp hp2 hn hpq _),
      isMonomial_mul (isMonomial_spSwapSp _) (isMonomial_permSp _),
      (commutesPar_pairSwap k).mul (commutesPar_sumCongr _), ?_⟩
    show (pairSwap k * Equiv.Perm.sumCongr (Equiv.swap i k) (Equiv.swap i k)) (Sum.inl i) =
      Sum.inr k
    rw [Equiv.Perm.mul_apply]
    show pairSwap k (Equiv.Perm.sumCongr (Equiv.swap i k) (Equiv.swap i k) (Sum.inl i)) = Sum.inr k
    simp [pairSwap]

theorem exists_isMonomial_map_inr (hp : p.Prime) (hp2 : p ≠ 2) (hn : Nat.card F = 2 ^ n)
    (hpq : p ∣ 2 ^ n - 1) (i : Fin ℓ) (b : Fin ℓ ⊕ Fin ℓ) :
    ∃ (g : ↥(StatedSp ℓ F)) (τ : Equiv.Perm (Fin ℓ ⊕ Fin ℓ)),
      g ∈ Subgroup.normalizer
          (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p :
            Set ↥(StatedSp ℓ F)) ∧
        IsMonomial g τ ∧ CommutesPar τ ∧ τ (Sum.inr i) = b := by
  rcases b with k | k
  · refine ⟨spSwapSp (K := F) k * permSp F (Equiv.swap i k),
      pairSwap k * Equiv.Perm.sumCongr (Equiv.swap i k) (Equiv.swap i k),
      Subgroup.mul_mem _ (spSwapSp_mem_normalizer_symplecticQTorus hp hp2 hn hpq k)
        (permSp_mem_normalizer_symplecticQTorus hp hp2 hn hpq _),
      isMonomial_mul (isMonomial_spSwapSp _) (isMonomial_permSp _),
      (commutesPar_pairSwap k).mul (commutesPar_sumCongr _), ?_⟩
    show (pairSwap k * Equiv.Perm.sumCongr (Equiv.swap i k) (Equiv.swap i k)) (Sum.inr i) =
      Sum.inl k
    rw [Equiv.Perm.mul_apply]
    show pairSwap k (Equiv.Perm.sumCongr (Equiv.swap i k) (Equiv.swap i k) (Sum.inr i)) = Sum.inl k
    simp [pairSwap]
  · refine ⟨permSp F (Equiv.swap i k),
      Equiv.Perm.sumCongr (Equiv.swap i k) (Equiv.swap i k),
      permSp_mem_normalizer_symplecticQTorus hp hp2 hn hpq _, isMonomial_permSp _,
      commutesPar_sumCongr _, ?_⟩
    show Equiv.Perm.sumCongr (Equiv.swap i k) (Equiv.swap i k) (Sum.inr i) = Sum.inr k
    simp

theorem mul_self_sAll_pairSwap (i : Fin ℓ) :
    (sAll ℓ * pairSwap i) * (sAll ℓ * pairSwap i) = 1 := by
  ext a
  rcases a with j | j
  · by_cases hj : j = i
    · subst hj; simp [Equiv.Perm.mul_apply, sAll_apply, pairSwap]
    · have h1 : (Sum.inl j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inl i := fun h => hj (Sum.inl_injective h)
      have h2 : (Sum.inl j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inr i := Sum.inl_ne_inr
      have h3 : (Sum.inr j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inl i := Sum.inr_ne_inl
      have h4 : (Sum.inr j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inr i := fun h => hj (Sum.inr_injective h)
      simp [Equiv.Perm.mul_apply, sAll_apply, pairSwap, Equiv.swap_apply_of_ne_of_ne h1 h2,
        Equiv.swap_apply_of_ne_of_ne h3 h4]
  · by_cases hj : j = i
    · subst hj; simp [Equiv.Perm.mul_apply, sAll_apply, pairSwap]
    · have h1 : (Sum.inr j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inl i := Sum.inr_ne_inl
      have h2 : (Sum.inr j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inr i := fun h => hj (Sum.inr_injective h)
      have h3 : (Sum.inl j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inl i := fun h => hj (Sum.inl_injective h)
      have h4 : (Sum.inl j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inr i := Sum.inl_ne_inr
      simp [Equiv.Perm.mul_apply, sAll_apply, pairSwap, Equiv.swap_apply_of_ne_of_ne h1 h2,
        Equiv.swap_apply_of_ne_of_ne h3 h4]

theorem mul_self_pairSwap_sAll (i : Fin ℓ) :
    (pairSwap i * sAll ℓ) * (pairSwap i * sAll ℓ) = 1 := by
  ext a
  rcases a with j | j
  · by_cases hj : j = i
    · subst hj; simp [Equiv.Perm.mul_apply, sAll_apply, pairSwap]
    · have h1 : (Sum.inl j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inl i := fun h => hj (Sum.inl_injective h)
      have h2 : (Sum.inl j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inr i := Sum.inl_ne_inr
      have h3 : (Sum.inr j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inl i := Sum.inr_ne_inl
      have h4 : (Sum.inr j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inr i := fun h => hj (Sum.inr_injective h)
      simp [Equiv.Perm.mul_apply, sAll_apply, pairSwap, Equiv.swap_apply_of_ne_of_ne h1 h2,
        Equiv.swap_apply_of_ne_of_ne h3 h4]
  · by_cases hj : j = i
    · subst hj; simp [Equiv.Perm.mul_apply, sAll_apply, pairSwap]
    · have h1 : (Sum.inr j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inl i := Sum.inr_ne_inl
      have h2 : (Sum.inr j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inr i := fun h => hj (Sum.inr_injective h)
      have h3 : (Sum.inl j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inl i := fun h => hj (Sum.inl_injective h)
      have h4 : (Sum.inl j : Fin ℓ ⊕ Fin ℓ) ≠ Sum.inr i := Sum.inl_ne_inr
      simp [Equiv.Perm.mul_apply, sAll_apply, pairSwap, Equiv.swap_apply_of_ne_of_ne h1 h2,
        Equiv.swap_apply_of_ne_of_ne h3 h4]

theorem symm_sAll_pairSwap (i : Fin ℓ) :
    (sAll ℓ * pairSwap i).symm = sAll ℓ * pairSwap i :=
  inv_eq_of_mul_eq_one_right (mul_self_sAll_pairSwap i)

theorem symm_pairSwap_sAll (i : Fin ℓ) :
    (pairSwap i * sAll ℓ).symm = pairSwap i * sAll ℓ :=
  inv_eq_of_mul_eq_one_right (mul_self_pairSwap_sAll i)

theorem sumCongr_swap_inv (i j : Fin ℓ) :
    (Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j))⁻¹ =
      Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j) := by
  ext a
  cases a <;> simp [Equiv.swap_inv]

theorem sumCongr_swap_symm (i j : Fin ℓ) :
    (Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j)).symm =
      Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j) := by
  change (Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j))⁻¹ =
    Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.swap i j)
  exact sumCongr_swap_inv i j

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
