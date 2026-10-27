module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSubspaceCount
public import CFSG.Timmesfeld.Orders.ClassicalOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryRegular
import all CFSG.Fischer.F4
public import CFSG.LieType.Chevalley.C2E6RootRestrictionD

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.FourthResidue

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry
  QuadraticMap Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev qBin : QuadraticForm (ZMod 2) (Fin 2 → ZMod 2) := binaryForm (ZMod 2) 1 1

theorem qBin_apply (z : Fin 2 → ZMod 2) : qBin z = z 0 ^ 2 + z 0 * z 1 + z 1 ^ 2 := by
  rw [binaryForm_apply]
  ring

theorem sq_add_add_one_ne_zero : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by
  decide

theorem qBin_anisotropic : qBin.Anisotropic := by
  intro z hz
  rw [qBin_apply] at hz
  have key : ∀ a b : ZMod 2, a ^ 2 + a * b + b ^ 2 = 0 → a = 0 ∧ b = 0 := by decide
  obtain ⟨h0, h1⟩ := key _ _ hz
  funext i
  fin_cases i
  exacts [h0, h1]

theorem polar_qBin (z w : Fin 2 → ZMod 2) : polar qBin z w = z 0 * w 1 + z 1 * w 0 := by
  rw [polar, qBin_apply, qBin_apply, qBin_apply]
  have key : ∀ a b c d : ZMod 2, (a + c) ^ 2 + (a + c) * (b + d) + (b + d) ^ 2 -
      (a ^ 2 + a * b + b ^ 2) - (c ^ 2 + c * d + d ^ 2) = a * d + b * c := by decide
  exact key _ _ _ _

theorem eq_zero_of_polar_qBin {z : Fin 2 → ZMod 2} (hz : ∀ w, polar qBin z w = 0) : z = 0 := by
  have h0 := hz (Pi.single 1 1)
  have h1 := hz (Pi.single 0 1)
  rw [polar_qBin] at h0 h1
  simp at h0 h1
  funext i
  fin_cases i
  exacts [h0, h1]

theorem polarBilin_qBin_nondegenerate : (polarBilin qBin).Nondegenerate := by
  refine ⟨fun z hz => eq_zero_of_polar_qBin fun w => ?_,
    fun z hz => eq_zero_of_polar_qBin fun w => ?_⟩
  · exact hz w
  · rw [polar_comm]
    exact hz w

abbrev a₀ : Fin 2 → ZMod 2 := Pi.single 0 1

theorem a₀_ne_zero : a₀ ≠ 0 := fun h => by simpa using congrFun h 0

abbrev V0 : Type := (Fin 3 ⊕ Fin 3 → ZMod 2) × (Fin 2 → ZMod 2)

abbrev Qminus : QuadraticForm (ZMod 2) V0 := quadTail 3 qBin

theorem Qminus_apply (v : V0) :
    Qminus v = ∑ i, v.1 (.inl i) * v.1 (.inr i) + (v.2 0 ^ 2 + v.2 0 * v.2 1 + v.2 1 ^ 2) := by
  rw [show Qminus v = quadTail 3 qBin v from rfl, quadTail_apply, quadPlus_apply, qBin_apply]

instance : Finite (V0 ≃ₗ[ZMod 2] V0) :=
  Finite.of_injective (fun g : V0 ≃ₗ[ZMod 2] V0 => (g : V0 → V0)) fun _ _ h =>
    LinearEquiv.ext (congrFun h)

abbrev tVec (j : Fin 2) : V0 := (0, Pi.single j 1)

theorem castSucc_ne_three : ∀ i : Fin 3, i.castSucc ≠ (3 : Fin 4) := by
  decide

theorem three_ne_castSucc : ∀ i : Fin 3, (3 : Fin 4) ≠ i.castSucc := by
  decide

@[expose] def tailCoeff (z : Fin 2 → ZMod 2) : K :=
  algebraMap (ZMod 2) K (z 0) + algebraMap (ZMod 2) K (z 1) * ω

theorem tailCoeff_add (z z' : Fin 2 → ZMod 2) :
    tailCoeff (z + z') = tailCoeff z + tailCoeff z' := by
  simp only [tailCoeff, Pi.add_apply, map_add]
  ring

theorem tailCoeff_smul (c : ZMod 2) (z : Fin 2 → ZMod 2) :
    tailCoeff (c • z) = c • tailCoeff z := by
  simp only [tailCoeff, Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]
  ring

theorem tailCoeff_eq_zero_iff (z : Fin 2 → ZMod 2) : tailCoeff z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h0 := t0_coe_add_mul_omega (z 0) (z 1)
    have h1 := t1_coe_add_mul_omega (z 0) (z 1)
    rw [← tailCoeff, h] at h0 h1
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
  · rintro rfl
    simp [tailCoeff]

theorem tailCoeff_mul_bar (z : Fin 2 → ZMod 2) :
    tailCoeff z * bar (tailCoeff z) = algebraMap (ZMod 2) K (qBin z) := by
  rw [qBin_apply, tailCoeff]
  generalize z 0 = a
  generalize z 1 = b
  revert a b
  decide

theorem bar_tailCoeff (z : Fin 2 → ZMod 2) :
    bar (tailCoeff z) = tailCoeff ![z 0 + z 1, z 1] := by
  simp only [tailCoeff, Matrix.cons_val_zero, Matrix.cons_val_one]
  generalize z 0 = a
  generalize z 1 = b
  revert a b
  decide

@[expose] def embedFun (v : V0) : Fin 4 ⊕ Fin 4 → K :=
  Sum.elim (Fin.snoc (α := fun _ => K) (fun i : Fin 3 => algebraMap (ZMod 2) K (v.1 (.inl i)))
      (tailCoeff v.2))
    (Fin.snoc (α := fun _ => K) (fun i : Fin 3 => algebraMap (ZMod 2) K (v.1 (.inr i)))
      (bar (tailCoeff v.2)))

theorem embedFun_inl_castSucc (v : V0) (i : Fin 3) :
    embedFun v (.inl i.castSucc) = algebraMap (ZMod 2) K (v.1 (.inl i)) := by
  simp [embedFun]

theorem embedFun_inr_castSucc (v : V0) (i : Fin 3) :
    embedFun v (.inr i.castSucc) = algebraMap (ZMod 2) K (v.1 (.inr i)) := by
  simp [embedFun]

theorem embedFun_inl_last (v : V0) : embedFun v (.inl (Fin.last 3)) = tailCoeff v.2 := by
  simp only [embedFun, Sum.elim_inl, Fin.snoc_last]

theorem embedFun_inr_last (v : V0) : embedFun v (.inr (Fin.last 3)) = bar (tailCoeff v.2) := by
  simp only [embedFun, Sum.elim_inr, Fin.snoc_last]

@[expose] def embed : V0 →ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → K) where
  toFun := embedFun
  map_add' v w := by
    funext c
    rcases c with i | i <;> induction i using Fin.lastCases
    · simp only [embedFun_inl_last, Pi.add_apply, Prod.snd_add, tailCoeff_add]
    · simp only [embedFun_inl_castSucc, Pi.add_apply, Prod.fst_add, map_add]
    · simp only [embedFun_inr_last, Pi.add_apply, Prod.snd_add, tailCoeff_add, bar_add]
    · simp only [embedFun_inr_castSucc, Pi.add_apply, Prod.fst_add, map_add]
  map_smul' c v := by
    funext x
    rcases x with i | i <;> induction i using Fin.lastCases
    · rw [Pi.smul_apply, embedFun_inl_last, embedFun_inl_last, Prod.smul_snd, tailCoeff_smul,
        RingHom.id_apply]
    · rw [Pi.smul_apply, embedFun_inl_castSucc, embedFun_inl_castSucc, Prod.smul_fst,
        Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def]
    · rw [Pi.smul_apply, embedFun_inr_last, embedFun_inr_last, Prod.smul_snd, tailCoeff_smul,
        RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, bar_mul, bar_coe]
    · rw [Pi.smul_apply, embedFun_inr_castSucc, embedFun_inr_castSucc, Prod.smul_fst,
        Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def]

theorem embed_inl_castSucc (v : V0) (i : Fin 3) :
    embed v (.inl i.castSucc) = algebraMap (ZMod 2) K (v.1 (.inl i)) :=
  embedFun_inl_castSucc v i

theorem embed_inr_castSucc (v : V0) (i : Fin 3) :
    embed v (.inr i.castSucc) = algebraMap (ZMod 2) K (v.1 (.inr i)) :=
  embedFun_inr_castSucc v i

theorem embed_inl_last (v : V0) : embed v (.inl (Fin.last 3)) = tailCoeff v.2 :=
  embedFun_inl_last v

theorem embed_inr_last (v : V0) : embed v (.inr (Fin.last 3)) = bar (tailCoeff v.2) :=
  embedFun_inr_last v

@[expose] def coords : (Fin 4 ⊕ Fin 4 → K) →ₗ[ZMod 2] V0 where
  toFun w := (fun c => t0 (w (Sum.map Fin.castSucc Fin.castSucc c)),
    ![t0 (w (.inl (Fin.last 3))), t1 (w (.inl (Fin.last 3)))])
  map_add' w w' := by
    refine Prod.ext (funext fun c => t0_add _ _) (funext fun i => ?_)
    fin_cases i
    · exact t0_add _ _
    · exact t1_add _ _
  map_smul' c w := by
    refine Prod.ext (funext fun x => t0_smul _ _) (funext fun i => ?_)
    fin_cases i
    · exact t0_smul _ _
    · exact t1_smul _ _

theorem coords_embed (v : V0) : coords (embed v) = v := by
  refine Prod.ext (funext fun c => ?_) (funext fun i => ?_)
  · rcases c with i | i
    · exact (congrArg t0 (embed_inl_castSucc v i)).trans (t0_coe _)
    · exact (congrArg t0 (embed_inr_castSucc v i)).trans (t0_coe _)
  · fin_cases i
    · exact (congrArg t0 (embed_inl_last v)).trans (t0_coe_add_mul_omega _ _)
    · exact (congrArg t1 (embed_inl_last v)).trans (t1_coe_add_mul_omega _ _)

theorem embed_injective : Function.Injective embed :=
  Function.LeftInverse.injective coords_embed

theorem eq_sum_hypVec_tVec (v : V0) :
    v = ∑ c, v.1 c • hypVec (ZMod 2) (Fin 2 → ZMod 2) c + v.2 0 • tVec 0 + v.2 1 • tVec 1 := by
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, hypVec, tVec, smul_zero, add_zero]
    conv_lhs => rw [← Finset.univ_sum_single v.1]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, hypVec, tVec, smul_zero,
      Finset.sum_const_zero, zero_add]
    funext i
    fin_cases i <;> simp

theorem embed_eq_sum (v : V0) :
    embed v = ∑ c, v.1 c • embed (hypVec (ZMod 2) (Fin 2 → ZMod 2) c) + v.2 0 • embed (tVec 0) +
      v.2 1 • embed (tVec 1) := by
  conv_lhs => rw [eq_sum_hypVec_tVec v]
  simp only [map_add, map_sum, map_smul]

theorem quadPlus_embed (v : V0) :
    quadPlus 4 K (embed v) = algebraMap (ZMod 2) K (Qminus v) := by
  rw [quadPlus_apply, Fin.sum_univ_castSucc, show Qminus v = quadTail 3 qBin v from rfl,
    quadTail_apply, quadPlus_apply, map_add, map_sum, embed_inl_last, embed_inr_last,
    tailCoeff_mul_bar]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [embed_inl_castSucc, embed_inr_castSucc, map_mul]

theorem embed_hypVec (c : Fin 3 ⊕ Fin 3) :
    embed (hypVec (ZMod 2) (Fin 2 → ZMod 2) c) =
      Pi.single (Sum.map Fin.castSucc Fin.castSucc c) 1 := by
  funext d
  rcases d with j | j <;> induction j using Fin.lastCases with
  | last =>
    first
    | rw [embed_inl_last]
    | rw [embed_inr_last]
    rcases c with i | i <;> simp [hypVec, tailCoeff, bar_zero, three_ne_castSucc]
  | cast j =>
    first
    | rw [embed_inl_castSucc]
    | rw [embed_inr_castSucc]
    rcases c with i | i <;> simp [hypVec, Pi.single_apply, Fin.castSucc_inj]

theorem embed_tVec_zero :
    embed (tVec 0) = Pi.single (.inl (Fin.last 3)) 1 + Pi.single (.inr (Fin.last 3)) 1 := by
  funext d
  rcases d with j | j <;> induction j using Fin.lastCases with
  | last =>
    first
    | rw [embed_inl_last]
    | rw [embed_inr_last]
    simp [tailCoeff, bar_one]
  | cast j =>
    first
    | rw [embed_inl_castSucc]
    | rw [embed_inr_castSucc]
    simp [castSucc_ne_three]

theorem embed_tVec_one :
    embed (tVec 1) =
      ω • Pi.single (.inl (Fin.last 3)) 1 + ω ^ 2 • Pi.single (.inr (Fin.last 3)) 1 := by
  funext d
  rcases d with j | j <;> induction j using Fin.lastCases with
  | last =>
    first
    | rw [embed_inl_last]
    | rw [embed_inr_last]
    simp [tailCoeff, bar]
  | cast j =>
    first
    | rw [embed_inl_castSucc]
    | rw [embed_inr_castSucc]
    simp [castSucc_ne_three]

@[expose] def frob8 (w : Fin 4 ⊕ Fin 4 → K) : Fin 4 ⊕ Fin 4 → K := fun c => bar (w c)

theorem frob8_frob8 (w : Fin 4 ⊕ Fin 4 → K) : frob8 (frob8 w) = w :=
  funext fun c => bar_bar (w c)

theorem swapE4F4_apply (w : Fin 4 ⊕ Fin 4 → K) (c : Fin 4 ⊕ Fin 4) :
    swapE4F4 w c = w (Equiv.swap (.inl 3) (.inr 3) c) :=
  rfl

theorem swap_inl_castSucc (i : Fin 3) :
    Equiv.swap (Sum.inl 3 : Fin 4 ⊕ Fin 4) (.inr 3) (.inl i.castSucc) = .inl i.castSucc :=
  Equiv.swap_apply_of_ne_of_ne (by simp [castSucc_ne_three]) (by simp)

theorem swap_inr_castSucc (i : Fin 3) :
    Equiv.swap (Sum.inl 3 : Fin 4 ⊕ Fin 4) (.inr 3) (.inr i.castSucc) = .inr i.castSucc :=
  Equiv.swap_apply_of_ne_of_ne (by simp) (by simp [castSucc_ne_three])

theorem swap_inl_last :
    Equiv.swap (Sum.inl 3 : Fin 4 ⊕ Fin 4) (.inr 3) (.inl (Fin.last 3)) = .inr (Fin.last 3) :=
  Equiv.swap_apply_left _ _

theorem swap_inr_last :
    Equiv.swap (Sum.inl 3 : Fin 4 ⊕ Fin 4) (.inr 3) (.inr (Fin.last 3)) = .inl (Fin.last 3) :=
  Equiv.swap_apply_right _ _

theorem swapE4F4_frob8_embed (v : V0) : swapE4F4 (frob8 (embed v)) = embed v := by
  funext c
  rw [swapE4F4_apply]
  rcases c with i | i <;> induction i using Fin.lastCases with
  | last =>
    first
    | rw [swap_inl_last, frob8, embed_inl_last, embed_inr_last, bar_bar]
    | rw [swap_inr_last, frob8, embed_inl_last, embed_inr_last]
  | cast i =>
    first
    | rw [swap_inl_castSucc, frob8, embed_inl_castSucc, bar_coe]
    | rw [swap_inr_castSucc, frob8, embed_inr_castSucc, bar_coe]

theorem embed_coords {w : Fin 4 ⊕ Fin 4 → K} (hw : swapE4F4 (frob8 w) = w) :
    embed (coords w) = w := by
  have h := fun c => congrFun hw c
  funext c
  rcases c with i | i <;> induction i using Fin.lastCases with
  | last =>
    first
    | rw [embed_inl_last]
      exact t0_add_t1_omega _
    | rw [embed_inr_last]
      have h1 := h (.inr (Fin.last 3))
      rw [swapE4F4_apply, swap_inr_last] at h1
      rw [← h1]
      exact congrArg bar (t0_add_t1_omega _)
  | cast i =>
    first
    | rw [embed_inl_castSucc]
      have h1 := h (.inl i.castSucc)
      rw [swapE4F4_apply, swap_inl_castSucc] at h1
      exact coe_t0_of_bar_eq _ h1
    | rw [embed_inr_castSucc]
      have h1 := h (.inr i.castSucc)
      rw [swapE4F4_apply, swap_inr_castSucc] at h1
      exact coe_t0_of_bar_eq _ h1

theorem mem_range_embed_iff (w : Fin 4 ⊕ Fin 4 → K) :
    w ∈ Set.range embed ↔ swapE4F4 (frob8 w) = w := by
  constructor
  · rintro ⟨v, rfl⟩
    exact swapE4F4_frob8_embed v
  · intro hw
    exact ⟨coords w, embed_coords hw⟩

theorem mem_range_embed_iff' (w : Fin 4 ⊕ Fin 4 → K) :
    w ∈ Set.range embed ↔
      (∀ i : Fin 3, w (.inl i.castSucc) ∈ Set.range (algebraMap (ZMod 2) K) ∧
        w (.inr i.castSucc) ∈ Set.range (algebraMap (ZMod 2) K)) ∧
      w (.inr (Fin.last 3)) = w (.inl (Fin.last 3)) ^ 2 := by
  rw [mem_range_embed_iff]
  constructor
  · intro hw
    have h := fun c => congrFun hw c
    refine ⟨fun i => ⟨⟨t0 (w (.inl i.castSucc)), ?_⟩, ⟨t0 (w (.inr i.castSucc)), ?_⟩⟩, ?_⟩
    · have h1 := h (.inl i.castSucc)
      rw [swapE4F4_apply, swap_inl_castSucc] at h1
      exact coe_t0_of_bar_eq _ h1
    · have h1 := h (.inr i.castSucc)
      rw [swapE4F4_apply, swap_inr_castSucc] at h1
      exact coe_t0_of_bar_eq _ h1
    · have h1 := h (.inr (Fin.last 3))
      rw [swapE4F4_apply, swap_inr_last] at h1
      exact h1.symm
  · rintro ⟨hhyp, htail⟩
    funext c
    rw [swapE4F4_apply]
    rcases c with i | i <;> induction i using Fin.lastCases with
    | last =>
      first
      | rw [swap_inl_last, frob8, htail]
        exact bar_bar _
      | rw [swap_inr_last, frob8, htail]
        rfl
    | cast i =>
      first
      | rw [swap_inl_castSucc, frob8]
        obtain ⟨x, hx⟩ := (hhyp i).1
        rw [← hx, bar_coe]
      | rw [swap_inr_castSucc, frob8]
        obtain ⟨x, hx⟩ := (hhyp i).2
        rw [← hx, bar_coe]

theorem omega_sq_add_omega : ω ^ 2 + ω = 1 := by
  decide

theorem single_inl_last_eq :
    (Pi.single (.inl (Fin.last 3)) 1 : Fin 4 ⊕ Fin 4 → K) =
      ω ^ 2 • embed (tVec 0) + embed (tVec 1) := by
  rw [embed_tVec_zero, embed_tVec_one, smul_add, add_add_add_comm, ← add_smul, ← add_smul,
    omega_sq_add_omega, one_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

theorem span_range_embed : Submodule.span K (Set.range embed) = ⊤ := by
  have hsingle : ∀ c, (Pi.single c 1 : Fin 4 ⊕ Fin 4 → K) ∈ Submodule.span K (Set.range embed) := by
    have hmem : ∀ v, embed v ∈ Submodule.span K (Set.range embed) := fun v =>
      Submodule.subset_span ⟨v, rfl⟩
    have he : (Pi.single (.inl (Fin.last 3)) 1 : Fin 4 ⊕ Fin 4 → K) ∈
        Submodule.span K (Set.range embed) := by
      rw [single_inl_last_eq]
      exact add_mem (Submodule.smul_mem _ _ (hmem _)) (hmem _)
    intro c
    rcases c with i | i <;> induction i using Fin.lastCases with
    | last =>
      first
      | exact he
      | have e : (Pi.single (.inr (Fin.last 3)) 1 : Fin 4 ⊕ Fin 4 → K) =
            embed (tVec 0) - Pi.single (.inl (Fin.last 3)) 1 := by
          rw [embed_tVec_zero, add_sub_cancel_left]
        rw [e]
        exact sub_mem (hmem _) he
    | cast i =>
      first
      | have e := embed_hypVec (.inl i)
        rw [Sum.map_inl] at e
        rw [← e]
        exact hmem _
      | have e := embed_hypVec (.inr i)
        rw [Sum.map_inr] at e
        rw [← e]
        exact hmem _
  refine eq_top_iff.mpr ?_
  rw [← (Pi.basisFun K (Fin 4 ⊕ Fin 4)).span_eq, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  rw [Pi.basisFun_apply]
  exact hsingle c

theorem linearMap_ext_embed {f g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (h : ∀ v, f (embed v) = g (embed v)) : f = g :=
  LinearMap.ext_on_range span_range_embed h

theorem embed_mem_flag_iff {k : ℕ} (hk : k ≤ 3) (v : V0) :
    embed v ∈ flag 4 K k ↔ v ∈ tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 k := by
  rw [mem_flag, mem_tailFlag_iff, mem_flag]
  have hinj : ∀ x : ZMod 2, algebraMap (ZMod 2) K x = 0 ↔ x = 0 := fun x =>
    (algebraMap (ZMod 2) K).injective.eq_iff' (map_zero _)
  constructor
  · rintro ⟨h1, h2⟩
    have hz : v.2 = 0 := by
      rw [← tailCoeff_eq_zero_iff, ← embed_inl_last]
      exact h2 (Fin.last 3) (by simpa using hk)
    refine ⟨⟨fun j => ?_, fun j hj => ?_⟩, hz⟩
    · have := h1 j.castSucc
      rwa [embed_inr_castSucc, hinj] at this
    · have := h2 j.castSucc (by simpa using hj)
      rwa [embed_inl_castSucc, hinj] at this
  · rintro ⟨⟨h1, h2⟩, hz⟩
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · induction j using Fin.lastCases with
      | last => rw [embed_inr_last, hz, (tailCoeff_eq_zero_iff 0).mpr rfl, bar_zero]
      | cast j => rw [embed_inr_castSucc, h1 j, map_zero]
    · induction j using Fin.lastCases with
      | last => rw [embed_inl_last, hz, (tailCoeff_eq_zero_iff 0).mpr rfl]
      | cast j => rw [embed_inl_castSucc, h2 j (by simpa using hj), map_zero]

theorem Qminus_tVec_zero : Qminus (tVec 0) = 1 := by
  rw [Qminus_apply]
  simp

@[expose] def sMinus : V0 ≃ₗ[ZMod 2] V0 := reflect Qminus (tVec 0)

theorem polar_tVec_zero (v : V0) : polar Qminus (tVec 0) v = v.2 1 := by
  rw [show polar Qminus (tVec 0) v = polar (quadTail 3 qBin) (tVec 0) v from rfl, polar_quadTail,
    polar_zero_left, zero_add, polar_qBin]
  simp

theorem sMinus_apply (v : V0) : sMinus v = (v.1, ![v.2 0 + v.2 1, v.2 1]) := by
  rw [sMinus, reflect_apply (by rw [Qminus_tVec_zero]; exact one_ne_zero), Qminus_tVec_zero,
    polar_tVec_zero, div_one]
  refine Prod.ext ?_ (funext fun i => ?_)
  · simp
  · fin_cases i
    · simp [CharTwo.sub_eq_add]
    · simp

theorem sMinus_hypVec (c : Fin 3 ⊕ Fin 3) :
    sMinus (hypVec (ZMod 2) (Fin 2 → ZMod 2) c) = hypVec (ZMod 2) (Fin 2 → ZMod 2) c := by
  rw [sMinus_apply]
  refine Prod.ext rfl (funext fun i => ?_)
  fin_cases i <;> simp [hypVec]

theorem sMinus_tVec_zero : sMinus (tVec 0) = tVec 0 := by
  rw [sMinus_apply]
  refine Prod.ext rfl (funext fun i => ?_)
  fin_cases i <;> simp

theorem sMinus_tVec_one : sMinus (tVec 1) = tVec 0 + tVec 1 := by
  rw [sMinus_apply]
  refine Prod.ext (by simp) (funext fun i => ?_)
  fin_cases i <;> simp

theorem sMinus_mem_orthogonalGroup : sMinus ∈ TauCeti.QuadraticMap.orthogonalGroup Qminus :=
  reflect_mem_orthogonalGroup Qminus (tVec 0)

theorem sMinus_mul_self : sMinus * sMinus = 1 :=
  reflect_mul_self Qminus (tVec 0)

theorem sMinus_ne_one : sMinus ≠ 1 := by
  intro h
  have := congrArg (· (tVec 1)) h
  simp only [sMinus_tVec_one] at this
  have h2 := congrArg (fun v : V0 => v.2 0) this
  simp at h2

theorem frob8_embed (v : V0) : frob8 (embed v) = embed (sMinus v) := by
  funext c
  rw [frob8]
  rcases c with i | i <;> induction i using Fin.lastCases with
  | last =>
    first
    | rw [embed_inl_last, embed_inl_last, sMinus_apply, bar_tailCoeff]
    | rw [embed_inr_last, embed_inr_last, sMinus_apply, bar_tailCoeff]
  | cast i =>
    first
    | rw [embed_inl_castSucc, embed_inl_castSucc, sMinus_apply, bar_coe]
    | rw [embed_inr_castSucc, embed_inr_castSucc, sMinus_apply, bar_coe]

@[expose] def eMinus : (quadMinus 4 (ZMod 2) 1 1).IsometryEquiv Qminus :=
  quadMinusIsometry 4 (ZMod 2) 1 1

theorem regular_Qminus : (polarBilin Qminus).Nondegenerate ∧
    ∃ T : Submodule (ZMod 2) V0, finrank (ZMod 2) T = 3 ∧ ∀ x ∈ T, Qminus x = 0 :=
  ⟨polar_nondegenerate_isometry eMinus
      (regular_quadMinus (n := 4) (by norm_num) sq_add_add_one_ne_zero).1,
    singular_three_isometry eMinus
      (regular_quadMinus (n := 4) (by norm_num) sq_add_add_one_ne_zero).2⟩

theorem commutator_orthogonalGroup_Qminus :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Qminus, TauCeti.QuadraticMap.orthogonalGroup Qminus⁆ =
      orthElementaryGroup Qminus :=
  derived_eq_elementary_isometry eMinus
    (commutator_orthogonalGroup_quadMinus (n := 4) (by norm_num) sq_add_add_one_ne_zero)

theorem card_orthogonalGroup_Qminus :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Qminus) = 394813440 := by
  rw [← CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr eMinus]
  have h := (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus (K := ZMod 2) 3
    sq_add_add_one_ne_zero).2
  rw [Nat.card_zmod] at h
  have e : (2 : ℤ) * ((2 : ℕ) : ℤ) ^ (3 * (3 + 1)) * (((2 : ℕ) : ℤ) ^ (3 + 1) + 1) *
      ∏ i ∈ Finset.Icc 1 3, (((2 : ℕ) : ℤ) ^ (2 * i) - 1) = 394813440 := by
    decide
  rw [e] at h
  exact_mod_cast h

theorem card_elementaryGroup_Qminus : Nat.card (orthElementaryGroup Qminus) = 197406720 := by
  rw [orthElementaryGroup, ← Nat.card_congr (elementaryIsometryEquiv eMinus).toEquiv]
  have h := CFSG.Timmesfeld.ClassicalOrders.card_elementaryGroup_quadMinus (n := 4)
    (K := ZMod 2) (by norm_num) sq_add_add_one_ne_zero
  rw [Nat.card_zmod] at h
  have e : ((2 : ℕ) : ℤ) ^ (4 * (4 - 1)) * (((2 : ℕ) : ℤ) ^ 4 + 1) *
      ∏ i ∈ Finset.Icc 1 (4 - 1), (((2 : ℕ) : ℤ) ^ (2 * i) - 1) = 197406720 := by
    decide
  rw [e] at h
  exact_mod_cast h

theorem card_singularFlags_Qminus : Nat.card (singularFlags Qminus 3) = 16065 := by
  have h := (orthogonal_geometry_tail_singular_subspace_count (r := 3) (by norm_num)
    qBin_anisotropic polarBilin_qBin_nondegenerate (k := 3) le_rfl).2.1
  rw [Nat.card_zmod, Module.finrank_fin_fun] at h
  have e : ∏ j ∈ Finset.range 3, (((2 : ℕ) : ℚ) ^ (3 - j) - 1) *
      (((2 : ℕ) : ℚ) ^ (3 + 2 - j - 1) + 1) / (((2 : ℕ) : ℚ) - 1) = 16065 := by
    norm_num [Finset.prod_range_succ]
  rw [e] at h
  exact_mod_cast h

theorem sMinus_not_mem_elementaryGroup : sMinus ∉ orthElementaryGroup Qminus :=
  (orthogonal_geometry_char_two_reflection_separation regular_Qminus.1
    regular_Qminus.2).choose_spec.2.2 (tVec 0) (by rw [Qminus_tVec_zero]; exact one_ne_zero)

abbrev elemO : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Qminus) :=
  (orthElementaryGroup Qminus).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Qminus)

abbrev sO : TauCeti.QuadraticMap.orthogonalGroup Qminus := ⟨sMinus, sMinus_mem_orthogonalGroup⟩

theorem card_elemO : Nat.card elemO = 197406720 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (orthElementaryGroup_le Qminus)).toEquiv,
    card_elementaryGroup_Qminus]

theorem index_elemO : elemO.index = 2 := by
  have h := elemO.card_mul_index
  rw [card_elemO, card_orthogonalGroup_Qminus] at h
  omega

instance : elemO.Normal :=
  Subgroup.normal_of_index_eq_two index_elemO

theorem orderOf_sO : orderOf sO = 2 :=
  orderOf_eq_prime (Subtype.ext (by rw [pow_two]; exact sMinus_mul_self))
    fun h => sMinus_ne_one (congrArg Subtype.val h)

theorem isComplement'_elemO : elemO.IsComplement' (Subgroup.zpowers sO) := by
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
  · rw [card_elemO, Nat.card_zpowers, orderOf_sO, card_orthogonalGroup_Qminus]
  · rw [Subgroup.disjoint_def]
    intro x hx hxs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxs
    rw [← zpow_mod_orderOf, orderOf_sO] at hx ⊢
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [Nat.cast_ofNat, h, zpow_zero]
    · rw [Nat.cast_ofNat, h, zpow_one] at hx
      exact absurd hx sMinus_not_mem_elementaryGroup

@[expose] noncomputable def semidirectEquiv :
    elemO ⋊[(elemO.normalizerMonoidHom).comp
      (Subgroup.inclusion (elemO.normalizer_eq_top ▸ le_top))] Subgroup.zpowers sO ≃*
        TauCeti.QuadraticMap.orthogonalGroup Qminus :=
  SemidirectProduct.mulEquivSubgroup isComplement'_elemO

theorem semidirectEquiv_apply (x : elemO ⋊[(elemO.normalizerMonoidHom).comp
      (Subgroup.inclusion (elemO.normalizer_eq_top ▸ le_top))] Subgroup.zpowers sO) :
    semidirectEquiv x = x.left * x.right :=
  SemidirectProduct.mulEquivSubgroup_apply _ x

end CFSG.LieType.Chevalley.C2E6Std.FourthResidue
