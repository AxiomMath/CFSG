module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherRootTransport
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix SymplecticFlag CFSG.Assembly.LowTwoRank SymplecticTorusWeyl

variable {r : ℕ} {K : Type} [Field K]

@[expose] def PreservesCut (σ : Equiv.Perm (Fin r ⊕ Fin r)) (i : ℕ) : Prop :=
  ∀ x, (flagOrder r x : ℕ) < i → (flagOrder r (σ x) : ℕ) < i

theorem PreservesCut.mul {σ τ : Equiv.Perm (Fin r ⊕ Fin r)} {i : ℕ} (hσ : PreservesCut σ i)
    (hτ : PreservesCut τ i) : PreservesCut (σ * τ) i :=
  fun x hx => hσ _ (hτ x hx)

theorem PreservesCut.inv {σ : Equiv.Perm (Fin r ⊕ Fin r)} {i : ℕ} (hσ : PreservesCut σ i) :
    PreservesCut σ⁻¹ i := by
  classical
  set S := Finset.univ.filter fun x : Fin r ⊕ Fin r => (flagOrder r x : ℕ) < i
  have hsub : S.image σ ⊆ S := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hσ x hx
  have heq : S.image σ = S :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ σ.injective])
  intro x hx
  have hxS : x ∈ S := by simp [S, hx]
  rw [← heq] at hxS
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxS
  simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
  simpa [S] using hy

theorem preservesCut_one (i : ℕ) : PreservesCut (1 : Equiv.Perm (Fin r ⊕ Fin r)) i :=
  fun _ hx => hx

theorem mulVec_single_of_isLinePerm {σ : Equiv.Perm (Fin r ⊕ Fin r)}
    {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (h : IsLinePerm σ M) (x : Fin r ⊕ Fin r) :
    M *ᵥ Pi.single x 1 = M (σ x) x • Pi.single (σ x) 1 := by
  funext y
  rw [mulVec_single_one, col_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hy : y = σ x
  · rw [hy, ite_eq_left rfl, mul_one]
  · rw [h.apply_eq_zero hy, ite_eq_right hy, mul_zero]

theorem preservesCut_of_mem_stabilizer {g : StatedSp r K} {σ : Equiv.Perm (Fin r ⊕ Fin r)}
    (h : IsLinePerm σ ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    {i : ℕ} (hg : g ∈ stabilizer r K (flag r K i)) : PreservesCut σ i := by
  intro x hx
  have hex : (Pi.single x (1 : K) : Fin r ⊕ Fin r → K) ∈ flag r K i := by
    rw [flag_eq_span]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  have hmem : ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
      Pi.single x 1 ∈ flag r K i := by
    rw [← mem_stabilizer.mp hg]
    exact ⟨_, hex, rfl⟩
  rw [mulVec_single_of_isLinePerm h] at hmem
  by_contra hge
  have := mem_flag_iff.mp hmem (σ x) (not_lt.mp hge)
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at this
  exact h.apply_ne_zero x this

theorem mem_stabilizer_of_preservesCut {g : StatedSp r K} {σ : Equiv.Perm (Fin r ⊕ Fin r)}
    (h : IsLinePerm σ ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    {i : ℕ} (hσ : PreservesCut σ i) : g ∈ stabilizer r K (flag r K i) := by
  have key : ∀ {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {τ : Equiv.Perm (Fin r ⊕ Fin r)},
      IsLinePerm τ M → PreservesCut τ i → ∀ v ∈ flag r K i, M *ᵥ v ∈ flag r K i := by
    intro M τ hM hτ v hv
    rw [flag_eq_span] at hv ⊢
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      rw [mulVec_single_of_isLinePerm hM]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨τ x, hτ x hx, rfl⟩)
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [mulVec_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mulVec_smul]; exact Submodule.smul_mem _ _ hy
  refine mem_stabilizer_of_mulVec_mem (key h hσ) (key ?_ hσ.inv)
  rw [Subgroup.coe_inv]
  exact h.inv

theorem mem_stabilizer_iff_preservesCut {g : StatedSp r K} {σ : Equiv.Perm (Fin r ⊕ Fin r)}
    (h : IsLinePerm σ ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (i : ℕ) : g ∈ stabilizer r K (flag r K i) ↔ PreservesCut σ i :=
  ⟨preservesCut_of_mem_stabilizer h, mem_stabilizer_of_preservesCut h⟩

theorem simpleRefl_preservesCut {k : Fin r} {i : ℕ} (hi : i ≤ r) (hik : i ≠ (k : ℕ) + 1) :
    PreservesCut (simpleRefl r k) i := by
  intro x hx
  obtain ⟨j, rfl, hj⟩ := exists_inl_of_flagOrder_lt hi hx
  unfold simpleRefl
  split_ifs with h
  · rw [Equiv.sumCongr_apply, Sum.map_inl, flagOrder_inl, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · have : (j : ℕ) = k := by rw [h1]
      show (k : ℕ) + 1 < i
      omega
    · have : (j : ℕ) = k + 1 := by rw [h2]
      omega
    · exact hj
  · have hjk : Sum.inl j ≠ (Sum.inl k : Fin r ⊕ Fin r) := fun e => by
      rw [Sum.inl_injective e] at hj
      have := k.2
      omega
    rw [Equiv.swap_apply_of_ne_of_ne hjk Sum.inl_ne_inr, flagOrder_inl]
    exact hj

theorem not_preservesCut_simpleRefl (k : Fin r) : ¬PreservesCut (simpleRefl r k) ((k : ℕ) + 1) := by
  intro h
  have := h (Sum.inl k) (by rw [flagOrder_inl]; omega)
  rw [simpleRefl_inl] at this
  unfold simpleSnd at this
  split_ifs at this with hk
  · rw [flagOrder_inl] at this
    simp at this
  · rw [flagOrder_inr] at this
    have := k.2
    omega

theorem epsAct_inv_mem_posRoots_of_preservesCut {w : Equiv.Perm (Fin r ⊕ Fin r)}
    (hw : w ∈ signedPermGroup r) (k : Fin r) (hcut : PreservesCut w ((k : ℕ) + 1)) :
    epsAct w⁻¹ (simpleRootVec r k) ∈ posRoots r := by
  rw [← rootVec_simpleSnd, epsAct_rootVec (inv_mem hw)]
  refine rootVec_mem_posRoots ?_
  have h1 : (flagOrder r (w⁻¹ (Sum.inl k)) : ℕ) < k + 1 :=
    hcut.inv _ (by rw [flagOrder_inl]; omega)
  have h2 : k + 1 ≤ (flagOrder r (w⁻¹ (simpleSnd k)) : ℕ) := by
    by_contra hlt
    have := hcut _ (not_le.mp hlt)
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at this
    unfold simpleSnd at this
    split_ifs at this with hk
    · rw [flagOrder_inl] at this
      simp at this
    · rw [flagOrder_inr] at this
      have := k.2
      omega
  omega

variable (r) in
@[expose] def parabolicWeyl (I : Set ℕ) : Subgroup (Equiv.Perm (Fin r ⊕ Fin r)) where
  carrier := {w | w ∈ signedPermGroup r ∧ ∀ i ∈ I, PreservesCut w i}
  mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, fun i hi => (ha.2 i hi).mul (hb.2 i hi)⟩
  one_mem' := ⟨one_mem _, fun i _ => preservesCut_one i⟩
  inv_mem' := fun ha => ⟨inv_mem ha.1, fun i hi => (ha.2 i hi).inv⟩

theorem mem_closure_of_mem_parabolicWeyl {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) :
    ∀ (n : ℕ) (w : Equiv.Perm (Fin r ⊕ Fin r)), invCount w = n → w ∈ parabolicWeyl r I →
      w ∈ Subgroup.closure {s | ∃ k : Fin r, (k : ℕ) + 1 ∉ I ∧ simpleRefl r k = s} := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hn hw
  by_cases h1 : w = 1
  · rw [h1]
    exact one_mem _
  obtain ⟨k, hk⟩ : ∃ k : Fin r, epsAct w⁻¹ (simpleRootVec r k) ∈ negRoots r := by
    by_contra! hall
    refine h1 (inv_eq_one.mp (eq_one_of_forall_simple (inv_mem hw.1) fun k => ?_))
    exact (epsAct_mem_posRoots_or (inv_mem hw.1)
      (Or.inl (simpleRootVec_mem_posRoots k))).resolve_right (hall k)
  have hkI : (k : ℕ) + 1 ∉ I := fun hkI =>
    not_mem_negRoots_of_mem_posRoots
      (epsAct_inv_mem_posRoots_of_preservesCut hw.1 k (hw.2 _ hkI)) hk
  have hsk : simpleRefl r k ∈ parabolicWeyl r I :=
    ⟨simpleRefl_mem k, fun i hi => simpleRefl_preservesCut (hI i hi)
      (fun e => hkI (e ▸ hi))⟩
  have hcount := (invCount_simpleRefl_mul hw.1 k).2 hk
  have hmem := ih _ (by omega) _ rfl (mul_mem hsk hw)
  have : w = simpleRefl r k * (simpleRefl r k * w) := by
    rw [← mul_assoc, simpleRefl_mul_self, one_mul]
  rw [this]
  exact mul_mem (Subgroup.subset_closure ⟨k, hkI, rfl⟩) hmem

theorem exists_mem_closure_weylRep {I : Set ℕ} {w : Equiv.Perm (Fin r ⊕ Fin r)}
    (hw : w ∈ Subgroup.closure {s | ∃ k : Fin r, (k : ℕ) + 1 ∉ I ∧ simpleRefl r k = s}) :
    ∃ P ∈ Subgroup.closure {g : StatedSp r K | ∃ k : Fin r, (k : ℕ) + 1 ∉ I ∧ weylRep K k = g},
      IsLinePerm w ((P : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  induction hw using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨k, hk, rfl⟩ := hs
    exact ⟨weylRep K k, Subgroup.subset_closure ⟨k, hk, rfl⟩, isLinePerm_weylRep k⟩
  | one =>
    refine ⟨1, one_mem _, ?_⟩
    rw [Subgroup.coe_one, Units.val_one]
    exact isLinePerm_one
  | mul x y _ _ hx hy =>
    obtain ⟨P, hP, hPx⟩ := hx
    obtain ⟨Q, hQ, hQy⟩ := hy
    refine ⟨P * Q, mul_mem hP hQ, ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul]
    exact hPx.mul hQy
  | inv x _ hx =>
    obtain ⟨P, hP, hPx⟩ := hx
    refine ⟨P⁻¹, inv_mem hP, ?_⟩
    rw [Subgroup.coe_inv]
    exact hPx.inv

variable (r K) in
@[expose] def subflagGens (I : Set ℕ) : Set (StatedSp r K) :=
  (borelSubgroup r K : Set (StatedSp r K)) ∪
    {g | ∃ k : Fin r, (k : ℕ) + 1 ∉ I ∧ weylRep K k = g}

theorem borelSubgroup_le_flagStabilizer {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) :
    borelSubgroup r K ≤ flagStabilizer r K I := by
  intro g hg
  refine mem_flagStabilizer.mpr fun i hi => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [mem_stabilizer, flag_zero, Submodule.map_bot]
  · exact mem_borelSubgroup.mp hg i hi0 (hI i hi)

theorem subflag_generation (I : Set ℕ) (hI : ∀ i ∈ I, i ≤ r) :
    flagStabilizer r K I = Subgroup.closure (subflagGens r K I) ∧
    (∀ k : Fin r, weylRep K k ∈ flagStabilizer r K I ↔ (k : ℕ) + 1 ∉ I) ∧
    (∀ W : Submodule K (Fin r ⊕ Fin r → K), IsTotallyIsotropic (pairedSympForm K r) W →
      (flagStabilizer r K I ≤ stabilizer r K W ↔ W = flag r K 0 ∨ ∃ i ∈ I, W = flag r K i)) := by
  classical
  have hBQ := borelSubgroup_le_flagStabilizer (K := K) hI
  have hn : ∀ k : Fin r, weylRep K k ∈ flagStabilizer r K I ↔ (k : ℕ) + 1 ∉ I := by
    intro k
    constructor
    · intro hk hkI
      have := mem_flagStabilizer.mp hk _ hkI
      exact not_preservesCut_simpleRefl k ((mem_stabilizer_iff_preservesCut
        (isLinePerm_weylRep k) _).mp this)
    · intro hkI
      refine mem_flagStabilizer.mpr fun i hi => ?_
      exact (mem_stabilizer_iff_preservesCut (isLinePerm_weylRep k) _).mpr
        (simpleRefl_preservesCut (hI i hi) (fun e => hkI (e ▸ hi)))
  have hgen : flagStabilizer r K I = Subgroup.closure (subflagGens r K I) := by
    refine le_antisymm (fun g hg => ?_) ((Subgroup.closure_le _).mpr ?_)
    · obtain ⟨w, hw⟩ := (symplectic_bruhat (K := K)).1 g
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hw
      have hwQ : dotW K w ∈ flagStabilizer r K I := by
        have := mul_mem (mul_mem (inv_mem (hBQ hb₁)) hg) (inv_mem (hBQ hb₂))
        convert this using 1
        group
      have hwI : (w : Equiv.Perm (Fin r ⊕ Fin r)) ∈ parabolicWeyl r I :=
        ⟨w.2, fun i hi => (mem_stabilizer_iff_preservesCut (isLinePerm_dotW w) i).mp
          (mem_flagStabilizer.mp hwQ i hi)⟩
      obtain ⟨P, hP, hPw⟩ := exists_mem_closure_weylRep (K := K)
        (mem_closure_of_mem_parabolicWeyl hI _ _ rfl hwI)
      obtain ⟨t, ht, hPt⟩ := exists_torus_of_isLinePerm hPw
      have hsub : Subgroup.closure {g : StatedSp r K | ∃ k : Fin r, (k : ℕ) + 1 ∉ I ∧
          weylRep K k = g} ≤ Subgroup.closure (subflagGens r K I) :=
        Subgroup.closure_mono fun x hx => Or.inr hx
      have hB : ∀ b ∈ borelSubgroup r K, b ∈ Subgroup.closure (subflagGens r K I) :=
        fun b hb => Subgroup.subset_closure (Or.inl hb)
      have hdot : dotW K w = P * t⁻¹ := by rw [hPt, mul_inv_cancel_right]
      rw [hdot]
      exact mul_mem (mul_mem (hB _ hb₁) (mul_mem (hsub hP)
        (hB _ (inv_mem (torus_le_borelSubgroup ht))))) (hB _ hb₂)
    · rintro g (hg | ⟨k, hk, rfl⟩)
      · exact hBQ hg
      · exact (hn k).mpr hk
  refine ⟨hgen, hn, fun W hW => ⟨fun hQ => ?_, ?_⟩⟩
  ·
    have hU : ∀ u ∈ unipotent r K, ∀ v ∈ W,
        ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ W := by
      intro u hu v hv
      rw [← mem_stabilizer.mp (hQ (hBQ (unipotent_le_borelSubgroup hu)))]
      exact ⟨v, hv, rfl⟩
    obtain ⟨d, hd, rfl⟩ := exists_eq_isoFlag hW hU
    have hfl : isoFlag r K d = flag r K d := (Submodule.ext fun v => mem_flag_of_le hd).symm
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · exact Or.inl hfl
    · refine Or.inr ⟨d, ?_, hfl⟩
      by_contra hdI
      set k : Fin r := ⟨d - 1, by omega⟩
      have hk1 : (k : ℕ) + 1 = d := by simp [k]; omega
      have hk : weylRep K k ∈ stabilizer r K (isoFlag r K d) :=
        hQ ((hn k).mpr (by rw [hk1]; exact hdI))
      rw [hfl, mem_stabilizer_iff_preservesCut (isLinePerm_weylRep k), ← hk1] at hk
      exact not_preservesCut_simpleRefl k hk
  · rintro (rfl | ⟨i, hi, rfl⟩) g _
    · rw [mem_stabilizer, flag_zero, Submodule.map_bot]
    · exact mem_flagStabilizer.mp ‹_› i hi

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
