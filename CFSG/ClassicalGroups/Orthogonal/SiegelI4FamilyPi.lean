module

public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Pair
public import CFSG.ClassicalGroups.Orthogonal.RootGroupCard
public import CFSG.HardMathSupport.Kantor79.SiegelEichler

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.HardMathSupport.Kantor79 CFSG.HardMathSupport.GuralnickMalle QuadraticMap Module

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  {Qf : QuadraticForm K V}

@[expose] def piGroup (Qf : QuadraticForm K V) (P W : Submodule K V) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure {s | IsLongRootElement Qf s ∧ P ≤ movedSpace s ∧ movedSpace s ≤ W}

theorem piGroup_mono {P P' W W' : Submodule K V} (hP : P' ≤ P) (hW : W ≤ W') :
    piGroup Qf P W ≤ piGroup Qf P' W' :=
  Subgroup.closure_mono fun _ h => ⟨h.1, hP.trans h.2.1, h.2.2.trans hW⟩

theorem isLongRootElement_mem_piGroup {P W : Submodule K V} {s : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) (hP : P ≤ movedSpace s) (hW : movedSpace s ≤ W) :
    s ∈ piGroup Qf P W :=
  Subgroup.subset_closure ⟨hs, hP, hW⟩

theorem eichler_apply_of_qf_eq_zero {p w : V} (hp : Qf p = 0) (hpw : polar Qf p w = 0)
    (hw : Qf w = 0) (x : V) :
    eichler Qf p w x = x + polar Qf x p • w + polar Qf x w • p := by
  rw [eichler_apply hp hpw, hw, zero_mul, add_zero, sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]

theorem eichler_eq_one_of_mem_span {p w : V} (hp : Qf p = 0)
    (hw : w ∈ Submodule.span K ({p} : Set V)) : eichler Qf p w = 1 := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  have h := eichler_add_smul_self hp (0 : V) c
  rwa [zero_add, eichler_zero_right] at h

theorem isLongRootElement_eichler (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {p w : V}
    (hp : Qf p = 0) (hw : Qf w = 0) (hpw : polar Qf p w = 0) (hp0 : p ≠ 0)
    (hwp : w ∉ Submodule.span K ({p} : Set V)) :
    IsLongRootElement Qf (eichler Qf p w) ∧
      movedSpace (eichler Qf p w) = Submodule.span K ({p, w} : Set V) := by
  have hli : LinearIndependent K ![p, w] := by
    rw [LinearIndependent.pair_iff' hp0]
    intro c hc
    exact hwp (hc ▸ Submodule.smul_mem _ c (Submodule.mem_span_singleton_self p))
  have h := isLongRootElement_siegelEquiv Qf p w hp hw hpw hnd hli (one_ne_zero : (1 : K) ≠ 0)
  rwa [siegelEquiv_eq_eichler hp hw hpw 1, one_smul] at h

theorem exists_ne_zero_span_eq_of_finrank_eq_one [FiniteDimensional K V] {P : Submodule K V}
    (hP : finrank K P = 1) : ∃ p : V, p ≠ 0 ∧ P = Submodule.span K ({p} : Set V) := by
  have hbot : P ≠ ⊥ := fun h => by rw [h, finrank_bot] at hP; omega
  obtain ⟨p, hpP, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine ⟨p, hp0, (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm⟩
  · exact (Submodule.span_singleton_le_iff_mem p P).mpr hpP
  · rw [finrank_span_singleton hp0, hP]

theorem mem_piGroup_iff (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {W : Submodule K V}
    (hW : ∀ w ∈ W, Qf w = 0) {p : V} (hp0 : p ≠ 0) (hpW : p ∈ W) {s : V ≃ₗ[K] V} :
    s ∈ piGroup Qf (Submodule.span K ({p} : Set V)) W ↔ ∃ w ∈ W, s = eichler Qf p w := by
  have hp : Qf p = 0 := hW p hpW
  have hpol : ∀ w ∈ W, polar Qf p w = 0 := fun w hw => polar_eq_zero_of_totallySingular hW hpW hw
  constructor
  · intro hs
    let T : Subgroup (V ≃ₗ[K] V) :=
      { carrier := {s | ∃ w ∈ W, s = eichler Qf p w}
        one_mem' := ⟨0, W.zero_mem, (eichler_zero_right Qf p).symm⟩
        mul_mem' := by
          rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
          exact ⟨w + w', W.add_mem hw hw', eichler_mul (hpol w hw) (hpol w' hw')⟩
        inv_mem' := by
          rintro _ ⟨w, hw, rfl⟩
          exact ⟨-w, W.neg_mem hw, eichler_inv (hpol w hw)⟩ }
    have hle : piGroup Qf (Submodule.span K ({p} : Set V)) W ≤ T := by
      rw [piGroup, Subgroup.closure_le]
      rintro t ⟨ht, hPt, htW⟩
      have hpA : p ∈ movedSpace t := (Submodule.span_singleton_le_iff_mem p _).mp hPt
      obtain ⟨b, hbA, hli, hspan⟩ :=
        exists_pair_of_mem_of_finrank_eq_two (ht.finrank_movedSpace hnd) hpA hp0
      obtain ⟨c, -, hc⟩ := exists_siegel_scalar hnd ht.isometry hli hspan
        (fun x hx => ht.qf_eq_zero_of_mem_movedSpace hx)
      have hcb : c • b ∈ W := W.smul_mem c (htW hbA)
      refine ⟨c • b, hcb, ?_⟩
      ext v
      rw [hc v, eichler_apply_of_qf_eq_zero hp (hpol _ hcb) (hW _ hcb), polar_smul_right,
        smul_eq_mul]
      module
    exact hle hs
  · rintro ⟨w, hw, rfl⟩
    by_cases hwp : w ∈ Submodule.span K ({p} : Set V)
    · rw [eichler_eq_one_of_mem_span hp hwp]
      exact Subgroup.one_mem _
    · obtain ⟨h1, h2⟩ := isLongRootElement_eichler hnd hp (hW w hw) (hpol w hw) hp0 hwp
      refine isLongRootElement_mem_piGroup h1 ?_ ?_
      · rw [h2, Submodule.span_singleton_le_iff_mem]
        exact Submodule.subset_span (by simp)
      · rw [h2, Submodule.span_le]
        rintro x (rfl | rfl)
        exacts [hpW, hw]

theorem mem_piGroup_iff_of_ne_one [FiniteDimensional K V]
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {P W : Submodule K V}
    (hW : ∀ w ∈ W, Qf w = 0) (hP : finrank K P = 1) (hPW : P ≤ W) {s : V ≃ₗ[K] V}
    (hs1 : s ≠ 1) :
    s ∈ piGroup Qf P W ↔ IsLongRootElement Qf s ∧ P ≤ movedSpace s ∧ movedSpace s ≤ W := by
  refine ⟨fun hs => ?_, fun ⟨h1, h2, h3⟩ => isLongRootElement_mem_piGroup h1 h2 h3⟩
  obtain ⟨p, hp0, rfl⟩ := exists_ne_zero_span_eq_of_finrank_eq_one hP
  have hpW : p ∈ W := hPW (Submodule.mem_span_singleton_self p)
  obtain ⟨w, hw, rfl⟩ := (mem_piGroup_iff hnd hW hp0 hpW).mp hs
  have hwp : w ∉ Submodule.span K ({p} : Set V) := fun h =>
    hs1 (eichler_eq_one_of_mem_span (hW p hpW) h)
  obtain ⟨h1, h2⟩ := isLongRootElement_eichler hnd (hW p hpW) (hW w hw)
    (polar_eq_zero_of_totallySingular hW hpW hw) hp0 hwp
  refine ⟨h1, ?_, ?_⟩
  · rw [h2, Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span (by simp)
  · rw [h2, Submodule.span_le]
    rintro x (rfl | rfl)
    exacts [hpW, hw]

theorem natCard_piGroup [Finite K] [FiniteDimensional K V]
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {P W : Submodule K V}
    (hW : ∀ w ∈ W, Qf w = 0) (hP : finrank K P = 1) (hPW : P ≤ W) :
    Nat.card (piGroup Qf P W) = Nat.card K ^ (finrank K W - 1) := by
  obtain ⟨p, hp0, rfl⟩ := exists_ne_zero_span_eq_of_finrank_eq_one hP
  have hpW : p ∈ W := hPW (Submodule.mem_span_singleton_self p)
  have hp : Qf p = 0 := hW p hpW
  have hpol : ∀ w ∈ W, polar Qf p w = 0 := fun w hw => polar_eq_zero_of_totallySingular hW hpW hw
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Submodule.span K ({p} : Set V))
  have hsup : Submodule.span K ({p} : Set V) ⊔ C ⊓ W = W := by
    rw [← sup_inf_assoc_of_le C hPW, hC.sup_eq_top, top_inf_eq]
  have hinf : Submodule.span K ({p} : Set V) ⊓ (C ⊓ W) = ⊥ :=
    eq_bot_iff.mpr (le_trans (inf_le_inf_left _ inf_le_left) hC.inf_eq_bot.le)
  let f : ↥(C ⊓ W) → piGroup Qf (Submodule.span K ({p} : Set V)) W := fun w =>
    ⟨eichler Qf p w, (mem_piGroup_iff hnd hW hp0 hpW).mpr ⟨w, (Submodule.mem_inf.mp w.2).2, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun w w' hww' => ?_, fun s => ?_⟩
    · have h := congrArg Subtype.val hww'
      obtain ⟨c, hc⟩ := (eichler_eq_eichler_iff (nondegenerate_polarBilin hnd) hp hp0
        (hpol _ (Submodule.mem_inf.mp w.2).2) (hpol _ (Submodule.mem_inf.mp w'.2).2)).mp h
      have hmem : c • p ∈ Submodule.span K ({p} : Set V) ⊓ (C ⊓ W) := by
        refine ⟨Submodule.smul_mem _ c (Submodule.mem_span_singleton_self p), ?_⟩
        have : c • p = (w' : V) - w := by rw [hc]; abel
        rw [this]
        exact Submodule.sub_mem _ w'.2 w.2
      rw [hinf, Submodule.mem_bot] at hmem
      apply Subtype.ext
      have : (w' : V) = w + c • p := hc
      rw [this, hmem, add_zero]
    · obtain ⟨w, hw, hs⟩ := (mem_piGroup_iff hnd hW hp0 hpW).mp s.2
      rw [← hsup] at hw
      obtain ⟨a, ha, w₀, hw₀, rfl⟩ := Submodule.mem_sup.mp hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      refine ⟨⟨w₀, hw₀⟩, Subtype.ext ?_⟩
      change eichler Qf p w₀ = s.1
      rw [hs, add_comm, eichler_add_smul_self hp]
  rw [← Nat.card_eq_of_bijective f hf, Module.natCard_eq_pow_finrank (K := K)]
  congr 1
  have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K ({p} : Set V)) (C ⊓ W)
  rw [hsup, hinf, finrank_bot, finrank_span_singleton hp0] at h
  omega

theorem piGroup_iSup {ι : Type*} [Nonempty ι] (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {W : ι → Submodule K V} (hW : ∀ w ∈ ⨆ i, W i, Qf w = 0) {p : V} (hp0 : p ≠ 0)
    (hpW : ∀ i, p ∈ W i) :
    piGroup Qf (Submodule.span K ({p} : Set V)) (⨆ i, W i) =
      ⨆ i, piGroup Qf (Submodule.span K ({p} : Set V)) (W i) := by
  have hpS : p ∈ ⨆ i, W i := Submodule.mem_iSup_of_mem (Classical.arbitrary ι) (hpW _)
  refine le_antisymm (fun s hs => ?_) (iSup_le fun i => piGroup_mono le_rfl (le_iSup W i))
  obtain ⟨w, hw, rfl⟩ := (mem_piGroup_iff hnd hW hp0 hpS).mp hs
  have hpol : ∀ w ∈ ⨆ i, W i, polar Qf p w = 0 := fun w hw =>
    polar_eq_zero_of_totallySingular hW hpS hw
  clear hs
  induction hw using Submodule.iSup_induction' with
  | mem i x hx =>
    exact Subgroup.mem_iSup_of_mem i ((mem_piGroup_iff hnd (fun w hw => hW w
      (Submodule.mem_iSup_of_mem i hw)) hp0 (hpW i)).mpr ⟨x, hx, rfl⟩)
  | zero =>
    rw [eichler_zero_right]
    exact one_mem _
  | add x y hx hy ihx ihy =>
    rw [← eichler_mul (hpol x hx) (hpol y hy)]
    exact mul_mem ihx ihy

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
