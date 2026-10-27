module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddGenForm
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddSp
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank
open scoped Matrix

section SpGen

variable {r : ℕ} {F : Type} [Field F] [Finite F] {q : ℕ} [Fact q.Prime] [CharP F q]

theorem spForm_eq_paired (u v : Fin r ⊕ Fin r → F) :
    (spForm r F).β u v = pairedSympForm F r u v := by
  rw [spForm_β]
  simp only [pairedSympForm, Matrix.toBilin'_apply']

@[expose] noncomputable def spUrad (W : Submodule F (Fin r ⊕ Fin r → F)) : Subgroup (StatedSp r F) :=
  flagKernel (natRep (StatedSp r F)) (isoCompletion (spForm r F) (oneStep W) 1)

theorem spUrad_isPGroup (W : Submodule F (Fin r ⊕ Fin r → F)) : IsPGroup q (spUrad W) :=
  isPGroup_flagKernel (natRep (StatedSp r F)) q (natRep_injective _)
    (isoCompletion_zero (oneStep_zero W) 1) (isoCompletion_top (oneStep_zero W) 1)

theorem stabilizer_le_normalizer_spUrad {W : Submodule F (Fin r ⊕ Fin r → F)} :
    SymplecticFlag.stabilizer r F W ≤ Subgroup.normalizer (spUrad W : Set (StatedSp r F)) := by
  refine le_trans ?_ (flagStab_le_normalizer_flagKernel (natRep (StatedSp r F)) _)
  refine le_flagStab_isoCompletion (natRep (StatedSp r F)) (isIsometric_natRep_statedSp r F) 1 ?_
  intro h hh k v hv
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [oneStep_zero, Submodule.mem_bot] at hv
    rw [hv, map_zero, oneStep_zero]
    exact Submodule.zero_mem _
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [oneStep_succ] at hv ⊢
    have hmem : ((h : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ v ∈
        W.map (Matrix.mulVecLin ((h : GL (Fin r ⊕ Fin r) F) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) := ⟨v, hv, rfl⟩
    rw [SymplecticFlag.mem_stabilizer.1 hh] at hmem
    rw [natRep_apply]
    exact hmem

theorem spForm_single_inl (i : Fin r) (v : Fin r ⊕ Fin r → F) :
    (spForm r F).β (Pi.single (Sum.inl i) 1) v = v (Sum.inr i) := by
  rw [spForm_β, dotProduct_spJ_mulVec]
  have h1 : (Pi.single (Sum.inl i) (1 : F) : Fin r ⊕ Fin r → F) ∘ Sum.inl = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply]
  have h2 : (Pi.single (Sum.inl i) (1 : F) : Fin r ⊕ Fin r → F) ∘ Sum.inr = 0 := by
    funext j
    simp [Pi.single_apply]
  rw [h1, h2, zero_dotProduct, sub_zero, single_dotProduct, one_mul]
  rfl

theorem isTotallyIsotropic_spFlag {d : ℕ} (hdr : d ≤ r) :
    (spForm r F).IsTotallyIsotropic (SymplecticFlag.flag r F d) := by
  intro x hx w hw
  rw [spForm_eq_paired]
  exact (SymplecticHigher.isCompleteIsotropicFlag_flag (r := r) (K := F)).2.2 d hdr w hw x hx

theorem exists_smul_of_mem_spScalars {g : StatedSp r F} (hg : g ∈ SymplecticHigher.spScalars r F) :
    ∃ c : F, ∀ v, natRep (StatedSp r F) g v = c • v := by
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨c, hc⟩ := hg
  refine ⟨(c : F), fun v => ?_⟩
  rw [natRep_apply, ← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext x
  simp [Matrix.mulVec_diagonal]

theorem exists_mem_spUrad_flag (hr : 2 ≤ r) {d : ℕ} (hd : 1 ≤ d) (hdr : d ≤ r) :
    ∃ g ∈ spUrad (SymplecticFlag.flag r F d), g ∉ SymplecticHigher.spScalars r F := by
  set i0 : Fin r := ⟨0, by omega⟩ with hi0
  set i1 : Fin r := ⟨1, by omega⟩ with hi1
  set x : Fin r ⊕ Fin r → F := Pi.single (Sum.inl i0) 1 with hx
  set w2 : Fin r ⊕ Fin r → F := Pi.single (Sum.inl i1) 1 with hw2
  set f1 : Fin r ⊕ Fin r → F := Pi.single (Sum.inr i0) 1 with hf1
  have hxW : x ∈ SymplecticFlag.flag r F d := by
    rw [SymplecticFlag.mem_flag_of_le hdr, SymplecticFlag.mem_isoFlag]
    refine ⟨fun j => by simp [hx], fun j hj => ?_⟩
    have : Sum.inl i0 ≠ (Sum.inl j : Fin r ⊕ Fin r) := by
      intro h
      have := Sum.inl.inj h
      have h2 := congrArg Fin.val this
      simp [hi0] at h2
      omega
    simp [hx, Pi.single_apply, this]
  have hβ1 : (spForm r F).β x w2 = 0 := by
    rw [hx, spForm_single_inl]
    simp [hw2]
  have hβ2 : (spForm r F).β x f1 = 1 := by
    rw [hx, spForm_single_inl]
    simp [hf1]
  obtain ⟨c₀, g, hc₀, hg⟩ := ea2_Sp (F := F) r x trivial
  refine ⟨g, ?_, fun hs => ?_⟩
  · have hiso := isTotallyIsotropic_spFlag (F := F) (r := r) hdr
    refine mem_flagKernel_isoCompletion (natRep (StatedSp r F))
      (oneStep_mono (SymplecticFlag.flag r F d)) (fun k => ?_) (Nat.lt_succ_self 0)
      (x := x) (y := x) (a := c₀ • x) (by rw [oneStep_succ]; exact hxW)
      (by rw [oneStep_succ]; exact hiso hxW) (by
        rw [oneStep_succ]
        exact Submodule.smul_mem _ _ (hiso hxW)) 0 (fun v => ?_)
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [oneStep_zero]; exact bot_le
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [oneStep_succ]; exact hiso
    · rw [hg v, zero_mul, zero_smul, add_zero, smul_smul, mul_comm]
  · obtain ⟨c, hc⟩ := exists_smul_of_mem_spScalars hs
    have h1 := hc w2
    rw [hg w2, hβ1, mul_zero, zero_smul, add_zero] at h1
    have h1' := congrFun h1 (Sum.inl i1)
    simp [hw2] at h1'
    have h2 := hc f1
    rw [hg f1, hβ2, mul_one] at h2
    have h2' := congrFun h2 (Sum.inl i0)
    simp [hf1, hx, h1'.symm] at h2'
    exact hc₀ h2'

theorem twoParabolics_PSp (hr : 2 ≤ r) : TwoParabolics q (StatedProj (StatedSp r F)) := by
  have hr1 : 1 ≤ r := by omega
  have hB : SymplecticFlag.projBorel r F ∈ SymplecticHigher.spSylowNormalizers r F q := by
    rw [SymplecticHigher.spSylowNormalizers_eq q hr1]
    refine ⟨1, ?_⟩
    have : (MulAut.conj (1 : StatedProj (StatedSp r F))).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply]
    rw [this, Subgroup.map_id]
  obtain ⟨U₀, hU₀⟩ := hB
  have hUB : (U₀ : Subgroup (StatedProj (StatedSp r F))) ≤ SymplecticFlag.projBorel r F :=
    hU₀ ▸ Subgroup.le_normalizer
  have hBP : ∀ d, d ≤ r → SymplecticFlag.projBorel r F ≤
      SymplecticHigher.projStabilizer r F (SymplecticFlag.flag r F d) := fun d hdr =>
    Subgroup.map_mono (SymplecticHigher.borelSubgroup_le_stabilizer_flag hdr)
  have hP₁ : IsCoatom (SymplecticHigher.projStabilizer r F (SymplecticFlag.flag r F 1)) :=
    SymplecticHigher.isCoatom_projStabilizer_flag le_rfl hr1
  have hP₂ : IsCoatom (SymplecticHigher.projStabilizer r F (SymplecticFlag.flag r F 2)) :=
    SymplecticHigher.isCoatom_projStabilizer_flag (by norm_num) hr
  have hfl : ∀ d, 1 ≤ d → d ≤ r → SymplecticFlag.flag r F d ≠ ⊥ := by
    intro d hd hdr h
    have := SymplecticHigher.finrank_flag (r := r) (K := F) (i := d) (by omega)
    rw [h, finrank_bot] at this
    omega
  have hne : ¬ SymplecticHigher.projStabilizer r F (SymplecticFlag.flag r F 2) ≤
      SymplecticHigher.projStabilizer r F (SymplecticFlag.flag r F 1) := by
    intro hle
    rcases hP₂.le_iff.mp hle with h | h
    · exact hP₁.1 h
    · have hinj := (SymplecticHigher.maximal_parabolics (r := r) (K := F) q hr1).2.2
        (SymplecticFlag.flag r F 1) (SymplecticFlag.flag r F 2) (hfl 1 le_rfl hr1)
        ((SymplecticHigher.isCompleteIsotropicFlag_flag (r := r) (K := F)).2.2 1 hr1)
        (hfl 2 (by norm_num) hr)
        ((SymplecticHigher.isCompleteIsotropicFlag_flag (r := r) (K := F)).2.2 2 hr) h
      have h1 := SymplecticHigher.finrank_flag (r := r) (K := F) (i := 1) (by omega)
      have h2 := SymplecticHigher.finrank_flag (r := r) (K := F) (i := 2) (by omega)
      rw [hinj] at h1
      omega
  have hQ : ∀ d, 1 ≤ d → d ≤ r →
      ((spUrad (SymplecticFlag.flag r F d)).map (SymplecticFlag.proj r F)) ≠ ⊥ ∧
      IsPGroup q ((spUrad (SymplecticFlag.flag r F d)).map (SymplecticFlag.proj r F)) ∧
      SymplecticHigher.projStabilizer r F (SymplecticFlag.flag r F d) ≤
        Subgroup.normalizer
          (((spUrad (SymplecticFlag.flag r F d)).map (SymplecticFlag.proj r F) :
            Subgroup (StatedProj (StatedSp r F))) : Set (StatedProj (StatedSp r F))) := by
    intro d hd hdr
    refine ⟨?_, (spUrad_isPGroup _).map _, ?_⟩
    · obtain ⟨g, hg, hgs⟩ := exists_mem_spUrad_flag (F := F) hr hd hdr
      intro hbot
      rw [Subgroup.eq_bot_iff_forall] at hbot
      have := hbot _ ⟨g, hg, rfl⟩
      apply hgs
      rw [← SymplecticHigher.ker_proj, MonoidHom.mem_ker]
      exact this
    · exact (Subgroup.map_mono stabilizer_le_normalizer_spUrad).trans
        (Subgroup.le_normalizer_map (SymplecticFlag.proj r F))
  obtain ⟨hQ1, hQ1p, hQ1n⟩ := hQ 1 le_rfl hr1
  obtain ⟨hQ2, hQ2p, hQ2n⟩ := hQ 2 (by norm_num) hr
  exact ⟨U₀, _, _, _, _, hP₁, hne, hUB.trans (hBP 1 hr1), hUB.trans (hBP 2 hr), hQ1, hQ1p, hQ1n,
    hQ2, hQ2p, hQ2n⟩

end SpGen

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
