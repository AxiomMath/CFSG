module

public import CFSG.HardMathSupport.Dickson.KD.CharPAux.Frame
public import CFSG.HardMathSupport.Dickson.KD.CharPAux.FlagGroup

public section

namespace CFSG.HardMathSupport.Dickson.KD

open Matrix CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.HardMathSupport.Timmesfeld.DefChar.Orth

section C

variable {r : ℕ} {K : Type} [Field K]

@[expose] def spRep (r : ℕ) (K : Type) [Field K] :
    StatedSp r K →* Module.End K ((Fin r ⊕ Fin r) → K) :=
  (glRep (Fin r ⊕ Fin r) K).comp (StatedSp r K).subtype

theorem spRep_injective : Function.Injective (spRep r K) :=
  glRep_injective.comp Subtype.val_injective

theorem mem_kerN_iff {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {x : Fin r ⊕ Fin r → K} :
    x ∈ kerN N ↔ x ∈ LinearMap.ker (Matrix.toLin' N) := by
  rw [Matrix.toLin'_apply']
  rfl

theorem mem_Wm_iff {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {x : Fin r ⊕ Fin r → K} :
    x ∈ Wm N ↔ x ∈ LinearMap.ker (Matrix.toLin' N) ⊓ LinearMap.range (Matrix.toLin' N) := by
  rw [Matrix.toLin'_apply']
  rfl

theorem spGen_mem_flagSub {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hs : (1 + N)ᵀ * formJ r K * (1 + N) = formJ r K) {w w' : Fin r ⊕ Fin r → K}
    (h : w ⬝ᵥ (formJ r K *ᵥ w') = 0) (hw : w ∈ Wm N) (hw' : w' ∈ kerN N) :
    spGen w w' h ∈ flagSub (spRep r K) (Matrix.toLin' N) := by
  show InFlag (Matrix.toLin' N) (Matrix.toLin'
    (((spGen w w' h : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
  rw [coe_spGen, map_add, Matrix.toLin'_one]
  have hX := symX_nilRad hs hw hw'
  obtain ⟨h1, h2⟩ := N_symX hs (mem_Wm.1 hw).1 (mem_kerN.1 hw')
  refine inFlag_one_add ?_ ?_ ?_
  · rw [toLin'_mul_eq, toLin'_mul_eq, h1, h2]
  · intro x hx
    rw [Matrix.toLin'_apply]
    exact mem_Wm_iff.1 (hX.2.1 x (mem_kerN_iff.2 hx))
  · intro x hx
    rw [Matrix.toLin'_apply]
    exact hX.2.2 x (mem_Wm_iff.2 hx)

theorem sp_mem_flagSub {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {sg : StatedSp r K}
    (hsg : ((sg : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + N) :
    sg ∈ flagSub (spRep r K) (Matrix.toLin' N) := by
  show InFlag (Matrix.toLin' N) (Matrix.toLin'
    ((sg : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
  rw [hsg, map_add, Matrix.toLin'_one]
  refine inFlag_one_add rfl ?_ ?_
  · intro x hx
    rw [LinearMap.mem_ker.1 hx]
    exact Submodule.zero_mem _
  · intro x hx
    exact LinearMap.mem_ker.1 hx.1

theorem frame_PSp_of_gen [NeZero r] {p : ℕ} [Fact p.Prime] [CharP K p] [Finite K] (hp2 : p ≠ 2)
    (hgen : ∀ α : MulAut (StatedProj (StatedSp r K)), ∃ (A : gsp r K) (σ : K ≃+* K),
      α = conjAut r K A * fieldAut r K σ)
    (y : StatedProj (StatedSp r K)) (hy : orderOf y = p) : Frame p y := by
  obtain ⟨sg, N, hsg, hN, hN0, hy0⟩ := sp_exists_nilpotent_of_orderOf_eq hp2 y hy
  have hs := sp_hs sg hsg
  haveI : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, Nat.pos_of_neZero r⟩⟩
  refine ⟨modelGenC r K N, {y}, ?_, ?_, ?_, ?_, ?_⟩
  · rintro q (hq | hq)
    · rw [hy0]
      exact model_h1C sg hsg q hq
    · rw [Set.mem_singleton_iff.1 hq]
  · intro s q hs' hq
    rw [Set.mem_singleton_iff.1 hq]
    exact hs'
  · intro s q hs' hq
    rw [hy0] at hs'
    exact model_hGenC hN sg hsg s hs' q hq
  · intro s hs hfix
    exact uniq_modelC_of_gen hp2 hgen hN hN0 sg hsg _
      (Nat.Coprime.coprime_dvd_left (orderOf_map_dvd MulAut.conj s) hs)
      (by rw [← hy0]; exact hfix y (Or.inr rfl))
      (fun q hq => hfix q (Or.inl hq))
  · refine isPGroup_closure_of_subset_map spRep_injective (isNilpotent_toLin' hN) (proj r K) ?_
    rintro q (⟨w, w', h, hw, hw', rfl⟩ | hq)
    · exact ⟨_, spGen_mem_flagSub hs h hw hw', rfl⟩
    · rw [Set.mem_singleton_iff.1 hq, hy0]
      exact ⟨_, sp_mem_flagSub hsg, rfl⟩

theorem frame_PSp [NeZero r] {p : ℕ} [Fact p.Prime] [CharP K p] [Finite K] (hp2 : p ≠ 2)
    (hr : 3 ≤ r) (y : StatedProj (StatedSp r K)) (hy : orderOf y = p) : Frame p y :=
  frame_PSp_of_gen hp2 (automorphism_generation (K := K) hr).2 y hy

theorem kdCharPAt_C (q : TauCeti.PrimePower) (r : ℕ) (hv : (TauCeti.LieTypeIndex.C r q).Valid)
    {p : ℕ} (hp2 : p ≠ 2) (hpq : p = q.p) :
    KDCharPAt p (TauCeti.CFSGIndex.lie ⟨.C r q, hv⟩).Group := by
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hr3 : 3 ≤ r := hrange.1
  have hfin := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField (⟨.C r q, hv⟩ :
    TauCeti.ValidLieTypeIndex)
  let K' := ↥(TauCeti.ValidLieTypeIndex.fixedField (⟨.C r q, hv⟩ : TauCeti.ValidLieTypeIndex))
  let e : (TauCeti.CFSGIndex.lie ⟨.C r q, hv⟩).Group ≃* StatedProj (StatedSp r K') :=
    CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv
  have hKq : Nat.card K' = q.p ^ q.exponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simp [TauCeti.ValidLieTypeIndex.fieldOrder]
  subst hpq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hchar : CharP K' q.p := by
    have := Fintype.ofFinite K'
    exact charP_of_card_eq_prime_pow (f := q.exponent) (by rw [← Nat.card_eq_fintype_card, hKq])
  haveI : NeZero r := ⟨by omega⟩
  have hp3 : 3 ≤ q.p := by
    have := q.prime_p.two_le
    omega
  have h3 : 3 ≤ Nat.card K' := by
    rw [hKq]
    exact hp3.trans (Nat.le_self_pow q.exponent_pos.ne' _)
  have hsimple : IsSimpleGroup (StatedProj (StatedSp r K')) := by
    refine CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K' r (by omega) ?_
    by_cases h : Nat.card K' = 3
    · exact Or.inr (Or.inl ⟨h, by omega⟩)
    · exact Or.inl (Or.inr (by omega))
  exact kdCharPAt_of_frame_simple e hsimple fun y hy => frame_PSp hp2 hr3 y hy

theorem kdCharPAt_B_two (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B 2 q).Valid)
    {p : ℕ} (hp2 : p ≠ 2) (hpq : p = q.p) :
    KDCharPAt p (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩).Group := by
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv
    (MulEquiv.refl (TauCeti.ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩))
  have hsimple := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2
    q.p q.exponent hm
  obtain ⟨hprime, K', _, hfin, hK, ⟨e⟩⟩ := hm
  subst hpq
  have : Fact q.p.Prime := ⟨hprime.1⟩
  have hchar : CharP K' q.p := by
    have := Fintype.ofFinite K'
    exact charP_of_card_eq_prime_pow (f := q.exponent) (by rw [← Nat.card_eq_fintype_card, hK])
  have h2K : (2 : K') ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K') = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K' q.p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hprime.1 Nat.prime_two).1 this)
  haveI : NeZero 2 := ⟨by norm_num⟩
  have hgen := (CFSG.RankThree.PartOne.AUTSL.SpTwo.automorphism_generation_two h2K).2
  haveI : IsSimpleGroup (TauCeti.ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩) := hsimple
  exact kdCharPAt_of_frame_simple e e.symm.isSimpleGroup fun y hy => frame_PSp_of_gen hp2 hgen y hy

end C

end CFSG.HardMathSupport.Dickson.KD
