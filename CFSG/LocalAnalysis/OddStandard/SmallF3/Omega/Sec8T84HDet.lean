module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoOmega
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Det
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoDef

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {c : ZMod 3}

theorem orthogonalDet_mono (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    (σ : Equiv.Perm (Fin 6)) (J : Finset (Fin 6)) :
    QuadraticMap.orthogonalDet Q (fr.permOrth σ * fr.signChange J) =
      (if Equiv.Perm.sign σ = 1 then (1 : (ZMod 3)ˣ) else -1) * (-1 : (ZMod 3)ˣ) ^ J.card := by
  have hmul : QuadraticMap.orthogonalDet Q (fr.permOrth σ * fr.signChange J) =
      QuadraticMap.orthogonalDet Q (fr.permOrth σ) *
        QuadraticMap.orthogonalDet Q (fr.signChange J) := by
    have h := congrArg Prod.fst (map_mul (CFSG.ClassicalInvolution.detSpinorNorm hQ)
      (fr.permOrth σ) (fr.signChange J))
    rw [CFSG.ClassicalInvolution.detSpinorNorm_apply,
      CFSG.ClassicalInvolution.detSpinorNorm_apply,
      CFSG.ClassicalInvolution.detSpinorNorm_apply, Prod.fst_mul] at h
    exact h
  have hp : QuadraticMap.orthogonalDet Q (fr.permOrth σ) =
      (if Equiv.Perm.sign σ = 1 then (1 : (ZMod 3)ˣ) else -1) := by
    have h := congrArg Prod.fst (ffMono_detSpinor_permOrth hQ fr σ)
    change (CFSG.ClassicalInvolution.detSpinorNorm hQ (fr.permOrth σ)).1 = _
    rw [h]
    by_cases hs : Equiv.Perm.sign σ = 1
    · rw [if_pos hs, if_pos hs]; rfl
    · rw [if_neg hs, if_neg hs]
  have ht : QuadraticMap.orthogonalDet Q (fr.signChange J) = (-1 : (ZMod 3)ˣ) ^ J.card := by
    have h := congrArg Prod.fst (ffMono_detSpinor_signChange hQ fr J)
    change (CFSG.ClassicalInvolution.detSpinorNorm hQ (fr.signChange J)).1 = _
    rw [h]
  rw [hmul, hp, ht]

theorem mono_parity (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    {σ : Equiv.Perm (Fin 6)} {J : Finset (Fin 6)}
    (h2 : (fr.permOrth σ * fr.signChange J) * (fr.permOrth σ * fr.signChange J) = 1)
    (hodd : Odd (invDim (fr.permOrth σ * fr.signChange J))) :
    (σ ∈ alternatingGroup (Fin 6) ∧ Odd J.card) ∨
      (σ ∉ alternatingGroup (Fin 6) ∧ Even J.card) := by
  have hdet1 : QuadraticMap.orthogonalDet Q (fr.permOrth σ * fr.signChange J) = -1 := by
    rw [orthogonalDet_involution h2, Odd.neg_one_pow hodd]
  have hdet2 : QuadraticMap.orthogonalDet Q (fr.permOrth σ * fr.signChange J) =
      (if Equiv.Perm.sign σ = 1 then (1 : (ZMod 3)ˣ) else -1) *
        (-1 : (ZMod 3)ˣ) ^ J.card :=
    orthogonalDet_mono hQ fr σ J
  by_cases hs : Equiv.Perm.sign σ = 1
  · left
    refine ⟨Equiv.Perm.mem_alternatingGroup.mpr hs, ?_⟩
    have h : (-1 : (ZMod 3)ˣ) ^ J.card = -1 := by
      calc (-1 : (ZMod 3)ˣ) ^ J.card
          = QuadraticMap.orthogonalDet Q (fr.permOrth σ * fr.signChange J) := by
            rw [hdet2, if_pos hs, one_mul]
        _ = -1 := hdet1
    exact (neg_one_pow_eq_neg_one_iff_odd (by decide : (-1 : (ZMod 3)ˣ) ≠ 1)).mp h
  · right
    refine ⟨fun hmem => hs (Equiv.Perm.mem_alternatingGroup.mp hmem), ?_⟩
    have hneg : (-1 : (ZMod 3)ˣ) * (-1 : (ZMod 3)ˣ) ^ J.card = -1 := by
      calc (-1 : (ZMod 3)ˣ) * (-1 : (ZMod 3)ˣ) ^ J.card
          = QuadraticMap.orthogonalDet Q (fr.permOrth σ * fr.signChange J) := by
            rw [hdet2, if_neg hs]
        _ = -1 := hdet1
    have h : (-1 : (ZMod 3)ˣ) ^ J.card = 1 := by
      have hmul : (-1 : (ZMod 3)ˣ) * (-1 : (ZMod 3)ˣ) ^ J.card =
          (-1 : (ZMod 3)ˣ) * 1 := by rw [mul_one]; exact hneg
      exact mul_left_cancel hmul
    exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : (ZMod 3)ˣ) ≠ 1)).mp h

@[expose] noncomputable def hH1 (fr : NFrame Q (Fin 6) c) : OGroup Q :=
  fr.signChange {3, 4, 5}

@[expose] noncomputable def hH2 (fr : NFrame Q (Fin 6) c) : OGroup Q :=
  fr.permOrth (Equiv.swap 4 5) * fr.signChange {1, 3}

theorem hH1_mul_self (fr : NFrame Q (Fin 6) c) : hH1 fr * hH1 fr = 1 := by
  rw [hH1]
  exact fr.signChange_mul_self {3, 4, 5}

theorem hH2_mul_self (fr : NFrame Q (Fin 6) c) : hH2 fr * hH2 fr = 1 := by
  have h := ffMono_mul fr (Equiv.swap 4 5) (Equiv.swap 4 5) {1, 3} {1, 3}
  rw [hH2, h, Equiv.swap_mul_self 4 5]
  have hmap : (Finset.map ((Equiv.swap 4 5)⁻¹).toEmbedding ({1, 3} : Finset (Fin 6))) =
      ({1, 3} : Finset (Fin 6)) := by decide
  rw [hmap, symmDiff_self, Finset.bot_eq_empty, fr.permOrth_one, fr.signChange_empty, mul_one]

private lemma t84h_repr_sub (fr : NFrame Q (Fin 6) c) (a b j : Fin 6) :
    fr.b.repr (fr.b a - fr.b b) j = (if a = j then 1 else 0) - (if b = j then 1 else 0) := by
  simp only [map_sub, Module.Basis.repr_self, Finsupp.sub_apply, Finsupp.single_apply]

private lemma t84h_repr_add (fr : NFrame Q (Fin 6) c) (a b j : Fin 6) :
    fr.b.repr (fr.b a + fr.b b) j = (if a = j then 1 else 0) + (if b = j then 1 else 0) := by
  simp only [map_add, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.single_apply]

private lemma t84h_linearIndependent_of_pivot {ι : Type} [Fintype ι]
    {fr : NFrame Q (Fin 6) c} (v : ι → V) (p : ι → Fin 6)
    (hdiag : ∀ i, fr.b.repr (v i) (p i) = 1)
    (hoff : ∀ i j, i ≠ j → fr.b.repr (v i) (p j) = 0) :
    LinearIndependent (ZMod 3) v := by
  rw [Fintype.linearIndependent_iff]
  intro a ha j
  have h := congrArg (fun x => fr.b.repr x (p j)) ha
  simp only [map_zero, Finsupp.zero_apply] at h
  have hsum : fr.b.repr (∑ i, a i • v i) (p j) = a j := by
    rw [map_sum]
    simp only [map_smul]
    rw [Finset.sum_apply']
    simp only [Finsupp.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · rw [hdiag j, mul_one]
    · intro i _ hij
      rw [hoff i j hij, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [hsum] at h
  exact h

private lemma t84h_card_le_finrank {ι : Type} [Fintype ι] {v : ι → V}
    (hv : LinearIndependent (ZMod 3) v) {W : Submodule (ZMod 3) V} (hW : ∀ i, v i ∈ W) :
    Fintype.card ι ≤ Module.finrank (ZMod 3) W := by
  have hle : Submodule.span (ZMod 3) (Set.range v) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hW i
  calc Fintype.card ι
      = Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range v)) :=
        (finrank_span_eq_card hv).symm
    _ ≤ Module.finrank (ZMod 3) W := Submodule.finrank_mono hle

theorem hH1_invDim (fr : NFrame Q (Fin 6) c) : invDim (hH1 fr) = 3 := by
  rw [hH1, ffMono_invDim_signChange]
  decide

theorem hH2_invDim (fr : NFrame Q (Fin 6) c) : invDim (hH2 fr) = 3 := by
  set g : OGroup Q := hH2 fr with hg
  have hgg' : g * g = 1 := by rw [hg]; exact hH2_mul_self fr
  have hgb : ∀ i : Fin 6, (g : V ≃ₗ[ZMod 3] V) (fr.b i) =
      (if i ∈ ({1, 3} : Finset (Fin 6)) then (-1 : ZMod 3) else 1) •
        fr.b ((Equiv.swap 4 5) i) := by
    intro i
    rw [hg, hH2]
    exact ffMono_basis fr (Equiv.swap 4 5) {1, 3} i
  have hg0 : (g : V ≃ₗ[ZMod 3] V) (fr.b 0) = fr.b 0 := by
    rw [hgb 0]; simp [Equiv.swap_apply_def]
  have hg1 : (g : V ≃ₗ[ZMod 3] V) (fr.b 1) = -fr.b 1 := by
    rw [hgb 1]; simp [Equiv.swap_apply_def]
  have hg2 : (g : V ≃ₗ[ZMod 3] V) (fr.b 2) = fr.b 2 := by
    rw [hgb 2]; simp [Equiv.swap_apply_def]
  have hg3 : (g : V ≃ₗ[ZMod 3] V) (fr.b 3) = -fr.b 3 := by
    rw [hgb 3]; simp [Equiv.swap_apply_def]
  have hg4 : (g : V ≃ₗ[ZMod 3] V) (fr.b 4) = fr.b 5 := by
    rw [hgb 4]; simp [Equiv.swap_apply_def]
  have hg5 : (g : V ≃ₗ[ZMod 3] V) (fr.b 5) = fr.b 4 := by
    rw [hgb 5]; simp [Equiv.swap_apply_def]
  have h1 : fr.b 1 ∈ commSp g := by
    rw [mem_commSp_iff hgg', hg1]
  have h3 : fr.b 3 ∈ commSp g := by
    rw [mem_commSp_iff hgg', hg3]
  have h45 : fr.b 4 - fr.b 5 ∈ commSp g := by
    rw [mem_commSp_iff hgg', map_sub, hg4, hg5, neg_sub]
  have h0 : fr.b 0 ∈ fixSp g := by
    rw [mem_fixSp_iff, hg0]
  have h2 : fr.b 2 ∈ fixSp g := by
    rw [mem_fixSp_iff, hg2]
  have h45' : fr.b 4 + fr.b 5 ∈ fixSp g := by
    rw [mem_fixSp_iff, map_add, hg4, hg5, add_comm]
  have hoff_li : LinearIndependent (ZMod 3)
      (![fr.b 1, fr.b 3, fr.b 4 - fr.b 5] : Fin 3 → V) := by
    apply t84h_linearIndependent_of_pivot (fr := fr)
      (![fr.b 1, fr.b 3, fr.b 4 - fr.b 5] : Fin 3 → V) (![1, 3, 4] : Fin 3 → Fin 6)
    · intro i
      fin_cases i <;> simp [t84h_repr_sub]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [t84h_repr_sub]
  have hon_li : LinearIndependent (ZMod 3)
      (![fr.b 0, fr.b 2, fr.b 4 + fr.b 5] : Fin 3 → V) := by
    apply t84h_linearIndependent_of_pivot (fr := fr)
      (![fr.b 0, fr.b 2, fr.b 4 + fr.b 5] : Fin 3 → V) (![0, 2, 4] : Fin 3 → Fin 6)
    · intro i
      fin_cases i <;> simp [t84h_repr_add]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [t84h_repr_add]
  have hoff_le : 3 ≤ Module.finrank (ZMod 3) (commSp g) := by
    have h := t84h_card_le_finrank hoff_li (W := commSp g) (fun i => by
      fin_cases i
      · simpa using h1
      · simpa using h3
      · simpa using h45)
    simpa using h
  have hon_le : 3 ≤ Module.finrank (ZMod 3) (fixSp g) := by
    have h := t84h_card_le_finrank hon_li (W := fixSp g) (fun i => by
      fin_cases i
      · simpa using h0
      · simpa using h2
      · simpa using h45')
    simpa using h
  have hsum : Module.finrank (ZMod 3) (fixSp g) + Module.finrank (ZMod 3) (commSp g) = 6 := by
    rw [finrank_fixSp_add_finrank_commSp g, Module.finrank_eq_card_basis fr.b]
    simp
  simp only [invDim]
  omega

theorem hH1_ne_one (fr : NFrame Q (Fin 6) c) : hH1 fr ≠ 1 := by
  intro h
  have h3 : invDim (1 : OGroup Q) = 3 := by rw [← h]; exact hH1_invDim fr
  have h0 : invDim (1 : OGroup Q) = 0 := by
    change (invType (1 : OGroup Q)).1 = 0
    exact congrArg Prod.fst (invType_one (Q := Q))
  rw [h0] at h3
  exact absurd h3 (by decide)

theorem hH1_ne_piOrth (fr : NFrame Q (Fin 6) c) : hH1 fr ≠ piOrth Q := by
  intro h
  have h3 : invDim (piOrth Q) = 3 := by rw [← h]; exact hH1_invDim fr
  have h6 : invDim (piOrth Q) = 6 := by
    rw [fr.piOrth_eq_signChange_univ, ffMono_invDim_signChange]
    simp
  rw [h6] at h3
  exact absurd h3 (by decide)

theorem hH2_ne_one (fr : NFrame Q (Fin 6) c) : hH2 fr ≠ 1 := by
  intro h
  have h3 : invDim (1 : OGroup Q) = 3 := by rw [← h]; exact hH2_invDim fr
  have h0 : invDim (1 : OGroup Q) = 0 := by
    change (invType (1 : OGroup Q)).1 = 0
    exact congrArg Prod.fst (invType_one (Q := Q))
  rw [h0] at h3
  exact absurd h3 (by decide)

theorem hH2_ne_piOrth (fr : NFrame Q (Fin 6) c) : hH2 fr ≠ piOrth Q := by
  intro h
  have h3 : invDim (piOrth Q) = 3 := by rw [← h]; exact hH2_invDim fr
  have h6 : invDim (piOrth Q) = 6 := by
    rw [fr.piOrth_eq_signChange_univ, ffMono_invDim_signChange]
    simp
  rw [h6] at h3
  exact absurd h3 (by decide)

end CFSG.OddStandard.SmallF3.Omega
