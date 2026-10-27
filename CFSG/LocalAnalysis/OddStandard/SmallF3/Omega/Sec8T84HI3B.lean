module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HSyl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HI3P
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HI3T

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem hPm_modelI3_aux (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) {x : ProjOrth Q}
    (hx : x ∈ normalizer (hPm hQ fr : Set (ProjOrth Q))) (hx2 : x * x = 1)
    {r : ℕ} (hr : r = 1 ∨ r = 3) {α : ℤˣ} (hα : HasType x r α) :
    HI3Conc (hPm hQ fr) x := by
  obtain ⟨-, t, ht2, httype, hxt⟩ := hα
  have hdimt : invDim t = r := by
    simpa only [invType] using congrArg Prod.fst httype
  have hodd : Odd (invDim t) := by
    rw [hdimt]
    rcases hr with rfl | rfl <;> decide
  have htN : t ∈ normalizer (ffP0 hQ fr : Set (OGroup Q)) := by
    apply mem_normalizer_of_toProj hQ fr
    rw [hxt]
    exact hx
  obtain ⟨n, hnN, hnt⟩ := exists_conj_into_hPO hQ hdim hsgn fr htN ht2
  set t' : OGroup Q := n * t * n⁻¹ with ht'def
  have ht'2 : t' * t' = 1 := by
    rw [ht'def, show (n * t * n⁻¹) * (n * t * n⁻¹) = n * (t * t) * n⁻¹ by group,
      ht2, mul_one, mul_inv_cancel]
  have ht'type : invType t' = invType t := by
    rw [ht'def]
    exact invType_conj hQ ht2 n
  have hdimt' : invDim t' = r := by
    have h1 : invDim t' = invDim t := by
      simpa only [invType] using congrArg Prod.fst ht'type
    rw [h1, hdimt]
  have hodd' : Odd (invDim t') := by rw [hdimt', ← hdimt]; exact hodd
  obtain ⟨U, hUle, hπU, hUc, hUs, hUcard, p, hpP0, hpt2, hptc, hptdim, hptne1, hptneπ⟩ :=
    po_translate hQ fr (by rw [ht'def]; exact hnt) ht'2 hodd'
  have hBle : U.map (toProj Q) ≤ hPm hQ fr := by
    rw [hPm]
    exact Subgroup.map_mono hUle
  have hElem : IsElemAb2 (U.map (toProj Q)) 4 :=
    map_toProj_isElemAb2 (by rw [hdim]; norm_num) hπU hUc hUs (by rw [hUcard])
  have hp'mem : toProj Q p ∈ hPm hQ fr :=
    (mem_hPm_iff hQ fr).mpr ⟨p, hpP0, rfl⟩
  have hyne : toProj Q (p * t') ≠ 1 := by
    intro h
    have hmem : p * t' ∈ piGroup Q := by
      have h' : QuotientGroup.mk' (piGroup Q) (p * t') = 1 := h
      rw [QuotientGroup.mk'_apply] at h'
      exact (QuotientGroup.eq_one_iff (p * t')).mp h'
    rcases mem_piGroup_iff.mp hmem with h1 | hπ
    · exact hptne1 h1
    · exact hptneπ hπ
  have hconc' : HI3Conc (hPm hQ fr) (toProj Q t') := by
    unfold HI3Conc
    refine ⟨U.map (toProj Q), hBle, hElem, toProj Q p, hp'mem, ?_, ?_, invSign (p * t'), ?_⟩
    · have h := congrArg (toProj Q) hpt2
      simpa only [map_mul, map_one] using h
    · intro b hb
      rw [Subgroup.mem_map] at hb
      obtain ⟨u, hu, rfl⟩ := hb
      have h := congrArg (toProj Q) (hptc u hu)
      simpa only [map_mul] using h
    · simp only [HasType]
      refine ⟨?_, p * t', hpt2, ?_, map_mul (toProj Q) p t'⟩
      · rw [← map_mul]
        exact hyne
      · show (invDim (p * t'), invSign (p * t')) = (3, invSign (p * t'))
        exact Prod.ext hptdim rfl
  have hxeq : toProj Q n * x * (toProj Q n)⁻¹ = toProj Q t' := by
    rw [← hxt, ht'def]
    simp only [map_mul, map_inv]
  refine hI3Conc_of_conj hQ (toProj Q n) (mem_hPm_conj_iff hQ fr hnN) ?_
  rwa [hxeq]

theorem hPm_modelI3 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) {x : ProjOrth Q}
    (hx : x ∈ normalizer (hPm hQ fr : Set (ProjOrth Q))) (hx2 : x * x = 1)
    (hty : ∃ α : ℤˣ, HasType x 1 α ∨ HasType x 3 α) : HI3Conc (hPm hQ fr) x := by
  obtain ⟨α, hα | hα⟩ := hty
  · exact hPm_modelI3_aux (r := 1) hQ hdim hsgn fr hx hx2 (Or.inl rfl) hα
  · exact hPm_modelI3_aux (r := 3) hQ hdim hsgn fr hx hx2 (Or.inr rfl) hα

theorem sec8t84_modelI3 :
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate),
      Module.finrank (ZMod 3) V = 6 → quadSign Q = -1 →
        ∀ P : Subgroup (ProjOrth Q), IsSylow2Of P (omegaProj hQ) →
          ∀ x : ProjOrth Q, x ∈ normalizer (P : Set (ProjOrth Q)) → x * x = 1 →
            (∃ α : ℤˣ, HasType x 1 α ∨ HasType x 3 α) →
              ∃ B : Subgroup (ProjOrth Q), B ≤ P ∧ IsElemAb2 B 4 ∧ ∃ p ∈ P,
                (p * x) * (p * x) = 1 ∧ (∀ b ∈ B, (p * x) * b = b * (p * x)) ∧
                  ∃ α : ℤˣ, HasType (p * x) 3 α := by
  intro V _ _ _ Q hQ hdim hsgn P hP
  haveI : Finite (OGroup Q) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_oGroup_six_minus hQ hdim hsgn]; norm_num)
  haveI : Finite (ProjOrth Q) :=
    Finite.of_surjective (toProj Q) (QuotientGroup.mk'_surjective (piGroup Q))
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hsgn
  obtain ⟨a, -, ha⟩ := IsSylow2Of.exists_conj_mem (hPm_sylow hQ hdim hsgn fr) hP
  exact modelI3_of_conj hQ a ha
    (fun x hx hx2 hty => hPm_modelI3 hQ hdim hsgn fr hx hx2 hty)

end CFSG.OddStandard.SmallF3.Omega
