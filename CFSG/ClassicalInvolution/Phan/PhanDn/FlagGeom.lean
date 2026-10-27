module

public import CFSG.ClassicalInvolution.Phan.PhanDn.Chambers

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Models.OrthogonalPairs

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {σ : K ≃+* K} [CharP K 2]
variable {m : ℕ}

variable (σ m) in
@[expose] def FlagVert : Type :=
  {U : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) //
    IsFlipflopSub σ U ∧ U ≠ ⊥ ∧ Module.finrank K U ≠ m}

@[expose] noncomputable def flagTyp (U : FlagVert σ m) : Fin (m + 1) :=
  if Module.finrank K U.1 = m + 1 then
    if Even ((m + 1) - Module.finrank K ↥(U.1 ⊓ stdLag (m + 1) K)) then Fin.last m
    else ⟨m - 1, by omega⟩
  else ⟨min (Module.finrank K U.1 - 1) m, by omega⟩

variable (σ m) in
@[expose] def flagGraph : SimpleGraph (FlagVert σ m) where
  Adj U W := U.1 < W.1 ∨ W.1 < U.1 ∨ (Module.finrank K U.1 = m + 1 ∧
    Module.finrank K W.1 = m + 1 ∧ Module.finrank K ↥(U.1 ⊓ W.1) = m)
  symm := ⟨fun U W h => by
    rcases h with h | h | ⟨h₁, h₂, h₃⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨h₂, h₁, by rwa [inf_comm]⟩)⟩
  loopless := ⟨fun U h => by
    rcases h with h | h | ⟨h₁, -, h₃⟩
    · exact lt_irrefl _ h
    · exact lt_irrefl _ h
    · rw [inf_idem] at h₃
      omega⟩

theorem bcLin_inv_comp_bcLin (E : QuadExt F K σ) (n : ℕ)
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n))) :
    (bcLin E n ((g⁻¹ : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n))) :
        (Fin n → K) →ₗ[F] (Fin n → K))).comp
      (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))) = LinearMap.id := by
  rw [← bcLin_comp, ← bcLin_id E n]
  congr 1
  rw [show ((g⁻¹ : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n))) :
        (Fin n → K) →ₗ[F] (Fin n → K)).comp (g : (Fin n → K) →ₗ[F] (Fin n → K)) =
      ((g⁻¹ * g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n))) :
        (Fin n → K) →ₗ[F] (Fin n → K)) from rfl, inv_mul_cancel]
  rfl

theorem map_bcLin_inv_map_bcLin (E : QuadExt F K σ) (n : ℕ)
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n)))
    (U : Submodule K (Fin n ⊕ Fin n → K)) :
    (U.map (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)))).map
      (bcLin E n ((g⁻¹ : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n))) :
        (Fin n → K) →ₗ[F] (Fin n → K))) = U := by
  rw [← Submodule.map_comp, bcLin_inv_comp_bcLin, Submodule.map_id]

theorem finrank_map_bcLin (E : QuadExt F K σ) (n : ℕ)
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n)))
    (U : Submodule K (Fin n ⊕ Fin n → K)) :
    Module.finrank K ↥(U.map (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)))) =
      Module.finrank K U := by
  refine le_antisymm (Submodule.finrank_map_le _ _) ?_
  calc Module.finrank K U
      = Module.finrank K ↥((U.map (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)))).map
          (bcLin E n ((g⁻¹ : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n))) :
            (Fin n → K) →ₗ[F] (Fin n → K)))) := by rw [map_bcLin_inv_map_bcLin]
    _ ≤ _ := Submodule.finrank_map_le _ _

@[expose] noncomputable def flagSmul (E : QuadExt F K σ) (m : ℕ)
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) (U : FlagVert σ m) :
    FlagVert σ m :=
  ⟨U.1.map (bcLin E (m + 1) (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))),
    U.2.1.map_bcLin E (m + 1) (mem_orthogonalGroup_of_mem_orthDerived E (m + 1) g.2),
    fun h => U.2.2.1 (by
      rw [← map_bcLin_inv_map_bcLin E (m + 1) g U.1, h, Submodule.map_bot]),
    by rw [finrank_map_bcLin]; exact U.2.2.2⟩

noncomputable instance mulActionFlagVert (E : QuadExt F K σ) (m : ℕ) :
    MulAction ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) (FlagVert σ m) where
  smul := flagSmul E m
  one_smul U := by
    apply Subtype.ext
    change U.1.map (bcLin E (m + 1)
      ((1 : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) = U.1
    rw [show ((1 : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) = LinearMap.id from rfl, bcLin_id,
      Submodule.map_id]
  mul_smul g h U := by
    apply Subtype.ext
    change U.1.map (bcLin E (m + 1)
        ((g * h : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
          (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
      (U.1.map (bcLin E (m + 1) (h : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)))).map
        (bcLin E (m + 1) (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)))
    rw [show ((g * h : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) =
        ((g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)).comp
          (h : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) from rfl, bcLin_comp,
      Submodule.map_comp]

theorem coe_smul_flagVert (E : QuadExt F K σ)
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) (U : FlagVert σ m) :
    (g • U).1 = U.1.map (bcLin E (m + 1) (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) :=
  rfl

@[expose] noncomputable def flagChamber (E : QuadExt F K σ) (m : ℕ) (i : Fin (m + 1)) :
    FlagVert σ m :=
  ⟨(stdDChamber σ (m + 1)).elt i,
    (stdDChamber σ (m + 1)).toFlipFrame.isFlipflopSub_elt E.isUnitary.invol i, by
    have h := (stdDChamber σ (m + 1)).toFlipFrame.finrank_elt E.isUnitary.invol i
    refine ⟨fun hbot => ?_, fun hm => ?_⟩
    · rw [hbot, finrank_bot] at h
      by_cases h' : (i : ℕ) + 1 < m
      · rw [if_pos h'] at h
        omega
      · rw [if_neg h'] at h
        omega
    · rw [hm] at h
      by_cases h' : (i : ℕ) + 1 < m
      · rw [if_pos h'] at h
        omega
      · rw [if_neg h'] at h
        omega⟩

omit [CharP K 2] in
theorem coe_flagChamber (E : QuadExt F K σ) (i : Fin (m + 1)) :
    (flagChamber E m i).1 = (stdDChamber σ (m + 1)).elt i :=
  rfl

end CFSG.ClassicalInvolution.PhanDn
