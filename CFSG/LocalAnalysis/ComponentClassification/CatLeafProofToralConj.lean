module

public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.LieType.Chevalley.OddToralInvolutionComponents
public import CFSG.LocalAnalysis.ComponentInitial.GroupComponents

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

theorem map_conj_canonicalRep_toralCentralizer
    (a b : Fin τ.rank → Kˣ) (w : WeylGroup τ)
    (h : ∀ v : Fin τ.rank → ℤ, rootChar a (w • v) = rootChar b v) :
    (toralCentralizer τ K b).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom =
      toralCentralizer τ K a := by
  have hd := (rootDiagUnit_eq_conj_canonicalRep_iff a b w).2 h
  have hn := canonicalRep_mem_adjointGroup (coxeterSystem τ) K w
  rw [toralCentralizer, toralCentralizer, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn), map_centralizer_singleton,
    MulAut.conj_apply, ← hd]

@[expose] def bitsTuple (b : Fin τ.rank → Bool) : Fin τ.rank → Kˣ :=
  fun j => if b j then -1 else 1

theorem bitsTuple_mem (b : Fin τ.rank → Bool) (j : Fin τ.rank) :
    bitsTuple (K := K) b j = 1 ∨ bitsTuple (K := K) b j = -1 := by
  unfold bitsTuple
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem signTupleBits_bitsTuple (hK : ringChar K ≠ 2) (b : Fin τ.rank → Bool) :
    signTupleBits (bitsTuple (K := K) b) = b := by
  classical
  have h1 : (1 : Kˣ) ≠ -1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hK (congrArg Units.val h).symm
  funext j
  unfold signTupleBits bitsTuple
  cases b j
  · simp [h1]
  · simp

theorem exists_conj_toralCentralizer_of_orbitCheck
    (hK : ringChar K ≠ 2) {reps : List (List Bool)}
    {entries : List (List Bool × ℕ × List ℕ)} (hcert : OrbitCheck τ reps entries)
    {b : Fin τ.rank → Kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1) :
    ∃ ρ < reps.length, ∃ w : WeylGroup τ,
      (∀ v : Fin τ.rank → ℤ,
        rootChar b (w • v) = rootChar (bitsTuple (listMask (reps.getD ρ []))) v) ∧
      (toralCentralizer τ K (bitsTuple (listMask (reps.getD ρ [])))).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom =
          toralCentralizer τ K b := by
  obtain ⟨ρ, hρ, t, ht⟩ := exists_isCharConj_of_orbitCheck hcert (maskChar (signTupleBits b))
  have h : ∀ v : Fin τ.rank → ℤ,
      rootChar b (t • v) = rootChar (bitsTuple (listMask (reps.getD ρ []))) v := fun v => by
    rw [rootChar_eq_intUnitsMap hK hb, rootChar_eq_intUnitsMap hK (bitsTuple_mem _),
      signTupleBits_bitsTuple hK, ht (t • v), inv_smul_smul]
  exact ⟨ρ, hρ, t, h, map_conj_canonicalRep_toralCentralizer _ _ t h⟩

theorem eq_one_of_rootChar_smul_eq_one {b : Fin τ.rank → Kˣ} {w : WeylGroup τ}
    (h : ∀ v : Fin τ.rank → ℤ, rootChar b (w • v) = rootChar 1 v) : b = 1 := by
  funext i
  have h1 := h (w⁻¹ • Pi.single i 1)
  rw [smul_inv_smul] at h1
  have h2 : rootChar b (Pi.single i 1) = b i := by
    simpa using rootChar_nsmul_single b i 1
  have h3 : rootChar (1 : Fin τ.rank → Kˣ) (w⁻¹ • Pi.single i 1) = 1 := by
    simp [rootChar]
  rw [h2, h3] at h1
  exact h1

end CFSG.ComponentClassification.CatLeafProof
