module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.ClassicalInvolution.Q3.AE.Bar
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AECov

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

theorem one_symm_apply (x : Fin n) : (1 : Equiv.Perm (Fin n)).symm x = x := rfl

theorem one_symm_apply_four (x : Fin 4) : (1 : Equiv.Perm (Fin 4)).symm x = x := rfl

theorem vec_conj_embed (ι : Fin 4 ↪ Fin n) {w : Wr n} (hw : w.perm = 1) (a : Wr 4) :
    w * embed ι a * w⁻¹ =
      embed ι (ofVec (fun i => w.vec (ι i)) * a * (ofVec (fun i => w.vec (ι i)))⁻¹) := by
  refine Wr.ext (funext fun x => ?_) ?_
  · rw [mul_vec, mul_vec, inv_vec, embed_vec]
    simp only [mul_perm, hw, one_mul, one_symm_apply, Equiv.Perm.one_apply, embed_vec,
      embed_perm]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [embedVec_apply, embedVec_apply, embedPerm_symm_apply, mul_vec, mul_vec, inv_vec]
      simp only [ofVec, mul_perm, one_mul, one_symm_apply_four, Equiv.Perm.one_apply]
    · rw [embedVec_of_not_mem ι _ hx, embedVec_of_not_mem ι _ hx, embedPerm_symm_of_not_mem ι _ hx,
        add_zero, zmod_two_add_self]
  · simp only [mul_perm, inv_perm, hw, one_mul, inv_one, mul_one, embed_perm, ofVec]

theorem kList_conj_vec : ∀ u : Fin 4 → ZMod 2,
    ((∀ a ∈ kList, ofVec u * a * (ofVec u)⁻¹ ∈ kList) ∧
        ∀ a ∈ kStarList, ofVec u * a * (ofVec u)⁻¹ ∈ kStarList) ∨
      ((∀ a ∈ kList, ofVec u * a * (ofVec u)⁻¹ ∈ kStarList) ∧
        ∀ a ∈ kStarList, ofVec u * a * (ofVec u)⁻¹ ∈ kList) := by
  decide +kernel

theorem ofVec_inv_self (u : Fin 4 → ZMod 2) : (ofVec u)⁻¹ = ofVec u := by
  refine Wr.ext (funext fun i => ?_) ?_
  · rfl
  · show (1 : Equiv.Perm (Fin 4))⁻¹ = 1
    rw [inv_one]

theorem map_conj_ofVec_eq {S T : Subgroup (Wr 4)} (u : Fin 4 → ZMod 2)
    (hST : ∀ a ∈ S, ofVec u * a * (ofVec u)⁻¹ ∈ T) (hTS : ∀ a ∈ T, ofVec u * a * (ofVec u)⁻¹ ∈ S) :
    S.map (MulAut.conj (ofVec u)).toMonoidHom = T := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact hST a ha
  · intro hx
    refine ⟨ofVec u * x * (ofVec u)⁻¹, hTS x hx, ?_⟩
    show ofVec u * (ofVec u * x * (ofVec u)⁻¹) * (ofVec u)⁻¹ = x
    rw [ofVec_inv_self]
    have h1 : ofVec u * ofVec u = (1 : Wr 4) := by
      rw [← mul_inv_cancel (ofVec u), ofVec_inv_self]
    calc ofVec u * (ofVec u * x * ofVec u) * ofVec u
        = (ofVec u * ofVec u) * x * (ofVec u * ofVec u) := by group
      _ = x := by rw [h1, one_mul, mul_one]

theorem kQ_conj_vec (u : Fin 4 → ZMod 2) :
    (kQ.map (MulAut.conj (ofVec u)).toMonoidHom = kQ ∧
        kQStar.map (MulAut.conj (ofVec u)).toMonoidHom = kQStar) ∨
      (kQ.map (MulAut.conj (ofVec u)).toMonoidHom = kQStar ∧
        kQStar.map (MulAut.conj (ofVec u)).toMonoidHom = kQ) := by
  rcases kList_conj_vec u with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨map_conj_ofVec_eq u h1 h1, map_conj_ofVec_eq u h2 h2⟩
  · exact Or.inr ⟨map_conj_ofVec_eq u h1 h2, map_conj_ofVec_eq u h2 h1⟩

theorem map_embed_conj (ι : Fin 4 ↪ Fin n) {w : Wr n} (hw : w.perm = 1) (S : Subgroup (Wr 4)) :
    (S.map (embed ι)).map (MulAut.conj w).toMonoidHom =
      (S.map (MulAut.conj (ofVec (fun i => w.vec (ι i)))).toMonoidHom).map (embed ι) := by
  have e : (MulAut.conj w).toMonoidHom.comp (embed ι) =
      (embed ι).comp (MulAut.conj (ofVec (fun i => w.vec (ι i)))).toMonoidHom :=
    MonoidHom.ext fun a => vec_conj_embed ι hw a
  rw [Subgroup.map_map, Subgroup.map_map, e]

theorem conjSub_memBar_of_perm_eq_one {w : Wr n} (hw : w.perm = 1) (α : Finset (Fin n))
    (h : α.card = 4) (b : Bool) :
    conjSub (mkQ n w) (memBar α h b) = memBar α h true ∨
      conjSub (mkQ n w) (memBar α h b) = memBar α h false := by
  have hmk : conjSub (mkQ n w) (memBar α h b) =
      ((memAt α h b).map (MulAut.conj w).toMonoidHom).map (mkQ n) := by
    show ((memAt α h b).map (mkQ n)).map (MulAut.conj (mkQ n w)).toMonoidHom = _
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [hmk]
  have hK : (memK (emb α h)).map (MulAut.conj w).toMonoidHom = memK (emb α h) ∨
      (memK (emb α h)).map (MulAut.conj w).toMonoidHom = memKStar (emb α h) := by
    unfold memK memKStar
    rw [map_embed_conj _ hw]
    rcases kQ_conj_vec (fun i => w.vec (emb α h i)) with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl (by rw [h1])
    · exact Or.inr (by rw [h1])
  have hKs : (memKStar (emb α h)).map (MulAut.conj w).toMonoidHom = memKStar (emb α h) ∨
      (memKStar (emb α h)).map (MulAut.conj w).toMonoidHom = memK (emb α h) := by
    unfold memK memKStar
    rw [map_embed_conj _ hw]
    rcases kQ_conj_vec (fun i => w.vec (emb α h i)) with ⟨-, h1⟩ | ⟨-, h1⟩
    · exact Or.inl (by rw [h1])
    · exact Or.inr (by rw [h1])
  cases b
  · rcases hKs with h1 | h1
    · right
      show ((memKStar (emb α h)).map (MulAut.conj w).toMonoidHom).map (mkQ n) = memBar α h false
      rw [h1]
      rfl
    · left
      show ((memKStar (emb α h)).map (MulAut.conj w).toMonoidHom).map (mkQ n) = memBar α h true
      rw [h1]
      rfl
  · rcases hK with h1 | h1
    · left
      show ((memK (emb α h)).map (MulAut.conj w).toMonoidHom).map (mkQ n) = memBar α h true
      rw [h1]
      rfl
    · right
      show ((memK (emb α h)).map (MulAut.conj w).toMonoidHom).map (mkQ n) = memBar α h false
      rw [h1]
      rfl

end CFSG.ClassicalInvolution.Q3.TL4.AECov
