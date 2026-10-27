module

public import CFSG.ClassicalInvolution.Q3.TL4AECoverA
public import CFSG.ClassicalInvolution.Q3.TL4D1MAMA

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AECov

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

theorem kList_conj_vec_odd : ∀ u : Fin 4 → ZMod 2, u 0 + u 1 + u 2 + u 3 = 1 →
    (∀ a ∈ kList, ofVec u * a * (ofVec u)⁻¹ ∈ kStarList) ∧
      ∀ a ∈ kStarList, ofVec u * a * (ofVec u)⁻¹ ∈ kList := by
  decide +kernel

theorem univ_map_emb (α : Finset (Fin n)) (h : α.card = 4) :
    (Finset.univ : Finset (Fin 4)).map (emb α h) = α := by
  apply Finset.coe_injective
  rw [Finset.coe_map, Finset.coe_univ, Set.image_univ, range_emb]

theorem sum_emb (α : Finset (Fin n)) (h : α.card = 4) (f : Fin n → ZMod 2) :
    f (emb α h 0) + f (emb α h 1) + f (emb α h 2) + f (emb α h 3) = ∑ x ∈ α, f x := by
  have e : ∑ x ∈ (Finset.univ : Finset (Fin 4)).map (emb α h), f x = ∑ x ∈ α, f x := by
    rw [univ_map_emb α h]
  rw [← e, Finset.sum_map, Fin.sum_univ_four]

theorem conjSub_memBar_of_odd {w : Wr n} (hw : w.perm = 1) (α : Finset (Fin n)) (h : α.card = 4)
    (b : Bool) (hodd : ∑ x ∈ α, w.vec x = 1) :
    conjSub (mkQ n w) (memBar α h b) = memBar α h (!b) := by
  have hmk : conjSub (mkQ n w) (memBar α h b) =
      ((memAt α h b).map (MulAut.conj w).toMonoidHom).map (mkQ n) := by
    show ((memAt α h b).map (mkQ n)).map (MulAut.conj (mkQ n w)).toMonoidHom = _
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [hmk]
  set u : Fin 4 → ZMod 2 := fun i => w.vec (emb α h i) with hu
  have hsum : u 0 + u 1 + u 2 + u 3 = 1 := by
    rw [← hodd, ← sum_emb α h w.vec]
  obtain ⟨h1, h2⟩ := kList_conj_vec_odd u hsum
  have hK : kQ.map (MulAut.conj (ofVec u)).toMonoidHom = kQStar := map_conj_ofVec_eq u h1 h2
  have hKs : kQStar.map (MulAut.conj (ofVec u)).toMonoidHom = kQ := map_conj_ofVec_eq u h2 h1
  cases b
  · show ((memKStar (emb α h)).map (MulAut.conj w).toMonoidHom).map (mkQ n) = memBar α h true
    unfold memKStar
    rw [map_embed_conj _ hw, hKs]
    rfl
  · show ((memK (emb α h)).map (MulAut.conj w).toMonoidHom).map (mkQ n) = memBar α h false
    unfold memK
    rw [map_embed_conj _ hw, hK]
    rfl

theorem sum_pairVec_of_mem {γ : Finset (Fin n)} {a c : Fin n} (ha : a ∈ γ) (hc : c ∉ γ) :
    ∑ x ∈ γ, pairVec a c x = 1 := by
  classical
  have hac : a ≠ c := fun e => hc (e ▸ ha)
  rw [Finset.sum_eq_single a]
  · rw [pairVec_apply]
    simp [hac]
  · intro x hx hxa
    have hxc : x ≠ c := fun e => hc (e ▸ hx)
    rw [pairVec_apply]
    simp [hxa, hxc]
  · intro h'
    exact absurd ha h'

end CFSG.ClassicalInvolution.Q3.TL4.AECov

