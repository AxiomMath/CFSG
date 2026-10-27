module

public import Certificates.Certificate24848
public import Certificates.Certificate24864

public section

namespace CFSG.EvenSporadicStandard.M24Std.Sym6

open CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint

theorem perm_apply_inv (f : Equiv.Perm (Fin 24)) (x : Fin 24) : f (f⁻¹ x) = x :=
  f.apply_symm_apply x

theorem perm_inv_apply (f : Equiv.Perm (Fin 24)) (x : Fin 24) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x

theorem qdNorm_inv {g : S24} (hg : QdNorm g) : QdNorm g⁻¹ := fun s => by
  have h := hg (g⁻¹ * s * g⁻¹⁻¹)
  rw [show g * (g⁻¹ * s * g⁻¹⁻¹) * g⁻¹ = s by group] at h
  exact h.symm

theorem qdNorm_of_mem {x : S24} (hx : x ∈ m24E1l) : QdNorm x := by
  obtain ⟨-, -, -, hmul, hsq, -⟩ := m24_e1_check
  have hinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
  intro s
  rw [hinv]
  refine ⟨fun hs => hmul _ (hmul _ hx _ hs) _ hx, fun hs => ?_⟩
  have e : x * (x * s * x) * x = s := by
    rw [show x * (x * s * x) * x = (x * x) * s * (x * x) by group, hsq x hx]
    group
  rw [← e]
  exact hmul _ (hmul _ hx _ hs) _ hx

theorem qdNorm_qdOmega : QdNorm qdOmega :=
  Certificates.certificate24848.1.norm

theorem swapImg_eq : ∀ i : Fin 6, swapImg i = Equiv.swap (0 : Fin 6) 1 i := by decide

theorem rotImg_eq : ∀ i : Fin 6, rotImg i = finRotate 6 i := by decide

theorem closure_rot_swap :
    Subgroup.closure ({finRotate 6, Equiv.swap 0 1} : Set (Equiv.Perm (Fin 6))) = ⊤ := by
  have h := Equiv.Perm.closure_cycle_adjacent_swap (isCycle_finRotate_of_le (by norm_num : 2 ≤ 6))
    (support_finRotate_of_le (by norm_num)) (0 : Fin 6)
  rwa [show finRotate 6 (0 : Fin 6) = 1 by decide] at h


theorem tetIdx_of_mem {x : S24} (hx : x ∈ m24E1l) (p : Fin 24) :
    tetIdx ((x : Equiv.Perm (Fin 24)) p) = tetIdx p :=
  Certificates.certificate24864.1 x hx p

theorem tetIdx_qdOmega (p : Fin 24) :
    tetIdx ((qdOmega : Equiv.Perm (Fin 24)) p) = tetIdx p :=
  Certificates.certificate24864.2.2.2.1 p

theorem tetIdx_eq_of_norm {g : S24} (hg : QdNorm g) {p q : Fin 24} (hpq : tetIdx p = tetIdx q) :
    tetIdx ((g : Equiv.Perm (Fin 24)) p) = tetIdx ((g : Equiv.Perm (Fin 24)) q) := by
  obtain ⟨hpres, htrans, -⟩ := Certificates.certificate24864
  obtain ⟨x, hx, hxp⟩ := htrans p q hpq
  have e : (g : Equiv.Perm (Fin 24)) q =
      ((g * x * g⁻¹ : S24) : Equiv.Perm (Fin 24)) ((g : Equiv.Perm (Fin 24)) p) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply,
      perm_inv_apply, hxp]
  rw [e, hpres _ ((hg x).1 hx)]

theorem tetIdx_apply_of_norm {g : S24} (hg : QdNorm g) (p : Fin 24) :
    tetIdx ((g : Equiv.Perm (Fin 24)) p) =
      tetIdx ((g : Equiv.Perm (Fin 24)) (tetRep (tetIdx p))) :=
  tetIdx_eq_of_norm hg (tetIdx_tetRep (tetIdx p)).symm

@[expose] def tetAct (g : S24) (hg : QdNorm g) : Equiv.Perm (Fin 6) where
  toFun i := tetIdx ((g : Equiv.Perm (Fin 24)) (tetRep i))
  invFun i := tetIdx (((g⁻¹ : S24) : Equiv.Perm (Fin 24)) (tetRep i))
  left_inv i := by
    show tetIdx (((g⁻¹ : S24) : Equiv.Perm (Fin 24))
      (tetRep (tetIdx ((g : Equiv.Perm (Fin 24)) (tetRep i))))) = i
    rw [← tetIdx_apply_of_norm (qdNorm_inv hg) ((g : Equiv.Perm (Fin 24)) (tetRep i)),
      Subgroup.coe_inv, perm_inv_apply, tetIdx_tetRep]
  right_inv i := by
    show tetIdx ((g : Equiv.Perm (Fin 24))
      (tetRep (tetIdx (((g⁻¹ : S24) : Equiv.Perm (Fin 24)) (tetRep i))))) = i
    rw [← tetIdx_apply_of_norm hg (((g⁻¹ : S24) : Equiv.Perm (Fin 24)) (tetRep i)),
      Subgroup.coe_inv, perm_apply_inv, tetIdx_tetRep]

theorem tetAct_apply {g : S24} (hg : QdNorm g) (i : Fin 6) :
    tetAct g hg i = tetIdx ((g : Equiv.Perm (Fin 24)) (tetRep i)) := rfl

theorem tetAct_tetIdx {g : S24} (hg : QdNorm g) (p : Fin 24) :
    tetAct g hg (tetIdx p) = tetIdx ((g : Equiv.Perm (Fin 24)) p) :=
  (tetIdx_apply_of_norm hg p).symm

theorem tetAct_mul {g h : S24} (hg : QdNorm g) (hh : QdNorm h) :
    tetAct (g * h) (hg.mul hh) = tetAct g hg * tetAct h hh := by
  refine Equiv.ext fun i => ?_
  show tetIdx (((g * h : S24) : Equiv.Perm (Fin 24)) (tetRep i)) =
    tetAct g hg (tetIdx ((h : Equiv.Perm (Fin 24)) (tetRep i)))
  rw [tetAct_tetIdx hg, Subgroup.coe_mul, Equiv.Perm.mul_apply]

theorem tetAct_eq_one_iff {g : S24} (hg : QdNorm g) :
    tetAct g hg = 1 ↔ ∀ p : Fin 24, tetIdx ((g : Equiv.Perm (Fin 24)) p) = tetIdx p := by
  constructor
  · intro h1 p
    rw [← tetAct_tetIdx hg p, h1, Equiv.Perm.one_apply]
  · intro hfix
    refine Equiv.ext fun i => ?_
    rw [tetAct_apply, hfix, tetIdx_tetRep, Equiv.Perm.one_apply]

theorem qdNorm_sxS : QdNorm sxS := Certificates.certificate24864.2.2.2.2.2.1.norm

theorem qdNorm_sxT : QdNorm sxT := Certificates.certificate24864.2.2.2.2.2.2.1.norm

theorem tetAct_sxS : tetAct sxS qdNorm_sxS = Equiv.swap 0 1 := by
  refine Equiv.ext fun i => ?_
  rw [tetAct_apply, Certificates.certificate24864.2.2.2.2.2.2.2.1 i, swapImg_eq]

theorem tetAct_sxT : tetAct sxT qdNorm_sxT = finRotate 6 := by
  refine Equiv.ext fun i => ?_
  rw [tetAct_apply, Certificates.certificate24864.2.2.2.2.2.2.2.2.1 i, rotImg_eq]

end CFSG.EvenSporadicStandard.M24Std.Sym6
