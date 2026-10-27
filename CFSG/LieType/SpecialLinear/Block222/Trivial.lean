module

public import CFSG.LieType.SpecialLinear.Block222.Basic
public import CFSG.LieType.SpecialLinear.CurtisDatum

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.SpecialLinear
  CFSG.LieType.RootSystem CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open scoped MatrixGroups

noncomputable section

variable (c : ℕ) (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

@[expose] noncomputable def leftHom222 :
    SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F ×
      SpecialLinearGroup (Fin c) F × SpecialLinearGroup (Fin 2) F where
  toFun g := (g, 1, 1)
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

@[expose] noncomputable def rightHom222 :
    SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F ×
      SpecialLinearGroup (Fin c) F × SpecialLinearGroup (Fin 2) F where
  toFun g := (1, 1, g)
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

theorem blockEmbed222_rankOne_x_left (x : F) :
    blockEmbed222 c F ((rankOne 1 F p).x (0 : Fin 1) x, 1, 1) =
      (rankOne (c + 3) F p).x (⟨0, by omega⟩ : Fin (c + 3)) x := by
  have h := blockEmbed222_transvection_left (c := c) (F := F)
    (hij := (Fin.castSucc_lt_succ (i := (0 : Fin 1))).ne) x
  change blockEmbed222 c F
      (SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := (0 : Fin 1))).ne) x,
        1, 1) = _
  rw [h]
  rw [show (rankOne (c + 3) F p).x (⟨0, by omega⟩ : Fin (c + 3)) x =
    SpecialLinearGroup.transvection
      ((Fin.castSucc_lt_succ (i := (⟨0, by omega⟩ : Fin (c + 3)))).ne) x from rfl]
  have hi : (e222 c) (Sum.inl (Fin.castSucc (0 : Fin 1))) =
      ((⟨0, by omega⟩ : Fin (c + 3)).castSucc) :=
    Fin.ext (by simp [e222_inl])
  have hj : (e222 c) (Sum.inl (Fin.succ (0 : Fin 1))) =
      ((⟨0, by omega⟩ : Fin (c + 3)).succ) :=
    Fin.ext (by simp [e222_inl])
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
    hi, hj]

theorem blockEmbed222_rankOne_x_right (x : F) :
    blockEmbed222 c F (1, 1, (rankOne 1 F p).x (0 : Fin 1) x) =
      (rankOne (c + 3) F p).x (⟨c + 2, by omega⟩ : Fin (c + 3)) x := by
  have h := blockEmbed222_transvection_right (c := c) (F := F)
    (hij := (Fin.castSucc_lt_succ (i := (0 : Fin 1))).ne) x
  change blockEmbed222 c F
      (1, 1, SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := (0 : Fin 1))).ne) x) = _
  rw [h]
  rw [show (rankOne (c + 3) F p).x (⟨c + 2, by omega⟩ : Fin (c + 3)) x =
    SpecialLinearGroup.transvection
      ((Fin.castSucc_lt_succ (i := (⟨c + 2, by omega⟩ : Fin (c + 3)))).ne) x from rfl]
  have hi : (e222 c) (Sum.inr (Sum.inr (Fin.castSucc (0 : Fin 1)))) =
      ((⟨c + 2, by omega⟩ : Fin (c + 3)).castSucc) :=
    Fin.ext (by simp [e222_inr_inr])
  have hj : (e222 c) (Sum.inr (Sum.inr (Fin.succ (0 : Fin 1)))) =
      ((⟨c + 2, by omega⟩ : Fin (c + 3)).succ) :=
    Fin.ext (by simp [e222_inr_inr])
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
    hi, hj]

omit [Fact (Nat.Prime p)] in
theorem blockEmbed222_n_left :
    blockEmbed222 c F ((curtisDatum 1 F p).n (0 : Fin 1), 1, 1) =
      (curtisDatum (c + 3) F p).n (⟨0, by omega⟩ : Fin (c + 3)) :=
  blockEmbed222_weylRep_left c F

omit [Fact (Nat.Prime p)] in
theorem blockEmbed222_n_right :
    blockEmbed222 c F (1, 1, (curtisDatum 1 F p).n (0 : Fin 1)) =
      (curtisDatum (c + 3) F p).n (⟨c + 2, by omega⟩ : Fin (c + 3)) :=
  blockEmbed222_weylRep_right c F

theorem heckeT_comp_of {m n : ℕ} (φ : SpecialLinearGroup (Fin (m + 1)) F →*
    SpecialLinearGroup (Fin (n + 1)) F) (ι : Fin m → Fin n)
    (hx : ∀ (s : Fin m) (x : F),
      φ ((rankOne m F p).x s x) = (rankOne n F p).x (ι s) x)
    (hn : ∀ s : Fin m,
      φ ((curtisDatum m F p).n s) = (curtisDatum n F p).n (ι s))
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (n + 1)) F) V) (s : Fin m) (v : V) :
    (curtisDatum m F p).heckeT (ρ.comp φ) s v =
      (curtisDatum n F p).heckeT ρ (ι s) v := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype ↥((curtisDatum m F p).X s) := Fintype.ofFinite _
  let : Fintype ↥((curtisDatum n F p).X (ι s)) := Fintype.ofFinite _
  rw [CurtisDatum.heckeT_apply, CurtisDatum.heckeT_apply]
  change (∑ x : ↥((curtisDatum m F p).X s),
      ρ (φ ((x : SpecialLinearGroup (Fin (m + 1)) F) * (curtisDatum m F p).n s)) v) =
    ∑ y : ↥((curtisDatum n F p).X (ι s)),
      ρ ((y : SpecialLinearGroup (Fin (n + 1)) F) * (curtisDatum n F p).n (ι s)) v
  have hn_small : (coverId m F p).nhat s = (curtisDatum m F p).n s := by
    rw [CentralCoverData.nhat]
    have h := (coverId m F p).map_nhatW ((curtisCoxeterSystem m).simple s)
    simp only [MonoidHom.id_apply] at h
    rw [h, CentralCoverData.nW_simple]
  have hn_big : (coverId n F p).nhat (ι s) = (curtisDatum n F p).n (ι s) := by
    rw [CentralCoverData.nhat]
    have h := (coverId n F p).map_nhatW ((curtisCoxeterSystem n).simple (ι s))
    simp only [MonoidHom.id_apply] at h
    rw [h, CentralCoverData.nW_simple]
  let es : F ≃ ↥((curtisDatum m F p).X s) :=
    ((rankOne m F p).xEquiv s).trans ((coverId m F p).lXEquiv s)
  let eb : F ≃ ↥((curtisDatum n F p).X (ι s)) :=
    ((rankOne n F p).xEquiv (ι s)).trans ((coverId n F p).lXEquiv (ι s))
  have hsmall : (∑ x : ↥((curtisDatum m F p).X s),
      ρ (φ ((x : SpecialLinearGroup (Fin (m + 1)) F) * (curtisDatum m F p).n s)) v) =
      ∑ x : F, ρ (φ (((rankOne m F p).x s x) *
        (coverId m F p).nhat s)) v := by
    refine (Fintype.sum_equiv es _ _ ?_).symm
    intro x
    rw [hn_small]
    rfl
  have hbig : (∑ x : F, ρ (((rankOne n F p).x (ι s) x) *
        (coverId n F p).nhat (ι s)) v) =
      ∑ y : ↥((curtisDatum n F p).X (ι s)),
        ρ ((y : SpecialLinearGroup (Fin (n + 1)) F) * (curtisDatum n F p).n (ι s)) v := by
    refine Fintype.sum_equiv eb _ _ ?_
    intro x
    rw [hn_big]
    rfl
  rw [hsmall, ← hbig]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hn_small, hn_big, map_mul, hx s x, hn s]

end

end CFSG.LieType.SpecialLinear
