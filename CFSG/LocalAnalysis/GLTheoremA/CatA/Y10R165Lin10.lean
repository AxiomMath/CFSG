module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin7

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open Matrix CFSG.RankThree.PartTwo.Census

namespace LinEngine

variable {F V : Type} [Field F] [CharP F 2] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {p : ℕ}
variable [Finite (SpecialLinearGroup F V)]

noncomputable def f2BlockMat (m : ℕ) (a : Fin 3 → ZMod 3) :
    Matrix (Fin 2 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Fin m)))
      (Fin 2 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Fin m))) F :=
  fromBlocks (threeCycleMat F ^ (a 0).val) 0 0
    (fromBlocks (threeCycleMat F ^ (a 1).val) 0 0
      (fromBlocks (threeCycleMat F ^ (a 2).val) 0 0 (1 : Matrix (Fin m) (Fin m) F)))

theorem det_f2BlockMat (m : ℕ) (a : Fin 3 → ZMod 3) :
    (f2BlockMat (F := F) m a).det = 1 := by
  rw [f2BlockMat, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁]
  simp [det_pow, det_threeCycleMat]

theorem f2BlockMat_add (m : ℕ) (a a' : Fin 3 → ZMod 3) :
    f2BlockMat (F := F) m (a + a') = f2BlockMat (F := F) m a * f2BlockMat (F := F) m a' := by
  simp only [f2BlockMat, Pi.add_apply, threeCycleMat_pow_val_add, fromBlocks_multiply]
  simp

theorem threeCycleMat_pow_val_injective {x y : ZMod 3}
    (h : threeCycleMat F ^ x.val = threeCycleMat F ^ y.val) : x = y := by
  have h3z : (3 : ZMod 3) = 0 := by decide
  have e1 : x + (3 - y) = x - y := by
    rw [show (3 : ZMod 3) - y = -y by rw [h3z]; abel]
    abel
  have e2 : y + (3 - y) = 0 := by
    rw [show (3 : ZMod 3) - y = -y by rw [h3z]; abel]
    abel
  have hmul : threeCycleMat F ^ (x - y).val = 1 := by
    have h' := congrArg (fun M => M * threeCycleMat F ^ (3 - y).val) h
    rw [← threeCycleMat_pow_val_add, ← threeCycleMat_pow_val_add, e1, e2] at h'
    simpa using h'
  have hz : (threeCycleMat F ^ (x - y).val) 0 1 = 0 := by
    rw [hmul]
    simp
  exact sub_eq_zero.mp (threeCycleMat_pow_val_zero_one hz)

noncomputable def f2BlockHom (m : ℕ) :
    Multiplicative (Fin 3 → ZMod 3) →*
      Matrix.SpecialLinearGroup (Fin 2 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Fin m))) F where
  toFun a := ⟨f2BlockMat (F := F) m a.toAdd, det_f2BlockMat m a.toAdd⟩
  map_one' := by
    apply Subtype.ext
    change f2BlockMat (F := F) m 0 = 1
    simp [f2BlockMat, fromBlocks_one]
  map_mul' a b := by
    apply Subtype.ext
    change f2BlockMat (F := F) m (a.toAdd + b.toAdd) =
      f2BlockMat (F := F) m a.toAdd * f2BlockMat (F := F) m b.toAdd
    rw [f2BlockMat_add]

theorem f2BlockHom_injective (m : ℕ) : Function.Injective (f2BlockHom (F := F) m) := by
  intro a b hab
  have h1 : f2BlockMat (F := F) m a.toAdd = f2BlockMat (F := F) m b.toAdd :=
    congrArg Subtype.val hab
  have hk : ∀ k : Fin 3, a.toAdd k = b.toAdd k := by
    intro k
    apply threeCycleMat_pow_val_injective (F := F)
    fin_cases k
    · ext i j
      have := congrFun (congrFun h1 (Sum.inl i)) (Sum.inl j)
      simpa [f2BlockMat, fromBlocks_apply₁₁] using this
    · ext i j
      have := congrFun (congrFun h1 (Sum.inr (Sum.inl i))) (Sum.inr (Sum.inl j))
      simpa [f2BlockMat, fromBlocks_apply₂₂, fromBlocks_apply₁₁] using this
    · ext i j
      have := congrFun (congrFun h1 (Sum.inr (Sum.inr (Sum.inl i))))
        (Sum.inr (Sum.inr (Sum.inl j)))
      simpa [f2BlockMat, fromBlocks_apply₂₂, fromBlocks_apply₁₁] using this
  exact Multiplicative.toAdd.injective (funext hk)

theorem pow_three_multiplicative_fin_three (u : Multiplicative (Fin 3 → ZMod 3)) : u ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext k
  show (3 : ℕ) • u.toAdd k = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem isElemAbelian_range_f2BlockHom (m : ℕ) :
    IsElemAbelian 3 (f2BlockHom (F := F) m).range := by
  rw [← Subgroup.map_top (f2BlockHom (F := F) m)]
  refine CFSG.SectionRank.isElemAbelian_map (p := 3) ?_ (f2BlockHom (F := F) m)
  exact ⟨⟨⟨fun a b => mul_comm' a b⟩⟩, fun x _ => pow_three_multiplicative_fin_three x⟩

theorem card_range_f2BlockHom (m : ℕ) :
    Nat.card ↥(f2BlockHom (F := F) m).range = 3 ^ 3 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (f2BlockHom_injective m)).toEquiv]
  simp [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem three_le_pRank_range_f2BlockHom [Finite F] (m : ℕ) :
    3 ≤ CFSG.Open.pRank 3 (f2BlockHom (F := F) m).range :=
  CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl
    (isElemAbelian_range_f2BlockHom m) (card_range_f2BlockHom m)

noncomputable def sixBlockEquiv (k : ℕ) (hk : 6 ≤ k) :
    Fin k ≃ Fin 2 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Fin (k - 6))) := by
  have h1 : 2 + (2 + (2 + (k - 6))) = k := by omega
  have eA : Fin 2 ⊕ (Fin 2 ⊕ Fin (k - 6)) ≃ Fin (2 + (2 + (k - 6))) :=
    (Equiv.sumCongr (Equiv.refl (Fin 2)) finSumFinEquiv).trans finSumFinEquiv
  have eB : Fin 2 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Fin (k - 6))) ≃
      Fin (2 + (2 + (2 + (k - 6)))) :=
    (Equiv.sumCongr (Equiv.refl (Fin 2)) eA).trans finSumFinEquiv
  exact (eB.trans (finCongr h1)).symm


theorem exists_elemAbelian_three_Jsub_of_f2 [Fintype F]
    (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (D : HypBlocks.Hyperplane A p)
    (hdim : 6 ≤ Module.finrank F
      ↥(HypBlocks.fixedByEnd (HypBlocks.blockEnd A hp hpF hA t ht D))) :
    ∃ Q : Subgroup (SpecialLinearGroup F V),
      Q ≤ Jsub A hp hpF hA t ht D ∧ IsElemAbelian 3 Q ∧ 3 ≤ CFSG.Open.pRank 3 Q := by
  classical
  let W : Submodule F V := HypBlocks.fixedByEnd (HypBlocks.blockEnd A hp hpF hA t ht D)
  have hK : 6 ≤ Module.finrank F W := hdim
  let b : Module.Basis (Fin 2 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Fin (Module.finrank F W - 6)))) F W :=
    (Module.finBasis F W).reindex (sixBlockEquiv (Module.finrank F W) hK)
  let e₁ : Matrix.SpecialLinearGroup
      (Fin 2 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Fin (Module.finrank F W - 6)))) F ≃*
      SpecialLinearGroup F W := Matrix.SpecialLinearGroup.toLin_equiv b
  let e₂ : ↥(Jsub A hp hpF hA t ht D) ≃* SpecialLinearGroup F W :=
    JsubEquiv A hp hpF hA t ht D
  let ψ : Matrix.SpecialLinearGroup
      (Fin 2 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Fin (Module.finrank F W - 6)))) F →*
      ↥(Jsub A hp hpF hA t ht D) := e₂.symm.toMonoidHom.comp e₁.toMonoidHom
  let Φ : Matrix.SpecialLinearGroup
      (Fin 2 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Fin (Module.finrank F W - 6)))) F →*
      SpecialLinearGroup F V := (Jsub A hp hpF hA t ht D).subtype.comp ψ
  refine ⟨(f2BlockHom (F := F) (Module.finrank F W - 6)).range.map Φ, ?_, ?_, ?_⟩
  · rintro x ⟨y, -, rfl⟩
    exact (ψ y).2
  · exact CFSG.SectionRank.isElemAbelian_map (isElemAbelian_range_f2BlockHom _) Φ
  · have hfinj : Function.Injective Φ := by
      intro x y hxy
      have h1 : ψ x = ψ y := Subtype.ext hxy
      have h2 : e₁ x = e₁ y := e₂.symm.injective h1
      exact e₁.injective h2
    have hrank := CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective
      (G := SpecialLinearGroup F V) (p := 3) (by norm_num) Φ hfinj
      (f2BlockHom (F := F) (Module.finrank F W - 6)).range
    rw [hrank]
    exact three_le_pRank_range_f2BlockHom (Module.finrank F W - 6)

end LinEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F

