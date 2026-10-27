module

public import CFSG.LieType.SpecialLinear.Block222.Borel.Blocks

public section

namespace CFSG.LieType.SpecialLinear

open Matrix

noncomputable section

variable (c : ℕ) (F : Type) [Field F]

@[expose] def tripleCongr {G₁ G₂ G₃ G₁' G₂' G₃' : Type*} [Group G₁] [Group G₂] [Group G₃]
    [Group G₁'] [Group G₂'] [Group G₃'] (e₁ : G₁ ≃* G₁') (e₂ : G₂ ≃* G₂') (e₃ : G₃ ≃* G₃') :
    (G₁ × G₂ × G₃) ≃* (G₁' × G₂' × G₃') where
  toFun x := (e₁ x.1, e₂ x.2.1, e₃ x.2.2)
  invFun x := (e₁.symm x.1, e₂.symm x.2.1, e₃.symm x.2.2)
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by
    apply Prod.ext
    · exact map_mul e₁ x.1 y.1
    · apply Prod.ext
      · exact map_mul e₂ x.2.1 y.2.1
      · exact map_mul e₃ x.2.2 y.2.2

@[expose] def tripleSwap {G H : Type*} [Group G] [Group H] :
    (G × H × G) ≃* (G × H × G) where
  toFun x := (x.2.2, x.2.1, x.1)
  invFun x := (x.2.2, x.2.1, x.1)
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> rfl

variable (A : GL (Fin (c + 4)) F) (hA : IsUpperGL A) (σ : F ≃+* F)

abbrev BlockLevi222 := SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin c) F ×
  SpecialLinearGroup (Fin 2) F

@[expose] def blockStd222Even : BlockLevi222 c F ≃* BlockLevi222 c F :=
  tripleCongr (CFSG.QuasithinUnique.K1.stdAut (blockGL1 c F A hA) σ 0)
    (CFSG.QuasithinUnique.K1.stdAut (blockGL2 c F A hA) σ 0)
    (CFSG.QuasithinUnique.K1.stdAut (blockGL3 c F A hA) σ 0)

@[expose] def blockStd222Odd : BlockLevi222 c F ≃* BlockLevi222 c F :=
  (tripleCongr (borelGraph 2 F) (borelGraph c F) (borelGraph 2 F)).trans
    ((tripleSwap.trans (tripleCongr
      (CFSG.QuasithinUnique.K1.stdAut (blockGL1 c F A hA) σ 0)
      (CFSG.QuasithinUnique.K1.stdAut (blockGL2 c F A hA) σ 0)
      (CFSG.QuasithinUnique.K1.stdAut (blockGL3 c F A hA) σ 0))))

@[expose] def blockStd222 (ε : ℕ) : BlockLevi222 c F ≃* BlockLevi222 c F :=
  if ε % 2 = 0 then blockStd222Even c F A hA σ else blockStd222Odd c F A hA σ

@[simp] theorem blockStd222_apply_even {ε : ℕ} (hε : ε % 2 = 0) (g : BlockLevi222 c F) :
    blockStd222 c F A hA σ ε g = blockStd222Even c F A hA σ g := by
  rw [blockStd222, if_pos hε]

@[simp] theorem blockStd222_apply_odd {ε : ℕ} (hε : ε % 2 = 1) (g : BlockLevi222 c F) :
    blockStd222 c F A hA σ ε g = blockStd222Odd c F A hA σ g := by
  rw [blockStd222, if_neg (by omega)]

theorem blockStd222Even_apply (g : BlockLevi222 c F) :
    blockStd222Even c F A hA σ g =
      (CFSG.QuasithinUnique.K1.stdAut (blockGL1 c F A hA) σ 0 g.1,
        CFSG.QuasithinUnique.K1.stdAut (blockGL2 c F A hA) σ 0 g.2.1,
        CFSG.QuasithinUnique.K1.stdAut (blockGL3 c F A hA) σ 0 g.2.2) := rfl

theorem blockStd222Odd_apply (g : BlockLevi222 c F) :
    blockStd222Odd c F A hA σ g =
      (CFSG.QuasithinUnique.K1.stdAut (blockGL1 c F A hA) σ 0 (borelGraph 2 F g.2.2),
        CFSG.QuasithinUnique.K1.stdAut (blockGL2 c F A hA) σ 0 (borelGraph c F g.2.1),
        CFSG.QuasithinUnique.K1.stdAut (blockGL3 c F A hA) σ 0 (borelGraph 2 F g.1)) := by
  simp [blockStd222Odd, tripleCongr, tripleSwap, MulEquiv.trans_apply]

end

end CFSG.LieType.SpecialLinear
