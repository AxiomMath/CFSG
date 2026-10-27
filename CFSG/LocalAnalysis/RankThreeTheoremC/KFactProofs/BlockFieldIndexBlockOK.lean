module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28LinTorus
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexLeviGeneric

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime Matrix
open CFSG.RankThree.PartOne.OutStructure (exists_pow_eq_of_pow_eq)
open scoped commutatorElement

section ElemNine

variable {F : Type} [Field F]

theorem linTorus_injective {r n : ℕ} (hn : r + 1 ≤ n) :
    Function.Injective (linTorus F r hn) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  funext j
  have h1 := congrArg (fun A : SpecialLinearGroup (Fin n) F =>
    (A : Matrix (Fin n) (Fin n) F) ⟨j, by omega⟩ ⟨j, by omega⟩) ht
  simp only [coe_linTorus, diagonal_apply_eq, SpecialLinearGroup.coe_one, one_apply_eq] at h1
  have h2 : (linTorusVec t (⟨j, by omega⟩ : Fin n) : F) = (t j : F) := by
    simp [linTorusVec, j.isLt]
  rw [h2] at h1
  exact Units.ext (h1.trans (by simp))

theorem exists_elemAbelian_nine_sl [Finite F] {m : ℕ} (hm : 3 ≤ m) (h3 : 3 ∣ Nat.card Fˣ) :
    ∃ E : Subgroup (GL (Fin m) F),
      E ≤ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) F →* GL (Fin m) F).range ∧
        IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3
  set C : Subgroup Fˣ := Subgroup.zpowers ω with hC
  have hCcard : Nat.card C = 3 := by rw [hC, Nat.card_zpowers, hω]
  have hC3 : ∀ x : C, x ^ 3 = 1 := fun x => by
    have := pow_card_eq_one' (G := C) (x := x)
    rwa [hCcard] at this
  let f : (Fin 2 → C) →* SpecialLinearGroup (Fin m) F :=
    (linTorus F 2 (by omega)).comp (Pi.monoidHom fun i => C.subtype.comp (Pi.evalMonoidHom _ i))
  have hfinj : Function.Injective f := by
    refine (linTorus_injective (by omega)).comp ?_
    intro a b hab
    funext i
    exact Subtype.ext (congrFun hab i)
  let f' : (Fin 2 → C) →* GL (Fin m) F := SpecialLinearGroup.toGL.comp f
  have hf'inj : Function.Injective f' :=
    SpecialLinearGroup.toGL_injective.comp hfinj
  refine ⟨f'.range, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨f x, rfl⟩
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨z, hz⟩ := b.2
      apply Subtype.ext
      change (a : GL (Fin m) F) * b = b * a
      rw [← hx, ← hz, ← map_mul, ← map_mul, mul_comm x z]
    · obtain ⟨x, rfl⟩ := hy
      rw [← map_pow]
      have : x ^ 3 = 1 := by
        funext i
        simp only [Pi.pow_apply, Pi.one_apply]
        exact hC3 (x i)
      rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf'inj).toEquiv, Nat.card_fun, hCcard,
      Nat.card_fin]
    norm_num

end ElemNine

section GLSL

variable {F : Type} [Field F] [Finite F]

theorem scalar_mul_comm {m : ℕ} (u : Fˣ) (x : GL (Fin m) F) :
    GeneralLinearGroup.scalar (Fin m) u * x = x * GeneralLinearGroup.scalar (Fin m) u := by
  apply Units.ext
  simp only [Units.val_mul]
  exact (Matrix.scalar_commute (u : F) (fun r => Commute.all _ _) _).eq

theorem blockOK_gl_sl (m : ℕ) (hm : 2 ≤ m) :
    BlockOK (⊤ : Subgroup (GL (Fin m) F))
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) F →* GL (Fin m) F).range := by
  classical
  intro g _ hn k hk
  by_cases hdiv : 3 ∣ Nat.gcd m (Nat.card Fˣ)
  · right
    have h3c : 3 ∣ Nat.card Fˣ := hdiv.trans (Nat.gcd_dvd_right _ _)
    have h3m : 3 ∣ m := hdiv.trans (Nat.gcd_dvd_left _ _)
    exact exists_elemAbelian_nine_sl (by have := Nat.le_of_dvd (by omega) h3m; omega) h3c
  · left
    have hcomm : ∀ τ : TransvectionStruct (Fin m) F,
        Commute τ.toMatrix ((g ^ (3 ^ k) : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by
      intro τ
      have hmem : (SpecialLinearGroup.toGL (SpecialLinearGroup.transvection τ.hij τ.c) :
          GL (Fin m) F) ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) F →*
            GL (Fin m) F).range := ⟨_, rfl⟩
      have h1 := hk _ hmem
      have h2 : (g ^ (3 ^ k)) * SpecialLinearGroup.toGL (SpecialLinearGroup.transvection τ.hij τ.c)
          = SpecialLinearGroup.toGL (SpecialLinearGroup.transvection τ.hij τ.c) * (g ^ (3 ^ k)) :=
        by rw [mul_inv_eq_iff_eq_mul] at h1; exact h1.symm.symm
      have h3 := congrArg (fun x : GL (Fin m) F => (x : Matrix (Fin m) (Fin m) F)) h2
      simp only [Units.val_mul] at h3
      exact h3.symm
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct hcomm
    have hdet : (GeneralLinearGroup.det (g ^ (3 ^ k)) : F) = c ^ m := by
      have : ((g ^ (3 ^ k) : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = Matrix.scalar (Fin m) c :=
        hc.symm
      rw [GeneralLinearGroup.val_det_apply, this, Matrix.scalar_apply, Matrix.det_diagonal,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hc0 : c ≠ 0 := by
      intro h0
      have h1 := (GeneralLinearGroup.det (g ^ (3 ^ k))).ne_zero
      rw [hdet, h0, zero_pow (by omega)] at h1
      exact h1 rfl
    set u : Fˣ := Units.mk0 c hc0 with hu
    have hpow : (GeneralLinearGroup.det g) ^ (3 ^ k) = u ^ m := by
      calc (GeneralLinearGroup.det g) ^ (3 ^ k) = GeneralLinearGroup.det (g ^ (3 ^ k)) :=
            (map_pow _ _ _).symm
        _ = u ^ m := Units.ext (by rw [hdet, Units.val_pow_eq_pow_val]; rfl)
    obtain ⟨μ, hμ⟩ := exists_pow_eq_of_pow_eq Nat.prime_three hdiv hpow
    set p : GL (Fin m) F := GeneralLinearGroup.scalar (Fin m) μ⁻¹ * g with hp
    have hdetp : GeneralLinearGroup.det p = 1 := by
      rw [hp, map_mul]
      have : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin m) μ⁻¹) = (μ⁻¹) ^ m := by
        apply Units.ext
        rw [GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val]
        simp [GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.det_diagonal]
      rw [this, inv_pow, hμ, inv_mul_cancel]
    have hpS : p ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) F →* GL (Fin m) F).range
      := by
      rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
      exact hdetp
    refine ⟨p, hpS, fun s _ => ?_⟩
    have hg : g = GeneralLinearGroup.scalar (Fin m) μ * p := by
      rw [hp, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    have hc' := scalar_mul_comm μ (p * s * p⁻¹)
    calc g * s * g⁻¹ = GeneralLinearGroup.scalar (Fin m) μ * (p * s * p⁻¹) *
          (GeneralLinearGroup.scalar (Fin m) μ)⁻¹ := by rw [hg]; group
      _ = p * s * p⁻¹ := by rw [hc']; group

end GLSL

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
