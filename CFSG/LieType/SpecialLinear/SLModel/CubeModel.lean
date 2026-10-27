module

public import CFSG.LieType.SpecialLinear.SLModel.Models
public import CFSG.LieType.SpecialLinear.SLModel.MatrixModel
public import CFSG.LieType.SpecialLinear.PureMiddle.InnerRank
public import CFSG.LieType.SpecialLinear.PureMiddle.CubeBound

public section

open Module Matrix CFSG.LieType.SpecialLinear.ExteriorModel CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar CFSG.HardMathSupport.GuralnickMalle
  CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc CFSG.LieType.SpecialLinear.PureMiddle

namespace CFSG.LieType.SpecialLinear.SLModel

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {k : Type} [Field k] [CharP k 2]
  [Algebra F k] {f : ℕ}

private noncomputable def cubeMat (r₀ : Fin f) :
    SpecialLinearGroup (Fin 6) F → Matrix (Set.powersetCard (Fin 6) 3)
      (Set.powersetCard (Fin 6) 3) F :=
  fun g => (minorMatrix 3 (g : Matrix (Fin 6) (Fin 6) F)).map
    (iterateFrobeniusEquiv F 2 r₀ : F →+* F)

private theorem cubeMat_intertwines (ε : Fin f → Finset (Fin 6)) (r₀ : Fin f)
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (hε : ε r₀ = {3}) :
    ∃ β : BModel k ε ≃ₗ[k] (Set.powersetCard (Fin 6) 3 → k),
      ∀ g v, β (slModelRep (F := F) (k := k) ε g v) =
        (cubeMat (F := F) (f := f) r₀ g).map (algebraMap F k) *ᵥ β v := by
  obtain ⟨β, hβ⟩ := exists_equiv_single (F := F) (k := k) (m := 5) ε (r₀ := r₀)
    (j := (⟨3, by norm_num⟩ : Fin 6)) (by simpa using hε) hε'
  exact ⟨β, fun g v => by simpa [cubeMat] using hβ g v⟩

theorem six_le_finrank_range_slModelRep_cube (ε : Fin f → Finset (Fin 6)) (r₀ : Fin f)
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (hε : ε r₀ = {3})
    {u : SpecialLinearGroup (Fin 6) F} (hu : u * u = 1) (hu1 : u ≠ 1) :
    6 ≤ finrank k (LinearMap.range (slModelRep (F := F) (k := k) ε u - 1)) := by
  classical
  obtain ⟨β, hβ⟩ := cubeMat_intertwines (F := F) (k := k) (f := f) ε r₀ hε' hε
  have hrank := finrank_range_sub_one_eq_rank (F := F) (k := k)
    (σ := slModelRep (F := F) (k := k) ε)
    β (cubeMat (F := F) (f := f) r₀) hβ u
  rw [hrank]
  have hg : (u : Matrix (Fin 6) (Fin 6) F) * (u : Matrix (Fin 6) (Fin 6) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hu, Matrix.SpecialLinearGroup.coe_one]
  have hg1 : (u : Matrix (Fin 6) (Fin 6) F) ≠ 1 := by
    intro h
    apply hu1
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have := congrFun (congrFun h i) j
    simpa using this
  have h6 := six_le_rank_minor_map_sub_one (K := F) (k := F)
    ((iterateFrobeniusEquiv F 2 r₀ : F ≃+* F) : F →+* F)
    (u : Matrix (Fin 6) (Fin 6) F) hg hg1
  rw [show Matrix.of (fun s t : Set.powersetCard (Fin 6) 3 =>
      minor ((u : Matrix (Fin 6) (Fin 6) F).map
        ((iterateFrobeniusEquiv F 2 r₀ : F ≃+* F) : F →+* F)) s t) =
      minorMatrix 3 ((u : Matrix (Fin 6) (Fin 6) F).map
        ((iterateFrobeniusEquiv F 2 r₀ : F ≃+* F) : F →+* F)) from rfl] at h6
  rw [minorMatrix_map] at h6
  simpa [cubeMat] using h6

theorem sixteen_lt_pow_finrank_range_slModelRep_cube (ε : Fin f → Finset (Fin 6)) (r₀ : Fin f)
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (hε : ε r₀ = {3}) {N : ℕ} (hN : 2 ≤ N)
    {u : SpecialLinearGroup (Fin 6) F} (hu : u * u = 1) (hu1 : u ≠ 1) :
    16 < N ^ finrank k (LinearMap.range (slModelRep (F := F) (k := k) ε u - 1)) := by
  have h6 := six_le_finrank_range_slModelRep_cube (k := k) ε r₀ hε' hε hu hu1
  calc 16 < 2 ^ 6 := by norm_num
    _ ≤ 2 ^ finrank k (LinearMap.range (slModelRep (F := F) (k := k) ε u - 1)) :=
        Nat.pow_le_pow_right (by norm_num) h6
    _ ≤ N ^ finrank k (LinearMap.range (slModelRep (F := F) (k := k) ε u - 1)) :=
        Nat.pow_le_pow_left hN _

theorem two_mul_card_lt_pow_codim_slModelRep_cube (hF : Fintype.card F = 2 ^ f)
    (hq : 2 < Fintype.card F) (ε : Fin f → Finset (Fin 6)) (r₀ : Fin f)
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (hε : ε r₀ = {3}) {N : ℕ} (hN : 2 ^ f ≤ N)
    {P : Subgroup (SpecialLinearGroup (Fin 6) F)} (hP1 : P ≠ ⊥) (hP : ∀ a ∈ P, a * a = 1) :
    2 * Nat.card P < N ^ (finrank k (BModel k ε) -
      finrank k (fixSub (slModelRep (F := F) (k := k) ε) P)) := by
  classical
  obtain ⟨β, hβ⟩ := cubeMat_intertwines (F := F) (k := k) (f := f) ε r₀ hε' hε
  have hfixSubGen : fixSub (slModelRep (F := F) (k := k) ε) P =
      fixSubGen (slModelRep (F := F) (k := k) ε) P := rfl
  have hfix := finrank_fixSubGen_eq_finrank_fixF (F := F) (k := k)
    (σ := slModelRep (F := F) (k := k) ε)
    β (cubeMat (F := F) (f := f) r₀) hβ P
  have hPel : CFSG.IsElementaryAbelian 2 P := by
    refine CFSG.IsElementaryAbelian.of_forall (p := 2) (E := P) ?_ ?_
    · intro a ha b hb
      have hab : a * b * (a * b) = 1 := hP _ (P.mul_mem ha hb)
      have hinv : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
      have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hP a ha)
      have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hP b hb)
      calc a * b = (a * b)⁻¹ := hinv.symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = b * a := by rw [ha', hb']
    · intro a ha
      rw [pow_two]
      exact hP a ha
  have hcube := two_mul_card_mul_pow_finrank_fixK_minorMatrix_lt (K := F) (k := k) hq
    (iterateFrobeniusEquiv F 2 r₀) P hP1 hPel
  have hfixK : finrank k (fixK (k := k) (fun a : P => minorMatrix 3
      ((((a : P) : SpecialLinearGroup (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).map
        (iterateFrobeniusEquiv F 2 r₀)))) =
      finrank F (fixF (fun a : P => cubeMat (F := F) (f := f) r₀
        ((a : P) : SpecialLinearGroup (Fin 6) F))) := by
    rw [finrank_fixK]
    have hfun : (fun a : P => minorMatrix 3
        ((((a : P) : SpecialLinearGroup (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).map
          (iterateFrobeniusEquiv F 2 r₀))) =
        fun a : P => cubeMat (F := F) (f := f) r₀
          ((a : P) : SpecialLinearGroup (Fin 6) F) := by
      funext a
      show minorMatrix 3 (((((a : P) : SpecialLinearGroup (Fin 6) F) :
          Matrix (Fin 6) (Fin 6) F)).map (iterateFrobeniusEquiv F 2 r₀)) =
        (minorMatrix 3 (((a : P) : SpecialLinearGroup (Fin 6) F) :
          Matrix (Fin 6) (Fin 6) F)).map (iterateFrobeniusEquiv F 2 r₀)
      simpa only [RingEquiv.coe_toRingHom] using
        (minorMatrix_map (iterateFrobeniusEquiv F 2 r₀ : F →+* F) 3
          (((a : P) : SpecialLinearGroup (Fin 6) F) : Matrix (Fin 6) (Fin 6) F))
    rw [hfun]
  rw [hfixK] at hcube
  have hcube' : 2 * Nat.card P * Fintype.card F ^
      finrank k (fixSubGen (slModelRep (F := F) (k := k) ε) P) < Fintype.card F ^ 20 := by
    rw [hfix]
    exact hcube
  have hdim : finrank k (BModel k ε) = 20 := by
    rw [β.finrank_eq, Module.finrank_fintype_fun_eq_card, card_powersetCard_fin_six_three]
  have hle : finrank k (fixSubGen (slModelRep (F := F) (k := k) ε) P) ≤ 20 := by
    rw [← hdim]
    exact Submodule.finrank_le _
  have hqpow : Fintype.card F ^ 20 = Fintype.card F ^
      finrank k (fixSubGen (slModelRep (F := F) (k := k) ε) P) *
      Fintype.card F ^ (20 - finrank k (fixSubGen
        (slModelRep (F := F) (k := k) ε) P)) := by
    rw [← pow_add, Nat.add_sub_cancel' hle]
  rw [hqpow] at hcube'
  have hkey : 2 * Nat.card P < Fintype.card F ^ (20 -
      finrank k (fixSubGen (slModelRep (F := F) (k := k) ε) P)) := by
    have h := hcube'
    rw [mul_comm (Fintype.card F ^ finrank k
      (fixSubGen (slModelRep (F := F) (k := k) ε) P))] at h
    exact Nat.lt_of_mul_lt_mul_right h
  have hkey' : 2 * Nat.card P < N ^ (finrank k (BModel k ε) -
      finrank k (fixSubGen (slModelRep (F := F) (k := k) ε) P)) := by
    calc 2 * Nat.card P < Fintype.card F ^ (20 -
          finrank k (fixSubGen (slModelRep (F := F) (k := k) ε) P)) := hkey
      _ = (2 ^ f) ^ (finrank k (BModel k ε) - finrank k (fixSubGen
            (slModelRep (F := F) (k := k) ε) P)) := by rw [hF, ← hdim]
      _ ≤ N ^ (finrank k (BModel k ε) - finrank k (fixSubGen
            (slModelRep (F := F) (k := k) ε) P)) := Nat.pow_le_pow_left hN _
  change 2 * Nat.card P < N ^ (finrank k (BModel k ε) -
    finrank k (fixSubGen (slModelRep (F := F) (k := k) ε) P))
  exact hkey'

end CFSG.LieType.SpecialLinear.SLModel
