module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisSplitBlocks
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisAbs
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisDim
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisOneAdd

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.RankThree.PartOne.KCLinPlane CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.Classical

variable {n p : ℕ} {F : Type} [Field F]

theorem toLin'_pow_scalar {T : GL (Fin n) F} {c : Fˣ} {p : ℕ}
    (hT : T ^ p = GeneralLinearGroup.scalar (Fin n) c) :
    Matrix.toLin' (T : Matrix (Fin n) (Fin n) F) ^ p = (c : F) • (1 : Module.End F (Fin n → F)) := by
  rw [← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val, hT]
  ext v i
  by_cases hi : i = v <;> simp [Matrix.toLin'_apply, hi]

theorem toLin'_inv_mul {T : GL (Fin n) F} :
    Matrix.toLin' (T : Matrix (Fin n) (Fin n) F) * Matrix.toLin' ((T⁻¹ : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = 1 := by
  rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.toLin'_one]
  rfl

theorem toLin'_inv_mul' {T : GL (Fin n) F} :
    Matrix.toLin' ((T⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      Matrix.toLin' (T : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.toLin'_one]
  rfl

theorem heis_eq_top [Finite F] (hp : p.Prime) (hp2 : p ≠ 2) {ω : F}
    (hω : IsPrimitiveRoot ω p) (hpF : (p : F) ≠ 0) (hF4 : 3 < Nat.card F)
    (hn : 0 < n) (hnp : n ≠ p) {S T : GL (Fin n) F} {c : Fˣ}
    (hS : S ^ p = 1) (hT : T ^ p = GeneralLinearGroup.scalar (Fin n) c)
    (hST : Matrix.toLin' (S : Matrix (Fin n) (Fin n) F) *
        Matrix.toLin' (T : Matrix (Fin n) (Fin n) F) =
      ω • (Matrix.toLin' (T : Matrix (Fin n) (Fin n) F) *
        Matrix.toLin' (S : Matrix (Fin n) (Fin n) F)))
    (𝒢 : Subgroup (SpecialLinearGroup (Fin n) F))
    (hSb : ∀ (hsq : Squarefree (minpoly F (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F))))
      (h : primaryFactors (Matrix.toLin' (S : Matrix (Fin n) (Fin n) F))), GoodBlock h →
      blockImage hsq h ≤ 𝒢.map SpecialLinearGroup.toGL)
    (hTb : ∀ (hsq : Squarefree (minpoly F (Matrix.toLin' (T : Matrix (Fin n) (Fin n) F))))
      (h : primaryFactors (Matrix.toLin' (T : Matrix (Fin n) (Fin n) F))), GoodBlock h →
      blockImage hsq h ≤ 𝒢.map SpecialLinearGroup.toGL) :
    𝒢 = ⊤ := by
  classical
  haveI hfact : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set s : Module.End F (Fin n → F) := Matrix.toLin' (S : Matrix (Fin n) (Fin n) F) with hsdef
  set t : Module.End F (Fin n → F) := Matrix.toLin' (T : Matrix (Fin n) (Fin n) F) with htdef
  set ti : Module.End F (Fin n → F) :=
    Matrix.toLin' ((T⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with htidef
  have hs : s ^ p = 1 := toLin'_pow_eq_one hS
  have ht : t ^ p = (c : F) • (1 : Module.End F (Fin n → F)) := toLin'_pow_scalar hT
  have htti : t * ti = 1 := toLin'_inv_mul
  have hti_t : ti * t = 1 := toLin'_inv_mul'
  set ψ : AddChar (ZMod p) F := AddChar.zmodChar p hω.pow_eq_one with hψdef
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root p hω
  have hψ1 : ψ 1 = ω := by rw [hψdef, AddChar.zmodChar_apply, ZMod.val_one, pow_one]
  have H : HeisData p (eigProj ψ s) t ti (c : F) :=
    heisData_of_split hψ hs hpF (by rw [hψ1]; exact hST) htti hti_t ht
  have hfin : finrank F (Fin n → F) = n := Module.finrank_fin_fun F
  have hd := H.finrank_eq_mul
  rw [hfin] at hd
  set d := finrank F (LinearMap.range (eigProj ψ s 0)) with hddef
  have hd2 : 2 ≤ d := by
    by_contra hlt
    have : d = 0 ∨ d = 1 := by omega
    rcases this with h0 | h1
    · rw [h0] at hd; omega
    · rw [h1] at hd; exact hnp (by omega)
  have hdimS : ∀ j, 2 ≤ finrank F (LinearMap.range (eigProj ψ s j)) := fun j => by
    rw [H.finrank_range j]; exact hd2
  have hsqS : Squarefree (minpoly F s) := squarefree_minpoly_of_pow_eq_one hpF hs
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  have hsqT : Squarefree (minpoly F t) :=
    squarefree_minpoly_of_aeval_eq_zero (separable_X_pow_sub_C (c : F) hpF hc0).squarefree
      (aeval_X_pow_sub_C_eq_zero hT)
  have hax1 : (1 : F)⁻¹ • s = s := by simp
  have goodS : ∀ h : primaryFactors s, GoodBlock h := fun h =>
    goodBlock_split (x := s) (e := 1) hax1 hpF one_ne_zero hψ hs hsqS hdimS hF4 h
  have hSblocks : ∀ h : primaryFactors s, blockImage hsqS h ≤ 𝒢.map SpecialLinearGroup.toGL :=
    fun h => hSb hsqS h (goodS h)
  have goodT : ∀ h : primaryFactors t, GoodBlock h := by
    by_cases hcp : ∃ e : F, e ^ p = c
    · obtain ⟨e, he⟩ := hcp
      have he0 : e ≠ 0 := by
        rintro rfl
        rw [zero_pow hp.ne_zero] at he
        exact hc0 he.symm
      have ht' : (e⁻¹ • t) ^ p = 1 := by
        rw [_root_.smul_pow, ht, smul_smul, inv_pow, he, inv_mul_cancel₀ hc0, one_smul]
      have hω' : IsPrimitiveRoot ω⁻¹ p := hω.inv
      set ψ' : AddChar (ZMod p) F := AddChar.zmodChar p hω'.pow_eq_one with hψ'def
      have hψ' : ψ'.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root p hω'
      have hψ'1 : ψ' 1 = ω⁻¹ := by rw [hψ'def, AddChar.zmodChar_apply, ZMod.val_one, pow_one]
      set si : Module.End F (Fin n → F) :=
        Matrix.toLin' ((S⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hsidef
      have hs_si : s * si = 1 := toLin'_inv_mul
      have hsi_s : si * s = 1 := toLin'_inv_mul'
      have hω0 : ω ≠ 0 := hω.ne_zero hp.ne_zero
      have hab' : (e⁻¹ • t) * s = ψ' 1 • (s * (e⁻¹ • t)) := by
        rw [hψ'1, smul_mul_assoc, mul_smul_comm]
        have : t * s = ω⁻¹ • (s * t) := by
          rw [hST, smul_smul, inv_mul_cancel₀ hω0, one_smul]
        rw [this, smul_comm]
      have H' : HeisData p (eigProj ψ' (e⁻¹ • t)) s si 1 :=
        heisData_of_split hψ' ht' hpF hab' hs_si hsi_s (by rw [hs, one_smul])
      have hd' := H'.finrank_eq_mul
      rw [hfin] at hd'
      have hdd : finrank F (LinearMap.range (eigProj ψ' (e⁻¹ • t) 0)) = d := by
        have : p * finrank F (LinearMap.range (eigProj ψ' (e⁻¹ • t) 0)) = p * d := by
          rw [← hd', hd]
        exact Nat.eq_of_mul_eq_mul_left hp.pos this
      have hdimT : ∀ j, 2 ≤ finrank F (LinearMap.range (eigProj ψ' (e⁻¹ • t) j)) := fun j => by
        rw [H'.finrank_range j, hdd]; exact hd2
      exact fun h => goodBlock_split (x := t) (e := e) (a := e⁻¹ • t) rfl hpF he0 hψ' ht' hsqT
        hdimT hF4 h
    · push Not at hcp
      have hirr : Irreducible (X ^ p - C (c : F) : F[X]) := X_pow_sub_C_irreducible_of_prime hp hcp
      rintro ⟨a, ha⟩
      have hamem := mem_primaryFactors.1 ha
      have hdvd : a ∣ X ^ p - C (c : F) :=
        hamem.2.2.trans (minpoly.dvd F t (aeval_X_pow_sub_C_eq_zero hT))
      have haeq : a = X ^ p - C (c : F) :=
        eq_of_monic_of_associated hamem.2.1 (monic_X_pow_sub_C _ hp.ne_zero)
          (associated_of_dvd_dvd hdvd (hamem.1.dvd_symm hirr hdvd))
      subst haeq
      haveI : Fact (Irreducible (X ^ p - C (c : F) : F[X])) := ⟨hirr⟩
      have hfr := finrank_primaryComponent t (X ^ p - C (c : F) : F[X])
      have hall : primaryComponent t (X ^ p - C (c : F) : F[X]) = ⊤ := by
        refine eq_top_iff.2 fun v _ => ?_
        exact mem_primaryComponent_X_pow_sub_C hT v
      have hfcomp : finrank F (primaryComponent t (X ^ p - C (c : F) : F[X])) = n := by
        rw [hall, finrank_top, hfin]
      rw [hfcomp, natDegree_X_pow_sub_C] at hfr
      have hmult : 2 ≤ mult t ⟨_, ha⟩ := by
        show 2 ≤ finrank (AdjoinRoot (X ^ p - C (c : F) : F[X]))
          (primaryComponent t (X ^ p - C (c : F) : F[X]))
        have : p * finrank (AdjoinRoot (X ^ p - C (c : F) : F[X]))
            (primaryComponent t (X ^ p - C (c : F) : F[X])) = p * d := by rw [← hfr, hd]
        have := Nat.eq_of_mul_eq_mul_left hp.pos this
        omega
      refine Or.inr ⟨hmult, ?_⟩
      have hcard : Nat.card (Efac t ⟨_, ha⟩) = Nat.card F ^ (X ^ p - C (c : F) : F[X]).natDegree :=
        natCard_adjoinRoot (X ^ p - C (c : F) : F[X])
      rw [hcard, natDegree_X_pow_sub_C]
      calc 3 < Nat.card F := hF4
        _ = Nat.card F ^ 1 := (pow_one _).symm
        _ ≤ Nat.card F ^ p := Nat.pow_le_pow_right Finite.card_pos hp.one_lt.le
  have hTblocks : ∀ h : primaryFactors t, blockImage hsqT h ≤ 𝒢.map SpecialLinearGroup.toGL :=
    fun h => hTb hsqT h (goodT h)
  set b₀ := Pi.basisFun F (Fin n) with hb₀
  set G : Subgroup ((Fin n → F) ≃ₗ[F] (Fin n → F)) := 𝒢.map (slAction b₀) with hG
  have hGdet : ∀ g ∈ G, LinearEquiv.det g = 1 := by
    rintro _ ⟨s', -, rfl⟩
    exact det_slAction b₀ s'
  have hsupp : ∀ j, suppGroup (eigProj ψ s j) ≤ G := by
    intro j g hg
    have hlink : primaryProjection s (X - C (ψ j)) = eigProj ψ s j := by
      have := primaryProjection_split (x := s) (e := 1) hax1 hpF one_ne_zero hψ hs hsqS hdimS j
      simpa using this
    have hmem : (X - C (ψ j) : F[X]) ∈ primaryFactors s := by
      have := mem_primaryFactors_split (x := s) (e := 1) hax1 hpF one_ne_zero hs hdimS j
      simpa using this
    rw [← hlink] at hg
    obtain ⟨A', hA'⟩ := exists_slAction_eq b₀ hg.1
    have hAv : ∀ v, Matrix.toLin' (A' : Matrix (Fin n) (Fin n) F) v = g v := fun v => by
      rw [toLin'_apply_eq_slAction, hA']
    have hblk := suppGroup_le_blockImage (S := S) hsqS hmem hg hAv
    obtain ⟨s', hs'𝒢, hs'⟩ := hSblocks _ hblk
    refine ⟨s', hs'𝒢, ?_⟩
    rw [SpecialLinearGroup.toGL_injective hs']
    exact hA'
  have hGt : ∀ β : Module.End F (Fin n → F), β * t = t * β → (∀ v, β (β v) = 0) →
      ∃ x ∈ G, ∀ v, x v = v + β v := by
    intro β hβt hββ
    obtain ⟨s', hs'𝒢, hs'v⟩ := exists_mem_one_add_of_blocks (M := T) rfl hsqT 𝒢 hTblocks hβt
      (LinearMap.ext fun v => hββ v)
    refine ⟨slAction b₀ s', ⟨s', hs'𝒢, rfl⟩, fun v => ?_⟩
    rw [← toLin'_apply_eq_slAction, hs'v]
  have hmain := eq_top_of_heisData hp2 H hdimS G hGdet hsupp hGt
  refine eq_top_iff.mpr fun s' _ => ?_
  obtain ⟨s'', hs''𝒢, hs''⟩ := hmain (slAction b₀ s') (det_slAction b₀ s')
  exact (slAction_injective b₀ hs'') ▸ hs''𝒢

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis
