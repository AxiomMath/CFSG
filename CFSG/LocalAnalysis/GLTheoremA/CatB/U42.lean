module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.GH74.Exceptional

namespace U42

abbrev ι2 : Type := Fin 2 ⊕ Fin 2

abbrev Jm : Matrix ι2 ι2 (ZMod 3) := fromBlocks 0 1 (-1) 0

def mkSp (M N : Matrix ι2 ι2 (ZMod 3)) (h1 : M * N = 1) (h2 : N * M = 1)
    (hs : Mᵀ * Jm * M = Jm) : StatedSp 2 (ZMod 3) :=
  ⟨⟨M, N, h1, h2⟩, CFSG.Open.StatedAPI.mem_statedSp_iff.2 hs⟩

def Um (S : Matrix (Fin 2) (Fin 2) (ZMod 3)) : Matrix ι2 ι2 (ZMod 3) := fromBlocks 1 S 0 1

theorem Um_mul (S S' : Matrix (Fin 2) (Fin 2) (ZMod 3)) : Um S * Um S' = Um (S + S') := by
  simp [Um, fromBlocks_multiply, add_comm]

theorem Um_zero : Um 0 = 1 := by simp [Um]

theorem Um_symp (S : Matrix (Fin 2) (Fin 2) (ZMod 3)) (hS : Sᵀ = S) :
    (Um S)ᵀ * Jm * Um S = Jm := by
  simp [Um, fromBlocks_multiply, fromBlocks_transpose, hS]

def Sm (a b c : ZMod 3) : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![a, b; b, c]

theorem Sm_add (a b c a' b' c' : ZMod 3) :
    Sm a b c + Sm a' b' c' = Sm (a + a') (b + b') (c + c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Sm]

theorem Sm_zero : Sm 0 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Sm]

theorem Sm_transpose (a b c : ZMod 3) : (Sm a b c)ᵀ = Sm a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Sm]

theorem Um_neg_mul (S : Matrix (Fin 2) (Fin 2) (ZMod 3)) : Um S * Um (-S) = 1 := by
  rw [Um_mul, add_neg_cancel, Um_zero]

theorem Um_neg_mul' (S : Matrix (Fin 2) (Fin 2) (ZMod 3)) : Um (-S) * Um S = 1 := by
  rw [Um_mul, neg_add_cancel, Um_zero]

def Usp (S : Matrix (Fin 2) (Fin 2) (ZMod 3)) (hS : Sᵀ = S) : StatedSp 2 (ZMod 3) :=
  mkSp (Um S) (Um (-S)) (Um_neg_mul S) (Um_neg_mul' S) (Um_symp S hS)

def Tphi : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3) →* PSp43 where
  toFun v := QuotientGroup.mk (Usp (Sm v.toAdd.1 v.toAdd.2.1 v.toAdd.2.2) (Sm_transpose _ _ _))
  map_one' := by
    show QuotientGroup.mk (Usp (Sm 0 0 0) (Sm_transpose _ _ _)) = 1
    have : Usp (Sm 0 0 0) (Sm_transpose _ _ _) = 1 := Subtype.ext (Units.ext (by
      show Um (Sm 0 0 0) = 1
      rw [Sm_zero, Um_zero]))
    rw [this]; rfl
  map_mul' x y := by
    rw [← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    show Um (Sm (x.toAdd + y.toAdd).1 (x.toAdd + y.toAdd).2.1 (x.toAdd + y.toAdd).2.2) =
      Um (Sm x.toAdd.1 x.toAdd.2.1 x.toAdd.2.2) * Um (Sm y.toAdd.1 y.toAdd.2.1 y.toAdd.2.2)
    rw [Um_mul, Sm_add]
    rfl

theorem Um_apply_inl_inr (S : Matrix (Fin 2) (Fin 2) (ZMod 3)) (i j : Fin 2) :
    Um S (Sum.inl i) (Sum.inr j) = S i j := by
  simp [Um]

theorem Tphi_injective : Function.Injective Tphi := by
  intro x y hxy
  obtain ⟨u, hu⟩ := (CFSG.Open.StatedAPI.statedProj_mk_eq_iff _ _ _).1 hxy
  have hM : ∀ S S' : Matrix (Fin 2) (Fin 2) (ZMod 3), Um S' = Um S * ((u : ZMod 3) • 1) →
      S' = S := by
    intro S S' h
    have h1 := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)
    have hu1 : (u : ZMod 3) = 1 := by
      simpa [Um, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, Fintype.sum_sum_type,
        Fin.sum_univ_two, fromBlocks_apply₁₁] using h1.symm
    rw [hu1, one_smul, mul_one] at h
    ext i j
    have h2 := congrFun (congrFun h (Sum.inl i)) (Sum.inr j)
    simpa [Um_apply_inl_inr] using h2
  have hS := hM _ _ hu
  have e00 := congrFun (congrFun hS 0) 0
  have e01 := congrFun (congrFun hS 0) 1
  have e11 := congrFun (congrFun hS 1) 1
  simp only [Sm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e11
  apply Multiplicative.toAdd.injective
  exact Prod.ext e00.symm (Prod.ext e01.symm e11.symm)

theorem pow_three_eq_one (a : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3)) : a ^ 3 = 1 := by
  revert a
  decide

theorem psp43_exists_E27 : ∃ E : Subgroup PSp43, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  refine ⟨Tphi.range, isElemAbelian_range Tphi pow_three_eq_one, ?_⟩
  rw [card_range_eq_of_injective Tphi Tphi_injective,
    Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  norm_num

def zMat : Matrix ι2 ι2 (ZMod 3) := fromBlocks !![-1, 0; 0, 1] 0 0 !![-1, 0; 0, 1]

theorem zMat_sq : zMat * zMat = 1 := by decide

theorem zMat_symp : zMatᵀ * Jm * zMat = Jm := by decide

def zsp : StatedSp 2 (ZMod 3) := mkSp zMat zMat zMat_sq zMat_sq zMat_symp

def zbar : PSp43 := QuotientGroup.mk zsp

theorem zbar_sq : zbar ^ 2 = 1 := by
  rw [pow_two, zbar, ← QuotientGroup.mk_mul]
  have : zsp * zsp = 1 := Subtype.ext (Units.ext zMat_sq)
  rw [this]; rfl

theorem zbar_ne_one : zbar ≠ 1 := by
  intro h
  rw [zbar, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  obtain ⟨u, hu⟩ := h
  have h1 := congrArg (fun g : GL ι2 (ZMod 3) => (g : Matrix ι2 ι2 (ZMod 3)) (Sum.inl 0) (Sum.inl 0)) hu
  have h2 := congrArg (fun g : GL ι2 (ZMod 3) => (g : Matrix ι2 ι2 (ZMod 3)) (Sum.inl 1) (Sum.inl 1)) hu
  simp [zsp, mkSp, zMat, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply] at h1 h2
  have h3 : (1 : (ZMod 3)ˣ) = -1 := h2.symm.trans h1
  revert h3
  decide

def emb2 : Multiplicative (ZMod 3 × ZMod 3) →* Multiplicative (ZMod 3 × ZMod 3 × ZMod 3) where
  toFun v := Multiplicative.ofAdd (v.toAdd.1, 0, v.toAdd.2)
  map_one' := rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp [toAdd_mul]

theorem emb2_injective : Function.Injective emb2 := by
  intro x y h
  apply Multiplicative.toAdd.injective
  have h' := congrArg Multiplicative.toAdd h
  simp only [emb2, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, Prod.mk.injEq] at h'
  exact Prod.ext h'.1 h'.2.2

theorem zMat_comm_Um : ∀ a c : ZMod 3, zMat * Um (Sm a 0 c) = Um (Sm a 0 c) * zMat := by
  decide

theorem zbar_comm_Tphi2 (v : Multiplicative (ZMod 3 × ZMod 3)) :
    zbar * (Tphi.comp emb2) v = (Tphi.comp emb2) v * zbar := by
  show QuotientGroup.mk zsp * QuotientGroup.mk _ = QuotientGroup.mk _ * QuotientGroup.mk zsp
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  exact zMat_comm_Um _ _

theorem pow_three_eq_one₂ (a : Multiplicative (ZMod 3 × ZMod 3)) : a ^ 3 = 1 := by
  revert a
  decide

theorem psp43_exists_inv_E9 : ∃ z : PSp43, z ^ 2 = 1 ∧ z ≠ 1 ∧ ∃ E : Subgroup PSp43,
    E ≤ Subgroup.centralizer {z} ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  refine ⟨zbar, zbar_sq, zbar_ne_one, (Tphi.comp emb2).range, ?_, ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (zbar_comm_Tphi2 v).symm
  · exact isElemAbelian_range _ pow_three_eq_one₂ 
  · rw [card_range_eq_of_injective _ (fun x y h => emb2_injective (Tphi_injective h)),
      Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod]
    norm_num

theorem psp43_exists_order3_normalizes_two : ∃ y : PSp43, orderOf y = 3 ∧
    ∃ W : Subgroup PSp43, IsPGroup 2 W ∧ W ≠ ⊥ ∧ y ∈ Subgroup.normalizer (W : Set PSp43) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj : Function.Injective (Tphi.comp emb2) := fun x y h => emb2_injective (Tphi_injective h)
  set y := (Tphi.comp emb2) (Multiplicative.ofAdd ((1 : ZMod 3), (0 : ZMod 3))) with hy
  have hy3 : y ^ 3 = 1 := by rw [hy, ← map_pow, pow_three_eq_one₂, map_one]
  have hy1 : y ≠ 1 := by
    intro h
    have h' := hinj (h.trans (map_one (Tphi.comp emb2)).symm)
    have h'' := congrArg Multiplicative.toAdd h'
    simp at h''
  refine ⟨y, orderOf_eq_prime hy3 hy1, Subgroup.zpowers zbar,
    isPGroup_zpowers_of_pow_eq_one zbar_sq, ?_, ?_⟩
  · intro h
    have : zbar ∈ (⊥ : Subgroup PSp43) := h ▸ Subgroup.mem_zpowers zbar
    exact zbar_ne_one (Subgroup.mem_bot.1 this)
  · exact mem_normalizer_zpowers_of_commute (zbar_comm_Tphi2 _).symm

end U42

open U42

section Centre

variable {G : Type} [Group G] [Finite G]

theorem center_pQuot_eq_bot_u4two (hGA : CFSG.Open.GriessAllModelsStatement) {J : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (PQuot 3 J)) (h : catalogIs (PSimple 3 J) S9.isU4two) :
    Subgroup.center (PQuot 3 J) = ⊥ := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := lieIndex_isU4two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq2.trans (by norm_num))
  have hm := lieModel_twistedA' 3 q hv e
  rw [h1, h2] at hm
  have hdvd := card_center_dvd_of_table hGA hq hm (a := 1) (b := 1) (c := 2) (d := 1)
    (by decide) (by decide) (by norm_num)
  by_contra hne
  haveI : Nontrivial (Subgroup.center (PQuot 3 J)) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  exact false_of_pGroup_dvd Nat.prime_three
    (CFSG.LocalAnalysis.GLTheoremA.I2611.isPGroup_center_pQuot' Nat.prime_three J) hdvd
    (by norm_num)

end Centre

section Rows

variable {G : Type} [Group G] [Finite G]

theorem i102U4At_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) : I102U4At G := by
  intro X J hJ hcat
  have hq := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
  have hZ := center_pQuot_eq_bot_u4two hGA hq hcat
  obtain ⟨e⟩ := bridge_u4two hcat
  obtain ⟨π, hπs, hkc⟩ := exists_hom_of_simple_equiv e
  have hk3 : ¬ 3 ∣ Nat.card π.ker := not_three_dvd_card_ker J hkc hZ
  obtain ⟨E, hEel, hEcard⟩ := psp43_exists_E27
  obtain ⟨W, hWp, hWmap, hWinj⟩ := exists_pSubgroup_lift Nat.prime_three π hk3
    (isPGroup_of_isElemAbelian hEel) (by rw [MonoidHom.range_eq_top_of_surjective π hπs]; exact le_top)
  obtain ⟨hWel, hWcard⟩ := map_subtype_isElemAbelian_card π hWmap hWinj hEel
  exact ⟨W.map J.subtype, Subgroup.map_subtype_le _, hWel, hWcard.trans hEcard⟩

theorem i2811At_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) : I2811At G := by
  intro X J hJ hcat hodd
  have hq := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
  have hZ := center_pQuot_eq_bot_u4two hGA hq hcat
  obtain ⟨e⟩ := bridge_u4two hcat
  obtain ⟨π, hπs, hkc⟩ := exists_hom_of_simple_equiv e
  have hk3 : ¬ 3 ∣ Nat.card π.ker := not_three_dvd_card_ker J hkc hZ
  have hk2 : ¬ 2 ∣ Nat.card π.ker := odd_card_ker J hkc hodd
  have hrange : π.range = ⊤ := MonoidHom.range_eq_top_of_surjective π hπs
  obtain ⟨zb, hzb2, hzb1, Eb, hEbc, hEbel, hEbcard⟩ := psp43_exists_inv_E9
  obtain ⟨z, hz2, hzπ⟩ := exists_pow_lift Nat.prime_two π hk2
    (by rw [hrange]; exact Subgroup.mem_top _) hzb2
  obtain ⟨W, hWp, hWc, hWmap, hWinj⟩ := exists_pSubgroup_lift_centralizer Nat.prime_three
    Nat.prime_two π hk3 hk2 hz2 (isPGroup_of_isElemAbelian hEbel)
    (by rw [hrange]; exact le_top) (by rw [hzπ]; exact hEbc)
  obtain ⟨hWel, hWcard⟩ := map_subtype_isElemAbelian_card π hWmap hWinj hEbel
  refine ⟨(z : G), z.2, ?_, ?_, W.map J.subtype, ?_, hWel, hWcard.trans hEbcard⟩
  · exact congrArg Subtype.val hz2
  · intro h1
    apply hzb1
    rw [← hzπ, show z = 1 from Subtype.ext h1, map_one]
  · refine le_inf (Subgroup.map_subtype_le _) ?_
    rintro _ ⟨w, hw, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 (hWc hw)))

end Rows

section Holds

theorem i102U4At_holds (G : Type) [Group G] [Finite G] : I102U4At G :=
  i102U4At_of_griess CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

theorem i2811At_holds (G : Type) [Group G] [Finite G] : I2811At G :=
  i2811At_of_griess CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

end Holds

end CFSG.LocalAnalysis.GLTheoremA.CatB
