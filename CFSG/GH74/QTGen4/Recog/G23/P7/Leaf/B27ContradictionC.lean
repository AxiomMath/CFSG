module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionB

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable
open CFSG.GH74.QTGen4.Recog.G23.P7.B27A

variable {G : Type} [Group G]

section UGroup

@[expose] def uMat (a b : ZMod 3) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![1, 0, 0; a, 1, 0; b, 0, 1]

theorem uMat_mul (a b a' b' : ZMod 3) : uMat a b * uMat a' b' = uMat (a + a') (b + b') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uMat_zero : uMat 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

theorem uMat_conj (g h : Matrix (Fin 3) (Fin 3) (ZMod 3)) (hgh : g * h = 1)
    (hg01 : g 0 1 = 0) (hg02 : g 0 2 = 0) (hh01 : h 0 1 = 0) (hh02 : h 0 2 = 0) (a b : ZMod 3) :
    g * uMat a b * h = uMat ((g * uMat a b * h) 1 0) ((g * uMat a b * h) 2 0) := by
  have e : ∀ i j, (g * uMat a b * h) i j = (g * h) i j + (a * g i 1 + b * g i 2) * h 0 j := by
    intro i j
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  have hgh00 : (g * h) 0 0 = 1 := by rw [hgh]; simp
  have hgh01 : (g * h) 0 1 = 0 := by rw [hgh]; simp
  have hgh02 : (g * h) 0 2 = 0 := by rw [hgh]; simp
  have hgh11 : (g * h) 1 1 = 1 := by rw [hgh]; simp
  have hgh12 : (g * h) 1 2 = 0 := by rw [hgh]; simp
  have hgh21 : (g * h) 2 1 = 0 := by rw [hgh]; simp
  have hgh22 : (g * h) 2 2 = 1 := by rw [hgh]; simp
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [e] <;>
    simp [uMat, hgh00, hgh01, hgh02, hgh11, hgh12, hgh21, hgh22, hg01, hg02, hh01, hh02]

end UGroup

theorem zmod3_add_neg : ∀ a : ZMod 3, a + -a = 0 := by decide

theorem zmod3_neg_add : ∀ a : ZMod 3, -a + a = 0 := by decide

theorem uMat_mul_neg (a b : ZMod 3) : uMat a b * uMat (-a) (-b) = 1 := by
  rw [uMat_mul, zmod3_add_neg a, zmod3_add_neg b, uMat_zero]

theorem neg_mul_uMat (a b : ZMod 3) : uMat (-a) (-b) * uMat a b = 1 := by
  rw [uMat_mul, zmod3_neg_add a, zmod3_neg_add b, uMat_zero]

@[expose] def uGL (a b : ZMod 3) : GL (Fin 3) (ZMod 3) :=
  Units.mk (uMat a b) (uMat (-a) (-b)) (uMat_mul_neg a b) (neg_mul_uMat a b)

@[expose] def U0 : Subgroup (GL (Fin 3) (ZMod 3)) where
  carrier := {g | ∃ a b : ZMod 3, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) = uMat a b}
  mul_mem' := by
    rintro _ _ ⟨a, b, hx⟩ ⟨a', b', hy⟩
    exact ⟨a + a', b + b', by rw [Units.val_mul, hx, hy, uMat_mul]⟩
  one_mem' := ⟨0, 0, by rw [Units.val_one, uMat_zero]⟩
  inv_mem' := by
    rintro g ⟨a, b, hx⟩
    refine ⟨-a, -b, ?_⟩
    have h1 : uMat (-a) (-b) * uMat a b = 1 := neg_mul_uMat a b
    have h2 : uMat a b * ((g⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = 1 := by
      rw [← hx]
      exact Units.mul_inv g
    calc ((g⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3))
        = (uMat (-a) (-b) * uMat a b) * ((g⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
          rw [h1, Matrix.one_mul]
      _ = uMat (-a) (-b) * (uMat a b * ((g⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3))) := by
          rw [Matrix.mul_assoc]
      _ = uMat (-a) (-b) := by rw [h2, Matrix.mul_one]

theorem card_U0 : Nat.card U0 = 9 := by
  have hinj : Function.Injective
      (fun p : ZMod 3 × ZMod 3 => (⟨uGL p.1 p.2, p.1, p.2, rfl⟩ : U0)) := by
    intro p q h
    have h' := congrArg (fun x : U0 => ((x : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 0) h
    have h'' := congrArg (fun x : U0 => ((x : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 0) h
    simp [uGL, uMat] at h' h''
    exact Prod.ext h' h''
  have hsurj : Function.Surjective
      (fun p : ZMod 3 × ZMod 3 => (⟨uGL p.1 p.2, p.1, p.2, rfl⟩ : U0)) := by
    rintro ⟨g, a, b, hab⟩
    exact ⟨(a, b), Subtype.ext (Units.ext hab.symm)⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩), Nat.card_prod]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem U0_conj_mem {g u : GL (Fin 3) (ZMod 3)} (hu : u ∈ U0)
    (hg01 : (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 1 = 0)
    (hg02 : (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 2 = 0)
    (hg'01 : ((g⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 1 = 0)
    (hg'02 : ((g⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 2 = 0) :
    g * u * g⁻¹ ∈ U0 := by
  obtain ⟨a, b, hab⟩ := hu
  have key := uMat_conj (g : Matrix (Fin 3) (Fin 3) (ZMod 3))
    ((g⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3))
    (Units.mul_inv g) hg01 hg02 hg'01 hg'02 a b
  have hval : ((g * u * g⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) * uMat a b *
        ((g⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
    rw [Units.val_mul, Units.val_mul, hab]
  exact ⟨_, _, hval.trans key⟩

theorem card_sup_mul_card_inf {X : Type*} [Group X] [Finite X] (A B : Subgroup X)
    (hA : A ≤ Subgroup.normalizer (B : Set X)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hE := QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hA
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hA
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hA
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hA
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hA
  have hE' := Nat.card_congr hE.toEquiv
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf (A ⊔ B))
  have h3 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : B ≤ A ⊔ B)).toEquiv
  have h4 : Nat.card ↥(B.subgroupOf A) = Nat.card ↥(A ⊓ B) := by
    apply Nat.card_congr
    exact
      { toFun := fun x => ⟨(x : ↥A), Subgroup.mem_inf.mpr ⟨(x : ↥A).2, Subgroup.mem_subgroupOf.mp x.2⟩⟩
        invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.mp y.2).1⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp y.2).2⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl }
  rw [hE'] at h1
  rw [h3] at h2
  rw [h4] at h1
  rw [h1, h2]
  ring

section Yrange

open scoped IsMulCommutative

variable {H H₁ H₂ M₁ Pb W₁ Mf : Subgroup G} {e : Fin 6 → G} {t' : G}

theorem rho_H₂_00 [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hv : VertexCore e H (e 0) H₂ M₁)
    (hst : B27State e M₁ Pb W₁ Mf t')
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (w d : G) (hwM : w ∈ M₁) (hdM : d ∈ M₁)
    (hb0 : b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁))
    (hb1 : b 1 = Additive.ofMul (⟨w, hwM⟩ : M₁)) (hb2 : b 2 = Additive.ofMul (⟨d, hdM⟩ : M₁))
    (hwD : w ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv))
    (hdD : d ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv)) {h : G} (hh : h ∈ H₂) :
    rhoMat b ⟨h, H₂_le_normalizer_M₁ hlet hv hh⟩ 0 0 = 1 := by
  have hcent := Subgroup.mem_centralizer_iff.mp (H₂_le_cent_e0 hlet hh) (e 0) (Set.mem_singleton _)
  have hk : h * e 0 * h⁻¹ = e 0 ^ (1 : ℤ) := by
    rw [zpow_one, ← hcent, mul_inv_cancel_right]
  obtain ⟨-, -, -, -, r00⟩ := rho_block hone hlet hv hst b w d hwM hdM hb0 hb1 hb2 hwD hdD
    ⟨h, H₂_le_normalizer_M₁ hlet hv hh⟩ (hone.le_two hh) 1 hk
  rw [r00]
  simp

theorem rho_t_00 [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hF : HFacts H H₁ H₂ e)
    (hv : VertexCore e H (e 0) H₂ M₁) (hst : B27State e M₁ Pb W₁ Mf t')
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (w d : G) (hwM : w ∈ M₁) (hdM : d ∈ M₁)
    (hb0 : b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁))
    (hb1 : b 1 = Additive.ofMul (⟨w, hwM⟩ : M₁)) (hb2 : b 2 = Additive.ofMul (⟨d, hdM⟩ : M₁))
    (hwD : w ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv))
    (hdD : d ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv)) :
    rhoMat b ⟨e 4, e4_mem_normalizer_M₁ hlet hv⟩ 0 0 = -1 := by
  have hkt : (e 4 : G) * e 0 * (e 4)⁻¹ = e 0 ^ (-1 : ℤ) := by
    rw [zpow_neg_one]
    exact e4_conj_e0 hone hlet hF hv
  obtain ⟨-, -, -, -, r00⟩ := rho_block hone hlet hv hst b w d hwM hdM hb0 hb1 hb2 hwD hdD
    ⟨e 4, e4_mem_normalizer_M₁ hlet hv⟩ (e4_mem_H hlet) (-1) hkt
  rw [r00]
  decide

theorem Y0Subgroup_le_range [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hF : HFacts H H₁ H₂ e)
    (hv : VertexCore e H (e 0) H₂ M₁) (hst : B27State e M₁ Pb W₁ Mf t')
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (w d : G) (hwM : w ∈ M₁) (hdM : d ∈ M₁)
    (hb0 : b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁))
    (hb1 : b 1 = Additive.ofMul (⟨w, hwM⟩ : M₁)) (hb2 : b 2 = Additive.ofMul (⟨d, hdM⟩ : M₁))
    (hwD : w ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv))
    (hdD : d ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv)) :
    Y0Subgroup ≤ (rhoGL b).range := by
  let φ₂ : H₂ →* GL (Fin 3) (ZMod 3) :=
    (rhoGL b).comp (Subgroup.inclusion (H₂_le_normalizer_M₁ hlet hv))
  have hφ₂apply : ∀ x : H₂, φ₂ x = rhoGL b ⟨(x : G), H₂_le_normalizer_M₁ hlet hv x.2⟩ :=
    fun x => rfl
  have hφ₂inj : Function.Injective φ₂ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hφ₂apply] at hx
    have hc := (rhoGL_eq_one_iff b _).mp hx
    have hmem : (x : G) ∈ Subgroup.centralizer (M₁ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have h' := hc m hm
      rw [mul_inv_eq_iff_eq_mul] at h'
      exact h'.symm
    have hbot := fix_H₂_eq_bot hone hlet hv hst
    have hx1 : (x : G) ∈ Subgroup.centralizer (M₁ : Set G) ⊓ H₂ :=
      Subgroup.mem_inf.mpr ⟨hmem, x.2⟩
    rw [hbot, Subgroup.mem_bot] at hx1
    exact Subtype.ext hx1
  let tN : Subgroup.normalizer (M₁ : Set G) := ⟨e 4, e4_mem_normalizer_M₁ hlet hv⟩
  have hφ₂card : Nat.card φ₂.range = 24 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφ₂inj, Subgroup.card_top,
      card_H₂ hone]
  have hsub : φ₂.range ⊔ Subgroup.zpowers (rhoGL b tN) ≤ Y0Subgroup := by
    refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      rw [hφ₂apply]
      exact rho_H₂_mem_Y0 hone hlet hF hv hst b w d hwM hdM hb0 hb1 hb2 hwD hdD x.2
    · rw [Subgroup.zpowers_le]
      exact rho_t_mem_Y0 hone hlet hF hv hst b w d hwM hdM hb0 hb1 hb2 hwD hdD
  have hne : φ₂.range ≠ φ₂.range ⊔ Subgroup.zpowers (rhoGL b tN) := by
    intro heq
    have hmem : rhoGL b tN ∈ φ₂.range := by
      rw [heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    obtain ⟨x, hx⟩ := hmem
    have h1 := rho_H₂_00 hone hlet hv hst b w d hwM hdM hb0 hb1 hb2 hwD hdD x.2
    have h2 : ((rhoGL b tN : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 0 = -1 := by
      rw [rhoGL_val]
      exact rho_t_00 hone hlet hF hv hst b w d hwM hdM hb0 hb1 hb2 hwD hdD
    rw [← hx, hφ₂apply, rhoGL_val] at h2
    rw [h1] at h2
    exact absurd h2 (by decide)
  set K := φ₂.range ⊔ Subgroup.zpowers (rhoGL b tN) with hKdef
  have hLcard : Nat.card K ≥ 48 := by
    have hcm := Subgroup.card_mul_index (φ₂.range.subgroupOf K)
    have hc1 : Nat.card (φ₂.range.subgroupOf K) = 24 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : φ₂.range ≤ K)).toEquiv, hφ₂card]
    have hidx : 2 ≤ (φ₂.range.subgroupOf K).index := by
      have h0 : (φ₂.range.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h1 : (φ₂.range.subgroupOf K).index ≠ 1 := by
        intro h1
        rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at h1
        exact hne (le_antisymm le_sup_left h1) 
      omega
    rw [hc1] at hcm
    rw [← hcm]
    omega
  have hKY : K ≤ Y0Subgroup := hsub
  have hEq : K = Y0Subgroup := Subgroup.eq_of_le_of_card_ge hKY (by
    have := card_Y0Subgroup_le
    omega)
  rw [← hEq, hKdef]
  refine sup_le ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨⟨(x : G), H₂_le_normalizer_M₁ hlet hv x.2⟩, (hφ₂apply x).symm⟩
  · rw [Subgroup.zpowers_le]
    exact ⟨tN, rfl⟩

end Yrange

end CFSG.GH74.QTGen4.Recog.G23.P7
