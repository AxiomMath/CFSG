module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25YMH01
public import CFSG.ClassicalInvolution.Generic.Generation.Layer

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P25

open scoped MatrixGroups
open CFSG.ClassicalInvolution.Q3.Q3T6 CFSG.ClassicalInvolution.Generic

theorem natCard_gf3 : Nat.card (GaloisField 3 1) = 3 :=
  Q3Z.natCard_galoisField_three

theorem odd_natCard_gf3 : Odd (Nat.card (GaloisField 3 1)) := by
  rw [natCard_gf3]
  decide

theorem le_of_le_sup_center3 {G : Type} [Group G] {H A Z : Subgroup G}
    (e : H ≃* SL(2, ZMod 3)) (hZ : Z ≤ Subgroup.center G) (hZ2 : ∀ z ∈ Z, z * z = 1)
    (hle : H ≤ A ⊔ Z) : H ≤ A := by
  set N := A ⊔ Z with hN
  have hAN : A ≤ N := le_sup_left
  have hZc : ∀ z ∈ Z, ∀ h ∈ (⊤ : Subgroup G), z * h = h * z := fun z hz h _ =>
    (Subgroup.mem_center_iff.mp (hZ hz) h).symm
  have hnorm : (A.subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAN]
    intro h n hh hn
    obtain ⟨a, ha, z, hz, rfl⟩ := exists_mul_of_mem_sup_central le_top hZc hn
    have hzz : z * h * z⁻¹ = h := by
      have := Subgroup.mem_center_iff.mp (hZ hz) h
      calc z * h * z⁻¹ = (h * z) * z⁻¹ := by rw [this]
        _ = h := by group
    have : a * z * h * (a * z)⁻¹ = a * (z * h * z⁻¹) * a⁻¹ := by group
    rw [this, hzz]
    exact A.mul_mem (A.mul_mem ha hh) (A.inv_mem ha)
  let ψ : H →* N ⧸ A.subgroupOf N :=
    (QuotientGroup.mk' (A.subgroupOf N)).comp (Subgroup.inclusion hle)
  have hψ := hom_trivial3 e ψ (by
    rintro _ ⟨h, rfl⟩
    obtain ⟨a, ha, z, hz, hh⟩ := exists_mul_of_mem_sup_central le_top hZc (hle h.2)
    have h2 : (h : G) * h = a * a := by
      rw [hh]
      have := Subgroup.mem_center_iff.mp (hZ hz) a
      calc a * z * (a * z) = a * (z * a) * z := by group
        _ = a * (a * z) * z := by rw [this]
        _ = a * a * (z * z) := by group
        _ = a * a := by rw [hZ2 z hz, mul_one]
    show ψ h * ψ h = 1
    rw [← map_mul]
    have : (h * h : H) = ⟨a * a, by simpa [h2] using (h * h).2⟩ := Subtype.ext h2
    show QuotientGroup.mk' (A.subgroupOf N) (Subgroup.inclusion hle (h * h)) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show ((h * h : H) : G) ∈ A
    rw [Subgroup.coe_mul, h2]
    exact A.mul_mem ha ha)
  intro h hh
  have := hψ ⟨h, hh⟩
  have h2 : (⟨h, hle hh⟩ : N) ∈ A.subgroupOf N := (QuotientGroup.eq_one_iff _).mp this
  exact Subgroup.mem_subgroupOf.mp h2

theorem le_of_le_sup_center3_card {G : Type} [Group G] {H A Z : Subgroup G} {F : Type}
    [Field F] (h3 : Nat.card F = 3) (e : H ≃* SL(2, F)) (hZ : Z ≤ Subgroup.center G)
    (hZ2 : ∀ z ∈ Z, z * z = 1) (hle : H ≤ A ⊔ Z) : H ≤ A := by
  obtain ⟨e'⟩ := nonempty_mulEquiv_sl2Three_of_card h3
  exact le_of_le_sup_center3 (e.trans e') hZ hZ2 hle

theorem mul_self_of_mem_center_sp {F : Type} [Field F] [Finite F]
    {z : CFSG.Assembly.LowTwoRank.StatedSp 2 F}
    (hz : z ∈ Subgroup.center (CFSG.Assembly.LowTwoRank.StatedSp 2 F)) : z * z = 1 := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F] at hz
  exact mul_self_of_mem_spScalars hz

theorem ringEquiv_eq3 {F : Type} [Field F] (h3 : Nat.card F = 3) (ρ₁ ρ₂ : F ≃+* F) : ρ₁ = ρ₂ := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [h3]; norm_num)
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨r⟩ : Nonempty (ZMod 3 ≃+* F) :=
    ⟨FiniteField.ringEquivOfCardEq (by rw [ZMod.card, ← Nat.card_eq_fintype_card, h3])⟩
  have h : (ρ₁ : F →+* F).comp (r : ZMod 3 →+* F) = (ρ₂ : F →+* F).comp (r : ZMod 3 →+* F) :=
    RingHom.ext_zmod _ _
  ext x
  obtain ⟨y, rfl⟩ := r.surjective x
  exact RingHom.congr_fun h y

open Matrix in
@[expose] noncomputable def slMapEquivF {R S : Type} [CommRing R] [CommRing S] (r : R ≃+* S) :
    SL(2, R) ≃* SL(2, S) where
  toFun := SpecialLinearGroup.map (r : R →+* S)
  invFun := SpecialLinearGroup.map (r.symm : S →+* R)
  left_inv x := by
    ext i j
    simp [SpecialLinearGroup.map_apply_coe]
  right_inv x := by
    ext i j
    simp [SpecialLinearGroup.map_apply_coe]
  map_mul' x y := map_mul _ x y

theorem sl2_aut_eq_conj3 {F : Type} [Field F] (hF : Nat.card F = 3) (α : MulAut SL(2, F)) :
    ∃ g : GL (Fin 2) F, ∀ b : SL(2, F),
      ((α b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        (g : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F) *
          ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨r⟩ : Nonempty (ZMod 3 ≃+* F) :=
    ⟨FiniteField.ringEquivOfCardEq (by rw [ZMod.card, ← Nat.card_eq_fintype_card, hF])⟩
  let Φ : SL(2, ZMod 3) ≃* SL(2, F) := slMapEquivF r
  let α' : MulAut SL(2, ZMod 3) := Φ.trans (α.trans Φ.symm)
  obtain ⟨g, hg⟩ := sl2Three_aut_eq_conj α'
  refine ⟨Matrix.GeneralLinearGroup.map (r : ZMod 3 →+* F) g, fun b => ?_⟩
  have key := hg (Φ.symm b)
  have h1 : α' (Φ.symm b) = Φ.symm (α b) := by
    simp [α']
  rw [h1] at key
  have hΦ : ∀ y : SL(2, ZMod 3), ((Φ y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (y : Matrix (Fin 2) (Fin 2) (ZMod 3)).map r := fun y => by
    simp [Φ, slMapEquivF, Matrix.SpecialLinearGroup.map_apply_coe]
  have e1 : ((α b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      ((Φ.symm (α b) : SL(2, ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).map r := by
    rw [← hΦ, Φ.apply_symm_apply]
  have e2 : (b : Matrix (Fin 2) (Fin 2) F) =
      ((Φ.symm b : SL(2, ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).map r := by
    rw [← hΦ, Φ.apply_symm_apply]
  have e3 : ((Matrix.GeneralLinearGroup.map (r : ZMod 3 →+* F) g : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).map r := rfl
  have e4 : (((Matrix.GeneralLinearGroup.map (r : ZMod 3 →+* F) g)⁻¹ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) =
      ((g⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).map r := by
    rw [← map_inv]
    rfl
  rw [e1, key, e3, e4, e2]
  simp only [Matrix.map_mul]

theorem exists_semilinear3 {F : Type} [Field F] (h3 : Nat.card F = 3)
    (α : MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) :
    ∃ (G : Matrix.GeneralLinearGroup (Fin 2) F) (σ : F ≃+* F), ∀ b,
      Matrix.SpecialLinearGroup.toGL (α b) =
        G * Matrix.GeneralLinearGroup.map (σ : F →+* F) (Matrix.SpecialLinearGroup.toGL b) *
          G⁻¹ := by
  obtain ⟨g, hg⟩ := sl2_aut_eq_conj3 h3 α
  refine ⟨g, RingEquiv.refl F, fun b => ?_⟩
  have hmap : Matrix.GeneralLinearGroup.map ((RingEquiv.refl F : F ≃+* F) : F →+* F)
      (Matrix.SpecialLinearGroup.toGL b) = Matrix.SpecialLinearGroup.toGL b := by
    apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map]
  rw [hmap]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact hg b

end CFSG.ClassicalInvolution.Q3.Q3T7P25
