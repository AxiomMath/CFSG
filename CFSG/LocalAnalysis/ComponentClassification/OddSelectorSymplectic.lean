module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorGraph
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBIsometry
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorField

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal

variable {k : Type} [Field k] [Finite k] {m : ℕ}

theorem transpose_eq_or_eq_neg_of_pureGraph (hm : 3 ≤ m) (B : GL (Fin m) k)
    (hα : (conjAut m k B * dualAut m k) ^ 2 = 1) :
    (B : Matrix (Fin m) (Fin m) k)ᵀ = B ∨ (B : Matrix (Fin m) (Fin m) k)ᵀ = -B := by
  have hα' : (conjAut m k B * fieldAut m k 1 * dualAut m k) ^ 2 = 1 := by
    rwa [map_one, mul_one]
  rw [sq_conjAut_fieldAut_dualAut] at hα'
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hm _ _ hα'
  have hmap : ∀ X : GL (Fin m) k, GeneralLinearGroup.map ((1 : k ≃+* k) : k →+* k) X = X :=
    fun X => Units.ext (by ext i j; rfl)
  rw [hmap] at hc
  set M : Matrix (Fin m) (Fin m) k := (B : Matrix (Fin m) (Fin m) k) with hMdef
  set N : Matrix (Fin m) (Fin m) k := ((B⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) with hNdef
  have hMN : M * N = 1 := by rw [hMdef, hNdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hscal : ((GeneralLinearGroup.scalar (Fin m) c : GL (Fin m) k) :
      Matrix (Fin m) (Fin m) k) = (c : k) • (1 : Matrix (Fin m) (Fin m) k) := by
    rw [smul_one_eq_diagonal]
    rfl
  have hc' : (c : k) • (1 : Matrix (Fin m) (Fin m) k) = M * Nᵀ := by
    rw [← hscal, hc, Units.val_mul, GeneralLinearGroup.coe_inverseTranspose]
  have h1 : M = (c : k) • Mᵀ := by
    calc M = M * (M * N)ᵀ := by rw [hMN, transpose_one, Matrix.mul_one]
      _ = (M * Nᵀ) * Mᵀ := by rw [transpose_mul, Matrix.mul_assoc]
      _ = (c : k) • Mᵀ := by rw [← hc', Matrix.smul_mul, Matrix.one_mul]
  have h2 : Mᵀ = (c : k) • M := by
    conv_lhs => rw [h1]
    rw [transpose_smul, transpose_transpose]
  have hM0 : M ≠ 0 := by
    intro h0
    have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    rw [h0, Matrix.zero_mul] at hMN
    exact zero_ne_one hMN
  have hcc : (c : k) * c = 1 := by
    have h3 : ((c : k) * c - 1) • M = 0 := by
      rw [sub_smul, one_smul, mul_smul, ← h2, ← h1, sub_self]
    rcases smul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hM0
  rcases mul_self_eq_one_iff.1 hcc with h | h
  · left
    rw [h2, h, one_smul]
  · right
    rw [h2, h, neg_one_smul]

omit [Finite k] in
theorem eq_top_of_isComponent_quasisimple {X : Type*} [Group X] (hX : CFSG.IsQuasisimple X)
    {B : Subgroup X} (hB : CFSG.IsComponent B) : B = ⊤ := by
  rcases quasisimple_subnormal_subgroups hX hB.2 with h | h
  · exact h
  · exfalso
    have : Nontrivial B := CFSG.LocalCores.isQuasisimple_nontrivial hB.1
    have hcomm : ∀ a b : B, a * b = b * a := fun a b => Subtype.ext
      (mem_center_iff.1 (h a.2) b).symm
    have : Group.IsPerfect B := hB.1.1
    exact Group.IsPerfect.not_isSolvable B (Group.isSolvable_of_comm hcomm)

variable {A : Type} [Group A] {a : A} {L : Subgroup A}

theorem symplectic_case_false {ℓ e : ℕ} (hm : 4 ≤ m) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = ℓ ^ e) {ρ : A →* MulAut (projectiveSL m k)} (hinj : Function.Injective ρ)
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {ρ a}))
    {B : GL (Fin m) k} (hρa : ρ a = conjAut m k B * dualAut m k)
    (hB : (B : Matrix (Fin m) (Fin m) k)ᵀ = -B) {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2) : False := by
  classical
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have hm3 : 3 ≤ m := by omega
  rw [hρa] at hL₁
  obtain ⟨hXh, hmap, -⟩ := graph_component_lift hm3 B hL₁
  set Xh := ⁅(L.map ρ).comap (conjAut m k), (L.map ρ).comap (conjAut m k)⁆ with hXhdef
  set R : GL (Fin m) k := B⁻¹ with hRdef
  set O := CatalogueBGraphForm.isometryGroup m k R with hOdef
  have hR : (R : Matrix (Fin m) (Fin m) k)ᵀ = -R := by
    have hBR : (B : Matrix (Fin m) (Fin m) k) * R = 1 := by
      rw [hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hRB : (R : Matrix (Fin m) (Fin m) k) * B = 1 := by
      rw [hRdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hRt : (R : Matrix (Fin m) (Fin m) k)ᵀ * (B : Matrix (Fin m) (Fin m) k)ᵀ = 1 := by
      rw [← transpose_mul, hBR, transpose_one]
    calc (R : Matrix (Fin m) (Fin m) k)ᵀ = (R : Matrix (Fin m) (Fin m) k)ᵀ * (B * R) := by
          rw [hBR, Matrix.mul_one]
      _ = -(((R : Matrix (Fin m) (Fin m) k)ᵀ * (B : Matrix (Fin m) (Fin m) k)ᵀ) * R) := by
          rw [hB, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, neg_neg]
      _ = -R := by rw [hRt, Matrix.one_mul]
  have eI := CatalogueBLinearHigherB.isometryGroupEquiv R
  obtain ⟨r, hdim, ⟨eS⟩⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic
    (CatalogueBLinearHigherB.matrixForm R) (CatalogueBLinearHigherB.matrixForm_isAlt hk2 R hR)
    (CatalogueBLinearHigherB.matrixForm_nondegenerate R)
  have hmr : m = 2 * r := by simpa using hdim
  have hr2 : 2 ≤ r := by omega
  have heq := CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := r) (K := k)
  set ι : StatedSp r k ≃* O := (MulEquiv.subgroupCongr heq).trans (eS.symm.trans eI) with hι
  have hqO : CFSG.IsQuasisimple O := by
    have hq := CatalogueBAlternatingIsometry.symplectic_quasisimple k r (by omega) hodd
      (Or.inl (by omega))
    exact (isQuasisimple_congr (eS.symm.trans eI)).1 hq
  have hXO : Xh = O := by
    have hcomp := (isComponentOf_iff_isComponent_subgroupOf hXh.1).mp hXh
    have htop := eq_top_of_isComponent_quasisimple hqO hcomp
    exact le_antisymm hXh.1 fun x hx => by
      have : (⟨x, hx⟩ : O) ∈ Xh.subgroupOf O := htop ▸ mem_top _
      exact this
  have hσL : ∀ x : StatedSp r k, conjAut m k (ι x : GL (Fin m) k) ∈ L.map ρ := by
    intro x
    rw [← hmap]
    exact ⟨ι x, by rw [hXO]; exact (ι x).2, rfl⟩
  set σ : StatedSp r k →* L := (L.equivMapOfInjective ρ hinj).symm.toMonoidHom.comp
    (((conjAut m k).comp (O.subtype.comp ι.toMonoidHom)).codRestrict (L.map ρ) hσL) with hσ
  have hker : σ.ker ≤ center (StatedSp r k) := by
    intro x hx
    have h1 : conjAut m k (ι x : GL (Fin m) k) = 1 := by
      have : (L.equivMapOfInjective ρ hinj).symm
          ((((conjAut m k).comp (O.subtype.comp ι.toMonoidHom)).codRestrict (L.map ρ) hσL) x) =
            1 := hx
      rw [MulEquiv.map_eq_one_iff] at this
      exact congrArg Subtype.val this
    have h2 := ker_conjAut_le_center hm3 h1
    have hιx : ι x ∈ center O := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_center_iff.mp h2 y)
    rw [mem_center_iff]
    intro y
    apply ι.injective
    rw [map_mul, map_mul]
    exact mem_center_iff.mp hιx (ι y)
  exact false_of_not_small_source
    (not_small_source_of_sp_cover hr2 hℓ hℓ2 he hk σ hker) hp2 hsrc

end CFSG.ComponentClassification.OddSelector
