module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeAffineOrbitTwoGroup
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeCanonicalOrder512Core

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix BinarySymThreeOrbit
open scoped commutatorElement Pointwise

namespace BinarySymThreeOrbit.IsAffineOrbit

variable {M : Type*} [Group M] {R : Subgroup M} [R.Normal]
  {θ : R ≃* Multiplicative (binarySymMatrices 3 × ZMod 2)}

@[expose] noncomputable def toSymThreeAffineData (H : IsAffineOrbit θ) : SymThreeAffineData M where
  R := R
  θ := θ
  D := H.transSub
  D_normal := H.transSub_normal
  R_le_D := H.le_transSub
  τ m := H.permHom m 0
  τ_mul d hd d' _ := by
    rw [H.permHom_mul_zero hd, add_comm]
  τ_eq_zero d hd := ⟨fun h => H.mem_R_of_permHom_zero hd h, fun h => by
    rw [(H.mem_ker_permHom.mpr h : H.permHom d = 1)]
    rfl⟩
  τ_surj a := by
    obtain ⟨d, hd⟩ := H.transVec_surjective (Multiplicative.ofAdd a)
    refine ⟨d, d.2, ?_⟩
    rw [← H.transVec_apply, hd, toAdd_ofAdd]
  conj_D d hd B ε := by
    have h := H.conj_symm_trans (d := d) (a := H.permHom d 0) (fun v => by
      rw [H.conj_ell_transSub ⟨d, hd⟩ v, H.transVec_apply]) B ε
    rw [h]
    congr 3
    refine Prod.ext (Subtype.ext ?_) rfl
    change _ = (symThreeTransl (H.permHom d 0) ε B : Matrix (Fin 3) (Fin 3) (ZMod 2))
    rw [coe_symThreeTransl, symThreePolar]
    simp only [add_assoc]
  lin m := H.linPart m⁻¹
  conj_lin m hm B ε := by
    rw [← ell_zero] at hm
    obtain ⟨L, hL⟩ := H.stab_linear m hm
    have hlin : (H.linPart m⁻¹ : Matrix (Fin 3) (Fin 3) (ZMod 2)) = L :=
      H.linPart_inv_eq (b := 0) fun v => by rw [hL v, zero_add]
    rw [H.conj_symm_linear hL B ε]
    congr 3
    refine Prod.ext (Subtype.ext ?_) rfl
    change _ = (symThreeCongr (H.linPart m⁻¹) B : Matrix (Fin 3) (Fin 3) (ZMod 2))
    rw [coe_symThreeCongr, hlin]
  τ_conj m _ d hd := by
    have h := H.permHom_conj_zero' m⁻¹ d hd
    rwa [inv_inv] at h
  lin_mul m m' _ _ := by
    rw [_root_.mul_inv_rev, map_mul]
  lin_one := by
    rw [inv_one, map_one]
  mem_R_of_lin m hm h := by
    rw [← ell_zero] at hm
    obtain ⟨L, hL⟩ := H.stab_linear m hm
    have hlin : (H.linPart m⁻¹ : Matrix (Fin 3) (Fin 3) (ZMod 2)) = L :=
      H.linPart_inv_eq (b := 0) fun v => by rw [hL v, zero_add]
    apply H.faithful
    intro v
    rw [hL v, ← hlin, h, Units.val_one, one_mulVec]
  exists_lin L := by
    obtain ⟨m, hm⟩ := H.linear_stab L
    refine ⟨m, ?_, Units.ext (H.linPart_inv_eq (b := 0) fun v => by rw [hm v, zero_add])⟩
    have h0 := hm 0
    rw [mulVec_zero, ell_zero] at h0
    exact h0
  A_normal m B := by
    obtain ⟨B', hB', -⟩ := H.conj_symm m⁻¹ B 0
    rw [inv_inv] at hB'
    exact ⟨B', hB'⟩
  I_normal m B hB := by
    obtain ⟨B', hB', hB'alt⟩ := H.conj_symm m⁻¹ B 0
    rw [inv_inv] at hB'
    exact ⟨B', mem_altSym_iff.mp (hB'alt (mem_altSym_iff.mpr hB) rfl), hB'⟩

end BinarySymThreeOrbit.IsAffineOrbit

theorem binary_symmetric_three_canonical_order512_subgroup
    {M : Type*} [Group M] [Finite M] {R : Subgroup M} [R.Normal]
    {θ : R ≃* Multiplicative (binarySymMatrices 3 × ZMod 2)} (H : IsAffineOrbit θ)
    (A I D : Subgroup M)
    (hA : ∀ x : M, x ∈ A ↔ ∃ B : binarySymMatrices 3, x = θ.symm (.ofAdd (B, 0)))
    (hI : ∀ x : M, x ∈ I ↔ ∃ B : binarySymMatrices 3,
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ binaryAltMatrices 3 ∧
        x = θ.symm (.ofAdd (B, 0)))
    (hD : D = CFSG.Assembly.pCore 2 M) :
    A.Normal ∧ I.Normal ∧ (A ≤ D ∧ (∀ d ∈ D, d ^ 2 ∈ A) ∧ A.relIndex D = 16) ∧
    ∃ C : Subgroup M, (C ≤ D ∧ I ≤ C ∧ ⁅C, C⁆ ≤ I ∧ I.relIndex C = 64) ∧
      (∀ C' : Subgroup M, C' ≤ D → I ≤ C' → ⁅C', C'⁆ ≤ I → I.relIndex C' = 64 → C' = C) ∧
      (C.subgroupOf D).Characteristic ∧ C.Normal ∧ Nat.card C = 512 ∧ A ≤ C ∧
      (D : Set M) = (R : Set M) * (C : Set M) ∧ R ⊓ C = A ∧
      (Subgroup.center C).map C.subtype = I ∧ ⁅C, C⁆ = I ∧
      Subgroup.closure {x | ∃ c ∈ C, c ^ 2 = x} = I ∧ (∀ c ∈ C, c ^ 2 ∈ I) ∧
      Group.nilpotencyClass C = 2 ∧ Monoid.exponent C = 4 ∧
      (∃ Y : Subgroup M, Y ≤ Subgroup.centralizer {ell θ 0} ∧ Nat.card Y = 7) ∧
      ∀ Y : Subgroup M, Y ≤ Subgroup.centralizer {ell θ 0} → Nat.card Y = 7 →
        ∀ l : List M, l.Nodup → (∀ y, y ∈ l ↔ y ∈ Y) →
          ∀ d ∈ D, (d ∈ C ↔ (l.map fun y => y⁻¹ * d * y).prod ∈ A) := by
  set S := H.toSymThreeAffineData with hS
  have hAS : A = S.A := by
    ext x
    rw [hA]
    rfl
  have hIS : I = S.I := by
    ext x
    rw [hI, S.mem_I]
    refine exists_congr fun B => and_congr_left fun _ => ?_
    rw [mem_binaryAltMatrices]
    exact ⟨fun h => funext h.2, fun h => ⟨B.2, fun i => congrFun h i⟩⟩
  have hDS : D = S.D := by
    rw [hD]
    exact H.transSub_eq_pCore.symm
  have hzS : ell θ 0 = S.z := ell_zero θ
  have hcen : ∀ Y : Subgroup M, Y ≤ Subgroup.centralizer {ell θ 0} ↔
      ∀ y ∈ Y, y⁻¹ * S.z * y = S.z := by
    intro Y
    constructor
    · intro hY y hy
      have h := Subgroup.mem_centralizer_singleton_iff.1 (hY hy)
      rw [hzS] at h
      exact S.fix_iff.2 h.symm
    · intro hY y hy
      rw [Subgroup.mem_centralizer_singleton_iff, hzS]
      exact (S.fix_iff.1 (hY y hy)).symm
  subst hAS hIS hDS
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19⟩ := S.canonical_summary
  refine ⟨h1, h2, h3, S.C, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, ?_,
    fun Y hY hY7 l hl hlY d hd => h19 Y ((hcen Y).1 hY) hY7 l hl hlY d hd⟩
  obtain ⟨Y, hY, hY7⟩ := h18
  exact ⟨Y, (hcen Y).2 hY, hY7⟩

end CFSG.LocalAnalysis.ComponentInitial
