module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om1.ClassPkg
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylAut

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check

set_option linter.unusedSectionVars false


@[ext] private structure FsTup where
  p0 : Equiv.Perm (Fin 240)
  p1 : Equiv.Perm (Fin 240)
  p2 : Equiv.Perm (Fin 240)
  p3 : Equiv.Perm (Fin 240)

private instance fsSMul : SMul WP FsTup where
  smul g t :=
    ⟨(g : Equiv.Perm (Fin 240)) * t.p0 * (g : Equiv.Perm (Fin 240))⁻¹,
      (g : Equiv.Perm (Fin 240)) * t.p1 * (g : Equiv.Perm (Fin 240))⁻¹,
      (g : Equiv.Perm (Fin 240)) * t.p2 * (g : Equiv.Perm (Fin 240))⁻¹,
      (g : Equiv.Perm (Fin 240)) * t.p3 * (g : Equiv.Perm (Fin 240))⁻¹⟩

private theorem fs_smul_p0 (g : WP) (t : FsTup) :
    (g • t).p0 = (g : Equiv.Perm (Fin 240)) * t.p0 * (g : Equiv.Perm (Fin 240))⁻¹ := rfl

private theorem fs_smul_p1 (g : WP) (t : FsTup) :
    (g • t).p1 = (g : Equiv.Perm (Fin 240)) * t.p1 * (g : Equiv.Perm (Fin 240))⁻¹ := rfl

private theorem fs_smul_p2 (g : WP) (t : FsTup) :
    (g • t).p2 = (g : Equiv.Perm (Fin 240)) * t.p2 * (g : Equiv.Perm (Fin 240))⁻¹ := rfl

private theorem fs_smul_p3 (g : WP) (t : FsTup) :
    (g • t).p3 = (g : Equiv.Perm (Fin 240)) * t.p3 * (g : Equiv.Perm (Fin 240))⁻¹ := rfl

private instance fsAction : MulAction WP FsTup where
  one_smul t := by
    ext <;> simp [fs_smul_p0, fs_smul_p1, fs_smul_p2, fs_smul_p3]
  mul_smul g h t := by
    ext <;> simp [fs_smul_p0, fs_smul_p1, fs_smul_p2, fs_smul_p3, mul_assoc]

private def fsOf (a b c d : WP) : FsTup :=
  ⟨(a : Equiv.Perm (Fin 240)), (b : Equiv.Perm (Fin 240)), (c : Equiv.Perm (Fin 240)),
    (d : Equiv.Perm (Fin 240))⟩

private theorem fs_smul_fsOf (x a b c d : WP) :
    x • fsOf a b c d = fsOf (x * a * x⁻¹) (x * b * x⁻¹) (x * c * x⁻¹) (x * d * x⁻¹) := rfl

private noncomputable def fs0 : FsTup := fsOf i0 j0 (s1 * i0 * s1⁻¹) (s1 * j0 * s1⁻¹)

private def fsTuple (u : FsTup) :
    Equiv.Perm (Fin 240) × Equiv.Perm (Fin 240) × Equiv.Perm (Fin 240) × Equiv.Perm (Fin 240) :=
  (u.p0, u.p1, u.p2, u.p3)

private theorem fsTuple_injective : Function.Injective fsTuple := by
  intro u v h
  simp only [fsTuple, Prod.mk.injEq] at h
  exact FsTup.ext h.1 h.2.1 h.2.2.1 h.2.2.2

private theorem fs_tuple_smul (x : WP) : fsTuple (x • fs0) = Om1Facts.tup (x : Equiv.Perm (Fin 240)) := by
  rw [fs0, fs_smul_fsOf]
  simp only [fsTuple, fsOf, Om1Facts.tup, Om1Facts.i0', Om1Facts.j0',
    Subgroup.coe_mul, Subgroup.coe_inv, coe_i0, coe_j0, coe_s1]

private theorem fs_ncard_orbit : 576 ≤ (MulAction.orbit (closureW wT) fs0).ncard := by
  have h := Certificates.certificate197001.2.2.2.2.2.2.2.2.2.1
  have hws := wordOK_of_sub wT_sub
  have e : {p | ∃ s ∈ Om1Facts.G wT, p = Om1Facts.tup s} =
      fsTuple '' MulAction.orbit (closureW wT) fs0 := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨x, hx, rfl⟩ := exists_of_mem_G hws hs
      exact ⟨x • fs0, ⟨⟨x, hx⟩, rfl⟩, fs_tuple_smul x⟩
    · rintro ⟨u, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
      exact ⟨x, (mem_closureW_iff hws).1 hx, fs_tuple_smul x⟩
  rwa [e, Set.ncard_image_of_injective _ fsTuple_injective] at h

private theorem fs_card_stab : Nat.card (MulAction.stabilizer ↥T0 fs0) ≤ 192 := by
  obtain ⟨hT, -, hcardT, -⟩ := classPkg0
  have h1 := fs_ncard_orbit
  rw [hT] at h1
  have h2 : Nat.card (MulAction.stabilizer ↥T0 fs0) * (MulAction.orbit ↥T0 fs0).ncard =
      Nat.card ↥T0 := by
    rw [← MulAction.index_stabilizer, Subgroup.card_mul_index]
  rw [hcardT] at h2
  by_contra hc
  rw [not_le] at hc
  nlinarith

private theorem fs_cent_mem {x : WP}
    (hx : x ∈ Subgroup.centralizer
      {y : WP | ∃ J ∈ ({R0, R0'} : Set (Subgroup WP)), y ∈ J}) :
    x ∈ T0 ∧ x • fs0 = fs0 := by
  rw [Subgroup.mem_centralizer_iff] at hx
  have hi0 : i0 ∈ R0 := Subgroup.subset_closure (by simp)
  have hj0 : j0 ∈ R0 := Subgroup.subset_closure (by simp)
  have c1 : i0 * x = x * i0 := hx i0 ⟨R0, by simp, hi0⟩
  have c2 : j0 * x = x * j0 := hx j0 ⟨R0, by simp, hj0⟩
  have c3 : (s1 * i0 * s1⁻¹) * x = x * (s1 * i0 * s1⁻¹) :=
    hx _ ⟨R0', by simp, CFSG.ClassicalInvolution.Generic.conj_mem_conjSub hi0⟩
  have c4 : (s1 * j0 * s1⁻¹) * x = x * (s1 * j0 * s1⁻¹) :=
    hx _ ⟨R0', by simp, CFSG.ClassicalInvolution.Generic.conj_mem_conjSub hj0⟩
  refine ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff, ← i0_mul_self]
    calc x * (i0 * i0) = (x * i0) * i0 := (mul_assoc _ _ _).symm
      _ = (i0 * x) * i0 := by rw [c1]
      _ = i0 * (x * i0) := mul_assoc _ _ _
      _ = i0 * (i0 * x) := by rw [c1]
      _ = (i0 * i0) * x := (mul_assoc _ _ _).symm
  · unfold fs0
    rw [fs_smul_fsOf]
    have k1 : x * i0 * x⁻¹ = i0 := mul_inv_eq_iff_eq_mul.2 c1.symm
    have k2 : x * j0 * x⁻¹ = j0 := mul_inv_eq_iff_eq_mul.2 c2.symm
    have k3 : x * (s1 * i0 * s1⁻¹) * x⁻¹ = s1 * i0 * s1⁻¹ := mul_inv_eq_iff_eq_mul.2 c3.symm
    have k4 : x * (s1 * j0 * s1⁻¹) * x⁻¹ = s1 * j0 * s1⁻¹ := mul_inv_eq_iff_eq_mul.2 c4.symm
    rw [k1, k2, k3, k4]

private theorem fs_card_centralizer_le :
    Nat.card (Subgroup.centralizer
      {y : WP | ∃ J ∈ ({R0, R0'} : Set (Subgroup WP)), y ∈ J}) ≤ 192 := by
  refine le_trans ?_ fs_card_stab
  refine Nat.card_le_card_of_injective
    (fun x => ⟨⟨x.1, (fs_cent_mem x.2).1⟩, (MulAction.mem_stabilizer_iff).2 (fs_cent_mem x.2).2⟩)
    fun x y h => Subtype.ext ?_
  exact congrArg (fun z => z.1.1) h

theorem card_fixSet_le {B : Set (Subgroup WP)} (h0 : R0 ∈ B) (h1 : R0' ∈ B) :
    Nat.card (fixSet (⊤ : Subgroup WP) B) ≤ 192 := by
  have hsub : ({R0, R0'} : Set (Subgroup WP)) ⊆ B := by
    intro J hJ
    rcases hJ with rfl | hJ
    · exact h0
    · rw [Set.mem_singleton_iff] at hJ
      rw [hJ]
      exact h1
  have hAut : Nat.card (MulAut ↥(⊤ : Subgroup WP)) = 348364800 := by
    rw [← card_mulAut_wPlus]
    exact Nat.card_congr (MulAut.congr Subgroup.topEquiv).toEquiv
  haveI : Finite (MulAut ↥(⊤ : Subgroup WP)) := Nat.finite_of_card_ne_zero (by rw [hAut]; norm_num)
  have h2 : Nat.card (fixSet (⊤ : Subgroup WP) B) ≤
      Nat.card (fixSet (⊤ : Subgroup WP) ({R0, R0'} : Set (Subgroup WP))) :=
    Subgroup.card_le_of_le (OmGen.fixSet_anti hsub)
  have h3 := OmGen.card_fixSet_mul_le (H := WP) ({R0, R0'} : Set (Subgroup WP))
  rw [hAut, card_wPlus] at h3
  have h4 := Nat.le_of_mul_le_mul_right h3 (by norm_num)
  have h5 := fs_card_centralizer_le
  omega

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1
