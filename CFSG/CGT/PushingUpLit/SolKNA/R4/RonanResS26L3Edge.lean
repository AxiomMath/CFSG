module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L3Elt
public import CFSG.ClassicalInvolution.Q3.TL4E3S3GenL3
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocL3U3
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Gen

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open Matrix
open scoped MatrixGroups

section Cit3


theorem l3_exists_comm_conj {r : ℕ} (hr : 4 ≤ r) {A : Type} [Group A] [Finite A]
    (T : Subgroup A) [T.Normal] (hT : IsSimpleGroup ↥T) (hab : ∃ a b : ↥T, a * b ≠ b * a)
    (hC : Subgroup.centralizer (T : Set A) = ⊥)
    (hL3 : CFSG.ClassicalInvolution.Q3.TA3.SmallL3Ne3 ↥T)
    {R : Subgroup A} {S : Sylow 2 R} {z : A} (hd : TightDatum R S z) (hc : TightClsR r A R S z)
    {x : A} (hxR : x ∈ R) (hxo : orderOf x = 2 ^ (r - 1)) :
    ∃ g : A, g * z * g⁻¹ ≠ z ∧ x * (g * z * g⁻¹) = (g * z * g⁻¹) * x := by
  have hL3' := hL3
  obtain ⟨p, f, hp, hp2, hf, hq3, hm⟩ := hL3
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
      (Or.inl ⟨by decide, hm⟩ : CFSG.Blueprint.LieModel ↥T .PSL 3 p f)
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h4 : 4 ≤ Nat.card K := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    rw [hK]
    omega
  have h2 : (2 : K) ≠ 0 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero K hodd
  obtain ⟨hzT, -⟩ := CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.z_mem_of_comm2 hr hC
    (CFSG.CGT.PushingUpLit.SolKNA.R4.socleOutAbelian_l3 hL3').comm2 hd hc
  obtain ⟨F⟩ := CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.L3.exists_l3Frame T hodd e hzT hd.order
  obtain ⟨-, c, hc'⟩ :=
    CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.L3.a_form hC hd hodd h4 h2 F hxR (k := r - 1)
      (by omega) hxo
  have hdiag : (Matrix.diagonal ![(1 : K), -1] : Matrix (Fin 2) (Fin 2) K) *
      Matrix.diagonal ![(1 : K), -1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  obtain ⟨d, hdM⟩ : ∃ d : GL (Fin 2) K,
      (d : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![1, -1] :=
    ⟨⟨Matrix.diagonal ![1, -1], Matrix.diagonal ![1, -1], hdiag, hdiag⟩, rfl⟩
  have hdd : d * d = 1 := Units.ext (by rw [Units.val_mul, hdM, Units.val_one]; exact hdiag)
  obtain ⟨y, hy⟩ : ∃ y : A, F.π ⟨d, Subgroup.mem_top _⟩ = y := ⟨_, rfl⟩
  have hyT : y ∈ T := by rw [← hy]; exact F.hπN _
  have hy2 : y * y = 1 := by
    rw [← hy, ← map_mul, show (⟨d, Subgroup.mem_top _⟩ * ⟨d, Subgroup.mem_top _⟩ :
      ↥(⊤ : Subgroup (GL (Fin 2) K))) = 1 from Subtype.ext hdd, map_one]
  have hy1 : y ≠ 1 := by
    intro h1
    obtain ⟨ω, -, hω⟩ := F.hk ⟨d, Subgroup.mem_top _⟩ (hy.trans h1)
    have h00 := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 0 0) hω
    have h11 := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 1 1) hω
    simp [hdM, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h00 h11
    apply h2
    linear_combination h00 - h11
  have hy2' : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  have hyz : y ≠ z := by
    intro h
    have hzz : z * z = 1 := by rw [← pow_two, ← hd.order, pow_orderOf_eq_one]
    have hprod : F.π ⟨d * -1, Subgroup.mem_top _⟩ = 1 := by
      rw [show (⟨d * -1, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup (GL (Fin 2) K))) =
        ⟨d, Subgroup.mem_top _⟩ * ⟨-1, Subgroup.mem_top _⟩ from rfl, map_mul, hy, F.hπ1, h, hzz]
    obtain ⟨ω, -, hω⟩ := F.hk ⟨d * -1, Subgroup.mem_top _⟩ hprod
    have h00 := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 0 0) hω
    have h11 := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 1 1) hω
    simp [hdM, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h00 h11
    apply h2
    linear_combination h11 - h00
  have hxy : x * y = y * x := by
    have hcomm : (⟨GeneralLinearGroup.scalar (Fin 2) c, Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup (GL (Fin 2) K))) * ⟨d, Subgroup.mem_top _⟩ =
        ⟨d, Subgroup.mem_top _⟩ * ⟨GeneralLinearGroup.scalar (Fin 2) c, Subgroup.mem_top _⟩ :=
      Subtype.ext (CFSG.ClassicalInvolution.Q3.TA3.Q5GL2.scalar_mul_comm c d)
    rw [← hc', ← hy, ← map_mul, ← map_mul, hcomm]
  have ha : orderOf (e ⟨z, hzT⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hd.order
  have hb : orderOf (e ⟨y, hyT⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hy2'
  obtain ⟨g', hg'⟩ := CFSG.ClassicalInvolution.Q3.TL4.E3S3Gen.exists_conj_psl3 hodd ha hb
  have key : e.symm g' * ⟨z, hzT⟩ * (e.symm g')⁻¹ = (⟨y, hyT⟩ : ↥T) := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hg'
  have hgz : (e.symm g' : A) * z * (e.symm g' : A)⁻¹ = y := by
    have := congrArg Subtype.val key
    simpa using this
  exact ⟨(e.symm g' : A), by rw [hgz]; exact hyz, by rw [hgz]; exact hxy⟩

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
