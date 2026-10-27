module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinDefs
import CFSG.Assembly.GL83StatedBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped MatrixGroups

private theorem pow_card_eq_one_of_mem_scalars_SL {d : ℕ} {F : Type} [Field F]
    (z : ↥(LinSL d F)) (hz : (z : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F) : z ^ d = 1 := by
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hz
  have hzSL : (z : GL (Fin d) F) ∈ StatedSL d F := by
    rw [← largeEvenSLGroup_eq_statedSL]
    exact z.2
  have hdet : Matrix.GeneralLinearGroup.det (z : GL (Fin d) F) = 1 :=
    Units.ext (CFSG.Open.StatedAPI.det_of_mem_statedSL hzSL)
  have hc1 : c ^ d = 1 := by
    have h2 : Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar (Fin d) c) = 1 := by
      rw [hc, hdet]
    rwa [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h2
  have hzpow : (z : GL (Fin d) F) ^ d = 1 := by
    rw [← hc, ← map_pow, hc1, map_one]
  exact Subtype.ext (by simpa using hzpow)

private theorem mul_comm_of_mem_kernel {G : Type} [Group G] {Z : Subgroup G}
    (hZc : Z ≤ Subgroup.center G) {p d : ℕ} (hcop : Nat.Coprime p d)
    (hZd : ∀ z ∈ Z, z ^ d = 1) {a g : G} (ha : a ^ p = 1)
    (hmem : g * a * g⁻¹ * a⁻¹ ∈ Z) : g * a = a * g := by
  have hc : Commute (g * a * g⁻¹ * a⁻¹) a :=
    (Subgroup.mem_center_iff.mp (hZc hmem) a).symm
  have hzp : (g * a * g⁻¹ * a⁻¹) ^ p = 1 := by
    have h1 : (g * a * g⁻¹) ^ p = 1 := by rw [conj_pow, ha]; simp
    have h2 : g * a * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * a := by group
    rw [h2, Commute.mul_pow hc, ha, mul_one] at h1
    exact h1
  have hz1 : g * a * g⁻¹ * a⁻¹ = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_iff_pow_eq_one.mpr hzp)
      (orderOf_dvd_iff_pow_eq_one.mpr (hZd _ hmem)))
  have hconj : g * a * g⁻¹ = a := by
    rw [show g * a * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * a by group, hz1, one_mul]
  calc g * a = g * a * g⁻¹ * g := by group
    _ = a * g := by rw [hconj]

theorem lin_centralizer_quot {p n d : ℕ} {F : Type} [Field F] [Finite F] (h : LinArith p n d F)
    {a : ↥(LinSL d F)} (hap : (a : GL (Fin d) F) ^ p = 1) {g : ↥(LinSL d F)}
    (hg : LinMk d F g ∈ Subgroup.centralizer ({LinMk d F a} : Set (LinPSL d F))) :
    (g : GL (Fin d) F) * a = a * g := by
  have hcop : Nat.Coprime p d := h.1.coprime_iff_not_dvd.mpr h.2.2.2.1
  have hZc : (LargeEvenScalars (Fin d) F).subgroupOf (LinSL d F) ≤
      Subgroup.center ↥(LinSL d F) :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center (LinSL d F)
  have hZd : ∀ z ∈ (LargeEvenScalars (Fin d) F).subgroupOf (LinSL d F), z ^ d = 1 :=
    fun z hz => pow_card_eq_one_of_mem_scalars_SL z (Subgroup.mem_subgroupOf.1 hz)
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have h1 : LinMk d F (g * a * g⁻¹ * a⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hg]
    group
  have hmem : g * a * g⁻¹ * a⁻¹ ∈ (LargeEvenScalars (Fin d) F).subgroupOf (LinSL d F) :=
    (QuotientGroup.eq_one_iff (N := (LargeEvenScalars (Fin d) F).subgroupOf (LinSL d F))
      (g * a * g⁻¹ * a⁻¹)).mp h1
  have ha : a ^ p = 1 := Subtype.ext (by simpa using hap)
  have hcomm := mul_comm_of_mem_kernel hZc hcop hZd ha hmem
  simpa using congrArg (fun x : ↥(LinSL d F) => (x : GL (Fin d) F)) hcomm

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
