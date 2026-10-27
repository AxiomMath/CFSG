module

public import CFSG.ClassicalInvolution.Asc77.AscB3C2
public import CFSG.ClassicalInvolution.Asc77.AscT7Z10

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace B3C

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp
open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 (r0 exists_conj_r0)
open scoped commutatorElement MatrixGroups

section Model

variable {F : Type} [Field F]

theorem sp4_adapted_core_tw [Finite F] (h2 : (2 : F) ≠ 0) {c e : StatedSp 2 F}
    {Rp : Subgroup (StatedSp 2 F)} (hRp : Rp = (R0' F).map (MulAut.conj c).toMonoidHom)
    (he : e = c * u0 F * c⁻¹) :
    ∃ c' : StatedSp 2 F, Rp = (longBlock F 2 1).range.map (MulAut.conj c'⁻¹).toMonoidHom ∧
      (twShort h2).range.map (MulAut.conj c'⁻¹).toMonoidHom ≤
        Subgroup.centralizer ({e} : Set (StatedSp 2 F)) := by
  obtain ⟨A₀, hA₀⟩ := exists_conj_r0 h2 (rho0 h2) (rho0_sq h2)
  obtain ⟨A₁, hA₁⟩ := exists_conj_r0 h2 (rho1 h2) (rho1_sq h2)
  set d : StatedSp 2 F := blk F A₀ A₁ with hd
  refine ⟨d * c⁻¹, ?_, ?_⟩
  · have hmap : (longBlock F 2 1).range.map (MulAut.conj (d * c⁻¹)⁻¹).toMonoidHom =
        (R0' F).map (MulAut.conj c).toMonoidHom := by
      have h1 : (d * c⁻¹)⁻¹ = c * d⁻¹ := by group
      rw [h1]
      have h2' : (MulAut.conj (c * d⁻¹)).toMonoidHom =
          (MulAut.conj c).toMonoidHom.comp (MulAut.conj d⁻¹).toMonoidHom := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [h2', ← Subgroup.map_map]
      show ((R0' F).map (MulAut.conj d⁻¹).toMonoidHom).map _ = _
      rw [hd, blk_inv, T7Z.R0'_map_conj_blk]
    rw [hRp, hmap]
  · rintro _ ⟨_, ⟨A', rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    set s : StatedSp 2 F := twShort h2 A' with hs
    set u' : StatedSp 2 F := blk F (rho0 h2) (rho1 h2) with hu'
    have hdu : d * u0 F * d⁻¹ = u' := by
      rw [hd, hu', u0_eq_blk, blk_inv, blk_mul, blk_mul, ← hA₀, ← hA₁]
    have h1 : d * u0 F = u' * d := by rw [← hdu]; group
    have h2'' : d⁻¹ * u' = u0 F * d⁻¹ := by rw [← hdu]; group
    have hcs : s * u' = u' * s := twShort_comm_dB h2 A'
    have hy : (MulAut.conj (d * c⁻¹)⁻¹).toMonoidHom s = c * d⁻¹ * s * d * c⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hy, he]
    calc c * d⁻¹ * s * d * c⁻¹ * (c * u0 F * c⁻¹)
        = c * d⁻¹ * s * (d * u0 F) * c⁻¹ := by group
      _ = c * d⁻¹ * s * (u' * d) * c⁻¹ := by rw [h1]
      _ = c * d⁻¹ * (s * u') * d * c⁻¹ := by group
      _ = c * d⁻¹ * (u' * s) * d * c⁻¹ := by rw [hcs]
      _ = c * (d⁻¹ * u') * s * d * c⁻¹ := by group
      _ = c * (u0 F * d⁻¹) * s * d * c⁻¹ := by rw [h2'']
      _ = c * u0 F * c⁻¹ * (c * d⁻¹ * s * d * c⁻¹) := by group

variable [Finite F]

theorem sp4_adapted_tw (h2 : (2 : F) ≠ 0) {R R' : Subgroup (StatedSp 2 F)}
    (hR : ∃ i, IsLongRootSp2 R i) (hR' : ∃ i, IsLongRootSp2 R' i) (hne : R ≠ R')
    {x x' : StatedSp 2 F} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) (hc : x' * x⁻¹ ∈ Subgroup.center (StatedSp 2 F))
    {a b : StatedSp 2 F} (ha : a ∈ R) (haa : a * a = x) (hb : b ∈ R') (hbb : b * b = x')
    (hab : a * b = b * a) :
    ∃ (c : StatedSp 2 F) (Rp : Subgroup (StatedSp 2 F)), (Rp = R ∨ Rp = R') ∧
      Rp = (longBlock F 2 1).range.map (MulAut.conj c⁻¹).toMonoidHom ∧
      (twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom ≤
        Subgroup.centralizer ({a * b} : Set (StatedSp 2 F)) := by
  obtain ⟨g, k, hRg, hR'g⟩ := ModelFacts.Orth15.OuterSp4.twin_std_sp h2 hR hR' hne hxR hx2 hx1
    hx'R' hx'2 hx'1 hc
  fin_cases k
  · obtain ⟨c, hxc, habc⟩ := T7L.exists_conj_x0_u0_sp h2 hRg hR'g hxR hx2 hx1 hx'R' hx'2 hx'1 ha
      haa hb hbb
    have hp := T7Z.twin_plane1_eq h2 hRg hR'g hxR hx2 hx1 hx'R' hx'2 hx'1 hxc
    obtain ⟨c', h1, h2'⟩ := sp4_adapted_core_tw h2 hp habc
    exact ⟨c', R', Or.inr rfl, h1, h2'⟩
  · obtain ⟨c, hxc, habc⟩ := T7L.exists_conj_x0_u0_sp h2 hR'g hRg hx'R' hx'2 hx'1 hxR hx2 hx1 hb
      hbb ha haa
    have hp := T7Z.twin_plane1_eq h2 hR'g hRg hx'R' hx'2 hx'1 hxR hx2 hx1 hxc
    obtain ⟨c', h1, h2'⟩ := sp4_adapted_core_tw h2 hp (hab ▸ habc)
    exact ⟨c', R, Or.inl rfl, h1, h2'⟩

end Model

end B3C

end CFSG.ClassicalInvolution.Asc77
