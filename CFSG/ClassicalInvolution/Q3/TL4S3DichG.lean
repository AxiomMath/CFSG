module

public import CFSG.ClassicalInvolution.Q3.TL4S3DichB
public import CFSG.ClassicalInvolution.Q3.Q3AM289Dich
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHG2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.S3Dich

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.Disconnected.AschTight.S19F
  CFSG.ClassicalInvolution.Disconnected.AschTight.S19G CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance.Q27
open scoped MatrixGroups


theorem invDich_adjointG2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (hq : p ^ e = 3) {R : Subgroup ↥(adjointGroup .G2 (GaloisField p e))}
    (hR : R ∈ fundamentalSubgroups .G2 (g2Datum (GaloisField p e)))
    {L₀ : Subgroup ↥(adjointGroup .G2 (GaloisField p e))} (hL₀ : IsSylow2In L₀ R) :
    InvDich ↥(adjointGroup .G2 (GaloisField p e)) L₀ := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .G2 0 p e :=
    ⟨Fact.out, he, rfl, by omega⟩
  have hK : Nat.card (GaloisField p e) = 3 := by rw [GaloisField.card p e (by omega), hq]
  obtain ⟨e0⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three hK
  have hchar : ringChar (GaloisField p e) ≠ 2 := by
    rw [ringChar.eq (GaloisField p e) p]
    exact hp2
  obtain ⟨i, g, hRg⟩ := exists_eq_conjSub_g2Chart hR
  set ι : SL(2, ZMod 3) →* ↥(adjointGroup .G2 (GaloisField p e)) :=
    (MulAut.conj g).toMonoidHom.comp ((g2Chart (GaloisField p e) i).comp e0.symm.toMonoidHom)
    with hιdef
  have hι : Function.Injective ι :=
    (MulAut.conj g).injective.comp ((g2Chart_injective hchar i).comp e0.symm.injective)
  have hιR : ι.range = R := by
    rw [hιdef, hRg, MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective e0.symm.toMonoidHom e0.symm.surjective,
      ← MonoidHom.range_eq_map]
    rfl
  have hO : InvolutionOddCoreTrivial ↥(adjointGroup .G2 (GaloisField p e)) :=
    thm5IH_g2_oddCoreTrivial hp2 hadm
  have hZ : Subgroup.center ↥(adjointGroup .G2 (GaloisField p e)) = ⊥ :=
    CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inl rfl) 0 he
  have hU : IsUniqueInvolution R (ι (-1)) := by
    rw [← hιR]
    exact isUniqueInvolution_range ι hι
  have hT : ∀ h, IsUniqueInvolution (conjSub h ι.range) (ι (-1)) →
      conjSub h ι.range = ι.range := by
    rw [hιR]
    intro h hh
    exact noTwinsFund_g2 hp2 hadm R hR (ι (-1)) hU h hh
  have hfg : InvDich ↥(adjointGroup .G2 (GaloisField p e)) ι.range := by
    rw [hιR]
    exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.invol_fixes_of_fg0 hZ (fg0Model_g2 hp2 he hR)
  rw [← hιR] at hL₀
  exact invDich_of_upgrade ι hι hO (normalizes_of_noTwins ι hι hT) hfg hL₀

theorem invDich_g2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) (hq : p ^ e = 3)
    {R : Subgroup (modelUniv .G2 0 p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .G2 (modelUniv .G2 0 p e Fact.out).D)
    {L₀ : Subgroup (modelUniv .G2 0 p e Fact.out).K} (hL₀ : IsSylow2In L₀ R) :
    InvDich (modelUniv .G2 0 p e Fact.out).K L₀ :=
  invDich_adjointG2 hp2 he hq hR hL₀

end CFSG.ClassicalInvolution.Q3.TL4.S3Dich
