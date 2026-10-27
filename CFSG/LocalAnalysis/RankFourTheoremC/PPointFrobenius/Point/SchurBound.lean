module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Point.Quasi
public import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.RankThree.PerfectCover CFSG.LieType.Steinberg.CentralExt.SL2Closed

theorem ptSchurBound_holds :
    PtSchurBound := by
  intro L _ _ p n _ hp5 hn hperf ⟨e⟩
  have hp : p.Prime := Fact.out
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p n) = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p n (by omega)
  have hpn : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn
  have hp2 : 25 ≤ p ^ 2 := by nlinarith
  have h5 : 5 ≤ Fintype.card (GaloisField p n) := by
    rw [hcard]
    omega
  have h9 : Fintype.card (GaloisField p n) ≠ 9 := by
    rw [hcard]
    omega
  obtain ⟨hcomm, ⟨hM⟩⟩ := psl_two_hopfMultiplier h5 h9
  haveI hperfS : Group.IsPerfect PSL(2, GaloisField p n) := Group.isPerfect_def.mpr hcomm
  haveI hfinS : Finite PSL(2, GaloisField p n) := Finite.of_equiv _ e.toEquiv
  set S := PSL(2, GaloisField p n) with hS
  let q : L →* S := (e : L ⧸ center L →* S).comp (QuotientGroup.mk' (center L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center L := by
    ext l
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk l) = 1 ↔ _
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff l
  obtain ⟨-, -, -, f, hf⟩ := perfect_central_kernel_quotient_of_schur_multiplier q hq hker.le
  obtain ⟨-, ⟨F⟩⟩ := hopf_formula_hopfMultiplier (S := S)
  set g := Nat.gcd 2 (Fintype.card (GaloisField p n) - 1) with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hg2 : g ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  haveI : NeZero g := ⟨hg0.ne'⟩
  let Φ := F.trans hM
  haveI : Finite (Multiplicative (groupHomology.H2 (Rep.trivial ℤ S ℤ))) :=
    Finite.of_equiv _ Φ.symm.toEquiv
  have hcardH : Nat.card (Multiplicative (groupHomology.H2 (Rep.trivial ℤ S ℤ))) = g := by
    rw [Nat.card_congr Φ.toEquiv, Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod g) ≃ ZMod g),
      Nat.card_eq_fintype_card, ZMod.card]
  have hrange : Nat.card f.range ≤
      Nat.card (Multiplicative (groupHomology.H2 (Rep.trivial ℤ S ℤ))) :=
    Nat.card_le_card_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  calc Nat.card (center L) = Nat.card q.ker := by rw [hker]
    _ = Nat.card f.range := by rw [hf]
    _ ≤ g := hcardH ▸ hrange
    _ ≤ 2 := hg2

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
