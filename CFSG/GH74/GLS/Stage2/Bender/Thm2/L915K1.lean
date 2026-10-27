module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915K1b
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Cases
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Char
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open CFSG.GH74.KGroups.L3Eps CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem k1_congr_conj {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem k1_congr_apply {G H : Type*} [Group G] [Group H] (e : G ≃* H) (r : MulAut G) (y : H) :
    MulAut.congr e r y = e (r (e.symm y)) := by
  simp [MulAut.congr_apply]

theorem aut_pgroup_trivial_of_centralizes_involution {X : Type} [Group X] {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) (hX : CFSG.Blueprint.LieModel X .PSL 3 p n)
    {ζ : X} (hζ2 : ζ * ζ = 1) (hζ1 : ζ ≠ 1)
    {R : Subgroup (MulAut X)} (hR : IsPGroup p ↥R) (hRζ : ∀ r ∈ R, r ζ = ζ)
    (hRn : ∀ d : X, d * ζ = ζ * d → ∀ r ∈ R, MulAut.conj d * r * (MulAut.conj d)⁻¹ ∈ R) :
    R = ⊥ := by
  have hpp : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, iF, fF, hFcard, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hX
  have hpF : p ∣ Nat.card F := by
    rw [hFcard]
    exact dvd_pow_self p (by omega)
  have hchar : CharP F p := charP_of_dvd_card p hpF
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff F p 2).mp h'))
  obtain ⟨e', he'⟩ := exists_equiv_tInv h2 e hζ2 hζ1
  have hsymm : e'.symm tInv = ζ := by rw [← he']; exact e'.symm_apply_apply ζ
  set R' : Subgroup (MulAut (projectiveSL 3 F)) := R.map (MulAut.congr e').toMonoidHom with hR'
  have hR'p : IsPGroup p ↥R' := hR.map _
  have hR'ζ : ∀ r' ∈ R', r' tInv = tInv := by
    rintro _ ⟨r, hr, rfl⟩
    show MulAut.congr e' r tInv = tInv
    rw [k1_congr_apply, hsymm, hRζ r hr, he']
  have hR'n : ∀ d : projectiveSL 3 F, d * tInv = tInv * d → ∀ r' ∈ R',
      MulAut.conj d * r' * (MulAut.conj d)⁻¹ ∈ R' := by
    rintro d hd _ ⟨r, hr, rfl⟩
    have hdζ : e'.symm d * ζ = ζ * e'.symm d := by
      apply e'.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, he']
      exact hd
    refine ⟨MulAut.conj (e'.symm d) * r * (MulAut.conj (e'.symm d))⁻¹, hRn _ hdζ r hr, ?_⟩
    show MulAut.congr e' (MulAut.conj (e'.symm d) * r * (MulAut.conj (e'.symm d))⁻¹) = _
    rw [map_mul, map_mul, map_inv, k1_congr_conj, MulEquiv.apply_symm_apply]
    rfl
  have hbot := k1_core h2 p hpF hR'p hR'ζ hR'n
  refine eq_bot_iff.mpr fun r hr => ?_
  rw [Subgroup.mem_bot]
  have hmem : MulAut.congr e' r ∈ R' := ⟨r, hr, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (MulAut.congr e').injective (hmem.trans (map_one _).symm)

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
