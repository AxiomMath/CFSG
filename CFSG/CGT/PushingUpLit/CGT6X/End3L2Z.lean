module

public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End3

open Matrix

theorem sl2_center_bot {F : Type} [Field F] [CharP F 2] :
    Subgroup.center (SpecialLinearGroup (Fin 2) F) = ⊥ := by
  refine eq_bot_iff.mpr fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
  subst hr1
  rw [Subgroup.mem_bot]
  ext i j
  have := congrFun (congrFun hrA i) j
  simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm

@[expose] noncomputable def slEquivPsl (F : Type) [Field F] [CharP F 2] :
    SpecialLinearGroup (Fin 2) F ≃* ProjectiveSpecialLinearGroup (Fin 2) F :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F)))
    ⟨by
      rw [injective_iff_map_eq_one]
      intro x hx
      have := (QuotientGroup.eq_one_iff x).mp hx
      rwa [sl2_center_bot, Subgroup.mem_bot] at this,
    QuotientGroup.mk'_surjective _⟩

theorem center_eq_bot_of_model
    {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    {m : ℕ} (hm4 : 4 ≤ m)
    (hmod : CFSG.Assembly.LowTwoRank.StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 2 2 m) :
    Subgroup.center L = ⊥ := by
  classical
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have hK16 : 16 ≤ Nat.card K := by
    rw [hK]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm4
  have hK9 : Nat.card K ≠ 9 := by
    rw [hK]
    intro h
    have hev : Even (2 ^ m) := (Nat.even_pow' (by omega)).mpr even_two
    rw [h] at hev
    exact absurd hev (by decide)
  let e1 : L ⧸ Subgroup.center L ≃* ProjectiveSpecialLinearGroup (Fin 2) K :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  let π : L →* SpecialLinearGroup (Fin 2) K :=
    (slEquivPsl K).symm.toMonoidHom.comp
      (e1.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))
  have hπs : Function.Surjective π := by
    intro x
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) (e1.symm (slEquivPsl K x))
    refine ⟨y, ?_⟩
    simp only [π, MonoidHom.comp_apply, hy, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      MulEquiv.symm_apply_apply]
  have hπk : π.ker = Subgroup.center L := by
    ext x
    rw [MonoidHom.mem_ker]
    simp only [π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.SL2Closed.sl2_exists_section_of_central
    (k := K) (by omega) hK9 hπs hπk.le
  have : Group.IsPerfect L := hperf
  have h := CFSG.LieType.Steinberg.CentralExt.SL2Closed.ker_eq_bot_of_section π hπk.le σ hσ
  rwa [hπk] at h

theorem model_of_center_bot {L : Type} [Group L] [Finite L] {m : ℕ}
    (hZ : Subgroup.center L = ⊥)
    (hmod : CFSG.Assembly.LowTwoRank.StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 2 2 m) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSL 2 2 m ∧
      Nonempty (L ≃* SpecialLinearGroup (Fin 2) (GaloisField 2 m)) := by
  classical
  have hq : L ≃* L ⧸ Subgroup.center L :=
    MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center L))
      ⟨by
        rw [injective_iff_map_eq_one]
        intro x hx
        have := (QuotientGroup.eq_one_iff x).mp hx
        rwa [hZ, Subgroup.mem_bot] at this,
      QuotientGroup.mk'_surjective _⟩
  have hmod' := hmod
  obtain ⟨hadm, K, hF, hFin, hK, ⟨e⟩⟩ := hmod'
  refine ⟨⟨hadm, K, hF, hFin, hK, ⟨hq.trans e⟩⟩, ?_⟩
  obtain ⟨e2⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField
    (L ⧸ Subgroup.center L) 2 2 m hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (GaloisField 2 m) 2 := inferInstance
  exact ⟨(hq.trans e2).trans (slEquivPsl (GaloisField 2 m)).symm⟩

end CFSG.CGT.PushingUpLit.CGT6X.End3
