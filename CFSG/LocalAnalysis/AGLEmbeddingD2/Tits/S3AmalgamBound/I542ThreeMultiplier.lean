module

public import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Final

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape CFSG.RankThree.PerfectCover

theorem card_ker_dvd_hopfMultiplier {R S : Type} [Group R] [Finite R] [Group.IsPerfect R]
    [Group S] [Finite S] (p : R →* S) (hp : Function.Surjective p)
    (hC : p.ker ≤ Subgroup.center R) : Nat.card p.ker ∣ Nat.card (hopfMultiplier S) := by
  haveI : Group.IsPerfect S := Group.IsPerfect.ofSurjective hp
  obtain ⟨-, h, -, -, -, -, ⟨e, -⟩⟩ := perfect_central_kernel_quotient_of_hopf_multiplier p hp hC
  rw [← Nat.card_congr e.toEquiv]
  exact Subgroup.card_quotient_dvd_card _

theorem center_eq_bot_of_dvd {R : Type} [Group R] [Finite R] [Group.IsPerfect R] {m : ℕ}
    (hm : Nat.card (hopfMultiplier (R ⧸ Subgroup.center R)) = m)
    (hcop : Nat.Coprime (Nat.card (Subgroup.center R)) m) : Subgroup.center R = ⊥ := by
  have hdvd := card_ker_dvd_hopfMultiplier (QuotientGroup.mk' (Subgroup.center R))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
  rw [QuotientGroup.ker_mk', hm] at hdvd
  have h1 : Nat.card (Subgroup.center R) = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
  exact Subgroup.card_eq_one.mp h1


theorem center_eq_bot_of_layerType
    {R : Type} [Group R] [Finite R] [Group.IsPerfect R]
    (hty : IsRankTwoLayerType (R ⧸ Subgroup.center R))
    (h2 : ¬ 2 ∣ Nat.card (Subgroup.center R)) (h3 : ¬ 3 ∣ Nat.card (Subgroup.center R)) :
    Subgroup.center R = ⊥ := by
  have hdvd : Nat.card (Subgroup.center R) ∣ Nat.card (hopfMultiplier (R ⧸ Subgroup.center R)) := by
    have := card_ker_dvd_hopfMultiplier (QuotientGroup.mk' (Subgroup.center R))
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
    rwa [QuotientGroup.ker_mk'] at this
  have hc2 : Nat.Coprime (Nat.card (Subgroup.center R)) 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
  have hc3 : Nat.Coprime (Nat.card (Subgroup.center R)) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
  rcases hty with h | h | h
  ·
    obtain ⟨e⟩ := h
    let p : R →* alternatingGroup (Fin 6) := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center R))
    have hp : Function.Surjective p := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : p.ker = Subgroup.center R := by
      ext g
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_eq_one_iff e e.injective, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    have hd := card_ker_dvd_hopfMultiplier p hp hker.le
    rw [hker, (CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six).2] at hd
    have hcop : Nat.Coprime (Nat.card (Subgroup.center R)) 6 := by
      have : (6 : ℕ) = 2 * 3 := by norm_num
      rw [this]; exact Nat.Coprime.mul_right hc2 hc3
    exact Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hd)
  ·
    obtain ⟨e₁⟩ := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.nonempty_gl32_of_statedClassicalModel h
    obtain ⟨e₂⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
    have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    let e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) ≃* (R ⧸ Subgroup.center R) :=
      e₂.symm.trans (e₁.symm.trans (MulEquiv.refl _))
    have key := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_two_hopfMultiplier_of_mulEquiv
      (k := ZMod 7) (by rw [ZMod.card]; norm_num) (by rw [ZMod.card]; norm_num) e
    obtain ⟨-, ⟨g⟩⟩ := key
    have hcard : Nat.card (hopfMultiplier (R ⧸ Subgroup.center R)) = 2 := by
      rw [← Nat.card_congr (hopfMultiplierEquivGriess (R ⧸ Subgroup.center R)).toEquiv,
        Nat.card_congr g.toEquiv]
      simp [Nat.card_eq_fintype_card, ZMod.card]
    rw [hcard] at hdvd
    exact Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hc2 dvd_rfl hdvd)
  ·
    obtain ⟨-, ⟨g⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_odd_row (X := R ⧸ Subgroup.center R)
      (n := 3) (p := 3) (f := 1) h (by decide)
    have hcard : Nat.card (hopfMultiplier (R ⧸ Subgroup.center R)) = 1 := by
      rw [← Nat.card_congr (hopfMultiplierEquivGriess (R ⧸ Subgroup.center R)).toEquiv,
        Nat.card_congr g.toEquiv]
      have h1 : CFSG.Blueprint.Multiplier.genericOrders .PSU 3 3 1 = (1, 1) := by
        simp [CFSG.Blueprint.Multiplier.genericOrders]
      have h2 : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 3 1 = (1, 1) := by
        simp [CFSG.Blueprint.Multiplier.exceptionalOrders]
      unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
      rw [h1, h2]
      simp
    rw [hcard] at hdvd
    exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp hdvd)

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
