module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.LeafOdd4
import CFSG.RankThree.PartTwo.Census.NineCoverU43
public import CFSG.LieType.Multipliers.U43Action

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4.Census

theorem KConf.twoLocalPrimeRank_le_two {K : Type} [Group K] [Finite K] {L V MK : Subgroup K}
    (hK : KConf K L V MK) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    twoLocalPrimeRank p K ≤ 2 := by
  refine csSup_le' ?_
  rintro _ ⟨H, ⟨R, hR, hR2, rfl⟩, rfl⟩
  exact CFSG.SectionRank.pRank_le hp.one_lt fun E hE hEel =>
    hK.card_le R hR hR2 p hp hp2 E hE hEel

theorem KConf.center_eq_bot_of_U43
    {K : Type} [Group K]
    [Finite K] {L V MK : Subgroup K} (hK : KConf K L V MK)
    (hm : StatedClassicalModel (K ⧸ Subgroup.center K) .PSU 4 3 1) :
    Subgroup.center K = ⊥ := by
  obtain ⟨eX⟩ := CFSG.LieType.Multipliers.U43.nonempty_mulEquiv_X₀ (Or.inl ⟨by decide, hm⟩)
  obtain ⟨eP⟩ := CFSG.LieType.Multipliers.U43.nonempty_mulEquiv_X₀ NineCoverU43.lieModel_U43
  let φ : K →* CFSG.LieType.Multipliers.U43.X₀ :=
    eX.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hφ : Function.Surjective φ := eX.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center K := by
    ext g
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  by_contra hZ
  obtain ⟨r, hr, hrZ⟩ := Nat.exists_prime_and_dvd fun h => hZ (Subgroup.card_eq_one.mp h)
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' r hrZ
  have h12 : (z : K) ^ 12 = 1 :=
    NineCoverU43.pow_twelve_eq_one_of_mem_center hK.quasisimple (eX.trans eP.symm) z.2
  have hr12 : r ∣ 4 * 3 := by
    rw [← hz, ← Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one h12
  have hr3 : r = 3 := by
    rcases (Nat.Prime.dvd_mul hr).mp hr12 with h4 | h3
    · have h2 : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
        (hr.dvd_of_dvd_pow (n := 2) h4)
      have hodd := Nat.odd_iff.mp hK.odd_card_center
      exact absurd (h2 ▸ hrZ) (by omega)
    · exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3
  have hrank := TripleCoverLift.succ_le_localRank_of_lift hφ hker.le Nat.prime_three
    (by norm_num) (hker ▸ hr3 ▸ hrZ) (E := NineCoverU43.theta.range)
    (fun _ hx _ hy => NineCoverU43.commute_of_mem_range hφ hker.le hx hy)
    (fun _ he => NineCoverU43.exists_lift_of_mem_range hφ hker.le he) NineCoverU43.tBar_ne_one
    NineCoverU43.tBar_sq (fun _ he => NineCoverU43.commute_tBar he) (r := 2)
    NineCoverU43.card_range_theta.ge
  have := hrank.trans (hK.twoLocalPrimeRank_le_two Nat.prime_three (by norm_num))
  omega

theorem u43Covers_holds :
    U43Covers := by
  intro K _ _ L V MK hK _ hm hZ
  exact (hZ (hK.center_eq_bot_of_U43 hm)).elim

end CFSG.SectionRank.QTK.Insp443
