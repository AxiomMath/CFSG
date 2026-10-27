module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepSix
import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma55
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiagK
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Three
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.ComponentClassification.PerfectAutomorphisms

theorem kFactAltSixFixed_holds : KFactAltSixFixed := by
  intro Y _ _ hY ⟨e⟩ φ n hφn hφ1
  haveI : Group.IsPerfect Y := ⟨hY.1⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hψn : onCenterQuotient φ ^ (3 ^ n) = 1 := by
    have h := map_pow (centerQuotientHom Y) φ (3 ^ n)
    rw [hφn, map_one] at h
    exact h.symm
  have hψ1 : onCenterQuotient φ ≠ 1 := fun h => hφ1 (onCenterQuotient_eq_one_imp φ h)
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp
    (CFSG.RankThree.PartTwo.Sec15.Proof15Res8Diag.mem_inner_of_pow_eq_one_six e hψn)
  have hcen : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ :=
    CFSG.ComponentClassification.GSThmB.center_eq_bot_of_mulEquiv_alternating (by norm_num) e
  have hxn : x ^ (3 ^ n) = 1 := by
    have h1 : MulAut.conj (x ^ (3 ^ n)) = 1 := by rw [map_pow, hx, hψn]
    have hmem : x ^ (3 ^ n) ∈ Subgroup.center (Y ⧸ Subgroup.center Y) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := congrArg (fun f : MulAut (Y ⧸ Subgroup.center Y) => f g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at hg
      calc g * x ^ 3 ^ n = x ^ 3 ^ n * g * (x ^ 3 ^ n)⁻¹ * x ^ 3 ^ n := by rw [hg]
        _ = x ^ 3 ^ n * g := by group
    rw [hcen] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hψ1 (by rw [← hx, map_one])
  have h3x : 3 ∣ orderOf x := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hxn)
    rcases j with _ | j
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hj)) hx1
    · rw [hj, pow_succ]
      exact dvd_mul_left 3 _
  have hao : orderOf (e (x ^ (orderOf x / 3))) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_pow_orderOf_div (orderOf_pos x).ne' h3x
  have hC9 := CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_centralizer_of_orderOf_eq_three hao
  have hP : IsPGroup 3 ↥(Subgroup.centralizer
      ({e (x ^ (orderOf x / 3))} : Set (alternatingGroup (Fin 6)))) :=
    IsPGroup.of_card (n := 2) (by rw [hC9]; norm_num)
  let f : ↥(φ.toMonoidHom.eqLocus (MonoidHom.id Y)) →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center Y)).comp
      (φ.toMonoidHom.eqLocus (MonoidHom.id Y)).subtype)
  have hf : ∀ c, f c = e (QuotientGroup.mk' (Subgroup.center Y) (c : Y)) := fun _ => rfl
  have hrange : f.range ≤ Subgroup.centralizer
      ({e (x ^ (orderOf x / 3))} : Set (alternatingGroup (Fin 6))) := by
    rintro _ ⟨c, rfl⟩
    have hφc : φ (c : Y) = c := c.2
    have hfix : onCenterQuotient φ (QuotientGroup.mk' (Subgroup.center Y) (c : Y)) =
        QuotientGroup.mk' (Subgroup.center Y) (c : Y) := by
      rw [onCenterQuotient_apply_mk, hφc]
    rw [← hx, MulAut.conj_apply] at hfix
    have hcx : Commute (QuotientGroup.mk' (Subgroup.center Y) (c : Y)) x := by
      have h' : x * QuotientGroup.mk' (Subgroup.center Y) (c : Y) =
          QuotientGroup.mk' (Subgroup.center Y) (c : Y) * x := by
        calc x * QuotientGroup.mk' (Subgroup.center Y) (c : Y) =
            x * QuotientGroup.mk' (Subgroup.center Y) (c : Y) * x⁻¹ * x := by group
          _ = QuotientGroup.mk' (Subgroup.center Y) (c : Y) * x := by rw [hfix]
      exact h'.symm
    have hca := (hcx.pow_right (orderOf x / 3)).map e
    rw [hf]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hca.eq
  have hker : f.ker ≤ Subgroup.center ↥(φ.toMonoidHom.eqLocus (MonoidHom.id Y)) := by
    intro c hc
    have h1 : e (QuotientGroup.mk' (Subgroup.center Y) (c : Y)) = 1 := by
      rw [← hf]
      exact hc
    rw [MulEquiv.map_eq_one_iff] at h1
    have hcZ : (c : Y) ∈ Subgroup.center Y := (QuotientGroup.eq_one_iff _).mp h1
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hcZ) g)
  haveI : Group.IsNilpotent ↥f.range := (hP.to_le hrange).isNilpotent
  have hnil : Group.IsNilpotent ↥(φ.toMonoidHom.eqLocus (MonoidHom.id Y)) :=
    isNilpotent_of_ker_le_center f.rangeRestrict (by rw [MonoidHom.ker_rangeRestrict]; exact hker)
  exact CFSG.BenderSuzuki.External.hkt_hasNormalPComplement_of_nilpotent hnil

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
