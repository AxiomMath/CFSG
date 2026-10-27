module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021FixCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021FixMax
import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021RankHolds
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactSeitzOutside

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.I2015

section Certs

theorem t2021FixFact_holds : T2021FixFact := by
  intro H _ _ p 𝔅 _ _ ψ T hp hp2 hchev hperf _ hexp _ hT2 hTinv hTO hTmax _ g hg
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := GLAPPrimeCore p H with hN
  let ψQ : 𝔅 →* MulAut (ppQuot p H) := (MulAut.mapQuotient N).comp ψ
  have hψQ : ∀ (g : 𝔅) (l : H), ψQ g (QuotientGroup.mk l) = QuotientGroup.mk (ψ g l) :=
    fun g l => MulAut.mapQuotient_mk N (ψ g) l
  set Z := Subgroup.center (ppQuot p H) with hZ
  let ψS : 𝔅 →* MulAut (psimpleOf p H) := (MulAut.mapQuotient Z).comp ψQ
  have hψS : ∀ (g : 𝔅) (x : ppQuot p H), ψS g (QuotientGroup.mk x) = QuotientGroup.mk (ψQ g x) :=
    fun g x => MulAut.mapQuotient_mk Z (ψQ g) x
  have h𝔅 : IsPGroup p 𝔅 := fun g => ⟨1, by rw [pow_one]; exact hexp g⟩
  have hs : IsSimpleGroup (psimpleOf p H) :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.isSimpleGroup_of_isChevSimple_two hchev
  have hna : ∃ a b : psimpleOf p H, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have htop : commutator (psimpleOf p H) = ⊤ := by
      have h1 := Subgroup.map_commutator (⊤ : Subgroup (ppQuot p H)) ⊤ (QuotientGroup.mk' Z)
      rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z)] at h1
      rw [commutator_def, ← h1, ← commutator_def, hperf, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective Z)]
    have hbot : commutator (psimpleOf p H) = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _ y _
      exact hc y x
    have h1 : (⊤ : Subgroup (psimpleOf p H)) = ⊥ := htop.symm.trans hbot
    obtain ⟨a, b, hab⟩ := exists_pair_ne (psimpleOf p H)
    have ha : a = 1 := by
      have : a ∈ (⊤ : Subgroup (psimpleOf p H)) := trivial
      rw [h1, Subgroup.mem_bot] at this
      exact this
    have hb : b = 1 := by
      have : b ∈ (⊤ : Subgroup (psimpleOf p H)) := trivial
      rw [h1, Subgroup.mem_bot] at this
      exact this
    exact hab (ha.trans hb.symm)
  set Tb : Subgroup (psimpleOf p H) := (T.map (QuotientGroup.mk' N)).map (QuotientGroup.mk' Z) with hTb
  have hTb2 : IsPGroup 2 Tb := (hT2.map _).map _
  have hZodd : Odd (Nat.card Z) := t2021Fix_odd_center hp hp2
  have hTb1 : Tb ≠ ⊥ := by
    intro hbot
    apply hTO
    intro t ht
    have hq : (QuotientGroup.mk t : ppQuot p H) ∈ Z := by
      have h1 : QuotientGroup.mk' Z (QuotientGroup.mk' N t) ∈ Tb := ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨k, hk⟩ := (hT2.map (QuotientGroup.mk' N)) ⟨_, ⟨t, ht, rfl⟩⟩
    have hk' : (QuotientGroup.mk t : ppQuot p H) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hord : orderOf (⟨_, hq⟩ : Z) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext hk')
    have hodd : Odd (orderOf (⟨_, hq⟩ : Z)) := hZodd.of_dvd_nat (orderOf_dvd_natCard _)
    have h1 : orderOf (⟨_, hq⟩ : Z) = 1 := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [hj, h0, pow_zero]
      · exfalso
        rw [hj] at hodd
        exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, h0.ne'⟩)
    have h2 : (QuotientGroup.mk t : ppQuot p H) = 1 :=
      congrArg Subtype.val (orderOf_eq_one_iff.1 h1)
    exact (QuotientGroup.eq_one_iff t).1 h2
  have hrad := t2021Fix_radical hp hp2 ψ ψQ hψQ ψS hψS h𝔅 hT2 hTinv hTmax
  have hgT : ∀ x ∈ Tb, ψS g x = x := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    simp only [QuotientGroup.mk'_apply]
    rw [hψS, hψQ]
    congr 1
    exact QuotientGroup.eq_iff_div_mem.2 (by rw [div_eq_mul_inv]; exact hg t ht)
  have hgp : ψS g ^ p = 1 := by rw [← map_pow, hexp, map_one]
  have hcore : ψS g = 1 := t2021Fix_core hs hna hchev hp hp2 hTb2 hTb1 hrad hgp hgT
  exact t2021Fix_trivAut hperf (ψ g) (ψQ g) (hψQ g) hcore

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T2021

end
