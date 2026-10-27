module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SylowU43
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.LieRank

open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.LieType.Multipliers.U43
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.U43Six
open CFSG.RankThree.PartTwo.Sec4.Census CFSG.Assembly.LowTwoRank

theorem five_le_pRank_of_cover {G : Type} [Group G] [Finite G] (φ : G →* X₀)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G) {Z : Subgroup G}
    (hZk : Z ≤ φ.ker) (hZp : ∀ z ∈ Z, z ^ 3 = 1) (hZ : 3 ≤ Nat.card Z) :
    5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ x ∈ thetaBar.range.comap φ, ∀ y ∈ thetaBar.range.comap φ, x * y = y * x :=
    fun x hx y hy => commute_of_mem_range hφ hker hx hy
  set U := TripleCoverLift.powOneSubgroup φ thetaBar.range 3 hcomm with hUdef
  have hUab : CFSG.Open.IsElemAbelian 3 U :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm _ (TripleCoverLift.mem_powOneSubgroup.mp a.2).1 _
      (TripleCoverLift.mem_powOneSubgroup.mp b.2).1)⟩⟩,
      fun x hx => (TripleCoverLift.mem_powOneSubgroup.mp hx).2⟩
  have hUP : IsPGroup 3 U := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact (TripleCoverLift.mem_powOneSubgroup.mp x.2).2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hUP
  let ψ : U →* X₀ := φ.comp U.subtype
  have hψr : ψ.range = thetaBar.range := by
    ext e
    constructor
    · rintro ⟨x, rfl⟩
      exact (TripleCoverLift.mem_powOneSubgroup.mp x.2).1
    · intro he
      obtain ⟨y, hy, hyp⟩ := exists_lift_of_mem_range hφ hker he
      exact ⟨⟨y, TripleCoverLift.mem_powOneSubgroup.mpr ⟨hy ▸ he, hyp⟩⟩, hy⟩
  have hZU : Z ≤ U := fun z hz => TripleCoverLift.mem_powOneSubgroup.mpr
    ⟨by rw [MonoidHom.mem_ker.mp (hZk hz)]; exact thetaBar.range.one_mem, hZp z hz⟩
  have hZψ : Z.subgroupOf U ≤ ψ.ker := fun w hw =>
    MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (hZk (Subgroup.mem_subgroupOf.mp hw)))
  have hψk : 3 ≤ Nat.card ψ.ker := by
    calc 3 ≤ Nat.card Z := hZ
      _ = Nat.card (Z.subgroupOf U) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv).symm
      _ ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hZψ
  have h243 : 3 ^ 5 ≤ 3 ^ k := by
    rw [← hk, ← Subgroup.card_ker_mul_card_range ψ, hψr, card_range_thetaBar]
    calc 3 ^ 5 = 3 * 3 ^ 4 := by norm_num
      _ ≤ Nat.card ψ.ker * 3 ^ 4 := Nat.mul_le_mul hψk le_rfl
  have hk5 : 5 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp h243
  exact hk5.trans (CFSG.SectionRank.le_pRank (by norm_num) le_top hUab hk)

theorem pRank_quotient_le_of_cover_U43 {L : Type} [Group L] [Finite L]
    (e : L ⧸ Subgroup.center L ≃* X₀) (h3 : 3 ∣ Nat.card (Subgroup.center L)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center L)) 3 h3
  have hzL : orderOf (z : L) = 3 := by rw [Subgroup.orderOf_coe]; exact hz
  let φ : L →* X₀ := (e : L ⧸ Subgroup.center L →* X₀).comp (QuotientGroup.mk' (Subgroup.center L))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center L := by
    ext x
    simp [φ]
  have hz3 : (z : L) ^ 3 = 1 := by rw [← hzL]; exact pow_orderOf_eq_one _
  have h5 := five_le_pRank_of_cover φ hφ hker.le (Z := Subgroup.zpowers (z : L))
    (by rw [hker]; exact Subgroup.zpowers_le.mpr z.2)
    (fun w hw => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow])
    (by rw [Nat.card_zpowers, hzL])
  have h4 := pRank_X₀_le_four
  have heq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
  omega

end CFSG.HardMathSupport.Timmesfeld.LieRank
