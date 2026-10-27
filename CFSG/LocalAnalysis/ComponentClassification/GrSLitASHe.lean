module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFinal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoM11
public import CFSG.LocalAnalysis.OddStandard.RankTwoHeFlat

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

namespace ASHe

theorem one_le_openPRank_of_mem {G : Type} [Group G] [Finite G] {X : Subgroup G} {x : G}
    (hx : x ∈ X) (hord : orderOf x = 2) : 1 ≤ CFSG.Open.pRank 2 X := by
  have hx2 : x ^ 2 = 1 := by rw [← hord, pow_orderOf_eq_one]
  have helem : CFSG.Open.IsElemAbelian 2 (zpowers x) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨i, hi⟩ := mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp b.2
      rw [coe_mul, coe_mul, ← hi, ← hj]
      exact (Commute.zpow_zpow_self x i j).eq
    · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
  have hbdd : BddAbove {k | ∃ E : Subgroup G, E ≤ X ∧ CFSG.Open.IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k} := by
    refine ⟨Nat.card G, fun k hk => ?_⟩
    obtain ⟨E, -, -, hE⟩ := hk
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
    omega
  exact le_csSup hbdd ⟨zpowers x, zpowers_le.mpr hx, helem, by rw [Nat.card_zpowers, hord]; rfl⟩

theorem not_normal {G : Type} [Group G] [Finite G]
    (hsF : IsSimpleGroup ↥(GeneralizedFitting.subgroup G)) {L : Subgroup G}
    (heven : Even (Nat.card ↥(centralizer (L : Set G))))
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) : ¬ L.Normal := by
  intro hN
  set F := GeneralizedFitting.subgroup G with hFdef
  set C := centralizer (L : Set G) with hCdef
  have hFn : F.Normal := GeneralizedFitting.normal G
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hCF : centralizer (F : Set G) ≤ F := GeneralizedFitting.centralizer_le G
  have hnorm : ((C ⊓ F).subgroupOf F).Normal := Subgroup.Normal.subgroupOf inferInstance F
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsF _ hnorm with h | h
  ·
    rw [Subgroup.subgroupOf_eq_bot] at h
    have hinf : C ⊓ F = ⊥ := disjoint_self.mp (h.mono_right inf_le_right)
    have hcomm : ⁅C, F⁆ = ⊥ := le_bot_iff.mp (hinf ▸ Subgroup.commutator_le_inf C F)
    have hCle : C ≤ F := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hCF
    have hC : C = ⊥ := by rw [← hinf, inf_eq_left.mpr hCle]
    rw [hC, Subgroup.card_bot] at heven
    exact Nat.not_even_one heven
  ·
    rw [Subgroup.subgroupOf_eq_top] at h
    have hFC : F ≤ C := h.trans inf_le_left
    have hLF : L ≤ F := (Subgroup.le_centralizer_iff.mp hFC).trans hCF
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have ha : (a : G) ∈ C := hFC (hLF a.2)
    exact Subtype.ext ((mem_centralizer_iff.mp ha (b : G) b.2).symm)

end ASHe

theorem aschbacherSeitzHeldInput_holds :
    AschbacherSeitzHeldInput := by
  intro G _ _ hK hsF _ L hstd ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup Blueprint.NativeSporadic.He := Sporadic.He.isSimpleGroup_He
  have heven : Even (Nat.card ↥(centralizer (L : Set G))) := hstd.2.1
  have hZHe : center Blueprint.NativeSporadic.He = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Blueprint.NativeSporadic.He) with
      h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_mul_ne_held
      have hb : b ∈ center Blueprint.NativeSporadic.He := by
        rw [h]
        exact mem_top b
      exact hab (mem_center_iff.mp hb a)
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_mul_ne_held
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hnn : ¬ L.Normal := ASHe.not_normal hsF heven hnab
  rw [AS76b.pRank_type_eq_open]
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centralizer (L : Set G))) 2
    (even_iff_two_dvd.mp heven)
  have hge : 1 ≤ CFSG.Open.pRank 2 (centralizer (L : Set G)) :=
    ASHe.one_le_openPRank_of_mem t.2 (by rw [Subgroup.orderOf_coe, ht])
  have hle : CFSG.Open.pRank 2 (centralizer (L : Set G)) ≤ 1 := by
    by_contra hlt
    have h2 : 2 ≤ CFSG.Open.pRank 2 (centralizer (L : Set G)) := by omega
    have hZL : center ↥L = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hz' : e z ∈ center Blueprint.NativeSporadic.He := by
        rw [mem_center_iff] at hz ⊢
        intro g
        obtain ⟨y, rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul, hz y]
      rw [hZHe, mem_bot, MulEquiv.map_eq_one_iff] at hz'
      exact mem_bot.mpr hz'
    have heQ : ↥L ⧸ center ↥L ≃* Blueprint.NativeSporadic.He :=
      (QuotientGroup.quotientMulEquivOfEq hZL).trans (QuotientGroup.quotientBot.trans e)
    have hstd' : CFSG.Open.standardComponentIsStandard L :=
      RankTwoM11.standardComponentIsStandard_of_isStandardSubgroup hstd
    have hyp : RankTwoStandard.RankTwoHyp G L := ⟨hK, hstd', hnn, h2⟩
    have hspor : Blueprint.NativeSporadic.IsSporadic (RankTwoStandard.rankTwoQuot L) .He := ⟨heQ⟩
    have hRT : OddStandard.RankTwoHeStandard :=
      OddStandard.rankTwoHeStandard_of_flat RankTwoFoundation.thm5Flat
    exact hRT G L hyp hspor
  omega

end CFSG.ComponentClassification.GrSLit
