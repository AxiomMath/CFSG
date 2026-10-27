module

public import CFSG.Milestones.CL_LIT_Monster_existence_Griess_Conway
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveTwoB
public import CFSG.Sporadic.Bridge.BBound
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5AssemblyInv
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenHypAux
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Tools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Monster.Existence CFSG.LocalAnalysis.GLTheoremA.H1017
  CFSG.HardMathSupport.Dickson.I271.TabMFive CFSG.Yardstones.Md0ec50421ce4

section Generic

variable {G : Type} [Group G] [Finite G]

private theorem orderOf_eq_two_of_mem_center {R : Subgroup G} (hR : timmesfeldIsExtraspecial ↥R)
    {z : G} (hz : z ∈ (Subgroup.center ↥R).map R.subtype) (hz1 : z ≠ 1) : orderOf z = 2 := by
  have hdvd := Subgroup.orderOf_dvd_natCard _ hz
  rw [card_center_map_eq_two hR rfl] at hdvd
  exact ((Nat.dvd_prime Nat.prime_two).1 hdvd).resolve_left fun h => hz1 (orderOf_eq_one_iff.1 h)

private theorem not_comm_of_extraspecial {R : Subgroup G} (hR : timmesfeldIsExtraspecial ↥R)
    (h : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) : False := by
  have hc : commutator ↥R = ⊥ :=
    (commutator_eq_bot_iff (G := ↥R)).2 ⟨⟨fun a b => Subtype.ext (h a a.2 b b.2)⟩⟩
  have h2 := hR.2.2.2
  rw [← hR.2.2.1, ← hR.2.1, hc, Subgroup.card_bot] at h2
  exact absurd h2 (by norm_num)

private theorem false_of_quot_center {K : Type*} [Group K] [Finite K] {p r : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hrk : GLATwoLocalRank p K < r) {z : G} (hz2 : orderOf z = 2)
    (hZ : (Subgroup.center (cent z)).map (cent z).subtype = Subgroup.zpowers z)
    (e : cent z ⧸ Subgroup.center (cent z) ≃* K) {B R0 : Subgroup G}
    (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ r) (hR0 : timmesfeldIsExtraspecial ↥R0)
    (hz : z ∈ (Subgroup.center ↥R0).map R0.subtype)
    (hBR0 : B ≤ Subgroup.normalizer (R0 : Set G)) : False := by
  have hBz : B ≤ cent z := fun b hb => Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 (normalizer_le_centralizer_center hR0 rfl (hBR0 hb)) z hz).symm
  have hRz : R0 ≤ cent z := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 ((mem_center_map_iff.1 hz).2 x hx)
  have hN : IsPGroup 2 (Subgroup.center (cent z)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [← Subgroup.card_map_of_injective (cent z).subtype_injective, hZ, Nat.card_zpowers, hz2,
      pow_one]
  obtain ⟨hF, hFc⟩ := H1016M5.isElemAbelian_card_map_quot hp hp2 hN e (hB.subgroupOf (cent z))
  have hT1 : (R0.subgroupOf (cent z)).map (e.toMonoidHom.comp (QuotientGroup.mk' _)) ≠ ⊥ := by
    intro hbot
    have hc : ∀ t (ht : t ∈ R0), (⟨t, hRz ht⟩ : cent z) ∈ Subgroup.center (cent z) := by
      intro t ht
      have h0 : e (QuotientGroup.mk ⟨t, hRz ht⟩) = 1 :=
        MonoidHom.mem_ker.1 ((Subgroup.map_eq_bot_iff _).1 hbot
          (show (⟨t, hRz ht⟩ : cent z) ∈ R0.subgroupOf (cent z) from ht))
      rwa [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h0
    exact not_comm_of_extraspecial hR0 fun x hx y hy =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.1 (hc x hx) ⟨y, hRz hy⟩)).symm
  have hFT0 : B.subgroupOf (cent z) ≤
      Subgroup.normalizer ((R0.subgroupOf (cent z) : Subgroup (cent z)) : Set (cent z)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hRz]
    exact Subgroup.comap_mono hBR0
  have hk := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_glaTwoLocalRank_of_le_normalizer
    hp.one_lt hT1 (hR0.1.comap_subtype.map _) hF
    ((Subgroup.map_mono hFT0).trans (Subgroup.le_normalizer_map _))
    (hFc.trans ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBz).toEquiv).trans hBc))
  exact absurd hrk (not_lt.2 hk)

end Generic


theorem isConj_xGriess_of_extraspecial {p r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hr : 0 < r)
    (hBaby : TwoRankLe p .B (r - 1)) {B R0 : Subgroup MGriess} {z : MGriess}
    (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ r) (hR0 : timmesfeldIsExtraspecial ↥R0)
    (hz : z ∈ (Subgroup.center ↥R0).map R0.subtype) (hz1 : z ≠ 1)
    (hBR0 : B ≤ Subgroup.normalizer (R0 : Set MGriess)) : IsConj xGriess z := by
  have hE : MonsterExistenceStatement MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  haveI : Finite MGriess := hE.1.1
  have hz2 := orderOf_eq_two_of_mem_center hR0 hz hz1
  obtain ⟨-, a, z₀, -, -, -, hcls, hA, hZ₀, -⟩ := id hE
  rcases hcls z hz2 with h | h
  · haveI : Finite CFSG.Blueprint.NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
    have hcat : catalogIs CFSG.Blueprint.NativeSporadic.B (S8.sporIs .B) :=
      ⟨TauCeti.CFSGIndex.sporadic .B, rfl, CFSG.Sporadic.Bridge.B.nonempty_mulEquiv⟩
    have hrk : GLATwoLocalRank p CFSG.Blueprint.NativeSporadic.B < r :=
      (hBaby _ hcat).trans_lt (Nat.sub_lt hr one_pos)
    obtain ⟨-, hZ, ⟨e⟩⟩ := hA z h
    exact (false_of_quot_center (Fact.out : p.Prime) hp2 hrk hz2 hZ e hB hBc hR0 hz hBR0).elim
  · exact isConj_xGriess_of_card hE card_nativeB hz2 (hZ₀ z h).2.2.2.2.1

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
