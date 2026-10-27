module

public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.Kernel
public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.Outer
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.GTwoFour

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem seitz_oddCore_eq_bot_of_simple {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (h2 : 2 ∣ Nat.card G) : standardComponentOddCore G = ⊥ := by
  refine le_bot_iff.1 (sSup_le ?_)
  rintro N ⟨hN, hNodd⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with rfl | rfl
  · exact le_rfl
  · rw [card_top] at hNodd
    exact absurd h2 hNodd.not_two_dvd_nat

theorem seitz_mem_center_of_oddCore_eq_bot {G : Type} [Group G] [Finite G]
    (hO : standardComponentOddCore G = ⊥) {t : G} (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hiso : ∀ g : G, g * t * g⁻¹ ∈ centralizer ({t} : Set G) → g * t * g⁻¹ = t) :
    t ∈ center G := by
  have := Fintype.ofFinite G
  obtain ⟨N, hN, hNodd, hNt⟩ := CFSG.Milestones.glauberman_zStar G t ht1 ht2
    fun g hg => hiso g (mem_centralizer_singleton_iff.2 hg)
  have hN1 : N ≤ standardComponentOddCore G := le_sSup ⟨hN, hNodd⟩
  rw [hO, le_bot_iff] at hN1
  refine mem_center_iff.2 fun g => ?_
  have h1 := hNt g
  rw [hN1, mem_bot, mul_inv_eq_one] at h1
  calc g * t = g * t * g⁻¹ * g := by group
    _ = t * g := by rw [h1]

theorem SeitzSetup.eq_t_of_isConj_of_mem
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type}
    [Field K] [CharP K 2] (S : SeitzSetup G L K) {y : G} (hyt : y ∈ centralizer ({S.t} : Set G))
    (hy : IsConj S.t y) : y = S.t :=
  S.eq_t_of_isConj (S.mem_L_of_mem_sup (S.mem_sup_of_isConj hyt hy) hy) hy

theorem exists_seitzSetup
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : standardComponentIsStandard L)
    (hcyc : ∃ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))))
    (hcard : Nat.card (center L) = 2) (hmodel : LieModel (L ⧸ center L) .G2 0 2 2) :
    ∃ (K : Type) (_ : Field K) (_ : CharP K 2), Nonempty (SeitzSetup G L K) := by
  rcases hmodel with ⟨hc, -⟩ | ⟨-, -, hX⟩ | ⟨-, hr, -⟩ | ⟨-, hs, -⟩
  · exact absurd hc (by decide)
  · obtain ⟨K, _, _, hK, ⟨ι⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hX.2
    have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
    have hchar : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two (k := 2) (by norm_num) (by rw [hK4]; norm_num)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center L) 2 (by simp [hcard])
    have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz; exact absurd hz (by decide)
    obtain ⟨z', -, hz'u⟩ := (Nat.card_eq_two_iff' (1 : center L)).1 hcard
    refine ⟨K, inferInstance, hchar, ⟨{
      standard := hL
      cyclic := hcyc
      card_field := hK4
      t := ((z : L) : G)
      t_mem := (z : L).2
      t_ne_one := fun h => hz1 (Subtype.ext (Subtype.ext h))
      mem_center_iff := fun l => ⟨fun hl => ?_, ?_⟩
      ι := ι }⟩⟩
    · by_cases hl1 : (⟨l, hl⟩ : center L) = 1
      · exact Or.inl (congrArg Subtype.val hl1)
      · right
        have h1 := hz'u _ hl1
        have h2 := hz'u _ hz1
        exact congrArg (fun x : center L => ((x : L) : G)) (h1.trans h2.symm)
    · rintro (rfl | h)
      · exact one_mem _
      · have : l = z := Subtype.ext h
        rw [this]
        exact z.2
  · exact absurd hr (by decide)
  · exact absurd hs (by decide)

theorem seitz_theorem4
    (G : Type) [Group G] [Finite G]
    (hO : standardComponentOddCore G = ⊥)
    (L : Subgroup G) (hL : standardComponentIsStandard L) (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G)))) (hcard : Nat.card (center L) = 2)
    (hmodel : CFSG.Blueprint.LieModel (L ⧸ center L) .G2 0 2 2) : L.Normal := by
  obtain ⟨K, _, _, ⟨T⟩⟩ := exists_seitzSetup hL ⟨S, hS⟩ hcard hmodel
  have hZ : T.t ∈ center G := seitz_mem_center_of_oddCore_eq_bot hO T.t_ne_one T.t_mul_t
    fun g hg => T.eq_t_of_isConj_of_mem hg (isConj_iff.2 ⟨g, rfl⟩)
  have htop : normalizer (L : Set G) = ⊤ := by
    rw [← T.centralizer_t_eq, eq_top_iff]
    intro g _
    exact mem_centralizer_singleton_iff.2 (mem_center_iff.1 hZ g)
  exact normalizer_eq_top_iff.1 htop

theorem seitz_theorem4_simple
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (L : Subgroup G) (hL : standardComponentIsStandard L) (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G)))) (hcard : Nat.card (center L) = 2)
    (hmodel : CFSG.Blueprint.LieModel (L ⧸ center L) .G2 0 2 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center L) 2 (by simp [hcard])
  have hzG : orderOf ((z : L) : G) = 2 := by rw [orderOf_coe, orderOf_coe, hz]
  have hz1 : ((z : L) : G) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hzG
    exact absurd hzG (by decide)
  have hO := seitz_oddCore_eq_bot_of_simple (G := G) (hzG ▸ orderOf_dvd_natCard _)
  have hLn := seitz_theorem4 G hO L hL S hS hcard hmodel
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with rfl | rfl
  · exact hz1 (mem_bot.1 (z : (⊥ : Subgroup G)).2)
  ·
    have hzc : ((z : (⊤ : Subgroup G)) : G) ∈ center G := mem_center_iff.2 fun g =>
      congrArg Subtype.val (mem_center_iff.1 z.2 ⟨g, mem_top g⟩)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exact hz1 (mem_bot.1 (h ▸ hzc))
    · have hcomm : commutator (⊤ : Subgroup G) = ⊥ := by
        rw [_root_.commutator_def, eq_bot_iff, commutator_le]
        intro a _ b _
        have hb : (b : G) ∈ center G := by
          rw [h]
          exact mem_top _
        rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact Subtype.ext (mem_center_iff.1 hb a)
      have hz1' : (z : (⊤ : Subgroup G)) = 1 := by
        have h1 : (z : (⊤ : Subgroup G)) ∈ commutator (⊤ : Subgroup G) := by
          rw [hL.1.1]
          exact mem_top _
        rw [hcomm] at h1
        exact mem_bot.1 h1
      exact hz1 (by rw [hz1']; rfl)

theorem childG2F4_G2
    (G : Type) [Group G] [Finite G] (L : Subgroup G)
    (hset : StandardSetting G L) (hcard : Nat.card (center L) = 2)
    (hmodel : LieModel (L ⧸ center L) .G2 0 2 2) : False := by
  have := hset.simple
  obtain ⟨S, hS⟩ := hset.cyclic
  exact seitz_theorem4_simple G L hset.standard S hS hcard hmodel

theorem childG2F4_of_F4
    (hF4 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
      Nat.card (center L) = 2 → LieModel (L ⧸ center L) .F4 0 2 1 → False) :
    ChildG2F4 := by
  intro G _ _ L hset hcard h
  rcases h with h | h
  · exact childG2F4_G2 G L hset hcard h
  · exact hF4 G L hset hcard h

end CFSG.EvenSmallLie.GTwoFour
