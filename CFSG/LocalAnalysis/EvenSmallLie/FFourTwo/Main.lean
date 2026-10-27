module

public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.Outer
public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.Main
public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.Inner

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.FFourTwo

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_setup
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) (hcard : Nat.card (center L) = 2)
    (hmodel : LieModel (L ⧸ center L) .F4 0 2 1) :
    ∃ (K : Type) (_ : Field K), Nonempty (Setup G L K) := by
  rcases hmodel with ⟨hc, -⟩ | ⟨-, -, hX⟩ | ⟨-, hr, -⟩ | ⟨-, hs, -⟩
  · exact absurd hc (by decide)
  · obtain ⟨K, _, _, hK, ⟨ι⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hX.2
    have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center L) 2 (by simp [hcard])
    have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz; exact absurd hz (by decide)
    obtain ⟨z', -, hz'u⟩ := (Nat.card_eq_two_iff' (1 : center L)).1 hcard
    refine ⟨K, inferInstance, ⟨{
      std := hset
      card_field := hK2
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

theorem childG2F4_F4
    (G : Type) [Group G] [Finite G] (L : Subgroup G)
    (hset : StandardSetting G L) (hcard : Nat.card (center L) = 2)
    (hmodel : LieModel (L ⧸ center L) .F4 0 2 1) : False := by
  obtain ⟨K, _, ⟨S⟩⟩ := exists_setup hset hcard hmodel
  have := hset.simple
  exact false_of_fours_group hset.nonab S.orderOf_t (M := L ⊔ centralizer (L : Set G))
    (mem_sup_left S.t_mem) S.relIndex_le_two (fun y hy hyc => S.eq_t_of_isConj_of_mem_sup hy hyc)
    (fun y hy hyM hyc => S.exists_four hy hyM hyc)

theorem childG2F4 :
    ChildG2F4 := GTwoFour.childG2F4_of_F4 childG2F4_F4

end CFSG.EvenSmallLie.FFourTwo
