module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeNodeLevi
public import CFSG.ClassicalInvolution.Generic.TypeCSmallRecognitionProof
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeNodeOrderP
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeNodeBridge

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

theorem c3ShortNodeA2 (p f : ℕ) [Fact p.Prime] : C3ShortNodeA2 p f := by
  intro G _ _ _ hnab K z S hS
  have cs := cSetupW_of_routeDSetup S hS
  have hconn := S.conn
  have hZ : Subgroup.center G = ⊥ := center_eq_bot hnab
  obtain ⟨Fr⟩ := exists_frameW cs
  obtain ⟨P⟩ := exists_leviParams cs Fr
  refine ⟨Fr, P.T₀, P.T₁, P.isShortNode₀, P.isShortNode₁, ?_⟩
  set Y : Subgroup G := P.T₀ ⊔ P.T₁ with hY
  have hΛ := P.inClass hconn hZ
  have hLie : LieSystemMod p f P.family := S.below ↥Y (P.card_lt hZ) P.family hΛ
  have hO : classicalInvolutionOddCore ↥Y ≤ Subgroup.center ↥Y :=
    oddCore_levi_le_center cs hconn hZ Fr P.x₀_mem P.x₁_mem P.x₂_mem P.hn01 P.hz01 P.hn12 P.hz12
  have hS₀ : P.T₀.subgroupOf Y ∈ P.family := ⟨1, Or.inl (conjSub_one _).symm⟩
  have hS₁ : P.T₁.subgroupOf Y ∈ P.family := ⟨1, Or.inr (conjSub_one _).symm⟩
  obtain ⟨e₀⟩ := P.nonempty_equiv₀
  obtain ⟨e₁⟩ := P.nonempty_equiv₁
  have hex₀ : classicalInvolutionOddCore (P.T₀.subgroupOf Y) = ⊥ :=
    oddCore_subgroupOf_eq_bot P.T₀_le_Y e₀.symm cs.odd_card (by have := cs.four_le; omega)
  have hex₁ : classicalInvolutionOddCore (P.T₁.subgroupOf Y) = ⊥ :=
    oddCore_subgroupOf_eq_bot P.T₁_le_Y e₁.symm cs.odd_card (by have := cs.four_le; omega)
  have hz2 : Fr.zf 2 ∈ P.T₀ := P.zf_two_mem hconn hZ
  have hz0 : Fr.zf 0 ∈ P.T₁ := P.zf_zero_mem hconn hZ
  have hnc : ¬ Commutes (P.T₀.subgroupOf Y) (P.T₁.subgroupOf Y) := by
    intro h
    refine P.not_commutes hconn hZ fun a ha b hb => ?_
    have := h ⟨a, P.T₀_le_Y ha⟩ (Subgroup.mem_subgroupOf.mpr ha) ⟨b, P.T₁_le_Y hb⟩
      (Subgroup.mem_subgroupOf.mpr hb)
    exact congrArg Subtype.val this
  have hsolv : Group.IsSolvable ↥(Subgroup.centralizer ((P.T₀.subgroupOf Y : Subgroup ↥Y) :
      Set ↥Y)) := by
    have hW := P.solvable_centralizer hconn hZ
    let φ : ↥(Subgroup.centralizer ((P.T₀.subgroupOf Y : Subgroup ↥Y) : Set ↥Y)) →*
        ↥(Y ⊓ Subgroup.centralizer (P.T₀ : Set G)) :=
      { toFun := fun c => ⟨(c : ↥Y), (c : ↥Y).2, Subgroup.mem_centralizer_iff.mpr fun t ht =>
          congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp c.2 ⟨t, P.T₀_le_Y ht⟩
            (Subgroup.mem_subgroupOf.mpr ht))⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Group.isSolvable_of_isSolvable_injective (f := φ) fun a b h =>
      Subtype.ext (Subtype.ext (congrArg (fun w : ↥(Y ⊓ Subgroup.centralizer (P.T₀ : Set G)) =>
        (w : G)) h))
  have hnop : ∀ c ∈ Subgroup.centralizer ((P.T₀.subgroupOf Y : Subgroup ↥Y) : Set ↥Y),
      orderOf c ≠ p := by
    intro c hc hcp
    have hcp' : (c : G) ^ p = 1 := by
      have := pow_orderOf_eq_one c
      rw [hcp] at this
      exact congrArg Subtype.val this
    have h1 : (c : G) = 1 := P.eq_one_of_pow_eq_one hconn hZ (c : ↥Y).2
      (fun t ht => congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc ⟨t, P.T₀_le_Y ht⟩
        (Subgroup.mem_subgroupOf.mpr ht))) hcp'
    have h2 : c = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hcp
    exact (Fact.out : p.Prime).one_lt.ne hcp
  obtain ⟨t, htT, hto, hnorm⟩ := P.exists_torus_normalizing
  have hγ : ∃ a ∈ P.T₀.subgroupOf Y, orderOf a = p ^ f - 1 ∧
      conjSub a (P.T₁.subgroupOf Y) = P.T₁.subgroupOf Y := by
    refine ⟨⟨t, P.T₀_le_Y htT⟩, Subgroup.mem_subgroupOf.mpr htT, ?_, ?_⟩
    · rw [Subgroup.orderOf_mk]
      exact hto
    · rw [conjSub_subgroupOf]
      exact congrArg (fun L => L.subgroupOf Y) hnorm
  obtain ⟨W, hW⟩ := LieBridge.lieA2Bridge' p f cs.odd cs.five ↥Y P.family hΛ hLie hO _ _
    ⟨Fr.zf 2, P.T₀_le_Y hz2⟩ ⟨Fr.zf 0, P.T₁_le_Y hz0⟩ hS₀ hS₁ hex₀ hex₁
    (Subgroup.mem_subgroupOf.mpr hz2) (Subgroup.mem_subgroupOf.mpr hz0)
    (by rw [Subgroup.orderOf_mk]; exact (Fr.clsW cs 2).orderOf_eq_two)
    (by rw [Subgroup.orderOf_mk]; exact (Fr.clsW cs 0).orderOf_eq_two)
    (Subtype.ext (Fr.zf_commW cs 2 0))
    (fun h => zf_ne_of_ne cs Fr (i := 2) (j := 0) (by decide) (congrArg Subtype.val h))
    hnc hsolv hnop hγ
  have hker : (Y.subtype).ker ≤ Subgroup.center ↥Y := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr Y.subtype_injective]
    exact bot_le
  have hmap := CFSG.ClassicalInvolution.Balance.linearBlockStandardPair_map_of_ker_le_center hW
    Y.subtype hker
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr P.T₀_le_Y, inf_eq_left.mpr P.T₁_le_Y] at hmap
  exact ⟨_, hmap⟩

theorem psp6Recognition (p f : ℕ) [Fact p.Prime] : PSp6Recognition p f :=
  psp6Recognition_of_shortNodes (c3ShortNodeA2 p f)

end CFSG.ClassicalInvolution.Generic.CoreAssembly
