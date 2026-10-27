module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3TwE6Rank
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5AssemblyInv
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveCo1Bridge
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Co1Five

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3

open CFSG.Open CFSG.Monster.Visible CFSG.Monster.Existence CFSG.Monster.Griess
  CFSG.Monster.Existence.Co1Bridge CFSG.HardMathSupport.Dickson.I271.TabMFive
  CFSG.Sporadic.Co1Schreier CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M5

open scoped Matrix

private theorem mem_Gvis_of_mem_cent {h : MGriess} (hh : h ∈ cent xGriess) :
    (h : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis := by
  have : (h : SpaceB ≃ₗ[ℚ] SpaceB) ∈ (cent xGriess).map AutO.subtype := ⟨h, hh, rfl⟩
  rwa [map_cent_xGriess] at this

section Fix


private theorem card_pCore_inf_le_two (k : cent xGriess)
    (hk : ∀ v : Fin 24 → ZMod 2, (((cosetEquivJ24 (QuotientGroup.mk k) : J24) :
      GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v → v = 0) :
    Nat.card ↥(CFSG.pCore 2 (cent xGriess) ⊓ Subgroup.centralizer ({k} : Set (cent xGriess))) ≤
      2 := by
  obtain ⟨p, hp⟩ := mem_Gvis.1 (mem_Gvis_of_mem_cent k.2)
  have h2 := card_pCore_inf_cent_le k p hp
  have h3 := card_fixed_conjQ_le p
  rw [natCard_fixed_modTwoEnd _ p.1.2 (conjHom_cosetEquivJ24 k p hp)] at h3
  have h5 : fixCount (((cosetEquivJ24 (QuotientGroup.mk k) : J24) : GL (Fin 24) (ZMod 2)) :
      Matrix (Fin 24) (Fin 24) (ZMod 2)) ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.2
      ⟨fun a b => Subtype.ext ((hk a.1 a.2).trans (hk b.1 b.2).symm)⟩
  exact h2.trans (h3.trans (Nat.mul_le_mul_left 2 h5))

end Fix

section Data


theorem co1_three_ha (t : GA) (ht : orderOf t = 2) :
    ¬ 3 ^ 6 ∣ Nat.card (Subgroup.centralizer ({t} : Set GA)) := by
  obtain ⟨hA, hC, hB⟩ := card_cent_classes
  rcases CFSG.Sporadic.Co1Block.involution_classes.1 t ht with h | h | h
  · rw [H1017.card_centralizer_of_isConj h, hA]; norm_num
  · rw [H1017.card_centralizer_of_isConj h, hC]; norm_num
  · rw [H1017.card_centralizer_of_isConj h, hB]; norm_num

theorem card_le_two_of_xGriess_mem_three (hb : Co1ThreeSixFixFact) {F W : Subgroup MGriess}
    (hxW : xGriess ∈ W) (hF : IsElemAbelian 3 F) (hFc : Nat.card F = 3 ^ 6)
    (hW : IsElemAbelian 2 W) (hFW : F ≤ Subgroup.centralizer (W : Set MGriess)) :
    Nat.card W ≤ 2 := by
  haveI : Finite (cent xGriess) := finite_cent_xGriess
  have hcomm : ∀ f ∈ F, ∀ w ∈ W, f * w = w * f := fun f hf w hw =>
    (Subgroup.mem_centralizer_iff.1 (hFW hf) w hw).symm
  have hWC : W ≤ cent xGriess := fun w hw => Subgroup.mem_centralizer_singleton_iff.2
    (congrArg Subtype.val (hW.1.is_comm.comm ⟨w, hw⟩ ⟨xGriess, hxW⟩))
  have hFC : F ≤ cent xGriess := fun f hf =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm f hf _ hxW)
  obtain ⟨e, he⟩ : ∃ e : cent xGriess ⧸ CFSG.pCore 2 (cent xGriess) ≃* GA, ∀ x,
      ((e x : GA) : GL (Fin 24) (ZMod 2)) = ((cosetEquivJ24 x : J24) : GL (Fin 24) (ZMod 2)) :=
    ⟨cosetEquivJ24.trans (MulEquiv.subgroupCongr J24_eq_GA), fun x => by
      rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]⟩
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv]
  refine card_le_two_of_quot (n := 6) Nat.prime_three (by norm_num) CFSG.pCore_isPGroup
    (fun j : GA => ∀ v : Fin 24 → ZMod 2,
      ((j : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v → v = 0)
    co1_three_ha hb e
    (fun k hk => card_pCore_inf_le_two k fun v hv => hk v (by rw [he]; exact hv))
    (hF.subgroupOf _) ?_ (hW.subgroupOf _) fun f hf w hw => Subtype.ext (hcomm _ hf _ hw)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv, hFc]

section TwoA


theorem false_of_four_three (hE : MonsterExistenceStatement MGriess)
    (hB : Nat.card CFSG.Blueprint.NativeSporadic.B = CFSG.Open.monsterBabyOrder)
    (hb : Co1ThreeSixFixFact) (F W : Subgroup MGriess) (hF : IsElemAbelian 3 F)
    (hFc : Nat.card F = 3 ^ 6) (hW : IsElemAbelian 2 W) (hW4 : 2 ^ 2 ≤ Nat.card W)
    (hFW : F ≤ Subgroup.centralizer (W : Set MGriess)) : False := by
  haveI : Finite MGriess := hE.1.1
  obtain ⟨-, a, z, -, hz, -, hcls, -, hZ, hgraph⟩ := id hE
  obtain ⟨-, c, -, -, hc1, -, -, -, -, hshape, -⟩ := hgraph
  have hcomm : ∀ f ∈ F, ∀ w ∈ W, f * w = w * f := fun f hf w hw =>
    (Subgroup.mem_centralizer_iff.1 (hFW hf) w hw).symm
  by_cases h2B : ∃ u ∈ W, IsConj z u
  ·
    obtain ⟨u, huW, hzu⟩ := h2B
    have hu2 : orderOf u = 2 := by
      obtain ⟨g, hg⟩ := isConj_iff.1 hzu
      have h := MulEquiv.orderOf_eq (MulAut.conj g) z
      rw [MulAut.conj_apply, hg, hz] at h
      exact h
    obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_xGriess_of_card hE hB hu2 (hZ u hzu).2.2.2.2.1)
    let cg : MGriess →* MGriess := (MulAut.conj g⁻¹).toMonoidHom
    have hc : Function.Injective cg := (MulAut.conj g⁻¹).injective
    have hx : xGriess ∈ W.map cg := Subgroup.mem_map.2 ⟨u, huW, by
      show g⁻¹ * u * g⁻¹⁻¹ = xGriess
      rw [← hg]
      group⟩
    have hFW' : F.map cg ≤ Subgroup.centralizer ((W.map cg : Subgroup MGriess) : Set MGriess) := by
      intro y hy
      obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 hy
      rw [Subgroup.mem_centralizer_iff]
      intro y' hy'
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy'
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 (hFW hf) w hw]
    have h2 := card_le_two_of_xGriess_mem_three hb hx (hF.map cg)
      (by rw [Subgroup.card_map_of_injective hc]; exact hFc) (hW.map cg) hFW'
    rw [Subgroup.card_map_of_injective hc] at h2
    exact absurd (hW4.trans h2) (by norm_num)
  ·
    push Not at h2B
    have h2A : ∀ u ∈ W, u ≠ 1 → IsConj a u := fun u hu hu1 =>
      (hcls u (orderOf_eq_prime (hW.2 u hu) hu1)).resolve_right (h2B u hu)
    have hWbot : W ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.card_bot] at hW4
      norm_num at hW4
    obtain ⟨⟨α, hαW⟩, hα1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hWbot
    have hα1' : α ≠ 1 := fun h => hα1 (Subtype.ext h)
    have hnle : ¬ W ≤ Subgroup.zpowers α := by
      intro hle
      have h := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, orderOf_eq_prime (hW.2 α hαW) hα1'] at h
      exact absurd (hW4.trans h) (by norm_num)
    obtain ⟨β, hβW, hβα⟩ := SetLike.not_le_iff_exists.1 hnle
    have hβ1 : β ≠ 1 := fun h => hβα (h ▸ one_mem _)
    have hαβ1 : α * β ≠ 1 := fun h => hβα (by
      rw [eq_inv_of_mul_eq_one_right h]
      exact inv_mem (Subgroup.mem_zpowers α))
    have hab : IsConj (α * β) (c 1) := (h2A _ (mul_mem hαW hβW) hαβ1).symm.trans hc1
    obtain ⟨N, hN, -, hN4, hL⟩ := hshape α β 1 (h2A α hαW hα1') (h2A β hβW hβ1) hab
    haveI := hN
    have hFD : F ≤ cent2 α β := fun f hf =>
      ⟨Subgroup.mem_centralizer_singleton_iff.2 (hcomm f hf α hαW),
        Subgroup.mem_centralizer_singleton_iff.2 (hcomm f hf β hβW)⟩
    have h5 := card_le_of_le_quot Nat.prime_three (by norm_num) (IsPGroup.of_card hN4)
      (card_le_of_lieModel_twistedE6_two hL) (MulEquiv.refl _) hFD hF
    rw [hFc] at h5
    exact absurd h5 (by norm_num)

end TwoA

end Data

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3
