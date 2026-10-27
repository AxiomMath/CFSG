module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5AssemblyInv
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveCo1Bridge
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Co1Five

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M5

open CFSG.Open CFSG.Monster.Visible CFSG.Monster.Existence CFSG.Monster.Griess
  CFSG.Monster.Existence.Co1Bridge CFSG.HardMathSupport.Dickson.I271.TabMFive
  CFSG.Sporadic.Co1Schreier

open scoped Matrix

private theorem mem_Gvis_of_mem_cent {h : MGriess} (hh : h ∈ cent xGriess) :
    (h : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis := by
  have : (h : SpaceB ≃ₗ[ℚ] SpaceB) ∈ (cent xGriess).map AutO.subtype := ⟨h, hh, rfl⟩
  rwa [map_cent_xGriess] at this

section Data


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

private theorem card_le_two_of_xGriess_mem (hb : Co1FiveCubeFacts) {F W : Subgroup MGriess}
    (hxW : xGriess ∈ W) (hF : IsElemAbelian 5 F) (hFc : Nat.card F = 5 ^ 3)
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
  refine card_le_two_of_quot (n := 3) Nat.prime_five (by norm_num) CFSG.pCore_isPGroup
    (fun j : GA => ∀ v : Fin 24 → ZMod 2,
      ((j : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v → v = 0)
    co1_five_ha hb.2 e
    (fun k hk => card_pCore_inf_le_two k fun v hv => hk v (by rw [he]; exact hv))
    (hF.subgroupOf _) ?_ (hW.subgroupOf _) fun f hf w hw => Subtype.ext (hcomm _ hf _ hw)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv, hFc]

theorem false_of_twoB (hE : MonsterExistenceStatement MGriess)
    (hB : Nat.card CFSG.Blueprint.NativeSporadic.B = CFSG.Open.monsterBabyOrder)
    (hG5 : ∀ A : Subgroup MGriess, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
      8 ≤ Nat.card ↥A → ∃ u ∈ A, orderOf u = 2 ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set MGriess)) = twoBCentralizerOrder)
    (hb : Co1FiveCubeFacts) (F W : Subgroup MGriess) (hF : IsElemAbelian 5 F)
    (hFc : Nat.card F = 5 ^ 3) (hW : IsElemAbelian 2 W) (hW16 : 2 ^ 4 ≤ Nat.card W)
    (hFW : F ≤ Subgroup.centralizer (W : Set MGriess)) : False := by
  obtain ⟨u, huW, hu2, huc⟩ := hG5 W (fun a ha b hb' => congrArg Subtype.val
    (hW.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb'⟩)) hW.2 (le_trans (by norm_num) hW16)
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_xGriess_of_card hE hB hu2 huc)
  let c : MGriess →* MGriess := (MulAut.conj g⁻¹).toMonoidHom
  have hc : Function.Injective c := (MulAut.conj g⁻¹).injective
  have hx : xGriess ∈ W.map c := Subgroup.mem_map.2 ⟨u, huW, by
    show g⁻¹ * u * g⁻¹⁻¹ = xGriess
    rw [← hg]
    group⟩
  have hFW' : F.map c ≤ Subgroup.centralizer ((W.map c : Subgroup MGriess) : Set MGriess) := by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 hy
    rw [Subgroup.mem_centralizer_iff]
    intro y' hy'
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy'
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 (hFW hf) w hw]
  have h2 := card_le_two_of_xGriess_mem hb hx (hF.map c)
    (by rw [Subgroup.card_map_of_injective hc]; exact hFc) (hW.map c) hFW'
  rw [Subgroup.card_map_of_injective hc] at h2
  exact absurd (hW16.trans h2) (by norm_num)

end Data

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M5
