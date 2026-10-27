module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7RkB

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Subgroup

theorem i227rk_isSubnormal_trans {G : Type*} [Group G] {A B C : Subgroup G}
    (h₁ : CFSG.Open.IsSubnormal A B) (h₂ : CFSG.Open.IsSubnormal B C) :
    CFSG.Open.IsSubnormal A C :=
  h₁.trans h₂

theorem i227rk_isSubnormal_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {A B : Subgroup X}
    (h : CFSG.Open.IsSubnormal A B) : CFSG.Open.IsSubnormal (A.map f) (B.map f) :=
  h.map f

theorem i227rk_isQuasisimple_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) {K : Subgroup X} (hK : CFSG.Open.IsQuasisimple K) :
    CFSG.Open.IsQuasisimple (K.map f) := by
  set e : K ≃* K.map f := K.equivMapOfInjective f hf
  obtain ⟨hp, hs⟩ := hK
  have hc : (Subgroup.center K).map (e : K →* K.map f) = Subgroup.center (K.map f) :=
    Subgroup.map_center_eq e
  let e' := QuotientGroup.congr _ _ e hc
  refine ⟨?_, e'.symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hp ⊢
  rw [← Subgroup.map_top_of_surjective (e : K →* K.map f) e.surjective,
    ← Subgroup.map_commutator, hp]

theorem i227rk_normal_map {K : Type*} [Group K] (W : Subgroup K) [W.Normal] (N : Subgroup W)
    [hN : N.Characteristic] : (N.map W.subtype).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨n, hn, rfl⟩ g
  have hmem : (MulAut.conjNormal g : MulAut W) n ∈ N :=
    (Subgroup.characteristic_iff_map_le.mp hN) (MulAut.conjNormal g)
      (Subgroup.mem_map_of_mem _ hn)
  exact ⟨_, hmem, by simp⟩

theorem i227_rank_holds : I22_7Rank := by
  intro K _ _ hK hO R' W _ hW hnc hrk
  have hWn : W.Normal := by rw [hW]; infer_instance
  have hcore : CFSG.pPrimeCore 3 W = ⊥ := by
    set N := CFSG.pPrimeCore 3 W with hNdef
    have hN : (N.map W.subtype).Normal := i227rk_normal_map W N
    have hcop : Nat.Coprime 3 (Nat.card (N.map W.subtype)) := by
      rw [← Nat.card_congr (N.equivMapOfInjective W.subtype W.subtype_injective).toEquiv]
      exact CFSG.pPrimeCore_coprime_card
    have hle : N.map W.subtype ≤ CFSG.Open.GLAPPrimeCore 3 K := le_sSup ⟨hN, hcop⟩
    rw [hO, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective N W.subtype_injective).mp hle
  have hlayer : CFSG.layer W = ⊥ := by
    refine le_bot_iff.mp (sSup_le fun L hL => ?_)
    exfalso
    obtain ⟨-, hsub, hqs⟩ := (CFSG.isComponent_iff_open L).mp hL
    have hJsub : CFSG.Open.IsSubnormal (L.map W.subtype) ⊤ := by
      have h1 := i227rk_isSubnormal_map W.subtype hsub
      rw [Subgroup.map_top, Subgroup.range_subtype] at h1
      exact i227rk_isSubnormal_trans h1
        (CFSG.Open.IsSubnormal.step le_top inferInstance (CFSG.Open.IsSubnormal.refl ⊤))
    exact hnc _ (Subgroup.map_subtype_le L) hJsub
      (i227rk_isQuasisimple_map W.subtype W.subtype_injective hqs)
  have hchar : CFSG.IsCharacteristicP 3 W :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot W 3 hcore hlayer
  set O : Subgroup W := CFSG.pCore 3 W with hOdef
  set V : Subgroup K := O.map W.subtype with hVdef
  have hVn : V.Normal := i227rk_normal_map W O
  have hVp : IsPGroup 3 V :=
    (CFSG.pCore_isPGroup (p := 3) (G := W)).of_equiv
      (O.equivMapOfInjective W.subtype W.subtype_injective)
  have hVle : V ≤ W := Subgroup.map_subtype_le O
  have hVO : V ≤ oThreeIn W := le_sSup ⟨hVle, hVn, hVp⟩
  have hr : ∀ E : Subgroup K, E ≤ V → CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 9 := by
    intro E hE hEa
    have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hEa.2 x x.2)⟩
    obtain ⟨n, hn⟩ := hEp.exists_card_eq
    have hbdd : BddAbove {k | ∃ E : Subgroup K, E ≤ oThreeIn W ∧ CFSG.Open.IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ k} := by
      refine ⟨Nat.card K, ?_⟩
      rintro k ⟨E', -, -, hk⟩
      have h1 : 3 ^ k ≤ Nat.card K := hk ▸ Subgroup.card_le_card_group E'
      exact (Nat.lt_pow_self (by norm_num : 1 < 3)).le.trans h1
    have hnle : n ≤ CFSG.Open.pRank 3 (oThreeIn W) := le_csSup hbdd ⟨E, hE.trans hVO, hEa, hn⟩
    have hn2 : n ≤ 2 := hnle.trans hrk
    rw [hn]
    calc 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
      _ = 9 := by norm_num
  have hcent : ∀ k : K, ∀ v ∈ V, k * v = v * k :=
    i227rk_centralizes_of_rank_le_two hK V hVp hr
  have hWV : W ≤ V := by
    intro w hw
    have hmem : (⟨w, hw⟩ : W) ∈ Subgroup.centralizer (O : Set W) := by
      rw [Subgroup.mem_centralizer_iff]
      intro o ho
      exact Subtype.ext (hcent w _ (Subgroup.mem_map_of_mem _ ho)).symm
    exact ⟨_, hchar hmem, rfl⟩
  have hWK : ⁅W, (⊤ : Subgroup K)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro g _
    exact hcent g w (hWV hw)
  have hrot : ⁅⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆, R'⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [Subgroup.commutator_comm (⊤ : Subgroup K) R', ← hW]; exact hWK
    · rw [← hW]; exact hWK
  have htop : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
    rw [← _root_.commutator_def]; exact hK
  rw [htop] at hrot
  rw [hW, Subgroup.commutator_comm]
  exact hrot

end CFSG.HardMathSupport.Solomon.Coordinator
