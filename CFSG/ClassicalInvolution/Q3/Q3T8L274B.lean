module

public import CFSG.ClassicalInvolution.Q3.Q3T8L274A
public import CFSG.ClassicalInvolution.Q3.Q3T8C274Five
public import CFSG.ClassicalInvolution.Q3.Q3T8E274B
public import CFSG.ClassicalInvolution.Q3.Q3T7LayerT
import CFSG.ClassicalInvolution.Asc77.AscT8MinProofEng

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Layer

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T7
  CFSG.ClassicalInvolution.Q3.Disc3 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8
open scoped commutatorElement

section Coprime

variable {G : Type} [Group G]

omit [Group G] in
theorem exists_embedding_fin_five {α : Type*} (h : 8 ≤ Nat.card α) : Nonempty (Fin 5 ↪ α) :=
  CFSG.ClassicalInvolution.Asc77.T8.exists_embedding_fin_five h

theorem closure_pair_mul_comm {z b : G} (hzb : z * b = b * z) {u v : G}
    (hu : u ∈ Subgroup.closure ({z, b} : Set G)) (hv : v ∈ Subgroup.closure ({z, b} : Set G)) :
    u * v = v * u :=
  CFSG.ClassicalInvolution.Asc77.T8.closure_pair_mul_comm hzb hu hv

theorem closure_pair_sq {z b : G} (hz : z * z = 1) (hb : b * b = 1) (hzb : z * b = b * z)
    {u : G} (hu : u ∈ Subgroup.closure ({z, b} : Set G)) : u ^ 2 = 1 :=
  CFSG.ClassicalInvolution.Asc77.T8.closure_pair_sq hz hb hzb hu

theorem four_le_natCard_closure_pair [Finite G] {z b : G} (hz : z * z = 1) (hz1 : z ≠ 1)
    (hb1 : b ≠ 1) (hne : z ≠ b) :
    4 ≤ Nat.card (Subgroup.closure ({z, b} : Set G)) := by
  exact CFSG.ClassicalInvolution.Asc77.T8.four_le_natCard_closure_pairE hz hz1 hb1 hne

end Coprime

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


theorem not_central_of_ne_one3 [IsSimpleGroup G] {K : Subgroup G}
    (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hK : K ∈ Ω) {x : G} (hx1 : x ≠ 1) :
    ¬ ({x} : Set G) ⊆ Subgroup.center G := by
  intro hc
  have hxc : x ∈ Subgroup.center G := hc rfl
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  obtain ⟨a, -, b, -, hab⟩ := hz.exists_noncomm
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h | h
  · rw [h] at hxc
    exact hx1 (by simpa using hxc)
  · have hb : b ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 hb a)

omit [Finite G] in
theorem exists_xMem_of_mem_RSet3 [Finite G] (hΩ : HypOmegaGen Ω)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {x : G} {X : Subgroup G} (hX : X ∈ RSet Ω)
    (hxX : ∀ y ∈ X, x * y = y * x) :
    ∃ M z', XMem Ω x M ∧ IsSylow2In X M ∧ IsUniqueInvolution M z' ∧ z' ∈ X := by
  obtain ⟨M, hM, hXM⟩ := exists_isSylow2In_of_mem_RSet hX
  obtain ⟨z', hz'⟩ := Sec6Gen.exists_uniqueInvolution hΩ hM
  have hz'X : z' ∈ X :=
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8.IsFrameInv.mem hΩ hX ⟨M, hM, hXM, hz'⟩
  refine ⟨M, z', ⟨hM, ?_, X, hXM, fun r hr => (hxX r hr).symm⟩, hXM, hz', hz'X⟩
  exact centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hM (hnt M hM) hz'
    (Subgroup.mem_centralizer_singleton_iff.mpr (hxX z' hz'X))

theorem dConnected_layerFam3 {K₀ : Subgroup G} (hs : AscStand3 Ω K₀)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {x : G} (hx : x * x = 1)
    (hnc : ¬ ({x} : Set G) ⊆ Subgroup.center G) (S₂ : Sylow 2 G)
    (hcount : 8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S₂ : Subgroup G)})
    (hcent : ∀ Y ∈ RSet Ω, Y ≤ (S₂ : Subgroup G) → ∀ y ∈ Y, x * y = y * x) :
    DConnected (layerFam3 Ω x) := by
  classical
  have hΩ : HypOmegaGen Ω := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hs.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers x) := isPGroup_zpowers_of_sq hx
  obtain ⟨e⟩ := exists_embedding_fin_five hcount
  have hdat : ∀ i, ∃ M z', XMem Ω x M ∧ IsSylow2In (e i).1 M ∧ IsUniqueInvolution M z' ∧
      z' ∈ (e i).1 := fun i =>
    exists_xMem_of_mem_RSet3 hΩ hnt (e i).2.1 (fun y hy => hcent _ (e i).2.1 (e i).2.2 y hy)
  choose M zi hMX hMS hzi hziX using hdat
  have hMt : ∀ i, M i ∈ tqMembers3 Ω x := fun i => (hMX i).mem_tqMembers3 hΩ hx
  have hne : ∀ i j, i ≠ j → (e i).1 ≠ (e j).1 := fun i j hij h =>
    hij (e.injective (Subtype.ext h))
  have hcm : ∀ i j, i ≠ j → Commutes (e i).1 (e j).1 := fun i j hij =>
    Q3CP.l67Gen G Ω hΩ S₂ _ (e i).2.1 _ (e j).2.1 (e i).2.2 (e j).2.2 (hne i j hij)
  have hPcen : ∀ i, (e i).1 ≤ cenZ x := fun i y hy =>
    mem_cenZ_iff.mpr (hcent _ (e i).2.1 (e i).2.2 y hy).symm
  have hPN : ∀ i j, i ≠ j → (e j).1 ≤ Subgroup.normalizer (M i : Set G) := by
    intro i j hij y hy
    exact centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (hMX i).1 (hnt _ (hMX i).1)
      (hzi i) (Subgroup.mem_centralizer_singleton_iff.mpr
        ((hcm i j hij) (zi i) (hziX i) y hy).symm)
  have himg : ∀ i j, i ≠ j → layerImg3 Ω x (M i) ≠ layerImg3 Ω x (M j) := fun i j hij =>
    layerImg3_ne (hMt i) (hMt j) (hMS i) (hMS j) (hPcen i) (hPcen j) (hcm i j hij) (hne i j hij)
  have hne0 : (tqMembers3 Ω x).Nonempty := ⟨M 0, hMt 0⟩
  refine dConnected_of_five_clique3 hs.ih hs.below (Q3T7.card_layerQuot3_lt hnc)
    (Q3T7.hypOmegaModU_layerFam3 hs hc2 hne0) Q3T7.layerQuot3_oddCore_eq_bot
    (Q3T7.omegaGen_layerFam3 hs hc2 hne0) (Q3T7.aEmpty_layerFam3 hs hc2 hne0)
    (fun i => layerImg3 Ω x (M i)) (fun i => layerImg3_mem (hMt i)) ?_ ?_
  · intro i j h
    by_contra hij
    exact himg i j hij h
  · intro i j hij
    exact layerImg3_omegaNbr (hMt i) (hMt j) (hMS j) (hPcen j) (hPN i j hij) (himg i j hij)

omit [Finite G] in
theorem le_centralizer_singleton_of_forall {R : Subgroup G} {x : G}
    (h : ∀ r ∈ R, x * r = r * x) : R ≤ Subgroup.centralizer ({x} : Set G) := fun r hr =>
  Subgroup.mem_centralizer_singleton_iff.mpr (h r hr).symm

theorem oddCoreOf_exactLayer3_le_H274 {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 Ω K J S R T W z t) {x : G} (hx : x * x = 1) (hKX : XMem Ω x K)
    (hRx : R ≤ cenZ x) {X₂ M₂ : Subgroup G} {z₂ : G} (hX₂ : X₂ ∈ RSet Ω) (hM₂ : XMem Ω x M₂)
    (hX₂M₂ : IsSylow2In X₂ M₂) (hz₂ : IsUniqueInvolution M₂ z₂) (hz₂X : z₂ ∈ X₂)
    (hX₂x : X₂ ≤ cenZ x) (hcomm : Commutes R X₂) (hRX₂ : R ≠ X₂) :
    oddCoreOf (exactLayer3 Ω x) ≤ H274 Ω K z := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hKt : K ∈ tqMembers3 Ω x := hKX.mem_tqMembers3 hΩ hx
  have hM₂t : M₂ ∈ tqMembers3 Ω x := hM₂.mem_tqMembers3 hΩ hx
  obtain ⟨hRΩ, hRK, -⟩ := hs.hR
  have hRsyl : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hzR : z ∈ R :=
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8.IsFrameInv.mem hΩ hRΩ ⟨K, hK, hRsyl, hs.hz⟩
  have hzz₂ : z * z₂ = z₂ * z := hcomm z hzR z₂ hz₂X
  have hX₂N : X₂ ≤ Subgroup.normalizer (K : Set G) := fun y hy =>
    centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hzR y hy).symm)
  have hM₂K : M₂ ≠ K := by
    intro h
    rw [h] at hX₂M₂
    exact hRX₂ (eq_of_commutes_isSylow2In hRsyl hX₂M₂ hcomm).symm
  have hM₂nbr : M₂ ∈ omegaNbr Ω K := ⟨hM₂.1, hM₂K, X₂, hX₂, hX₂M₂.1, hX₂N⟩
  have hznes : z ≠ z₂ := ne_of_mem_omegaNbr hs.noTwins hM₂nbr hs.hz hz₂
  have hHz : Subgroup.centralizer ({z} : Set G) ≤ H274 Ω K z :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz).trans
      ((normalizer_le_sigmaNorm hΩ.conjInvariant hK).trans (sigmaNorm_le_H274 K z))
  have hHz₂ : Subgroup.centralizer ({z₂} : Set G) ≤ H274 Ω K z :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hM₂.1
      (noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM₂.1) hz₂).trans
      ((normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK
        (mem_dComp_of_mem_omegaNbr hM₂nbr)).trans (sigmaNorm_le_H274 K z))
  have hHzz₂ : Subgroup.centralizer ({z * z₂} : Set G) ≤ H274 Ω K z :=
    centralizer_mul_le_H274 hM₂nbr hz₂
  have hRL : R ≤ exactCore3 x K :=
    le_inf hRK ((cenZ_eq_centralizer x) ▸ hRx)
  have hX₂L : X₂ ≤ exactCore3 x M₂ :=
    le_inf hX₂M₂.1 ((cenZ_eq_centralizer x) ▸ hX₂x)
  have hzY : z ∈ exactLayer3 Ω x := exactCore3_le_exactLayer3 hKt (hRL hzR)
  have hz₂Y : z₂ ∈ exactLayer3 Ω x := exactCore3_le_exactLayer3 hM₂t (hX₂L hz₂X)
  have hEY : Subgroup.closure ({z, z₂} : Set G) ≤ exactLayer3 Ω x := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hzY
    · exact hz₂Y
  refine CFSG.Goldschmidt.LemmaX.le_of_forall_inf_centralizer_le
    (E := Subgroup.closure ({z, z₂} : Set G))
    ⟨⟨fun a b => Subtype.ext (closure_pair_mul_comm hzz₂ a.2 b.2)⟩⟩
    (fun w hw => closure_pair_sq hs.hz.sq hz₂.sq hzz₂ hw)
    (four_le_natCard_closure_pair hs.hz.sq hs.hz.ne_one hz₂.ne_one hznes)
    (fun w hw => mem_normalizer_oddCoreOf (hEY hw)) (odd_natCard_oddCoreOf _) ?_
  intro e he he1
  refine inf_le_right.trans ?_
  rcases mem_closure_pair_involutions hs.hz.sq hz₂.sq hzz₂ he with h | h | h | h
  · exact absurd h he1
  · rw [h]
    exact hHz
  · rw [h]
    exact hHz₂
  · rw [h]
    exact hHzz₂

theorem centralizer_le_H274_of_eight3 [IsSimpleGroup G] {K J : Subgroup G} {S : Sylow 2 G}
    {R T W : Subgroup G} {z t : G} (hs : Std8 Ω K J S R T W z t) {S₂ : Sylow 2 G}
    (hRS₂ : R ≤ (S₂ : Subgroup G))
    (hcount : 8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S₂ : Subgroup G)}) {x : G}
    (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hcent : ∀ Y ∈ RSet Ω, Y ≤ (S₂ : Subgroup G) → ∀ y ∈ Y, x * y = y * x) :
    Subgroup.centralizer ({x} : Set G) ≤ H274 Ω K z := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hs3 : AscStand3 Ω K := hs.stand.toStand3
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hnc := not_central_of_ne_one3 hs.stand.modU hK hx1
  have hconn := dConnected_layerFam3 hs3 hnt hx2 hnc S₂ hcount hcent
  obtain ⟨hRΩ, hRK, -⟩ := hs.hR
  have hRsyl : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hzR : z ∈ R :=
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8.IsFrameInv.mem hΩ hRΩ ⟨K, hK, hRsyl, hs.hz⟩
  have hRx : ∀ r ∈ R, x * r = r * x := hcent R hRΩ hRS₂
  have hKX : XMem Ω x K :=
    ⟨hK, centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr (hRx z hzR)), R, hRsyl,
      fun r hr => (hRx r hr).symm⟩
  have hKt : K ∈ tqMembers3 Ω x := hKX.mem_tqMembers3 hΩ hx2
  have hL : LayerHyp Ω x := LayerHyp.of_stand3 hs3 hx2 ⟨K, hKt⟩
  obtain ⟨e⟩ := exists_embedding_fin_five hcount
  have h01 : (e 0).1 ≠ (e 1).1 := fun h => absurd (e.injective (Subtype.ext h)) (by decide)
  obtain ⟨X₂, hX₂Ω, hX₂S, hX₂R⟩ : ∃ X₂ : Subgroup G, X₂ ∈ RSet Ω ∧
      X₂ ≤ (S₂ : Subgroup G) ∧ X₂ ≠ R := by
    by_cases h : (e 0).1 = R
    · exact ⟨(e 1).1, (e 1).2.1, (e 1).2.2, fun h' => h01 (h.trans h'.symm)⟩
    · exact ⟨(e 0).1, (e 0).2.1, (e 0).2.2, h⟩
  have hcm : Commutes R X₂ :=
    Q3CP.l67Gen G Ω hΩ S₂ R hRΩ X₂ hX₂Ω hRS₂ hX₂S hX₂R.symm
  obtain ⟨M₂, z₂, hM₂, hX₂M₂, hz₂, hz₂X⟩ :=
    exists_xMem_of_mem_RSet3 hΩ hnt hX₂Ω (hcent X₂ hX₂Ω hX₂S)
  have hO := oddCoreOf_exactLayer3_le_H274 hs hx2 hKX
    (fun y hy => mem_cenZ_iff.mpr (hRx y hy).symm) hX₂Ω hM₂ hX₂M₂ hz₂ hz₂X
    (fun y hy => mem_cenZ_iff.mpr (hcent X₂ hX₂Ω hX₂S y hy).symm) hcm hX₂R.symm
  intro c hc
  have hcz : c ∈ cenZ x := by
    rw [cenZ_eq_centralizer]
    exact hc
  have hKXc : XMem Ω x (conjSub c K) := hKX.conj3 hΩ.conjInvariant hcz
  obtain ⟨ν, hν, hνc⟩ :=
    exists_oddCore_conj_mem_dComp3 hL hKt hconn (hKXc.mem_tqMembers3 hΩ hx2)
  rw [← conjSub_mul] at hνc
  have hνN : ν * c ∈ sigmaNorm Ω K := (mem_sigmaNorm_iff hΩ.conjInvariant hK).mpr hνc
  have hνH : ν ∈ H274 Ω K z := hO hν
  have := (H274 Ω K z).mul_mem ((H274 Ω K z).inv_mem hνH) (sigmaNorm_le_H274 K z hνN)
  simpa using this

end Main

end CFSG.ClassicalInvolution.Q3.Q3T8.Layer
