module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Alpha

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S8

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance

section Min


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_xMem_of_mem_RSet (hΩ : HypOmegaGen Ω)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {x : G} {X : Subgroup G} (hX : X ∈ RSet Ω)
    (hxX : ∀ y ∈ X, x * y = y * x) :
    ∃ M z', T8.XMem Ω x M ∧ IsSylow2In X M ∧ IsUniqueInvolution M z' ∧ z' ∈ X := by
  obtain ⟨M, hM, hXM⟩ := exists_isSylow2In_of_mem_RSet hX
  obtain ⟨z', hz'⟩ := Sec6Gen.exists_uniqueInvolution hΩ hM
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hX
  have hz'X : z' ∈ X := T3.mem_of_isPGroup hz' hXM.1 hXM.2.1 (by omega)
  refine ⟨M, z', ⟨hM, ?_, X, hXM, fun r hr => (hxX r hr).symm⟩, hXM, hz', hz'X⟩
  exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hM (hnt M hM) hz'
    (Subgroup.mem_centralizer_singleton_iff.mpr (hxX z' hz'X))

theorem oddCoreOf_layerJoin_le_H274 {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Asc77.Std8 Ω K J S R T W z t) {x : G} (hx : x * x = 1)
    (hKX : T8.XMem Ω x K) (hRx : R ≤ T8.cenZ x) {X₂ M₂ : Subgroup G} {z₂ : G}
    (hX₂ : X₂ ∈ RSet Ω) (hM₂ : T8.XMem Ω x M₂) (hX₂M₂ : IsSylow2In X₂ M₂)
    (hz₂ : IsUniqueInvolution M₂ z₂) (hz₂X : z₂ ∈ X₂) (hX₂x : X₂ ≤ T8.cenZ x)
    (hcomm : Commutes R X₂) (hRX₂ : R ≠ X₂) :
    oddCoreOf (T8.layerJoin Ω x) ≤ T8.H274 Ω K z := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hcls := hs.stand.std.classical
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, -⟩ := hs.hR
  have hRsyl : IsSylow2In R K := Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hRΩ
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
  have hzz₂ : z * z₂ = z₂ * z := hcomm z hzR z₂ hz₂X
  have hX₂N : X₂ ≤ Subgroup.normalizer (K : Set G) := fun y hy =>
    T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hzR y hy).symm)
  have hM₂K : M₂ ≠ K := by
    intro h
    rw [h] at hX₂M₂
    exact hRX₂ (T8.eq_of_commutes_isSylow2In hRsyl hX₂M₂ hcomm).symm
  have hM₂nbr : M₂ ∈ omegaNbr Ω K := ⟨hM₂.1, hM₂K, X₂, hX₂, hX₂M₂.1, hX₂N⟩
  have hznes : z ≠ z₂ := T8.ne_of_mem_omegaNbr hs.noTwins hM₂nbr hs.hz hz₂
  have hHz : Subgroup.centralizer ({z} : Set G) ≤ T8.H274 Ω K z :=
    (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz).trans
      ((T8.normalizer_le_sigmaNorm hΩ.conjInvariant hK).trans (T8.sigmaNorm_le_H274 K z))
  have hHz₂ : Subgroup.centralizer ({z₂} : Set G) ≤ T8.H274 Ω K z :=
    (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hM₂.1
      (T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM₂.1) hz₂).trans
      ((T8.normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK
        (T8.mem_dComp_of_mem_omegaNbr hM₂nbr)).trans (T8.sigmaNorm_le_H274 K z))
  have hHzz₂ : Subgroup.centralizer ({z * z₂} : Set G) ≤ T8.H274 Ω K z :=
    T8.centralizer_mul_le_H274 hM₂nbr hz₂
  have hRL : R ≤ T8.layerRes x K :=
    (Asc77.T8.XMem.isSylow2In_layerRes_of_le hΩ hcls hx hKX hRsyl hRx).1
  have hX₂L : X₂ ≤ T8.layerRes x M₂ :=
    (Asc77.T8.XMem.isSylow2In_layerRes_of_le hΩ hcls hx hM₂ hX₂M₂ hX₂x).1
  have hzY : z ∈ T8.layerJoin Ω x := T8.le_layerJoin ⟨K, hKX, rfl⟩ (hRL hzR)
  have hz₂Y : z₂ ∈ T8.layerJoin Ω x := T8.le_layerJoin ⟨M₂, hM₂, rfl⟩ (hX₂L hz₂X)
  have hEY : Subgroup.closure ({z, z₂} : Set G) ≤ T8.layerJoin Ω x := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hzY
    · exact hz₂Y
  refine CFSG.Goldschmidt.LemmaX.le_of_forall_inf_centralizer_le
    (E := Subgroup.closure ({z, z₂} : Set G))
    ⟨⟨fun a b => Subtype.ext (T8.closure_pair_mul_comm hzz₂ a.2 b.2)⟩⟩
    (fun w hw => T8.closure_pair_sq hs.hz.sq hz₂.sq hzz₂ hw)
    (T8.four_le_natCard_closure_pair hs.hz.sq hs.hz.ne_one hz₂.ne_one hznes)
    (fun w hw => mem_normalizer_oddCoreOf (hEY hw)) (odd_natCard_oddCoreOf _) ?_
  intro e he he1
  refine inf_le_right.trans ?_
  rcases T8.mem_closure_pair_involutions hs.hz.sq hz₂.sq hzz₂ he with h | h | h | h
  · exact absurd h he1
  · rw [h]
    exact hHz
  · rw [h]
    exact hHz₂
  · rw [h]
    exact hHzz₂

variable [IsSimpleGroup G]

theorem centralizer_le_H274_of_eight {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Asc77.Std8 Ω K J S R T W z t) {S₂ : Sylow 2 G}
    (hRS₂ : R ≤ (S₂ : Subgroup G))
    (hcount : 8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S₂ : Subgroup G)}) {x : G}
    (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hcent : ∀ Y ∈ RSet Ω, Y ≤ (S₂ : Subgroup G) → ∀ y ∈ Y, x * y = y * x) :
    Subgroup.centralizer ({x} : Set G) ≤ T8.H274 Ω K z := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hL : Asc77.T8.LayerHyp Ω x := layerHyp_of_pre hs.stand.std.toPre2A7 hx2 hx1
  obtain ⟨hRΩ, hRK, -⟩ := hs.hR
  have hRsyl : IsSylow2In R K := Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hRΩ
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
  have hRx : ∀ r ∈ R, x * r = r * x := hcent R hRΩ hRS₂
  have hKX : T8.XMem Ω x K :=
    ⟨hK, T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr (hRx z hzR)), R, hRsyl,
      fun r hr => (hRx r hr).symm⟩
  obtain ⟨X₂, hX₂Ω, hX₂S, hX₂R⟩ : ∃ X₂ : Subgroup G, X₂ ∈ RSet Ω ∧
      X₂ ≤ (S₂ : Subgroup G) ∧ X₂ ≠ R := by
    have hnt' : Nontrivial {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S₂ : Subgroup G)} :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨b, hb⟩ := exists_ne (⟨R, hRΩ, hRS₂⟩ :
      {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S₂ : Subgroup G)})
    exact ⟨b.1, b.2.1, b.2.2, fun h => hb (Subtype.ext h)⟩
  have hcm : Commutes R X₂ :=
    Asc77.l6_7_proved G Ω hΩ S₂ R hRΩ X₂ hX₂Ω hRS₂ hX₂S hX₂R.symm
  obtain ⟨M₂, z₂, hM₂, hX₂M₂, hz₂, hz₂X⟩ :=
    exists_xMem_of_mem_RSet hΩ hnt hX₂Ω (hcent X₂ hX₂Ω hX₂S)
  have hO := oddCoreOf_layerJoin_le_H274 hs hx2 hKX
    (fun y hy => T8.mem_cenZ_iff.mpr (hRx y hy).symm) hX₂Ω hM₂ hX₂M₂ hz₂ hz₂X
    (fun y hy => T8.mem_cenZ_iff.mpr (hcent X₂ hX₂Ω hX₂S y hy).symm) hcm hX₂R.symm
  intro c hc
  obtain ⟨ν, hν, hνN⟩ := exists_mul_mem_sigmaNorm_of_centralizer hL hKX hc
  have hνH : ν ∈ T8.H274 Ω K z := hO hν
  have := (T8.H274 Ω K z).mul_mem ((T8.H274 Ω K z).inv_mem hνH) (T8.sigmaNorm_le_H274 K z hνN)
  simpa using this

end Min

end CFSG.ClassicalInvolution.Hat2A7S8
