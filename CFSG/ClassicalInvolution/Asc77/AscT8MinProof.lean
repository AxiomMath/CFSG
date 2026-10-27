module

public import CFSG.ClassicalInvolution.Asc77.AscT8Clique
public import CFSG.ClassicalInvolution.Asc77.AscT8LayerCl
public import CFSG.ClassicalInvolution.Asc77.AscT8Eight
import CFSG.ClassicalInvolution.Asc77.AscT8MinProofEng

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.GH74.Uniqueness CFSG.StronglyEmbedded.UniqueCoset
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3

namespace T8

section Frame

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem exists_xMem_of_mem_RSet (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {x : G} {X : Subgroup G} (hX : X ∈ RSet Ω)
    (hxX : ∀ y ∈ X, x * y = y * x) :
    ∃ M z', XMem Ω x M ∧ IsSylow2In X M ∧ IsUniqueInvolution M z' ∧ z' ∈ X := by
  obtain ⟨M, hM, hXM⟩ := exists_isSylow2In_of_mem_RSet hX
  obtain ⟨z', hz'⟩ := hΩ.exists_uniqueInvolution hp hq hM
  have hz'X : z' ∈ X := IsFrameInv.mem hp hΩ hX ⟨M, hM, hXM, hz'⟩
  refine ⟨M, z', ⟨hM, ?_, X, hXM, fun r hr => (hxX r hr).symm⟩, hXM, hz', hz'X⟩
  exact centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hM (hnt M hM) hz'
    (Subgroup.mem_centralizer_singleton_iff.mpr (hxX z' hz'X))

omit [Finite G] in
theorem exists_embedding_fin_five {α : Type*} (h : 8 ≤ Nat.card α) : Nonempty (Fin 5 ↪ α) := by
  have hfin : Finite α := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype α := Fintype.ofFinite α
  apply Function.Embedding.nonempty_of_card_le
  rw [Fintype.card_fin]
  rw [Nat.card_eq_fintype_card] at h
  omega

omit [Finite G] in
theorem omegaGen_layerFamQ (Ω : Set (Subgroup G)) (x : G) : omegaGen (layerFamQ Ω x) = ⊤ :=
  omegaGen_quotFamily_of_gen _ _ (omegaGen_restrictFamily_omegaGen (layerSet Ω x))

end Frame

section Connected

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem dConnected_layerFamQ (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {n : ℕ} (hn : CITBelowU p f n) {x : G}
    (hx : x * x = 1) (hlt : Nat.card (LayerQuot Ω x) < n) (S₂ : Sylow 2 G)
    (hcount : 8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S₂ : Subgroup G)})
    (hcent : ∀ Y ∈ RSet Ω, Y ≤ (S₂ : Subgroup G) → ∀ y ∈ Y, x * y = y * x) :
    DConnected (layerFamQ Ω x) := by
  classical
  obtain ⟨e⟩ := exists_embedding_fin_five hcount
  have hdat : ∀ i, ∃ M z', XMem Ω x M ∧ IsSylow2In (e i).1 M ∧ IsUniqueInvolution M z' ∧
      z' ∈ (e i).1 := fun i =>
    exists_xMem_of_mem_RSet hp hq hΩ hnt (e i).2.1 (fun y hy => hcent _ (e i).2.1 (e i).2.2 y hy)
  choose M zi hMX hMS hzi hziX using hdat
  have hne : ∀ i j, i ≠ j → (e i).1 ≠ (e j).1 := fun i j hij h =>
    hij (e.injective (Subtype.ext h))
  have hcm : ∀ i j, i ≠ j → Commutes (e i).1 (e j).1 := fun i j hij =>
    l6_7_proved p f hp hq G Ω hΩ S₂ _ (e i).2.1 _ (e j).2.1 (e i).2.2 (e j).2.2 (hne i j hij)
  have hPcen : ∀ i, (e i).1 ≤ cenZ x := fun i y hy =>
    mem_cenZ_iff.mpr (hcent _ (e i).2.1 (e i).2.2 y hy).symm
  have hPN : ∀ i j, i ≠ j → (e j).1 ≤ Subgroup.normalizer (M i : Set G) := by
    intro i j hij y hy
    exact centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (hMX i).1 (hnt _ (hMX i).1)
      (hzi i) (Subgroup.mem_centralizer_singleton_iff.mpr
        ((hcm i j hij) (zi i) (hziX i) y hy).symm)
  have himg : ∀ i j, i ≠ j → layerImg Ω x (M i) ≠ layerImg Ω x (M j) := fun i j hij =>
    layerImg_ne hp hq hΩ hx (hMX i) (hMX j) (hMS i) (hMS j) (hPcen i) (hPcen j) (hcm i j hij)
      (hne i j hij)
  refine dConnected_of_five_clique hn hlt hp hq (hypOmegaMod_layerQuot hp hq hΩ hx)
    (CFSG.ComponentClassification.OddCore.quotient_corefree _) (omegaGen_layerFamQ Ω x)
    (noTwins_layerQuot hp hq hΩ hnt hx) (fun i => layerImg Ω x (M i))
    (fun i => layerImg_mem (hMX i)) ?_ ?_
  · intro i j h
    by_contra hij
    exact himg i j hij h
  · intro i j hij
    exact layerImg_omegaNbr hp hq hΩ hx (hMX i) (hMX j) (hMS j) (hPcen j) (hPN i j hij)
      (himg i j hij)

end Connected

section Coprime

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem closure_pair_mul_comm {z b : G} (hzb : z * b = b * z) {u v : G}
    (hu : u ∈ Subgroup.closure ({z, b} : Set G)) (hv : v ∈ Subgroup.closure ({z, b} : Set G)) :
    u * v = v * u := by
  have h1 : ∀ w ∈ Subgroup.closure ({z, b} : Set G), ∀ y ∈ ({z, b} : Set G), y * w = w * y := by
    intro w hw
    have : Subgroup.closure ({z, b} : Set G) ≤ Subgroup.centralizer ({z, b} : Set G) := by
      rw [Subgroup.closure_le]
      intro a ha y hy
      rcases ha with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exact hzb.symm
      · exact hzb
      · rfl
    exact fun y hy => (Subgroup.mem_centralizer_iff.mp (this hw)) y hy
  have h2 : Subgroup.closure ({z, b} : Set G) ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact h1 u hu a ha
  exact (Subgroup.mem_centralizer_singleton_iff.mp (h2 hv)).symm

omit [Finite G] in
theorem closure_pair_sq {z b : G} (hz : z * z = 1) (hb : b * b = 1) (hzb : z * b = b * z)
    {u : G} (hu : u ∈ Subgroup.closure ({z, b} : Set G)) : u ^ 2 = 1 := by
  rcases mem_closure_pair_involutions hz hb hzb hu with rfl | rfl | rfl | rfl
  · simp
  · rw [pow_two]; exact hz
  · rw [pow_two]; exact hb
  · rw [pow_two]; exact mul_self_of_commute hz hb hzb

theorem four_le_natCard_closure_pair {z b : G} (hz : z * z = 1) (hz1 : z ≠ 1) (hb1 : b ≠ 1)
    (hne : z ≠ b) :
    4 ≤ Nat.card (Subgroup.closure ({z, b} : Set G)) := by
  exact four_le_natCard_closure_pairE hz hz1 hb1 hne

end Coprime

section Main

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem not_central_of_ne_one [IsSimpleGroup G] {K : Subgroup G} {z : G}
    (hΩ : HypOmegaMod p f Ω) (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) {x : G} (hx1 : x ≠ 1) :
    ¬ ({x} : Set G) ⊆ Subgroup.center G := by
  intro hc
  have hxc : x ∈ Subgroup.center G := hc rfl
  have hKs := not_isSolvable_of_mem hΩ hK hz
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h | h
  · rw [h] at hxc
    exact hx1 (by simpa using hxc)
  · have hcomm : ∀ a b : G, a * b = b * a := fun a b => by
      have hb : b ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top b
      exact (Subgroup.mem_center_iff.1 hb a)
    have : Group.IsSolvable G := IsSimpleGroup.comm_iff_isSolvable.mp hcomm
    exact hKs inferInstance

theorem oddCoreOf_layerJoin_le_H274 {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 p f Ω K J S R T W z t) {x : G} (hx : x * x = 1) (hKX : XMem Ω x K)
    (hRx : R ≤ cenZ x) {X₂ M₂ : Subgroup G} {z₂ : G} (hX₂ : X₂ ∈ RSet Ω) (hM₂ : XMem Ω x M₂)
    (hX₂M₂ : IsSylow2In X₂ M₂) (hz₂ : IsUniqueInvolution M₂ z₂) (hz₂X : z₂ ∈ X₂)
    (hX₂x : X₂ ≤ cenZ x) (hcomm : Commutes R X₂) (hRX₂ : R ≠ X₂) :
    oddCoreOf (layerJoin Ω x) ≤ H274 Ω K z := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, -⟩ := hs.hR
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hRΩ hRK
  have hzR : z ∈ R := IsFrameInv.mem hp hΩ hRΩ ⟨K, hK, hRsyl, hs.hz⟩
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
  have hRL : R ≤ layerRes x K := (hKX.isSylow2In_layerRes_of_le hp hq hΩ hx hRsyl hRx).1
  have hX₂L : X₂ ≤ layerRes x M₂ := (hM₂.isSylow2In_layerRes_of_le hp hq hΩ hx hX₂M₂ hX₂x).1
  have hzY : z ∈ layerJoin Ω x := le_layerJoin ⟨K, hKX, rfl⟩ (hRL hzR)
  have hz₂Y : z₂ ∈ layerJoin Ω x := le_layerJoin ⟨M₂, hM₂, rfl⟩ (hX₂L hz₂X)
  have hEY : Subgroup.closure ({z, z₂} : Set G) ≤ layerJoin Ω x := by
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

theorem centralizer_le_H274_of_eight [IsSimpleGroup G] {K J : Subgroup G} {S : Sylow 2 G}
    {R T W : Subgroup G} {z t : G} (hs : Std8 p f Ω K J S R T W z t) {S₂ : Sylow 2 G}
    (hRS₂ : R ≤ (S₂ : Subgroup G))
    (hcount : 8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S₂ : Subgroup G)}) {x : G}
    (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hcent : ∀ Y ∈ RSet Ω, Y ≤ (S₂ : Subgroup G) → ∀ y ∈ Y, x * y = y * x) :
    Subgroup.centralizer ({x} : Set G) ≤ H274 Ω K z := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hn : CITBelowU p f (Nat.card G) := hs.stand.below f hq
  have hlt := card_layerQuot_lt (Ω := Ω) (not_central_of_ne_one hΩ hK hs.hz hx1)
  have hconn := dConnected_layerFamQ hp hq hΩ hnt hn hx2 hlt S₂ hcount hcent
  obtain ⟨hRΩ, hRK, -⟩ := hs.hR
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hRΩ hRK
  have hzR : z ∈ R := IsFrameInv.mem hp hΩ hRΩ ⟨K, hK, hRsyl, hs.hz⟩
  have hRx : ∀ r ∈ R, x * r = r * x := hcent R hRΩ hRS₂
  have hKX : XMem Ω x K :=
    ⟨hK, centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr (hRx z hzR)), R, hRsyl,
      fun r hr => (hRx r hr).symm⟩
  obtain ⟨e⟩ := exists_embedding_fin_five hcount
  have h01 : (e 0).1 ≠ (e 1).1 := fun h => absurd (e.injective (Subtype.ext h)) (by decide)
  obtain ⟨X₂, hX₂Ω, hX₂S, hX₂R⟩ : ∃ X₂ : Subgroup G, X₂ ∈ RSet Ω ∧
      X₂ ≤ (S₂ : Subgroup G) ∧ X₂ ≠ R := by
    by_cases h : (e 0).1 = R
    · exact ⟨(e 1).1, (e 1).2.1, (e 1).2.2, fun h' => h01 (h.trans h'.symm)⟩
    · exact ⟨(e 0).1, (e 0).2.1, (e 0).2.2, h⟩
  have hcm : Commutes R X₂ :=
    l6_7_proved p f hp hq G Ω hΩ S₂ R hRΩ X₂ hX₂Ω hRS₂ hX₂S hX₂R.symm
  obtain ⟨M₂, z₂, hM₂, hX₂M₂, hz₂, hz₂X⟩ :=
    exists_xMem_of_mem_RSet hp hq hΩ hnt hX₂Ω (hcent X₂ hX₂Ω hX₂S)
  have hO := oddCoreOf_layerJoin_le_H274 hs hx2 hKX
    (fun y hy => mem_cenZ_iff.mpr (hRx y hy).symm) hX₂Ω hM₂ hX₂M₂ hz₂ hz₂X
    (fun y hy => mem_cenZ_iff.mpr (hcent X₂ hX₂Ω hX₂S y hy).symm) hcm hX₂R.symm
  intro c hc
  have hcz : c ∈ cenZ x := by
    rw [cenZ_eq_centralizer]
    exact hc
  obtain ⟨ν, hν, hνc⟩ :=
    exists_oddCore_conj_mem_dComp hp hq hΩ hx2 hKX hconn (hKX.conj hΩ hcz)
  rw [← conjSub_mul] at hνc
  have hνN : ν * c ∈ sigmaNorm Ω K := (mem_sigmaNorm_iff hΩ.conjInvariant hK).mpr hνc
  have hνH : ν ∈ H274 Ω K z := hO hν
  have := (H274 Ω K z).mul_mem ((H274 Ω K z).inv_mem hνH) (sigmaNorm_le_H274 K z hνN)
  simpa using this

end Main

end T8

variable {p f : ℕ} [Fact p.Prime]

theorem c27_4M_proved : C27_4M p f := by
  intro G _ _ _ Ω K J S R T W z t hs _ S₂ hRS₂ hcount x _ hx2 hx1 hcent
  exact T8.centralizer_le_H274_of_eight hs hRS₂ hcount hx2 hx1 hcent

end CFSG.ClassicalInvolution.Asc77
