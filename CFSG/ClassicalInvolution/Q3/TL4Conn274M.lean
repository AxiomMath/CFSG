module

public import CFSG.ClassicalInvolution.Q3.TL4Conn274MLift
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Main

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Gen

variable {G : Type} [Group G] [Finite G] {r : ℕ} {Ω : Set (Subgroup G)}

theorem exists_xMem_of_mem_RSet (h : TypeRFam r Ω) {x : G} {X : Subgroup G} (hX : X ∈ RSet Ω)
    (hxX : ∀ y ∈ X, x * y = y * x) :
    ∃ M z', XMem Ω x M ∧ IsSylow2In X M ∧ IsUniqueInvolution M z' ∧ z' ∈ X := by
  obtain ⟨M, hM, hXM⟩ := exists_isSylow2In_of_mem_RSet hX
  obtain ⟨z', hz'⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hM
  have h8 : 8 ≤ Nat.card X := Sec6Gen.eight_le_of_mem_RSet h.hyp hX
  have hz'X : z' ∈ X := T3.mem_of_isPGroup hz' hXM.1 hXM.2.1 (by omega)
  exact ⟨M, z', ⟨hM, h.tight M hM z' hz' (Subgroup.mem_centralizer_singleton_iff.mpr
    (hxX z' hz'X)), X, hXM, fun y hy => (hxX y hy).symm⟩, hXM, hz', hz'X⟩

theorem dConnected_secFam_of_eight {n : ℕ} (h5 : TightSec5CliqueR r n) (h : TypeRFam r Ω)
    {x : G} (hn : Nat.card (SecQuot Ω x) < n) (S₂ : Sylow 2 G)
    (hcount : 8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S₂ : Subgroup G)})
    (hcent : ∀ X ∈ RSet Ω, X ≤ (S₂ : Subgroup G) → ∀ y ∈ X, x * y = y * x) :
    DConnected (secFam Ω x) := by
  classical
  have hΩ : HypOmegaGen Ω := h.hyp
  obtain ⟨e⟩ := exists_embedding_fin_five hcount
  have hdat : ∀ i, ∃ M z', XMem Ω x M ∧ IsSylow2In (e i).1 M ∧ IsUniqueInvolution M z' ∧
      z' ∈ (e i).1 := fun i =>
    exists_xMem_of_mem_RSet h (e i).2.1 (fun y hy => hcent _ (e i).2.1 (e i).2.2 y hy)
  choose M zi hMX hMS hzi hziX using hdat
  have hne : ∀ i j, i ≠ j → (e i).1 ≠ (e j).1 := fun i j hij h' =>
    hij (e.injective (Subtype.ext h'))
  have hcm : ∀ i j, i ≠ j → Commutes (e i).1 (e j).1 := fun i j hij =>
    Q3CP.l67Gen G Ω hΩ S₂ _ (e i).2.1 _ (e j).2.1 (e i).2.2 (e j).2.2 (hne i j hij)
  have hzne : ∀ i j, i ≠ j → zi i ≠ zi j := by
    intro i j hij hz
    have hzj : IsUniqueInvolution (M j) (zi i) := by
      rw [hz]
      exact hzi j
    have hMM : M j = M i := h.noTwins _ (hMX i).1 _ ⟨(hMX j).1, zi i, hzi i, hzj⟩
    have hS' : IsSylow2In (e j).1 (M i) := by
      rw [← hMM]
      exact hMS j
    exact hne i j hij (eq_of_commutes_isSylow2In (hMS i) hS' (hcm i j hij)).symm
  have himg : ∀ i j, i ≠ j → secImg Ω x (M i) ≠ secImg Ω x (M j) := fun i j hij =>
    secImg_ne h (hMX i) (hMX j) (hzi i) (hzi j) (hcm i j hij _ (hziX i) _ (hziX j))
      (hzne i j hij)
  have hPx : ∀ i, (e i).1 ≤ Subgroup.centralizer ({x} : Set G) := fun i y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcent _ (e i).2.1 (e i).2.2 y hy).symm
  have hPN : ∀ i j, i ≠ j → (e j).1 ≤ Subgroup.normalizer (M i : Set G) := fun i j hij y hy =>
    h.tight _ (hMX i).1 _ (hzi i) (Subgroup.mem_centralizer_singleton_iff.mpr
      ((hcm i j hij) (zi i) (hziX i) y hy).symm)
  refine h5 (SecQuot Ω x) hn (secFam Ω x) h.secFam secQuot_oddCore_eq_bot omegaGen_secFam
    (aEmpty_secFam h) (fun i => secImg Ω x (M i)) (fun i => secImg_mem (hMX i)) ?_ ?_
  · intro i j hij
    by_contra hne'
    exact himg i j hne' hij
  · intro i j hij
    exact secImg_mem_omegaNbr (hMX i) (hMX j) (hMS j) (hPx j) (hPN i j hij) (himg i j hij)

end Gen

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.oddCoreOf_layerY_le_H274 (hs : TightStd8R r n Rd Sd z J S R T W t) {x : Y}
    (hRx : ∀ y ∈ R, x * y = y * x) {X₂ M₂ : Subgroup Y} {z₂ : Y}
    (hX₂ : X₂ ∈ RSet (CoreAssembly.conjClass (tightCore Rd)))
    (hM₂ : XMem (CoreAssembly.conjClass (tightCore Rd)) x M₂) (hX₂M₂ : IsSylow2In X₂ M₂)
    (hz₂ : IsUniqueInvolution M₂ z₂) (hz₂X : z₂ ∈ X₂) (hX₂x : ∀ y ∈ X₂, x * y = y * x)
    (hcomm : Commutes R X₂) (hRX₂ : R ≠ X₂) :
    oddCoreOf (layerY (CoreAssembly.conjClass (tightCore Rd)) x) ≤
      H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z := by
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore Rd)) := hs.hyp
  have hRsyl : IsSylow2In R (tightCore Rd) :=
    Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.mem hs.hR.1 hs.hR.2.1
  have h8 : 8 ≤ Nat.card R := Sec6Gen.eight_le_of_mem_RSet hΩ hs.hR.1
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRsyl.1 hRsyl.2.1 (by omega)
  have hzz₂ : z * z₂ = z₂ * z := hcomm z hzR z₂ hz₂X
  have hX₂N : X₂ ≤ Subgroup.normalizer (tightCore Rd : Set Y) := fun y hy =>
    h.tight _ hs.mem z hs.hz (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hzR y hy).symm)
  have hM₂K : M₂ ≠ tightCore Rd := by
    intro he
    rw [he] at hX₂M₂
    exact hRX₂ (eq_of_commutes_isSylow2In hRsyl hX₂M₂ hcomm).symm
  have hM₂nbr : M₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) :=
    ⟨hM₂.1, hM₂K, X₂, hX₂, hX₂M₂.1, hX₂N⟩
  have hzne : z ≠ z₂ := ne_of_mem_omegaNbr hs.noTwins hM₂nbr hs.hz hz₂
  have hHz : Subgroup.centralizer ({z} : Set Y) ≤
      H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z :=
    hs.centralizer_le_sigmaNorm.trans (sigmaNorm_le_H274 _ z)
  have hHz₂ : Subgroup.centralizer ({z₂} : Set Y) ≤
      H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z :=
    ((h.tight M₂ hM₂.1 z₂ hz₂).trans (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hs.mem
      (mem_dComp_of_mem_omegaNbr hM₂nbr))).trans (sigmaNorm_le_H274 _ z)
  exact oddCoreOf_layerY_le_of_good_pair hΩ.conjInvariant hs.hz.sq hz₂.sq hzz₂ hs.hz.ne_one
    hz₂.ne_one hzne (Subgroup.mem_centralizer_singleton_iff.mpr (hRx z hzR).symm)
    (Subgroup.mem_centralizer_singleton_iff.mpr (hX₂x z₂ hz₂X).symm) hHz hHz₂
    (centralizer_mul_le_H274 hM₂nbr hz₂)

theorem TightStd8R.centralizer_le_H274_of_eight (h5 : TightSec5CliqueR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t) {S₂ : Sylow 2 Y} (hRS₂ : R ≤ (S₂ : Subgroup Y))
    (hcount : 8 ≤ Nat.card {X : Subgroup Y //
      X ∈ RSet (CoreAssembly.conjClass (tightCore Rd)) ∧ X ≤ (S₂ : Subgroup Y)})
    {x : Y} (hx1 : x ≠ 1)
    (hcent : ∀ X ∈ RSet (CoreAssembly.conjClass (tightCore Rd)), X ≤ (S₂ : Subgroup Y) →
      ∀ y ∈ X, x * y = y * x) :
    Subgroup.centralizer ({x} : Set Y) ≤
      H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z := by
  classical
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore Rd)) := hs.hyp
  have hnc : ∃ g : Y, g * x ≠ x * g := by
    by_contra hcon
    push Not at hcon
    have hmem : x ∈ Subgroup.center Y := Subgroup.mem_center_iff.mpr fun g => hcon g
    rw [hs.large.center, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  have hn : Nat.card (SecQuot (CoreAssembly.conjClass (tightCore Rd)) x) < n :=
    hs.large.card ▸ TL4.natCard_secQuot_lt hnc
  have hconn := dConnected_secFam_of_eight h5 h hn S₂ hcount hcent
  have hRsyl : IsSylow2In R (tightCore Rd) :=
    Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.mem hs.hR.1 hs.hR.2.1
  have h8 : 8 ≤ Nat.card R := Sec6Gen.eight_le_of_mem_RSet hΩ hs.hR.1
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRsyl.1 hRsyl.2.1 (by omega)
  have hRx : ∀ y ∈ R, x * y = y * x := hcent R hs.hR.1 hRS₂
  have hKX : XMem (CoreAssembly.conjClass (tightCore Rd)) x (tightCore Rd) :=
    ⟨hs.mem, h.tight _ hs.mem z hs.hz (Subgroup.mem_centralizer_singleton_iff.mpr (hRx z hzR)),
      R, hRsyl, fun y hy => (hRx y hy).symm⟩
  obtain ⟨e⟩ := exists_embedding_fin_five hcount
  have h01 : (e 0).1 ≠ (e 1).1 := fun h' => absurd (e.injective (Subtype.ext h')) (by decide)
  obtain ⟨X₂, hX₂Ω, hX₂S, hX₂R⟩ : ∃ X₂ : Subgroup Y,
      X₂ ∈ RSet (CoreAssembly.conjClass (tightCore Rd)) ∧ X₂ ≤ (S₂ : Subgroup Y) ∧ X₂ ≠ R := by
    by_cases h0 : (e 0).1 = R
    · exact ⟨(e 1).1, (e 1).2.1, (e 1).2.2, fun h' => h01 (h0.trans h'.symm)⟩
    · exact ⟨(e 0).1, (e 0).2.1, (e 0).2.2, h0⟩
  have hcm : Commutes R X₂ :=
    Q3CP.l67Gen Y _ hΩ S₂ R hs.hR.1 X₂ hX₂Ω hRS₂ hX₂S hX₂R.symm
  obtain ⟨M₂, z₂, hM₂, hX₂M₂, hz₂, hz₂X⟩ :=
    exists_xMem_of_mem_RSet h hX₂Ω (hcent X₂ hX₂Ω hX₂S)
  have hO := hs.oddCoreOf_layerY_le_H274 hRx hX₂Ω hM₂ hX₂M₂ hz₂ hz₂X (hcent X₂ hX₂Ω hX₂S) hcm
    hX₂R.symm
  intro c hc
  have hKXc := XMem.conj' hΩ.conjInvariant hKX hc
  obtain ⟨ν, hν, hνc⟩ := exists_conj_mem_dComp_of_conn h hKX hconn hKXc
  rw [← conjSub_mul] at hνc
  have hνN : (ν : Y) * c ∈ sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) :=
    (mem_sigmaNorm_iff hΩ.conjInvariant hs.mem).mpr hνc
  have hνH : (ν : Y) ∈ H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z :=
    hO ⟨ν, hν, rfl⟩
  have := (H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z).mul_mem
    ((H274 _ _ z).inv_mem hνH) (sigmaNorm_le_H274 _ z hνN)
  simpa using this

theorem tightC27_4MR_of (h5 : TightSec5CliqueR r n) : TightC27_4MR r n :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hs _ _ hRS₂ hcount _ _ _ hx1 hcent =>
    hs.centralizer_le_H274_of_eight h5 hRS₂ hcount hx1 hcent

theorem tightConnLeafR'_of_residuals₃ (h26_2 : TightC26_2R r n) (h26_13 : TightC26_13R r n)
    (h5 : TightSec5CliqueR r n) (hB : TightBenderEndR) (hE4 : TightF26E4R r n)
    (hTri : TightSecTriangleR r n) (hT4 : Thm4RBelow r n) (hH : TightHyp51TriR r n)
    (hN : TightAlphaNormR r n) (hYs : TightC27_YsmallR r n) : TightConnLeafR' r n :=
  tightConnLeafR'_of_residuals₂ h26_2 h26_13 (tightC27_4MR_of h5) hB hE4 hTri hT4 hH hN hYs

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
