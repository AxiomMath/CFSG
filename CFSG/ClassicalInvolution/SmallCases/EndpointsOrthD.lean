module

public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthNodes
public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthLayerD
public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthClosure
public import CFSG.ClassicalInvolution.RouteD.LocalTwinChain
import CFSG.ClassicalInvolution.RouteD.GapsEnd4Final
import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.Phan (Su)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair spinMinusModel minusLongBlock)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (NoCover)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem ncard_fund_psu_le (hp2 : p ≠ 2) {n : ℕ} (hadm : StatedLieAdmissible .PSU n p f) :
    (fundamentalSubgroups .PSU (modelUniv .PSU n p f Fact.out).D).ncard ≤
      (longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f)
        (by have := hadm.2.2.1; omega : 2 ≤ n)).ncard := by
  obtain ⟨e, he⟩ := psu_model_equiv hp2 hadm
  refine Set.ncard_le_ncard_of_injOn (fun R => R.map e.toMonoidHom) (fun R hR => (he R).mp hR) ?_
    (Set.toFinite _)
  intro R _ R' _ h
  exact Subgroup.map_injective e.injective h

theorem minus10_closure [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hb : SU4SpinMinus p f (minusCoeffs_irr p f)) (hg6 : SpinMinus6Generated (minusCoeffs_irr p f))
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hconn : DeltaConnected Ω)
    {K₀ K₁ K₂ Us : Subgroup G} (hK₀ : K₀ ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀)
    {z : G} (hz : IsClassicalMember p f K₀ z) (hP1 : LocalOddCentral Ω {z})
    (hshape : LocalShapeT p f 2 .PSU 4 Ω z) (c02 : Commutes K₀ K₂) (c0s : Commutes K₀ Us)
    (c1s : Commutes K₁ Us) (p01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₀ K₁)
    (p12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂)
    (hs : ∃ W, TwistedB2BlockPair (minusCoeffs_irr p f) W K₂ Us) :
    ∃ Ψ : spinGroup (Spin.quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2) →* G, Ψ.ker ≤ Subgroup.center _ ∧ Function.Surjective Ψ ∧
      Ψ.range = K₀ ⊔ K₁ ⊔ K₂ ⊔ Us ∧
      ∀ L : Subgroup G, L ∈ Ω ↔
        ∃ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 5 (minusCoeffs_irr p f)),
          L = R.map Ψ := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  set F := GaloisField p f with hFdef
  have hF : Nat.card F = p ^ f := GaloisField.card p f (by omega)
  have h4 : 4 ≤ Nat.card F := by rw [hF]; omega
  have hirr := minusCoeffs_irr p f
  have := fact_shortField hirr
  have hn3 : 3 ≤ 5 := by norm_num
  have hadm : StatedLieAdmissible .POmegaMinus 5 p f := ⟨Fact.out, hf, by norm_num⟩
  have hadmU : StatedLieAdmissible .PSU 4 p f :=
    ⟨Fact.out, hf, by norm_num, fun h => by have := congrArg Prod.snd h; simp at this; omega⟩
  let U : Fin (5 - 1) → Subgroup G := ![K₀, K₁, K₂, Us]
  have hcomm : ∀ i j : Fin (5 - 1), i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    exacts [c02, c0s, c1s]
  have hpair : ∀ i j : Fin (5 - 1), i.val + 1 = j.val → j.val + 2 < 5 →
      ∃ W, LinearBlockStandardPair F W (U i) (U j) := by
    intro i j hij hj
    fin_cases i <;> fin_cases j <;> simp at hij hj
    exacts [p01, p12]
  have htw : ∀ i j : Fin (5 - 1), i.val + 3 = 5 → j.val + 2 = 5 →
      ∃ W, TwistedB2BlockPair hirr W (U i) (U j) := by
    intro i j hi hj
    fin_cases i <;> fin_cases j <;> simp at hi hj
    exact hs
  obtain ⟨Ψ, hker, hrange, hblk⟩ := weakCT_spinMinus_subgroup hadm hp2 hF h4 hirr hg6 U hcomm
    hpair htw
  have hsingleN : FundamentalSingleClass .POmegaMinus (minusDatum 5 hirr) :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaMinus 5 p f Fact.out trivial
      hadm (by decide) (by decide)
  have hk0 : (twIdx0 hn3).val + 1 < 5 - 1 := by simp only [twIdx0]; omega
  have hr0 : (CurtisTits.rankOne (minusDatum 5 hirr).rootGroup (twIdx0 hn3)).map Ψ = K₀ :=
    hblk _
  have hr0mem := rankOne_mem_fund_minus hirr hk0
  have hΩΨ : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 5 hirr), R.map Ψ ∈ Ω := by
    intro R hR
    obtain ⟨g, hg⟩ := hsingleN _ hr0mem R hR
    rw [hg, map_conjSub_eq, hr0]
    exact hΩ.conjInvariant _ _ hK₀
  have hTU : ∀ j : Fin (5 - 1), 2 ≤ j.val →
      Commutes ((rankOneHiMinus hirr hn3).map Ψ) (U j) := by
    intro j hj
    rw [← hblk j]
    exact commutes_map_hom Ψ (commutes_rankOneHiMinus hirr hn3 hj)
  have hTN : Commutes ((rankOneHiMinus hirr hn3).map Ψ)
      ((CurtisTits.rankOne (minusDatum 5 hirr).rootGroup (twIdx0 hn3)).map Ψ) :=
    commutes_map_hom Ψ (commutes_hiMinus_twin hirr hn3)
  obtain ⟨e, he⟩ := hb
  obtain ⟨W, hW⟩ := hs
  obtain ⟨θ, hθrange, hθker, hθl, hθU, hθV⟩ := hW
  let ψD : Su (GaloisField p (2 * f)) p f 4 →* G := θ.comp e.symm.toMonoidHom
  have hkerD : ψD.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f 4) := by
    intro x hx
    have hx1 : e.symm x ∈ θ.ker := hx
    have hc := hθker hx1
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro y
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact hc (e.symm y)
  have hWle : W ≤ K₂ ⊔ Us := by
    rw [← hθrange, MonoidHom.range_eq_map, ← hg6, Subgroup.map_sup, hθU, hθV]
  have hψDrange : ψD.range = W := by
    rw [← hθrange]
    show (θ.comp e.symm.toMonoidHom).range = θ.range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective, Subgroup.map_top]
  have hN₂ : (CurtisTits.rankOne (minusDatum 5 hirr).rootGroup (⟨2, by norm_num⟩ : Fin (5 - 1))).map
      Ψ = K₂ := hblk _
  have hK₂le : K₂ ≤ Ψ.range := by rw [hrange]; exact le_iSup U 2
  have hUsle : Us ≤ Ψ.range := by rw [hrange]; exact le_iSup U 3
  have hψDle : ψD.range ≤ Ψ.range := by
    rw [hψDrange]
    exact hWle.trans (sup_le hK₂le hUsle)
  have hrangeComm : Commutes (K₂ ⊔ Us) K₀ := commutes_sup_of_both c02.symm c0s.symm
  have hTK₂ : Commutes ((rankOneHiMinus hirr hn3).map Ψ) K₂ := hTU 2 (by simp)
  have hTUs : Commutes ((rankOneHiMinus hirr hn3).map Ψ) Us := hTU 3 (by simp)
  have hTcomm : Commutes ((rankOneHiMinus hirr hn3).map Ψ) (K₂ ⊔ Us) := fun x hx y hy => by
    have h1 : Commutes (K₂ ⊔ Us) ((rankOneHiMinus hirr hn3).map Ψ) :=
      commutes_sup_of_both hTK₂.symm hTUs.symm
    exact (h1 y hy x hx).symm
  have hk24 : 2 ≤ 4 := by norm_num
  have hYconj : ∀ R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) hk24,
      ∃ g : Su (GaloisField p (2 * f)) p f 4,
        R = conjSub g ((spinMinusModel hirr).lb.range.map e.toMonoidHom) := by
    intro R hR
    obtain ⟨g₁, hg₁⟩ := (mem_longRootSetU_iff (K := GaloisField p (2 * f)) (p := p) (f := f)
      hk24).mp hR
    obtain ⟨g₂, hg₂⟩ := (mem_longRootSetU_iff (K := GaloisField p (2 * f)) (p := p) (f := f)
      hk24).mp he
    refine ⟨g₁ * g₂⁻¹, ?_⟩
    have hh : g₁ * g₂⁻¹ * g₂ = g₁ := by simp
    have e1 : (spinMinusModel hirr).lb.range.map e.toMonoidHom =
        conjSub g₂ (rootSU2 (GaloisField p (2 * f)) p f hk24) := hg₂
    rw [e1, hg₁, ← conjSub_mul, hh]
    rfl
  have hE₀perf : ((spinMinusModel hirr).lb.range.map e.toMonoidHom) ≤
      ⁅(spinMinusModel hirr).lb.range.map e.toMonoidHom,
        (spinMinusModel hirr).lb.range.map e.toMonoidHom⁆ :=
    map_perfect e.toMonoidHom (range_perfect_of_sl2 h4 (spinMinusModel hirr).lb)
  have hE₀ψ : ((spinMinusModel hirr).lb.range.map e.toMonoidHom).map ψD = K₂ := by
    rw [Subgroup.map_map]
    have : ψD.comp e.toMonoidHom = θ := by
      ext x
      simp [ψD]
    rw [this, hθU]
  have hfinY : Finite (modelUniv .PSU 4 p f Fact.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 Fact.out trivial hadmU
  have hcount := (hshape.ncard_locFamily_le (show StatedLieTag.PSU ≠ .trialityD4 by decide)
    hfinY).trans (Nat.add_le_add_left (ncard_fund_psu_le hp2 hadmU) 2)
  have hclos := surjective_of_layer_closure hΩ hconn hK₀ hsingle hz hP1
    (FT := fundamentalSubgroups .POmegaMinus (minusDatum 5 hirr))
    (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR R' hR' => hsingleN R hR R' hR') Ψ hΩΨ
    (N₀R := CurtisTits.rankOne (minusDatum 5 hirr).rootGroup (twIdx0 hn3))
    (TR := rankOneHiMinus hirr hn3) hr0mem (rankOneHiMinus_mem_fund hirr hn3) hTN
    (KY := Su (GaloisField p (2 * f)) p f 4)
    (Y := longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) hk24) ψD hkerD
    (fun R hR => by
      obtain ⟨g, rfl⟩ := hYconj R hR
      exact conjSub_perfect hE₀perf g)
    (fun R hR => by
      obtain ⟨g, rfl⟩ := hYconj R hR
      obtain ⟨h, hh⟩ : ψD g ∈ Ψ.range := hψDle ⟨g, rfl⟩
      refine ⟨conjSub h (CurtisTits.rankOne (minusDatum 5 hirr).rootGroup
        (⟨2, by norm_num⟩ : Fin (5 - 1))), conjSub_mem_fundamentalSubgroups
          (rankOne_mem_fund_minus hirr (by simp)) h, ?_⟩
      rw [map_conjSub_eq, map_conjSub_eq, hE₀ψ, hN₂, hh])
    (fun R hR => by
      obtain ⟨g, rfl⟩ := hYconj R hR
      rw [hr0]
      intro x hx y hy
      have hx' : x ∈ K₂ ⊔ Us := hWle (hψDrange ▸ Subgroup.map_le_range ψD _ hx)
      exact hrangeComm x hx' y hy)
    (fun R hR => by
      obtain ⟨g, rfl⟩ := hYconj R hR
      intro x hx y hy
      have hy' : y ∈ K₂ ⊔ Us := hWle (hψDrange ▸ Subgroup.map_le_range ψD _ hy)
      exact hTcomm x hx y hy')
    hcount
  refine ⟨Ψ, hker, hclos.2, ?_, hclos.1⟩
  rw [hrange]
  refine le_antisymm (iSup_le fun k => ?_)
    (sup_le (sup_le (sup_le (le_iSup U 0) (le_iSup U 1)) (le_iSup U 2)) (le_iSup U 3))
  fin_cases k
  · exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
  · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  · exact le_sup_of_le_left le_sup_right
  · exact le_sup_right

theorem minus10_generation [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hb : SU4SpinMinus p f (minusCoeffs_irr p f)) (hg6 : SpinMinus6Generated (minusCoeffs_irr p f))
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hconn : DeltaConnected Ω)
    {K₀ K₁ K₂ Us : Subgroup G} (hK₀ : K₀ ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀)
    {z : G} (hz : IsClassicalMember p f K₀ z) (hP1 : LocalOddCentral Ω {z})
    (hshape : LocalShapeT p f 2 .PSU 4 Ω z) (c02 : Commutes K₀ K₂) (c0s : Commutes K₀ Us)
    (c1s : Commutes K₁ Us) (p01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₀ K₁)
    (p12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂)
    (hs : ∃ W, TwistedB2BlockPair (minusCoeffs_irr p f) W K₂ Us) :
    K₀ ⊔ K₁ ⊔ K₂ ⊔ Us = ⊤ := by
  obtain ⟨Ψ, -, hsurj, hrange, -⟩ := minus10_closure hp2 hq hb hg6 hΩ hconn hK₀ hsingle hz hP1
    hshape c02 c0s c1s p01 p12 hs
  rw [← hrange]
  exact MonoidHom.range_eq_top.mpr hsurj

theorem minus10_lieSystem [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hb : SU4SpinMinus p f (minusCoeffs_irr p f)) (hg6 : SpinMinus6Generated (minusCoeffs_irr p f))
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hconn : DeltaConnected Ω)
    {K₀ K₁ K₂ Us : Subgroup G} (hK₀ : K₀ ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀)
    {z : G} (hz : IsClassicalMember p f K₀ z) (hP1 : LocalOddCentral Ω {z})
    (hshape : LocalShapeT p f 2 .PSU 4 Ω z) (c02 : Commutes K₀ K₂) (c0s : Commutes K₀ Us)
    (c1s : Commutes K₁ Us) (p01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₀ K₁)
    (p12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂)
    (hs : ∃ W, TwistedB2BlockPair (minusCoeffs_irr p f) W K₂ Us) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaMinus ∧ D.rank i = 5 := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hirr := minusCoeffs_irr p f
  have := fact_shortField hirr
  have hn3 : 3 ≤ 5 := by norm_num
  have hadm : StatedLieAdmissible .POmegaMinus 5 p f := ⟨Fact.out, hf, by norm_num⟩
  obtain ⟨Ψ, hker, hsurj, -, hΩΨ⟩ := minus10_closure hp2 hq hb hg6 hΩ hconn hK₀ hsingle hz hP1
    hshape c02 c0s c1s p01 p12 hs
  have hk0 : (twIdx0 hn3).val + 1 < 5 - 1 := by simp only [twIdx0]; omega
  exact exists_lieSystemData_of_fundamental (t := .POmegaMinus) trivial hadm Ψ hsurj hker
    ⟨_, rankOne_mem_fund_minus hirr hk0⟩ hΩΨ

theorem smallEndpoint_minus10 [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hb : SU4SpinMinus p f (minusCoeffs_irr p f)) (hg6 : SpinMinus6Generated (minusCoeffs_irr p f))
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hconn : DeltaConnected Ω)
    {K₀ K₁ K₂ : Subgroup G} (hK₀ : K₀ ∈ Ω) (hK₁ : K₁ ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) {z₀ z₁ : G}
    (hz₀ : IsClassicalMember p f K₀ z₀) (hz₁ : IsClassicalMember p f K₁ z₁)
    (hP1 : LocalOddCentral Ω {z₀}) (Λ : SuLayer p f 2 Ω z₀) (c02 : Commutes K₀ K₂)
    (p01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₀ K₁)
    (p12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂)
    (hpat : ∃ Us : Subgroup G, Λ.IsShortNode (minusCoeffs_irr p f) K₂ Us ∧
      Us ≤ Subgroup.centralizer ({z₁} : Set G)) :
    ∃ Ψ : spinGroup (Spin.quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2) →* G, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧
      CFSG.IsQuasisimple G ∧
        CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G) .POmegaMinus 5 p f := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [hF]; omega
  have hadm : StatedLieAdmissible .POmegaMinus 5 p f := ⟨Fact.out, hf, by norm_num⟩
  have : NeZero f := ⟨by omega⟩
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField hp2 hq
  obtain ⟨Us, ⟨hUsY, hUsperf, hUsrange, hspair, hUsc, -⟩, hUsz₁⟩ := hpat
  have c0s : Commutes K₀ Us := by
    obtain ⟨j, hj, hKj⟩ := Λ.exists_other_of_self hp2 hq hK₀ hz₀
    exact hUsc K₀ ⟨hK₀, le_centralizer_of_isClassicalMember hz₀⟩ j hj hKj
  have c1s : Commutes K₁ Us :=
    commutes_partner_of_perfect_conj hp2 hq (Gaps.fundNoncentral p) hS3 hΩ hsingle hz₀
      ⟨Λ.D, by rw [Λ.card_eq]; norm_num⟩ hP1 hK₁ hz₁ p01 hUsperf hUsz₁
      (fun u hu => Subgroup.mem_centralizer_iff.mpr fun k hk => c0s k hk u hu)
  have hshape : LocalShapeT p f 2 .PSU 4 Ω z₀ :=
    ⟨Λ.D, Λ.card_eq, Λ.i₁, Λ.tag_eq, Λ.rank_eq, Λ.rest⟩
  have hgen := minus10_generation hp2 hq hb hg6 hΩ hconn hK₀ hsingle hz₀ hP1 hshape c02 c0s c1s
    p01 p12 hspair
  exact smallEndpoint_minus10_of_nodes hadm hp2 hF h4 (minusCoeffs_irr p f) hgen c02 c0s c1s p01
    p12 hspair

end CFSG.ClassicalInvolution.RouteD
