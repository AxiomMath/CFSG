module

public import CFSG.ClassicalInvolution.Q3.Q3TSClosure
public import CFSG.ClassicalInvolution.Q3.Q3TWRowB
public import CFSG.ClassicalInvolution.Q3.Q3ZModel
public import CFSG.ClassicalInvolution.Q3.Q3TWWPairStmt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TPS

open CFSG.LieType CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Universal.Spin CFSG.Timmesfeld
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair longBlock
  planeGroup IsHyperbolicPlane exists_planeGroup_eq_conj_longBlock mem_fundamentalSubgroups_PSp_iff
  symplecticBlockPair_le_sup)
open scoped MatrixGroups

theorem oddLieType_of_chainB4_3_pair {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) (hconn : RouteD.DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember3 K₀ z) (hshape : LocalShapeC3 2 (CompData.model .PSp 2) Ω z)
    (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z) (hW : Q3TW.WeakCT3OddMapPair 4)
    (U : Fin 4 → Subgroup G) (hU0 : U 0 ∈ Ω)
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin 4, i.val + 1 = j.val → j.val + 1 < 4 →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j))
    (hsp : ∀ i j : Fin 4, i.val + 2 = 4 → j.val + 1 = 4 →
      ∃ W, SymplecticBlockPair (GaloisField 3 1) W (U i) (U j)) :
    CFSG.Blueprint.OddLieType G := by
  have hp : Nat.Prime 3 := Nat.prime_three
  set F := GaloisField 3 1 with hFdef
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField 1
    (by norm_num)
  have hn3 : 3 ≤ 4 := by norm_num
  have hadm : StatedLieAdmissible .POmegaOdd 4 3 1 := ⟨hp, le_rfl, by norm_num, by norm_num⟩
  have hadmP : StatedLieAdmissible .PSp 2 3 1 := Q3Z.statedLieAdmissible_psp2
  have hfundM : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .POmegaOdd := trivial
  have hscT : FundamentalSingleClass .POmegaOdd (oddDatum 4 F) :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaOdd 4 3 1 hp hfundM hadm
      (by decide) (by decide)
  obtain ⟨Ψ, hker, -, hΨ⟩ := hW U hcomm hpair hsp
  set n0 : Fin 4 := zeroB (by norm_num) with hn0
  have hlong0 : n0.val + 1 < 4 := by simp [n0, zeroB_val]
  have hN₀ : (rankOne (oddDatum 4 F).rootGroup n0).map Ψ = U n0 := hΨ n0
  have hTc : ∀ k : Fin 4, k.val ≠ 1 → Commutes ((rootθB 4 F).map Ψ) (U k) := by
    intro k hk
    rw [← hΨ k]
    exact commutes_map_hom Ψ (commutes_rootθB_rankOne hn3 h2 hk)
  have hΩΨ : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum 4 F), R.map Ψ ∈ Ω := by
    intro R hR
    obtain ⟨g, hg⟩ := hscT (rankOne (oddDatum 4 F).rootGroup n0)
      (rankOne_mem_fundamentalSubgroups_oddDatum hn3 hlong0) R hR
    rw [hg, ← CFSG.ClassicalInvolution.Generic.conjSub_map, hN₀]
    exact hΩ.conjInvariant _ _ hU0
  obtain ⟨W, hWsp⟩ := hsp 2 3 rfl rfl
  have hWle : W ≤ U 2 ⊔ U 3 := symplecticBlockPair_le_sup hWsp
  obtain ⟨θ, c, hrange, hkerθ, -, hφU, -⟩ := hWsp
  set ψD : StatedSp 2 F →* G := θ.comp (MulAut.conj c⁻¹).toMonoidHom with hψD
  have hψDker : ψD.ker ≤ Subgroup.center (StatedSp 2 F) := by
    intro x hx
    have hx' : c⁻¹ * x * c⁻¹⁻¹ ∈ θ.ker := hx
    have hz' := hkerθ hx'
    rw [Subgroup.mem_center_iff] at hz' ⊢
    intro y
    have h := hz' (c⁻¹ * y * c⁻¹⁻¹)
    have e1 : c * (c⁻¹ * y * c⁻¹⁻¹ * (c⁻¹ * x * c⁻¹⁻¹)) * c⁻¹ = y * x := by group
    have e2 : c * (c⁻¹ * x * c⁻¹⁻¹ * (c⁻¹ * y * c⁻¹⁻¹)) * c⁻¹ = x * y := by group
    rw [← e1, ← e2, h]
  have hψDL : (longBlock F 2 1).range.map ψD = U 2 := by
    rw [hψD, ← Subgroup.map_map]
    exact hφU
  have hψDle : ψD.range ≤ U 2 ⊔ U 3 := by
    rintro _ ⟨x, rfl⟩
    have hx : ψD x ∈ θ.range := ⟨c⁻¹ * x * c⁻¹⁻¹, rfl⟩
    rw [hrange] at hx
    exact hWle hx
  have hΨrange : U 2 ⊔ U 3 ≤ Ψ.range := by
    refine sup_le ?_ ?_
    · rw [← hΨ 2]
      exact Subgroup.map_le_range Ψ _
    · rw [← hΨ 3]
      exact Subgroup.map_le_range Ψ _
  have hcopD : ∀ w ∈ ψD.ker, ¬ 3 ∣ orderOf w := fun w hw =>
    Q3Z.orderOf_not_dvd_three_of_center_sp (by norm_num : 1 ≤ 2) (hψDker hw)
  have hYpow : ∀ R ∈ fundamentalSubgroups .PSp (modelUniv .PSp 2 3 1 hp).D, Pow3 R :=
    (powCop3_model (t := .PSp) (n := 2) trivial hadmP (by decide) (by decide)).pow3
  have hYFT : ∀ R ∈ fundamentalSubgroups .PSp (modelUniv .PSp 2 3 1 hp).D,
      ∃ S ∈ fundamentalSubgroups .POmegaOdd (oddDatum 4 F), R.map ψD = S.map Ψ := by
    intro R hR
    obtain ⟨P, hP, rfl⟩ := (mem_fundamentalSubgroups_PSp_iff hadmP R).mp hR
    obtain ⟨g, hg⟩ := exists_planeGroup_eq_conj_longBlock hP (1 : Fin 2)
    obtain ⟨h, hh⟩ : ψD g ∈ Ψ.range := hΨrange (hψDle ⟨g, rfl⟩)
    refine ⟨conjSub h (rankOne (oddDatum 4 F).rootGroup (⟨2, by norm_num⟩ : Fin 4)),
      conjSub_mem_fundamentalSubgroups
        (rankOne_mem_fundamentalSubgroups_oddDatum hn3 (by simp)) h, ?_⟩
    rw [hg]
    change Subgroup.map ψD (conjSub g (longBlock F 2 1).range) = _
    rw [map_conjSub_eq, map_conjSub_eq, hψDL, ← hΨ 2, hh]
    rfl
  have hY0 : Commutes (U 2 ⊔ U 3) (U 0) :=
    commutes_sup_of_both (hcomm 0 2 (by norm_num)).symm (hcomm 0 3 (by norm_num)).symm
  have hT0 : Commutes (U 2 ⊔ U 3) ((rootθB 4 F).map Ψ) :=
    commutes_sup_of_both (hTc 2 (by simp)).symm (hTc 3 (by simp)).symm
  have hcount := hshape.ncard_locFamily_le Q3Z.finite_psp2
  obtain ⟨-, hsurj⟩ := Q3TS.surjective_of_layer_closure3 hΩ hex hconn hK₀ hsingle hz hP1 hO3
    (FT := fundamentalSubgroups .POmegaOdd (oddDatum 4 F))
    (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR R' hR' => hscT R hR R' hR') Ψ hΩΨ
    (N₀R := rankOne (oddDatum 4 F).rootGroup n0) (TR := rootθB 4 F)
    (rankOne_mem_fundamentalSubgroups_oddDatum hn3 hlong0) (rootθB_mem_fundamentalSubgroups hn3)
    (by rw [hN₀]; exact hTc n0 (by simp [n0, zeroB_val]))
    (KY := StatedSp 2 F) (Y := fundamentalSubgroups .PSp (modelUniv .PSp 2 3 1 hp).D)
    ψD hψDker hcopD hYpow hYFT
    (fun R hR x hx y hy => by
      rw [hN₀] at hy
      exact hY0 x (hψDle (Subgroup.map_le_range ψD R hx)) y hy)
    (fun R hR x hx y hy => (hT0 y (hψDle (Subgroup.map_le_range ψD R hy)) x hx).symm)
    hcount
  have hmodel : CFSG.Blueprint.LieModel
      (spinGroup (quadOdd 4 (GaloisField 3 1)) ⧸
        Subgroup.center (spinGroup (quadOdd 4 (GaloisField 3 1)))) .POmegaOdd 4 3 1 :=
    (curtisTitsConclusion_spinOdd.{0} hadm (by rw [card_gf3, pow_one])).1.2.2
  exact oddLieType_of_model3 hnab hadm
    (Q3TW.lieModel_of_surjective_simple3 hnab Ψ hsurj hker hmodel)

@[expose] def ChainPiece3TwinSp2Pair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 2 (CompData.model .PSp 2) (conjClass3 K) z →
      ∃ U : Fin 4 → Subgroup G, U 0 ∈ conjClass3 K ∧
        (∀ i j : Fin 4, i.val + 1 < j.val → Commutes (U i) (U j)) ∧
        (∀ i j : Fin 4, i.val + 1 = j.val → j.val + 1 < 4 →
          ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) ∧
        ∀ i j : Fin 4, i.val + 2 = 4 → j.val + 1 = 4 →
          ∃ W, SymplecticBlockPair (GaloisField 3 1) W (U i) (U j)

theorem piece3TwinSp2_of_chain_pair (h3 : OddThreeFreeInput) (hW : Q3TW.WeakCT3OddMapPair 4)
    (h : ChainPiece3TwinSp2Pair) : Piece3TwinSp2 := by
  rintro a t n ⟨rfl, rfl, rfl⟩ G _ _ _ hnab K z hR hshape
  obtain ⟨U, hU0, hcomm, hpair, hsp⟩ := h G hnab K z hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  exact Or.inl (oddLieType_of_chainB4_3_pair hnab hR.inClass hex hK hsingle hconn hR.cls hshape hP1
    (h3 G K z hR) hW U hU0 hcomm hpair hsp)

end CFSG.ClassicalInvolution.Q3.Q3TPS
