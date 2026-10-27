module

public import CFSG.ClassicalInvolution.Q3.Q3TSClosure
public import CFSG.ClassicalInvolution.Q3.Q3TWRowB

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TS

open CFSG.LieType CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.Timmesfeld CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair spinMinusModel
  minusLongBlock)
open scoped MatrixGroups

section Conj

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem exists_conj_of_mem_longRootSetU {hn : 2 ≤ n} {L₁ L₂ : Subgroup (Su K p f n)}
    (h₁ : L₁ ∈ longRootSetU (K := K) (p := p) (f := f) hn)
    (h₂ : L₂ ∈ longRootSetU (K := K) (p := p) (f := f) hn) :
    ∃ g : Su K p f n, L₁ = conjSub g L₂ := by
  obtain ⟨i₁, g₁, hL₁, -⟩ := h₁
  obtain ⟨i₂, g₂, hL₂, -⟩ := h₂
  refine ⟨g₁ * g₂⁻¹, ?_⟩
  have e1 : L₁ = conjSub g₁ (rootSU2 K p f hn) := hL₁
  have e2 : L₂ = conjSub g₂ (rootSU2 K p f hn) := hL₂
  rw [e1, e2, conjSub_mul, conjSub_inv_conjSub]

theorem equiv_mem_center {A B : Type*} [Group A] [Group B] (e : A ≃* B) {a : A}
    (h : a ∈ Subgroup.center A) : e a ∈ Subgroup.center B := by
  rw [Subgroup.mem_center_iff] at h ⊢
  intro b
  obtain ⟨c, rfl⟩ := e.surjective b
  rw [← map_mul, ← map_mul, h c]

end Conj


theorem oddLieType_of_chainSU4_3 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) (hconn : RouteD.DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember3 K₀ z) (hshape : LocalShapeC3 2 (CompData.model .PSU 4) Ω z)
    (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z) (hW : Q3TW.WeakCT3MinusMap 5)
    (U : Fin (5 - 1) → Subgroup G) (hU0 : U (twIdx0 (by norm_num : 3 ≤ 5)) ∈ Ω)
    (hcomm : ∀ i j : Fin (5 - 1), i.val + 1 < j.val → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin (5 - 1), i.val + 1 = j.val → j.val + 2 < 5 →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j))
    (htw : ∀ i j : Fin (5 - 1), i.val + 3 = 5 → j.val + 2 = 5 →
      ∃ W, TwistedB2BlockPair (minusCoeffs_irr 3 1) W (U i) (U j)) :
    CFSG.Blueprint.OddLieType G := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hn3 : 3 ≤ 5 := by norm_num
  have hirr := minusCoeffs_irr 3 1
  have hadm : StatedLieAdmissible .POmegaMinus 5 3 1 := ⟨hp, le_rfl, by show 4 ≤ 5; omega⟩
  have hadmU : StatedLieAdmissible .PSU 4 3 1 := ⟨hp, le_rfl, by norm_num, by decide⟩
  have hfundM : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .POmegaMinus := trivial
  have hscT : FundamentalSingleClass .POmegaMinus (modelUniv .POmegaMinus 5 3 1 hp).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaMinus 5 3 1 hp hfundM hadm
      (by decide) (by decide)
  have hscT' : FundamentalSingleClass .POmegaMinus (minusDatum 5 hirr) := hscT
  obtain ⟨Ψ, hker, hΨ⟩ := hW U hcomm hpair htw
  set n0 : Fin (5 - 1) := twIdx0 hn3 with hn0
  have hlong0 : n0.val + 1 < 5 - 1 := by simp only [n0, twIdx0]; omega
  have hN₀ : (rankOne (minusDatum 5 hirr).rootGroup n0).map Ψ = U n0 := hΨ n0
  have hTc : ∀ k : Fin (5 - 1), 2 ≤ k.val → Commutes ((rankOneHiMinus hirr hn3).map Ψ) (U k) := by
    intro k hk
    rw [← hΨ k]
    exact commutes_map_hom Ψ (commutes_rankOneHiMinus hirr hn3 hk)
  have hΩΨ : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 5 hirr), R.map Ψ ∈ Ω := by
    intro R hR
    obtain ⟨g, hg⟩ := hscT' (rankOne (minusDatum 5 hirr).rootGroup n0)
      (rankOne_mem_fund_minus hirr hlong0) R hR
    rw [hg, ← CFSG.ClassicalInvolution.Generic.conjSub_map, hN₀]
    exact hΩ.conjInvariant _ _ hU0
  obtain ⟨W, hWtw⟩ := htw 2 3 rfl rfl
  have hWle : W ≤ U 2 ⊔ U 3 :=
    twistedB2BlockPair_le_sup hirr (spinMinus6Generated_galois hp2) hWtw
  have := fact_shortField hirr
  obtain ⟨θ, hrange, hkerθ, -, hlbU, -⟩ := hWtw
  obtain ⟨s, hsL⟩ := CFSG.ClassicalInvolution.WeakCT.SU4.su4SpinMinus_exists (p := 3) (f := 1)
    hp2 (by norm_num) hirr
  obtain ⟨e₀, he₀⟩ := psu_model_equiv (p := 3) (f := 1) hp2 hadmU
  set ψD : (modelUniv .PSU 4 3 1 hp).K →* G :=
    θ.comp (s.symm.toMonoidHom.comp e₀.toMonoidHom) with hψD
  have hψDker : ψD.ker ≤ Subgroup.center (modelUniv .PSU 4 3 1 hp).K := by
    intro x hx
    have hx' : s.symm (e₀ x) ∈ θ.ker := hx
    have h1 := equiv_mem_center s (hkerθ hx')
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 := equiv_mem_center e₀.symm h1
    rwa [MulEquiv.symm_apply_apply] at h2
  have hψDle : ψD.range ≤ U 2 ⊔ U 3 := by
    rintro _ ⟨x, rfl⟩
    have hx : ψD x ∈ θ.range := ⟨s.symm (e₀ x), rfl⟩
    rw [hrange] at hx
    exact hWle hx
  have hΨrange : U 2 ⊔ U 3 ≤ Ψ.range := by
    refine sup_le ?_ ?_
    · rw [← hΨ 2]
      exact Subgroup.map_le_range Ψ _
    · rw [← hΨ 3]
      exact Subgroup.map_le_range Ψ _
  have hpc := powCop3_model (t := .PSU) (n := 4) trivial hadmU (by decide) (by decide)
  have hcopD : ∀ w ∈ ψD.ker, ¬ 3 ∣ orderOf w := fun w hw => hpc.cop w (hψDker hw)
  have hYFT : ∀ R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 hp).D,
      ∃ S ∈ fundamentalSubgroups .POmegaMinus (minusDatum 5 hirr), R.map ψD = S.map Ψ := by
    intro R hR
    obtain ⟨g, hg⟩ := exists_conj_of_mem_longRootSetU ((he₀ R).mp hR) hsL
    obtain ⟨h, hh⟩ : θ (s.symm g) ∈ Ψ.range := by
      have hmem : θ (s.symm g) ∈ θ.range := ⟨_, rfl⟩
      rw [hrange] at hmem
      exact hΨrange (hWle hmem)
    have hLmap : (Subgroup.map s.toMonoidHom (minusLongBlock (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2).range).map (θ.comp s.symm.toMonoidHom) = U 2 := by
      rw [Subgroup.map_map]
      have : (θ.comp s.symm.toMonoidHom).comp s.toMonoidHom = θ :=
        MonoidHom.ext fun x => by simp
      rw [this]
      exact hlbU
    have hfun : (θ.comp s.symm.toMonoidHom) g = Ψ h := by
      rw [hh]
      rfl
    refine ⟨conjSub h (rankOne (minusDatum 5 hirr).rootGroup (2 : Fin (5 - 1))),
      conjSub_mem_fundamentalSubgroups
        (rankOne_mem_fund_minus hirr (by norm_num : (2 : Fin (5 - 1)).val + 1 < 5 - 1)) h, ?_⟩
    have e1 : R.map ψD = (R.map e₀.toMonoidHom).map (θ.comp s.symm.toMonoidHom) := by
      rw [Subgroup.map_map]
      rfl
    rw [e1, hg, map_conjSub_eq, hLmap, hfun, ← hΨ 2]
    exact CFSG.ClassicalInvolution.Generic.conjSub_map Ψ h _
  have hY0 : Commutes (U 2 ⊔ U 3) (U n0) :=
    commutes_sup_of_both (hcomm n0 2 (by simp [n0, twIdx0])).symm
      (hcomm n0 3 (by simp [n0, twIdx0])).symm
  have hT0 : Commutes (U 2 ⊔ U 3) ((rankOneHiMinus hirr hn3).map Ψ) :=
    commutes_sup_of_both (hTc 2 (by simp)).symm (hTc 3 (by simp)).symm
  have hfin : Finite (CompData.model .PSU 4).G :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) hp trivial hadmU
  have hcount := hshape.ncard_locFamily_le hfin
  obtain ⟨-, hsurj⟩ := surjective_of_layer_closure3 hΩ hex hconn hK₀ hsingle hz hP1 hO3
    (FT := fundamentalSubgroups .POmegaMinus (minusDatum 5 hirr))
    (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR R' hR' => hscT' R hR R' hR') Ψ hΩΨ
    (N₀R := rankOne (minusDatum 5 hirr).rootGroup n0) (TR := rankOneHiMinus hirr hn3)
    (rankOne_mem_fund_minus hirr hlong0) (rankOneHiMinus_mem_fund hirr hn3)
    (commutes_map_hom Ψ (commutes_hiMinus_twin hirr hn3))
    (KY := (modelUniv .PSU 4 3 1 hp).K)
    (Y := fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 hp).D)
    ψD hψDker hcopD hpc.pow3 hYFT
    (fun R hR x hx y hy => by
      rw [hN₀] at hy
      exact hY0 x (hψDle (Subgroup.map_le_range ψD R hx)) y hy)
    (fun R hR x hx y hy => (hT0 y (hψDle (Subgroup.map_le_range ψD R hy)) x hx).symm)
    hcount
  have hmodel : CFSG.Blueprint.LieModel
      (spinGroup (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) ⧸
        Subgroup.center (spinGroup (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
          (minusCoeffs 3 1).2))) .POmegaMinus 5 3 1 :=
    (curtisTitsConclusion_spinMinus.{0} hirr hadm (by rw [card_gf3, pow_one])).1.2.2
  exact oddLieType_of_model3 hnab hadm
    (Q3TW.lieModel_of_surjective_simple3 hnab Ψ hsurj hker hmodel)

@[expose] def ChainPiece3TwinSU4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 2 (CompData.model .PSU 4) (conjClass3 K) z →
      ∃ U : Fin (5 - 1) → Subgroup G, U (twIdx0 (by norm_num : 3 ≤ 5)) ∈ conjClass3 K ∧
        (∀ i j : Fin (5 - 1), i.val + 1 < j.val → Commutes (U i) (U j)) ∧
        (∀ i j : Fin (5 - 1), i.val + 1 = j.val → j.val + 2 < 5 →
          ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) ∧
        ∀ i j : Fin (5 - 1), i.val + 3 = 5 → j.val + 2 = 5 →
          ∃ W, TwistedB2BlockPair (minusCoeffs_irr 3 1) W (U i) (U j)

theorem piece3TwinSU4_of_chain (h3 : OddThreeFreeInput) (hW : Q3TW.WeakCT3MinusMap 5)
    (h : ChainPiece3TwinSU4) : Piece3TwinSU4 := by
  rintro a t n ⟨rfl, rfl, rfl⟩ G _ _ _ hnab K z hR hshape
  obtain ⟨U, hU0, hcomm, hpair, htw⟩ := h G hnab K z hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  exact Or.inl (oddLieType_of_chainSU4_3 hnab hR.inClass hex hK hsingle hconn hR.cls hshape hP1
    (h3 G K z hR) hW U hU0 hcomm hpair htw)

end CFSG.ClassicalInvolution.Q3.Q3TS
