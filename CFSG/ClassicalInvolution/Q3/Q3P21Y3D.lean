module

public import CFSG.ClassicalInvolution.Q3.Q3P21Y3C
public import CFSG.ClassicalInvolution.Q3.Q3P21Y3S
public import CFSG.ClassicalInvolution.Q3.Q3P21Y1S
public import CFSG.ClassicalInvolution.Q3.Q3P21S4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open scoped MatrixGroups Matrix
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt TwinRow)
open CFSG.ClassicalInvolution.Q3 (CompData IsClassicalMember3)


@[expose] def LiftYAll : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}
    (c : Q3TP.TCtxS3 .PSU 4 Ω K z), LiftYStmt c

@[expose] def StabAll : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}
    (c : Q3TP.TCtxS3 .PSU 4 Ω K z), StabStmt c

theorem twinSU4Linear3_of_inputs (h3 : OddThreeFreeInput) (hP : Q3TC.ProductP1Input3)
    (hY1c : Y1cStmt) (hY1a : Y1aStmt) (hY1b : Y1bStmt) (hlift : LiftYAll) (hstab : StabAll) :
    TwinSU4Linear3 := by
  intro G _ _ _ hnab K z hR hshape c N K₂ t hNΩ hNt hK₂ hK₂K hnotTwin hKK₂ p1 p2 ht
  classical
  obtain ⟨T, K₃, w, hTz, hTQ, hK₃z, hK₃K, hK₃T, hK₃K₂, hK₂K₃, hK₂Q, hK₃Q, hw, hwt, hpairNK₃,
    hpar⟩ := chainParity3 h3 hP hnab hR hshape c hNΩ hNt hK₂ hK₂K hnotTwin hKK₂ p1 p2
  have ht2 : t * t = 1 := Q3TLK.mul_self_eq_one_of_orderOf_eq_two3 hNt.orderOf_eq_two
  set τ : locQuot (conjClass3 K) z ≃* locQuot (conjClass3 K) z :=
    Gaps.locAut c.hΩ.conjInvariant ht with hτdef
  have hτ2 : ∀ x, τ (τ x) = x := Gaps.locAut_locAut c.hΩ.conjInvariant ht ht2
  obtain ⟨R₂, hR₂, hK₂R⟩ := c.exists_fund_of_ne hK₂ hK₂K hK₂Q
  obtain ⟨R₃, hR₃, hK₃R⟩ := c.exists_fund_of_ne hK₃z hK₃K hK₃Q
  have hR₂₃ : R₂ ≠ R₃ := fun h =>
    hK₃K₂ (c.eq_of_locImg_eq hK₃z hK₂ (by rw [hK₃R, hK₂R, h]))
  have hcR : Commutes R₂ R₃ := (c.commutes_iff_fund hK₂ hK₃z hR₂ hK₂R hK₃R).mp hK₂K₃
  have hadmU : StatedLieAdmissible .PSU 4 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  obtain ⟨φ₀, hφ₀⟩ := psu_model_equiv (p := 3) (f := 1) (by norm_num) hadmU
  obtain ⟨g, hg₂, hg₃⟩ := hY1c (R₂.map φ₀.toMonoidHom) ((hφ₀ R₂).mp hR₂) (R₃.map φ₀.toMonoidHom)
    ((hφ₀ R₃).mp hR₃) (fun h => hR₂₃ (Subgroup.map_injective φ₀.injective h))
    ((Gaps.commutes_map_equiv φ₀).mpr hcR)
  set φ : (modelUniv .PSU 4 3 1 Nat.prime_three).K ≃* Su (GaloisField 3 (2 * 1)) 3 1 4 :=
    φ₀.trans (MulAut.conj g⁻¹) with hφdef
  have hmapφ : ∀ R : Subgroup (modelUniv .PSU 4 3 1 Nat.prime_three).K,
      R.map φ.toMonoidHom = conjSub g⁻¹ (R.map φ₀.toMonoidHom) := fun R => by
    unfold conjSub
    rw [Subgroup.map_map]
    rfl
  have hfund : ∀ R : Subgroup (modelUniv .PSU 4 3 1 Nat.prime_three).K,
      R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Nat.prime_three).D ↔
        R.map φ.toMonoidHom ∈ longRootSetU (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1)
          (by norm_num : 2 ≤ 4) := by
    intro R
    rw [hmapφ]
    constructor
    · intro hR
      exact longRootSetU_conjInvariant (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1)
        (by norm_num : 2 ≤ 4) g⁻¹ _ ((hφ₀ R).mp hR)
    · intro h
      have h1 := longRootSetU_conjInvariant (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1)
        (by norm_num : 2 ≤ 4) g _ h
      rw [conjSub_conjSub_inv] at h1
      exact (hφ₀ R).mpr h1
  have hR₂φ : R₂.map φ.toMonoidHom = rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4) := by
    rw [hmapφ, hg₂]
    exact conjSub_inv_conjSub g _
  have hR₃φ : R₃.map φ.toMonoidHom = rootSU2Two := by
    rw [hmapφ, hg₃]
    exact conjSub_inv_conjSub g _
  set ψ : Su (GaloisField 3 (2 * 1)) 3 1 4 →* locQuot (conjClass3 K) z :=
    c.d.ψ.comp φ.symm.toMonoidHom with hψdef
  have hψφ : ∀ r, ψ (φ r) = c.d.ψ r := fun r => by simp [hψdef]
  have hker' : ψ.ker ≤ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4) := by
    intro y hy
    have h1 : φ.symm y ∈ c.d.ψ.ker := hy
    have h2 := c.d.ker_le h1
    have : y = φ (φ.symm y) := by simp
    rw [this]
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro w'
    apply φ.symm.injective
    rw [map_mul, map_mul]
    simpa using h2 (φ.symm w')
  have hrange : ψ.range = c.d.ψ.range := by
    rw [hψdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr φ.symm.surjective,
      ← MonoidHom.range_eq_map]
  have himg₂ : (rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4)).map ψ =
      locImg (conjClass3 K) z K₂ := by
    rw [← hR₂φ, Subgroup.map_map, hK₂R]
    congr 1
    ext r
    simp [hψdef]
  have himg₃ : rootSU2Two.map ψ = locImg (conjClass3 K) z K₃ := by
    rw [← hR₃φ, Subgroup.map_map, hK₃R]
    congr 1
    ext r
    simp [hψdef]
  obtain ⟨θ₀, hθ₀r, hθ₀τ⟩ :=
    Q3TPS.exists_chart3 c.hΩ.conjInvariant hNt (le_centralizingLayer hK₂) ht p2
  obtain ⟨θ₂, hθ₂r, hθ₂τ⟩ :=
    Q3TPS.exists_chart3 c.hΩ.conjInvariant hNt (le_centralizingLayer hK₃z) ht hpairNK₃
  obtain ⟨H₁, H₂, y, hy, -, hyR₀, hyR₂, hd1, hd2⟩ := hY1a ψ hker' τ hτ2 θ₀ θ₂
    (hθ₀r.trans himg₂.symm) (hθ₂r.trans himg₃.symm) hθ₀τ hθ₂τ
  have hact : ∀ {R : Subgroup (Su (GaloisField 3 (2 * 1)) 3 1 4)} {L : Subgroup G},
      R.map ψ = locImg (conjClass3 K) z L → (∀ b ∈ R, τ (ψ b) = ψ (y * b * y⁻¹)) →
        ∀ a ∈ locImg (conjClass3 K) z L, ψ y * a * (ψ y)⁻¹ = τ a := by
    intro R L hRL hyR a ha
    rw [← hRL] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    rw [hyR b hb, map_mul, map_mul, map_inv]
  obtain ⟨ŷ, hŷ, hmk, hŷw, hŷK, hŷT, hŷ₂, hŷ₃⟩ := hlift c t ht K₂ K₃ T w hK₂ hK₃z hTz hTQ hw hwt
    (ψ y) ⟨φ.symm y, rfl⟩ (hact himg₂ hyR₀) (hact himg₃ hyR₂)
  have hyt : ŷ * t * ŷ⁻¹ = t := hpar ŷ hŷ hŷw hŷK hŷT hŷ₂ hŷ₃
  have hfixy : τ (ψ y) = ψ y := by
    rw [← hmk]
    exact locAut_locMk_of_commute c.hΩ.conjInvariant ht hŷ hyt
  have hstabτ : ∀ x, τ (ψ x) ∈ ψ.range := by
    intro x
    rw [hrange]
    exact hstab c t ht ht2 (conjSub_eq_of_stdPair3 hNt p1) (φ.symm x)
  exact ⟨φ, hfund, hY1b ψ hker' τ hτ2 hstabτ H₁ H₂ y hy hyR₀ hyR₂ hd1 hd2 hfixy⟩

end CFSG.ClassicalInvolution.Q3.Q3P21
