module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleMinus
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.RouteD.TWU

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.WeakCT

set_option linter.unusedSectionVars false

section Generic

theorem conj_eq_of_split {G : Type} [Group G] {s u₂ x l : G} (hs : s = u₂ * x)
    (hux : u₂ * x = x * u₂) (hul : u₂ * l = l * u₂) : s * l * s⁻¹ = x * l * x⁻¹ := by
  rw [hs, hux]
  calc x * u₂ * l * (x * u₂)⁻¹ = x * (u₂ * l * u₂⁻¹) * x⁻¹ := by group
    _ = x * l * x⁻¹ := by rw [mul_inv_eq_iff_eq_mul.mpr hul]

theorem spinAction_conj_apply {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (ĉ y : spinGroup Q) (v : V) :
    spinAction Q (ĉ * y * ĉ⁻¹) (spinAction Q ĉ v) = spinAction Q ĉ (spinAction Q y v) := by
  rw [map_mul, map_mul, map_inv]
  have h : (spinAction Q ĉ)⁻¹ (spinAction Q ĉ v) = v := LinearEquiv.symm_apply_apply _ v
  show (spinAction Q ĉ) ((spinAction Q y) ((spinAction Q ĉ)⁻¹ (spinAction Q ĉ v))) = _
  rw [h]

end Generic

section Group

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}



theorem locImg_twin_le_Q₁ (c : TCtx p f .POmegaMinus 4 Ω K z) {T : Subgroup G}
    (hTz : T ∈ centralizingMembers Ω {z}) (hzT : IsClassicalMember p f T z) (hTK : T ≠ K) :
    locImg Ω z T ≤ c.d.Q₁ := by
  have hmem : locImg Ω z T ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨T, hTz, rfl⟩
  rcases c.d.fam_cases _ hmem with h | h | ⟨R, hR, hTR⟩
  · exact absurd (c.eq_of_locImg_le_Q₀ hTz h) hTK
  · exact h
  · exact (not_locImg_eq_map_fund c.hY hTz hzT c.d.ψ c.d.ker_le hR hTR).elim

theorem locAut_eq_conj_td4 (c : TCtx p f .POmegaMinus 4 Ω K z) {s x : G}
    (htz : s * z * s⁻¹ = z) (hxY : x ∈ locLayer Ω z)
    {ĉ : (modelUniv .POmegaMinus 4 p f Fact.out).K} (hĉ : c.d.ψ ĉ = locElt Ω z x hxY)
    (hconjL : ∀ L ∈ centralizingMembers Ω {z}, L ≠ K → ¬ locImg Ω z L ≤ c.d.Q₁ →
      ∀ l ∈ L, s * l * s⁻¹ = x * l * x⁻¹) :
    ∀ y, c.d.ψ (ĉ * y * ĉ⁻¹) = locAut c.hΩ.conjInvariant htz (c.d.ψ y) := by
  classical
  have hadm : StatedLieAdmissible .POmegaMinus 4 p f :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.mpr c.hf, by show 4 ≤ 4; omega⟩
  let E : Subgroup (locQuot Ω z) := MonoidHom.eqLocus
    (locAut c.hΩ.conjInvariant htz).toMonoidHom (MulAut.conj (c.d.ψ ĉ)).toMonoidHom
  have hE : ∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 p f Fact.out).D,
      R.map c.d.ψ ≤ E := by
    intro R hR
    obtain ⟨L, hL, hLK, hLQ, hLR⟩ := c.exists_member_of_fund hR
    rw [← hLR]
    rintro _ ⟨l', hl', rfl⟩
    have hlay : layerAut c.hΩ.conjInvariant htz l' =
        (⟨x, hxY⟩ : ↥(locLayer Ω z)) * l' * (⟨x, hxY⟩ : ↥(locLayer Ω z))⁻¹ := by
      apply Subtype.ext
      rw [coe_layerAut]
      exact hconjL L hL hLK hLQ l' (Subgroup.mem_subgroupOf.mp hl')
    show locMk Ω z (layerAut c.hΩ.conjInvariant htz l') = c.d.ψ ĉ * locMk Ω z l' * (c.d.ψ ĉ)⁻¹
    rw [hlay, hĉ, map_mul, map_mul, map_inv]
    rfl
  have hrange := Exotic.range_le_iSup_fund_minus (by omega) hadm c.hY.std c.d.ψ
  intro y
  have hy : c.d.ψ y ∈ E := (iSup₂_le hE) (hrange ⟨y, rfl⟩)
  have hyeq : locAut c.hΩ.conjInvariant htz (c.d.ψ y) = c.d.ψ ĉ * c.d.ψ y * (c.d.ψ ĉ)⁻¹ := hy
  rw [map_mul, map_mul, map_inv]
  exact hyeq.symm

end Group

end CFSG.ClassicalInvolution.RouteD.TWU
