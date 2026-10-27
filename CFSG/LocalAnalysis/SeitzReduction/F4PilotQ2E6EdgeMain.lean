module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6EdgeFrame
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6EdgeRigid
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6RelayMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapUOOmegaParam

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule TauCeti.GLSymplecticFin
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open CFSG.SeitzReduction.SymplecticPilot (q2OmMIota)
open CFSG.LieType.Universal.Symplectic.SpExtras (elt)
open CFSG.LieType.Steinberg.TwistedE6 (sigma)
open CFSG.Assembly.LowTwoRank (StatedSp StatedOmega StatedQuadMinus)
open CFSG.LieType.Ree (ReeTag)
open scoped MatrixGroups

local instance f4PilotQ2E6EdgeMainNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotQ2E6EdgeMainNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section YParam

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {X₀ : Subgroup (adjointGroup .F4 K)}

theorem trans_graphAutF4_symm_symm_apply (e : L ≃* adjointGroup .F4 K) (m : adjointGroup .F4 K) :
    (e.trans (graphAutF4 K).symm).symm m = e.symm (graphAutF4 K m) := by
  rw [MulEquiv.symm_trans_apply, MulEquiv.symm_symm]

variable (e : L ≃* adjointGroup .F4 K) (g : adjointGroup .F4 K)

@[expose] noncomputable def edgeYParam
    (Φ₁ : StatedOmega (StatedQuadMinus (3 + 1) K 1 1) ≃*
      centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)) :
    StatedOmega (StatedQuadMinus (3 + 1) K 1 1) →* G :=
  (MulAut.conj ((e.symm g : L) : G)).toMonoidHom.comp
    ((centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)).subtype.comp
      Φ₁.toMonoidHom)

variable {e g}

theorem edgeYParam_apply
    (Φ₁ : StatedOmega (StatedQuadMinus (3 + 1) K 1 1) ≃*
      centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀))
    (y : StatedOmega (StatedQuadMinus (3 + 1) K 1 1)) :
    edgeYParam e g Φ₁ y = ((e.symm g : L) : G) * (Φ₁ y : G) * ((e.symm g : L) : G)⁻¹ :=
  rfl

theorem edgeYParam_injective
    (Φ₁ : StatedOmega (StatedQuadMinus (3 + 1) K 1 1) ≃*
      centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)) :
    Function.Injective (edgeYParam e g Φ₁) :=
  (MulAut.conj _).injective.comp (Subtype.val_injective.comp Φ₁.injective)

theorem edgeYParam_iota {ι : StatedSp 3 K →* StatedOmega (StatedQuadMinus (3 + 1) K 1 1)}
    {Φ₁ : StatedOmega (StatedQuadMinus (3 + 1) K 1 1) ≃*
      centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)}
    (hΦ₁ : IsTwoGraphParam (e.trans (graphAutF4 K).symm) X₀ ι Φ₁) (s : StatedSp 3 K) :
    edgeYParam e g Φ₁ (ι s) =
      ((e.symm (g * graphAutF4 K (c3LeviHom K s) * g⁻¹) : L) : G) := by
  rw [edgeYParam_apply, hΦ₁ s, trans_graphAutF4_symm_symm_apply, map_mul, map_mul, map_inv,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]

theorem commute_edgeYParam
    (Φ₁ : StatedOmega (StatedQuadMinus (3 + 1) K 1 1) ≃*
      centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀))
    (y : StatedOmega (StatedQuadMinus (3 + 1) K 1 1)) {z : adjointGroup .F4 K} (hz : z ∈ X₀) :
    Commute (edgeYParam e g Φ₁ y) ((e.symm (g * graphAutF4 K z * g⁻¹) : L) : G) := by
  have hc : Commute ((Φ₁ y : centralizerPerfectCore _) : G)
      (((e.trans (graphAutF4 K).symm).symm z : L) : G) := by
    have h := centralizerPerfectCore_le_centralizer _ (Φ₁ y).2
    exact (mem_centralizer_iff.1 h _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩).symm
  rw [trans_graphAutF4_symm_symm_apply] at hc
  rw [edgeYParam_apply, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv]
  exact (Commute.conj_iff _).2 hc

end YParam

section Alpha

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {X₀ : Subgroup (adjointGroup .F4 K)} {I : Finset (Fin 6)}

@[expose] noncomputable def edgeAlpha (σ : Fin 4 ≃ I) (e : L ≃* adjointGroup .F4 K)
    (g : adjointGroup .F4 K)
    (Φ₁ : StatedOmega (StatedQuadMinus (3 + 1) K 1 1) ≃*
      centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)) :
    blockSpecialLinear (K := K) I →* G :=
  (edgeYParam e g Φ₁).comp ((edgeMuOm K).comp (blockSL4Equiv K σ).toMonoidHom)

variable {σ : Fin 4 ≃ I} {e : L ≃* adjointGroup .F4 K} {g : adjointGroup .F4 K}
  {Φ₁ : StatedOmega (StatedQuadMinus (3 + 1) K 1 1) ≃*
    centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)}

theorem edgeAlpha_apply (x : blockSpecialLinear (K := K) I) :
    edgeAlpha σ e g Φ₁ x = edgeYParam e g Φ₁ (edgeMuOm K (blockSL4Equiv K σ x)) :=
  rfl

theorem edgeAlpha_injective (hK : Nat.card K = 2) : Function.Injective (edgeAlpha σ e g Φ₁) :=
  (edgeYParam_injective Φ₁).comp ((edgeMuOm_injective hK).comp (blockSL4Equiv K σ).injective)

theorem commutator_range_edgeAlpha :
    ⁅(edgeAlpha σ e g Φ₁).range, (edgeAlpha σ e g Φ₁).range⁆ = (edgeAlpha σ e g Φ₁).range := by
  have hP : Group.IsPerfect (SpecialLinearGroup (Fin 4) K) :=
    LinearPilot.isPerfect_specialLinearGroup_of_three_le_card (Fin 4) (by simp)
  have hperf : ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 4) K)), ⊤⁆ = ⊤ := hP.commutator_eq_top
  have hrange : (edgeAlpha σ e g Φ₁).range = ((edgeYParam e g Φ₁).comp (edgeMuOm K)).range := by
    rw [edgeAlpha, ← MonoidHom.comp_assoc, MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 (blockSL4Equiv K σ).surjective, ← MonoidHom.range_eq_map]
  rw [hrange, MonoidHom.range_eq_map, ← Subgroup.map_commutator, hperf]

theorem subgroupToG_zpowers (e : L ≃* adjointGroup .F4 K) (z : adjointGroup .F4 K) :
    subgroupToG e (zpowers z) = zpowers ((e.symm z : L) : G) := by
  rw [subgroupToG, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

theorem edge_mem_centralizer_zpowers_of_commute {x w : G} (h : Commute x w) :
    x ∈ centralizer (zpowers w : Set G) := by
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  exact ((h.zpow_right k).eq).symm

theorem range_edgeAlpha_le (hK : Nat.card K = 2) {hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0}
    (hΦ₁ : IsTwoGraphParam (e.trans (graphAutF4 K).symm) X₀ (q2OmMIota le_rfl hirr hK) Φ₁)
    {β : Fin (Tag.rank .F4) → ℤ} (hX₀ : X₀ = zpowers (chainZ K rootR))
    (hg0 : g * graphAutF4 K (chainZ K rootR) * g⁻¹ = chainZ K rootR * chainZ K β)
    (hgc : g * graphAutF4 K (c3LeviHom K (spL0 K * spN0 K)) * g⁻¹ =
      chainZ K rootR * (chainZ K β)⁻¹)
    (hzc : chainZ K rootR * chainZ K β = chainZ K β * chainZ K rootR)
    (hzo : chainZ K rootR ^ 3 = 1) :
    (edgeAlpha σ e g Φ₁).range ≤
      centralizerPerfectCore (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β))) := by
  set zr := chainZ K rootR with hzr
  set zb := chainZ K β with hzb
  have hzr2 : zr = (zr * zb * (zr * zb⁻¹)) ^ 2 := by
    have h1 : zr * zb * (zr * zb⁻¹) = zr ^ 2 :=
      calc zr * zb * (zr * zb⁻¹) = zr * (zb * zr) * zb⁻¹ := by group
        _ = zr * (zr * zb) * zb⁻¹ := by rw [hzc]
        _ = zr ^ 2 := by rw [mul_assoc, mul_inv_cancel_right, sq]
    rw [h1, ← pow_mul]
    calc zr = zr ^ 3 * zr := by rw [hzo, one_mul]
      _ = zr ^ (2 * 2) := by group
  have hzb2 : zb = zr⁻¹ * (zr * zb) := by group
  have hgen : ∀ y : StatedOmega (StatedQuadMinus (3 + 1) K 1 1),
      Commute (edgeYParam e g Φ₁ y) ((e.symm (zr * zb) : L) : G) →
      Commute (edgeYParam e g Φ₁ y) ((e.symm (zr * zb⁻¹) : L) : G) →
        Commute (edgeYParam e g Φ₁ y) ((e.symm zr : L) : G) ∧
          Commute (edgeYParam e g Φ₁ y) ((e.symm zb : L) : G) := by
    intro y h1 h2
    have hr : Commute (edgeYParam e g Φ₁ y) ((e.symm zr : L) : G) := by
      rw [hzr2, map_pow, map_mul, Subgroup.coe_pow, Subgroup.coe_mul]
      exact (h1.mul_right h2).pow_right 2
    refine ⟨hr, ?_⟩
    rw [hzb2, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hr.inv_right.mul_right h1
  have hall : ∀ x : blockSpecialLinear (K := K) I,
      Commute (edgeAlpha σ e g Φ₁ x) ((e.symm zr : L) : G) ∧
        Commute (edgeAlpha σ e g Φ₁ x) ((e.symm zb : L) : G) := by
    intro x
    set y := edgeMuOm K (blockSL4Equiv K σ x) with hy
    have c1 : Commute (edgeYParam e g Φ₁ y) ((e.symm (zr * zb) : L) : G) := by
      have h := commute_edgeYParam (g := g) Φ₁ y (z := zr) (by rw [hX₀]; exact mem_zpowers _)
      rwa [hg0] at h
    have c2 : Commute (edgeYParam e g Φ₁ y) ((e.symm (zr * zb⁻¹) : L) : G) := by
      have h := edgeYParam_iota (g := g) hΦ₁ (spL0 K * spN0 K)
      rw [hgc] at h
      rw [← h]
      exact ((commute_q2OmMIota_cPrime_edgeMuOm hK hirr _).map (edgeYParam e g Φ₁)).symm
    exact hgen y c1 c2
  refine le_centralizerPerfectCore_sup commutator_range_edgeAlpha ?_ ?_
  · rintro _ ⟨x, rfl⟩
    have hX : subgroupToG e X₀ = zpowers ((e.symm zr : L) : G) := by
      rw [← subgroupToG_zpowers, ← hX₀]
    rw [hX]
    exact edge_mem_centralizer_zpowers_of_commute (hall x).1
  · rintro _ ⟨x, rfl⟩
    rw [subgroupToG_zpowers]
    exact edge_mem_centralizer_zpowers_of_commute (hall x).2

theorem edgeAlpha_transvection (hK : Nat.card K = 2) {hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0}
    (hΦ₁ : IsTwoGraphParam (e.trans (graphAutF4 K).symm) X₀ (q2OmMIota le_rfl hirr hK) Φ₁)
    {i j : Fin 6} (hij : i ≠ j)
    (hmem : SpecialLinearGroup.transvection hij (1 : K) ∈ blockSpecialLinear I)
    {p q : Fin 4} (hpq : p ≠ q) (hp : ((σ p : I) : Fin 6) = i) (hq : ((σ q : I) : Fin 6) = j)
    {r : RootSubgroupIndex 3}
    (hι : q2OmMIota le_rfl hirr hK (elt r 1) = edgeMuOm K (SpecialLinearGroup.transvection hpq 1))
    {m : adjointGroup .F4 K} (hg : g * graphAutF4 K (c3LeviHom K (elt r 1)) * g⁻¹ = m) :
    edgeAlpha σ e g Φ₁ ⟨_, hmem⟩ = ((e.symm m : L) : G) := by
  rw [edgeAlpha_apply, blockSL4Equiv_transvection' σ hij 1 hmem hpq hp hq, ← hι,
    edgeYParam_iota hΦ₁, hg]

theorem transvection_zero_eq_one {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    SpecialLinearGroup.transvection hab (0 : K) = 1 := by
  apply Subtype.ext
  simp

theorem commute_edgeAlpha_of_relay (hK : Nat.card K = 2) {hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0}
    (hΦ₁ : IsTwoGraphParam (e.trans (graphAutF4 K).symm) X₀ (q2OmMIota le_rfl hirr hK) Φ₁)
    {s : StatedSp 3 K} {v : adjointGroup .F4 K}
    (hgv : g * graphAutF4 K (c3LeviHom K s) * g⁻¹ = v) {a b : Fin 6} (hab : a ≠ b)
    (ha : a ∈ I) (hb : b ∈ I) {p q : Fin 4} (hpq : p ≠ q) (hp : ((σ p : I) : Fin 6) = a)
    (hq : ((σ q : I) : Fin 6) = b)
    (h1 : Commute (q2OmMIota le_rfl hirr hK s) (edgeMuOm K (SpecialLinearGroup.transvection hpq 1)))
    (h2 : Commute (q2OmMIota le_rfl hirr hK s)
      (edgeMuOm K (SpecialLinearGroup.transvection hpq.symm 1)))
    (x : blockSpecialLinear (K := K) I)
    (hx : (x : SpecialLinearGroup (Fin 6) K) ∈ blockSpecialLinear ({a, b} : Finset (Fin 6))) :
    Commute ((e.symm v : L) : G) (edgeAlpha σ e g Φ₁ x) := by
  have hv : ((e.symm v : L) : G) = edgeYParam e g Φ₁ (q2OmMIota le_rfl hirr hK s) := by
    rw [edgeYParam_iota hΦ₁, hgv]
  set H : Subgroup (blockSpecialLinear (K := K) I) :=
    (centralizer ({((e.symm v : L) : G)} : Set G)).comap (edgeAlpha σ e g Φ₁) with hH
  have hgen : ∀ (c : K) (hc : SpecialLinearGroup.transvection hab c ∈ blockSpecialLinear I),
      (⟨_, hc⟩ : blockSpecialLinear (K := K) I) ∈ H := by
    intro c hc
    rcases SymplecticPilot.eq_zero_or_eq_one_of_natCard_two hK c with rfl | rfl
    · have h0 : (⟨_, hc⟩ : blockSpecialLinear (K := K) I) = 1 :=
        Subtype.ext (transvection_zero_eq_one hab)
      rw [h0]
      exact H.one_mem
    · rw [hH, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
        edgeAlpha_apply, blockSL4Equiv_transvection' σ hab 1 hc hpq hp hq, hv]
      exact ((h1.map (edgeYParam e g Φ₁)).eq).symm
  have hgen' : ∀ (c : K) (hc : SpecialLinearGroup.transvection hab.symm c ∈ blockSpecialLinear I),
      (⟨_, hc⟩ : blockSpecialLinear (K := K) I) ∈ H := by
    intro c hc
    rcases SymplecticPilot.eq_zero_or_eq_one_of_natCard_two hK c with rfl | rfl
    · have h0 : (⟨_, hc⟩ : blockSpecialLinear (K := K) I) = 1 :=
        Subtype.ext (transvection_zero_eq_one hab.symm)
      rw [h0]
      exact H.one_mem
    · rw [hH, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
        edgeAlpha_apply, blockSL4Equiv_transvection' σ hab.symm 1 hc hpq.symm hq hp, hv]
      exact ((h2.map (edgeYParam e g Φ₁)).eq).symm
  have key : blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6)) ≤
      H.map (blockSpecialLinear (K := K) I).subtype := by
    refine (blockSpecialLinear_pair_le_closure hab).trans ((closure_le _).2 ?_)
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨_, hgen c (LinearPilot.transvection_mem_blockSpecialLinear hab ha hb c), rfl⟩
    · exact ⟨_, hgen' c (LinearPilot.transvection_mem_blockSpecialLinear hab.symm hb ha c), rfl⟩
  obtain ⟨y, hy, hyx⟩ := key hx
  have hyx' : y = x := Subtype.ext hyx
  rw [← hyx']
  have h := Subgroup.mem_comap.1 hy
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  exact h.symm

end Alpha

section Overlaps

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] in
theorem chainZ_inv_charTwo (γ : Fin (Tag.rank .F4) → ℤ) :
    (chainZ K γ)⁻¹ = Adjoint.f4Par K (-γ) 1 * Adjoint.f4Par K γ 1 := by
  rw [chainZ, _root_.mul_inv_rev, Adjoint.xPar_neg, Adjoint.xPar_neg, CharTwo.neg_eq (1 : K)]

@[expose] noncomputable def edgeSigma1 : Fin 4 ≃ (({2, 5} : Finset (Fin 6))ᶜ : Finset (Fin 6)) :=
  Equiv.ofBijective (fun k => ⟨![0, 1, 3, 4] k, by fin_cases k <;> decide⟩) (by decide)

@[expose] noncomputable def edgeSigma3 : Fin 4 ≃ (({0, 3} : Finset (Fin 6))ᶜ : Finset (Fin 6)) :=
  Equiv.ofBijective (fun k => ⟨![1, 2, 4, 5] k, by fin_cases k <;> decide⟩) (by decide)

variable {e : L ≃* adjointGroup .F4 K} {ΦA : e6ScLevi K e6A5Nodes →* G}

theorem chainSL6_transvection_one_four (hn : IsLeviNormalizedA e ΦA) :
    chainSL6 ΦA (SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 4 by decide) 1) =
      ((e.symm (Adjoint.f4Par K v0120 1) : L) : G) := by
  rw [← relaySp6ToSL6_x_root021, chainSL6_sp6ToSL6_x hn]
  rfl

theorem chainSL6_transvection_four_one (hn : IsLeviNormalizedA e ΦA) :
    chainSL6 ΦA (SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 1 by decide) 1) =
      ((e.symm (Adjoint.f4Par K (-v0120) 1) : L) : G) := by
  rw [← relaySp6ToSL6_x_neg_root021, chainSL6_sp6ToSL6_x hn, map_neg]
  rfl

theorem edgeInput_one (hK : Nat.card K = 2) {t : G} (hw : F4Work L K t 1)
    {X₀ : Subgroup (adjointGroup .F4 K)} (hX₀ : X₀ = zpowers (chainZ K rootR))
    (hr : ΦA.range = centralizerPerfectCore (subgroupToG e X₀))
    (hker : ΦA.ker ≤ center (e6ScLevi K e6A5Nodes))
    (hconj : ∀ x y : e6ScLevi K e6A5Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y)
    (hn : IsLeviNormalizedA e ΦA) {hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0}
    {Φ₁ : StatedOmega (StatedQuadMinus (3 + 1) K 1 1) ≃*
      centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)}
    (hΦ₁ : IsTwoGraphParam (e.trans (graphAutF4 K).symm) X₀ (q2OmMIota le_rfl hirr hK) Φ₁) :
    ∃ α' : blockSpecialLinear (K := K) ({2, 5} : Finset (Fin 6))ᶜ →* G,
      Function.Injective α' ∧
      α'.range ≤ centralizerPerfectCore
        (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K (Pi.single 1 1)))) ∧
      (∀ x : blockSpecialLinear (K := K) ({2, 5} : Finset (Fin 6))ᶜ,
        chainSL6 ΦA x ∈ L → α' x = chainSL6 ΦA x) ∧
      ∀ x : blockSpecialLinear (K := K) ({2, 5} : Finset (Fin 6))ᶜ,
        (x : SpecialLinearGroup (Fin 6) K) ∈ blockSpecialLinear ({0, 1} : Finset (Fin 6)) →
          Commute ((e.symm (relayAlign K root1242) : L) : G) (α' x) ∧
            Commute ((e.symm (relayAlign' K root1242) : L) : G) (α' x) := by
  have hinj := chainSL6_injective hK hker
  have hrange := range_edgeAlpha_le (σ := edgeSigma1) (g := edgeH1 K * wRep K [3, 2])
    (Φ₁ := Φ₁) hK hΦ₁ hX₀ (frame1_chainZ_rootR hK)
    ((frame1_cPrime hK).trans (by rw [chainZ_inv_charTwo])) (chainZ_rootR_comm_a2 hK)
    (by rw [← orderOf_chainZ_rootR hK]; exact pow_orderOf_eq_one _)
  refine ⟨edgeAlpha edgeSigma1 e (edgeH1 K * wRep K [3, 2]) Φ₁, edgeAlpha_injective hK, hrange,
    ?_, ?_⟩
  · have hL1 : chainSL6 ΦA (SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 3 by decide) 1) ∈
        L := by
      rw [← sp6ToSL6_x_root221]
      exact relay_chainSL6_sp6ToSL6_mem hn _
    have hL2 : chainSL6 ΦA (SpecialLinearGroup.transvection (show (3 : Fin 6) ≠ 0 by decide) 1) ∈
        L := by
      rw [← sp6ToSL6_x_neg_root221]
      exact relay_chainSL6_sp6ToSL6_mem hn _
    have hL3 : chainSL6 ΦA (SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 4 by decide) 1) ∈
        L := by
      rw [← relaySp6ToSL6_x_root021]
      exact relay_chainSL6_sp6ToSL6_mem hn _
    have hL4 : chainSL6 ΦA (SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 1 by decide) 1) ∈
        L := by
      rw [← relaySp6ToSL6_x_neg_root021]
      exact relay_chainSL6_sp6ToSL6_mem hn _
    have htm : ∃ x ∈ blockSpecialLinear (K := K) ({2, 5} : Finset (Fin 6))ᶜ,
        t * chainSL6 ΦA x * t⁻¹ ≠ chainSL6 ΦA x := by
      refine ⟨_, LinearPilot.transvection_mem_blockSpecialLinear
        (show (0 : Fin 6) ≠ 1 by decide) (by decide) (by decide) (1 : K), ?_⟩
      rw [relay_conj_chainSL6_transvection hconj (show (0 : Fin 6) ≠ 1 by decide)
        (show (4 : Fin 6) ≠ 3 by decide) a5Root_graphSwapPerm_zero_one.1
        relay_a5Root_rho_check.1 1]
      exact fun h => relay_transvection_four_three_ne (hinj h)
    have h1 := edgeAlpha_transvection (σ := edgeSigma1) (g := edgeH1 K * wRep K [3, 2]) hK hΦ₁
      (show (0 : Fin 6) ≠ 3 by decide)
      (LinearPilot.transvection_mem_blockSpecialLinear _ (by decide) (by decide) 1)
      (show (0 : Fin 4) ≠ 2 by decide) rfl rfl (q2OmMIota_P12 hK hirr) (frame1_P12 hK)
    have h2 := edgeAlpha_transvection (σ := edgeSigma1) (g := edgeH1 K * wRep K [3, 2]) hK hΦ₁
      (show (3 : Fin 6) ≠ 0 by decide)
      (LinearPilot.transvection_mem_blockSpecialLinear _ (by decide) (by decide) 1)
      (show (2 : Fin 4) ≠ 0 by decide) rfl rfl (q2OmMIota_M12 hK hirr) (frame1_M12 hK)
    have h3 := edgeAlpha_transvection (σ := edgeSigma1) (g := edgeH1 K * wRep K [3, 2]) hK hΦ₁
      (show (1 : Fin 6) ≠ 4 by decide)
      (LinearPilot.transvection_mem_blockSpecialLinear _ (by decide) (by decide) 1)
      (show (1 : Fin 4) ≠ 3 by decide) rfl rfl (q2OmMIota_D12 hK hirr) (frame1_D12 hK)
    have h4 := edgeAlpha_transvection (σ := edgeSigma1) (g := edgeH1 K * wRep K [3, 2]) hK hΦ₁
      (show (4 : Fin 6) ≠ 1 by decide)
      (LinearPilot.transvection_mem_blockSpecialLinear _ (by decide) (by decide) 1)
      (show (3 : Fin 4) ≠ 1 by decide) rfl rfl (q2OmMIota_D21 hK hirr) (frame1_D21 hK)
    rw [← chainSL6_transvection_zero_three hn] at h1
    rw [← chainSL6_transvection_three_zero hn] at h2
    rw [← chainSL6_transvection_one_four hn] at h3
    rw [← chainSL6_transvection_four_one hn] at h4
    have hrig := edge_eq_or_eq_conj hK hw.mem_centralizer hr hinj (show (2 : Fin 6) ≠ 5 by decide)
      (isRoot_single _ 1) (chainSL6_transvection_two_five hn) (chainSL6_transvection_five_two hn)
      (show (0 : Fin 6) ≠ 3 by decide) (show (1 : Fin 6) ≠ 4 by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hL1 hL2 hL3 hL4 htm (edgeAlpha_injective hK) hrange
      h1 h2 h3 h4
    intro x hx
    rcases hrig with h | h
    · exact h x
    · rw [h x, ← mem_centralizer_iff.1 hw.mem_centralizer _ hx, mul_inv_cancel_right]
  · intro x hx
    exact ⟨commute_edgeAlpha_of_relay hK hΦ₁ (frame1_relay hK) (show (0 : Fin 6) ≠ 1 by decide)
        (by decide) (by decide) (show (0 : Fin 4) ≠ 1 by decide) rfl rfl
        (commute_q2OmMIota_relay_t01 hK hirr) (commute_q2OmMIota_relay_t10 hK hirr) x hx,
      commute_edgeAlpha_of_relay hK hΦ₁ (frame1_relay' hK) (show (0 : Fin 6) ≠ 1 by decide)
        (by decide) (by decide) (show (0 : Fin 4) ≠ 1 by decide) rfl rfl
        (commute_q2OmMIota_relay'_t01 hK hirr) (commute_q2OmMIota_relay'_t10 hK hirr) x hx⟩

theorem edgeInput_three (hK : Nat.card K = 2) {t : G} (hw : F4Work L K t 1)
    {X₀ : Subgroup (adjointGroup .F4 K)} (hX₀ : X₀ = zpowers (chainZ K rootR))
    (hr : ΦA.range = centralizerPerfectCore (subgroupToG e X₀))
    (hker : ΦA.ker ≤ center (e6ScLevi K e6A5Nodes))
    (hconj : ∀ x y : e6ScLevi K e6A5Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y)
    (hn : IsLeviNormalizedA e ΦA) {hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0}
    {Φ₁ : StatedOmega (StatedQuadMinus (3 + 1) K 1 1) ≃*
      centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)}
    (hΦ₁ : IsTwoGraphParam (e.trans (graphAutF4 K).symm) X₀ (q2OmMIota le_rfl hirr hK) Φ₁) :
    ∃ α' : blockSpecialLinear (K := K) ({0, 3} : Finset (Fin 6))ᶜ →* G,
      Function.Injective α' ∧
      α'.range ≤ centralizerPerfectCore
        (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K rootE1mE2Align))) ∧
      (∀ x : blockSpecialLinear (K := K) ({0, 3} : Finset (Fin 6))ᶜ,
        chainSL6 ΦA x ∈ L → α' x = chainSL6 ΦA x) ∧
      ∀ x : blockSpecialLinear (K := K) ({0, 3} : Finset (Fin 6))ᶜ,
        (x : SpecialLinearGroup (Fin 6) K) ∈ blockSpecialLinear ({1, 2} : Finset (Fin 6)) →
          Commute ((e.symm (relayAlign K rootE2pE3Align) : L) : G) (α' x) ∧
            Commute ((e.symm (relayAlign' K rootE2pE3Align) : L) : G) (α' x) := by
  have hinj := chainSL6_injective hK hker
  have hrange := range_edgeAlpha_le (σ := edgeSigma3) (g := edgeH3 K * wRep K [])
    (Φ₁ := Φ₁) hK hΦ₁ hX₀ (frame3_chainZ_rootR hK)
    ((frame3_cPrime hK).trans (by rw [chainZ_inv_charTwo])) (chainZ_rootR_comm_e1e2 hK)
    (by rw [← orderOf_chainZ_rootR hK]; exact pow_orderOf_eq_one _)
  refine ⟨edgeAlpha edgeSigma3 e (edgeH3 K * wRep K []) Φ₁, edgeAlpha_injective hK, hrange,
    ?_, ?_⟩
  · have hL1 : chainSL6 ΦA (SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 4 by decide) 1) ∈
        L := by
      rw [← relaySp6ToSL6_x_root021]
      exact relay_chainSL6_sp6ToSL6_mem hn _
    have hL2 : chainSL6 ΦA (SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 1 by decide) 1) ∈
        L := by
      rw [← relaySp6ToSL6_x_neg_root021]
      exact relay_chainSL6_sp6ToSL6_mem hn _
    have hL3 : chainSL6 ΦA (SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 5 by decide) 1) ∈
        L := by
      rw [← sp6ToSL6_x_single_two]
      exact relay_chainSL6_sp6ToSL6_mem hn _
    have hL4 : chainSL6 ΦA (SpecialLinearGroup.transvection (show (5 : Fin 6) ≠ 2 by decide) 1) ∈
        L := by
      rw [← sp6ToSL6_x_neg_single_two]
      exact relay_chainSL6_sp6ToSL6_mem hn _
    have htm : ∃ x ∈ blockSpecialLinear (K := K) ({0, 3} : Finset (Fin 6))ᶜ,
        t * chainSL6 ΦA x * t⁻¹ ≠ chainSL6 ΦA x := by
      refine ⟨_, LinearPilot.transvection_mem_blockSpecialLinear
        (show (1 : Fin 6) ≠ 2 by decide) (by decide) (by decide) (1 : K), ?_⟩
      rw [relay_conj_chainSL6_transvection hconj (show (1 : Fin 6) ≠ 2 by decide)
        (show (5 : Fin 6) ≠ 4 by decide) a5Root_graphSwapPerm_check.2.2.1
        relay_a5Root_rho_check.2 1]
      exact fun h => relay_transvection_five_four_ne (hinj h)
    have h1 := edgeAlpha_transvection (σ := edgeSigma3) (g := edgeH3 K * wRep K []) hK hΦ₁
      (show (1 : Fin 6) ≠ 4 by decide)
      (LinearPilot.transvection_mem_blockSpecialLinear _ (by decide) (by decide) 1)
      (show (0 : Fin 4) ≠ 2 by decide) rfl rfl (q2OmMIota_P12 hK hirr) (frame3_P12 hK)
    have h2 := edgeAlpha_transvection (σ := edgeSigma3) (g := edgeH3 K * wRep K []) hK hΦ₁
      (show (4 : Fin 6) ≠ 1 by decide)
      (LinearPilot.transvection_mem_blockSpecialLinear _ (by decide) (by decide) 1)
      (show (2 : Fin 4) ≠ 0 by decide) rfl rfl (q2OmMIota_M12 hK hirr) (frame3_M12 hK)
    have h3 := edgeAlpha_transvection (σ := edgeSigma3) (g := edgeH3 K * wRep K []) hK hΦ₁
      (show (2 : Fin 6) ≠ 5 by decide)
      (LinearPilot.transvection_mem_blockSpecialLinear _ (by decide) (by decide) 1)
      (show (1 : Fin 4) ≠ 3 by decide) rfl rfl (q2OmMIota_D12 hK hirr) (frame3_D12 hK)
    have h4 := edgeAlpha_transvection (σ := edgeSigma3) (g := edgeH3 K * wRep K []) hK hΦ₁
      (show (5 : Fin 6) ≠ 2 by decide)
      (LinearPilot.transvection_mem_blockSpecialLinear _ (by decide) (by decide) 1)
      (show (3 : Fin 4) ≠ 1 by decide) rfl rfl (q2OmMIota_D21 hK hirr) (frame3_D21 hK)
    rw [← chainSL6_transvection_one_four hn] at h1
    rw [← chainSL6_transvection_four_one hn] at h2
    rw [← chainSL6_transvection_two_five hn] at h3
    rw [← chainSL6_transvection_five_two hn] at h4
    have hrig := edge_eq_or_eq_conj hK hw.mem_centralizer hr hinj (show (0 : Fin 6) ≠ 3 by decide)
      isRoot_rootE1mE2Align (chainSL6_transvection_zero_three hn)
      (chainSL6_transvection_three_zero hn) (show (1 : Fin 6) ≠ 4 by decide)
      (show (2 : Fin 6) ≠ 5 by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hL1 hL2 hL3 hL4 htm (edgeAlpha_injective hK) hrange h1 h2 h3 h4
    intro x hx
    rcases hrig with h | h
    · exact h x
    · rw [h x, ← mem_centralizer_iff.1 hw.mem_centralizer _ hx, mul_inv_cancel_right]
  · intro x hx
    exact ⟨commute_edgeAlpha_of_relay hK hΦ₁ (frame3_relay hK) (show (1 : Fin 6) ≠ 2 by decide)
        (by decide) (by decide) (show (0 : Fin 4) ≠ 1 by decide) rfl rfl
        (commute_q2OmMIota_relay_t01 hK hirr) (commute_q2OmMIota_relay_t10 hK hirr) x hx,
      commute_edgeAlpha_of_relay hK hΦ₁ (frame3_relay' hK) (show (1 : Fin 6) ≠ 2 by decide)
        (by decide) (by decide) (show (0 : Fin 4) ≠ 1 by decide) rfl rfl
        (commute_q2OmMIota_relay'_t01 hK hirr) (commute_q2OmMIota_relay'_t10 hK hirr) x hx⟩

end Overlaps

theorem eq_one_and_eq_one_of_irreducible_two {K : Type} [Field K] [CharP K 2]
    (hK : Nat.card K = 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b = 1 ∧ c = 1 := by
  have hc : c = 1 := by
    rcases SymplecticPilot.eq_zero_or_eq_one_of_natCard_two hK c with h | h
    · exact absurd (by rw [h]; ring) (hirr 0)
    · exact h
  refine ⟨?_, hc⟩
  rcases SymplecticPilot.eq_zero_or_eq_one_of_natCard_two hK b with h | h
  · exfalso
    apply hirr 1
    rw [h, hc]
    have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
    linear_combination h2
  · exact h

theorem twoE6RelayEdgeInput_holds : TwoE6RelayEdgeInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ' ΦA hr hker hconj hn
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hK : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  obtain ⟨b, c, hirr, Φ₁, hΦ₁⟩ := twoOmegaMinusParamInput_holds K hK X₀ hXJ hcyc hX₀ G L
    (e.trans (graphAutF4 K).symm) t hw hκ'
  obtain ⟨rfl, rfl⟩ := eq_one_and_eq_one_of_irreducible_two hK hirr
  have hXe : X₀ = zpowers (chainZ K rootR) :=
    eq_of_le_rootSL2 hK isRoot_rootR (le_rootSL2_rootR_of_le_highestRootRankOne hXJ)
      (zpowers_chainZ_le isRoot_rootR) hX₀ (by rw [Nat.card_zpowers, orderOf_chainZ_rootR hK])
  exact ⟨edgeInput_one hK hw hXe hr hker hconj hn hΦ₁,
    edgeInput_three hK hw hXe hr hker hconj hn hΦ₁⟩

end CFSG.SeitzReduction.F4Pilot
