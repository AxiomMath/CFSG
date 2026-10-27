module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightDichGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus plusIndexEquiv regular_coordinateQuadPlus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam AgreeOn FlipOn SwapPairExclusion)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Conj

variable {G : Type*} [Group G] {t : G}

theorem agreeOn_or_flipOn_of_conj {D D' : Subgroup G} (P : SwapParam t D)
    (P' : SwapParam t D') (hinj : Function.Injective P.Ψ) (hinj' : Function.Injective P'.Ψ)
    [IsSimpleGroup D'] (hZ : center D' = ⊥) {n : G}
    (hD' : D.map (MulAut.conj n).toMonoidHom = D')
    (hrange : P.Ψ.range.map (MulAut.conj n).toMonoidHom = P'.Ψ.range)
    {O : Subgroup G} (hOD : O ≤ D) (hOD' : O ≤ D') (hnO : ∀ x ∈ O, n * x * n⁻¹ = x)
    (hnP : ∀ x ∈ O, n * P.lft x * n⁻¹ = P.lft x) :
    AgreeOn P P' O ∨ FlipOn P P' O := by
  have hφmem : ∀ y : D', n⁻¹ * (y : G) * n ∈ D := by
    intro y
    have hy : (y : G) ∈ D.map (MulAut.conj n).toMonoidHom := hD' ▸ y.2
    obtain ⟨d, hd, hdy⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hdy
    rw [← hdy, show n⁻¹ * (n * d * n⁻¹) * n = d by group]
    exact hd
  let φ : D' →* D :=
    { toFun := fun y => ⟨n⁻¹ * y * n, hφmem y⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp only [Subgroup.coe_mul]; group }
  have hφ : ∀ y : D', (φ y : G) = n⁻¹ * y * n := fun y => rfl
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    rw [hφ, hφ] at h
    exact Subtype.ext (by simpa using h)
  have hφsurj : Function.Surjective φ := by
    intro d
    have hd : n * (d : G) * n⁻¹ ∈ D' := hD' ▸ ⟨d, d.2, rfl⟩
    exact ⟨⟨_, hd⟩, Subtype.ext (by rw [hφ]; group)⟩
  set Ψ₂ : D' × D' →* G :=
    (MulAut.conj n).toMonoidHom.comp (P.Ψ.comp (φ.prodMap φ)) with hΨ₂
  have hΨ₂a : ∀ x y : D', Ψ₂ (x, y) = n * P.Ψ (φ x, φ y) * n⁻¹ := fun x y => rfl
  have hΨ₂inj : Function.Injective Ψ₂ := by
    intro x y hxy
    rw [hΨ₂, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MonoidHom.comp_apply] at hxy
    have h1 := hinj ((MulAut.conj n).injective hxy)
    obtain ⟨x₁, x₂⟩ := x
    obtain ⟨y₁, y₂⟩ := y
    simp only [MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.comp_apply,
      MonoidHom.coe_fst, MonoidHom.coe_snd, Prod.mk.injEq] at h1
    exact Prod.ext (hφinj h1.1) (hφinj h1.2)
  have hsurj : Function.Surjective (φ.prodMap φ) := by
    rintro ⟨d₁, d₂⟩
    obtain ⟨y₁, rfl⟩ := hφsurj d₁
    obtain ⟨y₂, rfl⟩ := hφsurj d₂
    exact ⟨(y₁, y₂), rfl⟩
  have hr : Ψ₂.range = P'.Ψ.range := by
    rw [hΨ₂, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj,
      ← MonoidHom.range_eq_map, hrange]
  have hd : ∀ y : D', Ψ₂ (y, y) = P'.Ψ (y, y) := by
    intro y
    rw [hΨ₂a, P.diag, P'.diag, hφ]
    group
  have hZ' := SeitzQ2.eq_one_of_forall_mul_comm_of_center_eq_bot hZ
  have hkey : ∀ x (hx : x ∈ O), Ψ₂ (⟨x, hOD' hx⟩, 1) = P.lft x := by
    intro x hx
    have hφx : φ ⟨x, hOD' hx⟩ = ⟨x, hOD hx⟩ := by
      apply Subtype.ext
      rw [hφ]
      calc n⁻¹ * x * n = n⁻¹ * (n * x * n⁻¹) * n := by rw [hnO x hx]
        _ = x := by group
    rw [hΨ₂a, hφx, map_one, ← P.lft_of_mem (hOD hx), hnP x hx]
  rcases SeitzQ2.eq_or_eq_comp_prodComm_of_range_eq hZ' hinj' hΨ₂inj hr hd with h | h
  · left
    intro x hx
    rw [P'.lft_of_mem (hOD' hx), ← hkey x hx, h]
  · right
    intro x hx
    have h1 : P'.Ψ (1, ⟨x, hOD' hx⟩) = P.lft x := by
      rw [← hkey x hx, h]
      rfl
    rw [P'.lft_of_mem (hOD' hx), ← P'.swap, h1]

end Conj

section Swap

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem plusPairSwap_mem (a b : Fin 4) :
    pairSwap (coordinateQuadPlus 4 K) (plusIndexEquiv 4 (.inl a)) (plusIndexEquiv 4 (.inr a))
      (plusIndexEquiv 4 (.inl b)) (plusIndexEquiv 4 (.inr b)) ∈
        orthDerived (coordinateQuadPlus 4 K) :=
  pairSwap_mem_orthDerived (regular_coordinateQuadPlus 4 K (by norm_num)).1
    (regular_coordinateQuadPlus 4 K (by norm_num)).2

@[expose] noncomputable def plusSwapElt (a b : Fin 4) :
    matrixProjectiveDerived (coordinateQuadPlus 4 K) :=
  projHom _ ⟨_, plusPairSwap_mem (K := K) a b⟩

theorem map_conj_plusSwapElt {a b : Fin 4} (hab : a ≠ b) :
    (pairTorus (K := K) a).map (MulAut.conj (plusSwapElt (K := K) a b)).toMonoidHom =
        pairTorus b ∧
      (pairPerp (K := K) a).map (MulAut.conj (plusSwapElt (K := K) a b)).toMonoidHom =
        pairPerp b :=
  map_conj_pairSwap_eq (isHypCoord_coordinateQuadPlus a) (isHypCoord_coordinateQuadPlus b)
    (pairDisjoint_plus hab) (plusPairSwap_mem a b)

theorem plusSwapElt_mem_stabTwoBar {a b c d : Fin 4} (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a)
    (hdb : d ≠ b) : plusSwapElt (K := K) a b ∈ stabTwoBar K c d := by
  have h := isHypFrame_plus K 4
  exact ⟨⟨_, plusPairSwap_mem a b⟩,
    mem_subgroupOf.2 ⟨h.pairSwap_mem_stabSub hca hcb, h.pairSwap_mem_stabSub hda hdb⟩, rfl⟩

theorem commute_plusSwapElt_of_mem_stabTwoBar {a b : Fin 4} {x : matrixProjectiveDerived
    (coordinateQuadPlus 4 K)} (hx : x ∈ stabTwoBar K a b) :
    plusSwapElt (K := K) a b * x = x * plusSwapElt a b := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨⟨hga, hga'⟩, ⟨hgb, hgb'⟩⟩ := mem_subgroupOf.1 hg
  have hgO : (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 4 K) :=
    Subgroup.commutator_le_self _ g.2
  have hconj := eichler_conj hgO
    (Pi.single (plusIndexEquiv 4 (.inl a)) 1 + Pi.single (plusIndexEquiv 4 (.inl b)) 1)
    (Pi.single (plusIndexEquiv 4 (.inr a)) 1 + Pi.single (plusIndexEquiv 4 (.inr b)) 1)
  rw [map_add, map_add, hga, hga', hgb, hgb'] at hconj
  have hcomm : (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) *
      pairSwap (coordinateQuadPlus 4 K) (plusIndexEquiv 4 (.inl a)) (plusIndexEquiv 4 (.inr a))
        (plusIndexEquiv 4 (.inl b)) (plusIndexEquiv 4 (.inr b)) =
      pairSwap (coordinateQuadPlus 4 K) (plusIndexEquiv 4 (.inl a)) (plusIndexEquiv 4 (.inr a))
        (plusIndexEquiv 4 (.inl b)) (plusIndexEquiv 4 (.inr b)) * g := by
    rw [mul_inv_eq_iff_eq_mul] at hconj
    exact hconj
  have hcomm' : (⟨_, plusPairSwap_mem a b⟩ : orthDerived (coordinateQuadPlus 4 K)) * g =
      g * ⟨_, plusPairSwap_mem a b⟩ := Subtype.ext hcomm.symm
  rw [plusSwapElt, ← map_mul, ← map_mul, hcomm']

theorem plusOverlap_eq_stabTwoBar_four (hq : 4 ≤ Nat.card K) {a b : Fin 4} (hab : a ≠ b) :
    plusOverlap (K := K) a b = stabTwoBar K a b :=
  perfectCore_pairPerpOf_inf_centralizer_pairTorusOf hq (isHypCoord_coordinateQuadPlus a)
    (isHypCoord_coordinateQuadPlus b) (plusFourLeviInput_holds K hq a b hab).1

end Swap

@[expose] def PlusFourSwapCommInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (3 + 1) K)) (t : G),
      orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
        (∃ hz : z ∈ L, IsLongRoot _ (e ⟨z, hz⟩)) ∧
        (∃ hz : z ∈ CFSG.conjugate L x,
          IsLongRoot _ (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)) ∧
        ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹) →
      (∀ k : Fin (3 + 1), OmegaRowAt t (modelToG e (pairTorus (K := K) k))
        (modelToG e (pairPerp (K := K) k)) .swap) →
      ∀ a b c d : Fin (3 + 1), a ≠ b → c ≠ d → c ≠ a → c ≠ b → d ≠ a → d ≠ b →
        centralizerPerfectCore (modelToG e (pairTorus (K := K) a) ⊔
            modelToG e (pairTorus (K := K) b)) ≤
          centralizer (modelToG e (stabTwoBar K c d) : Set G)

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem agreeOn_or_flipOn_pairTorus_four {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G}
    (htC : t ∈ centralizer (L : Set G))
    (Ψ : ∀ k : Fin 4, SwapParam t (modelToG e (pairPerp (K := K) k)))
    (hinj : ∀ k, Function.Injective (Ψ k).Ψ)
    (hrange : ∀ k, (Ψ k).Ψ.range = centralizerPerfectCore (modelToG e (pairTorus (K := K) k)))
    {a b c d : Fin 4} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (hcomm : centralizerPerfectCore (modelToG e (pairTorus (K := K) a) ⊔
        modelToG e (pairTorus (K := K) b)) ≤
      centralizer (modelToG e (stabTwoBar K c d) : Set G)) :
    AgreeOn (Ψ a) (Ψ b) (perfectCore (modelToG e (pairPerp (K := K) a) ⊓
        centralizer (modelToG e (pairTorus (K := K) b) : Set G))) ∨
      FlipOn (Ψ a) (Ψ b) (perfectCore (modelToG e (pairPerp (K := K) a) ⊓
        centralizer (modelToG e (pairTorus (K := K) b) : Set G))) := by
  set n : G := ((e.symm (plusSwapElt (K := K) a b) : L) : G) with hn
  obtain ⟨hXn, hDn⟩ := map_conj_plusSwapElt (K := K) hab
  obtain ⟨-, -, -, -, -, -, -, hDq, hZ, -, -⟩ := neighbour_data_pairTorus_four hKc hq b e htC
    (X := modelToG e (pairTorus (K := K) b)) rfl (D := modelToG e (pairPerp (K := K) b)) rfl
  have := isSimpleGroup_of_isQuasisimple_of_center_eq_bot hDq hZ
  have hO : perfectCore (modelToG e (pairPerp (K := K) a) ⊓
      centralizer (modelToG e (pairTorus (K := K) b) : Set G)) =
        modelToG e (stabTwoBar K a b) := by
    rw [perfectCore_modelToG_inf_centralizer]
    exact congrArg (modelToG e) (plusOverlap_eq_stabTwoBar_four hq hab)
  have hOa : modelToG e (stabTwoBar K a b) ≤ modelToG e (pairPerp (K := K) a) :=
    UnitaryPilot.modelToG_mono e (stabTwoBar_le_pairPerp a b)
  have hOb : modelToG e (stabTwoBar K a b) ≤ modelToG e (pairPerp (K := K) b) :=
    UnitaryPilot.modelToG_mono e (by rw [← pairPerp_inf_pairPerp]; exact inf_le_right)
  have hXD : modelToG e (pairTorus (K := K) b) ≤ modelToG e (pairPerp (K := K) a) :=
    UnitaryPilot.modelToG_mono e (pairTorus_le_pairPerp hab)
  have hcore := (Ψ a).centralizerPerfectCore_sup_eq (hinj a) (hrange a) hXD
  rw [hO] at hcore ⊢
  refine agreeOn_or_flipOn_of_conj (Ψ a) (Ψ b) (hinj a) (hinj b) hZ (n := n) ?_ ?_ hOa hOb ?_ ?_
  · rw [hn, ← UnitaryPilot.modelToG_map_conj, hDn]
  · rw [hrange a, hrange b, F4Pilot.map_centralizerPerfectCore, hn,
      ← UnitaryPilot.modelToG_map_conj, hXn]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hx
    have h := commute_plusSwapElt_of_mem_stabTwoBar hy
    have h' : n * ((e.symm y : L) : G) = ((e.symm y : L) : G) * n := by
      rw [hn, ← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, h]
    rw [h', mul_inv_cancel_right]
  · intro x hx
    have hmem : (Ψ a).lft x ∈ centralizerPerfectCore (modelToG e (pairTorus (K := K) a) ⊔
        modelToG e (pairTorus (K := K) b)) := by
      rw [hcore, (Ψ a).lft_of_mem (hOa hx)]
      exact ⟨(⟨x, hOa hx⟩, 1), Subgroup.mem_prod.2 ⟨mem_subgroupOf.2 hx, one_mem _⟩, rfl⟩
    have hnR : n ∈ modelToG e (stabTwoBar K c d) :=
      UnitaryPilot.symm_mem_modelToG e (plusSwapElt_mem_stabTwoBar hca hcb hda hdb)
    rw [mem_centralizer_iff.1 (hcomm hmem) n hnR, mul_inv_cancel_right]

theorem plusFourSwapDichotomyInput_of_comm (hcomm : PlusFourSwapCommInput) :
    PlusFourSwapDichotomyInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hR5 hrow Ψ hinj hrange a b hab
  have hq : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨c, hca, hcb⟩ := exists_ne_ne_fin (by norm_num : 3 ≤ 4) a b
  obtain ⟨d, hda, hdb, hdc⟩ := exists_ne_ne_ne_fin (by norm_num) a b c
  exact agreeOn_or_flipOn_pairTorus_four hKc hq e htC Ψ hinj hrange hab hca hcb hda hdb
    (hcomm G L hset f K hKc hf e t ht hKt hR5 hrow a b c d hab (Ne.symm hdc) hca hcb hda hdb)

end Main

section Final


theorem omegaPlusFourSwapInput_of_comm (hcomm : PlusFourSwapCommInput)
    (hP : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
      SwapPairExclusion (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :
    OmegaPlusFourSwapInput :=
  omegaPlusFourSwapInput_of_dichotomy (plusFourSwapDichotomyInput_of_comm hcomm) hP

end Final

end CFSG.SeitzReduction.OmegaPilot
