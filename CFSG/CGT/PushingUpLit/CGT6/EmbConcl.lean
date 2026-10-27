module

public import CFSG.CGT.PushingUpLit.CGT6.EmbX

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit CFSG.Quasithin
open CFSG.CGT.PushingUpLit.SixThree
open scoped commutatorElement

section Stage

variable {G : Type} [Group G] [Finite G]

theorem emb_stage_one (hchar : IsCharacteristicP 2 G) {Y V P : Subgroup G} [V.Normal]
    (hVe : IsElementaryAbelian 2 V) (hY : InClassX ↥Y)
    (hYV : ¬ Y ≤ Subgroup.centralizer (V : Set G))
    (hYN : Y ≤ Subgroup.normalizer ((P ⊔ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
    (hs : (Y.subgroupOf (Subgroup.normalizer
      ((P ⊔ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))).IsSubnormal) :
    V ≤ Subgroup.normalizer (Y : Set G) ∧ ⁅V, Y⁆ = ⁅oTwoIn Y, Y⁆ ∧
      ⁅pCore 2 G ⊓ Subgroup.centralizer (V : Set G), Y⁆ = ⁅oTwoIn Y, Y⁆ ∧
      Subgroup.centralizer (V : Set G) ≤ centralizerModCore Y := by
  set C := Subgroup.centralizer (V : Set G) with hC
  set H := Subgroup.normalizer ((P ⊔ C : Subgroup G) : Set G) with hH
  have hV2 : IsPGroup 2 V := IsElementaryAbelian.isPGroup 2 ↥V
  have hmax : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N ≤ pCore 2 G :=
    fun N hN hN2 => le_sSup ⟨hN, hN2⟩
  have hVQ : V ≤ pCore 2 G := hmax V inferInstance hV2
  have hVC : V ≤ C :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hVe.toIsMulCommutative
  have hCH : C ≤ H := le_sup_right.trans Subgroup.le_normalizer
  have hne : ⁅V, Y⁆ ≠ ⊥ := fun h => hYV (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (by rw [Subgroup.commutator_comm]; exact h))
  have hYn : ∀ N : Subgroup G, N.Normal → Y ≤ Subgroup.normalizer (N : Set G) := fun N _ => by
    rw [Subgroup.normalizer_eq_top N]
    exact le_top
  have hQ2 : IsPGroup 2 ↥(pCore 2 G) := pCore_isPGroup
  have hQ₁2 : IsPGroup 2 ↥(pCore 2 G ⊓ C) := hQ2.to_le inf_le_left
  obtain ⟨hVN, -, hVU⟩ := commutator_eq_U_of_isSubnormal hY.1 hV2 (hYn V inferInstance) hYN
    (hVC.trans hCH) hs
  obtain ⟨-, -, hQU⟩ := commutator_eq_U_of_isSubnormal hY.1 hQ₁2
    (hYn (pCore 2 G ⊓ C) inferInstance) hYN (inf_le_right.trans hCH) hs
  have hVU' : ⁅V, Y⁆ = ⁅oTwoIn Y, Y⁆ := hVU.resolve_left hne
  have hQne : ⁅pCore 2 G ⊓ C, Y⁆ ≠ ⊥ := fun h => hne (eq_bot_iff.mpr
    ((Subgroup.commutator_mono (le_inf hVQ hVC) le_rfl).trans h.le))
  refine ⟨hVN, hVU', hQU.resolve_left hQne, ?_⟩
  exact centralizer_le_centralizerModCore (H := H) pCore_isPGroup hchar hmax hVQ hVC hY.1 hYN hCH hs
    hne

end Stage

section Conj

variable {G : Type} [Group G]

theorem le_normalizer_commutator_left {V X : Subgroup G} [V.Normal] :
    X ≤ Subgroup.normalizer ((⁅V, X⁆ : Subgroup G) : Set G) := by
  have key : ∀ x ∈ X, ∀ z ∈ (⁅V, X⁆ : Subgroup G), x * z * x⁻¹ ∈ (⁅V, X⁆ : Subgroup G) := by
    intro x hx z hz
    have h1 : x * z * x⁻¹ ∈ (⁅V, X⁆ : Subgroup G).map (MulAut.conj x).toMonoidHom :=
      ⟨z, hz, by simp [MulAut.conj_apply]⟩
    rw [Subgroup.map_commutator] at h1
    refine Subgroup.commutator_mono ?_ ?_ h1
    · rintro _ ⟨v, hv, rfl⟩
      simpa [MulAut.conj_apply] using (inferInstance : V.Normal).conj_mem v hv x
    · rintro _ ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)
  intro x hx
  exact mem_normalizer_of_conj_mem (key x hx) (fun z hz => by
    simpa using key x⁻¹ (X.inv_mem hx) z hz)

theorem conj_mem_commutator_conjClosure {Y Xt V : Subgroup G} [V.Normal] {g : G} (hg : g ∈ Xt)
    {z : G} (hz : z ∈ (⁅V, Y⁆ : Subgroup G)) :
    g * z * g⁻¹ ∈ (⁅V, conjClosure Y Xt⁆ : Subgroup G) := by
  have h1 : g * z * g⁻¹ ∈ (⁅V, Y⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom :=
    ⟨z, hz, by simp [MulAut.conj_apply]⟩
  rw [Subgroup.map_commutator] at h1
  refine Subgroup.commutator_mono ?_ (map_conj_le_conjClosure hg) h1
  rintro _ ⟨v, hv, rfl⟩
  simpa [MulAut.conj_apply] using (inferInstance : V.Normal).conj_mem v hv g

theorem commutatorElement_conj_right (m g y : G) :
    ⁅m, g * y * g⁻¹⁆ = g * ⁅g⁻¹ * m * g, y⁆ * g⁻¹ := by
  rw [conjugate_commutatorElement]
  have e : g * (g⁻¹ * m * g) * g⁻¹ = m := by group
  rw [e]

end Conj

section ConjFacts

variable {G : Type} [Group G] [Finite G]

theorem emb_conj_facts (hchar : IsCharacteristicP 2 G) {Y V Xt : Subgroup G} [V.Normal]
    (hQU : ⁅pCore 2 G ⊓ Subgroup.centralizer (V : Set G), Y⁆ = ⁅V, Y⁆) :
    ⁅pCore 2 G ⊓ Subgroup.centralizer (V : Set G), conjClosure Y Xt⁆ ≤ ⁅V, conjClosure Y Xt⁆ ∧
      conjClosure Y Xt ⊓ Subgroup.centralizer (V : Set G) ≤ pCore 2 G ∧
      ⁅conjClosure Y Xt ⊓ Subgroup.centralizer (V : Set G), conjClosure Y Xt⁆ ≤
        ⁅V, conjClosure Y Xt⁆ := by
  set C := Subgroup.centralizer (V : Set G) with hC
  set Q := pCore 2 G with hQ
  set X := conjClosure Y Xt with hX
  have hQn : (Q ⊓ C).Normal := inferInstance
  have hVV : ⁅V, X⁆ ≤ V := Subgroup.commutator_le_left V X
  have hgen : ∀ g ∈ Xt, ∀ y ∈ Y, ∀ m ∈ Q ⊓ C, ⁅m, g * y * g⁻¹⁆ ∈ (⁅V, X⁆ : Subgroup G) := by
    intro g hg y hy m hm
    rw [commutatorElement_conj_right]
    have h1 : ⁅g⁻¹ * m * g, y⁆ ∈ (⁅V, Y⁆ : Subgroup G) := by
      rw [← hQU]
      exact Subgroup.commutator_mem_commutator (by
        simpa [mul_assoc] using hQn.conj_mem m hm g⁻¹) hy
    exact conj_mem_commutator_conjClosure hg h1
  have hQX : ⁅Q ⊓ C, X⁆ ≤ ⁅V, X⁆ :=
    commutator_conjClosure_le le_normalizer_commutator_left hgen
  have hQXV : ⁅Q ⊓ C, X⁆ ≤ V := hQX.trans hVV
  have hXC : X ⊓ C ≤ Q := by
    have hsub : X ⊓ C ≤ stabSeries V (Q ⊓ C) := by
      rintro x ⟨hxX, hxC⟩
      refine ⟨hxC, fun q hq => ?_⟩
      rw [← commutatorElement_inv]
      exact V.inv_mem (hQXV (Subgroup.commutator_mem_commutator hq hxX))
    exact hsub.trans (stabSeries_inf_le pCore_isPGroup hchar fun N hN hN2 => le_sSup ⟨hN, hN2⟩)
  refine ⟨hQX, hXC, ?_⟩
  exact (Subgroup.commutator_mono (le_inf hXC inf_le_right) le_rfl).trans hQX

end ConjFacts

end CFSG.CGT.PushingUpLit.CGT6
