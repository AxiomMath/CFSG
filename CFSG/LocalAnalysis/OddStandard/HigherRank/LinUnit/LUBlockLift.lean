module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence

public noncomputable section

namespace CFSG.OddStandard.HigherRank.LinUnit

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial (isComponentOf_iff_isComponent_subgroupOf
  full_central_kernel_involution_fixed_component_correspondence)

@[expose] def HasFourElt (L : Type) [Group L] : Prop :=
  Blueprint.LieModel (L ⧸ center L) .PSU 4 3 1 → ∃ x : L, x ∈ center L ∧ orderOf x = 4

theorem HasFourElt.of_mulEquiv {L M : Type} [Group L] [Group M] (e : L ≃* M)
    (h : HasFourElt M) : HasFourElt L := by
  intro hm
  have hm' : Blueprint.LieModel (M ⧸ center M) .PSU 4 3 1 :=
    Blueprint.LieModel.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center L) (Subgroup.center M) e
        (Subgroup.map_center_eq e)) hm
  obtain ⟨x, hx, hxo⟩ := h hm'
  exact ⟨e.symm x, by
      rw [Subgroup.mem_center_iff]
      intro y
      apply e.injective
      simp only [map_mul, e.apply_symm_apply]
      exact (Subgroup.mem_center_iff.mp hx) (e y), by
      rw [MulEquiv.orderOf_eq e.symm x, hxo]⟩

theorem hasFourElt_of_component_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : ∀ N : Subgroup H, IsComponent N → HasFourElt N) {M : Subgroup G}
    (hM : IsComponent M) : HasFourElt M :=
  (h _ (LocalCores.isComponent_map_mulEquiv e hM)).of_mulEquiv
    (M.equivMapOfInjective e.toMonoidHom e.injective)

theorem hasFourElt_of_centralLift {P S : Type} [Group P] [Group S] [Finite P]
    {π : P →* S} (hπ : Function.Surjective π) (hK : π.ker ≤ center P) {a : MulAut P}
    {α : MulAut S} (ha : ∀ x, a (a x) = x) (hα : ∀ s, α (α s) = s)
    (hcomm : ∀ x, π (a x) = α (π x))
    (h : ∀ Q : Subgroup (fixedSubgroup a), IsComponent Q →
      Blueprint.LieModel (Q ⧸ center Q) .PSU 4 3 1 →
        ∃ q : Q, q ∈ center Q ∧ orderOf (π ((q : fixedSubgroup a) : P)) = 4)
    {L : Subgroup (fixedSubgroup α)} (hL : IsComponent L) : HasFourElt L := by
  intro hm
  obtain ⟨-, -, -, hlift, -⟩ :=
    full_central_kernel_involution_fixed_component_correspondence hπ hK ha hα hcomm
  set R := L.map (fixedSubgroup α).subtype with hRdef
  have hR : Assembly.IsComponentOf R (fixedSubgroup α) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le L)).2 ?_
    have hRL : R.subgroupOf (fixedSubgroup α) = L :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) L
    rw [hRL]
    exact hL
  obtain ⟨-, hQ, hQmap, -, -, -, ⟨eQR⟩⟩ := hlift R hR
  let Q : Subgroup P := ⁅R.comap π, R.comap π⁆
  have hQab : Assembly.IsComponentOf Q (fixedSubgroup a) := hQ
  have hQmapQ : Q.map π = R := hQmap
  let eL : L ≃* R := L.equivMapOfInjective (fixedSubgroup α).subtype (subtype_injective _)
  let Q' : Subgroup (fixedSubgroup a) := Q.subgroupOf (fixedSubgroup a)
  have hQ' : IsComponent Q' := (isComponentOf_iff_isComponent_subgroupOf hQab.1).1 hQab
  have eQ : Q' ≃* Q := Subgroup.subgroupOfEquivOfLe hQab.1
  have eQZ : Q' ⧸ center Q' ≃* Q ⧸ center Q :=
    QuotientGroup.congr (Subgroup.center Q') (Subgroup.center Q) eQ
      (Subgroup.map_center_eq eQ)
  have eLZ : L ⧸ center L ≃* R ⧸ center R :=
    QuotientGroup.congr (Subgroup.center L) (Subgroup.center R) eL (Subgroup.map_center_eq eL)
  have hm' : Blueprint.LieModel (Q' ⧸ center Q') .PSU 4 3 1 :=
    Blueprint.LieModel.of_mulEquiv (eLZ.trans (eQR.symm.trans eQZ.symm)) hm
  obtain ⟨q, hqc, hqo⟩ := h Q' hQ' hm'
  have hqQ : ((q : fixedSubgroup a) : P) ∈ Q :=
    Subgroup.mem_subgroupOf.mp q.2
  let y : S := π ((q : fixedSubgroup a) : P)
  have hyR : y ∈ R := by
    rw [← hQmapQ]
    exact Subgroup.mem_map_of_mem π hqQ
  let yR : R := ⟨y, hyR⟩
  have hyRc : yR ∈ center R := by
    rw [Subgroup.mem_center_iff]
    intro r
    have hrQ : (r : S) ∈ Q.map π := by
      rw [hQmapQ]
      exact r.2
    obtain ⟨q', hq', hq'eq⟩ := Subgroup.mem_map.mp hrQ
    let q'' : Q' := ⟨⟨q', hQab.1 hq'⟩, Subgroup.mem_subgroupOf.mpr hq'⟩
    have hcq : q'' * q = q * q'' := (Subgroup.mem_center_iff.mp hqc) q''
    have hmap := congrArg (π.comp ((fixedSubgroup a).subtype.comp Q'.subtype)) hcq
    rw [map_mul, map_mul] at hmap
    have hq'' : (π.comp ((fixedSubgroup a).subtype.comp Q'.subtype)) q'' = (r : S) := by
      change π q' = (r : S)
      exact hq'eq
    have hqy : (π.comp ((fixedSubgroup a).subtype.comp Q'.subtype)) q = y := rfl
    rw [hqy, hq''] at hmap
    exact Subtype.ext hmap
  refine ⟨eL.symm yR, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro z
    apply eL.injective
    simp only [map_mul, eL.apply_symm_apply]
    exact (Subgroup.mem_center_iff.mp hyRc) (eL z)
  · calc orderOf (eL.symm yR) = orderOf yR := MulEquiv.orderOf_eq eL.symm yR
      _ = orderOf (yR : S) := (Subgroup.orderOf_coe yR).symm
      _ = 4 := by
          rw [show (yR : S) = π ((q : fixedSubgroup a) : P) from rfl]
          exact hqo

end CFSG.OddStandard.HigherRank.LinUnit
