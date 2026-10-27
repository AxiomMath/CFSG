module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Quot.Elem

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] (M : Subgroup G) [M.Normal]

omit [Finite G] in
theorem normal_inf_subgroupOf (X : Subgroup G) : ((M ⊓ X).subgroupOf X).Normal := by
  have : (M ⊓ X).subgroupOf X = M.subgroupOf X := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
  rw [this]
  exact Subgroup.Normal.subgroupOf ‹M.Normal› _

theorem isCompIn_le_or_commute {Z X : Subgroup G} (hZ : IsCompIn Z X) :
    Z ≤ M ⊓ X ∨ Z ≤ centralizer ((M ⊓ X : Subgroup G) : Set G) := by
  have := CFSG.LocalCores.component_normal_subgroup hZ.2 (normal_inf_subgroupOf M X)
  rcases this with h | h
  · left
    intro x hx
    exact (show (⟨x, hZ.1 hx⟩ : ↥X) ∈ (M ⊓ X).subgroupOf X from h hx)
  · right
    have h1 := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hZ.1 h
    rw [inf_eq_left.2 (inf_le_right : M ⊓ X ≤ X)] at h1
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1

theorem lf_sup_conj_eq_conjClosure
    (hperf : ∀ P : Subgroup (CQ M), ⁅P, P⁆ = P → P ≤ M.map (cq M))
    {Lp Li Tq : Subgroup (CQ M)} {T : Subgroup G} {s : G} (hT : T.map (cq M) = Tq)
    (hsT : s ∈ normalizer (T : Set G)) (hLp : CFSG.IsQuasisimple ↥Lp)
    (hLi : CFSG.IsQuasisimple ↥Li) (hLpM : Lp ≤ M.map (cq M)) (hLiM : Li ≤ M.map (cq M))
    (hcomp : IsCompIn Li (centralizer (Tq : Set (CQ M))))
    (hincl : Lp ≤ Li ⊔ Li.map (MulAut.conj (cq M s)).toMonoidHom)
    (heq : Li ⊔ Li.map (MulAut.conj (cq M s)).toMonoidHom =
      conjClosure Lp (layerIn (centralizer (Tq : Set (CQ M))))) :
    lf M Li ⊔ (lf M Li).map (MulAut.conj s).toMonoidHom =
      conjClosure (lf M Lp) (layerIn (centralizer (T : Set G))) := by
  have hLip : ⁅Li, Li⁆ = Li := Subgroup.isPerfect_iff.1 hLi.1
  have hLpp : ⁅Lp, Lp⁆ = Lp := Subgroup.isPerfect_iff.1 hLp.1
  have hMq : (M.map (cq M)).Normal := Subgroup.Normal.map ‹_› _ (QuotientGroup.mk'_surjective _)
  have hcM : Li.map (MulAut.conj (cq M s)).toMonoidHom ≤ M.map (cq M) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hMq.conj_mem x (hLiM hx) _
  have hQqp : ⁅Li ⊔ Li.map (MulAut.conj (cq M s)).toMonoidHom,
      Li ⊔ Li.map (MulAut.conj (cq M s)).toMonoidHom⁆ =
      Li ⊔ Li.map (MulAut.conj (cq M s)).toMonoidHom :=
    commutator_sup_of_perfect hLip (commutator_map_of_perfect _ hLip)
  have hQqM : Li ⊔ Li.map (MulAut.conj (cq M s)).toMonoidHom ≤ M.map (cq M) := sup_le hLiM hcM
  set Qq := Li ⊔ Li.map (MulAut.conj (cq M s)).toMonoidHom with hQq
  set Q := lf M Li ⊔ (lf M Li).map (MulAut.conj s).toMonoidHom with hQ
  have hQeq : Q = lf M Qq := lf_sup_conj M hLip hLiM s
  have hQM : Q ≤ M := hQeq ▸ lf_le M _
  have hQp : ⁅Q, Q⁆ = Q := hQeq ▸ commutator_lf M hQqp hQqM
  have hπQ : Q.map (cq M) = Qq := by rw [hQeq]; exact map_lf M hQqp hQqM
  have hLpQ : lf M Lp ≤ Q := lf_le_lf_sup_conj M hLpp hLip hLpM hLiM s hincl
  have hLpp' : ⁅lf M Lp, lf M Lp⁆ = lf M Lp := commutator_lf M hLpp hLpM
  set X : Subgroup G := centralizer (T : Set G) with hX
  have hLiC : lf M Li ≤ X := lf_le_centralizer M T hLip
    (le_inf hLiM (by rw [hT]; exact hcomp.1))
  have hQA : Q ≤ M ⊓ X := by
    refine sup_le (le_inf (lf_le M Li) hLiC) ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(inferInstance : M.Normal).conj_mem x (lf_le M Li hx) s, ?_⟩
    refine mem_centralizer_iff.2 fun t ht => ?_
    have hst : s⁻¹ * t * s ∈ T := by
      have := (Subgroup.mem_normalizer_iff.1 ((normalizer (T : Set G)).inv_mem hsT) t).1 ht
      simpa using this
    have := mem_centralizer_iff.1 (hLiC hx) _ hst
    calc t * (s * x * s⁻¹) = s * ((s⁻¹ * t * s) * x) * s⁻¹ := by group
      _ = s * (x * (s⁻¹ * t * s)) * s⁻¹ := by rw [this]
      _ = (s * x * s⁻¹) * t := by group
  have hA : layerIn X ≤ normalizer (Q : Set G) := by
    rw [layerIn_le_iff]
    intro Z hZ
    rcases isCompIn_le_or_commute M hZ with h1 | h1
    · have hZM : Z ≤ M := h1.trans inf_le_left
      have hZq := isCompIn_map_cq M T hZM hZ
      rw [hT] at hZq
      have hZn : Z.map (cq M) ≤ normalizer (Qq : Set (CQ M)) := by
        refine (le_layerIn_of_isCompIn hZq).trans ?_
        rw [heq]
        exact le_normalizer_conjClosure _ _
      intro z hz
      have hz' : cq M z ∈ normalizer (Qq : Set (CQ M)) := hZn ⟨z, hz, rfl⟩
      rw [Solomon78.mem_normalizer_iff_map_conj_eq]
      refine eq_of_map_eq_cq M (map_conj_le_of_normal M hQM z) hQM
        (by rw [← Subgroup.map_commutator, hQp]) hQp ?_
      rw [← Hyp.map_map_conj, hπQ]
      exact Solomon78.mem_normalizer_iff_map_conj_eq.1 hz'
    · intro z hz
      refine Subgroup.centralizer_le_normalizer (Q : Set G) (mem_centralizer_iff.2 fun q hq => ?_)
      exact mem_centralizer_iff.1 (h1 hz) q (hQA hq)
  have hB : conjClosure (lf M Lp) (layerIn X) ≤ Q := conjClosure_le_of_le_normalizer hLpQ hA
  refine le_antisymm ?_ hB
  set C := conjClosure (lf M Lp) (layerIn X) with hC
  have hCM : C ≤ M := hB.trans hQM
  have hCp : ⁅C, C⁆ = C := commutator_conjClosure hLpp'
  have hlay : layerIn (centralizer (Tq : Set (CQ M))) ≤ (layerIn X).map (cq M) := by
    rw [layerIn_le_iff]
    intro Zq hZq
    have hZqM : Zq ≤ M.map (cq M) := hperf Zq (Subgroup.isPerfect_iff.1 hZq.isQuasisimple.1)
    have hlfZ := isCompIn_lf_of_map M hT hZqM hZq.isQuasisimple hZq
    have := Subgroup.map_mono (le_layerIn_of_isCompIn hlfZ) (f := cq M)
    rwa [map_lf M (Subgroup.isPerfect_iff.1 hZq.isQuasisimple.1) hZqM] at this
  have hcC : conjClosure Lp (layerIn (centralizer (Tq : Set (CQ M)))) ≤ C.map (cq M) := by
    refine iSup₂_le fun g hg => ?_
    obtain ⟨g', hg', rfl⟩ := hlay hg
    have e1 : Lp = (lf M Lp).map (cq M) := (map_lf M hLpp hLpM).symm
    calc Lp.map (MulAut.conj (cq M g')).toMonoidHom
        = ((lf M Lp).map (cq M)).map (MulAut.conj (cq M g')).toMonoidHom := by rw [← e1]
      _ = ((lf M Lp).map (MulAut.conj g').toMonoidHom).map (cq M) := Hyp.map_map_conj _ _ _
      _ ≤ C.map (cq M) := Subgroup.map_mono (map_conj_le_conjClosure hg')
  have hQC : Q.map (cq M) ≤ C.map (cq M) := by
    rw [hπQ, heq]
    exact hcC
  exact le_of_map_le_cq M hQM hCM hQp hCp hQC

end CFSG.EvenSporadicStandard.Induction.Junction
