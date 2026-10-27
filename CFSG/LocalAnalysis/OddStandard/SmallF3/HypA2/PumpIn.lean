module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Pump
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

private theorem centralizer_mk_eq_inf {G : Type} [Group G] {H : Subgroup G} {x : G} (hx : x ∈ H) :
    Subgroup.centralizer ({(⟨x, hx⟩ : H)} : Set H) =
      (H ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf H := by
  ext y
  constructor
  · intro hy
    refine Subgroup.mem_subgroupOf.mpr ⟨y.2, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy ⟨x, hx⟩ rfl)
  · intro hy
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hy
    exact Subgroup.mem_centralizer_iff.mpr fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hy.2 x rfl)

theorem exists_component_pump_in {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : oddCore ↥H = ⊥) {s : G} (hsH : s ∈ H) (hs : orderOf s = 2) {T : Subgroup G}
    (hT : ComponentClassification.HarrisLit.IsTwoComponentIn T
      (H ⊓ centralizer ({s} : Set G))) :
    ∃ M : Subgroup G, Omega.IsComponentIn M H ∧
      ((M.map (MulAut.conj s).toMonoidHom = M ∧ T ≤ M) ∨
        (M.map (MulAut.conj s).toMonoidHom ≠ M ∧
          ⁅M, M.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧
          ∃ φ : ↥M →* G, (∀ m : ↥M, φ m = (m : G) * (s * m * s⁻¹)) ∧ T = φ.range ∧
            φ.ker ≤ center ↥M)) := by
  set s' : ↥H := ⟨s, hsH⟩ with hs'def
  have hs' : orderOf s' = 2 := by
    rw [hs'def, Subgroup.orderOf_mk]
    exact hs
  have hTH : T ≤ H := hT.1.trans inf_le_left
  have hC : centralizer ({s'} : Set ↥H) = (H ⊓ centralizer ({s} : Set G)).subgroupOf H := by
    rw [hs'def]
    exact centralizer_mk_eq_inf hsH
  have hT' : ComponentClassification.HarrisLit.IsTwoComponentIn (T.subgroupOf H)
      (centralizer ({s'} : Set ↥H)) := by
    rw [hC]
    have hle : T.subgroupOf H ≤ (H ⊓ centralizer ({s} : Set G)).subgroupOf H :=
      fun x hx => hT.1 hx
    rw [ComponentClassification.HarrisLit.isTwoComponentIn_iff hle,
      CFSG.ComponentClassification.UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
        (inf_le_left) 2 Nat.prime_two]
    exact (ComponentClassification.HarrisLit.isTwoComponentIn_iff hT.1).mp hT
  obtain ⟨M', hM'comp, hcases⟩ := exists_component_pump hH hs' hT'
  have hconj : (MulAut.conj s).toMonoidHom.comp H.subtype =
      H.subtype.comp (MulAut.conj s').toMonoidHom := by
    ext m
    simp [MulAut.conj_apply, hs'def]
  set M : Subgroup G := M'.map H.subtype with hMdef
  have hMsub : M.subgroupOf H = M' := by
    rw [hMdef]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective M'
  have hmap_eq : M.map (MulAut.conj s).toMonoidHom =
      (M'.map (MulAut.conj s').toMonoidHom).map H.subtype := by
    rw [hMdef]
    simp only [Subgroup.map_map, hconj]
  refine ⟨M, ⟨Subgroup.map_subtype_le M', ?_⟩, ?_⟩
  · rw [hMsub]
    exact hM'comp
  · rcases hcases with ⟨hfix, hTM⟩ | ⟨hne, hcomm, φ, hφapply, hT'φ, hker⟩
    · left
      refine ⟨?_, ?_⟩
      · rw [hmap_eq, hfix]
      · rw [hMdef]
        calc T = (T.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hTH).symm
          _ ≤ M'.map H.subtype := Subgroup.map_mono hTM
    · right
      have hneG : M.map (MulAut.conj s).toMonoidHom ≠ M := by
        intro h
        exact hne (Subgroup.map_injective H.subtype_injective (hmap_eq.symm.trans h))
      have hcommG : ⁅M, M.map (MulAut.conj s).toMonoidHom⁆ = ⊥ := by
        have h1 : Subgroup.map H.subtype ⁅M', M'.map (MulAut.conj s').toMonoidHom⁆ = ⊥ := by
          rw [hcomm, Subgroup.map_bot]
        rw [Subgroup.map_commutator] at h1
        rw [← hMdef, ← hmap_eq] at h1
        exact h1
      let e : ↥M' ≃* ↥M := M'.equivMapOfInjective H.subtype H.subtype_injective
      let φ' : ↥M →* G := H.subtype.comp (φ.comp e.symm.toMonoidHom)
      have hrange : φ'.range = φ.range.map H.subtype := by
        change (H.subtype.comp (φ.comp e.symm.toMonoidHom)).range = φ.range.map H.subtype
        rw [MonoidHom.range_comp (g := H.subtype) (f := φ.comp e.symm.toMonoidHom),
          MonoidHom.range_comp (g := φ) (f := e.symm.toMonoidHom),
          MonoidHom.range_eq_top_of_surjective e.symm.toMonoidHom e.symm.surjective,
          Subgroup.map_top]
      have hker_eq : φ'.ker = φ.ker.map e.toMonoidHom := by
        ext m
        constructor
        · intro hm
          rw [MonoidHom.mem_ker] at hm
          refine ⟨e.symm m, MonoidHom.mem_ker.mpr ?_, e.apply_symm_apply m⟩
          exact H.subtype_injective (by rw [map_one]; exact hm)
        · rintro ⟨k, hk, hkm⟩
          rw [← hkm]
          refine MonoidHom.mem_ker.mpr ?_
          change H.subtype (φ (e.symm (e k))) = 1
          rw [e.symm_apply_apply, MonoidHom.mem_ker.mp hk, map_one]
      have hker' : φ'.ker ≤ center ↥M :=
        calc φ'.ker = φ.ker.map e.toMonoidHom := hker_eq
          _ ≤ (center ↥M').map e.toMonoidHom := Subgroup.map_mono hker
          _ = center ↥M := Subgroup.map_center_eq e
      refine ⟨hneG, hcommG, φ', ?_, ?_, hker'⟩
      · intro m
        have hesymm : H.subtype (e.symm m) = (m : G) := by
          have h :=
            Subgroup.coe_equivMapOfInjective_apply M' H.subtype H.subtype_injective (e.symm m)
          rw [e.apply_symm_apply] at h
          exact h.symm
        change H.subtype (φ (e.symm m)) = (m : G) * (s * m * s⁻¹)
        rw [hφapply (e.symm m)]
        simp only [map_mul, map_inv, hesymm, hs'def]
        rfl
      · calc T = (T.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hTH).symm
          _ = φ.range.map H.subtype := by rw [hT'φ]
          _ = φ'.range := hrange.symm

end CFSG.OddStandard.SmallF3.HypA2
