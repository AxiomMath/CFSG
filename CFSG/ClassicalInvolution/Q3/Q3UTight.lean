module

public import CFSG.ClassicalInvolution.Q3.Q3UWiel
public import CFSG.ClassicalInvolution.Q3.Q3MApp

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Orbit

variable {Y : Type} [Group Y] {L T : Subgroup Y}

@[expose] def layerOrbit (L T : Subgroup Y) : Subgroup Y := ⨆ l ∈ L, conjSub l T

theorem conjSub_le_layerOrbit {l : Y} (hl : l ∈ L) : conjSub l T ≤ layerOrbit L T :=
  le_iSup₂_of_le l hl le_rfl

theorem le_layerOrbit : T ≤ layerOrbit L T := by
  have := conjSub_le_layerOrbit (T := T) (L.one_mem)
  rwa [conjSub_one] at this

theorem conjSub_layerOrbit_le {l : Y} (hl : l ∈ L) :
    conjSub l (layerOrbit L T) ≤ layerOrbit L T := by
  unfold layerOrbit
  rw [conjSub, Subgroup.map_iSup]
  refine iSup_le fun l' => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hl' => ?_
  have h : (conjSub l' T).map (MulAut.conj l).toMonoidHom = conjSub (l * l') T := by
    rw [conjSub_mul]
    rfl
  rw [h]
  exact conjSub_le_layerOrbit (L.mul_mem hl hl')

theorem conjSub_layerOrbit {l : Y} (hl : l ∈ L) : conjSub l (layerOrbit L T) = layerOrbit L T := by
  refine le_antisymm (conjSub_layerOrbit_le hl) ?_
  have h := conjSub_mono (n := l) (conjSub_layerOrbit_le (T := T) (L.inv_mem hl))
  rwa [conjSub_conjSub_inv] at h

theorem layerOrbit_normal (hTL : T ⊔ L = ⊤) : (layerOrbit L T).Normal := by
  have h : T ⊔ L ≤ Subgroup.normalizer (layerOrbit L T : Set Y) := by
    refine sup_le (fun t ht => ?_) (fun l hl => ?_)
    · exact Subgroup.le_normalizer (le_layerOrbit ht)
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      have h := conjSub_layerOrbit (T := T) hl
      constructor
      · intro hy
        have := conj_mem_conjSub (n := l) hy
        rwa [h] at this
      · intro hy
        rw [← h, mem_conjSub_iff] at hy
        have e : l⁻¹ * (l * y * l⁻¹) * l = y := by group
        rwa [e] at hy
  rw [hTL, top_le_iff, Subgroup.normalizer_eq_top_iff] at h
  exact h

end Orbit

section Centralizer

variable {Y : Type} [Group Y] [Finite Y] {L T : Subgroup Y} {z : Y}

omit [Finite Y] in
theorem exists_mul_of_mem_centralizer (hz : IsClassicalMember3 L z) (hTL : T ⊔ L = ⊤) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({z} : Set Y)) :
    ∃ e ∈ layerOrbit L T ⊓ Subgroup.centralizer ({z} : Set Y), ∃ l ∈ L, c = e * l := by
  have : (layerOrbit L T).Normal := layerOrbit_normal hTL
  have hEL : layerOrbit L T ⊔ L = ⊤ :=
    top_le_iff.mp (hTL ▸ sup_le_sup_right le_layerOrbit L)
  have hc' : c ∈ layerOrbit L T ⊔ L := hEL ▸ Subgroup.mem_top c
  obtain ⟨e, he, l, hl, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hc'
  refine ⟨e, ⟨he, ?_⟩, l, hl, rfl⟩
  have hlC : l ∈ Subgroup.centralizer ({z} : Set Y) := isSubnormal_le hz.subnormal hl
  have : e = (e * l) * l⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hlC)

theorem tight_commutator (hz : IsClassicalMember3 L z) (hTL : T ⊔ L = ⊤)
    (P : Sylow 3 ↥(Subgroup.centralizer ({z} : Set Y)))
    {σ ω : ↥(Subgroup.centralizer ({z} : Set Y))} (hσP : σ ∈ (P : Subgroup _))
    (hσL : (σ : Y) ∈ L) (hω : (ω : Y) ∈ layerOrbit L T) :
    ∃ l : ↥(Subgroup.centralizer ({z} : Set Y)), (l : Y) ∈ L ∧ (l : Y) ∈ layerOrbit L T ∧
      ∃ π : ↥(Subgroup.centralizer ({z} : Set Y)), π ∈ (P : Subgroup _) ∧
        (π : Y) ∈ layerOrbit L T ∧ σ⁻¹ * ω⁻¹ * σ * ω = l * (ω⁻¹ * π * ω) := by
  have : (layerOrbit L T).Normal := layerOrbit_normal hTL
  have : ((layerOrbit L T).subgroupOf (Subgroup.centralizer ({z} : Set Y))).Normal :=
    Subgroup.normal_subgroupOf
  have hL' : (L.subgroupOf (Subgroup.centralizer ({z} : Set Y))).IsSubnormal :=
    M.isSubnormal_subgroupOf_top' hz.subnormal
  have hWL : (layerOrbit L T).subgroupOf (Subgroup.centralizer ({z} : Set Y)) ⊔
      L.subgroupOf (Subgroup.centralizer ({z} : Set Y)) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    obtain ⟨e, he, l, hl, hcel⟩ := exists_mul_of_mem_centralizer hz hTL c.2
    have hlC : l ∈ Subgroup.centralizer ({z} : Set Y) := isSubnormal_le hz.subnormal hl
    have : c = (⟨e, he.2⟩ : ↥(Subgroup.centralizer ({z} : Set Y))) *
        (⟨l, hlC⟩ : ↥(Subgroup.centralizer ({z} : Set Y))) := Subtype.ext hcel
    rw [this]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr he.1)
      (Subgroup.mem_subgroupOf.mpr hl)
  obtain ⟨l, hl, π, hπ, h⟩ := exists_commutator_eq hL' hWL P hσP
    (Subgroup.mem_subgroupOf.mpr hσL) (Subgroup.mem_subgroupOf.mpr hω)
  exact ⟨l, Subgroup.mem_subgroupOf.mp hl.1, Subgroup.mem_subgroupOf.mp hl.2, π, hπ.1,
    Subgroup.mem_subgroupOf.mp hπ.2, h⟩

end Centralizer

end CFSG.ClassicalInvolution.Q3
