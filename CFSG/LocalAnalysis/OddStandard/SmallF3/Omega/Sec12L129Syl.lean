module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L46

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec12_conj_mem_jElem {R0 : Subgroup G} {g : G}
    (hg : g ∈ normalizer (R0 : Set G)) :
    ∀ x ∈ JElem R0, g * x * g⁻¹ ∈ JElem R0 := by
  intro x hx
  change x ∈ Subgroup.closure {x : G | ∃ A : Subgroup G, IsMaxElemAbelianIn R0 A ∧ x ∈ A} at hx
  have hgen : ∀ y ∈ ({x : G | ∃ A : Subgroup G, IsMaxElemAbelianIn R0 A ∧ x ∈ A} : Set G),
      (MulAut.conj g) y ∈
        ({x : G | ∃ A : Subgroup G, IsMaxElemAbelianIn R0 A ∧ x ∈ A} : Set G) := by
    rintro y ⟨A, hA, hyA⟩
    have hle : CFSG.conjugate A g⁻¹ ≤ R0 := by
      intro w hw
      have hw' : g⁻¹ * w * (g⁻¹)⁻¹ ∈ A := mem_conjugate_iff'.mp hw
      have hwR : g⁻¹ * w * (g⁻¹)⁻¹ ∈ R0 := hA.1 hw'
      have h2 : g * (g⁻¹ * w * (g⁻¹)⁻¹) * g⁻¹ ∈ R0 :=
        (Subgroup.mem_normalizer_iff.mp hg _).mp hwR
      have h3 : g * (g⁻¹ * w * (g⁻¹)⁻¹) * g⁻¹ = w := by group
      rwa [h3] at h2
    refine ⟨CFSG.conjugate A g⁻¹, sec4_isMaxElemAbelianIn_conjugate hA g⁻¹ hle, ?_⟩
    rw [MulAut.conj_apply, mem_conjugate_iff']
    have h3 : g⁻¹ * (g * y * g⁻¹) * (g⁻¹)⁻¹ = y := by group
    rw [h3]
    exact hyA
  have hmap : (Subgroup.closure
      {x : G | ∃ A : Subgroup G, IsMaxElemAbelianIn R0 A ∧ x ∈ A}).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.closure {x : G | ∃ A : Subgroup G, IsMaxElemAbelianIn R0 A ∧ x ∈ A} := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro y ⟨a, ha, rfl⟩
    exact hgen a ha
  have hx' := hmap (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx)
  have h2 : g * x * g⁻¹ ∈
      Subgroup.closure {x : G | ∃ A : Subgroup G, IsMaxElemAbelianIn R0 A ∧ x ∈ A} := by
    simpa [MulAut.conj_apply] using hx'
  exact h2

theorem sec12_mem_normalizer_jElem {R0 : Subgroup G} {g : G} (hg : g ∈ normalizer (R0 : Set G)) :
    g ∈ normalizer (JElem R0 : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => sec12_conj_mem_jElem hg y hy, fun hy => ?_⟩
  have hg' : g⁻¹ ∈ normalizer (R0 : Set G) := (normalizer (R0 : Set G)).inv_mem hg
  have h := sec12_conj_mem_jElem hg' _ hy
  have h' : g⁻¹ * (g * y * g⁻¹) * (g⁻¹)⁻¹ = y := by group
  rwa [h'] at h

theorem sec12_isSylow2Of_top_of_normalizes [Finite G] {R0 Y : Subgroup G}
    (hR0 : IsSylow2Of R0 (normalizer (Y : Set G)))
    (hnorm : ∀ x ∈ normalizer (R0 : Set G), x ∈ normalizer (Y : Set G)) :
    IsSylow2Of R0 ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Pstar, hPstar_le⟩ := hR0.2.1.exists_le_sylow
  have hPeq : R0 = Pstar := by
    by_contra hne
    have hlt : R0 < Pstar := lt_of_le_of_ne hPstar_le hne
    let H : Subgroup ↥Pstar := R0.subgroupOf Pstar
    have hHlt : H < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      exact hne (le_antisymm hPstar_le (Subgroup.subgroupOf_eq_top.mp htop))
    haveI : Group.IsNilpotent ↥Pstar := Pstar.isPGroup'.isNilpotent
    have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥Pstar)
    obtain ⟨x, hxnorm, hxH⟩ := SetLike.exists_of_lt (hnc H hHlt)
    have hxPstar : (x : G) ∈ Pstar := x.2
    have hxnormR0 : (x : G) ∈ normalizer (R0 : Set G) := by
      have hmap := Subgroup.le_normalizer_map (f := (Pstar : Subgroup G).subtype) (H := H)
      have hxmem : (x : G) ∈ (Subgroup.normalizer H).map (Pstar : Subgroup G).subtype :=
        ⟨x, hxnorm, rfl⟩
      have hthis := hmap hxmem
      rwa [Subgroup.map_subgroupOf_eq_of_le hPstar_le] at hthis
    have hxN : (x : G) ∈ normalizer (Y : Set G) := hnorm _ hxnormR0
    let J : Subgroup G := R0 ⊔ Subgroup.zpowers (x : G)
    have hsup_le : J ≤ normalizer (Y : Set G) :=
      sup_le hR0.1 (Subgroup.zpowers_le.mpr hxN)
    have hzp2 : IsPGroup 2 (Subgroup.zpowers (x : G)) :=
      Pstar.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxPstar)
    have hsup2 : IsPGroup 2 J :=
      hR0.2.1.to_sup_of_normal_left' hzp2 (Subgroup.zpowers_le.mpr hxnormR0)
    have hJeq : J = R0 := hR0.eq_of_le hsup_le hsup2 le_sup_left
    have hxJ : (x : G) ∈ J := Subgroup.mem_sup_right (Subgroup.mem_zpowers (x : G))
    rw [hJeq] at hxJ
    exact hxH (Subgroup.mem_subgroupOf.mpr hxJ)
  refine ⟨le_top, hR0.2.1, ?_⟩
  rw [Subgroup.relIndex_top_right, hPeq]
  exact Pstar.not_dvd_index

theorem sec12_isSylow2Of_top_of_jElem [Finite G] {R0 V : Subgroup G}
    (hR0 : IsSylow2Of R0 (normalizer (V : Set G))) (hJ : JElem R0 = V) : IsSylow2Of R0 ⊤ :=
  sec12_isSylow2Of_top_of_normalizes hR0 fun _ hx => hJ ▸ sec12_mem_normalizer_jElem hx

end CFSG.OddStandard.SmallF3.Omega
