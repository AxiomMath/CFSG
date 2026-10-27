module

public import CFSG.Goldschmidt75.Closure

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_normalizer_conj (P : Sylow p G) {S : Subgroup G} (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P) {x g : G} (hx : x ∈ centralizer (S : Set G))
    (hxg : g⁻¹ * x * g ∈ centralizer (S : Set G)) :
    ∃ m ∈ normalizer (S : Set G), m⁻¹ * x * m = g⁻¹ * x * g := by
  set y := g⁻¹ * x * g
  set C := centralizer ({y} : Set G)
  have hSC : S ≤ C := fun s hs => mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp hxg s hs)
  have hSgC : conjSub g S ≤ C := by
    intro s hs
    rw [mem_conjSub] at hs
    rw [mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_iff.mp hx _ hs
    calc s * y = g⁻¹ * ((g * s * g⁻¹) * x) * g := by simp only [y]; group
      _ = g⁻¹ * (x * (g * s * g⁻¹)) * g := by rw [h1]
      _ = y * s := by simp only [y]; group
  have hpS : IsPGroup p S := P.isPGroup'.to_le hSP
  obtain ⟨Q, hQ⟩ := (hpS.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨Q', hQ'⟩ := ((hpS.map (MulAut.conj g⁻¹).toMonoidHom).comap_subtype (K := C)
    |>.exists_le_sylow)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q' Q
  set QG := (Q : Subgroup C).map C.subtype
  have hSQ : S ≤ QG := fun s hs => ⟨⟨s, hSC hs⟩, hQ (by simpa [mem_subgroupOf] using hs), rfl⟩
  have hSgQ : conjSub (g * (c : G)⁻¹) S ≤ QG := by
    intro z hz
    rw [conjSub_mul, mem_conjSub, inv_inv] at hz
    have hwC : ((c : G)⁻¹ * z * c) ∈ C := hSgC hz
    have hw : (⟨(c : G)⁻¹ * z * c, hwC⟩ : C) ∈ (Q' : Subgroup C) :=
      hQ' (show _ ∈ conjSub g S from hz)
    have hzC : z ∈ C := by
      have := C.mul_mem (C.mul_mem c.2 hwC) (C.inv_mem c.2)
      simpa [mul_assoc] using this
    have hmem : (⟨z, hzC⟩ : C) ∈ (Q : Subgroup C) := by
      rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      refine ⟨_, hw, Subtype.ext ?_⟩
      simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    exact ⟨_, hmem, rfl⟩
  obtain ⟨P', hP'⟩ := (Q.2.map C.subtype).exists_le_sylow
  have hS' := stronglyClosed_of_le_sylow P P' hS (hSQ.trans hP')
  have heq := conj_eq_of_conj_le hS' (hSgQ.trans hP')
  refine ⟨g * (c : G)⁻¹, mem_normalizer_of_conjSub_eq heq, ?_⟩
  have hcy : (c : G) * y = y * c := mem_centralizer_singleton_iff.mp c.2
  calc (g * (c : G)⁻¹)⁻¹ * x * (g * (c : G)⁻¹) = (c : G) * y * (c : G)⁻¹ := by
        simp only [y]; group
    _ = y * c * (c : G)⁻¹ := by rw [hcy]
    _ = y := by group

omit [Finite G] [Fact p.Prime] in
theorem mem_centralizer_subgroupOf_iff {H A : Subgroup G} (hAH : A ≤ H) {x : H} :
    x ∈ centralizer ((A.subgroupOf H : Subgroup H) : Set H) ↔
      (x : G) ∈ centralizer (A : Set G) := by
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h a ha
    exact congrArg Subtype.val (h ⟨a, hAH ha⟩ (by simpa [mem_subgroupOf] using ha))
  · intro h a ha
    exact Subtype.ext (h a ha)

theorem exists_normalizer_conj_of_le {H S : Subgroup G} (T : Sylow p H) (hSH : S ≤ H)
    (hST : S.subgroupOf H ≤ T)
    (hS : fusionStronglyClosed ((S.subgroupOf H : Subgroup H) : Set H) T) {x g : G}
    (hxH : x ∈ H) (hgH : g ∈ H) (hx : x ∈ centralizer (S : Set G))
    (hxg : g⁻¹ * x * g ∈ centralizer (S : Set G)) :
    ∃ m ∈ H ⊓ normalizer (S : Set G), m⁻¹ * x * m = g⁻¹ * x * g := by
  have hx' : (⟨x, hxH⟩ : H) ∈ centralizer ((S.subgroupOf H : Subgroup H) : Set H) :=
    (mem_centralizer_subgroupOf_iff hSH).2 hx
  have hxg' : (⟨g, hgH⟩ : H)⁻¹ * ⟨x, hxH⟩ * ⟨g, hgH⟩ ∈
      centralizer ((S.subgroupOf H : Subgroup H) : Set H) :=
    (mem_centralizer_subgroupOf_iff hSH).2 (by simpa using hxg)
  obtain ⟨m, hm, hmeq⟩ := exists_normalizer_conj T hST hS hx' hxg'
  refine ⟨m, ⟨m.2, mem_normalizer_of_mem_normalizer_subgroupOf hSH hm⟩, ?_⟩
  simpa using congrArg Subtype.val hmeq

end CFSG.Goldschmidt75
