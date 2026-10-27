module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G]

theorem derivedOf_le (H : Subgroup G) : derivedOf H ≤ H :=
  Subgroup.map_subtype_le _

theorem mem_derivedOf_iff {H : Subgroup G} {x : G} :
    x ∈ derivedOf H ↔ ∃ h : x ∈ H, (⟨x, h⟩ : ↥H) ∈ _root_.commutator ↥H := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact Subgroup.mem_map.mpr ⟨⟨x, h⟩, hx, rfl⟩

theorem derivedOf_mono {H K : Subgroup G} (hHK : H ≤ K) : derivedOf H ≤ derivedOf K := by
  intro x hx
  obtain ⟨hxH, hxc⟩ := mem_derivedOf_iff.mp hx
  refine mem_derivedOf_iff.mpr ⟨hHK hxH, ?_⟩
  have hmap : (_root_.commutator ↥H).map (Subgroup.inclusion hHK) ≤ _root_.commutator ↥K := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact hmap (Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, hxc, rfl⟩)

theorem conj_mem_derivedOf {H : Subgroup G} {c t : G} (hc : c ∈ H) (ht : t ∈ derivedOf H) :
    c * t * c⁻¹ ∈ derivedOf H := by
  obtain ⟨htH, htc⟩ := mem_derivedOf_iff.mp ht
  refine mem_derivedOf_iff.mpr ⟨H.mul_mem (H.mul_mem hc htH) (H.inv_mem hc), ?_⟩
  have hn : (_root_.commutator ↥H).Normal := inferInstance
  exact hn.conj_mem _ htc ⟨c, hc⟩

theorem commutator_eq_top_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : _root_.commutator A = ⊤) : _root_.commutator B = ⊤ := by
  have h1 : (_root_.commutator A).map e.toMonoidHom = _root_.commutator B := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  rw [← h1, h, Subgroup.map_top_of_surjective _ e.surjective]

theorem le_derivedOf_of_commutator_eq_top {H K : Subgroup G} (hK : K ≤ H)
    (hP : _root_.commutator ↥K = ⊤) : K ≤ derivedOf H := by
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥K) ∈ _root_.commutator ↥K := by rw [hP]; trivial
  have h2 : derivedOf K ≤ derivedOf H := derivedOf_mono hK
  refine h2 (mem_derivedOf_iff.mpr ⟨hx, hx'⟩)

end CFSG.EvenSporadicStandard.HNRecog.Section3
