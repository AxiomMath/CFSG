module

public import CFSG.CGT.Timmesfeld75.CentralQuotient
public import CFSG.CGT.T75D.LayerBasic

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {H : Type*} [Group H] [Finite H]

theorem normalizer_eq_comap_of_isElemAbelian_map_mk_eq {Z : Subgroup H} [Z.Normal]
    (hZ : Z ≤ Subgroup.center H) (hZodd : Odd (Nat.card Z))
    {T : Subgroup H} (hT : IsElemAbelian 2 T) {Tbar : Subgroup (H ⧸ Z)}
    (hmap : T.map (QuotientGroup.mk' Z) = Tbar) :
    Subgroup.normalizer (T : Set H) =
      (Subgroup.normalizer (Tbar : Set (H ⧸ Z))).comap (QuotientGroup.mk' Z) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_comap]
    rw [mem_normalizer_iff_conjSubgroup_eq] at hx ⊢
    calc conjSubgroup (QuotientGroup.mk' Z x) Tbar
        = conjSubgroup (QuotientGroup.mk' Z x) (T.map (QuotientGroup.mk' Z)) := by rw [hmap]
      _ = (conjSubgroup x T).map (QuotientGroup.mk' Z) := (map_conjSubgroup _ _ _).symm
      _ = T.map (QuotientGroup.mk' Z) := by rw [hx]
      _ = Tbar := hmap
  · intro x hx
    rw [Subgroup.mem_comap] at hx
    rw [mem_normalizer_iff_conjSubgroup_eq] at hx ⊢
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro t ⟨t₀, ht₀, rfl⟩
      have htbar : (QuotientGroup.mk' Z) ((MulAut.conj x) t₀) ∈ Tbar := by
        have h1 : (MulAut.conj x) t₀ ∈ conjSubgroup x T :=
          Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom ht₀
        have h2 := Subgroup.mem_map_of_mem (QuotientGroup.mk' Z) h1
        rwa [map_conjSubgroup, hmap, hx] at h2
      obtain ⟨a, haT, ha⟩ := Subgroup.mem_map.mp (by rw [hmap]; exact htbar)
      have ht2 : ((MulAut.conj x) t₀) * ((MulAut.conj x) t₀) = 1 := by
        have h := hT.2 t₀ ht₀
        rw [pow_two] at h
        calc (MulAut.conj x) t₀ * (MulAut.conj x) t₀
            = (MulAut.conj x) (t₀ * t₀) := by rw [map_mul]
          _ = 1 := by rw [h, map_one]
      have ha2 : a * a = 1 := by
        have h := hT.2 a haT
        rwa [pow_two] at h
      have hta : (MulAut.conj x) t₀ = a :=
        (CFSG.CGT.T75D.eq_of_mk_eq Z (fun o ho y => Subgroup.mem_center_iff.mp (hZ ho) y) hZodd
          ha2 ht2 ha).symm
      change (MulAut.conj x) t₀ ∈ T
      rw [hta]
      exact haT
    · exact (card_conjSubgroup x T).ge

theorem weaklyClosedIn_of_map_mk_eq {Z : Subgroup H} [Z.Normal]
    (hZ : Z ≤ Subgroup.center H) (hZodd : Odd (Nat.card Z))
    {T : Subgroup H} (hT : IsElemAbelian 2 T) {Tbar : Subgroup (H ⧸ Z)}
    (hmap : T.map (QuotientGroup.mk' Z) = Tbar)
    (hwc : WeaklyClosedIn Tbar (Subgroup.normalizer (Tbar : Set (H ⧸ Z)))) :
    WeaklyClosedIn T (Subgroup.normalizer (T : Set H)) := by
  refine ⟨Subgroup.le_normalizer, ?_⟩
  intro x hx
  have hN := normalizer_eq_comap_of_isElemAbelian_map_mk_eq hZ hZodd hT hmap
  have hxN : x ∈ Subgroup.normalizer (T : Set H) := by
    rw [hN, Subgroup.mem_comap, mem_normalizer_iff_conjSubgroup_eq]
    refine hwc.2 (QuotientGroup.mk' Z x) ?_
    calc conjSubgroup (QuotientGroup.mk' Z x) Tbar
        = conjSubgroup (QuotientGroup.mk' Z x) (T.map (QuotientGroup.mk' Z)) := by rw [hmap]
      _ = (conjSubgroup x T).map (QuotientGroup.mk' Z) := (map_conjSubgroup _ _ _).symm
      _ ≤ (Subgroup.normalizer (T : Set H)).map (QuotientGroup.mk' Z) :=
          Subgroup.map_mono hx
      _ ≤ Subgroup.normalizer (Tbar : Set (H ⧸ Z)) := by
          rw [hN]
          exact Subgroup.map_comap_le _ _
  exact mem_normalizer_iff_conjSubgroup_eq.mp hxN

end CFSG.GroupTheory

end
