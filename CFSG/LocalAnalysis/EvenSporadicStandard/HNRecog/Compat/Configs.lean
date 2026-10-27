module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpCfgFour
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpCfgS7
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpCfgTrans
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpCfgTrans2

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

private theorem isConj_conj' {c x : G} (hx : IsConj c x) (g : G) : IsConj c (g * x * g⁻¹) :=
  hx.trans (isConj_iff.2 ⟨g, rfl⟩)

private theorem eq_conj_inv_of {g t s : G} (h : g * t * g⁻¹ = s) : t = g⁻¹ * s * g := by
  rw [← h]; group

private theorem mem_Gx_conj_inv {g t s x : G} (hgt : g * t * g⁻¹ = s) (hx : x ∈ Gx s) :
    g⁻¹ * x * g ∈ Gx t := by
  rw [mem_Gx] at hx ⊢
  have ht : t = g⁻¹ * s * g := eq_conj_inv_of hgt
  rw [ht]
  calc (g⁻¹ * s * g) * (g⁻¹ * x * g) = g⁻¹ * (s * x) * g := by group
    _ = g⁻¹ * (x * s) * g := by rw [hx]
    _ = (g⁻¹ * x * g) * (g⁻¹ * s * g) := by group

private theorem mem_Gxy_conj_inv {g t t' s s' x : G}
    (hgt : g * t * g⁻¹ = s) (hgt' : g * t' * g⁻¹ = s') (hx : x ∈ Gxy s s') :
    g⁻¹ * x * g ∈ Gxy t t' := by
  rw [mem_Gxy] at hx ⊢
  exact ⟨mem_Gx_conj_inv hgt hx.1, mem_Gx_conj_inv hgt' hx.2⟩

private theorem conj_inv_eq_self_of_mem_Gx {g : G} (hg : g ∈ Gx a) : g⁻¹ * a * g = a := by
  have h1 : a * g = g * a := mem_Gx.1 hg
  calc g⁻¹ * a * g = g⁻¹ * (a * g) := by group
    _ = g⁻¹ * (g * a) := by rw [h1]
    _ = a := by group

private theorem mem_orb3A_conj_inv (h : F5Std a z) {g x : G} (hg : g ∈ Gx a)
    (hx : x ∈ orb3A a a) : g⁻¹ * x * g ∈ orb3A a a := by
  have hginv : g⁻¹ ∈ Gx a := (Gx a).inv_mem hg
  have hmem := h.loc.s7.self.orbit.conj_mem g⁻¹ hginv x hx
  simpa using hmem

private theorem mem_orb4B_conj_inv (h : F5Std a z) {g x : G} (hg : g ∈ Gx a)
    (hx : x ∈ orb4B a a) : g⁻¹ * x * g ∈ orb4B a a := by
  have hginv : g⁻¹ ∈ Gx a := (Gx a).inv_mem hg
  have hmem := (h.loc.tableV.self.partition.orbit 3).conj_mem g⁻¹ hginv x
    (by simpa [tab5Set] using hx)
  simpa [tab5Set] using hmem

private theorem mem_orb4A_conj_inv (h : F5Std a z) {g x : G} (hg : g ∈ Gx a)
    (hx : x ∈ orb4A a z a) : g⁻¹ * x * g ∈ orb4A a z a := by
  have hginv : g⁻¹ ∈ Gx a := (Gx a).inv_mem hg
  have hmem := (h.loc.tableV.self.partition.orbit 2).conj_mem g⁻¹ hginv x
    (by simpa [tab5Set] using hx)
  simpa [tab5Set] using hmem

theorem config_ABBB (h : F5Std a z) {t t' : G} (ht : t ∈ orb2A a a) (ht' : t' ∈ orb2B a z a)
    (htt : t * t' ∈ orb2BB a z a) : ∃ x ∈ orb3A a a, x ∈ Gxy t t' := by
  obtain ⟨s, s', x, hs, hs', hss, hx, hxs⟩ := cp_s7_pair_ABBB h
  obtain ⟨g, hg, hgt, hgt'⟩ := cp_pairs_ABBB h ht ht' htt hs hs' hss
  exact ⟨g⁻¹ * x * g, mem_orb3A_conj_inv h hg hx, mem_Gxy_conj_inv hgt hgt' hxs⟩

theorem config_BBB (h : F5Std a z) {t t' : G} (ht : t ∈ orb2B a z a) (ht' : t' ∈ orb2B a z a)
    (htt : t * t' ∈ orb2B a z a) : ∃ x ∈ orb3A a a, x ∈ Gxy t t' := by
  obtain ⟨s, s', x, hs, hs', hss, hx, hxs⟩ := cp_s7_pair_BBB h
  obtain ⟨g, hg, hgt, hgt'⟩ := cp_pairs_BBB h ht ht' htt hs hs' hss
  exact ⟨g⁻¹ * x * g, mem_orb3A_conj_inv h hg hx, mem_Gxy_conj_inv hgt hgt' hxs⟩

theorem config_AAAB (h : F5Std a z) {t t' : G} (ht : t ∈ orb2A a a) (ht' : t' ∈ orb2A a a)
    (htt : t * t' ∈ orb2AB a z a) :
    (∃ x ∈ orb4B a a, x ∈ Gxy t t') ∧
      ∃ y ∈ orb4A a z a, y ∈ Gxy t t' ∧ t ∈ orb2A a y ∧ t' ∈ orb2A a y ∧ t * t' = (a * y) ^ 2 := by
  constructor
  · obtain ⟨s, s', x, hs, hs', hss, hx, hxs⟩ := cp_four_pair_B h
    obtain ⟨g, hg, hgt, hgt'⟩ := cp_pairs_AAAB h ht ht' htt hs hs' hss
    exact ⟨g⁻¹ * x * g, mem_orb4B_conj_inv h hg hx, mem_Gxy_conj_inv hgt hgt' hxs⟩
  · obtain ⟨s, s', y, hs, hs', hss, hy, hys, hs2A, hs'2A, hss_eq⟩ := cp_four_pair_A h
    obtain ⟨g, hg, hgt, hgt'⟩ := cp_pairs_AAAB h ht ht' htt hs hs' hss
    have hgai : g⁻¹ * a * g = a := conj_inv_eq_self_of_mem_Gx hg
    have ht_eq : t = g⁻¹ * s * g := eq_conj_inv_of hgt
    have ht'_eq : t' = g⁻¹ * s' * g := eq_conj_inv_of hgt'
    refine ⟨g⁻¹ * y * g, mem_orb4A_conj_inv h hg hy, mem_Gxy_conj_inv hgt hgt' hys,
      ?_, ?_, ?_⟩
    · refine ⟨ht.1, ?_⟩
      have e : (g⁻¹ * y * g) * t = g⁻¹ * (y * s) * g := by rw [ht_eq]; group
      rw [e]
      simpa using isConj_conj' hs2A.2 g⁻¹
    · refine ⟨ht'.1, ?_⟩
      have e : (g⁻¹ * y * g) * t' = g⁻¹ * (y * s') * g := by rw [ht'_eq]; group
      rw [e]
      simpa using isConj_conj' hs'2A.2 g⁻¹
    · have hay : a * (g⁻¹ * y * g) = g⁻¹ * (a * y) * g := by
        calc a * (g⁻¹ * y * g) = (g⁻¹ * a * g) * (g⁻¹ * y * g) := by rw [hgai]
          _ = g⁻¹ * (a * y) * g := by group
      have hsq : (a * (g⁻¹ * y * g)) ^ 2 = g⁻¹ * (a * y) ^ 2 * g := by
        rw [hay]
        simpa using conj_pow (a := g⁻¹) (b := a * y) (i := 2)
      calc t * t' = (g⁻¹ * s * g) * (g⁻¹ * s' * g) := by rw [ht_eq, ht'_eq]
        _ = g⁻¹ * (s * s') * g := by group
        _ = g⁻¹ * (a * y) ^ 2 * g := by rw [hss_eq]
        _ = (a * (g⁻¹ * y * g)) ^ 2 := hsq.symm

end CFSG.EvenSporadicStandard.HNRecog.Section4