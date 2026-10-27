module

public import CFSG.LargeExtraspecial.S14SMJH
public import CFSG.LargeExtraspecial.S14SMIMain
public import CFSG.LargeExtraspecial.S14SMJDim
public import CFSG.LargeExtraspecial.S14SMJDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMJ

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_theta_t {t u : G} (htt : t * t = 1) (huu : u * u = 1) (h3 : (t * u) ^ 3 = 1) :
    t * u * t * (t * u)⁻¹ = u := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have h3' : t * u * (t * u) * (t * u) = 1 := by rw [← h3, pow_succ, sq]
  calc t * u * t * (t * u)⁻¹ = t * u * t * u⁻¹ * t⁻¹ := by group
    _ = t * u * t * u * t := by rw [hti, hui]
    _ = t * u * (t * u) * (t * u) * u⁻¹ := by group
    _ = u := by rw [h3', one_mul, hui]

theorem mem_Qt_or
    (hM : SmithE22Module) [IsSimpleGroup G] (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {g c : G} (htM : g * S.z * g⁻¹ ∈ S.M)
    (htQ : g * S.z * g⁻¹ ∉ S.QG) (hc : IsConj S.z c) (hcQ : c ∈ S.QG) (hcz : c ≠ S.z)
    (hct : Commute c (g * S.z * g⁻¹)) :
    g⁻¹ * c * g ∈ S.QG ∨ g⁻¹ * (S.z * c) * g ∈ S.QG := by
  by_cases hb : g⁻¹ * c * g ∈ S.QG
  · exact Or.inl hb
  right
  have hzc : IsConj S.z (S.z * c) := by
    obtain ⟨q, -, hq⟩ := SME.exists_conj_eq_mul_z S hcQ (SME.ne_one_of_isConj S hc) hcz
    refine hc.trans (isConj_iff.mpr ⟨q, ?_⟩)
    rw [hq]
    exact S.z_comm_QG hcQ
  have h := SMI.mul_mem_QG hM S hw hU (a := g⁻¹ * S.z * g) (b := g⁻¹ * c * g)
    (SmithGraph.isConj_conj (IsConj.refl _) g) (SmithGraph.isConj_conj hc g)
    ((SME.mem_M_conj_iff S g S.z).mpr (S.z_comm htM).symm) ((SME.mem_M_conj_iff S g c).mpr hct)
    (SMF.conj_z_not_mem_QG S htQ) hb (commute_conj g (S.z_comm_QG hcQ).symm)
    (by
      rw [show g⁻¹ * S.z * g * (g⁻¹ * c * g) = g⁻¹ * (S.z * c) * g by group]
      exact SmithGraph.isConj_conj hzc g)
  rwa [show g⁻¹ * S.z * g * (g⁻¹ * c * g) = g⁻¹ * (S.z * c) * g by group] at h

theorem isConj_z_mul (S : Setting G) {c : G} (hc : IsConj S.z c) (hcQ : c ∈ S.QG)
    (hcz : c ≠ S.z) : IsConj S.z (S.z * c) := by
  obtain ⟨q, -, hq⟩ := SME.exists_conj_eq_mul_z S hcQ (SME.ne_one_of_isConj S hc) hcz
  refine hc.trans (isConj_iff.mpr ⟨q, ?_⟩)
  rw [hq]
  exact S.z_comm_QG hcQ

theorem eq_z_of_mem_cent2
    (hM : SmithE22Module) [IsSimpleGroup G] (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {t u : G} (C : Cfg S t u) {c : G}
    (hc : IsConj S.z c) (hcQ : c ∈ S.QG) (hcH : c ∈ cent2 t u) : c = S.z := by
  by_contra hcz
  have htt : t * t = 1 := SmithQ.mul_self_eq_one_of_isConj S C.ht
  have huu : u * u = 1 := SmithQ.mul_self_eq_one_of_isConj S C.hu
  have h3p : (t * u) ^ 3 = 1 := by rw [← C.h3]; exact pow_orderOf_eq_one _
  have hzH := z_mem_cent2 S C.htM C.huM
  obtain ⟨g, hg⟩ := isConj_iff.mp C.ht
  obtain ⟨e, he, heQ, heH, heQt⟩ : ∃ e : G, IsConj S.z e ∧ e ∈ S.QG ∧ e ∈ cent2 t u ∧
      g⁻¹ * e * g ∈ S.QG := by
    rcases mem_Qt_or hM S hw hU (hg ▸ C.htM) (hg ▸ C.htQ) hc hcQ hcz
      (hg ▸ (mem_cent2.mp hcH).1) with h | h
    · exact ⟨c, hc, hcQ, hcH, h⟩
    · exact ⟨S.z * c, isConj_z_mul S hc hcQ hcz, S.QG.mul_mem S.z_mem_QG hcQ,
        mul_mem hzH hcH, h⟩
  obtain ⟨k, rfl⟩ := isConj_iff.mp he
  have htQe : k⁻¹ * t * k ∈ S.QG := by
    have h := SME.mem_Qa_symm S (g := g) (k := k) heQt (by rw [hg]; exact fun h => C.htQ (h ▸ heQ))
    rwa [hg] at h
  set θ := t * u with hθ
  have hθt : θ * t * θ⁻¹ = u := conj_theta_t htt huu h3p
  have hu' : (θ * g) * S.z * (θ * g)⁻¹ = u := by
    rw [← hθt, ← hg]
    group
  have heθ : θ⁻¹ * (k * S.z * k⁻¹) * θ = k * S.z * k⁻¹ := by
    obtain ⟨het, heu⟩ := mem_cent2.mp heH
    have hc' : Commute (k * S.z * k⁻¹) θ := het.mul_right heu
    calc θ⁻¹ * (k * S.z * k⁻¹) * θ = θ⁻¹ * ((k * S.z * k⁻¹) * θ) := by group
      _ = θ⁻¹ * (θ * (k * S.z * k⁻¹)) := by rw [hc'.eq]
      _ = k * S.z * k⁻¹ := by group
  have heQu : (θ * g)⁻¹ * (k * S.z * k⁻¹) * (θ * g) ∈ S.QG := by
    rw [show (θ * g)⁻¹ * (k * S.z * k⁻¹) * (θ * g) = g⁻¹ * (θ⁻¹ * (k * S.z * k⁻¹) * θ) * g by
      group, heθ]
    exact heQt
  have huQe : k⁻¹ * u * k ∈ S.QG := by
    have h := SME.mem_Qa_symm S (g := θ * g) (k := k) heQu
      (by rw [hu']; exact fun h => C.huQ (h ▸ heQ))
    rwa [hu'] at h
  refine mul_not_mem_QG S (t := k⁻¹ * t * k) (u := k⁻¹ * u * k) ?_ (S.QG.mul_mem htQe huQe)
  rw [show k⁻¹ * t * k * (k⁻¹ * u * k) = k⁻¹ * (t * u) * k by group, orderOf_kconj]
  exact C.h3

theorem Loc.of
    (hM : SmithE22Module) (hLoc : SmithE23a) [IsSimpleGroup G]
    {S : Setting G} (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {t u : G}
    (C : Cfg S t u) : Loc S t u := by
  obtain ⟨h2, h3, h4, ⟨y, hy, hyM, hyQ, hyt, hyu⟩⟩ :=
    hLoc G S hw hU t u C.ht C.hu C.htM C.huM C.htQ C.huQ C.h3
  refine ⟨card_cent2_ge hM (smithE25_of hM) (smithE34a_of_module hM) S hw hU C.ht C.hu C.htM
    C.huM C.htQ C.huQ C.h3, ?_, ?_, ?_, ⟨y, hy, hyM, hyQ, mem_cent2.mpr ⟨hyt, hyu⟩⟩,
    fun c hc hcQ hcH => eq_z_of_mem_cent2 hM S hw hU C hc hcQ hcH⟩
  · intro c hcH hcM hcq
    obtain ⟨hct, hcu⟩ := mem_cent2.mp hcH
    exact h2 c hcM hct hcu fun q hq hqt hqu => hcq q (mem_inf.mpr ⟨hq, mem_cent2.mpr ⟨hqt, hqu⟩⟩)
  · intro P hP hPn hP2
    refine h3 P (fun p hp => (hP hp).2) (fun p hp => mem_cent2.mp (hP hp).1) ?_ hP2
    intro c hcM hct hcu p hp
    exact hPn c (mem_inf.mpr ⟨mem_cent2.mpr ⟨hct, hcu⟩, hcM⟩) p hp
  · intro R hzR hR hRn
    rcases h4 R hzR (fun r hr => (hR hr).1) (fun r hr => mem_cent2.mp (hR hr).2)
      (fun c hcM hct hcu r hr => hRn c (mem_inf.mpr ⟨mem_cent2.mpr ⟨hct, hcu⟩, hcM⟩) r hr)
      with h | h
    · exact Or.inl h
    · refine Or.inr fun q hq => ?_
      obtain ⟨hqQ, hqH⟩ := mem_inf.mp hq
      exact h q hqQ (mem_cent2.mp hqH).1 (mem_cent2.mp hqH).2

end CFSG.LargeExtraspecial.S14.SMJ
