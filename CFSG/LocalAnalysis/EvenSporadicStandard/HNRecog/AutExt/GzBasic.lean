module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.IsoOn
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Qz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Extraspecial.Quotient

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'}

theorem IsIsoOn.mem_Qz_iff {φ : G → G'} {w : G} {w' : G'} (hφ : IsIsoOn (Gx w) (Gx w') φ)
    {x : G} (hx : x ∈ Gx w) : x ∈ Qz w ↔ φ x ∈ Qz w' := by
  let e : ↥(Gx w) ≃* ↥(Gx w') := hφ.toMulEquiv
  have he : ∀ u : ↥(Gx w), (e u : G') = φ u := fun u => hφ.toMulEquiv_apply u
  constructor
  · intro hxQ
    change x ∈ (CFSG.pCore 2 ↥(Gx w)).map (Gx w).subtype at hxQ
    change φ x ∈ (CFSG.pCore 2 ↥(Gx w')).map (Gx w').subtype
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxQ
    refine Subgroup.mem_map.mpr ⟨e y, ?_, ?_⟩
    · rw [← CFSG.pCore_map_iso 2 e]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hy
    · change (e y : G') = φ x
      rw [he y]
      exact congrArg φ hyx
  · intro hxQ
    change φ x ∈ (CFSG.pCore 2 ↥(Gx w')).map (Gx w').subtype at hxQ
    change x ∈ (CFSG.pCore 2 ↥(Gx w)).map (Gx w).subtype
    obtain ⟨y', hy', hy'x⟩ := Subgroup.mem_map.mp hxQ
    have hy'mem : (⟨φ x, hφ.mem x hx⟩ : ↥(Gx w')) ∈ CFSG.pCore 2 ↥(Gx w') := by
      have h : y' = ⟨φ x, hφ.mem x hx⟩ := Subtype.ext hy'x
      rw [h] at hy'
      exact hy'
    have hsym : e.symm ⟨φ x, hφ.mem x hx⟩ ∈ CFSG.pCore 2 ↥(Gx w) := by
      rw [← CFSG.pCore_map_iso 2 e.symm]
      exact Subgroup.mem_map_of_mem e.symm.toMonoidHom hy'mem
    refine Subgroup.mem_map.mpr ⟨e.symm ⟨φ x, hφ.mem x hx⟩, hsym, ?_⟩
    apply hφ.injOn _ (e.symm ⟨φ x, hφ.mem x hx⟩).2 x hx
    rw [← he (e.symm ⟨φ x, hφ.mem x hx⟩)]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨φ x, hφ.mem x hx⟩)

theorem eq_one_or_eq_of_central_Gz (h : F5Std a z) {g : G} (hg : g ∈ Gx z)
    (hc : ∀ x ∈ Gx z, g * x = x * g) : g = 1 ∨ g = z := by
  obtain ⟨Q, hQn, hAH⟩ := h.loc.gz9.self.aschbacher
  haveI : Q.Normal := hQn
  have hE : IsExtraspecialPGroup 2 Q := hAH.plus.isExtraspecialPGroup
  let u : Q := ⟨⟨g, hg⟩, hAH.centralizer_le (by
    rw [Subgroup.mem_centralizer_iff]
    intro e _
    exact Subtype.ext (hc (e : G) e.2).symm)⟩
  let v : Q := ⟨GxSelf z, hAH.centralizer_le (by
    rw [Subgroup.mem_centralizer_iff]
    intro e _
    exact Subtype.ext (mem_Gx.mp e.2).symm)⟩
  have hu : u ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact (hc ((y : ↥(Gx z)) : G) (y : ↥(Gx z)).2).symm
  have hv : v ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact (mem_Gx.mp (y : ↥(Gx z)).2).symm
  have hv1 : v ≠ 1 := by
    intro hv1
    have hzval : z = 1 := by
      have h := congrArg (fun t : Q => (t : G)) hv1
      have hvG : ((v : Q) : G) = z := rfl
      have h1G : (((1 : Q) : G)) = (1 : G) := rfl
      simpa only [hvG, h1G] using h
    have h2 := h.typ.orderOf_z
    rw [hzval, orderOf_one] at h2
    omega
  rcases eq_or_ne g 1 with hg1 | hg1
  · exact Or.inl hg1
  · right
    have hu1 : u ≠ 1 := by
      intro hu1
      apply hg1
      have h := congrArg (fun t : Q => (t : G)) hu1
      have huG : ((u : Q) : G) = g := rfl
      have h1G : (((1 : Q) : G)) = (1 : G) := rfl
      simpa only [huG, h1G] using h
    have huv := CFSG.RankThree.Literature.FSmith.eq_of_mem_center hE hu hv hu1 hv1
    have h := congrArg (fun t : Q => (t : G)) huv
    have huG : ((u : Q) : G) = g := rfl
    have hvG : ((v : Q) : G) = z := rfl
    simpa only [huG, hvG] using h

theorem sq_mem_Qz (h : F5Std a z) {q : G} (hq : q ∈ Qz z) : q ^ 2 = 1 ∨ q ^ 2 = z := by
  haveI : Finite G := h.finite
  obtain ⟨Q, hQn, hAH⟩ := h.loc.gz9.self.aschbacher
  haveI : Q.Normal := hQn
  have hE : IsExtraspecialPGroup 2 Q := hAH.plus.isExtraspecialPGroup
  have hQz : Qz z = Q.map (Gx z).subtype := by
    change (CFSG.pCore 2 ↥(Gx z)).map (Gx z).subtype = Q.map (Gx z).subtype
    rw [CFSG.EvenSporadicStandard.HNRecog.Section3.IsExtraspecialPlusByA5WrTwoWith.pCore_eq
      hAH.toIsExtraspecialPlusByA5WrTwoWith]
  rw [hQz] at hq
  obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.mp hq
  let w : Q := (⟨y, hy⟩ : Q) ^ 2
  have hw : w ∈ Subgroup.center Q := CFSG.RankThree.Literature.FSmith.sq_mem_center hE ⟨y, hy⟩
  let v : Q := ⟨GxSelf z, hAH.centralizer_le (by
    rw [Subgroup.mem_centralizer_iff]
    intro e _
    exact Subtype.ext (mem_Gx.mp e.2).symm)⟩
  have hv : v ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro e
    apply Subtype.ext
    apply Subtype.ext
    exact (mem_Gx.mp (e : ↥(Gx z)).2).symm
  have hv1 : v ≠ 1 := by
    intro hv1
    have hzval : z = 1 := by
      have h := congrArg (fun t : Q => (t : G)) hv1
      have hvG : ((v : Q) : G) = z := rfl
      have h1G : (((1 : Q) : G)) = (1 : G) := rfl
      simpa only [hvG, h1G] using h
    have h2 := h.typ.orderOf_z
    rw [hzval, orderOf_one] at h2
    omega
  have hsqval : ((w : ↥(Gx z)) : G) = q ^ 2 := by
    change (y : G) ^ 2 = q ^ 2
    exact congrArg (fun t : G => t ^ 2) hyq
  have hvval : ((v : ↥(Gx z)) : G) = z := rfl
  rcases eq_or_ne w 1 with hw1 | hw1
  · left
    have : ((w : ↥(Gx z)) : G) = 1 := by rw [hw1]; rfl
    rw [← hsqval, this]
  · right
    have hwv : w = v := CFSG.RankThree.Literature.FSmith.eq_of_mem_center hE hw hv hw1 hv1
    have : ((w : ↥(Gx z)) : G) = z := by rw [hwv]; exact hvval
    rw [← hsqval, this]

theorem iso_apply_self_Gz (h : F5Std a z) (h' : F5Std a' z') {φ : G → G'}
    (hφ : IsIsoOn (Gx z) (Gx z') φ) : φ z = z' := by
  have hz : z ∈ Gx z := self_mem_Gx z
  have hc : ∀ y ∈ Gx z', φ z * y = y * φ z := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hφ.surjOn y hy
    rw [← hφ.map_mul _ hz _ hx, ← hφ.map_mul _ hx _ hz, mem_Gx.mp hx]
  rcases eq_one_or_eq_of_central_Gz h' (hφ.mem z hz) hc with h1 | h1
  · exfalso
    have h2 := hφ.orderOf_eq hz
    rw [h1, orderOf_one, h.typ.orderOf_z] at h2
    omega
  · exact h1

end CFSG.EvenSporadicStandard.HNRecog.Section4
