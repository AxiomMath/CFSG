module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78Str
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L771Act
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec7l771_sylow_N [Finite G] (h36 : Asc82Lemma36) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    IsSylow2Of (S ⊓ L) (L ⊓ normalizer (B : Set G)) := by
  have hle : S ⊓ L ≤ L ⊓ normalizer (B : Set G) :=
    le_inf inf_le_right
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hc.normalE16.1).mp hc.normalE16.2.2)
  refine ⟨hle, (hc.ctx.isSylow2Of_inf h36).2.1, ?_⟩
  intro h2
  have h := Subgroup.relIndex_mul_relIndex (S ⊓ L) (L ⊓ normalizer (B : Set G)) L hle
    inf_le_left
  exact (hc.ctx.isSylow2Of_inf h36).2.2 (h ▸ dvd_mul_of_dvd_left h2 _)

theorem sec7l771_z_facts [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    z ∈ B ∧ z ≠ 1 ∧ ∀ x ∈ S ⊓ L, x * z = z * x := by
  have hzB : z ∈ B :=
    hP.center_le G L hc.ctx.isOm6P (S ⊓ L) (hc.ctx.isSylow2Of_inf h36) B hc.normalE16
      hc.ctx.z_mem_centerIn
  refine ⟨hzB, ?_, fun x hx => hc.ctx.central x hx.1⟩
  intro hz1
  have h := hc.ctx.pocket.1
  rw [hz1, orderOf_one] at h
  norm_num at h

theorem sec7l771_ZP [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    ∀ y ∈ S ⊓ L, (∀ x ∈ S ⊓ L, x * y = y * x) → y = 1 ∨ y = z := by
  intro y hy hcomm
  have hyZ : y ∈ centerIn (S ⊓ L) :=
    Subgroup.mem_map.mpr ⟨⟨y, hy.1, hy.2⟩,
      Subgroup.mem_center_iff.mpr fun a => Subtype.ext (hcomm a.1 a.2), rfl⟩
  have hyB : y ∈ B :=
    hP.center_le G L hc.ctx.isOm6P (S ⊓ L) (hc.ctx.isSylow2Of_inf h36) B hc.normalE16 hyZ
  obtain ⟨φ, hφ⟩ := sec7l78_act_of_aut_B hP hc.ctx.isOm6P (hc.ctx.isSylow2Of_inf h36)
    hc.normalE16
  have hPN : IsSylow2Of (S ⊓ L) (L ⊓ normalizer (B : Set G)) := sec7l771_sylow_N h36 hc
  have hzB : z ∈ B := (sec7l771_z_facts h36 hP hc).1
  have hz1 : z ≠ 1 := (sec7l771_z_facts h36 hP hc).2.1
  have hzP : ∀ x ∈ S ⊓ L, x * z = z * x := (sec7l771_z_facts h36 hP hc).2.2
  exact (sec7l771_centralB hφ hPN hzB hz1 hzP).2 y hyB hcomm

theorem sec7l771_cent_s [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B)
    {ν : G} (hν : ν ∈ L ⊓ normalizer (B : Set G)) (hνz : ν * z = z * ν) :
    ν * (g⁻¹ * t * g) = (g⁻¹ * t * g) * ν := by
  have hs := sec7l78_sideL h36 h76 hP hc
  obtain ⟨u, huA, hucen, b, hbB, hs_eq⟩ :=
    Sec7L78Side.decomp hP hs (g⁻¹ * t * g) (sec7l78_s_mem_A hP h36 hc)
  have hbP : b ∈ S ⊓ L := hc.normalE16.1 hbB
  have hbcen : ∀ x ∈ S ⊓ L, x * b = b * x := by
    intro x hx
    have hxN : x ∈ L ⊓ normalizer (B : Set G) := (sec7l771_sylow_N h36 hc).1 hx
    have hux : x * u = u * x := (hucen x hxN).symm
    have hux' : x * u⁻¹ = u⁻¹ * x := ((commute_iff_eq x u).mpr hux).inv_right.eq
    have hsx : x * (g⁻¹ * t * g) = (g⁻¹ * t * g) * x := sec7l78_s_cent_P hc x hx
    have hb_eq : b = u⁻¹ * (g⁻¹ * t * g) := by rw [hs_eq]; group
    calc x * b = x * (u⁻¹ * (g⁻¹ * t * g)) := by rw [hb_eq]
      _ = (x * u⁻¹) * (g⁻¹ * t * g) := by group
      _ = (u⁻¹ * x) * (g⁻¹ * t * g) := by rw [hux']
      _ = u⁻¹ * (x * (g⁻¹ * t * g)) := by group
      _ = u⁻¹ * ((g⁻¹ * t * g) * x) := by rw [hsx]
      _ = (u⁻¹ * (g⁻¹ * t * g)) * x := by group
      _ = b * x := by rw [hb_eq]
  rcases sec7l771_ZP h36 hP hc b hbP hbcen with hb1 | hbz
  · rw [hb1, mul_one] at hs_eq
    rw [hs_eq]
    exact (hucen ν hν).symm
  · rw [hbz] at hs_eq
    have hνu : ν * u = u * ν := (hucen ν hν).symm
    calc ν * (g⁻¹ * t * g) = ν * (u * z) := by rw [hs_eq]
      _ = (ν * u) * z := by group
      _ = (u * ν) * z := by rw [hνu]
      _ = u * (ν * z) := by group
      _ = u * (z * ν) := by rw [hνz]
      _ = (u * z) * ν := by group
      _ = (g⁻¹ * t * g) * ν := by rw [hs_eq]

theorem sec7l771_z_type [Finite G] (hP : Asc82Tab6P) (hF : Asc82AutFacts) (h73 : Asc82Lemma73)
    {t : G} {L S : Subgroup G} {z : G} (hc : Sec7Ctx G t L S z) {g : G}
    (hzK : z ∈ CFSG.conjugate L g) (hzs : z * (g⁻¹ * t * g) = (g⁻¹ * t * g) * z) :
    IsI4PlusIn (CFSG.conjugate L g) z := by
  let K : Subgroup G := CFSG.conjugate L g
  have hK : IsOm6P K := isOm6P_conjugate hc.isOm6P g
  have hz2 : orderOf z = 2 := (sec7_z_type hF hc).1
  have hzN : z ∈ normalizer (K : Set G) := Subgroup.le_normalizer hzK
  have hinv := sec7_involution_types hP hK hzK hz2
  have hzC : z ∈ centralizer ({g⁻¹ * t * g} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzs
  have hsym := sec7_lemma73_sym h73 hc g (IsConj.refl z) hzC
  have h4 : InducesTypeSome K z 6 1 4 1 := by
    rcases hsym with ⟨α, h3⟩ | h4
    · rcases hinv with h4 | h2
      · exact h4
      · exact absurd (show ∃ α : ℤˣ, InducesTypeSome K z 6 1 3 α from ⟨α, h3⟩)
          (hP.excl G K hK z hz2 hzN 1 3 (by norm_num) (by norm_num) (by norm_num) h2)
    · exact h4
  exact (hF.pocket_P G K hK z hzK).mpr ⟨hz2, h4⟩

theorem sec7l771_card_A_b [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76)
    (hP : Asc82Tab6P) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) (hne : ¬ IsConj t (t * z))
    (hα : ∃ α : ℤˣ, InducesTypeSome L (g⁻¹ * t * g) 6 1 1 α) :
    64 ≤ Nat.card (ASub S B) := by
  classical
  let A : Subgroup G := ASub S B
  let B' : Subgroup ↥A := B.subgroupOf A
  have hBA : B ≤ A := sec7l77_B_le_A hc
  have hcommA := sec7l78_A_comm_sq h36 h76 hP hc
  haveI : IsMulCommutative ↥A :=
    isMulCommutative_iff.mpr fun a b => Subtype.ext (hcommA.1 a.1 a.2 b.1 b.2)
  have htA : t ∈ A := sec7l78_t_mem_A hc
  have hsA : g⁻¹ * t * g ∈ A := sec7l78_s_mem_A hP h36 hc
  have htsA : t * (g⁻¹ * t * g) ∈ A := A.mul_mem htA hsA
  let q : ↥A → ↥A ⧸ B' := QuotientGroup.mk
  have hq_mem : ∀ {x y : G} (hx : x ∈ A) (hy : y ∈ A),
      q ⟨x, hx⟩ = q ⟨y, hy⟩ → x⁻¹ * y ∈ B := by
    intro x y hx hy hxy
    have h := QuotientGroup.eq.mp hxy
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  have ht2 : t * t = 1 := by
    rw [← pow_two]
    simpa [hc.ctx.involution] using pow_orderOf_eq_one t
  have hs_ord : orderOf (g⁻¹ * t * g) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t
    simpa [MulAut.conj_apply, hc.ctx.involution] using h
  have hs2 : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    rw [← pow_two]
    simpa [hs_ord] using pow_orderOf_eq_one (g⁻¹ * t * g)
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hs_inv : (g⁻¹ * t * g)⁻¹ = g⁻¹ * t * g := inv_eq_of_mul_eq_one_right hs2
  have hcomm_ts : t * (g⁻¹ * t * g) = (g⁻¹ * t * g) * t :=
    hcommA.1 t htA (g⁻¹ * t * g) hsA
  have htB : t ∉ B := by
    intro htB
    have htL : t ∈ L := sec7l77_B_le_L hc htB
    have htZ : t ∈ centerIn L :=
      Subgroup.mem_map.mpr ⟨⟨t, htL⟩,
        Subgroup.mem_center_iff.mpr fun a => Subtype.ext
          (Subgroup.mem_centralizer_iff.mp hc.ctx.t_mem_centralizer a.1 a.2), rfl⟩
    have ht1 : t = 1 :=
      Subgroup.mem_bot.mp (by rwa [hP.center_triv G L hc.ctx.isOm6P] at htZ)
    have h := hc.ctx.involution
    rw [ht1, orderOf_one] at h
    norm_num at h
  have hsB : g⁻¹ * t * g ∉ B := by
    intro hsB
    have hsL : g⁻¹ * t * g ∈ L := sec7l77_B_le_L hc hsB
    have hs2' : orderOf (g⁻¹ * t * g) = 2 := hs_ord
    have hN : g⁻¹ * t * g ∈ normalizer (L : Set G) := Subgroup.le_normalizer hsL
    rcases sec7_involution_types hP hc.ctx.isOm6P hsL hs2' with h4 | h2
    · exact (hP.excl G L hc.ctx.isOm6P _ hs2' hN 0 2 (by norm_num) (by norm_num)
        (by norm_num) h4) hα
    · exact (hP.excl G L hc.ctx.isOm6P _ hs2' hN 1 2 (by norm_num) (by norm_num)
        (by norm_num) h2) hα
  have htsB : t * (g⁻¹ * t * g) ∉ B := by
    intro htsB
    have hbP : t * (g⁻¹ * t * g) ∈ S ⊓ L :=
      ⟨sec7l77_B_le_S hc htsB, sec7l77_B_le_L hc htsB⟩
    have hbcent : ∀ x ∈ S ⊓ L,
        x * (t * (g⁻¹ * t * g)) = (t * (g⁻¹ * t * g)) * x := by
      intro x hx
      have hxt : x * t = t * x :=
        Subgroup.mem_centralizer_singleton_iff.mp (hc.ctx.le_centralizer hx.2)
      have hxs : x * (g⁻¹ * t * g) = (g⁻¹ * t * g) * x := sec7l78_s_cent_P hc x hx
      calc x * (t * (g⁻¹ * t * g)) = (x * t) * (g⁻¹ * t * g) := by group
        _ = (t * x) * (g⁻¹ * t * g) := by rw [hxt]
        _ = t * (x * (g⁻¹ * t * g)) := by group
        _ = t * ((g⁻¹ * t * g) * x) := by rw [hxs]
        _ = (t * (g⁻¹ * t * g)) * x := by group
    rcases sec7l771_ZP h36 hP hc (t * (g⁻¹ * t * g)) hbP hbcent with hb1 | hbz
    · have hs_eq_t : g⁻¹ * t * g = t := by
        calc g⁻¹ * t * g = 1 * (g⁻¹ * t * g) := (one_mul _).symm
          _ = (t * t) * (g⁻¹ * t * g) := by rw [ht2]
          _ = t * (t * (g⁻¹ * t * g)) := by group
          _ = t * 1 := by rw [hb1]
          _ = t := mul_one t
      exact hc.s_ne hs_eq_t
    · have hs_eq_tz : g⁻¹ * t * g = t * z := by
        calc g⁻¹ * t * g = 1 * (g⁻¹ * t * g) := (one_mul _).symm
          _ = (t * t) * (g⁻¹ * t * g) := by rw [ht2]
          _ = t * (t * (g⁻¹ * t * g)) := by group
          _ = t * z := by rw [hbz]
      have hconj : IsConj t (t * z) := by
        refine isConj_iff_inv_mul.mpr ⟨g, ?_⟩
        exact hs_eq_tz
      exact hne hconj
  have h01 : q ⟨1, A.one_mem⟩ ≠ q ⟨t, htA⟩ := by
    intro h
    exact htB (by simpa using hq_mem A.one_mem htA h)
  have h02 : q ⟨1, A.one_mem⟩ ≠ q ⟨g⁻¹ * t * g, hsA⟩ := by
    intro h
    exact hsB (by simpa using hq_mem A.one_mem hsA h)
  have h03 : q ⟨1, A.one_mem⟩ ≠ q ⟨t * (g⁻¹ * t * g), htsA⟩ := by
    intro h
    exact htsB (by simpa using hq_mem A.one_mem htsA h)
  have h12 : q ⟨t, htA⟩ ≠ q ⟨g⁻¹ * t * g, hsA⟩ := by
    intro h
    have hmem := hq_mem htA hsA h
    rw [ht_inv] at hmem
    exact htsB hmem
  have h13 : q ⟨t, htA⟩ ≠ q ⟨t * (g⁻¹ * t * g), htsA⟩ := by
    intro h
    have hmem := hq_mem htA htsA h
    have hs_eq : t⁻¹ * (t * (g⁻¹ * t * g)) = g⁻¹ * t * g := by
      rw [← mul_assoc, inv_mul_cancel, one_mul]
    rw [hs_eq] at hmem
    exact hsB hmem
  have h23 : q ⟨g⁻¹ * t * g, hsA⟩ ≠ q ⟨t * (g⁻¹ * t * g), htsA⟩ := by
    intro h
    have hmem := hq_mem hsA htsA h
    have ht_eq : (g⁻¹ * t * g)⁻¹ * (t * (g⁻¹ * t * g)) = t := by
      rw [hs_inv]
      calc (g⁻¹ * t * g) * (t * (g⁻¹ * t * g))
          = ((g⁻¹ * t * g) * t) * (g⁻¹ * t * g) := by group
        _ = (t * (g⁻¹ * t * g)) * (g⁻¹ * t * g) := by rw [hcomm_ts]
        _ = t * ((g⁻¹ * t * g) * (g⁻¹ * t * g)) := by group
        _ = t * 1 := by rw [hs2]
        _ = t := mul_one t
    rw [ht_eq] at hmem
    exact htB hmem
  have h4 : 4 ≤ B'.index := by
    letI : Fintype (↥A ⧸ B') := Fintype.ofFinite _
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    let f : Fin 4 → ↥A ⧸ B' :=
      ![q ⟨1, A.one_mem⟩, q ⟨t, htA⟩, q ⟨g⁻¹ * t * g, hsA⟩,
        q ⟨t * (g⁻¹ * t * g), htsA⟩]
    have hinj : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [f]
    simpa using Fintype.card_le_of_injective f hinj
  have hcardB'B : Nat.card B' = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv
  have hcardB : Nat.card B = 16 := by
    rw [hc.normalE16.2.1.2]
    norm_num
  calc 64 = 4 * 16 := by norm_num
    _ ≤ B'.index * Nat.card B' := Nat.mul_le_mul h4 (le_of_eq (hcardB'B.trans hcardB).symm)
    _ = Nat.card ↥A := Subgroup.index_mul_card B'
    _ = Nat.card A := rfl

end CFSG.OddStandard.SmallF3.Omega
