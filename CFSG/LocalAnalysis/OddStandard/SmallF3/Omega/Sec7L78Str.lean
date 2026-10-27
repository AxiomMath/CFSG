module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78Side
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L77Str
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Statements

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec7l78_comm_of_quot_mem [Finite G] (h76 : Asc82Lemma76)
    {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) {u v : G}
    (huS : u ∈ S) (hvcent : v ∈ centralizer ({t} : Set G))
    (hvB : ∀ b ∈ B, v * b = b * v)
    (hquot : ∃ b ∈ B, u * b⁻¹ ∈ centralizer (L : Set G)) : u * v = v * u := by
  obtain ⟨b, hbB, hbC⟩ := hquot
  have hbS : b ∈ S := sec7l77_B_le_S hc hbB
  have hubS : u * b⁻¹ ∈ S := S.mul_mem huS (S.inv_mem hbS)
  have hmem : u * b⁻¹ ∈ zpowers t := by
    have h : u * b⁻¹ ∈ S ⊓ centralizer (L : Set G) := ⟨hubS, hbC⟩
    rwa [← h76 G t L S z hc.ctx] at h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hu_eq : u = t ^ k * b := by rw [hk]; group
  have hvt : v * t = t * v := Subgroup.mem_centralizer_singleton_iff.mp hvcent
  have htk_v : t ^ k * v = v * t ^ k := Commute.zpow_left hvt.symm k
  have hbv : b * v = v * b := (hvB b hbB).symm
  calc u * v = (t ^ k * b) * v := by rw [hu_eq]
    _ = t ^ k * (b * v) := by group
    _ = t ^ k * (v * b) := by rw [hbv]
    _ = (t ^ k * v) * b := by group
    _ = (v * t ^ k) * b := by rw [htk_v]
    _ = v * (t ^ k * b) := by group
    _ = v * u := by rw [hu_eq]

private theorem sec7l78_gens_comm [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76)
    (hP : Asc82Tab6P) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) {x y : G}
    (hx : x ∈ S ⊓ centralizer (B : Set G) ∧ x ^ 2 = 1)
    (hy : y ∈ S ⊓ centralizer (B : Set G) ∧ y ^ 2 = 1) : x * y = y * x := by
  have hxS : x ∈ S := hx.1.1
  have hyS : y ∈ S := hy.1.1
  have hxB : ∀ b ∈ B, x * b = b * x :=
    fun b hb => (Subgroup.mem_centralizer_iff.mp hx.1.2 b hb).symm
  have hyB : ∀ b ∈ B, y * b = b * y :=
    fun b hb => (Subgroup.mem_centralizer_iff.mp hy.1.2 b hb).symm
  have hxN : x ∈ normalizer (L : Set G) :=
    hc.ctx.cent_le_normalizer h36 x (hc.ctx.sylow.1 hxS)
  have hyN : y ∈ normalizer (L : Set G) :=
    hc.ctx.cent_le_normalizer h36 y (hc.ctx.sylow.1 hyS)
  have hxt : x ∈ centralizer ({t} : Set G) := hc.ctx.sylow.1 hxS
  have hyt : y ∈ centralizer ({t} : Set G) := hc.ctx.sylow.1 hyS
  by_cases hA : ∃ b ∈ B, x * b⁻¹ ∈ centralizer (L : Set G)
  · exact sec7l78_comm_of_quot_mem h76 hc hxS hyt hyB hA
  · push Not at hA
    by_cases hB : ∃ b ∈ B, y * b⁻¹ ∈ centralizer (L : Set G)
    · exact (sec7l78_comm_of_quot_mem h76 hc hyS hxt hxB hB).symm
    · push Not at hB
      obtain ⟨b, hbB, hbC⟩ := hP.cent_B_index G L hc.ctx.isOm6P (S ⊓ L)
        (hc.ctx.isSylow2Of_inf h36) B hc.normalE16 x y hxN hyN hxB hyB hA hB
      have hx2 : x * x = 1 := by rw [← pow_two]; exact hx.2
      have hy2 : y * y = 1 := by rw [← pow_two]; exact hy.2
      have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
      have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
      have hbS : b ∈ S := sec7l77_B_le_S hc hbB
      have hxyS : x * y⁻¹ ∈ S := S.mul_mem hxS (S.inv_mem hyS)
      have hmem : x * y⁻¹ * b⁻¹ ∈ zpowers t := by
        have h : x * y⁻¹ * b⁻¹ ∈ S ⊓ centralizer (L : Set G) :=
          ⟨S.mul_mem hxyS (S.inv_mem hbS), hbC⟩
        rwa [← h76 G t L S z hc.ctx] at h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hxy_eq : x * y⁻¹ = t ^ k * b := by rw [hk]; group
      have hb2 : b * b = 1 := by
        rw [← pow_two]
        exact hc.normalE16.2.1.1.2 b hbB
      have htb : b * t = t * b :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (hc.ctx.le_centralizer (sec7l77_B_le_L hc hbB))
      have hbk : b * t ^ k = t ^ k * b := Commute.zpow_right htb k
      have ht2z : t ^ (2 : ℤ) = 1 := by
        simpa [hc.ctx.involution] using pow_orderOf_eq_one t
      have htk2 : t ^ k * t ^ k = 1 := by
        rw [← zpow_add]
        have hk2 : k + k = (2 : ℤ) * k := by ring
        rw [hk2, zpow_mul, ht2z, one_zpow]
      have hsq : (t ^ k * b) * (t ^ k * b) = 1 := by
        calc (t ^ k * b) * (t ^ k * b) = t ^ k * (b * t ^ k) * b := by group
          _ = t ^ k * (t ^ k * b) * b := by rw [hbk]
          _ = (t ^ k * t ^ k) * (b * b) := by group
          _ = 1 := by rw [htk2, hb2, one_mul]
      have hxsq : x * y = t ^ k * b := by
        rw [← hyi]
        exact hxy_eq
      have hxy_sq : (x * y) * (x * y) = 1 := by rw [hxsq]; exact hsq
      have hxy_inv : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy_sq
      calc x * y = (x * y)⁻¹ := hxy_inv.symm
        _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
        _ = y * x := by rw [hyi, hxi]

theorem sec7l78_A_le_cent_t [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) : ASub S B ≤ centralizer ({t} : Set G) := by
  refine (Subgroup.closure_le (K := centralizer ({t} : Set G))).mpr ?_
  rintro x ⟨hx, -⟩
  exact hc.ctx.sylow.1 hx.1

theorem sec7l78_t_mem_A [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) : t ∈ ASub S B := by
  refine Subgroup.subset_closure ⟨⟨hc.ctx.t_mem_S, ?_⟩, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (hc.ctx.le_centralizer (sec7l77_B_le_L hc hb))
  · simpa [hc.ctx.involution] using pow_orderOf_eq_one t

theorem sec7l78_A_comm_sq [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76)
    (hP : Asc82Tab6P) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) :
    (∀ a ∈ ASub S B, ∀ b ∈ ASub S B, a * b = b * a) ∧ ∀ a ∈ ASub S B, a * a = 1 := by
  let I : Set G := {x | x ∈ S ⊓ centralizer (B : Set G) ∧ x ^ 2 = 1}
  have hI : ASub S B = Subgroup.closure I := rfl
  have hpair : I.Pairwise Commute := by
    intro x hx y hy _
    exact sec7l78_gens_comm h36 h76 hP hc hx hy
  haveI : IsMulCommutative (Subgroup.closure I) := Subgroup.isMulCommutative_closure hpair
  refine ⟨?_, ?_⟩
  · intro a ha b hb
    rw [hI] at ha hb
    exact setLike_mul_comm ha hb
  · intro a ha
    rw [hI] at ha
    refine Subgroup.closure_induction (k := I) (p := fun x _ => x * x = 1) ?_ ?_ ?_ ?_ ha
    · intro x hx
      rw [← pow_two]
      exact hx.2
    · rw [one_mul]
    · intro x y hx hy ihx ihy
      have hcomm : x * y = y * x := setLike_mul_comm hx hy
      calc (x * y) * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hcomm.symm]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx, ihy, one_mul]
    · intro x hx ihx
      rw [← mul_inv_rev, ihx, inv_one]

theorem sec7l78_s_mem_A [Finite G] (hP : Asc82Tab6P) (h36 : Asc82Lemma36) {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    g⁻¹ * t * g ∈ ASub S B := by
  have hzB : z ∈ B :=
    (hP.center_le G L hc.ctx.isOm6P (S ⊓ L) (hc.ctx.isSylow2Of_inf h36) B hc.normalE16)
      hc.ctx.z_mem_centerIn
  refine Subgroup.subset_closure ⟨⟨hc.s_mem, ?_⟩, ?_⟩
  · rcases hc.choice with h | h
    · rw [h]
      refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
      have htb : t * b = b * t :=
        (Subgroup.mem_centralizer_singleton_iff.mp
          (hc.ctx.le_centralizer (sec7l77_B_le_L hc hb))).symm
      have hzb : z * b = b * z :=
        congrArg Subtype.val (hc.normalE16.2.1.1.1.is_comm.comm ⟨z, hzB⟩ ⟨b, hb⟩)
      calc b * (t * z) = (b * t) * z := by group
        _ = (t * b) * z := by rw [htb]
        _ = t * (b * z) := by group
        _ = t * (z * b) := by rw [hzb]
        _ = (t * z) * b := by group
    · exact (Subgroup.centralizer_le hc.normalE16.1) h.2.1
  · rw [pow_two]
    have ht2 : t * t = 1 := by
      rw [← pow_two]
      simpa [hc.ctx.involution] using pow_orderOf_eq_one t
    have h : (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
    rw [h, ht2]; group

theorem sec7l78_s_cent_P [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) :
    ∀ x ∈ S ⊓ L, x * (g⁻¹ * t * g) = (g⁻¹ * t * g) * x := by
  intro x hx
  rcases hc.choice with h | h
  · rw [h]
    have hxt : x * t = t * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hc.ctx.le_centralizer hx.2)
    have hxz : x * z = z * x := hc.ctx.central x hx.1
    calc x * (t * z) = (x * t) * z := by group
      _ = (t * x) * z := by rw [hxt]
      _ = t * (x * z) := by group
      _ = t * (z * x) := by rw [hxz]
      _ = (t * z) * x := by group
  · exact Subgroup.mem_centralizer_iff.mp h.2.1 x hx

theorem sec7l78_A_cent_t [Finite G] (h76 : Asc82Lemma76) (h36 : Asc82Lemma36)
    (hP : Asc82Tab6P) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) :
    ∀ a ∈ ASub S B, a ∈ centralizer (L : Set G) → a = 1 ∨ a = t := by
  intro a ha haC
  have hA_S : ASub S B ≤ S := (Subgroup.closure_le (K := S)).mpr fun x hx => hx.1.1
  have hmem : a ∈ zpowers t := by
    have h : a ∈ S ⊓ centralizer (L : Set G) := ⟨hA_S ha, haC⟩
    rwa [← h76 G t L S z hc.ctx] at h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have ht2z : t ^ (2 : ℤ) = 1 := by
    simpa [hc.ctx.involution] using pow_orderOf_eq_one t
  rw [hk.symm]
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, ht2z, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, ht2z, one_zpow, zpow_one, one_mul]

theorem sec7l78_sideL [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    Sec7L78Side L (S ⊓ L) B (ASub S B) t := by
  refine ⟨hc.ctx.isOm6P, hc.ctx.isSylow2Of_inf h36, hc.normalE16, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · intro a ha
    exact hc.ctx.cent_le_normalizer h36 a (sec7l78_A_le_cent_t hc ha)
  · exact sec7l77_A_inf_L h36 hP hc
  · exact sec7l78_t_mem_A hc
  · exact hc.ctx.t_mem_centralizer
  · exact hc.ctx.involution
  · intro a ha haC
    exact sec7l78_A_cent_t h76 h36 hP hc a ha haC
  · intro a ha b hb
    exact (sec7l78_A_comm_sq h36 h76 hP hc).1 a ha b hb
  · intro a ha
    exact (sec7l78_A_comm_sq h36 h76 hP hc).2 a ha

end CFSG.OddStandard.SmallF3.Omega
