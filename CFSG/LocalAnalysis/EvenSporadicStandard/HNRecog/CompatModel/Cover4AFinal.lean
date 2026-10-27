module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpInputs
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpFourA
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Cover4AGroup
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.FiveType
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.Shape4A
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVBasic
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elem2Rec
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Cent

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CompatModel

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.EvenSporadicStandard.HNRecog.Section4

section Closure

variable {G : Type*} [Group G]

theorem cover_mul_self_eq_one {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  have h := pow_orderOf_eq_one x
  rwa [hx, pow_two] at h

theorem cover_card_closure_triple [Finite G] {s a w : G} (hs : orderOf s = 2)
    (ha : orderOf a = 2) (hw : orderOf w = 2) (hsa : s * a = a * s) (hsw : s * w = w * s)
    (haw : a * w = w * a) (hs1 : s ≠ 1) (hsa' : s ≠ a) (hsw' : s ≠ w) (hsaw : s ≠ a * w)
    (haw' : a ≠ w) : Nat.card ↥(closure ({s, a, w} : Set G)) = 8 := by
  have haa := cover_mul_self_eq_one ha
  have hww := cover_mul_self_eq_one hw
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; omega
  have hw1 : w ≠ 1 := fun h => by rw [h, orderOf_one] at hw; omega
  have hK : closure ({a, w} : Set G) ≤ centralizer ({s} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.2 hsa.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 hsw.symm
  have hdisj : Disjoint (zpowers s) (closure ({a, w} : Set G)) := by
    rw [Subgroup.disjoint_def]
    intro x hx hxK
    rcases CFSG.EvenSporadicStandard.HSStd.HL34.eq_one_or_eq_of_mem_zpowers hs hx with rfl | rfl
    · rfl
    · exfalso
      rcases (CFSG.EvenSporadicStandard.HNRecog.TwoHSData.mem_closure_pair_iff haa hww haw).1
          hxK with h | h | h | h
      · exact hs1 h
      · exact hsa' h
      · exact hsw' h
      · exact hsaw h
  have hcl : closure ({s, a, w} : Set G) = zpowers s ⊔ closure ({a, w} : Set G) := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure]
  rw [hcl, CFSG.EvenSporadicStandard.HSStd.HL34.card_zpowers_sup hK hdisj, hs,
    CFSG.EvenSporadicStandard.HNRecog.TwoHSData.card_closure_pair haa hww haw ha1 hw1 haw']

end Closure

theorem cover_no_triple {G : Type} [Group G] [Finite G] {P : Subgroup G}
    (hP : IsMinusExtraspecial 2 P) {s a w : G} (hs : orderOf s = 2) (ha : orderOf a = 2)
    (hw : orderOf w = 2) (hsa : s * a = a * s) (hsw : s * w = w * s) (haw : a * w = w * a)
    (hs1 : s ≠ 1) (hsa' : s ≠ a) (hsw' : s ≠ w) (hsaw : s ≠ a * w) (haw' : a ≠ w)
    (hsP : s ∈ P) (haP : a ∈ P) (hwP : w ∈ P) : False := by
  refine hP.2.2 ⟨closure ({s, a, w} : Set G), ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
    · intro x hx y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        first | rfl | exact hsa | exact hsa.symm | exact hsw | exact hsw.symm | exact haw |
          exact haw.symm
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> rw [pow_two] <;>
        first | exact cover_mul_self_eq_one hs |
          exact cover_mul_self_eq_one ha | exact cover_mul_self_eq_one hw
  · exact (cover_card_closure_triple hs ha hw hsa hsw haw hs1 hsa' hsw' hsaw haw').trans
      (by norm_num)

section Config

variable {G : Type} [Group G] {a z : G}

theorem cover_orderOf_w (h : F5Std a z) {y : G} (hy : y ∈ orb4A a z a) :
    orderOf ((a * y) ^ 2) = 2 :=
  h.orderOf_eq_two (Or.inr hy.2)

theorem cover_dihedral (h : F5Std a z) {y : G} (hy : y ∈ orb4A a z a) :
    a * (a * y) ^ 2 = (a * y) ^ 2 * a ∧ y * (a * y) ^ 2 = (a * y) ^ 2 * y ∧
      IsConj a (a * (a * y) ^ 2) ∧ IsConj a (y * (a * y) ^ 2) := by
  have ha2 : a ^ 2 = 1 := by
    have h2 := pow_orderOf_eq_one a
    rwa [h.typ.orderOf_a] at h2
  have hy2 : y ^ 2 = 1 := by
    have h2 := pow_orderOf_eq_one y
    rwa [h.orderOf_eq_two (Or.inl hy.1)] at h2
  exact tableV_dihedral ha2 hy2 hy.1 (m := 2) (by rw [tableV_orderOf_orb4A h.typ hy])

theorem cover_a_mem_Qz (h : F5Std a z) {y : G} (hy : y ∈ orb4A a z a) :
    a ∈ Qz ((a * y) ^ 2) :=
  (h.loc.fusion3.self.shape_2AB _ ⟨hy.2, (cover_dihedral h hy).2.2.1⟩).2

theorem cover_y_mem_Qz (h : F5Std a z) {y : G} (hy : y ∈ orb4A a z a) :
    y ∈ Qz ((a * y) ^ 2) := by
  have hF3 : Fusion3Facts y z := h.loc.fusion3 y z hy.1 (IsConj.refl z)
  exact (hF3.shape_2AB _ ⟨hy.2, hy.1.symm.trans (cover_dihedral h hy).2.2.2⟩).2

theorem cover_K_le (a y : G) : Gxy a y ≤ Gx ((a * y) ^ 2) := by
  intro g hg
  rw [tableV_Gxy_eq_Gxyz_pow a y 2] at hg
  exact (mem_Gxyz.1 hg).2.1

theorem cover_w_mem_K (h : F5Std a z) {y : G} (hy : y ∈ orb4A a z a) :
    (a * y) ^ 2 ∈ Gxy a y := by
  obtain ⟨h1, h2, -, -⟩ := cover_dihedral h hy
  exact mem_Gxy.2 ⟨mem_Gx.2 h1, mem_Gx.2 h2⟩

theorem cover_a_not_mem_K (h : F5Std a z) {y : G} (hy : y ∈ orb4A a z a) : a ∉ Gxy a y :=
  fun ha => cp_not_comm_of_orb4A h hy (mem_Gx.1 (mem_Gxy.1 ha).2).symm

theorem cover_card_K (h : F5Std a z) {y : G} (hy : y ∈ orb4A a z a) :
    Nat.card ↥(Gxy a y) = 640 := by
  have h1 := h.loc.tableV.self.card_stab 2 y (by simpa [tab5Set] using hy)
  rw [← Gxy_eq_inf] at h1
  simpa using h1

theorem cover_card_KQ (h : F5Std a z) {y : G} (hy : y ∈ orb4A a z a) :
    Nat.card ↥(Gxy a y ⊓ Qz ((a * y) ^ 2)) = 2 ^ 7 := by
  haveI := h.finite
  have hw : F5Std a ((a * y) ^ 2) := h.of_isConj (IsConj.refl a) hy.2
  have haa := cover_mul_self_eq_one h.typ.orderOf_a
  have hw2 := cover_orderOf_w h hy
  have hya : y ≠ a := by
    rintro rfl
    exact cp_not_comm_of_orb4A h hy rfl
  have hyaw : y ≠ a * (a * y) ^ 2 := by
    intro hyeq
    have h1 : a * y = (a * y) ^ 2 := by
      calc a * y = a * (a * (a * y) ^ 2) := by rw [← hyeq]
        _ = (a * a) * (a * y) ^ 2 := by rw [mul_assoc]
        _ = (a * y) ^ 2 := by rw [haa, one_mul]
    have h2 : orderOf (a * y) = 2 := by
      rw [h1]
      exact hw2
    have h3 := tableV_orderOf_orb4A h.typ hy
    omega
  have hmem : y ∈ tab3Set a ((a * y) ^ 2) a 2 := by
    have h1 : y ∈ tab3Base a ((a * y) ^ 2) a ∧ (a * y) ^ 2 = (a * y) ^ 2 :=
      ⟨⟨cover_y_mem_Qz h hy, hy.1, hya, hyaw⟩, rfl⟩
    simpa [tab3Set] using h1
  have h1 := tableIII_card_inf_Qz_4A h.iface hw.typ (cover_a_mem_Qz h hy) (IsConj.refl a) hmem
  rwa [← tableV_Gxy_eq_Gxyz_pow a y 2] at h1

theorem cover_inv_mem_Qz (h : F5Std a z) {y : G} (hy : y ∈ orb4A a z a) {t : G}
    (ht : t ∈ InvIn (Gxy a y)) : t ∈ Qz ((a * y) ^ 2) := by
  haveI := h.finite
  have hKw := cover_K_le a y
  have hNn : ((Qz ((a * y) ^ 2)).subgroupOf (Gxy a y)).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact tableIII_conj_mem_Qz (hKw g.2) hn⟩
  have hNcard : Nat.card ↥((Qz ((a * y) ^ 2)).subgroupOf (Gxy a y)) = 2 ^ 7 := by
    rw [← Subgroup.card_map_of_injective (Gxy a y).subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
    exact cover_card_KQ h hy
  have hindex : ((Qz ((a * y) ^ 2)).subgroupOf (Gxy a y)).index = 5 := by
    have h1 := Subgroup.card_mul_index ((Qz ((a * y) ^ 2)).subgroupOf (Gxy a y))
    rw [hNcard, cover_card_K h hy] at h1
    omega
  have hmem := Subgroup.pow_index_mem ((Qz ((a * y) ^ 2)).subgroupOf (Gxy a y))
    (⟨t, ht.1⟩ : ↥(Gxy a y))
  rw [hindex, Subgroup.mem_subgroupOf] at hmem
  have ht2 : t ^ 2 = 1 := by
    have h2 := pow_orderOf_eq_one t
    rwa [ht.2] at h2
  have h5 : t ^ 5 = t := by
    rw [show 5 = 2 * 2 + 1 from rfl, pow_succ, pow_mul, ht2, one_pow, one_mul]
  simpa [h5] using hmem

theorem cover_exists_rho (h : F5Std a z) {y : G} (hy : y ∈ orb4A a z a) :
    ∃ ρ ∈ Gxy a y, orderOf ρ = 5 := by
  haveI := h.finite
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hdvd : 5 ∣ Nat.card ↥(Gxy a y) := by
    rw [cover_card_K h hy]
    norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 hdvd
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

end Config

section Fixed

variable {G : Type} [Group G] {a z : G}

theorem cover_self_mem_Qz {w : G} (hw2 : orderOf w = 2)
    (hQ : IsExtraspecialPlusByA5WrTwoWith ↥(Gx w) (CFSG.pCore 2 ↥(Gx w))) : w ∈ Qz w := by
  have hmem : GxSelf w ∈ centerOf (CFSG.pCore 2 ↥(Gx w)) := by
    rw [centerOf_eq_zpowers hw2 hQ]
    exact Subgroup.mem_zpowers _
  rw [centerOf, Subgroup.mem_inf] at hmem
  exact Subgroup.mem_map.2 ⟨GxSelf w, hmem.1, rfl⟩

theorem cover_fixed (h : F5Std a z) {y : G} (hy : y ∈ orb4A a z a) {ρ : G}
    (hρK : ρ ∈ Gxy a y) (hρ : orderOf ρ = 5) {s : G} (hs : s ∈ InvIn (Gxy a y))
    (hρs : ρ * s = s * ρ) : s = (a * y) ^ 2 := by
  haveI := h.finite
  by_contra hsw
  have hw : F5Std a ((a * y) ^ 2) := h.of_isConj (IsConj.refl a) hy.2
  have hw2 := cover_orderOf_w h hy
  have ha2 := h.typ.orderOf_a
  have hρw : ρ ∈ Gx ((a * y) ^ 2) := cover_K_le a y hρK
  have haQ := cover_a_mem_Qz h hy
  have hwK := cover_w_mem_K h hy
  have haK := cover_a_not_mem_K h hy
  have hww := cover_mul_self_eq_one hw2
  have hQ := isExtraspecialPlusByA5WrTwoWith_pCore (z := (a * y) ^ 2) hw.typ.cent_z
  have hwQ := cover_self_mem_Qz hw2 hQ
  have hρa : ρ * a = a * ρ := (mem_Gx.1 (mem_Gxy.1 hρK).1).symm
  have hρ' : orderOf (⟨ρ, hρw⟩ : ↥(Gx ((a * y) ^ 2))) = 5 := by
    rw [← Subgroup.orderOf_coe]
    exact hρ
  have ha1 : a ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ha2; omega
  have haw : a ≠ (a * y) ^ 2 := by
    intro h1
    apply haK
    have h2 := hwK
    rwa [← h1] at h2
  have hmin := (tableIII_five_type hw.typ hw.loc.structGz.self hρ' haQ ha1 haw hρa).2
  have hs2 : orderOf s = 2 := hs.2
  have hsa : s * a = a * s := (mem_Gx.1 (mem_Gxy.1 hs.1).1).symm
  have hsw' : s * (a * y) ^ 2 = (a * y) ^ 2 * s := (mem_Gx.1 (cover_K_le a y hs.1)).symm
  have hs1 : s ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hs2; omega
  have hsa' : s ≠ a := by
    intro h1
    apply haK
    have h2 := hs.1
    rwa [h1] at h2
  have hsaw : s ≠ a * (a * y) ^ 2 := by
    intro h1
    apply haK
    have h2 : s * (a * y) ^ 2 = a := by rw [h1, mul_assoc, hww, mul_one]
    have h3 : s * (a * y) ^ 2 ∈ Gxy a y := mul_mem hs.1 hwK
    rwa [h2] at h3
  exact cover_no_triple hmin hs2 ha2 hw2 hsa hsw' (cover_dihedral h hy).1 hs1 hsa' hsw hsaw haw
    (Subgroup.mem_inf.2 ⟨cover_inv_mem_Qz h hy hs, mem_Gx.2 hρs⟩)
    (Subgroup.mem_inf.2 ⟨haQ, mem_Gx.2 hρa⟩)
    (Subgroup.mem_inf.2 ⟨hwQ, mem_Gx.2 (mem_Gx.1 hρw).symm⟩)

end Fixed

section Transfer

variable {G : Type} [Group G]

theorem cover_transfer {w : G} (hw2 : orderOf w = 2)
    (hQ : IsExtraspecialPlusByA5WrTwoWith ↥(Gx w) (CFSG.pCore 2 ↥(Gx w)))
    {ρ a d t : G} (hρw : ρ ∈ Gx w) (hρ5 : orderOf ρ = 5) (haQ : a ∈ Qz w) (ha1 : a ≠ 1)
    (haw : a ≠ w) (hρa : ρ * a = a * ρ) (hdQ : d ∈ Qz w) (hρd : ρ * d ≠ d * ρ)
    (htQ : t ∈ Qz w) (hft : ρ * t = t * ρ → t = w) :
    ∃ i : ℕ, i < 5 ∧ ρ ^ i * d * (ρ ^ i)⁻¹ * t = t * (ρ ^ i * d * (ρ ^ i)⁻¹) := by
  have hcenter : centerOf (CFSG.pCore 2 ↥(Gx w)) = Subgroup.zpowers (GxSelf w) :=
    centerOf_eq_zpowers hw2 hQ
  have hmemQ : ∀ {x : G} (hx : x ∈ Gx w),
      (⟨x, hx⟩ : ↥(Gx w)) ∈ CFSG.pCore 2 ↥(Gx w) ↔ x ∈ Qz w := fun {x} hx =>
    (Subgroup.mem_map_iff_mem (Gx w).subtype_injective (K := CFSG.pCore 2 ↥(Gx w))
      (x := ⟨x, hx⟩)).symm
  have hw1 : w ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hw2; omega
  have hρ5' : (⟨ρ, hρw⟩ : ↥(Gx w)) ^ 5 = 1 := by
    apply Subtype.ext
    have h5 := pow_orderOf_eq_one ρ
    rw [hρ5] at h5
    simpa using h5
  have hwc : GxSelf w ∈ centerOf (CFSG.pCore 2 ↥(Gx w)) := by
    rw [hcenter]
    exact Subgroup.mem_zpowers _
  have hw1' : GxSelf w ≠ 1 := fun h1 => hw1 (congrArg Subtype.val h1)
  have hρw' : (⟨ρ, hρw⟩ : ↥(Gx w)) * GxSelf w = GxSelf w * ⟨ρ, hρw⟩ :=
    Subtype.ext (mem_Gx.1 hρw).symm
  have haw0 : a ∈ Gx w := tableIII_Qz_le w haQ
  have hdw0 : d ∈ Gx w := tableIII_Qz_le w hdQ
  have htw0 : t ∈ Gx w := tableIII_Qz_le w htQ
  have ha' : (⟨a, haw0⟩ : ↥(Gx w)) ∉ centerOf (CFSG.pCore 2 ↥(Gx w)) := by
    rw [hcenter]
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hk' : w ^ k = a := by simpa [GxSelf] using congrArg Subtype.val hk
    rcases CFSG.EvenSporadicStandard.HSStd.HL34.eq_one_or_eq_of_mem_zpowers hw2
        (Subgroup.mem_zpowers_iff.2 ⟨k, hk'⟩) with h1 | h1
    · exact ha1 h1
    · exact haw h1
  obtain ⟨i, hi, hcomm⟩ := cover_group (Q := CFSG.pCore 2 ↥(Gx w)) hQ.plus hρ5' hwc hw1' hρw'
    ((hmemQ haw0).2 haQ) ha' (Subtype.ext hρa) ((hmemQ hdw0).2 hdQ)
    (fun h1 => hρd (congrArg Subtype.val h1)) ((hmemQ htw0).2 htQ)
    (fun h1 => by
      have ht := hft (congrArg Subtype.val h1)
      have h2 : (⟨t, htw0⟩ : ↥(Gx w)) = GxSelf w := Subtype.ext ht
      rw [hcenter, h2]
      exact Subgroup.mem_zpowers _)
  refine ⟨i, hi, ?_⟩
  simpa only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv] using
    congrArg Subtype.val hcomm

end Transfer

section Main

variable {G : Type} [Group G] {a z : G}

theorem cover_main (h : F5Std a z) {y : G} (hy : y ∈ orb4A a z a) {d t : G}
    (hd : d ∈ InvIn (Gxy a y)) (hdw : d ≠ (a * y) ^ 2) (ht : t ∈ InvIn (Gxy a y)) :
    ∃ k ∈ Gxy a y, k * d * k⁻¹ * t = t * (k * d * k⁻¹) := by
  haveI := h.finite
  obtain ⟨ρ, hρK, hρ⟩ := cover_exists_rho h hy
  have hw : F5Std a ((a * y) ^ 2) := h.of_isConj (IsConj.refl a) hy.2
  have hQ := isExtraspecialPlusByA5WrTwoWith_pCore (z := (a * y) ^ 2) hw.typ.cent_z
  have hw2 := cover_orderOf_w h hy
  have ha2 := h.typ.orderOf_a
  have ha1 : a ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ha2; omega
  have haw : a ≠ (a * y) ^ 2 := by
    intro h1
    apply cover_a_not_mem_K h hy
    have h2 := cover_w_mem_K h hy
    rwa [← h1] at h2
  obtain ⟨i, -, hi⟩ := cover_transfer hw2 hQ (cover_K_le a y hρK) hρ (cover_a_mem_Qz h hy) ha1 haw
    (mem_Gx.1 (mem_Gxy.1 hρK).1).symm (cover_inv_mem_Qz h hy hd)
    (fun hc => hdw (cover_fixed h hy hρK hρ hd hc)) (cover_inv_mem_Qz h hy ht)
    (fun hc => cover_fixed h hy hρK hρ ht hc)
  exact ⟨ρ ^ i, pow_mem hρK i, hi⟩

end Main

end CFSG.EvenSporadicStandard.HNRecog.CompatModel

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.EvenSporadicStandard.HNRecog.CompatModel

theorem cover4A_holds : Cover4A := by
  intro G _ a z h y hy d hd t ht
  have hdK : d ∈ Gxy a y :=
    mem_Gxy.2 ⟨h.mem_Gx_of_orb2A (IsConj.refl a) hd.1, h.mem_Gx_of_orb2A hy.1 hd.2⟩
  have hd2 : orderOf d = 2 := h.orderOf_eq_two (Or.inl hd.1.1)
  have hdw : d ≠ (a * y) ^ 2 := by
    intro hdw
    have h1 : IsConj a ((a * y) ^ 2) := by
      have h2 := hd.1.1
      rwa [hdw] at h2
    exact h.not_isConj (h1.trans hy.2.symm)
  obtain ⟨k, hkK, hk⟩ := cover_main h hy ⟨hdK, hd2⟩ hdw ht
  have hrK : k⁻¹ * t * k ∈ Gxy a y := mul_mem (mul_mem (inv_mem hkK) ht.1) hkK
  refine ⟨k⁻¹ * t * k, ⟨mem_Gxyz.2 ⟨(mem_Gxy.1 hrK).1, ?_, (mem_Gxy.1 hrK).2⟩, ?_⟩, k, hkK, ?_⟩
  · refine mem_Gx.2 ?_
    calc d * (k⁻¹ * t * k) = k⁻¹ * (k * d * k⁻¹ * t) * k := by group
      _ = k⁻¹ * (t * (k * d * k⁻¹)) * k := by rw [hk]
      _ = (k⁻¹ * t * k) * d := by group
  · have h1 := MulEquiv.orderOf_eq (MulAut.conj k⁻¹) t
    simpa [MulAut.conj_apply] using h1.trans ht.2
  · group

end CFSG.EvenSporadicStandard.HNRecog.Section4
