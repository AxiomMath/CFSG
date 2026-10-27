module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CSideCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerD

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

namespace DSide

variable {G : Type} [Group G] [Finite G] {L B D : Subgroup G} {z : G}

@[expose] noncomputable def ztD (hs : LocalSetting G L z) (hBL : B ≤ L) (hD : NData B z D) :
    egQD D :=
  QuotientGroup.mk (⟨z, LayerD.z_mem_normalizer_D hs hBL hD⟩ : normalizer (D : Set G))

theorem ztD_mul_self (hs : LocalSetting G L z) (hBL : B ≤ L) (hD : NData B z D) :
    ztD hs hBL hD * ztD hs hBL hD = 1 := by
  rw [ztD, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
  refine mem_subgroupOf.2 ?_
  show z * z ∈ D
  rw [Octad.z_mul_self hs]
  exact one_mem _

theorem exists_decomp (hs : LocalSetting G L z) (hBL : B ≤ L) (hb : OctadBasics L B)
    (hD : NData B z D) {n : G} (hnN : n ∈ normalizer (D : Set G))
    (hc : ztD hs hBL hD * QuotientGroup.mk (⟨n, hnN⟩ : normalizer (D : Set G)) =
      QuotientGroup.mk (⟨n, hnN⟩ : normalizer (D : Set G)) * ztD hs hBL hD) :
    ∃ d ∈ D, ∃ l ∈ L, d⁻¹ * n = l ∨ d⁻¹ * n = l * z := by
  have hzN := LayerD.z_mem_normalizer_D hs hBL hD
  have hzi := Octad.z_inv hs
  have hzz := Octad.z_mul_self hs
  have h1 : ((⟨n, hnN⟩ * ⟨z, hzN⟩ : normalizer (D : Set G))⁻¹ * (⟨z, hzN⟩ * ⟨n, hnN⟩)) ∈
      D.subgroupOf (normalizer (D : Set G)) :=
    QuotientGroup.eq.1 (by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact hc.symm)
  have hc' : z⁻¹ * n⁻¹ * z * n ∈ D := by
    have h2 := mem_subgroupOf.1 h1
    have e : (((⟨n, hnN⟩ * ⟨z, hzN⟩ : normalizer (D : Set G))⁻¹ *
        (⟨z, hzN⟩ * ⟨n, hnN⟩) : normalizer (D : Set G)) : G) = z⁻¹ * n⁻¹ * z * n := by
      show (n * z)⁻¹ * (z * n) = z⁻¹ * n⁻¹ * z * n
      group
    rwa [e] at h2
  have hwz : n * z⁻¹ * n⁻¹ * z ∈ D := by
    have h3 := (mem_normalizer_iff.1 hnN _).1 hc'
    have e : n * (z⁻¹ * n⁻¹ * z * n) * n⁻¹ = n * z⁻¹ * n⁻¹ * z := by group
    rwa [e] at h3
  have hdD : z * (n * z * n⁻¹) ∈ D := by
    have h4 := inv_mem hwz
    have e : (n * z⁻¹ * n⁻¹ * z)⁻¹ = z * (n * z * n⁻¹) := by
      simp only [mul_inv_rev, inv_inv, hzi, mul_assoc]
    rwa [e] at h4
  have hw2 : (n * z * n⁻¹) * (n * z * n⁻¹) = 1 := by
    calc (n * z * n⁻¹) * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
      _ = 1 := by rw [hzz, mul_one, mul_inv_cancel]
  set d := z * (n * z * n⁻¹) with hd_def
  have hzd : z * d = n * z * n⁻¹ := by rw [hd_def, ← mul_assoc, hzz, one_mul]
  have hd2 : d * d = 1 := hD.elem.2 _ hdD
  have h5 : z * d * z * d = d * d := by
    rw [hd2]
    calc z * d * z * d = (z * d) * (z * d) := by group
      _ = 1 := by rw [hzd]; exact hw2
  have h6 : z * d * z = d := mul_right_cancel h5
  have hdz : d * z = z * d := by
    calc d * z = (z * z) * d * z := by rw [hzz, one_mul]
      _ = z * (z * d * z) := by group
      _ = z * d := by rw [h6]
  have hdB : d ∈ B := LayerD.mem_B_of_mem_D_of_comm hs hBL hb hD hdD hdz
  obtain ⟨d', hd'D, hd'⟩ := hD.onto d hdB
  have hconj : d' * z * d'⁻¹ = n * z * n⁻¹ := by
    rw [← hzd, ← hd', hzi]
    calc d' * z * d'⁻¹ = (z * z) * d' * z * d'⁻¹ := by rw [hzz, one_mul]
      _ = z * (z * d' * z * d'⁻¹) := by group
  have hmz : (d'⁻¹ * n) * z = z * (d'⁻¹ * n) := by
    have e1 : (d'⁻¹ * n) * z * (d'⁻¹ * n)⁻¹ = z := by
      calc (d'⁻¹ * n) * z * (d'⁻¹ * n)⁻¹ = d'⁻¹ * (n * z * n⁻¹) * d' := by group
        _ = d'⁻¹ * (d' * z * d'⁻¹) * d' := by rw [hconj]
        _ = z := by group
    calc (d'⁻¹ * n) * z = (d'⁻¹ * n) * z * (d'⁻¹ * n)⁻¹ * (d'⁻¹ * n) := by group
      _ = z * (d'⁻¹ * n) := by rw [e1]
  obtain ⟨l, hlL, hm | hm⟩ := Octad.exists_of_comm hs hmz
  · exact ⟨d', hd'D, l, hlL, Or.inl hm⟩
  · exact ⟨d', hd'D, l, hlL, Or.inr hm⟩

omit [Finite G] in
theorem le_centralizer_self (hD : NData B z D) : D ≤ centralizer (D : Set G) := fun d hd =>
  mem_centralizer_iff.2 fun d' hd' => hD.elem.1 d' hd' d hd

omit [Finite G] in
theorem mem_B_of_mem_centralizer (hb : OctadBasics L B) (hD : NData B z D) {l : G} (hlL : l ∈ L)
    (hl : l ∈ centralizer (D : Set G)) : l ∈ B :=
  hb.cent l hlL fun b hbB => (mem_centralizer_iff.1 hl b (hD.B_le hbB)).symm

theorem z_not_mem_centralizer (hb : OctadBasics L B) (hD : NData B z D) :
    z ∉ centralizer (D : Set G) := by
  intro hz
  have h1 : 1 < Nat.card B := by rw [hb.card_B]; norm_num
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
      ((Subgroup.one_lt_card_iff_ne_bot B).1 h1)
    exact ⟨b, b.2, fun h => hb1 (Subtype.ext h)⟩
  obtain ⟨d, hdD, hd⟩ := hD.onto b hbB
  have hdz : d * z = z * d := mem_centralizer_iff.1 hz d hdD
  apply hb1
  rw [← hd]
  calc z * d * z⁻¹ * d⁻¹ = (z * d) * z⁻¹ * d⁻¹ := rfl
    _ = (d * z) * z⁻¹ * d⁻¹ := by rw [hdz]
    _ = 1 := by group

theorem eq_one_of_comm (hs : LocalSetting G L z) (hBL : B ≤ L) (hb : OctadBasics L B)
    (hD : NData B z D) {n : egQD D} (hn : n ∈ CSide.cQuot D)
    (hc : ztD hs hBL hD * n = n * ztD hs hBL hD) : n = 1 := by
  obtain ⟨m, hm, rfl⟩ := hn
  have hmC : (m : G) ∈ centralizer (D : Set G) := mem_subgroupOf.1 hm
  obtain ⟨d, hdD, l, hlL, hdl⟩ := exists_decomp hs hBL hb hD m.2 hc
  have hdC : d⁻¹ ∈ centralizer (D : Set G) := inv_mem (le_centralizer_self hD hdD)
  have hdm : d⁻¹ * (m : G) ∈ centralizer (D : Set G) := mul_mem hdC hmC
  rcases hdl with hl | hl
  · rw [hl] at hdm
    have hlB : l ∈ B := mem_B_of_mem_centralizer hb hD hlL hdm
    have hmD : (m : G) ∈ D := by
      have e : (m : G) = d * l := by rw [← hl]; group
      rw [e]
      exact mul_mem hdD (hD.B_le hlB)
    exact (QuotientGroup.eq_one_iff m).2 (mem_subgroupOf.2 hmD)
  · exfalso
    rw [hl] at hdm
    have hlB : l ∈ B := by
      refine hb.cent _ hlL fun b hbB => ?_
      have h1 := mem_centralizer_iff.1 hdm b (hD.B_le hbB)
      have h2 : z * b = b * z := Octad.z_comm hs (hBL hbB)
      have : b * l * z = l * b * z := by
        calc b * l * z = b * (l * z) := by group
          _ = l * z * b := h1
          _ = l * (z * b) := by group
          _ = l * (b * z) := by rw [h2]
          _ = l * b * z := by group
      exact (mul_right_cancel this).symm
    have hlc : l ∈ centralizer (D : Set G) := le_centralizer_self hD (hD.B_le hlB)
    apply z_not_mem_centralizer hb hD
    have e : z = l⁻¹ * (l * z) := by group
    rw [e]
    exact mul_mem (inv_mem hlc) hdm

theorem cQuot_le_oddCore (hs : LocalSetting G L z) (hBL : B ≤ L) (hb : OctadBasics L B)
    (hD : NData B z D) : CSide.cQuot D ≤ fusionOddCore (egQD D) := by
  have := CSide.cQuot_normal D
  exact normal_le_fusionOddCore_of_fixedPointFree (CSide.cQuot D) (ztD hs hBL hD)
    (ztD_mul_self hs hBL hD) fun s hs' hcomm => eq_one_of_comm hs hBL hb hD hs' hcomm

end DSide

end CFSG.EvenSporadicStandard.M24Std
