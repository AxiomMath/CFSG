module

public import CFSG.GF2Type.SmithTypeE.LMod.UaDefs
public import Certificates.Certificate38604

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6
open scoped Pointwise

attribute [local irreducible] stabGens elemGens planeImg meetCard dRoot tvIdxTab tvTab tvImg tvList

theorem transReach_holds :
    K.Reach 1395 1953 (· == 0) (fun k u v => planeImg k u == v) :=
  Certificates.certificate38604.1

theorem planeReach_holds :
    K.Reach 1395 1953 (fun j => j == dRoot (meetCard 0 j))
      (fun p u v => planeImg p 0 == 0 && meetCard 0 u == meetCard 0 v && planeImg p u == v) :=
  Certificates.certificate38604.2.1

theorem uCounts_holds :
    (List.range 512).countP (fun v => uCls uSums v == 1) = 49 ∧
    (List.range 512).countP (fun v => uCls uSums v == 2) = 294 ∧
    (List.range 512).countP (fun v => uCls uSums v == 3) = 168 :=
  ⟨Certificates.certificate38604.2.2.1, Certificates.certificate38604.2.2.2.1,
    Certificates.certificate38604.2.2.2.2.1⟩

theorem uReach_holds :
    K.Reach 512 1953 (fun v => v == uRoot uSums (uCls uSums v))
      (fun p u v => planeImg p 0 == 0 && uCls uSums u == uCls uSums v &&
        CFSG.SmithE.applyCols (ucols p) u == v) :=
  Certificates.certificate38604.2.2.2.2.2

theorem mem_stabGens {p : ℕ} : p ∈ stabGens ↔ p < 1953 ∧ planeImg p 0 = 0 := by
  simp [stabGens, List.mem_filter]

section Orbit

theorem exists_image_wPlane_zero {j : ℕ} (hj : j < 1395) :
    ∃ g ∈ T6, ⇑g '' wPlane 0 = wPlane j := by
  refine transReach_holds (fun j => ∃ g ∈ T6, ⇑g '' wPlane 0 = wPlane j) ?_ ?_ j hj
  · intro v _ hv
    have : v = 0 := by simpa using hv
    subst this
    exact ⟨1, T6.one_mem, by simp⟩
  · intro k hk u hu v hv he ⟨g', hg', hg'e⟩
    have hv' : planeImg k u = v := by simpa using he
    refine ⟨tvP ⟨k, hk⟩ * g', T6.mul_mem (tvP_mem _) hg', ?_⟩
    rw [Equiv.Perm.coe_mul, Set.image_comp, hg'e, image_wPlane_tvP hu]
    exact congrArg wPlane hv'

end Orbit

section Dist

theorem meetCard_zero_eq {j : ℕ} (hj : j < 1395) :
    meetCard 0 j = (wPlane 0 ∩ wPlane j).ncard := by
  rw [meetCard_eq_card (by norm_num) hj, wPlane, wPlane, ← Finset.coe_inter,
    Set.ncard_coe_finset]

theorem tvP_mem_PA_zero {p : ℕ} (hp : p ∈ stabGens) :
    tvP ⟨p, (mem_stabGens.1 hp).1⟩ ∈ PA 0 := by
  obtain ⟨h1, h2⟩ := mem_stabGens.1 hp
  rw [mem_PA]
  refine ⟨tvP_mem _, ?_⟩
  rw [image_wPlane_tvP (by norm_num)]
  exact congrArg wPlane h2

theorem exists_PA_zero_image {j : ℕ} (hj : j < 1395) :
    ∃ g ∈ PA 0, ⇑g '' wPlane (dRoot (meetCard 0 j)) = wPlane j := by
  refine planeReach_holds
    (fun j => ∃ g ∈ PA 0, ⇑g '' wPlane (dRoot (meetCard 0 j)) = wPlane j) ?_ ?_ j hj
  · intro v _ hv
    have : v = dRoot (meetCard 0 v) := by simpa using hv
    refine ⟨1, (PA 0).one_mem, ?_⟩
    rw [← this]
    simp
  · intro q hq u hu v hv he ⟨g', hg', hg'e⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨⟨h0, hc⟩, hp⟩ := he
    have hmem : q ∈ stabGens := mem_stabGens.2 ⟨hq, h0⟩
    refine ⟨tvP ⟨q, (mem_stabGens.1 hmem).1⟩ * g',
      (PA 0).mul_mem (tvP_mem_PA_zero hmem) hg', ?_⟩
    rw [Equiv.Perm.coe_mul, Set.image_comp, ← hc, hg'e, image_wPlane_tvP hu]
    exact congrArg wPlane hp

theorem exists_PA_image_zero {j j' : ℕ} (hj : j < 1395) (hj' : j' < 1395)
    (h : (wPlane 0 ∩ wPlane j).ncard = (wPlane 0 ∩ wPlane j').ncard) :
    ∃ g ∈ PA 0, ⇑g '' wPlane j = wPlane j' := by
  obtain ⟨x, hx, hxj⟩ := exists_PA_zero_image hj
  obtain ⟨y, hy, hyj⟩ := exists_PA_zero_image hj'
  rw [meetCard_zero_eq hj, h, ← meetCard_zero_eq hj'] at hxj
  refine ⟨y * x⁻¹, (PA 0).mul_mem hy ((PA 0).inv_mem hx), ?_⟩
  rw [Equiv.Perm.coe_mul, Set.image_comp, image_wPlane_inv hxj, hyj]

theorem conj_mem_PA {i : ℕ} {h : Equiv.Perm (Fin 1953)} (hh : h ∈ T6)
    (hW : ⇑h '' wPlane 0 = wPlane i) {g : Equiv.Perm (Fin 1953)} (hg : g ∈ PA 0) :
    h * g * h⁻¹ ∈ PA i := by
  obtain ⟨hgT, hgW⟩ := mem_PA.1 hg
  rw [mem_PA]
  refine ⟨T6.mul_mem (T6.mul_mem hh hgT) (T6.inv_mem hh), ?_⟩
  rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, Set.image_comp, Set.image_comp,
    image_wPlane_inv hW, hgW, hW]

theorem exists_PA_image {i : ℕ} (hi : i < 1395) {j j' : ℕ} (hj : j < 1395) (hj' : j' < 1395)
    (h : (wPlane i ∩ wPlane j).ncard = (wPlane i ∩ wPlane j').ncard) :
    ∃ g ∈ PA i, ⇑g '' wPlane j = wPlane j' := by
  obtain ⟨x, hx, hxW⟩ := exists_image_wPlane_zero hi
  obtain ⟨k, hk, hkj⟩ := exists_image_wPlane (T6.inv_mem hx) hj
  obtain ⟨k', hk', hkj'⟩ := exists_image_wPlane (T6.inv_mem hx) hj'
  have hinv := image_wPlane_inv hxW
  have hmeet : (wPlane 0 ∩ wPlane k).ncard = (wPlane 0 ∩ wPlane k').ncard := by
    rw [← hinv, ← hkj, ← hkj', ← Set.image_inter x⁻¹.injective,
      ← Set.image_inter x⁻¹.injective, Set.ncard_image_of_injective _ x⁻¹.injective,
      Set.ncard_image_of_injective _ x⁻¹.injective, h]
  obtain ⟨g, hg, hgk⟩ := exists_PA_image_zero hk hk' hmeet
  refine ⟨x * g * x⁻¹, conj_mem_PA hx hxW hg, ?_⟩
  rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, Set.image_comp, Set.image_comp, hkj, hgk,
    ← image_wPlane_inv hkj', inv_inv]

end Dist

end CFSG.GF2Type.SmithTypeE.LMod
