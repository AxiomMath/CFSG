module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Classes

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog.SideF4

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HNOddCore
  CFSG.Sporadic.HNOddCore.Native CFSG.ONSchreier CFSG.ONSchreier.Native Equiv

section Radical


abbrev ZJ : Subgroup CJ := QJ ⊓ Subgroup.centralizer (QJ : Set CJ)

theorem ZJ_conj {z : CJ} (hz : z ∈ ZJ) (g : CJ) : g * z * g⁻¹ ∈ ZJ := by
  refine ⟨QJ_normal.conj_mem z hz.1 g, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ QJ := by simpa using QJ_normal.conj_mem y hy g⁻¹
  have h := Subgroup.mem_centralizer_iff.1 hz.2 _ hy'
  calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
    _ = g * z * g⁻¹ * y := by group

theorem rhoGen_eq_rhoJ {g : ℕ} (hg : g < 10) : rhoGen g = rhoJ (gJn g) := by
  rw [gJn, dif_pos hg, rhoJ_gJ]

open scoped Classical in
@[expose] def TZ : Finset ℕ := (Finset.range 256).filter fun m => qb m ∈ ZJ.map rhoJ

theorem mem_TZ {m : ℕ} : m ∈ TZ ↔ m < 256 ∧ qb m ∈ ZJ.map rhoJ := by
  simp [TZ]

theorem qb_inj {a b : ℕ} (ha : a < 256) (hb : b < 256) (h : qb a = qb b) : a = b := by
  have := qb_injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (Subtype.ext h)
  exact congrArg Fin.val this

theorem pinvs_eq_pinvCand {n : ℕ} {S : Array (Array ℕ)} {g : ℕ} (hg : g < S.size) :
    (pinvs n S)[g]! = pinvCand n S[g]! := by
  unfold pinvs
  rw [getElem!_pos _ g (by simpa using hg), Array.getElem_map, getElem!_pos _ g hg]

theorem TZ_conj {g : ℕ} (hg : g < 10) {m : ℕ} (hm : m < 256) (hmT : m ∈ TZ) :
    (colPerms[g]!)[m]! ∈ TZ := by
  obtain ⟨z, hz, hzm⟩ := Subgroup.mem_map.1 (mem_TZ.1 hmT).2
  rw [mem_TZ]
  refine ⟨colPerm_lt (by omega) hm, Subgroup.mem_map.2 ⟨(gJn g)⁻¹ * z * gJn g, ?_, ?_⟩⟩
  · simpa using ZJ_conj hz (gJn g)⁻¹
  · rw [← colPerm_spec (by omega) hm, rhoGen_eq_rhoJ hg, map_mul, map_mul, map_inv, hzm, mul_assoc]

theorem TZ_conj_inv {g : ℕ} (hg : g < 10) {m : ℕ} (hm : m < 256) (hmT : m ∈ TZ) :
    ((pinvs 256 colPerms)[g]!)[m]! ∈ TZ := by
  have hcs : colPerms.size = 11 := q_parts.2.2.2.1
  have hinv : pisInv 256 colPerms[g]! (pinvs 256 colPerms)[g]! = true := by
    rw [pinvs_eq_pinvCand (by rw [hcs]; omega)]
    exact (q_parts.2.2.2.2.2.2.2.2.2.1 g (by omega)).1
  obtain ⟨hp1, hp2⟩ := prep_permOfArr hinv
  set π := permOfArr 256 colPerms[g]! with hπ
  have h1 : ((pinvs 256 colPerms)[g]!)[m]! = ((π⁻¹ ⟨m, hm⟩ : Fin 256) : ℕ) := hp2 ⟨m, hm⟩
  have h2 : (colPerms[g]!)[((π⁻¹ ⟨m, hm⟩ : Fin 256) : ℕ)]! = m := by
    rw [hp1 (π⁻¹ ⟨m, hm⟩)]
    simp
  obtain ⟨z, hz, hzm⟩ := Subgroup.mem_map.1 (mem_TZ.1 hmT).2
  rw [h1, mem_TZ]
  refine ⟨(π⁻¹ ⟨m, hm⟩ : Fin 256).2, Subgroup.mem_map.2 ⟨gJn g * z * (gJn g)⁻¹, ZJ_conj hz _, ?_⟩⟩
  have hspec := colPerm_spec (g := g) (by omega) (m := ((π⁻¹ ⟨m, hm⟩ : Fin 256) : ℕ))
    (π⁻¹ ⟨m, hm⟩ : Fin 256).2
  rw [h2] at hspec
  rw [map_mul, map_mul, map_inv, hzm, ← rhoGen_eq_rhoJ hg, ← hspec]
  group

theorem TZ_closed : ∀ l : ℤ, plettersOK 10 [l] = true → ∀ m ∈ TZ,
    (pletter colPerms (pinvs 256 colPerms) l)[m]! ∈ TZ := by
  intro l hl m hm
  have hl' : l ≠ 0 ∧ l.natAbs ≤ 10 := by
    simpa [plettersOK] using hl
  have hm256 : m < 256 := (mem_TZ.1 hm).1
  unfold pletter
  by_cases hpos : 0 < l
  · rw [if_pos hpos]
    exact TZ_conj (g := l.toNat - 1) (by omega) hm256 hm
  · rw [if_neg hpos]
    exact TZ_conj_inv (g := (-l).toNat - 1) (by omega) hm256 hm

theorem zero_mem_TZ : 0 ∈ TZ :=
  mem_TZ.2 ⟨by norm_num, by rw [qb_zero]; exact (ZJ.map rhoJ).one_mem⟩

theorem map_ZJ_le_Qbar : ZJ.map rhoJ ≤ Qbar := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
  exact mem_QJ.1 hz.1

theorem card_TZ : TZ.card = Nat.card (ZJ.map rhoJ) := by
  let f : TZ → ZJ.map rhoJ := fun m => ⟨qb m, (mem_TZ.1 m.2).2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h : qb a = qb b := congrArg Subtype.val hab
    exact Subtype.ext (qb_inj (mem_TZ.1 a.2).1 (mem_TZ.1 b.2).1 h)
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨m, hm⟩ := Qbar_subset (mem_QJ.1 hz.1)
    have hm' : qb m = rhoJ z := hm
    refine ⟨⟨m, mem_TZ.2 ⟨m.2, ?_⟩⟩, Subtype.ext hm'⟩
    rw [hm']
    exact hx
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_coe]

theorem card_TZ_dvd : TZ.card ∣ 256 := by
  rw [card_TZ, ← card_Qbar]
  exact Subgroup.card_dvd_of_le map_ZJ_le_Qbar

theorem t4G_mem_center : t4G ∈ Subgroup.center CJ :=
  Subgroup.mem_center_iff.2 fun g => (t4G_central g).symm

theorem zpowers_t4G_central {w : CJ} (hw : w ∈ Subgroup.zpowers t4G) (y : CJ) :
    w * y = y * w :=
  ((Subgroup.mem_center_iff.1 (Subgroup.zpowers_le.2 t4G_mem_center hw)) y).symm

theorem centre_QJ_le (hnc : ∃ x ∈ QJ, ∃ y ∈ QJ, x * y ≠ y * x) :
    ∀ x ∈ QJ, (∀ y ∈ QJ, x * y = y * x) → x ∈ Subgroup.zpowers t4G := by
  intro x hx hxc
  have hxZ : x ∈ ZJ := ⟨hx, Subgroup.mem_centralizer_iff.2 fun y hy => (hxc y hy).symm⟩
  rcases class_trichotomy sideF4ClassOK_true TZ (fun m hm => (mem_TZ.1 hm).1) zero_mem_TZ
      TZ_closed card_TZ_dvd with h | h
  · have hmem : rhoJ x ∈ ZJ.map rhoJ := Subgroup.mem_map_of_mem _ hxZ
    obtain ⟨m, hm⟩ := Qbar_subset (mem_QJ.1 hx)
    have hm' : qb m = rhoJ x := hm
    have hmT : m.val ∈ TZ := mem_TZ.2 ⟨m.2, by rw [hm']; exact hmem⟩
    rw [h, Finset.mem_singleton] at hmT
    have h1 : rhoJ x = 1 := by rw [← hm', hmT, qb_zero]
    rw [← ker_rhoJ]
    exact h1
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    have hdec : ∀ y ∈ QJ, ∃ z ∈ ZJ, z⁻¹ * y ∈ Subgroup.zpowers t4G := by
      intro y hy
      obtain ⟨m, hm⟩ := Qbar_subset (mem_QJ.1 hy)
      have hm' : qb m = rhoJ y := hm
      have hmT : m.val ∈ TZ := by rw [h]; exact Finset.mem_range.2 m.2
      obtain ⟨z, hz, hzm⟩ := Subgroup.mem_map.1 (mem_TZ.1 hmT).2
      refine ⟨z, hz, ?_⟩
      rw [← ker_rhoJ, MonoidHom.mem_ker, map_mul, map_inv, hzm, hm', inv_mul_cancel]
    obtain ⟨za, hza, hta⟩ := hdec a ha
    have hw : ∀ y : CJ, (za⁻¹ * a) * y = y * (za⁻¹ * a) := zpowers_t4G_central hta
    have hzb : b * za = za * b := Subgroup.mem_centralizer_iff.1 hza.2 b hb
    apply hab
    calc a * b = za * ((za⁻¹ * a) * b) := by group
      _ = za * (b * (za⁻¹ * a)) := by rw [hw b]
      _ = (za * b) * (za⁻¹ * a) := by group
      _ = (b * za) * (za⁻¹ * a) := by rw [hzb]
      _ = b * a := by group

end Radical

end CFSG.EvenSporadicStandard.HNRecog.SideF4
