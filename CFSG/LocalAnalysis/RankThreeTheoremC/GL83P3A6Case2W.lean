module

public import CFSG.Open.LocalVocabulary

@[expose] public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6W

open CFSG.Open Subgroup

variable {G : Type} [Group G]

def Wsub (R : Subgroup G) : Subgroup G where
  carrier := {w | w ∈ R ∧ w ^ 2 = 1 ∧ ∀ r ∈ R, r * w = w * r}
  mul_mem' := by
    rintro a b ⟨haR, ha2, haC⟩ ⟨hbR, hb2, hbC⟩
    refine ⟨R.mul_mem haR hbR, ?_, fun r hr => ?_⟩
    · have hab : b * a = a * b := haC b hbR
      calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
        _ = a * (a * b) * b := by rw [hab]
        _ = a ^ 2 * b ^ 2 := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [ha2, hb2, one_mul]
    · calc r * (a * b) = (r * a) * b := by group
        _ = (a * r) * b := by rw [haC r hr]
        _ = a * (r * b) := by group
        _ = a * (b * r) := by rw [hbC r hr]
        _ = (a * b) * r := by group
  one_mem' := ⟨R.one_mem, by group, fun r _ => by group⟩
  inv_mem' := by
    rintro a ⟨haR, ha2, haC⟩
    refine ⟨R.inv_mem haR, ?_, fun r hr => ?_⟩
    · have : a⁻¹ ^ 2 = (a ^ 2)⁻¹ := by group
      rw [this, ha2]
      group
    · have := haC r hr
      calc r * a⁻¹ = a⁻¹ * (a * r) * a⁻¹ := by group
        _ = a⁻¹ * (r * a) * a⁻¹ := by rw [this]
        _ = a⁻¹ * r := by group

theorem Wsub_le (R : Subgroup G) : Wsub R ≤ R := fun _ hw => hw.1

theorem Wsub_sq {R : Subgroup G} {w : G} (hw : w ∈ Wsub R) : w ^ 2 = 1 := hw.2.1

theorem Wsub_central {R : Subgroup G} {w r : G} (hw : w ∈ Wsub R) (hr : r ∈ R) :
    r * w = w * r := hw.2.2 r hr

theorem Wsub_comm {R : Subgroup G} {a b : G} (ha : a ∈ Wsub R) (hb : b ∈ Wsub R) :
    a * b = b * a := hb.2.2 a ha.1

theorem isElemAbelian_Wsub (R : Subgroup G) : IsElemAbelian 2 (Wsub R) :=
  ⟨IsMulCommutative.of_setLike_mul_comm fun _ ha _ hb => Wsub_comm ha hb, fun _ hz => hz.2.1⟩

theorem conj_mem_Wsub {R : Subgroup G} {h : G} (hh : h ∈ normalizer (R : Set G)) {w : G}
    (hw : w ∈ Wsub R) : h * w * h⁻¹ ∈ Wsub R := by
  have hR := mem_normalizer_iff.mp hh
  refine ⟨(hR w).mp hw.1, ?_, fun r hr => ?_⟩
  · calc (h * w * h⁻¹) ^ 2 = h * w ^ 2 * h⁻¹ := conj_pow
      _ = 1 := by rw [Wsub_sq hw]; group
  ·
    have hr' : h⁻¹ * r * h ∈ R := by
      apply (hR (h⁻¹ * r * h)).mpr
      rwa [show h * (h⁻¹ * r * h) * h⁻¹ = r by group]
    have := Wsub_central hw hr'
    calc r * (h * w * h⁻¹) = h * ((h⁻¹ * r * h) * w) * h⁻¹ := by group
      _ = h * (w * (h⁻¹ * r * h)) * h⁻¹ := by rw [this]
      _ = (h * w * h⁻¹) * r := by group

theorem mem_normalizer_Wsub {R : Subgroup G} {h : G} (hh : h ∈ normalizer (R : Set G)) :
    h ∈ normalizer ((Wsub R : Subgroup G) : Set G) := by
  refine mem_normalizer_iff.mpr fun w => ⟨fun hw => conj_mem_Wsub hh hw, fun hw => ?_⟩
  have h1 := conj_mem_Wsub ((normalizer (R : Set G)).inv_mem hh) hw
  rwa [show h⁻¹ * (h * w * h⁻¹) * h⁻¹⁻¹ = w by group] at h1

theorem Wsub_ne_bot [Finite G] {R : Subgroup G} (hR : IsPGroup 2 R) (hne : R ≠ ⊥) :
    Wsub R ≠ ⊥ := by
  haveI : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hne
  haveI := hR.center_nontrivial
  obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center R)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR) z
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hz1' (orderOf_eq_one_iff.mp (by simpa using hk))
  obtain ⟨w, hw⟩ : ∃ w : R, w = z ^ (2 ^ (k - 1)) := ⟨_, rfl⟩
  have hw2 : w ^ 2 = 1 := by
    rw [hw, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
    rw [← hk]
    exact pow_orderOf_eq_one z
  have hw1 : w ≠ 1 := by
    intro h1
    rw [hw] at h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hk] at this
    have h2 : 2 ^ k ≤ 2 ^ (k - 1) := Nat.le_of_dvd (by positivity) this
    have h3 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hwc : w ∈ Subgroup.center R := hw ▸ Subgroup.pow_mem _ hz _
  intro hbot
  have hwmem : (w : G) ∈ Wsub R :=
    ⟨w.2, by simpa using congrArg Subtype.val hw2, fun r hr => by
      simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hwc ⟨r, hr⟩)⟩
  rw [hbot, mem_bot] at hwmem
  exact hw1 (Subtype.ext hwmem)

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6W
