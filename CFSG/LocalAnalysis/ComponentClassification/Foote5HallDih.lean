module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSylowTools
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.Foote5.HallD8

open CFSG Subgroup DihedralGroup

variable {G : Type} [Group G] {D : Subgroup G}

theorem d8_cases : ∀ x : DihedralGroup 4, x * x = 1 ∨ x = r 1 ∨ x = r 3 := by decide

theorem d8_inv_cases :
    ∀ x : DihedralGroup 4, x * x = 1 → x = 1 ∨ x = r 2 ∨ x * r 1 * x⁻¹ = r 3 := by decide

theorem d8_exists_mul :
    ∀ x : DihedralGroup 4, ∃ a b : DihedralGroup 4, a * a = 1 ∧ b * b = 1 ∧ x = a * b := by
  decide

theorem d8_four : ∀ a b : DihedralGroup 4, a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → a ≠ b →
    (a * b) * (a * b) = 1 → r 2 = a ∨ r 2 = b ∨ r 2 = a * b := by decide

@[expose] def rot (e : D ≃* DihedralGroup 4) : G := (e.symm (r 1) : G)

@[expose] def cen (e : D ≃* DihedralGroup 4) : G := (e.symm (r 2) : G)

variable (e : D ≃* DihedralGroup 4)

theorem rot_mem : rot e ∈ D := (e.symm (r 1)).2

theorem cen_mem : cen e ∈ D := (e.symm (r 2)).2

theorem eq_of_e_eq {x y : G} (hx : x ∈ D) (hy : y ∈ D) (h : e ⟨x, hx⟩ = e ⟨y, hy⟩) : x = y :=
  congrArg Subtype.val (e.injective h)

theorem e_mul {x y : G} (hx : x ∈ D) (hy : y ∈ D) :
    e ⟨x * y, mul_mem hx hy⟩ = e ⟨x, hx⟩ * e ⟨y, hy⟩ := by
  rw [← map_mul]
  rfl

theorem e_inv {x : G} (hx : x ∈ D) : e ⟨x⁻¹, inv_mem hx⟩ = (e ⟨x, hx⟩)⁻¹ := by
  rw [← map_inv]
  rfl

theorem e_rot : e ⟨rot e, rot_mem e⟩ = r 1 := by
  change e (e.symm (r 1)) = r 1
  exact e.apply_symm_apply _

theorem e_cen : e ⟨cen e, cen_mem e⟩ = r 2 := by
  change e (e.symm (r 2)) = r 2
  exact e.apply_symm_apply _

theorem e_one : e ⟨1, one_mem D⟩ = 1 := map_one e

theorem rot_mul_rot : rot e * rot e = cen e := by
  apply eq_of_e_eq e (mul_mem (rot_mem e) (rot_mem e)) (cen_mem e)
  rw [e_mul e (rot_mem e) (rot_mem e), e_rot, e_cen, r_mul_r]
  rfl

theorem cen_mul_cen : cen e * cen e = 1 := by
  apply eq_of_e_eq e (mul_mem (cen_mem e) (cen_mem e)) (one_mem D)
  rw [e_mul e (cen_mem e) (cen_mem e), e_cen, e_one]
  decide

theorem cen_ne_one : cen e ≠ 1 := fun h => by
  have h1 := e_cen e
  have h2 : e ⟨cen e, cen_mem e⟩ = e ⟨1, one_mem D⟩ := by
    congr 1
    exact Subtype.ext h
  rw [h2, e_one] at h1
  exact absurd h1 (by decide)

theorem rot_ne_inv : rot e ≠ (rot e)⁻¹ := fun h => by
  have h2 : rot e * rot e = 1 := by
    calc rot e * rot e = rot e * (rot e)⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel _
  rw [rot_mul_rot] at h2
  exact cen_ne_one e h2

theorem inv_rot_mul_inv_rot : (rot e)⁻¹ * (rot e)⁻¹ = cen e := by
  rw [← mul_inv_rev, rot_mul_rot]
  exact inv_eq_of_mul_eq_one_right (cen_mul_cen e)

theorem mem_cases {x : G} (hx : x ∈ D) : x * x = 1 ∨ x = rot e ∨ x = (rot e)⁻¹ := by
  rcases d8_cases (e ⟨x, hx⟩) with h | h | h
  · left
    apply eq_of_e_eq e (mul_mem hx hx) (one_mem D)
    rw [e_mul e hx hx, e_one]
    exact h
  · right; left
    apply eq_of_e_eq e hx (rot_mem e)
    rw [e_rot]
    exact h
  · right; right
    apply eq_of_e_eq e hx (inv_mem (rot_mem e))
    rw [e_inv e (rot_mem e), e_rot, h]
    decide

theorem inv_cases {x : G} (hx : x ∈ D) (hx2 : x * x = 1) :
    x = 1 ∨ x = cen e ∨ x * rot e * x⁻¹ = (rot e)⁻¹ := by
  have h2 : e ⟨x, hx⟩ * e ⟨x, hx⟩ = 1 := by
    rw [← e_mul e hx hx, ← e_one e]
    congr 1
    exact Subtype.ext hx2
  rcases d8_inv_cases (e ⟨x, hx⟩) h2 with h | h | h
  · left
    apply eq_of_e_eq e hx (one_mem D)
    rw [e_one]
    exact h
  · right; left
    apply eq_of_e_eq e hx (cen_mem e)
    rw [e_cen]
    exact h
  · right; right
    apply eq_of_e_eq e (mul_mem (mul_mem hx (rot_mem e)) (inv_mem hx)) (inv_mem (rot_mem e))
    rw [e_mul e (mul_mem hx (rot_mem e)) (inv_mem hx), e_mul e hx (rot_mem e), e_inv e hx,
      e_inv e (rot_mem e), e_rot, h]
    decide

include e in
theorem exists_mul {x : G} (hx : x ∈ D) :
    ∃ a ∈ D, ∃ b ∈ D, a * a = 1 ∧ b * b = 1 ∧ x = a * b := by
  obtain ⟨a, b, ha, hb, hab⟩ := d8_exists_mul (e ⟨x, hx⟩)
  refine ⟨e.symm a, (e.symm a).2, e.symm b, (e.symm b).2, ?_, ?_, ?_⟩
  · rw [← coe_mul, ← map_mul, ha, map_one]
    rfl
  · rw [← coe_mul, ← map_mul, hb, map_one]
    rfl
  · have : (⟨x, hx⟩ : D) = e.symm a * e.symm b := by
      rw [← map_mul, ← hab, e.symm_apply_apply]
    exact congrArg Subtype.val this

theorem comm_cen {x : G} (hx : x ∈ D) : x * cen e = cen e * x := by
  apply eq_of_e_eq e (mul_mem hx (cen_mem e)) (mul_mem (cen_mem e) hx)
  rw [e_mul e hx (cen_mem e), e_mul e (cen_mem e) hx, e_cen]
  generalize e ⟨x, hx⟩ = y
  revert y
  decide

theorem conj_rot {t : G} (ht : t ∈ normalizer (D : Set G)) :
    t * rot e * t⁻¹ = rot e ∨ t * rot e * t⁻¹ = (rot e)⁻¹ := by
  have hmem : t * rot e * t⁻¹ ∈ D := (mem_normalizer_iff.mp ht (rot e)).mp (rot_mem e)
  rcases mem_cases e hmem with h | h | h
  · exfalso
    apply cen_ne_one e
    have : t * (rot e * rot e) * t⁻¹ = 1 := by
      rw [← h]
      group
    rw [rot_mul_rot] at this
    calc cen e = t⁻¹ * (t * cen e * t⁻¹) * t := by group
      _ = 1 := by rw [this]; group
  · exact Or.inl h
  · exact Or.inr h

theorem conj_cen {t : G} (ht : t ∈ normalizer (D : Set G)) : t * cen e * t⁻¹ = cen e := by
  have h : t * cen e * t⁻¹ = (t * rot e * t⁻¹) * (t * rot e * t⁻¹) := by
    rw [← rot_mul_rot]
    group
  rcases conj_rot e ht with h1 | h1 <;> rw [h, h1]
  · exact rot_mul_rot e
  · exact inv_rot_mul_inv_rot e

theorem sq_conj_rot {w : G} (hw : w ∈ normalizer (D : Set G)) :
    (w * w) * rot e * (w * w)⁻¹ = rot e := by
  have h : (w * w) * rot e * (w * w)⁻¹ = w * (w * rot e * w⁻¹) * w⁻¹ := by group
  rcases conj_rot e hw with h1 | h1
  · rw [h, h1, h1]
  · rw [h, h1, show w * (rot e)⁻¹ * w⁻¹ = (w * rot e * w⁻¹)⁻¹ by group, h1, inv_inv]

theorem sq_cases {w : G} (hw : w ∈ normalizer (D : Set G)) (hwD : w * w ∈ D)
    (hw2 : (w * w) * (w * w) = 1) : w * w = 1 ∨ w * w = cen e := by
  rcases inv_cases e hwD hw2 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (h.symm.trans (sq_conj_rot e hw)) (rot_ne_inv e).symm

variable (hcl : ∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
  ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d)
include hcl

theorem conj_mem_of_sic {d g : G} (hd : d ∈ D) (hd2 : d * d = 1)
    (hN : g⁻¹ * d * g ∈ normalizer (D : Set G)) : g⁻¹ * d * g ∈ D := by
  by_cases hd1 : d = 1
  · rw [hd1, mul_one, inv_mul_cancel]
    exact one_mem _
  by_contra hx
  have hdo : orderOf d = 2 := orderOf_eq_prime (by rw [sq]; exact hd2) hd1
  have hxo : orderOf (g⁻¹ * d * g) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) d
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, hdo]
  exact hcl _ hN hx hxo d hd hdo g⁻¹ (by group)

include e in
theorem conj_mem_of_sic_of_le {T : Subgroup G} (hT : T ≤ normalizer (D : Set G)) {g : G}
    (hg : ∀ d ∈ D, g⁻¹ * d * g ∈ T) {d : G} (hd : d ∈ D) : g⁻¹ * d * g ∈ D := by
  obtain ⟨a, ha, b, hb, ha2, hb2, rfl⟩ := exists_mul e hd
  rw [show g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) by group]
  exact mul_mem (conj_mem_of_sic hcl ha ha2 (hT (hg a ha)))
    (conj_mem_of_sic hcl hb hb2 (hT (hg b hb)))

include e in
theorem le_normalizer_of_sic [Finite G] {S : Subgroup G} (hS : IsPGroup 2 S) (hDS : D ≤ S) :
    S ≤ normalizer (D : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hle
  set H := S ⊓ normalizer (D : Set G) with hH
  have hlt : H < S := lt_of_le_of_ne inf_le_left fun h => hle (h ▸ inf_le_right)
  obtain ⟨y, hyS, hyH, hyN⟩ := FooteLit.exists_mem_normalizer_of_lt hS hlt
  apply hyH
  refine mem_inf.mpr ⟨hyS, ?_⟩
  have hHN : H ≤ normalizer (D : Set G) := inf_le_right
  have hsub : ∀ d ∈ D, y * d * y⁻¹ ∈ D := by
    intro d hd
    have h := conj_mem_of_sic_of_le e hcl hHN (g := y⁻¹) (fun d hd => by
      rw [inv_inv]
      exact (mem_normalizer_iff.mp hyN d).mp (mem_inf.mpr ⟨hDS hd, le_normalizer hd⟩)) hd
    rwa [inv_inv] at h
  have hmap : D.map (MulAut.conj y).toMonoidHom = D := by
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective (MulAut.conj y).injective).ge
    rintro _ ⟨d, hd, rfl⟩
    exact hsub d hd
  exact mem_normalizer_iff_map_conj_eq.mpr hmap

theorem mem_centralizer_of_conj {T : Subgroup G} (hT : T ≤ normalizer (D : Set G)) {d g : G}
    (hd : d * d = cen e) (hdg : g⁻¹ * d * g ∈ T) :
    g ∈ centralizer ({cen e} : Set G) := by
  have hsq : (g⁻¹ * d * g) * (g⁻¹ * d * g) = g⁻¹ * cen e * g := by
    rw [← hd]
    group
  have hwN : g⁻¹ * d * g ∈ normalizer (D : Set G) := hT hdg
  have hzN : g⁻¹ * cen e * g ∈ normalizer (D : Set G) := by
    rw [← hsq]
    exact mul_mem hwN hwN
  have hzD : g⁻¹ * cen e * g ∈ D := conj_mem_of_sic hcl (cen_mem e) (cen_mul_cen e) hzN
  have hz2 : (g⁻¹ * cen e * g) * (g⁻¹ * cen e * g) = 1 := by
    rw [show (g⁻¹ * cen e * g) * (g⁻¹ * cen e * g) = g⁻¹ * (cen e * cen e) * g by group,
      cen_mul_cen]
    group
  rw [← hsq] at hzD hz2
  rcases sq_cases e hwN hzD hz2 with h | h
  · exfalso
    rw [hsq] at h
    apply cen_ne_one e
    calc cen e = g * (g⁻¹ * cen e * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  · rw [hsq] at h
    rw [mem_centralizer_singleton_iff]
    calc g * cen e = g * (g⁻¹ * cen e * g) := by rw [h]
      _ = cen e * g := by group

end CFSG.ComponentClassification.Foote5.HallD8
