module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.AS35EBender
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace CQuotE

variable {G : Type} [Group G] (E : Set G)

abbrev Cx : Subgroup G := centralizer E

@[expose] def Nx : Subgroup (Cx E) where
  carrier := {c | c ∈ center (Cx E) ∧ Odd (orderOf c)}
  mul_mem' := by
    rintro a b ⟨ha, hao⟩ ⟨hb, hbo⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have hc : Commute a b := (mem_center_iff.mp hb a)
    exact Odd.of_dvd_nat (hao.mul hbo) (hc.orderOf_mul_dvd_lcm.trans
      (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)))
  one_mem' := ⟨one_mem _, by rw [orderOf_one]; decide⟩
  inv_mem' := by
    rintro a ⟨ha, hao⟩
    exact ⟨inv_mem ha, by rwa [orderOf_inv]⟩

theorem Nx_le_center : Nx E ≤ center (Cx E) := fun _ hc => hc.1

instance Nx_normal : (Nx E).Normal := Subgroup.normal_of_le_center (Nx_le_center E)

abbrev GQ : Type := Cx E ⧸ Nx E

abbrev mkQ : Cx E →* GQ E := QuotientGroup.mk' (Nx E)

theorem mkQ_surjective : Function.Surjective (mkQ E) := QuotientGroup.mk'_surjective _

variable {E}

theorem mkQ_eq_one_of_mem {n : Cx E} (hn : n ∈ Nx E) : mkQ E n = 1 :=
  (QuotientGroup.eq_one_iff _).mpr hn

theorem mkQ_mul_of_mem (c : Cx E) {n : Cx E} (hn : n ∈ Nx E) : mkQ E (c * n) = mkQ E c := by
  rw [map_mul, mkQ_eq_one_of_mem hn, mul_one]

theorem exists_mem_Nx_of_mkQ_eq {a b : Cx E} (h : mkQ E a = mkQ E b) :
    ∃ n ∈ Nx E, b = a * n :=
  ⟨a⁻¹ * b, (QuotientGroup.eq).mp h, by group⟩

theorem eq_one_of_mem_Nx_of_pow {n : Cx E} (hn : n ∈ Nx E) {m : ℕ} (hm : n ^ (2 ^ m) = 1) :
    n = 1 := by
  have h1 : orderOf n ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  have h2 : Nat.Coprime (orderOf n) (2 ^ m) := (Nat.coprime_two_right.mpr hn.2).pow_right m
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)

theorem eq_of_mkQ_eq {a b : Cx E} {m : ℕ} (ha : a ^ (2 ^ m) = 1) (hb : b ^ (2 ^ m) = 1)
    (h : mkQ E a = mkQ E b) : a = b := by
  obtain ⟨n, hn, rfl⟩ := exists_mem_Nx_of_mkQ_eq h
  have hc : Commute a n := mem_center_iff.mp hn.1 a
  have h1 : n ^ (2 ^ m) = 1 := by
    rw [hc.mul_pow, ha, one_mul] at hb
    exact hb
  rw [eq_one_of_mem_Nx_of_pow hn h1, mul_one]

theorem commute_of_mkQ_commute {a u : Cx E} {m : ℕ} (hu : u ^ (2 ^ m) = 1)
    (h : mkQ E a * mkQ E u = mkQ E u * mkQ E a) : a * u = u * a := by
  have h1 : (a * u * a⁻¹) ^ (2 ^ m) = 1 := by
    rw [conj_pow, hu, mul_one, mul_inv_cancel]
  have h2 : mkQ E (a * u * a⁻¹) = mkQ E u := by
    rw [map_mul, map_mul, map_inv, h, mul_assoc, mul_inv_cancel, mul_one]
  have h3 := eq_of_mkQ_eq h1 hu h2
  calc a * u = a * u * a⁻¹ * a := by group
    _ = u * a := by rw [h3]

theorem mkQ_conj (a b : Cx E) : mkQ E (a * b * a⁻¹) = mkQ E a * mkQ E b * (mkQ E a)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

theorem conj_mem_Cx {g c : G} (hg : ∀ e ∈ E, g⁻¹ * e * g ∈ E) (hc : c ∈ Cx E) :
    g * c * g⁻¹ ∈ Cx E := by
  rw [mem_centralizer_iff] at hc ⊢
  intro e he
  have h1 := hc _ (hg e he)
  calc e * (g * c * g⁻¹) = g * ((g⁻¹ * e * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * e * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * e := by group

@[expose] def conjCx (g : G) (hg : ∀ e ∈ E, g * e * g⁻¹ ∈ E)
    (hg' : ∀ e ∈ E, g⁻¹ * e * g ∈ E) : Cx E ≃* Cx E where
  toFun c := ⟨g * c * g⁻¹, conj_mem_Cx hg' c.2⟩
  invFun c := ⟨g⁻¹ * c * g⁻¹⁻¹, conj_mem_Cx (by simpa using hg) c.2⟩
  left_inv c := Subtype.ext (by simp only; group)
  right_inv c := Subtype.ext (by simp only; group)
  map_mul' a b := Subtype.ext (by
    change g * (a * b : G) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹)
    group)

@[simp] theorem coe_conjCx (g : G) (hg : ∀ e ∈ E, g * e * g⁻¹ ∈ E)
    (hg' : ∀ e ∈ E, g⁻¹ * e * g ∈ E) (c : Cx E) :
    ((conjCx g hg hg' c : Cx E) : G) = g * c * g⁻¹ := rfl

theorem mem_Nx_of_mulEquiv (e : Cx E ≃* Cx E) {c : Cx E} (hc : c ∈ Nx E) : e c ∈ Nx E := by
  refine ⟨mem_center_iff.mpr fun d => ?_, by rw [MulEquiv.orderOf_eq]; exact hc.2⟩
  obtain ⟨d', rfl⟩ := e.surjective d
  rw [← map_mul, ← map_mul, mem_center_iff.mp hc.1 d']

theorem map_Nx_of_mulEquiv (e : Cx E ≃* Cx E) : (Nx E).map (e : Cx E →* Cx E) = Nx E := by
  refine le_antisymm ?_ fun c hc => ⟨e.symm c, mem_Nx_of_mulEquiv e.symm hc, by simp⟩
  rintro _ ⟨c, hc, rfl⟩
  exact mem_Nx_of_mulEquiv e hc

@[expose] noncomputable def conjQ (g : G) (hg : ∀ e ∈ E, g * e * g⁻¹ ∈ E)
    (hg' : ∀ e ∈ E, g⁻¹ * e * g ∈ E) : GQ E ≃* GQ E :=
  QuotientGroup.congr (Nx E) (Nx E) (conjCx g hg hg') (map_Nx_of_mulEquiv _)

theorem conjQ_mkQ (g : G) (hg : ∀ e ∈ E, g * e * g⁻¹ ∈ E)
    (hg' : ∀ e ∈ E, g⁻¹ * e * g ∈ E) (c : Cx E) :
    conjQ g hg hg' (mkQ E c) = mkQ E (conjCx g hg hg' c) := rfl

@[expose] def xC {x : G} (hxc : x ∈ Cx E) : Cx E := ⟨x, hxc⟩

theorem xC_mem_Nx {x : G} (hxE : x ∈ E) (hxc : x ∈ Cx E) (hx : Odd (orderOf x)) :
    xC hxc ∈ Nx E := by
  refine ⟨mem_center_iff.mpr fun c => Subtype.ext ?_, by rwa [xC, Subgroup.orderOf_mk]⟩
  exact (mem_centralizer_iff.mp c.2 x hxE).symm

theorem card_GQ_lt [Finite G] {x : G} (hxE : x ∈ E) (hxc : x ∈ Cx E) (hx3 : orderOf x = 3) :
    Nat.card (GQ E) < Nat.card G := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Nx E)
  have hxN : xC hxc ∈ Nx E := xC_mem_Nx hxE hxc (by rw [hx3]; decide)
  have hx1 : xC hxc ≠ 1 := by
    intro h
    have := congrArg (fun w : Cx E => (w : G)) h
    simp only [xC, OneMemClass.coe_one] at this
    rw [this, orderOf_one] at hx3
    exact absurd hx3 (by norm_num)
  have h2 : 1 < Nat.card (Nx E) := (Subgroup.one_lt_card_iff_ne_bot _).mpr fun h => hx1 (by
    rw [h, mem_bot] at hxN
    exact hxN)
  have h3 : Nat.card (Cx E) ≤ Nat.card G := Subgroup.card_le_card_group _
  have h4 : 0 < Nat.card (Cx E ⧸ Nx E) := Nat.card_pos
  change Nat.card (Cx E ⧸ Nx E) < Nat.card G
  have h5 : Nat.card (Cx E ⧸ Nx E) * 2 ≤ Nat.card (Cx E) := by
    rw [h1]
    exact Nat.mul_le_mul_left _ h2
  omega

end CQuotE

end CFSG.LargeExtraspecial
