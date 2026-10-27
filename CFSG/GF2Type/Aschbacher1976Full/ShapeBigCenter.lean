module

public import CFSG.GF2Type.Aschbacher1976Full.ShapeHallR3
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GF2Type.Aschbacher1976Full.ShapeBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Shape

open CFSG CFSG.SectionRank.Ccomm CFSG.Blueprint Subgroup

section Q4

variable {P : Type*} [Group P] [Finite P] {D E R : Subgroup P} {z : P}

def Q4 (c : CritData D E R z) : Subgroup P where
  carrier := {x | x ∈ D ∧ x ^ 4 = 1}
  one_mem' := ⟨one_mem _, one_pow 4⟩
  mul_mem' := fun {x y} hx hy => by
    obtain ⟨e, he, u, hu, rfl⟩ := c.exists_mul_of_mem_D hx.1
    obtain ⟨e', he', u', hu', rfl⟩ := c.exists_mul_of_mem_D hy.1
    have h1 : Commute e u := CritData.Z_comm D hu (c.E_le_D he)
    have h2 : Commute e' u' := CritData.Z_comm D hu' (c.E_le_D he')
    have hu4 : u ^ 4 = 1 := by
      have := hx.2
      rwa [h1.mul_pow, c.E_four e he, one_mul] at this
    have hu4' : u' ^ 4 = 1 := by
      have := hy.2
      rwa [h2.mul_pow, c.E_four e' he', one_mul] at this
    refine ⟨mul_mem hx.1 hy.1, ?_⟩
    have h3 : Commute u e' := (CritData.Z_comm D hu (c.E_le_D he')).symm
    have h4 : e * u * (e' * u') = (e * e') * (u * u') := by
      calc e * u * (e' * u') = e * (u * e') * u' := by group
        _ = e * (e' * u) * u' := by rw [h3.eq]
        _ = (e * e') * (u * u') := by group
    have h5 : Commute (e * e') (u * u') :=
      CritData.Z_comm D (mul_mem hu hu') (c.E_le_D (mul_mem he he'))
    have h6 : Commute u u' := CritData.Z_comm D hu' (CritData.Z_le_D D hu)
    rw [h4, h5.mul_pow, c.E_four _ (mul_mem he he'), one_mul, h6.mul_pow, hu4, hu4', one_mul]
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

theorem mem_Q4 {c : CritData D E R z} {x : P} : x ∈ Q4 c ↔ x ∈ D ∧ x ^ 4 = 1 := Iff.rfl

theorem E_le_Q4 (c : CritData D E R z) : E ≤ Q4 c :=
  fun e he => ⟨c.E_le_D he, c.E_four e he⟩

theorem mem_Q4_of_mem_Z (c : CritData D E R z) {y : P} (hy : y ∈ Zof D) (hy4 : y ^ 4 = 1) :
    y ∈ Q4 c :=
  ⟨CritData.Z_le_D D hy, hy4⟩

end Q4

section Centralizer

variable {G : Type} [Group G] [Finite G] {z : G}

theorem Q4_conj {D E R : Subgroup ↥(Fz z)} {zz : ↥(Fz z)} (c : CritData D E R zz) {h : G}
    (hh : h ∈ Hz z) {x : G} (hx : x ∈ lift (Q4 c)) : h * x * h⁻¹ ∈ lift (Q4 c) := by
  haveI : D.Characteristic := c.crit.1
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
  have hq' := mem_Q4.mp hq
  refine Subgroup.mem_map.mpr ⟨actF z ⟨h, hh⟩ q, mem_Q4.mpr ⟨?_, ?_⟩, rfl⟩
  · exact FiveTransitive.CharacteristicAutomorphism.mem D _ hq'.1
  · rw [← map_pow, hq'.2, map_one]

theorem cent_Q4_le (hsymp : CFSG.Open.GLASymplecticType (Fz z)) {D E R : Subgroup ↥(Fz z)}
    {zz : ↥(Fz z)} (c : CritData D E R zz)
    (hmax : ∀ D' : Subgroup ↥(Fz z), ThompsonCritical D' → Nat.card D' ≤ Nat.card D)
    (hk8 : 8 ≤ Nat.card (Zof D)) {h : G} (hh : h ∈ Hz z)
    (hc : ∀ x ∈ lift (Q4 c), h * x = x * h) : h ∈ lift (Zof D) := by
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  haveI := c.char
  set N : Subgroup G :=
    Subgroup.centralizer ((lift (Q4 c) : Subgroup G) : Set G) ⊓ Hz z with hN
  have hNH : N ≤ Hz z := inf_le_right
  have hNnorm : ∀ u ∈ Hz z, ∀ n ∈ N, u * n * u⁻¹ ∈ N := by
    intro u hu n hn
    obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.mp hn
    refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (mul_mem hu hn2) (inv_mem hu)⟩
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : u⁻¹ * x * u⁻¹⁻¹ ∈ lift (Q4 c) := Q4_conj c (inv_mem hu) hx
    have h1 := mem_centralizer_iff.mp hn1 _ hx'
    rw [inv_inv] at h1
    calc x * (u * n * u⁻¹) = u * ((u⁻¹ * x * u) * n) * u⁻¹ := by group
      _ = u * (n * (u⁻¹ * x * u)) * u⁻¹ := by rw [h1]
      _ = (u * n * u⁻¹) * x := by group
  have hNp : IsPGroup 2 ↥N := by
    refine isPGroup_two_of_forall_odd fun n hodd => ?_
    have hodd' : Odd (orderOf (n : G)) := by
      rw [Subgroup.orderOf_coe]
      exact hodd
    have hn1 : (n : G) = 1 := by
      refine eq_one_of_stable_cyclic hF2 (hNH n.2) hodd' c.cyc fun d hd => ?_
      have hd' : d ∈ D := by
        have : d ∈ centralizer ((Zof D : Subgroup ↥(Fz z)) : Set ↥(Fz z)) :=
          mem_centralizer_iff.mpr hd
        rwa [c.cent] at this
      obtain ⟨e, he, y, hy, rfl⟩ := c.exists_mul_of_mem_D hd'
      have h1 : (e : G) * n = n * e :=
        mem_centralizer_iff.mp (Subgroup.mem_inf.mp n.2).1 (e : G) (mem_lift.mpr (E_le_Q4 c he))
      have h2 := fixes_of_cyclic hF2 (hNH n.2) hodd' c.cyc y hy
      calc (n : G) * ((e * y : ↥(Fz z)) : G) * (n : G)⁻¹ =
          ((n : G) * e * (n : G)⁻¹) * ((n : G) * y * (n : G)⁻¹) := by
            simp only [Subgroup.coe_mul]
            group
        _ = ((e * y : ↥(Fz z)) : G) := by
            rw [h2, show (n : G) * e * (n : G)⁻¹ = e by rw [mul_inv_eq_iff_eq_mul]; exact h1.symm]
            rfl
    exact Subtype.ext hn1
  have hNF : N ≤ Fz z := le_Fz_of_normalized_isPGroup hF2 hNH hNnorm hNp
  have hhN : h ∈ N :=
    Subgroup.mem_inf.mpr ⟨mem_centralizer_iff.mpr fun x hx => (hc x hx).symm, hh⟩
  set g : ↥(Fz z) := ⟨h, hNF hhN⟩ with hg
  have hgR : g ∈ R := by
    rw [c.R_eq, mem_centralizer_iff]
    intro e he
    exact Subtype.ext (hc (e : G) (mem_lift.mpr (E_le_Q4 c he))).symm
  have hgD : g ∈ D := by
    refine hallR hF2 c hmax hk8 (g := g) fun y hy hy4 => ?_
    have h1 := hc (y : G) (mem_lift.mpr (mem_Q4_of_mem_Z c hy hy4))
    refine Subtype.ext ?_
    change h * (y : G) * h⁻¹ = y
    rw [mul_inv_eq_iff_eq_mul]
    exact h1
  have hgZ : g ∈ Zof D := by
    have : g ∈ R ⊓ centralizer ((Zof D : Subgroup ↥(Fz z)) : Set ↥(Fz z)) :=
      ⟨hgR, by rw [c.cent]; exact hgD⟩
    rwa [c.RZ] at this
  exact mem_lift.mpr hgZ

end Centralizer

end CFSG.GF2Type.Aschbacher1976Full.Shape
