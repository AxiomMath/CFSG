module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolCount
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Lift
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Statement

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.RankThree.PartTwo Equiv Equiv.Perm MulAction
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

section Orbits

variable {Ω : Type*} {E : Subgroup (Perm Ω)}

theorem mem_orbit_iff_perm {x y : Ω} : y ∈ orbit E x ↔ ∃ g ∈ E, g x = y := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

theorem apply_mem_orbit_iff {g : Perm Ω} (hg : g ∈ E) {x y : Ω} :
    g y ∈ orbit E x ↔ y ∈ orbit E x := by
  constructor
  · intro h
    obtain ⟨h', hh', hh'y⟩ := mem_orbit_iff_perm.1 h
    refine mem_orbit_iff_perm.2 ⟨g⁻¹ * h', E.mul_mem (E.inv_mem hg) hh', ?_⟩
    rw [Perm.mul_apply, hh'y, perm_inv_apply_apply]
  · intro h
    obtain ⟨h', hh', rfl⟩ := mem_orbit_iff_perm.1 h
    exact mem_orbit_iff_perm.2 ⟨g * h', E.mul_mem hg hh', rfl⟩

theorem isPretransitive_of_forall_mem_orbit {i₀ : Ω} (h : ∀ j, j ∈ orbit E i₀) :
    IsPretransitive E Ω :=
  ⟨fun x y => by
    obtain ⟨g, rfl⟩ := h x
    obtain ⟨g', rfl⟩ := h y
    exact ⟨g' * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩⟩

variable [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem exists_pair_of_card_orbit_eq_two {p : Ω} (h : Nat.card (orbit E p) = 2) :
    ∃ q, q ≠ p ∧ ∀ g ∈ E, g p = p ∧ g q = q ∨ g p = q ∧ g q = p := by
  have hfin := Set.toFinite (orbit E p)
  have h2 : (orbit E p).ncard ≤ 2 := by rw [← Nat.card_coe_set_eq, h]
  obtain ⟨q, hq, hqp⟩ := Set.exists_ne_of_one_lt_ncard
    (by rw [← Nat.card_coe_set_eq, h]; norm_num : 1 < (orbit E p).ncard) p
  refine ⟨q, hqp, fun g hg => ?_⟩
  have hgp : g p ∈ orbit E p := mem_orbit_iff_perm.2 ⟨g, hg, rfl⟩
  have hgq : g q ∈ orbit E p := (apply_mem_orbit_iff hg).2 hq
  rcases eq_of_mem_of_ncard_le hfin h2 (mem_orbit_self p) hq (Ne.symm hqp) hgp with h1 | h1 <;>
    rcases eq_of_mem_of_ncard_le hfin h2 (mem_orbit_self p) hq (Ne.symm hqp) hgq with h3 | h3
  · exact absurd (g.injective (h3.trans h1.symm)) hqp
  · exact Or.inl ⟨h1, h3⟩
  · exact Or.inr ⟨h1, h3⟩
  · exact absurd (g.injective (h3.trans h1.symm)) hqp

theorem four_le_card_orbit (hE : IsExp2 E) {p : Ω} (h1 : Nat.card (orbit E p) ≠ 1)
    (h2 : Nat.card (orbit E p) ≠ 2) : 4 ≤ Nat.card (orbit E p) := by
  obtain ⟨d, hd⟩ := hE.card_orbit p
  rw [hd] at h1 h2 ⊢
  rcases d with _ | _ | d
  · exact absurd (pow_zero 2) h1
  · exact absurd (pow_one 2) h2
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (d + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem even_of_card_orbit_ne_one (hE : IsExp2 E) (h : ∀ p : Ω, Nat.card (orbit E p) ≠ 1) :
    Even (Nat.card Ω) := by
  rw [card_eq_sum_orbits E]
  refine Finset.even_sum _ fun ω _ => ?_
  obtain ⟨d, hd⟩ := hE.card_orbit ω.out
  rw [hd]
  rcases d with _ | d
  · exact absurd (hd.trans (pow_zero 2)) (h ω.out)
  · exact Nat.even_pow.2 ⟨even_two, by omega⟩

theorem four_dvd_of_four_le_card_orbit (hE : IsExp2 E) (h : ∀ p : Ω, 4 ≤ Nat.card (orbit E p)) :
    4 ∣ Nat.card Ω := by
  rw [card_eq_sum_orbits E]
  refine Finset.dvd_sum fun ω _ => ?_
  obtain ⟨d, hd⟩ := hE.card_orbit ω.out
  have h4 := h ω.out
  rw [hd] at h4 ⊢
  rcases d with _ | _ | d
  · norm_num at h4
  · norm_num at h4
  · exact ⟨2 ^ d, by ring⟩

end Orbits

theorem card_orbit_le_card_orbit {m n : ℕ} (ι : Fin m ↪ Fin n) {E : Subgroup (Perm (Fin n))}
    {B : Subgroup (Perm (Fin m))} (hEB : ∀ g ∈ E, ∃ b ∈ B, ∀ j, ι (b j) = g (ι j)) (i : Fin m) :
    Nat.card (orbit E (ι i)) ≤ Nat.card (orbit B i) := by
  have key : ∀ y : orbit E (ι i), ∃ j : orbit B i, ι j = y := by
    rintro ⟨y, hy⟩
    obtain ⟨g, hg, rfl⟩ := mem_orbit_iff_perm.1 hy
    obtain ⟨b, hb, hbg⟩ := hEB g hg
    exact ⟨⟨b i, mem_orbit_iff_perm.2 ⟨b, hb, rfl⟩⟩, hbg i⟩
  choose f hf using key
  exact Nat.card_le_card_of_injective f fun y₁ y₂ h =>
    Subtype.ext ((hf y₁).symm.trans (by rw [h, hf]))

section Image

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}
  {A : Subgroup (MulAut V)}

theorem mem_map_subgroupOf {g : Perm (Fin n)} :
    g ∈ (A.subgroupOf H).map ψ ↔ ∃ a : ↥H, (a : MulAut V) ∈ A ∧ ψ a = g :=
  ⟨fun ⟨a, ha, hag⟩ => ⟨a, ha, hag⟩, fun ⟨a, ha, hag⟩ => ⟨a, ha, hag⟩⟩

theorem isExp2_map_subgroupOf (hA : IsElemAbelian2 A) : IsExp2 ((A.subgroupOf H).map ψ) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_mul]
  have : a * a = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, ← pow_two]
    exact hA.2 _ ha)
  rw [this, map_one]

end Image

theorem card_altHeart_le_of_natVia {Y : Type} [CommGroup Y] [Finite Y] {G : Subgroup (MulAut Y)}
    {m : ℕ} {ψG : ↥G →* Perm (Fin m)} (hinj : Function.Injective ψG) (hnat : NatVia ψG (commV G))
    {A' : Subgroup (MulAut Y)} (hA' : IsFFStarOffender G A') :
    Nat.card (altHeart m) ≤ Nat.card ((A'.subgroupOf G).map ψG) *
      Nat.card (altFix m ((A'.subgroupOf G).map ψG)) := by
  obtain ⟨π, hπ, hker, heq⟩ := hnat
  have hAB : ∀ b ∈ (A'.subgroupOf G).map ψG, ∃ a ∈ A', ∀ u v : ↥(commV G), (v : Y) = a u →
      Multiplicative.toAdd (π v) = altAct b (Multiplicative.toAdd (π u)) := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, fun u v huv => heq a u v huv⟩
  have n1 := card_mul_card_inf_fixV_le (Y := ⊤) inf_le_left le_top π hπ hker hAB
  rw [top_inf_eq, Subgroup.card_top] at n1
  have o1 : Nat.card Y ≤ Nat.card A' * Nat.card (fixV A') := by
    have := hA'.2.2.2 ⊥ bot_le
    rwa [B1.card_bot_mul_card_fixV] at this
  have hcard : Nat.card ((A'.subgroupOf G).map ψG) = Nat.card A' := by
    rw [Subgroup.card_map_of_injective hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'.1).toEquiv
  have hC : 0 < Nat.card (fixV A') := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hC
  calc Nat.card (altHeart m) * Nat.card (fixV A')
      ≤ Nat.card Y * Nat.card (altFix m ((A'.subgroupOf G).map ψG)) := n1
    _ ≤ Nat.card A' * Nat.card (fixV A') * Nat.card (altFix m ((A'.subgroupOf G).map ψG)) :=
        Nat.mul_le_mul_right _ o1
    _ = Nat.card ((A'.subgroupOf G).map ψG) *
          Nat.card (altFix m ((A'.subgroupOf G).map ψG)) * Nat.card (fixV A') := by
        rw [hcard]
        ring

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
