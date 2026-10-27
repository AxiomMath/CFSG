module

public import CFSG.GF2Type.Aschbacher1976Full.WidthStab
public import CFSG.GF2Type.Aschbacher1976Common.CyclicTICommute

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Width

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup
open CFSG.GF2Type.Aschbacher1976Common (commute_of_conjugate_le)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conjugate_one' {H : Subgroup G} : conjugate H 1 = H := by
  ext x
  simp [mem_conjugate_iff]

theorem card_conjugate' (Z : Subgroup G) (g : G) :
    Nat.card ↥(conjugate Z g) = Nat.card ↥Z := by
  unfold conjugate
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

theorem isCyclic_conjugate' (Z : Subgroup G) [IsCyclic Z] (g : G) :
    IsCyclic ↥(conjugate Z g) :=
  isCyclic_of_surjective
    (Subgroup.equivMapOfInjective Z (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).toMonoidHom
    (Subgroup.equivMapOfInjective Z (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).surjective

section Z1

variable {z : G} {w : ℕ} {Z A : Subgroup G}

theorem stabSub_isPGroup (hD : Z4Data z w Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z)) :
    IsPGroup 2 ↥(stabSub hD hz) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_card]
  have hpos : Nat.card ↥(stabSub hD hz) ≠ 0 := (Nat.card_pos).ne'
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hpos ?_⟩
  intro d hd hdn
  by_contra hd2
  have hodd : Odd d := hd.eq_two_or_odd'.resolve_left hd2
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(stabSub hD hz)) d hdn
  have hxG : orderOf (x : G) = d := by rw [Subgroup.orderOf_coe, hx]
  have h1 : (x : G) = 1 := stab_odd_eq_one hD hz hF2 x.2 (by rw [hxG]; exact hodd)
  rw [h1, orderOf_one] at hxG
  have := hd.one_lt
  omega

theorem stab_le_F (hD : Z4Data z w Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z)) :
    stabSub hD hz ≤ Fz z :=
  le_Fz_of_normal_two hF2 (fun h hh => (mem_stabSub.mp hh).1)
    (fun g hg x hx => stabSub_normal hD hz hg hx)
    (stabSub_isPGroup hD hz hF2)

theorem z1_mem_F (hD : Z4Data z w Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z))
    {g : G} (hg : ∀ x ∈ Z, g⁻¹ * x * g ∈ Hz z) : g⁻¹ * z * g ∈ Fz z := by
  obtain ⟨k, hkZ, hkord, hgen, hk2⟩ := exists_gen_Z hD hz
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hD.cyc
  have hAH : ∀ y ∈ conjugate Z g, y ∈ Hz z := by
    intro y hy
    have h1 := hg _ (mem_conjugate_iff.mp hy)
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rwa [e] at h1
  have hcard : Nat.card ↥(conjugate Z g) = 4 := by
    rw [card_conjugate', hD.card_Z]
  have hA2 : IsPGroup 2 ↥(conjugate Z g) := IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num)
  have hA4 : 4 ≤ Nat.card ↥(conjugate Z g) := by rw [hcard]
  have hA_cyc : IsCyclic ↥(conjugate Z g) := isCyclic_conjugate' Z g
  have hTI : ∀ g' : G, conjugate (conjugate Z g) g' = conjugate Z g ∨
      conjugate Z g ⊓ conjugate (conjugate Z g) g' = ⊥ := by
    intro g'
    rw [conjugate_conjugate]
    rcases conj_pair_eq_or_disjoint hD hz hF2 g (g * g') with h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr h1
  have hS : IsPGroup 2 ↥(conjugate Z g ⊔ Fz z) := by
    apply IsPGroup.to_sup_of_normal_right' hA2 hF2
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · intro hf
      exact Fz_conj_mem (hAH y hy) hf
    · intro hf
      have h1 := Fz_conj_mem ((Hz z).inv_mem (hAH y hy)) hf
      have e : y⁻¹ * (y * f * y⁻¹) * y⁻¹⁻¹ = f := by group
      rwa [e] at h1
  obtain ⟨k', hk'⟩ : ∃ k' : G, k' = g⁻¹ * k * g := ⟨_, rfl⟩
  have hk'A : k' ∈ conjugate Z g := by
    apply mem_conjugate_iff.mpr
    rw [hk', show g * (g⁻¹ * k * g) * g⁻¹ = k by group]
    exact hkZ
  have hk'H : k' ∈ Hz z := hAH k' hk'A
  have hz1 : g⁻¹ * z * g = k' ^ 2 := by
    rw [hk', ← hk2, sq, sq]
    group
  have hcomm : ∀ a ∈ Fz z, k' * (a⁻¹ * k' * a) = (a⁻¹ * k' * a) * k' := by
    intro a ha
    have haS : a ∈ conjugate Z g ⊔ Fz z := Subgroup.mem_sup_right ha
    have hh1 : conjugate (conjugate Z g) a ≤ conjugate Z g ⊔ Fz z := by
      intro y hy
      rw [mem_conjugate_iff] at hy
      have hyA : y = a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ := by group
      rw [hyA]
      exact (conjugate Z g ⊔ Fz z).mul_mem
        ((conjugate Z g ⊔ Fz z).mul_mem ((conjugate Z g ⊔ Fz z).inv_mem haS)
          (Subgroup.mem_sup_left hy)) ((conjugate Z g ⊔ Fz z).inv_mem ((conjugate Z g ⊔ Fz z).inv_mem haS))
    have hg1 : conjugate (conjugate Z g) 1 ≤ conjugate Z g ⊔ Fz z := by
      rw [conjugate_one']
      exact (le_sup_left : conjugate Z g ≤ conjugate Z g ⊔ Fz z)
    have hk1 : k' ∈ conjugate (conjugate Z g) 1 := by
      rw [conjugate_one']
      exact hk'A
    have hy : a⁻¹ * k' * a ∈ conjugate (conjugate Z g) a := by
      apply mem_conjugate_iff.mpr
      rw [show a * (a⁻¹ * k' * a) * a⁻¹ = k' by group]
      exact hk'A
    exact commute_of_conjugate_le hA_cyc hA2 hA4 hTI hS hg1 hh1 k' hk1 (a⁻¹ * k' * a) hy
  have hF_c : ∀ a ∈ Fz z, a⁻¹ * k'⁻¹ * a * k' ∈ Fz z := by
    intro a ha
    have h2 : k'⁻¹ * a * k'⁻¹⁻¹ ∈ Fz z := Fz_conj_mem ((Hz z).inv_mem hk'H) ha
    rw [inv_inv] at h2
    have h3 := (Fz z).mul_mem ((Fz z).inv_mem ha) h2
    simpa only [mul_assoc] using h3
  have hformula : ∀ a ∈ Fz z, (g⁻¹ * z * g)⁻¹ * a * (g⁻¹ * z * g) =
      a * (a⁻¹ * k'⁻¹ * a * k') ^ 2 := by
    intro a ha
    obtain ⟨c, hcdef⟩ : ∃ c : G, c = a⁻¹ * k'⁻¹ * a * k' := ⟨_, rfl⟩
    rw [← hcdef]
    have hac : k'⁻¹ * a * k' = a * c := by
      rw [hcdef]
      group
    have hcX : c = (a⁻¹ * k' * a)⁻¹ * k' := by
      rw [hcdef]
      group
    have hkc' : Commute k' c := by
      rw [hcX]
      exact ((show Commute k' (a⁻¹ * k' * a) from hcomm a ha).inv_right).mul_right
        (Commute.refl k')
    have hkc : k'⁻¹ * c * k' = c := by
      calc k'⁻¹ * c * k' = k'⁻¹ * (c * k') := by group
        _ = k'⁻¹ * (k' * c) := by rw [← hkc'.eq]
        _ = c := by group
    rw [hz1, sq k']
    calc (k' * k')⁻¹ * a * (k' * k') = k'⁻¹ * (k'⁻¹ * a * k') * k' := by group
      _ = k'⁻¹ * (a * c) * k' := by rw [hac]
      _ = (k'⁻¹ * a * k') * (k'⁻¹ * c * k') := by group
      _ = (a * c) * c := by rw [hac, hkc]
      _ = a * c ^ 2 := by rw [sq, mul_assoc]
  have hz1H : g⁻¹ * z * g ∈ Hz z := by
    apply hAH
    apply mem_conjugate_iff.mpr
    rw [show g * (g⁻¹ * z * g) * g⁻¹ = z by group]
    exact hD.mem_z
  have hmem : g⁻¹ * z * g ∈ stabSub hD hz := by
    rw [mem_stabSub]
    refine ⟨hz1H, fun a ha => ?_⟩
    rw [hformula a ha, inv_mul_cancel_left]
    rcases sq_F hD hz (hF_c a ha) with h | h
    · rw [h]
      exact Z.one_mem
    · rw [h]
      exact hD.mem_z
  exact stab_le_F hD hz hF2 hmem

end Z1

end CFSG.GF2Type.Aschbacher1976Full.Width
