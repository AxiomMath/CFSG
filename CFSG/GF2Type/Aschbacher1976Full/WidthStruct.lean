module

public import CFSG.GF2Type.Aschbacher1976Full.WidthBasic

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Width

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Product

variable {z : G} {w : ℕ} {Z A : Subgroup G}

def mulHom (hD : Z4Data z w Z A) : ↥Z × ↥A →* G where
  toFun p := (p.1 : G) * (p.2 : G)
  map_one' := by simp
  map_mul' p q := by
    have hc : Commute (q.1 : G) (p.2 : G) := commute_ZA hD q.1.2 p.2.2
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    rw [Commute.mul_mul_mul_comm hc]

theorem range_mulHom (hD : Z4Data z w Z A) : (mulHom hD).range = Z ⊔ A := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    exact mul_mem_sup p.1.2 p.2.2
  · apply sup_le
    · intro c hc
      exact ⟨(⟨c, hc⟩, 1), by simp [mulHom]⟩
    · intro a ha
      exact ⟨(1, ⟨a, ha⟩), by simp [mulHom]⟩

theorem exists_decomp (hD : Z4Data z w Z A) {x : G} (hx : x ∈ Fz z) :
    ∃ c ∈ Z, ∃ a ∈ A, x = c * a := by
  rw [← hD.sup_eq, ← range_mulHom hD] at hx
  obtain ⟨p, rfl⟩ := hx
  exact ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩

theorem card_ker (hD : Z4Data z w Z A) (hz : orderOf z = 2) :
    Nat.card (mulHom hD).ker = 2 := by
  have hkey : ∀ p : (mulHom hD).ker,
      ((p : ↥Z × ↥A).1 : G) * ((p : ↥Z × ↥A).2 : G) = 1 :=
    fun p => p.2
  let f : (mulHom hD).ker → ↥(Z ⊓ A) := fun p =>
    ⟨((p : ↥Z × ↥A).1 : G), ⟨(p : ↥Z × ↥A).1.2, by
      rw [eq_inv_of_mul_eq_one_left (hkey p)]
      exact A.inv_mem (p : ↥Z × ↥A).2.2⟩⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro p q hpq
      have h1 : ((p : ↥Z × ↥A).1 : G) = ((q : ↥Z × ↥A).1 : G) := by
        have := congrArg Subtype.val hpq
        exact this
      have h2 : ((p : ↥Z × ↥A).2 : G) = ((q : ↥Z × ↥A).2 : G) := by
        rw [eq_inv_of_mul_eq_one_right (hkey p), eq_inv_of_mul_eq_one_right (hkey q), h1]
      apply Subtype.ext
      apply Prod.ext
      · exact Subtype.ext h1
      · exact Subtype.ext h2
    · intro c
      obtain ⟨hcZ, hcA⟩ := c.2
      have hq : ((⟨c, hcZ⟩, ⟨c⁻¹, A.inv_mem hcA⟩) : ↥Z × ↥A) ∈ (mulHom hD).ker := by
        rw [MonoidHom.mem_ker]
        exact mul_inv_cancel (c : G)
      exact ⟨⟨_, hq⟩, Subtype.ext rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hbij), hD.inf_eq, Nat.card_zpowers, hz]

theorem card_Fz (hD : Z4Data z w Z A) (hz : orderOf z = 2) :
    Nat.card (Fz z) = 2 ^ (2 * w + 2) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (mulHom hD).ker
  have h2 : Nat.card ((↥Z × ↥A) ⧸ (mulHom hD).ker) = Nat.card ↥(mulHom hD).range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (mulHom hD)).toEquiv
  rw [Nat.card_prod, hD.card_Z, hD.card_A, h2, card_ker hD hz, range_mulHom hD,
    hD.sup_eq] at h1
  have key : Nat.card (Fz z) * 2 = 2 ^ (2 * w + 2) * 2 := by
    rw [← h1]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) key

theorem Z_comm_F (hD : Z4Data z w Z A) {h : G} (hh : h ∈ Z) {f : G} (hf : f ∈ Fz z) :
    h * f = f * h := by
  obtain ⟨c, hc, a, ha, rfl⟩ := exists_decomp hD hf
  have h1 := comm_Z hD hh hc
  have h2 := (commute_ZA hD hh ha).eq
  rw [← mul_assoc, h1, mul_assoc c h a, h2, ← mul_assoc c a h]

theorem sq_F (hD : Z4Data z w Z A) (hz : orderOf z = 2) {x : G} (hx : x ∈ Fz z) :
    x ^ 2 = 1 ∨ x ^ 2 = z := by
  obtain ⟨c, hc, a, ha, rfl⟩ := exists_decomp hD hx
  have hcomm : Commute c a := commute_ZA hD hc ha
  rw [hcomm.mul_pow]
  have h4 : c ^ 4 = 1 := by
    have h := orderOf_dvd_natCard (⟨c, hc⟩ : Z)
    rw [hD.card_Z, Subgroup.orderOf_mk] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hc2 : c ^ 2 = 1 ∨ c ^ 2 = z := by
    by_cases h : c ^ 2 = 1
    · exact Or.inl h
    · refine Or.inr (involution_eq hD hz (Z.pow_mem hc 2) ?_ h)
      rw [← pow_mul]
      exact h4
  have ha2 := sq_mem_zpowers_A hD hz ha
  have hzz : z * z = 1 := by rw [← sq]; exact z_sq hz
  rcases hc2 with h1 | h1 <;> rcases mem_zpowers_involution hz ha2 with h2 | h2 <;>
    simp [h1, h2, hzz]

theorem comm_F (hD : Z4Data z w Z A) (hz : orderOf z = 2) {x y : G} (hx : x ∈ Fz z)
    (hy : y ∈ Fz z) : ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z := by
  obtain ⟨c, hc, a, ha, rfl⟩ := exists_decomp hD hx
  obtain ⟨c', hc', a', ha', rfl⟩ := exists_decomp hD hy
  have hcc' : Commute c c' := comm_Z hD hc hc'
  have hca' : Commute c a' := commute_ZA hD hc ha'
  have hc'a : Commute c' a := commute_ZA hD hc' ha
  have hc'a' : Commute c' a' := commute_ZA hD hc' ha'
  rw [comm_mul_left (commute_ZA hD hc ha) (hcc'.mul_right hca'),
    comm_mul_right hc'a' hc'a]
  exact mem_zpowers_involution hz (comm_mem_zpowers_A hD hz ha ha')

theorem mem_Z_of_comm (hD : Z4Data z w Z A) (hz : orderOf z = 2) {x : G} (hx : x ∈ Fz z)
    (hxA : ∀ b ∈ A, x * b = b * x) : x ∈ Z := by
  obtain ⟨c, hc, a, ha, rfl⟩ := exists_decomp hD hx
  have haA : ∀ b ∈ A, a * b = b * a := by
    intro b hb
    have h1 := hxA b hb
    have hcb : c * b = b * c := (commute_ZA hD hc hb).eq
    have h2 : c * (a * b) = c * (b * a) := by
      rw [← mul_assoc, h1, ← mul_assoc, ← hcb, mul_assoc]
    exact mul_left_cancel h2
  have haz := mem_zpowers_of_central hD hz ha haA
  have hzZ : zpowers z ≤ Z := zpowers_le.mpr hD.mem_z
  exact Z.mul_mem hc (hzZ haz)

end Product

end CFSG.GF2Type.Aschbacher1976Full.Width
