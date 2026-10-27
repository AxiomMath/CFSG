module

public import CFSG.RankThree.PartOne.CTP.AltGen
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallA

public section

namespace CFSG.ComponentClassification.SolMax

open Equiv Equiv.Perm CFSG.RankThree.PartOne.CTP.Alt

theorem eq_one_of_pow_five_of_commute {ζ π : Perm (Fin 9)} (hζ : ζ * ζ = 1) (hπ5 : π ^ 5 = 1)
    (hπζ : π * ζ = ζ * π) (hfix : ζ.supportᶜ.card < 5) : π = 1 := by
  classical
  by_contra h1
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have ho : orderOf π = 5 := orderOf_eq_prime hπ5 h1
  obtain ⟨k, hk⟩ := cycleType_prime_order (σ := π) (by rw [ho]; norm_num)
  have hsupp : π.support.card = 5 * (k + 1) := by
    rw [← sum_cycleType, hk, Multiset.sum_replicate, ho, smul_eq_mul]
    ring
  have hle : π.support.card ≤ 9 := by
    have := Finset.card_le_univ π.support
    rwa [Fintype.card_fin] at this
  have hk0 : k = 0 := by omega
  subst hk0
  have hcyc : π.IsCycle := card_cycleType_eq_one.mp (by rw [hk]; simp)
  have hζs : ∀ x, ζ x ∈ π.support ↔ x ∈ π.support := by
    intro x
    rw [mem_support, mem_support]
    have h2 : π (ζ x) = ζ (π x) := by rw [← Perm.mul_apply, hπζ, Perm.mul_apply]
    rw [h2]
    constructor
    · intro hx h
      exact hx (by rw [h])
    · intro hx h
      exact hx (ζ.injective h)
  have hodd : Odd (Nat.card {x // x ∈ π.support}) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_mem_eq_inter,
      Finset.univ_inter, hsupp]
    decide
  set ζ' : Perm {x // x ∈ π.support} := ζ.subtypePerm hζs with hζ'def
  have hζ'2 : ∀ x, ζ' (ζ' x) = x := by
    intro x
    apply Subtype.ext
    change ζ (ζ x) = x
    rw [← Perm.mul_apply, hζ, Perm.one_apply]
  obtain ⟨⟨x₀, hx₀⟩, hfx⟩ := exists_apply_eq_of_odd_card hodd ζ' hζ'2
  have hζx₀ : ζ x₀ = x₀ := congrArg Subtype.val hfx
  have hsub : π.support ⊆ ζ.supportᶜ := by
    intro y hy
    rw [Finset.mem_compl, mem_support, not_not]
    obtain ⟨i, rfl⟩ := hcyc.exists_pow_eq (mem_support.mp hx₀) (mem_support.mp hy)
    have hc : Commute ζ (π ^ i) := Commute.pow_right (show Commute ζ π from hπζ.symm) i
    rw [← Perm.mul_apply, hc.eq, Perm.mul_apply, hζx₀]
  have := Finset.card_le_card hsub
  omega

theorem swap_mul_swap_mul_swap_mul_swap {V : Type*} [DecidableEq V] {x y u v : V} (hxy : x ≠ y)
    (hxu : x ≠ u) (hxv : x ≠ v) (hyu : y ≠ u) (hyv : y ≠ v) (huv : u ≠ v) :
    (swap x u * swap u v) * (swap y v * swap v u) = swap y x * swap x u := by
  have := hxy.symm
  have := hxu.symm
  have := hxv.symm
  have := hyu.symm
  have := hyv.symm
  have := huv.symm
  ext w
  simp only [Perm.coe_mul, Function.comp_apply]
  by_cases h1 : w = x
  · subst h1
    simp [swap_apply_of_ne_of_ne, *]
  by_cases h2 : w = y
  · subst h2
    simp [swap_apply_of_ne_of_ne, *]
  by_cases h3 : w = u
  · subst h3
    simp [swap_apply_of_ne_of_ne, *]
  by_cases h4 : w = v
  · subst h4
    simp [swap_apply_of_ne_of_ne, *]
  simp [swap_apply_of_ne_of_ne, *]

theorem alternatingGroup_le_of_fix_and_point {N : Subgroup (Perm (Fin 9))} {G : Finset (Fin 9)}
    (hG2 : 2 ≤ G.card) (hF3 : 3 ≤ Gᶜ.card) {q : Fin 9} (hq : q ∉ G)
    (hNF : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → x ∉ G → y ∉ G → z ∉ G → swap x y * swap y z ∈ N)
    (hNG : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → (x ∈ G ∨ x = q) → (y ∈ G ∨ y = q) →
      (z ∈ G ∨ z = q) → swap x y * swap y z ∈ N) :
    alternatingGroup (Fin 9) ≤ N := by
  classical
  have hrot : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → swap x y * swap y z ∈ N →
      swap y z * swap z x ∈ N := fun x y z hxy hyz hxz h => by
    rwa [swap_mul_swap_rot hxy hyz hxz] at h
  have hflip : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → swap x y * swap y z ∈ N →
      swap x z * swap z y ∈ N := fun x y z hxy hyz hxz h => by
    have := N.inv_mem h
    rwa [swap_mul_swap_inv hxy hyz hxz] at this
  have htwo : ∀ x y z, y ≠ z → x ∉ G → y ∈ G → z ∈ G → swap x y * swap y z ∈ N := by
    intro x y z hyz hx hy hz
    have hxy : x ≠ y := fun h => hx (h ▸ hy)
    have hxz : x ≠ z := fun h => hx (h ▸ hz)
    have hqy : q ≠ y := fun h => hq (h ▸ hy)
    have hqz : q ≠ z := fun h => hq (h ▸ hz)
    by_cases hxq : x = q
    · subst hxq
      exact hNG _ _ _ hxy hyz hxz (Or.inr rfl) (Or.inl hy) (Or.inl hz)
    obtain ⟨w, hwG, hwq, hwx⟩ : ∃ w, w ∉ G ∧ w ≠ q ∧ w ≠ x := by
      by_contra h
      push Not at h
      have h1 : Gᶜ ⊆ {q, x} := by
        intro w hw
        rw [Finset.mem_compl] at hw
        by_cases hwq : w = q
        · simp [hwq]
        · simp [h w hw hwq]
      have h2 := Finset.card_le_card h1
      have h3 := Finset.card_le_two (a := q) (b := x)
      omega
    have hg : swap q x * swap x w ∈ N :=
      hNF _ _ _ (Ne.symm hxq) (Ne.symm hwx) (Ne.symm hwq) hq hx hwG
    have hc : swap q y * swap y z ∈ N :=
      hNG _ _ _ hqy hyz hqz (Or.inr rfl) (Or.inl hy) (Or.inl hz)
    have hwy : w ≠ y := fun h => hwG (h ▸ hy)
    have hwz : w ≠ z := fun h => hwG (h ▸ hz)
    set g := swap q x * swap x w with hgdef
    have h1 := N.mul_mem (N.mul_mem hg hc) (N.inv_mem hg)
    have hgq : g q = x := by
      rw [hgdef, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hxq) (Ne.symm hwq),
        swap_apply_left]
    have hgy : g y = y := by
      rw [hgdef, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hxy) (Ne.symm hwy),
        swap_apply_of_ne_of_ne (Ne.symm hqy) hxy.symm]
    have hgz : g z = z := by
      rw [hgdef, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hxz) (Ne.symm hwz),
        swap_apply_of_ne_of_ne (Ne.symm hqz) hxz.symm]
    have h2 : g * (swap q y * swap y z) * g⁻¹ = swap x y * swap y z := by
      have h3 : g * (swap q y * swap y z) * g⁻¹ =
          (g * swap q y * g⁻¹) * (g * swap y z * g⁻¹) := by group
      rw [h3, ← swap_apply_apply, ← swap_apply_apply, hgq, hgy, hgz]
    rwa [h2] at h1
  have hone : ∀ x x' y, x ≠ x' → x ∉ G → x' ∉ G → y ∈ G → swap x' x * swap x y ∈ N := by
    intro x x' y hxx' hx hx' hy
    obtain ⟨z, hzG, hzy⟩ : ∃ z ∈ G, z ≠ y := Finset.exists_mem_ne (by omega) y
    have hxy : x ≠ y := fun h => hx (h ▸ hy)
    have hxz : x ≠ z := fun h => hx (h ▸ hzG)
    have hx'y : x' ≠ y := fun h => hx' (h ▸ hy)
    have hx'z : x' ≠ z := fun h => hx' (h ▸ hzG)
    have h1 := htwo x y z hzy.symm hx hy hzG
    have h2 := hflip _ _ _ hx'y hzy.symm hx'z (htwo x' y z hzy.symm hx' hy hzG)
    have h3 := N.mul_mem h1 h2
    rwa [swap_mul_swap_mul_swap_mul_swap hxx' hxy hxz hx'y hx'z hzy.symm] at h3
  have h3 : ∀ x y z : Fin 9, x ≠ y → y ≠ z → x ≠ z → swap x y * swap y z ∈ N := by
    intro x y z hxy hyz hxz
    have r1 : ∀ a b c, a ≠ b → b ≠ c → a ≠ c → swap a b * swap b c ∈ N →
        swap b c * swap c a ∈ N := hrot
    by_cases hx : x ∈ G <;> by_cases hy : y ∈ G <;> by_cases hz : z ∈ G
    · exact hNG _ _ _ hxy hyz hxz (Or.inl hx) (Or.inl hy) (Or.inl hz)
    ·
      exact r1 _ _ _ (Ne.symm hxz) hxy (Ne.symm hyz) (htwo z x y hxy hz hx hy)
    ·
      exact r1 _ _ _ (Ne.symm hxz) hxy (Ne.symm hyz)
        (r1 _ _ _ hyz (Ne.symm hxz) (Ne.symm hxy) (htwo y z x (Ne.symm hxz) hy hz hx))
    ·
      exact r1 _ _ _ (Ne.symm hxz) hxy (Ne.symm hyz)
        (r1 _ _ _ hyz (Ne.symm hxz) (Ne.symm hxy) (hone z y x (Ne.symm hyz) hz hy hx))
    · exact htwo x y z hyz hx hy hz
    ·
      exact r1 _ _ _ (Ne.symm hxz) hxy (Ne.symm hyz) (hone x z y hxz hx hz hy)
    ·
      exact hone y x z (Ne.symm hxy) hy hx hz
    · exact hNF _ _ _ hxy hyz hxz hx hy hz
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro σ hσ
  have hσ3 : σ.IsThreeCycle := hσ
  obtain ⟨c, hc⟩ : σ.support.Nonempty := by
    rw [← Finset.card_pos, hσ3.card_support]
    norm_num
  have h1 := (hσ3.eq_swap_mul_swap_iff_mem_support (a := c)).mpr hc
  obtain ⟨hc1, hc2⟩ := List.nodup_cons.mp (hσ3.nodup_iff_mem_support.mpr hc)
  obtain ⟨hc3, -⟩ := List.nodup_cons.mp hc2
  simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hc1 hc3
  have h4 := h3 _ _ _ hc1.1 hc3 hc1.2
  change σ ∈ N
  rw [← h1] at h4
  exact h4

end CFSG.ComponentClassification.SolMax
