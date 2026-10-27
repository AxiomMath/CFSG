module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup DihedralGroup

theorem zmod_exists_two_mul (n : ℕ) [NeZero n] (e : ZMod n) :
    ∃ c : ZMod n, e = 2 * c ∨ e = 2 * c + 1 := by
  obtain ⟨c, hc | hc⟩ := Nat.even_or_odd' (ZMod.val e)
  · refine ⟨(c : ZMod n), Or.inl ?_⟩
    have h := ZMod.natCast_zmod_val e
    rw [← h, hc]
    push_cast
    ring
  · refine ⟨(c : ZMod n), Or.inr ?_⟩
    have h := ZMod.natCast_zmod_val e
    rw [← h, hc]
    push_cast
    ring

theorem dihedral_outer_conj_aux {m : ℕ} (hm : 2 ≤ m) (N₀ : Subgroup (DihedralGroup (2 ^ m)))
    (hN₀ : N₀.index = 2) (hnc : ¬ IsCyclic ↥N₀) {x y : DihedralGroup (2 ^ m)} (hx2 : x * x = 1)
    (hy2 : y * y = 1) (hx : x ∉ N₀) (hy : y ∉ N₀) : ∃ p ∈ N₀, p * y * p⁻¹ = x := by
  have hsq : ∀ g, g * g ∈ N₀ := fun g => Subgroup.mul_self_mem_of_index_two hN₀ g
  have hmul : ∀ a b, a * b ∈ N₀ ↔ (a ∈ N₀ ↔ b ∈ N₀) := fun a b =>
    Subgroup.mul_mem_iff_of_index_two hN₀
  have hrev : ∀ c : ZMod (2 ^ m), r (2 * c) ∈ N₀ := fun c => by
    have := hsq (r c)
    rw [r_mul_r] at this
    rwa [two_mul]
  have hodd : ∀ c : ZMod (2 ^ m), r (2 * c + 1) ∉ N₀ := by
    intro c hc
    apply hnc
    have h1 : r (1 : ZMod (2 ^ m)) ∈ N₀ := by
      have := mul_mem hc (inv_mem (hrev c))
      rw [inv_r, r_mul_r] at this
      simpa using this
    have hle : zpowers (r (1 : ZMod (2 ^ m))) ≤ N₀ := (zpowers_le).2 h1
    have hcardN : Nat.card ↥N₀ = 2 ^ m := by
      have h := Subgroup.card_mul_index N₀
      rw [hN₀, DihedralGroup.nat_card] at h
      omega
    have hcardZ : Nat.card ↥(zpowers (r (1 : ZMod (2 ^ m)))) = 2 ^ m := by
      rw [Nat.card_zpowers, orderOf_r_one]
    have heq : zpowers (r (1 : ZMod (2 ^ m))) = N₀ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardN, hcardZ])
    rw [← heq]
    infer_instance
  have hrefl : ∀ g : DihedralGroup (2 ^ m), g * g = 1 → g ∉ N₀ → ∃ j, g = sr j := by
    intro g hg2 hg
    cases g with
    | r i =>
      exfalso
      obtain ⟨c, hc | hc⟩ := zmod_exists_two_mul (2 ^ m) i
      · exact hg (by rw [hc]; exact hrev c)
      · rw [r_mul_r, ← r_zero] at hg2
        have h0 : i + i = 0 := by injection hg2
        have h4 : ((4 * ZMod.val c + 2 : ℕ) : ZMod (2 ^ m)) = 0 := by
          have hc' : c = ((ZMod.val c : ℕ) : ZMod (2 ^ m)) := (ZMod.natCast_zmod_val c).symm
          rw [hc, hc'] at h0
          push_cast
          linear_combination h0
        rw [ZMod.natCast_eq_zero_iff] at h4
        have h44 : 4 ∣ 2 ^ m := by
          have : 2 ^ 2 ∣ 2 ^ m := pow_dvd_pow 2 hm
          simpa using this
        have := h44.trans h4
        omega
    | sr j => exact ⟨j, rfl⟩
  obtain ⟨j, rfl⟩ := hrefl x hx2 hx
  obtain ⟨k, rfl⟩ := hrefl y hy2 hy
  have hd : r (k - j) ∈ N₀ := by
    have := (hmul (sr j) (sr k)).2 (iff_of_false hx hy)
    rwa [sr_mul_sr] at this
  obtain ⟨a, ha | ha⟩ := zmod_exists_two_mul (2 ^ m) (k - j)
  swap
  · exact absurd (by rw [ha] at hd; exact hd) (hodd a)
  by_cases hra : r a ∈ N₀
  · refine ⟨r a, hra, ?_⟩
    rw [inv_r, r_mul_sr, sr_mul_r]
    congr 1
    linear_combination ha
  · have hra' : r (-a) ∉ N₀ := fun h => hra (by simpa [inv_r] using inv_mem h)
    have hp : sr k * r (-a) ∈ N₀ := (hmul _ _).2 (iff_of_false hy hra')
    refine ⟨sr k * r (-a), hp, ?_⟩
    rw [sr_mul_r, inv_sr, sr_mul_sr, r_mul_sr]
    congr 1
    linear_combination ha

theorem dihedral_outer_conj {m : ℕ} (hm : 2 ≤ m) {T : Type} [Group T] (e : T ≃* DihedralGroup (2 ^ m))
    (N₀ : Subgroup T) (hN₀ : N₀.index = 2) (hnc : ¬ IsCyclic ↥N₀) {x y : T} (hx2 : x * x = 1)
    (hy2 : y * y = 1) (hx : x ∉ N₀) (hy : y ∉ N₀) : ∃ p ∈ N₀, p * y * p⁻¹ = x := by
  have hmem : ∀ g : T, e g ∈ N₀.map e.toMonoidHom ↔ g ∈ N₀ := fun g => by
    constructor
    · rintro ⟨h, hh, hg⟩
      have : h = g := e.injective hg
      rwa [← this]
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hidx : (N₀.map e.toMonoidHom).index = 2 := by
    rw [Subgroup.index_map_of_bijective e.bijective, hN₀]
  have hcyc : ¬ IsCyclic ↥(N₀.map e.toMonoidHom) := fun h => hnc (by
    have e' : ↥N₀ ≃* ↥(N₀.map e.toMonoidHom) := N₀.equivMapOfInjective e.toMonoidHom e.injective
    exact e'.isCyclic.mpr h)
  obtain ⟨p, hp, hpy⟩ := dihedral_outer_conj_aux hm (N₀.map e.toMonoidHom) hidx hcyc (x := e x)
    (y := e y) (by rw [← map_mul, hx2, map_one]) (by rw [← map_mul, hy2, map_one])
    (fun h => hx ((hmem x).1 h)) (fun h => hy ((hmem y).1 h))
  refine ⟨e.symm p, ?_, ?_⟩
  · have : e (e.symm p) ∈ N₀.map e.toMonoidHom := by simpa using hp
    exact (hmem _).1 this
  · apply e.injective
    simpa using hpy

end CFSG.GH74.GLS.IVK.Lifted
