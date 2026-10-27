module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralDihedral
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitElem
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitInputs

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup DihedralGroup
open CFSG.ComponentClassification.HSFLit (ElemAbelianTwo)

section Dihedral

variable {m : ℕ}

theorem eq_r_half_of_central (hm : Even m) (h3 : 3 ≤ m) {g : DihedralGroup m}
    (hg : ∀ h : DihedralGroup m, g * h = h * g) (hg1 : g ≠ 1) :
    g = r ((m / 2 : ℕ) : ZMod m) := by
  have hm0 : m ≠ 0 := by omega
  rcases (commute_sr_iff hm hm0 0 g).mp (hg (sr 0)) with h | h | h | h
  · exact absurd h hg1
  · exact h
  all_goals
    exfalso
    rw [h] at hg
    have h1 := hg (r 1)
    have : NeZero m := ⟨hm0⟩
    have h2 := (commute_r_sr_iff _ (1 : ZMod m)).mp h1.symm
    rw [mul_one] at h2
    have h3' : ((2 : ℕ) : ZMod m) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at h3'
    have := Nat.le_of_dvd (by norm_num) h3'
    omega

end Dihedral

section Tbar

variable {A : Type} [Group A] {T : Subgroup A} {m : ℕ} (e : ↥T ≃* DihedralGroup m)

include e in
theorem Tbar_card : Nat.card T = 2 * m := by
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem Tbar_eq_r_half (hm : Even m) (h3 : 3 ≤ m) {zb : A} (hzT : zb ∈ T)
    (hzc : ∀ g ∈ T, zb * g = g * zb) (hz1 : zb ≠ 1) :
    e ⟨zb, hzT⟩ = r ((m / 2 : ℕ) : ZMod m) := by
  refine eq_r_half_of_central hm h3 (fun h => ?_) (fun h => hz1 ?_)
  · obtain ⟨g, rfl⟩ := e.surjective h
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzc g g.2)
  · have : (⟨zb, hzT⟩ : ↥T) = 1 := by
      rw [← map_one e] at h
      exact e.injective h
    exact congrArg Subtype.val this

include e in
theorem Tbar_eq_of_comm_mod (hm : Even m) (h8 : 8 ≤ m) {zb : A} (hzT : zb ∈ T)
    (hzc : ∀ g ∈ T, zb * g = g * zb) (hz1 : zb ≠ 1) {g : A} (hgT : g ∈ T) (hg2 : g ^ 2 = 1)
    (hc : ∀ h ∈ T, g * h * g⁻¹ * h⁻¹ = 1 ∨ g * h * g⁻¹ * h⁻¹ = zb) : g = 1 ∨ g = zb := by
  have hz := Tbar_eq_r_half e hm (by omega) hzT hzc hz1
  have hg2' : e ⟨g, hgT⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨g, hgT⟩ : ↥T) ^ 2 = 1 := Subtype.ext (by simpa using hg2)
    rw [this, map_one]
  have hcy : ∀ y : DihedralGroup m, e ⟨g, hgT⟩ * y * (e ⟨g, hgT⟩)⁻¹ * y⁻¹ = 1 ∨
      e ⟨g, hgT⟩ * y * (e ⟨g, hgT⟩)⁻¹ * y⁻¹ = r ((m / 2 : ℕ) : ZMod m) := by
    intro y
    obtain ⟨h, rfl⟩ := e.surjective y
    have hcomm : (⟨g, hgT⟩ : ↥T) * h * (⟨g, hgT⟩ : ↥T)⁻¹ * h⁻¹ = 1 ∨
        (⟨g, hgT⟩ : ↥T) * h * (⟨g, hgT⟩ : ↥T)⁻¹ * h⁻¹ = ⟨zb, hzT⟩ := by
      rcases hc h h.2 with h' | h'
      · exact Or.inl (Subtype.ext h')
      · exact Or.inr (Subtype.ext h')
    rcases hcomm with h' | h'
    · left
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, h', map_one]
    · right
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, h', hz]
  rcases eq_of_comm_mod_center hm h8 _ hg2' hcy with h | h
  · left
    rw [← map_one e] at h
    exact congrArg Subtype.val (e.injective h)
  · right
    rw [← hz] at h
    exact congrArg Subtype.val (e.injective h)

include e in
theorem Tbar_card_le_four (hm : Even m) (hm0 : m ≠ 0) {E : Subgroup A} (hET : E ≤ T)
    (hsq : ∀ x ∈ E, x ^ 2 = 1) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : Nat.card E ≤ 4 := by
  set E' := (E.subgroupOf T).map e.toMonoidHom
  have hcard : Nat.card E' = Nat.card E := by
    rw [card_map_of_injective e.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hET).toEquiv
  rw [← hcard]
  refine card_le_four_of_sq hm hm0 E' ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (by simpa using hsq _ hx)
    rw [this, map_one]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm _ hx _ hy)

end Tbar

section General

variable {G : Type} [Group G] [Finite G]

theorem exists_central_inv_of_normal {S N : Subgroup G} (hS : IsPGroup 2 S) (hNS : N ≤ S)
    (hN : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) (hne : ∃ n ∈ N, n ≠ 1) :
    ∃ u ∈ N, u ≠ 1 ∧ u ^ 2 = 1 ∧ ∀ s ∈ S, s * u = u * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥S := hS.isNilpotent
  set N' := N.subgroupOf S
  have hN'n : N'.Normal := ⟨fun x hx s => by
    rw [mem_subgroupOf] at hx ⊢
    exact hN s s.2 x hx⟩
  have hN'ne : N' ≠ ⊥ := by
    obtain ⟨n, hn, hn1⟩ := hne
    intro h
    have : (⟨n, hNS hn⟩ : ↥S) ∈ N' := mem_subgroupOf.mpr hn
    rw [h, mem_bot] at this
    exact hn1 (congrArg Subtype.val this)
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'ne
  have h2 : IsPGroup 2 ↥(N' ⊓ center ↥S) := hS.to_subgroup _
  have hnt : Nontrivial ↥(N' ⊓ center ↥S) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card (α := ↥(N' ⊓ center ↥S))).ne' hn
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hn]; exact dvd_pow_self 2 hn0)
  obtain ⟨huN, huZ⟩ := mem_inf.mp u.2
  refine ⟨((u : ↥S) : G), mem_subgroupOf.mp huN, ?_, ?_, ?_⟩
  · intro h1
    have : u = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hu
    norm_num at hu
  · have := pow_orderOf_eq_one u
    rw [hu] at this
    exact congrArg (fun v : ↥(N' ⊓ center ↥S) => ((v : ↥S) : G)) this
  · intro s hs
    exact (congrArg Subtype.val ((mem_center_iff.mp huZ) ⟨s, hs⟩))

end General

end CFSG.ComponentClassification.HSDihedral
