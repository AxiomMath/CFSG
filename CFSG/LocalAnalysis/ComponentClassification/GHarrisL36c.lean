module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL36b
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL33b

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem SCert.SE.comm_a_l : SE.gen 8 * SE.gen 1 * (SE.gen 8)⁻¹ * (SE.gen 1)⁻¹ = SE.gen 0 := by
  decide

theorem SCert.SE.card_centralizer_l :
    (Finset.univ.filter fun c : SE => c * SE.gen 1 = SE.gen 1 * c).card = 256 := by
  decide +kernel

namespace GHSylow

variable (D : GHSylow G)

@[expose] def M1 : Subgroup G where
  carrier := {g | g ∈ D.M ∧ g * D.l * g⁻¹ * D.l⁻¹ ∈ D.OM}
  mul_mem' {g h} hg hh := ⟨mul_mem hg.1 hh.1, by
    rw [show g * h * D.l * (g * h)⁻¹ * D.l⁻¹ =
      g * (h * D.l * h⁻¹ * D.l⁻¹) * g⁻¹ * (g * D.l * g⁻¹ * D.l⁻¹) by group]
    exact mul_mem (D.conj_mem_OM hg.1 hh.2) hg.2⟩
  one_mem' := ⟨one_mem _, by rw [inv_one, mul_one, one_mul, mul_inv_cancel]; exact one_mem _⟩
  inv_mem' {g} hg := ⟨inv_mem hg.1, by
    rw [show g⁻¹ * D.l * g⁻¹⁻¹ * D.l⁻¹ = g⁻¹ * (g * D.l * g⁻¹ * D.l⁻¹)⁻¹ * g by group]
    exact D.conj_mem_OM' hg.1 (inv_mem hg.2)⟩

omit [Finite G] in
theorem mem_M1 {g : G} : g ∈ D.M1 ↔ g ∈ D.M ∧ g * D.l * g⁻¹ * D.l⁻¹ ∈ D.OM := Iff.rfl

omit [Finite G] in
theorem M1_le_M : D.M1 ≤ D.M := fun _ h => h.1

theorem z_not_mem_OM : D.z ∉ D.OM := fun h =>
  D.z_ne_one (D.eq_one_of_mem_OM h (a := 1) (by rw [pow_one, pow_two]; exact D.z_mul_z))

omit [Finite G] in
theorem comm_a_l : D.a * D.l * D.a⁻¹ * D.l⁻¹ = D.z := by
  change D.toG (SE.invRep 7) * D.toG (SE.gen 1) * (D.toG (SE.invRep 7))⁻¹ *
    (D.toG (SE.gen 1))⁻¹ = D.toG (SE.gen 0)
  rw [SE.invRep_seven, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, SE.comm_a_l]

omit [Finite G] in
theorem a_mem_M : D.a ∈ D.M := D.S_le_M (D.toG_mem _)

theorem a_not_mem_M1 : D.a ∉ D.M1 := fun h => D.z_not_mem_OM (D.comm_a_l ▸ h.2)

omit [Finite G] in
theorem comm_mul_a {g : G} (hg : g ∈ D.M) :
    g * D.a * D.l * (g * D.a)⁻¹ * D.l⁻¹ = D.z * (g * D.l * g⁻¹ * D.l⁻¹) := by
  have hgz := D.z_comm_of_mem_M (inv_mem hg)
  rw [inv_inv] at hgz
  calc g * D.a * D.l * (g * D.a)⁻¹ * D.l⁻¹ =
      g * (D.a * D.l * D.a⁻¹ * D.l⁻¹) * g⁻¹ * (g * D.l * g⁻¹ * D.l⁻¹) := by group
    _ = g * D.z * g⁻¹ * (g * D.l * g⁻¹ * D.l⁻¹) := by rw [D.comm_a_l]
    _ = D.z * (g * D.l * g⁻¹ * D.l⁻¹) := by rw [hgz]

theorem M1_index : (D.M1.subgroupOf D.M).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨D.a, D.a_mem_M⟩, fun b => ?_⟩
  rw [mem_subgroupOf, mem_subgroupOf]
  have hb := b.2
  change Xor (b * D.a ∈ D.M1) ((b : G) ∈ D.M1)
  rw [D.mem_M1, D.mem_M1, D.comm_mul_a hb]
  have hbaM : (b : G) * D.a ∈ D.M := mul_mem hb D.a_mem_M
  rcases D.comm_l_mem_OM hb with h | h
  · refine Or.inr ⟨⟨hb, h⟩, fun ⟨_, h'⟩ => D.z_not_mem_OM ?_⟩
    have := mul_mem h' (inv_mem h)
    rwa [mul_inv_cancel_right] at this
  · refine Or.inl ⟨⟨hbaM, h⟩, fun ⟨_, h'⟩ => D.z_not_mem_OM ?_⟩
    have := mul_mem h (inv_mem h')
    rwa [mul_inv_cancel_right] at this

theorem mem_M1_iff_of_mem_S {s : G} (hs : s ∈ (D.S : Subgroup G)) :
    s ∈ D.M1 ↔ s * D.l = D.l * s := by
  constructor
  · intro h
    have hS : s * D.l * s⁻¹ * D.l⁻¹ ∈ (D.S : Subgroup G) :=
      mul_mem (mul_mem (mul_mem hs (D.toG_mem _)) (inv_mem hs)) (inv_mem (D.toG_mem _))
    have h1 : s * D.l * s⁻¹ * D.l⁻¹ = 1 := by
      have := D.eq_one_of_mem_OM h.2 (a := 9)
      apply this
      obtain ⟨c, hc⟩ := D.exists_toG hS
      rw [← hc, ← map_pow, show c ^ (2 ^ 9) = 1 by
        rw [← orderOf_dvd_iff_pow_eq_one]
        rw [show (2 : ℕ) ^ 9 = Nat.card SE by rw [SE.card_SE]; norm_num]
        exact orderOf_dvd_natCard c, map_one]
    calc s * D.l = s * D.l * s⁻¹ * D.l⁻¹ * (D.l * s) := by group
      _ = D.l * s := by rw [h1, one_mul]
  · intro h
    refine ⟨D.S_le_M hs, ?_⟩
    rw [h, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _

abbrev S1 : Subgroup G := (D.S : Subgroup G) ⊓ centralizer ({D.l} : Set G)

theorem S1_le_M1 : D.S1 ≤ D.M1 := fun _ hs => (D.mem_M1_iff_of_mem_S (mem_inf.mp hs).1).mpr
  (mem_centralizer_singleton_iff.mp (mem_inf.mp hs).2)

omit [Finite G] in
theorem card_S1 : Nat.card D.S1 = 256 := by
  classical
  rw [D.card_inf_centralizer_toG, ← SE.card_centralizer_l, Nat.card_eq_fintype_card,
    ← Fintype.card_coe]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [mem_centralizer_singleton_iff, Finset.mem_filter]
  exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩

theorem isSylowOf_S1_M1 : IsSylowOf 2 D.S1 D.M1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSM : IsSylowOf 2 (D.S : Subgroup G) D.M := (isSylowOf_top D.S).of_le D.S_le_M le_top
  rw [isSylowOf_iff] at hSM ⊢
  refine ⟨D.S1_le_M1, D.S.isPGroup'.to_le inf_le_left, fun hdvd => hSM.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex D.S1 D.M1 D.M D.S1_le_M1 D.M1_le_M
  have h2 := Subgroup.relIndex_mul_relIndex D.S1 (D.S : Subgroup G) D.M inf_le_left D.S_le_M
  have h3 : D.M1.relIndex D.M = 2 := D.M1_index
  have h4 : D.S1.relIndex (D.S : Subgroup G) = 2 := by
    have h5 := Subgroup.relIndex_mul_card D.S1 (D.S : Subgroup G)
    rw [inf_eq_left.mpr inf_le_left, D.card_S1, D.card_S_eq] at h5
    omega
  rw [h3] at h1
  rw [h4] at h2
  have h6 : D.S1.relIndex D.M1 = (D.S : Subgroup G).relIndex D.M := by omega
  rwa [← h6]

end GHSylow

end CFSG.ComponentClassification.GHarris
