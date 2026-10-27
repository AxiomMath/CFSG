module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ChainLemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.CanLoc
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Embed

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup

@[expose] def SylowNonabelian (G : Type) [Group G] : Prop :=
  ∀ S : Sylow 2 G, ∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x

theorem not_twoSubgroupsAbelian_of_sylow_le {Q : Type} [Group Q] [Finite Q] {M : Subgroup Q}
    (S : Sylow 2 Q) (hSM : (S : Subgroup Q) ≤ M) (hS : ∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x) :
    ¬ TwoSubgroupsAbelian ↥M := by
  intro h
  obtain ⟨x, hx, y, hy, hxy⟩ := hS
  have hP : IsPGroup 2 ↥((S : Subgroup Q).subgroupOf M) :=
    S.isPGroup'.of_injective (Subgroup.subgroupOfEquivOfLe hSM).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hSM).injective
  have := h _ hP ⟨x, hSM hx⟩ (mem_subgroupOf.2 hx) ⟨y, hSM hy⟩ (mem_subgroupOf.2 hy)
  exact hxy (congrArg Subtype.val this)

theorem sylowNonabelian_of_dihedral {G : Type} [Group G] [Finite G] {u v : G} (hu : u * u = 1)
    (hv : v * v = 1) (huv : (u * v) ^ 4 = 1) (hne : u * v ≠ v * u) : SylowNonabelian G := by
  intro S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hT : IsPGroup 2 ↥(zpowers (u * v)) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    have h4 : orderOf (u * v) ∣ 2 ^ 2 := by simpa using orderOf_dvd_of_pow_eq_one huv
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4
    exact ⟨j, hj⟩
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hconj : u * (u * v) * u⁻¹ = (u * v)⁻¹ := by
    rw [mul_inv_rev, hui, hvi]
    calc u * (u * v) * u = (u * u) * v * u := by group
      _ = v * u := by rw [hu, one_mul]
  have hfwd : ∀ z ∈ zpowers (u * v), u * z * u⁻¹ ∈ zpowers (u * v) := by
    rintro z ⟨k, rfl⟩
    refine ⟨-k, ?_⟩
    show (u * v) ^ (-k) = u * (u * v) ^ k * u⁻¹
    rw [← conj_zpow, hconj, inv_zpow, ← zpow_neg]
  have hN : u ∈ normalizer (zpowers (u * v) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨hfwd z, fun hz => ?_⟩
    have := hfwd _ hz
    have e : u * (u * z * u⁻¹) * u⁻¹ = z := by
      calc u * (u * z * u⁻¹) * u⁻¹ = (u * u) * z * (u⁻¹ * u⁻¹) := by group
        _ = z := by rw [hu, hui, hu, one_mul, mul_one]
    rwa [e] at this
  have hsq : u ^ 2 ∈ zpowers (u * v) := by rw [sq, hu]; exact one_mem _
  have hP : IsPGroup 2 ↥(zpowers (u * v) ⊔ zpowers u) := isPGroup_sup_zpowers hT hN hsq
  obtain ⟨S', hS'⟩ := hP.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S' S
  have hmem : ∀ y ∈ zpowers (u * v) ⊔ zpowers u,
      g * y * g⁻¹ ∈ ((g • S' : Sylow 2 G) : Subgroup G) := by
    intro y hy
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨y, hS' hy, rfl⟩
  have hu_mem : u ∈ zpowers (u * v) ⊔ zpowers u := mem_sup_right (mem_zpowers u)
  have hv_mem : v ∈ zpowers (u * v) ⊔ zpowers u := by
    have h1 : u * v ∈ zpowers (u * v) ⊔ zpowers u := mem_sup_left (mem_zpowers _)
    have := mul_mem (inv_mem hu_mem) h1
    simpa using this
  refine ⟨g * u * g⁻¹, hmem u hu_mem, g * v * g⁻¹, hmem v hv_mem, fun h => hne ?_⟩
  have h' : g * (u * v) * g⁻¹ = g * (v * u) * g⁻¹ := by
    calc g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
      _ = (g * v * g⁻¹) * (g * u * g⁻¹) := h
      _ = g * (v * u) * g⁻¹ := by group
  simpa using h'

theorem SylowNonabelian.of_mulEquiv {A B : Type} [Group A] [Group B] [Finite A] (e : A ≃* B)
    (h : SylowNonabelian B) : SylowNonabelian A := by
  intro S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : Function.Surjective e.toMonoidHom := e.surjective
  obtain ⟨x', hx', y', hy', hne⟩ := h (Sylow.mapSurjective hf S)
  have hx'' : x' ∈ (S : Subgroup A).map e.toMonoidHom := hx'
  have hy'' : y' ∈ (S : Subgroup A).map e.toMonoidHom := hy'
  obtain ⟨x, hx, rfl⟩ := hx''
  obtain ⟨y, hy, rfl⟩ := hy''
  exact ⟨x, hx, y, hy, fun h => hne (by simp only [MulEquiv.coe_toMonoidHom, ← map_mul, h])⟩

theorem not_sec_of_odd_canLoc {G : Type} [Group G] [Finite G] {K₁ N₀ : Subgroup G}
    (hodd : Odd (Nat.card ↥(center ↥K₁))) (hcan : CanLoc K₁ N₀)
    (hS : SylowNonabelian (↥K₁ ⧸ center ↥K₁)) :
    ¬ (Group.IsSolvable ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))) ∧
      (True → TwoSubgroupsAbelian ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))))) := by
  rintro ⟨-, hab⟩
  have hab := hab trivial
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hcan with ⟨hev, -⟩ | ⟨-, R, -, hRK, hRcard, rfl⟩
  · exact (Nat.not_even_iff_odd.2 hodd) hev
  · have hR'card : Nat.card ↥(R.subgroupOf K₁) = 2 ^ (Nat.card ↥K₁).factorization 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv]
      exact hRcard
    let SR : Sylow 2 ↥K₁ := Sylow.ofCard (R.subgroupOf K₁) hR'card
    have hπ : Function.Surjective (QuotientGroup.mk' (center ↥K₁)) :=
      QuotientGroup.mk'_surjective _
    let S₀ : Sylow 2 (↥K₁ ⧸ center ↥K₁) := Sylow.mapSurjective hπ SR
    have hle : (S₀ : Subgroup (↥K₁ ⧸ center ↥K₁)) ≤
        (((normalizer (R : Set G) ⊓ K₁).subgroupOf K₁)).map (QuotientGroup.mk' (center ↥K₁)) := by
      rw [Sylow.coe_mapSurjective, Sylow.coe_ofCard]
      refine Subgroup.map_mono fun x hx => ?_
      exact ⟨Subgroup.le_normalizer (Subgroup.mem_subgroupOf.1 hx), x.2⟩
    exact not_twoSubgroupsAbelian_of_sylow_le S₀ hle (hS S₀) hab

end CFSG.EvenSporadicStandard.Induction
