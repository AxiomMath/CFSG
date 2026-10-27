module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.A7Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.FixFourDef

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.ABGLocalTools

variable {X : Type} [Group X]

theorem exists_conj_mem_isSylowOf_of_pow_eq_one [Finite X] {K T : Subgroup X} (hT : IsSylowOf 2 T K)
    {y : X} (hy : y ∈ K) {n : ℕ} (hyn : y ^ 2 ^ n = 1) : ∃ c ∈ K, c * y * c⁻¹ ∈ T := by
  obtain ⟨S, rfl⟩ := hT
  have hZ : IsPGroup 2 (Subgroup.zpowers (⟨y, hy⟩ : K)) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hyn)
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hk]
  obtain ⟨S', hS'⟩ := hZ.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq K S' S
  have hmem : m * ⟨y, hy⟩ * m⁻¹ ∈ (S : Subgroup K) := by
    rw [← hm, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS' (Subgroup.mem_zpowers _))
  exact ⟨m, m.2, ⟨_, hmem, rfl⟩⟩

theorem card_le_four_of_forall_mem {H : Subgroup X} (l : List X) (hl : l.length ≤ 3)
    (h : ∀ x ∈ H, x = 1 ∨ x ∈ l) : Nat.card H ≤ 4 := by
  classical
  have hsub : (H : Set X) ⊆ ↑(insert (1 : X) l.toFinset) := fun x hx => by
    simpa using h x hx
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at h1
  have h2 := (Finset.card_insert_le (1 : X) l.toFinset).trans
    (Nat.succ_le_succ (List.toFinset_card_le l))
  exact (h1.trans h2).trans (Nat.succ_le_succ hl)

theorem FixFour.of_isSylowOf [Finite X] {L F T : Subgroup X} (hF : IsPGroup 2 F)
    (hT : IsSylowOf 2 T (normalizer (F : Set X) ⊓ L))
    (h : ∀ d ∈ T, d ∉ F → d * d ∈ F → Nat.card ↥(F ⊓ centralizer ({d} : Set X)) ≤ 4) :
    FixFour L F := by
  intro d hd hdF hd2
  obtain ⟨k, hk⟩ := hF ⟨d * d, hd2⟩
  have hdk : d ^ 2 ^ (k + 1) = 1 := by
    have := congrArg Subtype.val hk
    rw [pow_succ', pow_mul, sq]
    simpa using this
  obtain ⟨c, hc, hcd⟩ := exists_conj_mem_isSylowOf_of_pow_eq_one hT hd hdk
  have hc' := Subgroup.mem_normalizer_iff.1 (Subgroup.mem_inf.1 hc).1
  have h1 : c * d * c⁻¹ ∉ F := fun hh => hdF ((hc' d).2 hh)
  have h2 : c * d * c⁻¹ * (c * d * c⁻¹) ∈ F := by
    rw [show c * d * c⁻¹ * (c * d * c⁻¹) = c * (d * d) * c⁻¹ by group]
    exact (hc' _).1 hd2
  have hmap : ∀ x ∈ F ⊓ centralizer ({d} : Set X),
      c * x * c⁻¹ ∈ F ⊓ centralizer ({c * d * c⁻¹} : Set X) := by
    intro x hx
    obtain ⟨hxF, hxC⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨(hc' x).1 hxF, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxC ⊢
    calc c * x * c⁻¹ * (c * d * c⁻¹) = c * (x * d) * c⁻¹ := by group
      _ = c * (d * x) * c⁻¹ := by rw [hxC]
      _ = c * d * c⁻¹ * (c * x * c⁻¹) := by group
  refine le_trans (Nat.card_le_card_of_injective
    (fun x : ↥(F ⊓ centralizer ({d} : Set X)) => (⟨c * x * c⁻¹, hmap x x.2⟩ :
      ↥(F ⊓ centralizer ({c * d * c⁻¹} : Set X)))) ?_) (h _ hcd h1 h2)
  intro x y hxy
  have h3 : c * (x : X) * c⁻¹ = c * (y : X) * c⁻¹ := congrArg Subtype.val hxy
  exact Subtype.ext (mul_left_cancel (mul_right_cancel h3))

theorem FixFour.map {G : Type} [Group G] {φ : X →* G} (hφ : Function.Injective φ)
    {F : Subgroup X} (h : FixFour (⊤ : Subgroup X) F) : FixFour φ.range (F.map φ) := by
  intro d' hd' hdF hd2
  rw [normalizer_map_inf_range hφ F] at hd'
  obtain ⟨d, hdN, rfl⟩ := hd'
  have hdF' : d ∉ F := fun hh => hdF (Subgroup.mem_map_of_mem φ hh)
  have hd2' : d * d ∈ F := by
    rw [← map_mul] at hd2
    exact (Subgroup.mem_map_iff_mem hφ).1 hd2
  have key := h d (Subgroup.mem_inf.2 ⟨hdN, Subgroup.mem_top _⟩) hdF' hd2'
  have hmapeq : (F ⊓ centralizer ({d} : Set X)).map φ =
      F.map φ ⊓ centralizer ({φ d} : Set G) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hxF, hxC⟩ := Subgroup.mem_inf.1 hx
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem φ hxF, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hxC ⊢
      rw [← map_mul, ← map_mul, hxC]
    · intro hy
      obtain ⟨hyF, hyC⟩ := Subgroup.mem_inf.1 hy
      obtain ⟨x, hxF, rfl⟩ := hyF
      refine ⟨x, Subgroup.mem_inf.2 ⟨hxF, ?_⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
      exact hφ (by rw [map_mul, map_mul]; exact hyC)
  rw [← hmapeq, Subgroup.card_map_of_injective hφ]
  exact key

end CFSG.EvenSporadicStandard.M23Std
