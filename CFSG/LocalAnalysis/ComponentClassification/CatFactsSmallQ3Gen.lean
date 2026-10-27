module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Q3
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallModel

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup
open CFSG.ComponentClassification.GSThmB

theorem commutator_eq_of_index_two {G : Type*} [Group G] {C L : Subgroup G} [Finite C]
    (hLC : L ≤ C) (hidx : Nat.card C = 2 * Nat.card L) (hgen : L ≤ ⁅C, C⁆) : ⁅C, C⁆ = L := by
  refine le_antisymm ?_ hgen
  have : Finite L := Finite.of_injective (inclusion hLC) (inclusion_injective hLC)
  have hcardL : Nat.card (L.subgroupOf C) = Nat.card L :=
    Nat.card_congr (subgroupOfEquivOfLe hLC).toEquiv
  have hi : (L.subgroupOf C).index = 2 := by
    have h := index_mul_card (L.subgroupOf C)
    rw [hcardL, hidx] at h
    have hpos : 0 < Nat.card L := Nat.card_pos
    nlinarith
  have : (L.subgroupOf C).Normal := normal_of_index_eq_two hi
  have hQ : Nat.card (C ⧸ L.subgroupOf C) = 2 := by rw [← index_eq_card, hi]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (C ⧸ L.subgroupOf C) := isCyclic_of_prime_card hQ
  have hle : commutator C ≤ L.subgroupOf C :=
    Normal.quotient_commutative_iff_commutator_le.1 inferInstance
  rw [← map_subtype_commutator]
  have h2 := map_mono (f := C.subtype) hle
  rwa [subgroupOf_map_subtype, inf_eq_left.2 hLC] at h2

variable {n : ℕ}

@[expose, noinline] def oddNormalCheck (LL : List (Equiv.Perm (Fin n))) (m : ℕ) : Bool :=
  LL.all fun x => decide (x = 1) || !(decide (x ^ m = 1)) ||
    LL.any fun c => !(decide ((x * c * x⁻¹ * c⁻¹) ^ m = 1))

theorem oddNormal_of_check (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) {m : ℕ}
    (hm : ∀ d : ℕ, d ∣ Nat.card Q.originalSubgroup → Odd d → d ∣ m)
    (h : oddNormalCheck (elemsT Q) m = true) (N : Subgroup (Equiv.Perm (Fin n)))
    (hNQ : N ≤ Q.originalSubgroup)
    (hnorm : ∀ x ∈ Q.originalSubgroup, ∀ y ∈ N, x * y * x⁻¹ ∈ N) (hodd : Odd (Nat.card N)) :
    N = ⊥ := by
  have hpow : ∀ y ∈ N, y ^ m = 1 := by
    intro y hy
    have h1 : orderOf y ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hy
    have h2 : Nat.card N ∣ Nat.card Q.originalSubgroup := card_dvd_of_le hNQ
    exact orderOf_dvd_iff_pow_eq_one.1 (h1.trans (hm _ h2 hodd))
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  by_contra hy1
  have h1 := List.all_eq_true.1 h y ((mem_elemsT Q hQ y).2 (hNQ hy))
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    List.any_eq_true] at h1
  rcases h1 with (h1 | h1) | ⟨c, hc, hc'⟩
  · exact hy1 h1
  · exact h1 (hpow y hy)
  · apply hc'
    apply hpow
    have hcQ : c ∈ Q.originalSubgroup := (mem_elemsT Q hQ c).1 hc
    have : c * y⁻¹ * c⁻¹ ∈ N := hnorm c hcQ _ (inv_mem hy)
    rw [show y * c * y⁻¹ * c⁻¹ = y * (c * y⁻¹ * c⁻¹) by group]
    exact mul_mem hy this

@[expose, noinline] def admCheck (LA : List (Equiv.Perm (Fin n))) (QP : RawSchreierDatum n)
    (L5 : List (Equiv.Perm (Fin n))) (s₀ : Equiv.Perm (Fin n))
    (cs : List (Equiv.Perm (Fin n))) : Bool :=
  LA.all fun s => !(decide (s * s = 1)) || QP.sift s 0 ||
    (cs.any fun k => decide (k * s₀ * k⁻¹ = s)) ||
    L5.all fun x => !(decide (x * s = s * x))

theorem exists_conj_of_admCheck {LA : List (Equiv.Perm (Fin n))} {QP : RawSchreierDatum n}
    (hQP : ValidSchreier QP) {L5 : List (Equiv.Perm (Fin n))} {s₀ : Equiv.Perm (Fin n)}
    {cs : List (Equiv.Perm (Fin n))} (h : admCheck LA QP L5 s₀ cs = true)
    {s : Equiv.Perm (Fin n)} (hs : s ∈ LA) (hs2 : s * s = 1) (hsP : s ∉ QP.originalSubgroup)
    {x : Equiv.Perm (Fin n)} (hx : x ∈ L5) (hxs : x * s = s * x) :
    ∃ k ∈ cs, k * s₀ * k⁻¹ = s := by
  have h1 := List.all_eq_true.1 h s hs
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    List.any_eq_true, List.all_eq_true] at h1
  rcases h1 with ((h1 | h1) | h1) | h1
  · exact absurd hs2 h1
  · exact absurd ((mem_iff_sift QP hQP s).2 h1) hsP
  · exact h1
  · exact absurd hxs (h1 x hx)

variable {K : Type} {G : Type*} [Group K] [Group G] (M : AutModel K G)

theorem map_centralizer_singleton (θ : MulAut K) :
    (centralizer ({θ} : Set (MulAut K))).map M.ι =
      M.A ⊓ centralizer ({(M.Φ θ : G)} : Set G) := by
  ext y
  rw [mem_map, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨η, hη, rfl⟩
    rw [mem_centralizer_singleton_iff] at hη
    refine ⟨M.ι_mem η, ?_⟩
    have h := congrArg M.ι hη
    rwa [map_mul, map_mul] at h
  · rintro ⟨hy, hc⟩
    refine ⟨M.Φ.symm ⟨y, hy⟩, mem_centralizer_singleton_iff.2 (M.ι_injective ?_), ?_⟩
    · rw [map_mul, map_mul]
      show (M.Φ (M.Φ.symm ⟨y, hy⟩) : G) * M.ι θ = M.ι θ * (M.Φ (M.Φ.symm ⟨y, hy⟩) : G)
      rw [MulEquiv.apply_symm_apply]
      exact hc
    · show (M.Φ (M.Φ.symm ⟨y, hy⟩) : G) = y
      rw [MulEquiv.apply_symm_apply]

variable (hPA : M.P ≤ M.A) (hcent : ∀ g ∈ M.A, (∀ x ∈ M.P, g * x = x * g) → g = 1)
include hPA hcent

theorem map_innFix (θ : MulAut K) :
    (Cat8.innFix K θ).map M.ι = M.P ⊓ centralizer ({(M.Φ θ : G)} : Set G) := by
  rw [Cat8.innFix, map_inf_eq _ _ _ M.ι_injective, map_centralizer_singleton]
  have hinn : (Cat8.Inn K).map M.ι = M.P := by
    ext y
    constructor
    · rintro ⟨η, hη, rfl⟩
      exact (mem_range_conj_iff M hPA hcent η).1 hη
    · intro hy
      refine ⟨M.Φ.symm ⟨y, hPA hy⟩, (mem_range_conj_iff M hPA hcent _).2 ?_, ?_⟩
      · show (M.Φ (M.Φ.symm ⟨y, hPA hy⟩) : G) ∈ M.P
        rw [MulEquiv.apply_symm_apply]
        exact hy
      · show (M.Φ (M.Φ.symm ⟨y, hPA hy⟩) : G) = y
        rw [MulEquiv.apply_symm_apply]
  rw [hinn, ← inf_assoc, inf_eq_left.2 hPA]

theorem l0_of_model (θ : MulAut K) (L : Subgroup G)
    (hL : ⁅M.P ⊓ centralizer ({(M.Φ θ : G)} : Set G),
      M.P ⊓ centralizer ({(M.Φ θ : G)} : Set G)⁆ = L) (hcard : Nat.card L = 360)
    (hodd : ∀ N : Subgroup G, N ≤ L → (∀ x ∈ L, ∀ y ∈ N, x * y * x⁻¹ ∈ N) →
      Odd (Nat.card N) → N = ⊥) :
    Nat.card (Cat8.L0 K θ) = 360 ∧
      ∀ N : Subgroup (MulAut K), N ≤ Cat8.L0 K θ → (N.subgroupOf (Cat8.L0 K θ)).Normal →
        Odd (Nat.card N) → N = ⊥ := by
  have hmap : (Cat8.L0 K θ).map M.ι = L := by
    rw [Cat8.L0, map_commutator, map_innFix M hPA hcent, hL]
  refine ⟨by rw [← card_map_of_injective M.ι_injective, hmap, hcard], ?_⟩
  intro N hN hNn hNodd
  have hN' : N.map M.ι = ⊥ := by
    refine hodd _ (hmap ▸ map_mono hN) ?_ (by rwa [card_map_of_injective M.ι_injective])
    rintro _ hx _ ⟨y, hy, rfl⟩
    rw [← hmap] at hx
    obtain ⟨x, hxL, rfl⟩ := hx
    have := hNn.conj_mem ⟨y, hN hy⟩ (by simpa [mem_subgroupOf] using hy) ⟨x, hxL⟩
    rw [mem_subgroupOf] at this
    refine ⟨x * y * x⁻¹, by simpa using this, ?_⟩
    rw [map_mul, map_mul, map_inv]
  exact (map_eq_bot_iff_of_injective N M.ι_injective).1 hN'

end CFSG.ComponentClassification.CatFactsSmall
