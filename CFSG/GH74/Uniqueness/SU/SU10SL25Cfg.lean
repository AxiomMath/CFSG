module

public import CFSG.GH74.Uniqueness.SU.SU10SL25
public import CFSG.GH74.Uniqueness.SU.SU10Zbar

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU8 CFSG.Blueprint

section Generic

variable {X : Type} [Group X] [Finite X]

theorem eq_or_eq_of_pRank_one {C : Subgroup X} (hC : Open.pRank 2 C = 1) {w q : X} (hwC : w ∈ C)
    (hqC : q ∈ C) (hw2 : orderOf w = 2) (hqq : q * q = 1) (hcomm : q * w = w * q) :
    q = 1 ∨ q = w := by
  by_cases hq1 : q = 1
  · exact Or.inl hq1
  · right
    by_contra hqw
    have hq2 : orderOf q = 2 := orderOf_eq_prime (by rw [sq]; exact hqq) hq1
    have h2 := two_le_pRank_of_commuting_involutions hqC hwC hq2 hw2 hqw hcomm
    omega

theorem isSylowIn_inf_of_normal {N P K : Subgroup X} (hP : IsSylowIn N P) (hKN : K ≤ N)
    (hK : N ≤ normalizer (K : Set X)) : IsSylowIn K (P ⊓ K) := by
  have hcard := card_inf_of_sylowIn hP hKN hK
  have h1 : (P ⊓ K).relIndex K * Nat.card ((P ⊓ K) ⊓ K : Subgroup X) = Nat.card K :=
    Subgroup.relIndex_mul_card (P ⊓ K) K
  rw [inf_of_le_left (inf_le_right : P ⊓ K ≤ K), hcard] at h1
  refine ⟨inf_le_right, hP.2.1.to_inf_left, ?_⟩
  have hdiv : Nat.card K / 2 ^ (Nat.card K).factorization 2 = (P ⊓ K).relIndex K :=
    Nat.div_eq_of_eq_mul_left (pow_pos two_pos _) h1.symm
  rw [← hdiv]
  exact Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two Nat.card_pos.ne')

theorem qpair_of_sl25 (T : Sylow 2 X) {K₁ : Subgroup X} (hSL : K.IsSL25 ↥K₁) {w : X}
    (hw2 : orderOf w = 2) (hwc : ∀ x : X, x * w = w * x) (hwT : w ∈ (T : Subgroup X))
    (hC : Open.pRank 2 (centralizer (K₁ : Set X)) = 1)
    (hR : IsSylowIn K₁ ((T : Subgroup X) ⊓ K₁)) :
    QPair ((T : Subgroup X) ⊓ K₁) ((T : Subgroup X) ⊓ centralizer (K₁ : Set X)) w := by
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw2, sq] at this
  have hw1 : w ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hw2
    exact absurd hw2 (by norm_num)
  have hwC : w ∈ centralizer (K₁ : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h _
    exact hwc h
  have hwK : w ∈ K₁ := by
    obtain ⟨ζ, hζ2, hζc⟩ := exists_central_involution_of_isSL25 hSL
    have hζ2' : orderOf (ζ : X) = 2 := (Subgroup.orderOf_coe ζ).trans hζ2
    have hζC : (ζ : X) ∈ centralizer (K₁ : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hζc ⟨h, hh⟩)
    by_contra hwK
    have hne : (ζ : X) ≠ w := fun h => hwK (h ▸ ζ.2)
    have h2 := two_le_pRank_of_commuting_involutions hζC hwC hζ2' hw2 hne (hwc _)
    omega
  have hwR : w ∈ (T : Subgroup X) ⊓ K₁ := Subgroup.mem_inf.mpr ⟨hwT, hwK⟩
  obtain ⟨φ⟩ := sylow_isSL25_q8 hSL (sylowIn hR)
  let ψ : QuaternionGroup 2 ≃* ↥((T : Subgroup X) ⊓ K₁) :=
    φ.symm.trans ((MulEquiv.subgroupCongr (coe_sylowIn hR)).trans
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : (T : Subgroup X) ⊓ K₁ ≤ K₁)))
  let ι : QuaternionGroup 2 →* X := ((T : Subgroup X) ⊓ K₁).subtype.comp ψ.toMonoidHom
  have hιinj : Function.Injective ι :=
    ((T : Subgroup X) ⊓ K₁).subtype_injective.comp ψ.injective
  have hrange : ι.range = (T : Subgroup X) ⊓ K₁ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (ψ y).2
    · intro hx
      obtain ⟨y, hy⟩ := ψ.surjective ⟨x, hx⟩
      exact ⟨y, by simp [ι, hy]⟩
  have hq8 := IsQ8Like.of_injective ι hιinj
  rw [hrange] at hq8
  have hwz : w = ι (QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2))) :=
    (hq8.inv w hwR hww).resolve_left hw1
  rw [← hwz] at hq8
  refine ⟨hq8, Subgroup.mem_inf.mpr ⟨hwT, hwC⟩, ?_, ?_⟩
  · intro r hr q hq
    exact Subgroup.mem_centralizer_iff.mp hq.2 r hr.2
  · intro q hq hqq
    exact eq_or_eq_of_pRank_one hC hwC hq.2 hw2 hqq (hwc q)

end Generic

section Cases

variable {G : Type} [Group G] [Finite G]

theorem sl25_contradiction_normal {S : Sylow 2 G} {M : Subgroup G} {z : G} (h : Hyp21 S M z)
    {T : Sylow 2 (Hbar (centralizer ({z} : Set G)))}
    (hT : (T : Subgroup (Hbar (centralizer ({z} : Set G)))) =
      hbarImage (centralizer ({z} : Set G)) (S : Subgroup G))
    {K₁ : Subgroup (Hbar (centralizer ({z} : Set G)))} [K₁.Normal] (hSL : K.IsSL25 ↥K₁)
    (hC : Open.pRank 2 (centralizer (K₁ : Set (Hbar (centralizer ({z} : Set G))))) = 1)
    (hle : Subgroup.closure {g : Hbar (centralizer ({z} : Set G)) |
        g ∈ (T : Subgroup (Hbar (centralizer ({z} : Set G)))) ∧ g * g = 1} ≤
      K₁ ⊔ centralizer (K₁ : Set (Hbar (centralizer ({z} : Set G))))) : False := by
  have hwT : zbar z ∈ (T : Subgroup (Hbar (centralizer ({z} : Set G)))) := by
    rw [hT]
    exact zbar_mem_hbarImage h.z_mem
  have hpair := qpair_of_sl25 T hSL (zbar_orderOf h.z_invol) (zbar_central z) hwT hC
    (isSylowIn_inf_normal T K₁)
  refine fusion_contradiction h hT hpair inf_le_left inf_le_left ?_
  intro t ht htt
  have htle : t ∈ K₁ ⊔ centralizer (K₁ : Set (Hbar (centralizer ({z} : Set G)))) :=
    hle (Subgroup.subset_closure ⟨ht, htt⟩)
  have hKC : ∀ a ∈ K₁, ∀ b ∈ centralizer (K₁ : Set (Hbar (centralizer ({z} : Set G)))),
      a * b = b * a := fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha
  obtain ⟨r, hr, q, hq, hrq⟩ := mem_sup_of_isSylowIn_commute hKC
    (isSylowIn_inf_normal T (K₁ ⊔ centralizer (K₁ : Set (Hbar (centralizer ({z} : Set G))))))
    (t := t) ⟨ht, htle⟩
  exact ⟨r, ⟨hr.1.1, hr.2⟩, q, ⟨hq.1.1, hq.2⟩, hrq⟩

theorem sl25_contradiction_product {S : Sylow 2 G} {M : Subgroup G} {z : G} (h : Hyp21 S M z)
    {T : Sylow 2 (Hbar (centralizer ({z} : Set G)))}
    (hT : (T : Subgroup (Hbar (centralizer ({z} : Set G)))) =
      hbarImage (centralizer ({z} : Set G)) (S : Subgroup G))
    {K₁ K₂ : Subgroup (Hbar (centralizer ({z} : Set G)))} (hSL : K.IsSL25 ↥K₁)
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hN : generalizedFitting (Hbar (centralizer ({z} : Set G))) = K₁ ⊔ K₂)
    (hC : Open.pRank 2 (centralizer (K₁ : Set (Hbar (centralizer ({z} : Set G))))) = 1)
    (hle : Subgroup.closure {g : Hbar (centralizer ({z} : Set G)) |
        g ∈ (T : Subgroup (Hbar (centralizer ({z} : Set G)))) ∧ g * g = 1} ≤
      generalizedFitting (Hbar (centralizer ({z} : Set G)))) : False := by
  have hNn : (K₁ ⊔ K₂).Normal := by
    have := (CFSG.LocalCores.generalized_fitting_characteristic
      (G := Hbar (centralizer ({z} : Set G)))).2
    rwa [hN] at this
  have hP := isSylowIn_inf_normal T (K₁ ⊔ K₂)
  have hR : IsSylowIn K₁ ((T : Subgroup (Hbar (centralizer ({z} : Set G)))) ⊓ K₁) := by
    have := isSylowIn_inf_of_normal hP (le_sup_left : K₁ ≤ K₁ ⊔ K₂)
      (sup_le_normalizer_of_commute hcomm)
    rwa [inf_assoc, inf_of_le_right (le_sup_left : K₁ ≤ K₁ ⊔ K₂)] at this
  have hwT : zbar z ∈ (T : Subgroup (Hbar (centralizer ({z} : Set G)))) := by
    rw [hT]
    exact zbar_mem_hbarImage h.z_mem
  have hpair := qpair_of_sl25 T hSL (zbar_orderOf h.z_invol) (zbar_central z) hwT hC hR
  refine fusion_contradiction h hT hpair inf_le_left inf_le_left ?_
  intro t ht htt
  have htle : t ∈ K₁ ⊔ K₂ := hN ▸ hle (Subgroup.subset_closure ⟨ht, htt⟩)
  obtain ⟨r, hr, q, hq, hrq⟩ := mem_sup_of_isSylowIn_commute hcomm hP (t := t) ⟨ht, htle⟩
  refine ⟨r, ⟨hr.1.1, hr.2⟩, q, ⟨hq.1.1, ?_⟩, hrq⟩
  exact Subgroup.mem_centralizer_iff.mpr fun a ha => hcomm a ha q hq.2

end Cases

end CFSG.GH74.Uniqueness.SU.SU10
