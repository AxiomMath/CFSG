module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Gen
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Comp

public section

namespace CFSG.OddStandard.Seitz77.CaseB45

open Subgroup CFSG.Open

variable {G : Type} [Group G] {G₁ G₂ : Subgroup G} {t : G} {Q : Type} [Group Q]

structure EmbSpec (cd : CompData G₁ G₂ t) (M : ModelData Q) where
  θ : ↥(normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) →* Wr Q
  ker : ∀ n : ↥(normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)), θ n = 1 →
    (n : G) ∈ centralizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)
  e_iff : ∀ n : ↥(normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)),
    (θ n).e = false ↔ (n : G) ∈ normalizer (G₁ : Set G)
  swap : θ ⟨t, cd.t_mem_normalizer⟩ = Wr.swap
  inner : ∀ n : ↥(normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)), (n : G) ∈ G₁ ⊔ G₂ →
    θ n ∈ Wr.ss M.Lm

namespace EmbSpec

variable {cd : CompData G₁ G₂ t} {M : ModelData Q} (E : EmbSpec cd M)

theorem odd_inj [Finite G] (hodd : Odd (Nat.card (centralizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))))
    {T₀ : Subgroup G} (hT : IsPGroup 2 T₀)
    (hTN : T₀ ≤ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) :
    Function.Injective (restrT E.θ hTN) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have hyc : (y : G) ∈ centralizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) := E.ker ⟨y, hTN y.2⟩ hy
  obtain ⟨k, hk⟩ := hT y
  have h1 : orderOf (y : G) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : orderOf (y : G) ∣ Nat.card (centralizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) := by
    have := orderOf_dvd_natCard (⟨(y : G), hyc⟩ : centralizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (centralizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have h3 : orderOf (y : G) = 1 := Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h1) h2
  have : (y : G) = 1 := orderOf_eq_one_iff.1 h3
  exact Subtype.ext this

theorem imgT_le_ss {R S : Subgroup G} (hRN : R ≤ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))
    (hSG : S ≤ G₁ ⊔ G₂) : imgT (θ := E.θ) (hTN := hRN) S ≤ Wr.ss M.Lm := by
  rintro _ ⟨z, hz, rfl⟩
  exact E.inner ⟨z.1, hRN z.2⟩ (hSG (Subgroup.mem_subgroupOf.1 hz))

variable [Finite Q]

include E

theorem elem_le [Finite G]
    (hodd : Odd (Nat.card (centralizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))))
    {R : Subgroup G} (hR : IsPGroup 2 R)
    (hRN : R ≤ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) {S : Subgroup G} (hSR : S ≤ R)
    (hSG : S ≤ G₁ ⊔ G₂) (hcS : Nat.card S = 2 ^ 12) {Y : Subgroup G} (hYR : Y ≤ R)
    (hY : IsElemAbelian 2 Y) (hcY : Nat.card Y = 2 ^ 8) : Y ≤ S :=
  gen_elem_le M hR (E.odd_inj hodd hR hRN) hSR (E.imgT_le_ss hRN hSG) hcS hYR hY hcY

theorem not_equiv [Finite G]
    (hodd : Odd (Nat.card (centralizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))))
    {T₀ : Subgroup G} (hT : IsPGroup 2 T₀)
    (hTN : T₀ ≤ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) {S : Subgroup G} (hST : S ≤ T₀)
    (hSG : S ≤ G₁ ⊔ G₂) (hcS : Nat.card S = 2 ^ 12) {τ x : G} (hτT : τ ∈ T₀)
    (hτ : τ ∉ normalizer (G₁ : Set G)) (hτ2 : τ * τ = 1) (hxT : x ∈ T₀)
    (hx : x ∈ normalizer (G₁ : Set G)) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ¬ Nonempty (↥(T₀ ⊓ centralizer {x}) ≃* ↥(T₀ ⊓ centralizer {τ})) := by
  refine gen_not_equiv M hT (E.odd_inj hodd hT hTN) hST (E.imgT_le_ss hTN hSG) hcS hτT hxT ?_
    hτ2 ?_ hx2 hx1
  · have h := mt (E.e_iff ⟨τ, hTN hτT⟩).1 hτ
    show (E.θ ⟨τ, hTN hτT⟩).e = true
    simpa using h
  · exact (E.e_iff ⟨x, hTN hxT⟩).2 hx

omit [Finite Q] in
theorem relIndex_two {T₀ : Subgroup G} (hTN : T₀ ≤ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))
    (htT : t ∈ T₀) : (T₀ ⊓ normalizer (G₁ : Set G)).relIndex T₀ = 2 := by
  let φ : ↥T₀ →* Multiplicative (ZMod 2) := Wr.eHom.comp (restrT E.θ hTN)
  have hker : (T₀ ⊓ normalizer (G₁ : Set G)).subgroupOf T₀ = φ.ker := by
    ext y
    rw [mem_subgroupOf, mem_inf, MonoidHom.mem_ker]
    simp only [φ, MonoidHom.comp_apply, Wr.eHom_eq_one_iff, restrT_apply, E.e_iff]
    exact ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩
  have hne : φ ⟨t, htT⟩ ≠ 1 := by
    simp only [φ, MonoidHom.comp_apply, ne_eq, Wr.eHom_eq_one_iff, restrT_apply]
    rw [E.swap]
    simp [Wr.swap]
  have hrange : φ.range = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have key : ∀ w a : Multiplicative (ZMod 2), a ≠ 1 → w = 1 ∨ w = a := by decide
    rcases key z _ hne with h | h
    · rw [h]
      exact φ.range.one_mem
    · rw [h]
      exact ⟨_, rfl⟩
  rw [Subgroup.relIndex, hker, Subgroup.index_ker, hrange, Subgroup.card_top]
  simp

end EmbSpec

end CFSG.OddStandard.Seitz77.CaseB45
