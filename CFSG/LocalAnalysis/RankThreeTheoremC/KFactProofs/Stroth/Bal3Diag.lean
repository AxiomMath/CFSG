module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Sec
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Reduce

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open scoped Pointwise

section Diag

variable {X : Type*} [Group X]

theorem exists_diag_hom {d : X} (hd3 : d ^ 3 = 1) {K₁ K₂ K₃ : Subgroup X}
    (hc₁ : MulAut.conj d • K₁ = K₂) (hc₂ : MulAut.conj d • K₂ = K₃)
    (h₂₁ : K₂ ≤ centralizer (K₁ : Set X)) (h₃₁ : K₃ ≤ centralizer (K₁ : Set X))
    (h₃₂ : K₃ ≤ centralizer (K₂ : Set X)) (hZ₁ : center K₁ = ⊥) :
    ∃ ψ : ↥K₁ →* X, Function.Injective ψ ∧ ∀ k, ψ k ∈ centralizer ({d} : Set X) := by
  let f₁ : ↥K₁ →* X := K₁.subtype
  let f₂ : ↥K₁ →* X := (MulAut.conj d).toMonoidHom.comp f₁
  let f₃ : ↥K₁ →* X := (MulAut.conj d).toMonoidHom.comp f₂
  have hf₂ : ∀ k : ↥K₁, f₂ k ∈ K₂ := fun k => by
    rw [← hc₁]; exact Subgroup.mem_map_of_mem _ k.2
  have hf₃ : ∀ k : ↥K₁, f₃ k ∈ K₃ := fun k => by
    rw [← hc₂]; exact Subgroup.mem_map_of_mem _ (hf₂ k)
  have hc₂₃ : ∀ m n : ↥K₁, Commute (f₂ m) (f₃ n) := fun m n =>
    mem_centralizer_iff.1 (h₃₂ (hf₃ n)) (f₂ m) (hf₂ m)
  let diag : ↥K₁ →* ↥K₁ × ↥K₁ := (MonoidHom.id ↥K₁).prod (MonoidHom.id ↥K₁)
  let g : ↥K₁ →* X := (f₂.noncommCoprod f₃ hc₂₃).comp diag
  have hg : ∀ k : ↥K₁, g k = f₂ k * f₃ k := fun k => by
    simp [g, diag, MonoidHom.noncommCoprod_apply]
  have hc₁g : ∀ m n : ↥K₁, Commute (f₁ m) (g n) := fun m n => by
    rw [hg]
    exact Commute.mul_right
      (mem_centralizer_iff.1 (h₂₁ (hf₂ n)) (f₁ m) m.2)
      (mem_centralizer_iff.1 (h₃₁ (hf₃ n)) (f₁ m) m.2)
  let ψ : ↥K₁ →* X := (f₁.noncommCoprod g hc₁g).comp diag
  have hψ : ∀ k : ↥K₁, ψ k = (k : X) * (f₂ k * f₃ k) := fun k => by
    simp [ψ, diag, MonoidHom.noncommCoprod_apply, hg, f₁]
  refine ⟨ψ, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro k hk
    rw [hψ] at hk
    have hkc : (k : X) ∈ centralizer (K₁ : Set X) := by
      have hk' : (k : X) = (f₂ k * f₃ k)⁻¹ := eq_inv_of_mul_eq_one_left hk
      rw [hk']
      refine inv_mem (mul_mem (h₂₁ (hf₂ k)) (h₃₁ (hf₃ k)))
    have hkZ : k ∈ center K₁ := by
      rw [mem_center_iff]
      intro y
      apply Subtype.ext
      exact mem_centralizer_iff.1 hkc y y.2
    rw [hZ₁, mem_bot] at hkZ
    exact hkZ
  · intro k
    rw [mem_centralizer_singleton_iff, hψ]
    have hf₂e : f₂ k = d * (k : X) * d⁻¹ := rfl
    have hf₃e : f₃ k = d * (d * (k : X) * d⁻¹) * d⁻¹ := rfl
    have e3 : d * (d * (d * (k : X) * d⁻¹) * d⁻¹) * d⁻¹ = (k : X) := by
      have h3 : d * (d * (d * (k : X) * d⁻¹) * d⁻¹) * d⁻¹ =
          (d * d * d) * (k : X) * (d * d * d)⁻¹ := by group
      have hd3' : d * d * d = 1 := by rw [← pow_three', hd3]
      rw [h3, hd3']
      simp
    have hconj : d * ((k : X) * (f₂ k * f₃ k)) * d⁻¹ = f₂ k * f₃ k * (k : X) := by
      rw [hf₂e, hf₃e]
      calc d * ((k : X) * (d * (k : X) * d⁻¹ * (d * (d * (k : X) * d⁻¹) * d⁻¹))) * d⁻¹
          = (d * (k : X) * d⁻¹) * (d * (d * (k : X) * d⁻¹) * d⁻¹) *
              (d * (d * (d * (k : X) * d⁻¹) * d⁻¹) * d⁻¹) := by group
        _ = d * (k : X) * d⁻¹ * (d * (d * (k : X) * d⁻¹) * d⁻¹) * (k : X) := by rw [e3]
    have hcomm : (k : X) * (f₂ k * f₃ k) = (f₂ k * f₃ k) * (k : X) :=
      (Commute.mul_right (mem_centralizer_iff.1 (h₂₁ (hf₂ k)) (k : X) k.2)
        (mem_centralizer_iff.1 (h₃₁ (hf₃ k)) (k : X) k.2)).eq
    have hy : d * ((k : X) * (f₂ k * f₃ k)) * d⁻¹ = (k : X) * (f₂ k * f₃ k) := by
      rw [hconj, hcomm]
    exact (mul_inv_eq_iff_eq_mul.1 hy).symm

end Diag

section SectionLift

variable {H : Type*} [Group H] [Finite H] {p : ℕ}

theorem false_of_section_centralizer (hp : p.Prime) (O : Subgroup H) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {d₀ : H} (hd₀ : IsPGroup p (zpowers d₀))
    {S : Type*} [Group S] [IsSimpleGroup S] [Finite S]
    (hS : ∃ a b : S, a * b ≠ b * a) (hpS : p ∣ Nat.card S) (ψ : S →* H ⧸ O)
    (hψ : Function.Injective ψ)
    (hψC : ∀ s, ψ s ∈ centralizer ({QuotientGroup.mk' O d₀} : Set (H ⧸ O)))
    (hSec : NoSimpleSec p ↥(centralizer ({d₀} : Set H))) : False := by
  set π := QuotientGroup.mk' O with hπ
  set T : Subgroup (H ⧸ O) := ψ.range with hT
  let e : S ≃* T := MonoidHom.ofInjective hψ
  haveI : IsSimpleGroup T := MulEquiv.isSimpleGroup e.symm
  set C : Subgroup H := centralizer ({d₀} : Set H) with hC
  set G : Subgroup ↥C := (T.comap π).subgroupOf C with hG
  have hmem : ∀ x : ↥G, π ((x : ↥C) : H) ∈ T := fun x => Subgroup.mem_subgroupOf.1 x.2
  let φ : ↥G →* T := MonoidHom.codRestrict ((π.comp C.subtype).comp G.subtype) T hmem
  have hφ : Function.Surjective φ := by
    intro t
    obtain ⟨s, hs⟩ := t.2
    have htC : (t : H ⧸ O) ∈
        centralizer ((((zpowers d₀).map π : Subgroup (H ⧸ O))) : Set (H ⧸ O)) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      have hc : (t : H ⧸ O) * π d₀ = π d₀ * (t : H ⧸ O) := by
        have := hψC s
        rw [hs] at this
        exact mem_centralizer_singleton_iff.1 this
      rw [map_zpow]
      exact (Commute.zpow_left (show Commute (t : H ⧸ O) (π d₀) from hc).symm k).eq
    obtain ⟨x, hx, hxt⟩ := centralizer_map_le_map_centralizer hp O hO hd₀ htC
    have hxC : x ∈ C := centralizer_le (Set.singleton_subset_iff.2 (mem_zpowers d₀)) hx
    refine ⟨⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.2 (by
      rw [Subgroup.mem_comap, hxt]; exact t.2)⟩, ?_⟩
    exact Subtype.ext hxt
  have hnonab : ∃ a b : T, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hS
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
  have hpT : p ∣ Nat.card T := (Nat.card_congr e.toEquiv) ▸ hpS
  exact not_noSimpleSec_of_surjective G φ hφ hnonab hpT hSec

end SectionLift


end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
