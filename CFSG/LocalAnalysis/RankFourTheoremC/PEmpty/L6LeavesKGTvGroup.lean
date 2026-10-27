module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGTvSec

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGTv

open Module CFSG.ComponentClassification.OutcomeLocal CFSG.HardMathSupport.Solomon.Coordinator

section Group

variable {X : Type} [Group X] {N : Subgroup X}

theorem eq_bot_or_le_of_normal [N.Normal] (hNs : IsSimpleGroup ↥N)
    (hC : ∀ x : X, (∀ n ∈ N, x * n = n * x) → x = 1) {K : Subgroup X} [K.Normal] :
    K = ⊥ ∨ N ≤ K := by
  rcases hNs.eq_bot_or_eq_top_of_normal (K.subgroupOf N) with h | h
  · left
    rw [eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    apply hC
    intro n hn
    have hcN : k * n * k⁻¹ * n⁻¹ ∈ N :=
      N.mul_mem (Subgroup.Normal.conj_mem inferInstance n hn k) (N.inv_mem hn)
    have hcK : k * n * k⁻¹ * n⁻¹ ∈ K := by
      have h1 : n * k⁻¹ * n⁻¹ ∈ K := Subgroup.Normal.conj_mem inferInstance k⁻¹ (K.inv_mem hk) n
      have h2 := K.mul_mem hk h1
      rwa [← mul_assoc, ← mul_assoc] at h2
    have hmem : (⟨k * n * k⁻¹ * n⁻¹, hcN⟩ : ↥N) ∈ K.subgroupOf N := hcK
    rw [h, Subgroup.mem_bot] at hmem
    have h3 : k * n * k⁻¹ * n⁻¹ = 1 := congrArg Subtype.val hmem
    calc k * n = (k * n * k⁻¹ * n⁻¹) * (n * k) := by group
      _ = n * k := by rw [h3, one_mul]
  · right
    intro n hn
    have : (⟨n, hn⟩ : ↥N) ∈ K.subgroupOf N := by
      rw [h]
      exact Subgroup.mem_top _
    exact this

theorem eq_bot_of_pow_four [Finite X] [N.Normal] (hNs : IsSimpleGroup ↥N)
    (hNn : ∃ x y : ↥N, x * y ≠ y * x) (hC : ∀ x : X, (∀ n ∈ N, x * n = n * x) → x = 1)
    {K : Subgroup X} [K.Normal] (h4 : ∀ k ∈ K, k ^ 4 = 1) : K = ⊥ := by
  rcases eq_bot_or_le_of_normal hNs hC (K := K) with h | h
  · exact h
  · exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥N := fun g => ⟨2, by
      apply Subtype.ext
      have := h4 (g : X) (h g.2)
      simpa using this⟩
    obtain ⟨x, y, hxy⟩ := hNn
    haveI : Nontrivial ↥N := ⟨⟨x, 1, fun h1 => hxy (by rw [h1, one_mul, mul_one])⟩⟩
    have hbot := hp.bot_lt_center
    rcases hNs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥N) with hc | hc
    · rw [hc] at hbot
      exact lt_irrefl _ hbot
    · apply hxy
      have hx : x ∈ Subgroup.center ↥N := by rw [hc]; exact Subgroup.mem_top _
      exact (Subgroup.mem_center_iff.mp hx y).symm

theorem exists_irreducible_module [Finite X] [N.Normal] (hNs : IsSimpleGroup ↥N)
    (hNn : ∃ x y : ↥N, x * y ≠ y * x) (hC : ∀ x : X, (∀ n ∈ N, x * n = n * x) → x = 1) {a : X}
    (ha1 : a ≠ 1) (hX : ∀ x : X, x ∈ N ∨ x * a ∈ N) {M : Type} [AddCommGroup M]
    [Module (ZMod 2) M] [Finite M] (ρ₀ : X →* LinearMap.GeneralLinearGroup (ZMod 2) M)
    (hinj : Function.Injective ρ₀) (hτ : IsF2Transvection (ρ₀ a)) :
    ∃ (U : Type) (_ : AddCommGroup U) (_ : Module (ZMod 2) U) (_ : Finite U)
      (ψ : X →* LinearMap.GeneralLinearGroup (ZMod 2) U), Function.Injective ψ ∧
      (∀ T : Submodule (ZMod 2) U,
        (∀ g ∈ ψ.range, ∀ w ∈ T, (g : U →ₗ[ZMod 2] U) w ∈ T) → T = ⊥ ∨ T = ⊤) ∧
      (∃ T : Set (LinearMap.GeneralLinearGroup (ZMod 2) U),
        (∀ t ∈ T, IsF2Transvection t) ∧ ψ.range = Subgroup.closure T) ∧
      IsF2Transvection (ψ a) := by
  obtain ⟨φ, a₀, hφa, hφ, ha₀, hτeq⟩ := (isF2Transvection_iff _).1 hτ
  have hτX : tv φ a₀ hφa ∈ ρ₀.range := ⟨a, hτeq⟩
  have hO2 : ∀ K : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) M), K ≤ ρ₀.range →
      (∀ x ∈ ρ₀.range, ∀ k ∈ K, x * k * x⁻¹ ∈ K) → (∀ k ∈ K, k ^ 4 = 1) → K = ⊥ := by
    intro K hKR hKn hK4
    haveI : (K.comap ρ₀).Normal := ⟨fun n hn g => by
      have := hKn (ρ₀ g) ⟨g, rfl⟩ (ρ₀ n) hn
      rwa [← map_mul, ← map_inv, ← map_mul] at this⟩
    have h4 : ∀ k ∈ K.comap ρ₀, k ^ 4 = 1 := fun k hk =>
      hinj (by rw [map_pow, map_one]; exact hK4 _ hk)
    have hbot := eq_bot_of_pow_four hNs hNn hC h4
    rw [eq_bot_iff]
    intro k hk
    obtain ⟨x, rfl⟩ := hKR hk
    have hx : x ∈ K.comap ρ₀ := hk
    rw [hbot, Subgroup.mem_bot] at hx
    rw [hx, map_one]
    exact Subgroup.one_mem _
  let S : i285_Setup M := ⟨ρ₀.range, φ, a₀, hφa, hφ, ha₀, hτX, hO2⟩
  have hSτ : S.τ = ρ₀ a := hτeq.symm
  have hXW : S.X ≤ S.W := by
    haveI : (S.W.comap ρ₀).Normal := ⟨fun n hn g => by
      have := S.conj_mem_W (x := ρ₀ g) ⟨g, rfl⟩ (w := ρ₀ n) hn
      rwa [← map_mul, ← map_inv, ← map_mul] at this⟩
    have haW : a ∈ S.W.comap ρ₀ := by
      rw [Subgroup.mem_comap, ← hSτ]
      exact S.τ_mem_W
    have hle : N ≤ S.W.comap ρ₀ := by
      rcases eq_bot_or_le_of_normal hNs hC (K := S.W.comap ρ₀) with h | h
      · rw [h, Subgroup.mem_bot] at haW
        exact absurd haW ha1
      · exact h
    rintro _ ⟨x, rfl⟩
    show x ∈ S.W.comap ρ₀
    rcases hX x with hx | hx
    · exact hle hx
    · have := (S.W.comap ρ₀).mul_mem (hle hx) ((S.W.comap ρ₀).inv_mem haW)
      rwa [mul_inv_cancel_right] at this
  obtain ⟨U, _, _, _, ψ₀, hinj₀, hirr, hgen, hψτ⟩ := exists_irreducible_section S hXW
  have hrange : (ψ₀.comp ρ₀.rangeRestrict).range = ψ₀.range := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, hx⟩ := ρ₀.rangeRestrict_surjective y
      exact ⟨x, by simp [hx]⟩
  refine ⟨U, inferInstance, inferInstance, inferInstance, ψ₀.comp ρ₀.rangeRestrict,
    hinj₀.comp (MonoidHom.rangeRestrict_injective_iff.2 hinj), ?_, ?_, ?_⟩
  · intro T hT
    rw [hrange] at hT
    exact hirr T hT
  · obtain ⟨T, hT, hTr⟩ := hgen
    exact ⟨T, hT, by rw [hrange]; exact hTr⟩
  · have : (⟨S.τ, S.hτX⟩ : ↥S.X) = ρ₀.rangeRestrict a := Subtype.ext hSτ
    rw [this] at hψτ
    exact hψτ

end Group

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGTv
