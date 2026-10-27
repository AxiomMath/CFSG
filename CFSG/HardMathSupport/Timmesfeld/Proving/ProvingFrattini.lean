module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

variable {X : Type*} [Group X]

theorem exists_mul_mem_normalizer_of_commutator_mem_prime [Finite X] {p : ℕ} (hp : p.Prime)
    {N B T : Subgroup X} [N.Normal]
    (hT : T = B ⊔ N)
    (S : Sylow p T) (hBS : B.subgroupOf T ≤ S) {y : X}
    (hy : ∀ b ∈ B, y * b * y⁻¹ * b⁻¹ ∈ N) :
    ∃ n ∈ N, n⁻¹ * y ∈ Subgroup.normalizer
      (((S : Subgroup T).map T.subtype : Subgroup X) : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  have hBT : B ≤ T := hT ▸ le_sup_left
  have hNT : N ≤ T := hT ▸ le_sup_right
  set P : Subgroup X := (S : Subgroup T).map T.subtype with hP
  have hPT : P ≤ T := Subgroup.map_subtype_le _
  have hBP : B ≤ P := fun b hb => ⟨⟨b, hBT hb⟩,
    hBS ((Subgroup.mem_subgroupOf).mpr hb), rfl⟩
  have hPp : IsPGroup p P := S.isPGroup'.map _
  have hyT : ∀ t ∈ T, y * t * y⁻¹ ∈ T := by
    intro t ht
    rw [hT] at ht
    obtain ⟨b, hb, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ht
    have h1 : y * b * y⁻¹ ∈ T := by
      have : y * b * y⁻¹ = (y * b * y⁻¹ * b⁻¹) * b := by group
      rw [this]
      exact mul_mem (hNT (hy b hb)) (hBT hb)
    have h2 : y * n * y⁻¹ ∈ T := hNT (‹N.Normal›.conj_mem n hn y)
    have : y * (b * n) * y⁻¹ = (y * b * y⁻¹) * (y * n * y⁻¹) := by group
    rw [this]
    exact mul_mem h1 h2
  set P' : Subgroup X := P.map (MulAut.conj y).toMonoidHom with hP'
  have hP'T : P' ≤ T := by
    rintro _ ⟨q, hq, rfl⟩
    exact hyT q (hPT hq)
  have hP'p : IsPGroup p (P'.subgroupOf T) :=
    (hPp.map _).comap_of_injective _ T.subtype_injective
  obtain ⟨S₂, hS₂⟩ := IsPGroup.exists_le_sylow hP'p
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥T) S S₂
  have hconj : ∀ x ∈ P, ∃ s ∈ P, (g : X) * s * (g : X)⁻¹ = y * x * y⁻¹ := by
    intro x hx
    have hxS : (⟨y * x * y⁻¹, hyT x (hPT hx)⟩ : T) ∈ (S₂ : Subgroup T) :=
      hS₂ ((Subgroup.mem_subgroupOf).mpr ⟨x, hx, rfl⟩)
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxS
    obtain ⟨s, hs, hsx⟩ := hxS
    refine ⟨s, ⟨s, hs, rfl⟩, ?_⟩
    have := congrArg Subtype.val hsx
    simpa [MulAut.smul_def] using this
  set m : X := (g : X)⁻¹ * y with hm
  have hmP : ∀ x ∈ P, m * x * m⁻¹ ∈ P := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ := hconj x hx
    have : m * x * m⁻¹ = s := by
      calc m * x * m⁻¹ = (g : X)⁻¹ * (y * x * y⁻¹) * (g : X) := by rw [hm]; group
        _ = (g : X)⁻¹ * ((g : X) * s * (g : X)⁻¹) * (g : X) := by rw [hsx]
        _ = s := by group
    rw [this]
    exact hs
  have hmnorm : m ∈ Subgroup.normalizer (P : Set X) := by
    have hle : P.map (MulAut.conj m).toMonoidHom ≤ P := by
      rintro _ ⟨x, hx, rfl⟩
      exact hmP x hx
    have heq : P.map (MulAut.conj m).toMonoidHom = P := by
      have hc : Nat.card (P.map (MulAut.conj m).toMonoidHom) = Nat.card P :=
        Subgroup.card_map_of_injective (MulAut.conj m).injective
      exact Subgroup.eq_of_le_of_card_ge hle hc.ge
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => hmP h hh
    · intro hh
      have : m * h * m⁻¹ ∈ P.map (MulAut.conj m).toMonoidHom := by rw [heq]; exact hh
      obtain ⟨x, hx, hxh⟩ := this
      have : x = h := (MulAut.conj m).injective hxh
      rw [← this]
      exact hx
  have hgNP : (g : X) ∈ N ⊔ P := by
    have : (g : X) ∈ T := g.2
    have hTle : T ≤ N ⊔ P := by
      rw [hT]
      exact sup_le (hBP.trans le_sup_right) le_sup_left
    exact hTle this
  obtain ⟨n, hn, q, hq, hnq⟩ := Subgroup.mem_sup_of_normal_left.mp hgNP
  refine ⟨n, hn, ?_⟩
  have : n⁻¹ * y = q * m := by
    rw [hm, ← hnq]
    group
  rw [this]
  exact mul_mem (Subgroup.le_normalizer hq) hmnorm

end CFSG.HardMathSupport.Timmesfeld.Proving

end
