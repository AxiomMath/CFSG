module

public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain
public import CFSG.ClassicalInvolution.RouteD.LocalPair
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSU

public section

namespace CFSG.ClassicalInvolution.RouteD.SU4Pattern

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

@[expose] def restrictAut4 {Y : Type*} [Group Y] (ρ : Y ≃* Y)
    (hρ : ∀ y, ρ (ρ (ρ (ρ y))) = y) (Q : Subgroup Y) (hQ : ∀ y ∈ Q, ρ y ∈ Q) : Q ≃* Q where
  toFun y := ⟨ρ y, hQ y y.2⟩
  invFun y := ⟨ρ (ρ (ρ y)), hQ _ (hQ _ (hQ _ y.2))⟩
  left_inv y := Subtype.ext (hρ y)
  right_inv y := Subtype.ext (hρ y)
  map_mul' x y := Subtype.ext (map_mul ρ (x : Y) (y : Y))

section Stab

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem su4_eq_top_of_normal_of_not_le_center (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    {N : Subgroup (Su K p f 4)} [N.Normal] (hN : ¬ N ≤ Subgroup.center (Su K p f 4)) :
    N = ⊤ := by
  classical
  have hq' := CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple_su (F := K) (p := p) (f := f)
    hK hq (k := 4) (by norm_num)
  have hsimple : IsSimpleGroup (Su K p f 4 ⧸ Subgroup.center (Su K p f 4)) := hq'.2
  set Z : Subgroup (Su K p f 4) := Subgroup.center (Su K p f 4) with hZ
  have hmapN : (N.map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
  rcases hmapN.eq_bot_or_eq_top with h | h
  · exfalso
    apply hN
    intro n hn
    have : QuotientGroup.mk' Z n ∈ N.map (QuotientGroup.mk' Z) := ⟨n, hn, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff n).1 this
  · have hsup : (⊤ : Subgroup (Su K p f 4)) ≤ N ⊔ Z := by
      intro g _
      have : QuotientGroup.mk' Z g ∈ N.map (QuotientGroup.mk' Z) := by rw [h]; trivial
      obtain ⟨n, hn, hng⟩ := this
      have hmem : n⁻¹ * g ∈ Z := QuotientGroup.eq.mp hng
      have : g = n * (n⁻¹ * g) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hmem)
    have hperf : (⊤ : Subgroup (Su K p f 4)) ≤ ⁅(⊤ : Subgroup (Su K p f 4)), ⊤⁆ := by
      have h1 := hq'.1
      rw [← commutator_def, h1]
    exact eq_top_iff.2 (le_of_perfect_of_le_sup_center le_rfl hperf hsup)

theorem stab_of_noncentral (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) {X : Type} [Group X]
    (ψ : Su K p f 4 →* X) (hnorm : ψ.range.Normal) (ρ : X ≃* X) {y₀ : Su K p f 4}
    (hy₀ : y₀ ∉ Subgroup.center (Su K p f 4)) (hρy₀ : ρ (ψ y₀) ∈ ψ.range) :
    ∀ x, ρ (ψ x) ∈ ψ.range := by
  set N : Subgroup (Su K p f 4) := ψ.range.comap (ρ.toMonoidHom.comp ψ) with hNdef
  have hNn : N.Normal := ⟨fun n hn g => by
    have hn' : ρ (ψ n) ∈ ψ.range := hn
    show ρ (ψ (g * n * g⁻¹)) ∈ ψ.range
    simp only [map_mul, map_inv]
    exact hnorm.conj_mem _ hn' _⟩
  have hN : ¬ N ≤ Subgroup.center (Su K p f 4) := fun hle => hy₀ (hle hρy₀)
  have hNtop := su4_eq_top_of_normal_of_not_le_center hK hq hN
  intro x
  have : x ∈ N := by rw [hNtop]; trivial
  exact this

end Stab

section Lift

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_lift_of_stab (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {X : Type} [Group X] (ψ : Su K p f 4 →* X) (hker : ψ.ker ≤ Subgroup.center (Su K p f 4))
    (ρ : X ≃* X) (hρ : ∀ x, ρ (ρ (ρ (ρ x))) = x) (hstab : ∀ x, ρ (ψ x) ∈ ψ.range) :
    ∃ (α : Su K p f 4 →* Su K p f 4) (g : GL (Fin 4) K) (φ : K ≃+* K),
      (∀ x, ψ (α x) = ρ (ψ x)) ∧
      (∀ x, ((α x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (g : Matrix (Fin 4) (Fin 4) K) *
          φ.mapMatrix ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) ∧
      ((g : Matrix (Fin 4) (Fin 4) K).map (unitaryInvolution K p f))ᵀ *
        (g : Matrix (Fin 4) (Fin 4) K) = 1 := by
  have hQ : ∀ y ∈ ψ.range, ρ y ∈ ψ.range := by
    rintro _ ⟨x, rfl⟩
    exact hstab x
  obtain ⟨α, g, φ, h1, h2, h3, -⟩ := unitaryAutClassification_isometry_of_card hK hp2 hq
    (by norm_num : 3 ≤ 4) ψ.range ψ.rangeRestrict ψ.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hker) (restrictAut4 ρ hρ ψ.range hQ)
  exact ⟨α, g, φ, fun x => congrArg Subtype.val (h1 x), h2, h3⟩

end Lift

end CFSG.ClassicalInvolution.RouteD.SU4Pattern
