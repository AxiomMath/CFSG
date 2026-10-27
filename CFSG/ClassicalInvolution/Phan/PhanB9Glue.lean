module

public import CFSG.ClassicalInvolution.Phan.PhanB2Family
public import CFSG.ClassicalInvolution.Asc77.AscB3C2
import CFSG.ClassicalInvolution.Phan.Coherent
import CFSG.ClassicalInvolution.Phan.TorusAgree
import CFSG.ClassicalInvolution.Phan.AutSU3
public import CFSG.ClassicalInvolution.Phan.PhanD5Mat

public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.PhanD4 (exists_normOne_sq_ne_one torusTwo_mul_mul_inv)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock)
open CFSG.ClassicalInvolution.Asc77.B3C (twShort SymplecticPhanPair)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem eq_or_pow_four_of_normalizes {x₀ : normOne (unitaryInvolution K p f)}
    (hx₀ : x₀ * x₀ ≠ 1) {g : Su K p f 2}
    (h : g * torusTwo (unitaryInvolution K p f) x₀ * g⁻¹ ∈
      (torusTwo (unitaryInvolution K p f)).range) :
    g ∈ (torusTwo (unitaryInvolution K p f)).range ∨ g ^ 4 = 1 := by
  obtain ⟨t, ht⟩ := h
  have h' : torusTwo (unitaryInvolution K p f) t * g =
      g * torusTwo (unitaryInvolution K p f) x₀ := by rw [ht]; group
  have h'' := congrArg (fun g : Su K p f 2 => ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) h'
  simp only [Subgroup.coe_mul, Units.val_mul, coe_torusTwo] at h''
  have e00 := congrFun (congrFun h'' 0) 0
  have e01 := congrFun (congrFun h'' 0) 1
  have e10 := congrFun (congrFun h'' 1) 0
  have e11 := congrFun (congrFun h'' 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hs : ((x₀ : Kˣ) : K) ^ 2 ≠ 1 := by
    intro h1
    apply hx₀
    exact Subtype.ext (Units.ext (by simpa [pow_two] using h1))
  have hs0 : ((x₀ : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hdet1 : ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 *
      ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 -
      ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 *
      ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have := g.2.1
    rwa [Matrix.det_fin_two] at this
  rcases monomial_aux hs hs0 (by simp [hdet1]) e00.symm e01.symm e10.symm e11.symm with
    ⟨hy, hz⟩ | ⟨hx, hw⟩
  · exact Or.inl (mem_range_torusTwo_of_offDiag g hy hz)
  · right
    have hyz : ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 *
        ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = -1 := by
      rw [hx, hw] at hdet1
      linear_combination -hdet1
    refine Subtype.ext (Units.ext ?_)
    have hM : ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = -1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, hx, hw] <;> linear_combination hyz
    show (((g ^ 4 : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
    have : g ^ 4 = (g * g) * (g * g) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [this]
    simp only [Subgroup.coe_mul, Units.val_mul, hM]
    simp

variable {hK : Nat.card K = (p ^ f) ^ 2} {F : Type} [Field F] {h2 : (2 : F) ≠ 0}
  (C : B2Coord hK F h2) {G : Type} [Group G]

include hK in
theorem alpha_torus_le (hq7 : 7 ≤ p ^ f)
    {θ₀ : Su K p f 3 →* G} (hker : θ₀.ker ≤ Subgroup.center (Su K p f 3))
    {ϑ : StatedSp 2 F →* G}
    (hcomm : ∀ x ∈ (B12 K p f).map θ₀, ∀ y ∈ C.s.range.map ϑ, x * y = y * x)
    (α : Su K p f 2 ≃* Su K p f 2)
    (hα : ∀ g, θ₀ (embSUid (unitaryInvolution K p f) 0 (α g)) = ϑ (C.ℓ g)) :
    (torusTwo (unitaryInvolution K p f)).range.map α.toMonoidHom ≤
      (torusTwo (unitaryInvolution K p f)).range := by
  obtain ⟨x₀, hx₀⟩ := exists_normOne_sq_ne_one hK (by omega : 3 ≤ p ^ f)
  have hx₀1 : (x₀ : Kˣ) ≠ 1 := by
    intro h
    apply hx₀
    have : x₀ = 1 := Subtype.ext h
    rw [this, mul_one]
  set a₀ := θ₀ (embSUid (unitaryInvolution K p f) 2 (torusTwo (unitaryInvolution K p f) x₀))
    with ha₀
  have ha₀mem : a₀ ∈ (B12 K p f).map θ₀ := ⟨_, ⟨_, rfl⟩, rfl⟩
  have centr : ∀ A : Su K p f 2, θ₀ (embSUid (unitaryInvolution K p f) 0 A) * a₀ =
      a₀ * θ₀ (embSUid (unitaryInvolution K p f) 0 A) →
      A ∈ (torusTwo (unitaryInvolution K p f)).range := fun A h =>
    mem_diagTorus2_of_map_commute_two hK hker hx₀1 h
  have centr2 : ∀ v : normOne (unitaryInvolution K p f),
      θ₀ (embSUid (unitaryInvolution K p f) 0 (torusTwo (unitaryInvolution K p f) v)) * a₀ =
        a₀ * θ₀ (embSUid (unitaryInvolution K p f) 0 (torusTwo (unitaryInvolution K p f) v)) := by
    intro v
    rw [ha₀, ← map_mul, ← map_mul, embSUid_two_torus_comm]
  have hcy : ∀ y : normOne (unitaryInvolution K p f),
      ϑ (C.s (torusTwo (unitaryInvolution K p f) y)) * a₀ =
        a₀ * ϑ (C.s (torusTwo (unitaryInvolution K p f) y)) := fun y =>
    (hcomm a₀ ha₀mem _ ⟨C.s (torusTwo (unitaryInvolution K p f) y), ⟨_, rfl⟩, rfl⟩).symm
  have step5 : ∀ u v : normOne (unitaryInvolution K p f),
      α (torusTwo (unitaryInvolution K p f) u) * torusTwo (unitaryInvolution K p f) v *
        (α (torusTwo (unitaryInvolution K p f) u))⁻¹ ∈
        (torusTwo (unitaryInvolution K p f)).range := by
    intro u v
    apply centr
    obtain ⟨g, hg⟩ := α.surjective (torusTwo (unitaryInvolution K p f) v)
    have e1 : α (torusTwo (unitaryInvolution K p f) u) * torusTwo (unitaryInvolution K p f) v *
        (α (torusTwo (unitaryInvolution K p f) u))⁻¹ =
        α (torusTwo (unitaryInvolution K p f) u * g *
          (torusTwo (unitaryInvolution K p f) u)⁻¹) := by
      rw [map_mul, map_mul, map_inv, hg]
    have e2 := congrArg ϑ (C.conj_s_ℓ u⁻¹ g)
    rw [inv_inv, ← torusTwo_mul_mul_inv hK, map_mul, map_mul, map_inv ϑ] at e2
    have hA : θ₀ (embSUid (unitaryInvolution K p f) 0 (α (torusTwo (unitaryInvolution K p f) u) *
        torusTwo (unitaryInvolution K p f) v * (α (torusTwo (unitaryInvolution K p f) u))⁻¹)) =
        ϑ (C.s (torusTwo (unitaryInvolution K p f) u⁻¹)) *
          θ₀ (embSUid (unitaryInvolution K p f) 0 (torusTwo (unitaryInvolution K p f) v)) *
          (ϑ (C.s (torusTwo (unitaryInvolution K p f) u⁻¹)))⁻¹ := by
      rw [e1, hα, ← hg, hα g]
      exact e2.symm
    rw [hA]
    have hc' : Commute (ϑ (C.s (torusTwo (unitaryInvolution K p f) u⁻¹))) a₀ := hcy _
    have hm' : Commute (θ₀ (embSUid (unitaryInvolution K p f) 0
        (torusTwo (unitaryInvolution K p f) v))) a₀ := centr2 v
    exact ((hc'.mul_left hm').mul_left hc'.inv_left).eq
  obtain ⟨u₀, hu₀⟩ := IsCyclic.exists_generator (α := normOne (unitaryInvolution K p f))
  have hord : orderOf u₀ = p ^ f + 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu₀, card_normOne hK]
  have hγ : α (torusTwo (unitaryInvolution K p f) u₀) ∈
      (torusTwo (unitaryInvolution K p f)).range := by
    rcases eq_or_pow_four_of_normalizes hx₀ (g := α (torusTwo (unitaryInvolution K p f) u₀))
      (step5 u₀ x₀) with h | h
    · exact h
    · exfalso
      have h1 : orderOf (α (torusTwo (unitaryInvolution K p f) u₀)) ∣ 4 :=
        orderOf_dvd_of_pow_eq_one h
      have h2' : orderOf (α (torusTwo (unitaryInvolution K p f) u₀)) = p ^ f + 1 := by
        have := orderOf_injective α.toMonoidHom α.injective (torusTwo (unitaryInvolution K p f) u₀)
        simp only [MulEquiv.coe_toMonoidHom] at this
        rw [this, orderOf_injective _ (torusTwo_injective _) u₀, hord]
      have := Nat.le_of_dvd (by norm_num) h1
      omega
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  obtain ⟨k, hk⟩ := hu₀ v
  rw [MulEquiv.coe_toMonoidHom, ← hk, map_zpow, map_zpow]
  exact zpow_mem hγ k

end CFSG.ClassicalInvolution.PhanB3
