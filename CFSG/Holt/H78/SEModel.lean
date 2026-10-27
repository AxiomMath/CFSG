module

public import CFSG.GH74.Uniqueness.Bender.Lemma32
public import CFSG.GH74.Uniqueness.Bender.UnitaryIrreducible
public import CFSG.GH74.Uniqueness.Bender.OddCentralizer
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Holt.H78

open MulAction CFSG.GH74.Uniqueness.Bender
open scoped Pointwise

structure IsBenderAction (X : Type*) [Group X] (Ω : Type*) [MulAction X Ω] (n i e : ℕ) :
    Prop where
  benderType : BenderType X n i e
  isPretransitive : IsPretransitive X Ω
  card_eq : Nat.card Ω = (2 ^ n) ^ i + 1

namespace IsBenderAction

variable {X : Type*} [Group X] {Ω : Type*} [MulAction X Ω] {n i e : ℕ}

section Basic

theorem params (hA : IsBenderAction X Ω n i e) : 1 ≤ i ∧ i ≤ 3 ∧ 2 ≤ n := by
  rcases hA.benderType.cases' with ⟨rfl, -, hn⟩ | ⟨rfl, -, a, ha, rfl⟩ | ⟨rfl, -, hn⟩ <;> omega

theorem four_le_q (hA : IsBenderAction X Ω n i e) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hA.params.2.2

theorem four_le_pow (hA : IsBenderAction X Ω n i e) : 4 ≤ (2 ^ n) ^ i :=
  hA.four_le_q.trans (Nat.le_self_pow (by have := hA.params; omega) _)

theorem finite (hA : IsBenderAction X Ω n i e) : Finite Ω :=
  Nat.finite_of_card_ne_zero (by rw [hA.card_eq]; omega)

theorem odd_card (hA : IsBenderAction X Ω n i e) : Odd (Nat.card Ω) := by
  rw [hA.card_eq]
  obtain ⟨hi, -, hn⟩ := hA.params
  exact (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by omega⟩).add_one

theorem exists_le_stabilizer (hA : IsBenderAction X Ω n i e) {P : Subgroup X}
    (hP : IsPGroup 2 P) : ∃ ω : Ω, P ≤ stabilizer X ω := by
  have := hA.finite
  obtain ⟨ω, hω⟩ := fixSet_nonempty_of_odd hA.odd_card hP
  exact ⟨ω, mem_fixSet_iff_le_stabilizer.mp hω⟩

theorem exists_sylow_le_stabilizer (hA : IsBenderAction X Ω n i e) (ω : Ω) :
    ∃ Q : Sylow 2 X, (Q : Subgroup X) ≤ stabilizer X ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hA.isPretransitive
  obtain ⟨Q₀⟩ : Nonempty (Sylow 2 X) := inferInstance
  obtain ⟨ω₀, hω₀⟩ := hA.exists_le_stabilizer Q₀.isPGroup'
  obtain ⟨g, rfl⟩ := exists_smul_eq X ω₀ ω
  refine ⟨g • Q₀, fun x hx => ?_⟩
  have hx' := hω₀ ((mem_sylow_smul_iff g Q₀ x).mp hx)
  rw [mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff] at hx'
  exact mem_stabilizer_iff.mpr hx'

end Basic

private theorem smul_eq_iff_of_mul_self {t : X} (ht : t * t = 1) {a b : Ω} :
    t • a = b ↔ a = t • b := by
  constructor
  · rintro rfl
    rw [smul_smul, ht, one_smul]
  · rintro rfl
    rw [smul_smul, ht, one_smul]

section Borel

variable [Finite X]

theorem stabilizer_eq_borel (hA : IsBenderAction X Ω n i e) {ω : Ω} {Q : Sylow 2 X}
    (hQ : (Q : Subgroup X) ≤ stabilizer X ω) : stabilizer X ω = borel (Q : Subgroup X) := by
  have := hA.isPretransitive
  obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
  have hidx : (stabilizer X ω).index = (2 ^ n) ^ i + 1 := by
    rw [index_stabilizer_of_transitive, hA.card_eq]
  have hne : stabilizer X ω ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.index_top] at hidx
    have := hA.four_le_pow
    omega
  have hle := hA.benderType.le_borel_of_sylow_le Q hQ hne
  refine le_antisymm hle (Subgroup.relIndex_eq_one.mp ?_)
  have h1 := Subgroup.relIndex_mul_index hle
  rw [hidx, hc.index_eq] at h1
  exact Nat.eq_of_mul_eq_mul_right (by omega) (h1.trans (one_mul _).symm)

theorem mem_borel_iff (hA : IsBenderAction X Ω n i e) {ω : Ω} {Q : Sylow 2 X}
    (hQ : (Q : Subgroup X) ≤ stabilizer X ω) {x : X} :
    x ∈ borel (Q : Subgroup X) ↔ x • ω = ω := by
  rw [← hA.stabilizer_eq_borel hQ, mem_stabilizer_iff]

theorem mem_cartan_iff (hA : IsBenderAction X Ω n i e) {ω : Ω} {Q : Sylow 2 X}
    (hQ : (Q : Subgroup X) ≤ stabilizer X ω) {t : X} (ht : t * t = 1) {x : X} :
    x ∈ cartan (Q : Subgroup X) t ↔ x • ω = ω ∧ x • (t • ω) = t • ω := by
  rw [cartan, Subgroup.mem_inf, mem_conjugate_iff_mul_inv, hA.mem_borel_iff hQ,
    hA.mem_borel_iff hQ, inv_eq_of_mul_self ht, mul_smul, mul_smul,
    smul_eq_iff_of_mul_self ht, eq_comm]

theorem benderCore (hA : IsBenderAction X Ω n i e) {ω : Ω} {Q : Sylow 2 X}
    (hQ : (Q : Subgroup X) ≤ stabilizer X ω) {t : X} (ht : t * t = 1) (htω : t • ω ≠ ω) :
    BenderCore (2 ^ n) i e (Q : Subgroup X) t :=
  hA.benderType.benderCore Q ht fun h => htω ((hA.mem_borel_iff hQ).mp h)

theorem lemma32 (hA : IsBenderAction X Ω n i e) {ω : Ω} {Q : Sylow 2 X}
    (hQ : (Q : Subgroup X) ≤ stabilizer X ω) {t : X} (ht : t * t = 1) (htω : t • ω ≠ ω) :
    Lemma32 n i e (Q : Subgroup X) t :=
  hA.benderType.lemma_3_2 Q ht fun h => htω ((hA.mem_borel_iff hQ).mp h)

end Borel

section Regular

variable [Finite X]

theorem exists_mem_smul_eq (hA : IsBenderAction X Ω n i e) {ω : Ω} {Q : Sylow 2 X}
    (hQ : (Q : Subgroup X) ≤ stabilizer X ω) {β γ : Ω} (hβ : β ≠ ω) (hγ : γ ≠ ω) :
    ∃ p ∈ (Q : Subgroup X), p • β = γ := by
  have := hA.isPretransitive
  obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
  have key : ∀ δ : Ω, δ ≠ ω → ∃ p ∈ (Q : Subgroup X), p • (t • ω) = δ := by
    intro δ hδ
    obtain ⟨x, rfl⟩ := exists_smul_eq X ω δ
    have hx : x ∉ borel (Q : Subgroup X) := fun hx => hδ ((hA.mem_borel_iff hQ).mp hx)
    obtain ⟨p, hp, m, hm, rfl⟩ := hc.bruhat hx
    exact ⟨p, hp, by rw [mul_smul, mul_smul, (hA.mem_borel_iff hQ).mp hm]⟩
  obtain ⟨p₁, hp₁, h₁⟩ := key β hβ
  obtain ⟨p₂, hp₂, h₂⟩ := key γ hγ
  exact ⟨p₂ * p₁⁻¹, mul_mem hp₂ (inv_mem hp₁), by rw [mul_smul, ← h₁, inv_smul_smul, h₂]⟩

theorem eq_one_of_smul_eq (hA : IsBenderAction X Ω n i e) {ω : Ω} {Q : Sylow 2 X}
    (hQ : (Q : Subgroup X) ≤ stabilizer X ω) {p : X} (hp : p ∈ (Q : Subgroup X)) {β : Ω}
    (hβ : β ≠ ω) (hpβ : p • β = β) : p = 1 := by
  obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
  have ht0 : t • ω ≠ ω := fun h => hc.not_mem ((hA.mem_borel_iff hQ).mpr h)
  obtain ⟨p₁, hp₁, h₁⟩ := hA.exists_mem_smul_eq hQ ht0 hβ
  have hmem : p₁⁻¹ * p * p₁ ∈ (Q : Subgroup X) := mul_mem (mul_mem (inv_mem hp₁) hp) hp₁
  have hy : p₁⁻¹ * p * p₁ ∈ (Q : Subgroup X) ⊓ cartan (Q : Subgroup X) t := by
    refine ⟨hmem, (hA.mem_cartan_iff hQ hc.sq_eq_one).mpr ⟨hQ hmem, ?_⟩⟩
    rw [mul_smul, mul_smul, h₁, hpβ, ← h₁, inv_smul_smul]
  rw [hc.inf_eq, Subgroup.mem_bot] at hy
  have h : p = p₁ * (p₁⁻¹ * p * p₁) * p₁⁻¹ := by group
  rw [h, hy, mul_one, mul_inv_cancel]

theorem existsUnique_smul_eq (hA : IsBenderAction X Ω n i e) {ω : Ω} {Q : Sylow 2 X}
    (hQ : (Q : Subgroup X) ≤ stabilizer X ω) {β γ : Ω} (hβ : β ≠ ω) (hγ : γ ≠ ω) :
    ∃! p, p ∈ (Q : Subgroup X) ∧ p • β = γ := by
  obtain ⟨p, hp, hpβ⟩ := hA.exists_mem_smul_eq hQ hβ hγ
  refine ⟨p, ⟨hp, hpβ⟩, fun p' ⟨hp', hp'β⟩ => ?_⟩
  have h := hA.eq_one_of_smul_eq hQ (mul_mem (inv_mem hp) hp') hβ
    (by rw [mul_smul, hp'β, ← hpβ, inv_smul_smul])
  exact (inv_mul_eq_one.mp h).symm

theorem existsUnique_le_stabilizer (hA : IsBenderAction X Ω n i e) (Q : Sylow 2 X) :
    ∃! ω : Ω, (Q : Subgroup X) ≤ stabilizer X ω := by
  obtain ⟨ω, hω⟩ := hA.exists_le_stabilizer Q.isPGroup'
  refine ⟨ω, hω, fun ω' hω' => ?_⟩
  by_contra hne
  have hbot : (Q : Subgroup X) = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    exact Subgroup.mem_bot.mpr (hA.eq_one_of_smul_eq hω hp hne (hω' hp))
  obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
  have h := hc.card_eq
  rw [hbot, Subgroup.card_bot] at h
  have := hA.four_le_pow
  omega

theorem existsUnique_fixed (hA : IsBenderAction X Ω n i e) {x : X} (hx : orderOf x = 2) :
    ∃! ω : Ω, x • ω = ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨ω, hω, -⟩ := hA.existsUnique_le_stabilizer Q
  have hxQ : x ∈ (Q : Subgroup X) := hQ (Subgroup.mem_zpowers x)
  refine ⟨ω, hω hxQ, fun β hβ => ?_⟩
  by_contra hne
  have h1 := hA.eq_one_of_smul_eq hω hxQ hne hβ
  rw [h1, orderOf_one] at hx
  omega

theorem exists_involution_smul_eq (hA : IsBenderAction X Ω n i e) {α β : Ω} (hαβ : α ≠ β) :
    ∃ t : X, t * t = 1 ∧ t • α = β := by
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer α
  obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
  have ht0 : t • α ≠ α := fun h => hc.not_mem ((hA.mem_borel_iff hQ).mpr h)
  obtain ⟨p, hp, hpβ⟩ := hA.exists_mem_smul_eq hQ ht0 hαβ.symm
  refine ⟨p * t * p⁻¹, ?_, ?_⟩
  · calc p * t * p⁻¹ * (p * t * p⁻¹) = p * (t * t) * p⁻¹ := by group
      _ = 1 := by rw [hc.sq_eq_one, mul_one, mul_inv_cancel]
  · rw [mul_smul, mul_smul, mem_stabilizer_iff.mp (hQ (inv_mem hp)), hpβ]

end Regular

section TwoPoint

variable [Finite X]

theorem stabilizer_inf_eq_cartan (hA : IsBenderAction X Ω n i e) {α β : Ω} {Q : Sylow 2 X}
    (hQ : (Q : Subgroup X) ≤ stabilizer X α) {t : X} (ht : t * t = 1) (htα : t • α = β) :
    stabilizer X α ⊓ stabilizer X β = cartan (Q : Subgroup X) t := by
  ext x
  rw [hA.mem_cartan_iff hQ ht, htα, Subgroup.mem_inf, mem_stabilizer_iff, mem_stabilizer_iff]

theorem exists_benderCore (hA : IsBenderAction X Ω n i e) {α β : Ω} (hαβ : α ≠ β) :
    ∃ (Q : Sylow 2 X) (t : X), (Q : Subgroup X) ≤ stabilizer X α ∧ t • α = β ∧
      BenderCore (2 ^ n) i e (Q : Subgroup X) t := by
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer α
  obtain ⟨t, ht, htα⟩ := hA.exists_involution_smul_eq hαβ
  exact ⟨Q, t, hQ, htα, hA.benderCore hQ ht (htα.trans_ne hαβ.symm)⟩

theorem isCyclic_stabilizer_inf (hA : IsBenderAction X Ω n i e) {α β : Ω} (hαβ : α ≠ β) :
    IsCyclic ↥(stabilizer X α ⊓ stabilizer X β) := by
  obtain ⟨Q, t, hQ, htα, hc⟩ := hA.exists_benderCore hαβ
  rw [hA.stabilizer_inf_eq_cartan hQ hc.sq_eq_one htα]
  exact hc.isCyclic

theorem card_stabilizer_inf (hA : IsBenderAction X Ω n i e) {α β : Ω} (hαβ : α ≠ β) :
    Nat.card ↥(stabilizer X α ⊓ stabilizer X β) = (2 ^ n - 1) * e := by
  obtain ⟨Q, t, hQ, htα, hc⟩ := hA.exists_benderCore hαβ
  rw [hA.stabilizer_inf_eq_cartan hQ hc.sq_eq_one htα]
  exact hc.card_cartan

theorem odd_card_stabilizer_inf (hA : IsBenderAction X Ω n i e) {α β : Ω} (hαβ : α ≠ β) :
    Odd (Nat.card ↥(stabilizer X α ⊓ stabilizer X β)) := by
  obtain ⟨Q, t, hQ, htα, hc⟩ := hA.exists_benderCore hαβ
  rw [hA.stabilizer_inf_eq_cartan hQ hc.sq_eq_one htα]
  exact hc.odd_card_cartan

theorem stabilizer_inf_decomposition (hA : IsBenderAction X Ω n i e) {α β : Ω}
    {Q : Sylow 2 X} (hQ : (Q : Subgroup X) ≤ stabilizer X α) (hαβ : α ≠ β) {t : X}
    (ht : t * t = 1) (htα : t • α = β) :
    IsCyclic ↥⁅stabilizer X α ⊓ stabilizer X β, Subgroup.zpowers t⁆ ∧
      Nat.card ↥⁅stabilizer X α ⊓ stabilizer X β, Subgroup.zpowers t⁆ = 2 ^ n - 1 ∧
      (∀ d ∈ ⁅stabilizer X α ⊓ stabilizer X β, Subgroup.zpowers t⁆, t * d * t = d⁻¹) ∧
      (∀ z ∈ rootCenter (Q : Subgroup X), z ≠ 1 → ∀ z' ∈ rootCenter (Q : Subgroup X), z' ≠ 1 →
        ∃! d, d ∈ ⁅stabilizer X α ⊓ stabilizer X β, Subgroup.zpowers t⁆ ∧ z' = d⁻¹ * z * d) ∧
      IsCyclic ↥(stabilizer X α ⊓ stabilizer X β ⊓ Subgroup.centralizer {t}) ∧
      Nat.card ↥(stabilizer X α ⊓ stabilizer X β ⊓ Subgroup.centralizer {t}) = e ∧
      stabilizer X α ⊓ stabilizer X β = ⁅stabilizer X α ⊓ stabilizer X β, Subgroup.zpowers t⁆ ⊔
        (stabilizer X α ⊓ stabilizer X β ⊓ Subgroup.centralizer {t}) ∧
      ⁅stabilizer X α ⊓ stabilizer X β, Subgroup.zpowers t⁆ ⊓
        (stabilizer X α ⊓ stabilizer X β ⊓ Subgroup.centralizer {t}) = ⊥ := by
  have hL := hA.lemma32 hQ ht (htα.trans_ne hαβ.symm)
  have hc := hA.benderCore hQ ht (htα.trans_ne hαβ.symm)
  rw [hA.stabilizer_inf_eq_cartan hQ ht htα]
  exact ⟨hL.isCyclic_commutator, hL.card_commutator, hL.inverted, hL.regular, hL.isCyclic_fix,
    hL.card_fix, hc.cartan_eq_sup, hc.inf_commutator_fixCartan⟩

theorem isStronglyEmbedded_stabilizer (hA : IsBenderAction X Ω n i e) (ω : Ω) :
    CFSG.IsStronglyEmbedded (stabilizer X ω) := by
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer ω
  obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
  rw [hA.stabilizer_eq_borel hQ]
  exact hc.strong

end TwoPoint

section SemiRegular

variable [Finite X]

theorem mem_rootCenter_of_commutator_mem (hA : IsBenderAction X Ω n i e) {α β : Ω}
    {Q : Sylow 2 X} (hQ : (Q : Subgroup X) ≤ stabilizer X α) (hαβ : α ≠ β) {d : X}
    (hd : d ∈ stabilizer X α ⊓ stabilizer X β) (hd1 : d ≠ 1) {x : X}
    (hx : x ∈ (Q : Subgroup X)) (hdx : d * x * d⁻¹ * x⁻¹ ∈ rootCenter (Q : Subgroup X)) :
    x ∈ rootCenter (Q : Subgroup X) := by
  obtain ⟨t, ht, htα⟩ := hA.exists_involution_smul_eq hαβ
  have hc := hA.benderCore hQ ht (htα.trans_ne hαβ.symm)
  have htQ : t ∉ borel (Q : Subgroup X) := hc.not_mem
  rw [hA.stabilizer_inf_eq_cartan hQ ht htα] at hd
  rcases hA.benderType.cases' with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, -, -⟩
  · have hZ : rootCenter (Q : Subgroup X) = Q :=
      Subgroup.eq_of_le_of_card_ge (rootCenter_le _) (by rw [hc.card_center, hc.card_eq, pow_one])
    rwa [hZ]
  · set z := d * x * d⁻¹ * x⁻¹ with hz
    have hzc := mem_rootCenter_iff.mp hdx
    have hdxd : d * x * d⁻¹ = z * x := by rw [hz]; group
    have hxx : x * x * d = d * (x * x) := by
      have h1 : d * (x * x) * d⁻¹ = x * x := by
        calc d * (x * x) * d⁻¹ = (d * x * d⁻¹) * (d * x * d⁻¹) := by group
          _ = z * x * (z * x) := by rw [hdxd]
          _ = z * (x * z) * x := by group
          _ = z * (z * x) * x := by rw [hzc.2 x hx]
          _ = (z * z) * (x * x) := by group
          _ = x * x := by rw [hc.center_sq z hdx, one_mul]
      calc x * x * d = d * (x * x) * d⁻¹ * d := by rw [h1]
        _ = d * (x * x) := by group
    have h2 := hc.eq_one_of_commute_cartan Q.isPGroup' hd hd1 (mul_mem hx hx) hxx
    exact hc.mem_rootCenter_of_mul_self hx h2
  · exact hA.benderType.fixedPointFree_unitary Q ht htQ hd hd1 hx hdx

theorem eq_one_of_commute_of_mem_commutator (hA : IsBenderAction X Ω n i e) {α β : Ω}
    {Q : Sylow 2 X} (hQ : (Q : Subgroup X) ≤ stabilizer X α) (hαβ : α ≠ β) {t : X}
    (ht : t * t = 1) (htα : t • α = β) {d : X}
    (hd : d ∈ ⁅stabilizer X α ⊓ stabilizer X β, Subgroup.zpowers t⁆) (hd1 : d ≠ 1) {x : X}
    (hx : x ∈ (Q : Subgroup X)) (hxd : x * d = d * x) : x = 1 := by
  have hL := hA.lemma32 hQ ht (htα.trans_ne hαβ.symm)
  rw [hA.stabilizer_inf_eq_cartan hQ ht htα] at hd
  have hdD : d ∈ stabilizer X α ⊓ stabilizer X β := by
    rw [hA.stabilizer_inf_eq_cartan hQ ht htα]
    exact (hA.benderCore hQ ht (htα.trans_ne hαβ.symm)).commutator_cartan_le hd
  have hxZ : x ∈ rootCenter (Q : Subgroup X) :=
    hA.mem_rootCenter_of_commutator_mem hQ hαβ hdD hd1 hx
      (by rw [show d * x * d⁻¹ * x⁻¹ = 1 by rw [← hxd]; group]; exact one_mem _)
  by_contra hx1
  obtain ⟨d', -, huniq⟩ := hL.regular x hxZ hx1 x hxZ hx1
  have h1 := huniq 1 ⟨one_mem _, by group⟩
  have h2 := huniq d ⟨hd, by rw [mul_assoc, hxd, ← mul_assoc, inv_mul_cancel, one_mul]⟩
  exact hd1 (h2.trans h1.symm)

theorem eq_one_of_mem_commutator_of_smul_eq (hA : IsBenderAction X Ω n i e) {α β γ : Ω}
    (hαβ : α ≠ β) {t : X} (ht : t * t = 1) (htα : t • α = β) {d : X}
    (hd : d ∈ ⁅stabilizer X α ⊓ stabilizer X β, Subgroup.zpowers t⁆) (hγα : γ ≠ α)
    (hγβ : γ ≠ β) (hdγ : d • γ = γ) : d = 1 := by
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer α
  have hc := hA.benderCore hQ ht (htα.trans_ne hαβ.symm)
  have hdD : d ∈ stabilizer X α ⊓ stabilizer X β := by
    rw [hA.stabilizer_inf_eq_cartan hQ ht htα]
    rw [hA.stabilizer_inf_eq_cartan hQ ht htα] at hd
    exact hc.commutator_cartan_le hd
  by_contra hd1
  obtain ⟨x, ⟨hx, hxβ⟩, hxu⟩ := hA.existsUnique_smul_eq hQ (Ne.symm hαβ) hγα
  have hdB : d ∈ borel (Q : Subgroup X) := (hA.mem_borel_iff hQ).mpr hdD.1
  have hdx : d * x * d⁻¹ ∈ (Q : Subgroup X) := (Subgroup.mem_normalizer_iff.mp hdB x).mp hx
  have hdxβ : (d * x * d⁻¹) • β = γ := by
    rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hdD.2.symm, hxβ, hdγ]
  have heq : d * x * d⁻¹ = x := hxu _ ⟨hdx, hdxβ⟩
  have hxd : x * d = d * x := by
    calc x * d = d * x * d⁻¹ * d := by rw [heq]
      _ = d * x := by group
  have hx1 := hA.eq_one_of_commute_of_mem_commutator hQ hαβ ht htα hd hd1 hx hxd
  rw [hx1, one_smul] at hxβ
  exact hγβ hxβ.symm

theorem eq_one_of_mem_stabilizer_inf_of_smul_eq (hA : IsBenderAction X Ω n i e) (hi : i ≠ 3)
    {α β γ : Ω} (hαβ : α ≠ β) {d : X} (hd : d ∈ stabilizer X α ⊓ stabilizer X β)
    (hγα : γ ≠ α) (hγβ : γ ≠ β) (hdγ : d • γ = γ) : d = 1 := by
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer α
  obtain ⟨t, ht, htα⟩ := hA.exists_involution_smul_eq hαβ
  have hL := hA.lemma32 hQ ht (htα.trans_ne hαβ.symm)
  have hd' : d ∈ ⁅stabilizer X α ⊓ stabilizer X β, Subgroup.zpowers t⁆ := by
    rw [hA.stabilizer_inf_eq_cartan hQ ht htα, ← hL.cartan_eq_commutator hi]
    rwa [hA.stabilizer_inf_eq_cartan hQ ht htα] at hd
  exact hA.eq_one_of_mem_commutator_of_smul_eq hαβ ht htα hd' hγα hγβ hdγ

end SemiRegular

section Dihedral

variable [Finite X]

private theorem odd_orderOf_mul_aux (hinv : ∀ g : X, orderOf g = 2 → ∃! ω : Ω, g • ω = ω)
    {a b : X} (ha : orderOf a = 2) (hb : orderOf b = 2) {α β : Ω} (haα : a • α = α)
    (hbβ : b • β = β) (hαβ : α ≠ β) : Odd (orderOf (a * b)) := by
  have ha2 : a * a = 1 := by rw [← sq, ← ha, pow_orderOf_eq_one]
  have hb2 : b * b = 1 := by rw [← sq, ← hb, pow_orderOf_eq_one]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  by_contra hodd
  have heven : 2 ∣ orderOf (a * b) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have hz := orderOf_pow_orderOf_div (orderOf_pos (a * b)).ne' heven
  set z := (a * b) ^ (orderOf (a * b) / 2) with hzdef
  have hz2 : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hconj : ∀ c : X, c * (a * b) * c⁻¹ = (a * b)⁻¹ → c * z = z * c := by
    intro c hc
    have h1 : c * z * c⁻¹ = z := by rw [hzdef, ← conj_pow, hc, inv_pow, ← hzdef, hzi]
    calc c * z = c * z * c⁻¹ * c := by group
      _ = z * c := by rw [h1]
  have haz : a * z = z * a := hconj a (by
    calc a * (a * b) * a⁻¹ = (a * a) * b * a⁻¹ := by group
      _ = (a * b)⁻¹ := by rw [ha2, one_mul, mul_inv_rev, hbi])
  have hbz : b * z = z * b := hconj b (by
    calc b * (a * b) * b⁻¹ = b * a := by group
      _ = (a * b)⁻¹ := by rw [mul_inv_rev, hbi, hai])
  have hfix : ∀ c : X, orderOf c = 2 → ∀ γ : Ω, c • γ = γ → c * z = z * c → z • γ = γ := by
    intro c hc γ hγ hcz
    obtain ⟨δ, -, hδ⟩ := hinv c hc
    have h1 : c • (z • γ) = z • γ := by rw [← mul_smul, hcz, mul_smul, hγ]
    exact (hδ _ h1).trans (hδ γ hγ).symm
  obtain ⟨δ, -, hδ⟩ := hinv z hz
  exact hαβ ((hδ α (hfix a ha α haα haz)).trans (hδ β (hfix b hb β hbβ hbz)).symm)

theorem odd_orderOf_mul (hA : IsBenderAction X Ω n i e) {a b : X} (ha : orderOf a = 2)
    (hb : orderOf b = 2) {α β : Ω} (haα : a • α = α) (hbβ : b • β = β) (hαβ : α ≠ β) :
    Odd (orderOf (a * b)) :=
  odd_orderOf_mul_aux (fun _ hg => hA.existsUnique_fixed hg) ha hb haα hbβ hαβ

theorem false_of_commute (hA : IsBenderAction X Ω n i e) {s a b : X} (hs : orderOf s = 2)
    (ha : orderOf a = 2) (hb : orderOf b = 2) {α β : Ω} (haα : a • α = α) (hbβ : b • β = β)
    (hαβ : α ≠ β) (hsa : s * a = a * s) (hsb : s * b = b * s) : False := by
  have hfix : ∀ c : X, orderOf c = 2 → ∀ γ : Ω, c • γ = γ → s * c = c * s → s • γ = γ := by
    intro c hc γ hγ hsc
    obtain ⟨δ, -, hδ⟩ := hA.existsUnique_fixed hc
    have h1 : c • (s • γ) = s • γ := by rw [← mul_smul, ← hsc, mul_smul, hγ]
    exact (hδ _ h1).trans (hδ γ hγ).symm
  obtain ⟨δ, -, hδ⟩ := hA.existsUnique_fixed hs
  exact hαβ ((hδ α (hfix a ha α haα hsa)).trans (hδ β (hfix b hb β hbβ hsb)).symm)

theorem eq_one_of_mul_mul_inv_eq_inv (hA : IsBenderAction X Ω n i e) {α : Ω} {x s : X}
    (hxα : x • α = α) (hx : Odd (orderOf x)) (hsα : s • α = α) (hs : orderOf s = 2)
    (hsx : s * x * s⁻¹ = x⁻¹) : x = 1 := by
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer α
  obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
  have hsQ : s ∈ (Q : Subgroup X) :=
    rootCenter_le _ (hc.center_of_involution s ((hA.mem_borel_iff hQ).mpr hsα) hs)
  have hxB : x ∈ borel (Q : Subgroup X) := (hA.mem_borel_iff hQ).mpr hxα
  have h1 : x * s⁻¹ * x⁻¹ ∈ (Q : Subgroup X) :=
    (Subgroup.mem_normalizer_iff.mp hxB s⁻¹).mp (inv_mem hsQ)
  have h2 : x * x ∈ (Q : Subgroup X) := by
    have h3 : s * (x * s⁻¹ * x⁻¹) = (x * x)⁻¹ := by
      calc s * (x * s⁻¹ * x⁻¹) = (s * x * s⁻¹) * x⁻¹ := by group
        _ = (x * x)⁻¹ := by rw [hsx, mul_inv_rev]
    have h4 := mul_mem hsQ h1
    rw [h3] at h4
    exact inv_mem_iff.mp h4
  obtain ⟨k, hk⟩ := exists_sq_eq_of_odd_orderOf hx
  have hxQ : x ∈ (Q : Subgroup X) := by
    have h5 : x = (x * x) ^ k := by rw [(Commute.refl x).mul_pow, hk]
    rw [h5]
    exact pow_mem h2 k
  obtain ⟨m, hm⟩ := Q.isPGroup' ⟨x, hxQ⟩
  have hdvd : orderOf x ∣ 2 ^ m :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hm)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hx.coprime_two_right.pow_right m) hdvd)

theorem isSolvable_stabilizer_pair (hA : IsBenderAction X Ω n i e) (α β : Ω) :
    Group.IsSolvable ↥(stabilizer X ({α, β} : Set Ω)) := by
  classical
  by_cases hαβ : α = β
  · subst hαβ
    obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer α
    obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
    have hset : ({α, α} : Set Ω) = {α} := Set.pair_eq_singleton α
    rw [hset, stabilizer_singleton, hA.stabilizer_eq_borel hQ]
    exact hc.isSolvable_borel
  · set S := stabilizer X ({α, β} : Set Ω)
    have hD : stabilizer X α ⊓ stabilizer X β ≤ S := by
      intro x hx
      rw [mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton, hx.1, hx.2]
    have : IsCyclic ↥(stabilizer X α ⊓ stabilizer X β) := hA.isCyclic_stabilizer_inf hαβ
    have hsD : Group.IsSolvable ↥(stabilizer X α ⊓ stabilizer X β) :=
      Group.isSolvable_of_comm fun a b => IsCyclic.commGroup.mul_comm a b
    have : Finite ↥({α, β} : Set Ω) := Set.toFinite _
    have hcard : Nat.card (Equiv.Perm ↥({α, β} : Set Ω)) = 2 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Set.card_insert _ (by simpa using hαβ),
        Set.card_singleton]
      rfl
    have : Fact (Nat.Prime (Nat.card (Equiv.Perm ↥({α, β} : Set Ω)))) := ⟨hcard ▸ Nat.prime_two⟩
    have : IsCyclic (Equiv.Perm ↥({α, β} : Set Ω)) := isCyclic_of_prime_card rfl
    have hsP : Group.IsSolvable (Equiv.Perm ↥({α, β} : Set Ω)) :=
      Group.isSolvable_of_comm fun a b => IsCyclic.commGroup.mul_comm a b
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hD)
      (MulAction.toPermHom ↥S ↥({α, β} : Set Ω)) fun x hx => ?_
    have hx' : ∀ y : ↥({α, β} : Set Ω), x • y = y := fun y => by
      have := congrArg (fun π : Equiv.Perm ↥({α, β} : Set Ω) => π y) hx
      simpa using this
    have h1 := congrArg Subtype.val (hx' ⟨α, by simp⟩)
    have h2 := congrArg Subtype.val (hx' ⟨β, by simp⟩)
    exact ⟨⟨x, h1, h2⟩, rfl⟩

end Dihedral

section Sylow

variable [Finite X]

theorem le_sylow_of_isPGroup (hA : IsBenderAction X Ω n i e) {α : Ω} {Q : Sylow 2 X}
    (hQ : (Q : Subgroup X) ≤ stabilizer X α) {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPα : P ≤ stabilizer X α) : P ≤ Q := by
  have hPN : P ≤ Subgroup.normalizer ((Q : Subgroup X) : Set X) :=
    hPα.trans (hA.stabilizer_eq_borel hQ).le
  have h := Q.is_maximal' (hP.to_sup_of_normal_right' Q.isPGroup' hPN) le_sup_right
  exact le_sup_left.trans h.le

theorem exists_eq_stabilizer (hA : IsBenderAction X Ω n i e) {Y : Subgroup X}
    (hY : Y.index = (2 ^ n) ^ i + 1) : ∃ ω : Ω, Y = stabilizer X ω := by
  have hB : IsBenderAction X (X ⧸ Y) n i e := ⟨hA.benderType, inferInstance, hY⟩
  obtain ⟨Q, hQ⟩ := hB.exists_sylow_le_stabilizer ((1 : X) : X ⧸ Y)
  have h1 := hB.stabilizer_eq_borel hQ
  rw [MulAction.stabilizer_quotient] at h1
  obtain ⟨ω, hω, -⟩ := hA.existsUnique_le_stabilizer Q
  exact ⟨ω, h1.trans (hA.stabilizer_eq_borel hω).symm⟩

end Sylow

end IsBenderAction

end CFSG.Holt.H78
