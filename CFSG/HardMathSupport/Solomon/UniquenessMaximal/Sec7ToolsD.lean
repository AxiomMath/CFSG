module

public import CFSG.LocalAnalysis.GLTheoremB.UniqDefs
import CFSG.RankThree.PartTwo.KFacts.L34Aut
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section CommutatorCommutator

variable {G : Type*} [Group G] {A C : Subgroup G}

theorem conj_mem_commutator_of_mem_left {z : G} (hz : z ∈ A) {x : G} (hx : x ∈ ⁅A, C⁆) :
    z * x * z⁻¹ ∈ ⁅A, C⁆ := by
  rw [Subgroup.commutator_def] at hx ⊢
  refine Subgroup.closure_induction
    (p := fun x _ => z * x * z⁻¹ ∈ Subgroup.closure {g | ∃ g₁ ∈ A, ∃ g₂ ∈ C, ⁅g₁, g₂⁆ = g})
    (fun g hg => ?_) (by simp [one_mem]) (fun u v _ _ hu hv => ?_) (fun u _ hu => ?_) hx
  · obtain ⟨a, ha, c, hc, rfl⟩ := hg
    have h1 : z * ⁅a, c⁆ * z⁻¹ = ⁅z * a, c⁆ * ⁅z, c⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact mul_mem (Subgroup.subset_closure ⟨z * a, mul_mem hz ha, c, hc, rfl⟩)
      (inv_mem (Subgroup.subset_closure ⟨z, hz, c, hc, rfl⟩))
  · have : z * (u * v) * z⁻¹ = (z * u * z⁻¹) * (z * v * z⁻¹) := by group
    rw [this]; exact mul_mem hu hv
  · have : z * u⁻¹ * z⁻¹ = (z * u * z⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem hu

theorem conj_mem_commutator_of_mem_right (hC : C ≤ Subgroup.normalizer (A : Set G)) {g : G}
    (hg : g ∈ C) {x : G} (hx : x ∈ ⁅A, C⁆) : g * x * g⁻¹ ∈ ⁅A, C⁆ := by
  rw [Subgroup.commutator_def] at hx ⊢
  refine Subgroup.closure_induction
    (p := fun x _ => g * x * g⁻¹ ∈ Subgroup.closure {g | ∃ g₁ ∈ A, ∃ g₂ ∈ C, ⁅g₁, g₂⁆ = g})
    (fun y hy => ?_) (by simp [one_mem]) (fun u v _ _ hu hv => ?_) (fun u _ hu => ?_) hx
  · obtain ⟨a, ha, c, hc, rfl⟩ := hy
    have h1 : g * ⁅a, c⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * c * g⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact Subgroup.subset_closure ⟨g * a * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hC hg) a).mp ha,
      g * c * g⁻¹, mul_mem (mul_mem hg hc) (inv_mem hg), rfl⟩
  · have : g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
    rw [this]; exact mul_mem hu hv
  · have : g * u⁻¹ * g⁻¹ = (g * u * g⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem hu

theorem commutator_le_left (hC : C ≤ Subgroup.normalizer (A : Set G)) : ⁅A, C⁆ ≤ A := by
  rw [Subgroup.commutator_def, Subgroup.closure_le]
  rintro _ ⟨a, ha, c, hc, rfl⟩
  have h1 : c * a⁻¹ * c⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hC hc) a⁻¹).mp (inv_mem ha)
  have : ⁅a, c⁆ = a * (c * a⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
  rw [this]
  exact mul_mem ha h1

theorem commutator_mem_commutator_commutator [Finite G] (hA3 : ¬ 3 ∣ Nat.card A)
    (hC : C ≤ Subgroup.normalizer (A : Set G)) {c : G} (hc : c ∈ C)
    (hc3 : IsPGroup 3 (Subgroup.zpowers c)) {a : G} (ha : a ∈ A) :
    ⁅a, c⁆ ∈ ⁅⁅A, C⁆, C⁆ := by
  classical
  have := Fintype.ofFinite G
  set X : Subgroup G := ⁅A, C⁆ with hX
  have hXA : X ≤ A := commutator_le_left hC
  have hX3 : ¬ 3 ∣ Nat.card X := fun h => hA3 (h.trans (Subgroup.card_dvd_of_le hXA))
  obtain ⟨k, hk⟩ := hc3.exists_card_eq
  rw [Nat.card_zpowers] at hk
  have hmem : ∀ w : G, a⁻¹ * w ∈ X → a⁻¹ * (c * w * c⁻¹) ∈ X := by
    intro w hw
    have h1 : a⁻¹ * (c * w * c⁻¹) = ⁅a⁻¹, c⁆ * (c * (a⁻¹ * w) * c⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact mul_mem (Subgroup.commutator_mem_commutator (inv_mem ha) hc)
      (conj_mem_commutator_of_mem_right hC hc hw)
  let α := {w : G // a⁻¹ * w ∈ X}
  let f : Function.End α := fun w => ⟨c * w.1 * c⁻¹, hmem w.1 w.2⟩
  have hpow : ∀ n : ℕ, ∀ y : α, ((f ^ n) y).1 = c ^ n * y.1 * (c ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro y; show y.1 = _; simp
    | succ n ih =>
      intro y
      rw [pow_succ]
      show ((f ^ n) (f y)).1 = _
      rw [ih (f y)]
      show c ^ n * (c * y.1 * c⁻¹) * (c ^ n)⁻¹ = c ^ (n + 1) * y.1 * (c ^ (n + 1))⁻¹
      group
  have hf : f ^ 3 ^ k = 1 := by
    funext y
    apply Subtype.ext
    rw [hpow, ← hk, pow_orderOf_eq_one]
    show _ = y.1
    simp
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := k) hf
  have hcard : Fintype.card α = Nat.card X := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft a⁻¹) (fun w => Iff.rfl))
  have hpos : 0 < Fintype.card f.fixedPoints := by
    rcases Nat.eq_zero_or_pos (Fintype.card f.fixedPoints) with h0 | h0
    · exfalso
      apply hX3
      rw [← hcard]
      rw [h0] at hmod
      exact (Nat.modEq_zero_iff_dvd).1 hmod
    · exact h0
  obtain ⟨⟨⟨z, hzX⟩, hz⟩⟩ := Fintype.card_pos_iff.1 hpos
  have hzc : c * z * c⁻¹ = z := congrArg Subtype.val hz
  have hzA : z ∈ A := by
    have : z = a * (a⁻¹ * z) := by group
    rw [this]; exact mul_mem ha (hXA hzX)
  have hz' : z⁻¹ * c * z = c := by
    have : c * z = z * c := (mul_inv_eq_iff_eq_mul.mp hzc)
    calc z⁻¹ * c * z = z⁻¹ * (c * z) := by group
      _ = c := by rw [this]; group
  have hy : z * (a⁻¹ * z)⁻¹ * z⁻¹ ∈ X :=
    conj_mem_commutator_of_mem_left hzA (inv_mem hzX)
  have h2 : ⁅a, c⁆ = ⁅z * (a⁻¹ * z)⁻¹ * z⁻¹, c⁆ := by
    simp only [commutatorElement_def]
    have h3 : z * (a⁻¹ * z)⁻¹ * z⁻¹ * c * (z * (a⁻¹ * z)⁻¹ * z⁻¹)⁻¹ * c⁻¹ =
        z * (a⁻¹ * z)⁻¹ * (z⁻¹ * c * z) * (a⁻¹ * z) * z⁻¹ * c⁻¹ := by group
    rw [h3, hz']
    group
  rw [h2]
  exact Subgroup.commutator_mem_commutator hy hc

theorem commutator_commutator_eq {G : Type*} [Group G] [Finite G] {A C : Subgroup G}
    (hA3 : ¬ 3 ∣ Nat.card A) (hC : C ≤ Subgroup.normalizer (A : Set G))
    (hgen : C = Subgroup.closure {c : G | c ∈ C ∧ IsPGroup 3 (Subgroup.zpowers c)}) :
    ⁅⁅A, C⁆, C⁆ = ⁅A, C⁆ := by
  apply le_antisymm (Subgroup.commutator_mono (commutator_le_left hC) le_rfl)
  have hall : ∀ c ∈ C, ∀ a ∈ A, ⁅a, c⁆ ∈ ⁅⁅A, C⁆, C⁆ := by
    intro c hc
    have hc' : c ∈ Subgroup.closure {c : G | c ∈ C ∧ IsPGroup 3 (Subgroup.zpowers c)} := by
      rw [← hgen]; exact hc
    refine Subgroup.closure_induction
      (p := fun c _ => c ∈ C ∧ ∀ a ∈ A, ⁅a, c⁆ ∈ ⁅⁅A, C⁆, C⁆) (fun c hc => ?_) ?_ ?_ ?_ hc' |>.2
    · exact ⟨hc.1, fun a ha => commutator_mem_commutator_commutator hA3 hC hc.1 hc.2 ha⟩
    · exact ⟨one_mem _, fun a _ => by simp [commutatorElement_def, one_mem]⟩
    · rintro c₁ c₂ _ _ ⟨hc₁, h₁⟩ ⟨hc₂, h₂⟩
      refine ⟨mul_mem hc₁ hc₂, fun a ha => ?_⟩
      have hb : c₂ * a * c₂⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hC hc₂) a).mp ha
      have : ⁅a, c₁ * c₂⁆ = ⁅a, c₂⁆ * ⁅c₂ * a * c₂⁻¹, c₁⁆ := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact mul_mem (h₂ a ha) (h₁ _ hb)
    · rintro c _ ⟨hc, h⟩
      refine ⟨inv_mem hc, fun a ha => ?_⟩
      have hb : c⁻¹ * a * c ∈ A := by
        have := (Subgroup.mem_normalizer_iff.mp (hC (inv_mem hc)) a).mp ha
        simpa using this
      have : ⁅a, c⁻¹⁆ = ⁅c⁻¹ * a * c, c⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact inv_mem (h _ hb)
  rw [Subgroup.commutator_def, Subgroup.closure_le]
  rintro _ ⟨a, ha, c, hc, rfl⟩
  exact hall c hc a ha

end CommutatorCommutator

section L34

theorem eq_bot_of_two_group_normalized_by_nine {X : Type} [Group X] [Finite X] (h : IsLThreeFour X)
    {E S : Subgroup X} (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9) (hS : IsPGroup 2 S)
    (hES : E ≤ Subgroup.normalizer (S : Set X)) : S = ⊥ := by
  have _ := hE
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  have e' : X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F)
  let P := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F
  let S' : Subgroup P := S.map e'.toMonoidHom
  let E' : Subgroup P := E.map e'.toMonoidHom
  let X' : Subgroup (MulAut P) := S'.map (MulAut.conj : P →* MulAut P)
  have hE' : Nat.card E' = 9 := by
    rw [← hEc]; exact Subgroup.card_map_of_injective e'.injective
  have hS' : IsPGroup 2 S' := hS.map _
  have hX' : ¬ 3 ∣ Nat.card X' := by
    obtain ⟨n, hn⟩ := (hS'.map (MulAut.conj : P →* MulAut P)).exists_card_eq
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hSn : ∀ y ∈ E', y ∈ Subgroup.normalizer (S' : Set P) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro g
    obtain ⟨t, rfl⟩ := e'.surjective g
    have h1 : e' y * e' t * (e' y)⁻¹ = e' (y * t * y⁻¹) := by simp
    show e' t ∈ S' ↔ e' y * e' t * (e' y)⁻¹ ∈ S'
    rw [h1]
    exact (Subgroup.mem_map_iff_mem e'.injective).trans
      (((Subgroup.mem_normalizer_iff.mp (hES hy) t)).trans
        (Subgroup.mem_map_iff_mem e'.injective).symm)
  have key : ∀ p ∈ Subgroup.normalizer (S' : Set P), ∀ g ∈ X',
      MulAut.conj p * g * (MulAut.conj p)⁻¹ ∈ X' := by
    intro p hp g hg
    obtain ⟨s, hs, rfl⟩ := hg
    refine ⟨p * s * p⁻¹, (Subgroup.mem_normalizer_iff.mp hp s).mp hs, ?_⟩
    simp
  have hEX : ∀ x ∈ E', MulAut.conj x ∈ Subgroup.normalizer (X' : Set (MulAut P)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨key x (hSn x hx) g, fun hg => ?_⟩
    have := key x⁻¹ (inv_mem (hSn x hx)) _ hg
    simpa [mul_assoc] using this
  have hbot := CFSG.RankThree.PartTwo.KFacts.L34.comap_conj_eq_bot hcard hE' hX' hEX
  have hS'bot : S' = ⊥ := by
    rw [← Subgroup.comap_map_eq_self_of_injective
      (CFSG.RankThree.PartTwo.KFacts.L34.conj_injective hcard) S']
    exact hbot
  exact (Subgroup.map_eq_bot_iff_of_injective S e'.injective).1 hS'bot

end L34

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
