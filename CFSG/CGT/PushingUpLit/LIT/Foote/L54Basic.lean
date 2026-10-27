module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L54Aux
public import CFSG.CGT.PushingUpLit.LIT.Foote.Transport
public import CFSG.CGT.PushingUpLit.LIT.Foote.L53

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Three (M J : Subgroup G) : Prop :=
  ∃ a ∈ M, ∃ b ∈ M, rightConjugate J a ≠ J ∧ rightConjugate J b ≠ J ∧
    rightConjugate J a ≠ rightConjugate J b

theorem Three.of_not_twoOrbit {M J : Subgroup G} (c : CE G M J) (h : ¬ TwoOrbit M J) :
    Three M J := by
  obtain ⟨a, ha, hna⟩ := c.exists_conj_ne
  by_contra hn
  apply h
  refine ⟨rightConjugate J a, hna, fun m hm => ?_⟩
  by_contra hcon
  push Not at hcon
  exact hn ⟨a, ha, m, hm, hna, hcon.1, fun h' => hcon.2 h'.symm⟩

namespace Three

variable {M J : Subgroup G}

omit [Finite G] in
theorem exists_notin (h : Three M J) (X Y : Subgroup G) :
    ∃ c ∈ M, rightConjugate J c ≠ X ∧ rightConjugate J c ≠ Y := by
  obtain ⟨a, ha, b, hb, hJa, hJb, hab⟩ := h
  by_contra hcon
  push Not at hcon
  have h1 : J ≠ X → J = Y := fun h => by
    have := hcon 1 M.one_mem (by rwa [rightConjugate_one])
    rwa [rightConjugate_one] at this
  have h2 : rightConjugate J a ≠ X → rightConjugate J a = Y := hcon a ha
  have h3 : rightConjugate J b ≠ X → rightConjugate J b = Y := hcon b hb
  by_cases hX1 : J = X
  · by_cases hX2 : rightConjugate J a = X
    · exact hJa (hX2.trans hX1.symm)
    · by_cases hX3 : rightConjugate J b = X
      · exact hJb (hX3.trans hX1.symm)
      · exact hab ((h2 hX2).trans (h3 hX3).symm)
  · have e1 := h1 hX1
    by_cases hX2 : rightConjugate J a = X
    · by_cases hX3 : rightConjugate J b = X
      · exact hab (hX2.trans hX3.symm)
      · exact hJb ((h3 hX3).trans e1.symm)
    · exact hJa ((h2 hX2).trans e1.symm)

omit [Finite G] in
theorem exists_notin_g (h : Three M J) (g : G) (X Y : Subgroup G) :
    ∃ c ∈ M, rightConjugate J (c * g) ≠ X ∧ rightConjugate J (c * g) ≠ Y := by
  obtain ⟨c, hc, hX, hY⟩ := h.exists_notin (rightConjugate X g⁻¹) (rightConjugate Y g⁻¹)
  refine ⟨c, hc, fun e => hX ?_, fun e => hY ?_⟩
  · rw [← e, rightConjugate_mul, mul_inv_cancel_right]
  · rw [← e, rightConjugate_mul, mul_inv_cancel_right]

omit [Finite G] in
theorem transport (h : Three M J) (g : G) : Three (rightConjugate M g) (rightConjugate J g) := by
  obtain ⟨a, ha, b, hb, hJa, hJb, hab⟩ := h
  have hmem : ∀ m ∈ M, g⁻¹ * m * g ∈ rightConjugate M g := fun m hm => by
    rw [mem_rightConjugate_iff]
    have e : g * (g⁻¹ * m * g) * g⁻¹ = m := by group
    rw [e]
    exact hm
  have key : ∀ m : G, rightConjugate (rightConjugate J g) (g⁻¹ * m * g) =
      rightConjugate (rightConjugate J m) g := fun m => by
    rw [rightConjugate_mul, rightConjugate_mul]
    congr 1
    group
  refine ⟨g⁻¹ * a * g, hmem a ha, g⁻¹ * b * g, hmem b hb, ?_, ?_, ?_⟩
  · rw [key]
    exact fun e => hJa (rightConjugate_inj'.1 e)
  · rw [key]
    exact fun e => hJb (rightConjugate_inj'.1 e)
  · rw [key, key]
    exact fun e => hab (rightConjugate_inj'.1 e)

end Three

omit [Finite G] in
theorem twoElem_of_mul_self {w : G} (h : w * w = 1) : ∃ n : ℕ, w ^ 2 ^ n = 1 :=
  ⟨1, by simpa [pow_two] using h⟩

omit [Finite G] in
theorem conj_mem_rightConjugate {M : Subgroup G} {m : G} (hm : m ∈ M) (g : G) :
    g⁻¹ * m * g ∈ rightConjugate M g := by
  rw [mem_rightConjugate_iff]
  have e : g * (g⁻¹ * m * g) * g⁻¹ = m := by group
  rw [e]
  exact hm

omit [Finite G] in
theorem rightConjugate_conj_g (J : Subgroup G) (m g : G) :
    rightConjugate (rightConjugate J g) (g⁻¹ * m * g) = rightConjugate J (m * g) := by
  rw [rightConjugate_mul]
  congr 1
  group

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem centralizer_le_of_centralizes {w b : G} (hw1 : w ≠ 1) (hw2 : ∃ n : ℕ, w ^ 2 ^ n = 1)
    (hb : b ∈ M) (hcomm : ∀ x ∈ rightConjugate J b, x * w = w * x) :
    Subgroup.centralizer ({w} : Set G) ≤ M := by
  have hA := L54.isPGroup_zpowers hw2
  have hA1 : Subgroup.zpowers w ≠ ⊥ := fun h => hw1 (Subgroup.zpowers_eq_bot.1 h)
  have hN : rightConjugate J b ≤ Subgroup.normalizer ((Subgroup.zpowers w : Subgroup G) : Set G) :=
    fun y hy => mem_normalizer_zpowers (hcomm y hy)
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff] at hk
  exact c.normalizer_le hA hA1 hb hN (mem_normalizer_zpowers hk)

theorem kp {w b h : G} (hw1 : w ≠ 1) (hw2 : ∃ n : ℕ, w ^ 2 ^ n = 1) (hb : b ∈ M)
    (hcb : ∀ x ∈ rightConjugate J b, x * w = w * x)
    (hch : ∀ x ∈ rightConjugate J h, x * w = w * x) : h ∈ M := by
  have hC := c.centralizer_le_of_centralizes hw1 hw2 hb hcb
  apply c.mem_of_conj_le
  intro x hx
  apply hC
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hch x hx

theorem kp_g {w b c' g : G} (hw1 : w ≠ 1) (hw2 : ∃ n : ℕ, w ^ 2 ^ n = 1) (hb : b ∈ M)
    (hc' : c' ∈ M) (hcb : ∀ x ∈ rightConjugate J b, x * w = w * x)
    (hch : ∀ x ∈ rightConjugate J (c' * g), x * w = w * x) : g ∈ M := by
  have := c.kp hw1 hw2 hb hcb hch
  simpa using M.mul_mem (M.inv_mem hc') this

theorem comm_conj {a b : G} (ha : a ∈ M) (hb : b ∈ M)
    (hne : rightConjugate J a ≠ rightConjugate J b) {x y : G} (hx : x ∈ rightConjugate J a)
    (hy : y ∈ rightConjugate J b) : x * y = y * x := by
  have hcomm := c.commutator_conj_conj_eq_bot ha hb hne
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hx
  exact (Subgroup.mem_centralizer_iff.1 this y hy).symm

theorem comm_J {a : G} (ha : a ∈ M) (hne : rightConjugate J a ≠ J) {x y : G} (hx : x ∈ J)
    (hy : y ∈ rightConjugate J a) : x * y = y * x := by
  have hcomm := c.commutator_conj_eq_bot ha hne
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hx
  exact (Subgroup.mem_centralizer_iff.1 this y hy).symm

theorem comm_conj_g (g : G) {a b : G} (ha : a ∈ M) (hb : b ∈ M)
    (hne : rightConjugate J (a * g) ≠ rightConjugate J (b * g)) {x y : G}
    (hx : x ∈ rightConjugate J (a * g)) (hy : y ∈ rightConjugate J (b * g)) : x * y = y * x := by
  have hmem : ∀ m ∈ M, g⁻¹ * m * g ∈ rightConjugate M g := fun m hm => conj_mem_rightConjugate hm g
  have key : ∀ m : G, rightConjugate (rightConjugate J g) (g⁻¹ * m * g) =
      rightConjugate J (m * g) := fun m => rightConjugate_conj_g J m g
  refine (c.transport g).comm_conj (hmem a ha) (hmem b hb) ?_ ?_ ?_
  · rw [key, key]
    exact hne
  · rw [key]
    exact hx
  · rw [key]
    exact hy

theorem centralizer_le_of_centralizes_g (g : G) {w b : G} (hw1 : w ≠ 1)
    (hw2 : ∃ n : ℕ, w ^ 2 ^ n = 1) (hb : b ∈ M)
    (hcomm : ∀ x ∈ rightConjugate J (b * g), x * w = w * x) :
    Subgroup.centralizer ({w} : Set G) ≤ rightConjugate M g := by
  refine (c.transport g).centralizer_le_of_centralizes hw1 hw2 (conj_mem_rightConjugate hb g) ?_
  intro x hx
  rw [rightConjugate_conj_g] at hx
  exact hcomm x hx

theorem fourGroup_normalizes_g (hA : FooteTheoremA) {z₀ : G} (hz₀ : ZData J z₀) {g : G}
    (hg : g ∉ M) {F : Subgroup G} (hFM : F ≤ rightConjugate M g)
    (hF2 : CFSG.Open.IsElemAbelian 2 F) (hF4 : Nat.card F = 4)
    (hC : ∀ w ∈ F, w ≠ 1 → Subgroup.centralizer ({w} : Set G) ≤ M) :
    F ≤ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G) := by
  refine (c.transport g).lemma_5_3 hA (hz₀.transport g) hFM hF2 hF4 (g := g⁻¹) ?_ ?_
  · intro hmem
    rw [mem_rightConjugate_iff] at hmem
    apply hg
    have : g * g⁻¹ * g⁻¹⁻¹ = g := by group
    simpa using M.inv_mem (by simpa using hmem)
  · intro w hw hw1
    rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
    exact hC w hw hw1

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
