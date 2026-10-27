module

public import CFSG.CGT.PushingUpLit.LIT.Foote.Orbit
public import CFSG.CGT.PushingUpLit.LIT.Foote.L52

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

@[expose] def zConj (M : Subgroup G) (z₀ : G) : Set G := {z | ∃ m ∈ M, z = m⁻¹ * z₀ * m}

@[expose] def zSub (M : Subgroup G) (z₀ : G) : Subgroup G := Subgroup.closure (zConj M z₀)

structure ZData (J : Subgroup G) (z₀ : G) : Prop where
  mem : z₀ ∈ J
  central : ∀ j ∈ J, z₀ * j = j * z₀
  sq : z₀ * z₀ = 1
  ne_one : z₀ ≠ 1

namespace CE

variable {M J : Subgroup G} {z₀ : G}

theorem zgen_commute (c : CE G M J) (h : ZData J z₀) {m m' : G} (hm : m ∈ M) (hm' : m' ∈ M)
    {y : G} (hy : y ∈ rightConjugate J m) : (m'⁻¹ * z₀ * m') * y = y * (m'⁻¹ * z₀ * m') := by
  by_cases hne : rightConjugate J m = rightConjugate J m'
  · rw [hne, mem_rightConjugate_iff] at hy
    have h1 := h.central _ hy
    calc m'⁻¹ * z₀ * m' * y = m'⁻¹ * (z₀ * (m' * y * m'⁻¹)) * m' := by group
      _ = m'⁻¹ * ((m' * y * m'⁻¹) * z₀) * m' := by rw [h1]
      _ = y * (m'⁻¹ * z₀ * m') := by group
  · have hmem' : m'⁻¹ * z₀ * m' ∈ rightConjugate J m' := by
      rw [mem_rightConjugate_iff]
      have e : m' * (m'⁻¹ * z₀ * m') * m'⁻¹ = z₀ := by group
      rw [e]
      exact h.mem
    have hcomm := c.commutator_conj_conj_eq_bot hm hm' hne
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hy
    exact Subgroup.mem_centralizer_iff.1 this _ hmem'

theorem zSub_centralizes (c : CE G M J) (h : ZData J z₀) {z : G} (hz : z ∈ zSub M z₀) {m : G}
    (hm : m ∈ M) {y : G} (hy : y ∈ rightConjugate J m) : z * y = y * z := by
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨m', hm', rfl⟩ := hz
    exact c.zgen_commute h hm hm' hy
  | one => simp
  | mul a b _ _ ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | inv a _ ha =>
    have hc : Commute a y := ha
    exact hc.inv_left.eq

theorem zSub_comm (c : CE G M J) (h : ZData J z₀) {z z' : G} (hz : z ∈ zSub M z₀)
    (hz' : z' ∈ zSub M z₀) : z * z' = z' * z := by
  have hgen : ∀ s ∈ zConj M z₀, z * s = s * z := by
    rintro _ ⟨m', hm', rfl⟩
    refine c.zSub_centralizes h hz hm' ?_
    rw [mem_rightConjugate_iff]
    have e : m' * (m'⁻¹ * z₀ * m') * m'⁻¹ = z₀ := by group
    rw [e]
    exact h.mem
  induction hz' using Subgroup.closure_induction with
  | mem s hs => exact hgen s hs
  | one => simp
  | mul a b _ _ ha hb => rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]
  | inv a _ ha =>
    have hc : Commute z a := ha
    exact hc.inv_right.eq

theorem zSub_sq (c : CE G M J) (h : ZData J z₀) {z : G} (hz : z ∈ zSub M z₀) : z * z = 1 := by
  induction hz using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨m, hm, rfl⟩ := hs
    calc m⁻¹ * z₀ * m * (m⁻¹ * z₀ * m) = m⁻¹ * (z₀ * z₀) * m := by group
      _ = 1 := by rw [h.sq]; group
  | one => simp
  | mul a b ha hb ha2 hb2 =>
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [c.zSub_comm h hb ha]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  | inv a _ ha =>
    calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
      _ = 1 := by rw [ha]; simp

theorem isPGroup_zSub (c : CE G M J) (h : ZData J z₀) : IsPGroup 2 (zSub M z₀) := fun g =>
  ⟨1, Subtype.ext (by simpa [pow_two] using c.zSub_sq h g.2)⟩

omit [Finite G] in
theorem zSub_conj {k z : G} (hk : k ∈ M) (hz : z ∈ zSub M z₀) : k * z * k⁻¹ ∈ zSub M z₀ := by
  induction hz using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨m, hm, rfl⟩ := hs
    apply Subgroup.subset_closure
    refine ⟨m * k⁻¹, M.mul_mem hm (M.inv_mem hk), ?_⟩
    group
  | one => simp
  | mul a b _ _ ha hb =>
    have e : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have e : k * a⁻¹ * k⁻¹ = (k * a * k⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ha

omit [Finite G] in
theorem le_normalizer_zSub : M ≤ Subgroup.normalizer (zSub M z₀ : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hh => zSub_conj hk hh, fun hh => ?_⟩
  have := zSub_conj (M.inv_mem hk) hh
  simpa [mul_assoc] using this

omit [Finite G] in
theorem z₀_mem : z₀ ∈ zSub M z₀ := Subgroup.subset_closure ⟨1, M.one_mem, by simp⟩

omit [Finite G] in
theorem zSub_ne_bot (h : ZData J z₀) : zSub M z₀ ≠ ⊥ := fun hb =>
  h.ne_one (Subgroup.mem_bot.1 (hb ▸ z₀_mem))

omit [Finite G] in
theorem isPGroup_zpowers_of_sq {z : G} (h2 : z * z = 1) (h1 : z ≠ 1) :
    IsPGroup 2 (Subgroup.zpowers z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact h2) h1
  exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho]; simp)

theorem centralizer_le (c : CE G M J) (h : ZData J z₀) {z : G} (hz : z ∈ zSub M z₀) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) ≤ M := by
  have hz2 := c.zSub_sq h hz
  have hA := isPGroup_zpowers_of_sq hz2 hz1
  have hA1 : Subgroup.zpowers z ≠ ⊥ := fun hb => hz1 (Subgroup.zpowers_eq_bot.1 hb)
  have hJ : rightConjugate J 1 ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    intro y hy
    exact mem_normalizer_zpowers (c.zSub_centralizes h hz M.one_mem hy).symm
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff] at hk
  exact c.normalizer_le hA hA1 M.one_mem hJ (mem_normalizer_zpowers hk)

theorem isPGroup_zg (c : CE G M J) (h : ZData J z₀) (g : G) :
    IsPGroup 2 (rightConjugate (zSub M z₀) g) :=
  (c.isPGroup_zSub h).map _

omit [Finite G] in
theorem normalizer_zg (g : G) :
    rightConjugate M g ≤
      Subgroup.normalizer ((rightConjugate (zSub M z₀) g : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_rightConjugate_iff] at hx
  exact mem_normalizer_rightConjugate.2 (le_normalizer_zSub hx)

theorem centralizer_le_zg (c : CE G M J) (h : ZData J z₀) {g z : G}
    (hz : z ∈ rightConjugate (zSub M z₀) g) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) ≤ rightConjugate M g := by
  rw [mem_rightConjugate_iff] at hz
  have hz1' : g * z * g⁻¹ ≠ 1 := fun h' => hz1 (by simpa using h')
  intro w hw
  rw [Subgroup.mem_centralizer_singleton_iff] at hw
  rw [mem_rightConjugate_iff]
  apply c.centralizer_le h hz hz1'
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * w * g⁻¹ * (g * z * g⁻¹) = g * (w * z) * g⁻¹ := by group
    _ = g * (z * w) * g⁻¹ := by rw [hw]
    _ = g * z * g⁻¹ * (g * w * g⁻¹) := by group

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
