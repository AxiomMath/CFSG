module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Subgroup.Simple
public import CFSG.Certificates.Kernel.OrbRow.Tight
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.KC.OrbRow.CentLGrp

open Subgroup

theorem prod_le_card_chain {α : Type*} [Finite α] (b : ℕ → α) (L : ℕ)
    (G : ℕ → Subgroup (Equiv.Perm α)) (k : ℕ → ℕ)
    (hfix : ∀ i ≤ L, ∀ g ∈ G i, ∀ t < i, g (b t) = b t) (hdec : ∀ i < L, G (i + 1) ≤ G i)
    (horb : ∀ i < L, ∃ s : Finset α, s.card = k i ∧ ∀ y ∈ s, ∃ g ∈ G i, g (b i) = y) :
    ∀ i ≤ L, ∏ t ∈ Finset.Ico i L, k t ≤ Nat.card (G i) := by
  suffices h : ∀ d i, i + d = L → ∏ t ∈ Finset.Ico i L, k t ≤ Nat.card (G i) from
    fun i hi => h (L - i) i (by omega)
  intro d
  induction d with
  | zero =>
    intro i hi
    have : i = L := by omega
    subst this
    rw [Finset.Ico_self, Finset.prod_empty]
    exact Nat.card_pos
  | succ d ih =>
    intro i hi
    have hiL : i < L := by omega
    rw [Finset.prod_eq_prod_Ico_succ_bot hiL]
    obtain ⟨s, hs, hreach⟩ := horb i hiL
    have hc := card_ge_of_orbit (G i) (b i) s hreach (G (i + 1))
      (fun g hg => ⟨hdec i hiL hg, hfix (i + 1) (by omega) g hg i (Nat.lt_succ_self i)⟩)
    rw [hs] at hc
    exact (Nat.mul_le_mul_left _ (ih (i + 1) (by omega))).trans hc

theorem commutator_eq_top_of_simple {L : Type*} [Group L] [IsSimpleGroup L]
    (hnab : ∃ a b : L, a * b ≠ b * a) : commutator L = ⊤ := by
  obtain ⟨a, b, hab⟩ := hnab
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator L) with h | h
  · exfalso
    rw [commutator_def] at h
    have ha := (commutator_eq_bot_iff_le_centralizer.1 h) (mem_top a)
    exact hab ((mem_centralizer_iff.1 ha) b (mem_top b)).symm
  · exact h

variable {G : Type*} [Group G]

theorem not_mem_of_simple (L : Subgroup G) [IsSimpleGroup L] (hnab : ∃ a b : L, a * b ≠ b * a)
    {x : G} (hx : x ≠ 1) (hc : ∀ l ∈ L, l * x = x * l) : x ∉ L := by
  intro hxL
  have hz : (⟨x, hxL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hc g.1 g.2)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center L) with h | h
  · rw [h, mem_bot] at hz
    exact hx (congrArg Subtype.val hz)
  · obtain ⟨a, b, hab⟩ := hnab
    have hb : b ∈ center L := h ▸ mem_top b
    exact hab ((mem_center_iff.1 hb) a)

theorem pow_two_mul {x : G} (hx3 : x ^ 3 = 1) : x * x * (x * x) = x := by
  have h4 : x * x * (x * x) = x ^ 3 * x := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [h4, hx3, one_mul]

theorem conj_mem_of_card (C L : Subgroup G) [Finite C] {x : G} (hxC : x ∈ C) (hLC : L ≤ C)
    (hc : ∀ l ∈ L, l * x = x * l) (hx3 : x ^ 3 = 1) (hxL : x ∉ L) (hperf : commutator L = ⊤)
    (hcard : Nat.card C ≤ 6 * Nat.card L) : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
  classical
  have hx1 : x ≠ 1 := fun h => hxL (h ▸ L.one_mem)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hcomm : ∀ (a : L) (b : zpowers x), Commute (L.subtype a) ((zpowers x).subtype b) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    have h1 : Commute a x := hc a ha
    exact h1.zpow_right k
  let φ := MonoidHom.noncommCoprod L.subtype (zpowers x).subtype hcomm
  have hφ : ∀ p, φ p = (p.1 : G) * (p.2 : G) := fun p => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ h
    rw [hφ] at h
    change a * b = 1 at h
    have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    have hbL : b ∈ L := hb' ▸ L.inv_mem ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    have e : x ^ k = x ^ (k % 3) := by
      rw [← zpow_mod_orderOf, hox]
      simp
    have hk : x ^ k = 1 := by
      rw [e] at hbL ⊢
      have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases this with h0 | h1 | h2
      · rw [h0, zpow_zero]
      · rw [h1, zpow_one] at hbL
        exact absurd hbL hxL
      · rw [h2, zpow_two] at hbL
        have := L.mul_mem hbL hbL
        rw [pow_two_mul hx3] at this
        exact absurd this hxL
    rw [hk, mul_one] at h
    subst h
    refine Prod.ext (Subtype.ext rfl) (Subtype.ext ?_)
    exact hk
  set M := φ.range with hMdef
  have hMC : M ≤ C := by
    rintro _ ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩
    rw [hφ]
    exact C.mul_mem (hLC ha) ((zpowers_le.2 hxC) hb)
  have hLM : ∀ l ∈ L, l ∈ M := fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hφ]; simp⟩
  have : Finite L := Finite.of_injective (inclusion hLC) (inclusion_injective hLC)
  have hcM : Nat.card M = Nat.card L * 3 := by
    have e1 : Nat.card M = Nat.card (L × zpowers x) :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [e1, Nat.card_prod, Nat.card_zpowers, hox]
  have hcS : Nat.card (M.subgroupOf C) = Nat.card M :=
    Nat.card_congr (subgroupOfEquivOfLe hMC).toEquiv
  have hidx := (M.subgroupOf C).card_mul_index
  rw [hcS, hcM] at hidx
  have hLpos : 0 < Nat.card L := Nat.card_pos
  have hi0 : (M.subgroupOf C).index ≠ 0 := index_ne_zero_of_finite
  have hi2 : (M.subgroupOf C).index ≤ 2 := by nlinarith
  have hN : (M.subgroupOf C).Normal := by
    have : (M.subgroupOf C).index = 1 ∨ (M.subgroupOf C).index = 2 := by omega
    rcases this with h | h
    · rw [index_eq_one] at h
      rw [h]
      infer_instance
    · exact normal_of_index_eq_two h
  have hconjM : ∀ g ∈ C, ∀ m ∈ M, g * m * g⁻¹ ∈ M := by
    intro g hg m hm
    have := hN.conj_mem ⟨m, hMC hm⟩ (mem_subgroupOf.2 hm) ⟨g, hg⟩
    rw [mem_subgroupOf] at this
    simpa using this
  let e := MonoidHom.ofInjective hinj
  let ψ : M →* zpowers x := (MonoidHom.snd _ _).comp e.symm.toMonoidHom
  have hψ : ∀ m : M, ψ m = 1 → (m : G) ∈ L := by
    intro m hm
    have he : (m : G) = φ (e.symm m) := by
      rw [← MonoidHom.ofInjective_apply hinj, MulEquiv.apply_symm_apply]
    have h2 : (e.symm m).2 = 1 := hm
    rw [he, hφ, h2, OneMemClass.coe_one, mul_one]
    exact (e.symm m).1.2
  intro g hg l hl
  let c : L →* M := ((MulAut.conj g).toMonoidHom.comp L.subtype).codRestrict M
    (fun l => hconjM g hg l (hLM l l.2))
  have hker := Abelianization.commutator_subset_ker (ψ.comp c)
  rw [hperf] at hker
  have h1 : (ψ.comp c) ⟨l, hl⟩ = 1 := hker (mem_top _)
  exact hψ (c ⟨l, hl⟩) h1

end CFSG.KC.OrbRow.CentLGrp

end
