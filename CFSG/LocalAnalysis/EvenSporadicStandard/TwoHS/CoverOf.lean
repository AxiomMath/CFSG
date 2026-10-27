module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Defs

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

structure CoverData {C P : Type} [Group C] [Group P] (φ : C →* P) (D : Subgroup P) (t : C) :
    Prop where
  card_ker : Nat.card φ.ker = 2
  mem_ker : t ∈ φ.ker
  ne_one : t ≠ 1
  central : ∀ x : C, x * t = t * x
  le_range : D ≤ φ.range
  normalizes : φ.range ≤ Subgroup.normalizer (D : Set P)
  index_two : (D.subgroupOf φ.range).index = 2
  simple : IsSimpleGroup D
  noncomm : ∃ a b : D, a * b ≠ b * a
  centralizer_trivial : ∀ z : P, (∀ d ∈ D, z * d = d * z) → z = 1
  quotient : IsSporadic D .HS

section Simple

variable {K : Type*} [Group K] [IsSimpleGroup K]

theorem center_eq_bot_of_simple_noncomm (h : ∃ a b : K, a * b ≠ b * a) :
    center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with h0 | h0
  · exact h0
  · obtain ⟨a, b, hab⟩ := h
    exact absurd (mem_center_iff.1 (h0 ▸ mem_top b) a) hab

theorem isPerfect_of_simple_noncomm (h : ∃ a b : K, a * b ≠ b * a) :
    Group.IsPerfect K := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator K) with h0 | h0
  · exfalso
    obtain ⟨x, y, hxy⟩ := h
    apply hxy
    have hmem : ⁅x, y⁆ ∈ commutator K := by
      rw [_root_.commutator_def]
      exact commutator_mem_commutator (mem_top x) (mem_top y)
    rw [h0, mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  · exact h0

end Simple

namespace CoverData

variable {C P : Type} [Group C] [Group P] {φ : C →* P} {D : Subgroup P} {t : C}

theorem eq_one_or_eq (hd : CoverData φ D t) {z : C} (hz : z ∈ φ.ker) : z = 1 ∨ z = t := by
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : φ.ker)).1 hd.card_ker
  by_cases h1 : z = 1
  · exact Or.inl h1
  · right
    have h1' : (⟨z, hz⟩ : φ.ker) ≠ 1 := fun h => h1 (congrArg Subtype.val h)
    have h2' : (⟨t, hd.mem_ker⟩ : φ.ker) ≠ 1 := fun h => hd.ne_one (congrArg Subtype.val h)
    exact congrArg Subtype.val ((huniq _ h1').trans (huniq _ h2').symm)

theorem sq_eq_one (hd : CoverData φ D t) {z : C} (hz : z ∈ φ.ker) : z ^ 2 = 1 := by
  have h := pow_card_eq_one' (G := φ.ker) (x := ⟨z, hz⟩)
  rw [hd.card_ker] at h
  simpa using congrArg Subtype.val h

theorem mul_comm_of_mem_ker (hd : CoverData φ D t) {z : C} (hz : z ∈ φ.ker) (x : C) :
    x * z = z * x := by
  rcases hd.eq_one_or_eq hz with rfl | rfl
  · simp
  · exact hd.central x

theorem normal_comap (hd : CoverData φ D t) : (D.comap φ).Normal where
  conj_mem n hn g := by
    have h := (mem_normalizer_iff.1 (hd.normalizes (φ.mem_range.2 ⟨g, rfl⟩)) (φ n)).1 hn
    simpa [mem_comap] using h

theorem index_comap (hd : CoverData φ D t) : (D.comap φ).index = 2 := by
  rw [Subgroup.index_comap]
  exact hd.index_two

theorem map_comap (hd : CoverData φ D t) : (D.comap φ).map φ = D := by
  rw [Subgroup.map_comap_eq, inf_eq_right.2 hd.le_range]

theorem exists_mem_comap (hd : CoverData φ D t) {d : P} (hd' : d ∈ D) :
    ∃ g ∈ D.comap φ, φ g = d := by
  obtain ⟨g, hg⟩ := hd.le_range hd'
  exact ⟨g, by rw [mem_comap, hg]; exact hd', hg⟩

theorem commutator_comap_sup_ker (hd : CoverData φ D t) :
    ⁅D.comap φ, D.comap φ⁆ ⊔ φ.ker = D.comap φ := by
  have := hd.simple
  have hperf : ⁅D, D⁆ = D :=
    Subgroup.isPerfect_iff.1 (isPerfect_of_simple_noncomm hd.noncomm)
  rw [← Subgroup.comap_map_eq, Subgroup.map_commutator, hd.map_comap, hperf]

theorem commutator_comap (hd : CoverData φ D t) (hw : ∃ x ∈ D.comap φ, x ^ 2 = t) :
    ⁅D.comap φ, D.comap φ⁆ = D.comap φ := by
  have hsup := hd.commutator_comap_sup_ker
  obtain ⟨x, hx, hxt⟩ := hw
  have hx' : x ∈ ⁅D.comap φ, D.comap φ⁆ ⊔ φ.ker := by rw [hsup]; exact hx
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at hx'
  obtain ⟨e, he, z, hz, rfl⟩ := hx'
  have hzc : Commute e z := hd.mul_comm_of_mem_ker hz e
  have ht : t ∈ ⁅D.comap φ, D.comap φ⁆ := by
    rw [← hxt, hzc.mul_pow, hd.sq_eq_one hz, mul_one]
    exact pow_mem he 2
  have hker : φ.ker ≤ ⁅D.comap φ, D.comap φ⁆ := fun z hz => by
    rcases hd.eq_one_or_eq hz with rfl | rfl
    · exact one_mem _
    · exact ht
  exact (sup_eq_left.2 hker).symm.trans hsup

theorem center_comap (hd : CoverData φ D t) :
    center (D.comap φ) = φ.ker.subgroupOf (D.comap φ) := by
  have := hd.simple
  ext ⟨e, he⟩
  constructor
  · intro hc
    have hcD : (⟨φ e, he⟩ : D) ∈ center D := by
      rw [mem_center_iff]
      intro d
      obtain ⟨g, hgE, hg⟩ := hd.exists_mem_comap d.2
      have h2 := congrArg (fun x : D.comap φ => φ (x : C)) (mem_center_iff.1 hc ⟨g, hgE⟩)
      exact Subtype.ext (by simpa [hg] using h2)
    rw [center_eq_bot_of_simple_noncomm hd.noncomm, mem_bot] at hcD
    exact congrArg Subtype.val hcD
  · intro hk
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hd.mul_comm_of_mem_ker (mem_subgroupOf.1 hk) g)

theorem card_center_comap (hd : CoverData φ D t) : Nat.card (center (D.comap φ)) = 2 := by
  rw [hd.center_comap, ← hd.card_ker]
  exact Nat.card_congr (subgroupOfEquivOfLe (MonoidHom.ker_le_comap φ D)).toEquiv

theorem quotient_comap (hd : CoverData φ D t) :
    IsSporadic (D.comap φ ⧸ center (D.comap φ)) .HS := by
  have := hd.normal_comap
  have hψ : Function.Surjective (φ.subgroupComap D) := fun d => by
    obtain ⟨g, hg, hgd⟩ := hd.exists_mem_comap d.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgd⟩
  have hker : (φ.subgroupComap D).ker = center (D.comap φ) := by
    rw [hd.center_comap]
    ext e
    rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  obtain ⟨e⟩ := hd.quotient
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hψ)).trans e⟩

theorem centralizer_comap_le_ker (hd : CoverData φ D t) :
    centralizer ((D.comap φ : Subgroup C) : Set C) ≤ φ.ker := by
  intro y hy
  rw [MonoidHom.mem_ker]
  refine hd.centralizer_trivial _ fun d hd' => ?_
  obtain ⟨g, hg, rfl⟩ := hd.exists_mem_comap hd'
  rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hy g hg]

theorem centralizer_comap_le (hd : CoverData φ D t) :
    centralizer ((D.comap φ : Subgroup C) : Set C) ≤ D.comap φ :=
  hd.centralizer_comap_le_ker.trans (MonoidHom.ker_le_comap φ D)

theorem isHSCover (hd : CoverData φ D t) (hw : ∃ x ∈ D.comap φ, x ^ 2 = t) :
    IsHSCover C (D.comap φ) where
  normal := hd.normal_comap
  index_dvd_two := by rw [hd.index_comap]
  perfect := Subgroup.isPerfect_iff.2 (hd.commutator_comap hw)
  card_center := hd.card_center_comap
  quotient := hd.quotient_comap
  centralizer_le := hd.centralizer_comap_le

theorem sign (hd : CoverData φ D t) (hs : ∀ g : C, g ∉ D.comap φ → g ^ 2 = t → False) :
    ∀ g : C, g ∉ D.comap φ → g ^ 2 ∈ Subgroup.centralizer ((D.comap φ : Subgroup C) : Set C) →
      g ^ 2 = 1 := by
  intro g hg hg2
  rcases hd.eq_one_or_eq (hd.centralizer_comap_le_ker hg2) with h | h
  · exact h
  · exact (hs g hg h).elim

end CoverData

end CFSG.EvenSporadicStandard.TwoHS
