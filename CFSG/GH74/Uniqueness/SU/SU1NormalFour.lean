module

public import CFSG.GH74.Uniqueness.SU.SU1Normal4
public import CFSG.GH74.Uniqueness.SU.SU1Normal5

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup

theorem mem_zpowers_subtype {P : Type} [Group P] {Q : Subgroup P} {a x : Q} :
    x ∈ zpowers a ↔ (x : P) ∈ zpowers (a : P) := by
  constructor
  · intro hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, by rw [← hm]; simp⟩
  · intro hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext (by simpa using hm)⟩

theorem exists_normal_four_of_card_eight {P : Type} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {Q : Subgroup P} [hQ : Q.Normal] {E : Subgroup P} (hEQ : E ≤ Q)
    (hE : Open.IsElemAbelian 2 E) (hc : Nat.card E = 2 ^ 3) :
    ∃ U : Subgroup P, U.Normal ∧ U ≤ Q ∧ Open.IsElemAbelian 2 U ∧ Nat.card U = 2 ^ 2 := by
  by_contra hcon
  have hstar : ∀ U : Subgroup P, U.Normal → U ≤ Q → Open.IsElemAbelian 2 U →
      Nat.card U = 2 ^ 2 → False := fun U hU hUQ hUel hUc => hcon ⟨U, hU, hUQ, hUel, hUc⟩
  obtain ⟨F, hFE, hF, hFc⟩ := exists_subgroup_card Nat.prime_two hE (j := 2) (by norm_num) hc
  obtain ⟨k, a, hk, hord, haQ, y, hyQ, hyA, hy2, hcos, hconj⟩ :=
    two_shape_of_rank hP hstar ⟨F, hFE.trans hEQ, hF, hFc⟩
  have hcosQ : ∀ g : Q, g ∈ zpowers (⟨a, haQ⟩ : Q) ∨
      (⟨y, hyQ⟩ : Q)⁻¹ * g ∈ zpowers (⟨a, haQ⟩ : Q) := by
    intro g
    rcases hcos g g.2 with h | h
    · exact Or.inl (mem_zpowers_subtype.mpr h)
    · exact Or.inr (mem_zpowers_subtype.mpr (by simpa using h))
  have hy2Q : (⟨y, hyQ⟩ : Q) * ⟨y, hyQ⟩ ∈ zpowers (⟨a, haQ⟩ : Q) :=
    mem_zpowers_subtype.mpr (by simpa using hy2)
  have hyQ' : (⟨y, hyQ⟩ : Q) ∉ zpowers (⟨a, haQ⟩ : Q) := fun h =>
    hyA (by simpa using mem_zpowers_subtype.mp h)
  have hidx : (zpowers (⟨a, haQ⟩ : Q)).index = 2 := index_eq_two_of_cosets hy2Q hyQ' hcosQ
  have hE2 := (isElemAbelian_iff.mp hE).2
  have hle := card_le_four_of_cyclic_index_two hidx (E := E.subgroupOf Q) (fun x hx => by
    apply Subtype.ext
    have := hE2 x.1 (Subgroup.mem_subgroupOf.mp hx)
    simpa [pow_two] using this)
  have hcard : Nat.card (E.subgroupOf Q) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ).toEquiv
  rw [hcard, hc] at hle
  norm_num at hle

theorem exists_normal_fourGroup_of_pRank_ge_three {G : Type} [Group G] [Finite G] {P : Subgroup G}
    (hP : IsPGroup 2 P) (h3 : 3 ≤ Open.pRank 2 P) :
    ∃ U : Subgroup G, U ≤ P ∧ P ≤ Subgroup.normalizer (U : Set G) ∧ Open.IsElemAbelian 2 U ∧
      Nat.card U = 4 := by
  obtain ⟨E, hEP, hE, hEc⟩ := exists_isElemAbelian_of_le_pRank Nat.prime_two h3
  have hE' : Open.IsElemAbelian 2 (E.subgroupOf P) := by
    have hE1 := isElemAbelian_iff.mp hE
    rw [isElemAbelian_iff]
    refine ⟨fun a ha b hb => Subtype.ext (hE1.1 a ha b hb), fun a ha => ?_⟩
    apply Subtype.ext
    simpa using hE1.2 a ha
  have hcard : Nat.card (E.subgroupOf P) = 2 ^ 3 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv
  obtain ⟨U', hU'n, -, hU'el, hU'c⟩ := exists_normal_four_of_card_eight (Q := ⊤) hP
    (le_top : E.subgroupOf P ≤ ⊤) hE' hcard
  refine ⟨U'.map P.subtype, Subgroup.map_subtype_le U', ?_, ?_, ?_⟩
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hh
      exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * u * ⟨g, hg⟩⁻¹, hU'n.conj_mem u hu ⟨g, hg⟩, rfl⟩
    · intro hh
      obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.mp hh
      refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩⁻¹ * u * ⟨g, hg⟩, ?_, ?_⟩
      · have := hU'n.conj_mem u hu ⟨g, hg⟩⁻¹
        simpa using this
      · have e : (P.subtype u : G) = g * h * g⁻¹ := hue
        calc P.subtype (⟨g, hg⟩⁻¹ * u * ⟨g, hg⟩) = g⁻¹ * (P.subtype u) * g := by simp
          _ = g⁻¹ * (g * h * g⁻¹) * g := by rw [e]
          _ = h := by group
  · have hU'1 := isElemAbelian_iff.mp hU'el
    rw [isElemAbelian_iff]
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
      simpa using congrArg Subtype.val (hU'1.1 u hu v hv)
    · obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      have := congrArg Subtype.val (hU'1.2 u hu)
      simpa using this
  · rw [Subgroup.card_map_of_injective P.subtype_injective, hU'c]
    norm_num

end CFSG.GH74.Uniqueness.SU.SU1
