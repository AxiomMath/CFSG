module

public import CFSG.GH74.Uniqueness.SU.KInputs

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG.GH74.Uniqueness.SU.K

section Abstract

variable {H : Type} [Group H]

theorem map_center_subtype' (Q : Subgroup H) :
    (center ↥Q).map Q.subtype = Q ⊓ centralizer (Q : Set H) := by
  ext a
  simp only [mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe,
    Subgroup.mem_center_iff, Subgroup.coe_subtype]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, fun q hq => ?_⟩
    have := hz ⟨q, hq⟩
    exact congrArg Subtype.val this
  · rintro ⟨ha, hc⟩
    refine ⟨⟨a, ha⟩, fun q => ?_, rfl⟩
    exact Subtype.ext (hc q q.2)

theorem map_centralizer_inf {N : Type} [Group N] (ι : N →* H) (hι : Function.Injective ι)
    (S E : Subgroup N) :
    (centralizer (S : Set N) ⊓ E).map ι =
      centralizer ((S.map ι : Subgroup H) : Set H) ⊓ E.map ι := by
  ext a
  simp only [mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨g, ⟨hg, hgE⟩, rfl⟩
    refine ⟨?_, g, hgE, rfl⟩
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, hg s hs]
  · rintro ⟨hc, g, hgE, rfl⟩
    refine ⟨g, ⟨fun s hs => ?_, hgE⟩, rfl⟩
    have := hc (ι s) ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact hι this

theorem map_center_subgroupOf {N : Subgroup H} (Q : Subgroup H) (hQN : Q ≤ N) :
    ((center ↥(Q.subgroupOf N)).map (Q.subgroupOf N).subtype).map N.subtype =
      (center ↥Q).map Q.subtype := by
  rw [map_center_subtype', map_center_subtype', inf_comm, map_centralizer_inf N.subtype
    N.subtype_injective, inf_comm]
  have h1 : (Q.subgroupOf N).map N.subtype = Q := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hQN]
  rw [h1]

@[expose] def J2S (JJ LL : Type) [Group JJ] [Group LL] (H : Type) [Group H] (T Q : Subgroup H) :
    Prop :=
  Nonempty (↥T ≃* JJ) ∧ Nonempty (↥Q ≃* LL) ∧
    ∃ E : Subgroup H,
      normalizer (Q : Set H) = Q ⊔ E ∧ Q ⊓ E = ⊥ ∧
      (Nonempty (↥E ≃* Equiv.Perm (Fin 3)) ∨
        Nonempty (↥E ≃* Equiv.Perm (Fin 3) × Multiplicative (ZMod 3))) ∧
      ∃ E₀ : Subgroup H, E₀ ≤ E ∧ Nonempty (↥E₀ ≃* Equiv.Perm (Fin 3)) ∧
        E = E₀ ⊔ (centralizer (((center ↥Q).map Q.subtype : Subgroup H) : Set H) ⊓ E) ∧
        E₀ ⊓ (centralizer (((center ↥Q).map Q.subtype : Subgroup H) : Set H) ⊓ E) = ⊥ ∧
        (∀ a ∈ E₀, ∀ c ∈ centralizer (((center ↥Q).map Q.subtype : Subgroup H) : Set H) ⊓ E,
          a * c = c * a) ∧
        (∀ a ∈ E₀, orderOf a = 3 → ∀ t ∈ Q, a * t * a⁻¹ = t → t = 1) ∧
        (Nat.card ↥(centralizer (((center ↥Q).map Q.subtype : Subgroup H) : Set H) ⊓ E) = 1 ∨
          Nat.card ↥(centralizer (((center ↥Q).map Q.subtype : Subgroup H) : Set H) ⊓ E) = 3)

theorem J2S.of_normalizer {JJ LL : Type} [Group JJ] [Group LL] (T Q : Subgroup H)
    (hTN : T ≤ normalizer (Q : Set H))
    (hJ : J2S JJ LL ↥(normalizer (Q : Set H)) (T.subgroupOf (normalizer (Q : Set H)))
      (Q.subgroupOf (normalizer (Q : Set H)))) :
    J2S JJ LL H T Q := by
  set N : Subgroup H := normalizer (Q : Set H) with hNdef
  obtain ⟨hT, hQ, E', hN, hinf, hE, E₀', hle, hE₀, hsup, hinf2, hcomm, hord, hcard⟩ := hJ
  have hQN : Q ≤ N := Subgroup.le_normalizer
  have hι : Function.Injective N.subtype := N.subtype_injective
  have hQmap : (Q.subgroupOf N).map N.subtype = Q := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hQN]
  have hZmap := map_center_subgroupOf Q hQN
  set ZN : Subgroup ↥N := (center ↥(Q.subgroupOf N)).map (Q.subgroupOf N).subtype with hZN
  set ZH : Subgroup H := (center ↥Q).map Q.subtype with hZH
  have hZ : ZN.map N.subtype = ZH := hZmap
  have hC : (centralizer (ZN : Set ↥N) ⊓ E').map N.subtype =
      centralizer (ZH : Set H) ⊓ E'.map N.subtype := by
    rw [map_centralizer_inf N.subtype hι ZN E', hZ]
  have hNtop : normalizer ((Q.subgroupOf N : Subgroup ↥N) : Set ↥N) = ⊤ := by
    rw [Subgroup.normalizer_eq_top_iff]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).2 le_rfl
  refine ⟨⟨(Subgroup.subgroupOfEquivOfLe hTN).symm.trans hT.some⟩,
    ⟨(Subgroup.subgroupOfEquivOfLe hQN).symm.trans hQ.some⟩, E'.map N.subtype, ?_, ?_, ?_,
    E₀'.map N.subtype, Subgroup.map_mono hle, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := congrArg (Subgroup.map N.subtype) hN
    rw [hNtop, Subgroup.map_top, Subgroup.range_subtype, Subgroup.map_sup, hQmap] at h1
    exact h1
  · have h1 := congrArg (Subgroup.map N.subtype) hinf
    rw [Subgroup.map_inf _ _ _ hι, hQmap, Subgroup.map_bot] at h1
    exact h1
  · rcases hE with hE | hE
    · exact Or.inl ⟨(E'.equivMapOfInjective N.subtype hι).symm.trans hE.some⟩
    · exact Or.inr ⟨(E'.equivMapOfInjective N.subtype hι).symm.trans hE.some⟩
  · exact ⟨(E₀'.equivMapOfInjective N.subtype hι).symm.trans hE₀.some⟩
  · have h1 := congrArg (Subgroup.map N.subtype) hsup
    rw [Subgroup.map_sup, hC] at h1
    exact h1
  · have h1 := congrArg (Subgroup.map N.subtype) hinf2
    rw [Subgroup.map_inf _ _ _ hι, hC, Subgroup.map_bot] at h1
    exact h1
  · intro a ha c hc
    obtain ⟨a', ha', rfl⟩ := ha
    have hc' : c ∈ (centralizer (ZN : Set ↥N) ⊓ E').map N.subtype := by rw [hC]; exact hc
    obtain ⟨c', hc'', rfl⟩ := hc'
    exact congrArg Subtype.val (hcomm a' ha' c' hc'')
  · intro a ha h3 t ht hat
    obtain ⟨a', ha', rfl⟩ := ha
    have h3' : orderOf a' = 3 := by
      rw [← h3]
      exact (orderOf_injective N.subtype hι a').symm
    have ht' : (⟨t, hQN ht⟩ : ↥N) ∈ Q.subgroupOf N := ht
    have := hord a' ha' h3' ⟨t, hQN ht⟩ ht' (hι (by simpa using hat))
    simpa using congrArg Subtype.val this
  · rw [← hC, Subgroup.card_map_of_injective hι]
    exact hcard

end Abstract

theorem J2Structure_iff {H : Type} [Group H] (T : Sylow 2 H) :
    J2Structure H T ↔
      J2S SU5.J2Syl CFSG.GH74.GLS.Bg.TwoGroups.SylSL3_4 H (T : Subgroup H) (Psub H T) :=
  Iff.rfl

theorem J2Structure.of_normalizer {H : Type} [Group H] [Finite H] (T : Sylow 2 H)
    (P : Subgroup H) (hTN : (T : Subgroup H) ≤ normalizer (P : Set H))
    (hP : Psub H T = P)
    (hJ : J2Structure ↥(normalizer (P : Set H)) (T.subtype hTN))
    (hPN : Psub ↥(normalizer (P : Set H)) (T.subtype hTN) =
      P.subgroupOf (normalizer (P : Set H))) :
    J2Structure H T := by
  rw [J2Structure_iff] at hJ ⊢
  rw [hPN] at hJ
  rw [hP]
  exact J2S.of_normalizer (T : Subgroup H) P hTN hJ

end CFSG.GH74.Uniqueness.SU.K.R4
