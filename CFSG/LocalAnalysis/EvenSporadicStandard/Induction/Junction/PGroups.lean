module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup

variable {G : Type*} [Group G]

theorem exists_index_two [Finite G] {W W₁ : Subgroup G} (hW : IsPGroup 2 W) (hle : W₁ ≤ W)
    (hne : W₁ ≠ W) :
    ∃ (W' : Subgroup G) (s : G), W₁ ≤ W' ∧ W' ≤ W ∧ s ∈ W ∧ s ∉ W' ∧ s ^ 2 ∈ W' ∧
      (∀ g ∈ W, ∀ u ∈ W', g * u * g⁻¹ ∈ W') ∧ (∀ g ∈ W, g ∈ W' ∨ s⁻¹ * g ∈ W') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥W := hW.isNilpotent
  have hne' : W₁.subgroupOf W ≠ ⊤ := fun h => hne (le_antisymm hle (subgroupOf_eq_top.1 h))
  obtain ⟨c, hc, hcle⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (W₁.subgroupOf W)).resolve_left hne'
  have hidx : c.index = 2 := (hW.isCoatom_iff_index_eq_prime).1 hc
  have : c.Normal := Subgroup.normal_of_index_eq_two hidx
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hidx
  have ha1 : a ∉ c := by
    rcases ha 1 with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact absurd c.one_mem h'
    · simpa using h'
  have ha2 : a * a ∈ c := by
    rcases ha a with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact h
    · exact absurd h ha1
  have hcov : ∀ g : ↥W, g ∈ c ∨ a⁻¹ * g ∈ c := by
    intro g
    by_cases hg : g ∈ c
    · exact Or.inl hg
    · right
      have h1 : g * a⁻¹ ∈ c := by
        rcases ha (g * a⁻¹) with ⟨h, h'⟩ | ⟨h, h'⟩
        · exact absurd (by simpa using h) hg
        · exact h
      have h2 : a⁻¹ * g = a⁻¹ * (g * a⁻¹) * a⁻¹⁻¹ := by group
      rw [h2]
      exact ‹c.Normal›.conj_mem _ h1 _
  refine ⟨c.map W.subtype, (a : G), ?_, ?_, a.2, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hle hx⟩, hcle hx, rfl⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro ⟨y, hy, hya⟩
    exact ha1 (by rw [← Subtype.ext hya]; exact hy)
  · exact ⟨a * a, ha2, by simp [pow_two]⟩
  · rintro g hg _ ⟨y, hy, rfl⟩
    exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, ‹c.Normal›.conj_mem _ hy _, by simp⟩
  · intro g hg
    rcases hcov ⟨g, hg⟩ with h | h
    · exact Or.inl ⟨⟨g, hg⟩, h, rfl⟩
    · exact Or.inr ⟨a⁻¹ * ⟨g, hg⟩, h, by simp⟩

theorem perfect_le_of_sup_eq_top [Finite G] {N V P : Subgroup G} [N.Normal] (hV : IsPGroup 2 V)
    (hNV : N ⊔ V = ⊤) (hP : ⁅P, P⁆ = P) : P ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVmap : V.map (QuotientGroup.mk' N) = ⊤ := by
    have h1 : (N ⊔ V).map (QuotientGroup.mk' N) = ⊤ := by
      rw [hNV, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h1
  have hpg : IsPGroup 2 (G ⧸ N) := by
    have h2 : IsPGroup 2 ↥(V.map (QuotientGroup.mk' N)) := hV.map _
    rw [hVmap] at h2
    exact h2.of_equiv Subgroup.topEquiv
  have : Group.IsNilpotent (G ⧸ N) := hpg.isNilpotent
  have hperf : Group.IsPerfect ↥(P.map (QuotientGroup.mk' N)) := by
    have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hP
    exact Group.IsPerfect.map _
  by_contra hPN
  have hne : P.map (QuotientGroup.mk' N) ≠ ⊥ := by
    intro hb
    apply hPN
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
    exact hb
  have : Nontrivial ↥(P.map (QuotientGroup.mk' N)) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 hne
  exact Group.IsPerfect.not_isNilpotent ↥(P.map (QuotientGroup.mk' N)) inferInstance

theorem sylow_select {Q : Type*} [Group Q] [Finite G] (π : G →* Q) (hπ : Function.Surjective π)
    {T : Subgroup G} [T.Normal] (hT : IsPGroup 2 T) (hTk : T ≤ π.ker) {Tq : Subgroup Q} {sq : Q}
    (hTq : IsPGroup 2 Tq) (hsq : sq ∈ normalizer (Tq : Set Q)) (hsq2 : IsPGroup 2 (zpowers sq))
    (hsqT : sq ^ 2 ∈ Tq) :
    ∃ (T' : Subgroup G) (s : G), IsPGroup 2 T' ∧ T ≤ T' ∧ T'.map π = Tq ∧
      IsPGroup 2 (zpowers s) ∧ s ∈ normalizer (T' : Set G) ∧ π s = sq ∧ s ^ 2 ∈ T' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Dq : Subgroup Q := Tq ⊔ zpowers sq with hDq
  have hzle : zpowers sq ≤ normalizer (Tq : Set Q) := by
    rw [Subgroup.zpowers_le]
    exact hsq
  have hDq2 : IsPGroup 2 Dq := by
    rw [hDq, sup_comm]
    exact IsPGroup.to_sup_of_normal_right' hsq2 hTq hzle
  set D : Subgroup G := Dq.comap π with hD
  have : Finite ↥D := inferInstance
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥D) := inferInstance
  let φ : ↥D →* ↥Dq := (π.comp D.subtype).codRestrict Dq (fun x => x.2)
  have hφ : Function.Surjective φ := by
    intro d
    obtain ⟨g, hg⟩ := hπ (d : Q)
    exact ⟨⟨g, by simp [hD, hg]⟩, Subtype.ext hg⟩
  have hDqtop : (P.mapSurjective hφ : Subgroup ↥Dq) = ⊤ := by
    have hDq2' : IsPGroup 2 ↥Dq := hDq2
    exact ((P.mapSurjective hφ).is_maximal' (Q := ⊤) (hDq2'.of_equiv Subgroup.topEquiv.symm)
      le_top).symm
  set Pg : Subgroup G := (P : Subgroup ↥D).map D.subtype with hPg
  have hPg2 : IsPGroup 2 Pg := P.isPGroup'.map _
  have hπPg : Pg.map π = Dq := by
    have h1 : (P : Subgroup ↥D).map φ = ⊤ := hDqtop
    have h2 : Pg.map π = ((P : Subgroup ↥D).map φ).map Dq.subtype := by
      rw [hPg, Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h2, h1, Subgroup.map_top, Subgroup.range_subtype]
  have hTD : T ≤ D := fun t ht => by
    show π t ∈ Dq
    rw [MonoidHom.mem_ker.1 (hTk ht)]
    exact Dq.one_mem
  have hTPg : T ≤ Pg := by
    have hTn : (T.subgroupOf D).Normal := Subgroup.Normal.subgroupOf inferInstance D
    have hT2 : IsPGroup 2 (T.subgroupOf D) := hT.comap_subtype
    have := IsPGroup.le_sylow_of_normal hT2 P
    intro t ht
    exact ⟨⟨t, hTD ht⟩, this ht, rfl⟩
  set C : Subgroup G := Tq.comap π with hC
  have hTC : T ≤ C := fun t ht => by
    show π t ∈ Tq
    rw [MonoidHom.mem_ker.1 (hTk ht)]
    exact Tq.one_mem
  have hsqD : sq ∈ Dq := (le_sup_right : zpowers sq ≤ Dq) (mem_zpowers sq)
  obtain ⟨s, hsPg, hπs⟩ : ∃ s ∈ Pg, π s = sq := by
    have : sq ∈ Pg.map π := hπPg ▸ hsqD
    obtain ⟨s, hs, hπs⟩ := this
    exact ⟨s, hs, hπs⟩
  refine ⟨Pg ⊓ C, s, hPg2.to_le inf_le_left, le_inf hTPg hTC, ?_, ?_, ?_, hπs, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro t ht
      have : t ∈ Pg.map π := hπPg ▸ (le_sup_left : Tq ≤ Dq) ht
      obtain ⟨p, hp, rfl⟩ := this
      exact ⟨p, ⟨hp, ht⟩, rfl⟩
  · exact hPg2.to_le (by rw [Subgroup.zpowers_le]; exact hsPg)
  · rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxP, hxC⟩
      refine ⟨Pg.mul_mem (Pg.mul_mem hsPg hxP) (Pg.inv_mem hsPg), ?_⟩
      show π (s * x * s⁻¹) ∈ Tq
      rw [map_mul, map_mul, map_inv, hπs]
      exact (mem_normalizer_iff.1 hsq (π x)).1 hxC
    · rintro ⟨hxP, hxC⟩
      have hx1 : x = s⁻¹ * (s * x * s⁻¹) * s := by group
      refine ⟨?_, ?_⟩
      · rw [hx1]
        exact Pg.mul_mem (Pg.mul_mem (Pg.inv_mem hsPg) hxP) hsPg
      · show π x ∈ Tq
        have hsx : π (s * x * s⁻¹) ∈ Tq := hxC
        rw [map_mul, map_mul, map_inv, hπs] at hsx
        exact (mem_normalizer_iff.1 hsq (π x)).2 hsx
  · refine ⟨Pg.pow_mem hsPg 2, ?_⟩
    show π (s ^ 2) ∈ Tq
    rw [map_pow, hπs]
    exact hsqT

end CFSG.EvenSporadicStandard.Induction.Junction
