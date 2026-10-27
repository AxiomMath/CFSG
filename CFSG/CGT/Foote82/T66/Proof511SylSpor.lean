module

public import CFSG.Monster.B.Mathieu.M22Sylow
public import CFSG.Monster.B.Mathieu.M23Sylow
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsSylow
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.CGT.Foote82.Proof511

namespace SylSpor

open CFSG.Monster.B.Mathieu

theorem card_sqOne_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card {x : A // x ^ 2 = 1} = Nat.card {x : B // x ^ 2 = 1} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    change x ^ 2 = 1 ↔ e x ^ 2 = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff])

theorem card_sqOne_sylow_eq {Y G : Type*} [Group Y] [Finite Y] [Group G] (e : Y ≃* G)
    (P : Sylow 2 Y) (Q : Sylow 2 G) :
    Nat.card {x : ↥(P : Subgroup Y) // x ^ 2 = 1} =
      Nat.card {x : ↥(Q : Subgroup G) // x ^ 2 = 1} := by
  have : Finite G := Finite.of_equiv Y e.toEquiv
  rw [card_sqOne_congr ((P : Subgroup Y).equivMapOfInjective e.toMonoidHom e.injective)]
  exact card_sqOne_congr (Sylow.equiv (P.mapSurjective (f := e.toMonoidHom) e.surjective) Q)

theorem exists_sylow_two_of_eq {G : Type*} [Group G] {p : ℕ} (hp : p = 2) (P : Sylow p G)
    {c : ℕ} (hc : Nat.card {x : ↥(P : Subgroup G) // x ^ 2 = 1} = c) :
    ∃ Q : Sylow 2 G, Nat.card {x : ↥(Q : Subgroup G) // x ^ 2 = 1} = c := by
  subst hp
  exact ⟨P, hc⟩

theorem mem_sq_eq_one_iff {n N : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {gs : List (Equiv.Perm (Fin n))} {s : SylowRecord} (h : SylowFacts G N gs s)
    (hp : s.prime = 2) (g : Equiv.Perm (Fin n)) :
    (g ∈ s.subgroup n ∧ g ^ 2 = 1) ↔ (g = 1 ∨ g ∈ s.reps n) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, hreps, huniq, -, -⟩ := h
  constructor
  · rintro ⟨hg, hg2⟩
    by_cases h1 : g = 1
    · exact Or.inl h1
    · right
      have hord : orderOf g = 2 := orderOf_eq_prime hg2 h1
      obtain ⟨x, ⟨hx, hxQ⟩, -⟩ := huniq _ (Subgroup.zpowers_le.2 hg)
        (by rw [Nat.card_zpowers, hord, hp])
      rw [mem_zpowers_iff_mem_range_orderOf, hord, Finset.mem_image] at hxQ
      obtain ⟨k, hk, rfl⟩ := hxQ
      rw [Finset.mem_range] at hk
      interval_cases k
      · obtain ⟨-, hxo, -⟩ := hreps _ hx
        rw [pow_zero, orderOf_one, hp] at hxo
        exact absurd hxo (by norm_num)
      · simpa using hx
  · rintro (rfl | hg)
    · exact ⟨Subgroup.one_mem _, one_pow 2⟩
    · obtain ⟨hgP, hgo, -⟩ := hreps g hg
      exact ⟨hgP, by rw [← hp, ← hgo]; exact pow_orderOf_eq_one g⟩

theorem card_sqOne_subgroup {n N : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {gs : List (Equiv.Perm (Fin n))} {s : SylowRecord} (h : SylowFacts G N gs s)
    (hp : s.prime = 2) :
    Nat.card {x : ↥(s.subgroup n) // x ^ 2 = 1} = s.normalGeneration.length + 1 := by
  classical
  have hnd : (s.reps n).Nodup := h.2.2.2.2.2.2.1
  have h1 : (1 : Equiv.Perm (Fin n)) ∉ s.reps n := fun h1 => by
    have h1o := (h.2.2.2.2.2.2.2.1 1 h1).2.1
    rw [orderOf_one, hp] at h1o
    exact absurd h1o (by norm_num)
  have hF : ∀ g, g ∈ (insert 1 (s.reps n).toFinset : Finset (Equiv.Perm (Fin n))) ↔
      g ∈ s.subgroup n ∧ g ^ 2 = 1 := fun g => by
    rw [mem_sq_eq_one_iff h hp, Finset.mem_insert, List.mem_toFinset]
  let e : {x : ↥(s.subgroup n) // x ^ 2 = 1} ≃
      (insert 1 (s.reps n).toFinset : Finset (Equiv.Perm (Fin n))) :=
    { toFun := fun x => ⟨x.1.1, (hF _).2 ⟨x.1.2, congrArg Subtype.val x.2⟩⟩
      invFun := fun g => ⟨⟨g.1, ((hF _).1 g.2).1⟩, Subtype.ext ((hF _).1 g.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_insert_of_notMem (mt List.mem_toFinset.1 h1), List.toFinset_card_of_nodup hnd,
    SylowRecord.reps, List.length_map]

theorem exists_sylow_card_sqOne {n N : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {gs : List (Equiv.Perm (Fin n))} {s : SylowRecord} (h : SylowFacts G N gs s)
    (hp : s.prime = 2) :
    ∃ P : Sylow 2 G, Nat.card {x : ↥(P : Subgroup G) // x ^ 2 = 1} =
      s.normalGeneration.length + 1 := by
  obtain ⟨P, hP, -⟩ := h.2.2.2.2.2.2.2.2.2.2
  refine exists_sylow_two_of_eq hp P ?_
  rw [card_sqOne_congr ((P : Subgroup G).equivMapOfInjective G.subtype G.subtype_injective), hP]
  exact card_sqOne_subgroup h hp

theorem card_sqOne_of_record {Y : Type} [Group Y] [Finite Y] {n N : ℕ}
    {G : Subgroup (Equiv.Perm (Fin n))} {gs : List (Equiv.Perm (Fin n))} {r : GroupRecord}
    (hfacts : ∀ s ∈ r.sylows, SylowFacts G N gs s)
    (hmem : (2, 35) ∈ r.sylows.map (fun s => (s.prime, s.normalGeneration.length)))
    (e : Y ≃* G) (P : Sylow 2 Y) :
    Nat.card {x : ↥(P : Subgroup Y) // x ^ 2 = 1} = 36 := by
  obtain ⟨s, hs, hs2⟩ := List.mem_map.1 hmem
  simp only [Prod.mk.injEq] at hs2
  obtain ⟨Q, hQ⟩ := exists_sylow_card_sqOne (hfacts s hs) hs2.1
  rw [card_sqOne_sylow_eq e P Q, hQ, hs2.2]

open CFSG.ComponentClassification.J2Cover.Models

theorem card_mulIdx_self : Fintype.card {a : Fin 128 // mulIdx a a = 0} = 36 := by
  decide +kernel

theorem card_sqOne_S :
    Nat.card {x : ↥S // x ^ 2 = 1} = 36 := by
  have key : ∀ a : Fin 128, mulIdx a a = 0 ↔ eltEquiv a ^ 2 = 1 := fun a => by
    obtain ⟨hlt, he⟩ := mulIdx_spec (a := a) a.2
    change mulIdx a a = 0 ↔ elt a ^ 2 = 1
    rw [pow_two, ← he, ← elt_zero]
    exact ⟨fun h => by rw [h], fun h => elt_injective hlt (by norm_num) h⟩
  rw [← Nat.card_congr (eltEquiv.subtypeEquiv (p := fun a : Fin 128 => mulIdx a a = 0)
    (q := fun x : ↥S => x ^ 2 = 1) key), Nat.card_eq_fintype_card, card_mulIdx_self]

theorem nonempty_equiv_P :
    Nonempty (CFSG.Blueprint.NativeSporadic.J2 ≃* ↥P) :=
  ⟨CFSG.Sporadic.J2.nativeEquiv.trans
    ((MonoidHom.ofInjective (f := MulAction.toPermHom CFSG.Sporadic.J2.J (Fin 315))
      MulAction.toPerm_injective).trans (MulEquiv.subgroupCongr P_eq_range.symm))⟩

end SylSpor

open SylSpor

theorem sqOne_card_M22 {Y : Type}
    [Group Y] [Finite Y] (h : CFSG.Blueprint.NativeSporadic.IsSporadic Y .M22) (P : Sylow 2 Y) :
    Nat.card {x : ↥(P : Subgroup Y) // x ^ 2 = 1} = 36 := by
  obtain ⟨e⟩ := h
  obtain ⟨r, -, -, -, hcounts, -, hfacts⟩ := CFSG.Monster.B.Mathieu.fam_M22_sylow_normal_generation
  exact card_sqOne_of_record hfacts (by rw [hcounts]; simp)
    (e : Y ≃* ↥CFSG.Blueprint.NativeSporadic.M22) P

theorem sqOne_card_M23 {Y : Type}
    [Group Y] [Finite Y] (h : CFSG.Blueprint.NativeSporadic.IsSporadic Y .M23) (P : Sylow 2 Y) :
    Nat.card {x : ↥(P : Subgroup Y) // x ^ 2 = 1} = 36 := by
  obtain ⟨e⟩ := h
  obtain ⟨r, -, -, -, hcounts, -, hfacts⟩ := CFSG.Monster.B.Mathieu.fam_M23_sylow_normal_generation
  exact card_sqOne_of_record hfacts (by rw [hcounts]; simp)
    (e : Y ≃* ↥CFSG.Blueprint.NativeSporadic.M23) P

theorem sqOne_card_J2 {Y : Type}
    [Group Y] [Finite Y] (h : CFSG.Blueprint.NativeSporadic.IsSporadic Y .J2) (P : Sylow 2 Y) :
    Nat.card {x : ↥(P : Subgroup Y) // x ^ 2 = 1} = 36 := by
  obtain ⟨e⟩ := h
  obtain ⟨eP⟩ := nonempty_equiv_P
  rw [card_sqOne_sylow_eq (e.trans eP) P CFSG.ComponentClassification.J2Cover.Models.sylowS,
    CFSG.ComponentClassification.J2Cover.Models.coe_sylowS,
    card_sqOne_congr (Subgroup.subgroupOfEquivOfLe
      CFSG.ComponentClassification.J2Cover.Models.S_le_P), card_sqOne_S]

end CFSG.CGT.Foote82.Proof511
