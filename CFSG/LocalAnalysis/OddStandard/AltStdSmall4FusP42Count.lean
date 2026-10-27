module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.AltStdSmall4.Fus.P42

open MulAction Equiv

abbrev Om := Fin 16 × Bool

@[expose] def isO6 (k : Fin 16) : Bool := (k.val % 4 == 0) != (k.val / 4 == 0)

@[expose] def isO9 (k : Fin 16) : Bool := (k.val % 4 != 0) && (k.val / 4 != 0)

@[expose] def piTab : Fin 11 → Fin 16 → Fin 16 :=
  ![![0, 2, 1, 3, 4, 6, 5, 7, 12, 14, 13, 15, 8, 10, 9, 11],
    ![0, 3, 2, 1, 4, 7, 6, 5, 12, 15, 14, 13, 8, 11, 10, 9],
    ![0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15],
    ![0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15],
    ![0, 12, 4, 8, 2, 14, 6, 10, 3, 15, 7, 11, 1, 13, 5, 9],
    ![0, 1, 3, 2, 8, 9, 11, 10, 4, 5, 7, 6, 12, 13, 15, 14],
    ![0, 2, 1, 3, 8, 10, 9, 11, 4, 6, 5, 7, 12, 14, 13, 15],
    ![0, 3, 2, 1, 8, 11, 10, 9, 4, 7, 6, 5, 12, 15, 14, 13],
    ![0, 1, 3, 2, 12, 13, 15, 14, 8, 9, 11, 10, 4, 5, 7, 6],
    ![0, 2, 1, 3, 12, 14, 13, 15, 8, 10, 9, 11, 4, 6, 5, 7],
    ![0, 3, 2, 1, 12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5]]

section Finite

private theorem cls (i : Fin 16) : i = 0 ∨ isO6 i = true ∨ isO9 i = true := by
  revert i
  decide

private theorem isO9_of_isO6 {i : Fin 16} (h : isO6 i = true) : isO9 i = false := by
  revert i h
  decide

private theorem base6 : ∀ i : Fin 16, isO6 i = true → i = 1 ∨ ∃ j, piTab j 1 = i := by
  decide

private theorem base9 : ∀ i : Fin 16, isO9 i = true → i = 5 ∨ ∃ j, piTab j 5 = i := by
  decide

private def tau6 : Perm Om :=
  swap (1, true) (4, true) * swap (2, true) (8, true) * swap (3, true) (12, true)

private theorem tau6_eq : ∀ k : Fin 16, isO6 k = true → tau6 (k, true) = (piTab 2 k, true) := by
  decide

private theorem tau6_iff : ∀ ω : Om, (isO6 (tau6 ω).1 = true ∧ (tau6 ω).2 = true) ↔
    (isO6 ω.1 = true ∧ ω.2 = true) := by
  decide

private theorem tau6_supp : ∀ ω : Om, tau6 ω ≠ ω → (isO6 ω.1 = true ∧ ω.2 = true) := by
  decide

private theorem sign_tau6 : Perm.sign tau6 = -1 := by
  rw [tau6, Perm.sign_mul, Perm.sign_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide),
    Perm.sign_swap (by decide)]
  decide

private theorem card_Z6 :
    Nat.card {ω : Om // isO6 ω.1 = true ∧ ω.2 = true} = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

end Finite

section Count

variable {N : Type*} [Group N] [MulAction N Om]

private theorem smul_mem_orbit' {a ω : Om} (h : ω ∈ orbit N a) (g : N) : g • ω ∈ orbit N a := by
  obtain ⟨h', rfl⟩ := mem_orbit_iff.1 h
  exact mem_orbit_iff.2 ⟨g * h', mul_smul _ _ _⟩

private theorem mem_orbit_of_smul {a ω : Om} {g : N} (h : g • ω ∈ orbit N a) : ω ∈ orbit N a := by
  have := smul_mem_orbit' h g⁻¹
  rwa [inv_smul_smul] at this

variable (hw : ∀ j : Fin 11, ∃ g : N, ∀ k b, g • ((k, b) : Om) = (piTab j k, b))
include hw

private theorem exists_smul_one {i : Fin 16} (hi : isO6 i = true) :
    ∃ g : N, ∀ b, g • ((1, b) : Om) = (i, b) := by
  rcases base6 i hi with rfl | ⟨j, rfl⟩
  · exact ⟨1, fun b => one_smul _ _⟩
  · obtain ⟨g, hg⟩ := hw j
    exact ⟨g, fun b => hg 1 b⟩

private theorem exists_smul_five {i : Fin 16} (hi : isO9 i = true) :
    ∃ g : N, ∀ b, g • ((5, b) : Om) = (i, b) := by
  rcases base9 i hi with rfl | ⟨j, rfl⟩
  · exact ⟨1, fun b => one_smul _ _⟩
  · obtain ⟨g, hg⟩ := hw j
    exact ⟨g, fun b => hg 5 b⟩

private theorem mem_orbit_O6 {a : Om} {i i' : Fin 16} (hi : isO6 i = true) (hi' : isO6 i' = true)
    {b : Bool} (h : ((i, b) : Om) ∈ orbit N a) : ((i', b) : Om) ∈ orbit N a := by
  obtain ⟨g, hg⟩ := exists_smul_one hw hi
  obtain ⟨g', hg'⟩ := exists_smul_one hw hi'
  have h1 : (g' * g⁻¹) • ((i, b) : Om) = (i', b) := by
    rw [mul_smul, ← hg b, inv_smul_smul, hg' b]
  rw [← h1]
  exact smul_mem_orbit' h _

private theorem not_smul_eq_O6_aux (K : Subgroup N)
    (hK : ∀ k ∈ K, ∀ ω : Om, k • ω = ω)
    (hKf : ∀ g : N, (∀ i : Fin 16, isO6 i = true → g • ((i, true) : Om) = (i, true)) → g ∈ K)
    (hidx : K.index = 36 * (stabilizer N ((0, true) : Om)).index)
    (hone : ∀ g : N, g • ((0, false) : Om) = (0, false))
    (hz : ∀ g : N, (g • ((0, true) : Om)).2 = true)
    (hzw : ∃ g : N, g • ((0, true) : Om) = (5, true))
    (g : N) (i : Fin 16) (hi : isO6 i = true) : g • ((5, false) : Om) ≠ (i, false) := by
  intro hgi
  set c : Prop := ((1, true) : Om) ∈ orbit N ((0, true) : Om) with hc_def
  have hOz : ∀ ω : Om, ω ∈ orbit N ((0, true) : Om) ↔ ω.2 = true ∧ (isO6 ω.1 = true → c) := by
    rintro ⟨k, b⟩
    constructor
    · intro h
      obtain ⟨h', hh'⟩ := mem_orbit_iff.1 h
      have hb : b = true := by
        have := hz h'
        rw [hh'] at this
        exact this
      subst hb
      exact ⟨rfl, fun hk => mem_orbit_O6 hw hk (by decide) h⟩
    · rintro ⟨hb, hk⟩
      simp only at hb hk
      subst hb
      rcases cls k with rfl | h6 | h9
      · exact mem_orbit_self _
      · exact mem_orbit_O6 hw (by decide) h6 (hk h6)
      · obtain ⟨g₀, hg₀⟩ := hzw
        obtain ⟨g₁, hg₁⟩ := exists_smul_five hw h9
        refine mem_orbit_iff.2 ⟨g₁ * g₀, ?_⟩
        rw [mul_smul, hg₀, hg₁]
  have hwz : ((5, false) : Om) ∉ orbit N ((0, true) : Om) := by
    intro h
    have := ((hOz _).1 h).1
    exact Bool.false_ne_true this
  have hdisj : ∀ ω : Om, ω ∈ orbit N ((5, false) : Om) → ω ∉ orbit N ((0, true) : Om) := by
    intro ω hω hωz
    obtain ⟨h', rfl⟩ := mem_orbit_iff.1 hω
    exact hwz (mem_orbit_of_smul hωz)
  have hi6 : ((i, false) : Om) ∈ orbit N ((5, false) : Om) := mem_orbit_iff.2 ⟨g, hgi⟩
  set d : Prop := ((1, true) : Om) ∈ orbit N ((5, false) : Om) with hd_def
  have hOw : ∀ ω : Om, ω ∈ orbit N ((5, false) : Om) ↔
      (ω.2 = false ∧ ω.1 ≠ 0) ∨ (ω.2 = true ∧ isO6 ω.1 = true ∧ d) := by
    rintro ⟨k, b⟩
    constructor
    · intro h
      cases b with
      | false =>
        refine Or.inl ⟨rfl, ?_⟩
        rintro (rfl : k = 0)
        obtain ⟨h', hh'⟩ := mem_orbit_iff.1 h
        have h1 : ((5, false) : Om) = h'⁻¹ • ((0, false) : Om) := by
          rw [← hh', inv_smul_smul]
        rw [hone] at h1
        exact absurd (congrArg Prod.fst h1) (by decide)
      | true =>
        refine Or.inr ⟨rfl, ?_⟩
        rcases cls k with rfl | h6 | h9
        · exact absurd (mem_orbit_self _) (hdisj _ h)
        · exact ⟨h6, mem_orbit_O6 hw h6 (by decide) h⟩
        · exfalso
          apply hdisj _ h
          rw [hOz]
          exact ⟨rfl, fun h6 => absurd (isO9_of_isO6 h6) (by simp [h9])⟩
    · rintro (⟨hb, hk⟩ | ⟨hb, hk, hdd⟩)
      · simp only at hb hk
        subst hb
        rcases cls k with h0 | h6 | h9
        · exact absurd h0 hk
        · exact mem_orbit_O6 hw hi h6 hi6
        · obtain ⟨g₁, hg₁⟩ := exists_smul_five hw h9
          exact mem_orbit_iff.2 ⟨g₁, hg₁ false⟩
      · simp only at hb hk
        subst hb
        exact mem_orbit_O6 hw (by decide) hk hdd
  have hKw : K ≤ stabilizer N ((5, false) : Om) := fun k hk => hK k hk _
  have hdvd : (orbit N ((5, false) : Om)).ncard ∣ K.index := by
    rw [← index_stabilizer]
    exact Subgroup.index_dvd_of_le hKw
  rw [index_stabilizer] at hidx
  by_cases hc : c
  ·
    have hnd : ¬ d := fun hd => hdisj _ hd hc
    have h1 : orbit N ((0, true) : Om) = ↑(Finset.univ.filter fun ω : Om => ω.2 = true) := by
      ext ω
      rw [hOz]
      simp [hc]
    have h2 : orbit N ((5, false) : Om) =
        ↑(Finset.univ.filter fun ω : Om => ω.2 = false ∧ ω.1 ≠ 0) := by
      ext ω
      rw [hOw]
      simp [hnd]
    rw [h1, Set.ncard_coe_finset] at hidx
    rw [h2, Set.ncard_coe_finset, hidx] at hdvd
    revert hdvd
    decide
  · have h1 : orbit N ((0, true) : Om) =
        ↑(Finset.univ.filter fun ω : Om => ω.2 = true ∧ isO6 ω.1 = false) := by
      ext ω
      rw [hOz]
      simp [hc]
    rw [h1, Set.ncard_coe_finset] at hidx
    have hidx' : K.index = 360 := by
      rw [hidx]
      decide
    by_cases hd : d
    ·
      have h2 : orbit N ((5, false) : Om) =
          ↑(Finset.univ.filter fun ω : Om =>
            (ω.2 = false ∧ ω.1 ≠ 0) ∨ (ω.2 = true ∧ isO6 ω.1 = true)) := by
        ext ω
        rw [hOw]
        simp [hd]
      rw [h2, Set.ncard_coe_finset, hidx'] at hdvd
      revert hdvd
      decide
    ·
      have hinv1 : ∀ (g' : N) (ω : Om), isO6 ω.1 = true ∧ ω.2 = true →
          isO6 (g' • ω).1 = true ∧ (g' • ω).2 = true := by
        rintro g' ⟨k, b⟩ ⟨hk, hb⟩
        simp only at hk hb
        subst hb
        have hnz : g' • ((k, true) : Om) ∉ orbit N ((0, true) : Om) := by
          intro h
          exact hc (((hOz _).1 (mem_orbit_of_smul h)).2 hk)
        have hnw : g' • ((k, true) : Om) ∉ orbit N ((5, false) : Om) := by
          intro h
          rcases (hOw _).1 (mem_orbit_of_smul h) with ⟨hb, -⟩ | ⟨-, -, hdd⟩
          · simp at hb
          · exact hd hdd
        have hn1 : g' • ((k, true) : Om) ≠ (0, false) := by
          intro h
          have h1 : ((k, true) : Om) = g'⁻¹ • ((0, false) : Om) := by
            rw [← h, inv_smul_smul]
          rw [hone] at h1
          simp at h1
        generalize g' • ((k, true) : Om) = ω' at hnz hnw hn1 ⊢
        obtain ⟨k', b'⟩ := ω'
        cases b' with
        | false =>
          exfalso
          by_cases hk0 : k' = 0
          · exact hn1 (by rw [hk0])
          · exact hnw ((hOw _).2 (Or.inl ⟨rfl, hk0⟩))
        | true =>
          refine ⟨?_, rfl⟩
          rcases cls k' with rfl | h6 | h9
          · exact absurd (mem_orbit_self _) hnz
          · exact h6
          · exact absurd ((hOz _).2 ⟨rfl, fun h6 => absurd (isO9_of_isO6 h6) (by simp [h9])⟩) hnz
      have hinv : ∀ (g' : N) (ω : Om), (isO6 (g' • ω).1 = true ∧ (g' • ω).2 = true) ↔
          (isO6 ω.1 = true ∧ ω.2 = true) := by
        intro g' ω
        refine ⟨fun h => ?_, hinv1 g' ω⟩
        have := hinv1 g'⁻¹ _ h
        rwa [inv_smul_smul] at this
      let φ : N →* Perm {ω : Om // isO6 ω.1 = true ∧ ω.2 = true} :=
        { toFun := fun g' => (MulAction.toPerm g').subtypePerm (hinv g')
          map_one' := Equiv.ext fun x => Subtype.ext (one_smul N (x : Om))
          map_mul' := fun g₁ g₂ => Equiv.ext fun x => Subtype.ext (mul_smul g₁ g₂ (x : Om)) }
      have hφ : ∀ (g' : N) (x : {ω : Om // isO6 ω.1 = true ∧ ω.2 = true}),
          ((φ g' x : {ω : Om // isO6 ω.1 = true ∧ ω.2 = true}) : Om) = g' • (x : Om) :=
        fun _ _ => rfl
      have hker : φ.ker = K := by
        ext g'
        rw [MonoidHom.mem_ker]
        constructor
        · intro h
          apply hKf
          intro k hk
          have := congrArg Subtype.val (Equiv.ext_iff.1 h ⟨(k, true), hk, rfl⟩)
          rw [hφ] at this
          exact this
        · intro h
          exact Equiv.ext fun x => Subtype.ext (hK g' h x)
      have hrange : Nat.card φ.range = 360 := by
        rw [← Subgroup.index_ker, hker, hidx']
      have hperm : Nat.card (Perm {ω : Om // isO6 ω.1 = true ∧ ω.2 = true}) = 720 := by
        rw [Nat.card_perm, card_Z6]
        decide
      have hidx2 : φ.range.index = 2 := by
        have := Subgroup.card_mul_index φ.range
        rw [hrange, hperm] at this
        omega
      have halt := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx2
      obtain ⟨t, ht⟩ := hw 2
      have hφt : φ t = tau6.subtypePerm tau6_iff := by
        refine Equiv.ext fun x => Subtype.ext ?_
        obtain ⟨⟨k, b⟩, hk, hb⟩ := x
        simp only at hk hb
        subst hb
        show t • ((k, true) : Om) = tau6 (k, true)
        rw [ht k true, tau6_eq k hk]
      have hmem : φ t ∈ alternatingGroup {ω : Om // isO6 ω.1 = true ∧ ω.2 = true} := by
        rw [← halt]
        exact ⟨t, rfl⟩
      rw [Perm.mem_alternatingGroup, hφt, Perm.sign_subtypePerm _ _ tau6_supp, sign_tau6] at hmem
      exact absurd hmem (by decide)

end Count

theorem not_smul_eq_O6 {N : Type*} [Group N] (act : N → Om → Om) (act_one : ∀ ω, act 1 ω = ω)
    (act_mul : ∀ g h ω, act (g * h) ω = act g (act h ω))
    (hw : ∀ j : Fin 11, ∃ g : N, ∀ k b, act g (k, b) = (piTab j k, b))
    (K S : Subgroup N) (hK : ∀ k ∈ K, ∀ ω : Om, act k ω = ω)
    (hKf : ∀ g : N, (∀ i : Fin 16, isO6 i = true → act g (i, true) = (i, true)) → g ∈ K)
    (hS : ∀ g : N, g ∈ S ↔ act g (0, true) = (0, true)) (hidx : K.index = 36 * S.index)
    (hone : ∀ g : N, act g (0, false) = (0, false))
    (hz : ∀ g : N, (act g (0, true)).2 = true)
    (hzw : ∃ g : N, act g (0, true) = (5, true))
    (g : N) (i : Fin 16) (hi : isO6 i = true) : act g (5, false) ≠ (i, false) := by
  letI : MulAction N Om := { smul := act, one_smul := act_one, mul_smul := act_mul }
  have hS' : S = stabilizer N ((0, true) : Om) := by
    ext g'
    exact hS g'
  subst hS'
  exact not_smul_eq_O6_aux hw K hK hKf hidx hone hz hzw g i hi

end CFSG.OddStandard.AltStdSmall4.Fus.P42
