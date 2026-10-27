module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.AbelianTransitive
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open Equiv MulAction

theorem fixedPoints_ne_univ_of_ne_bot_bound {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {D : Subgroup G} (hD : D ≠ ⊥) : MulAction.fixedPoints D (Fin n) ≠ Set.univ := by
  intro hfix
  apply hD
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  apply Subtype.ext
  apply Equiv.ext
  intro i
  have hi : i ∈ MulAction.fixedPoints D (Fin n) := by
    rw [hfix]
    exact Set.mem_univ i
  have h := MulAction.mem_fixedPoints.mp hi ⟨x, hx⟩
  simp only [Subgroup.coe_one, Equiv.Perm.one_apply]
  exact h

theorem eq_bot_of_normal_solvable_of_bound {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPreprimitive G (Fin n)] (S : Subgroup G) [S.Normal] [Group.IsSolvable S]
    (hG : ∀ A : Subgroup (Equiv.Perm (Fin n)), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ i j : Fin n, ∃ a ∈ A, a i = j) → Nat.card A * Nat.card (MulAut A) < Nat.card G) :
    S = ⊥ := by
  classical
  by_contra hS
  have hex : ∃ n, derivedSeries S n = ⊥ := Group.IsSolvable.solvable
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hS
    have hbot : derivedSeries S 0 = ⊥ := by
      have := Nat.find_spec hex
      rwa [h0] at this
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have h1 : (⟨x, hx⟩ : S) ∈ derivedSeries S 0 := Subgroup.mem_top _
    rw [hbot, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero hm0
  have hkne : derivedSeries S k ≠ ⊥ := fun h =>
    Nat.find_min hex (show k < Nat.find hex by omega) h
  have hkbot : derivedSeries S (k + 1) = ⊥ := by
    rw [← hk]
    exact Nat.find_spec hex
  have hcommS : ∀ x ∈ derivedSeries S k, ∀ y ∈ derivedSeries S k, x * y = y * x := by
    intro x hx y hy
    have hmem := Subgroup.commutator_mem_commutator hx hy
    rw [← derivedSeries_succ, hkbot, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  obtain ⟨D, hDdef⟩ : ∃ D : Subgroup G, D = (derivedSeries S k).map S.subtype := ⟨_, rfl⟩
  have hDnormal : D.Normal := by
    rw [hDdef]
    infer_instance
  have hDne : D ≠ ⊥ := by
    intro h
    apply hkne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxD : S.subtype x ∈ D := by
      rw [hDdef]
      exact Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot] at hxD
    exact Subtype.ext hxD
  have hfix : MulAction.fixedPoints D (Fin n) ≠ Set.univ :=
    fixedPoints_ne_univ_of_ne_bot_bound hDne
  have hpt : MulAction.IsPretransitive D (Fin n) :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (N := D) hfix
  obtain ⟨φ, hφ⟩ : ∃ φ : S →* Equiv.Perm (Fin n), φ = G.subtype.comp S.subtype := ⟨_, rfl⟩
  have hφx : ∀ x : S, φ x = ((S.subtype x : G) : Equiv.Perm (Fin n)) := by
    intro x
    rw [hφ]
    rfl
  obtain ⟨A, hAdef⟩ : ∃ A : Subgroup (Equiv.Perm (Fin n)),
      A = (derivedSeries S k).map φ := ⟨_, rfl⟩
  have hAle : A ≤ G := by
    intro a ha
    rw [hAdef] at ha
    obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.mp ha
    rw [hφx]
    exact (S.subtype x).2
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    rw [hAdef] at ha hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hcommS x hx y hy]
  have hAtrans : ∀ i j : Fin n, ∃ a ∈ A, a i = j := by
    intro i j
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D i j
    have hgD : (g : G) ∈ (derivedSeries S k).map S.subtype := by
      rw [← hDdef]
      exact g.2
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hgD
    refine ⟨φ x, ?_, ?_⟩
    · rw [hAdef]
      exact Subgroup.mem_map_of_mem φ hx
    · rw [hφx, hxg, ← hg]
      rfl
  have hAn : (A.subgroupOf G).Normal := by
    have hAD : A.subgroupOf G = D := by
      ext g
      rw [Subgroup.mem_subgroupOf, hAdef]
      constructor
      · intro hg
        obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hg
        rw [hDdef]
        refine Subgroup.mem_map.mpr ⟨x, hx, Subtype.ext ?_⟩
        rw [hφx] at hxeq
        exact hxeq
      · intro hg
        rw [hDdef] at hg
        obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hg
        refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
        rw [hφx, hxg]
    rw [hAD]
    exact hDnormal
  have hbound := card_le_of_abelian_transitive_normal G A hAle hAn hAcomm hAtrans
  exact lt_irrefl _ (lt_of_lt_of_le (hG A hAcomm hAtrans) hbound)

theorem aschbacherSolvableCore_eq_bot_of_hom {H : Type*} [Group H] [Finite H] {n : ℕ}
    (φ : H →* Equiv.Perm (Fin n)) [MulAction.IsPreprimitive φ.range (Fin n)]
    (hG : ∀ A : Subgroup (Equiv.Perm (Fin n)), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ i j : Fin n, ∃ a ∈ A, a i = j) → Nat.card A * Nat.card (MulAut A) < Nat.card φ.range)
    (hker : IsPGroup 3 φ.ker) :
    CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 H = ⊥ := by
  classical
  obtain ⟨-, -, -, -, hgreat, -, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
      (H := H) (p := 3) Nat.prime_three
  set S := CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 H with hSdef
  obtain ⟨hnorm, hsolvS, hndvd⟩ := hgreat.1
  have hsurj : Function.Surjective φ.rangeRestrict := MonoidHom.rangeRestrict_surjective φ
  have hSn : (S.map φ.rangeRestrict).Normal := hnorm.map φ.rangeRestrict hsurj
  have hgsurj : Function.Surjective
      ((φ.rangeRestrict.comp S.subtype).codRestrict (S.map φ.rangeRestrict)
        (fun x => Subgroup.mem_map_of_mem _ x.2)) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hSsolv : Group.IsSolvable (S.map φ.rangeRestrict) :=
    Group.isSolvable_of_surjective hgsurj
  have hbot : S.map φ.rangeRestrict = ⊥ := by
    have := hSn
    have := hSsolv
    exact eq_bot_of_normal_solvable_of_bound φ.range (S.map φ.rangeRestrict) hG
  have hSker : S ≤ φ.ker := by
    intro x hx
    have hxmem : φ.rangeRestrict x ∈ S.map φ.rangeRestrict := Subgroup.mem_map_of_mem _ hx
    rw [hbot, Subgroup.mem_bot] at hxmem
    rw [MonoidHom.mem_ker]
    have := congrArg Subtype.val hxmem
    simpa using this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hker
  have hdvd : Nat.card S ∣ 3 ^ k := hk ▸ Subgroup.card_dvd_of_le hSker
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  rcases i with _ | j
  · exact Subgroup.eq_bot_of_card_eq (H := S) (by simpa using hi)
  · exfalso
    apply hndvd
    rw [hi]
    exact dvd_pow_self 3 (Nat.succ_ne_zero j)

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
