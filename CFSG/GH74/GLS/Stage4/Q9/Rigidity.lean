module

public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.GroupAction.CardCommute

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Matrix
open scoped MatrixGroups

section SL

variable {F : Type*} [Field F] [Finite F]

private theorem exists_ne_zero_sq_ne_one (hF : 4 ≤ Nat.card F) : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  obtain ⟨x, hx⟩ : IsCyclic Fˣ := by infer_instance
  refine ⟨x, Units.ne_zero x, fun h ↦ ?_⟩
  grw [Nat.card_eq_card_units_add_one F, ← orderOf_eq_card_of_forall_mem_zpowers hx,
    orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at hF
  omega

theorem card_specialLinearGroup_two_nine (hF : Nat.card F = 9) : Nat.card SL(2, F) = 720 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = 9 := by rw [← Nat.card_eq_fintype_card, hF]
  rw [Matrix.card_SL_field 2, hq]
  simp [Fin.prod_univ_two]

private theorem card_center_specialLinearGroup_two_le :
    Nat.card (Subgroup.center SL(2, F)) ≤ 2 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h := Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := F) (0 : Fin 2)).toEquiv
  rw [h]
  simpa using card_rootsOfUnity F (Fintype.card (Fin 2))

private theorem sl2_nine_hom_trivial_aux (hF : Nat.card F = 9) {H : Type*} [Group H] [Finite H]
    (φ : SL(2, F) →* H) (hH : ¬ 360 ∣ Nat.card H) : φ = 1 := by
  classical
  obtain ⟨a, ha, hasq⟩ := exists_ne_zero_sq_ne_one (F := F) (by omega)
  have hperf : Group.IsPerfect SL(2, F) := ⟨Matrix.SL2.commutator_eq_top ha hasq⟩
  have hsimple : IsSimpleGroup (SL(2, F) ⧸ Subgroup.center SL(2, F)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hcardS : Nat.card SL(2, F) = 720 := card_specialLinearGroup_two_nine hF
  by_cases hNZ : φ.ker ≤ Subgroup.center SL(2, F)
  ·
    exfalso
    have h1 : Nat.card φ.ker ≤ 2 :=
      (Nat.card_le_card_of_injective (Subgroup.inclusion hNZ)
        (Subgroup.inclusion_injective hNZ)).trans card_center_specialLinearGroup_two_le
    have h2 : Nat.card φ.ker * Nat.card φ.range = 720 := by
      rw [← hcardS, ← Subgroup.index_ker, Subgroup.card_mul_index]
    have h0 : 0 < Nat.card φ.ker := Nat.card_pos
    have h3 : 360 ∣ Nat.card φ.range := by
      interval_cases hk : Nat.card φ.ker <;> omega
    exact hH (h3.trans (Subgroup.card_subgroup_dvd_card φ.range))
  ·
    set Z := Subgroup.center SL(2, F) with hZdef
    have hnormN : (φ.ker.map (QuotientGroup.mk' Z)).Normal :=
      (MonoidHom.normal_ker φ).map _ (QuotientGroup.mk'_surjective Z)
    have hmap : φ.ker.map (QuotientGroup.mk' Z) = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map (QuotientGroup.mk' Z)) with h | h
      · exfalso
        apply hNZ
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
        exact h
      · exact h
    have hsup : φ.ker ⊔ Z = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' Z) φ.ker
      rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hrange : φ.range = Z.map φ := by
      rw [MonoidHom.range_eq_map, ← hsup, Subgroup.map_sup,
        (Subgroup.map_eq_bot_iff _).mpr le_rfl, bot_sup_eq]
    have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
    have : IsMulCommutative φ.range := by
      refine ⟨⟨fun x y => ?_⟩⟩
      have hx : (x : H) ∈ Z.map φ := by rw [← hrange]; exact x.2
      have hy : (y : H) ∈ Z.map φ := by rw [← hrange]; exact y.2
      obtain ⟨z₁, hz₁, hx'⟩ := hx
      obtain ⟨z₂, hz₂, hy'⟩ := hy
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hx', ← hy', ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz₂ z₁]
    have : Subsingleton φ.range := inferInstance
    ext s
    have := Subsingleton.elim (⟨φ s, φ.mem_range.mpr ⟨s, rfl⟩⟩ : φ.range) 1
    simpa using congrArg Subtype.val this

end SL

theorem sl2_nine_hom_trivial {K : Type*} [Group K] {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 9) (e : K ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    {H : Type*} [Group H] [Finite H] (ψ : K →* H) (hH : ¬ 360 ∣ Nat.card H) : ψ = 1 := by
  have h := sl2_nine_hom_trivial_aux hF (ψ.comp e.symm.toMonoidHom) hH
  ext k
  simpa using DFunLike.congr_fun h (e k)

section Aut

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

private theorem card_dvd_of_free {P Y : Type*} [Group P] [MulAction P Y] [Finite P] [Finite Y]
    (hfree : ∀ (g : P) (y : Y), g • y = y → g = 1) : Nat.card P ∣ Nat.card Y := by
  classical
  have := Fintype.ofFinite P
  have := Fintype.ofFinite Y
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    MulAction.card_eq_sum_card_group_div_card_stabilizer P Y]
  refine Finset.dvd_sum fun ω _ => ?_
  have hstab : Fintype.card (MulAction.stabilizer P ω.out) = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨1, fun g => Subtype.ext (hfree g.1 _ g.2)⟩
  rw [hstab, Nat.div_one]

omit [Finite X] in
private theorem card_eq_sq_of_not_isCyclic (hp : p.Prime) (hX : Nat.card X ∣ p ^ 2)
    (hnc : ¬ IsCyclic X) : Nat.card X = p ^ 2 := by
  obtain ⟨k, hk, hXk⟩ := (Nat.dvd_prime_pow hp).1 hX
  interval_cases k
  · exfalso
    apply hnc
    have : Subsingleton X := (Nat.card_eq_one_iff_unique.1 (by simpa using hXk)).1
    infer_instance
  · exfalso
    apply hnc
    have : Fact p.Prime := ⟨hp⟩
    exact isCyclic_of_prime_card (by simpa using hXk)
  · exact hXk

private theorem orderOf_eq_prime_of_ne_one (hp : p.Prime) (hX : Nat.card X = p ^ 2)
    (hnc : ¬ IsCyclic X) {a : X} (ha : a ≠ 1) : orderOf a = p := by
  obtain ⟨i, hi, hia⟩ := (Nat.dvd_prime_pow hp).1 (hX ▸ orderOf_dvd_natCard a)
  interval_cases i
  · exact absurd (orderOf_eq_one_iff.1 (by simpa using hia)) ha
  · simpa using hia
  · exact absurd (isCyclic_of_orderOf_eq_card a (by rw [hia, hX])) hnc

private theorem closure_pair_eq_top (hp : p.Prime) (hX : Nat.card X = p ^ 2)
    (hnc : ¬ IsCyclic X) {a b : X} (ha : a ≠ 1) (hb : b ∉ Subgroup.zpowers a) :
    Subgroup.closure ({a, b} : Set X) = ⊤ := by
  have hord := orderOf_eq_prime_of_ne_one hp hX hnc ha
  set M := Subgroup.closure ({a, b} : Set X) with hM
  have haM : Subgroup.zpowers a ≤ M :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  have hbM : b ∈ M := Subgroup.subset_closure (by simp)
  have hdvd : Nat.card (Subgroup.zpowers a) ∣ Nat.card M := Subgroup.card_dvd_of_le haM
  rw [Nat.card_zpowers, hord] at hdvd
  obtain ⟨j, hj, hMj⟩ := (Nat.dvd_prime_pow hp).1
    (hX ▸ Subgroup.card_subgroup_dvd_card M : Nat.card M ∣ p ^ 2)
  interval_cases j
  · exfalso
    rw [pow_zero] at hMj
    exact hp.one_lt.ne' (Nat.dvd_one.1 (hMj ▸ hdvd))
  · exfalso
    apply hb
    have : Subgroup.zpowers a = M := by
      apply Subgroup.eq_of_le_of_card_ge haM
      rw [Nat.card_zpowers, hord, hMj, pow_one]
    exact this ▸ hbM
  · exact Subgroup.eq_top_of_card_eq M (by rw [hMj, hX])

private theorem card_mulAut_dvd_of_not_isCyclic (hp : p.Prime) (hX : Nat.card X = p ^ 2)
    (hnc : ¬ IsCyclic X) : Nat.card (MulAut X) ∣ (p ^ 2 - 1) * (p ^ 2 - p) := by
  classical
  let Ω : Type _ := {x : X × X // x.1 ≠ 1 ∧ x.2 ∉ Subgroup.zpowers x.1}
  let _ : MulAction (MulAut X) Ω :=
    { smul := fun φ ω => ⟨(φ ω.1.1, φ ω.1.2), by
        refine ⟨fun h => ω.2.1 (φ.injective (h.trans (map_one φ).symm)), fun h => ω.2.2 ?_⟩
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h
        rw [← map_zpow] at hn
        exact Subgroup.mem_zpowers_iff.2 ⟨n, φ.injective hn⟩⟩
      one_smul := fun ω => Subtype.ext rfl
      mul_smul := fun φ ψ ω => Subtype.ext rfl }
  have hfree : ∀ (φ : MulAut X) (ω : Ω), φ • ω = ω → φ = 1 := by
    intro φ ω h
    have h1 : φ ω.1.1 = ω.1.1 := congrArg (fun z : Ω => z.1.1) h
    have h2 : φ ω.1.2 = ω.1.2 := congrArg (fun z : Ω => z.1.2) h
    have htop := closure_pair_eq_top hp hX hnc ω.2.1 ω.2.2
    ext x
    have hx : x ∈ Subgroup.closure ({ω.1.1, ω.1.2} : Set X) := by rw [htop]; trivial
    have := MonoidHom.eqOn_closure (f := (φ : MulAut X).toMonoidHom) (g := MonoidHom.id X)
      (s := {ω.1.1, ω.1.2}) (by
        intro y hy
        rcases hy with rfl | rfl
        · exact h1
        · exact h2) hx
    simpa using this
  have hcard : Nat.card Ω = (p ^ 2 - 1) * (p ^ 2 - p) := by
    have : Fintype X := Fintype.ofFinite X
    have hXc : Fintype.card X = p ^ 2 := by rw [← Nat.card_eq_fintype_card, hX]
    rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun a b : X => a ≠ 1 ∧ b ∉ Subgroup.zpowers a)), Nat.card_sigma]
    have hfib : ∀ a : X, Nat.card {b : X // a ≠ 1 ∧ b ∉ Subgroup.zpowers a} =
        if a = 1 then 0 else p ^ 2 - p := by
      intro a
      by_cases ha : a = 1
      · simp [ha]
      · simp only [ha, ite_false, ne_eq, not_false_eq_true, true_and]
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, hXc]
        congr 1
        rw [← Nat.card_eq_fintype_card (α := {b : X // b ∈ Subgroup.zpowers a})]
        exact (Nat.card_zpowers a).trans (orderOf_eq_prime_of_ne_one hp hX hnc ha)
    simp_rw [hfib]
    rw [← Finset.sum_erase Finset.univ (a := (1 : X)) (by simp)]
    have hconst : ∀ x ∈ Finset.univ.erase (1 : X),
        (if x = 1 then 0 else p ^ 2 - p) = p ^ 2 - p :=
      fun x hx => by simp [Finset.ne_of_mem_erase hx]
    rw [Finset.sum_congr rfl hconst]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hXc,
      smul_eq_mul]
  rw [← hcard]
  exact card_dvd_of_free hfree

theorem card_mulAut_dvd_of_card_dvd_prime_sq (hp : p.Prime) (hX : Nat.card X ∣ p ^ 2) :
    Nat.card (MulAut X) ∣ (p ^ 2 - 1) * (p ^ 2 - p) := by
  by_cases hcyc : IsCyclic X
  · rw [IsCyclic.card_mulAut]
    obtain ⟨k, hk, hXk⟩ := (Nat.dvd_prime_pow hp).1 hX
    rw [hXk]
    interval_cases k
    · simp
    · rw [pow_one, Nat.totient_prime hp]
      have h := Nat.sub_dvd_pow_sub_pow p 1 2
      rw [one_pow] at h
      exact h.mul_right _
    · rw [Nat.totient_prime_pow hp (by norm_num)]
      have h : p ^ 2 - p = p ^ (2 - 1) * (p - 1) := by
        rw [pow_two, Nat.mul_sub_one]
        simp
      rw [← h]
      exact dvd_mul_left _ _
  · exact card_mulAut_dvd_of_not_isCyclic hp (card_eq_sq_of_not_isCyclic hp hX hcyc) hcyc

theorem card_mulAut_dvd_480 (hX : Nat.card X ∣ 25) : Nat.card (MulAut X) ∣ 480 := by
  have h := card_mulAut_dvd_of_card_dvd_prime_sq (X := X) (p := 5) Nat.prime_five
    (by simpa using hX)
  simpa using h

theorem card_mulAut_dvd_48 (hX : Nat.card X ∣ 9) : Nat.card (MulAut X) ∣ 48 := by
  have h := card_mulAut_dvd_of_card_dvd_prime_sq (X := X) (p := 3) Nat.prime_three
    (by simpa using hX)
  simpa using h

theorem not_dvd_card_mulAut_of_card_dvd (hX : Nat.card X ∣ 25 ∨ Nat.card X ∣ 9) :
    ¬ 360 ∣ Nat.card (MulAut X) := by
  intro h
  rcases hX with hX | hX
  · have := h.trans (card_mulAut_dvd_480 hX)
    omega
  · have := h.trans (card_mulAut_dvd_48 hX)
    omega

end Aut

theorem sl2_nine_centralizes_small {G : Type*} [Group G] {K X : Subgroup G} {F : Type*} [Field F]
    [Finite F] (hF : Nat.card F = 9) (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) [Finite G]
    (hnorm : ∀ k ∈ K, ∀ x ∈ X, k * x * k⁻¹ ∈ X)
    (_hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hX : Nat.card X ∣ 25 ∨ Nat.card X ∣ 9) : ∀ k ∈ K, ∀ x ∈ X, k * x = x * k := by
  have hKle : K ≤ Subgroup.normalizer (X : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hnorm k hk h hh, fun hh => ?_⟩
    have := hnorm k⁻¹ (K.inv_mem hk) _ hh
    simpa [mul_assoc] using this
  let ψ : K →* MulAut X := X.normalizerMonoidHom.comp (Subgroup.inclusion hKle)
  have hψ : ψ = 1 := sl2_nine_hom_trivial hF e ψ (not_dvd_card_mulAut_of_card_dvd hX)
  intro k hk x hx
  have h := congrArg (fun f : MulAut X => ((f ⟨x, hx⟩ : X) : G))
    (DFunLike.congr_fun hψ ⟨k, hk⟩)
  simp [ψ] at h
  exact mul_inv_eq_iff_eq_mul.1 h

end CFSG.GH74.GLS.Stage4.Q9
