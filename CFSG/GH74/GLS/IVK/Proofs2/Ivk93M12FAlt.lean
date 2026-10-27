module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Leaves

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Equiv

namespace Ivk93M12FAlt

theorem false_of_card {J : Type} [Group J] [Finite J] {y : J} (hD : Ivk93M12Data J y) {a m : ℕ}
    (hm : Odd m) (h : Nat.card J = 2 ^ a * m) (h3 : a ≠ 3) (h5 : a ≠ 5) (h6 : a ≠ 6) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 J) := inferInstance
  have hS := Sylow.card_eq_multiplicity S
  have hfac : (Nat.card J).factorization 2 = a := by
    rw [h, Nat.factorization_def _ Nat.prime_two, padicValNat.mul (by positivity) hm.pos.ne',
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by have := Nat.odd_iff.1 hm; omega),
      add_zero]
  rw [hfac] at hS
  rcases hD.sylow_card S with h8 | h32 | h64
  · rw [hS] at h8
    exact h3 (Nat.pow_right_injective (le_refl 2) (h8.trans (by norm_num : (8 : ℕ) = 2 ^ 3)))
  · rw [hS] at h32
    exact h5 (Nat.pow_right_injective (le_refl 2) (h32.trans (by norm_num : (32 : ℕ) = 2 ^ 5)))
  · rw [hS] at h64
    exact h6 (Nat.pow_right_injective (le_refl 2) (h64.trans (by norm_num : (64 : ℕ) = 2 ^ 6)))

theorem false_of_injective {J : Type} [Group J] [Finite J] {y : J} (hD : Ivk93M12Data J y)
    {H : Type} [Group H] [Finite H] (f : H →* J) (hf : Function.Injective f)
    (hc : ∀ a b : H, a * b = b * a) (h2 : ∀ a : H, a ^ 2 = 1) (hcard : 9 ≤ Nat.card H) : False := by
  have hle := hD.elemAbelian_le f.range
    (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul, hc])
    (by
      rintro _ ⟨a, rfl⟩
      rw [← map_pow, h2, map_one])
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv] at hle
  omega

theorem exists_elemAbelian_sixteen {G : Type} [Group G] [Finite G] (a b c d : G)
    (hab : a * b = b * a) (hac : a * c = c * a) (had : a * d = d * a) (hbc : b * c = c * b)
    (hbd : b * d = d * b) (hcd : c * d = d * c) (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hd : d * d = 1)
    (hnodup : [1, a, b, a * b, c, a * c, b * c, a * b * c, d, a * d, b * d, a * b * d, c * d,
      a * c * d, b * c * d, a * b * c * d].Nodup) :
    ∃ E : Subgroup G, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ 2 = 1) ∧
      16 ≤ Nat.card E := by
  have hS : ({a, b, c, d} : Set G).Pairwise Commute := by
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hxy
        | assumption
        | exact Eq.symm ‹_›
  have hcomm := Subgroup.isMulCommutative_closure hS
  set E : Subgroup G := Subgroup.closure ({a, b, c, d} : Set G) with hE
  have hcomm' : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => setLike_mul_comm hx hy
  refine ⟨E, hcomm', ?_, ?_⟩
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simpa [pow_two]
    | one => simp
    | mul x y hx hy hx2 hy2 =>
      rw [Commute.mul_pow (hcomm' x hx y hy), hx2, hy2, one_mul]
    | inv x hx hx2 => rw [inv_pow, hx2, inv_one]
  · have ha' : a ∈ E := Subgroup.subset_closure (by simp)
    have hb' : b ∈ E := Subgroup.subset_closure (by simp)
    have hc' : c ∈ E := Subgroup.subset_closure (by simp)
    have hd' : d ∈ E := Subgroup.subset_closure (by simp)
    have hmem : ∀ x ∈ [1, a, b, a * b, c, a * c, b * c, a * b * c, d, a * d, b * d, a * b * d,
        c * d, a * c * d, b * c * d, a * b * c * d], x ∈ E := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
      · exact one_mem _
      · exact ha'
      · exact hb'
      · exact mul_mem ha' hb'
      · exact hc'
      · exact mul_mem ha' hc'
      · exact mul_mem hb' hc'
      · exact mul_mem (mul_mem ha' hb') hc'
      · exact hd'
      · exact mul_mem ha' hd'
      · exact mul_mem hb' hd'
      · exact mul_mem (mul_mem ha' hb') hd'
      · exact mul_mem hc' hd'
      · exact mul_mem (mul_mem ha' hc') hd'
      · exact mul_mem (mul_mem hb' hc') hd'
      · exact mul_mem (mul_mem (mul_mem ha' hb') hc') hd'
    let f : Fin 16 → E := fun i =>
      ⟨_, hmem _ (List.getElem_mem (l := [1, a, b, a * b, c, a * c, b * c, a * b * c, d, a * d,
        b * d, a * b * d, c * d, a * c * d, b * c * d, a * b * c * d]) (n := i.1) (by simp))⟩
    have hf : Function.Injective f := by
      intro i j hij
      have := congrArg Subtype.val hij
      exact Fin.ext (List.Nodup.getElem_inj_iff hnodup |>.1 this)
    simpa using Nat.card_le_card_of_injective f hf

theorem pow_two_eq_one_of_sylow {J : Type} [Group J] [Finite J] {a m : ℕ} (hm : Odd m)
    (h : Nat.card J = 2 ^ a * m) {E : Subgroup J} (hE : Nat.card E = 2 ^ a)
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) {x : J} (hx : x ^ 4 = 1) : x ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (Nat.card J).factorization 2 = a := by
    rw [h, Nat.factorization_def _ Nat.prime_two, padicValNat.mul (by positivity) hm.pos.ne',
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by have := Nat.odd_iff.1 hm; omega),
      add_zero]
  obtain ⟨S', hS'⟩ := (IsPGroup.of_card hE).exists_le_sylow
  have hS'card : Nat.card (S' : Subgroup J) = 2 ^ a := by
    rw [Sylow.card_eq_multiplicity, hfac]
  have hES : E = S' := Subgroup.eq_of_le_of_card_ge hS' (by rw [hE, hS'card])
  have hxp : IsPGroup 2 (Subgroup.zpowers x) := by
    have h4 : orderOf x ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by norm_num; exact hx)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨S, hS⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J S' S
  have hxS : x ∈ (S : Subgroup J) := hS (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxS
  have hxE : g⁻¹ * x * g ∈ E := by
    rw [hES]
    simpa using hxS
  have h2 := hE2 _ hxE
  have h3 : (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by
    have := conj_pow (a := g⁻¹) (b := x) (i := 2)
    simpa using this
  rw [h3] at h2
  have h4 : x ^ 2 = g * (g⁻¹ * x ^ 2 * g) * g⁻¹ := by group
  rw [h4, h2]
  group

theorem exists_elemAbelian_alt (n : ℕ) (hn : n = 8 ∨ n = 9) :
    ∃ E : Subgroup (alternatingGroup (Fin n)), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      (∀ x ∈ E, x ^ 2 = 1) ∧ 16 ≤ Nat.card E := by
  rcases hn with rfl | rfl
  · exact exists_elemAbelian_sixteen (G := alternatingGroup (Fin 8))
      ⟨swap 0 1 * swap 2 3, by simp [Perm.mem_alternatingGroup, Perm.sign_mul]⟩
      ⟨swap 0 2 * swap 1 3, by simp [Perm.mem_alternatingGroup, Perm.sign_mul]⟩
      ⟨swap 4 5 * swap 6 7, by simp [Perm.mem_alternatingGroup, Perm.sign_mul]⟩
      ⟨swap 4 6 * swap 5 7, by simp [Perm.mem_alternatingGroup, Perm.sign_mul]⟩
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact exists_elemAbelian_sixteen (G := alternatingGroup (Fin 9))
      ⟨swap 0 1 * swap 2 3, by simp [Perm.mem_alternatingGroup, Perm.sign_mul]⟩
      ⟨swap 0 2 * swap 1 3, by simp [Perm.mem_alternatingGroup, Perm.sign_mul]⟩
      ⟨swap 4 5 * swap 6 7, by simp [Perm.mem_alternatingGroup, Perm.sign_mul]⟩
      ⟨swap 4 6 * swap 5 7, by simp [Perm.mem_alternatingGroup, Perm.sign_mul]⟩
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)

theorem nat_card_alternatingGroup_fin (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

end Ivk93M12FAlt

open Ivk93M12FAlt in
theorem ivk93m12_alt : ∀ m : ℕ, 7 ≤ m → m ≤ 11 →
    Ivk93M12Empty (fun X _ => Nonempty (X ≃* alternatingGroup (Fin m))) := by
  intro m h7 h11 J _ _ hJ y hD
  obtain ⟨e⟩ := hJ
  have hcard : Nat.card J = m.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv]
    exact nat_card_alternatingGroup_fin m (by omega)
  interval_cases m
  · obtain ⟨E, -, -, hE2, hEc⟩ := hD.elemAbelian_cent
    have h2520 : Nat.card J = 2 ^ 3 * 315 := by
      rw [hcard]
      norm_num [Nat.factorial]
    let x : alternatingGroup (Fin 7) :=
      ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, by
        simp [Perm.mem_alternatingGroup, Perm.sign_mul]⟩
    have hx4 : x ^ 4 = 1 := by decide
    have hx2 : x ^ 2 ≠ 1 := by decide
    have h4 : (e.symm x) ^ 4 = 1 := by rw [← map_pow, hx4, map_one]
    refine hx2 (e.symm.injective ?_)
    rw [map_pow, map_one]
    exact pow_two_eq_one_of_sylow (by decide) h2520 (E := E) (by rw [hEc]; norm_num) hE2 h4
  · obtain ⟨E, hEc, hE2, hE16⟩ := exists_elemAbelian_alt 8 (Or.inl rfl)
    exact false_of_injective hD (e.symm.toMonoidHom.comp E.subtype)
      (e.symm.injective.comp E.subtype_injective) (fun a b => Subtype.ext (hEc a a.2 b b.2))
      (fun a => Subtype.ext (by simpa using hE2 a a.2)) (by omega)
  · obtain ⟨E, hEc, hE2, hE16⟩ := exists_elemAbelian_alt 9 (Or.inr rfl)
    exact false_of_injective hD (e.symm.toMonoidHom.comp E.subtype)
      (e.symm.injective.comp E.subtype_injective) (fun a b => Subtype.ext (hEc a a.2 b b.2))
      (fun a => Subtype.ext (by simpa using hE2 a a.2)) (by omega)
  · exact false_of_card hD (a := 7) (m := 14175) (by decide)
      (by rw [hcard]; norm_num [Nat.factorial]) (by norm_num) (by norm_num) (by norm_num)
  · exact false_of_card hD (a := 7) (m := 155925) (by decide)
      (by rw [hcard]; norm_num [Nat.factorial]) (by norm_num) (by norm_num) (by norm_num)

end CFSG.GH74.GLS.IVK.Proofs2
