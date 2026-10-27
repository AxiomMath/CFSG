module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.SylowColumns.CharacterSums
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFifteen.OddQuotient

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

variable {G : Type} [Group G]

section Element

theorem exists_normalizer_element_order_three [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) :
    ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
      n ^ 3 ∈ innerActing (S : Subgroup G) ∧
      ∀ z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, z ≠ 1 →
        n * z * n⁻¹ ≠ z := by
  classical
  obtain ⟨hRn, -, hd, hloc⟩ := lyons_unitary_four_normalizer_odd_quotient hnonab hT S U hSU
  set Sg := (S : Subgroup G) with hSg
  set N := Subgroup.normalizer (Sg : Set G) with hN
  set R := Sg ⊔ Subgroup.centralizer (Sg : Set G) with hR
  set R' := R.subgroupOf N with hR'
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card (N ⧸ R') := by
    rw [← Subgroup.index_eq_card]
    rcases hd with h | h <;> norm_num [h]
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨n', rfl⟩ := QuotientGroup.mk_surjective q
  have hcube : (n' : G) ^ 3 ∈ R := by
    have h : (n' : N ⧸ R') ^ 3 = 1 := by rw [← hq]; exact pow_orderOf_eq_one _
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hR', Subgroup.mem_subgroupOf] at h
    simpa using h
  have hnR : (n' : G) ∉ R := by
    intro h
    have h1 : (n' : N ⧸ R') = 1 := by
      rw [QuotientGroup.eq_one_iff, hR', Subgroup.mem_subgroupOf]
      exact h
    rw [h1, orderOf_one] at hq
    norm_num at hq
  refine ⟨n', n'.property, sup_centralizer_le_innerActing Sg hcube, ?_⟩
  intro z hz hz1 hfix
  obtain ⟨-, -, hRM, -, -, -, hidx⟩ := hloc z hz hz1
  set M := N ⊓ Subgroup.centralizer ({z} : Set G) with hM
  have hnM : (n' : G) ∈ M := by
    refine Subgroup.mem_inf.mpr ⟨n'.property, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (n' : G) * z = (n' : G) * z * (n' : G)⁻¹ * n' := by group
      _ = z * n' := by rw [hfix]
  set RM := R.subgroupOf M with hRM'
  have hRMnormal : RM.Normal := by
    constructor
    intro a ha b
    rw [hRM', Subgroup.mem_subgroupOf] at ha ⊢
    have haN : (a : G) ∈ N := (Subgroup.mem_inf.mp a.property).1
    have hbN : (b : G) ∈ N := (Subgroup.mem_inf.mp b.property).1
    have h := hRn.conj_mem ⟨a, haN⟩ (by rw [Subgroup.mem_subgroupOf]; exact ha) ⟨b, hbN⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  set nM : M := ⟨n', hnM⟩
  have hord : orderOf (nM : M ⧸ RM) = 3 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hRM', Subgroup.mem_subgroupOf]
      simpa [nM] using hcube
    · intro h
      rw [QuotientGroup.eq_one_iff, hRM', Subgroup.mem_subgroupOf] at h
      exact hnR h
  have hdvd : 3 ∣ RM.index := by
    rw [Subgroup.index_eq_card, ← hord]
    exact orderOf_dvd_natCard _
  rcases hidx with h | h <;> rw [hRM', h] at hdvd <;> norm_num at hdvd

end Element

section Cube

theorem conj_orbit_product_mem_center {S : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (S : Set G)) (h3 : n ^ 3 ∈ innerActing S)
    (hsq : ∀ x ∈ S, x ^ 2 = 1 ↔ x ∈ (Subgroup.center S).map S.subtype)
    (hsqmem : ∀ x ∈ S, x ^ 2 ∈ (Subgroup.center S).map S.subtype)
    (hcomm : (Subgroup.center S).map S.subtype = ⁅S, S⁆)
    (hfix : ∀ z ∈ (Subgroup.center S).map S.subtype, z ≠ 1 → n * z * n⁻¹ ≠ z) {x : G}
    (hx : x ∈ S) :
    x * (n⁻¹ * x * n) * ((n ^ 2)⁻¹ * x * n ^ 2) ∈ (Subgroup.center S).map S.subtype := by
  set a := n⁻¹ * x * n with ha_def
  set b := (n ^ 2)⁻¹ * x * n ^ 2 with hb_def
  have ha : a ∈ S := conj_mem_of_mem_normalizer hn hx
  have hb : b ∈ S := conj_mem_of_mem_normalizer (Subgroup.pow_mem _ hn 2) hx
  obtain ⟨s, hs, hsn⟩ := h3
  have hcube : n⁻¹ * b * n = s⁻¹ * x * s := by
    rw [← hsn x hx, hb_def]
    group
  set y := x * a * b with hy_def
  have hyS : y ∈ S := S.mul_mem (S.mul_mem hx ha) hb
  have hc : x⁻¹ * (s⁻¹ * x * s) ∈ (Subgroup.center S).map S.subtype := by
    rw [hcomm]
    have := Subgroup.commutator_mem_commutator (S.inv_mem hx) (S.inv_mem hs)
    rw [commutatorElement_def, inv_inv, inv_inv] at this
    simpa only [mul_assoc] using this
  have hcomm2 : a * b * x * (a * b)⁻¹ * x⁻¹ ∈ (Subgroup.center S).map S.subtype := by
    rw [hcomm]
    have := Subgroup.commutator_mem_commutator (S.mul_mem ha hb) hx
    rwa [commutatorElement_def] at this
  set c := x⁻¹ * (s⁻¹ * x * s) with hc_def
  have hcc : ∀ w ∈ S, c * w = w * c := fun w hw => ((mem_map_center_iff.mp hc).2 w hw).symm
  have h1 : n⁻¹ * y * n = a * b * (x * c) := by
    calc n⁻¹ * y * n = (n⁻¹ * x * n) * (n⁻¹ * a * n) * (n⁻¹ * b * n) := by
          rw [hy_def]; group
      _ = a * b * (s⁻¹ * x * s) := by
          rw [hcube, ha_def, hb_def, pow_two]; group
      _ = a * b * (x * c) := by rw [hc_def]; group
  have hw : (a * b)⁻¹ * x⁻¹ ∈ S := S.mul_mem (S.inv_mem (S.mul_mem ha hb)) (S.inv_mem hx)
  have hkey : n⁻¹ * y * n * y⁻¹ = (a * b * x * (a * b)⁻¹ * x⁻¹) * c := by
    rw [h1]
    calc a * b * (x * c) * y⁻¹ = a * b * x * (c * ((a * b)⁻¹ * x⁻¹)) := by
          rw [hy_def]; group
      _ = a * b * x * (((a * b)⁻¹ * x⁻¹) * c) := by rw [hcc _ hw]
      _ = (a * b * x * (a * b)⁻¹ * x⁻¹) * c := by group
  have hmem : n⁻¹ * y * n⁻¹⁻¹ * y⁻¹ ∈ (Subgroup.center S).map S.subtype := by
    rw [inv_inv, hkey]
    exact Subgroup.mul_mem _ hcomm2 hc
  have hfix' : ∀ z ∈ (Subgroup.center S).map S.subtype, z ≠ 1 → n⁻¹ * z * n⁻¹⁻¹ ≠ z := by
    intro z hz hz1 h
    apply hfix z hz hz1
    calc n * z * n⁻¹ = n * (n⁻¹ * z * n⁻¹⁻¹) * n⁻¹ := by rw [h]
      _ = z := by group
  exact mem_center_of_conj_mul_inv_mem hsq hsqmem hfix' hyS hmem

theorem sum_one_sub_signs {u v w : ℂ} (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1)
    (hw : w = 1 ∨ w = -1) (h : u * v * w = 1) :
    ∃ k : ℤ, (1 - u) + (1 - v) + (1 - w) = 4 * k := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
  · exact ⟨0, by norm_num⟩
  · norm_num at h
  · norm_num at h
  · exact ⟨1, by norm_num⟩
  · norm_num at h
  · exact ⟨1, by norm_num⟩
  · exact ⟨1, by norm_num⟩
  · norm_num at h

end Cube

section Orbits

theorem orbit_sign_sum {S : Subgroup G} (hshape : UnitaryFourSylowShape S) [Finite S] {n : G}
    (hn : n ∈ Subgroup.normalizer (S : Set G)) (h3 : n ^ 3 ∈ innerActing S)
    (hsq : ∀ x ∈ S, x ^ 2 = 1 ↔ x ∈ (Subgroup.center S).map S.subtype)
    (hsqmem : ∀ x ∈ S, x ^ 2 ∈ (Subgroup.center S).map S.subtype)
    (hcomm : (Subgroup.center S).map S.subtype = ⁅S, S⁆)
    (hfix : ∀ z ∈ (Subgroup.center S).map S.subtype, z ≠ 1 → n * z * n⁻¹ ≠ z)
    {θ : S → ℂ} (hθ : θ ∈ CFSG.BlocksIrr S) (h1 : θ 1 = 1) (x : S) :
    ∃ k : ℤ, ∑ a : Fin 3, (1 - conjugateCharacter S (n ^ (a : ℕ)) θ x) = 4 * k := by
  have hpow : ∀ a : ℕ, n ^ a ∈ Subgroup.normalizer (S : Set G) :=
    fun a => Subgroup.pow_mem _ hn a
  have hval : ∀ a : ℕ, conjugateCharacter S (n ^ a) θ x =
      θ ⟨(n ^ a)⁻¹ * x * n ^ a, conj_mem_of_mem_normalizer (hpow a) x.property⟩ :=
    fun a => conjugateCharacter_apply (hpow a) θ x
  have hsign : ∀ a : ℕ, conjugateCharacter S (n ^ a) θ x = 1 ∨
      conjugateCharacter S (n ^ a) θ x = -1 := by
    intro a
    rw [hval]
    exact hshape.linear_apply_eq_one_or hθ h1 _
  have hprod : conjugateCharacter S (n ^ 0) θ x * conjugateCharacter S (n ^ 1) θ x *
      conjugateCharacter S (n ^ 2) θ x = 1 := by
    rw [hval, hval, hval, ← hshape.linear_mul hθ h1, ← hshape.linear_mul hθ h1]
    apply hshape.linear_apply_center hθ h1
    have hmem := conj_orbit_product_mem_center hn h3 hsq hsqmem hcomm hfix x.property
    obtain ⟨w, hw, hweq⟩ := hmem
    have hw' : w ∈ Subgroup.center S := hw
    convert hw' using 1
    apply Subtype.ext
    have hweq' : (w : G) = (x : G) * (n⁻¹ * x * n) * ((n ^ 2)⁻¹ * x * n ^ 2) := hweq
    rw [hweq']
    simp only [Subgroup.coe_mul, pow_zero, inv_one, one_mul, mul_one, pow_one]
  obtain ⟨k, hk⟩ := sum_one_sub_signs (hsign 0) (hsign 1) (hsign 2) hprod
  refine ⟨k, ?_⟩
  rw [Fin.sum_univ_three]
  simpa using hk

end Orbits

section Data

theorem restriction_congruence_data [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) {V : Type}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    ∃ L c : ℕ, ρ.character 1 = L + 12 * c ∧
      (∀ z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, z ≠ 1 →
        ρ.character z = L - 4 * c) ∧
      ∀ x ∈ (S : Subgroup G),
        x ∉ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype →
        ∃ k : ℤ, (L : ℂ) - ρ.character x = 4 * k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Sg := (S : Subgroup G) with hSg
  obtain ⟨-, hcomm, hsq, -, -, -, -, -, -, -, -, -⟩ :=
    lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  obtain ⟨-, -, -, hsqmem₀, -⟩ := unitary_four_sylow_structure hT S U hSU
  have hsqmem : ∀ x ∈ Sg, x ^ 2 ∈ (Subgroup.center Sg).map Sg.subtype :=
    fun x hx => ⟨⟨x, hx⟩ ^ 2, hsqmem₀ ⟨x, hx⟩, rfl⟩
  have hshape := unitaryFourSylowShape_of_mulEquiv hT S U hSU
  obtain ⟨n, hn, h3, hfix⟩ := exists_normalizer_element_order_three hnonab hT S U hSU
  obtain ⟨m, hm, hminv⟩ := restriction_multiplicities Sg ρ
  have hpow : ∀ j : ℕ, n ^ j ∈ Subgroup.normalizer (Sg : Set G) :=
    fun j => Subgroup.pow_mem _ hn j
  have hφ := normalizerConj_fixedPointFree hn hfix
  set Lin := nonprincipalLinearCharacters Sg with hLin
  set Psi := degreeFourCharacters Sg with hPsi
  have hsplit : ∀ y : Sg, ρ.character y =
      m 1 + ∑ θ ∈ Lin, (m θ : ℂ) * θ y + ∑ θ ∈ Psi, (m θ : ℂ) * θ y := by
    intro y
    rw [hm y, hshape.irreducibleCharacters_eq,
      Finset.sum_insert one_not_mem_linear_union_degreeFour,
      Finset.sum_union disjoint_linear_degreeFour]
    simp only [Pi.one_apply, mul_one]
    ring
  have hPL : ∀ k ∈ Subgroup.normalizer (Sg : Set G), ∀ θ, θ ∈ Lin →
      conjugateCharacter Sg k θ ∈ Lin := by
    intro k hk θ hθ
    rw [hLin, mem_nonprincipalLinearCharacters] at hθ ⊢
    exact ⟨conjugateCharacter_mem_blocksIrr hk hθ.1,
      by rw [conjugateCharacter_apply_one hk, hθ.2.1], conjugateCharacter_ne_one hk hθ.2.2⟩
  have hPD : ∀ k ∈ Subgroup.normalizer (Sg : Set G), ∀ θ, θ ∈ Psi →
      conjugateCharacter Sg k θ ∈ Psi := by
    intro k hk θ hθ
    rw [hPsi, mem_degreeFourCharacters] at hθ ⊢
    exact ⟨conjugateCharacter_mem_blocksIrr hk hθ.1,
      by rw [conjugateCharacter_apply_one hk, hθ.2]⟩
  let σL := conjugatePerm hn (fun θ => θ ∈ Lin) (hPL n hn) (hPL n⁻¹ (inv_mem hn))
  let σD := conjugatePerm hn (fun θ => θ ∈ Psi) (hPD n hn) (hPD n⁻¹ (inv_mem hn))
  have hcube : ∀ θ ∈ CFSG.BlocksIrr Sg, conjugateCharacter Sg (n ^ 3) θ = θ :=
    fun θ hθ => conjugateCharacter_innerActing h3 θ (blocksIrr_conj hθ)
  have hσL3 : σL ^ 3 = 1 := by
    ext θ : 1
    apply Subtype.ext
    rw [conjugatePerm_pow_val, hcube _ (mem_nonprincipalLinearCharacters.mp θ.property).1]
    rfl
  have hσD3 : σD ^ 3 = 1 := by
    ext θ : 1
    apply Subtype.ext
    rw [conjugatePerm_pow_val, hcube _ (mem_degreeFourCharacters.mp θ.property).1]
    rfl
  have hσLfix : ∀ θ, σL θ ≠ θ := by
    intro θ h
    have h' := congrArg Subtype.val h
    change conjugateCharacter Sg n θ.val = θ.val at h'
    rw [conjugateCharacter_eq_comp hn] at h'
    have hθ := mem_nonprincipalLinearCharacters.mp θ.property
    exact hshape.linear_comp_ne (normalizerConj Sg hn) hφ hθ.1 hθ.2.1 hθ.2.2 h'
  have hσDfix : ∀ θ, σD θ ≠ θ := by
    intro θ h
    have h' := congrArg Subtype.val h
    change conjugateCharacter Sg n θ.val = θ.val at h'
    rw [conjugateCharacter_eq_comp hn] at h'
    have hθ := mem_degreeFourCharacters.mp θ.property
    exact hshape.degree_four_comp_ne (normalizerConj Sg hn) hφ hθ.1 hθ.2 h'
  obtain ⟨kL, repL, hbijL⟩ := exists_orbit_representatives_three σL hσL3 hσLfix
  obtain ⟨kD, repD, hbijD⟩ := exists_orbit_representatives_three σD hσD3 hσDfix
  have hkD : kD = 1 := by
    have h := Nat.card_eq_of_bijective _ hbijD
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin,
      Fintype.card_fin, Nat.card_eq_fintype_card, Fintype.card_coe,
      hshape.card_degreeFourCharacters] at h
    omega
  subst hkD
  set c := m (repD 0).val with hc
  have hmD : ∀ θ ∈ Psi, m θ = c := by
    intro θ hθ
    obtain ⟨⟨i, a⟩, hia⟩ := hbijD.2 ⟨θ, hθ⟩
    have h := congrArg Subtype.val hia
    simp only at h
    rw [conjugatePerm_pow_val] at h
    rw [← h, Subsingleton.elim i 0, hminv _ (mem_degreeFourCharacters.mp (repD 0).property).1 _
      (hpow _)]
  have hPsiSum : ∀ y : Sg, ∑ θ ∈ Psi, (m θ : ℂ) * θ y = c * ∑ θ ∈ Psi, θ y := by
    intro y
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun θ hθ => by rw [hmD θ hθ]
  have hLinSum : ∀ f : (Sg → ℂ) → ℂ, ∑ θ ∈ Lin, f θ =
      ∑ i, ∑ a : Fin 3, f (conjugateCharacter Sg (n ^ (a : ℕ)) (repL i).val) := by
    intro f
    rw [← Finset.sum_coe_sort Lin, ← hbijL.sum_comp (fun t => f t.val), Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    rw [conjugatePerm_pow_val]
  have hLin1 : ∀ y : Sg, y ∈ Subgroup.center Sg →
      ∑ θ ∈ Lin, (m θ : ℂ) * θ y = ∑ θ ∈ Lin, (m θ : ℂ) := by
    intro y hy
    exact Finset.sum_congr rfl fun θ hθ => by
      rw [hshape.linear_apply_center (mem_nonprincipalLinearCharacters.mp hθ).1
        (mem_nonprincipalLinearCharacters.mp hθ).2.1 hy, mul_one]
  refine ⟨m 1 + ∑ θ ∈ Lin, m θ, c, ?_, ?_, ?_⟩
  · have h := hsplit 1
    rw [show ((1 : Sg) : G) = 1 from rfl] at h
    rw [h, hLin1 1 (Subgroup.one_mem _), hPsiSum, hshape.sum_degreeFour, ite_eq_left rfl]
    push_cast
    ring
  · intro z hz hz1
    obtain ⟨w, hw, rfl⟩ := hz
    have hw1 : w ≠ 1 := fun h => hz1 (by rw [h]; rfl)
    have hw' : w ∈ Subgroup.center Sg := hw
    have h := hsplit w
    change ρ.character (w : G) = _
    rw [h, hLin1 w hw', hPsiSum, hshape.sum_degreeFour, ite_eq_right hw1, ite_eq_left hw']
    push_cast
    ring
  · intro x hx hxZ
    set x' : Sg := ⟨x, hx⟩ with hx'
    have hx'Z : x' ∉ Subgroup.center Sg := fun h => hxZ ⟨x', h, rfl⟩
    have hx'1 : x' ≠ 1 := fun h => hx'Z (h ▸ Subgroup.one_mem _)
    have h := hsplit x'
    rw [hPsiSum, hshape.sum_degreeFour, ite_eq_right hx'1, ite_eq_right hx'Z, mul_zero,
      add_zero] at h
    have hdiff : ((m 1 + ∑ θ ∈ Lin, m θ : ℕ) : ℂ) - ρ.character x =
        ∑ θ ∈ Lin, (m θ : ℂ) * (1 - θ x') := by
      rw [show ρ.character x = ρ.character x' from rfl, h]
      push_cast
      rw [← sub_sub, add_sub_cancel_left, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro θ _
      ring
    choose k hk using fun i : Fin kL =>
      orbit_sign_sum hshape hn h3 hsq hsqmem hcomm hfix
        (mem_nonprincipalLinearCharacters.mp (repL i).property).1
        (mem_nonprincipalLinearCharacters.mp (repL i).property).2.1 x'
    refine ⟨∑ i, (m (repL i).val : ℤ) * k i, ?_⟩
    rw [hdiff, hLinSum (fun θ => (m θ : ℂ) * (1 - θ x'))]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hconst : ∀ a : Fin 3, m (conjugateCharacter Sg (n ^ (a : ℕ)) (repL i).val) =
        m (repL i).val := fun a =>
      hminv _ (mem_nonprincipalLinearCharacters.mp (repL i).property).1 _ (hpow _)
    simp_rw [hconst]
    rw [← Finset.mul_sum, hk i]
    ring

end Data

section Node

theorem lyons_sylow_character_congruences_and_degree_bound [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) :
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ G V),
      ∀ z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, z ≠ 1 →
      ∀ x ∈ (S : Subgroup G), orderOf x = 4 →
        (∃ k : ℤ, ρ.character z = k) ∧ (∃ k : ℤ, ρ.character x = k) ∧
        (∃ m : ℕ, ρ.character 1 - ρ.character z = 16 * m) ∧
        ∃ k : ℤ, ρ.character z - ρ.character x = 4 * k) ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ G V), ρ.IsIrreducible → ρ.character ≠ 1 →
        12 ≤ Module.finrank ℂ V := by
  classical
  obtain ⟨-, -, hsq, hZcard, -, -, -, -, -, -, -, -⟩ :=
    lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  refine ⟨fun V _ _ _ ρ z hz hz1 x hx hx4 => ?_, fun V _ _ _ ρ hirr hne => ?_⟩
  · obtain ⟨L, c, h1, hz', hx'⟩ := restriction_congruence_data hnonab hT S U hSU ρ
    have hxZ : x ∉ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype := by
      intro h
      have h2 := orderOf_dvd_of_pow_eq_one ((hsq x hx).mpr h)
      rw [hx4] at h2
      norm_num at h2
    obtain ⟨k, hk⟩ := hx' x hx hxZ
    refine ⟨sylow_character_integer hT S U hSU ρ (mem_map_center_iff.mp hz).1,
      sylow_character_integer hT S U hSU ρ hx, ⟨c, ?_⟩, ⟨k - c, ?_⟩⟩
    · rw [h1, hz' z hz hz1]
      ring
    · rw [hz' z hz hz1]
      push_cast
      linear_combination hk
  · obtain ⟨L, c, h1, hz', -⟩ := restriction_congruence_data hnonab hT S U hSU ρ
    have hdeg : (Module.finrank ℂ V : ℂ) = L + 12 * c :=
      (Representation.char_one ρ).symm.trans h1
    have hdegN : Module.finrank ℂ V = L + 12 * c := by exact_mod_cast hdeg
    by_contra hlt
    push Not at hlt
    have hc0 : c = 0 := by omega
    set Z := (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype with hZ
    have hZker : Z ≤ MonoidHom.ker ρ := by
      apply le_ker_of_character_eq_degree ρ Z
      intro z hz
      by_cases hz1 : z = 1
      · rw [hz1]
      · rw [hz' z hz hz1, h1, hc0]
        push_cast
        ring
    have hZbot : Z ≠ ⊥ := by
      intro h
      have hcard : Nat.card Z = 4 := by
        rw [hZ, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hZcard]
      rw [h, Subgroup.card_bot] at hcard
      norm_num at hcard
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker ρ) with hk | hk
    · exact hZbot (le_bot_iff.mp (hk ▸ hZker))
    · apply hne
      have htriv : ∀ g : G, ρ g = 1 := by
        intro g
        have : g ∈ MonoidHom.ker ρ := by rw [hk]; exact Subgroup.mem_top g
        exact this
      let data : FiniteComplexRepresentation.{0, 0} G := { vector := V, representation := ρ }
      have hone : Module.finrank ℂ V = 1 :=
        finrank_eq_one_of_commutator_trivial data hirr (fun g h => by
          change ρ g * ρ h = ρ h * ρ g
          rw [htriv g, htriv h])
      funext g
      change LinearMap.trace ℂ V (ρ g) = 1
      rw [htriv g, LinearMap.trace_one, hone]
      norm_num

end Node

end CFSG.LyonsUnitaryFour
