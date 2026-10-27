module

public import CFSG.LocalAnalysis.OddStandard.ThmCO2A8Quot

public section

namespace CFSG.OddStandard.ThmC.O2.A8

open CFSG Subgroup

section Counting

variable {K : Type} [Group K] [Finite K] {A : Type} [Group A] [Finite A]
  {ρ : K →* MulAut A} {V : Sylow 2 K} {Z : Subgroup A}

omit [Finite K] [Finite A] in
theorem tr_rho_mul (k l : K) (a : A) : ρ (k * l) a = ρ k (ρ l a) := by
  rw [map_mul, MulAut.mul_apply]

omit [Finite K] [Finite A] in
theorem tr_rho_one (a : A) : ρ 1 a = a := by
  rw [map_one, MulAut.one_apply]

omit [Finite K] [Finite A] in
theorem tr_rho_inv (k : K) (a : A) : ρ k⁻¹ (ρ k a) = a := by
  rw [← tr_rho_mul, inv_mul_cancel, tr_rho_one]

omit [Finite K] [Finite A] in
theorem tr_card_Zne (h : Hyp ρ V Z) : Nat.card {z : A // z ∈ Z ∧ z ≠ 1} = 3 := by
  have h1 : {z : A | z ∈ Z ∧ z ≠ 1} = (Z : Set A) \ {1} := by
    ext z
    simp
  rw [show Nat.card {z : A // z ∈ Z ∧ z ≠ 1} = Set.ncard {z : A | z ∈ Z ∧ z ≠ 1} from rfl, h1,
    Set.ncard_sdiff_singleton_of_mem (by exact Z.one_mem)]
  have h4 : Set.ncard (Z : Set A) = 4 := h.cardZ
  omega

omit [Finite K] [Finite A] in
theorem tr_card_ne1 (h : Hyp ρ V Z) : Nat.card {a : A // a ≠ 1} = 15 := by
  have h1 : {a : A | a ≠ 1} = (Set.univ : Set A) \ {1} := by
    ext a
    simp
  rw [show Nat.card {a : A // a ≠ 1} = Set.ncard {a : A | a ≠ 1} from rfl, h1,
    Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, h.cardA]

theorem tr_partition (h : Hyp ρ V Z) (a : A) (ha : a ≠ 1) :
    ∃ g : K, ∃ z ∈ Z, z ≠ 1 ∧ ρ g z = a := by
  classical
  let g : Sylow 2 K → K := fun W => Classical.choose (MulAction.exists_smul_eq K V W)
  have hg : ∀ W, g W • V = W := fun W => Classical.choose_spec (MulAction.exists_smul_eq K V W)
  let φ : Sylow 2 K × {z : A // z ∈ Z ∧ z ≠ 1} → {a : A // a ≠ 1} := fun p =>
    ⟨ρ (g p.1) p.2.1, fun h1 => p.2.2.2 ((ρ (g p.1)).injective (h1.trans (map_one _).symm))⟩
  have hinj : Function.Injective φ := by
    rintro ⟨W, z, hzZ, hz1⟩ ⟨W', z', hzZ', hz1'⟩ hφ
    have hφ' : ρ (g W) z = ρ (g W') z' := congrArg Subtype.val hφ
    by_cases hWW : W = W'
    · subst hWW
      have hzz : z = z' := (ρ (g W)).injective hφ'
      subst hzz
      rfl
    · exfalso
      have hk : (g W)⁻¹ * g W' ∉ normalizer ((V : Subgroup K) : Set K) := by
        intro hmem
        apply hWW
        have h1 : ((g W)⁻¹ * g W') • V = V := Sylow.smul_eq_iff_mem_normalizer.2 hmem
        rw [mul_smul, inv_smul_eq_iff, hg W', hg W] at h1
        exact h1.symm
      refine hz1 (h.fixer_unique hk hzZ ?_)
      refine ⟨z', hzZ', ?_⟩
      show ρ ((g W)⁻¹ * g W') z' = z
      rw [tr_rho_mul, ← hφ', tr_rho_inv]
  have hbij : Function.Bijective φ := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_prod, h.card_sylow, tr_card_Zne h, tr_card_ne1 h]
  obtain ⟨⟨W, z⟩, hz⟩ := hbij.2 ⟨a, ha⟩
  exact ⟨g W, z.1, z.2.1, z.2.2, congrArg Subtype.val hz⟩

omit [Finite K] in
theorem tr_Z_elems (h : Hyp ρ V Z) {s t : A} (hs : s ∈ Z) (ht : t ∈ Z) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) (hst : s ≠ t) (w : A) (hw : w ∈ Z) :
    w = 1 ∨ w = s ∨ w = t ∨ w = s * t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hw1, hws, hwt, hwst⟩ := hcon
  have hss : s * s = 1 := h.sq s
  have hst1 : s * t ≠ 1 := fun e => hst (mul_left_cancel (e.trans hss.symm)).symm
  have hsts : s * t ≠ s := fun e => ht1 (by simpa using e)
  have hstt : s * t ≠ t := fun e => hs1 (by simpa using e)
  have hsub : ({1, s, t, s * t, w} : Set A) ⊆ (Z : Set A) := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact Z.one_mem
    · exact hs
    · exact ht
    · exact Z.mul_mem hs ht
    · exact hw
  have h1 : (1 : A) ∉ ({s, t, s * t, w} : Set A) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hs1.symm, ht1.symm, hst1.symm, hw1.symm⟩
  have h2 : s ∉ ({t, s * t, w} : Set A) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hst, hsts.symm, hws.symm⟩
  have h3 : t ∉ ({s * t, w} : Set A) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hstt.symm, hwt.symm⟩
  have h4 : s * t ∉ ({w} : Set A) := by
    simp only [Set.mem_singleton_iff]
    exact hwst.symm
  have hcard : ({1, s, t, s * t, w} : Set A).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_insert_of_notMem h3, Set.ncard_insert_of_notMem h4, Set.ncard_singleton]
  have hle := Set.ncard_le_ncard hsub
  have hZ4 : (Z : Set A).ncard = 4 := h.cardZ
  omega

theorem tr_odd (h : Hyp ρ V Z) {x : K} (hx : x ∈ normalizer ((V : Subgroup K) : Set K))
    {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1) :
    (∀ z ∈ Z, ρ x z = z) ∨ ∀ z₁ ∈ Z, z₁ ≠ 1 → ∀ z₂ ∈ Z, z₂ ≠ 1 →
      ∃ n ∈ normalizer ((V : Subgroup K) : Set K), ρ n z₁ = z₂ := by
  by_cases htriv : ∀ z ∈ Z, ρ x z = z
  · exact Or.inl htriv
  right
  push Not at htriv
  obtain ⟨t, htZ, htne⟩ := htriv
  have hstab : ∀ a ∈ Z, ρ x a ∈ Z := (h.stab_iff x).2 hx
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact htne (map_one (ρ x))
  have huZ : ρ x t ∈ Z := hstab t htZ
  have hu1 : ρ x t ≠ 1 := fun e => ht1 ((ρ x).injective (e.trans (map_one (ρ x)).symm))
  have hvZ : ρ x (ρ x t) ∈ Z := hstab _ huZ
  have hcases := tr_Z_elems h htZ huZ ht1 hu1 (Ne.symm htne) (ρ x (ρ x t)) hvZ
  rcases hcases with h1 | h1 | h1 | hv
  · exact absurd ((ρ x).injective (h1.trans (map_one (ρ x)).symm)) hu1
  · exfalso
    have hxx : ρ (x * x) t = t := by
      rw [tr_rho_mul]
      exact h1
    have hpow : ∀ n : ℕ, ρ ((x * x) ^ n) t = t := by
      intro n
      induction n with
      | zero => rw [pow_zero]; exact tr_rho_one t
      | succ n ih => rw [pow_succ, tr_rho_mul, hxx, ih]
    obtain ⟨j, rfl⟩ := hm
    have hx' : (x * x) ^ (j + 1) = x := by
      rw [← pow_two, ← pow_mul, show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ, hxm,
        one_mul]
    apply htne
    have := hpow (j + 1)
    rwa [hx'] at this
  · exact absurd ((ρ x).injective h1) htne
  · have hO : ∀ z ∈ Z, z ≠ 1 → ∃ n ∈ normalizer ((V : Subgroup K) : Set K), ρ n t = z := by
      intro z hzZ hz1
      rcases tr_Z_elems h htZ huZ ht1 hu1 (Ne.symm htne) z hzZ with h1 | h1 | h1 | h1
      · exact absurd h1 hz1
      · rw [h1]
        exact ⟨1, Subgroup.one_mem _, tr_rho_one t⟩
      · rw [h1]
        exact ⟨x, hx, rfl⟩
      · rw [h1]
        refine ⟨x * x, Subgroup.mul_mem _ hx hx, ?_⟩
        rw [tr_rho_mul]
        exact hv
    intro z₁ hz₁ hz₁1 z₂ hz₂ hz₂1
    obtain ⟨n₁, hn₁, rfl⟩ := hO z₁ hz₁ hz₁1
    obtain ⟨n₂, hn₂, rfl⟩ := hO z₂ hz₂ hz₂1
    exact ⟨n₂ * n₁⁻¹, Subgroup.mul_mem _ hn₂ (Subgroup.inv_mem _ hn₁),
      by rw [tr_rho_mul, tr_rho_inv]⟩

theorem tr_prod (h : Hyp ρ V Z) {g : K} (hg : g ∉ normalizer ((V : Subgroup K) : Set K))
    (a : A) : ∃ z ∈ Z, ∃ w ∈ Z, a = z * ρ g w := by
  let Φ : Z × Z → A := fun p => p.1.1 * ρ g p.2.1
  have hinj : Function.Injective Φ := by
    rintro ⟨⟨z, hz⟩, ⟨w, hw⟩⟩ ⟨⟨z', hz'⟩, ⟨w', hw'⟩⟩ hΦ
    have hΦ' : z * ρ g w = z' * ρ g w' := hΦ
    have hd : z'⁻¹ * z = ρ g (w' * w⁻¹) := by
      rw [map_mul, map_inv, eq_mul_inv_iff_mul_eq, mul_assoc, hΦ', inv_mul_cancel_left]
    have h1 : z'⁻¹ * z = 1 :=
      h.fixer_unique hg (Z.mul_mem (Z.inv_mem hz') hz)
        ⟨w' * w⁻¹, Z.mul_mem hw' (Z.inv_mem hw), hd.symm⟩
    have hzz : z = z' := (inv_mul_eq_one.1 h1).symm
    subst hzz
    have hww : w = w' := (ρ g).injective (mul_left_cancel hΦ')
    subst hww
    rfl
  have hbij : Function.Bijective Φ := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_prod, h.cardA, h.cardZ]
  obtain ⟨⟨⟨z, hz⟩, ⟨w, hw⟩⟩, hzw⟩ := hbij.2 a
  exact ⟨z, hz, w, hw, hzw.symm⟩

theorem tr_fix_all (h : Hyp ρ V Z) {x g : K} (hg : g ∉ normalizer ((V : Subgroup K) : Set K))
    (hx : ∀ z ∈ Z, ρ x z = z) (hy : ∀ z ∈ Z, ρ (g⁻¹ * x * g) z = z) : x = 1 := by
  apply h.inj
  rw [map_one]
  ext a
  obtain ⟨z, hz, w, hw, rfl⟩ := tr_prod h hg a
  show ρ x (z * ρ g w) = z * ρ g w
  rw [map_mul, hx z hz, ← tr_rho_mul]
  have hxg : x * g = g * (g⁻¹ * x * g) := by group
  rw [hxg, tr_rho_mul, hy w hw]

theorem tr_three_cycle (p : Fin 5) :
    ∃ (c : Equiv.Perm (Fin 5)) (r : Fin 5), Equiv.Perm.sign c = 1 ∧ c ≠ 1 ∧ c ^ 3 = 1 ∧
      r ≠ p ∧ c p = p ∧ c r = r := by
  revert p
  decide +kernel

theorem tr_exists_x (h : Hyp ρ V Z) :
    ∃ (x g : K) (m : ℕ), x ∈ normalizer ((V : Subgroup K) : Set K) ∧
      g⁻¹ * x * g ∈ normalizer ((V : Subgroup K) : Set K) ∧
      g ∉ normalizer ((V : Subgroup K) : Set K) ∧ x ≠ 1 ∧ Odd m ∧ x ^ m = 1 := by
  obtain ⟨e, f, hsurj, hodd, hact, -⟩ := h.quot_A5
  obtain ⟨c, r, hcs, hc1, hc3, hrp, hcp, hcr⟩ := tr_three_cycle (e V)
  have hcA : c ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 hcs
  obtain ⟨x, hx⟩ := hsurj ⟨c, hcA⟩
  have hfx : (f x : Equiv.Perm (Fin 5)) = c := congrArg Subtype.val hx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K V (e.symm r)
  have hxV : x • V = V := by
    apply e.injective
    rw [hact, hfx, hcp]
  have hxg : x • (g • V) = g • V := by
    rw [hg]
    apply e.injective
    rw [hact, hfx, Equiv.apply_symm_apply, hcr]
  refine ⟨x, g, 3 * Nat.card f.ker, Sylow.smul_eq_iff_mem_normalizer.1 hxV, ?_, ?_, ?_, ?_, ?_⟩
  · apply Sylow.smul_eq_iff_mem_normalizer.1
    rw [mul_assoc, mul_smul, mul_smul, hxg, inv_smul_smul]
  · intro hgN
    have h1 : g • V = V := Sylow.smul_eq_iff_mem_normalizer.2 hgN
    rw [hg] at h1
    apply hrp
    rw [← h1, Equiv.apply_symm_apply]
  · intro hx1
    apply hc1
    rw [← hfx, hx1, map_one]
    rfl
  · exact Odd.mul ⟨1, rfl⟩ hodd
  · have hx3 : x ^ 3 ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_pow, hx]
      apply Subtype.ext
      exact hc3
    have h2 : (⟨x ^ 3, hx3⟩ : f.ker) ^ Nat.card f.ker = 1 := pow_card_eq_one'
    have h3 := congrArg Subtype.val h2
    simpa [pow_mul] using h3

theorem tr_Ntrans (h : Hyp ρ V Z) :
    ∀ z₁ ∈ Z, z₁ ≠ 1 → ∀ z₂ ∈ Z, z₂ ≠ 1 →
      ∃ n ∈ normalizer ((V : Subgroup K) : Set K), ρ n z₁ = z₂ := by
  obtain ⟨x, g, m, hxN, hyN, hgN, hx1, hm, hxm⟩ := tr_exists_x h
  have hym : (g⁻¹ * x * g) ^ m = 1 := by
    rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hxm]
    simp
  rcases tr_odd h hxN hm hxm with hxt | htr
  · rcases tr_odd h hyN hm hym with hyt | htr
    · exact absurd (tr_fix_all h hgN hxt hyt) hx1
    · exact htr
  · exact htr

theorem Hyp.transitive (h : Hyp ρ V Z) :
    ∀ u v : A, u ≠ 1 → v ≠ 1 → ∃ k : K, ρ k u = v := by
  intro u v hu hv
  obtain ⟨g₁, z₁, hz₁, hz₁1, rfl⟩ := tr_partition h u hu
  obtain ⟨g₂, z₂, hz₂, hz₂1, rfl⟩ := tr_partition h v hv
  obtain ⟨n, -, hn⟩ := tr_Ntrans h z₁ hz₁ hz₁1 z₂ hz₂ hz₂1
  refine ⟨g₂ * n * g₁⁻¹, ?_⟩
  rw [tr_rho_mul, tr_rho_mul, tr_rho_inv, hn]

end Counting

end CFSG.OddStandard.ThmC.O2.A8
