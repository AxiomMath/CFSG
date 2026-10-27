module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SInnU6Diag
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SInnU6Perp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.InnU6

open CFSG.LocalAnalysis.GLTheoremA.CatB Module

theorem K4_exists_omega : ∃ ω : K4, ω ^ 2 + ω + 1 = 0 := by
  classical
  haveI : Fintype K4 := Fintype.ofFinite K4
  have hex : ∃ x : K4, x ≠ 0 ∧ x ≠ 1 := by
    by_contra h
    push_neg at h
    have hsub : (Finset.univ : Finset K4) ⊆ {0, 1} := by
      intro x _
      by_cases hx : x = 0
      · simp [hx]
      · simp [h x hx]
    have h4 : Fintype.card K4 ≤ 2 := by
      calc Fintype.card K4 = (Finset.univ : Finset K4).card := (Finset.card_univ).symm
        _ ≤ ({0, 1} : Finset K4).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    have h5 : Fintype.card K4 = 4 := by
      rw [Fintype.card_eq_nat_card]
      exact K4_card
    omega
  obtain ⟨x, hx0, hx1⟩ := hex
  refine ⟨x, ?_⟩
  have h3 := K4_pow_card_sub_one hx0
  have hmul : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.1 hmul with h | h
  · exact absurd (sub_eq_zero.1 h) hx1
  · exact h

theorem K4_two_eq_zero : (2 : K4) = 0 := by
  rw [show (2 : K4) = 1 + 1 by norm_num]
  exact CharTwo.add_self_eq_zero (1 : K4)

theorem cube_root_mem {ω c : K4} (hω : ω ^ 2 + ω + 1 = 0) (hc : c ^ 3 = 1) :
    c = 1 ∨ c = ω ∨ c = ω ^ 2 := by
  have h1 : (c - 1) * (c ^ 2 + c + 1) = 0 := by linear_combination hc
  rcases mul_eq_zero.1 h1 with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · have h2 : (c - ω) * (c - ω ^ 2) = 0 := by
      linear_combination h + (ω - 1 - c) * hω
    rcases mul_eq_zero.1 h2 with h' | h'
    · exact Or.inr (Or.inl (sub_eq_zero.1 h'))
    · exact Or.inr (Or.inr (sub_eq_zero.1 h'))

theorem hermF_add_left (x y z : Fin 6 → K4) : hermF (x + y) z = hermF x z + hermF y z := by
  unfold hermF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, CharTwo.add_sq, add_mul]

theorem hermF_sum_left {ι : Type*} (s : Finset ι) (g : ι → Fin 6 → K4) (z : Fin 6 → K4) :
    hermF (∑ i ∈ s, g i) z = ∑ i ∈ s, hermF (g i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermF]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hermF_add_left, ih]

theorem hermF_sum_right {ι : Type*} (s : Finset ι) (z : Fin 6 → K4) (g : ι → Fin 6 → K4) :
    hermF z (∑ i ∈ s, g i) = ∑ i ∈ s, hermF z (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermF_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hermF_add_right, ih]

theorem card_le_of_fixes_isotropic {Q : Type} [Finite Q] (ρ : Q → Module.End K4 (Fin 6 → K4))
    (hρ : Function.Injective ρ) (hcomm : ∀ q q', Commute (ρ q) (ρ q')) (hpow : ∀ q, ρ q ^ 3 = 1)
    (hiso : ∀ q x y, hermF (ρ q x) (ρ q y) = hermF x y)
    (hdet : ∀ q, LinearMap.det (ρ q) = 1)
    (R : Submodule K4 (Fin 6 → K4)) (hfix : ∀ q, ∀ r ∈ R, ρ q r = r)
    (hisoR : ∀ r ∈ R, ∀ r' ∈ R, hermF r r' = 0) :
    Nat.card Q ≤ 3 ^ (5 - 2 * Module.finrank K4 R) := by
  classical
  letI : Fintype K4 := Fintype.ofFinite K4
  obtain ⟨ω, hω⟩ := K4_exists_omega
  obtain ⟨I, hIfin, b, χ, hb⟩ := exists_eigenbasis K4_two_eq_zero hω ρ hcomm hpow
  letI : Fintype I := Fintype.ofFinite I
  have hmat : ∀ q, LinearMap.toMatrix b b (ρ q) = Matrix.diagonal (fun x => χ x q) := by
    intro q
    ext x y
    rw [LinearMap.toMatrix_apply, hb y q, map_smul, Basis.repr_self, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst hxy
      simp [Finsupp.single_apply]
    · simp [Finsupp.single_apply, hxy, Ne.symm hxy]
  have K1 : ∀ q (v : Fin 6 → K4) (x : I), b.repr (ρ q v) x = χ x q * b.repr v x := by
    intro q v x
    have h := congrFun (LinearMap.toMatrix_mulVec_repr b b (ρ q) v) x
    rw [hmat q, Matrix.mulVec_diagonal] at h
    exact h.symm
  have hdetχ : ∀ q, ∏ x, χ x q = 1 := by
    intro q
    rw [← hdet q, ← LinearMap.det_toMatrix b, hmat q, Matrix.det_diagonal]
  have hpowb : ∀ q (x : I) (n : ℕ), (ρ q ^ n) (b x) = χ x q ^ n • b x := by
    intro q x n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, hb x q, map_smul, ih, smul_smul, ← pow_succ']
  have hcube : ∀ q (x : I), χ x q ^ 3 = 1 := by
    intro q x
    have h := hpowb q x 3
    rw [hpow q, Module.End.one_apply] at h
    have hc := congrArg (fun v => b.repr v x) h
    simpa [Basis.repr_self] using hc.symm
  let J : Finset I := Finset.univ.filter (fun x => ∃ q, χ x q ≠ 1)
  have hJ : ∀ x, x ∈ J ↔ ∃ q, χ x q ≠ 1 := fun x => by simp [J]
  have Rcoord : ∀ r ∈ R, ∀ x ∈ J, b.repr r x = 0 := by
    intro r hr x hx
    obtain ⟨q, hq⟩ := (hJ x).1 hx
    have h := K1 q r x
    rw [hfix q r hr] at h
    have hm : (χ x q - 1) * b.repr r x = 0 := by linear_combination -h
    rcases mul_eq_zero.1 hm with h1 | h1
    · exact absurd (sub_eq_zero.1 h1) hq
    · exact h1
  have O1 : ∀ x ∉ J, ∀ y ∈ J, hermF (b x) (b y) = 0 := by
    intro x hx y hy
    have hxq : ∀ q, χ x q = 1 := by
      intro q
      by_contra h
      exact hx ((hJ x).2 ⟨q, h⟩)
    obtain ⟨q, hq⟩ := (hJ y).1 hy
    have h := hiso q (b x) (b y)
    rw [hb x q, hb y q, hermF_smul_left, hermF_smul_right, hxq q] at h
    have hm : (χ y q - 1) * hermF (b x) (b y) = 0 := by linear_combination h
    rcases mul_eq_zero.1 hm with h1 | h1
    · exact absurd (sub_eq_zero.1 h1) hq
    · exact h1
  let VJ : Submodule K4 (Fin 6 → K4) := Submodule.span K4 (Set.range fun x : J => b x.1)
  have hVJ_fin : Module.finrank K4 VJ = J.card := by
    have hli : LinearIndependent K4 (fun x : J => b x.1) :=
      b.linearIndependent.comp _ Subtype.val_injective
    rw [finrank_span_eq_card hli, Fintype.card_coe]
  have VJcoord : ∀ y ∈ VJ, ∀ x ∉ J, b.repr y x = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x', rfl⟩ := hz
      intro x hx
      have hne : x'.1 ≠ x := fun h => hx (h ▸ x'.2)
      rw [Basis.repr_self, Finsupp.single_apply, if_neg hne]
    | zero => intro x _; simp
    | add y z _ _ hy hz => intro x hx; rw [map_add, Finsupp.add_apply, hy x hx, hz x hx, add_zero]
    | smul c y _ hy => intro x hx; rw [map_smul, Finsupp.smul_apply, hy x hx, smul_zero]
  have orthVJ : ∀ r ∈ R, ∀ y ∈ VJ, hermF r y = 0 := by
    intro r hr y hy
    have hrc := Rcoord r hr
    have hyc := VJcoord y hy
    calc hermF r y
        = hermF (∑ x, b.repr r x • b x) (∑ x', b.repr y x' • b x') := by
          rw [b.sum_repr r, b.sum_repr y]
      _ = ∑ x, ∑ x', (b.repr r x) ^ 2 * (b.repr y x' * hermF (b x) (b x')) := by
          rw [hermF_sum_left]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hermF_smul_left, hermF_sum_right, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x' _ => ?_
          rw [hermF_smul_right]
      _ = 0 := by
          refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun x' _ => ?_
          by_cases hx : x ∈ J
          · rw [hrc x hx]
            ring
          · by_cases hx' : x' ∈ J
            · rw [O1 x hx x' hx']
              ring
            · rw [hyc x' hx']
              ring
  have hinf : R ⊓ VJ = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    obtain ⟨hR, hV⟩ := Submodule.mem_inf.1 hr
    rw [Submodule.mem_bot]
    apply b.repr.injective
    ext x
    by_cases hx : x ∈ J
    · simp [Rcoord r hR x hx]
    · simp [VJcoord r hV x hx]
  have hsub : R ⊔ VJ ≤ perp R := by
    refine sup_le ?_ ?_
    · intro r hr
      exact mem_perp.2 fun w hw => hisoR w hw r hr
    · intro y hy
      exact mem_perp.2 fun w hw => orthVJ w hw y hy
  have hdim : Module.finrank K4 R + J.card ≤ 6 - Module.finrank K4 R := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq R VJ
    rw [hinf, finrank_bot, add_zero, hVJ_fin] at h1
    have h2 := Submodule.finrank_mono hsub
    have h3 := finrank_perp_add R
    omega
  rcases J.eq_empty_or_nonempty with hJe | ⟨j₀, hj₀⟩
  ·
    have hall : ∀ q, ρ q = 1 := by
      intro q
      apply b.ext
      intro x
      have hxq : ∀ q, χ x q = 1 := by
        intro q
        by_contra h
        have hxJ : x ∈ J := (hJ x).2 ⟨q, h⟩
        rw [hJe] at hxJ
        simp at hxJ
      rw [hb x q, hxq q, one_smul, Module.End.one_apply]
    have hsubs : Subsingleton Q := ⟨fun q q' => hρ ((hall q).trans (hall q').symm)⟩
    have hle : Nat.card Q ≤ 1 := Finite.card_le_one_iff_subsingleton.2 hsubs
    exact le_trans hle (Nat.one_le_pow _ _ (by norm_num))
  ·
    let Jp : Finset I := J.erase j₀
    have hJp : Jp.card = J.card - 1 := Finset.card_erase_of_mem hj₀
    have hT3 : Nat.card {c : K4 // c ^ 3 = 1} ≤ 3 := by
      have hsub3 : (Finset.univ.filter fun c : K4 => c ^ 3 = 1) ⊆
          ({1, ω, ω ^ 2} : Finset K4) := by
        intro c hc
        rw [Finset.mem_filter] at hc
        rcases cube_root_mem hω hc.2 with h | h | h <;> simp [h]
      have hcard : (Finset.univ.filter fun c : K4 => c ^ 3 = 1).card ≤ 3 :=
        le_trans (Finset.card_le_card hsub3) Finset.card_le_three
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact hcard
    let Φ : Q → (Jp → {c : K4 // c ^ 3 = 1}) := fun q x => ⟨χ x.1 q, hcube q x.1⟩
    have hΦ : Function.Injective Φ := by
      intro q q' h
      have hJp_eq : ∀ x ∈ Jp, χ x q = χ x q' := fun x hx => by
        have := congrArg (fun φ : Jp → {c : K4 // c ^ 3 = 1} => (φ ⟨x, hx⟩).1) h
        simpa [Φ] using this
      have hPq : ∀ q₀, ∏ x, χ x q₀ = χ j₀ q₀ * ∏ x ∈ Jp, χ x q₀ := by
        intro q₀
        rw [← Finset.mul_prod_erase Finset.univ (fun x => χ x q₀) (Finset.mem_univ j₀)]
        congr 1
        have hsub : Jp ⊆ Finset.univ.erase j₀ := fun x hx =>
          Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hx).1, Finset.mem_univ _⟩
        refine (Finset.prod_subset hsub fun x hx hxJ => ?_).symm
        have hxj : x ≠ j₀ := (Finset.mem_erase.1 hx).1
        have hxJ : x ∉ J := fun hxJ' => hxJ (Finset.mem_erase.2 ⟨hxj, hxJ'⟩)
        have hone : ∀ q₁, χ x q₁ = 1 := fun q₁ => by
          by_contra h'
          exact hxJ ((hJ x).2 ⟨q₁, h'⟩)
        exact hone q₀
      have hall_eq : ∀ y, χ y q = χ y q' := by
        intro y
        by_cases hyj : y = j₀
        · rw [hyj]
          have hPeq : ∏ x ∈ Jp, χ x q = ∏ x ∈ Jp, χ x q' :=
            Finset.prod_congr rfl fun x hx => hJp_eq x hx
          have hne : ∏ x ∈ Jp, χ x q ≠ 0 := by
            intro h0
            have h1 := hdetχ q
            rw [hPq q, h0, mul_zero] at h1
            exact zero_ne_one h1
          have e1 : χ j₀ q * ∏ x ∈ Jp, χ x q = 1 := by rw [← hPq q, hdetχ q]
          have e2 : χ j₀ q' * ∏ x ∈ Jp, χ x q = 1 := by
            rw [hPeq, ← hPq q', hdetχ q']
          exact mul_right_cancel₀ hne (e1.trans e2.symm)
        · by_cases hy : y ∈ J
          · exact hJp_eq y (Finset.mem_erase.2 ⟨hyj, hy⟩)
          · have h1 : ∀ q₀, χ y q₀ = 1 := fun q₀ => by
              by_contra h'
              exact hy ((hJ y).2 ⟨q₀, h'⟩)
            rw [h1 q, h1 q']
      apply hρ
      apply b.ext
      intro x
      rw [hb x q, hb x q', hall_eq x]
    have hcard_le : Nat.card Q ≤ Nat.card (Jp → {c : K4 // c ^ 3 = 1}) :=
      Nat.card_le_card_of_injective Φ hΦ
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Jp), Fintype.card_coe] at hcard_le
    have hpow3 : Nat.card {c : K4 // c ^ 3 = 1} ^ Jp.card ≤ 3 ^ Jp.card :=
      Nat.pow_le_pow_left hT3 _
    have hJcard : 1 ≤ J.card := Finset.card_pos.2 ⟨j₀, hj₀⟩
    have hexp : J.card - 1 ≤ 5 - 2 * Module.finrank K4 R := by omega
    calc Nat.card Q ≤ 3 ^ Jp.card := le_trans hcard_le hpow3
      _ = 3 ^ (J.card - 1) := by rw [hJp]
      _ ≤ 3 ^ (5 - 2 * Module.finrank K4 R) := Nat.pow_le_pow_right (by norm_num) hexp

end CFSG.LocalAnalysis.GLTheoremA.CatB.InnU6

end
