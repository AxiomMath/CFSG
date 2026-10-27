module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32B
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigPerm
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpNotLie

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat

open CFSG Subgroup Equiv CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem altCover_card_ker_le_orderOf_sq {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    {m : ℕ} (η : G →* alternatingGroup (Fin (m + 2))) (hη : Function.Surjective η)
    (hK : η.ker ≤ Subgroup.center G) (hK2 : IsPGroup 2 η.ker) {x : Fin m → G}
    (hxη : ∀ i, η (x i) = altThreeCycle i) (hx3 : ∀ i, x i ^ 3 = 1) {i₀ i₁ : Fin m}
    (h01 : i₀ ≠ i₁) : Nat.card η.ker ≤ orderOf ((x i₀ * x i₁) ^ 2) := by
  classical
  have hL : Subgroup.closure (Set.range x) = ⊤ := by
    have hmap : (Subgroup.closure (Set.range x)).map η = ⊤ := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      have : η ∘ x = altThreeCycle := funext hxη
      rw [this, closure_altThreeCycle]
    have hsup : Subgroup.closure (Set.range x) ⊔ η.ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
    have h := CFSG.ComponentClassification.CentralExtensions.commutator_sup_central
      (Subgroup.closure (Set.range x)) η.ker hK
    rw [hsup, ← _root_.commutator_def, Group.IsPerfect.commutator_eq_top] at h
    exact eq_top_iff.mpr (h.le.trans (Subgroup.commutator_le_self _))
  set z := (x i₀ * x i₁) ^ 2
  have hzc : z ∈ Subgroup.center G := hK (by
    rw [MonoidHom.mem_ker, map_pow, map_mul, hxη, hxη, altThreeCycle_mul_sq h01])
  have hzij : ∀ i j, i ≠ j → (x i * x j) ^ 2 = z := fun i j hij =>
    lift_sq_eq η hη hK hK2 hxη hx3 hij h01
  set K₀ := Subgroup.zpowers z
  have : K₀.Normal := ⟨fun k hk g => by
    obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    have hc := Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hzc e) g
    rw [hc, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) e⟩
  have hcardQ : Nat.card (G ⧸ K₀) ≤ (m + 2).factorial / 2 := by
    have h := card_closure_le_of_carmichael m (QuotientGroup.mk' K₀ ∘ x)
      (fun i => by rw [Function.comp_apply, ← map_pow, hx3, map_one])
      (fun i j hij => by
        rw [Function.comp_apply, Function.comp_apply, ← map_mul, ← map_pow, hzij i j hij]
        exact (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_zpowers z))
    have hgen : Subgroup.closure (Set.range (QuotientGroup.mk' K₀ ∘ x)) = ⊤ := by
      rw [Set.range_comp, ← MonoidHom.map_closure, hL,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rw [hgen, Subgroup.card_top] at h
    exact h
  have hP1 : Nat.card G = Nat.card (G ⧸ K₀) * Nat.card K₀ :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup K₀
  have hP2 : Nat.card G = Nat.card (alternatingGroup (Fin (m + 2))) * Nat.card η.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup η.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective η hη).toEquiv]
  have hA : Nat.card (alternatingGroup (Fin (m + 2))) = (m + 2).factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hApos : 0 < (m + 2).factorial / 2 := by
    rw [← hA]
    exact Nat.card_pos
  have hle : (m + 2).factorial / 2 * Nat.card η.ker ≤ (m + 2).factorial / 2 * Nat.card K₀ := by
    calc (m + 2).factorial / 2 * Nat.card η.ker = Nat.card G := by rw [hP2, hA]
      _ = Nat.card (G ⧸ K₀) * Nat.card K₀ := hP1
      _ ≤ (m + 2).factorial / 2 * Nat.card K₀ := Nat.mul_le_mul_right _ hcardQ
  have h1 := Nat.le_of_mul_le_mul_left hle hApos
  rwa [Nat.card_zpowers] at h1

private theorem altCover_sq_eq_one_of_card_le_two {K : Type*} [Group K] [Finite K]
    (h : Nat.card K ≤ 2) (k : K) : k ^ 2 = 1 := by
  have hpow := pow_card_eq_one' (G := K) (x := k)
  have hpos : 0 < Nat.card K := Nat.card_pos
  interval_cases h' : Nat.card K
  · rw [pow_one] at hpow
    rw [hpow, one_pow]
  · exact hpow

private theorem altCover_injective_four {α : Type*} {a b c d : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective ![a, b, c, d] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm hbc,
    Ne.symm hbd, Ne.symm hcd]

private theorem altCover_exists_four {n : ℕ} (hn : 6 ≤ n) {a b c d a' b' c' d' : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hab' : a' ≠ b') (hac' : a' ≠ c') (had' : a' ≠ d') (hbc' : b' ≠ c') (hbd' : b' ≠ d')
    (hcd' : c' ≠ d') :
    ∃ σ : alternatingGroup (Fin n), (σ : Perm (Fin n)) a = a' ∧ (σ : Perm (Fin n)) b = b' ∧
      (σ : Perm (Fin n)) c = c' ∧ (σ : Perm (Fin n)) d = d' := by
  haveI := alternatingGroup.isMultiplyPretransitive (Fin n)
  haveI : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin n)) (Fin n) 4 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card (Fin n) - 2)
      (by rw [Nat.card_fin]; omega) (Nat.sub_le _ _)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin n))
    (⟨![a, b, c, d], altCover_injective_four hab hac had hbc hbd hcd⟩ : Fin 4 ↪ Fin n)
    (⟨![a', b', c', d'], altCover_injective_four hab' hac' had' hbc' hbd' hcd'⟩ : Fin 4 ↪ Fin n)
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · exact congrArg (fun f : Fin 4 ↪ Fin n => f 0) hg
  · exact congrArg (fun f : Fin 4 ↪ Fin n => f 1) hg
  · exact congrArg (fun f : Fin 4 ↪ Fin n => f 2) hg
  · exact congrArg (fun f : Fin 4 ↪ Fin n => f 3) hg

theorem altCover_ker_eq_bot_of_involution_lift {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    {m : ℕ} (hm : 4 ≤ m) (η : G →* alternatingGroup (Fin (m + 2))) (hη : Function.Surjective η)
    (hK : η.ker ≤ Subgroup.center G) (hK2 : IsPGroup 2 η.ker) {p q s t : Fin (m + 2)}
    (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t) (hqs : q ≠ s) (hqt : q ≠ t) (hst : s ≠ t) {g : G}
    (hg : g * g = 1)
    (hgη : ((η g : alternatingGroup (Fin (m + 2))) : Perm (Fin (m + 2))) = swap p q * swap s t) :
    η.ker = ⊥ := by
  have hlift : ∀ i : Fin m, ∃ x : G, η x = altThreeCycle i ∧ x ^ 3 = 1 := fun i => by
    obtain ⟨y, hy⟩ := hη (altThreeCycle i)
    obtain ⟨x, hx, hx3⟩ := exists_lift_pow_three_eq_one hK hK2
      (by rw [hy]; exact altThreeCycle_pow_three i)
    exact ⟨x, hx.trans hy, hx3⟩
  choose x hxη hx3 using hlift
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  obtain ⟨w, hwdef⟩ : ∃ w : G, w = x i₀ * x i₁ := ⟨_, rfl⟩
  have hzc : w ^ 2 ∈ Subgroup.center G := hK (by
    rw [MonoidHom.mem_ker, map_pow, hwdef, map_mul, hxη, hxη, altThreeCycle_mul_sq h01])
  have hz2 : (w ^ 2) ^ 2 = 1 := by
    rw [hwdef]
    exact sq_sq_lift_eq_one η hK hK2 h01 (hxη i₀) (hxη i₁) (hx3 i₀) (hx3 i₁)
  have hcard : Nat.card η.ker ≤ orderOf (w ^ 2) := by
    rw [hwdef]
    exact altCover_card_ker_le_orderOf_sq η hη hK hK2 hxη hx3 h01
  have hcard2 : Nat.card η.ker ≤ 2 := hcard.trans (orderOf_le_of_pow_eq_one (by norm_num) hz2)
  obtain ⟨σ, hσ0, hσa, hσ1, hσb⟩ := altCover_exists_four (n := m + 2) (by omega)
    (a := 0) (b := i₀.addNat 2) (c := 1) (d := i₁.addNat 2) (a' := p) (b' := q) (c' := s)
    (d' := t) (addNat_two_ne_zero i₀).symm zero_ne_one_fin (addNat_two_ne_zero i₁).symm
    (addNat_two_ne_one i₀) (addNat_two_ne h01) (addNat_two_ne_one i₁).symm hpq hps hpt hqs hqt hst
  obtain ⟨h, hh⟩ := hη σ
  have hηy : η (h * w * h⁻¹) = η g := by
    apply Subtype.ext
    rw [hgη]
    have hηw : ((η w : alternatingGroup (Fin (m + 2))) : Perm (Fin (m + 2))) =
        swap 0 (i₀.addNat 2) * swap 1 (i₁.addNat 2) := by
      rw [hwdef, map_mul, hxη, hxη]
      exact coe_altThreeCycle_mul h01
    have h1 : ((η (h * w * h⁻¹) : alternatingGroup (Fin (m + 2))) : Perm (Fin (m + 2))) =
        (σ : Perm (Fin (m + 2))) *
          ((η w : alternatingGroup (Fin (m + 2))) : Perm (Fin (m + 2))) *
          (σ : Perm (Fin (m + 2)))⁻¹ := by
      rw [map_mul, map_mul, map_inv, hh]
      rfl
    rw [h1, hηw]
    calc (σ : Perm (Fin (m + 2))) * (swap 0 (i₀.addNat 2) * swap 1 (i₁.addNat 2)) *
          (σ : Perm (Fin (m + 2)))⁻¹
        = ((σ : Perm (Fin (m + 2))) * swap 0 (i₀.addNat 2) * (σ : Perm (Fin (m + 2)))⁻¹) *
          ((σ : Perm (Fin (m + 2))) * swap 1 (i₁.addNat 2) * (σ : Perm (Fin (m + 2)))⁻¹) := by
          group
      _ = swap ((σ : Perm (Fin (m + 2))) 0) ((σ : Perm (Fin (m + 2))) (i₀.addNat 2)) *
          swap ((σ : Perm (Fin (m + 2))) 1) ((σ : Perm (Fin (m + 2))) (i₁.addNat 2)) := by
          rw [swap_apply_apply (σ : Perm (Fin (m + 2))) 0 (i₀.addNat 2),
            swap_apply_apply (σ : Perm (Fin (m + 2))) 1 (i₁.addNat 2)]
      _ = swap p q * swap s t := by rw [hσ0, hσa, hσ1, hσb]
  obtain ⟨k, hkdef⟩ : ∃ k : G, k = (h * w * h⁻¹)⁻¹ * g := ⟨_, rfl⟩
  have hk : k ∈ η.ker := by
    rw [MonoidHom.mem_ker, hkdef, map_mul, map_inv, hηy, inv_mul_cancel]
  have hkc : ∀ u : G, u * k = k * u := Subgroup.mem_center_iff.mp (hK hk)
  have hgk : g = h * w * h⁻¹ * k := by
    rw [hkdef, mul_inv_cancel_left]
  have hz : h * w ^ 2 * h⁻¹ = w ^ 2 := by
    rw [Subgroup.mem_center_iff.mp hzc h, mul_inv_cancel_right]
  have hgg : g * g = w ^ 2 * k ^ 2 := by
    have hc : Commute (h * w * h⁻¹) k := hkc _
    rw [← sq, hgk, hc.mul_pow, conj_pow, hz]
  have hk2 : k ^ 2 = 1 := by
    have h2 := altCover_sq_eq_one_of_card_le_two hcard2 ⟨k, hk⟩
    exact congrArg Subtype.val h2
  have hz1 : w ^ 2 = 1 := by
    rw [hg, hk2, mul_one] at hgg
    exact hgg.symm
  have hle1 : Nat.card η.ker ≤ 1 := by
    rw [hz1, orderOf_one] at hcard
    exact hcard
  exact Subgroup.eq_bot_of_card_le _ hle1

private theorem altCover_eq_of_factorial_div_two_eq {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : a.factorial / 2 = b.factorial / 2) : a = b := by
  have h2a : 2 ∣ a.factorial := Nat.dvd_factorial (by norm_num) ha
  have h2b : 2 ∣ b.factorial := Nat.dvd_factorial (by norm_num) hb
  have h1 : a.factorial = b.factorial := by
    rw [← Nat.div_mul_cancel h2a, ← Nat.div_mul_cancel h2b, h]
  exact (Nat.factorial_inj (by omega)).mp h1

theorem altCover_exists_double_transposition {S : Type} [Group S] [Finite S] {m : ℕ}
    (hm5 : 5 ≤ m) (hm6 : m ≠ 6) (e : S ≃* alternatingGroup (Fin m)) {σ : MulAut S}
    {P : Subgroup S} (hP : CatLeaf.ProperFixedComponent σ P)
    (eP : ↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin 5)) :
    Nat.card P = 60 ∧ ∃ u ∈ P, ∃ p q s t : Fin m, p ≠ q ∧ p ≠ s ∧ p ≠ t ∧ q ≠ s ∧ q ≠ t ∧
      s ≠ t ∧ ((e u : alternatingGroup (Fin m)) : Perm (Fin m)) = swap p q * swap s t := by
  classical
  obtain ⟨hP', ⟨f⟩⟩ := hP.map e
  obtain ⟨τ, hτ2, hστ, hdeg, ⟨eA⟩⟩ :=
    CatLeaf.exists_involution_of_properFixedComponent_alternating hm5 hm6 hP'
  have hΩ5 : (Finset.univ.filter fun x => τ x = x).card = 5 := by
    have h1 := card_of_mulEquiv_alt (m := 5) (by norm_num) (eA.symm.trans (f.symm.trans eP))
    have : Nontrivial ↥(Finset.univ.filter fun x => τ x = x) := by
      rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_coe]
      omega
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_coe] at h1
    exact altCover_eq_of_factorial_div_two_eq (by omega) (by norm_num) h1
  have hsum : (Finset.univ.filter fun x => τ x = x).card + τ.support.card = m := by
    have hsupp : τ.support = Finset.univ.filter fun x => ¬ τ x = x := rfl
    rw [hsupp, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hle : P.map e.toMonoidHom ≤ fixAlt τ := by
    have hPF : P.map e.toMonoidHom ≤
        fixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin m)) τ) := by
      rw [← hστ]
      exact hP'.2.1
    have hPc : IsPComponent 2 ((P.map e.toMonoidHom).subgroupOf
        (fixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin m)) τ))) := by
      rw [← hστ]
      exact hP'.2.2.1
    intro x hx
    rw [mem_fixAlt]
    intro ω hω
    rw [Finset.mem_compl, Perm.mem_support, not_not]
    by_contra hcon
    exact (Perm.mem_support.mp hω) (support_of_isPComponent_fixed_conj hτ2 hPF hPc x hx ω hcon)
  have hcardfix : Nat.card (fixAlt τ) = 60 := by
    have h5 : m - τ.support.card = 5 := by omega
    rw [card_fixAlt (by omega), h5]
    decide
  have h60 : 60 ≤ Nat.card P := by
    have h1 : Nat.card (↥P ⧸ Open.fusionZStar ↥P) = 60 := by
      rw [card_of_mulEquiv_alt (by norm_num) eP]
      decide
    exact h1 ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have hcardmap : Nat.card (P.map e.toMonoidHom) = Nat.card P :=
    (Nat.card_congr (P.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  have hP60 : Nat.card P = 60 := by
    have h1 := Subgroup.card_le_of_le hle
    omega
  have hPeq : P.map e.toMonoidHom = fixAlt τ :=
    Subgroup.eq_of_le_of_card_ge hle (by omega)
  obtain ⟨p, q, s, t, hpq, hps, hpt, hqs, hqt, hst, hp, hq, hs, ht⟩ :
      ∃ p q s t : Fin m, p ≠ q ∧ p ≠ s ∧ p ≠ t ∧ q ≠ s ∧ q ≠ t ∧ s ≠ t ∧
        τ p = p ∧ τ q = q ∧ τ s = s ∧ τ t = t := by
    let ι : ↥(Finset.univ.filter fun x => τ x = x) ≃ Fin 5 :=
      Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hΩ5)
    have hfix : ∀ ω : ↥(Finset.univ.filter fun x => τ x = x), τ ω.1 = ω.1 := fun ω =>
      (Finset.mem_filter.mp ω.2).2
    refine ⟨(ι.symm 0).1, (ι.symm 1).1, (ι.symm 2).1, (ι.symm 3).1, ?_, ?_, ?_, ?_, ?_, ?_,
      hfix _, hfix _, hfix _, hfix _⟩ <;>
      exact fun h => absurd (ι.symm.injective (Subtype.ext h)) (by decide)
  have hev : (swap p q * swap s t : Perm (Fin m)) ∈ alternatingGroup (Fin m) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hpq, Perm.sign_swap hst]
    rfl
  obtain ⟨u', hu'def⟩ : ∃ u' : alternatingGroup (Fin m),
      (u' : Perm (Fin m)) = swap p q * swap s t := ⟨⟨swap p q * swap s t, hev⟩, rfl⟩
  have hu' : u' ∈ fixAlt τ := by
    rw [mem_fixAlt]
    intro ω hω
    rw [Finset.mem_compl, Perm.mem_support, not_not]
    by_contra hωτ
    have hωp : ω ≠ p := fun h => hωτ (by rw [h]; exact hp)
    have hωq : ω ≠ q := fun h => hωτ (by rw [h]; exact hq)
    have hωs : ω ≠ s := fun h => hωτ (by rw [h]; exact hs)
    have hωt : ω ≠ t := fun h => hωτ (by rw [h]; exact ht)
    refine (Perm.mem_support.mp hω) ?_
    rw [hu'def, Perm.mul_apply, swap_apply_of_ne_of_ne hωs hωt, swap_apply_of_ne_of_ne hωp hωq]
  refine ⟨hP60, e.symm u', ?_, p, q, s, t, hpq, hps, hpt, hqs, hqt, hst, ?_⟩
  · have h1 : u' ∈ P.map e.toMonoidHom := by
      rw [hPeq]
      exact hu'
    exact Subgroup.mem_map_equiv.mp h1
  · rw [MulEquiv.apply_symm_apply]
    exact hu'def

end CFSG.ComponentClassification.SolMax.FiveCat
