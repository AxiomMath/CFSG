module

public import CFSG.LocalAnalysis.SectionRank.LocalDet
public import CFSG.LocalAnalysis.SectionRank.CatalogStep
public import CFSG.LocalAnalysis.SectionRank.Alternating

public section

namespace CFSG.SectionRank

open CFSG.Open

section NineCycles

@[expose] def cyc012 : Equiv.Perm (Fin 9) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def cyc345 : Equiv.Perm (Fin 9) := Equiv.swap 3 4 * Equiv.swap 4 5

@[expose] def cyc678 : Equiv.Perm (Fin 9) := Equiv.swap 6 7 * Equiv.swap 7 8

@[expose] def nineParam (v : Fin 3 → ZMod 3) : Equiv.Perm (Fin 9) :=
  cyc012 ^ (v 0).val * cyc345 ^ (v 1).val * cyc678 ^ (v 2).val

theorem nineParam_add : ∀ v w : Fin 3 → ZMod 3, nineParam (v + w) = nineParam v * nineParam w := by
  decide +kernel

theorem nineParam_zero : nineParam 0 = 1 := by decide +kernel

theorem nineParam_eq_one : ∀ v : Fin 3 → ZMod 3, nineParam v = 1 → v = 0 := by decide +kernel

theorem nineParam_sign : ∀ v : Fin 3 → ZMod 3, Equiv.Perm.sign (nineParam v) = 1 := by
  decide +kernel

@[expose] def nineSign0 : Equiv.Perm (Fin 9) := Equiv.swap 3 4 * Equiv.swap 6 7

@[expose] def nineSign1 : Equiv.Perm (Fin 9) := Equiv.swap 0 1 * Equiv.swap 3 4

theorem nineSign0_sign : Equiv.Perm.sign nineSign0 = 1 := by decide +kernel

theorem nineSign1_sign : Equiv.Perm.sign nineSign1 = 1 := by decide +kernel

theorem nineSign0_conj : ∀ v : Fin 3 → ZMod 3,
    nineSign0 * nineParam v * nineSign0⁻¹ = nineParam (![1, -1, -1] * v) := by
  decide +kernel

theorem nineSign1_conj : ∀ v : Fin 3 → ZMod 3,
    nineSign1 * nineParam v * nineSign1⁻¹ = nineParam (![-1, -1, 1] * v) := by
  decide +kernel

@[expose] def nineHom : Multiplicative (Fin 3 → ZMod 3) →* alternatingGroup (Fin 9) where
  toFun v := ⟨nineParam (Multiplicative.toAdd v), nineParam_sign _⟩
  map_one' := Subtype.ext nineParam_zero
  map_mul' v w := Subtype.ext (nineParam_add (Multiplicative.toAdd v) (Multiplicative.toAdd w))

theorem nineHom_injective : Function.Injective nineHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro v hv
  have h : nineParam (Multiplicative.toAdd v) = 1 := congrArg Subtype.val hv
  exact Subgroup.mem_bot.2 (Multiplicative.toAdd.injective (nineParam_eq_one _ h))

end NineCycles

section Embed

variable {k n : ℕ} (hk : k ≤ n)

@[expose] def firstPts : Fin k ≃ {x : Fin n // x.val < k} where
  toFun i := ⟨Fin.castLE hk i, i.2⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def altEmbed : alternatingGroup (Fin k) →* alternatingGroup (Fin n) :=
  ((Equiv.Perm.extendDomainHom (firstPts hk)).comp (alternatingGroup (Fin k)).subtype).codRestrict
    _ fun σ => by
      change Equiv.Perm.sign (Equiv.Perm.extendDomain _ _) = 1
      rw [Equiv.Perm.sign_extendDomain]
      exact σ.2

theorem altEmbed_injective : Function.Injective (altEmbed hk) := fun _ _ h =>
  Subtype.ext (Equiv.Perm.extendDomainHom_injective (firstPts hk) (congrArg Subtype.val h))

end Embed

theorem alternating_cover_rank_three {n : ℕ} (hn : 9 ≤ n) {E : Type*} [Group E] [Finite E]
    (π : E →* alternatingGroup (Fin n)) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) :
    ∃ F : Subgroup E, IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ι := altEmbed hn
  have h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup E) := by
    refine three_le_pRank_of_sign_lines (by norm_num) π.ker hC π hπ rfl (ι.comp nineHom)
      ((altEmbed_injective hn).comp nineHom_injective) (ι ⟨nineSign0, nineSign0_sign⟩)
      (ι ⟨nineSign1, nineSign1_sign⟩) (fun v => ?_) (fun v => ?_)
    · have h := congrArg ι (Subtype.ext (nineSign0_conj (Multiplicative.toAdd v)) :
        (⟨nineSign0, nineSign0_sign⟩ : alternatingGroup (Fin 9)) * nineHom v *
          (⟨nineSign0, nineSign0_sign⟩ : alternatingGroup (Fin 9))⁻¹ =
        nineHom (Multiplicative.ofAdd (![1, -1, -1] * Multiplicative.toAdd v)))
      rw [map_mul, map_mul, map_inv] at h
      exact h
    · have h := congrArg ι (Subtype.ext (nineSign1_conj (Multiplicative.toAdd v)) :
        (⟨nineSign1, nineSign1_sign⟩ : alternatingGroup (Fin 9)) * nineHom v *
          (⟨nineSign1, nineSign1_sign⟩ : alternatingGroup (Fin 9))⁻¹ =
        nineHom (Multiplicative.ofAdd (![-1, -1, 1] * Multiplicative.toAdd v)))
      rw [map_mul, map_mul, map_inv] at h
      exact h
  obtain ⟨F, -, hF, hcard⟩ := exists_isElemAbelian_card_of_le_pRank h3
  exact ⟨F, hF, hcard⟩

section SmallSylow

variable {J : Type*} [Group J] [Finite J]

theorem sylow_isCyclic_of_not_sq_dvd {r : ℕ} [hr : Fact r.Prime] (h : ¬ r ^ 2 ∣ Nat.card J)
    (P : Sylow r J) : IsCyclic (P : Subgroup J) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 P.isPGroup'
  have hdvd : r ^ k ∣ Nat.card J := hk ▸ Subgroup.card_subgroup_dvd_card _
  have hk1 : k ≤ 1 := by
    by_contra hk1
    push Not at hk1
    exact h ((pow_dvd_pow r hk1).trans hdvd)
  interval_cases k
  · rw [pow_zero] at hk
    have : Subsingleton (P : Subgroup J) := (Nat.card_eq_one_iff_unique.1 hk).1
    exact isCyclic_of_subsingleton
  · rw [pow_one] at hk
    exact isCyclic_of_prime_card hk

theorem card_ker_eq_one_or_three {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* J) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) (hr : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → ¬ r ^ 2 ∣ Nat.card J)
    (h3 : ∀ C3 : Sylow 3 π.ker, Nat.card (C3 : Subgroup π.ker) ≤ 3) :
    Nat.card π.ker = 1 ∨ Nat.card π.ker = 3 := by
  have hpos : Nat.card π.ker ≠ 0 := Nat.card_pos.ne'
  have hprime : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card π.ker → d = 3 := by
    intro d hd hdvd
    have : Fact d.Prime := ⟨hd⟩
    by_contra hd3
    have hd2 : d ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
    obtain ⟨Cd⟩ := (inferInstance : Nonempty (Sylow d π.ker))
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow d J))
    exact Sylow.ne_bot_of_dvd_card Cd hdvd
      (CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπ hC Cd Q
        (sylow_isCyclic_of_not_sq_dvd (hr d hd hd2 hd3) Q))
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hpos hprime
  set k := (Nat.card π.ker).primeFactorsList.length with hk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨C3⟩ := (inferInstance : Nonempty (Sylow 3 π.ker))
  have hC3 := Sylow.card_eq_multiplicity C3
  rw [hpow] at hC3
  simp only [Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_three,
    smul_eq_mul, mul_one] at hC3
  have hle := h3 C3
  rw [hC3] at hle
  have hk1 : k ≤ 1 := by
    by_contra hk1
    push Not at hk1
    have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
    omega
  interval_cases k
  · left; rw [hpow, pow_zero]
  · right; rw [hpow, pow_one]

end SmallSylow

section SixCycles

@[expose] def six012 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def six345 : Equiv.Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

@[expose] def sixParam (v : Fin 2 → ZMod 3) : Equiv.Perm (Fin 6) :=
  six012 ^ (v 0).val * six345 ^ (v 1).val

theorem sixParam_add : ∀ v w : Fin 2 → ZMod 3, sixParam (v + w) = sixParam v * sixParam w := by
  decide +kernel

theorem sixParam_zero : sixParam 0 = 1 := by decide +kernel

theorem sixParam_eq_one : ∀ v : Fin 2 → ZMod 3, sixParam v = 1 → v = 0 := by decide +kernel

theorem sixParam_sign : ∀ v : Fin 2 → ZMod 3, Equiv.Perm.sign (sixParam v) = 1 := by
  decide +kernel

theorem six012_sign : Equiv.Perm.sign six012 = 1 := by decide +kernel

theorem six345_sign : Equiv.Perm.sign six345 = 1 := by decide +kernel

@[expose] def sixHom : Multiplicative (Fin 2 → ZMod 3) →* alternatingGroup (Fin 6) where
  toFun v := ⟨sixParam (Multiplicative.toAdd v), sixParam_sign _⟩
  map_one' := Subtype.ext sixParam_zero
  map_mul' v w := Subtype.ext (sixParam_add (Multiplicative.toAdd v) (Multiplicative.toAdd w))

theorem sixHom_injective : Function.Injective sixHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro v hv
  have h : sixParam (Multiplicative.toAdd v) = 1 := congrArg Subtype.val hv
  exact Subgroup.mem_bot.2 (Multiplicative.toAdd.injective (sixParam_eq_one _ h))

theorem sixHom_apply (v : Multiplicative (Fin 2 → ZMod 3)) :
    sixHom v = ⟨six012, six012_sign⟩ ^ (Multiplicative.toAdd v 0).val *
      ⟨six345, six345_sign⟩ ^ (Multiplicative.toAdd v 1).val := rfl

end SixCycles

section SylowThree

variable {n : ℕ} (hn : 6 ≤ n)

@[expose] def sylowThreeAlt : Subgroup (alternatingGroup (Fin n)) :=
  ((altEmbed hn).comp sixHom).range

theorem card_sylowThreeAlt : Nat.card (sylowThreeAlt hn) = 3 ^ 2 := by
  have hinj : Function.Injective ((altEmbed hn).comp sixHom) :=
    (altEmbed_injective hn).comp sixHom_injective
  rw [sylowThreeAlt, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Nat.card_zmod]

theorem isElemAbelian_sylowThreeAlt : IsElemAbelian 3 (sylowThreeAlt hn) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : alternatingGroup (Fin n)) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    have : x ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      rw [toAdd_pow, Pi.smul_apply, toAdd_one, Pi.zero_apply, nsmul_eq_mul]
      exact mul_eq_zero_of_left (by decide) _
    rw [← map_pow, this, map_one]

@[expose] def altCycA : alternatingGroup (Fin n) := altEmbed hn ⟨six012, six012_sign⟩

@[expose] def altCycB : alternatingGroup (Fin n) := altEmbed hn ⟨six345, six345_sign⟩

theorem closure_altCyc : Subgroup.closure ({altCycA hn, altCycB hn} : Set _) =
    sylowThreeAlt hn := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · have h : sixHom (Multiplicative.ofAdd (Pi.single 0 1)) = ⟨six012, six012_sign⟩ :=
        Subtype.ext (by decide +kernel)
      exact ⟨Multiplicative.ofAdd (Pi.single 0 1), by rw [MonoidHom.comp_apply, h]; rfl⟩
    · have h : sixHom (Multiplicative.ofAdd (Pi.single 1 1)) = ⟨six345, six345_sign⟩ :=
        Subtype.ext (by decide +kernel)
      exact ⟨Multiplicative.ofAdd (Pi.single 1 1), by rw [MonoidHom.comp_apply, h]; rfl⟩
  · rintro _ ⟨v, rfl⟩
    rw [MonoidHom.comp_apply, sixHom_apply, map_mul, map_pow, map_pow,
      show altEmbed hn ⟨six012, six012_sign⟩ = altCycA hn from rfl,
      show altEmbed hn ⟨six345, six345_sign⟩ = altCycB hn from rfl]
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))) _)

theorem exists_sylow_eq_sylowThreeAlt (hn8 : n ≤ 8) :
    ∃ Q : Sylow 3 (alternatingGroup (Fin n)), (Q : Subgroup _) = sylowThreeAlt hn := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (sylowThreeAlt hn) := IsPGroup.of_card (card_sylowThreeAlt hn)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  refine ⟨Q, (Subgroup.eq_of_le_of_card_ge hQ ?_).symm⟩
  rw [card_sylowThreeAlt]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 Q.isPGroup'
  have hdvd : 3 ^ k ∣ Nat.card (alternatingGroup (Fin n)) := hk ▸ Subgroup.card_subgroup_dvd_card _
  have hcard : Nat.card (alternatingGroup (Fin n)) ∣ 20160 := by
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [nat_card_alternatingGroup, Nat.card_fin]
    interval_cases n <;> decide
  have hk2 : k ≤ 2 := by
    by_contra hk2
    push Not at hk2
    have : 3 ^ 3 ∣ 20160 := ((pow_dvd_pow 3 hk2).trans hdvd).trans hcard
    exact absurd this (by decide)
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) hk2

end SylowThree

section SmallCover

theorem card_alternatingGroup_dvd {n : ℕ} (hn2 : 2 ≤ n) (hn8 : n ≤ 8) :
    Nat.card (alternatingGroup (Fin n)) ∣ 20160 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn2
  rw [nat_card_alternatingGroup, Nat.card_fin]
  interval_cases n <;> decide

theorem not_sq_dvd_card_alternatingGroup {n : ℕ} (hn2 : 2 ≤ n) (hn8 : n ≤ 8) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) : ¬ r ^ 2 ∣ Nat.card (alternatingGroup (Fin n)) := by
  intro h
  have h' := h.trans (card_alternatingGroup_dvd hn2 hn8)
  have key : ∀ r < 142, r.Prime → r ^ 2 ∣ 20160 → r ≤ 3 := by decide
  have hlt : r < 142 := by
    by_contra hge
    push Not at hge
    have := Nat.le_of_dvd (by norm_num) h'
    nlinarith
  have := key r hlt hr h'
  have := hr.two_le
  omega

@[expose] def eightSign : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 6 7

theorem eightSign_sign : Equiv.Perm.sign eightSign = 1 := by decide +kernel

theorem eightSign_conj_A :
    (⟨eightSign, eightSign_sign⟩ : alternatingGroup (Fin 8)) * altCycA (by norm_num) *
      (⟨eightSign, eightSign_sign⟩ : alternatingGroup (Fin 8))⁻¹ =
      altCycA (by norm_num) ^ 2 * altCycB (by norm_num) ^ 0 :=
  Subtype.ext (by decide +kernel)

theorem eightSign_conj_B :
    (⟨eightSign, eightSign_sign⟩ : alternatingGroup (Fin 8)) * altCycB (by norm_num) *
      (⟨eightSign, eightSign_sign⟩ : alternatingGroup (Fin 8))⁻¹ =
      altCycA (by norm_num) ^ 0 * altCycB (by norm_num) ^ 1 :=
  Subtype.ext (by decide +kernel)

theorem alternating_small_odd_cover_bound {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≤ 8) {E : Type*}
    [Group E] [Finite E] [Group.IsPerfect E] (π : E →* alternatingGroup (Fin n))
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) :
    ((n = 5 ∨ n = 8) → π.ker = ⊥) ∧
      ((n = 6 ∨ n = 7) → Nat.card π.ker = 1 ∨ Nat.card π.ker = 3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hr := fun r hr hr2 hr3 => not_sq_dvd_card_alternatingGroup (by omega) hn8 (r := r) hr hr2 hr3
  have h3 : ∀ C3 : Sylow 3 π.ker, Nat.card (C3 : Subgroup π.ker) ≤ 3 := by
    intro C3
    rcases (show n = 5 ∨ 6 ≤ n by omega) with rfl | hn6
    · obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 3 (alternatingGroup (Fin 5))))
      have hcyc := sylow_isCyclic_of_not_sq_dvd (r := 3) (by
        rw [nat_card_alternatingGroup, Nat.card_fin]; decide) Q
      rw [CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπ hC C3 Q hcyc,
        Subgroup.card_bot]
      norm_num
    · obtain ⟨Q, hQ⟩ := exists_sylow_eq_sylowThreeAlt hn6 hn8
      exact (CFSG.ShultStronglyClosedTI.central_cover_elementary_rank_two_sylow_kernel_bound π hπ hC
        C3 Q (hQ ▸ isElemAbelian_sylowThreeAlt hn6) (hQ ▸ card_sylowThreeAlt hn6)).2
  have h13 := card_ker_eq_one_or_three π hπ hC hodd hr h3
  have hkill : (n = 5 ∨ n = 8) → ∀ C3 : Sylow 3 π.ker, (C3 : Subgroup π.ker) = ⊥ := by
    rintro (rfl | rfl) C3
    · obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 3 (alternatingGroup (Fin 5))))
      exact CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπ hC C3 Q
        (sylow_isCyclic_of_not_sq_dvd (r := 3) (by
          rw [nat_card_alternatingGroup, Nat.card_fin]; decide) Q)
    · obtain ⟨Q, hQ⟩ := exists_sylow_eq_sylowThreeAlt (n := 8) (by norm_num) le_rfl
      refine sylow_kernel_eq_bot_of_normalizer_det π hπ hC Q
        (hQ ▸ isElemAbelian_sylowThreeAlt _) (hQ ▸ closure_altCyc _) _ eightSign_conj_A
        eightSign_conj_B ?_ C3
      decide +revert
  refine ⟨fun h58 => ?_, fun _ => h13⟩
  obtain ⟨C3⟩ := (inferInstance : Nonempty (Sylow 3 π.ker))
  have hC3 := hkill h58 C3
  rcases h13 with h1 | h3'
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have hdvd : 3 ∣ Nat.card π.ker := by rw [h3']
    exact Sylow.ne_bot_of_dvd_card C3 hdvd hC3

end SmallCover

theorem catalog_alternating {L : Type} [Group L] [Finite L] (hL : IsQuasisimple L)
    (hSQT : IsStronglyQuasithin L) (hodd : Odd (Nat.card (Subgroup.center L))) {n : ℕ}
    (hn : 5 ≤ n) (e : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin n)) :
    CatalogStepConclusion L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect L := hL.1
  let π : L →* alternatingGroup (Fin n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center L := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hC : π.ker ≤ Subgroup.center L := hker.le
  have hn8 : n ≤ 8 := by
    by_contra h9
    push Not at h9
    obtain ⟨F, hF, hcard⟩ := alternating_cover_rank_three h9 π hπ hC
    have h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := le_pRank (by norm_num) le_top hF hcard
    have := isStronglyQuasithin_iff.1 hSQT 3 Nat.prime_three (by norm_num)
    omega
  have hodd' : Odd (Nat.card π.ker) := by rw [hker]; exact hodd
  obtain ⟨h58, h67⟩ := alternating_small_odd_cover_bound hn hn8 π hπ hC hodd'
  have hZ : Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3 := by
    rw [← hker]
    rcases (show n = 5 ∨ n = 8 ∨ n = 6 ∨ n = 7 by omega) with h | h | h | h
    · rw [h58 (Or.inl h), Subgroup.card_bot]; exact Or.inl rfl
    · rw [h58 (Or.inr h), Subgroup.card_bot]; exact Or.inl rfl
    · exact h67 (Or.inl h)
    · exact h67 (Or.inr h)
  refine catalogStepConclusion_of hSQT hZ (isStronglyQuasithin_of_mulEquiv e ?_)
  rw [isStronglyQuasithin_iff]
  exact fun q hq hq2 => pRank_alternating_le_two hn8 hq hq2

end CFSG.SectionRank
