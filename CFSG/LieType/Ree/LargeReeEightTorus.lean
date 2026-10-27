module

public import CFSG.LieType.Ree.LargeReeHeightQuotient

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag

variable {K : Type} [Field K] (a : ℕ)

theorem torusWeight_ne_one_of_not_dvd
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {β : Fin F4.tag.rank → ℤ}
    (h : ¬ ((2 * (2 ^ a : ℤ) ^ 2 - 1) ∣ torusExp0 (2 ^ a) β ∧
      (2 * (2 ^ a : ℤ) ^ 2 - 1) ∣ torusExp1 (2 ^ a) β)) :
    torusWeight (K := K) a β ≠ 1 := by
  intro h1
  obtain ⟨g, hg⟩ := exists_orderOf_eq_card_sub_one (K := K)
  have hN : ((orderOf g : ℕ) : ℤ) = 2 * (2 ^ a : ℤ) ^ 2 - 1 := by
    rw [hg, hK, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      two_pow_two_mul_add_one a, add_sub_cancel_right]
  have h0 : g ^ torusExp0 (2 ^ a) β = 1 := by
    rw [← torusWeight_fst, h1, MonoidHom.one_apply]
  have h1' : g ^ torusExp1 (2 ^ a) β = 1 := by
    rw [← torusWeight_snd, h1, MonoidHom.one_apply]
  rw [← orderOf_dvd_iff_zpow_eq_one, hN] at h0 h1'
  exact h ⟨h0, h1'⟩

theorem torusWeight_form_eq_zero_of
    [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {α β : Fin F4.tag.rank → ℤ}
    (hnd : ∀ i j : ℕ, i < 2 * a + 1 → j < 2 * a + 1 →
      ¬ ((2 * (2 ^ a : ℤ) ^ 2 - 1) ∣ 2 ^ i * torusExp0 (2 ^ a) α + 2 ^ j * torusExp0 (2 ^ a) β ∧
        (2 * (2 ^ a : ℤ) ^ 2 - 1) ∣ 2 ^ i * torusExp1 (2 ^ a) α + 2 ^ j * torusExp1 (2 ^ a) β))
    (F : K → K → ZMod 2) (hF₁ : ∀ c₁ c₂ d, F (c₁ + c₂) d = F c₁ d + F c₂ d)
    (hF₂ : ∀ c d₁ d₂, F c (d₁ + d₂) = F c d₁ + F c d₂)
    (hFT : ∀ (t : Kˣ × Kˣ) c d,
      F ((torusWeight a α t : K) * c) ((torusWeight a β t : K) * d) = F c d) :
    ∀ c d, F c d = 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ι : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hι : Function.Injective ι := ι.injective
  let G : K →+ K →+ K := AddMonoidHom.mk'
    (fun c => AddMonoidHom.mk' (fun d => ι (F c d)) fun d₁ d₂ => by rw [hF₂, map_add])
    fun c₁ c₂ => by
      ext d
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [hF₁, map_add]
  have hG : ∀ c d, G c d = ι (F c d) := fun _ _ => rfl
  obtain ⟨-, h2, -⟩ := CFSG.LocalAnalysis.ComponentInitial.finite_field_linearized_map_bases
    Nat.prime_two (n := 2 * a + 1) (by omega) hK
  obtain ⟨A, hA, hAuniq⟩ := h2 G
  have hcoef : ∀ (t : Kˣ × Kˣ) (i j : Fin (2 * a + 1)),
      A i j * ((torusWeight a α t : K) ^ 2 ^ (i : ℕ) * (torusWeight a β t : K) ^ 2 ^ (j : ℕ)) =
        A i j := by
    intro t
    have huniq := hAuniq
      (fun i j => A i j * ((torusWeight a α t : K) ^ 2 ^ (i : ℕ) *
        (torusWeight a β t : K) ^ 2 ^ (j : ℕ))) fun x y => by
      have h1 : G x y = G ((torusWeight a α t : K) * x) ((torusWeight a β t : K) * y) := by
        rw [hG, hG, hFT]
      rw [h1, hA]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow, mul_pow]
      ring
    intro i j
    exact congrFun (congrFun huniq i) j
  have hA0 : ∀ i j, A i j = 0 := by
    intro i j
    by_contra hne
    have key : ∀ t : Kˣ × Kˣ, ((torusWeight a α t ^ 2 ^ (i : ℕ) *
        torusWeight a β t ^ 2 ^ (j : ℕ) : Kˣ) : K) = 1 := fun t => by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
      exact (mul_eq_left₀ hne).1 (hcoef t i j)
    obtain ⟨g, hg⟩ := exists_orderOf_eq_card_sub_one (K := K)
    have hN : ((orderOf g : ℕ) : ℤ) = 2 * (2 ^ a : ℤ) ^ 2 - 1 := by
      rw [hg, hK, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
        two_pow_two_mul_add_one a, add_sub_cancel_right]
    have hdvd : ∀ (e e' : ℤ), ((g ^ e) ^ 2 ^ (i : ℕ) * (g ^ e') ^ 2 ^ (j : ℕ) : Kˣ) = 1 →
        (2 * (2 ^ a : ℤ) ^ 2 - 1) ∣ 2 ^ (i : ℕ) * e + 2 ^ (j : ℕ) * e' := by
      intro e e' he
      rw [← hN, orderOf_dvd_iff_zpow_eq_one, zpow_add, mul_comm ((2 : ℤ) ^ (i : ℕ)),
        mul_comm ((2 : ℤ) ^ (j : ℕ)), zpow_mul, zpow_mul]
      exact_mod_cast he
    refine hnd i j i.2 j.2 ⟨hdvd _ _ ?_, hdvd _ _ ?_⟩
    · have h := key (g, 1)
      rw [torusWeight_fst, torusWeight_fst] at h
      exact Units.val_eq_one.1 h
    · have h := key (1, g)
      rw [torusWeight_snd, torusWeight_snd] at h
      exact Units.val_eq_one.1 h
  intro c d
  have h0 : G c d = 0 := by
    rw [hA]
    simp [hA0]
  exact hι (by rw [map_zero, ← hG]; exact h0)

theorem heightQuot_prod_smul_eq_one_of
    [Fintype (Kˣ × Kˣ)]
    (hχ : ∀ β : Fin F4.tag.rank → ℤ, IsRoot F4.tag β → 0 < height β →
      torusWeight (K := K) a β ≠ 1) {h : ℤ} (q : HeightQuot K h) :
    ∏ t : Kˣ × Kˣ, heightQuotSmul a h t q = 1 := by
  induction q using heightQuot_induction with
  | hgen α hα c =>
    have hsum : ∑ t : Kˣ × Kˣ, (torusWeight a α t : K) = 0 := by
      refine sum_hom_units_eq_zero ((Units.coeHom K).comp (torusWeight a α)) fun h1 => ?_
      refine hχ α hα.1 hα.2.1 (MonoidHom.ext fun t => Units.ext ?_)
      exact DFunLike.congr_fun h1 t
    simp only [heightQuotSmul_rootElt]
    rw [← map_prod, ← ofAdd_sum, ← Finset.sum_mul, hsum, zero_mul, ofAdd_zero, map_one]
  | hone => simp
  | hmul q q' hq hq' => simp only [map_mul, Finset.prod_mul_distrib, hq, hq', mul_one]
  | hinv q hq => simp only [map_inv, Finset.prod_inv_distrib, hq, inv_one]

theorem mem_heightSeries_succ_of_forall_of
    [Finite K] [CharP K 2]
    (hT : Odd (Nat.card (Kˣ × Kˣ)))
    (hχ : ∀ β : Fin F4.tag.rank → ℤ, IsRoot F4.tag β → 0 < height β →
      torusWeight (K := K) a β ≠ 1) {h : ℤ} {x : (Module.End K (RootModule F4.tag K))ˣ}
    (hx : x ∈ heightSeries F4.tag K h)
    (hfix : ∀ t : Kˣ × Kˣ,
      (torusPair a t * x * (torusPair a t)⁻¹)⁻¹ * x ∈ heightSeries F4.tag K (h + 1)) :
    x ∈ heightSeries F4.tag K (h + 1) := by
  classical
  have := Fintype.ofFinite (Kˣ × Kˣ)
  set q : HeightQuot K h := QuotientGroup.mk ⟨x, hx⟩ with hq
  have hsmul : ∀ t, heightQuotSmul a h t q = q := fun t => by
    rw [hq, heightQuotSmul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hfix t
  have hprod := heightQuot_prod_smul_eq_one_of a hχ q
  simp only [hsmul, Finset.prod_const, Finset.card_univ] at hprod
  obtain ⟨k, hk⟩ := hT
  rw [← Nat.card_eq_fintype_card, hk, pow_succ, pow_mul, heightQuot_sq_eq_one, one_pow,
    one_mul] at hprod
  rw [hq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hprod
  exact hprod

theorem f4_eight_char_check : ∀ k < F4.tag.rootCertificate.roots.length,
    0 < height (F4.tag.rootCertificate.root k) →
    ¬ ((7 : ℤ) ∣ torusExp0 2 (F4.tag.rootCertificate.root k) ∧
      (7 : ℤ) ∣ torusExp1 2 (F4.tag.rootCertificate.root k)) := by
  decide +kernel

theorem torusWeight_ne_one_eight
    [Finite K] (hK : Nat.card K = 2 ^ (2 * 1 + 1))
    {β : Fin F4.tag.rank → ℤ} (hβ : IsRoot F4.tag β) (hβp : 0 < height β) :
    torusWeight (K := K) 1 β ≠ 1 := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check F4.tag)).1 hβ
  exact torusWeight_ne_one_of_not_dvd 1 hK (f4_eight_char_check k hk hβp)

end CFSG.LieType.Ree.LargeReeCover
