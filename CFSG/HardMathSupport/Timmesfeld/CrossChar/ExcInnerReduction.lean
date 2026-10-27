module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldE67Odd
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldEven
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldEvenF4G2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldOdd
public import CFSG.RankThree.Chevalley.SteinbergCFOddE8InnerField

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

section Inner

variable {K K' : Type*} [Group K] [Group K'] {p : ℕ}

@[expose] def IsInnerLocallyBalanced (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ D : Subgroup (MulAut K), IsElemAbelian p D → Nat.card D = p ^ 3 → D ≤ innerAut K →
    ∀ H : Subgroup (MulAut K), innerAut K ≤ H → D ≤ Subgroup.normalizer (H : Set (MulAut K)) →
      localDeltaIn p H D = ⊥

theorem IsLocallyBalancedAbs.isInnerLocallyBalanced (h : IsLocallyBalancedAbs p 3 K) :
    IsInnerLocallyBalanced p K := fun D hD hcard _ H hH hDH => h D hD hcard H hH hDH

theorem IsInnerLocallyBalanced.of_mulEquiv (e : K ≃* K') (h : IsInnerLocallyBalanced p K') :
    IsInnerLocallyBalanced p K := by
  intro D hD hcard hDin H hH hDH
  set ψ : MulAut K →* MulAut K' := (MulAut.congr e).toMonoidHom with hψdef
  have hψ : Function.Injective ψ := (MulAut.congr e).injective
  have hconj : ∀ x : K, ψ (MulAut.conj x) = MulAut.conj (e x) := fun x => by
    ext z
    simp [hψdef, MulAut.congr_apply, MulAut.conj_apply]
  have hinn : innerAut K' ≤ (innerAut K).map ψ := by
    rintro _ ⟨y, rfl⟩
    exact ⟨MulAut.conj (e.symm y), ⟨e.symm y, rfl⟩, by rw [hconj, MulEquiv.apply_symm_apply]⟩
  have hD' : IsElemAbelian p (D.map ψ) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      apply Subtype.ext
      change ψ x * ψ y = ψ y * ψ x
      have := congrArg Subtype.val (hD.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [← map_mul, ← map_mul]
      exact congrArg ψ this
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hD.2 x hx, map_one]
  have hcard' : Nat.card (D.map ψ) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective hψ, hcard]
  have hDin' : D.map ψ ≤ innerAut K' := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, rfl⟩ := hDin hx
    exact ⟨e y, (hconj y).symm⟩
  have hH' : innerAut K' ≤ H.map ψ := hinn.trans (Subgroup.map_mono hH)
  have hDH' : D.map ψ ≤ Subgroup.normalizer ((H.map ψ : Subgroup (MulAut K')) : Set (MulAut K')) :=
    (Subgroup.map_mono hDH).trans (Subgroup.le_normalizer_map ψ)
  have h0 := h (D.map ψ) hD' hcard' hDin' (H.map ψ) hH' hDH'
  have hle := map_localDeltaIn_le p ψ hψ H D
  rw [h0, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ hψ] at hle
  exact hle

theorem isLocallyBalancedAbs_of_inner_of_fieldCore [Finite K] (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) (hin : IsInnerLocallyBalanced p K)
    (hfc : ∀ x : MulAut K, x ^ p = 1 → x ∉ innerAut K → FieldCoreAt p x) :
    IsLocallyBalancedAbs p 3 K := by
  intro D hD hcard H hH hDH
  by_cases hDin : D ≤ innerAut K
  · exact hin D hD hcard hDin H hH hDH
  · obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
    have hx1 : x ≠ 1 := fun h => hxin (by rw [h]; exact one_mem _)
    exact localDeltaIn_eq_bot_of_fieldCore hp hinj hH hxD hx1 (hfc x (hD.2 x hxD) hxin)

@[expose] def CrossCharInnerAt (k : LieFamily) (R : TauCeti.ValidLieTypeIndex → ℕ → Prop) : Prop :=
  ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 → ∀ p : ℕ, p.Prime → p ≠ 2 →
    idx.1.characteristic ≠ p → R idx p → IsInnerLocallyBalanced p (Cat idx)

theorem CrossCharFamAt.innerAt {k : LieFamily} {R : TauCeti.ValidLieTypeIndex → ℕ → Prop}
    (h : CrossCharFamAt k R) : CrossCharInnerAt k R := fun idx hk p hp hp2 hc hR =>
  IsLocallyBalancedAbs.isInnerLocallyBalanced (h idx hk p hp hp2 hc hR)

end Inner

section Orders

theorem exists_degree_of_degCount_pos {τ : Tag} {e : ℕ} (h : 0 < degCount τ e) :
    ∃ d ∈ degreesW τ, e ∣ d := by
  obtain ⟨d, hd⟩ := List.exists_mem_of_length_pos h
  rw [List.mem_filter] at hd
  exact ⟨d, hd.1, by simpa using hd.2⟩

theorem dvd_div_of_dvd_of_coprime {p N g : ℕ} (hg : g ∣ N) (hcop : Nat.Coprime p g)
    (h : p ∣ N) : p ∣ N / g := by
  obtain ⟨c, rfl⟩ := hg
  rcases Nat.eq_zero_or_pos g with rfl | hg0
  · simp
  · rw [Nat.mul_div_cancel_left c hg0]
    exact hcop.dvd_of_dvd_mul_left h

theorem sub_one_dvd_sq_sub_one (q : ℕ) : q - 1 ∣ q ^ 2 - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow q 1 2

theorem dvd_ordE8_of_degCount_pos {p q : ℕ} (hq : 1 ≤ q)
    (h : 0 < degCount Tag.E8 (orderOf ((q : ℕ) : ZMod p))) : p ∣ ordE8 q := by
  obtain ⟨d, hd, hed⟩ := exists_degree_of_degCount_pos h
  refine (dvd_pow_sub_one_of_orderOf hq rfl hed).trans ?_
  change d ∈ [2, 8, 12, 14, 18, 20, 24, 30] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  unfold ordE8
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    repeat (first | exact dvd_mul_left _ _ | apply dvd_mul_of_dvd_left)

theorem dvd_ordF4_of_degCount_pos {p q : ℕ} (hq : 1 ≤ q)
    (h : 0 < degCount Tag.F4 (orderOf ((q : ℕ) : ZMod p))) : p ∣ ordF4 q := by
  obtain ⟨d, hd, hed⟩ := exists_degree_of_degCount_pos h
  refine (dvd_pow_sub_one_of_orderOf hq rfl hed).trans ?_
  change d ∈ [2, 6, 8, 12] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  unfold ordF4
  rcases hd with rfl | rfl | rfl | rfl <;>
    repeat (first | exact dvd_mul_left _ _ | apply dvd_mul_of_dvd_left)

theorem dvd_ordE7_of_degCount_pos {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 ≤ q)
    (h : 0 < degCount Tag.E7 (orderOf ((q : ℕ) : ZMod p))) : p ∣ ordE7 q := by
  obtain ⟨d, hd, hed⟩ := exists_degree_of_degCount_pos h
  have h1 := dvd_pow_sub_one_of_orderOf hq rfl hed
  unfold ordE7
  refine dvd_div_of_dvd_of_coprime ?_ ?_ ?_
  · exact (Nat.gcd_dvd_right 2 (q - 1)).trans ((sub_one_dvd_sq_sub_one q).trans
      (dvd_mul_left _ _))
  · exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 2 (q - 1))
      ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  · refine h1.trans ?_
    change d ∈ [2, 6, 8, 10, 12, 14, 18] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      repeat (first | exact dvd_mul_left _ _ | apply dvd_mul_of_dvd_left)

theorem dvd_ordE6_of_degCount_pos {p q : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hq : 1 ≤ q)
    (h : 0 < degCount Tag.E6 (orderOf ((q : ℕ) : ZMod p))) : p ∣ ordE6 q := by
  obtain ⟨d, hd, hed⟩ := exists_degree_of_degCount_pos h
  have h1 := dvd_pow_sub_one_of_orderOf hq rfl hed
  unfold ordE6
  refine dvd_div_of_dvd_of_coprime ?_ ?_ ?_
  · exact (Nat.gcd_dvd_right 3 (q - 1)).trans ((sub_one_dvd_sq_sub_one q).trans
      (dvd_mul_left _ _))
  · exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 (q - 1))
      ((Nat.coprime_primes hp Nat.prime_three).2 hp3)
  · refine h1.trans ?_
    change d ∈ [2, 5, 6, 8, 9, 12] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      repeat (first | exact dvd_mul_left _ _ | apply dvd_mul_of_dvd_left)

end Orders

section Cores


theorem isLocallyBalancedAbs_adjoint_of_inner_of_fieldCore {τ : Tag} (K : Type) [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (hin : IsInnerLocallyBalanced p (adjointGroup τ K))
    (hfc : ∀ x : MulAut (adjointGroup τ K), orderOf x = p →
      x ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range →
        FieldCoreAt p x) :
    IsLocallyBalancedAbs p 3 (adjointGroup τ K) := by
  have : Finite (ModGL τ K) := finite_modGL
  have hinj := mulAut_conj_injective_of_center_eq_bot
    (center_adjointGroup_eq_bot (τ := τ) (K := K))
  refine isLocallyBalancedAbs_of_inner_of_fieldCore hp hinj hin fun x hxp hxo => ?_
  have : Fact p.Prime := ⟨hp⟩
  exact hfc x (orderOf_eq_prime hxp fun h => hxo (by rw [h]; exact one_mem _)) hxo

theorem fieldCoreAt_adjointE8 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hcnt : 0 < degCount Tag.E8 (orderOf ((Nat.card K : ℕ) : ZMod p)))
    {x : MulAut (adjointGroup Tag.E8 K)} (hxp : orderOf x = p)
    (hxo : x ∉ (MulAut.conj : adjointGroup Tag.E8 K →* MulAut (adjointGroup Tag.E8 K)).range) :
    FieldCoreAt p x := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
      ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.E8 (fixSubfield σ))) := by
    intro σ hσp
    have : Finite (fixSubfield σ) := Subtype.finite
    rw [← Nat.Prime.dvd_iff_not_coprime hp,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8]
    refine dvd_ordE8_of_degCount_pos Nat.card_pos ?_
    rw [card_fixSubfield_cast hℓ hf hK hp hσp]
    exact hcnt
  by_cases h2 : ℓ = 2
  · subst h2
    exact fieldCoreAt_E78_even Tag.E8 (Or.inr rfl) hf K hK hp hdvd hxp hxo
  · exact fieldCoreAt_of_oddInnerField hℓ h2 hf K hK
      (odd_E8_inner_field_automorphisms_and_noninner_prime_core hℓ h2 hf K hK).1 hp hdvd hxp hxo

theorem fieldCoreAt_adjointE7 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcnt : 0 < degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p)))
    {x : MulAut (adjointGroup Tag.E7 K)} (hxp : orderOf x = p)
    (hxo : x ∉ (MulAut.conj : adjointGroup Tag.E7 K →* MulAut (adjointGroup Tag.E7 K)).range) :
    FieldCoreAt p x := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
      ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.E7 (fixSubfield σ))) := by
    intro σ hσp
    have : Finite (fixSubfield σ) := Subtype.finite
    rw [← Nat.Prime.dvd_iff_not_coprime hp,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7]
    refine dvd_ordE7_of_degCount_pos hp hp2 Nat.card_pos ?_
    rw [card_fixSubfield_cast hℓ hf hK hp hσp]
    exact hcnt
  by_cases h2 : ℓ = 2
  · subst h2
    exact fieldCoreAt_E78_even Tag.E7 (Or.inl rfl) hf K hK hp hdvd hxp hxo
  · exact fieldCoreAt_E7_odd hℓ h2 hf K hK hp hp2 hdvd hxp hxo

theorem fieldCoreAt_adjointE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hcnt : 0 < degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p)))
    {x : MulAut (adjointGroup Tag.E6 K)} (hxp : orderOf x = p)
    (hxo : x ∉ (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range) :
    FieldCoreAt p x := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
      ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.E6 (fixSubfield σ))) := by
    intro σ hσp
    have : Finite (fixSubfield σ) := Subtype.finite
    rw [← Nat.Prime.dvd_iff_not_coprime hp,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6]
    refine dvd_ordE6_of_degCount_pos hp (by omega) Nat.card_pos ?_
    rw [card_fixSubfield_cast hℓ hf hK hp hσp]
    exact hcnt
  by_cases h2 : ℓ = 2
  · subst h2
    exact fieldCoreAt_E6_even hf K hK hp hp3 hdvd hxp hxo
  · exact fieldCoreAt_E6_odd hℓ h2 hf K hK hp hp3 hdvd hxp hxo

theorem fieldCoreAt_adjointF4 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcnt : 0 < degCount Tag.F4 (orderOf ((Nat.card K : ℕ) : ZMod p)))
    {x : MulAut (adjointGroup Tag.F4 K)} (hxp : orderOf x = p)
    (hxo : x ∉ (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)).range) :
    FieldCoreAt p x := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
      ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.F4 (fixSubfield σ))) := by
    intro σ hσp
    have : Finite (fixSubfield σ) := Subtype.finite
    rw [← Nat.Prime.dvd_iff_not_coprime hp,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4]
    refine dvd_ordF4_of_degCount_pos Nat.card_pos ?_
    rw [card_fixSubfield_cast hℓ hf hK hp hσp]
    exact hcnt
  by_cases h2 : ℓ = 2
  · subst h2
    have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := by
      rw [show CFSG.LieType.Ree.ReeTag.F4.prime = 2 from rfl]
      exact finite_field_prime_power_characteristic Nat.prime_two hf hK
    exact fieldCoreAt_F4_even hf K hK hp hp2 hdvd hxp hxo
  · exact fieldCoreAt_of_oddInnerField hℓ h2 hf K hK (conj_normalForm_of_pointwise
      (odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ h2 hf K hK .F4
        (Or.inl rfl)).1) hp hdvd hxp hxo

end Cores

section Families


theorem crossCharFamAt_E8_ge_three_of_inner
    (h : CrossCharInnerAt .E8 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E8 q ∧
      3 ≤ degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p))) :
    CrossCharFamAt .E8 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E8 q ∧
      3 ≤ degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p)) := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc ⟨q, hd, hcnt⟩
  have hin := h ⟨d, hv⟩ hk p hp hp2 hc ⟨q, hd, hcnt⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  rw [← hK] at hcnt
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_adjoint_of_inner_of_fieldCore K
    hp (hin.of_mulEquiv e.symm) fun x hxp hxo =>
      fieldCoreAt_adjointE8 q.prime_p q.exponent_pos K hK' hp (by omega) hxp hxo)

theorem crossCharFamAt_E7_ge_three_of_inner
    (h : CrossCharInnerAt .E7 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧
      3 ≤ degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p))) :
    CrossCharFamAt .E7 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧
      3 ≤ degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p)) := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc ⟨q, hd, hcnt⟩
  have hin := h ⟨d, hv⟩ hk p hp hp2 hc ⟨q, hd, hcnt⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  rw [← hK] at hcnt
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_adjoint_of_inner_of_fieldCore K
    hp (hin.of_mulEquiv e.symm) fun x hxp hxo =>
      fieldCoreAt_adjointE7 q.prime_p q.exponent_pos K hK' hp hp2 (by omega) hxp hxo)

theorem crossCharFamAt_F4_ge_three_of_inner
    (h : CrossCharInnerAt .F4 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .F4 q ∧
      3 ≤ degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p))) :
    CrossCharFamAt .F4 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .F4 q ∧
      3 ≤ degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p)) := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc ⟨q, hd, hcnt⟩
  have hin := h ⟨d, hv⟩ hk p hp hp2 hc ⟨q, hd, hcnt⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  rw [← hK] at hcnt
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_adjoint_of_inner_of_fieldCore K
    hp (hin.of_mulEquiv e.symm) fun x hxp hxo =>
      fieldCoreAt_adjointF4 q.prime_p q.exponent_pos K hK' hp hp2 (by omega) hxp hxo)

theorem crossCharFamAt_E6_ge_three_of_inner
    (h : CrossCharInnerAt .E6 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E6 q ∧
      3 ≤ degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p)) ∧ 5 ≤ p) :
    CrossCharFamAt .E6 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E6 q ∧
      3 ≤ degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p)) ∧ 5 ≤ p := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc ⟨q, hd, hcnt, hp5⟩
  have hin := h ⟨d, hv⟩ hk p hp hp2 hc ⟨q, hd, hcnt, hp5⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  rw [← hK] at hcnt
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_adjoint_of_inner_of_fieldCore K
    hp (hin.of_mulEquiv e.symm) fun x hxp hxo =>
      fieldCoreAt_adjointE6 q.prime_p q.exponent_pos K hK' hp (by omega) (by omega) hxp hxo)

theorem crossCharFamAt_E6_ge_three_of
    (h5 : CrossCharInnerAt .E6 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E6 q ∧
      3 ≤ degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p)) ∧ 5 ≤ p)
    (h3 : CrossCharFamAt .E6 fun _ p => p = 3) :
    CrossCharFamAt .E6 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E6 q ∧
      3 ≤ degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p)) := by
  rintro idx hk p hp hp2 hc ⟨q, hd, hcnt⟩
  rcases eq_three_or_five_le hp hp2 with rfl | hp5
  · exact h3 idx hk 3 hp hp2 hc rfl
  · exact crossCharFamAt_E6_ge_three_of_inner h5 idx hk p hp hp2 hc ⟨q, hd, hcnt, hp5⟩

end Families

end CFSG.HardMathSupport.Timmesfeld.CrossChar
