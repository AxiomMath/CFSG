module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveLang

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.CrossChar

section Dichotomy

variable {C : Type*} [Group C] [Finite C] {p : ℕ}

theorem conj_pow_mem_of_normalizes {T : Subgroup C} {v : C} (hvT : ∀ t ∈ T, v * t * v⁻¹ ∈ T) :
    ∀ k : ℕ, ∀ t ∈ T, v ^ k * t * (v ^ k)⁻¹ ∈ T := by
  intro k
  induction k with
  | zero => intro t ht; simpa using ht
  | succ k ih =>
    intro t ht
    have := hvT _ (ih t ht)
    simpa [pow_succ', mul_assoc] using this

def semiProdSub (T : Subgroup C) (v : C) (hvT : ∀ t ∈ T, v * t * v⁻¹ ∈ T) : Subgroup C where
  carrier := {x | ∃ t ∈ T, ∃ k : ℕ, x = t * v ^ k}
  one_mem' := ⟨1, T.one_mem, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨t₁, ht₁, k₁, rfl⟩ ⟨t₂, ht₂, k₂, rfl⟩
    refine ⟨t₁ * (v ^ k₁ * t₂ * (v ^ k₁)⁻¹),
      T.mul_mem ht₁ (conj_pow_mem_of_normalizes hvT k₁ t₂ ht₂), k₁ + k₂, ?_⟩
    rw [pow_add]
    group
  inv_mem' := by
    intro x hx
    have hmul : ∀ y ∈ ({x | ∃ t ∈ T, ∃ k : ℕ, x = t * v ^ k} : Set C),
        ∀ z ∈ ({x | ∃ t ∈ T, ∃ k : ℕ, x = t * v ^ k} : Set C),
        y * z ∈ ({x | ∃ t ∈ T, ∃ k : ℕ, x = t * v ^ k} : Set C) := by
      rintro _ ⟨t₁, ht₁, k₁, rfl⟩ _ ⟨t₂, ht₂, k₂, rfl⟩
      refine ⟨t₁ * (v ^ k₁ * t₂ * (v ^ k₁)⁻¹),
        T.mul_mem ht₁ (conj_pow_mem_of_normalizes hvT k₁ t₂ ht₂), k₁ + k₂, ?_⟩
      rw [pow_add]
      group
    have hpow : ∀ n : ℕ, x ^ n ∈ ({x | ∃ t ∈ T, ∃ k : ℕ, x = t * v ^ k} : Set C) := by
      intro n
      induction n with
      | zero => exact ⟨1, T.one_mem, 0, by simp⟩
      | succ n ih => rw [pow_succ]; exact hmul _ ih _ hx
    have hinv : x⁻¹ = x ^ (orderOf x - 1) := by
      have h1 : x ^ (orderOf x - 1) * x = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
      exact (eq_inv_of_mul_eq_one_left h1).symm
    rw [hinv]
    exact hpow _

theorem le_semiProdSub (T : Subgroup C) (v : C) (hvT : ∀ t ∈ T, v * t * v⁻¹ ∈ T) :
    T ≤ semiProdSub T v hvT := fun t ht => ⟨t, ht, 0, by simp⟩

theorem v_mem_semiProdSub (T : Subgroup C) (v : C) (hvT : ∀ t ∈ T, v * t * v⁻¹ ∈ T) :
    v ∈ semiProdSub T v hvT := ⟨1, T.one_mem, 1, by simp⟩

theorem normal_subgroupOf_semiProdSub (T : Subgroup C) (v : C)
    (hvT : ∀ t ∈ T, v * t * v⁻¹ ∈ T) : (T.subgroupOf (semiProdSub T v hvT)).Normal := by
  refine ⟨fun n hn y => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨t₁, ht₁, k, hy⟩ := y.2
  have hy' : (y : C) = t₁ * v ^ k := hy
  have : (y : C) * n * (y : C)⁻¹ = t₁ * ((v ^ k) * n * (v ^ k)⁻¹) * t₁⁻¹ := by
    rw [hy']; group
  show (y : C) * (n : C) * (y : C)⁻¹ ∈ T
  rw [this]
  exact T.mul_mem (T.mul_mem ht₁ (conj_pow_mem_of_normalizes hvT k _ hn)) (T.inv_mem ht₁)

theorem card_semiProdSub (hp : p.Prime) (T : Subgroup C) (v : C)
    (hvT : ∀ t ∈ T, v * t * v⁻¹ ∈ T) (hvp : v ^ p ∈ T) (hvn : v ∉ T) :
    Nat.card (semiProdSub T v hvT) = Nat.card T * p := by
  classical
  set N := semiProdSub T v hvT with hN
  haveI hnorm : (T.subgroupOf N).Normal := normal_subgroupOf_semiProdSub T v hvT
  have hTN : T ≤ N := le_semiProdSub T v hvT
  have hvN : v ∈ N := v_mem_semiProdSub T v hvT
  set vN : N := ⟨v, hvN⟩ with hvNdef
  set vbar : N ⧸ T.subgroupOf N := QuotientGroup.mk vN with hvbar
  have hsurj : Subgroup.zpowers vbar = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    induction x using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨t, ht, k, hy⟩ := y.2
      refine ⟨k, ?_⟩
      show vbar ^ (k : ℤ) = QuotientGroup.mk y
      rw [zpow_natCast, hvbar, ← QuotientGroup.mk_pow, QuotientGroup.eq_iff_div_mem,
        Subgroup.mem_subgroupOf]
      have hdiv : (((vN ^ k) / y : N) : C) = t⁻¹ := by
        have hy' : (y : C) = t * v ^ k := hy
        rw [Subgroup.coe_div, Subgroup.coe_pow, hy']
        show v ^ k / (t * v ^ k) = t⁻¹
        rw [div_eq_mul_inv, mul_inv_rev]
        exact mul_inv_cancel_left _ _
      rw [hdiv]
      exact T.inv_mem ht
  have hne : vbar ≠ 1 := by
    intro h
    rw [hvbar, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact hvn h
  have hpow : vbar ^ p = 1 := by
    rw [hvbar, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hvp
  have hord : orderOf vbar = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hpow) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hne
    · exact h
  have hq : Nat.card (N ⧸ T.subgroupOf N) = p := by
    rw [← hord, ← Nat.card_zpowers, hsurj, Subgroup.card_top]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf N), hq,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv, mul_comm]

theorem exists_conj_dichotomy (hp : p.Prime) (T : Subgroup C)
    (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (v : C) (hvT : ∀ t ∈ T, v * t * v⁻¹ ∈ T)
    (hvp : v ^ p ∈ T) (hvn : v ∉ T)
    (hord : (Nat.card C).factorization p = (Nat.card T).factorization p + 1)
    {A : Subgroup C} (hAp : ∀ x ∈ A, x ^ p = 1) (hAc : Nat.card A = p ^ 2) :
    ∃ c : C, (∀ x ∈ A, c * x * c⁻¹ ∈ T) ∨
      ∃ u ∈ A, c * u * c⁻¹ ∈ T ∧ c * u * c⁻¹ ≠ 1 ∧ ∃ k : ℕ, ¬ p ∣ k ∧
        v ^ k * (c * u * c⁻¹) = (c * u * c⁻¹) * v ^ k := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set N := semiProdSub T v hvT with hN
  haveI hnorm : (T.subgroupOf N).Normal := normal_subgroupOf_semiProdSub T v hvT
  have hTN : T ≤ N := le_semiProdSub T v hvT
  have hcard : Nat.card N = Nat.card T * p := card_semiProdSub hp T v hvT hvp hvn
  have hTpos : 0 < Nat.card T := Nat.card_pos
  obtain ⟨P⟩ : Nonempty (Sylow p N) := inferInstance
  have hPcard : Nat.card (P.map N.subtype) = p ^ (Nat.card C).factorization p := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity, hcard,
      Nat.factorization_mul hTpos.ne' hp.ne_zero, Finsupp.add_apply, hp.factorization_self, ← hord]
  set Psyl : Sylow p C := Sylow.ofCard (P.map N.subtype) hPcard with hPsyl
  have hAP : IsPGroup p A := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hAp x x.2)⟩
  obtain ⟨Q, hAQ⟩ := hAP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C Psyl Q
  have hmemN : ∀ x ∈ A, g⁻¹ * x * g⁻¹⁻¹ ∈ N := by
    intro x hx
    have hxQ : x ∈ (Q : Subgroup C) := hAQ hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
    obtain ⟨s, hs, hsx⟩ := hxQ
    have hs' : s ∈ (Psyl : Subgroup C) := hs
    rw [hPsyl, Sylow.coe_ofCard] at hs'
    obtain ⟨n, -, rfl⟩ := hs'
    have : g⁻¹ * x * g⁻¹⁻¹ = (n : C) := by
      rw [← hsx]
      show g⁻¹ * (g * (n : C) * g⁻¹) * g⁻¹⁻¹ = n
      group
    rw [this]
    exact n.2
  refine ⟨g⁻¹, ?_⟩
  by_cases hall : ∀ x ∈ A, g⁻¹ * x * g⁻¹⁻¹ ∈ T
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨x₀, hx₀A, hx₀T⟩ := hall
  let f : A →* N :=
    { toFun := fun x => ⟨g⁻¹ * x * g⁻¹⁻¹, hmemN x x.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun x y => by apply Subtype.ext; simp [mul_assoc] }
  let ψ : A →* N ⧸ T.subgroupOf N := (QuotientGroup.mk' (T.subgroupOf N)).comp f
  have hq : Nat.card (N ⧸ T.subgroupOf N) = p := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf N)
    rw [hcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv,
      mul_comm (Nat.card (N ⧸ T.subgroupOf N))] at h1
    exact (Nat.eq_of_mul_eq_mul_left hTpos h1).symm
  have hnotinj : ¬ Function.Injective ψ := by
    intro hinj
    have := Nat.card_le_card_of_injective ψ hinj
    rw [hAc, hq] at this
    have h2 := hp.two_le
    nlinarith
  rw [injective_iff_map_eq_one] at hnotinj
  push Not at hnotinj
  obtain ⟨a, ha1, ha⟩ := hnotinj
  have hu'T : g⁻¹ * (a : C) * g⁻¹⁻¹ ∈ T := by
    have : f a ∈ T.subgroupOf N := (QuotientGroup.eq_one_iff _).1 ha1
    exact this
  refine ⟨a, a.2, hu'T, ?_, ?_⟩
  · intro h
    apply ha
    have : (a : C) = 1 := by
      have := congrArg (fun z => g * z * g⁻¹) h
      simpa [mul_assoc] using this
    exact Subtype.ext this
  · obtain ⟨t₀, ht₀, k, hk⟩ := hmemN x₀ hx₀A
    have hkp : ¬ p ∣ k := by
      rintro ⟨m, rfl⟩
      apply hx₀T
      rw [hk, pow_mul]
      exact T.mul_mem ht₀ (T.pow_mem hvp m)
    refine ⟨k, hkp, ?_⟩
    have hA : IsMulCommutative A :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) (G := A) hAc
    have hcomm : (x₀ : C) * a = a * x₀ :=
      congrArg Subtype.val (hA.is_comm.comm ⟨x₀, hx₀A⟩ a)
    have hcomm' : (g⁻¹ * x₀ * g⁻¹⁻¹) * (g⁻¹ * (a : C) * g⁻¹⁻¹) =
        (g⁻¹ * (a : C) * g⁻¹⁻¹) * (g⁻¹ * x₀ * g⁻¹⁻¹) := by
      calc (g⁻¹ * x₀ * g⁻¹⁻¹) * (g⁻¹ * (a : C) * g⁻¹⁻¹) = g⁻¹ * (x₀ * a) * g⁻¹⁻¹ := by group
        _ = g⁻¹ * (a * x₀) * g⁻¹⁻¹ := by rw [hcomm]
        _ = (g⁻¹ * (a : C) * g⁻¹⁻¹) * (g⁻¹ * x₀ * g⁻¹⁻¹) := by group
    rw [hk] at hcomm'
    have htu := hTc t₀ ht₀ _ hu'T
    refine mul_left_cancel (a := t₀) ?_
    set u' : C := g⁻¹ * (a : C) * g⁻¹⁻¹ with hu'
    calc t₀ * (v ^ k * u') = t₀ * v ^ k * u' := (mul_assoc _ _ _).symm
      _ = u' * (t₀ * v ^ k) := hcomm'
      _ = (u' * t₀) * v ^ k := (mul_assoc _ _ _).symm
      _ = (t₀ * u') * v ^ k := by rw [htu]
      _ = t₀ * (u' * v ^ k) := mul_assoc _ _ _

end Dichotomy

section Balance

variable {C : Type*} [Group C] [Finite C] {p : ℕ}

theorem innerPlaneBalance_of_dichotomy (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) (T : Subgroup C)
    (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (v : C) (hvT : ∀ t ∈ T, v * t * v⁻¹ ∈ T)
    (hvp : v ^ p ∈ T) (hvn : v ∉ T)
    (hord : (Nat.card C).factorization p = (Nat.card T).factorization p + 1)
    (hresT : ∀ D₁ : Subgroup C, (∀ x ∈ D₁, x ^ p = 1) → p < Nat.card D₁ → D₁ ≤ T →
      ∀ H : Subgroup (MulAut C), innerAut C ≤ H →
        localDeltaIn p H (D₁.map (MulAut.conj : C →* MulAut C)) = ⊥)
    (hresQ : ∀ u ∈ T, u ≠ 1 → u ^ p = 1 → (∃ k : ℕ, ¬ p ∣ k ∧ v ^ k * u = u * v ^ k) →
      ∀ H : Subgroup (MulAut C), innerAut C ≤ H →
        localDeltaIn p H ((Subgroup.zpowers u).map (MulAut.conj : C →* MulAut C)) = ⊥) :
    InnerPlaneBalance p C := by
  intro D hDin hD hcard H hH
  set D₀ : Subgroup C := D.comap (MulAut.conj : C →* MulAut C) with hD₀
  have hDD : D₀.map (MulAut.conj : C →* MulAut C) = D := Subgroup.map_comap_eq_self hDin
  have hD₀card : Nat.card D₀ = p ^ 2 := by
    rw [← hcard, ← hDD, Subgroup.card_map_of_injective hinj]
  have hpow₀ : ∀ x ∈ D₀, x ^ p = 1 := fun x hx => by
    have hx' : (MulAut.conj x) ^ p = 1 := hD.2 _ hx
    exact hinj (by rw [map_pow, hx', map_one])
  obtain ⟨c, hc⟩ := exists_conj_dichotomy hp T hTc v hvT hvp hvn hord hpow₀ hD₀card
  refine localDeltaIn_eq_bot_of_conj_sub hH (E := D₀) hDD.le c ?_
  set D₁ : Subgroup C := D₀.map (MulAut.conj c).toMonoidHom with hD₁
  have hpow₁ : ∀ x ∈ D₁, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show (c * x * c⁻¹) ^ p = 1
    rw [conj_pow, hpow₀ x hx, mul_one, mul_inv_cancel]
  have hcard₁ : Nat.card D₁ = p ^ 2 := by
    rw [hD₁, Subgroup.card_map_of_injective (MulAut.conj c).injective, hD₀card]
  rcases hc with hT | ⟨u, hu, huT, hu1, k, hk, hkc⟩
  · refine hresT D₁ hpow₁ ?_ ?_ H hH
    · rw [hcard₁]
      have := hp.two_le
      nlinarith
    · rintro _ ⟨x, hx, rfl⟩
      exact hT x hx
  · have hu₁ : c * u * c⁻¹ ∈ D₁ := ⟨u, hu, rfl⟩
    have hle : Subgroup.zpowers (c * u * c⁻¹) ≤ D₁ := by
      rw [Subgroup.zpowers_le]
      exact hu₁
    refine le_bot_iff.1 ((localDeltaIn_antitone H (Subgroup.map_mono hle)).trans ?_)
    refine le_of_eq (hresQ _ huT hu1 (hpow₁ _ hu₁) ⟨k, hk, hkc⟩ H hH)

end Balance

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
