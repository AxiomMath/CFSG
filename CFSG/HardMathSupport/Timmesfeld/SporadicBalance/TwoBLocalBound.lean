module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FixedFreeRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

variable {H Q : Type*} [Group H] [Group Q]

@[expose] noncomputable def centMap (K : Subgroup H) [K.Normal] (e : H ⧸ K ≃* Q) (x : H) :
    Subgroup.centralizer ({x} : Set H) →* Q :=
  (e.toMonoidHom.comp (QuotientGroup.mk' K)).comp (Subgroup.centralizer ({x} : Set H)).subtype

theorem centMap_apply (K : Subgroup H) [K.Normal] (e : H ⧸ K ≃* Q) (x : H)
    (h : Subgroup.centralizer ({x} : Set H)) : centMap K e x h = e (QuotientGroup.mk (h : H)) :=
  rfl

theorem mem_ker_centMap (K : Subgroup H) [K.Normal] (e : H ⧸ K ≃* Q) (x : H)
    (h : Subgroup.centralizer ({x} : Set H)) : h ∈ (centMap K e x).ker ↔ (h : H) ∈ K := by
  rw [MonoidHom.mem_ker, centMap_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem range_centMap_le (K : Subgroup H) [K.Normal] (e : H ⧸ K ≃* Q) (x : H) :
    (centMap K e x).range ≤ Subgroup.centralizer ({e (QuotientGroup.mk x)} : Set Q) := by
  rintro _ ⟨h, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, centMap_apply, ← map_mul, ← map_mul]
  congr 1
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    Subgroup.mem_centralizer_singleton_iff.1 h.2]

theorem card_centralizer_eq_mul [Finite H] (K : Subgroup H) [K.Normal] (e : H ⧸ K ≃* Q) (x : H) :
    Nat.card (Subgroup.centralizer ({x} : Set H)) =
      Nat.card (K ⊓ Subgroup.centralizer ({x} : Set H) : Subgroup H) *
        Nat.card (centMap K e x).range := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (centMap K e x).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (centMap K e x)).toEquiv] at h1
  have h2 : Nat.card (centMap K e x).ker =
      Nat.card (K ⊓ Subgroup.centralizer ({x} : Set H) : Subgroup H) := by
    refine Nat.card_congr
      { toFun := fun h => ⟨h.1.1, Subgroup.mem_inf.2 ⟨(mem_ker_centMap K e x h.1).1 h.2, h.1.2⟩⟩
        invFun := fun h => ⟨⟨h.1, (Subgroup.mem_inf.1 h.2).2⟩,
          (mem_ker_centMap K e x _).2 (Subgroup.mem_inf.1 h.2).1⟩
        left_inv := fun h => rfl
        right_inv := fun h => rfl }
  rw [h1, h2, mul_comm]

theorem card_centralizer_le_mul [Finite H] [Finite Q] (K : Subgroup H) [K.Normal]
    (e : H ⧸ K ≃* Q) (x : H) :
    Nat.card (Subgroup.centralizer ({x} : Set H)) ≤
      Nat.card (K ⊓ Subgroup.centralizer ({x} : Set H) : Subgroup H) *
        Nat.card (Subgroup.centralizer ({e (QuotientGroup.mk x)} : Set Q)) := by
  rw [card_centralizer_eq_mul K e x]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le (range_centMap_le K e x))

theorem eq_bot_of_odd_normal_centralizer [Finite H] [Finite Q] (K : Subgroup H) [K.Normal]
    (hK : IsPGroup 2 K) (e : H ⧸ K ≃* Q) {x : H}
    (hQ : Nat.card (Subgroup.centralizer ({e (QuotientGroup.mk x)} : Set Q)) ∣ 66)
    {w₀ e₀ : H} (hw₀ : w₀ ∈ Subgroup.centralizer ({x} : Set H)) (hw₃ : orderOf w₀ = 3)
    (he₀ : e₀ ∈ K ⊓ Subgroup.centralizer ({x} : Set H)) (hwe : w₀ * e₀ ≠ e₀ * w₀)
    {Y : Subgroup H} (hYC : Y ≤ Subgroup.centralizer ({x} : Set H))
    (hYn : ∀ g ∈ Subgroup.centralizer ({x} : Set H), ∀ y ∈ Y, g * y * g⁻¹ ∈ Y)
    (hodd : Odd (Nat.card Y)) (h11 : ¬ 11 ∣ Nat.card Y) : Y = ⊥ := by
  set D := Subgroup.centralizer ({x} : Set H) with hD
  obtain ⟨hYK, hYcomm⟩ := inf_eq_bot_and_commute_of_odd (X := ⊤) hK
    (fun g _ k hk => (inferInstance : K.Normal).conj_mem k hk g) le_top
    (fun y hy => Subgroup.mem_inf.2 ⟨Subgroup.mem_top y, hYC hy⟩)
    (fun g hg y hy => hYn g (Subgroup.mem_inf.1 hg).2 y hy) hodd
  let f : Y →* Q := (e.toMonoidHom.comp (QuotientGroup.mk' K)).comp Y.subtype
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : (y : H) ∈ K := by
      have : (QuotientGroup.mk (y : H) : H ⧸ K) = 1 := e.injective (hy.trans (map_one e).symm)
      exact (QuotientGroup.eq_one_iff _).1 this
    have h2 : (y : H) ∈ Y ⊓ K := Subgroup.mem_inf.2 ⟨y.2, h1⟩
    rw [hYK, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hfrange : f.range ≤ Subgroup.centralizer ({e (QuotientGroup.mk x)} : Set Q) := by
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show e (QuotientGroup.mk (y : H)) * e (QuotientGroup.mk x) =
      e (QuotientGroup.mk x) * e (QuotientGroup.mk (y : H))
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      Subgroup.mem_centralizer_singleton_iff.1 (hYC y.2)]
  have hY66 : Nat.card Y ∣ 66 := by
    have h1 : Nat.card f.range = Nat.card Y := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv]
    rw [← h1]
    exact (Subgroup.card_dvd_of_le hfrange).trans hQ
  have hY3 : Nat.card Y ∣ 3 := by
    have hcop2 : Nat.Coprime (Nat.card Y) 2 :=
      (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
        (fun h => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h))))
    have hcop11 : Nat.Coprime (Nat.card Y) 11 :=
      Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h11)
    have h66 : (66 : ℕ) = 2 * (3 * 11) := by norm_num
    rw [h66] at hY66
    exact (hcop11.dvd_of_dvd_mul_right ((hcop2.dvd_of_dvd_mul_left hY66)))
  have hDfac : (Nat.card D).factorization 3 = 1 := by
    have hDc := card_centralizer_eq_mul K e x
    obtain ⟨a, ha⟩ := (hK.to_le (inf_le_left : K ⊓ D ≤ K)).exists_card_eq
    have hr : Nat.card (centMap K e x).range ∣ 66 :=
      (Subgroup.card_dvd_of_le (range_centMap_le K e x)).trans hQ
    have h3 : 3 ∣ Nat.card D := hw₃ ▸ Subgroup.orderOf_dvd_natCard D hw₀
    have hpos : Nat.card D ≠ 0 := Nat.card_pos.ne'
    have h9 : ¬ 9 ∣ Nat.card D := by
      rw [hDc, ha]
      intro h9
      have hc : Nat.Coprime 9 (2 ^ a) := Nat.Coprime.pow_right _ (by norm_num)
      have := (hc.dvd_of_dvd_mul_left h9).trans hr
      norm_num at this
    have hle : (Nat.card D).factorization 3 ≤ 1 := by
      by_contra hc
      push_neg at hc
      apply h9
      have : 3 ^ 2 ∣ Nat.card D :=
        (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hpos).2 hc
      simpa using this
    have hge : 1 ≤ (Nat.card D).factorization 3 :=
      (Nat.Prime.dvd_iff_one_le_factorization (by norm_num) hpos).1 h3
    omega
  by_contra hY1
  have hY3' : Nat.card Y = 3 := by
    rcases (Nat.dvd_prime (by norm_num)).1 hY3 with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq Y h) hY1
    · exact h
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 (show 3 ∣ Nat.card Y by rw [hY3'])
  have hyD : (y : H) ∈ D := hYC y.2
  obtain ⟨d, hdD, j, hj⟩ := exists_mem_conj_pow_of_factorization_eq_one hDfac hw₀ hyD hw₃
    (by rw [← Subgroup.orderOf_coe] at hy; exact hy)
  have he' : d * e₀ * d⁻¹ ∈ K ⊓ Subgroup.centralizer ({x} : Set H) := by
    refine Subgroup.mem_inf.2 ⟨(inferInstance : K.Normal).conj_mem _ (Subgroup.mem_inf.1 he₀).1 d,
      ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hdD (Subgroup.mem_inf.1 he₀).2)
      (Subgroup.inv_mem _ hdD)
  have hc := hYcomm y y.2 _ he'
  rw [hj] at hc
  have hwj : w₀ ^ j * e₀ = e₀ * w₀ ^ j := by
    have := congrArg (fun g => d⁻¹ * g * d) hc
    simp only [mul_assoc, inv_mul_cancel_left] at this
    simpa [mul_assoc] using this
  have hj1 : w₀ ^ j ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hj
    have : (y : H) ≠ 1 := by
      intro h; rw [← Subgroup.orderOf_coe, h, orderOf_one] at hy; norm_num at hy
    exact this hj
  have hzc := centralizer_pow_eq_of_prime hw₃ hj1
  have hmem : e₀ ∈ Subgroup.centralizer ({w₀ ^ j} : Set H) :=
    Subgroup.mem_centralizer_singleton_iff.2 hwj.symm
  rw [hzc] at hmem
  exact hwe (Subgroup.mem_centralizer_singleton_iff.1 hmem).symm

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
