module

public import CFSG.GroupTheory.OddAutomorphismTwoGroup
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.GroupTheory

theorem mulAut_eq_one_of_pow_five_pow_eq_one {V : Type*} [Group V] [Finite V]
    (hV2 : IsPGroup 2 V) (h8 : Nat.card V ≤ 8) {σ : MulAut V} {k : ℕ}
    (hσ : σ ^ 5 ^ k = 1) : σ = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hdvd : orderOf σ ∣ 5 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hσ
  rcases (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 hdvd with ⟨j, -, hj⟩
  rcases j with _ | j
  · exact orderOf_eq_one_iff.mp (by simpa using hj)
  · exfalso
    have hpow : (σ ^ 5 ^ j) ^ 5 = 1 := by
      rw [← pow_mul]
      have h1 : 5 ^ j * 5 = 5 ^ (j + 1) := by rw [pow_succ]
      rw [h1, ← hj]
      exact pow_orderOf_eq_one σ
    have hne : σ ^ 5 ^ j ≠ 1 := by
      intro h
      have hd : orderOf σ ∣ 5 ^ j := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [hj] at hd
      have hle : 5 ^ (j + 1) ≤ 5 ^ j := Nat.le_of_dvd (pow_pos (by norm_num) j) hd
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).mp hle
      omega
    exact CFSG.GroupTheory.no_orderOf_five_mulAut hV2 h8
      (orderOf_eq_prime_iff.mpr ⟨hpow, hne⟩)

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_of_orderOf_five_pow_of_invariant {V₀ U : Subgroup G}
    (hV0el : CFSG.Open.IsElemAbelian 2 V₀) (hcard : Nat.card V₀ ≤ 16) (hU : U ≤ V₀)
    (hbot : U ≠ ⊥) (htop : U ≠ V₀) {x : G} (hxV0 : x ∈ Subgroup.normalizer (V₀ : Set G))
    (hxU : x ∈ Subgroup.normalizer (U : Set G)) {k : ℕ} (hxord : orderOf x = 5 ^ k) :
    x ∈ Subgroup.centralizer (V₀ : Set G) := by
  have : IsMulCommutative ↥V₀ := hV0el.1
  have : (U.subgroupOf V₀).Normal := Subgroup.normal_of_isMulCommutative _
  obtain ⟨m, hV0card⟩ := IsPGroup.iff_card.mp (CFSG.Open.IsElemAbelian.isPGroup hV0el)
  have hm : m ≤ 4 := by
    by_contra hm
    have h5 : 2 ^ 5 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hUsub : Nat.card ↥(U.subgroupOf V₀) ∣ Nat.card V₀ :=
    Subgroup.card_subgroup_dvd_card _
  have hUcardEq : Nat.card ↥(U.subgroupOf V₀) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv
  have hUcardDvd : Nat.card U ∣ 2 ^ m := hUcardEq ▸ hV0card ▸ hUsub
  obtain ⟨d, hdm, hUcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hUcardDvd
  have hU8 : Nat.card U ≤ 8 := by
    have hne : d ≠ m := by
      intro hdm'
      apply htop
      refine Subgroup.eq_of_le_of_card_ge hU ?_
      rw [hUcard, hV0card, hdm']
    have hdlt : d < m := lt_of_le_of_ne hdm hne
    have hdle : d ≤ 3 := by omega
    rw [hUcard]
    calc 2 ^ d ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hdle
      _ = 8 := by norm_num
  have hQcardDvd : Nat.card ((↥V₀ ⧸ (U.subgroupOf V₀))) ∣ 2 ^ m := by
    rw [← hV0card]
    exact ⟨Nat.card ↥(U.subgroupOf V₀),
      Subgroup.card_eq_card_quotient_mul_card_subgroup (U.subgroupOf V₀)⟩
  obtain ⟨e, he, hQcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hQcardDvd
  have hQ8 : Nat.card ((↥V₀ ⧸ (U.subgroupOf V₀))) ≤ 8 := by
    have hne : d ≠ 0 := by
      intro hd0
      apply hbot
      refine Subgroup.card_eq_one.mp ?_
      rw [hUcard, hd0]
      norm_num
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hne
    have hsum : (2 : ℕ) ^ m = 2 ^ (e + d) := by
      have h1 : Nat.card V₀ =
          Nat.card ((↥V₀ ⧸ (U.subgroupOf V₀))) * Nat.card ↥(U.subgroupOf V₀) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (U.subgroupOf V₀)
      rw [h1, hUcardEq, hQcard, hUcard, ← pow_add] at hV0card
      exact hV0card.symm
    have hed : e + d = m := (Nat.pow_right_injective (by norm_num : 2 ≤ 2)) hsum.symm
    have he3 : e ≤ 3 := by omega
    rw [hQcard]
    calc 2 ^ e ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) he3
      _ = 8 := by norm_num
  have hcoinj : IsPGroup 2 ↥(U.subgroupOf V₀) :=
    (IsPGroup.iff_card).mpr ⟨d, hUcardEq.trans hUcard⟩
  have hquotp : IsPGroup 2 (↥V₀ ⧸ (U.subgroupOf V₀)) :=
    (IsPGroup.iff_card).mpr ⟨e, hQcard⟩
  have hxord' : x ^ 5 ^ k = 1 := by
    rw [← hxord]; exact pow_orderOf_eq_one x
  have hxUtriv : ∀ u ∈ U, x * u * x⁻¹ = u := by
    intro u hu
    let σ : MulAut ↥U := U.normalizerMonoidHom ⟨x, hxU⟩
    have hpow : ∀ z : ↥U, ∀ n : ℕ, ((σ ^ n) z : G) = x ^ n * (z : G) * (x ^ n)⁻¹ := by
      intro z n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ']
        change ((σ ((σ ^ n) z) : ↥U) : G) = _
        rw [show ((σ ((σ ^ n) z) : ↥U) : G) =
          x * (((σ ^ n) z : ↥U) : G) * x⁻¹ from by
          simp [σ, Subgroup.normalizerMonoidHom_apply_apply_coe]]
        rw [ih]; group
    have hσpow : σ ^ 5 ^ k = 1 := by
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      rw [hpow z (5 ^ k), hxord']
      simp
    have hσ1 : σ = 1 := mulAut_eq_one_of_pow_five_pow_eq_one
      ((IsPGroup.iff_card).mpr ⟨d, hUcard⟩) hU8 hσpow
    have h1 := congrArg (fun f : MulAut ↥U => f ⟨u, hu⟩) hσ1
    have h2 : ((σ ⟨u, hu⟩ : ↥U) : G) = x * u * x⁻¹ := by
      simp [σ, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have := congrArg (fun z : ↥U => (z : G)) h1
    simpa [h2] using this
  have hxq : ∀ y ∈ V₀, x * y * x⁻¹ * y⁻¹ ∈ U := by
    intro y hy
    let σ : MulAut ↥V₀ := V₀.normalizerMonoidHom ⟨x, hxV0⟩
    have hσinv : ∀ u : ↥V₀, u ∈ U.subgroupOf V₀ → σ u ∈ U.subgroupOf V₀ := by
      intro u hu
      rw [Subgroup.mem_subgroupOf] at hu ⊢
      have h2 : ((σ u : ↥V₀) : G) = x * (u : G) * x⁻¹ := by
        simp [σ, Subgroup.normalizerMonoidHom_apply_apply_coe]
      rw [h2, hxUtriv (u : G) hu]
      exact hu
    have hτmap : (U.subgroupOf V₀).map σ.toMonoidHom = U.subgroupOf V₀ := by
      have hcard : Nat.card ↥((U.subgroupOf V₀).map σ.toMonoidHom) =
          Nat.card ↥(U.subgroupOf V₀) :=
        Subgroup.card_map_of_injective (K := U.subgroupOf V₀) σ.injective
      refine Subgroup.eq_of_le_of_card_ge ?_ hcard.ge
      rw [Subgroup.map_le_iff_le_comap]
      intro u hu
      exact hσinv u hu
    let τ : MulAut ((↥V₀ ⧸ (U.subgroupOf V₀))) :=
      QuotientGroup.congr (U.subgroupOf V₀) (U.subgroupOf V₀) σ hτmap
    have hσpow' : ∀ w : ↥V₀, ∀ n : ℕ, ((σ ^ n) w : G) =
        x ^ n * (w : G) * (x ^ n)⁻¹ := by
      intro w n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ']
        change ((σ ((σ ^ n) w) : ↥V₀) : G) = _
        rw [show ((σ ((σ ^ n) w) : ↥V₀) : G) =
          x * (((σ ^ n) w : ↥V₀) : G) * x⁻¹ from by
          simp [σ, Subgroup.normalizerMonoidHom_apply_apply_coe]]
        rw [ih]; group
    have hσpow : σ ^ 5 ^ k = 1 := by
      apply MulEquiv.ext
      intro w
      apply Subtype.ext
      rw [hσpow' w (5 ^ k), hxord']
      simp
    have hτpow : τ ^ 5 ^ k = 1 := by
      apply MulEquiv.ext
      intro q
      refine QuotientGroup.induction_on q fun z => ?_
      have hpow : ∀ n : ℕ, (τ ^ n) (QuotientGroup.mk z) =
          QuotientGroup.mk ((σ ^ n) z) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ']
          change τ ((τ ^ n) (QuotientGroup.mk z)) = _
          rw [ih]
          have h1 : τ (QuotientGroup.mk ((σ ^ n) z)) =
              QuotientGroup.mk (σ ((σ ^ n) z)) := by
            simpa using QuotientGroup.congr_mk (U.subgroupOf V₀) (U.subgroupOf V₀) σ hτmap
              ((σ ^ n) z)
          rw [h1, ← MulAut.mul_apply, ← pow_succ']
      rw [hpow (5 ^ k), hσpow, MulAut.one_apply]
      rfl
    have hτ1 : τ = 1 := mulAut_eq_one_of_pow_five_pow_eq_one hquotp hQ8 hτpow
    have h1 := congrArg (fun f : MulAut ((↥V₀ ⧸ (U.subgroupOf V₀))) =>
      f (QuotientGroup.mk ⟨y, hy⟩)) hτ1
    have h2 : τ (QuotientGroup.mk ⟨y, hy⟩) =
        QuotientGroup.mk (σ ⟨y, hy⟩) := QuotientGroup.congr_mk _ _ _ _ _
    rw [h2, show ((1 : MulAut ((↥V₀ ⧸ (U.subgroupOf V₀))))
      (QuotientGroup.mk ⟨y, hy⟩)) = QuotientGroup.mk ⟨y, hy⟩ from rfl,
      QuotientGroup.eq_iff_div_mem] at h1
    have hmem : (((σ ⟨y, hy⟩) / ⟨y, hy⟩ : ↥V₀) : G) ∈ U :=
      Subgroup.mem_subgroupOf.mp h1
    have hcoeeq : (((σ ⟨y, hy⟩) / ⟨y, hy⟩ : ↥V₀) : G) =
        x * y * x⁻¹ * y⁻¹ := by
      simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv,
        σ, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rwa [hcoeeq] at hmem
  have hxodd : Odd (orderOf x) := by
    rw [hxord]; exact Odd.pow (show Odd 5 from ⟨2, rfl⟩)
  have hxcomm : ∀ y ∈ V₀, x * y * x⁻¹ = y := fun _ hy =>
    CFSG.Quasithin.H13.A5.conj_eq_of_odd_of_comm hV0el hU hxodd (pow_orderOf_eq_one x)
      hxUtriv hxq hy
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h := hxcomm y hy
  calc y * x = x * y * x⁻¹ * x := by rw [h]
    _ = x * y := by group

end CFSG.GroupTheory
