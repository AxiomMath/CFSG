module

public import CFSG.ClassicalInvolution.AschTight.Sec7KeyMat
public import CFSG.ClassicalInvolution.Asc77.ModOApi

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem commutator_mem_oddCoreOf_of_commute (hΩ : HypOmegaMod p f Ω) {J : Subgroup G}
    (hJ : J ∈ Ω) {u a b : G} (hu : u ∈ J) (hu2 : IsPGroup 2 (Subgroup.zpowers u))
    (huu : u * u ≠ 1) (ha : a ∈ J) (hb : b ∈ J) (hau : a * u = u * a) (hbu : b * u = u * b) :
    a * b * a⁻¹ * b⁻¹ ∈ oddCoreOf J := by
  obtain ⟨φ, -, hφk⟩ := hΩ.exists_chart hJ
  have hx : φ ⟨u, hu⟩ * φ ⟨u, hu⟩ ≠ 1 := by
    intro h
    rw [← map_mul, hφk] at h
    apply huu
    have h2 : IsPGroup 2 (Subgroup.zpowers (u * u)) :=
      hu2.to_le (Subgroup.zpowers_le.mpr (Subgroup.mul_mem _ (Subgroup.mem_zpowers u)
        (Subgroup.mem_zpowers u)))
    exact eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard J)
      (mem_oddCoreOf_iff.mpr ⟨J.mul_mem hu hu, h⟩) h2
  have hya : φ ⟨a, ha⟩ * φ ⟨u, hu⟩ = φ ⟨u, hu⟩ * φ ⟨a, ha⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hau)
  have hyb : φ ⟨b, hb⟩ * φ ⟨u, hu⟩ = φ ⟨u, hu⟩ * φ ⟨b, hb⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hbu)
  have hc := sl2_commute_of_commute hx hya hyb
  have hc' : φ (⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥J)⁻¹ * (⟨b, hb⟩ : ↥J)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hc]
    group
  exact mem_oddCoreOf_iff.mpr ⟨_, (hφk _).mp hc'⟩

theorem commute_of_odd_of_cyclic {U : Subgroup G} (hUc : IsCyclic ↥U) (hU2 : IsPGroup 2 U)
    {h : G} (hh : h ∈ Subgroup.normalizer (U : Set G)) (hodd : Odd (orderOf h)) {x : G}
    (hx : x ∈ U) : h * x * h⁻¹ = x := by
  set N := Subgroup.normalizer (U : Set G)
  have hUN : U ≤ N := Subgroup.le_normalizer
  have e : ↥(U.subgroupOf N) ≃* ↥U := Subgroup.subgroupOfEquivOfLe hUN
  have : IsCyclic ↥(U.subgroupOf N) := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  obtain ⟨a, ha⟩ := hU2.exists_card_eq
  have hcard : Nat.card ↥(U.subgroupOf N) = 2 ^ a := by rw [Nat.card_congr e.toEquiv, ha]
  set σ := MulAut.conjNormal (H := U.subgroupOf N) (⟨h, hh⟩ : ↥N)
  have h1 : orderOf σ ∣ orderOf h := by
    have := orderOf_map_dvd (MulAut.conjNormal (H := U.subgroupOf N)) (⟨h, hh⟩ : ↥N)
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf σ ∣ Nat.totient (2 ^ a) := by
    rw [← hcard, ← IsCyclic.card_mulAut]
    exact orderOf_dvd_natCard σ
  have hσ : σ = 1 := by
    rw [← orderOf_eq_one_iff]
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    · subst ha0
      simpa using h2
    rw [Nat.totient_prime_pow Nat.prime_two ha0] at h2
    have h2' : orderOf σ ∣ 2 ^ (a - 1) := by simpa using h2
    have hcop : Nat.Coprime (orderOf h) (2 ^ (a - 1)) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
    exact Nat.eq_one_of_dvd_coprimes hcop h1 h2'
  have hxN : x ∈ N := hUN hx
  have := congrArg (fun τ : MulAut ↥(U.subgroupOf N) => ((τ ⟨⟨x, hxN⟩, hx⟩ : ↥N) : G)) hσ
  simpa [σ, MulAut.conjNormal_apply] using this

theorem mem_centralizer_of_odd {J W : Subgroup G} (hWJ : W ≤ Subgroup.normalizer (J : Set G))
    (hUc : IsCyclic ↥(J ⊓ W)) (hU2 : IsPGroup 2 ↥(J ⊓ W)) {h : G} (hhJ : h ∈ J)
    (hhW : h ∈ Subgroup.normalizer (W : Set G)) (hodd : Odd (orderOf h)) :
    h ∈ Subgroup.centralizer (W : Set G) := by
  have hhU : h ∈ Subgroup.normalizer ((J ⊓ W : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at hhW ⊢
    intro y
    have hJ' := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hhJ) y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hJ', hhW y]
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  set c := h * w * h⁻¹ * w⁻¹ with hc
  have hcW : c ∈ W := W.mul_mem ((Subgroup.mem_normalizer_iff.mp hhW w).mp hw) (W.inv_mem hw)
  have hcJ : c ∈ J := by
    have h1 : w * h⁻¹ * w⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hWJ hw) _).mp (J.inv_mem hhJ)
    have e : c = h * (w * h⁻¹ * w⁻¹) := by rw [hc]; group
    rw [e]
    exact J.mul_mem hhJ h1
  have hcc : h * c * h⁻¹ = c := commute_of_odd_of_cyclic hUc hU2 hhU hodd ⟨hcJ, hcW⟩
  have hpow : ∀ k : ℕ, h ^ k * w * (h ^ k)⁻¹ = c ^ k * w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hck : h * c ^ k * h⁻¹ = c ^ k := by rw [← conj_pow, hcc]
      calc h ^ (k + 1) * w * (h ^ (k + 1))⁻¹ = h * (h ^ k * w * (h ^ k)⁻¹) * h⁻¹ := by group
        _ = h * (c ^ k * w) * h⁻¹ := by rw [ih]
        _ = (h * c ^ k * h⁻¹) * (h * w * h⁻¹) := by group
        _ = c ^ k * (c * w) := by rw [hck, hc]; group
        _ = c ^ (k + 1) * w := by group
  have hm := hpow (orderOf h)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hm
  have hm' : c ^ orderOf h = 1 := by
    have := congrArg (· * w⁻¹) hm
    simp only [mul_inv_cancel, mul_inv_cancel_right] at this
    exact this.symm
  have hc1 : c = 1 := by
    have hdvd : orderOf c ∣ orderOf h := orderOf_dvd_of_pow_eq_one hm'
    obtain ⟨n, hn⟩ := (hU2.to_le (Subgroup.zpowers_le.mpr (show c ∈ J ⊓ W from ⟨hcJ, hcW⟩)) :
      IsPGroup 2 (Subgroup.zpowers c)).exists_card_eq
    rw [Nat.card_zpowers] at hn
    rw [hn] at hdvd
    have hn0 : n = 0 := by
      by_contra hne
      exact (Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat hdvd)) (Nat.even_pow.mpr ⟨even_two, hne⟩)
    rw [hn0, pow_zero] at hn
    exact orderOf_eq_one_iff.mp hn
  have : h * w * h⁻¹ * w⁻¹ = 1 := hc1
  calc w * h = (h * w * h⁻¹ * w⁻¹)⁻¹ * (h * w) := by group
    _ = h * w := by rw [this, inv_one, one_mul]

omit [Finite G] in
theorem odd_card_sup_of_le_normalizer' {H N : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hH : Odd (Nat.card H)) (hN : Odd (Nat.card N)) :
    Odd (Nat.card (H ⊔ N : Subgroup G)) := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv]
  exact (Odd.of_dvd_nat hH (Subgroup.card_quotient_dvd_card _)).mul hN

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
