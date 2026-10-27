module

public import CFSG.GH74.GLS.Stage2.OddAut.BTCanon

public section

namespace CFSG.LieType.BorelTits

open CFSG.Open CFSG.GH74.GLS.Stage2.OddAut

section Elementary

variable {X : Type*} [Group X]

theorem eq_one_of_mem_pGroup_of_pow_eq_one {p : ℕ} [Fact p.Prime] {R : Subgroup X}
    (hR : IsPGroup p R) {c : X} (hc : c ∈ R) {m : ℕ} (hm : m.Coprime p) (hcm : c ^ m = 1) :
    c = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hR) ⟨c, hc⟩
  rw [Subgroup.orderOf_mk] at hk
  have h1 : orderOf c ∣ m := orderOf_dvd_of_pow_eq_one hcm
  rw [hk] at h1
  have h2 : (p ^ k).Coprime m := Nat.Coprime.pow_left k (Nat.Coprime.symm hm)
  have h3 : p ^ k = 1 := Nat.Coprime.eq_one_of_dvd h2 h1
  exact orderOf_eq_one_iff.1 (hk.trans h3)

theorem exists_mem_normalizer_of_lt_pGroup' {p : ℕ} [Fact p.Prime] [Finite X] {H P : Subgroup X}
    (hP : IsPGroup p P) (hHP : H < P) :
    ∃ x ∈ P, x ∉ H ∧ x ∈ Subgroup.normalizer (H : Set X) := by
  set IP : Subgroup P := H.subgroupOf P with hIP
  have hIPlt : IP < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hHP.ne (le_antisymm hHP.le fun x hx => ?_)
    have : (⟨x, hx⟩ : P) ∈ IP := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : IP < Subgroup.normalizer (IP : Set P) :=
    Group.normalizerCondition_of_isNilpotent IP hIPlt
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨x, x.2, fun hx => hxnot (Subgroup.mem_subgroupOf.mpr hx), ?_⟩
  have hxsub : x ∈ (Subgroup.normalizer (H : Set X)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq hHP.le]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp hxsub

theorem commute_of_mem_inf_normalizer {p : ℕ} [Fact p.Prime] {R A U : Subgroup X}
    (hR : IsPGroup p R) {y : X} (hy : y ∈ Subgroup.normalizer (R : Set X))
    (hyp : (orderOf y).Coprime p) (hUR : U ≤ R)
    (hUA : R ⊓ Subgroup.normalizer (U : Set X) ≤ A) (hyA : ∀ a ∈ A, y * a = a * y) {z : X}
    (hz : z ∈ R ⊓ Subgroup.normalizer (A : Set X)) : y * z = z * y := by
  obtain ⟨hzR, hzN⟩ := hz
  set t : X := y * z * y⁻¹ with ht
  set c : X := z⁻¹ * t with hc
  have htR : t ∈ R := (Subgroup.mem_normalizer_iff.mp hy z).mp hzR
  have hcR : c ∈ R := R.mul_mem (R.inv_mem hzR) htR
  have hcA : ∀ b ∈ A, c * b = b * c := by
    intro b hb
    have hb' : z * b * z⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hzN b).mp hb
    have hyb : y * b = b * y := hyA b hb
    have hyb' : y * (z * b * z⁻¹) = (z * b * z⁻¹) * y := hyA _ hb'
    have e1 : y⁻¹ * b * y = b := by
      calc y⁻¹ * b * y = y⁻¹ * (b * y) := by group
        _ = y⁻¹ * (y * b) := by rw [hyb]
        _ = b := by group
    have e2 : y * (z * b * z⁻¹) * y⁻¹ = z * b * z⁻¹ := by
      calc y * (z * b * z⁻¹) * y⁻¹ = (y * (z * b * z⁻¹)) * y⁻¹ := rfl
        _ = ((z * b * z⁻¹) * y) * y⁻¹ := by rw [hyb']
        _ = z * b * z⁻¹ := by group
    have key : t * b * t⁻¹ = z * b * z⁻¹ := by
      calc t * b * t⁻¹ = y * z * (y⁻¹ * b * y) * z⁻¹ * y⁻¹ := by rw [ht]; group
        _ = y * (z * b * z⁻¹) * y⁻¹ := by rw [e1]; group
        _ = z * b * z⁻¹ := e2
    have hcbc : c * b * c⁻¹ = b := by
      calc c * b * c⁻¹ = z⁻¹ * (t * b * t⁻¹) * z := by rw [hc]; group
        _ = z⁻¹ * (z * b * z⁻¹) * z := by rw [key]
        _ = b := by group
    calc c * b = (c * b * c⁻¹) * c := by group
      _ = b * c := by rw [hcbc]
  have hcA' : c ∈ A := by
    apply hUA
    refine ⟨hcR, ?_⟩
    have hcU : c ∈ Subgroup.centralizer (U : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (hcA u (hUA ⟨hUR hu, Subgroup.le_normalizer hu⟩)).symm
    exact Subgroup.centralizer_le_normalizer (U : Set X) hcU
  have hyc : y * c = c * y := hyA c hcA'
  have hconj : t = z * c := by rw [hc]; group
  have hpow : ∀ k : ℕ, y ^ k * z * (y ^ k)⁻¹ = z * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hyc' : y * c * y⁻¹ = c := by
        calc y * c * y⁻¹ = (c * y) * y⁻¹ := by rw [hyc]
          _ = c := by group
      calc y ^ (k + 1) * z * (y ^ (k + 1))⁻¹ = y * (y ^ k * z * (y ^ k)⁻¹) * y⁻¹ := by group
        _ = y * (z * c ^ k) * y⁻¹ := by rw [ih]
        _ = (y * z * y⁻¹) * (y * c ^ k * y⁻¹) := by group
        _ = (y * z * y⁻¹) * ((y * c * y⁻¹) ^ k) := by rw [conj_pow]
        _ = z * c * c ^ k := by rw [hyc', ← ht, hconj]
        _ = z * c ^ (k + 1) := by rw [pow_succ']; group
  have hm := hpow (orderOf y)
  rw [pow_orderOf_eq_one] at hm
  have hcm : c ^ orderOf y = 1 := by
    have : z * c ^ orderOf y = z * 1 := by rw [← hm]; group
    exact mul_left_cancel this
  have hc1 : c = 1 := eq_one_of_mem_pGroup_of_pow_eq_one hR hcR hyp hcm
  have hyz : y * z * y⁻¹ = z := by
    rw [← ht, hconj, hc1]
    group
  calc y * z = (y * z * y⁻¹) * y := by group
    _ = z * y := by rw [hyz]

theorem commute_of_commute_inf_normalizer {p : ℕ} [Fact p.Prime] [Finite X] {R U : Subgroup X}
    (hR : IsPGroup p R) (hUR : U ≤ R) {y : X} (hy : y ∈ Subgroup.normalizer (R : Set X))
    (hyp : (orderOf y).Coprime p)
    (hy1 : ∀ z ∈ R ⊓ Subgroup.normalizer (U : Set X), y * z = z * y) :
    ∀ z ∈ R, y * z = z * y := by
  have key : ∀ A : Subgroup X, A ≤ R → R ⊓ Subgroup.normalizer (U : Set X) ≤ A →
      (∀ a ∈ A, y * a = a * y) → ∀ z ∈ R, y * z = z * y := by
    intro A
    induction A using WellFoundedGT.induction with
    | _ A ih =>
      intro hAR hUA hyA
      by_cases hAeq : A = R
      · intro z hz
        exact hyA z (hAeq ▸ hz)
      · have hlt : A < R := lt_of_le_of_ne hAR hAeq
        obtain ⟨x, hxR, hxA, hxN⟩ := exists_mem_normalizer_of_lt_pGroup' hR hlt
        have hAB : A ≤ R ⊓ Subgroup.normalizer (A : Set X) :=
          le_inf hAR Subgroup.le_normalizer
        have hlt' : A < R ⊓ Subgroup.normalizer (A : Set X) := by
          refine lt_of_le_of_ne hAB ?_
          intro h
          have : x ∈ R ⊓ Subgroup.normalizer (A : Set X) := ⟨hxR, hxN⟩
          rw [← h] at this
          exact hxA this
        exact ih _ hlt' inf_le_left (hUA.trans hAB)
          (fun a ha => commute_of_mem_inf_normalizer hR hy hyp hUR hUA hyA ha)
  exact key _ inf_le_left le_rfl hy1

end Elementary

section Main

variable {X : Type*} [Group X]

theorem mem_normalizer_inf_of_mem {R H : Subgroup X} {g : X}
    (hR : g ∈ Subgroup.normalizer (R : Set X)) (hH : g ∈ Subgroup.normalizer (H : Set X)) :
    g ∈ Subgroup.normalizer ((R ⊓ H : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at hR hH ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hR x, hH x]

variable [Finite X] {p : ℕ} [Fact p.Prime]

theorem centralizer_pCoreOf_le_of_holds (hBT : Holds X p)
    (hRC : ∀ R : Subgroup X, R ≠ ⊥ → IsPGroup p R →
      pCoreOf p (Subgroup.normalizer (R : Set X)) = R → Subgroup.normalizer (R : Set X) ≠ ⊤ →
      (∃ Sy : Sylow p X, Subgroup.normalizer ((Sy : Subgroup X) : Set X) ≤
        Subgroup.normalizer (R : Set X)) → Subgroup.centralizer (R : Set X) ≤ R)
    {U : Subgroup X} (hU : U ≠ ⊥) (hUp : IsPGroup p U) :
    Subgroup.normalizer (U : Set X) ⊓
        Subgroup.centralizer (pCoreOf p (Subgroup.normalizer (U : Set X)) : Set X) ≤
      pCoreOf p (Subgroup.normalizer (U : Set X)) := by
  obtain ⟨hUR, hRp, hHR, hRtop, hcore, hSyl⟩ := canonical_parabolic hBT hU hUp
  set R : Subgroup X := radInf p U with hRdef
  set H : Subgroup X := Subgroup.normalizer (U : Set X) with hH
  set W : Subgroup X := pCoreOf p H with hW
  have hRne : R ≠ ⊥ := fun h => hU (le_bot_iff.1 (hUR.trans h.le))
  have hCR : Subgroup.centralizer (R : Set X) ≤ R := hRC R hRne hRp hcore hRtop hSyl
  have hRH : R ⊓ H ≤ W := by
    refine le_pCoreOf_of_le_normalizer p inf_le_right ?_ (hRp.to_le inf_le_left)
    intro g hg
    exact mem_normalizer_inf_of_mem (hHR hg) (Subgroup.le_normalizer hg)
  set K : Subgroup X := H ⊓ Subgroup.centralizer (W : Set X) with hK
  have hK1 : ∀ y ∈ K, (orderOf y).Coprime p → y = 1 := by
    intro y hyK hyp
    obtain ⟨hyH, hyC⟩ := hyK
    have hyN : y ∈ Subgroup.normalizer (R : Set X) := hHR hyH
    have hy1 : ∀ z ∈ R ⊓ Subgroup.normalizer (U : Set X), y * z = z * y := by
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp hyC z (hRH hz)).symm
    have hcomm := commute_of_commute_inf_normalizer hRp hUR hyN hyp hy1
    have hyR : y ∈ R := by
      apply hCR
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hcomm z hz).symm
    exact eq_one_of_mem_pGroup_of_pow_eq_one hRp hyR hyp (pow_orderOf_eq_one y)
  have hKp : IsPGroup p K := by
    rw [IsPGroup.iff_card]
    refine ⟨(Nat.card K).primeFactorsList.length, ?_⟩
    refine Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {q} hq hqd => ?_
    by_contra hne
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) q hqd
    have hcop : (orderOf (x : X)).Coprime p := by
      rw [Subgroup.orderOf_coe, hx]
      exact (Nat.coprime_primes hq (Fact.out)).mpr hne
    have h1 : (x : X) = 1 := hK1 x x.2 hcop
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    exact hq.one_lt.ne hx
  have hconj : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
    intro h hh k hk
    have hkH : k ∈ H := hk.1
    have hkC : k ∈ Subgroup.centralizer (W : Set X) := hk.2
    refine ⟨H.mul_mem (H.mul_mem hh hkH) (H.inv_mem hh), ?_⟩
    show h * k * h⁻¹ ∈ Subgroup.centralizer (W : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : h⁻¹ * w * h ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf p H (H.inv_mem hh)) w).mp hw
      simpa using this
    have := Subgroup.mem_centralizer_iff.mp hkC _ hw'
    calc w * (h * k * h⁻¹) = h * ((h⁻¹ * w * h) * k) * h⁻¹ := by group
      _ = h * (k * (h⁻¹ * w * h)) * h⁻¹ := by rw [this]
      _ = h * k * h⁻¹ * w := by group
  have hnorm : H ≤ Subgroup.normalizer (K : Set X) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨hconj h hh k, fun hk => ?_⟩
    have := hconj h⁻¹ (H.inv_mem hh) _ hk
    simpa [mul_assoc] using this
  exact le_pCoreOf_of_le_normalizer p inf_le_left hnorm hKp

theorem isCharTwoType_of_holds (hBT : Holds X 2)
    (hRC : ∀ R : Subgroup X, R ≠ ⊥ → IsPGroup 2 R →
      pCoreOf 2 (Subgroup.normalizer (R : Set X)) = R → Subgroup.normalizer (R : Set X) ≠ ⊤ →
      (∃ Sy : Sylow 2 X, Subgroup.normalizer ((Sy : Subgroup X) : Set X) ≤
        Subgroup.normalizer (R : Set X)) → Subgroup.centralizer (R : Set X) ≤ R) :
    IsCharTwoType X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro H ⟨U, hU, hUp, rfl⟩
  exact centralizer_pCoreOf_le_of_holds hBT hRC hU hUp

end Main

end CFSG.LieType.BorelTits
