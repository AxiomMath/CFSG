module

public import CFSG.LocalAnalysis.ABGTheoremB.V4Basic
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.ABGTheoremB.V4

open CFSG.ABGLocalTools CFSG.ABGTheoremB.TotallyInverted
open scoped Pointwise

theorem eq_one_of_mem_centralizer_pCore {H : Type*} [Group H] [Finite H]
    (hsolv : Group.IsSolvable H) {p r : ℕ} [Fact p.Prime]
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ Nat.card H → q = p ∨ q = r)
    (hOp : CFSG.pCore p H = ⊥) {u : H} (hu : IsPGroup p (Subgroup.zpowers u))
    (hc : u ∈ Subgroup.centralizer (CFSG.pCore r H : Set H)) : u = 1 := by
  set U := Subgroup.zpowers u with hU
  have hUc : U ≤ Subgroup.centralizer (CFSG.fittingSubgroup H : Set H) := by
    apply CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores
    rintro ⟨⟨q, hq⟩, -⟩
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    rcases hprimes q hqp (Nat.dvd_of_mem_primeFactors hq) with rfl | rfl
    · rw [hOp]
      intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hz
      rw [hz, one_mul, mul_one]
    · exact (Subgroup.zpowers_le).mpr hc
  have hUF : U ≤ CFSG.fittingSubgroup H :=
    hUc.trans (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv)
  have hUO := le_pCore_of_isPGroup_of_le_fitting hu hUF
  rw [hOp, le_bot_iff, Subgroup.zpowers_eq_bot] at hUO
  exact hUO

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem eq_one_of_mem_centralizer_pCoreIn {p r : ℕ} [Fact p.Prime] {K : Subgroup Γ}
    (hsolv : Group.IsSolvable K) (hprimes : ∀ q : ℕ, q.Prime → q ∣ Nat.card K → q = p ∨ q = r)
    (hOp : pCoreIn p K = ⊥) {u : Γ} (huK : u ∈ K) {k : ℕ} (hu : u ^ p ^ k = 1)
    (hc : ∀ z ∈ pCoreIn r K, u * z = z * u) : u = 1 := by
  have hOp' : CFSG.pCore p K = ⊥ := by
    rw [pCoreIn, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at hOp
    exact hOp
  have hu' : (⟨u, huK⟩ : K) ^ p ^ k = 1 := Subtype.ext (by simpa using hu)
  have hup : IsPGroup p (Subgroup.zpowers (⟨u, huK⟩ : K)) := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu', one_zpow]
  have hc' : (⟨u, huK⟩ : K) ∈ Subgroup.centralizer (CFSG.pCore r K : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact Subtype.ext (hc z ⟨z, hz, rfl⟩).symm
  have := eq_one_of_mem_centralizer_pCore hsolv hprimes hOp' hup hc'
  exact congrArg Subtype.val this

theorem eq_one_of_conj_eq_inv_of_centralizes {p r : ℕ} [Fact p.Prime] {K : Subgroup Γ}
    (hsolv : Group.IsSolvable K) (hprimes : ∀ q : ℕ, q.Prime → q ∣ Nat.card K → q = p ∨ q = r)
    (hOp : pCoreIn p K = ⊥) (hKodd : Odd (Nat.card K)) {u s : Γ} (huK : u ∈ K) {k : ℕ}
    (hu : u ^ p ^ k = 1) (hsZ : ∀ z ∈ pCoreIn r K, s * z * s⁻¹ = z)
    (hsu : s * u * s⁻¹ = u⁻¹) : u = 1 := by
  apply eq_one_of_mem_centralizer_pCoreIn hsolv hprimes hOp huK hu
  intro z hz
  have huZ : u ∈ Subgroup.normalizer (pCoreIn r K : Set Γ) :=
    DataConstruction.le_normalizer_pCoreIn r K huK
  have hw : u * z * u⁻¹ ∈ pCoreIn r K := (Subgroup.mem_normalizer_iff.mp huZ z).mp hz
  have h1 : s * (u * z * u⁻¹) * s⁻¹ = u⁻¹ * z * u := by
    have hsu' : s * u⁻¹ * s⁻¹ = u := by
      rw [show s * u⁻¹ * s⁻¹ = (s * u * s⁻¹)⁻¹ by group, hsu, inv_inv]
    calc s * (u * z * u⁻¹) * s⁻¹ = (s * u * s⁻¹) * (s * z * s⁻¹) * (s * u⁻¹ * s⁻¹) := by group
      _ = u⁻¹ * z * u := by rw [hsu, hsZ z hz, hsu']
  rw [hsZ _ hw] at h1
  have hodd : Odd (orderOf u) := hKodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard K huK)
  apply comm_of_sq_comm hodd
  rw [sq]
  calc u * u * z = u * (u * z * u⁻¹) * u⁻¹ * (u * u) := by group
    _ = u * (u⁻¹ * z * u) * u⁻¹ * (u * u) := by rw [h1]
    _ = z * (u * u) := by group

theorem eq_one_of_conj_eq_inv_of_permutable {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hpr : p ≠ r) {K : Subgroup Γ} (hsolv : Group.IsSolvable K)
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ Nat.card K → q = p ∨ q = r) (hOp : pCoreIn p K = ⊥)
    (hKodd : Odd (Nat.card K)) {A R₁ : Subgroup Γ} (hR₁K : R₁ ≤ K) (hR₁p : IsPGroup p R₁)
    (hAr : IsPGroup r A) (hR₁A : (R₁ : Set Γ) * A = A * R₁) {s : Γ} (hs2 : orderOf s = 2)
    (hsK : s ∈ Subgroup.normalizer (K : Set Γ)) (hAinv : ∀ a ∈ A, s * a * s⁻¹ = a⁻¹)
    (hZinv : ∀ z ∈ pCoreIn r K, s * z * s⁻¹ = z⁻¹ → z ∈ A)
    (hZA : pCoreIn r K ≤ Subgroup.normalizer (A : Set Γ)) {u : Γ} (huR₁ : u ∈ R₁)
    (hsu : s * u * s⁻¹ = u⁻¹) : u = 1 := by
  set Z := pCoreIn r K with hZdef
  set I : Subgroup Γ := A ⊓ Z with hIdef
  have hKZ : K ≤ Subgroup.normalizer (Z : Set Γ) := DataConstruction.le_normalizer_pCoreIn r K
  have hZodd : Odd (Nat.card Z) := hKodd.of_dvd_nat (Subgroup.card_dvd_of_le (pCoreIn_le r K))
  have hZr : IsPGroup r Z := DataConstruction.isPGroup_pCoreIn r K
  have huK : u ∈ K := hR₁K huR₁
  have hodd : Odd (orderOf u) := hKodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard K huK)
  have hsu' : s * u⁻¹ * s⁻¹ = u := by
    rw [show s * u⁻¹ * s⁻¹ = (s * u * s⁻¹)⁻¹ by group, hsu, inv_inv]
  have hcop : Nat.Coprime (Nat.card R₁) (Nat.card A) := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR₁p
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hAr
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes Fact.out Fact.out).mpr hpr)
  have hR₁Z : R₁ ⊓ Z = ⊥ := by
    apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR₁p
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hZr
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes Fact.out Fact.out).mpr hpr)
  have hR₁I : R₁ ≤ Subgroup.normalizer (I : Set Γ) :=
    (permutable_inf_of_le_normalizer hR₁A hcop (hR₁K.trans hKZ)).2 hR₁Z
  have huI : ∀ i ∈ I, u * i = i * u := by
    intro i hi
    have hw : u * i * u⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.mp (hR₁I huR₁) i).mp hi
    have h1 : s * (u * i * u⁻¹) * s⁻¹ = u⁻¹ * i⁻¹ * u := by
      calc s * (u * i * u⁻¹) * s⁻¹ = (s * u * s⁻¹) * (s * i * s⁻¹) * (s * u⁻¹ * s⁻¹) := by group
        _ = u⁻¹ * i⁻¹ * u := by rw [hsu, hAinv i hi.1, hsu']
    rw [hAinv _ hw.1] at h1
    have h2 : u ^ 2 * i⁻¹ = i⁻¹ * u ^ 2 := by
      rw [sq]
      calc u * u * i⁻¹ = u * (u * i * u⁻¹)⁻¹ * u⁻¹ * (u * u) := by group
        _ = u * (u⁻¹ * i⁻¹ * u) * u⁻¹ * (u * u) := by rw [h1]
        _ = i⁻¹ * (u * u) := by group
    have h3 := comm_of_sq_comm hodd h2
    calc u * i = u * (i⁻¹)⁻¹ := by rw [inv_inv]
      _ = (i⁻¹)⁻¹ * (i⁻¹ * u) * (i⁻¹)⁻¹ := by group
      _ = (i⁻¹)⁻¹ * (u * i⁻¹) * (i⁻¹)⁻¹ := by rw [h3]
      _ = i * u := by group
  have hsZ : s ∈ Subgroup.normalizer (Z : Set Γ) :=
    DataConstruction.normalizer_le_normalizer_pCoreIn r K hsK
  have hdec : ∀ z ∈ Z, ∃ f ∈ Z, s * f * s⁻¹ = f ∧ ∃ i ∈ I, f * i = z := by
    intro z hz
    have hz' : z ∈ (Z : Set Γ) := hz
    rw [(odd_fixed_mul_inverted hZodd hs2 hsZ).1] at hz'
    obtain ⟨f, hf, i, hi, rfl⟩ := hz'
    refine ⟨f, hf.1, ?_, i, ⟨hZinv i hi.1 hi.2, hi.1⟩, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp hf.2
    rw [← this]
    group
  have hZI : Z ≤ Subgroup.normalizer (I : Set Γ) :=
    (le_inf hZA Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  set v := u * u with hvdef
  have hvI : ∀ i ∈ I, v * i = i * v := by
    intro i hi
    calc v * i = u * (u * i) := by rw [hvdef]; group
      _ = u * (i * u) := by rw [huI i hi]
      _ = (u * i) * u := by group
      _ = (i * u) * u := by rw [huI i hi]
      _ = i * v := by rw [hvdef]; group
  have hv2 : ∀ z ∈ Z, v * z * v⁻¹ * z⁻¹ ∈ I := by
    intro z hz
    obtain ⟨f, hfZ, hsf, i, hi, rfl⟩ := hdec z hz
    have hw : u * f * u⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hKZ huK) f).mp hfZ
    obtain ⟨f', hf'Z, hsf', i', hi', he⟩ := hdec _ hw
    have h1 : u⁻¹ * f * u = f' * i'⁻¹ := by
      have : s * (u * f * u⁻¹) * s⁻¹ = u⁻¹ * f * u := by
        calc s * (u * f * u⁻¹) * s⁻¹ = (s * u * s⁻¹) * (s * f * s⁻¹) * (s * u⁻¹ * s⁻¹) := by
              group
          _ = u⁻¹ * f * u := by rw [hsu, hsf, hsu']
      rw [← this, ← he]
      calc s * (f' * i') * s⁻¹ = (s * f' * s⁻¹) * (s * i' * s⁻¹) := by group
        _ = f' * i'⁻¹ := by rw [hsf', hAinv i' hi'.1]
    have hi'2 : i' * i' ∈ I := I.mul_mem hi' hi'
    have h2 : v * f * v⁻¹ = f * (i' * i') := by
      have e1 : u * f * u⁻¹ = (u⁻¹ * f * u) * (i' * i') := by
        rw [← he, h1]; group
      calc v * f * v⁻¹ = u * (u * f * u⁻¹) * u⁻¹ := by rw [hvdef]; group
        _ = u * ((u⁻¹ * f * u) * (i' * i')) * u⁻¹ := by rw [e1]
        _ = f * (u * (i' * i') * u⁻¹) := by group
        _ = f * (i' * i') := by rw [huI _ hi'2]; group
    have h4 : v * i * v⁻¹ = i := by rw [hvI i hi]; group
    have e : v * (f * i) * v⁻¹ * (f * i)⁻¹ = f * (i' * i') * f⁻¹ := by
      calc v * (f * i) * v⁻¹ * (f * i)⁻¹ = (v * f * v⁻¹) * (v * i * v⁻¹) * i⁻¹ * f⁻¹ := by
            group
        _ = f * (i' * i') * f⁻¹ := by rw [h2, h4]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hZI hfZ) _).mp hi'2
  obtain ⟨k, hk⟩ : ∃ k : ℕ, u ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := hR₁p ⟨u, huR₁⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hvk : v ^ p ^ k = 1 := by
    rw [hvdef, ← sq, ← pow_mul, mul_comm, pow_mul, hk, one_pow]
  have hv : v = 1 := by
    apply eq_one_of_mem_centralizer_pCoreIn hsolv hprimes hOp (K.mul_mem huK huK) hvk
    intro z hz
    set c := v * z * v⁻¹ * z⁻¹ with hc
    have hcI := hv2 z hz
    have hcv : v * c = c * v := hvI c hcI
    have hpow : ∀ n : ℕ, v ^ n * z * (v ^ n)⁻¹ = c ^ n * z := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hcn : v * c ^ n = c ^ n * v := (Commute.pow_right hcv n)
        calc v ^ (n + 1) * z * (v ^ (n + 1))⁻¹ = v * (v ^ n * z * (v ^ n)⁻¹) * v⁻¹ := by
              rw [pow_succ']; group
          _ = v * (c ^ n * z) * v⁻¹ := by rw [ih]
          _ = c ^ n * (v * z * v⁻¹) := by
              rw [show v * (c ^ n * z) * v⁻¹ = (v * c ^ n) * z * v⁻¹ by group, hcn]
              group
          _ = c ^ (n + 1) * z := by rw [hc, pow_succ]; group
    have h := hpow (p ^ k)
    rw [hvk, one_mul, inv_one, mul_one] at h
    have hcpow : c ^ p ^ k = 1 := by
      have := congrArg (· * z⁻¹) h
      simpa using this.symm
    have hcZ : c ∈ Z := hcI.2
    have hc1 : c = 1 := by
      have hdvd1 : orderOf c ∣ p ^ k := orderOf_dvd_of_pow_eq_one hcpow
      have hdvd2 : orderOf c ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hcZ
      obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hZr
      rw [hb] at hdvd2
      have hcop' : Nat.Coprime (p ^ k) (r ^ b) :=
        Nat.Coprime.pow k b ((Nat.coprime_primes Fact.out Fact.out).mpr hpr)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop' hdvd1 hdvd2)
    have : v * z * v⁻¹ = z := by
      have := congrArg (· * z) hc1
      simpa [hc, mul_assoc] using this
    calc v * z = v * z * v⁻¹ * v := by group
      _ = z * v := by rw [this]
  exact Omnibus.eq_one_of_sq_eq_one hodd (by rw [sq]; exact hv)

end CFSG.ABGTheoremB.V4
