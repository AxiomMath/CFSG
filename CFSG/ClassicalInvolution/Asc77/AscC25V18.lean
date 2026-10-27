module

public import CFSG.ClassicalInvolution.Asc77.AscC25V13
public import CFSG.ClassicalInvolution.Asc77.AscC25V17

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups commutatorElement

section Arith

variable {p : ℕ} [Fact p.Prime]

theorem factorization_sl2 (hp : p ≠ 2) {e₀ f : ℕ} (hf : f = 2 * e₀) (he₀ : 0 < e₀) :
    (Nat.card SL(2, GaloisField p f)).factorization 2 =
      (Nat.card SL(2, GaloisField p e₀)).factorization 2 + 1 := by
  subst hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two (GaloisField p e₀)
  have h2 := CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two (GaloisField p (2 * e₀))
  have c1 : Nat.card (GaloisField p e₀) = p ^ e₀ := GaloisField.card p e₀ he₀.ne'
  have c2 : Nat.card (GaloisField p (2 * e₀)) = p ^ (2 * e₀) :=
    GaloisField.card p (2 * e₀) (by omega)
  have hpodd : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp
  have hmodd : Odd (p ^ e₀) := hpodd.pow
  set m := p ^ e₀ with hm
  have hm3 : 3 ≤ m := by
    have h2le : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hp3 : 3 ≤ p := by
      rcases Nat.lt_or_ge p 3 with h | h
      · exfalso
        apply hp
        omega
      · exact h
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e₀ := Nat.pow_le_pow_right (by omega) he₀
  have hmsq : p ^ (2 * e₀) = m * m := by rw [two_mul, pow_add]
  change (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p (2 * e₀)))).factorization 2 =
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p e₀))).factorization 2 + 1
  rw [h1, h2, c1, c2, hmsq]
  have hmm1 : m * m - 1 ≠ 0 := by
    have : 1 < m * m := by nlinarith
    omega
  have hfac : (m * m) ^ 2 - 1 = (m * m - 1) * (m * m + 1) := by
    have : 1 ≤ m * m := by nlinarith
    zify [this, (by nlinarith : 1 ≤ (m * m) ^ 2)]
    ring
  have hm2 : m ^ 2 - 1 = m * m - 1 := by rw [sq]
  rw [hfac, hm2]
  have hm0 : m ≠ 0 := by omega
  have hmm0 : m * m + 1 ≠ 0 := by omega
  have hv : ∀ n : ℕ, n.factorization 2 = padicValNat 2 n := fun n =>
    Nat.factorization_def n Nat.prime_two
  rw [hv, hv, padicValNat.mul (mul_ne_zero hm0 hm0) (mul_ne_zero hmm1 hmm0),
    padicValNat.mul hmm1 hmm0, padicValNat.mul hm0 hm0, padicValNat.mul hm0 hmm1]
  have hv0 : padicValNat 2 m = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro h
    exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr h))
  have hv1 : padicValNat 2 (m * m + 1) = 1 := by
    obtain ⟨j, hj⟩ := hmodd
    have e : m * m + 1 = 2 * (2 * j * j + 2 * j + 1) := by rw [hj]; ring
    have hodd : Odd (2 * j * j + 2 * j + 1) := ⟨j * j + j, by ring⟩
    have hk : padicValNat 2 (2 * j * j + 2 * j + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by
      intro h
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h))
    rw [e, padicValNat.mul (by norm_num) (Nat.succ_ne_zero _), hk]
    simp
  rw [hv0, hv1]
  ring

end Arith

section SylowFixed

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

@[expose] noncomputable def fixHom {K : Subgroup G} {F : Type} [Field F]
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) {a : G}
    (haN : a ∈ Subgroup.normalizer (K : Set G)) :
    ↥(K ⊓ Subgroup.centralizer ({a} : Set G)) →* ↥(slFix e ⟨a, haN⟩) :=
  ((slProj K e).comp (Subgroup.inclusion inf_le_left)).codRestrict _ fun c => by
    change slAut K e ⟨a, haN⟩ (slProj K e (Subgroup.inclusion inf_le_left c)) =
      slProj K e (Subgroup.inclusion inf_le_left c)
    rw [slAut_slProj]
    congr 1
    apply Subtype.ext
    rw [normalizerConj_apply_coe]
    have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2.2
    change a * c * a⁻¹ = c
    rw [← hc]
    group

theorem fixHom_surjective {K : Subgroup G} {F : Type} [Field F]
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) {a : G}
    (haN : a ∈ Subgroup.normalizer (K : Set G)) (ha2 : a * a = 1) :
    Function.Surjective (fixHom e haN) := by
  rintro ⟨b, hb⟩
  obtain ⟨c, hca, hcb⟩ := exists_mem_centralizer_of_slAut_eq e haN ha2 hb
  exact ⟨⟨c, c.2, hca⟩, Subtype.ext hcb⟩

theorem mem_oddCoreOf_of_fixHom_eq_one {K : Subgroup G} {F : Type} [Field F]
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) {a : G}
    (haN : a ∈ Subgroup.normalizer (K : Set G))
    {x : ↥(K ⊓ Subgroup.centralizer ({a} : Set G))} (hx : fixHom e haN x = 1) :
    (x : G) ∈ oddCoreOf K := by
  have h2 : slProj K e (Subgroup.inclusion inf_le_left x) = 1 := congrArg Subtype.val hx
  exact (slProj_eq_one_iff e _).mp h2

theorem fs_sylow_fixed (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {b : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) (hb2 : b * b = 1)
    (hσ1 : fieldChar hp hq e ⟨b, hbN⟩ ≠ 1) {R : Subgroup G} (hR : IsSylow2In R K) :
    ∃ Q : Subgroup G, IsSylow2In Q (K ⊓ Subgroup.centralizer ({b} : Set G)) ∧ IsQuatSub Q ∧
      Nat.card R = 2 * Nat.card Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀, hfe, h5, ⟨φ'⟩⟩ := fs_fix_equiv hp hq h9 e hbN hb2 hσ1
  have he₀ : 0 < e₀ := by
    rcases Nat.eq_zero_or_pos e₀ with h | h
    · subst h
      simp at h5
    · exact h
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({b} : Set G) with hC
  let π := fixHom e hbN
  have hπs : Function.Surjective π := fixHom_surjective e hbN hb2
  let ρ : ↥C →* SL(2, GaloisField p e₀) := φ'.toMonoidHom.comp π
  have hρs : Function.Surjective ρ := φ'.surjective.comp hπs
  have hρk : ∀ x : ↥C, ρ x = 1 → (x : G) ∈ oddCoreOf K := by
    intro x hx
    have h1 : π x = 1 := by
      have : φ' (π x) = 1 := hx
      exact (MulEquiv.map_eq_one_iff φ').mp this
    exact mem_oddCoreOf_of_fixHom_eq_one e hbN h1
  have hbot : IsPGroup 2 (⊥ : Subgroup G) := by
    intro x
    exact ⟨0, Subtype.ext (by simp [Subgroup.mem_bot.mp x.2])⟩
  obtain ⟨Q, hQ, -⟩ := IsSylow2In.exists_ge hbot (bot_le : ⊥ ≤ C)
  refine ⟨Q, hQ, ?_⟩
  set Qc : Subgroup ↥C := Q.subgroupOf C with hQc
  set P : Sylow 2 ↥C := sylowOfIsSylow2In hQ with hPdef
  have hPc : (P : Subgroup ↥C) = Qc := coe_sylowOfIsSylow2In hQ
  have hF₀ : ringChar (GaloisField p e₀) ≠ 2 := by
    rw [ringChar.eq (GaloisField p e₀) p]
    exact hp
  have hinj : Function.Injective (ρ.comp Qc.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : ρ (x : ↥C) = 1 := hx
    have hxN := hρk _ hx1
    have hxQ : ((x : ↥C) : G) ∈ Q := x.2
    have hx2 : IsPGroup 2 (Subgroup.zpowers ((x : ↥C) : G)) :=
      hQ.2.1.to_le (Subgroup.zpowers_le.mpr hxQ)
    have : ((x : ↥C) : G) = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hxN hx2
    exact Subtype.ext (Subtype.ext this)
  have hcoe : ((Sylow.mapSurjective hρs P : Sylow 2 SL(2, GaloisField p e₀)) :
      Subgroup SL(2, GaloisField p e₀)) = Qc.map ρ := by
    rw [Sylow.coe_mapSurjective, hPc]
  obtain ⟨k, hk, ⟨qq⟩⟩ := specialLinearGroup_sylow_quaternion (GaloisField p e₀) hF₀
    (Sylow.mapSurjective hρs P)
  let e2 : ↥Qc ≃* ↥(Qc.map ρ) :=
    MulEquiv.ofBijective ((ρ.comp Qc.subtype).codRestrict (Qc.map ρ)
      (fun x => ⟨x, x.2, rfl⟩))
      ⟨fun a b h => hinj (congrArg Subtype.val h), by
        rintro ⟨_, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩⟩
  have eQ : ↥Q ≃* ↥(Qc.map ρ) := (Subgroup.subgroupOfEquivOfLe hQ.1).symm.trans e2
  have hQuat : IsQuatSub Q := by
    refine ⟨k, hk, ⟨?_⟩⟩
    exact eQ.trans ((MulEquiv.subgroupCongr hcoe.symm).trans qq)
  have hcardQ : Nat.card Q = 2 ^ (Nat.card SL(2, GaloisField p e₀)).factorization 2 := by
    have h1 := Sylow.card_eq_multiplicity (Sylow.mapSurjective hρs P)
    have h2 : Nat.card ↥((Sylow.mapSurjective hρs P : Sylow 2 SL(2, GaloisField p e₀)) :
          Subgroup SL(2, GaloisField p e₀)) =
        Nat.card ↥(Qc.map ρ) := by rw [hcoe]
    rw [h2, ← Nat.card_congr eQ.toEquiv] at h1
    exact h1
  have h1 : Nat.card R = 2 ^ (Nat.card K).factorization 2 := by
    have := Sylow.card_eq_multiplicity (sylowOfIsSylow2In hR)
    have c1 : Nat.card ↥((sylowOfIsSylow2In hR : Sylow 2 ↥K) : Subgroup ↥K) = Nat.card R := by
      rw [coe_sylowOfIsSylow2In]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR.1).toEquiv
    rw [← c1]
    exact this
  have hKcard : Nat.card K =
      Nat.card (↥K ⧸ classicalInvolutionOddCore ↥K) * Nat.card (classicalInvolutionOddCore ↥K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥K)) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hz : (Nat.card (classicalInvolutionOddCore ↥K)).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      intro h
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h))
  have hKQ : (Nat.card K).factorization 2 = (Nat.card SL(2, GaloisField p f)).factorization 2 := by
    have hne1 : Nat.card (↥K ⧸ classicalInvolutionOddCore ↥K) ≠ 0 := Nat.card_pos.ne'
    have hne2 : Nat.card (classicalInvolutionOddCore ↥K) ≠ 0 := Nat.card_pos.ne'
    rw [hKcard, Nat.factorization_mul hne1 hne2, Finsupp.add_apply, hz, add_zero,
      Nat.card_congr e.toEquiv]
  refine ⟨hQuat, ?_⟩
  rw [h1, hKQ, factorization_sl2 hp hfe he₀, pow_succ, hcardQ]
  ring

end SylowFixed

end CFSG.ClassicalInvolution.Asc77.C25V
