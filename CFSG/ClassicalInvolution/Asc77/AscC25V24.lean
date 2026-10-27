module

public import CFSG.ClassicalInvolution.Asc77.AscC25V19

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups commutatorElement

section Sylow

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem fs_fix_equiv' (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {b : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) (hb2 : b * b = 1)
    (hσ1 : fieldChar hp hq e ⟨b, hbN⟩ ≠ 1) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 0 < e₀ ∧
      Nonempty (↥(slFix e ⟨b, hbN⟩) ≃* SL(2, GaloisField p e₀)) := by
  have hf : f ≠ 0 := (gf_facts hp hq).1
  have hσ2 : fieldChar hp hq e ⟨b, hbN⟩ * fieldChar hp hq e ⟨b, hbN⟩ = 1 := by
    have h1 : (⟨b, hbN⟩ : Subgroup.normalizer (K : Set G)) * ⟨b, hbN⟩ = 1 := Subtype.ext hb2
    rw [← map_mul, h1, map_one]
  obtain ⟨e₀, hfe, hfrob⟩ := eq_frobenius_of_sq_eq_one hf hσ2 hσ1
  have he₀ : 0 < e₀ := by
    rcases Nat.eq_zero_or_pos e₀ with h | h
    · subst h
      rw [hfe] at hq
      simp at hq
    · exact h
  refine ⟨e₀, hfe, he₀, ?_⟩
  obtain ⟨g, hg⟩ := exists_semilinHom_of_mem e (gf_facts hp hq).2.1 (gf_facts hp hq).2.2.1
    (gf_facts hp hq).2.2.2 ⟨b, hbN⟩
  have hg' : ∀ x, slAut K e ⟨b, hbN⟩ x = semilinHom g (fieldChar hp hq e ⟨b, hbN⟩) x := hg
  have hφ : ∀ x, semilinHom g (fieldChar hp hq e ⟨b, hbN⟩)
      (semilinHom g (fieldChar hp hq e ⟨b, hbN⟩) x) = x := by
    intro x
    have h1 := slAut_slAut_of_mul_self e ⟨b, hbN⟩ hb2 x
    rw [← hg' x, ← hg' (slAut K e ⟨b, hbN⟩ x)]
    exact h1
  have hfix : ∀ x, slAut K e ⟨b, hbN⟩ x = x ↔
      semilinHom g (fieldChar hp hq e ⟨b, hbN⟩) x = x := fun x => by
    rw [hg' x]
  subst hfe
  obtain ⟨φ⟩ := factF0 p e₀ hp he₀ (fieldChar hp hq e ⟨b, hbN⟩) hσ1 hσ2 g hφ
  have hfixeq : slFix e ⟨b, hbN⟩ = MonoidHom.eqLocus
      (semilinHom g (fieldChar hp hq e ⟨b, hbN⟩))
      (MonoidHom.id SL(2, GaloisField p (2 * e₀))) := by
    ext x
    exact hfix x
  exact ⟨(MulEquiv.subgroupCongr hfixeq).trans φ⟩


theorem fs_sylow_fixed'' (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {b : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) (hb2 : b * b = 1)
    (hσ1 : fieldChar hp hq e ⟨b, hbN⟩ ≠ 1) {R : Subgroup G} (hR : IsSylow2In R K)
    {Q : Subgroup G} (hQ : IsSylow2In Q (K ⊓ Subgroup.centralizer ({b} : Set G))) :
    IsQuatSub Q ∧ Nat.card R = 2 * Nat.card Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀, hfe, he₀, ⟨φ'⟩⟩ := fs_fix_equiv' hp hq e hbN hb2 hσ1
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


theorem exists_strong_sylow' (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {b : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) (hb2 : b * b = 1)
    (hσ1 : fieldChar hp hq e ⟨b, hbN⟩ ≠ 1) {R : Subgroup G} (hR : IsSylow2In R K) :
    ∃ R₁ : Subgroup G, IsSylow2In R₁ K ∧ conjSub b R₁ = R₁ ∧ IsFAut R₁ b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : IsPGroup 2 (⊥ : Subgroup G) := by
    intro x
    exact ⟨0, Subtype.ext (by simp [Subgroup.mem_bot.mp x.2])⟩
  obtain ⟨Q, hQ, -⟩ := IsSylow2In.exists_ge hbot
    (bot_le : ⊥ ≤ K ⊓ Subgroup.centralizer ({b} : Set G))
  obtain ⟨hQuat, hcard⟩ := fs_sylow_fixed'' hp hq e hbN hb2 hσ1 hR hQ
  have hQK : Q ≤ K := fun x hx => (hQ.1 hx).1
  have hQc : ∀ q ∈ Q, q * b = b * q := fun q hq' =>
    Subgroup.mem_centralizer_singleton_iff.mp (hQ.1 hq').2
  have hb2g : IsPGroup 2 (Subgroup.zpowers b) := isPGroup_two_zpowers_of_sq hb2
  have hbQ : conjSub b Q = Q := T7F2.conjSub_eq_of_centralizes hQc
  have hbnQ : Subgroup.zpowers b ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_iff_conjSub_eq.mpr hbQ
  have hW2 : IsPGroup 2 ↥(Subgroup.zpowers b ⊔ Q) :=
    IsPGroup.to_sup_of_normal_right' hb2g hQ.2.1 hbnQ
  have hWK : (Subgroup.zpowers b ⊔ Q) ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hbN) (hQK.trans Subgroup.le_normalizer)
  obtain ⟨R₁, hR₁, hR₁W⟩ := exists_sylow_normalized hW2 hWK
  have hb₁ : conjSub b R₁ = R₁ := hR₁W b
    ((le_sup_left : Subgroup.zpowers b ≤ Subgroup.zpowers b ⊔ Q) (Subgroup.mem_zpowers b))
  have hQR₁ : Q ≤ R₁ := by
    have hQn : Q ≤ Subgroup.normalizer (R₁ : Set G) := fun q hq' =>
      mem_normalizer_iff_conjSub_eq.mpr (hR₁W q ((le_sup_right : Q ≤ Subgroup.zpowers b ⊔ Q) hq'))
    have hP := IsPGroup.to_sup_of_normal_right' hQ.2.1 hR₁.2.1 hQn
    have hle : Q ⊔ R₁ ≤ K := sup_le hQK hR₁.1
    have := hR₁.2.2 (Q ⊔ R₁) hle hP le_sup_right
    rw [← this]
    exact le_sup_left
  have hQeq : R₁ ⊓ Subgroup.centralizer ({b} : Set G) = Q := by
    refine hQ.2.2 _ (inf_le_inf_right _ hR₁.1) (hR₁.2.1.to_le inf_le_left) ?_
    exact le_inf hQR₁ (fun x hx => (hQ.1 hx).2)
  refine ⟨R₁, hR₁, hb₁, ?_⟩
  refine ⟨mem_normalizer_iff_conjSub_eq.mpr hb₁, fun k _ => by rw [hb2, one_mul, mul_one],
    Q, R₁, ?_, hQuat, ⟨le_rfl, hR₁.2.1, fun V' hV'R _ hRV' => le_antisymm hV'R hRV'⟩, ?_⟩
  · rw [hQeq]
    exact ⟨le_rfl, hQ.2.1, fun V' hV'Q _ hQV' => le_antisymm hV'Q hQV'⟩
  · rw [hR₁.natCard_eq hR]
    exact hcard


end Sylow

section Defs

variable (p f : ℕ) [Fact p.Prime]


@[expose] def FieldStrong25N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 → IsFAut R' a →
      ∀ (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (haK : a ∈ Subgroup.normalizer (K : Set G))
        (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)),
        fieldChar hp hq e ⟨a, haK⟩ ≠ 1 →
          ∃ r ∈ R, (a * r) * (a * r) = 1 ∧ IsFAut R (a * r)

end Defs

section Main

variable {p f : ℕ} [Fact p.Prime]



theorem fieldStrong25N : FieldStrong25N p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF' hp hq haK e hσ1
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have hfix := fix_of_isFAut h haS hF'
  have haKn : a ∉ K := fun haKm => hσ1 (fieldChar_eq_one_of_mem hp hq e haKm haK)
  have hKa : conjSub a K = K := mem_normalizer_iff_conjSub_eq.mp haK
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hconj : ∀ {A : Subgroup G}, conjSub a A = A → ∀ x ∈ A, a * x * a ∈ A := by
    intro A hA x hx
    have := conj_mem_conjSub (n := a) hx
    rw [hA, hai] at this
    exact this
  obtain ⟨R₁, hR₁, hR₁a, hF₁⟩ := exists_strong_sylow' hp hq e haK ha2 hσ1 h.hRsyl
  obtain ⟨g, hgR, r, hr, hgar⟩ := exists_twist_of_sylow ha2 haKn (hconj hKa) h.hRsyl hR₁
    (hconj hfix.1) (hconj hR₁a)
  refine ⟨r, hr, ?_, ?_⟩
  · calc a * r * (a * r) = (g * a * g⁻¹) * (g * a * g⁻¹) := by rw [hgar]
      _ = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  · have := T7U.isFAut_conjSub hF₁ g
    rw [hgR, hgar] at this
    exact this


end Main

end CFSG.ClassicalInvolution.Asc77.C25V
