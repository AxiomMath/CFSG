module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10Sp4Fd
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag CatFactsSp4
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace X10Sp4

theorem eq_of_pow_mul_eq {p a b A B : ℕ} (hp : p.Prime) (hA : ¬ p ∣ A) (hB : ¬ p ∣ B)
    (h : p ^ a * A = p ^ b * B) : a = b ∧ A = B := by
  have key : ∀ {a b A B : ℕ}, ¬ p ∣ A → p ^ a * A = p ^ b * B → ¬ a < b := by
    intro a b A B hA h hab
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
    rw [show p ^ (a + c + 1) * B = p ^ a * (p * (p ^ c * B)) by ring] at h
    exact hA ⟨p ^ c * B, Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos a) h⟩
  have hab : a = b := by
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact absurd hlt (key hA h)
    · exact heq
    · exact absurd hgt (key hB h.symm)
  subst hab
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos a) h⟩

theorem not_dvd_sub_one {p x : ℕ} (hp : p.Prime) (hx : p ∣ x) (hx1 : 1 ≤ x) : ¬ p ∣ x - 1 := by
  intro h
  have h1 := Nat.dvd_sub hx h
  rw [show x - (x - 1) = 1 by omega] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

theorem cofactor_lt {q : ℕ} (hq : 2 ≤ q) : (q ^ 2 - 1) * (q ^ 4 - 1) < (q ^ 4) ^ 2 - 1 := by
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have e : (q ^ 4) ^ 2 - 1 = (q ^ 4 + 1) * (q ^ 4 - 1) := by
    zify [h4, Nat.one_le_pow 2 (q ^ 4) (by omega)]
    ring
  rw [e]
  have h24 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h16 : 2 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
  exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)

theorem false_of_psp_eq_sl {p f g c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hc : c = 1 ∨ c = 2)
    (h : (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) =
      c * (p ^ g * ((p ^ g) ^ 2 - 1))) : False := by
  have hq2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have hpq : p ∣ p ^ f := dvd_pow_self p (by omega)
  have hpg : p ∣ p ^ g := dvd_pow_self p (by omega)
  have hX : ¬ p ∣ ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1) := by
    intro hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
    · exact not_dvd_sub_one hp (dvd_pow hpq two_ne_zero) (Nat.one_le_pow _ _ (by omega)) hd
    · exact not_dvd_sub_one hp (dvd_pow hpq (by norm_num)) (Nat.one_le_pow _ _ (by omega)) hd
  have hY : ¬ p ∣ c * ((p ^ g) ^ 2 - 1) := by
    intro hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
    · rcases hc with rfl | rfl
      · exact hp.one_lt.ne' (Nat.dvd_one.mp hd)
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
    · exact not_dvd_sub_one hp (dvd_pow hpg two_ne_zero)
        (Nat.one_le_pow _ _ (pow_pos hp.pos g)) hd
  have h' : p ^ (f * 4) * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) =
      p ^ g * (c * ((p ^ g) ^ 2 - 1)) := by
    rw [pow_mul, h]
    ring
  obtain ⟨hfg, hXY⟩ := eq_of_pow_mul_eq hp hX hY h'
  rw [← hfg, pow_mul] at hXY
  have hlt := cofactor_lt hq2
  set X := ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)
  set Y := ((p ^ f) ^ 4) ^ 2 - 1
  rcases hc with rfl | rfl <;> omega

theorem psp_lt_psp {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    a ^ 4 * ((a ^ 2 - 1) * (a ^ 4 - 1)) < b ^ 4 * ((b ^ 2 - 1) * (b ^ 4 - 1)) := by
  have h4 : a ^ 4 < b ^ 4 := Nat.pow_lt_pow_left hab (by norm_num)
  have h2 : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
  have ha2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
  have ha4 : 1 ≤ a ^ 4 := Nat.one_le_pow _ _ ha
  have hY : (a ^ 2 - 1) * (a ^ 4 - 1) ≤ (b ^ 2 - 1) * (b ^ 4 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hYb : 0 < (b ^ 2 - 1) * (b ^ 4 - 1) := Nat.mul_pos (by omega) (by omega)
  calc a ^ 4 * ((a ^ 2 - 1) * (a ^ 4 - 1)) ≤ a ^ 4 * ((b ^ 2 - 1) * (b ^ 4 - 1)) :=
        Nat.mul_le_mul_left _ hY
    _ < b ^ 4 * ((b ^ 2 - 1) * (b ^ 4 - 1)) := Nat.mul_lt_mul_of_pos_right h4 hYb

theorem psp_inj {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a ^ 4 * ((a ^ 2 - 1) * (a ^ 4 - 1)) = b ^ 4 * ((b ^ 2 - 1) * (b ^ 4 - 1))) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (psp_lt_psp ha hab).ne
  · exact hab
  · exact absurd h (psp_lt_psp hb hab).ne'

variable {K : Type} [Field K]

theorem eq_two_mul_of_fixed_psp [Finite K] {p f' f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf' : 1 ≤ f') (hK : Nat.card K = p ^ f') (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    {α : MulAut (StatedProj (StatedSp 2 K))} (hα2 : α * α = 1) (hα1 : α ≠ 1)
    {M : Subgroup (StatedProj (StatedSp 2 K))} (hMX : M ≤ fixOf α)
    (hM : IsPComponent 2 (M.subgroupOf (fixOf α)))
    (hMm : Blueprint.LieModel (↥M ⧸ pPrimeCore 2 ↥M) .PSp 2 p f) : f' = 2 * f := by
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h2 := two_ne_zero_of_odd_card hodd
  have hq3 : 3 ≤ p ^ f := by omega
  have hZ := two_mul_card_of_lieModel_psp hp2 hMm
  have h5K : 5 ≤ Nat.card K := by
    have hle : (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) ≤
        Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := by
      rw [← hZ, ← two_mul_card_P h2]
      exact Nat.mul_le_mul_right 2 ((Nat.le_of_dvd Nat.card_pos
        (Subgroup.card_quotient_dvd_card _)).trans (Subgroup.card_le_card_group M))
    by_contra hlt
    exact absurd hle (not_le.mpr (psp_lt_psp Nat.card_pos (by omega)))
  have hcM : pPrimeCore 2 ↥M = ⊥ →
      Nat.card M * 2 = (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) := by
    intro hO
    rw [← hZ, (pPrimeCore 2 ↥M).card_eq_card_quotient_mul_card_subgroup, hO, Subgroup.card_bot,
      mul_one]
  have hOs : IsSimpleGroup ↥M → pPrimeCore 2 ↥M = ⊥ := by
    intro hs
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥M)).resolve_right fun h => ?_
    have h1 : Nat.card (↥M ⧸ pPrimeCore 2 ↥M) = 1 := by
      rw [h]
      have : Subsingleton (↥M ⧸ (⊤ : Subgroup ↥M)) := QuotientGroup.subsingleton_quotient_top
      exact Nat.card_of_subsingleton (1 : ↥M ⧸ (⊤ : Subgroup ↥M))
    rw [h1, one_mul] at hZ
    have h81 : 3 ^ 4 ≤ (p ^ f) ^ 4 := Nat.pow_le_pow_left hq3 4
    have h9 : 3 ^ 2 ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq3 2
    have hX : 0 < ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1) := Nat.mul_pos (by omega) (by omega)
    have : 81 ≤ (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) :=
      le_trans (by omega) (Nat.le_mul_of_pos_right _ hX)
    omega
  obtain ⟨A, σ, hα, hσ2, ⟨d, hd⟩, -, hfield⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      (GH74.Generic.ringChar_ne_two_of_card_eq hp hp2 hK) le_rfl).2.2 α hα2 hα1
  rw [hα] at hMX hM hα1
  by_cases hσ : σ = 1
  ·
    exfalso
    subst hσ
    rw [map_one, mul_one] at hMX hM hα1
    rcases inner_cases hp hp2 hf' hK (hK ▸ h5K) A d (mul_self_of_rep A d hd) hα1 hMX hM with
      he | h1 | h1
    · obtain ⟨e⟩ := he
      have hO : pPrimeCore 2 ↥M = ⊥ := by
        rw [← pPrimeCore_map_iso 2 e.symm, pPrimeCore_SL2 h2 (by omega), Subgroup.map_bot]
      have h3 := hcM hO
      rw [Nat.card_congr e.toEquiv, card_SL2, hK] at h3
      exact false_of_psp_eq_sl hp hp2 hf hf' (Or.inr rfl) (by rw [← h3]; exact Nat.mul_comm _ _)
    · have h3 := hcM (hOs h1.2.1)
      rw [h1.2.2, card_SL2, hK] at h3
      exact false_of_psp_eq_sl hp hp2 hf hf' (Or.inl rfl) (by rw [← h3, one_mul])
    · have h3 := hcM (hOs h1.1)
      rw [h1.2] at h3
      exact false_of_psp_eq_sl hp hp2 hf (by omega : 1 ≤ f' * 2) (Or.inl rfl)
        (by rw [pow_mul p f' 2, ← h3, one_mul])
  ·
    obtain ⟨hs, hc⟩ := field_card hodd A σ hσ2 hσ d hd hMX hM
    have h3 := hcM (hOs hs)
    rw [hc] at h3
    obtain ⟨hKk, -⟩ := hfield hσ
    have hk : Nat.card {c : K // σ c = c} =
        Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun c =>
        (CatalogueBLinearTwoDescent.mem_fixedSubfield K σ c).symm)
    rw [hk] at hKk
    set k := Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ)
    have hk1 : 1 ≤ k := by
      by_contra h0
      rw [show k = 0 by omega, zero_pow two_ne_zero] at hKk
      omega
    have hkq := psp_inj hk1 (by omega) h3
    rw [hkq, hK, ← pow_mul] at hKk
    have := Nat.pow_right_injective hp.two_le hKk
    omega

theorem cf81X10RowSpTwo :
    ∀ (N : Type) [Group N] [Finite N] (p f' f : ℕ), p.Prime → p ≠ 2 →
      Blueprint.LieModel N .PSp 2 p f' → 1 ≤ f → 5 ≤ p ^ f →
      ∀ α : MulAut N, α * α = 1 → α ≠ 1 → ∀ L : Subgroup ↥(fixedSubgroup α), IsPComponent 2 L →
        Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSp 2 p f → f' = 2 * f := by
  intro N _ _ p f' f hp hp2 hN hf h5 α hα2 hα1 L hL hLm
  obtain ⟨-, hf', F, _, _, hF, ⟨e⟩⟩ := GH74.Generic.lieModel_psp_data hN
  set α₀ := MulAut.congr e α with hα₀def
  have hα₀2 : α₀ * α₀ = 1 := by rw [hα₀def, ← map_mul, hα2, map_one]
  have hα₀1 : α₀ ≠ 1 := fun h => hα1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  have hc : ∀ x, e (α x) = α₀ (e x) := fun x => by
    rw [hα₀def, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  have hL₁X : L.map (fixedSubgroup α).subtype ≤ fixOf α := map_subtype_le L
  have hL₁ : IsPComponent 2 ((L.map (fixedSubgroup α).subtype).subgroupOf (fixOf α)) := by
    rw [show (L.map (fixedSubgroup α).subtype).subgroupOf (fixOf α) = L from
      comap_map_eq_self_of_injective (fixedSubgroup α).subtype_injective L]
    exact hL
  obtain ⟨hMX, hM⟩ := isPComponent_map_fixOf hc hL₁X hL₁
  have eL : ↥L ≃* ↥((L.map (fixedSubgroup α).subtype).map e.toMonoidHom) :=
    (L.equivMapOfInjective _ (fixedSubgroup α).subtype_injective).trans
      ((L.map (fixedSubgroup α).subtype).equivMapOfInjective e.toMonoidHom e.injective)
  exact eq_two_mul_of_fixed_psp hp hp2 hf' hF hf h5 hα₀2 hα₀1 hMX hM
    (LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ eL (pPrimeCore_map_iso 2 eL)) hLm)

end X10Sp4

end CFSG.ComponentClassification.GSThmB
