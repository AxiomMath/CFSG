module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralModelStd
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral.Model

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.AutL2Facts

variable {F : Type} [Field F] [Finite F]

theorem sqLeft_conj (c x : PGammaL2 F) : SqLeft (c * x * c⁻¹) ↔ SqLeft x := by
  rw [sqLeft_mul, sqLeft_mul, sqLeft_inv]
  tauto

theorem sqLeft_of_involution (hodd : IsOddPrimePower (Nat.card F)) {r : PGammaL2 F}
    (hr2 : r * r = 1) (hr1 : r.right ≠ 1) : SqLeft r := by
  have hne : r ≠ 1 := fun h => hr1 (by rw [h]; rfl)
  have hord : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two, hr2]) hne
  obtain ⟨b, σ, -, hrb⟩ := isFieldInvModel_of_involution hodd hord hr1
  rw [hrb, sqLeft_conj]
  change (SemidirectProduct.inr σ : PGammaL2 F).left ∈ _
  exact one_mem _

theorem facts_of_even {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hfe : Even f) : IsSquare (-1 : F) ∧ Nat.card F % 4 = 1 ∧ 3 ≤ twoVal F := by
  have hq4 : Nat.card F % 4 = 1 := by rw [hF]; exact pow_mod_four_of_even hp hp2 hfe
  refine ⟨?_, hq4, ?_⟩
  · have : Fintype F := Fintype.ofFinite F
    classical
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
    omega
  · have h8 : 2 ^ 3 ∣ Nat.card F - 1 := by rw [hF]; exact eight_dvd_of_even hp hp2 hfe
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by
      have := Finite.one_lt_card (α := F); omega)).mp h8

theorem even_of_orderOf_two {p f : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ f)
    {σ₀ : F ≃+* F} (hσ₀ : orderOf σ₀ = 2) : Even f := by
  have := orderOf_dvd_natCard σ₀
  rw [hσ₀, card_ringAut F hp hF] at this
  exact even_iff_two_dvd.mpr this

theorem exists_conj_rStd (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    (hq4 : Nat.card F % 4 = 1) (T : Sylow 2 (PSL2 F)) :
    ∃ c ∈ pGammaL2PSLRange F, ∀ g : PGammaL2 F,
      g ∈ (T : Subgroup (PSL2 F)).map (incl F) ↔ c⁻¹ * g * c ∈ rStd F := by
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (PSL2 F) (stdSylow F hodd hsq hq4) T
  have hD : ∀ d : PSL2 F, d ∈ (T : Subgroup (PSL2 F)) ↔ h⁻¹ * d * h ∈ stdT F := by
    intro d
    rw [← hh, mem_smul_sylow_iff, coe_stdSylow]
  refine ⟨incl F h, ⟨h, rfl⟩, fun g => ⟨?_, ?_⟩⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨h⁻¹ * d * h, (hD d).mp hd, by simp only [map_mul, map_inv]⟩
  · rintro ⟨t, ht, hgt⟩
    refine ⟨h * t * h⁻¹, (hD _).mpr (by rwa [show h⁻¹ * (h * t * h⁻¹) * h = t by group]), ?_⟩
    rw [map_mul, map_mul, map_inv, hgt]
    group

theorem card_D0 (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    (hq4 : Nat.card F % 4 = 1) (T : Sylow 2 (PSL2 F)) :
    Nat.card ((T : Subgroup (PSL2 F)).map (incl F)) = 2 ^ twoVal F := by
  rw [card_map_of_injective (incl_injective F), Sylow.card_eq_multiplicity,
    ← card_stdT hodd hsq, ← coe_stdSylow hodd hsq hq4, Sylow.card_eq_multiplicity]

theorem eight_le_card {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hodd : IsOddPrimePower (Nat.card F)) (hfe : Even f) (T : Sylow 2 (PSL2 F)) :
    8 ≤ Nat.card ((T : Subgroup (PSL2 F)).map (incl F)) := by
  obtain ⟨hsq, hq4, hn⟩ := facts_of_even hp hp2 hF hfe
  rw [card_D0 hodd hsq hq4]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ twoVal F := Nat.pow_le_pow_right (by norm_num) hn

theorem right_sq_of_commute {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hodd : IsOddPrimePower (Nat.card F)) (T : Sylow 2 (PSL2 F)) (x : PGammaL2 F) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) (hx : ∀ d ∈ (T : Subgroup (PSL2 F)).map (incl F), x * d = d * x) :
    x.right ^ 2 = 1 := by
  have hk' : x.right ^ 2 ^ k = 1 := by
    rw [← right_pow, hk]; rfl
  rcases Nat.even_or_odd f with hfe | hfo
  · obtain ⟨hsq, hq4, hn⟩ := facts_of_even hp hp2 hF hfe
    obtain ⟨c, -, hc⟩ := exists_conj_rStd hodd hsq hq4 T
    have h := std_right_sq hp hp2 hF hodd hsq (by omega) (c⁻¹ * x * c) (k := k)
      (by rw [show (c⁻¹ * x * c).right = x.right by
        simpa using right_conj c⁻¹ x]; exact hk') (fun d hd => by
        have hd' : c * d * c⁻¹ ∈ (T : Subgroup (PSL2 F)).map (incl F) :=
          (hc _).mpr (by simpa [mul_assoc] using hd)
        have := hx _ hd'
        calc c⁻¹ * x * c * d = c⁻¹ * (x * (c * d * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * d * c⁻¹) * x) * c := by rw [this]
          _ = d * (c⁻¹ * x * c) := by group)
    rwa [show (c⁻¹ * x * c).right = x.right by simpa using right_conj c⁻¹ x] at h
  · rw [eq_one_of_two_power_ringAut hp hF hfo x.right k hk', one_pow]

theorem exists_k {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hodd : IsOddPrimePower (Nat.card F)) (T : Sylow 2 (PSL2 F)) {σ₀ : F ≃+* F}
    (hσ₀ : orderOf σ₀ = 2) :
    ∃ k : PGammaL2 F, k.right = σ₀ ∧ k * k = 1 ∧ SqLeft k ∧
      ∀ d ∈ (T : Subgroup (PSL2 F)).map (incl F), k * d = d * k := by
  obtain ⟨hsq, hq4, hn⟩ := facts_of_even hp hp2 hF (even_of_orderOf_two hp hF hσ₀)
  obtain ⟨c, -, hc⟩ := exists_conj_rStd hodd hsq hq4 T
  refine ⟨c * k0 σ₀ * c⁻¹, by rw [right_conj, k0_right], ?_, ?_, fun d hd => ?_⟩
  · calc c * k0 σ₀ * c⁻¹ * (c * k0 σ₀ * c⁻¹) = c * (k0 σ₀ * k0 σ₀) * c⁻¹ := by group
      _ = 1 := by rw [k0_mul_self hσ₀]; group
  · rw [sqLeft_conj]; exact k0_sqLeft hsq σ₀
  · have h := k0_commute hp hp2 hF hodd hsq hσ₀ ((hc d).mp hd)
    calc c * k0 σ₀ * c⁻¹ * d = c * (k0 σ₀ * (c⁻¹ * d * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * d * c) * k0 σ₀) * c⁻¹ := by rw [h]
      _ = d * (c * k0 σ₀ * c⁻¹) := by group

theorem mem_of_normalizes {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hodd : IsOddPrimePower (Nat.card F)) (hfe : Even f) (T : Sylow 2 (PSL2 F))
    {y : PGammaL2 F} (hyL : y ∈ pGammaL2PSLRange F)
    (hyN : ∀ d ∈ (T : Subgroup (PSL2 F)).map (incl F),
      y * d * y⁻¹ ∈ (T : Subgroup (PSL2 F)).map (incl F)) :
    y ∈ (T : Subgroup (PSL2 F)).map (incl F) := by
  obtain ⟨hsq, hq4, hn⟩ := facts_of_even hp hp2 hF hfe
  obtain ⟨c, hcL, hc⟩ := exists_conj_rStd hodd hsq hq4 T
  rw [hc]
  refine std_normalizer hodd hsq hn (mul_mem (mul_mem (inv_mem hcL) hyL) hcL) fun d hd => ?_
  have hd' : c * d * c⁻¹ ∈ (T : Subgroup (PSL2 F)).map (incl F) :=
    (hc _).mpr (by simpa [mul_assoc] using hd)
  have := (hc _).mp (hyN _ hd')
  simpa [mul_assoc] using this

end CFSG.ComponentClassification.HSDihedral.Model
