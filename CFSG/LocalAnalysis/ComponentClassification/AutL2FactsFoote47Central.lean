module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47Inputs
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFourgroupA7
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsAutPSL2Involution

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup Equiv
open scoped commutatorElement

theorem dihedral_center_le_commutator {n : ℕ} (hn : 4 ∣ n) :
    center (DihedralGroup n) ≤ ⁅(⊤ : Subgroup (DihedralGroup n)), ⊤⁆ := by
  obtain ⟨k, rfl⟩ := hn
  rw [DihedralGroup.center_eq_closure_of_even_ne_two ⟨2 * k, by ring⟩ (by omega), zpowers_le]
  have h1 : ⁅(DihedralGroup.r 1 : DihedralGroup (4 * k)), (DihedralGroup.sr 0 : DihedralGroup
      (4 * k))⁆ = DihedralGroup.r 2 := by
    rw [commutatorElement_def, DihedralGroup.inv_r, DihedralGroup.inv_sr, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
    congr 1
    ring
  have h2 : DihedralGroup.r (((4 * k / 2 : ℕ)) : ZMod (4 * k)) = DihedralGroup.r 2 ^ k := by
    rw [DihedralGroup.r_pow, show 4 * k / 2 = 2 * k by omega, Nat.cast_mul, Nat.cast_ofNat]
  rw [h2, ← h1]
  exact pow_mem (commutator_mem_commutator (mem_top _) (mem_top _)) k

theorem mem_commutator_of_dihedral {S : Type*} [Group S] {R : Subgroup S} {n : ℕ} (hn : 4 ∣ n)
    (ρ : R ≃* DihedralGroup n) {c : S} (hc : c ∈ R) (hcZ : ∀ r ∈ R, c * r = r * c) :
    c ∈ ⁅R, R⁆ := by
  have hcen : ρ ⟨c, hc⟩ ∈ center (DihedralGroup n) := by
    rw [mem_center_iff]
    intro d
    obtain ⟨d', rfl⟩ := ρ.surjective d
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcZ d' d'.2).symm
  have hmap : Subgroup.map (R.subtype.comp ρ.symm.toMonoidHom)
      ⁅(⊤ : Subgroup (DihedralGroup n)), ⊤⁆ ≤ ⁅R, R⁆ := by
    rw [map_commutator]
    apply commutator_mono <;> rintro _ ⟨x, -, rfl⟩ <;> exact (ρ.symm x).2
  have := hmap ⟨_, dihedral_center_le_commutator hn hcen, rfl⟩
  simpa using this

theorem exists_dihedral_eight_a7 :
    ∃ H : Subgroup (alternatingGroup (Fin 7)), Nonempty (H ≃* DihedralGroup 4) := by
  set ρ : alternatingGroup (Fin 7) := ⟨a7Rho, a7Rho_mem⟩
  set σ : alternatingGroup (Fin 7) := ⟨a7Sigma, a7Sigma_mem⟩
  have hσ2 : σ * σ = 1 := Subtype.ext (by decide)
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := Subtype.ext (by decide)
  have hne : ρ * σ ≠ σ * ρ := fun h => by
    have := congrArg Subtype.val h
    revert this
    decide
  have hρ4 : orderOf ρ = 4 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf a7Rho = 4
    apply (orderOf_eq_iff (by norm_num)).mpr
    constructor
    · decide
    · intro m hm0 hm4
      interval_cases m <;> decide
  have hσU : σ ∉ zpowers ρ := by
    rintro ⟨k, hk⟩
    apply hne
    rw [← hk]
    exact ((Commute.refl ρ).zpow_left k).eq.symm
  have hinv : ∀ x ∈ zpowers ρ, σ * x * σ⁻¹ = x⁻¹ := by
    rintro _ ⟨k, rfl⟩
    have := map_zpow (MulAut.conj σ) ρ k
    simp only [MulAut.conj_apply] at this
    rw [this, hrel, inv_zpow]
  have h := CFSG.Walter.nonempty_sup_zpowers_mulEquiv_dihedralGroup (zpowers ρ) σ hσU hσ2 hinv
  rw [Nat.card_zpowers, hρ4] at h
  exact ⟨_, h⟩

theorem sylow_two_dihedral_a7 {S : Type} [Group S] [Finite S] (e : S ≃* alternatingGroup (Fin 7))
    (R : Sylow 2 S) : Nonempty ((R : Subgroup S) ≃* DihedralGroup 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H, ⟨d⟩⟩ := exists_dihedral_eight_a7
  have hH8 : Nat.card H = 8 := by rw [Nat.card_congr d.toEquiv, DihedralGroup.nat_card]
  set H' := H.map e.symm.toMonoidHom with hH'
  have hH'card : Nat.card H' = 8 := by rw [hH', card_map_of_injective e.symm.injective, hH8]
  have hH'2 : IsPGroup 2 H' := IsPGroup.of_card (n := 3) (by rw [hH'card]; norm_num)
  have hidx : ¬ 2 ∣ H'.index := by
    have h1 := H'.card_mul_index
    rw [hH'card, Nat.card_congr e.toEquiv, card_alternatingGroup_seven] at h1
    omega
  exact ⟨(Sylow.equiv R (hH'2.toSylow hidx)).trans ((MulEquiv.subgroupCongr
    (IsPGroup.toSylow_coe hH'2 hidx)).trans ((H.equivMapOfInjective _ e.symm.injective).symm.trans
      d))⟩

theorem eight_dvd_card_of_sq {a : ℕ} (ha : Odd a) : 2 ^ 3 ∣ a ^ 2 * ((a ^ 2) ^ 2 - 1) / 2 := by
  have h1 : a ^ 2 % 8 = 1 := by
    rw [Nat.pow_mod]
    have hlt : a % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have hodd : a % 8 % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 8)]
      exact Nat.odd_iff.mp ha
    interval_cases h : a % 8 <;> simp_all
  obtain ⟨t, ht⟩ : ∃ t, a ^ 2 = 8 * t + 1 := ⟨a ^ 2 / 8, by omega⟩
  rw [ht]
  have h2 : (8 * t + 1) ^ 2 - 1 = 16 * (4 * t ^ 2 + t) := by
    rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
    ring
  rw [h2, show (8 * t + 1) * (16 * (4 * t ^ 2 + t)) = 2 * (8 * ((8 * t + 1) * (4 * t ^ 2 + t)))
    by ring, Nat.mul_div_cancel_left _ (by norm_num), show (2 : ℕ) ^ 3 = 8 by norm_num]
  exact Nat.dvd_mul_right 8 _

variable {F : Type} [Field F] [Finite F]

theorem autEquiv_commute_of_fix {Y : Type} [Group Y] (e : Y ≃* PSL2 F) {τ : MulAut Y} {r : Y}
    (hr : τ r = r) : autEquiv e τ * incl F (e r) = incl F (e r) * autEquiv e τ := by
  have h1 : τ * MulAut.conj r * τ⁻¹ = MulAut.conj r := by rw [mulAut_conj_conj, hr]
  have h2 : τ * MulAut.conj r = MulAut.conj r * τ := by
    calc τ * MulAut.conj r = τ * MulAut.conj r * τ⁻¹ * τ := by group
      _ = MulAut.conj r * τ := by rw [h1]
  rw [← autEquiv_conj, ← map_mul, ← map_mul, h2]

theorem cfFoote47CentralInvolution : Foote47.Foote47CentralInvolution := by
  intro S _ _ hS R τ hτ2 hτout hRτ c hcR hc2 hcZ hτc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdih : ∀ n : ℕ, 4 ∣ n → Nonempty ((R : Subgroup S) ≃* DihedralGroup n) →
      MulAut.conj c ∈ ⁅(R : Subgroup S).map (MulAut.conj : S →* MulAut S) ⊔ zpowers τ,
        (R : Subgroup S).map (MulAut.conj : S →* MulAut S) ⊔ zpowers τ⁆ := by
    rintro n hn ⟨ρ⟩
    have h2 : MulAut.conj c ∈ ⁅(R : Subgroup S), (R : Subgroup S)⁆.map
        (MulAut.conj : S →* MulAut S) := mem_map_of_mem _ (mem_commutator_of_dihedral hn ρ hcR hcZ)
    rw [map_commutator] at h2
    exact commutator_mono le_sup_left le_sup_left h2
  rcases hS with ⟨⟨e⟩⟩ | ⟨p, f, hp, hp2, hf1, -, hL⟩
  · exact hdih 4 (dvd_refl 4) (sylow_two_dihedral_a7 e R)
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hL
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hp.odd_of_ne_two hp2, hf1, hF⟩
  obtain ⟨m, hm1, hρ⟩ := sylow_two_dihedral_of_equiv e hodd R
  by_cases hm2 : 2 ≤ m
  · exact hdih (2 ^ m) (by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.pow_dvd_pow 2 hm2) hρ
  rw [show m = 1 by omega, pow_one] at hρ
  obtain ⟨ρ⟩ := hρ
  have hR4 : Nat.card (R : Subgroup S) = 4 := by
    rw [Nat.card_congr ρ.toEquiv, DihedralGroup.nat_card]
  have hfodd : ¬ Even f := by
    rintro ⟨t, rfl⟩
    have h8 : 2 ^ 3 ∣ Nat.card S := by
      rw [Nat.card_congr e.toEquiv, psl2_card_formula F hodd, hF, ← mul_two, pow_mul]
      exact eight_dvd_card_of_sq (hp.odd_of_ne_two hp2).pow
    have h4 : 2 ^ 3 ∣ Nat.card (R : Subgroup S) := R.pow_dvd_card_of_pow_dvd_card h8
    rw [hR4] at h4
    norm_num at h4
  have hright : (autEquiv e τ).right = 1 := by
    have h1 : (autEquiv e τ).right ^ 2 = 1 := by
      rw [pow_two, ← SemidirectProduct.mul_right, ← map_mul, hτ2, map_one,
        SemidirectProduct.one_right]
    have h2 : orderOf (autEquiv e τ).right ∣ f := by
      rw [← card_ringAut F hp hF]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1) with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at h2
      exact absurd (even_iff_two_dvd.mpr h2) hfodd
  have hD2 : ∀ x : DihedralGroup 2, x * x = 1 := by decide
  obtain ⟨a, haR, hτa⟩ : ∃ a ∈ (R : Subgroup S), τ a ≠ a := by
    by_contra hcon
    push Not at hcon
    set V := (R : Subgroup S).map ((incl F).comp e.toMonoidHom) with hV
    have hV4 : Nat.card V = 4 := by
      rw [hV, card_map_of_injective (f := (incl F).comp e.toMonoidHom)
        (fun x y h => e.injective (incl_injective F h)), hR4]
    have hV2 : ∀ v ∈ V, v * v = 1 := by
      rintro _ ⟨r, hr, rfl⟩
      have h1 : ρ (⟨r, hr⟩ * ⟨r, hr⟩) = ρ 1 := by rw [map_mul, map_one]; exact hD2 _
      have h2 : r * r = 1 := congrArg Subtype.val (ρ.injective h1)
      rw [← map_mul, h2, map_one]
    have hg2 : autEquiv e τ * autEquiv e τ = 1 := by rw [← map_mul, hτ2, map_one]
    have hgV : autEquiv e τ ∉ V := by
      intro hg
      apply hτout
      have : autEquiv e τ ∈ pGammaL2PSLRange F := by
        obtain ⟨r, -, hr⟩ := hg
        exact ⟨e r, hr⟩
      rw [← map_autEquiv_innAut e] at this
      obtain ⟨y, hy, hyg⟩ := this
      rwa [(autEquiv e).injective hyg] at hy
    have hgc : ∀ v ∈ V, autEquiv e τ * v = v * autEquiv e τ := by
      rintro _ ⟨r, hr, rfl⟩
      exact autEquiv_commute_of_fix e (hcon r hr)
    obtain ⟨E, -, -, hEle, hE2, hE8⟩ := exists_e8_of_centralizing V hV2 hV4 hg2 hgV hgc
    obtain ⟨y, hyE, hy⟩ := exists_right_ne_one_of_card_eight hodd E hE2 hE8.ge
    apply hy
    have hker : V ⊔ zpowers (autEquiv e τ) ≤
        (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F)).ker := by
      refine sup_le ?_ ?_
      · rintro _ ⟨r, -, rfl⟩
        rw [MonoidHom.mem_ker]
        simp [incl_apply]
      · rw [zpowers_le, MonoidHom.mem_ker]
        exact hright
    exact MonoidHom.mem_ker.mp (hker (hEle hyE))
  have hτaR : τ a ∈ (R : Subgroup S) := by
    rw [← hRτ]
    exact mem_map_of_mem _ haR
  have hinj : ∀ (u v : S) (hu : u ∈ (R : Subgroup S)) (hv : v ∈ (R : Subgroup S)),
      ρ ⟨u, hu⟩ = ρ ⟨v, hv⟩ → u = v := fun u v hu hv h => congrArg Subtype.val (ρ.injective h)
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hτa (map_one τ)
  have hac : a ≠ c := by
    rintro rfl
    exact hτa hτc
  have hkey : ∀ x y z : DihedralGroup 2, x ≠ 1 → y ≠ 1 → x ≠ y → z ≠ 1 → z ≠ x → z ≠ y →
      z = x * y := by decide
  have hτa' : τ a = a * c := by
    have h := hkey (ρ ⟨a, haR⟩) (ρ ⟨c, hcR⟩) (ρ ⟨τ a, hτaR⟩)
      (fun h => ha1 (hinj a 1 haR (one_mem _) (h.trans (map_one ρ).symm)))
      (fun h => hc1 (hinj c 1 hcR (one_mem _) (h.trans (map_one ρ).symm)))
      (fun h => hac (hinj a c haR hcR h))
      (fun h => ha1 ((map_eq_one_iff τ τ.injective).mp
        (hinj _ 1 hτaR (one_mem _) (h.trans (map_one ρ).symm))))
      (fun h => hτa (hinj _ a hτaR haR h))
      (fun h => hac (τ.injective ((hinj _ c hτaR hcR h).trans hτc.symm)))
    rw [← map_mul] at h
    exact congrArg Subtype.val (ρ.injective h)
  have hcomm : ⁅MulAut.conj a⁻¹, τ⁆ = MulAut.conj c := by
    rw [commutatorElement_def, map_inv, inv_inv]
    calc (MulAut.conj a)⁻¹ * τ * MulAut.conj a * τ⁻¹
        = (MulAut.conj a)⁻¹ * (τ * MulAut.conj a * τ⁻¹) := by group
      _ = (MulAut.conj a)⁻¹ * MulAut.conj (τ a) := by rw [mulAut_conj_conj]
      _ = MulAut.conj c := by rw [hτa', map_mul, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [← hcomm]
  exact commutator_mem_commutator (mem_sup_left (mem_map_of_mem _ (inv_mem haR)))
    (mem_sup_right (mem_zpowers τ))

end CFSG.ComponentClassification.AutL2Facts
