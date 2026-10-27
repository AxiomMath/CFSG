module

public import CFSG.GF2Type.Aschbacher1976Full.Defs
public import CFSG.Milestones.LR_semidihedral_simple_recognition
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8Tools

public section

namespace CFSG.GF2Type.Aschbacher1976Full.LeafSemidihedral

variable {G : Type} [Group G] [Finite G]

theorem mem_Hz_iff {z g : G} : g ∈ Hz z ↔ g * z = z * g :=
  Subgroup.mem_centralizer_singleton_iff

theorem exists_sylow_of_equiv {z : G} (hz : orderOf z = 2) {n : ℕ} (hn : 4 ≤ n)
    (e : ↥(Hz z) ≃* CFSG.Open.SemidihedralGroup n) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = Hz z := by
  have hcard : Nat.card ↥(Hz z) = 2 ^ n :=
    (Nat.card_congr e.toEquiv).trans (CFSG.Semidihedral.card n (by omega))
  have hP : IsPGroup 2 (Hz z) := IsPGroup.iff_card.mpr ⟨n, hcard⟩
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hzH : z ∈ Hz z := mem_Hz_iff.mpr rfl
  have hcenter : Nat.card (Subgroup.center ↥(Hz z)) = 2 :=
    (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans
      (CFSG.Semidihedral.center_card n hn)
  obtain ⟨zH, hzH_val⟩ : ∃ w : ↥(Hz z), (w : G) = z := ⟨⟨z, hzH⟩, rfl⟩
  have hzH_order : orderOf zH = 2 := by
    rw [← Subgroup.orderOf_coe, hzH_val]
    exact hz
  have hzH_mem : zH ∈ Subgroup.center ↥(Hz z) := by
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hzH_val]
    exact mem_Hz_iff.mp g.2
  have hzeq : Subgroup.zpowers zH = Subgroup.center ↥(Hz z) := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzH_mem)
    rw [Nat.card_zpowers, hzH_order, hcenter]
  have hN : Subgroup.normalizer ((Hz z : Subgroup G) : Set G) ≤ Hz z := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff] at hx
    have hu : x * z * x⁻¹ ∈ Hz z := (hx z).mp hzH
    have hconj : ∀ h ∈ Hz z, h * (x * z * x⁻¹) = (x * z * x⁻¹) * h := by
      intro h hh
      have hw : x⁻¹ * h * x ∈ Hz z := (hx (x⁻¹ * h * x)).mpr (by
        rw [show x * (x⁻¹ * h * x) * x⁻¹ = h by group]
        exact hh)
      have hwz := mem_Hz_iff.mp hw
      calc h * (x * z * x⁻¹) = x * ((x⁻¹ * h * x) * z) * x⁻¹ := by group
        _ = x * (z * (x⁻¹ * h * x)) * x⁻¹ := by rw [hwz]
        _ = (x * z * x⁻¹) * h := by group
    obtain ⟨uH, huH_val⟩ : ∃ w : ↥(Hz z), (w : G) = x * z * x⁻¹ := ⟨⟨x * z * x⁻¹, hu⟩, rfl⟩
    have huC : uH ∈ Subgroup.center ↥(Hz z) := by
      refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul, huH_val]
      exact hconj g.1 g.2
    have huz : uH ∈ Subgroup.zpowers zH := by
      rw [hzeq]
      exact huC
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp huz
    have hmod : zH ^ (k % 2) = zH ^ k := by
      have h := zpow_mod_orderOf zH k
      rw [hzH_order] at h
      exact_mod_cast h
    have hkey : zH ^ (k % 2) = uH := hmod.trans hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero] at hkey
      have h1' : x * z * x⁻¹ = 1 := by
        have := congrArg Subtype.val hkey.symm
        rw [Subgroup.coe_one, huH_val] at this
        exact this
      exact absurd (calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
        _ = 1 := by rw [h1']; group) hz1
    · rw [h1, zpow_one] at hkey
      have h2 : x * z * x⁻¹ = z := by
        have := congrArg Subtype.val hkey
        rw [hzH_val, huH_val] at this
        exact this.symm
      exact mem_Hz_iff.mpr (calc x * z = (x * z * x⁻¹) * x := by group
        _ = z * x := by rw [h2])
  obtain ⟨S, hS⟩ := CFSG.EvenSmallLie.OmegaEight.Child8.exists_sylow_eq_of_normalizer_le
    (p := 2) hP (fun Q _ hle hle' => le_antisymm hle' hle) hN
  exact ⟨S, hS⟩

end CFSG.GF2Type.Aschbacher1976Full.LeafSemidihedral

namespace CFSG.GF2Type.Aschbacher1976Full

open CFSG.GF2Type.Aschbacher1976Full.LeafSemidihedral


theorem leafSemidihedral_holds : Asc76LeafSemidihedral := by
  intro G _ _ z hS n hn hH he
  obtain ⟨hsimp, hnab, hz, -⟩ := hS
  obtain ⟨e⟩ := he
  have e' : ↥(Hz z) ≃* CFSG.Open.SemidihedralGroup n :=
    (MulEquiv.subgroupCongr hH).trans e
  have hcard : Nat.card (Subgroup.centralizer ({z} : Set G)) = 2 ^ n :=
    (Nat.card_congr e'.toEquiv).trans (CFSG.Semidihedral.card n (by omega))
  obtain ⟨S, hSH⟩ := exists_sylow_of_equiv hz hn e'
  have eS : (S : Subgroup G) ≃* CFSG.Open.SemidihedralGroup n :=
    (MulEquiv.subgroupCongr hSH).trans e'
  rcases CFSG.Milestones.lr_semidihedral_simple_recognition_1 G hnab ⟨S, n, hn, ⟨eS⟩⟩ with
    ⟨p, f, hp, hp2, hf, -, hL⟩ | ⟨p, f, hp, hp2, hf, -, hU⟩ | hM
  · have hval := (CFSG.Semidihedral.Principal.degree_three_model_characteristic_valuation_regularity
      .PSL (Or.inl rfl) p f hp (hp.odd_of_ne_two hp2) hf hL).2.2.1 z hz
    rw [hcard] at hval
    have hndvd : ¬ p ∣ 2 ^ n := fun hd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
    rw [padicValNat.eq_zero_of_not_dvd hndvd] at hval
    omega
  · have hval := (CFSG.Semidihedral.Principal.degree_three_model_characteristic_valuation_regularity
      .PSU (Or.inr rfl) p f hp (hp.odd_of_ne_two hp2) hf hU).2.2.1 z hz
    rw [hcard] at hval
    have hndvd : ¬ p ∣ 2 ^ n := fun hd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
    rw [padicValNat.eq_zero_of_not_dvd hndvd] at hval
    omega
  · have hc : Nat.card (Subgroup.centralizer ({z} : Set G)) = 48 :=
      (CFSG.Semidihedral.ProperSubgroupRegularity.stated_m11_involution_centralizer_card_and_core
        G hM z hz).1
    rw [hcard] at hc
    have h3 : 3 ∣ 2 ^ n := ⟨16, by omega⟩
    have h32 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32

end CFSG.GF2Type.Aschbacher1976Full

end
