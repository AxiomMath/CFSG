module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNDouble

public section

namespace CFSG.ComponentClassification.GrSLit.HeSN

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X] [Finite X]

theorem exists_outer_involution_mem
    {T₀ : Subgroup (Equiv.Perm (Fin 8330))}
    (hT₀ : T₀ ≤ heAutGroup) (hT₂ : IsPGroup 2 T₀) (h2048 : Nat.card T₀ = 2048) :
    ∃ σ ∈ T₀, σ ∉ heP ∧ σ * σ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : T₀.relIndex heAutGroup = 3935925 := by
    have h1 := Subgroup.card_mul_index (T₀.subgroupOf heAutGroup)
    rw [Nat.card_congr (subgroupOfEquivOfLe hT₀).toEquiv, h2048, card_heAutGroup] at h1
    show (T₀.subgroupOf heAutGroup).index = 3935925
    omega
  have hsyl : IsSylowTwoIn T₀ heAutGroup :=
    GrS4.isSylowTwoIn_of_not_dvd hT₀ hT₂ (by rw [hidx]; decide)
  obtain ⟨c, hcR, hc⟩ :=
    hsyl.exists_conj_le (zpowers_le.mpr heAutU_mem_heAutGroup) (isPGroup_zpowers orderOf_heAutU)
  refine ⟨c * heAutU * c⁻¹, hc _ (mem_zpowers _), fun hP => ?_, ?_⟩
  · have h1 := (mem_normalizer_iff.mp (heAutGroup_le_normalizer (inv_mem hcR)) _).mp hP
    rw [show c⁻¹ * (c * heAutU * c⁻¹) * c⁻¹⁻¹ = heAutU by group] at h1
    exact heAutU_not_mem h1
  · rw [show c * heAutU * c⁻¹ * (c * heAutU * c⁻¹) = c * (heAutU * heAutU) * c⁻¹ by group,
      ← sq, heAutU_sq]
    group

theorem exists_outer_sq
    {K : Subgroup X}
    (e : K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He) {S : Subgroup X}
    (hSN : S ≤ normalizer (K : Set X)) (hS2 : IsPGroup 2 S) (h1024 : Nat.card ↥(S ⊓ K) = 1024)
    {s : X} (hsS : s ∈ S) (hsK : s ∉ K ⊔ coreActionKernel K) :
    ∃ y ∈ S, y ∉ K ⊔ coreActionKernel K ∧ y * y ∈ coreActionKernel K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 ↥(S ⊓ K) := hS2.to_le inf_le_left
  have hI2 : IsPGroup 2 ↥(imN e S) := isPGroup_imN hSN hS2
  have hIR : imN e S ≤ heAutGroup := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := (mem_imN hSN).mp hy
    exact heN_mem (hSN hx)
  have hle : imL e (S ⊓ K) ≤ imN e S ⊓ heP := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := (mem_imL inf_le_right).mp hy
    exact mem_inf.mpr ⟨(mem_imN hSN).mpr ⟨t, (mem_inf.mp ht).1, heN_eq_heL (mem_inf.mp ht).2⟩,
      heL_mem_heP (mem_inf.mp ht).2⟩
  have heq : imL e (S ⊓ K) = imN e S ⊓ heP := by
    refine eq_of_le_of_card_ge hle ?_
    rw [card_imL inf_le_right h2, h1024]
    exact card_le_of_le_heP inf_le_right (hI2.to_le inf_le_left)
  have hcardP : Nat.card ↥(imN e S ⊓ heP) = 1024 := by
    rw [← heq, card_imL inf_le_right h2, h1024]
  have hsI : heN e s ∈ imN e S := (mem_imN hSN).mpr ⟨s, hsS, rfl⟩
  have hsP : heN e s ∉ heP := fun h' => hsK ((heN_mem_heP_iff (hSN hsS)).mp h')
  obtain ⟨k, hk⟩ := hI2.exists_card_eq
  have hk10 : 1024 ∣ 2 ^ k := hk ▸ hcardP ▸ card_dvd_of_le inf_le_left
  have hne : imN e S ⊓ heP ≠ imN e S := fun h' => hsP (h' ▸ hsI |> fun h'' => (mem_inf.mp h'').2)
  have hk11 : 11 ≤ k := by
    have h1 : 10 ≤ k := by
      by_contra hlt
      push Not at hlt
      have h3 : 2 ^ k < 2 ^ 10 := Nat.pow_lt_pow_right (by norm_num) hlt
      have h4 := Nat.le_of_dvd (by positivity) hk10
      omega
    rcases h1.lt_or_eq with h1 | h1
    · omega
    · exfalso
      apply hne
      refine eq_of_le_of_card_ge inf_le_left ?_
      rw [hk, hcardP, ← h1]
      norm_num
  have hkle : k ≤ 11 := by
    have hdvd : 2 ^ k ∣ 8060774400 := by
      rw [← hk, ← card_heAutGroup]
      exact card_dvd_of_le hIR
    by_contra h'
    push Not at h'
    have h12 : 2 ^ 12 ∣ 8060774400 := (pow_dvd_pow 2 h').trans hdvd
    norm_num at h12
  have h2048 : Nat.card ↥(imN e S) = 2048 := by
    rw [hk, show k = 11 by omega]
    norm_num
  obtain ⟨σ, hσI, hσP, hσσ⟩ := exists_outer_involution_mem hIR hI2 h2048
  obtain ⟨y, hyS, rfl⟩ := (mem_imN hSN).mp hσI
  refine ⟨y, hyS, fun h' => hσP ((heN_mem_heP_iff (hSN hyS)).mpr h'), ?_⟩
  rw [← heN_eq_one_iff (e := e) (mul_mem (hSN hyS) (hSN hyS)), heN_mul (hSN hyS) (hSN hyS)]
  exact hσσ

omit [Finite X] in
theorem commute_doubleHom_of_sq {Y : Subgroup X} {c : X}
    (hY : ∀ y ∈ Y, ∀ y' ∈ Y, Commute y (c⁻¹ * y' * c)) (y : ↥Y) (hcy : Commute (c * c) y) :
    Commute c (doubleHom hY y) := by
  rw [doubleHom_apply]
  have h1 := (hY y y.2 y y.2).eq
  have h2 : c * y * c⁻¹ = c⁻¹ * y * c := by
    calc c * y * c⁻¹ = c⁻¹ * (c * c * y) * c⁻¹ := by group
      _ = c⁻¹ * (y * (c * c)) * c⁻¹ := by rw [hcy.eq]
      _ = c⁻¹ * y * c := by group
  show c * ((y : X) * (c⁻¹ * y * c)) = (y : X) * (c⁻¹ * y * c) * c
  calc c * ((y : X) * (c⁻¹ * y * c)) = (c * y * c⁻¹) * y * c := by group
    _ = (c⁻¹ * y * c) * y * c := by rw [h2]
    _ = (y : X) * (c⁻¹ * y * c) * c := by rw [← h1]

end CFSG.ComponentClassification.GrSLit.HeSN
