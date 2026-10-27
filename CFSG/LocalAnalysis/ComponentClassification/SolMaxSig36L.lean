module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36K

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

variable {M : Subgroup X} {m : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)}

theorem false_of_two_components (hρ : IsPermAction θ ρ) [Finite X] (hm : 11 ≤ m)
    {H : Subgroup X} (hHN : H ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ H, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g)) {e₀ : X}
    (he₀H : e₀ ∈ H) (he₀2 : e₀ * e₀ = 1) (he₀4 : (ρ ⟨e₀, hHN he₀H⟩).support.card = 4)
    (hOH : (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map
      (centralizer ({e₀} : Set X)).subtype ≤ H)
    {N N' : Subgroup X} (hNC : N ≤ centralizer ({e₀} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({e₀} : Set X))))
    (hN'C : N' ≤ centralizer ({e₀} : Set X))
    (hN'pc : IsPComponent 2 (N'.subgroupOf (centralizer ({e₀} : Set X)))) (hne : N ≠ N')
    (hNH : N ≤ H) (hN'H : N' ≤ H) {r r' : ℕ} (hr : m - 6 ≤ r) (hr' : m - 6 ≤ r')
    (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r))
    (θN' : ↥N' ⧸ pPrimeCore 2 ↥N' ≃* alternatingGroup (Fin r')) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he₀N : e₀ ∈ normalizer (M : Set X) := hHN he₀H
  have hNN : N ≤ normalizer (M : Set X) := hNH.trans hHN
  have hN'N : N' ≤ normalizer (M : Set X) := hN'H.trans hHN
  have hρO : ∀ (o : X) (ho : o ∈ (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map
      (centralizer ({e₀} : Set X)).subtype), ρ ⟨o, hHN (hOH ho)⟩ = 1 := fun o ho =>
    rho_eq_one_of_mem_oddCore hρ (by omega) he₀N he₀2 he₀4 (hOH.trans hHN) ho
  set A := (N.subgroupOf (normalizer (M : Set X))).map ρ with hAdef
  set A' := (N'.subgroupOf (normalizer (M : Set X))).map ρ with hA'def
  set B := ((coreNOf N).subgroupOf (normalizer (M : Set X))).map ρ with hBdef
  have hN'K : N' ≤ UnbalancedLayer.coreActionKernel N :=
    GSThmB.B5a.le_coreActionKernel_of_ne hNC hN'C hNpc hN'pc hne
  have hcomm : ∀ a ∈ A, ∀ a' ∈ A', a * a' = a' * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    obtain ⟨-, hK⟩ := UnbalancedLayer.mem_coreActionKernel.mp (hN'K hx')
    obtain ⟨c, hc, hceq⟩ := hK x hx
    have hcO : (x : X)⁻¹ * (x' : X)⁻¹ * x * x' ∈
        (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map (centralizer ({e₀} : Set X)).subtype :=
      pPrimeCore_le_of_isPComponent hNC hNpc ⟨c, hc, hceq⟩
    have h1 := hρO _ hcO
    have h2 : (⟨(x : X)⁻¹ * (x' : X)⁻¹ * x * x', hHN (hOH hcO)⟩ : ↥(normalizer (M : Set X))) =
        x⁻¹ * x'⁻¹ * x * x' := rfl
    rw [h2, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc ρ x * ρ x' = ρ x' * ρ x * ((ρ x)⁻¹ * (ρ x')⁻¹ * ρ x * ρ x') := by group
      _ = ρ x' * ρ x := by rw [h1, mul_one]
  set K₀ := (fixAlt (ρ ⟨e₀, he₀N⟩)).map (alternatingGroup (Fin m)).subtype with hK₀def
  have hNperf : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent hNC hNpc
  have hN'perf : ⁅N', N'⁆ = N' := UnbalancedCorr.commutator_eq_of_isPComponent hN'C hN'pc
  have hAK₀ : A ⊔ A' ≤ K₀ := by
    refine sup_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      have hxo : (x : X) ∈ oddGen N := by rw [oddGen_eq_of_perfect hNperf]; exact hx
      exact rho_mem_fixAlt_of_mem_oddGen he₀N he₀2 he₀4.le hNN hNC hxo x.2
    · rintro _ ⟨x, hx, rfl⟩
      have hxo : (x : X) ∈ oddGen N' := by rw [oddGen_eq_of_perfect hN'perf]; exact hx
      exact rho_mem_fixAlt_of_mem_oddGen he₀N he₀2 he₀4.le hN'N hN'C hxo x.2
  have hτc : (ρ ⟨e₀, he₀N⟩).support.card ≤ m := by
    have := Finset.card_le_univ (ρ ⟨e₀, he₀N⟩).support
    rwa [Fintype.card_fin] at this
  have hK₀card : Nat.card K₀ = (m - 4).factorial / 2 := by
    rw [hK₀def, card_map_of_injective (alternatingGroup (Fin m)).subtype_injective,
      card_fixAlt (by omega), he₀4]
  have hr4 : 4 ≤ r := by omega
  have hAB : A ⊓ A' ≤ B := by
    rintro _ ⟨⟨x, hx, rfl⟩, ha'⟩
    refine ⟨x, ?_, rfl⟩
    show (x : X) ∈ coreNOf N
    have hxN : (x : X) ∈ N := hx
    have hcent : θN ((⟨x, hxN⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) ∈
        center (alternatingGroup (Fin r)) := by
      rw [mem_center_iff]
      intro q
      obtain ⟨q', rfl⟩ := θN.surjective q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q'
      have hyN : (y : X) ∈ normalizer (M : Set X) := hNN y.2
      have hρc : ρ ⟨y, hyN⟩ * ρ x = ρ x * ρ ⟨y, hyN⟩ :=
        hcomm _ ⟨⟨y, hyN⟩, y.2, rfl⟩ _ ha'
      have hz : (y : X) * x * (y : X)⁻¹ * (x : X)⁻¹ ∈ coreNOf N := by
        have hzN : (y : X) * x * (y : X)⁻¹ * (x : X)⁻¹ ∈ N :=
          mul_mem (mul_mem (mul_mem y.2 hxN) (inv_mem y.2)) (inv_mem hxN)
        refine mem_coreNOf_of_rho_eq_one hρ hHN hker hNH hzN ?_
        have h1 : (⟨(y : X) * x * (y : X)⁻¹ * (x : X)⁻¹, hHN (hNH hzN)⟩ :
            ↥(normalizer (M : Set X))) = ⟨y, hyN⟩ * x * (⟨y, hyN⟩)⁻¹ * x⁻¹ := rfl
        rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv, hρc]
        group
      obtain ⟨z, hz', hzeq⟩ := hz
      have h2 : y * ⟨x, hxN⟩ * y⁻¹ * (⟨x, hxN⟩ : ↥N)⁻¹ ∈ pPrimeCore 2 ↥N := by
        have h3 : y * ⟨x, hxN⟩ * y⁻¹ * (⟨x, hxN⟩ : ↥N)⁻¹ = z := Subtype.ext hzeq.symm
        rw [h3]
        exact hz'
      rw [← QuotientGroup.eq_one_iff] at h2
      have h4 := congrArg θN h2
      rw [map_one, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, map_mul, map_mul, map_mul, map_inv,
        map_inv] at h4
      calc θN (y : ↥N ⧸ pPrimeCore 2 ↥N) * θN ((⟨x, hxN⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) =
          θN (y : ↥N ⧸ pPrimeCore 2 ↥N) * θN ((⟨x, hxN⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) *
            (θN (y : ↥N ⧸ pPrimeCore 2 ↥N))⁻¹ *
            (θN ((⟨x, hxN⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N))⁻¹ *
            θN ((⟨x, hxN⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) * θN (y : ↥N ⧸ pPrimeCore 2 ↥N) := by
            group
        _ = θN ((⟨x, hxN⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) * θN (y : ↥N ⧸ pPrimeCore 2 ↥N) := by
            rw [h4, one_mul]
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega), mem_bot,
      ← map_one θN] at hcent
    have h5 := θN.injective hcent
    rw [QuotientGroup.eq_one_iff] at h5
    exact ⟨_, h5, rfl⟩
  have hcardN := card_eq_of_alt (by omega) θN
  have hcardN' := card_eq_of_alt (by omega) θN'
  have hNs : Nat.card (N.subgroupOf (normalizer (M : Set X))) = Nat.card N :=
    Nat.card_congr (subgroupOfEquivOfLe hNN).toEquiv
  have hN's : Nat.card (N'.subgroupOf (normalizer (M : Set X))) = Nat.card N' :=
    Nat.card_congr (subgroupOfEquivOfLe hN'N).toEquiv
  have hONs : Nat.card ((coreNOf N).subgroupOf (normalizer (M : Set X))) =
      Nat.card (coreNOf N) :=
    Nat.card_congr (subgroupOfEquivOfLe ((map_subtype_le _).trans hNN)).toEquiv
  have hk₁ := card_eq_card_map_mul_card_inf_ker' ρ (N.subgroupOf (normalizer (M : Set X)))
  have hk₂ := card_eq_card_map_mul_card_inf_ker' ρ
    ((coreNOf N).subgroupOf (normalizer (M : Set X)))
  have hk₃ := card_eq_card_map_mul_card_inf_ker' ρ (N'.subgroupOf (normalizer (M : Set X)))
  have hinf : N.subgroupOf (normalizer (M : Set X)) ⊓ ρ.ker =
      (coreNOf N).subgroupOf (normalizer (M : Set X)) ⊓ ρ.ker := by
    apply le_antisymm
    · rintro z ⟨hz, hzk⟩
      refine ⟨?_, hzk⟩
      exact mem_coreNOf_of_rho_eq_one hρ hHN hker hNH hz hzk
    · rintro z ⟨hz, hzk⟩
      exact ⟨(map_subtype_le (pPrimeCore 2 ↥N) : coreNOf N ≤ N) hz, hzk⟩
  have hk₃le : Nat.card (N'.subgroupOf (normalizer (M : Set X)) ⊓ ρ.ker : Subgroup _) ≤
      Nat.card (coreNOf N') := by
    have h1 : N'.subgroupOf (normalizer (M : Set X)) ⊓ ρ.ker ≤
        (coreNOf N').subgroupOf (normalizer (M : Set X)) := by
      rintro z ⟨hz, hzk⟩
      exact mem_coreNOf_of_rho_eq_one hρ hHN hker hN'H hz hzk
    rw [← Nat.card_congr (subgroupOfEquivOfLe ((map_subtype_le _).trans hN'N)).toEquiv]
    exact Subgroup.card_le_of_le h1
  rw [← hAdef, hNs, hinf] at hk₁
  rw [← hBdef, hONs] at hk₂
  rw [← hA'def, hN's] at hk₃
  set k₁ := Nat.card ((coreNOf N).subgroupOf (normalizer (M : Set X)) ⊓ ρ.ker : Subgroup _)
    with hk₁def
  have hk₁pos : 0 < k₁ := Nat.card_pos
  have hONpos : 0 < Nat.card (coreNOf N') := Nat.card_pos
  have hA : Nat.card A = (r.factorial / 2) * Nat.card B := by
    have h1 : Nat.card A * k₁ = (r.factorial / 2) * Nat.card B * k₁ := by
      rw [← hk₁, hcardN, hk₂, mul_assoc]
    exact Nat.eq_of_mul_eq_mul_right hk₁pos h1
  have hA' : r'.factorial / 2 ≤ Nat.card A' := by
    have h1 : (r'.factorial / 2) * Nat.card (coreNOf N') ≤
        Nat.card A' * Nat.card (coreNOf N') := by
      rw [← hcardN', hk₃]
      exact Nat.mul_le_mul_left _ hk₃le
    exact Nat.le_of_mul_le_mul_right h1 hONpos
  have hAnorm : A ≤ normalizer (A' : Set (Perm (Fin m))) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have h2 : a * b * a⁻¹ = b := by rw [hcomm a ha b hb]; group
      rw [h2]
      exact hb
    · intro hb
      have h1 := hcomm a ha _ hb
      have h2 : a * b * a⁻¹ = b := by
        calc a * b * a⁻¹ = a⁻¹ * (a * (a * b * a⁻¹)) := by group
          _ = a⁻¹ * ((a * b * a⁻¹) * a) := by rw [h1]
          _ = b := by group
      rw [← h2]
      exact hb
  have hsup := Sol78.card_sup_mul_card_inf' hAnorm
  have hsupK : Nat.card (A ⊔ A' : Subgroup _) ≤ (m - 4).factorial / 2 := by
    rw [← hK₀card]
    exact Subgroup.card_le_of_le hAK₀
  have hinfB : Nat.card (A ⊓ A' : Subgroup _) ≤ Nat.card B := Subgroup.card_le_of_le hAB
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hkey : (r.factorial / 2) * (r'.factorial / 2) ≤ (m - 4).factorial / 2 := by
    have h1 : (r.factorial / 2) * Nat.card A' * Nat.card B ≤
        ((m - 4).factorial / 2) * Nat.card B := by
      calc (r.factorial / 2) * Nat.card A' * Nat.card B = Nat.card A * Nat.card A' := by
            rw [hA]; ring
        _ = Nat.card (A ⊔ A' : Subgroup _) * Nat.card (A ⊓ A' : Subgroup _) := hsup.symm
        _ ≤ ((m - 4).factorial / 2) * Nat.card B := Nat.mul_le_mul hsupK hinfB
    have h2 := Nat.le_of_mul_le_mul_right h1 hBpos
    exact (Nat.mul_le_mul_left _ hA').trans h2
  have hlt := sq_card_alt_gt (m - 6) (by omega)
  rw [show m - 6 + 2 = m - 4 by omega] at hlt
  have hfr : (m - 6).factorial / 2 ≤ r.factorial / 2 :=
    Nat.div_le_div_right (Nat.factorial_le hr)
  have hfr' : (m - 6).factorial / 2 ≤ r'.factorial / 2 :=
    Nat.div_le_div_right (Nat.factorial_le hr')
  have := Nat.mul_le_mul hfr hfr'
  omega

end CFSG.ComponentClassification.SolMax
