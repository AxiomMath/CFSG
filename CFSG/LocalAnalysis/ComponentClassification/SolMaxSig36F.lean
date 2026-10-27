module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36E
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36A

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]
variable {M : Subgroup X} {r : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)}

theorem IsPermAction.exists_conj_of_four (hρ : IsPermAction θ ρ) [Finite X] (hr : 6 ≤ r)
    {H : Subgroup X} (hMH : M ≤ H)
    (hker : ∀ g ∈ H, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g)) {x y : X}
    (hxN : x ∈ normalizer (M : Set X)) (hyN : y ∈ normalizer (M : Set X)) (hxH : x ∈ H)
    (hyH : y ∈ H) (hx2 : x * x = 1) (hy2 : y * y = 1) (hx4 : (ρ ⟨x, hxN⟩).support.card = 4)
    (hy4 : (ρ ⟨y, hyN⟩).support.card = 4) : ∃ c ∈ H, c * x * c⁻¹ = y := by
  classical
  have hsq : ∀ g : ↥(normalizer (M : Set X)), (g : X) * g = 1 → ρ g * ρ g = 1 := by
    intro g hg
    rw [← map_mul, show g * g = 1 from Subtype.ext hg, map_one]
  obtain ⟨π, hπ⟩ := exists_alt_conj_of_four hr (hsq _ hx2) (hsq _ hy2) hx4 hy4
  obtain ⟨q, hq⟩ := θ.surjective π
  obtain ⟨h₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hρh₀ := hρ.apply_of_mem (by omega) h₀
  rw [hq] at hρh₀
  have hh₀N : (h₀ : X) ∈ normalizer (M : Set X) := le_normalizer h₀.2
  have hh₀H : (h₀ : X) ∈ H := hMH h₀.2
  set x' := (h₀ : X) * x * (h₀ : X)⁻¹ with hx'def
  have hx'N : x' ∈ normalizer (M : Set X) := mul_mem (mul_mem hh₀N hxN) (inv_mem hh₀N)
  have hx'H : x' ∈ H := mul_mem (mul_mem hh₀H hxH) (inv_mem hh₀H)
  have hx'2 : x' * x' = 1 := by
    rw [hx'def]
    calc (h₀ : X) * x * (h₀ : X)⁻¹ * ((h₀ : X) * x * (h₀ : X)⁻¹) =
        (h₀ : X) * (x * x) * (h₀ : X)⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hρx' : ρ ⟨x', hx'N⟩ = ρ ⟨y, hyN⟩ := by
    have h1 : (⟨x', hx'N⟩ : ↥(normalizer (M : Set X))) =
        ⟨h₀, hh₀N⟩ * ⟨x, hxN⟩ * (⟨h₀, hh₀N⟩ : ↥(normalizer (M : Set X)))⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv, hρh₀, ← hπ]
  have hprodN : x' * y ∈ normalizer (M : Set X) := mul_mem hx'N hyN
  have hρprod : ρ ⟨x' * y, hprodN⟩ = 1 := by
    have h1 : (⟨x' * y, hprodN⟩ : ↥(normalizer (M : Set X))) = ⟨x', hx'N⟩ * ⟨y, hyN⟩ := rfl
    rw [h1, map_mul, hρx']
    exact hsq _ hy2
  have hodd := hker _ (mul_mem hx'H hyH) (hρ.mem_coreActionKernel hprodN hρprod)
  obtain ⟨k, hk⟩ := exists_conj_of_odd_mul hx'2 hy2 hodd
  refine ⟨(x' * y) ^ k * (h₀ : X), mul_mem (pow_mem (mul_mem hx'H hyH) k) hh₀H, ?_⟩
  calc ((x' * y) ^ k * (h₀ : X)) * x * ((x' * y) ^ k * (h₀ : X))⁻¹ =
      (x' * y) ^ k * ((h₀ : X) * x * (h₀ : X)⁻¹) * ((x' * y) ^ k)⁻¹ := by group
    _ = y := hk

theorem IsPermAction.mem_of_conj_mem (hρ : IsPermAction θ ρ) [Finite X] (hr : 9 ≤ r)
    {H : Subgroup X} (hMH : M ≤ H) (hHN : H ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ H, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g))
    (hA : ∀ (e : X) (he : e ∈ H), e * e = 1 → (ρ ⟨e, hHN he⟩).support.card = 4 →
      centralizer ({e} : Set X) ≤ H)
    {t : X} (ht2 : t * t = 1) (hCt : centralizer ({t} : Set X) ≤ H) {g : X}
    (hg : g * t * g⁻¹ ∈ H) : g ∈ H := by
  classical
  set s := g * t * g⁻¹ with hsdef
  have hs2 : s * s = 1 := by
    rw [hsdef]
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  obtain ⟨e, heM, heo, he2, he4⟩ := hρ.exists_four_involution hr (hHN hg) hs2
  have heH : e ∈ H := hMH heM
  have he'o : g⁻¹ * e * g ∈ oddGen (centralizer ({t} : Set X)) := by
    have h1 := conj_mem_oddGen_centralizer (g := g⁻¹) heo
    rw [inv_inv] at h1
    have h2 : g⁻¹ * s * g = t := by rw [hsdef]; group
    rwa [h2] at h1
  have he'H : g⁻¹ * e * g ∈ H := hCt (oddGen_le _ he'o)
  have he'N : g⁻¹ * e * g ∈ normalizer (M : Set X) := hHN he'H
  have he'2 : g⁻¹ * e * g * (g⁻¹ * e * g) = 1 := by
    calc g⁻¹ * e * g * (g⁻¹ * e * g) = g⁻¹ * (e * e) * g := by group
      _ = 1 := by rw [he2]; group
  have he'A : ρ ⟨g⁻¹ * e * g, he'N⟩ ∈ alternatingGroup (Fin r) :=
    mem_alternatingGroup_of_mem_oddGen (hCt.trans hHN) he'o he'N
  have hσ2 : ρ ⟨g⁻¹ * e * g, he'N⟩ * ρ ⟨g⁻¹ * e * g, he'N⟩ = 1 := by
    rw [← map_mul, show (⟨g⁻¹ * e * g, he'N⟩ : ↥(normalizer (M : Set X))) *
      ⟨g⁻¹ * e * g, he'N⟩ = 1 from Subtype.ext he'2, map_one]
  have hCe : centralizer ({e} : Set X) ≤ H := hA e heH he2 he4
  have h4 : (ρ ⟨g⁻¹ * e * g, he'N⟩).support.card = 4 := by
    have hdvd := four_dvd_card_support_of_mem_alternating hσ2 he'A
    by_cases h8 : 8 ≤ (ρ ⟨g⁻¹ * e * g, he'N⟩).support.card
    · exfalso
      have h1 := hρ.mem_oddGen_of_eight (by omega) hMH hker he'N he'H he'2 he'A h8
      have h2 := conj_mem_oddGen_centralizer (g := g) h1
      have h3 : g * (g⁻¹ * e * g) * g⁻¹ = e := by group
      rw [h3] at h2
      exact not_mem_oddGen_of_four (hHN heH) he2 he4 (hCe.trans hHN) h2
    · rcases (show (ρ ⟨g⁻¹ * e * g, he'N⟩).support.card = 0 ∨
          (ρ ⟨g⁻¹ * e * g, he'N⟩).support.card = 4 by omega) with h0 | h4
      · exfalso
        rw [Finset.card_eq_zero, Perm.support_eq_empty_iff] at h0
        have hodd := hker _ he'H (hρ.mem_coreActionKernel he'N h0)
        have h1 : g⁻¹ * e * g = 1 := by
          have h2 : orderOf (g⁻¹ * e * g) ∣ 2 :=
            orderOf_dvd_of_pow_eq_one (by rw [sq]; exact he'2)
          have h3 : orderOf (g⁻¹ * e * g) = 1 := by
            rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
            · exact h
            · rw [h] at hodd
              exact absurd hodd (by decide)
          exact orderOf_eq_one_iff.mp h3
        have he1 : e = 1 := by
          calc e = g * (g⁻¹ * e * g) * g⁻¹ := by group
            _ = 1 := by rw [h1]; group
        have : (ρ ⟨e, le_normalizer heM⟩).support.card = 0 := by
          rw [show (⟨e, le_normalizer heM⟩ : ↥(normalizer (M : Set X))) = 1 from
            Subtype.ext he1, map_one, Perm.support_one, Finset.card_empty]
        omega
      · exact h4
  obtain ⟨c, hcH, hc⟩ := hρ.exists_conj_of_four (by omega) hMH hker (hHN heH) he'N heH he'H he2
    he'2 he4 h4
  have hgc : g * c ∈ centralizer ({e} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    calc g * c * e = g * (c * e * c⁻¹) * c := by group
      _ = g * (g⁻¹ * e * g) * c := by rw [hc]
      _ = e * (g * c) := by group
  have h1 := mul_mem (hCe hgc) (inv_mem hcH)
  rwa [mul_inv_cancel_right] at h1

theorem exists_sylow_le_of_conj_mem [Finite X] {H : Subgroup X} {t : X} (htH : t ∈ H)
    (ht2 : t * t = 1) (hfus : ∀ g : X, g * t * g⁻¹ ∈ H → g ∈ H) :
    ∃ S : Sylow 2 X, (S : Subgroup X) ≤ H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥H) := inferInstance
  set S₀ : Subgroup X := (P : Subgroup ↥H).map H.subtype with hS₀
  have hS₀H : S₀ ≤ H := map_subtype_le _
  have hS₀2 : IsPGroup 2 S₀ := P.isPGroup'.map H.subtype
  obtain ⟨T, hT⟩ := hS₀2.exists_le_sylow
  refine ⟨T, ?_⟩
  obtain ⟨c, hc⟩ := exists_conj_mem_of_card_eq P.card_eq_multiplicity
    (isPGroup_zpowers_of_mul_self (show (⟨t, htH⟩ : ↥H) * ⟨t, htH⟩ = 1 from Subtype.ext ht2))
  have huS : (c : X) * t * (c : X)⁻¹ ∈ S₀ := ⟨_, hc, rfl⟩
  by_contra hTH
  have hlt : S₀.subgroupOf (T : Subgroup X) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hTH
    intro z hz
    have hz' : (⟨z, hz⟩ : ↥(T : Subgroup X)) ∈ S₀.subgroupOf (T : Subgroup X) := by
      rw [h]
      exact mem_top _
    exact hS₀H hz'
  have : Group.IsNilpotent ↥(T : Subgroup X) := T.isPGroup'.isNilpotent
  obtain ⟨y, hyN, hyS⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hyu : (y : X) * ((c : X) * t * (c : X)⁻¹) * (y : X)⁻¹ ∈ S₀ := by
    have h1 := (mem_normalizer_iff.mp hyN ⟨_, hT huS⟩).mp huS
    exact h1
  have hyc : (y : X) * c ∈ H := by
    refine hfus _ ?_
    have h1 : (y : X) * c * t * ((y : X) * c)⁻¹ =
        (y : X) * ((c : X) * t * (c : X)⁻¹) * (y : X)⁻¹ := by group
    rw [h1]
    exact hS₀H hyu
  have hyH : (y : X) ∈ H := by
    have h1 := mul_mem hyc (inv_mem c.2)
    rwa [mul_inv_cancel_right] at h1
  have hQ : IsPGroup 2 ↥((P : Subgroup ↥H) ⊔ zpowers (⟨y, hyH⟩ : ↥H)) := by
    have hTH' : IsPGroup 2 ↥((T : Subgroup X).subgroupOf H) :=
      T.isPGroup'.comap_of_injective H.subtype H.subtype_injective
    refine hTH'.to_le (sup_le ?_ ?_)
    · intro z hz
      exact hT ⟨z, hz, rfl⟩
    · rw [zpowers_le]
      exact y.2
  have hPQ := P.is_maximal' hQ le_sup_left
  have hyP : (⟨y, hyH⟩ : ↥H) ∈ (P : Subgroup ↥H) := by
    rw [← hPQ]
    exact mem_sup_right (mem_zpowers _)
  exact hyS ⟨_, hyP, rfl⟩

end CFSG.ComponentClassification.SolMax
