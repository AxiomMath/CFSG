module

public import CFSG.CGT.PushingUpLit.SolK.GenFour
public import CFSG.CGT.PushingUpLit.SolK.Local
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7SuzTau
public import CFSG.GroupTheory.KleinFourAutomorphism

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG.GH74

section Perm3

variable {Ω : Type*} [Finite Ω]

theorem perm3_sq_of_two_power (h : Nat.card Ω = 3) (τ : Equiv.Perm Ω)
    (hτ : ∃ k : ℕ, τ ^ (2 ^ k) = 1) : τ ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := hτ
  have h6 : orderOf τ ∣ 6 := by
    have := orderOf_dvd_natCard τ
    rw [Nat.card_perm, h] at this
    exact this
  have hd2 : orderOf τ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd2
  have hi1 : i ≤ 1 := by
    by_contra hcon
    have h22 : 2 ^ 2 ∣ 2 ^ i := pow_dvd_pow 2 (by omega)
    rw [← hio] at h22
    have := dvd_trans h22 h6
    omega
  have : orderOf τ ∣ 2 := by
    rw [hio]
    exact (pow_dvd_pow 2 hi1).trans (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.1 this

theorem perm3_involutions (h : Nat.card Ω = 3) (τ₁ τ₂ : Equiv.Perm Ω) (h1 : τ₁ ^ 2 = 1)
    (h2 : τ₂ ^ 2 = 1) (h12 : (τ₁ * τ₂) ^ 2 = 1) : τ₁ = 1 ∨ τ₂ = 1 ∨ τ₁ = τ₂ := by
  have key : ∀ σ₁ σ₂ : Equiv.Perm (Fin 3), σ₁ ^ 2 = 1 → σ₂ ^ 2 = 1 → (σ₁ * σ₂) ^ 2 = 1 →
      σ₁ = 1 ∨ σ₂ = 1 ∨ σ₁ = σ₂ := by decide
  let e : Ω ≃ Fin 3 := (Finite.equivFin Ω).trans (finCongr h)
  let E : Equiv.Perm Ω ≃* Equiv.Perm (Fin 3) := e.permCongrHom
  have := key (E τ₁) (E τ₂) (by rw [← map_pow, h1, map_one]) (by rw [← map_pow, h2, map_one])
    (by rw [← map_mul, ← map_pow, h12, map_one])
  rcases this with h | h | h
  · exact Or.inl (E.injective (h.trans (map_one E).symm))
  · exact Or.inr (Or.inl (E.injective (h.trans (map_one E).symm)))
  · exact Or.inr (Or.inr (E.injective h))

end Perm3


section Suzuki

variable {G : Type} [Group G] [Finite G]

theorem sectionalTwoRankLE_four_of_card_four {S : Subgroup G} (h4 : Nat.card S = 4)
    (hsq : ∀ s ∈ S, s * s = 1) : SectionalTwoRankLE ↥S 4 := by
  classical
  have hnt : Nontrivial ↥S := Finite.one_lt_card_iff_nontrivial.1 (by rw [h4]; norm_num)
  obtain ⟨b, hb⟩ := exists_ne (1 : ↥S)
  have hb2 : b ^ 2 = 1 := by
    have := hsq b b.2
    refine Subtype.ext ?_
    simpa [pow_two] using this
  have hord : orderOf b = 2 := orderOf_eq_prime hb2 hb
  have hidx : (Subgroup.zpowers b).index = 2 := by
    have h1 := Subgroup.index_mul_card (Subgroup.zpowers b)
    rw [Nat.card_zpowers, hord, h4] at h1
    omega
  exact sectionalTwoRankLE_four_of_cyclic_index (Subgroup.zpowers b) (Or.inr hidx)

theorem sectionalTwoRankLE_four_of_selfCentralizing_four {S W : Subgroup G} (hS : IsPGroup 2 S)
    (hWS : W ≤ S) (hW4 : Nat.card W = 4) (hWsq : ∀ w ∈ W, w * w = 1)
    (hCW : ∀ g ∈ S, g ∈ Subgroup.normalizer (W : Set G) →
      (∀ w ∈ W, g * w * g⁻¹ = w) → g ∈ W) :
    SectionalTwoRankLE ↥S 4 := by
  classical
  have hinv : ∀ x ∈ W, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hWsq x hx)
  have hWab : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w := by
    intro w hw w' hw'
    have h1 : (w * w')⁻¹ = w * w' := hinv _ (W.mul_mem hw hw')
    rw [mul_inv_rev, hinv w hw, hinv w' hw'] at h1
    exact h1.symm
  by_cases hN : ∃ n ∈ S, n ∈ Subgroup.normalizer (W : Set G) ∧ n ∉ W
  ·
    obtain ⟨n, hnS, hnN, hnW⟩ := hN
    have hWnt : Nontrivial ↥W := Finite.one_lt_card_iff_nontrivial.1 (by rw [hW4]; norm_num)
    have hexp : Monoid.exponent ↥W = 2 := by
      refine (Monoid.exponent_eq_prime_iff Nat.prime_two).2 (fun g hg => ?_)
      have hg2 : g ^ 2 = 1 := by
        refine Subtype.ext ?_
        simpa [pow_two] using hWsq g g.2
      exact orderOf_eq_prime hg2 hg
    have : IsKleinFour ↥W := ⟨hW4, hexp⟩
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥(Subgroup.normalizer (W : Set G)) →* Equiv.Perm {x : ↥W // x ≠ 1},
        ∀ (g : ↥(Subgroup.normalizer (W : Set G))) (x : ↥W) (hx : x ≠ 1),
          (((ρ g ⟨x, hx⟩ : {x : ↥W // x ≠ 1}) : ↥W) : G) = (g : G) * (x : G) * (g : G)⁻¹ :=
      ⟨(CFSG.nonidentityAutomorphismAction ↥W).comp W.normalizerMonoidHom, fun g x hx => rfl⟩
    have hcard3 : Nat.card {x : ↥W // x ≠ 1} = 3 := CFSG.kleinFour_nonidentity_card ↥W
    have hsq2 : ∀ g : ↥(Subgroup.normalizer (W : Set G)), (g : G) ∈ S → ρ g ^ 2 = 1 := by
      intro g hg
      obtain ⟨k, hk⟩ := hS ⟨(g : G), hg⟩
      refine perm3_sq_of_two_power hcard3 (ρ g) ⟨k, ?_⟩
      rw [← map_pow]
      have : g ^ (2 ^ k) = 1 := by
        refine Subtype.ext ?_
        simpa using congrArg Subtype.val hk
      rw [this, map_one]
    have hker : ∀ g : ↥(Subgroup.normalizer (W : Set G)), (g : G) ∈ S → ρ g = 1 → (g : G) ∈ W := by
      intro g hg h1
      refine hCW (g : G) hg g.2 (fun w hw => ?_)
      by_cases hw1 : w = 1
      · rw [hw1]
        group
      · have := congrArg (fun f : Equiv.Perm {x : ↥W // x ≠ 1} => (((f ⟨⟨w, hw⟩, fun h => hw1 (congrArg Subtype.val h)⟩ : {x : ↥W // x ≠ 1}) : ↥W) : G)) h1
        simpa [hρ] using this
    have hn1 : ρ ⟨n, hnN⟩ ≠ 1 := fun h => hnW (hker ⟨n, hnN⟩ hnS h)
    obtain ⟨ω, hω⟩ : ∃ ω : {x : ↥W // x ≠ 1}, ρ ⟨n, hnN⟩ ω ≠ ω := by
      by_contra hcon
      push Not at hcon
      exact hn1 (Equiv.ext hcon)
    obtain ⟨u, hu⟩ : ∃ u : G, (((ω : ↥W)) : G) = u := ⟨_, rfl⟩
    have huW : u ∈ W := hu ▸ (ω : ↥W).2
    have hu1 : u ≠ 1 := fun h => ω.2 (Subtype.ext (hu.trans h))
    have hρω : ∀ g : ↥(Subgroup.normalizer (W : Set G)),
        (((ρ g ω : {x : ↥W // x ≠ 1}) : ↥W) : G) = (g : G) * u * (g : G)⁻¹ := by
      intro g
      rw [← hu]
      exact hρ g ω.1 ω.2
    have hMC : ∀ t ∈ S, t ∈ Subgroup.normalizer (W : Set G) → t * u * t⁻¹ = u → t ∈ W := by
      intro t htS htN htu
      have hτt : ρ ⟨t, htN⟩ ω = ω :=
        Subtype.ext (Subtype.ext (by rw [hρω, hu]; exact htu))
      have h1 : ρ ⟨t, htN⟩ ^ 2 = 1 := hsq2 ⟨t, htN⟩ htS
      have h2 : ρ ⟨n, hnN⟩ ^ 2 = 1 := hsq2 ⟨n, hnN⟩ hnS
      have h12 : (ρ ⟨t, htN⟩ * ρ ⟨n, hnN⟩) ^ 2 = 1 := by
        rw [← map_mul]
        exact hsq2 (⟨t, htN⟩ * ⟨n, hnN⟩) (S.mul_mem htS hnS)
      rcases perm3_involutions hcard3 _ _ h1 h2 h12 with h | h | h
      · exact hker ⟨t, htN⟩ htS h
      · exact absurd h hn1
      · exfalso
        apply hω
        rw [← h]
        exact hτt
    have hCu : ∀ s ∈ S, s * u * s⁻¹ = u → s ∈ W := by
      intro s hsS hsu
      by_contra hsW
      set T : Subgroup G := S ⊓ Subgroup.centralizer ({u} : Set G) with hT
      have hT2 : IsPGroup 2 ↥T := isPGroup_of_le hS inf_le_left
      have hcomm : ∀ x ∈ W, x * u = u * x := fun x hx => hWab x hx u huW
      have hWT : W ≤ T := fun w hw =>
        Subgroup.mem_inf.2 ⟨hWS hw, Subgroup.mem_centralizer_singleton_iff.2 (hcomm w hw)⟩
      have hsT : s ∈ T := Subgroup.mem_inf.2 ⟨hsS, Subgroup.mem_centralizer_singleton_iff.2 (by
        calc s * u = (s * u * s⁻¹) * s := by group
          _ = u * s := by rw [hsu])⟩
      have hneT : W ≠ T := fun h => hsW (h ▸ hsT)
      obtain ⟨t, htT, htW, htN⟩ := exists_mem_normalizer_of_lt hT2 hWT hneT
      have htu : t * u * t⁻¹ = u := by
        have := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 htT).2
        calc t * u * t⁻¹ = (u * t) * t⁻¹ := by rw [this]
          _ = u := by group
      exact htW (hMC t (Subgroup.mem_inf.1 htT).1 htN htu)
    have hS8 : 8 ≤ Nat.card ↥S := by
      have hdvd : Nat.card W ∣ Nat.card S := Subgroup.card_dvd_of_le hWS
      obtain ⟨m, hm⟩ := hdvd
      rw [hW4] at hm
      have hm0 : 0 < Nat.card S := Nat.card_pos
      have hm1 : m ≠ 1 := by
        intro h1
        rw [h1, mul_one] at hm
        have hWS' : W = S := Subgroup.eq_of_le_of_card_ge hWS (by rw [hm, hW4])
        exact hnW (hWS' ▸ hnS)
      omega
    let b : ↥S := ⟨u, hWS huW⟩
    have hb1 : b ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
    have hb2 : b ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hWsq u huW)
    have hbord : orderOf b = 2 := orderOf_eq_prime hb2 hb1
    have hcent : Nat.card (Subgroup.centralizer ({b} : Set ↥S)) = 4 := by
      have hmap : (Subgroup.centralizer ({b} : Set ↥S)).map S.subtype = W := by
        ext g
        constructor
        · rintro ⟨s, hs, rfl⟩
          have hs' := Subgroup.mem_centralizer_singleton_iff.1 hs
          have : (s : G) * u = u * (s : G) := congrArg Subtype.val hs'
          exact hCu s s.2 (by rw [this]; group)
        · intro hg
          exact ⟨⟨g, hWS hg⟩, Subgroup.mem_centralizer_singleton_iff.2
            (Subtype.ext (hWab g hg u huW)), rfl⟩
      rw [← Subgroup.card_map_of_injective S.subtype_injective, hmap, hW4]
    obtain ⟨p, r, -, hp, -, -⟩ :=
      CFSG.ComponentClassification.GSThmB.suzukiTausskyInput ↥S hS hS8 b hbord hcent
    have hidx : (Subgroup.zpowers p).index = 2 := by
      have h1 := Subgroup.index_mul_card (Subgroup.zpowers p)
      rw [Nat.card_zpowers] at h1
      have hpos : 0 < orderOf p := orderOf_pos p
      have : (Subgroup.zpowers p).index * orderOf p = 2 * orderOf p := by rw [h1, hp]
      exact Nat.eq_of_mul_eq_mul_right hpos this
    exact sectionalTwoRankLE_four_of_cyclic_index (Subgroup.zpowers p) (Or.inr hidx)
  ·
    push Not at hN
    have hSW : S = W := by
      by_contra hne
      obtain ⟨t, htS, htW, htN⟩ := exists_mem_normalizer_of_lt hS hWS (fun h => hne h.symm)
      exact htW (hN t htS htN)
    have h4 : Nat.card ↥S = 4 := by rw [hSW]; exact hW4
    have hsq : ∀ s ∈ S, s * s = 1 := by rw [hSW]; exact hWsq
    exact sectionalTwoRankLE_four_of_card_four h4 hsq

end Suzuki

end CFSG.CGT.PushingUpLit.SolK
