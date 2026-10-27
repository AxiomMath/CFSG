module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Fusion

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2.Tits.MsidePrelim
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {V M : Subgroup G} {hU : IsElemAbelian 2 V}
  {hMN : M ≤ Subgroup.normalizer (V : Set G)}

theorem exists_commuting_lifts {K : Subgroup G} (hKM : K ≤ M)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M))
    {g₁ g₂ : MulAut (IntMod V hU)} (h₁ : g₁ ∈ autI hU K) (h₂ : g₂ ∈ autI hU K)
    (hc : g₁ * g₂ = g₂ * g₁) (ho₁ : g₁ ^ 3 = 1) (ho₂ : g₂ ^ 3 = 1) :
    ∃ (x₁ : G) (x₂ : G) (hx₁ : x₁ ∈ K) (hx₂ : x₂ ∈ K), x₁ * x₂ = x₂ * x₁ ∧ x₁ ^ 3 = 1 ∧
      x₂ ^ 3 = 1 ∧ actM hU hMN ⟨x₁, hKM hx₁⟩ = g₁ ∧ actM hU hMN ⟨x₂, hKM hx₂⟩ = g₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ : ↥K →* MulAut (IntMod V hU) := (actM hU hMN).comp (Subgroup.inclusion hKM) with hφ
  have hφapp : ∀ k : ↥K, φ k = actM hU hMN ⟨k, hKM k.2⟩ := fun k => rfl
  have hφrange : ∀ g ∈ autI hU K, ∃ k : ↥K, φ k = g := by
    intro g hg
    obtain ⟨n, hnK, rfl⟩ := (mem_autI hU).1 hg
    exact ⟨⟨n, hnK⟩, (actM_eq_convI hU hMN _).trans rfl⟩
  have hφker : ∀ k : ↥K, φ k = 1 → (k : G) ∈ Subgroup.centralizer (V : Set G) ⊓ M := by
    intro k hk
    exact ⟨(actM_eq_one_iff hU hMN ⟨k, hKM k.2⟩).1 hk, hKM k.2⟩
  set Q : Subgroup (MulAut (IntMod V hU)) := Subgroup.closure {g₁, g₂} with hQ
  have hQp : IsPGroup 3 Q := isPGroup_three_closure_pair hc ho₁ ho₂
  have hQK : Q ≤ autI hU K := (Subgroup.closure_le _).2 (by
    intro a ha; rcases ha with rfl | ha; exact h₁; simp at ha; subst ha; exact h₂)
  set R : Subgroup ↥K := Q.comap φ with hR
  set ψ : ↥R →* ↥Q := (φ.comp R.subtype).codRestrict Q (fun r => r.2) with hψ
  have hψapp : ∀ r : ↥R, (ψ r : MulAut (IntMod V hU)) = φ r := fun r => rfl
  have hψs : Function.Surjective ψ := by
    intro q
    obtain ⟨k, hk⟩ := hφrange q.1 (hQK q.2)
    exact ⟨⟨k, by rw [hR, Subgroup.mem_comap, hk]; exact q.2⟩, Subtype.ext hk⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 ↥R) := inferInstance
  have hStop : ((S.mapSurjective hψs : Sylow 3 ↥Q) : Subgroup ↥Q) = ⊤ := by
    refine top_le_iff.1 ?_
    have hTop : IsPGroup 3 (⊤ : Subgroup ↥Q) := hQp.of_equiv Subgroup.topEquiv.symm
    exact ((S.mapSurjective hψs).is_maximal' (Q := ⊤) hTop le_top).le
  have hSmap : ∀ q : ↥Q, ∃ s ∈ (S : Subgroup ↥R), ψ s = q := by
    intro q
    have hq : q ∈ ((S.mapSurjective hψs : Sylow 3 ↥Q) : Subgroup ↥Q) := by rw [hStop]; trivial
    rw [Sylow.coe_mapSurjective] at hq
    obtain ⟨s, hs, hsq⟩ := Subgroup.mem_map.1 hq
    exact ⟨s, hs, hsq⟩
  have hSker : ∀ s ∈ (S : Subgroup ↥R), ψ s = 1 → s = 1 := by
    intro s hs h1
    have hφ1 : φ (s : ↥K) = 1 := by
      have := congrArg Subtype.val h1
      simpa [hψapp] using this
    have hmem := hφker (s : ↥K) hφ1
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    have hsk : (s : G) ^ (3 ^ k) = 1 := by
      have := congrArg (fun z : ↥S => ((z : ↥R) : ↥K).1) hk
      simpa using this
    have hord : orderOf (s : G) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hsk
    have hord2 : orderOf (s : G) ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M) :=
      Subgroup.orderOf_dvd_natCard _ hmem
    have hcop : Nat.Coprime (3 ^ k) (Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M)) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hC3)
    have h1' : orderOf (s : G) = 1 := (hcop.of_dvd_left hord).eq_one_of_dvd hord2
    have : (s : G) = 1 := orderOf_eq_one_iff.1 h1'
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨s₁, hs₁, e₁⟩ := hSmap ⟨g₁, Subgroup.subset_closure (by simp)⟩
  obtain ⟨s₂, hs₂, e₂⟩ := hSmap ⟨g₂, Subgroup.subset_closure (by simp)⟩
  have hψe₁ : φ (s₁ : ↥K) = g₁ := by simpa [hψapp] using congrArg Subtype.val e₁
  have hψe₂ : φ (s₂ : ↥K) = g₂ := by simpa [hψapp] using congrArg Subtype.val e₂
  have hcS : ((s₁ * s₂ * s₁⁻¹ * s₂⁻¹ : ↥R)) ∈ (S : Subgroup ↥R) :=
    S.mul_mem (S.mul_mem (S.mul_mem hs₁ hs₂) (S.inv_mem hs₁)) (S.inv_mem hs₂)
  have hψc : ψ (s₁ * s₂ * s₁⁻¹ * s₂⁻¹) = 1 := by
    apply Subtype.ext
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, e₁, e₂]
    show g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = 1
    rw [hc]; group
  have hcommR := hSker _ hcS hψc
  have hcommG : ((s₁ : ↥K) : G) * ((s₂ : ↥K) : G) = ((s₂ : ↥K) : G) * ((s₁ : ↥K) : G) := by
    have h := congrArg (fun r : ↥R => ((r : ↥K) : G)) hcommR
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at h
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h)
  have hcube : ∀ (s : ↥R) (g : ↥Q), s ∈ (S : Subgroup ↥R) → ψ s = g → g ^ 3 = 1 →
      ((s : ↥K) : G) ^ 3 = 1 := by
    intro s g hs hsg hg3
    have hs3 : s ^ 3 ∈ (S : Subgroup ↥R) := S.pow_mem hs 3
    have hψ3 : ψ (s ^ 3) = 1 := by rw [map_pow, hsg]; exact hg3
    have := hSker _ hs3 hψ3
    have h := congrArg (fun r : ↥R => ((r : ↥K) : G)) this
    simpa using h
  refine ⟨((s₁ : ↥K) : G), ((s₂ : ↥K) : G), (s₁ : ↥K).2, (s₂ : ↥K).2, hcommG,
    hcube s₁ ⟨g₁, _⟩ hs₁ e₁ (Subtype.ext ho₁), hcube s₂ ⟨g₂, _⟩ hs₂ e₂ (Subtype.ext ho₂), ?_, ?_⟩
  · exact hψe₁
  · exact hψe₂

theorem false_of_two_factors_of_pair (hMN : M ≤ Subgroup.normalizer (V : Set G)) {K : Subgroup G}
    (hKM : K ≤ M) (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    (hcard : ∀ L ∈ I, Nat.card L = 6) {L₁ L₂ : Subgroup (MulAut (IntMod V hU))} (h₁ : L₁ ∈ I)
    (h₂ : L₂ ∈ I) (hne : L₁ ≠ L₂) (hL₁ : L₁ ≤ autI hU K) (hL₂ : L₂ ≤ autI hU K)
    (hpair : ∀ x₁ x₂ : G, x₁ ∈ K → x₂ ∈ K → x₁ * x₂ = x₂ * x₁ → x₁ ^ 3 = 1 → x₂ ^ 3 = 1 →
      ∀ (hx₁M : x₁ ∈ M) (hx₂M : x₂ ∈ M), actM hU hMN ⟨x₁, hx₁M⟩ ∈ L₁ →
        actM hU hMN ⟨x₂, hx₂M⟩ ∈ L₂ → actM hU hMN ⟨x₁, hx₁M⟩ ≠ 1 → actM hU hMN ⟨x₂, hx₂M⟩ ≠ 1 →
        False) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : ∀ L ∈ I, ∃ g ∈ L, g ^ 3 = 1 ∧ g ≠ 1 := by
    intro L hL
    have h3 : 3 ∣ Nat.card L := by rw [hcard L hL]; norm_num
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := L) 3 h3
    refine ⟨g.1, g.2, ?_, ?_⟩
    · have := pow_orderOf_eq_one g
      rw [hg] at this
      exact congrArg Subtype.val this
    · intro h1
      have : g = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hg
      omega
  obtain ⟨g₁, hg₁, ho₁, hne₁⟩ := hord L₁ h₁
  obtain ⟨g₂, hg₂, ho₂, hne₂⟩ := hord L₂ h₂
  obtain ⟨x₁, x₂, hx₁, hx₂, hcomm, hx₁3, hx₂3, e₁, e₂⟩ := exists_commuting_lifts (hU := hU)
    (hMN := hMN) hKM hC3 (hL₁ hg₁) (hL₂ hg₂) (hI.comm L₁ h₁ L₂ h₂ hne g₁ hg₁ g₂ hg₂) ho₁ ho₂
  exact hpair x₁ x₂ hx₁ hx₂ hcomm hx₁3 hx₂3 (hKM hx₁) (hKM hx₂) (e₁ ▸ hg₁) (e₂ ▸ hg₂)
    (e₁ ▸ hne₁) (e₂ ▸ hne₂)


theorem false_of_two_factors_in_normalizer {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K₀) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) (hMN : M ≤ Subgroup.normalizer (V : Set G)) {X : Subgroup G}
    (hX1 : X ≠ ⊥) (hXp : IsPGroup 2 X)
    (hNX : ¬ Subgroup.normalizer (X : Set G) ≤ M) {K : Subgroup G} (hKM : K ≤ M)
    (hKN : K ≤ Subgroup.normalizer (X : Set G))
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    (hcard : ∀ L ∈ I, Nat.card L = 6) {L₁ L₂ : Subgroup (MulAut (IntMod V hU))} (h₁ : L₁ ∈ I)
    (h₂ : L₂ ∈ I) (hne : L₁ ≠ L₂) (hL₁ : L₁ ≤ autI hU K) (hL₂ : L₂ ≤ autI hU K) : False := by
  have hN : IsTwoLocal (Subgroup.normalizer (X : Set G)) := ⟨X, hX1, hXp, rfl⟩
  exact false_of_two_factors_of_pair hMN hKM hC3 hI hcard h₁ h₂ hne hL₁ hL₂
    fun _ _ hx₁ hx₂ hcomm hx₁3 hx₂3 hx₁M hx₂M he₁ he₂ hn₁ hn₂ =>
      false_of_same_side_pair hc hstr hOnly hN hNX hU hMN hI h₁ h₂ hne hx₁M hx₂M (hKN hx₁)
        (hKN hx₂) hcomm hx₁3 hx₂3 he₁ he₂ hn₁ hn₂

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
