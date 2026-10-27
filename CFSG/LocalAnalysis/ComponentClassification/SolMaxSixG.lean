module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixD
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightM
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem card_eq_two_pow_factorization_of_le_of_le {X : Type} [Group X] [Finite X]
    {S C H : Subgroup X} (hSC : S ≤ C) (hCH : C ≤ H)
    (hS : Nat.card S = 2 ^ (Nat.card H).factorization 2) :
    Nat.card S = 2 ^ (Nat.card C).factorization 2 := by
  have hCpos : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hHpos : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have h1 : (Nat.card C).factorization 2 ≤ (Nat.card H).factorization 2 :=
    (Nat.factorization_le_iff_dvd hCpos hHpos).mpr (Subgroup.card_dvd_of_le hCH) 2
  have h2 : (Nat.card H).factorization 2 ≤ (Nat.card C).factorization 2 := by
    have hdvd : 2 ^ (Nat.card H).factorization 2 ∣ Nat.card C := by
      rw [← hS]
      exact Subgroup.card_dvd_of_le hSC
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hCpos).mp hdvd
  rw [hS, le_antisymm h2 h1]

namespace Sig36

variable {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)} {E : Subgroup X} {D : Finset (Fin 9)}

theorem le_zpowers_of_le_centralizer_six
    (S₀ : Sig36 X t J 9 e E D) (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ)
    (hNoA9 : ∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      ∀ K : Subgroup X, K ≤ centralizer ({x} : Set X) →
        IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set X))) →
        IsEmpty (↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin 9)))
    {Q Sc : Subgroup X}
    (hQK : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M) (hQ2 : IsPGroup 2 Q)
    (hQcard : Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M)).factorization 2) (htQ : t ∈ Q) (hQS : Q ≤ Sc)
    (hSH : Sc ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) (hS2 : IsPGroup 2 Sc)
    (hScard : Nat.card Sc =
      2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2)
    (htZ : ∀ y ∈ Sc, y * t = t * y)
    (hCQ : ∀ y ∈ Q, orderOf y = 2 →
      centralizer ({y} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {s g : X} (hsS : s ∈ Sc) (hsQ : s ∉ Q) (hgs : g⁻¹ * t * g = s) (hs2 : s * s = 1)
    (hσ6 : ∀ hsN : s ∈ normalizer (M : Set X), (ρ ⟨s, hsN⟩).support.card = 6)
    {R : Subgroup X} (hRK : R ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M) (hRs : R ≤ centralizer ({s} : Set X))
    (hRt : R ≤ centralizer ({t} : Set X)) (hR2 : IsPGroup 2 R) : R ≤ zpowers t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  set Kst := H ⊓ UnbalancedLayer.coreActionKernel M with hKstdef
  have hto : orderOf t = 2 := S₀.pair.1.1
  have hCt : centralizer ({t} : Set X) ≤ H := hCQ t htQ hto
  have hst : s * t = t * s := htZ s hsS
  have hB2 : IsPGroup 2 (R ⊔ zpowers s : Subgroup X) :=
    isPGroup_sup_zpowers_of_le_centralizer hR2 (isPGroup_zpowers_of_mul_self hs2) hRs
  have hBC : R ⊔ zpowers s ≤ centralizer ({t} : Set X) :=
    sup_le hRt (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hst))
  have hSC : Sc ≤ centralizer ({t} : Set X) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (htZ y hy)
  have hScard' := card_eq_two_pow_factorization_of_le_of_le hSC hCt hScard
  obtain ⟨c, hc, hcB⟩ := exists_conj_le_of_card_eq_of_le hSC hScard' hBC hB2
  have hcH : c ∈ H := hCt hc
  have hct : c * t = t * c := mem_centralizer_singleton_iff.mp hc
  have hQeq : Sc ⊓ Kst = Q := by
    have hle : Q ≤ Sc ⊓ Kst := le_inf hQS hQK
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have h2 : IsPGroup 2 (Sc ⊓ Kst : Subgroup X) := hS2.to_le inf_le_left
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp h2
    have hdvd : 2 ^ k ∣ Nat.card Kst := by
      rw [← hk]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hkle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
    rw [hk, hQcard]
    exact Nat.pow_le_pow_right (by norm_num) hkle
  have hcK : ∀ k ∈ Kst, c * k * c⁻¹ ∈ Kst := fun k hk =>
    Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hcH (Subgroup.mem_inf.mp hk).1) (inv_mem hcH),
      hρ.conj_mem_coreActionKernel (by norm_num) (hHN hcH) (Subgroup.mem_inf.mp hk).2⟩
  set s' := c * s * c⁻¹ with hs'def
  have hs'S : s' ∈ Sc := hcB s (mem_sup_right (mem_zpowers s))
  have hs'H : s' ∈ H := hSH hs'S
  have hs'Q : s' ∉ Q := by
    intro h
    have h1 : c⁻¹ * s' * c⁻¹⁻¹ ∈ Kst :=
      Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hcH) (Subgroup.mem_inf.mp (hQK h)).1)
        (inv_mem (inv_mem hcH)), hρ.conj_mem_coreActionKernel (by norm_num) (hHN (inv_mem hcH))
          (Subgroup.mem_inf.mp (hQK h)).2⟩
    have h2 : c⁻¹ * s' * c⁻¹⁻¹ = s := by rw [hs'def]; group
    rw [h2] at h1
    exact hsQ (hQeq ▸ Subgroup.mem_inf.mpr ⟨hsS, h1⟩)
  have hgs' : (g * c⁻¹)⁻¹ * t * (g * c⁻¹) = s' := by
    rw [hs'def, ← hgs]
    group
  have hs'2 : s' * s' = 1 := by
    rw [hs'def]
    calc c * s * c⁻¹ * (c * s * c⁻¹) = c * (s * s) * c⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  have hs't : s' * t = t * s' := htZ s' hs'S
  have hd4' : ∀ y ∈ Q, y * s' = s' * y → y ≠ 1 →
      ∀ hy : g * c⁻¹ * y * (g * c⁻¹)⁻¹ ∈ normalizer (M : Set X),
        6 ≤ (ρ ⟨g * c⁻¹ * y * (g * c⁻¹)⁻¹, hy⟩).support.card := fun y hyQ hys hy1 hyN =>
    S₀.six_le_card_support_of_commute h33 h35 hT13 hML hSch hMH hMpc hJM hHN hsup θ hρ hQK hQ2
      hQcard htQ hQS hSH hS2 hCQ hs'S hs'Q htQ hgs' hs'2 hyQ hys hy1 hyN
  have hσ2' : ρ ⟨s', hHN hs'H⟩ * ρ ⟨s', hHN hs'H⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨s', hHN hs'H⟩ : ↥(normalizer (M : Set X))) * ⟨s', hHN hs'H⟩ = 1 :=
      Subtype.ext hs'2
    rw [h1, map_one]
  have hσ6' : (ρ ⟨s', hHN hs'H⟩).support.card = 6 := by
    have h1 : (⟨s', hHN hs'H⟩ : ↥(normalizer (M : Set X))) =
        ⟨c, hHN hcH⟩ * ⟨s, hHN (hSH hsS)⟩ * (⟨c, hHN hcH⟩ : ↥(normalizer (M : Set X)))⁻¹ :=
      Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv, Perm.card_support_conj]
    exact hσ6 _
  have hR6 := S₀.inf_centralizer_le_zpowers_of_six hT13 hML hSch hPump hN1 hJM hsup hρ hNoA9 hHN
    hQK hQ2 htQ hCt hs'H hs't hs'2 hgs' hd4' hσ2' hσ6'
  intro r hr
  have hcr : c * r * c⁻¹ ∈ Q ⊓ centralizer ({s'} : Set X) := by
    refine Subgroup.mem_inf.mpr
      ⟨hQeq ▸ Subgroup.mem_inf.mpr ⟨hcB r (mem_sup_left hr), hcK r (hRK hr)⟩, ?_⟩
    rw [mem_centralizer_singleton_iff, hs'def]
    have hrs : r * s = s * r := mem_centralizer_singleton_iff.mp (hRs hr)
    calc c * r * c⁻¹ * (c * s * c⁻¹) = c * (r * s) * c⁻¹ := by group
      _ = c * (s * r) * c⁻¹ := by rw [hrs]
      _ = c * s * c⁻¹ * (c * r * c⁻¹) := by group
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hR6 hcr)
  refine mem_zpowers_iff.mpr ⟨k, ?_⟩
  have hctk : c * t ^ k * c⁻¹ = t ^ k := by
    rw [← conj_zpow]
    congr 1
    rw [hct]
    group
  calc t ^ k = c⁻¹ * (c * t ^ k * c⁻¹) * c := by group
    _ = c⁻¹ * (c * r * c⁻¹) * c := by rw [hctk, hk]
    _ = r := by group

end Sig36

@[expose] def SignalizerNineSixDihedralLocalInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)) (E : Subgroup X) (D : Finset (Fin 9)),
    Sig36 X t J 9 e E D → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M → normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) →
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)), IsPermAction θ ρ →
      (∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
        ∀ K : Subgroup X, K ≤ centralizer ({x} : Set X) →
          IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set X))) →
          IsEmpty (↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin 9))) →
    ∀ Q S : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q → Q ≤ S →
      S ≤ normalizer (Sol78.signalizerCompletion E E : Set X) → IsPGroup 2 S →
      Nat.card S =
        2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2 →
      (∀ y ∈ S, y * t = t * y) →
      (∀ y ∈ Q, orderOf y = 2 →
        centralizer ({y} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      (∀ x y : X, y ∈ S → y ∉ Q → y ∈ Q.map (MulAut.conj x).toMonoidHom →
        Q ⊓ Q.map (MulAut.conj x).toMonoidHom = ⊥) →
    ∀ s ∈ S, s ∉ Q → ∀ g : X, g⁻¹ * t * g = s →
      g ∉ normalizer (Sol78.signalizerCompletion E E : Set X) → s * s = 1 →
      (∀ y ∈ Q, y * s = s * y → y ≠ 1 → ∀ hy : g * y * g⁻¹ ∈ normalizer (M : Set X),
        6 ≤ (ρ ⟨g * y * g⁻¹, hy⟩).support.card) →
    ∀ hsN : s ∈ normalizer (M : Set X), ρ ⟨s, hsN⟩ * ρ ⟨s, hsN⟩ = 1 →
      (ρ ⟨s, hsN⟩).support.card = 6 → (∃ y ∈ Q, orderOf y = 2 ∧ y ≠ t) →
      Q ⊓ centralizer ({s} : Set X) ≤ zpowers t →
      (∀ ht₁N : g * t * g⁻¹ ∈ normalizer (M : Set X),
        (ρ ⟨g * t * g⁻¹, ht₁N⟩).support.card = 6) →
      (∀ R : Subgroup X, R ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
          UnbalancedLayer.coreActionKernel M → R ≤ centralizer ({s} : Set X) →
          R ≤ centralizer ({t} : Set X) → IsPGroup 2 R → R ≤ zpowers t) →
      ¬ KernelBalanceAt t J e (normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M) → False

theorem signalizerNineSixDihedralLocalInput_of_dihedral (h : SignalizerNineSixDihedralInput) :
    SignalizerNineSixDihedralLocalInput := by
  intro X _ _ _ t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard htZ hCQ hd3 s hsS hsQ g hgs hgH hs2 hd4 hsN hρs2 h6 hy hR6 h6t _ _
  exact h X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard htZ hCQ hd3 s hsS hsQ g hgs hgH hs2 hd4 hsN hρs2 h6 hy hR6 h6t

end CFSG.ComponentClassification.SolMax
