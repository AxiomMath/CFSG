module

public import CFSG.LocalAnalysis.GH72.Sec4Max

public section

namespace CFSG.GH72

open Subgroup

namespace G4b

section Bar

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem bar_self (H : Subgroup G) : bar H H = ⊤ := by
  rw [bar, subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem isKleinFour_bar {H K : Subgroup G} (hKH : K ≤ H) (hK : IsKleinFour K) :
    IsKleinFour (bar H K) := by
  have hK2 : IsPGroup 2 K := IsPGroup.of_card (n := 2) (by rw [hK.card_four]; norm_num)
  obtain ⟨e⟩ := nonempty_mulEquiv_bar hKH hK2
  exact ⟨by rw [← Nat.card_congr e.toEquiv, hK.card_four],
    by rw [← Monoid.exponent_eq_of_mulEquiv e, hK.exponent_two]⟩

omit [Finite G] in
theorem exists_conj_of_map_conj {p : ℕ} {H A : Subgroup G} (x : G)
    (hT : ∀ Q₁ Q₂ : Subgroup G,
      IsMaxInvIn p (A.map (MulAut.conj x).toMonoidHom) (H.map (MulAut.conj x).toMonoidHom) Q₁ →
      IsMaxInvIn p (A.map (MulAut.conj x).toMonoidHom) (H.map (MulAut.conj x).toMonoidHom) Q₂ →
      ∃ g ∈ H.map (MulAut.conj x).toMonoidHom ⊓
          normalizer ((A.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G),
        Q₁.map (MulAut.conj g).toMonoidHom = Q₂)
    {P₁ P₂ : Subgroup G} (h₁ : IsMaxInvIn p A H P₁) (h₂ : IsMaxInvIn p A H P₂) :
    ∃ g ∈ H ⊓ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂ := by
  have hback : ∀ K : Subgroup G,
      (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = K :=
    fun K => map_conj_inv_map_conj K x
  obtain ⟨g', hg', hg'P⟩ := hT _ _ (IsMaxInvIn.map h₁ (MulAut.conj x))
    (IsMaxInvIn.map h₂ (MulAut.conj x))
  obtain ⟨hg'H, hg'A⟩ := mem_inf.1 hg'
  refine ⟨x⁻¹ * g' * x, mem_inf.2 ⟨mem_map_conj.1 hg'H, ?_⟩, ?_⟩
  · rw [mem_normalizer_iff_map_conj_eq', ← G4b.map_conj_map_conj, ← G4b.map_conj_map_conj,
      mem_normalizer_iff_map_conj_eq'.1 hg'A, hback]
  · rw [← G4b.map_conj_map_conj, ← G4b.map_conj_map_conj, hg'P, hback]

theorem le_O2_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H P : Subgroup G} (hPH : P ≤ H)
    (hP : IsPGroup p P) : P ≤ O2 H := fun _ hx =>
  mem_twoResidualOf_of_odd (hPH hx) (Odd.of_dvd_nat (odd_card_of_isPGroup hp hp2 hP)
    (Subgroup.orderOf_dvd_natCard P hx))

end Bar

end G4b

namespace Sec4Setting

open G4b

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G)

theorem exists_map_conj_sylow (H A : Subgroup G) (hAH : A ≤ H) (hA : IsE16 A) :
    ∃ x : G, A.map (MulAut.conj x).toMonoidHom ≤ 𝔖.S ∧
      ABGLocalTools.IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ H.map (MulAut.conj x).toMonoidHom)
        (H.map (MulAut.conj x).toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [hA.2]; norm_num)
  obtain ⟨T, hT, hAT⟩ := exists_isSylowOf_ge hAH hA2
  obtain ⟨x, hx⟩ := exists_map_conj_le_sylow 𝔖.S hT.isPGroup
  refine ⟨x, (map_mono hAT).trans hx, ?_⟩
  have hTx := isSylowOf_map_hom hT (MulAut.conj x).toMonoidHom
  have heq := hTx.eq_of_le (le_inf hx (map_mono hT.le)) inf_le_right
    ((𝔖.S.isPGroup').to_le inf_le_left)
  rw [heq]
  exact hTx


theorem lemma_4_5_noniso_of
    (h44 : ∀ H : Subgroup G, H ≠ ⊤ → (∀ t, ¬ IsIsolatedIn H t) →
      ∀ A : Subgroup G, A ≤ H → IsE16 A → ∀ J : Subgroup G, O2 H ⊔ A ≤ J → J ≤ H →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J)) J →
      ∃ L₁ L₂ : Subgroup (Bar H), L₁ ≤ bar H J ∧ L₂ ≤ bar H J ∧ L₁ ⊓ L₂ = ⊥ ∧
        L₂ ≤ centralizer (L₁ : Set (Bar H)) ∧ ((L₁ ⊔ L₂).subgroupOf (bar H J)).Normal ∧
        bar H J = (L₁ ⊔ L₂) ⊔ (bar H J ⊓ normalizer (bar H A : Set (Bar H))) ∧
        IsL2PGL2OrA7OrV4 L₁ ∧ IsL2PGL2OrA7OrV4 L₂ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔖.S₁ ⊓ L₁) L₁ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔖.S₂ ⊓ L₂) L₂ ∧
        bar H 𝔖.S₁ ⊓ bar H J ≤ L₁ ∧ bar H 𝔖.S₂ ⊓ bar H J ≤ L₂ ∧
        (L₁.subgroupOf (bar H J)).Normal ∧ (L₂.subgroupOf (bar H J)).Normal)
    (h44J : ∀ H : Subgroup G, H ≠ ⊤ → (∀ t, ¬ IsIsolatedIn H t) →
      ∀ A : Subgroup G, A ≤ H → A ≤ 𝔖.S → IsE16 A →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ H) H →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S₁ ⊓ (O2 H ⊔ A)) ⊔ (𝔖.S₂ ⊓ (O2 H ⊔ A)))
        (O2 H ⊔ A))
    (H : Subgroup G) (hH : H ≠ ⊤) (hiso : ∀ t, ¬ IsIsolatedIn H t) (A : Subgroup G)
    (hAH : A ≤ H) (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ H) H)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (P₁ P₂ : Subgroup G) (h₁ : IsMaxInvIn p A H P₁)
    (h₂ : IsMaxInvIn p A H P₂) :
    ∃ g ∈ H ⊓ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂ := by
  have : Fact p.Prime := ⟨hp⟩
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [hA.2]; norm_num)
  set J : Subgroup G := O2 H ⊔ A with hJ
  have hJH : J ≤ H := sup_le (twoResidualOf_le_self H) hAH
  obtain ⟨L₁, L₂, hL₁J, hL₂J, hLi, hLc, -, -, hL₁, hL₂, -, -, hS₁, hS₂, hN₁, hN₂⟩ :=
    h44 H hH hiso A hAH hA J le_rfl hJH (h44J H hH hiso A hAH hAS hA hsyl)
  set V₁ : Subgroup (Bar H) := bar H (𝔖.X A) with hV₁
  set V₂ : Subgroup (Bar H) := bar H (𝔖.Y A) with hV₂
  have hXH : 𝔖.X A ≤ H := (X_le_A 𝔖).trans hAH
  have hYH : 𝔖.Y A ≤ H := (Y_le_A 𝔖).trans hAH
  have hAJ : A ≤ J := le_sup_right
  have hV₁L : V₁ ≤ L₁ := (le_inf (bar_mono (X_le_S₁ 𝔖))
    (bar_mono ((X_le_A 𝔖).trans hAJ))).trans hS₁
  have hV₂L : V₂ ≤ L₂ := (le_inf (bar_mono (Y_le_S₂ 𝔖))
    (bar_mono ((Y_le_A 𝔖).trans hAJ))).trans hS₂
  have hVA : V₁ ⊔ V₂ = bar H A := by
    rw [hV₁, hV₂, ← bar_sup hXH hYH, X_sup_Y 𝔖 hAS hA]
  have hV₁4 : IsKleinFour V₁ := isKleinFour_bar hXH (isKleinFour_X 𝔖 hAS hA)
  have hV₂4 : IsKleinFour V₂ := isKleinFour_bar hYH (isKleinFour_Y 𝔖 hAS hA)
  have hJL₁ : bar H J ≤ normalizer (L₁ : Set (Bar H)) :=
    (normal_subgroupOf_iff_le_normalizer hL₁J).1 hN₁
  have hJL₂ : bar H J ≤ normalizer (L₂ : Set (Bar H)) :=
    (normal_subgroupOf_iff_le_normalizer hL₂J).1 hN₂
  have hbar : ∀ {P : Subgroup G}, IsMaxInvIn p A H P → IsMaxInvIn p (V₁ ⊔ V₂) ⊤ (bar H P) := by
    intro P hP
    have h := isMaxInvIn_bar hp hp2 le_rfl hAH hA2 hP
    rwa [bar_self, ← hVA] at h
  have hPJ : ∀ {P : Subgroup G}, IsMaxInvIn p A H P → bar H P ≤ bar H J := fun hP =>
    bar_mono ((le_O2_of_isPGroup hp hp2 hP.1 hP.2.1).trans le_sup_left)
  obtain ⟨y, hy, hyP⟩ := exists_conj_of_factors hp hp2 hV₁L hV₂L hL₁J hL₂J hJL₁ hJL₂ hLc hLi
    (by rw [hVA]; exact isPGroup_bar hA2)
    (fun Q hQ => normalizer_inf_centralizer_le_normalizer_of_isMaxInvIn hL₁ hV₁4 hV₁L hp hp2 hQ)
    (fun Q hQ => normalizer_inf_centralizer_le_normalizer_of_isMaxInvIn hL₂ hV₂4 hV₂L hp hp2 hQ)
    (fun Q Q' hQ hQ' => exists_conj_eq_of_isMaxInvIn hL₁ hV₁4 hV₁L hp hp2 hQ hQ')
    (fun Q Q' hQ hQ' => exists_conj_eq_of_isMaxInvIn hL₂ hV₂4 hV₂L hp hp2 hQ hQ')
    (hbar h₁) (hbar h₂) (hPJ h₁) (hPJ h₂)
  refine exists_conj_of_bar hp hp2 le_rfl hAH hA2 h₁ h₂ (y := y) ?_ hyP
  rw [bar_self, ← hVA]
  exact mem_inf.2 ⟨mem_top y, (mem_inf.1 hy).2⟩

end Sec4Setting

end CFSG.GH72
