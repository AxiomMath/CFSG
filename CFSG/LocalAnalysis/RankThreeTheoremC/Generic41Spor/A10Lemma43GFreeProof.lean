module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GFree
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GConcB
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GConcC

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup

theorem gammaStructAt_A10 : A10GammaStructAt A10Perm.A10 A10Perm.S₀ A10Perm.L1 A10Perm.L2 := by
  have h1 : A10Perm.S₀ ⊓ A10Perm.L1 = A10Perm.line₁ := A10Perm.S₀_inf_L1
  have h2 : A10Perm.S₀ ⊓ A10Perm.L2 = A10Perm.line₂ := A10Perm.S₀_inf_L2
  refine ⟨A10Perm.L1_le_gamma, A10Perm.L2_le_gamma, A10Perm.L1_inf_L2, A10Perm.L1_comm_L2,
    A10Perm.L1_iso, A10Perm.L2_iso, A10Perm.gamma_five, ?_, ?_, ?_, ?_, ?_, A10Perm.swap_L⟩
  · rw [h1]; exact A10Perm.card_line₁
  · rw [h2]; exact A10Perm.card_line₂
  · rw [h1, h2]; exact a10c_line_sup
  · intro s hs hs1 h
    exact A10Perm.cent_L s hs hs1 h
  · intro s hs h1' h2'
    exact A10Perm.cent_diag s hs h1' h2'

theorem a10t1_comap_equiv {K L : Type} [Group K] [Group L] (ψ : K ≃* L) (H : Subgroup L) :
    Nonempty (↥(H.comap ψ.toMonoidHom) ≃* ↥H) :=
  ⟨{ toFun := fun x => ⟨ψ x.1, x.2⟩
     invFun := fun y => ⟨ψ.symm y.1, by
       show ψ (ψ.symm y.1) ∈ H
       rw [MulEquiv.apply_symm_apply]; exact y.2⟩
     left_inv := fun x => by ext; simp
     right_inv := fun y => by ext; simp
     map_mul' := fun x y => Subtype.ext (map_mul ψ x.1 y.1) }⟩

theorem a10t1_card_comap {K L : Type} [Group K] [Group L] (ψ : K ≃* L) (H : Subgroup L) :
    Nat.card ↥(H.comap ψ.toMonoidHom) = Nat.card ↥H := by
  obtain ⟨e⟩ := a10t1_comap_equiv ψ H
  exact Nat.card_congr e.toEquiv

theorem a10t1_gamma_map {K L : Type} [Group K] [Group L] (ψ : K ≃* L) (S : Subgroup L) :
    (A10Gamma K (S.comap ψ.toMonoidHom)).map ψ.toMonoidHom = A10Gamma L S := by
  unfold A10Gamma
  rw [MonoidHom.map_closure]
  congr 1
  ext g'
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, ⟨B, hBS, hB1, hg⟩, rfl⟩
    refine ⟨B.map ψ.toMonoidHom, Subgroup.map_le_iff_le_comap.2 hBS, ?_, ?_⟩
    · intro h
      exact hB1 ((Subgroup.map_eq_bot_iff_of_injective B ψ.injective).1 h)
    · exact Subgroup.le_normalizer_map ψ.toMonoidHom ⟨g, hg, rfl⟩
  · rintro ⟨B', hB'S, hB'1, hg'⟩
    refine ⟨ψ.symm g', ⟨B'.comap ψ.toMonoidHom, Subgroup.comap_mono hB'S, ?_, ?_⟩, by simp⟩
    · intro h
      apply hB'1
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := ψ.toMonoidHom) ψ.surjective B', h,
        Subgroup.map_bot]
    · rw [← Subgroup.comap_normalizer_eq_of_surjective B' (f := ψ.toMonoidHom) ψ.surjective]
      refine Subgroup.mem_comap.2 ?_
      simpa using hg'

theorem a10t1_gamma_comap {K L : Type} [Group K] [Group L] (ψ : K ≃* L) (S : Subgroup L) :
    A10Gamma K (S.comap ψ.toMonoidHom) = (A10Gamma L S).comap ψ.toMonoidHom := by
  rw [← a10t1_gamma_map ψ S, Subgroup.comap_map_eq_self_of_injective ψ.injective]

theorem a10_gammaStructAt_of_equiv {K L : Type} [Group K] [Finite K] [Group L] [Finite L] (ψ : K ≃* L)
    {S Λ₁ Λ₂ : Subgroup L} (h : A10GammaStructAt L S Λ₁ Λ₂) :
    A10GammaStructAt K (S.comap ψ.toMonoidHom) (Λ₁.comap ψ.toMonoidHom) (Λ₂.comap ψ.toMonoidHom) := by
  have hΓ := a10t1_gamma_comap ψ S
  have hsup := Subgroup.comap_sup_eq ψ.toMonoidHom Λ₁ Λ₂ ψ.surjective
  have hne1 : ∀ s : K, s ≠ 1 → ψ s ≠ 1 := fun s hs h1 => hs (ψ.injective (by rw [h1, map_one]))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hΓ]; exact Subgroup.comap_mono h.le_gamma₁
  · rw [hΓ]; exact Subgroup.comap_mono h.le_gamma₂
  · refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have hx' : ψ x ∈ Λ₁ ⊓ Λ₂ := hx
    rw [h.inf_bot, Subgroup.mem_bot] at hx'
    exact ψ.injective (by rw [hx', map_one])
  · intro a ha b hb
    exact ψ.injective (by simpa [map_mul] using h.comm (ψ a) ha (ψ b) hb)
  · obtain ⟨e⟩ := h.iso₁
    obtain ⟨c⟩ := a10t1_comap_equiv ψ Λ₁
    exact ⟨c.trans e⟩
  · obtain ⟨e⟩ := h.iso₂
    obtain ⟨c⟩ := a10t1_comap_equiv ψ Λ₂
    exact ⟨c.trans e⟩
  · intro g hg ⟨k, hk⟩
    rw [hΓ] at hg
    have hg' : ψ g ∈ A10Gamma L S := hg
    have := h.five (ψ g) hg' ⟨k, by rw [← map_pow, hk, map_one]⟩
    rw [hsup]
    exact this
  · rw [← Subgroup.comap_inf, a10t1_card_comap]; exact h.S_card₁
  · rw [← Subgroup.comap_inf, a10t1_card_comap]; exact h.S_card₂
  · rw [← Subgroup.comap_inf, ← Subgroup.comap_inf, Subgroup.comap_sup_eq _ _ _ ψ.surjective, h.S_sup]
  · intro s hs hs1 hΛ
    rw [a10c_card_centralizer_equiv ψ s]
    exact h.cent₃₀₀ (ψ s) hs (hne1 s hs1) hΛ
  · intro s hs hs1 hs2
    rw [a10c_card_centralizer_equiv ψ s]
    exact h.cent₂₅ (ψ s) hs hs1 hs2
  · obtain ⟨n', hn', hswap⟩ := h.swap
    refine ⟨ψ.symm n', ?_, ?_⟩
    · rw [← Subgroup.comap_normalizer_eq_of_surjective S (f := ψ.toMonoidHom) ψ.surjective]
      refine Subgroup.mem_comap.2 ?_
      simpa using hn'
    · ext x
      constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
        have hy' : ψ y ∈ Λ₁ := hy
        show ψ (ψ.symm n' * y * (ψ.symm n')⁻¹) ∈ Λ₂
        rw [← hswap]
        refine Subgroup.mem_map.2 ⟨ψ y, hy', ?_⟩
        simp [map_mul, map_inv]
      · intro hx
        have hx' : ψ x ∈ Λ₂ := hx
        rw [← hswap] at hx'
        obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hx'
        refine Subgroup.mem_map.2 ⟨ψ.symm z, ?_, ?_⟩
        · show ψ (ψ.symm z) ∈ Λ₁
          rwa [MulEquiv.apply_symm_apply]
        · apply ψ.injective
          have : n' * z * n'⁻¹ = ψ x := hzx
          simp [map_mul, map_inv, this]

theorem a10_irred : ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → A10Irred K := by
  intro K _ _ hK S A hAS hinv
  have hS : Nat.card (S : Subgroup K) = 5 ^ 2 := (a10_sylow K hK S).2
  have hdvd : Nat.card A ∣ 5 ^ 2 := hS ▸ Subgroup.card_dvd_of_le hAS
  rcases (Nat.dvd_prime_pow Nat.prime_five).1 hdvd with ⟨k, hk, hkA⟩
  interval_cases k
  · left
    exact Subgroup.card_eq_one.1 (by simpa using hkA)
  · exfalso
    have hA5 : Nat.card A = 5 := by simpa using hkA
    have hne : A ≠ ⊥ := by
      intro h
      rw [h] at hA5
      simp at hA5
    obtain ⟨⟨t, htA⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
    have hAeq : A = Subgroup.zpowers t := A10Perm.eq_zpowers_of_card_five hA5 htA ht1'
    obtain ⟨n, hn, hnt⟩ := a10_movesLines K hK S t (hAS htA) ht1'
    exact hnt (hAeq ▸ hinv n hn t htA)
  · right
    refine Subgroup.eq_of_le_of_card_ge hAS ?_
    rw [hS, hkA]

theorem a10_L43Facts_holds : A10L43Facts := by
  refine ⟨?_, a10_irred⟩
  intro K _ _ hK S
  obtain ⟨-, ⟨e⟩⟩ := hK
  obtain ⟨ψ, hψ⟩ := A10Perm.exists_iso_sylow e S
  have hS : (S : Subgroup K) = A10Perm.S₀.comap ψ.toMonoidHom := by
    ext x
    exact hψ x
  refine ⟨A10Perm.L1.comap ψ.toMonoidHom, A10Perm.L2.comap ψ.toMonoidHom, ?_⟩
  rw [hS]
  exact a10_gammaStructAt_of_equiv ψ gammaStructAt_A10

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
