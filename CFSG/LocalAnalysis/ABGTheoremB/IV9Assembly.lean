module

public import CFSG.LocalAnalysis.ABGTheoremB.IV9Constrained
public import CFSG.LocalAnalysis.ABGTheoremB.IV9Criteria
public import CFSG.LocalAnalysis.ABGTheoremB.IV7Assembly
public import CFSG.LocalAnalysis.ABGTheoremB.IV8
public import CFSG.LocalAnalysis.ABGTheoremB.V2
public import CFSG.LocalAnalysis.ABGTheoremB.IV9Final
public import CFSG.LocalAnalysis.ABGTheoremB.V6Tools
public import CFSG.LocalAnalysis.ABGTheoremB.IV3

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGQGroups

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

omit [Finite G] in
private theorem iv9a_mem_normalizer_of_characteristic {P Q : Subgroup G} (hQP : Q ≤ P)
    (hchar : (Q.subgroupOf P).Characteristic) {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) : g ∈ Subgroup.normalizer (Q : Set G) := by
  have key : ∀ h : G, h ∈ Subgroup.normalizer (P : Set G) → ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := by
    intro h hh q hq
    have hPh : P.map (MulAut.conj h).toMonoidHom = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hh
    let φ : P ≃* P := ((MulAut.conj h).subgroupMap P).trans (MulEquiv.subgroupCongr hPh)
    have hφ : ((φ ⟨q, hQP hq⟩ : P) : G) = h * q * h⁻¹ := rfl
    have hmem : (⟨q, hQP hq⟩ : P) ∈ Q.subgroupOf P := hq
    have := (Subgroup.characteristic_iff_le_comap.mp hchar) φ hmem
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at this
    rw [← hφ]
    exact this
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · exact key g hg q
  · intro hq
    have := key g⁻¹ (inv_mem hg) _ hq
    simpa [mul_assoc] using this

theorem propIV91_of (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hN : σ.IVNFacts)
    (h_II54 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ F : Subgroup G, F ≤ H → Odd (Nat.card F) → σ.T ≤ Subgroup.normalizer (F : Set G) →
        ⁅F, σ.T⁆ = F → ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ oddCoreIn H)
    (h_II34 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      (∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.T ≤ Subgroup.normalizer (X : Set G) →
          X ≤ oddCoreIn H) ∨
        ((∀ Y : Subgroup G, Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) → oddCoreIn H ≤ Y →
            Y = oddCoreIn H ∨ Y = H) ∧
          ∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.D ≤ Subgroup.normalizer (X : Set G) →
            ∃ T₁ : Subgroup G, T₁ ≤ σ.D ∧ IsKleinFour T₁ ∧ ⁅X, T₁⁆ ≤ oddCoreIn H) ∨
        (σ.height = 1 ∧ ∃ q₁ : ℕ, 3 < q₁ ∧ IsLinearTypeWrt σ.T H q₁))
    (h_II57 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      IsLinearTypeWrt σ.T H 9 → H ⊓ Subgroup.centralizer (σ.T : Set G) ≤ σ.T ⊔ oddCoreIn H)
    (h_II56 : ∀ (M Z W : Subgroup G) (F : Type) [Field F] [Finite F], Z ≤ M → W ≤ Z →
      M ≤ Subgroup.normalizer (W : Set G) → Odd (Nat.card Z) → ⁅Z, M⁆ ≤ W →
      Odd (Nat.card F) → 3 < Nat.card F → Nat.card F ≠ 9 →
      (∃ ψ : M →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧
        ψ.ker = Z.subgroupOf M) →
        ⁅M, M⁆ ⊓ Z ≤ W ∧ ⁅M, M⁆ ⊔ Z = M)
    (h_II58 : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ (J W A : Subgroup G) (F : Type) [Field F] [Finite F],
      W ≤ J → J ≤ Subgroup.normalizer (W : Set G) → Odd (Nat.card W) → Odd (Nat.card F) →
      3 < Nat.card F →
      (∃ ψ : J →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧
        ψ.ker = W.subgroupOf J) →
      σ.T ≤ J → IsPGroup r A → A ≤ Subgroup.normalizer (J : Set G) →
      A ≤ Subgroup.normalizer (W : Set G) → A ≤ Subgroup.centralizer (σ.T : Set G) →
        ∃ g ∈ J, (∀ a ∈ A, a * g * a⁻¹ * g⁻¹ ∈ W) ∧
          g ∈ Subgroup.normalizer ((σ.T ⊔ W : Subgroup G) : Set G) ∧
          (∀ t ∈ σ.T, g ^ 3 * t * (g ^ 3)⁻¹ * t⁻¹ ∈ W) ∧ ∃ t ∈ σ.T, g * t * g⁻¹ * t⁻¹ ∉ W)
    (h_y : σ.height = 1 → ∃ y ∈ σ.D, y ∉ centerOf σ.D ∧ y ∈ σ.L₀ ∧
      ∀ S₁ : Sylow 2 G, σ.D ≤ (S₁ : Subgroup G) →
        ∃ s ∈ (S₁ : Subgroup G), y = σ.x₂ * (s * σ.x₂ * s⁻¹))
    (h_II52 : ∀ r : ℕ, ∀ H : Subgroup G, σ.T ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ¬ Odd (Nat.card (pPrimeCoreIn r H)) → σ.T ≤ pPrimeCoreIn r H)
    (h_II417 : ∀ r : ℕ, σ.HypIV7 r → ∀ d : σ.IV7Data r, ∀ W : Subgroup G, W ≤ d.R →
      Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G) →
      (∀ w ∈ W, w ^ r = 1) →
      Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (W : Set G) ≤
        solvRadIn (Subgroup.normalizer (d.R : Set G)) →
      ¬ ∃ a ∈ W, ∃ b ∈ W, W ≤ Subgroup.closure {a, b} ⊔ ⁅W, W⁆)
    (h_II34a : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ H : Subgroup G, σ.T ≤ H →
      IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ W : Subgroup G, W ≤ H ⊓ σ.N → IsPGroup r W → (∀ w ∈ W, w ^ r = 1) →
        σ.T ≤ Subgroup.normalizer (W : Set G) → ⁅W, W⁆ ≤ oddCoreIn H)
    (h_II510 : ∀ r : ℕ, σ.HypIV7 r → ∀ d : σ.IV7Data r, ∀ W : Subgroup G, W ≤ d.R →
      Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G) →
      (∀ a ∈ W, ∀ b ∈ W, a * b = b * a) → (∀ w ∈ W, w ^ r = 1) →
      Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (W : Set G) ≤
        solvRadIn (Subgroup.normalizer (d.R : Set G)) →
      (W ⊓ Subgroup.centralizer {σ.x₂}).relIndex W = r →
      ∃ u ∈ Subgroup.normalizer (d.R : Set G), ∃ s k : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ r ∧
        u ^ (s ^ k) ∈ Subgroup.centralizer (W : Set G) ∧
        u ∉ Subgroup.centralizer (W : Set G) ∧
        σ.x₂ * u * σ.x₂⁻¹ * u ∈ Subgroup.centralizer (W : Set G) ∧
        ∃ a ∈ W ⊓ Subgroup.centralizer {σ.x₂}, a ≠ 1 ∧ u * a = a * u)
    (h_II34b : ∀ H : Subgroup G, σ.T ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ W : Subgroup G, W ≤ H ⊓ σ.N → Odd (Nat.card W) →
        σ.T ≤ Subgroup.normalizer (W : Set G) → ∀ v ∈ H ⊓ σ.N, Odd (orderOf v) →
          σ.x₂ * v * σ.x₂⁻¹ = v⁻¹ → v ∈ Subgroup.normalizer (W : Set G) →
            W ≤ ⁅W, Subgroup.zpowers v⁆ → W ≤ oddCoreIn H) :
    σ.PropIV91 := by
  intro r hr K hK
  have hrp : r.Prime := hr.prime
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hrp hr.dvd_ON
  have : Fact r.Prime := ⟨hrp⟩
  obtain ⟨P, hP, hPD⟩ := σ.exists_sylow_C_normalized hN.C_le_oddCore_sup_D hrp hr2
  obtain ⟨R, hR, hRD, hRP⟩ := σ.exists_sylow_ON_normalized hσ hrp hr2 hP.le hP.isPGroup hPD
  obtain ⟨d, -, -⟩ := σ.propIV71_of_IVNFacts hσ hII hN r hr P R hP hPD hR hRD hRP
  have h81 := σ.lemmaIV81 hσ hII
  have h83 := σ.lemmaIV83 hσ hII
  have hPQ : d.P ≤ Subgroup.normalizer (d.Q : Set G) := by
    have := d.Q_characteristic
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer d.Q_le).mp inferInstance
  by_cases hc : σ.Constrained r
  · by_cases hQ : PConstrainedWithin r (Subgroup.normalizer (d.Q : Set G))
        (CFSG.oddCore (Subgroup.normalizer (d.Q : Set G)))
    · exact σ.constrained_of_exists_constrained hσ hII h_II54 hrp hr2
        ⟨_, σ.normalizer_Q_mem_familyMstar hr d h81 h83, hQ, d.P, d.P_sylow, d.P_D, hPQ⟩ hK
    · have h92 : ∀ K ∈ σ.familyMstar r, PConstrainedWithin r K (CFSG.oddCore K) ↔
          ∃ X : Subgroup G, IsSylowOf r X (oddCoreIn K) ∧
            σ.T ≤ Subgroup.normalizer (X : Set G) ∧ ¬ σ.T ≤ Subgroup.centralizer (X : Set G) :=
        fun K hK => σ.constrained_iff_exists_sylow_not_centralized hσ hII hrp hr2 hK
      have hqd := (σ.lemmaIV95_i hσ hII hr d hc hQ h81 h83 h92 h_II34).1
      obtain ⟨e⟩ := σ.nonempty_IV9UV hσ hII hr d hc
      obtain ⟨hH₁, hPH₁, -⟩ := σ.lemmaIV98 hσ hII hr hc hQ h81 h83 h92 h_II34 h_II57 h_II56
        (h_II58 r hrp hr2) e h_y (h_II52 r)
      obtain ⟨⟨hexp, hcl⟩, ⟨hPU, hPV⟩, hne, hPV0⟩ := σ.lemmaIV97 hσ hII hr hc hQ h81 h83 h92 h_II34
        h_II57 h_II56 (h_II58 r hrp hr2) e h_y
      have h95 := σ.lemmaIV95_iii hσ hII hr d hc hQ h81 h83 h92 h_II34 h_II57 h_II56
        (h_II58 r hrp hr2)
      have hTQP : σ.T ≤ Subgroup.normalizer (d.Q : Set G) ⊓ Subgroup.centralizer (d.P : Set G) :=
        le_inf (fun _ ht => iv9a_mem_normalizer_of_characteristic d.Q_le d.Q_characteristic
            (d.P_D ((σ.T_le_D hσ) ht)))
          (Subgroup.le_centralizer_iff.mp d.P_sylow.le)
      have h95iii : 3 ∣ automizerIndex (σ.T.subgroupOf (Subgroup.centralizer (d.P : Set G))) :=
        V56.three_dvd_automizerIndex_of_subset_mul (O := ⊥) bot_le (fun _ _ => by
            rw [Subgroup.mem_normalizer_iff]; intro; simp)
          (by simp) (fun g hg => ⟨1, rfl, g, hg, one_mul g⟩) le_rfl inf_le_right hTQP
          (σ.S.isPGroup'.to_le (σ.T_le_S hσ))
          (fun a ha _ hb => (Subgroup.mem_centralizer_iff.mp (σ.T_le_C hσ hb)) a ha) h95.2.2
      have hcomm3 : ⁅⁅e.U, e.U⁆, e.U⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro a ha b _
        have hz := hcl ha
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_centralizer_iff.mp hz.2) _ ‹b ∈ e.U› |>.symm
      have hCV : σ.C ⊓ e.V = ⊥ := hPV ▸ hPV0
      have h99 := σ.lemmaIV99 hσ hII hr d hqd e
        (fun h => (σ.constrained_iff_exists_sylow_not_centralized hσ hII hrp hr2 hH₁).mpr h)
        h95iii ⟨hexp, hcomm3, hPU, hCV, hne⟩ ⟨hH₁.2.1, hH₁.2.2.1⟩ h_II54 (h_II417 r hr d)
        (h_II34a r hrp hr2) (h_II510 r hr d) h_II34b
      exact σ.constrained_of_exists_constrained hσ hII h_II54 hrp hr2
        ⟨e.H₁, hH₁, h99, d.P, d.P_sylow, d.P_D, hPH₁⟩ hK
  · exact σ.familyMstar_constrained_of_not_constrained hσ hII (σ.lemmaIV33 hσ hII) h81 h83 h_II54
      hr hc d hK

theorem propIV91_of_height_ne_one (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hN : σ.IVNFacts)
    (hh : σ.height ≠ 1)
    (h_II54 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ F : Subgroup G, F ≤ H → Odd (Nat.card F) → σ.T ≤ Subgroup.normalizer (F : Set G) →
        ⁅F, σ.T⁆ = F → ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ oddCoreIn H)
    (h_II34 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      (∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.T ≤ Subgroup.normalizer (X : Set G) →
          X ≤ oddCoreIn H) ∨
        ((∀ Y : Subgroup G, Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) → oddCoreIn H ≤ Y →
            Y = oddCoreIn H ∨ Y = H) ∧
          ∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.D ≤ Subgroup.normalizer (X : Set G) →
            ∃ T₁ : Subgroup G, T₁ ≤ σ.D ∧ IsKleinFour T₁ ∧ ⁅X, T₁⁆ ≤ oddCoreIn H) ∨
        (σ.height = 1 ∧ ∃ q₁ : ℕ, 3 < q₁ ∧ IsLinearTypeWrt σ.T H q₁)) :
    σ.PropIV91 := by
  intro r hr K hK
  have hrp : r.Prime := hr.prime
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hrp hr.dvd_ON
  have : Fact r.Prime := ⟨hrp⟩
  obtain ⟨P, hP, hPD⟩ := σ.exists_sylow_C_normalized hN.C_le_oddCore_sup_D hrp hr2
  obtain ⟨R, hR, hRD, hRP⟩ := σ.exists_sylow_ON_normalized hσ hrp hr2 hP.le hP.isPGroup hPD
  obtain ⟨d, -, -⟩ := σ.propIV71_of_IVNFacts hσ hII hN r hr P R hP hPD hR hRD hRP
  have h81 := σ.lemmaIV81 hσ hII
  have h83 := σ.lemmaIV83 hσ hII
  have hPQ : d.P ≤ Subgroup.normalizer (d.Q : Set G) := by
    have := d.Q_characteristic
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer d.Q_le).mp inferInstance
  by_cases hc : σ.Constrained r
  · by_cases hQ : PConstrainedWithin r (Subgroup.normalizer (d.Q : Set G))
        (CFSG.oddCore (Subgroup.normalizer (d.Q : Set G)))
    · exact σ.constrained_of_exists_constrained hσ hII h_II54 hrp hr2
        ⟨_, σ.normalizer_Q_mem_familyMstar hr d h81 h83, hQ, d.P, d.P_sylow, d.P_D, hPQ⟩ hK
    · have h92 : ∀ K ∈ σ.familyMstar r, PConstrainedWithin r K (CFSG.oddCore K) ↔
          ∃ X : Subgroup G, IsSylowOf r X (oddCoreIn K) ∧
            σ.T ≤ Subgroup.normalizer (X : Set G) ∧ ¬ σ.T ≤ Subgroup.centralizer (X : Set G) :=
        fun K hK => σ.constrained_iff_exists_sylow_not_centralized hσ hII hrp hr2 hK
      exact absurd (σ.lemmaIV95_i hσ hII hr d hc hQ h81 h83 h92 h_II34).1 hh
  · exact σ.familyMstar_constrained_of_not_constrained hσ hII (σ.lemmaIV33 hσ hII) h81 h83 h_II54
      hr hc d hK

end Setting

end CFSG.ABGTheoremB
