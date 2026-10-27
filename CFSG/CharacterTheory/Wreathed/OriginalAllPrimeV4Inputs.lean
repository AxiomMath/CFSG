module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeV4InputsTransport
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeIVFacts

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.ABGTheoremB

variable {G : Type} [Group G]

namespace V4InputsW

theorem four_dvd_two_pow {n : ℕ} (hn : 2 ≤ n) : 4 ∣ 2 ^ n := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact pow_dvd_pow 2 hn

theorem wreathedSetting_exists_mul_self_eq_x₂ (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    ∃ c ∈ (wreathedSetting n S e p f).D, c * c = (wreathedSetting n S e p f).x₂ := by
  refine ⟨wreathModelHom S e (Original.s (2 ^ n) ^ (2 ^ n / 4)), ?_, ?_⟩
  · rw [wreathedSetting_D_eq n (by omega) S e p f]
    exact (e.symm _).property
  · change wreathModelHom S e _ * wreathModelHom S e _ = wreathModelHom S e (Original.x2 (2 ^ n))
    rw [← map_mul, ← pow_add, Original.x2]
    obtain ⟨k, hk⟩ := four_dvd_two_pow hn
    congr 2
    omega

end V4InputsW

variable [Finite G] [IsSimpleGroup G]

theorem wreathedSetting_lemmaII42Input
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∀ J : Subgroup G, (wreathedSetting n S e p f).IsV21Layer J →
      CFSG.ABGTheoremB.V4.LemmaII42Input (wreathedSetting n S e p f) J := by
  intro J hJ
  obtain ⟨F, _, _, Sigma, b, hSigma, φ, hW⟩ :=
    IVFacts.wreathedSetting_exists_isWModel hnonab n hn S e hfour p f hp hpodd hf hlocal
  exact V4InputsW.lemmaII42Input_of_isWModel hW
    (wreathedSetting_isValid hnonab n hn S e hfour p f hp hpodd hf hq hlocal)
    (wreathedSetting_C_odd_le_oddCore n hn S e p f) hJ

theorem wreathedSetting_lemmaII46Input
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∀ J : Subgroup G, (wreathedSetting n S e p f).IsV21Layer J →
      CFSG.ABGTheoremB.V4.LemmaII46Input (wreathedSetting n S e p f) J := by
  intro J hJ
  obtain ⟨F, _, _, Sigma, b, hSigma, φ, hW⟩ :=
    IVFacts.wreathedSetting_exists_isWModel hnonab n hn S e hfour p f hp hpodd hf hlocal
  exact V4InputsW.lemmaII46Input_of_isWModel hW
    (wreathedSetting_isValid hnonab n hn S e hfour p f hp hpodd hf hq hlocal) hJ

theorem wreathedSetting_lemmaII49Input
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∀ J : Subgroup G, (wreathedSetting n S e p f).IsV21Layer J →
      CFSG.ABGTheoremB.V4.LemmaII49Input (wreathedSetting n S e p f) J := by
  intro J _ W _ Y hYN hY hDY _
  obtain ⟨F, _, _, Sigma, b, hSigma, φ, hW⟩ :=
    IVFacts.wreathedSetting_exists_isWModel hnonab n hn S e hfour p f hp hpodd hf hlocal
  exact V4InputsW.le_C_sup_ON_of_odd hW (V4InputsW.four_dvd_two_pow hn)
    (V4InputsW.wreathedSetting_exists_mul_self_eq_x₂ n hn S e p f) hYN hY hDY

theorem wreathedSetting_x₂_commutator_mem_ON
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∀ X : Subgroup G, X ≤ (wreathedSetting n S e p f).N →
      IsPGroup (wreathedSetting n S e p f).p X →
      (wreathedSetting n S e p f).D ≤ Subgroup.normalizer (X : Set G) →
      ∀ y ∈ X, (wreathedSetting n S e p f).x₂ * y * (wreathedSetting n S e p f).x₂⁻¹ * y⁻¹ ∈
        (wreathedSetting n S e p f).ON := by
  intro X hXN hX hDX y hy
  obtain ⟨F, _, _, Sigma, b, hSigma, φ, hW⟩ :=
    IVFacts.wreathedSetting_exists_isWModel hnonab n hn S e hfour p f hp hpodd hf hlocal
  exact V4InputsW.x₂_commutator_mem_ON hW (V4InputsW.four_dvd_two_pow hn)
    (V4InputsW.wreathedSetting_exists_mul_self_eq_x₂ n hn S e p f) hXN hX hDX hy

end CFSG.Wreathed.OriginalAllPrime
