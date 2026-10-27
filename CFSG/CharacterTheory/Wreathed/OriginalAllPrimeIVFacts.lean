module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeIVFactsSylow
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeIVFactsSection
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeIVFactsPropIV51
public import CFSG.LocalAnalysis.ABGTheoremB.IVNFacts

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion

variable {G : Type} [Group G] [Finite G]

section Basic

theorem wreathedSetting_C_odd_le_oddCore (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    ∀ c ∈ (wreathedSetting n S e p f).C, Odd (orderOf c) →
      c ∈ oddCoreIn (wreathedSetting n S e p f).C :=
  IVFacts.wreath_C_odd_le_oddCore n hn S e p f

theorem wreathedSetting_C_le_oddCore_sup_D (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    (wreathedSetting n S e p f).C ≤
      oddCoreIn (wreathedSetting n S e p f).C ⊔ (wreathedSetting n S e p f).D :=
  IVFacts.wreath_C_le_oddCore_sup_D n hn S e p f

omit [Finite G] in
theorem wreathedSetting_sylow_quaternion_element (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    ∃ y ∈ ((wreathedSetting n S e p f).S : Subgroup G),
      y ∉ centerOf ((wreathedSetting n S e p f).S : Subgroup G) ∧
      ∀ X : Subgroup G, X ≤ (wreathedSetting n S e p f).S →
        ((wreathedSetting n S e p f).S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) →
          (∃ Q : Subgroup G, Q ≤ X ∧ Nonempty (Q ≃* QuaternionGroup 2)) → y ∈ X :=
  IVFacts.wreath_quaternion_element n hn S e p f

end Basic

variable [IsSimpleGroup G]

theorem wreathedSetting_L_normal
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    (wreathedSetting n S e p f).N ≤
      Subgroup.normalizer ((wreathedSetting n S e p f).L : Set G) := by
  obtain ⟨F, _, _, Sigma, b, hSigma, φ, hW⟩ :=
    IVFacts.wreathedSetting_exists_isWModel hnonab n hn S e hfour p f hp hpodd hf hlocal
  exact hW.L_normal

theorem wreathedSetting_N_mod_L_cyclic
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∃ g ∈ (wreathedSetting n S e p f).N, ∀ x ∈ (wreathedSetting n S e p f).N,
      ∃ k : ℤ, x * (g ^ k)⁻¹ ∈ (wreathedSetting n S e p f).L := by
  obtain ⟨F, _, _, Sigma, b, hSigma, φ, hW⟩ :=
    IVFacts.wreathedSetting_exists_isWModel hnonab n hn S e hfour p f hp hpodd hf hlocal
  exact hW.N_mod_L_cyclic

theorem wreathedSetting_C_inf_L_commutator
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ⁅(wreathedSetting n S e p f).C ⊓ (wreathedSetting n S e p f).L,
        (wreathedSetting n S e p f).C ⊓ (wreathedSetting n S e p f).L⁆ ≤
      solvRadIn (wreathedSetting n S e p f).L := by
  obtain ⟨F, _, _, Sigma, b, hSigma, φ, hW⟩ :=
    IVFacts.wreathedSetting_exists_isWModel hnonab n hn S e hfour p f hp hpodd hf hlocal
  exact hW.C_inf_L_commutator

theorem wreathedSetting_exists_inverting_D_L₀
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∃ d ∈ (wreathedSetting n S e p f).D, d ∈ (wreathedSetting n S e p f).L₀ ∧
      ∀ c ∈ (wreathedSetting n S e p f).C ⊓ (wreathedSetting n S e p f).L₀,
        Odd (orderOf c) → d * c * d⁻¹ * c ∈ (wreathedSetting n S e p f).ON := by
  obtain ⟨F, _, _, Sigma, b, hSigma, φ, hW⟩ :=
    IVFacts.wreathedSetting_exists_isWModel hnonab n hn S e hfour p f hp hpodd hf hlocal
  exact hW.exists_inverting_D_L₀

theorem wreathedSetting_C_inf_L₀_commutator
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ⁅(wreathedSetting n S e p f).C ⊓ (wreathedSetting n S e p f).L₀,
        (wreathedSetting n S e p f).C ⊓ (wreathedSetting n S e p f).L₀⁆ ≤
      (wreathedSetting n S e p f).ON := by
  obtain ⟨F, _, _, Sigma, b, hSigma, φ, hW⟩ :=
    IVFacts.wreathedSetting_exists_isWModel hnonab n hn S e hfour p f hp hpodd hf hlocal
  exact hW.C_inf_L₀_commutator

theorem wreathedSetting_center_le_L_or_inf_L_le
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card (wreathedSetting n S e p f).ON → ∀ P : Subgroup G,
      IsSylowOf r P (wreathedSetting n S e p f).C →
        (wreathedSetting n S e p f).D ≤ Subgroup.normalizer (P : Set G) →
          centerOf P ≤ (wreathedSetting n S e p f).L ∨
            P ⊓ (wreathedSetting n S e p f).L ≤ (wreathedSetting n S e p f).ON := by
  obtain ⟨F, _, _, Sigma, b, hSigma, φ, hW⟩ :=
    IVFacts.wreathedSetting_exists_isWModel hnonab n hn S e hfour p f hp hpodd hf hlocal
  exact hW.center_le_L_or_inf_L_le

theorem wreathedSetting_centralizer_SL2_section
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card (wreathedSetting n S e p f).ON → ∀ P : Subgroup G,
      IsSylowOf r P (wreathedSetting n S e p f).C →
        (wreathedSetting n S e p f).D ≤ Subgroup.normalizer (P : Set G) →
          ¬ centerOf P ≤ (wreathedSetting n S e p f).L₀ →
            P ⊓ (wreathedSetting n S e p f).L ≤ (wreathedSetting n S e p f).ON →
              ∃ Λ : Subgroup G, (∀ l : G, l ∈ Λ ↔ l ∈ (wreathedSetting n S e p f).L₀ ∧
                  ∀ g ∈ P, g * l * g⁻¹ * l⁻¹ ∈ (wreathedSetting n S e p f).ON) ∧
                ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (m : ℕ), 1 < m ∧ Odd m ∧
                  (wreathedSetting n S e p f).q = Nat.card F₀ ^ m ∧
                  ∃ φ : Λ →* Matrix.SpecialLinearGroup (Fin 2) F₀, Function.Surjective φ ∧
                    φ.ker = (wreathedSetting n S e p f).ON.subgroupOf Λ := by
  obtain ⟨F, _, _, Sigma, b, hSigma, φ, hW⟩ :=
    IVFacts.wreathedSetting_exists_isWModel hnonab n hn S e hfour p f hp hpodd hf hlocal
  exact hW.centralizer_SL2_section

theorem wreathedSetting_L_centralizer_D_odd_le
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∀ y ∈ (wreathedSetting n S e p f).L,
      y ∈ Subgroup.centralizer ((wreathedSetting n S e p f).D : Set G) →
        Odd (orderOf y) → y ∈ (wreathedSetting n S e p f).ON := by
  obtain ⟨F, _, _, Sigma, b, hSigma, φ, hW⟩ :=
    IVFacts.wreathedSetting_exists_isWModel hnonab n hn S e hfour p f hp hpodd hf hlocal
  exact hW.L_centralizer_D_odd_le

theorem wreathedSetting_frobenius_section
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∀ r : ℕ, r.Prime → r ≠ 2 →
      ∀ w ∈ Subgroup.centralizer ((wreathedSetting n S e p f).D : Set G),
        (∃ k : ℕ, w ^ r ^ k = 1) → w ∉ (wreathedSetting n S e p f).L →
          w ^ r ∈ (wreathedSetting n S e p f).ON → ∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ r ∧
            ∃ K₀ : Subgroup G, (wreathedSetting n S e p f).ON ≤ K₀ ∧
              K₀ ≤ (wreathedSetting n S e p f).N ∧
              (wreathedSetting n S e p f).ON.relIndex K₀ = s ∧
              w ∈ Subgroup.normalizer (K₀ : Set G) ∧
              (∀ k ∈ K₀, (wreathedSetting n S e p f).x₂ * k *
                (wreathedSetting n S e p f).x₂⁻¹ * k ∈ (wreathedSetting n S e p f).ON) ∧
              ∀ k ∈ K₀, w * k * w⁻¹ * k⁻¹ ∈ (wreathedSetting n S e p f).ON →
                k ∈ (wreathedSetting n S e p f).ON := by
  obtain ⟨F, _, _, Sigma, b, hSigma, φ, hW⟩ :=
    IVFacts.wreathedSetting_exists_isWModel hnonab n hn S e hfour p f hp hpodd hf hlocal
  exact hW.frobenius_section

theorem wreathedSetting_oddCore_C_inf_L₀_cyclic
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∃ g ∈ (wreathedSetting n S e p f).N,
      oddCoreIn (wreathedSetting n S e p f).C ⊓ (wreathedSetting n S e p f).L₀ ≤
        Subgroup.zpowers g ⊔ (wreathedSetting n S e p f).ON := by
  obtain ⟨F, _, _, Sigma, b, hSigma, φ, hW⟩ :=
    IVFacts.wreathedSetting_exists_isWModel hnonab n hn S e hfour p f hp hpodd hf hlocal
  exact hW.oddCore_C_inf_L₀_cyclic

theorem wreathedSetting_oddCore_C_inf_L₀_coprime
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ¬ (wreathedSetting n S e p f).p ∣ (wreathedSetting n S e p f).ON.relIndex
      (oddCoreIn (wreathedSetting n S e p f).C ⊓ (wreathedSetting n S e p f).L₀) := by
  obtain ⟨F, _, _, Sigma, b, hSigma, φ, hW⟩ :=
    IVFacts.wreathedSetting_exists_isWModel hnonab n hn S e hfour p f hp hpodd hf hlocal
  exact hW.oddCore_C_inf_L₀_coprime

theorem wreathedSetting_oddCore_C_inf_L₀_centralized
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∀ c ∈ (wreathedSetting n S e p f).D ⊓
        Subgroup.centralizer ((wreathedSetting n S e p f).T : Set G),
      ∀ k ∈ oddCoreIn (wreathedSetting n S e p f).C ⊓ (wreathedSetting n S e p f).L₀,
        c * k * c⁻¹ * k⁻¹ ∈ (wreathedSetting n S e p f).ON := by
  obtain ⟨F, _, _, Sigma, b, hSigma, φ, hW⟩ :=
    IVFacts.wreathedSetting_exists_isWModel hnonab n hn S e hfour p f hp hpodd hf hlocal
  exact hW.oddCore_C_inf_L₀_centralized

theorem wreathedSetting_oddCore_C_inf_L₀_inverted
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∃ d ∈ (wreathedSetting n S e p f).D,
      d ∉ Subgroup.centralizer ((wreathedSetting n S e p f).T : Set G) ∧
        ∀ k ∈ oddCoreIn (wreathedSetting n S e p f).C ⊓ (wreathedSetting n S e p f).L₀,
          d * k * d⁻¹ * k ∈ (wreathedSetting n S e p f).ON := by
  obtain ⟨F, _, _, Sigma, b, hSigma, φ, hW⟩ :=
    IVFacts.wreathedSetting_exists_isWModel hnonab n hn S e hfour p f hp hpodd hf hlocal
  exact hW.oddCore_C_inf_L₀_inverted

theorem wreathedSetting_propIV51
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hII : (wreathedSetting n S e p f).ChapterIIFacts) :
    (wreathedSetting n S e p f).PropIV51 :=
  IVFacts.wreath_propIV51 hnonab n hn S e hfour p f hp hpodd hf hlocal hII

theorem wreathedSetting_ivNFacts
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hII : (wreathedSetting n S e p f).ChapterIIFacts) :
    (wreathedSetting n S e p f).IVNFacts where
  L_normal := wreathedSetting_L_normal hnonab n hn S e hfour p f hp hpodd hf hlocal
  C_odd_le_oddCore := wreathedSetting_C_odd_le_oddCore n hn S e p f
  C_le_oddCore_sup_D := wreathedSetting_C_le_oddCore_sup_D n hn S e p f
  N_mod_L_cyclic := wreathedSetting_N_mod_L_cyclic hnonab n hn S e hfour p f hp hpodd hf hlocal
  C_inf_L_commutator :=
    wreathedSetting_C_inf_L_commutator hnonab n hn S e hfour p f hp hpodd hf hlocal
  exists_inverting_D_L₀ :=
    wreathedSetting_exists_inverting_D_L₀ hnonab n hn S e hfour p f hp hpodd hf hlocal
  C_inf_L₀_commutator :=
    wreathedSetting_C_inf_L₀_commutator hnonab n hn S e hfour p f hp hpodd hf hlocal
  center_le_L_or_inf_L_le :=
    wreathedSetting_center_le_L_or_inf_L_le hnonab n hn S e hfour p f hp hpodd hf hlocal
  centralizer_SL2_section :=
    wreathedSetting_centralizer_SL2_section hnonab n hn S e hfour p f hp hpodd hf hlocal
  L_centralizer_D_odd_le :=
    wreathedSetting_L_centralizer_D_odd_le hnonab n hn S e hfour p f hp hpodd hf hlocal
  frobenius_section :=
    wreathedSetting_frobenius_section hnonab n hn S e hfour p f hp hpodd hf hlocal
  oddCore_C_inf_L₀_cyclic :=
    wreathedSetting_oddCore_C_inf_L₀_cyclic hnonab n hn S e hfour p f hp hpodd hf hlocal
  oddCore_C_inf_L₀_coprime :=
    wreathedSetting_oddCore_C_inf_L₀_coprime hnonab n hn S e hfour p f hp hpodd hf hlocal
  oddCore_C_inf_L₀_centralized :=
    wreathedSetting_oddCore_C_inf_L₀_centralized hnonab n hn S e hfour p f hp hpodd hf hlocal
  oddCore_C_inf_L₀_inverted :=
    wreathedSetting_oddCore_C_inf_L₀_inverted hnonab n hn S e hfour p f hp hpodd hf hlocal
  sylow_quaternion_element := wreathedSetting_sylow_quaternion_element n hn S e p f
  propIV51 := wreathedSetting_propIV51 hnonab n hn S e hfour p f hp hpodd hf hlocal hII

end CFSG.Wreathed.OriginalAllPrime
