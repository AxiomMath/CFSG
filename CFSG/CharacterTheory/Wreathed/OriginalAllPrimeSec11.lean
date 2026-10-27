module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeSec11Model
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalInputsSection
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeTIFactsModel

public section

namespace CFSG.Wreathed.OriginalAllPrime

open Matrix CFSG.ABGTheoremB CFSG.ABGTheoremB.TotallyInverted
open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2

namespace Sec11W

section Transport

variable {G : Type} [Group G] {σ : Setting G} {H : Type} [Group H]
  {φ : σ.N →* H} {M : Subgroup H} {y : H} {J : Subgroup G}

theorem injective_comp_inclusion [Finite G] (hφ : TIFacts.IsModelMap σ φ M y) {Y : Subgroup G}
    (hYN : Y ≤ σ.N) (hY : IsPGroup 2 Y) :
    Function.Injective (φ.comp (Subgroup.inclusion hYN)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hker : Subgroup.inclusion hYN g ∈ φ.ker := hg
  rw [hφ.ker_eq, Subgroup.mem_subgroupOf] at hker
  obtain ⟨k, hk⟩ := hY g
  have h1 : orderOf (g : G) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf (g : G) ∣ Nat.card σ.ON := Subgroup.orderOf_dvd_natCard σ.ON hker
  have hcop : Nat.Coprime (2 ^ k) (Nat.card σ.ON) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr σ.odd_card_ON)
  have h3 : orderOf (g : G) = 1 := Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h1) h2
  exact Subtype.ext (orderOf_eq_one_iff.mp h3)

theorem map_le_and_card (hφ : TIFacts.IsModelMap σ φ M y) (hJ : σ.IsLayerComplement J)
    {Q : Subgroup G} (hQJ : Q ≤ J) :
    (Q.subgroupOf σ.N).map φ ≤ M ∧ Nat.card ((Q.subgroupOf σ.N).map φ) = Nat.card Q := by
  refine ⟨?_, hφ.card_map hJ hQJ⟩
  rw [← hφ.map_J hJ]
  exact Subgroup.map_mono (TIFacts.subgroupOf_mono_of_le hQJ σ.N)

theorem isCyclic_of_le_centralizer_of_model [Finite G] (hφ : TIFacts.IsModelMap σ φ M y)
    (hJ : σ.IsLayerComplement J) {q : ℕ}
    (hmodel : ∀ P : Subgroup H, P ≤ M → Nat.card P = q → ∀ X : Subgroup H, IsPGroup 2 X →
      X ≤ Subgroup.centralizer (P : Set H) → IsCyclic X)
    {Q : Subgroup G} (hQJ : Q ≤ J) (hQ : Nat.card Q = q) {Y : Subgroup G} (hYN : Y ≤ σ.N)
    (hY : IsPGroup 2 Y) (hYQ : Y ≤ Subgroup.centralizer (Q : Set G)) : IsCyclic Y := by
  obtain ⟨hPM, hP⟩ := map_le_and_card hφ hJ hQJ
  have hψ := injective_comp_inclusion hφ hYN hY
  have hX : IsPGroup 2 (φ.comp (Subgroup.inclusion hYN)).range :=
    hY.of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have hXP : (φ.comp (Subgroup.inclusion hYN)).range ≤
      Subgroup.centralizer (((Q.subgroupOf σ.N).map φ : Subgroup H) : Set H) := by
    rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp (hYQ g.2) u (Subgroup.mem_subgroupOf.mp hu)
    rw [MonoidHom.comp_apply, ← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hc)
  have := hmodel _ hPM (hP.trans hQ) _ hX hXP
  exact isCyclic_of_injective (φ.comp (Subgroup.inclusion hYN)).rangeRestrict
    (MonoidHom.rangeRestrict_injective_iff.mpr hψ)

theorem not_le_centralizer_of_model (hφ : TIFacts.IsModelMap σ φ M y)
    (hJ : σ.IsLayerComplement J) {q : ℕ} {w : H} (hwM : w ∈ M) (hwy : w * y = y * w)
    (hw : ∀ P : Subgroup H, P ≤ M → Nat.card P = q → w ∉ Subgroup.centralizer (P : Set H))
    {Q : Subgroup G} (hQJ : Q ≤ J) (hQ : Nat.card Q = q) :
    ¬ (σ.C ⊓ J ≤ Subgroup.centralizer (Q : Set G)) := by
  intro hle
  obtain ⟨hPM, hP⟩ := map_le_and_card hφ hJ hQJ
  apply hw _ hPM (hP.trans hQ)
  rw [← hφ.map_J hJ] at hwM
  obtain ⟨j, hj, rfl⟩ := hwM
  have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.mp hj
  have hjc := hφ.commute_of_mem_J hJ hjJ hwy
  have hjC : (j : G) ∈ σ.C := (TIFacts.mem_C_iff σ j.2).mpr (congrArg Subtype.val hjc)
  have hjQ := hle ⟨hjC, hjJ⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨u, hu, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.mp hjQ u (Subgroup.mem_subgroupOf.mp hu)
  rw [← map_mul, ← map_mul]
  exact congrArg φ (Subtype.ext hc)

end Transport

theorem wreathedSetting_ABG_II_4_4_and_II_4_10_iii
    {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    {r : ℕ} (Δ : Data (wreathedSetting n S e p f) r) :
    Sec11.ABG_II_4_4 Δ ∧ Sec11.ABG_II_4_10_iii Δ := by
  have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  obtain ⟨F, hfield, hfinite, Sigma, b, hSigma, ρ, Ψ, hdata⟩ :=
    exists_conditionalCompatibleModelData hnonab n hn S e hfour p f hp hp2 hf hlocal
  let : Field F := hfield
  let : Finite F := hfinite
  obtain ⟨h, hh⟩ := TIFacts.exists_liftMap_eq_modelY hnonab hfour hp hpodd hf hlocal hdata
  have hφ := TIFacts.liftMap_isModelMap hnonab hfour hp hpodd hf hlocal hdata hh
  have hJ (hδq : (wreathedSetting n S e p f).DeltaEpsMinus ∧ r ∣ (wreathedSetting n S e p f).q) :
      (wreathedSetting n S e p f).IsLayerComplement Δ.J :=
    ⟨Δ.J_le, Δ.L₀_eq, Sec11.J_inf_ON Δ hδq, Δ.J_normal, Δ.J_centralizes⟩
  refine ⟨fun hδq Y hYN hY hYQ => ?_, fun hδq => ?_⟩
  · have hmp : Nat.Coprime (2 ^ n) p :=
      ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).pow_left n
    have hmodel : ∀ P : Subgroup (SemilinearExtension F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn) Sigma hSigma),
        P ≤ ModelSignalizers.modelLayer b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
          Sigma hSigma → Nat.card P = p ^ f →
        ∀ X : Subgroup (SemilinearExtension F b (2 ^ n) (wreathModulus_pos n)
          (wreathModulus_even hn) Sigma hSigma), IsPGroup 2 X →
            X ≤ Subgroup.centralizer (P : Set (SemilinearExtension F b (2 ^ n)
              (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma)) → IsCyclic X :=
      fun P hPM hP X hX hXP => isCyclic_of_le_centralizer hp hp2 hdata.card hdata.nonsquare hmp
        hPM (hP.trans hdata.card.symm) hX hXP
    rcases hYQ with hYQ | hYQ
    · exact isCyclic_of_le_centralizer_of_model hφ (hJ hδq) hmodel (Sec11.Q_zero_le_J Δ)
        (Sec11.card_Q Δ hδq 0) hYN hY hYQ
    · exact isCyclic_of_le_centralizer_of_model hφ (hJ hδq) hmodel (Sec11.Qs_zero_le_J Δ)
        (Sec11.card_Qs Δ hδq 0) hYN hY hYQ
  · have hq4 : p ^ f % 4 = 1 := by
      rcases hδq.1 with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 (show n ≠ 1 by omega)
      · exact h2
    have h2F : (2 : F) ≠ 0 := two_ne_zero_of_not_isSquare hdata.nonsquare
    let : Fintype F := Fintype.ofFinite F
    obtain ⟨i, hi⟩ : IsSquare (-1 : F) := FiniteField.isSquare_neg_one_iff.mpr (by
      rw [Fintype.card_eq_nat_card, hdata.card]
      omega)
    have hTcard := OddFieldTorus.torus_card_split h2F i hi.symm
    have := OddFieldTorus.torus_isCyclic h2F
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := OddFieldTorus.torus F)
    have ht : orderOf (g : SpecialLinearGroup (Fin 2) F) = Nat.card F - 1 := by
      rw [Subgroup.orderOf_coe, hg, hTcard]
    have hwM : (SemidirectProduct.inl (specialInclusion F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn) g) : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n)
          (wreathModulus_even hn) Sigma hSigma) ∈
        ModelSignalizers.modelLayer b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
          Sigma hSigma :=
      ⟨_, ⟨g, rfl⟩, rfl⟩
    have hwy : (SemidirectProduct.inl (specialInclusion F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn) g) : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n)
          (wreathModulus_even hn) Sigma hSigma) *
        ModelSignalizers.modelY b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
          hSigma =
        ModelSignalizers.modelY b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
          hSigma * SemidirectProduct.inl (specialInclusion F b (2 ^ n) (wreathModulus_pos n)
            (wreathModulus_even hn) g) := by
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp
        ((ReducedInvolution.specialInclusion_mem_centralizer_iff (b := b)
          (hm := wreathModulus_pos n) (heven := wreathModulus_even hn)
          (g : SpecialLinearGroup (Fin 2) F)).mpr g.2)
      change _ * SemidirectProduct.inl (involutionY F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn)) = SemidirectProduct.inl (involutionY F b (2 ^ n)
          (wreathModulus_pos n) (wreathModulus_even hn)) * _
      rw [← map_mul, ← map_mul, h1]
    have h3 : 3 < Nat.card F := by
      rw [hdata.card]
      omega
    have hw : ∀ P : Subgroup (SemilinearExtension F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn) Sigma hSigma),
        P ≤ ModelSignalizers.modelLayer b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
          Sigma hSigma → Nat.card P = p ^ f →
        SemidirectProduct.inl (specialInclusion F b (2 ^ n) (wreathModulus_pos n)
          (wreathModulus_even hn) g) ∉ Subgroup.centralizer (P : Set (SemilinearExtension F b
            (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma)) :=
      fun P hPM hP => not_mem_centralizer_of_orderOf hp hdata.card h3 hPM
        (hP.trans hdata.card.symm) ht
    exact ⟨not_le_centralizer_of_model hφ (hJ hδq) hwM hwy hw (Sec11.Q_zero_le_J Δ)
        (Sec11.card_Q Δ hδq 0),
      not_le_centralizer_of_model hφ (hJ hδq) hwM hwy hw (Sec11.Qs_zero_le_J Δ)
        (Sec11.card_Qs Δ hδq 0)⟩

end Sec11W

theorem wreathedSetting_sec11Inputs
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    {r : ℕ} (Δ : CFSG.ABGTheoremB.TotallyInverted.Data (wreathedSetting n S e p f) r) :
    CFSG.ABGTheoremB.TotallyInverted.Sec11.Inputs Δ := by
  obtain ⟨h44, h410⟩ := Sec11W.wreathedSetting_ABG_II_4_4_and_II_4_10_iii hnonab n hn S e hfour
    p f hp hpodd hf hq hlocal Δ
  exact ⟨h44, h410, Sec11.abg_II_4_18_of
    (wreathedSetting_isValid hnonab n hn S e hfour p f hp hpodd hf hq hlocal) Δ⟩

end CFSG.Wreathed.OriginalAllPrime
