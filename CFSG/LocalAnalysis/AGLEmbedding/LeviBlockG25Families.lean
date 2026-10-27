module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeSetup
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniData
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockL33Orders
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSmall
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockPerfectCoreThreeLie
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusTypes
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympHas
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique

@[expose] def IsG25Order (n : ℕ) : Prop :=
  n = 5859000000

@[expose] def NoG25At {Y : Type} [Group Y] [Finite Y] (P : Subgroup Y) : Prop :=
  ∀ (O W : Subgroup Y), O ≤ P → P ≤ Subgroup.normalizer (O : Set Y) →
    Nat.Coprime 3 (Nat.card O) → W ≤ P →
    P ≤ Subgroup.normalizer ((W ⊔ O : Subgroup Y) : Set Y) → ⁅W, W⁆ = W →
    ∀ (U : Type) [Group U] [Finite U] [IsSimpleGroup U] (ψ : ↥W →* U),
      Function.Surjective ψ → ¬ IsG25Order (Nat.card U)

@[expose] def KFactCompParabNoG25 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P → NoG25At P

@[expose] def KFactCompParabNoG25On (C : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    C (↥L ⧸ Subgroup.center ↥L) → NoG25At P

namespace LeviBlock

theorem three_dvd_of_isG25Order {n : ℕ} (h : IsG25Order n) : 3 ∣ n := by
  rw [h]
  norm_num

theorem not_dvd_two_pow_mul_factorial_of_isG25Order {a n m : ℕ} (hn : n ≤ 11)
    (hm : IsG25Order m) : ¬ m ∣ 2 ^ a * n.factorial := by
  intro h
  have h31 : 31 ∣ m := by
    rw [hm]
    norm_num
  have hcop : Nat.Coprime 31 (2 ^ a) := by
    have h0 : Nat.Coprime 31 2 :=
      (Nat.coprime_primes (by norm_num) (by norm_num)).mpr (by norm_num)
    simpa using h0.pow_right a
  have h31n : 31 ∣ Nat.factorial n := hcop.dvd_of_dvd_mul_left (h31.trans h)
  have h31le : 31 ≤ n := (Nat.Prime.dvd_factorial (by norm_num)).mp h31n
  omega

theorem ordA_not_isG25Order {n q f : ℕ} (hq : q = 2 ^ f) :
    ¬ IsG25Order (ordA n q) := by
  rintro h
  refine ordA_false_of_two_part (n := n) hq (e := 6) (m := 91546875) (by norm_num)
    (by norm_num) (h.trans (by norm_num)) ?_
  intro n' f' h1 h2 h3
  interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordA; decide)

theorem ordTwistedA_not_isG25Order {n q f : ℕ} (hq : q = 2 ^ f) :
    ¬ IsG25Order (ordTwistedA n q) := by
  rintro h
  refine ordTwistedA_false_of_two_part (n := n) hq (e := 6) (m := 91546875)
    (by norm_num) (by norm_num) (h.trans (by norm_num)) ?_
  intro n' f' h1 h2 h3
  interval_cases n' <;> interval_cases f' <;>
    first | omega | (unfold ordTwistedA; decide)

theorem ordBC_not_isG25Order {n q f : ℕ} (hq : q = 2 ^ f) :
    ¬ IsG25Order (ordBC n q) := by
  rintro h
  refine ordBC_false_of_two_part (n := n) hq (e := 6) (m := 91546875) (by norm_num)
    (by norm_num) (h.trans (by norm_num)) ?_
  intro n' f' h1 h2 h3
  interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordBC; decide)

theorem ordD_not_isG25Order {n q f : ℕ} (hq : q = 2 ^ f) :
    ¬ IsG25Order (ordD n q) := by
  rintro h
  refine ordD_false_of_two_part (n := n) hq (e := 6) (m := 91546875) (by norm_num)
    (by norm_num) (h.trans (by norm_num)) ?_
  intro n' f' h1 h2 h3
  interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordD; decide)

theorem ordTwistedD_not_isG25Order {n q f : ℕ} (hq : q = 2 ^ f) :
    ¬ IsG25Order (ordTwistedD n q) := by
  rintro h
  refine ordTwistedD_false_of_two_part (n := n) hq (e := 6) (m := 91546875)
    (by norm_num) (by norm_num) (h.trans (by norm_num)) ?_
  intro n' f' h1 h2 h3
  interval_cases n' <;> interval_cases f' <;>
    first | omega | (unfold ordTwistedD; decide)

theorem card_alternatingGroup_not_isG25Order (n : ℕ) :
    ¬ IsG25Order (Nat.card (alternatingGroup (Fin n))) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have h1 : Nat.card (alternatingGroup (Fin n)) = 1 := by
      rw [Nat.card_eq_fintype_card]
      refine Fintype.card_eq_one_iff.mpr ⟨⟨1, Subgroup.one_mem _⟩, ?_⟩
      intro a
      exact Subtype.ext (Equiv.ext fun x => by
        interval_cases n
        · exact x.elim0
        · exact Subsingleton.elim _ _)
    rw [h1]
    rintro h
    change (1 : ℕ) = 5859000000 at h
    omega
  · haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    have hAc := nat_card_alternatingGroup (α := Fin n)
    rw [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at hAc
    rw [hAc]
    rcases Nat.lt_or_ge n 14 with hlt | hge
    · interval_cases n
      all_goals
        unfold IsG25Order
        decide
    · have hmono : (14 : ℕ).factorial / 2 ≤ n.factorial / 2 :=
        Nat.div_le_div_right (Nat.factorial_le hge)
      have h14 : ((14 : ℕ).factorial / 2) = 43589145600 := by decide
      rw [h14] at hmono
      rintro h
      change Nat.factorial n / 2 = 5859000000 at h
      omega

theorem not_isG25Order_of_mem_linBlockOrders {f : ℕ} (hf : 1 ≤ f) :
    ∀ n ∈ linBlockOrders (GaloisField 2 f), ¬ IsG25Order n := by
  rintro n ⟨m, -, rfl⟩
  exact ordA_not_isG25Order (f := f) (GaloisField.card 2 f (by omega))

theorem not_isG25Order_of_mem_uniBlockOrders (f s ε : ℕ) :
    ∀ n ∈ uniBlockOrders f s ε, ¬ IsG25Order n := by
  rintro n (⟨k, rfl⟩ | rfl)
  · exact ordA_not_isG25Order (q := (2 ^ f) ^ 2) (f := 2 * f)
      (by rw [← pow_mul, Nat.mul_comm])
  · exact ordTwistedA_not_isG25Order rfl

theorem not_isG25Order_of_mem_spBlockOrders {q f : ℕ} (hq : q = 2 ^ f) :
    ∀ n ∈ spBlockOrders q, ¬ IsG25Order n := by
  rintro n (⟨k, rfl⟩ | ⟨m, rfl⟩ | rfl)
  · exact ordA_not_isG25Order hq
  · exact ordBC_not_isG25Order hq
  · rintro h
    change (360 : ℕ) = 5859000000 at h
    omega

theorem not_isG25Order_of_mem_plusBlockOrders {q f : ℕ} (hq : q = 2 ^ f) :
    ∀ n ∈ plusBlockOrders q, ¬ IsG25Order n := by
  rintro n (⟨k, -, rfl⟩ | ⟨m, -, rfl⟩)
  · exact ordA_not_isG25Order hq
  · exact ordD_not_isG25Order hq

theorem not_isG25Order_of_mem_orthMinusBlockOrders {f : ℕ} :
    ∀ n ∈ orthMinusBlockOrders (2 ^ f), ¬ IsG25Order n := by
  rintro n (⟨k, -, rfl⟩ | ⟨m, -, rfl⟩)
  · exact ordA_not_isG25Order rfl
  · exact ordTwistedD_not_isG25Order rfl

end LeviBlock

theorem noG25At_of_levi {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hPL : P ≤ L)
    (h : ∃ (K : Type) (_ : Group K) (_ : Finite K) (ρ : K →* ↥L) (𝒯 : Set ℕ),
      Function.Surjective ρ ∧ HasLeviBlocks ↥((P.subgroupOf L).comap ρ) 𝒯 ∧
        ∀ n ∈ 𝒯, ¬ IsG25Order n) :
    NoG25At P := by
  intro O W hOP hPO hO3 hWP hPWO _ U _ _ _ ψ hψ hU
  exfalso
  obtain ⟨K, _, _, ρ, 𝒯, hρ, hQ, h𝒯⟩ := h
  have h3U : 3 ∣ Nat.card U := LeviBlock.three_dvd_of_isG25Order hU
  have hnc : ∃ a b : U, a * b ≠ b * a := by
    refine ThreeFives.exists_noncomm_of_simple inferInstance ?_
    rw [hU]
    norm_num
  have := card_mem_of_section hPL ρ hρ hQ hOP hPO hO3 hWP hPWO hnc h3U ψ hψ
  exact h𝒯 _ this hU

theorem kFactCompParabNoG25On_linear
    (hGA : GriessAllModelsStatement) :
    KFactCompParabNoG25On (IsLieOf IdxA) := by
  intro Y _ _ L P hCP hA
  obtain ⟨n, f, ρ, -, I, hn, hf, hρs, -, -, -, -, -, hcomap⟩ :=
    ToralCensus.exists_cover_comap_eq_flagStabilizer hGA hCP hA
  have hQ : HasLeviBlocks ↥((P.subgroupOf L).comap ρ) (linBlockOrders (GaloisField 2 f)) :=
    hcomap ▸ hasLeviBlocks_flagStabilizer (by omega) I
  exact noG25At_of_levi hCP.parab.1 ⟨_, inferInstance, inferInstance, ρ, _,
    hρs, hQ, LeviBlock.not_isG25Order_of_mem_linBlockOrders hf⟩

theorem kFactCompParabNoG25On_twistedA :
    KFactCompParabNoG25On (IsLieOf IdxTwistedA) := by
  intro Y _ _ L P hCP hC
  obtain ⟨d, hd, ⟨e⟩⟩ := hC
  obtain ⟨K, _, f, t, s, ε, h, ρ, I, g, hε, hI, hq, hρ, hJ⟩ :=
    exists_uniFlag_of_compParab hCP d hd e
  have : Finite K := h.finite
  exact noG25At_of_levi hCP.parab.1 ⟨_, inferInstance, inferInstance, ρ,
    uniBlockOrders f s ε, hρ, hasLeviBlocks_hypStab h hε hI g hJ,
    LeviBlock.not_isG25Order_of_mem_uniBlockOrders f s ε⟩

theorem kFactCompParabNoG25On_idxB (hZ : OddCenterRest) :
    KFactCompParabNoG25On (IsLieOf IdxB) := by
  intro Y _ _ L P hCP hB
  obtain ⟨K, _, _, ρ, f, hρ, hQ⟩ :=
    LocalAnalysis.RankThreeTheoremC.KFactProofs.exists_hasLeviBlocks_spBlockOrders_of_idxB hZ
      hCP hB
  exact noG25At_of_levi hCP.parab.1 ⟨K, inferInstance, inferInstance, ρ,
    LeviBlock.spBlockOrders (2 ^ f), hρ, hQ,
    LeviBlock.not_isG25Order_of_mem_spBlockOrders rfl⟩

theorem kFactCompParabNoG25On_idxD (hZ : OddCenterRest) :
    KFactCompParabNoG25On (IsLieOf IdxD) := by
  intro Y _ _ L P hCP hD
  obtain ⟨r, K, _, _, _, ρ, -, hQ, -⟩ := LeviBlock.exists_hasLeviBlocks_of_idxD hZ hCP hD
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact noG25At_of_levi hCP.parab.1 ⟨_, inferInstance,
    Finite.of_equiv _ ρ.symm.toEquiv, ρ.toMonoidHom, plusBlockOrders (Nat.card K),
    ρ.surjective, hQ,
    LeviBlock.not_isG25Order_of_mem_plusBlockOrders (q := Nat.card K) (f := n)
      (by rw [Nat.card_eq_fintype_card, hn])⟩

theorem kFactCompParabNoG25On_twistedD (hZ : OddCenterRest) :
    KFactCompParabNoG25On (IsLieOf IdxTwistedD) := by
  intro Y _ _ L P hCP hD
  obtain ⟨dI, hdI, ⟨e⟩⟩ := hD
  obtain ⟨K, _, _, ρ, f, hρ, hQ, -⟩ :=
    LeviBlock.exists_hasLeviBlocks_of_twistedD hZ hCP dI hdI e
  exact noG25At_of_levi hCP.parab.1 ⟨K, inferInstance, inferInstance, ρ,
    orthMinusBlockOrders (2 ^ f), hρ, hQ,
    LeviBlock.not_isG25Order_of_mem_orthMinusBlockOrders⟩

theorem kFactCompParabNoG25On_g2
    (hGA : GriessAllModelsStatement) :
    KFactCompParabNoG25On (IsLieOf IdxG2) := by
  intro Y _ _ L P hCP hG
  obtain ⟨K, _, _, ρ, f, hρ, hQ⟩ := hasLeviBlocks_g2 hGA hCP hG
  refine noG25At_of_levi hCP.parab.1 ⟨_, inferInstance, inferInstance, ρ,
    {ordA 1 (2 ^ f)}, hρ, hQ, ?_⟩
  intro n hn
  rw [Set.mem_singleton_iff] at hn
  subst hn
  exact LeviBlock.ordA_not_isG25Order (n := 1) (f := f) rfl

theorem kFactCompParabNoG25_small : KFactCompParabNoG25On IsSmallTwoOrG2 := by
  intro Y _ _ L P hCP hS O W hOP hPO hO3 hWP hPWO _ U _ _ _ ψ hψ hU
  exfalso
  have h2 : 2 ∣ Nat.card U := by
    rw [hU]
    norm_num
  have h1 := LeviBlock.card_dvd_card_centerQuotient (hWP.trans hCP.parab.1) hCP.odd h2 ψ hψ
  rcases LeviBlock.card_small_cases hS with h | h | h | h | h
  all_goals rw [h] at h1
  all_goals rw [hU] at h1
  all_goals norm_num at h1

end CFSG.AGLEmbedding
