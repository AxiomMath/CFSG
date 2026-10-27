module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockOmega
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaEightMinusAut

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactBlockThreeSolvableBeta : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L N₀ B : Subgroup G), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    N₀ ≤ B → B ≤ M ⊓ Subgroup.normalizer (S : Set G) →
    M ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (N₀ : Set G) →
    M ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (B : Set G) →
    Nat.Coprime 3 (Nat.card N₀) → (∀ b ∈ B, ∃ e : ℕ, b ^ 3 ^ e ∈ N₀) →
    (∀ k ∈ M ⊓ Subgroup.normalizer (S : Set G), ∃ e : ℕ, k ^ 2 ^ e ∈ B) →
    ∀ U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
        U ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) →
        (∀ u ∈ U, ∃ e : ℕ, u ^ 3 ^ e ∈
          Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) →
        ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈
          Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

theorem le_of_perfect_of_prime_pow_mem {X : Type*} [Group X] [Finite X] {W N : Subgroup X}
    {q : ℕ} [Fact q.Prime] (hWW : ⁅W, W⁆ = W) (hWN : W ≤ Subgroup.normalizer (N : Set X))
    (hpow : ∀ w ∈ W, ∃ e : ℕ, w ^ q ^ e ∈ N) : W ≤ N := by
  have : Group.IsPerfect W := Subgroup.isPerfect_iff.2 hWW
  have hN' : (N.subgroupOf W).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hWN
  have hp : IsPGroup q (W ⧸ N.subgroupOf W) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H w =>
      obtain ⟨e, he⟩ := hpow w w.2
      refine ⟨e, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact he
  have : Group.IsNilpotent (W ⧸ N.subgroupOf W) := hp.isNilpotent
  have hperf : Group.IsPerfect (W ⧸ N.subgroupOf W) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hsub : Subsingleton (W ⧸ N.subgroupOf W) := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable (W ⧸ N.subgroupOf W) inferInstance
  intro w hw
  have h1 : (QuotientGroup.mk ⟨w, hw⟩ : W ⧸ N.subgroupOf W) = 1 := Subsingleton.elim _ _
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (N := N.subgroupOf W) _).1 h1)

theorem kFactBlockThreeSolvable_of_beta (hβ : KFactBlockThreeSolvableBeta)
    (hOut : KFactBlockThreeOut) (h93 : Asc81bNineThree) : KFactBlockThreeSolvable := by
  intro G _ _ M S L N₀ B hK hA hL hX hSyl hN₀B hBK hNN₀ hNB hcop h3 h2
  refine ⟨hβ G M S L N₀ B hK hA hL hX hSyl hN₀B hBK hNN₀ hNB hcop h3 h2, ?_⟩
  refine hOut G M S L hK hA hL (h93 G M S L hK hA hL) hX hSyl ?_
  intro W hW hWW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLM : L ≤ M := hL.le
  have hWK : W ≤ barM M (M ⊓ Subgroup.normalizer (S : Set G)) :=
    hW.trans (Subgroup.map_mono (Subgroup.comap_mono (fun x hx => ⟨hLM hx.2, hx.1⟩)))
  have hWB : W ≤ barM M B := by
    refine le_of_perfect_of_prime_pow_mem (q := 2) hWW
      (hWK.trans (barM_le_normalizer_barM hNB)) ?_
    intro w hw
    obtain ⟨k, hk, rfl⟩ := hWK hw
    obtain ⟨e, he⟩ := h2 k hk
    exact ⟨e, ⟨k ^ 2 ^ e, by simpa [Subgroup.mem_subgroupOf] using he, by simp⟩⟩
  have hWN₀ : W ≤ barM M N₀ := by
    refine le_of_perfect_of_prime_pow_mem (q := 3) hWW
      (hWK.trans (barM_le_normalizer_barM hNN₀)) ?_
    intro w hw
    obtain ⟨b, hb, rfl⟩ := hWB hw
    obtain ⟨e, he⟩ := h3 b hb
    exact ⟨e, ⟨b ^ 3 ^ e, by simpa [Subgroup.mem_subgroupOf] using he, by simp⟩⟩
  have hdvd : Nat.card W ∣ Nat.card N₀ := by
    refine (Subgroup.card_dvd_of_le hWN₀).trans ((Subgroup.card_map_dvd _ _).trans ?_)
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (hN₀B.trans (hBK.trans inf_le_left))).toEquiv).dvd
  exact Nat.Coprime.coprime_dvd_right hdvd hcop

@[expose] def KFactOutFiveCyclicDvd : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L E Q : Subgroup Y), IsComponentOf L ⊤ →
    IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) → 5 ∣ Nat.card L →
    E ≤ Subgroup.normalizer (L : Set Y) →
    IsElemAbelian 5 E → Nat.card E = 5 ^ 2 →
    E ⊓ (L ⊔ Subgroup.centralizer (L : Set Y)) = ⊥ →
    Q ≤ Subgroup.normalizer (L : Set Y) → Q ≤ Subgroup.normalizer (E : Set Y) →
    (∀ F : Subgroup Y, F ≤ E → Q ≤ Subgroup.normalizer (F : Set Y) → F = ⊥ ∨ F = E) → False

theorem kFactOutFiveCyclic_of_dvd (hodd : KFactOutElemRankOdd) (h : KFactOutFiveCyclicDvd) :
    KFactOutFiveCyclic := by
  intro Y _ _ L E Q hL hcat hEN hE hcard hdisj hQL hQE hirr
  by_cases h5 : 5 ∣ Nat.card L
  · exact h Y L E Q hL hcat h5 hEN hE hcard hdisj hQL hQE hirr
  · have hEC : E ⊓ Subgroup.centralizer (L : Set Y) = ⊥ :=
      le_bot_iff.1 (hdisj ▸ inf_le_inf_left E le_sup_right)
    have := hodd Y L E hL hcat 5 Nat.prime_five (by norm_num) h5 hEN hE hEC
    rw [hcard] at this
    norm_num at this

@[expose] def OmegaEightMinusAutNoE81 : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), IsOmegaMinusTwoIndex 4 d →
    Nonempty (L ≃* CatGroup d) → ∀ E : Subgroup (MulAut L), IsElemAbelian 3 E →
      Nat.card E ≠ 3 ^ 4

theorem kFactOmegaEightMinusAutElemRank_of_noE81 (h : OmegaEightMinusAutNoE81) :
    KFactOmegaEightMinusAutElemRank := by
  intro L _ _ d hd he E hE
  have hp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have hdvd := kFactOmegaEightMinusAut L d hd he E hp
  obtain ⟨k, hk, hkE⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hk4 : k ≠ 4 := fun h4 => h L d hd he E hE (by rw [hkE, h4])
  rw [hkE]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.AGLEmbedding
