module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVTypes
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycSp
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalCoprimePreimages
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsSpTwo
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

namespace ToralReduce

section Perfect

variable {Y : Type*} [Group Y] [Finite Y]

theorem exists_perfect_isElemAbelian_of_surjective {J : Subgroup Y} {X : Type*} [Group X]
    (ψ : ↥J →* X) (hψ : Function.Surjective ψ) {B : Subgroup X} (hB : ⁅B, B⁆ = B)
    (hE : BlockCyc.HasE9 ↥B) : ∃ W : Subgroup Y, W ≤ J ∧ ⁅W, W⁆ = W ∧
      ∃ E : Subgroup Y, E ≤ W ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  have hBp : Group.IsPerfect B := Subgroup.isPerfect_iff.mpr hB
  set R₀ := perfectResidualOf (B.comap ψ)
  have hR₀ : R₀.map ψ = B := finite_canonical_perfect_preimage_image_eq ψ hψ B hBp
  have hR₀p : ⁅R₀, R₀⁆ = R₀ := Subgroup.isPerfect_iff.mp (finite_perfectResidualOf_isPerfect _)
  let ψR : ↥R₀ →* ↥B := (ψ.comp R₀.subtype).codRestrict B fun r => hR₀ ▸ ⟨r, r.2, rfl⟩
  have hψR : Function.Surjective ψR := by
    rintro ⟨b, hb⟩
    rw [← hR₀] at hb
    obtain ⟨r, hr, rfl⟩ := hb
    exact ⟨⟨r, hr⟩, rfl⟩
  obtain ⟨E₀, hE₀, hc⟩ := BlockCyc.hasE9_of_surjective hψR hE
  refine ⟨R₀.map J.subtype, Subgroup.map_subtype_le _, by
      rw [← Subgroup.map_commutator, hR₀p], (E₀.map R₀.subtype).map J.subtype,
    Subgroup.map_mono (Subgroup.map_subtype_le _),
    BlockCyc.isElemAbelian_map _ (BlockCyc.isElemAbelian_map _ hE₀), ?_⟩
  rw [Subgroup.card_map_of_injective J.subtype_injective,
    Subgroup.card_map_of_injective R₀.subtype_injective, hc]

theorem false_of_ib_of_surjective {J : Subgroup Y} (hIb : IbPerfectSections 3 J) {X : Type*}
    [Group X] (ψ : ↥J →* X) (hψ : Function.Surjective ψ) {B : Subgroup X} (hB : ⁅B, B⁆ = B)
    (hE : BlockCyc.HasE9 ↥B) : False := by
  obtain ⟨W, hWJ, hWp, E, hEW, -, hc⟩ := exists_perfect_isElemAbelian_of_surjective ψ hψ hB hE
  exact hIb W hWJ hWp (hc ▸ Subgroup.card_dvd_of_le hEW)

theorem false_of_cyc_of_surjective {J : Subgroup Y} (hcyc : CycPerfect 3 J) {X : Type*}
    [Group X] (ψ : ↥J →* X) (hψ : Function.Surjective ψ) {B : Subgroup X} (hB : ⁅B, B⁆ = B)
    (hE : BlockCyc.HasE9 ↥B) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨W, hWJ, hWp, E, hEW, hel, hc⟩ := exists_perfect_isElemAbelian_of_surjective ψ hψ hB hE
  exact BlockCyc.not_isCyclic_of_isElemAbelian_sq hel hc
    (hcyc W hWJ hWp E hEW (IsPGroup.of_card hc))

theorem hasE9_sp {k : ℕ} {d : TauCeti.ValidLieTypeIndex} (hk : 3 ≤ k)
    (hd : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q) :
    BlockCyc.HasE9 (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨d₁, hv⟩ := d
  obtain ⟨q, hq, hd₁⟩ := hd
  change d₁ = .B k q at hd₁
  subst hd₁
  have hp : q.p = 2 := by
    have h2 : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq
    exact ((Nat.Prime.pow_eq_iff Nat.prime_two).1 h2).1
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even k q hv hp hk
    (G := TauCeti.ValidLieTypeIndex.Group ⟨.B k q, hv⟩) (MulEquiv.refl _)
  rw [hp] at h
  exact BlockCyc.hasE9_of_model_psp h

theorem hasE9_top {X : Type*} [Group X] (h : BlockCyc.HasE9 X) : BlockCyc.HasE9 ↥(⊤ : Subgroup X) :=
  BlockCyc.hasE9_of_mulEquiv Subgroup.topEquiv.symm h

theorem not_nine_dvd_card_of_quotient_perm_le {J : Subgroup Y} {n : ℕ}
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Equiv.Perm (Fin n)) (hn : n ≤ 5) : ¬ 9 ∣ Nat.card J := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥J),
    Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n),
    Fintype.card_fin]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥J))
  rw [hk]
  intro h9
  have h9' : 9 ∣ n.factorial :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right _ (by norm_num)) h9
  interval_cases n <;> revert h9' <;> decide

theorem alternatingGroup_perfect_hasE9 {m : ℕ} (hm : 6 ≤ m) :
    ⁅alternatingGroup (Fin m), alternatingGroup (Fin m)⁆ = alternatingGroup (Fin m) ∧
      BlockCyc.HasE9 ↥(alternatingGroup (Fin m)) :=
  ⟨commutator_alternatingGroup_eq_self (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega),
    BlockCyc.hasE9_alternatingGroup hm⟩

omit [Finite Y] in
theorem le_five_of_quotient_perm {J : Subgroup Y} {n : ℕ}
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Equiv.Perm (Fin n))
    (hno : ∀ {X : Type} [Group X] (ψ : ↥J →* X), Function.Surjective ψ → ∀ {B : Subgroup X},
      ⁅B, B⁆ = B → BlockCyc.HasE9 ↥B → False) : n ≤ 5 := by
  by_contra hn
  obtain ⟨hp, hE⟩ := alternatingGroup_perfect_hasE9 (m := n) (by omega)
  exact hno (e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hp hE

end Perfect

section Bar

variable {G : Type} [Group G] [Finite G]

theorem not_nine_dvd_card_blockPL_of_no_e9 (hTPL : CitedBlockTransvectionPL) {M S L : Subgroup G}
    (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (h : NineThreeThree M S L ∨ NineThreeSix M S L ∨ NineThreeSeven M S L ∨
      NineThreeEight M S L)
    (hno : ∀ {X : Type} [Group X] (ψ : ↥(blockPL M S L) →* X), Function.Surjective ψ →
      ∀ {B : Subgroup X}, ⁅B, B⁆ = B → BlockCyc.HasE9 ↥B → False) :
    ¬ 9 ∣ Nat.card (blockPL M S L) := by
  rcases h with h3 | ⟨-, n, -, ⟨e⟩⟩ | ⟨-, n, -, ⟨e⟩⟩ |
    ⟨-, N, r, ⟨m, hm⟩, hr, h0, h2, h4, -, φ, -⟩
  · rcases hTPL G M S L hK hA hL hX hS h3 with ⟨k, d, hk, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exfalso
      exact hno (e.toMonoidHom.comp (QuotientGroup.mk' _))
        (e.surjective.comp (QuotientGroup.mk'_surjective _))
        (B := ⊤) (by rw [← commutator_def, kFactSpTwoPerfect_of_simple kFactSpTwoSimple_holds k d
          hk hd]) (hasE9_top (hasE9_sp hk hd))
    · exact not_nine_dvd_card_of_quotient_perm_le e (le_five_of_quotient_perm e hno)
  · exact not_nine_dvd_card_of_quotient_perm_le e (le_five_of_quotient_perm e hno)
  · exact not_nine_dvd_card_of_quotient_perm_le e (le_five_of_quotient_perm e hno)
  · exfalso
    obtain ⟨hp, hE⟩ := alternatingGroup_perfect_hasE9 (m := N - 2 * r) (by omega)
    exact hno ((MonoidHom.snd _ _).comp (φ.toMonoidHom.comp (QuotientGroup.mk' _)))
      (Prod.snd_surjective.comp (φ.surjective.comp (QuotientGroup.mk'_surjective _)))
      (B := (alternatingGroup (Fin (N - 2 * r)))) hp hE

theorem not_dvd_card_blockPL_of_ib_rest (hTPL : CitedBlockTransvectionPL) {M S L : Subgroup G}
    (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (h : NineThreeThree M S L ∨ NineThreeSix M S L ∨ NineThreeSeven M S L ∨
      NineThreeEight M S L) (hIb : IbPerfectSections 3 (blockPL M S L)) :
    ¬ 9 ∣ Nat.card (blockPL M S L) :=
  not_nine_dvd_card_blockPL_of_no_e9 hTPL hK hA hL hX hS h
    fun ψ hψ _ hB hE => false_of_ib_of_surjective hIb ψ hψ hB hE

theorem card_le_three_of_cyc_rest (hTPL : CitedBlockTransvectionPL) {M S L : Subgroup G}
    (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (h : NineThreeThree M S L ∨ NineThreeSix M S L ∨ NineThreeSeven M S L ∨
      NineThreeEight M S L) (hcyc : CycPerfect 3 (blockPL M S L))
    {Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hQ : Q ≤ blockPL M S L) (hQ3 : IsPGroup 3 Q) :
    Nat.card Q ≤ 3 := by
  have h9 := not_nine_dvd_card_blockPL_of_no_e9 hTPL hK hA hL hX hS h
    fun ψ hψ _ hB hE => false_of_cyc_of_surjective hcyc ψ hψ hB hE
  simpa using card_le_of_not_pow_dvd hQ hQ3 (j := 1) h9

end Bar

end ToralReduce

end CFSG.AGLEmbedding
