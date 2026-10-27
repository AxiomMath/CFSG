module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Setting

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

namespace Notation25

theorem card_witness_le_257 (N : Notation25 hs) {V : Subgroup G} (hV : IsWitness M V) :
    Nat.card V ≤ Nat.card N.S :=
  N.gammaU.1.card_le_of_isSylowTwoOf N.tuple.sylow hV

theorem charTwo_normalizer_of_mem_257 (N : Notation25 hs) {Q : Subgroup G} (hQ2 : IsPGroup 2 Q)
    (hzQ : N.z ∈ Q) : CharTwo (Subgroup.normalizer (Q : Set G)) := by
  have hDZ : Q ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
    intro hbot
    have hz : N.z ∈ Q ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) := ⟨hzQ, N.tuple.z_mem⟩
    rw [hbot] at hz
    exact N.tuple.z_ne_one (Subgroup.mem_bot.mp hz)
  exact charTwo_normalizer_of_inf_center hs.setting.qtke.2.1 hs.setting.sylow hQ2 hDZ

theorem pCoreOf_normalizer_ne_bot_257 (N : Notation25 hs) {Q : Subgroup G} (hQ2 : IsPGroup 2 Q)
    (hzQ : N.z ∈ Q) : pCoreOf 2 (Subgroup.normalizer (Q : Set G)) ≠ ⊥ := by
  intro hbot
  have hQ1 : Q ≠ ⊥ := fun h => N.tuple.z_ne_one (Subgroup.mem_bot.mp (h ▸ hzQ))
  have hle : Q ≤ pCoreOf 2 (Subgroup.normalizer (Q : Set G)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 Q _ Subgroup.le_normalizer
      ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl) hQ2
  rw [hbot] at hle
  exact hQ1 (le_bot_iff.mp hle)

theorem false_of_normalizer_witness (N : Notation25 hs) {Q U₀ : Subgroup G}
    (hQ2 : IsPGroup 2 Q) (hzQ : N.z ∈ Q) (hU₀ : IsConfining M U₀)
    (hU₀N : U₀ ≤ Subgroup.normalizer (Q : Set G)) (hcard : Nat.card N.S ≤ Nat.card U₀)
    (hnotM : ¬ Subgroup.normalizer (Q : Set G) ≤ M) : False := by
  have hchar := N.charTwo_normalizer_of_mem_257 hQ2 hzQ
  have hcore := N.pCoreOf_normalizer_ne_bot_257 hQ2 hzQ
  have hwit : IsWitnessPair M U₀ (Subgroup.normalizer (Q : Set G)) :=
    ⟨hU₀, hU₀N, hcore, hchar, hnotM⟩
  have htop : IsGammaTop M (Subgroup.normalizer (Q : Set G)) :=
    hwit.isGammaTop_of_le le_rfl hcore fun V hV => (N.card_witness_le_257 hV).trans hcard
  have hU : IsGammaU M (Subgroup.normalizer (Q : Set G)) := by
    refine ⟨htop, fun K hK => ?_⟩
    have h1 : twoPart K ≤ twoPart N.H := N.gammaU.2 K hK
    have h2 : Nat.card N.S = twoPart N.H := N.tuple.sylow.card_eq
    have h3 : Nat.card U₀ ≤ twoPart (Subgroup.normalizer (Q : Set G)) :=
      card_le_twoPart hU₀N hU₀.2.2.1
    omega
  exact hs.noCharTwo _ (Or.inl hU) hchar

end Notation25

end CFSG.QuasithinUnique
