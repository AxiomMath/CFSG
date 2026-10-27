module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesRankOne
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Model
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicJ4
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicMcL
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicTits
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporM11

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial

theorem kFactNineThreeNoTwoAt_of_aut {p : ℕ} {i : TauCeti.CFSGIndex}
    (h : ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* i.Group) → ∀ T : Sylow p K,
      ∀ V : Subgroup (MulAut K), IsPGroup 2 V →
        (∀ t ∈ (T : Subgroup K), MulAut.conj t ∈ Subgroup.normalizer (V : Set (MulAut K))) →
          V = ⊥) :
    KFactNineThreeNoTwoAt p i := by
  intro X _ _ K hK hiso _ T S hS hTS
  haveI := hK
  exact Hyp111.le_centralizer_of_aut (T := (T : Subgroup K).map K.subtype)
    (Subgroup.map_subtype_le _) (fun V hV hN => h K hiso T V hV fun t ht => hN t ⟨t, ht, rfl⟩)
    hS hTS

private theorem kFactNineThreeNoTwoAt_of_signalizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {i : TauCeti.CFSGIndex}
    (h : ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* i.Group) → SignalizerTrivialOn p K) :
    KFactNineThreeNoTwoAt p i := by
  refine kFactNineThreeNoTwoAt_of_aut fun K _ _ hK T V hV hTV => ?_
  refine h K hK T V ?_ fun g hg w hw => (Subgroup.mem_normalizer_iff.mp (hTV g hg) w).mp hw
  obtain ⟨k, hk⟩ := hV.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)

open CFSG.LocalAnalysis.RankThreeTheoremC.M11Model CFSG.Blueprint in
theorem kFactNineThreeNoTwoAt_m11 :
    KFactNineThreeNoTwoAt 3 (.sporadic .M11) := by
  refine kFactNineThreeNoTwoAt_of_aut fun K _ _ hK T V hV hTV => ?_
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hK
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow (e.trans eC.symm)
    (IsPGroup.of_card sylowR_card) sylowR_index T
  set ψ : MulAut K ≃* MulAut NativeSporadic.M11 := MulAut.congr Φ.symm with hψ
  have hψc : ∀ r : NativeSporadic.M11, ψ (MulAut.conj (Φ r)) = MulAut.conj r := by
    intro r
    ext a
    simp [hψ, MulAut.conj_apply]
  have hcen : Subgroup.center NativeSporadic.M11 = ⊥ := by
    haveI : IsSimpleGroup NativeSporadic.M11 := CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
    exact CFSG.RankThree.PartTwo.Sec4.Item434Spor.center_eq_bot_of_simple
      (by rw [CFSG.Sporadic.Mathieu.card_M11]; norm_num)
  have hinj := CFSG.RankThree.PartTwo.Sec4.Item434Kit.conj_injective_of_center_eq_bot hcen
  set R : Subgroup (MulAut NativeSporadic.M11) :=
    sylowR.map (MulAut.conj : NativeSporadic.M11 →* MulAut NativeSporadic.M11) with hR
  have hRe : IsElemAbelian 3 R := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := a.2
      obtain ⟨y, hy, hyb⟩ := b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul,
        sylowR_comm x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, sylowR_cube x hx, map_one]
  have hR9 : Nat.card R = 9 := by
    rw [hR, Subgroup.card_map_of_injective hinj, sylowR_card]
    norm_num
  have hY3 : ¬ 3 ∣ Nat.card (V.map ψ.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective]
    obtain ⟨k, hk⟩ := hV.exists_card_eq
    rw [hk]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hRY : R ≤ Subgroup.normalizer
      ((V.map ψ.toMonoidHom : Subgroup (MulAut NativeSporadic.M11)) :
        Set (MulAut NativeSporadic.M11)) := by
    rintro _ ⟨r, hr, rfl⟩
    have hrT : Φ r ∈ (T : Subgroup K) := by
      rw [hΦ]
      exact ⟨r, hr, rfl⟩
    rw [← Subgroup.map_equiv_normalizer_eq, ← hψc r]
    exact ⟨_, hTV _ hrT, rfl⟩
  have hYbot := CFSG.RankThree.PartTwo.Sec4.Item434SporM11.eq_bot_of_le_normalizer_mulAut hRe hR9
    hY3 hRY
  exact (Subgroup.map_eq_bot_iff_of_injective V ψ.injective).1 hYbot

theorem kFactNineThreeNoTwoAt_mcl :
    KFactNineThreeNoTwoAt 5 (.sporadic .McL) :=
  kFactNineThreeNoTwoAt_of_signalizer Nat.prime_five (by norm_num) signalizerTrivialMcL_holds

theorem kFactNineThreeNoTwoAt_tits
    (hv : TauCeti.LieTypeIndex.tits.Valid) : KFactNineThreeNoTwoAt 5 (.lie ⟨.tits, hv⟩) :=
  kFactNineThreeNoTwoAt_of_signalizer Nat.prime_five (by norm_num)
    fun K _ _ hK => signalizerTrivialTits_holds K ⟨hv, hK⟩

theorem kFactNineThreeNoTwoAt_j4 :
    KFactNineThreeNoTwoAt 11 (.sporadic .J4) :=
  kFactNineThreeNoTwoAt_of_signalizer (by norm_num) (by norm_num) signalizerTrivialJ4_holds

@[expose] def KFactNineThreeNoTwoRestThree : Prop :=
  ∀ p, p.Prime → p ≠ 2 → ∀ i, IsNineThreeIndex p i →
    (¬ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ IsCaseTwoIndex p d) →
    (¬ ∃ (n : ℕ) (hn : 5 ≤ n), i = .alternating n hn) →
    (¬ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧
      ∃ q : TauCeti.PrimePower, q.p = p ∧ 2 ≤ q.exponent ∧ d.1 = .A 1 q) →
    (¬ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧
      ∃ q : TauCeti.PrimePower, q.p = p ∧ d.1 = .twistedA 2 q) →
    (¬ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ p = 3 ∧ ∃ m : ℕ, d.1 = .reeG2 m) →
    ¬ (p = 3 ∧ i = .sporadic .M11) → ¬ (p = 5 ∧ i = .sporadic .McL) →
    ¬ (p = 11 ∧ i = .sporadic .J4) →
    (¬ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ p = 5 ∧ d.1 = .tits) →
    KFactNineThreeNoTwoAt p i

theorem kFactNineThreeNoTwoRestTwo_of_restThree
    (h : KFactNineThreeNoTwoRestThree) : KFactNineThreeNoTwoRestTwo := by
  intro p hp hp2 i hi h2 h3 h4 h5 h6
  by_cases h7 : p = 3 ∧ i = .sporadic .M11
  · obtain ⟨rfl, rfl⟩ := h7
    exact kFactNineThreeNoTwoAt_m11
  by_cases h8 : p = 5 ∧ i = .sporadic .McL
  · obtain ⟨rfl, rfl⟩ := h8
    exact kFactNineThreeNoTwoAt_mcl
  by_cases h9 : p = 11 ∧ i = .sporadic .J4
  · obtain ⟨rfl, rfl⟩ := h9
    exact kFactNineThreeNoTwoAt_j4
  by_cases h10 : ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ p = 5 ∧ d.1 = .tits
  · obtain ⟨⟨d, hv⟩, rfl, rfl, hd⟩ := h10
    simp only at hd
    subst hd
    exact kFactNineThreeNoTwoAt_tits hv
  exact h p hp hp2 i hi h2 h3 h4 h5 h6 h7 h8 h9 h10

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
