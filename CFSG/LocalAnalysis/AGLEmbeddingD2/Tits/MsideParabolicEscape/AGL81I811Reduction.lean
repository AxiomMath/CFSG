module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.AGL81I811Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeComponentCyclic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.TwoLocalN1
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.CyclicSylowNormal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.TwoLocalSylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PushUpInput

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2 CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.Tits.MsidePrelim

theorem pRank_three_eq_one_of_cyclic {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hcyc : ∀ X : Subgroup G, X ≤ L → IsPGroup 3 X → IsCyclic X) (h3 : 3 ∣ Nat.card L) :
    CFSG.Open.pRank 3 L = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold CFSG.Open.pRank
  refine IsGreatest.csSup_eq ⟨?_, ?_⟩
  · show ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 1
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) 3 h3
    have hx3 : (x.1 : G) ^ 3 = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      exact congrArg Subtype.val this
    refine ⟨Subgroup.zpowers x.1, (Subgroup.zpowers_le).mpr x.2, ⟨inferInstance, ?_⟩, ?_⟩
    · intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
    · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one]
  · rintro k ⟨E, hEL, ⟨hEc, hE3⟩, hEk⟩
    by_contra hk
    push Not at hk
    have hEk' : Nat.card E = 3 ^ k := hEk
    have hEp : IsPGroup 3 E := IsPGroup.of_card hEk'
    haveI := hcyc E hEL hEp
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
    have hg3 : g ^ 3 = 1 := Subtype.ext (hE3 g g.2)
    have hord : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
    have hdvd : Nat.card E ∣ 3 := by rw [← hord]; exact orderOf_dvd_of_pow_eq_one hg3
    rw [hEk'] at hdvd
    have h2 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
    have h9 : 9 ∣ 3 := by
      have := h2.trans hdvd
      simpa using this
    omega

theorem eq_of_card_three_of_le_normalizer {G : Type} [Group G] [Finite G] {B A A' : Subgroup G}
    (hcyc : ∀ X : Subgroup G, X ≤ B → IsPGroup 3 X → IsCyclic X) (hAB : A ≤ B) (hA'B : A' ≤ B)
    (hA : Nat.card A = 3) (hA' : Nat.card A' = 3) (hn : A' ≤ Subgroup.normalizer (A : Set G)) :
    A' = A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by rw [hA, pow_one])
  have hA'p : IsPGroup 3 A' := IsPGroup.of_card (n := 1) (by rw [hA', pow_one])
  have hQ : IsPGroup 3 (A ⊔ A' : Subgroup G) := hAp.to_sup_of_normal_left' hA'p hn
  haveI : IsCyclic ↥(A ⊔ A' : Subgroup G) := hcyc _ (sup_le hAB hA'B) hQ
  have hAle : A ≤ A ⊔ A' := le_sup_left
  have hA'le : A' ≤ A ⊔ A' := le_sup_right
  have h1 : A'.subgroupOf (A ⊔ A') = A.subgroupOf (A ⊔ A') := by
    apply eq_of_card_eq_of_isCyclic
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv, hA, hA']
  have h2 := Subgroup.subgroupOf_inj.mp h1
  rwa [inf_of_le_left hA'le, inf_of_le_left hAle] at h2

theorem isSylowTwoOf_of_I811 (h811 : AGL81I811) {G : Type} [Group G] [Finite G]
    (hglob : AGLGlobal G) {M : Subgroup G} (hM : GLBIsMaxTwoLocal M)
    (hstr : GLBStronglyEmbedded 3 M) {T : Subgroup G} (hT : IsSylowTwoOf T M) {N : Subgroup G}
    (hN : IsTwoLocal N) (hTN : T ≤ N) (hNM : ¬ N ≤ M)
    (hcyc : ∀ X : Subgroup G, X ≤ N ⊓ M → IsPGroup 3 X → IsCyclic X)
    (hns : ¬ CFSG.HallHigman.IsPSolvable 3 ↥(N ⊓ M))
    (hbound : ∀ S : Subgroup G, IsPGroup 2 S → Nat.card S ≤ 8 * Nat.card T) :
    IsSylowTwoOf T N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcycB : ∀ X : Subgroup ↥(N ⊓ M), IsPGroup 3 X → IsCyclic ↥X := by
    intro X hX
    have hXp : IsPGroup 3 (X.map (N ⊓ M).subtype) := hX.map _
    haveI := hcyc (X.map (N ⊓ M).subtype) (Subgroup.map_subtype_le X) hXp
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective X (N ⊓ M).subtype (N ⊓ M).subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  obtain ⟨L0, hL0, h3L0⟩ := exists_three_component_of_cyclic hcycB hns
  set L : Subgroup G := L0.map (N ⊓ M).subtype with hL
  have hLB : L ≤ N ⊓ M := Subgroup.map_subtype_le L0
  have hLsub : L.subgroupOf (N ⊓ M) = L0 :=
    Subgroup.comap_map_eq_self_of_injective (N ⊓ M).subtype_injective L0
  have hLcard : Nat.card L = Nat.card L0 := Subgroup.card_map_of_injective (N ⊓ M).subtype_injective
  have h3L : 3 ∣ Nat.card L := hLcard ▸ h3L0
  have hpr : CFSG.Open.pRank 3 L = 1 :=
    pRank_three_eq_one_of_cyclic (fun X hXL hXp => hcyc X (hXL.trans hLB) hXp) h3L
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) 3 h3L
  have hA0card : Nat.card (Subgroup.zpowers x.1) = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hA0L : Subgroup.zpowers x.1 ≤ L := (Subgroup.zpowers_le).mpr x.2
  have hweak : ∀ g : G, (Subgroup.zpowers x.1).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer (Subgroup.zpowers x.1 : Set G) ⊓ (N ⊓ M) →
      (Subgroup.zpowers x.1).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x.1 := by
    intro g hg
    refine eq_of_card_three_of_le_normalizer (B := N ⊓ M) hcyc (hA0L.trans hLB)
      (fun y hy => (hg hy).2) hA0card ?_ (fun y hy => (hg hy).1)
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hA0card]
  obtain ⟨S, hTS, hS⟩ := exists_isSylowTwoOf_of_le hTN hT.2.1
  have hrel : (S ⊓ M).relIndex S ≤ 8 := by
    have hTSM : T ≤ S ⊓ M := le_inf hTS hT.1
    have hdvd : (S ⊓ M).relIndex S ∣ T.relIndex S := Subgroup.relIndex_dvd_of_le_left S hTSM
    have hcardS : Nat.card (T.subgroupOf S) * T.relIndex S = Nat.card S :=
      Subgroup.card_mul_index (T.subgroupOf S)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTS).toEquiv] at hcardS
    have hTpos : 0 < Nat.card T := Nat.card_pos
    have hSle := hbound S hS.2.1
    have hle8 : T.relIndex S ≤ 8 := by
      by_contra h
      push Not at h
      have : 8 * Nat.card T < Nat.card T * T.relIndex S := by nlinarith
      omega
    have hne : T.relIndex S ≠ 0 := by
      intro h
      rw [h, mul_zero] at hcardS
      exact Nat.card_pos.ne' hcardS.symm
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd).trans hle8
  obtain ⟨S', hS', hS'M⟩ := h811 G hglob M N hM hstr hN L hLB
    (by rw [hLsub]; exact hL0) hpr (Subgroup.zpowers x.1) hA0card hA0L hweak S hS hrel
  have hSc : Nat.card S = twoPart N := hS.card_eq
  have hS'c : Nat.card S' = twoPart N := hS'.card_eq
  obtain ⟨V, hS'V, hV⟩ := exists_isSylowTwoOf_of_le hS'M hS'.2.1
  have hVT : Nat.card V = Nat.card T := hV.card_eq.trans hT.card_eq.symm
  have hS'V' : Nat.card S' ≤ Nat.card V := Subgroup.card_le_of_le hS'V
  have hTS' : Nat.card T ≤ Nat.card S := Subgroup.card_le_of_le hTS
  exact isSylowTwoOf_of_card_eq hTN hT.2.1 (by omega)

theorem d2L34BetaTwoLocalSylowCyclic_of_I811
    (hFF : CitedFFL34BestOffender) (h811 : AGL81I811) :
    D2L34BetaTwoLocalSylowCyclic := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll hKmax T hT N hN hTN hNM hcyc hns
  have hOnly := hAll.onlyL34At
  have hbound : ∀ S : Subgroup G, IsPGroup 2 S → Nat.card S ≤ 8 * Nat.card T := by
    obtain ⟨T0, -, hT0⟩ := exists_isSylowTwoOf_of_le (bot_le : (⊥ : Subgroup G) ≤ H ⊓ M)
      IsPGroup.of_bot
    obtain ⟨hT0M, -⟩ :=
      D2L34BetaConf.isSylowTwoOf_of_cover (d2L34BetaPushUpCoverSyl hFF) hc hstr hOnly hT0
    obtain ⟨U, hT0U, hU⟩ := exists_isSylowTwoOf_of_le (hT0.1.trans inf_le_left) hT0.2.1
    obtain ⟨hUtop, hUcard⟩ := D2L34BetaConf.isSylowTwoOf_top_and_card hFF hc hstr hOnly hT0 hU hT0U
    have hTT0 : Nat.card T0 = Nat.card T := hT0M.card_eq.trans hT.card_eq.symm
    intro S hS
    obtain ⟨V, hSV, hV⟩ := exists_isSylowTwoOf_of_le (le_top : S ≤ ⊤) hS
    have hVU : Nat.card V = Nat.card U := hV.card_eq.trans hUtop.card_eq.symm
    calc Nat.card S ≤ Nat.card V := Subgroup.card_le_of_le hSV
      _ = Nat.card U := hVU
      _ = 8 * Nat.card T := by rw [hUcard, hTT0]
  exact isSylowTwoOf_of_I811 h811 hc.glob.toAGLGlobal hc.esc.maxTwoLocal_M hstr hT hN hTN hNM hcyc
    hns hbound

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
