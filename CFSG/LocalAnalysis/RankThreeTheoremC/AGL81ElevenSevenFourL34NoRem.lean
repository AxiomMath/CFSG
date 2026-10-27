module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenFourL34Of
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroProductSolv
public import CFSG.LocalAnalysis.AGLEmbedding.SubnormalSymThreeDetermined
import CFSG.LocalAnalysis.AGLEmbedding.SUPairCommute
import CFSG.HardMathSupport.Cooperstein.Proving.QuotientPCoreTransfer
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTwentyTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenCfgOf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.ComponentClassification.AS76b (oUpperTwo)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace NoRem

theorem pCoreOf_map_conj (K : Subgroup G) (g : G) :
    pCoreOf 2 (K.map (MulAut.conj g).toMonoidHom) =
      (pCoreOf 2 K).map (MulAut.conj g).toMonoidHom := by
  set f := (MulAut.conj g).toMonoidHom
  set e : ↥K ≃* ↥(K.map f) := K.equivMapOfInjective f (MulAut.conj g).injective
  have h := CFSG.pCore_map_iso 2 e
  show (CFSG.pCore 2 ↥(K.map f)).map (K.map f).subtype = ((CFSG.pCore 2 ↥K).map K.subtype).map f
  rw [← h, map_map, map_map]
  rfl

theorem shape_map_conj {X I : Subgroup G}
    (hb : pCoreOf 2 I = pCoreOf 2 X ∧ IsSymThreeOrSUThreeTwo (↥I ⧸ CFSG.pCore 2 ↥I)) {g : G}
    (hg : g ∈ normalizer (X : Set G)) :
    pCoreOf 2 (I.map (MulAut.conj g).toMonoidHom) = pCoreOf 2 X ∧
      IsSymThreeOrSUThreeTwo (↥(I.map (MulAut.conj g).toMonoidHom) ⧸
        CFSG.pCore 2 ↥(I.map (MulAut.conj g).toMonoidHom)) := by
  have hX : X.map (MulAut.conj g).toMonoidHom = X := mem_normalizer_iff_map_conj_eq.mp hg
  refine ⟨?_, ?_⟩
  · rw [pCoreOf_map_conj, hb.1, ← pCoreOf_map_conj, hX]
  · exact IsSymThreeOrSUThreeTwo.of_mulEquiv
      (CFSG.HardMathSupport.Cooperstein.Proving.quotientPCoreMulEquiv 2
        (I.equivMapOfInjective _ (MulAut.conj g).injective)) hb.2

theorem image_data {X I : Subgroup G} (hI : IsCZeroMember X I)
    (hb : pCoreOf 2 I = pCoreOf 2 X ∧ IsSymThreeOrSUThreeTwo (↥I ⧸ CFSG.pCore 2 ↥I)) :
    IsSubnormal ((I.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) ⊤ ∧
      IsSymThreeOrSUThreeTwo ↥((I.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) ∧
      CFSG.pCore 2 ↥X ≤ I.subgroupOf X ∧
      (oUpperTwo (I.subgroupOf X)).map X.subtype = oUpperTwo I := by
  set N : Subgroup ↥X := CFSG.pCore 2 ↥X with hNdef
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hsub : IsSubnormal ((I.subgroupOf X).map π) ⊤ := by
    have := (IsSubnormal.of_mathlib hI.subnormal.subgroupOf).map π
    rwa [map_top_of_surjective π hπs] at this
  have hNI : N ≤ I.subgroupOf X := by
    intro n hn
    rw [mem_subgroupOf]
    have : (n : G) ∈ pCoreOf 2 X := mem_map_of_mem X.subtype hn
    rw [← hb.1] at this
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 I this
  set φ : ↥I →* ↥X ⧸ N := π.comp (inclusion hI.le) with hφ
  have hrange : φ.range = (I.subgroupOf X).map π := by
    rw [hφ, MonoidHom.range_comp, inclusion_range]
  have hker : φ.ker = CFSG.pCore 2 ↥I := by
    ext i
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    have h1 : inclusion hI.le i ∈ N ↔ (i : G) ∈ pCoreOf 2 X := by
      constructor
      · intro h
        exact ⟨_, h, rfl⟩
      · rintro ⟨y, hy, hyi⟩
        have : y = inclusion hI.le i := Subtype.ext hyi
        rwa [← this]
    rw [h1, ← hb.1]
    constructor
    · rintro ⟨y, hy, hyi⟩
      have : y = i := Subtype.ext hyi
      rwa [← this]
    · intro h
      exact ⟨_, h, rfl⟩
  have e : ↥I ⧸ CFSG.pCore 2 ↥I ≃* ↥((I.subgroupOf X).map π) :=
    ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange)
  refine ⟨hsub, IsSymThreeOrSUThreeTwo.of_mulEquiv e hb.2, hNI, ?_⟩
  rw [CFSG.AGLEmbedding.SUPair.map_oUpperTwo, subgroupOf_map_subtype, inf_of_le_left hI.le]

theorem eq_of_oUpperTwo_eq_cZero (hD : SubnormalSUThreeTwoDetermined) {X I₁ I₂ : Subgroup G}
    (h₁ : IsCZeroMember X I₁) (h₂ : IsCZeroMember X I₂)
    (hb₁ : pCoreOf 2 I₁ = pCoreOf 2 X ∧ IsSymThreeOrSUThreeTwo (↥I₁ ⧸ CFSG.pCore 2 ↥I₁))
    (hb₂ : pCoreOf 2 I₂ = pCoreOf 2 X ∧ IsSymThreeOrSUThreeTwo (↥I₂ ⧸ CFSG.pCore 2 ↥I₂))
    (h : oUpperTwo I₁ = oUpperTwo I₂) : I₁ = I₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hs₁, hb₁', hN₁, hm₁⟩ := image_data h₁ hb₁
  obtain ⟨hs₂, hb₂', hN₂, hm₂⟩ := image_data h₂ hb₂
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  have hO2 : oUpperTwo (I₁.subgroupOf X) = oUpperTwo (I₂.subgroupOf X) :=
    map_injective X.subtype_injective (hm₁.trans (h.trans hm₂.symm))
  have himg : oUpperTwo ((I₁.subgroupOf X).map π) = oUpperTwo ((I₂.subgroupOf X).map π) := by
    rw [← CFSG.AGLEmbedding.SUPair.map_oUpperTwo, ← CFSG.AGLEmbedding.SUPair.map_oUpperTwo, hO2]
  have heq := eq_of_oUpperTwo_eq_of_shape hD (CZeroProduct.pCore_quotient_pCore_eq_bot 2)
    (hs₁.mathlib IsSubnormal.top) (hs₂.mathlib IsSubnormal.top) hb₁' hb₂' himg
  have hc := congrArg (Subgroup.comap π) heq
  rw [comap_map_eq, comap_map_eq, QuotientGroup.ker_mk', sup_of_le_left hN₁,
    sup_of_le_left hN₂] at hc
  have := (subgroupOf_inj).mp hc
  rwa [inf_of_le_left h₁.le, inf_of_le_left h₂.le] at this

theorem two_le_pRank_of_commuting_mod' {Y N C₂ : Subgroup G} (hN : IsPGroup 2 N)
    (hYN : Y ≤ normalizer (N : Set G)) {u v : G} (huY : u ∈ Y) (hvY : v ∈ Y) (hvC : v ∈ C₂)
    (hind : u ∉ C₂ ⊔ N) (hu : orderOf u = 3) (hv : orderOf v = 3)
    (hcomm : u * v * u⁻¹ * v⁻¹ ∈ N) : 2 ≤ Open.pRank 3 Y := by
  have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hmeet : (zpowers u ⊔ N) ⊓ (C₂ ⊔ N) ≤ N := by
    intro w ⟨hw₁, hw₂⟩
    have hle : zpowers u ≤ normalizer (N : Set G) := (zpowers_le).mpr (hYN huY)
    have hw₁' : w ∈ ((zpowers u : Set G) * (N : Set G)) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _ hle]
      exact hw₁
    obtain ⟨x, hx, n, hn, rfl⟩ := hw₁'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    have hxC : u ^ k ∈ C₂ ⊔ N := by
      have : u ^ k = (u ^ k * n) * n⁻¹ := by group
      rw [this]
      exact (C₂ ⊔ N).mul_mem hw₂ ((C₂ ⊔ N).inv_mem (mem_sup_right hn))
    rw [← zpow_mod_orderOf, hu] at hxC ⊢
    have h0 : 0 ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h3 : k % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
    obtain ⟨r, hr⟩ : ∃ r : ℤ, r = k % ((3 : ℕ) : ℤ) := ⟨_, rfl⟩
    rw [← hr] at hxC h0 h3 ⊢
    interval_cases r
    · simpa using hn
    · exact absurd (by simpa using hxC) hind
    · exfalso
      apply hind
      have : u = (u ^ (2 : ℤ)) ^ (2 : ℤ) := by
        rw [← zpow_mul]
        norm_num
        rw [pow_succ, hu3, one_mul]
      rw [this]
      exact zpow_mem hxC 2
  exact SevenFourL34.two_le_pRank_of_commuting_mod hN hYN huY hvY (mem_zpowers u) hvC hmeet hu hv
    hcomm

theorem oUpperTwo_idem (I : Subgroup G) : oUpperTwo (oUpperTwo I) = oUpperTwo I := by
  simpa using CZeroProduct.oUpperTwo_sup_eq (I := I) (N := ⊥) bot_le

theorem oUpperTwo_mono {A B : Subgroup G} (h : A ≤ B) : oUpperTwo A ≤ oUpperTwo B :=
  closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem oUpperTwo_eq_of_rank {Xc R I₁ I₂ : Subgroup G} (h₁ : IsCZeroMember Xc I₁)
    (h₂ : IsCZeroMember Xc I₂)
    (hb₁ : pCoreOf 2 I₁ = pCoreOf 2 Xc ∧ IsSymThreeOrSUThreeTwo (↥I₁ ⧸ CFSG.pCore 2 ↥I₁))
    (hb₂ : pCoreOf 2 I₂ = pCoreOf 2 Xc ∧ IsSymThreeOrSUThreeTwo (↥I₂ ⧸ CFSG.pCore 2 ↥I₂))
    (hrank : Open.pRank 3 R ≤ 1) (hR₁ : oUpperTwo I₁ ≤ R) (hR₂ : oUpperTwo I₂ ≤ R)
    (h3 : 3 ∣ Nat.card (oUpperTwo I₂))
    (hcard : Nat.card (oUpperTwo I₁) = Nat.card (oUpperTwo I₂)) :
    oUpperTwo I₁ = oUpperTwo I₂ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  set N := pCoreOf 2 Xc
  have hcomm := commutator_oUpperTwo_le_pCoreOf
    CFSG.AGLEmbedding.SUPair.subnormalSUThreeTwoCommute_holds h₁ h₂ hb₁ hb₂ hne
  have hN₂ : N ≤ I₂ := by
    rw [← hb₂.1]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 I₂
  have hnle : ¬ oUpperTwo I₁ ≤ oUpperTwo I₂ ⊔ N := by
    intro hle
    have h12 : oUpperTwo I₁ ≤ oUpperTwo I₂ := by
      calc oUpperTwo I₁ = oUpperTwo (oUpperTwo I₁) := (oUpperTwo_idem I₁).symm
        _ ≤ oUpperTwo (oUpperTwo I₂ ⊔ N) := oUpperTwo_mono hle
        _ = oUpperTwo I₂ := CZeroProduct.oUpperTwo_sup_eq hN₂
    exact hne (eq_of_le_of_card_ge h12 hcard.symm.le)
  obtain ⟨u, ⟨huI, hodd⟩, hu⟩ : ∃ u, (u ∈ I₁ ∧ Odd (orderOf u)) ∧ u ∉ oUpperTwo I₂ ⊔ N := by
    by_contra hcon
    push_neg at hcon
    exact hnle ((closure_le _).mpr fun x hx => hcon x hx)
  have huO : u ∈ oUpperTwo I₁ := subset_closure ⟨huI, hodd⟩
  have hu3 : u ^ 3 = 1 := by
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥I₁)
    have hgen : π ⟨u, huI⟩ ∈ oUpperTwo (⊤ : Subgroup (↥I₁ ⧸ CFSG.pCore 2 ↥I₁)) := by
      refine subset_closure ⟨mem_top _, ?_⟩
      have hd : orderOf (π ⟨u, huI⟩) ∣ orderOf u := by
        rw [← Subgroup.orderOf_mk u huI]
        exact orderOf_map_dvd π _
      exact Odd.of_dvd_nat hodd hd
    have hc := IsSymThreeOrSUThreeTwo.cube kFactSUThreeTwoShape_holds hb₁.2 _ hgen
    rw [← map_pow] at hc
    have hmem := coe_mem_pCoreOf_two_of_mk_eq_one _ hc
    simp only [SubgroupClass.coe_pow] at hmem
    rw [hb₁.1] at hmem
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Xc) ⟨u ^ 3, hmem⟩
    have hk' : (u ^ 3) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hm : (u ^ 3) ^ orderOf u = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    have hco : Nat.Coprime (2 ^ k) (orderOf u) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    have := (pow_gcd_eq_one (a := u ^ 3) (m := 2 ^ k) (n := orderOf u)).mpr ⟨hk', hm⟩
    rwa [Nat.Coprime.gcd_eq_one hco, pow_one] at this
  have hu1 : u ≠ 1 := fun h => hu (h ▸ (oUpperTwo I₂ ⊔ N).one_mem)
  have huo : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  obtain ⟨⟨v, hvO⟩, hvo⟩ := exists_prime_orderOf_dvd_card' (G := ↥(oUpperTwo I₂)) 3 h3
  rw [Subgroup.orderOf_mk] at hvo
  have hind : u ∉ zpowers v ⊔ N := fun h => hu (sup_le_sup_right ((zpowers_le).mpr hvO) N h)
  have hc : u * v * u⁻¹ * v⁻¹ ∈ N := by
    have := hcomm (commutator_mem_commutator huO hvO)
    rwa [commutatorElement_def] at this
  have hYN : R ⊓ Xc ≤ normalizer (N : Set G) :=
    inf_le_right.trans (localGroup_le_normalizer_pCoreOf 2 Xc)
  have h2 := two_le_pRank_of_commuting_mod' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Xc) hYN
    ⟨hR₁ huO, h₁.le huI⟩ ⟨hR₂ hvO, h₂.le (oUpperTwo_le_self I₂ hvO)⟩ (mem_zpowers v) hind huo hvo
    hc
  have h3' := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (inf_le_left : R ⊓ Xc ≤ R)
  omega

theorem map_conj_eq_of_cZero (hD : SubnormalSUThreeTwoDetermined) {Xc R I₀ : Subgroup G} {q : G}
    (hrank : Open.pRank 3 R ≤ 1) (hR : oUpperTwo I₀ ≤ R)
    (hRq : oUpperTwo (I₀.map (MulAut.conj q).toMonoidHom) ≤ R)
    (h3 : 3 ∣ Nat.card (oUpperTwo I₀)) (hI₀ : IsCZeroMember Xc I₀)
    (hb : pCoreOf 2 I₀ = pCoreOf 2 Xc ∧ IsSymThreeOrSUThreeTwo (↥I₀ ⧸ CFSG.pCore 2 ↥I₀))
    (hq : q ∈ normalizer (Xc : Set G)) : I₀.map (MulAut.conj q).toMonoidHom = I₀ := by
  have hIq := hI₀.map_conj hq
  have hbq := shape_map_conj hb hq
  have hO : oUpperTwo (I₀.map (MulAut.conj q).toMonoidHom) =
      (oUpperTwo I₀).map (MulAut.conj q).toMonoidHom :=
    (CFSG.AGLEmbedding.SUPair.map_oUpperTwo _ I₀).symm
  have hcard : Nat.card (oUpperTwo (I₀.map (MulAut.conj q).toMonoidHom)) =
      Nat.card (oUpperTwo I₀) := by
    rw [hO, card_map_of_injective (MulAut.conj q).injective]
  have heq := oUpperTwo_eq_of_rank hIq hI₀ hbq hb hrank hRq hR h3 hcard
  exact eq_of_oUpperTwo_eq_cZero hD hIq hI₀ hbq hb heq

end NoRem

@[expose] def commMod' (H A : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ H ∧ ∀ b ∈ A, b * g * b⁻¹ * g⁻¹ ∈ pCoreOf 2 H}
  one_mem' := ⟨H.one_mem, fun b _ => by simp [(pCoreOf 2 H).one_mem]⟩
  mul_mem' := by
    rintro g h ⟨hg, hgA⟩ ⟨hh, hhA⟩
    refine ⟨H.mul_mem hg hh, fun b hb => ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (localGroup_le_normalizer_pCoreOf 2 H hg) _).mp (hhA b hb)
    have e : b * (g * h) * b⁻¹ * (g * h)⁻¹ =
        (b * g * b⁻¹ * g⁻¹) * (g * (b * h * b⁻¹ * h⁻¹) * g⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 H).mul_mem (hgA b hb) h1
  inv_mem' := by
    rintro g ⟨hg, hgA⟩
    refine ⟨H.inv_mem hg, fun b hb => ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (localGroup_le_normalizer_pCoreOf 2 H (H.inv_mem hg)) _).mp
      ((pCoreOf 2 H).inv_mem (hgA b hb))
    have e : b * g⁻¹ * b⁻¹ * g⁻¹⁻¹ = g⁻¹ * (b * g * b⁻¹ * g⁻¹)⁻¹ * g⁻¹⁻¹ := by group
    rw [e]
    exact h1

variable (G) in

theorem agl81ElevenSevenFourL34_of_noRem (hD : SubnormalSUThreeTwoDetermined)
    (h9N : AGL81NineThreeNormalCfg G) (h1013 : AGL81TenThirteenAt G)
    (h93r : AGL81NineThreeRankCfg G) (h1062 : AGL81TenSixTwelveCfg G)
    (h1031 : AGL81TenThreeOneAt G) :
    AGL81ElevenSevenFourL34 G := by
  intro hS p P M H Q K hσ hd hnc L hL hLn hno hp hK b hb x hx
  subst hp
  haveI hKn : K.Normal := h9N hS 3 P M H Q K hd
  have hZ : Subgroup.center K = ⊥ := CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.center_eq_bot_of_isLinThreeFour hK
  have h1 : ∀ I₀ ∈ cZero (H ⊓ L),
      CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ d1PlusCore 3 H K := by
    intro I₀ hI₀
    rcases h1013 hS 3 P M H Q K hσ hd L hL I₀ hI₀ with h | ⟨hp3, hA, hI⟩
    · exact h
    · exact absurd ⟨hp3, hA, I₀, hI₀, hI⟩ hno
  have hMn : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
  have hQN : ∀ q ∈ Q, q ∈ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have e1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hd.le_H hq)) y
    have e2 := Subgroup.mem_normalizer_iff.mp (hMn (hd.base.1 hq)) y
    exact ⟨fun hy => ⟨e1.mp hy.1, e2.mp hy.2⟩, fun hy => ⟨e1.mpr hy.1, e2.mpr hy.2⟩⟩
  have hrank := h93r hS 3 P M H Q K hd
  have hmem : ∀ I₀ ∈ cZero (H ⊓ L), ∀ b' ∈ d1LiftX 3 H Q K, ∀ y ∈ I₀,
      b' * y * b'⁻¹ * y⁻¹ ∈ pCoreOf 2 (H ⊓ L) := by
    intro I₀ hI₀ b' hb' y hy
    have hb'Q : b' ∈ Q := d1LiftX_le 3 H Q K hb'
    by_cases hIX : I₀ ≤ d1PlusCore 3 H K
    · have hT := h1062 hS 3 P M H Q K hd L hL I₀ hI₀ hIX b' hb' y hy
      have hJ : b' * y * b'⁻¹ * y⁻¹ ∈ H ⊓ L :=
        (H ⊓ L).mul_mem ((Subgroup.mem_normalizer_iff.mp (hQN b' hb'Q) y).mp (hI₀.le hy))
          ((H ⊓ L).inv_mem (hI₀.le hy))
      exact inf_pCoreOf_le (inf_le_left : H ⊓ L ≤ H) ⟨hJ, hT⟩
    · have hsh : pCoreOf 2 I₀ = pCoreOf 2 (H ⊓ L) ∧
          IsSymThreeOrSUThreeTwo (↥I₀ ⧸ CFSG.pCore 2 ↥I₀) :=
        hI₀.shape.resolve_left fun hc => hIX (by
          have := h1 I₀ hI₀
          rwa [SevenFourL34.oUpperTwo_eq_of_perfect hc.perfect] at this)
      have hnorm : ∀ q ∈ Q, I₀.map (MulAut.conj q).toMonoidHom = I₀ := fun q hq =>
        NoRem.map_conj_eq_of_cZero hD hrank (h1 I₀ hI₀) (h1 _ (hI₀.map_conj (hQN q hq)))
          (h1031 hS 3 P M H Q K hd L hL I₀ hI₀) hI₀ hsh (hQN q hq)
      have hAN : d1LiftX 3 H Q K ≤ Subgroup.normalizer (I₀ : Set G) := fun a ha =>
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hnorm a (d1LiftX_le 3 H Q K ha))
      have := SevenFourL34.commutator_mem_pCoreOf hKn hZ SevenFourL34.kFactSUThreeTwoNoNormalThreePrime_holds (hI₀.le.trans inf_le_left)
        (SevenFourL34.d1LiftX_le_kPre 3 H Q K) hAN (h1 I₀ hI₀) hsh.2 b' hb' y hy
      rwa [hsh.1] at this
  have hJS : jZero H L ≤ commMod' (H ⊓ L) (d1LiftX 3 H Q K) :=
    iSup₂_le fun I₀ hI₀ y hy => ⟨hI₀.le hy, fun b' hb' => hmem I₀ hI₀ b' hb' y hy⟩
  have hT : b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (H ⊓ L) := (hJS hx).2 b hb
  have hbN : b ∈ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) :=
    hQN b (d1LiftX_le 3 H Q K hb)
  have hJ : b * x * b⁻¹ * x⁻¹ ∈ jZero H L :=
    (jZero H L).mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_jZero H L hbN) x).mp hx)
      ((jZero H L).inv_mem hx)
  exact inf_pCoreOf_le (jZero_le H L) ⟨hJ, hT⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
