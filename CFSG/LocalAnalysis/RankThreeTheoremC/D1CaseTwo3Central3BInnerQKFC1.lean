module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQKFC1Cent
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQKFC1Aut
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQResidueLeaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQKFAThree
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3ReducedA
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.PreuniquenessRankFour.Helpers

@[expose] def KFactU33SylowIrr : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X),
    (∃ q : TauCeti.PrimePower, q.p = 3 ∧ q.card = 3 ∧
      CFSG.RankThree.PartOne.Census3.IsoLie ↥K (.twistedA 2 q)) →
    ∀ B : Subgroup X, B ≤ K → IsPGroup 3 B → ¬ 3 ∣ B.relIndex K →
      ∀ D : Subgroup X, D ≤ B → K ⊓ normalizer (B : Set X) ≤ normalizer (D : Set X) →
        D ≤ (frattini ↥B).map B.subtype ∨ D = B

@[expose] def KFactKFC1Central : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Sylow 3 X) (X₀ : Subgroup X) (x : X),
    CatalogSimpleSections X → ReducedNongeneration 3 X T X₀ →
    Open.pRank 3 (T : Subgroup X) = 3 → x ∈ center X → orderOf x = 3 →
    (∀ D : Subgroup X, D ≤ X₀ → IsPGroup 3 D → ¬ IsCyclic (D ⊔ zpowers x : Subgroup X) →
      normalizer (D : Set X) ≤ X₀) →
    ∀ K : Subgroup X, IsComponentOf K ⊤ → x ∈ K →
      (X₀ ≤ normalizer (((T : Subgroup X) ⊓ K : Subgroup X) : Set X) ∧
        K ⊓ normalizer (((T : Subgroup X) ⊓ K : Subgroup X) : Set X) ≤ X₀) ∧
      (∀ D : Subgroup X, D ≤ (T : Subgroup X) ⊓ K →
        K ⊓ normalizer (((T : Subgroup X) ⊓ K : Subgroup X) : Set X) ≤ normalizer (D : Set X) →
        D ≤ (frattini ↥((T : Subgroup X) ⊓ K)).map ((T : Subgroup X) ⊓ K).subtype ∨
          D = (T : Subgroup X) ⊓ K) ∧
      (∃ Q : Subgroup X, Q ≤ centralizer (((T : Subgroup X) ⊓ K : Subgroup X) : Set X) ∧
        centralizer (((T : Subgroup X) ⊓ K : Subgroup X) : Set X) ≤ normalizer (Q : Set X) ∧
        Nat.Coprime 3 (Nat.card Q) ∧
        ∀ g ∈ centralizer (((T : Subgroup X) ⊓ K : Subgroup X) : Set X), ∃ n : ℕ, g ^ 3 ^ n ∈ Q) ∧
      (∀ y ∈ centralizer (((T : Subgroup X) ⊓ K : Subgroup X) : Set X), IsPGroup 3 (zpowers y) →
        ∃ k ∈ K ⊓ centralizer (((T : Subgroup X) ⊓ K : Subgroup X) : Set X),
          y * k⁻¹ ∈ centralizer (K : Set X)) ∧
      (IsCyclic (centralizer (K : Set X)) ∧ IsPGroup 3 (centralizer (K : Set X))) ∧
      K.Normal

namespace InnerQ.KFC1

variable {X : Type} [Group X] [Finite X] {T : Sylow 3 X} {X₀ : Subgroup X} {x : X}

theorem le_two_of_isElemAbelian (hred : ReducedNongeneration 3 X T X₀)
    (hT3 : Open.pRank 3 (T : Subgroup X) = 3) (hxZ : x ∈ center X) (hxo : orderOf x = 3)
    {K : Subgroup X} (hxK : x ∉ K) {E : Subgroup X} (hET : E ≤ (T : Subgroup X) ⊓ K)
    (hE : IsElemAbelian 3 E) {a : ℕ} (ha : Nat.card E = 3 ^ a) : a ≤ 2 := by
  by_contra h
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hxp : x ^ 3 = 1 := hxo ▸ pow_orderOf_eq_one x
  have hEx : E ≤ centralizer ((zpowers x : Subgroup X) : Set X) :=
    le_centralizer_iff.mp (zpowers_le.mpr (center_le_centralizer _ hxZ))
  have hJ := elementary_abelian_sup_of_commuting 3 hE
    (CFSG.AGLEmbedding.isElemAbelian_zpowers hxp) hEx
  have hxT : x ∈ (T : Subgroup X) := mem_sylow_of_mem_center hxZ hxo T
  have hJT : E ⊔ zpowers x ≤ T := sup_le (hET.trans inf_le_left) (zpowers_le.mpr hxT)
  have heq := elementary_subgroup_eq_of_rank_bound 3 hp hJ le_sup_left a ha
    (by have := pRank_mono 3 hp hJT; omega)
  exact hxK ((hET (heq ▸ mem_sup_right (mem_zpowers x))).2)

theorem normalizer_le_subgroupOf (hxo : orderOf x = 3)
    (hΓ : ∀ D : Subgroup X, D ≤ X₀ → IsPGroup 3 D → ¬ IsCyclic (D ⊔ zpowers x : Subgroup X) →
      normalizer (D : Set X) ≤ X₀)
    {K : Subgroup X} (hxK : x ∉ K) {D : Subgroup K} (hDM : D ≤ X₀.subgroupOf K)
    (hDp : IsPGroup 3 D) (hD1 : D ≠ ⊥) : normalizer (D : Set K) ≤ X₀.subgroupOf K := by
  intro n hn
  set D' := D.map K.subtype
  have hD'X₀ : D' ≤ X₀ := by
    rintro _ ⟨d, hd, rfl⟩
    exact mem_subgroupOf.mp (hDM hd)
  have hD'1 : D' ≠ ⊥ := fun h => hD1 ((map_eq_bot_iff_of_injective _ K.subtype_injective).mp h)
  have hle := hΓ D' hD'X₀ (hDp.map _)
    (InnerQ.KFAThree.not_isCyclic_sup hxo hxK (map_subtype_le _) hD'1 (hDp.map _))
  refine mem_subgroupOf.mpr (hle ?_)
  rw [mem_normalizer_iff]
  intro y
  by_cases hy : y ∈ K
  · constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨_, (mem_normalizer_iff.mp hn d).mp hd, rfl⟩
    · rintro ⟨d, hd, hdy⟩
      have : (⟨y, hy⟩ : K) ∈ D := (mem_normalizer_iff.mp hn ⟨y, hy⟩).mpr (by
        rw [show n * ⟨y, hy⟩ * n⁻¹ = d from Subtype.ext hdy.symm]
        exact hd)
      exact ⟨_, this, rfl⟩
  · refine iff_of_false (fun ⟨d, _, hdy⟩ => hy (hdy ▸ d.2)) fun ⟨d, _, hdy⟩ => hy ?_
    have hdy' : (d : X) = n * y * (n : X)⁻¹ := hdy
    have h := mul_mem (mul_mem (inv_mem n.2) d.2) n.2
    rw [hdy'] at h
    simpa [mul_assoc] using h

theorem isoLie_of_top {K : Type} [Group K] {d : TauCeti.LieTypeIndex}
    (h : CFSG.RankThree.PartOne.Census3.IsoLie ↥(⊤ : Subgroup K) d) :
    CFSG.RankThree.PartOne.Census3.IsoLie K d := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  exact ⟨hv, ⟨Subgroup.topEquiv.symm.trans e⟩⟩

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree in
theorem kfc1_local
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hO : KFactOutCyclic)
    (hS : KFactSeitzCyc) (hcat : CatalogSimpleSections X)
    (hred : ReducedNongeneration 3 X T X₀) (hT3 : Open.pRank 3 (T : Subgroup X) = 3)
    (hxZ : x ∈ center X) (hxo : orderOf x = 3)
    (hΓ : ∀ D : Subgroup X, D ≤ X₀ → IsPGroup 3 D → ¬ IsCyclic (D ⊔ zpowers x : Subgroup X) →
      normalizer (D : Set X) ≤ X₀)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) (hxK : x ∉ K) (TK : Sylow 3 K)
    (hTK : (TK : Subgroup K).map K.subtype = (T : Subgroup X) ⊓ K) :
    X₀.subgroupOf K = normalizer ((TK : Subgroup K) : Set K) ∧ SqInner K TK ∧
      (IsCyclic (TK : Subgroup K) ∨
        (∀ D : Subgroup K, D ≤ TK →
          normalizer ((TK : Subgroup K) : Set K) ≤ normalizer (D : Set K) →
          D = ⊥ ∨ D = TK) ∨
        ∃ q : TauCeti.PrimePower, q.p = 3 ∧ q.card = 3 ∧
          CFSG.RankThree.PartOne.Census3.IsoLie K (.twistedA 2 q)) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  haveI hKn : K.Normal := hred.normal_of_isComponentOf_of_center hxZ hxo hK
  have hZK : center K = ⊥ := by
    rcases hred.mem_or_rankOne_of_center hxZ hxo hK with ⟨⟨k, -, hk⟩, -⟩ | ⟨-, hZ, -⟩
    · exact absurd (hk ▸ k.2) hxK
    · exact hZ
  have hKX₀ : ¬ K ≤ X₀ := hred.not_le_of_not_mem_of_center hxZ hxo hK hKn hxK
  have hTX₀ : (T : Subgroup X) ≤ X₀ := hred.sylow_le
  set M : Subgroup K := X₀.subgroupOf K with hMdef
  have hMtop : M ≠ ⊤ := fun h => hKX₀ fun k hk => by
    have : (⟨k, hk⟩ : K) ∈ M := h ▸ mem_top _
    exact mem_subgroupOf.mp this
  have hTKM : (TK : Subgroup K) ≤ M := fun k hk => by
    have : (k : X) ∈ (T : Subgroup X) ⊓ K := hTK ▸ ⟨k, hk, rfl⟩
    exact mem_subgroupOf.mpr (hTX₀ this.1)
  have hNM : ∀ D : Subgroup K, D ≤ TK → D ≠ ⊥ → normalizer (D : Set K) ≤ M := fun D hD hD1 =>
    normalizer_le_subgroupOf hxo hΓ hxK (hD.trans hTKM) (TK.isPGroup'.to_le hD) hD1
  have hTK1 : (TK : Subgroup K) ≠ ⊥ := by
    obtain ⟨t, ⟨htT, htK⟩, hto, -⟩ := exists_mem_sylow_inf_component hp (by norm_num)
      hred.core_eq_bot T hK
    intro h
    have : t ∈ (TK : Subgroup K).map K.subtype := hTK ▸ ⟨htT, htK⟩
    rw [h, Subgroup.map_bot, mem_bot] at this
    rw [this, orderOf_one] at hto
    omega
  have hA : ∀ E : Subgroup K, E ≤ TK → IsElemAbelian 3 E → ∀ a, Nat.card E = 3 ^ a → a ≤ 2 :=
    fun E hE he a ha => le_two_of_isElemAbelian hred hT3 hxZ hxo hxK (E := E.map K.subtype)
      (by rw [← hTK]; exact map_mono hE) (he.map _)
      (by rw [card_map_of_injective K.subtype_injective]; exact ha)
  haveI hsimple : IsSimpleGroup K :=
    (MulEquiv.isSimpleGroup_congr
      ((QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot)).mp hK.2.2.2
  by_cases hcyc : IsCyclic ((T : Subgroup X) ⊓ K : Subgroup X)
  ·
    have hcycall : ∀ L : Subgroup X, IsComponentOf L ⊤ →
        IsCyclic ((T : Subgroup X) ⊓ L : Subgroup X) := by
      intro L hL
      rw [hred.eq_of_isComponentOf_of_center hxZ hxo hL hK]
      exact hcyc
    have hL28 := hred.isCaseTwoGroup_of_not_le3 hcat hO hS hcycall hT3 hK hKX₀
    obtain ⟨ε₀⟩ := CFSG.AGLEmbedding.KFactProofs.L28Local.nonempty_equiv_G8 hL28
    have hdata := CFSG.AGLEmbedding.KFactProofs.L28Local.l28Data_of_equiv ε₀ TK
    refine ⟨?_, sqInner_l28 hL28 TK, Or.inl ?_⟩
    · rcases hdata.maximal (hNM TK le_rfl hTK1) with h | h
      · exact h
      · exact absurd h hMtop
    · rw [← hTK] at hcyc
      exact isCyclic_of_surjective
        ((TK : Subgroup K).equivMapOfInjective _ K.subtype_injective).symm.toMonoidHom
        (MulEquiv.surjective _)
  ·
    have hncTK : ¬ IsCyclic (TK : Subgroup K) := fun h => hcyc (by
      rw [← hTK]
      exact isCyclic_of_surjective
        ((TK : Subgroup K).equivMapOfInjective _ K.subtype_injective).toMonoidHom
        (MulEquiv.surjective _))
    have hKgrp : CFSG.Open.IsKGroup K := (catalogSimpleSections_iff_isKGroup.mp hcat).subgroup K
    have hnab : ∃ a b : K, a * b ≠ b * a := by
      by_contra h
      push Not at h
      obtain ⟨a, ha⟩ := exists_ne (1 : K)
      have : a ∈ center K := mem_center_iff.mpr fun g => h g a
      rw [hZK, mem_bot] at this
      exact ha this
    have hgam : ∀ y ∈ gammaCore 3 1 (⊤ : Subgroup K) (TK : Subgroup K), y ∈ M := by
      intro y hy
      refine (closure_le M).mpr ?_ hy
      rintro z ⟨-, R, hRT, hR1, hzR⟩
      refine hNM R hRT (fun hR => ?_) hzR
      obtain ⟨E, hER, -, hEc⟩ := pRank_attained 3 hp R
      have hE1 : Nat.card E = 1 := by
        rw [Subgroup.card_eq_one]
        exact le_bot_iff.mp (hR ▸ hER)
      rw [hEc] at hE1
      have : 3 ^ 1 ≤ 3 ^ Open.pRank 3 R := Nat.pow_le_pow_right (by norm_num) hR1
      omega
    have hgamlt : gammaCore 3 1 (⊤ : Subgroup K) (TK : Subgroup K) < ⊤ :=
      lt_of_le_of_ne le_top fun h => hMtop (eq_top_iff.mpr fun y _ =>
        hgam y (by rw [h]; exact mem_top y))
    have hcent : centralizer ((⊤ : Subgroup K) : Set K) = ⊥ := by
      rw [coe_top, centralizer_univ, hZK]
    have hsimpTop : IsSimpleGroup ↥(⊤ : Subgroup K) :=
      (MulEquiv.isSimpleGroup_congr Subgroup.topEquiv).mpr hsimple
    have hnabTop : ∃ a b : ↥(⊤ : Subgroup K), a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨⟨a, mem_top a⟩, ⟨b, mem_top b⟩, fun h => hab (congrArg Subtype.val h)⟩
    have hrk : 2 ≤ Open.pRank 3 (TK : Subgroup K) :=
      two_le_pRank_of_isPGroup_not_isCyclic hp (by norm_num) TK.isPGroup' hncTK
    obtain ⟨-, hmax, hrows⟩ := hG3 K hKgrp ⊤ inferInstance hsimpTop hnabTop hcent TK hrk hgamlt
    simp only [inf_top_eq] at hmax hrows
    have hMeq : ∀ N : Subgroup K,
        gammaCore 3 1 (⊤ : Subgroup K) (TK : Subgroup K) = ⊤ ⊓ N → M = N := by
      intro N hN
      have hle : gammaCore 3 1 (⊤ : Subgroup K) (TK : Subgroup K) ≤ M := hgam
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact absurd (hmax M hlt le_top) hMtop
      · rw [← heq, hN, top_inf_eq]
    have hcard_le : ∀ E : Subgroup K, E ≤ TK → IsElemAbelian 3 E → Nat.card E ≤ 9 := by
      intro E hE he
      obtain ⟨a, ha⟩ := (TK.isPGroup'.to_le hE).exists_card_eq
      have := hA E hE he a ha
      rw [ha]
      calc 3 ^ a ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
        _ = 9 := by norm_num
    rcases hrows with ⟨q, hq, ⟨hv, -⟩, -, -, -, hE, hc⟩ |
        ⟨q, hq, hI, -, hN, -, -, -, E, hET, hEe, hEc⟩ | ⟨m, ⟨hv, -⟩, -, -, -, E, hET, hEe, hEc⟩ |
        ⟨-, hidx, -⟩ | ⟨⟨φ, -⟩, -, hE, h9, hN, J, -, hJ, hirr⟩ |
        ⟨hI, -, -, hE, h9, hN, S, hS, -, -, -, hirr⟩ |
        ⟨⟨hM⟩, -, hE, h9, hN, S, hS, hsup, -, -, hSC, hirr⟩
    ·
      exfalso
      have h9 := hcard_le _ le_rfl hE
      rw [hc] at h9
      obtain ⟨hr, hd⟩ := (TauCeti.LieTypeIndex.valid_iff _).mp hv
      simp only [TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hr hd
      have hcard : q.card = 3 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq]
      have he : q.exponent ≤ 2 := by
        by_contra he
        have : 3 ^ 3 ≤ 3 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases h : q.exponent <;> simp_all
    ·
      have hcard : q.card = 3 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq]
      rw [hcard, ← pow_mul] at hEc
      have h2 := hA E hET hEe _ hEc
      have hq3 : q.card = 3 := by
        have := q.exponent_pos
        rw [hcard, show q.exponent = 1 by omega, pow_one]
      exact ⟨hMeq _ hN, sqInner_u3 hq (isoLie_of_top hI) TK,
        Or.inr (Or.inr ⟨q, hq, hq3, isoLie_of_top hI⟩)⟩
    ·
      exfalso
      have := hA E hET hEe _ hEc
      obtain ⟨hr, -⟩ := (TauCeti.LieTypeIndex.valid_iff _).mp hv
      simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hr
      omega
    ·
      exfalso
      rw [index_top] at hidx
      omega
    ·
      have hJN : J ≤ normalizer ((TK : Subgroup K) : Set K) := by
        refine le_sup_right.trans (hJ.symm.le.trans ?_)
        rw [hN]
        exact inf_le_right
      refine ⟨hMeq _ hN, sqInner_a6 ⟨Subgroup.topEquiv.symm.trans φ⟩ TK hE h9, Or.inr (Or.inl ?_)⟩
      exact fun D hD hDN => hirr D hD (hJN.trans hDN)
    ·
      have hSN : S ≤ normalizer ((TK : Subgroup K) : Set K) := by
        refine hS.trans ?_
        rw [hN]
        exact inf_le_right
      refine ⟨hMeq _ hN, sqInner_l34 (isoLie_of_top hI) TK, Or.inr (Or.inl ?_)⟩
      exact fun D hD hDN => hirr D hD (hSN.trans hDN)
    ·
      have hSN : S ≤ normalizer ((TK : Subgroup K) : Set K) := by
        refine hS.trans ?_
        rw [hN]
        exact inf_le_right
      have hC : ∀ k : K, (∀ b ∈ (TK : Subgroup K), k * b = b * k) → k ∈ (TK : Subgroup K) := by
        intro k hk
        have hkC : k ∈ centralizer ((TK : Subgroup K) : Set K) :=
          mem_centralizer_iff.mpr fun b hb => (hk b hb).symm
        have hkG : k ∈ (TK : Subgroup K) ⊔ S := by
          rw [hsup, hN]
          exact ⟨mem_top k, centralizer_le_normalizer _ hkC⟩
        rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hSN] at hkG
        obtain ⟨a, ha, t, ht, rfl⟩ := Set.mem_mul.mp hkG
        have htC : t ∈ centralizer ((TK : Subgroup K) : Set K) := by
          rw [mem_centralizer_iff]
          intro b hb
          have hab : a * b = b * a := congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
          have hk' := hk b hb
          calc b * t = a⁻¹ * (b * (a * t)) := by
                rw [← mul_assoc b a t, ← hab]
                group
            _ = a⁻¹ * (a * t * b) := by rw [hk']
            _ = t * b := by group
        have ht1 : t = 1 := by
          have : t ∈ S ⊓ centralizer ((TK : Subgroup K) : Set K) := ⟨ht, htC⟩
          rw [hSC, mem_bot] at this
          exact this
        rw [ht1, mul_one]
        exact ha
      exact ⟨hMeq _ hN, sqInner_m11 ⟨Subgroup.topEquiv.symm.trans hM⟩ TK hC,
        Or.inr (Or.inl fun D hD hDN => hirr D hD (hSN.trans hDN))⟩

theorem le_frattini_of_isCyclic {p : ℕ} [Fact p.Prime] {B D : Subgroup X} (hB : IsCyclic B)
    (hBp : IsPGroup p B) (hDB : D ≤ B) (hne : D ≠ B) : D ≤ (frattini ↥B).map B.subtype := by
  set D' := D.subgroupOf B
  have hD'top : D' ≠ ⊤ := fun h => hne (le_antisymm hDB (subgroupOf_eq_top.mp h))
  have hD'le : D' ≤ frattini ↥B := by
    simp only [frattini, Order.radical, le_iInf_iff]
    intro M hM
    obtain ⟨a, ha⟩ := (hBp.to_subgroup D').exists_card_eq
    obtain ⟨b, hb⟩ := (hBp.to_subgroup M).exists_card_eq
    by_cases hab : a ≤ b
    · rw [IsCyclic.subgroup_le_iff_card_dvd, ha, hb]
      exact pow_dvd_pow p hab
    · exfalso
      have hMD : M ≤ D' := by
        rw [IsCyclic.subgroup_le_iff_card_dvd, ha, hb]
        exact pow_dvd_pow p (by omega)
      have hMne : M ≠ D' := fun h => by
        rw [h, ha] at hb
        exact hab (le_of_eq (Nat.pow_right_injective (Fact.out : p.Prime).two_le hb))
      exact hD'top (hM.2 D' (lt_of_le_of_ne hMD hMne))
  intro d hd
  exact ⟨⟨d, hDB hd⟩, hD'le (mem_subgroupOf.mpr hd), rfl⟩

theorem coe_mem_normalizer_map {K : Subgroup X} {H : Subgroup K} {n : K}
    (hn : n ∈ normalizer (H : Set K)) :
    (n : X) ∈ normalizer ((H.map K.subtype : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff]
  intro y
  by_cases hy : y ∈ K
  · constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨_, (mem_normalizer_iff.mp hn d).mp hd, rfl⟩
    · rintro ⟨d, hd, hdy⟩
      have : (⟨y, hy⟩ : K) ∈ H := (mem_normalizer_iff.mp hn ⟨y, hy⟩).mpr (by
        rw [show n * ⟨y, hy⟩ * n⁻¹ = d from Subtype.ext hdy.symm]
        exact hd)
      exact ⟨_, this, rfl⟩
  · refine iff_of_false (fun ⟨d, _, hdy⟩ => hy (hdy ▸ d.2)) fun ⟨d, _, hdy⟩ => hy ?_
    have hdy' : (d : X) = n * y * (n : X)⁻¹ := hdy
    have h := mul_mem (mul_mem (inv_mem n.2) d.2) n.2
    rw [hdy'] at h
    simpa [mul_assoc] using h

end InnerQ.KFC1

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree in
theorem kFactKFC1_of_central
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hO : KFactOutCyclic)
    (hS : KFactSeitzCyc) (hU : KFactU33SylowIrr) (hZ : KFactKFC1Central) : KFactKFC1 := by
  intro X _ _ T X₀ x hcat hred hT3 hxZ hxo hΓ K hK
  by_cases hxK : x ∈ K
  · exact hZ X T X₀ x hcat hred hT3 hxZ hxo hΓ K hK hxK
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  haveI hKn : K.Normal := hred.normal_of_isComponentOf_of_center hxZ hxo hK
  have hKX₀ : ¬ K ≤ X₀ := hred.not_le_of_not_mem_of_center hxZ hxo hK hKn hxK
  have hTX₀ : (T : Subgroup X) ≤ X₀ := hred.sylow_le
  obtain ⟨TK, hTK⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal T
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨hM, hsq, hcase⟩ := InnerQ.KFC1.kfc1_local hG3 hO hS hcat hred hT3 hxZ hxo hΓ hK hxK TK hTK
  set B := (T : Subgroup X) ⊓ K with hBdef
  have hBK : B ≤ K := inf_le_right
  have hBp : IsPGroup 3 B := T.isPGroup'.to_le inf_le_left
  have hmemB : ∀ k : K, (k : X) ∈ B ↔ k ∈ (TK : Subgroup K) := fun k => by
    rw [← hTK]
    exact ⟨fun ⟨k', hk', hkk⟩ => (Subtype.ext hkk : k' = k) ▸ hk', fun hk => ⟨k, hk, rfl⟩⟩
  have hB1 : B ≠ ⊥ := by
    obtain ⟨t, ⟨htT, htK⟩, hto, -⟩ := exists_mem_sylow_inf_component hp (by norm_num)
      hred.core_eq_bot T hK
    intro h
    have : t ∈ B := ⟨htT, htK⟩
    rw [h, mem_bot] at this
    rw [this, orderOf_one] at hto
    omega
  have hconjB : ∀ g ∈ X₀, ∀ b ∈ B, g * b * g⁻¹ ∈ B := by
    intro g hg b hb
    have hbK : g * b * g⁻¹ ∈ K := hKn.conj_mem b (hBK hb) g
    set b' : K := ⟨g * b * g⁻¹, hbK⟩
    have hb'M : b' ∈ X₀.subgroupOf K :=
      mem_subgroupOf.mpr (mul_mem (mul_mem hg (hTX₀ hb.1)) (inv_mem hg))
    rw [hM] at hb'M
    have hb'p : IsPGroup 3 (zpowers b') := by
      obtain ⟨n, hn⟩ := hBp ⟨b, hb⟩
      have hdvd : orderOf b' ∣ 3 ^ n := by
        refine orderOf_dvd_of_pow_eq_one (Subtype.ext ?_)
        simp only [b', SubgroupClass.coe_pow, OneMemClass.coe_one]
        rw [conj_pow]
        have : b ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
        rw [this]
        group
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have hmem : b' ∈ zpowers b' ⊓ normalizer ((TK : Subgroup K) : Set K) :=
      ⟨mem_zpowers _, hb'M⟩
    have hmem' : b' ∈ zpowers b' ⊓ (TK : Subgroup K) := by
      rw [← hb'p.inf_normalizer_sylow TK]
      exact hmem
    exact (hmemB b').mpr hmem'.2
  have hXN : X₀ ≤ normalizer (B : Set X) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro b
    refine ⟨hconjB g hg b, fun hb => ?_⟩
    have := hconjB g⁻¹ (inv_mem hg) _ hb
    simpa [mul_assoc] using this
  have hNX : K ⊓ normalizer (B : Set X) ≤ X₀ :=
    inf_le_right.trans (hΓ B (inf_le_left.trans hTX₀) hBp
      (InnerQ.KFAThree.not_isCyclic_sup hxo hxK hBK hB1 hBp))
  have hb : ∀ D : Subgroup X, D ≤ B → K ⊓ normalizer (B : Set X) ≤ normalizer (D : Set X) →
      D ≤ (frattini ↥B).map B.subtype ∨ D = B := by
    intro D hDB hDN
    rcases hcase with hc | hirr | hU33
    · by_cases hDe : D = B
      · exact Or.inr hDe
      · refine Or.inl (InnerQ.KFC1.le_frattini_of_isCyclic ?_ hBp hDB hDe)
        rw [← hTK]
        exact isCyclic_of_surjective
          ((TK : Subgroup K).equivMapOfInjective _ K.subtype_injective).toMonoidHom
          (MulEquiv.surjective _)
    · set D' := D.subgroupOf K
      have hD'T : D' ≤ TK := fun d hd => (hmemB d).mp (hDB (mem_subgroupOf.mp hd))
      have hD'N : normalizer ((TK : Subgroup K) : Set K) ≤ normalizer (D' : Set K) := by
        intro n hn
        have hnX : (n : X) ∈ normalizer (D : Set X) := hDN ⟨n.2, by
          have := InnerQ.KFC1.coe_mem_normalizer_map hn
          rwa [hTK] at this⟩
        rw [mem_normalizer_iff]
        intro d
        simp only [D', mem_subgroupOf, coe_mul, coe_inv]
        exact mem_normalizer_iff.mp hnX d
      rcases hirr D' hD'T hD'N with h | h
      · left
        have : D = ⊥ := by
          rw [eq_bot_iff]
          intro d hd
          have : (⟨d, hDB hd |>.2⟩ : K) ∈ D' := mem_subgroupOf.mpr hd
          rw [h, mem_bot] at this
          rw [mem_bot]
          exact congrArg Subtype.val this
        rw [this]
        exact bot_le
      · right
        refine le_antisymm hDB fun b hb => ?_
        have : (⟨b, hBK hb⟩ : K) ∈ D' := h ▸ (hmemB _).mp hb
        exact mem_subgroupOf.mp this
    · refine hU X K hU33 B hBK hBp ?_ D hDB hDN
      rw [relIndex, show B.subgroupOf K = TK by
        ext k
        rw [mem_subgroupOf]
        exact hmemB k]
      exact TK.not_dvd_index
  have hC := InnerQ.KFC1.centralizer_isPGroup_isCyclic hred hxZ hxo hK hKX₀
  have hsq' : ∀ f : MulAut K, (∀ b : K, (b : X) ∈ B → f b = b) →
      ∃ t : K, (t : X) ∈ B ∧ f ^ 2 = MulAut.conj t := by
    intro f hf
    obtain ⟨t, ht, hft⟩ := hsq f fun b hb => hf b ((hmemB b).mpr hb)
    exact ⟨t, (hmemB t).mpr ht, hft⟩
  obtain ⟨hcc, hdd⟩ := InnerQ.KFC1.centralizer_facts hBK hBp hxZ hxo hC hsq'
  exact ⟨⟨hXN, hNX⟩, hb, hcc, hdd, ⟨hC.2, hC.1⟩, hKn⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
