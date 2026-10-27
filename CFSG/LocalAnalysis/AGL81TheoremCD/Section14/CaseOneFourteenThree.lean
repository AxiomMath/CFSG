module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenThreeComp
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenTwo
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneTransport
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenTwoDouble
import CFSG.RankThree.PartOne.S11d.FinalLemmas
import CFSG.RankThree.PartOne.S12.Sec15Frattini
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KNormalRank
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.GroupTheory.QuasiDihedralFusion.SemidihedralModel

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem two_kComp_sup_data
    {M H E Q J : Subgroup G} {N' : Subgroup G} (h : S14Choice G M H E Q J)
    (hA : TypeA M H) (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    (hL : PLayerNotLeAt M) (hNK : N' ≤ Subgroup.normalizer (kSub 3 M N' : Set G))
    (hQN' : Q ≤ N') (hN'C : HypCGen G M 3 E N') (hJK' : IsKComp M N' J)
    {J' : Subgroup G} (hJ'comp : IsKComp M N' J') (hJ'type : IsSL34Star J' ∨ Is3A6Star J')
    (hJ'ne : J' ≠ J) (hsupK' : kSub 3 M N' = J ⊔ J')
    (hK'J : kSub 3 M N' ≤ Subgroup.normalizer (J : Set G))
    (hK'J' : kSub 3 M N' ≤ Subgroup.normalizer (J' : Set G))
    (hQJ' : Q ≤ Subgroup.normalizer (J' : Set G))
    (hJS : IsSL34Star J) (hcardQ : Nat.card ↥Q = 3 ^ 5) :
    ∃ T₁ T₂ : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 3 T₁ J ∧
      CFSG.ABGLocalTools.IsSylowOf 3 T₂ J' ∧
      Nat.card ↥T₁ = 27 ∧ Nat.card ↥T₂ = 27 ∧
      T₁ ⊓ T₂ = (Subgroup.center ↥T₁).map T₁.subtype ∧
      Nat.card ↥((Subgroup.center ↥T₁).map T₁.subtype) = 3 ∧ Q = T₁ ⊔ T₂ := by
  classical
  have hQJ : Q ≤ Subgroup.normalizer (J : Set G) := h.Q_le_normalizer_J hpre hU
  have hX_le : Q ⊔ kSub 3 M N' ≤
      Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (J' : Set G) :=
    sup_le (le_inf hQJ hQJ') (le_inf hK'J hK'J')
  have hXN' : Q ⊔ kSub 3 M N' ≤ N' := sup_le hQN' (kSub_le 3 M N')
  obtain ⟨R, hRsyl, hQR⟩ := CFSG.RankThree.PartOne.exists_isSylowOf_ge
    (p := 3) (K := Q ⊔ kSub 3 M N') (Q := Q) le_sup_left h.sylow.isPGroup
  have hRJ : R ≤ Subgroup.normalizer (J : Set G) := hRsyl.le.trans (hX_le.trans inf_le_left)
  have hRJ' : R ≤ Subgroup.normalizer (J' : Set G) := hRsyl.le.trans (hX_le.trans inf_le_right)
  have hT₁syl : CFSG.ABGLocalTools.IsSylowOf 3 (R ⊓ J) J :=
    hRsyl.inf_of_le_normalizer (hJK'.1.trans le_sup_right) (hX_le.trans inf_le_left)
  have hT₂syl : CFSG.ABGLocalTools.IsSylowOf 3 (R ⊓ J') J' :=
    hRsyl.inf_of_le_normalizer (hJ'comp.1.trans le_sup_right) (hX_le.trans inf_le_right)
  have hRT₁ : R ≤ Subgroup.normalizer ((R ⊓ J : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer hRJ).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hRT₂ : R ≤ Subgroup.normalizer ((R ⊓ J' : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer hRJ').trans Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨hEsup, hcardsup, -, hinfT, -⟩ :=
    hN'C.le_sup_of_two_kComp (hL 3 E N' hN'C) hJ'ne.symm hJK' hJ'comp hJS hJ'type
      hT₁syl hT₂syl hRsyl.isPGroup (hRsyl.le.trans hXN') (h.E_le_Q.trans hQR)
      inf_le_left inf_le_left hRJ hRJ' hRT₁ hRT₂
  have hcardT₁ : Nat.card ↥(R ⊓ J) = 27 :=
    (IsKComp.sylow_three_structure hJK' (Or.inl hJS) hT₁syl).1
  have hcardT₂ : Nat.card ↥(R ⊓ J') = 27 :=
    (IsKComp.sylow_three_structure hJ'comp hJ'type hT₂syl).1
  have hZcardT₁ : Nat.card ↥((Subgroup.center ↥(R ⊓ J)).map (R ⊓ J).subtype) = 3 :=
    (IsKComp.sylow_three_structure hJK' (Or.inl hJS) hT₁syl).2.2.2
  have hQeq : Q = (R ⊓ J) ⊔ (R ⊓ J') := by
    have hQle : Q ≤ (R ⊓ J) ⊔ (R ⊓ J') := by
      calc Q = (Q ⊓ J) ⊔ E := (h.inf_J_sup_E hA hpre hU hL).symm
        _ ≤ (R ⊓ J) ⊔ (R ⊓ J') :=
          sup_le ((le_inf (inf_le_left.trans hQR) inf_le_right).trans le_sup_left) hEsup
    exact Subgroup.eq_of_le_of_card_ge hQle (by rw [hcardQ, hcardsup])
  exact ⟨R ⊓ J, R ⊓ J', hT₁syl, hT₂syl, hcardT₁, hcardT₂, hinfT, hZcardT₁, hQeq⟩

private theorem two_kComp_fac {M N' J J' T₁ T₂ Q : Subgroup G}
    (hsupK' : kSub 3 M N' = J ⊔ J')
    (hT₁ : CFSG.ABGLocalTools.IsSylowOf 3 T₁ J)
    (hT₂ : CFSG.ABGLocalTools.IsSylowOf 3 T₂ J')
    (hcardT₁ : Nat.card ↥T₁ = 27) (hcardT₂ : Nat.card ↥T₂ = 27)
    (hinfT : T₁ ⊓ T₂ = (Subgroup.center ↥T₁).map T₁.subtype)
    (hZcard : Nat.card ↥((Subgroup.center ↥T₁).map T₁.subtype) = 3)
    (hQeq : Q = T₁ ⊔ T₂) (hcardQ : Nat.card ↥Q = 3 ^ 5)
    (hNN' : J ≤ Subgroup.normalizer (J' : Set G)) :
    (Nat.card ↥(kSub 3 M N')).factorization 3 = 5 := by
  have hfacJ : (Nat.card ↥J).factorization 3 = 3 := by
    have h1 : 3 ^ (Nat.card ↥J).factorization 3 = 3 ^ 3 := by
      rw [← CFSG.ABGLocalTools.IsSylowOf.card_eq hT₁, hcardT₁]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  have hfacJ' : (Nat.card ↥J').factorization 3 = 3 := by
    have h1 : 3 ^ (Nat.card ↥J').factorization 3 = 3 ^ 3 := by
      rw [← CFSG.ABGLocalTools.IsSylowOf.card_eq hT₂, hcardT₂]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  have hcard_sup : Nat.card ↥(J ⊔ J') * Nat.card ↥(J ⊓ J') =
      Nat.card ↥J * Nat.card ↥J' :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hNN'
  have hTinfcard : Nat.card ↥(T₁ ⊓ T₂) = 3 := by
    rw [hinfT]
    exact hZcard
  have hdvd : 3 ∣ Nat.card ↥(J ⊓ J') := by
    have h := Subgroup.card_dvd_of_le
      (le_inf (inf_le_left.trans hT₁.le) (inf_le_right.trans hT₂.le) : T₁ ⊓ T₂ ≤ J ⊓ J')
    rwa [hTinfcard] at h
  have hfac_mul : ∀ a b : ℕ, a ≠ 0 → b ≠ 0 →
      (a * b).factorization 3 = a.factorization 3 + b.factorization 3 := by
    intro a b ha hb
    rw [Nat.factorization_mul ha hb]
    simp
  have hfac_eq : (Nat.card ↥(J ⊔ J')).factorization 3 +
      (Nat.card ↥(J ⊓ J')).factorization 3 = 6 := by
    rw [← hfac_mul (Nat.card ↥(J ⊔ J')) (Nat.card ↥(J ⊓ J'))
        (Nat.card_pos.ne') (Nat.card_pos.ne'), hcard_sup,
      hfac_mul (Nat.card ↥J) (Nat.card ↥J') (Nat.card_pos.ne') (Nat.card_pos.ne'),
      hfacJ, hfacJ']
  have hc1 : 1 ≤ (Nat.card ↥(J ⊓ J')).factorization 3 := by
    have h3 : 3 ^ 1 ∣ Nat.card ↥(J ⊓ J') := by
      rw [pow_one]
      exact hdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      (Nat.card_pos.ne')).mp h3
  have hc2 : 5 ≤ (Nat.card ↥(J ⊔ J')).factorization 3 := by
    have h5 : 3 ^ 5 ∣ Nat.card ↥(J ⊔ J') := by
      rw [← hcardQ, hQeq]
      exact Subgroup.card_dvd_of_le
        (sup_le (hT₁.le.trans le_sup_left) (hT₂.le.trans le_sup_right))
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      (Nat.card_pos.ne')).mp h5
  have hfac_sup : (Nat.card ↥(J ⊔ J')).factorization 3 = 5 := by omega
  rw [hsupK']
  exact hfac_sup

private theorem two_kComp_sylow
    {M H E Q J : Subgroup G} {N' : Subgroup G} (h : S14Choice G M H E Q J)
    (hA : TypeA M H) (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    (hL : PLayerNotLeAt M) (hNK : N' ≤ Subgroup.normalizer (kSub 3 M N' : Set G))
    (hQN' : Q ≤ N') (hN'C : HypCGen G M 3 E N') (hJK' : IsKComp M N' J)
    {J' : Subgroup G} (hJ'comp : IsKComp M N' J') (hJ'type : IsSL34Star J' ∨ Is3A6Star J')
    (hJ'ne : J' ≠ J) (hsupK' : kSub 3 M N' = J ⊔ J')
    (hK'J : kSub 3 M N' ≤ Subgroup.normalizer (J : Set G))
    (hK'J' : kSub 3 M N' ≤ Subgroup.normalizer (J' : Set G))
    (hQJ' : Q ≤ Subgroup.normalizer (J' : Set G))
    (hJS : IsSL34Star J) (hcardQ : Nat.card ↥Q = 3 ^ 5) :
    CFSG.ABGLocalTools.IsSylowOf 3 Q (kSub 3 M N') := by
  obtain ⟨T₁, T₂, hT₁, hT₂, hc₁, hc₂, hinfT, hZ, hQeq⟩ :=
    two_kComp_sup_data h hA hpre hU hL hNK hQN' hN'C hJK' hJ'comp hJ'type hJ'ne hsupK'
      hK'J hK'J' hQJ' hJS hcardQ
  have hfac := two_kComp_fac hsupK' hT₁ hT₂ hc₁ hc₂ hinfT hZ hQeq hcardQ
    (hJK'.1.trans hK'J')
  have hQle : Q ≤ kSub 3 M N' := by
    rw [hQeq, hsupK']
    exact sup_le (hT₁.le.trans le_sup_left) (hT₂.le.trans le_sup_right)
  exact CFSG.ABGLocalTools.isSylowOf_of_card hQle (by rw [hcardQ, hfac])

private theorem two_kComp_choice
    {M H E Q J : Subgroup G} {N' : Subgroup G} (h : S14Choice G M H E Q J)
    (hA : TypeA M H) (hU : NineNineOneAt M) (hJS : IsSL34Star J)
    (hJK' : IsKComp M N' J) (hN'Q : N' ∈ H2StarFam M Q) (hQN' : Q ≤ N')
    (hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q (kSub 3 M N')) :
    S14Choice G M N' E Q J := by
  have hE : E ≤ kSub 3 M N' := h.E_le_Q.trans hQsyl.le
  have hQsyl' : CFSG.ABGLocalTools.IsSylowOf 3 Q (kSub 3 M N' ⊔ E) := by
    rw [sup_eq_left.mpr hE]
    exact hQsyl
  exact
    { cstar := h.cstar
      maxLocal := h.maxLocal
      sigma_nonempty := h.sigma_nonempty
      mem := ⟨3, Q, h.Q_mem_QSet hU, hN'Q⟩
      E_le_H := h.E_le_Q.trans hQN'
      elem := h.elem
      card := h.card
      gamma := h.gamma
      E_le_Q := h.E_le_Q
      sylow := hQsyl'
      J_comp := ⟨hJK'.1, hJK'.isSubnormal, h.J_comp.2.2.1, h.J_comp.2.2.2⟩
      J_star := ⟨⟨N', hN'Q, hJK', Or.inl hJS.1⟩, h.J_star.2⟩
      prefA := fun _ => ⟨J, hJK', hJS⟩
      prefB := fun hno _ => absurd ⟨H, h.mem, hA⟩ hno }

private theorem two_kComp_frattini
    {M E Q J : Subgroup G} {N' : Subgroup G} {J' : Subgroup G} {n : G}
    (h' : S14Choice G M N' E Q J) (hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q (kSub 3 M N'))
    (hNK : N' ≤ Subgroup.normalizer (kSub 3 M N' : Set G))
    (hK'J' : kSub 3 M N' ≤ Subgroup.normalizer (J' : Set G))
    (hQnormM : Subgroup.normalizer (Q : Set G) ≤ M) (hnN' : n ∈ N')
    (hJ'eq : J' = J.map (MulAut.conj n).toMonoidHom) :
    ∃ t : G, t ∈ N' ∧ t ∈ Subgroup.normalizer (Q : Set G) ∧
      S14Choice G M N' E Q J' := by
  obtain ⟨k, hkK', hkt⟩ :=
    CFSG.RankThree.PartOne.Sec15Frattini.exists_mem_normalizer_of_isSylowOf hQsyl (hNK hnN')
  let t : G := k⁻¹ * n
  have htN' : t ∈ N' := N'.mul_mem (N'.inv_mem (kSub_le 3 M N' hkK')) hnN'
  have htQ : t ∈ Subgroup.normalizer (Q : Set G) := hkt
  have htM : t ∈ M := hQnormM htQ
  have hJ't : J.map (MulAut.conj t).toMonoidHom = J' := by
    have hk : k⁻¹ ∈ Subgroup.normalizer (J.map (MulAut.conj n).toMonoidHom : Set G) := by
      rw [← hJ'eq]
      exact hK'J' ((kSub 3 M N').inv_mem hkK')
    have hnorm : (J.map (MulAut.conj n).toMonoidHom).map (MulAut.conj k⁻¹).toMonoidHom =
        J.map (MulAut.conj n).toMonoidHom :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hk
    rw [show t = k⁻¹ * n from rfl, ← CFSG.QuasiDihedralFusion.map_conj_mul J k⁻¹ n]
    exact hnorm.trans hJ'eq.symm
  refine ⟨t, htN', htQ, ?_⟩
  have hc := h'.map_conj_J htM htN' htQ
  rwa [hJ't] at hc

private theorem two_kComp_kSub_eq {M H E Q J : Subgroup G} {N' N₁ : Subgroup G}
    {J' : Subgroup G} (h : S14Choice G M H E Q J) (hpre : PreambleTypes M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) (hN₁ : rankThreeIsMaxTwoLocal N₁)
    (hJN₁ : J ≤ N₁) (hQN₁ : Q ≤ N₁) (hJ'ne : J' ≠ J)
    (hsupK' : kSub 3 M N' = J ⊔ J')
    (hKN₁J : IsKComp M N₁ J) (hKN₁J' : IsKComp M N₁ J') :
    kSub 3 M N₁ = kSub 3 M N' := by
  have hfive₁ : FiveTypes M N₁ := (hpre 3 Q (h.Q_mem_QSet hU) N₁
    (h.hypCGen_of_le_isMaxTwoLocal hL hN₁ hJN₁ hQN₁).2).2
  rcases hfive₁ with ⟨hKcomp₁, -⟩ |
    ⟨B₁, B₂, hneB, hB₁, hB₂, hsup₁, honly₁, hSLB₁, hSLB₂⟩
  · exfalso
    have h1 : J = kSub 3 M N₁ := IsKComp.eq_kSub_of_isKComp_self hKcomp₁ hKN₁J
    have h2 : J' = kSub 3 M N₁ := IsKComp.eq_kSub_of_isKComp_self hKcomp₁ hKN₁J'
    exact hJ'ne (h2.trans h1.symm)
  · rw [hsup₁, hsupK']
    rcases honly₁ J hKN₁J with hJ₁ | hJ₂ <;> rcases honly₁ J' hKN₁J' with hJ'₁ | hJ'₂
    · exact absurd (hJ₁.trans hJ'₁.symm).symm hJ'ne
    · rw [← hJ₁, ← hJ'₂]
    · rw [← hJ₂, ← hJ'₁, sup_comm]
    · exact absurd (hJ₂.trans hJ'₂.symm).symm hJ'ne

private theorem two_kComp_eq {M E J : Subgroup G} {N₁ N' : Subgroup G}
    (hK : KNormalAt M) (hN₁ : rankThreeIsMaxTwoLocal N₁)
    (hN₁C : HypCGen G M 3 E N₁) (hN' : rankThreeIsMaxTwoLocal N')
    (hN'C : HypCGen G M 3 E N')
    (hK_eq : kSub 3 M N₁ = kSub 3 M N') (hJK' : IsKComp M N' J)
    (hK'J : kSub 3 M N' ≤ Subgroup.normalizer (J : Set G))
    (hO2ne : CFSG.Open.pCoreOf 2 J ≠ ⊥) :
    N' = N₁ := by
  have hO2J_le : CFSG.Open.pCoreOf 2 J ≤ kSub 3 M N' :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 J).trans hJK'.1
  have hO2J_norm : kSub 3 M N' ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 J : Set G) :=
    hK'J.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)
  have hO2J_le_O : CFSG.Open.pCoreOf 2 J ≤ CFSG.Open.pCoreOf 2 (kSub 3 M N') :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2
      (CFSG.Open.pCoreOf 2 J) (kSub 3 M N') hO2J_le
      ((Subgroup.normal_subgroupOf_iff hO2J_le).mpr fun h k hh hk =>
        (Subgroup.mem_normalizer_iff.mp (hO2J_norm hk) h).mp hh)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 J)
  have hOne : CFSG.Open.pCoreOf 2 (kSub 3 M N') ≠ ⊥ := fun hbot =>
    hO2ne (le_bot_iff.mp (hbot ▸ hO2J_le_O))
  have hOloc : IsTwoLocal
      (Subgroup.normalizer (CFSG.Open.pCoreOf 2 (kSub 3 M N') : Set G)) :=
    ⟨_, hOne, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (kSub 3 M N'), rfl⟩
  have hN'le : N' ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (kSub 3 M N') : Set G) :=
    (hK 3 E N' hN'C).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf
        2 (kSub 3 M N'))
  have hNG_eq : Subgroup.normalizer (CFSG.Open.pCoreOf 2 (kSub 3 M N') : Set G) = N' :=
    hN'.2 _ hOloc hN'le
  have hN₁_le : N₁ ≤ N' := by
    calc N₁ ≤ Subgroup.normalizer (kSub 3 M N₁ : Set G) := hK 3 E N₁ hN₁C
      _ = Subgroup.normalizer (kSub 3 M N' : Set G) := by rw [hK_eq]
      _ ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (kSub 3 M N') : Set G) :=
          CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf
            2 (kSub 3 M N')
      _ = N' := hNG_eq
  exact hN₁.2 N' hN'.1 hN₁_le

private theorem le_normalizer_of_single_component {M E J N' : Subgroup G}
    (hK : KNormalAt M) (hN'C : HypCGen G M 3 E N') (hJK' : IsKComp M N' J)
    (hKcomp : IsKComp M N' (kSub 3 M N')) :
    N' ≤ Subgroup.normalizer (J : Set G) := by
  have hNK : N' ≤ Subgroup.normalizer (kSub 3 M N' : Set G) := hK 3 E N' hN'C
  have hJeq : J = kSub 3 M N' := IsKComp.eq_kSub_of_isKComp_self hKcomp hJK'
  exact hJeq ▸ hNK

private theorem two_kComp_conj
    {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J) (hA : TypeA M H)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (h142 : FourteenTwoCaseOneAt M) (hK : KNormalAt M) (hJS : IsSL34Star J)
    (hQnormM : Subgroup.normalizer (Q : Set G) ≤ M) {N' : Subgroup G}
    (hN' : rankThreeIsMaxTwoLocal N') (hJN' : J ≤ N') (hQN' : Q ≤ N')
    (hN'J : ¬ N' ≤ Subgroup.normalizer (J : Set G)) (hN'C : HypCGen G M 3 E N')
    (hN'Q : N' ∈ H2StarFam M Q) (hJK' : IsKComp M N' J)
    {A₁ A₂ : Subgroup G} (hne : A₁ ≠ A₂) (hA₁ : IsKComp M N' A₁)
    (hA₂ : IsKComp M N' A₂) (hsup : kSub 3 M N' = A₁ ⊔ A₂)
    (honly : ∀ Y : Subgroup G, IsKComp M N' Y → Y = A₁ ∨ Y = A₂)
    (hSL₁ : IsSL34Star A₁) (hSL₂ : IsSL34Star A₂ ∨ Is3A6Star A₂) :
    ∃ J' : Subgroup G, IsKComp M N' J' ∧ (IsSL34Star J' ∨ Is3A6Star J') ∧ J' ≠ J ∧
      kSub 3 M N' = J ⊔ J' ∧ S14Choice G M N' E Q J' := by
  classical
  have hNK : N' ≤ Subgroup.normalizer (kSub 3 M N' : Set G) := hK 3 E N' hN'C
  have hcardQ : Nat.card ↥Q = 3 ^ 5 := (h142 H E Q J h hA).1.1
  have hfive : FiveTypes M N' :=
    Or.inr ⟨A₁, A₂, hne, hA₁, hA₂, hsup, honly, hSL₁, hSL₂⟩
  have hK'J : kSub 3 M N' ≤ Subgroup.normalizer (J : Set G) :=
    FiveTypes.kSub_le_normalizer_of_isKComp hfive hJK'
  obtain ⟨n, hnN', hnJ⟩ := Set.not_subset.mp hN'J
  let J' : Subgroup G := J.map (MulAut.conj n).toMonoidHom
  have hJ'comp : IsKComp M N' J' :=
    isPComponentIn_conj_of_mem_normalizer hJK' (hNK hnN')
  have hJ'ne : J' ≠ J := fun heq =>
    hnJ ((Subgroup.mem_normalizer_iff_map_conj_eq (H := J) (g := n)).mpr heq)
  have hJ'type : IsSL34Star J' ∨ Is3A6Star J' := by
    rcases honly J' hJ'comp with hA | hA
    · exact Or.inl (hA ▸ hSL₁)
    · exact hA ▸ hSL₂
  have hsupK' : kSub 3 M N' = J ⊔ J' := by
    rw [hsup]
    rcases honly J hJK' with hJ₁ | hJ₂ <;> rcases honly J' hJ'comp with hJ'₁ | hJ'₂
    · exact absurd (hJ₁.trans hJ'₁.symm).symm hJ'ne
    · rw [← hJ₁, ← hJ'₂]
    · rw [← hJ₂, ← hJ'₁, sup_comm]
    · exact absurd (hJ₂.trans hJ'₂.symm).symm hJ'ne
  have hK'J' : kSub 3 M N' ≤ Subgroup.normalizer (J' : Set G) :=
    FiveTypes.kSub_le_normalizer_of_isKComp hfive hJ'comp
  have hQK' : Q ≤ Subgroup.normalizer (kSub 3 M N' : Set G) := hQN'.trans hNK
  have hQJ' : Q ≤ Subgroup.normalizer (J' : Set G) :=
    le_normalizer_of_orbit_card_one
      (orbit_card_one_of_two_components hne honly hQK' h.sylow.isPGroup J' hJ'comp)
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q (kSub 3 M N') :=
    two_kComp_sylow h hA hpre hU hL hNK hQN' hN'C hJK' hJ'comp hJ'type hJ'ne hsupK'
      hK'J hK'J' hQJ' hJS hcardQ
  have h' : S14Choice G M N' E Q J := two_kComp_choice h hA hU hJS hJK' hN'Q hQN' hQsyl
  obtain ⟨t, -, -, hS14'⟩ := two_kComp_frattini h' hQsyl hNK hK'J' hQnormM hnN' rfl
  exact ⟨J', hJ'comp, hJ'type, hJ'ne, hsupK', hS14'⟩

private theorem two_kComp_eq_of_conj
    {M H E Q J : Subgroup G} {N₁ N' J' : Subgroup G} (h : S14Choice G M H E Q J)
    (hA : TypeA M H) (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    (hL : PLayerNotLeAt M) (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne)
    (h142 : FourteenTwoCaseOneAt M) (hK : KNormalAt M) (hJS : IsSL34Star J)
    (hO2ne : CFSG.Open.pCoreOf 2 J ≠ ⊥) (hN₁ : rankThreeIsMaxTwoLocal N₁)
    (hJN₁ : J ≤ N₁) (hQN₁ : Q ≤ N₁)
    (hNGJ : Subgroup.normalizer (J : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 J : Set G))
    (hN₁O : Subgroup.normalizer (CFSG.Open.pCoreOf 2 J : Set G) ≤ N₁)
    (hN' : rankThreeIsMaxTwoLocal N') (hJN' : J ≤ N') (hQN' : Q ≤ N')
    (hJK' : IsKComp M N' J) (hK'J : kSub 3 M N' ≤ Subgroup.normalizer (J : Set G))
    (hN'C : HypCGen G M 3 E N') (hJ'comp : IsKComp M N' J') (hJ'ne : J' ≠ J)
    (hsupK' : kSub 3 M N' = J ⊔ J') (hS14' : S14Choice G M N' E Q J') : N' = N₁ := by
  have hN₁C : HypCGen G M 3 E N₁ := (h.hypCGen_of_le_isMaxTwoLocal hL hN₁ hJN₁ hQN₁).1
  have hJ'N₁ : J' ≤ N₁ := (hJ'comp.1.trans hK'J).trans (hNGJ.trans hN₁O)
  have hKN₁J : IsKComp M N₁ J :=
    h.isKComp_of_isMaxTwoLocal hA hpre hU hL h711 h142 hN₁ hJN₁ hQN₁
  have hKN₁J' : IsKComp M N₁ J' :=
    hS14'.isKComp_of_isMaxTwoLocal ⟨J, hJK', hJS⟩ hpre hU hL h711 h142 hN₁ hJ'N₁ hQN₁
  have hK_eq : kSub 3 M N₁ = kSub 3 M N' :=
    two_kComp_kSub_eq h hpre hU hL hN₁ hJN₁ hQN₁ hJ'ne hsupK' hKN₁J hKN₁J'
  exact two_kComp_eq hK hN₁ hN₁C hN' hN'C hK_eq hJK' hK'J hO2ne

private theorem eq_of_two_components
    {M H E Q J : Subgroup G} {N₁ : Subgroup G} (h : S14Choice G M H E Q J)
    (hA : TypeA M H) (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    (hL : PLayerNotLeAt M) (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne)
    (h142 : FourteenTwoCaseOneAt M) (hK : KNormalAt M) (hJS : IsSL34Star J)
    (hQnormM : Subgroup.normalizer (Q : Set G) ≤ M)
    (hO2ne : CFSG.Open.pCoreOf 2 J ≠ ⊥) (hN₁ : rankThreeIsMaxTwoLocal N₁)
    (hN₁O : Subgroup.normalizer (CFSG.Open.pCoreOf 2 J : Set G) ≤ N₁)
    (hNGJ : Subgroup.normalizer (J : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 J : Set G))
    (hJN₁ : J ≤ N₁) (hQN₁ : Q ≤ N₁) {N' : Subgroup G}
    (hN' : rankThreeIsMaxTwoLocal N') (hJN' : J ≤ N') (hQN' : Q ≤ N')
    (hN'J : ¬ N' ≤ Subgroup.normalizer (J : Set G)) (hN'C : HypCGen G M 3 E N')
    (hN'Q : N' ∈ H2StarFam M Q) (hJK' : IsKComp M N' J) (hfive : FiveTypes M N') :
    N' = N₁ := by
  rcases hfive with ⟨hKcomp, -⟩ | ⟨A₁, A₂, hne, hA₁, hA₂, hsup, honly, hSL₁, hSL₂⟩
  · exact absurd (le_normalizer_of_single_component hK hN'C hJK' hKcomp) hN'J
  · have hK'J : kSub 3 M N' ≤ Subgroup.normalizer (J : Set G) :=
      FiveTypes.kSub_le_normalizer_of_isKComp (Or.inr ⟨A₁, A₂, hne, hA₁, hA₂, hsup,
        honly, hSL₁, hSL₂⟩) hJK'
    obtain ⟨J', hJ'comp, -, hJ'ne, hsupK', hS14'⟩ :=
      two_kComp_conj (H := H) (Q := Q) h hA hpre hU hL h142 hK hJS hQnormM
        hN' hJN' hQN' hN'J hN'C hN'Q hJK' hne hA₁ hA₂ hsup honly hSL₁ hSL₂
    exact two_kComp_eq_of_conj (H := H) (Q := Q) h hA hpre hU hL h711 h142 hK hJS hO2ne
      hN₁ hJN₁ hQN₁ hNGJ hN₁O hN' hJN' hQN' hJK' hK'J hN'C hJ'comp hJ'ne hsupK' hS14'

private theorem eq_of_isMaxTwoLocal_of_le_JQ
    {M H E Q J : Subgroup G} {N₁ : Subgroup G} (h : S14Choice G M H E Q J)
    (hA : TypeA M H) (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    (hL : PLayerNotLeAt M) (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne)
    (h142 : FourteenTwoCaseOneAt M) (hK : KNormalAt M) (hJS : IsSL34Star J)
    (hQnormM : Subgroup.normalizer (Q : Set G) ≤ M)
    (hO2ne : CFSG.Open.pCoreOf 2 J ≠ ⊥) (hN₁ : rankThreeIsMaxTwoLocal N₁)
    (hN₁O : Subgroup.normalizer (CFSG.Open.pCoreOf 2 J : Set G) ≤ N₁)
    (hNGJ : Subgroup.normalizer (J : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 J : Set G))
    (hJN₁ : J ≤ N₁) (hQN₁ : Q ≤ N₁)
    {N' : Subgroup G} (hN' : rankThreeIsMaxTwoLocal N') (hJN' : J ≤ N') (hQN' : Q ≤ N') :
    N' = N₁ := by
  by_cases hN'J : N' ≤ Subgroup.normalizer (J : Set G)
  · exact (hN'.2 N₁ hN₁.1 (hN'J.trans (hNGJ.trans hN₁O))).symm
  · obtain ⟨hN'C, hN'Q⟩ := h.hypCGen_of_le_isMaxTwoLocal hL hN' hJN' hQN'
    have hJK' : IsKComp M N' J :=
      h.isKComp_of_isMaxTwoLocal hA hpre hU hL h711 h142 hN' hJN' hQN'
    have hfive : FiveTypes M N' := (hpre 3 Q (h.Q_mem_QSet hU) N' hN'Q).2
    exact eq_of_two_components h hA hpre hU hL h711 h142 hK hJS hQnormM hO2ne
      hN₁ hN₁O hNGJ hJN₁ hQN₁ hN' hJN' hQN' hN'J hN'C hN'Q hJK' hfive

theorem S14Choice.pCoreOf_two_J_ne_bot {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) :
    CFSG.Open.pCoreOf 2 J ≠ ⊥ := by
  intro hbot
  have hK : KNormalAt M := kNormalAt_of_preamble hpre hU hL
  have hJK : IsKComp M H J := h.isKComp
  have hperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJK.isPerfect
  have hJ2 : ∀ N : Subgroup G, N ≤ J →
      (∀ g ∈ J, ∀ n ∈ N, g * n * g⁻¹ ∈ N) → IsPGroup 2 N →
      N ≤ Subgroup.centralizer (J : Set G) := by
    intro N hNJ hNnorm hN2
    have hNle : N ≤ CFSG.Open.pCoreOf 2 J :=
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 N J hNJ
        ((Subgroup.normal_subgroupOf_iff hNJ).mpr fun h k hh hk => hNnorm k hk h hh) hN2
    rw [hbot] at hNle
    rw [le_bot_iff.mp hNle]
    exact bot_le
  have hJnot2 : ¬ IsPGroup 2 J := by
    intro h2
    obtain ⟨m, hm⟩ := h2.exists_card_eq
    have h3 := hJK.three_dvd_card
    rw [hm] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hKn : ∀ g ∈ H, ∀ k ∈ kSub 3 M H, g * k * g⁻¹ ∈ kSub 3 M H := by
    intro g hg k hk
    have hg' : g ∈ Subgroup.normalizer (kSub 3 M H : Set G) := hK 3 E H h.hypCGen hg
    exact (Subgroup.mem_normalizer_iff.mp hg' k).mp hk
  have hJn : ∀ g ∈ kSub 3 M H, ∀ j ∈ J, g * j * g⁻¹ ∈ J := by
    intro g hg j hj
    have hg' : g ∈ Subgroup.normalizer (J : Set G) := h.kSub_le_normalizer_J hpre hU hg
    exact (Subgroup.mem_normalizer_iff.mp hg' j).mp hj
  exact (CFSG.RankThree.PartTwo.Census.not_isCharTwoType_of_perfect_subnormal_subgroup
    (H := G) (L := H) (K := kSub 3 M H) (J := J)
    h.hypCGen.isTwoLocal (kSub_le 3 M H) hKn hJK.1 hJn hperf hJ2 hJnot2)
    h.cstar.charTwo

theorem fourteenThreeCaseOneAt_of
    {M : Subgroup G} (hpre : PreambleTypes M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne) (h142 : FourteenTwoCaseOneAt M) :
    FourteenThreeCaseOneAt M := by
  classical
  intro H E Q J h hA N hN hJN hQN
  have hK : KNormalAt M := kNormalAt_of_preamble hpre hU hL
  have hJS : IsSL34Star J := h.isSL34Star_of_typeA hpre hU hA
  have hO2ne : CFSG.Open.pCoreOf 2 J ≠ ⊥ := h.pCoreOf_two_J_ne_bot hpre hU hL
  have hQJ : Q ≤ Subgroup.normalizer (J : Set G) := h.Q_le_normalizer_J hpre hU
  have hQnormM : Subgroup.normalizer (Q : Set G) ≤ M :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne.normalizer_le h.maxLocal
      (hU 3 E H h.hypCGen) h.hypCGen.E_le_M h.elem h.card h.gamma h.E_le_Q (h.Q_le_M hU)
  have hloc : IsTwoLocal (Subgroup.normalizer (CFSG.Open.pCoreOf 2 J : Set G)) :=
    ⟨CFSG.Open.pCoreOf 2 J, hO2ne,
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 J, rfl⟩
  obtain ⟨N₁, hN₁, hN₁O⟩ := CFSG.Quasithin.exists_maxTwoLocal_ge hloc
  have hNGJ : Subgroup.normalizer (J : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 J : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J
  have hJN₁ : J ≤ N₁ := (Subgroup.le_normalizer.trans hNGJ).trans hN₁O
  have hQN₁ : Q ≤ N₁ := hQJ.trans (hNGJ.trans hN₁O)
  have hNH : N = N₁ :=
    eq_of_isMaxTwoLocal_of_le_JQ h hA hpre hU hL h711 h142 hK hJS hQnormM hO2ne
      hN₁ hN₁O hNGJ hJN₁ hQN₁ (N' := N) hN hJN hQN
  have hHH : H = N₁ :=
    eq_of_isMaxTwoLocal_of_le_JQ h hA hpre hU hL h711 h142 hK hJS hQnormM hO2ne
      hN₁ hN₁O hNGJ hJN₁ hQN₁ (N' := H)
      (h.hypCGen.isMaxTwoLocal_of_mem_H2StarFam h.hypCGen.mem)
      (h.isKComp.1.trans (kSub_le 3 M H))
      (h.sylow.le.trans (sup_le (kSub_le 3 M H) h.E_le_H))
  exact hNH.trans hHH.symm

theorem fourteenThreeCaseOneGen_of
    (h1210 : TwelveTenThree) (h1211 : TwelveElevenGen)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen) (h96 : NineSixMoreoverGen)
    (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen)
    (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne) : FourteenThreeCaseOneGen := by
  intro G _ _ M H E Q J h hA N hN hJN hQN
  have hU : NineNineOneAt M := nineNineOneAt_of_twelveEleven h991 h1211
  have hpre : PreambleTypes M :=
    preambleTypes_of h1211 h.cstar h.maxLocal h.sigma_nonempty
      (preambleFiveTypes_of h1210 h97 h96 h.cstar h.maxLocal h.sigma_nonempty hU)
  have hL : PLayerNotLeAt M := pLayerNotLeAt_of h1211 h1210 h97 hU
  have h142 : FourteenTwoCaseOneAt M :=
    fourteenTwoCaseOneGen_of h1210 h1211 h97 h96 h991 G M
  exact fourteenThreeCaseOneAt_of hpre hU hL h711 h142 H E Q J h hA N hN hJN hQN

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
