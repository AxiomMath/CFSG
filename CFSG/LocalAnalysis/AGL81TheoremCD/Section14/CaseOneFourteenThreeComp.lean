module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenThreeRank
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneSetup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KNormalRank
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.GroupTheory.CardSupInf
import CFSG.GroupTheory.Commutator.JoinNormalizer
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.ClassicalInvolution.Asc77.AscT7Z13

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {M H E Q J N : Subgroup G}

private theorem le_quotientCentralizer_of_commutator_le {N L X : Subgroup G}
    (Q : Subgroup ↥L) [Q.Characteristic] (hLN : L ≤ N)
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hXN : X ≤ N) (hcomm : ⁅X, L⁆ ≤ Q.map L.subtype) :
    X ≤ quotientCentralizer N L Q hLN hNL := by
  haveI : Q.Normal := Subgroup.normal_of_characteristic Q
  intro x hx
  rw [mem_quotientCentralizer]
  refine ⟨⟨x, hXN hx⟩, rfl, ?_⟩
  apply MulEquiv.ext
  intro y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective Q y
  change conjQuotAction N L Q hLN hNL ⟨x, hXN hx⟩ (QuotientGroup.mk' Q l) =
    (1 : MulAut (↥L ⧸ Q)) (QuotientGroup.mk' Q l)
  rw [conjQuotAction_apply_mk, MulAut.one_apply]
  apply (QuotientGroup.eq).mpr
  have hc : x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ Q.map L.subtype :=
    Subgroup.commutator_le.mp hcomm x hx (l : G) l.2
  obtain ⟨c, hcQ, hcEq⟩ := Subgroup.mem_map.mp hc
  let a : ↥L := ⟨x * (l : G) * x⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hNL (hXN hx)) (l : G)).mp l.2⟩
  have haQ : a * l⁻¹ ∈ Q := by
    have hEq : a * l⁻¹ = c := Subtype.ext (by
      change (x * (l : G) * x⁻¹) * (l : G)⁻¹ = (c : G)
      exact hcEq.symm)
    rwa [hEq]
  have hlaQ : l * a⁻¹ ∈ Q := by
    simpa [mul_assoc] using Q.inv_mem haQ
  have hconj : a⁻¹ * (l * a⁻¹) * (a⁻¹)⁻¹ ∈ Q :=
    (inferInstance : Q.Normal).conj_mem (l * a⁻¹) hlaQ (a⁻¹)
  simpa [a, mul_assoc] using hconj

private theorem not_is3A6Star_of_le_isKComp {M H N J A : Subgroup G}
    (hJ : IsKComp M H J) (hJSL : IsSL34Star J)
    (hA : IsKComp M N A) (hJA : J ≤ A) : ¬ Is3A6Star A := by
  intro hA6
  classical
  let D : Subgroup G := (CFSG.pPrimeCore 3 ↥A).map A.subtype
  let E : Subgroup G := J ⊓ D
  have hDA : D ≤ A := Subgroup.map_subtype_le _
  have hDsubA : D.subgroupOf A = CFSG.pPrimeCore 3 ↥A := by
    unfold D
    exact Subgroup.comap_map_eq_self_of_injective A.subtype_injective _
  have hDnormA : (D.subgroupOf A).Normal := by
    rw [hDsubA]
    exact CFSG.pPrimeCore_normal
  have hEnormal : (E.subgroupOf J).Normal := by
    refine (Subgroup.normal_subgroupOf_iff (inf_le_left : E ≤ J)).mpr ?_
    intro e j he hj
    refine Subgroup.mem_inf.mpr ⟨J.mul_mem (J.mul_mem hj he.1) (J.inv_mem hj), ?_⟩
    exact (Subgroup.normal_subgroupOf_iff hDA).mp hDnormA e j he.2 (hJA hj)
  have hEne : E ≠ J := by
    intro hEeq
    have hJD : J ≤ D := by rw [← hEeq]; exact inf_le_right
    have hcopD : Nat.Coprime 3 (Nat.card D) := by
      rw [show Nat.card D = Nat.card (CFSG.pPrimeCore 3 ↥A) from
        Subgroup.card_map_of_injective A.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have hnot3D : ¬ 3 ∣ Nat.card D :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcopD
    exact hnot3D (dvd_trans hJ.three_dvd_card (Subgroup.card_dvd_of_le hJD))
  have hEo : E ≤ oTwoZStar J :=
    IsKComp.le_oTwoZStar_of_normal hJ inf_le_left hEnormal hEne
  have hOrel : (oTwoZStar J).relIndex J = 20160 := by
    rw [relIndex_oTwoZStar]
    have hmul := Subgroup.card_mul_index (Subgroup.center (threeStar J))
    rw [hJSL.2, IsSL34Star.card_threeStar hJSL] at hmul
    omega
  have hErel_ne : E.relIndex J ≠ 0 := by
    change (E.subgroupOf J).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have hErel : 20160 ≤ E.relIndex J := by
    rw [← hOrel]
    exact Subgroup.relIndex_le_of_le_left hEo hErel_ne
  have hJND : J ≤ Subgroup.normalizer (D : Set G) :=
    hJA.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hDA).mp hDnormA)
  have hindex : E.relIndex J ≤ D.relIndex A := by
    have hcard : Nat.card ↥(D ⊔ J) ≤ Nat.card A := Subgroup.card_le_of_le (sup_le hDA hJA)
    simpa [E, inf_comm] using
      CFSG.GroupTheory.relIndex_inf_le_relIndex_of_card_sup_le hDA hJND hcard
  have hDrelA : D.relIndex A = Nat.card (threeStar A) := by
    calc D.relIndex A = (D.subgroupOf A).index := rfl
      _ = (CFSG.pPrimeCore 3 ↥A).index := by rw [hDsubA]
      _ = Nat.card (threeStar A) := by rw [Subgroup.index_eq_card]
  have hcardA : Nat.card (threeStar A) = 1080 := Is3A6Star.card_threeStar hA6
  omega

private theorem isKComp_of_le_of_calK_type {M H E Q N A J : Subgroup G}
    (h : S14Choice G M H E Q J) (hNQ : N ∈ H2StarFam M Q)
    (hA : IsKComp M N A) (hJA : J ≤ A)
    (htype : IsL34Type (threeStar A) ∨ IsA11Star A) : IsKComp M N J := by
  have hAcal : A ∈ calK M Q := ⟨N, hNQ, hA, htype⟩
  have hAJ : A = J := h.J_star.2 A hAcal hJA
  rwa [hAJ] at hA

private theorem isPGroup_le_normalizer_of_two_components {P K A₁ A₂ : Subgroup G}
    (hPK : P ≤ Subgroup.normalizer (K : Set G)) (hP : IsPGroup 3 P) (hne : A₁ ≠ A₂)
    (hA₁ : IsPComponentIn 3 A₁ K) (hA₂ : IsPComponentIn 3 A₂ K)
    (honly : ∀ A, IsPComponentIn 3 A K → A = A₁ ∨ A = A₂) :
    P ≤ Subgroup.normalizer (A₁ : Set G) ∧ P ≤ Subgroup.normalizer (A₂ : Set G) := by
  have h₁ := orbit_card_one_of_two_components hne honly hPK hP A₁ hA₁
  have h₂ := orbit_card_one_of_two_components hne honly hPK hP A₂ hA₂
  exact ⟨le_normalizer_of_orbit_card_one h₁, le_normalizer_of_orbit_card_one h₂⟩

private theorem isPerfect_le_normalizer_of_two_components {X K A₁ A₂ : Subgroup G}
    (hperf : Group.IsPerfect ↥X) (hXK : X ≤ Subgroup.normalizer (K : Set G)) (hne : A₁ ≠ A₂)
    (hA₁ : IsPComponentIn 3 A₁ K) (hA₂ : IsPComponentIn 3 A₂ K)
    (honly : ∀ A, IsPComponentIn 3 A K → A = A₁ ∨ A = A₂) :
    X ≤ Subgroup.normalizer (A₁ : Set G) ∧ X ≤ Subgroup.normalizer (A₂ : Set G) := by
  classical
  have hperfComm : X ≤ ⁅X, X⁆ := by
    rw [Subgroup.isPerfect_iff.mp hperf]
  have hcomp : ∀ (w : G), w ∈ X → ∀ A : Subgroup G, IsPComponentIn 3 A K →
      w • A = A₁ ∨ w • A = A₂ := by
    intro w hw A hA
    have hmap : w • A = A.map (MulAut.conj w).toMonoidHom := rfl
    rw [hmap]
    exact honly _ (isPComponentIn_conj_of_mem_normalizer hA (hXK hw))
  have hmap : ∀ w ∈ X, (w • A₁ = A₁ ∧ w • A₂ = A₂) ∨
      (w • A₁ = A₂ ∧ w • A₂ = A₁) := by
    intro w hw
    have hinj : ∀ {B C : Subgroup G}, w • B = w • C → B = C := by
      intro B C h
      calc B = w⁻¹ • (w • B) := (inv_smul_smul w B).symm
        _ = w⁻¹ • (w • C) := by rw [h]
        _ = C := inv_smul_smul w C
    by_cases h1 : w • A₁ = A₁
    · have h2 : w • A₂ = A₂ := by
        rcases hcomp w hw A₂ hA₂ with h2 | h2
        · exact absurd (hinj (B := A₁) (C := A₂) (h1.trans h2.symm)) hne
        · exact h2
      exact Or.inl ⟨h1, h2⟩
    · have h1' : w • A₁ = A₂ := (hcomp w hw A₁ hA₁).resolve_left h1
      have h2 : w • A₂ = A₁ := by
        rcases hcomp w hw A₂ hA₂ with h2 | h2
        · exact h2
        · exact absurd (hinj (B := A₁) (C := A₂) (h1'.trans h2.symm)) hne
      exact Or.inr ⟨h1', h2⟩
  have hfix := CFSG.ClassicalInvolution.Asc77.T7Z.fix_of_perfect_two
    (fun (w : G) (A : Subgroup G) => w • A)
    (by intro x y A; rw [mul_smul])
    (by intro A; rw [one_smul])
    (L := X) hperfComm (s₀ := A₁) (s₁ := A₂) hmap
  constructor
  · intro w hw
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact (hfix w hw).1
  · intro w hw
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact (hfix w hw).2

private theorem le_quotientCentralizer_of_le_both {J N N₁ N₂ K A₁ A₂ : Subgroup G}
    (hKN : K ≤ N) (hNK : N ≤ Subgroup.normalizer (K : Set G)) (hsup : K = A₁ ⊔ A₂)
    (hJN : J ≤ N) (hA₁K : A₁ ≤ K) (hA₂K : A₂ ≤ K)
    (hAsub₁ : (A₁.subgroupOf K).IsSubnormal) (hAsub₂ : (A₂.subgroupOf K).IsSubnormal)
    (hAN₁ : A₁ ≤ N₁) (hNA₁ : N₁ ≤ Subgroup.normalizer (A₁ : Set G))
    (hAN₂ : A₂ ≤ N₂) (hNA₂ : N₂ ≤ Subgroup.normalizer (A₂ : Set G))
    (hJX₁ : J ≤ Xhat N₁ A₁ hAN₁ hNA₁) (hJX₂ : J ≤ Xhat N₂ A₂ hAN₂ hNA₂) :
    J ≤ Xhat N K hKN hNK := by
  classical
  let D₁ : Subgroup G := (CFSG.pPrimeCore 3 ↥A₁).map A₁.subtype
  let D₂ : Subgroup G := (CFSG.pPrimeCore 3 ↥A₂).map A₂.subtype
  let DK : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype
  have hcomm₁ : ⁅J, A₁⁆ ≤ D₁ := by
    refine Subgroup.commutator_le.mpr ?_
    intro j hj a ha
    exact commutator_mem_map_of_mem_quotientCentralizer (Q := CFSG.pPrimeCore 3 ↥A₁)
      hAN₁ hNA₁ (hJX₁ hj) ha
  have hcomm₂ : ⁅J, A₂⁆ ≤ D₂ := by
    refine Subgroup.commutator_le.mpr ?_
    intro j hj a ha
    exact commutator_mem_map_of_mem_quotientCentralizer (Q := CFSG.pPrimeCore 3 ↥A₂)
      hAN₂ hNA₂ (hJX₂ hj) ha
  have hD₁ : D₁ ≤ DK := by
    change CFSG.Open.GLAPPrimeCoreOf 3 A₁ ≤ CFSG.Open.GLAPPrimeCoreOf 3 K
    exact CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three
      ((CFSG.Open.IsSubnormal.iff_subgroupOf hA₁K).mpr hAsub₁)
  have hD₂ : D₂ ≤ DK := by
    change CFSG.Open.GLAPPrimeCoreOf 3 A₂ ≤ CFSG.Open.GLAPPrimeCoreOf 3 K
    exact CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three
      ((CFSG.Open.IsSubnormal.iff_subgroupOf hA₂K).mpr hAsub₂)
  have hDKle : DK ≤ K := Subgroup.map_subtype_le _
  have hDKnorm : (DK.subgroupOf K).Normal := by
    have hEq : DK.subgroupOf K = CFSG.pPrimeCore 3 ↥K := by
      unfold DK
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    rw [hEq]
    exact CFSG.pPrimeCore_normal
  have hKND : K ≤ Subgroup.normalizer (DK : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDKle).mp hDKnorm
  have hA₁ND : A₁ ≤ Subgroup.normalizer (DK : Set G) := hA₁K.trans hKND
  have hA₂ND : A₂ ≤ Subgroup.normalizer (DK : Set G) := hA₂K.trans hKND
  have hcommK : ⁅J, K⁆ ≤ DK := by
    rw [hsup]
    exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer hA₁ND hA₂ND
      (hcomm₁.trans hD₁) (hcomm₂.trans hD₂)
  exact le_quotientCentralizer_of_commutator_le (Q := CFSG.pPrimeCore 3 ↥K) hKN hNK hJN hcommK

private theorem isKComp_of_two_components
    (h : S14Choice G M H E Q J) (hA : TypeA M H)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (h142 : FourteenTwoCaseOneAt M) (hJN : J ≤ N) (hQN : Q ≤ N)
    (hN' : HypCGen G M 3 E N) (hNQ : N ∈ H2StarFam M Q)
    (hK : KNormalAt M) (hrankN : CFSG.Open.pRank 3 N ≤ 3)
    (hJXK : ¬ J ≤ Xhat N (kSub 3 M N) (kSub_le 3 M N) (hK 3 E N hN'))
    {A₁ A₂ : Subgroup G} (hne : A₁ ≠ A₂) (hA₁ : IsKComp M N A₁) (hA₂ : IsKComp M N A₂)
    (hsup : kSub 3 M N = A₁ ⊔ A₂) (honly : ∀ A, IsKComp M N A → A = A₁ ∨ A = A₂)
    (hSL₁ : IsSL34Star A₁) (hSL₂ : IsSL34Star A₂ ∨ Is3A6Star A₂) :
    IsKComp M N J := by
  classical
  let K : Subgroup G := kSub 3 M N
  have hJ : IsKComp M H J := h.isKComp
  have hJSL : IsSL34Star J := h.isSL34Star_of_typeA hpre hU hA
  have hNK : N ≤ Subgroup.normalizer (K : Set G) := hK 3 E N hN'
  have hJK : J ≤ Subgroup.normalizer (K : Set G) := hJN.trans hNK
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := hQN.trans hNK
  obtain ⟨hQNG₁, hQNG₂⟩ :=
    isPGroup_le_normalizer_of_two_components hQK h.sylow.isPGroup hne hA₁ hA₂ honly
  obtain ⟨hJNG₁, hJNG₂⟩ :=
    isPerfect_le_normalizer_of_two_components hJ.isPerfect hJK hne hA₁ hA₂ honly
  let N₁ : Subgroup G := N ⊓ Subgroup.normalizer (A₁ : Set G)
  let N₂ : Subgroup G := N ⊓ Subgroup.normalizer (A₂ : Set G)
  have hAN₁ : A₁ ≤ N₁ := le_inf (hA₁.1.trans (kSub_le 3 M N)) Subgroup.le_normalizer
  have hNA₁ : N₁ ≤ Subgroup.normalizer (A₁ : Set G) := inf_le_right
  have hAN₂ : A₂ ≤ N₂ := le_inf (hA₂.1.trans (kSub_le 3 M N)) Subgroup.le_normalizer
  have hNA₂ : N₂ ≤ Subgroup.normalizer (A₂ : Set G) := inf_le_right
  have hJN₁ : J ≤ N₁ := le_inf hJN hJNG₁
  have hQN₁ : Q ≤ N₁ := le_inf hQN hQNG₁
  have hJN₂ : J ≤ N₂ := le_inf hJN hJNG₂
  have hQN₂ : Q ≤ N₂ := le_inf hQN hQNG₂
  have hrank₁ : CFSG.Open.pRank 3 N₁ ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) inf_le_left).trans hrankN
  have hrank₂ : CFSG.Open.pRank 3 N₂ ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) inf_le_left).trans hrankN
  have htype₁ : IsSL34Star A₁ ∨ IsL34Star A₁ ∨ IsA11Star A₁ ∨ Is3A6Star A₁ := Or.inl hSL₁
  have htype₂ : IsSL34Star A₂ ∨ IsL34Star A₂ ∨ IsA11Star A₂ ∨ Is3A6Star A₂ := by
    rcases hSL₂ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  have hJor₁ : J ≤ A₁ ∨ J ≤ Xhat N₁ A₁ hAN₁ hNA₁ := by
    by_cases hX : J ≤ Xhat N₁ A₁ hAN₁ hNA₁
    · exact Or.inr hX
    · exact Or.inl (h.le_of_not_le_quotientCentralizer hA hpre hU hL h142 hAN₁ hNA₁
        hA₁ htype₁ hrank₁ hJN₁ hQN₁ hX)
  have hJor₂ : J ≤ A₂ ∨ J ≤ Xhat N₂ A₂ hAN₂ hNA₂ := by
    by_cases hX : J ≤ Xhat N₂ A₂ hAN₂ hNA₂
    · exact Or.inr hX
    · exact Or.inl (h.le_of_not_le_quotientCentralizer hA hpre hU hL h142 hAN₂ hNA₂
        hA₂ htype₂ hrank₂ hJN₂ hQN₂ hX)
  rcases hJor₁ with hJA₁ | hJX₁
  · exact isKComp_of_le_of_calK_type h hNQ hA₁ hJA₁ (Or.inl hSL₁.1)
  rcases hJor₂ with hJA₂ | hJX₂
  · have htype : IsL34Type (threeStar A₂) ∨ IsA11Star A₂ := by
      rcases hSL₂ with h | h
      · exact Or.inl h.1
      · exact absurd h (not_is3A6Star_of_le_isKComp hJ hJSL hA₂ hJA₂)
    exact isKComp_of_le_of_calK_type h hNQ hA₂ hJA₂ htype
  · exact absurd (le_quotientCentralizer_of_le_both (kSub_le 3 M N) hNK hsup hJN hA₁.1 hA₂.1
      hA₁.2.choose_spec.2.1 hA₂.2.choose_spec.2.1 hAN₁ hNA₁ hAN₂ hNA₂ hJX₁ hJX₂) hJXK

theorem S14Choice.isKComp_of_isMaxTwoLocal
    (h : S14Choice G M H E Q J) (hA : TypeA M H)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne) (h142 : FourteenTwoCaseOneAt M)
    {N : Subgroup G} (hN : CFSG.Open.rankThreeIsMaxTwoLocal N) (hJN : J ≤ N) (hQN : Q ≤ N) :
    IsKComp M N J := by
  classical
  have hK : KNormalAt M := kNormalAt_of_preamble hpre hU hL
  obtain ⟨hN', hNQ⟩ := h.hypCGen_of_le_isMaxTwoLocal hL hN hJN hQN
  have hLN : ¬ pLayerIn 3 N ≤ M := hL 3 E N hN'
  have hfive := (hpre 3 Q (h.Q_mem_QSet hU) N hNQ).2
  have hJ : IsKComp M H J := h.isKComp
  have hJSL : IsSL34Star J := h.isSL34Star_of_typeA hpre hU hA
  have hJXK : ¬ J ≤ Xhat N (kSub 3 M N) (kSub_le 3 M N) (hK 3 E N hN') :=
    HypCGen.not_le_quotientCentralizer_kSub h711 hN' hK hLN (h.not_le_M hL) hJ.isPerfect
  have hrankN : CFSG.Open.pRank 3 N ≤ 3 :=
    h.cstar.pRank_le_three_of_isTwoLocal Nat.prime_three (by norm_num) hN'.not_mem_sigmaA
      (show CFSG.Open.IsMaxTwoLocalSubgroup N from hN).1
  rcases hfive with ⟨hKcomp, htypeK⟩ | ⟨A₁, A₂, hne, hA₁, hA₂, hsup, honly, hSL₁, hSL₂⟩
  · have htype : IsSL34Star (kSub 3 M N) ∨ IsL34Star (kSub 3 M N) ∨
        IsA11Star (kSub 3 M N) ∨ Is3A6Star (kSub 3 M N) := by
      rcases htypeK with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
    have hJK : J ≤ kSub 3 M N :=
      h.le_of_not_le_quotientCentralizer hA hpre hU hL h142 (kSub_le 3 M N)
        (hK 3 E N hN') hKcomp htype hrankN hJN hQN hJXK
    have htypeCal : IsL34Type (threeStar (kSub 3 M N)) ∨ IsA11Star (kSub 3 M N) := by
      rcases htypeK with h | h | h
      · exact Or.inl h.1
      · exact Or.inl h.1
      · exact Or.inr h
    exact isKComp_of_le_of_calK_type h hNQ hKcomp hJK htypeCal
  · exact isKComp_of_two_components h hA hpre hU hL h142 hJN hQN hN' hNQ hK hrankN
      hJXK hne hA₁ hA₂ hsup honly hSL₁ hSL₂

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
