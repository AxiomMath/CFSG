module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SporTables3b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1310
import all CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1310

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporK

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple PSimple)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Prop1116Design

section SporDown

@[expose] def InputSporDownChevK : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ s : TauCeti.SporadicName, IsSporType s S →
    CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic s).Group →
    ∀ α : MulAut S, α ^ p = 1 → ∀ I : Subgroup S, GLAPComponent p (fixSubgroup α) I →
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → IsChevSimple q (PSimple p I) →
      α ≠ 1 ∧
        ((p = 3 ∧ (s = .M23 ∨ s = .HS) ∧ IsLpType 2 5 (PSimple p I)) ∨
          (p = 3 ∧ (s = .M24 ∨ s = .He) ∧ IsLpType 2 7 (PSimple p I)) ∨
          (p = 5 ∧ s = .Suz ∧ IsLpType 2 9 (PSimple p I)) ∨
          (p = 13 ∧ s = .M ∧ IsLpType 3 3 (PSimple p I)))

@[expose] def Input14_13SporK : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ}, p.Prime → p ≠ 2 → ∀ {e a : G} {J0 J1 : Subgroup G},
    a * e = e * a → a ^ p = 1 → GLAPComponent p (Cg e) J1 →
    GLAPComponent p (GLAPLayer p (Kx p J0 e ⊓ Cg a)) J0 →
    Kx p J0 e = ⨆ g ∈ Subgroup.zpowers a, GLBConj g J1 →
    ∀ s : TauCeti.SporadicName, IsSporType s (barOf p J1 ⧸ Subgroup.center (barOf p J1)) →
    CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic s).Group →
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p →
      IsChevSimple q (barOf p J0 ⧸ Subgroup.center (barOf p J0)) →
      GLBConj a J1 = J1 ∧
        ((p = 3 ∧ (s = .M23 ∨ s = .HS) ∧
            IsLpType 2 5 (barOf p J0 ⧸ Subgroup.center (barOf p J0))) ∨
          (p = 3 ∧ (s = .M24 ∨ s = .He) ∧
            IsLpType 2 7 (barOf p J0 ⧸ Subgroup.center (barOf p J0))) ∨
          (p = 5 ∧ s = .Suz ∧ IsLpType 2 9 (barOf p J0 ⧸ Subgroup.center (barOf p J0))) ∨
          (p = 13 ∧ s = .M ∧ IsLpType 3 3 (barOf p J0 ⧸ Subgroup.center (barOf p J0))))

theorem input14_13Spor_of_inputK (h : InputSporDownChevK) : Input14_13SporK := by
  intro G _ _ p hp hp2 e a J0 J1 hae hap hJ1 hJ0 hKx s hs hK q hq hq2 hqp hchev
  obtain ⟨hsimple, hnonab⟩ := CFSG.LocalAnalysis.GLTheoremA.chev_pSimple_simple_nonabelian hp hJ1
  rcases Claims1116b.config_cases hp hp2 hae hap hJ1 hJ0 hKx with ⟨haN, hJ0''⟩ | he2
  · obtain ⟨α, hα, I, hI, ⟨eJ⟩⟩ := Claims1116b.transfer_step hp haN hap hJ0''
    obtain ⟨-, hlist⟩ := h _ hsimple hnonab p hp hp2 s hs hK α hα I hI q hq hq2 hqp
      (Claims1116.isChevSimple_congr eJ hchev)
    refine ⟨mem_normalizer_iff_gLBConj_eq.1 haN, ?_⟩
    rcases hlist with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2, Claims1116b.isLpType_congr eJ h3⟩
    · exact Or.inr (Or.inl ⟨h1, h2, Claims1116b.isLpType_congr eJ h3⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, Claims1116b.isLpType_congr eJ h3⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, Claims1116b.isLpType_congr eJ h3⟩))
  · exfalso
    obtain ⟨e2⟩ := he2
    haveI := hsimple
    have hO : GLAPPrimeCore p (PSimple p J1) = ⊥ :=
      CFSG.LocalAnalysis.GLTheoremA.glaPPrimeCore_pSimple_eq_bot hp hJ1
    have hT := Claims1116b.glaPComponent_top_fixSubgroup_one hnonab hO
    have hT' : GLAPComponent p (⊤ : Subgroup (PSimple p J1)) ⊤ := by
      rw [Claims1116b.fixSubgroup_one_eq_top] at hT
      exact hT
    obtain ⟨e3⟩ := CFSG.LocalAnalysis.GLTheoremA.chevQ_pSimple_top_equiv hp hnonab hT'
    exact (h _ hsimple hnonab p hp hp2 s hs hK 1 (one_pow p) ⊤ hT q hq hq2 hqp
      (Claims1116.isChevSimple_congr (e2.trans e3.symm) hchev)).1 rfl

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} {q : ℕ}
  {e : G} {J0 J1 : Subgroup G}

theorem isKGroup_spor_of_prep (P : Prep1116 G m p B M E A a K q e J0 J1) {s : TauCeti.SporadicName}
    (hs : IsSporType s (barOf p J1 ⧸ Subgroup.center (barOf p J1))) :
    CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic s).Group := by
  have hKe : CFSG.Open.IsKGroup ↥(Cg e) :=
    Prop1310a5b.isKGroup_centralizer_of_standing P.standing P.he.2
  have hKJ : CFSG.Open.IsKGroup (barOf p J1 ⧸ Subgroup.center (barOf p J1)) :=
    ((hKe.of_le P.hJ1.1).quotient _).quotient _
  obtain ⟨f⟩ := hs
  exact hKJ.of_surjective f.toMonoidHom f.surjective

theorem prop1116_spor_of_inputsK (hSpor : Input14_13SporK) (hAut : Claims1116.InputSporAutRank)
    (hSuz : Claims1116.InputSuzFive) (hField : Claims1116.Input14_4_1Field)
    (h113 : Lemma113_iStatement) (h104i : Lemma104_iStatement) (h104ii : Lemma104_iiStatement)
    (h104vi : Lemma104_viStatement) : Prop1116SporStatement := by
  intro G _ _ m p B M E A a K q e J0 J1 P s hs
  have hp : p.Prime := P.hp
  have hp2 : p ≠ 2 := P.standing.ne_two
  obtain ⟨hJ1a, hcases⟩ := hSpor hp hp2 (Claims1116.prep_hea P) (Claims1116.prep_hap P) P.hJ1 P.hJ0'
    P.hJstar s hs (isKGroup_spor_of_prep P hs) q P.hq.1 P.hq.2.1 P.hq.2.2 P.hJ0chev
  have hKx : Kx p J0 e = J1 := by
    rw [P.hJstar]
    apply le_antisymm
    · exact iSup₂_le fun g hg => le_of_eq (gLBConj_eq_of_zpowers hJ1a hg)
    · exact le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (le_of_eq (gLBConj_one J1).symm)
  have hgam : ¬ barX p (Cg e) J1 ≤ GLBCore p 2 (barX p (Cg e) E) := by
    rw [← hKx]
    exact P.hgamma
  have hlist : (p = 3 ∧ (s = .M23 ∨ s = .HS ∨ s = .M24 ∨ s = .He)) ∨ (p = 5 ∧ s = .Suz) ∨
      (p = 13 ∧ s = .M) := by
    rcases hcases with ⟨h3, h | h, -⟩ | ⟨h3, h | h, -⟩ | ⟨h5, h, -⟩ | ⟨h13, h, -⟩
    · exact Or.inl ⟨h3, Or.inl h⟩
    · exact Or.inl ⟨h3, Or.inr (Or.inl h)⟩
    · exact Or.inl ⟨h3, Or.inr (Or.inr (Or.inl h))⟩
    · exact Or.inl ⟨h3, Or.inr (Or.inr (Or.inr h))⟩
    · exact Or.inr (Or.inl ⟨h5, h⟩)
    · exact Or.inr (Or.inr ⟨h13, h⟩)
  have hE3 : CFSG.Open.pRank p E = 3 := Claims1116.spor_rank hAut P hlist hs hgam
  rcases hcases with ⟨hp3, -, -⟩ | ⟨hp3, -, -⟩ | ⟨hp5, hsS, -⟩ | ⟨hp13, -, hL33⟩
  · subst hp3
    have := h113 P.toSec11 P.ha.1 P.ha.2 P.notD
    omega
  · subst hp3
    have := h113 P.toSec11 P.ha.1 P.ha.2 P.notD
    omega
  · subst hp5
    subst hsS
    exact Claims1116.spor_five hSuz h104i h104ii P hs hJ1a hgam hE3
  · subst hp13
    have hAel : IsElemAbelian 13 A := sec11_isElemAbelian_A P.toSec11
    exact P.notIv ⟨rfl, h104vi P.toSec11.toSec10Fails P.pair hE3,
      hField P.hK P.hq.1 P.hq.2.1 P.hq.2.2 P.hchev
        (inf_le_right.trans (Claims1116.le_cg_of_elemAbelian hAel P.ha.1))
        (Claims1116.isElemAbelian_of_le hAel inf_le_right) P.he.1 P.he.2 P.hJ0 P.hJ0K hL33⟩

end SporDown

section A5

open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)

@[expose] def Concl256K (K : Type) [Group K] (x : MulAut K) (y : K) (L : Subgroup K) : Prop :=
  ∃ S : MulAut K → Set (Subgroup K),
    (∀ a ∈ Prop1310a5b.Agrp x y, a ≠ 1 → ∀ J ∈ S a, GLAPComponent 3 (Prop1310a5.fixedSub a) J) ∧
    (∀ Y : Subgroup K, CFSG.Open.IsSubnormal Y (Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) S) → L ≤ Y →
      ¬ IsAltType 5 (barOf 3 Y)) ∧
    (∀ a ∈ Prop1310a5b.Agrp x y, a ≠ 1 → ∀ J ∈ S a, Prop1310a5b.IsAltOrChev (barOf 3 J) ∧
      ∀ (H : Type) [Group H] [Finite H], CFSG.LocalAnalysis.GLTheoremA.IsKHat H → CFSG.Open.IsKGroup H →
        GLAPPrimeCore 3 H = ⊥ → Prop1310a5b.IsPumpupOrSelf (barOf 3 J) H → Prop1310a5b.Good2319 H) ∧
    L ≤ ⨆ (J : Subgroup K) (_ : J ∈ S x), J

@[expose] def Input25_6A5K : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K → CFSG.Open.IsKGroup K →
    GLAPPrimeCore 3 K = ⊥ → ¬ IsPiGroup 3 K →
    ∀ x : MulAut K, orderOf x = 3 → ∀ L : Subgroup K, GLAPComponent 3 (Prop1310a5.fixedSub x) L →
      IsAltType 5 (barOf 3 L) → ∀ y ∈ L, orderOf y = 3 → Concl256K K x y L

@[expose] def Input25_6A5NonAltK : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K → CFSG.Open.IsKGroup K →
    GLAPPrimeCore 3 K = ⊥ → ¬ IsPiGroup 3 K → (¬ ∃ n : ℕ, IsAltType n (K ⧸ Subgroup.center K)) →
    ∀ x : MulAut K, orderOf x = 3 → ∀ L : Subgroup K, GLAPComponent 3 (Prop1310a5.fixedSub x) L →
      IsAltType 5 (barOf 3 L) → ∀ y ∈ L, orderOf y = 3 → Concl256K K x y L

theorem input25_6A5_of_nonAltK (hres : Input25_6A5NonAltK) : Input25_6A5K := by
  intro K _ _ hKhat hKK hcore hnotPi x hx L hL hL5 y hyL hy
  by_cases hAlt : ∃ n : ℕ, IsAltType n (K ⧸ Subgroup.center K)
  · obtain ⟨n, ⟨f⟩⟩ := hAlt
    exact absurd (InputsSeitz2.isPiGroup_of_alt_pumpup hKhat.1 hcore f hx hL hL5) hnotPi
  · exact hres K hKhat hKK hcore hnotPi hAlt x hx L hL hL5 y hyL hy

@[expose] def InputSporDownChev3K : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ s : TauCeti.SporadicName, IsSporType s S → CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic s).Group →
    ∀ α : MulAut S, α ^ 3 = 1 → ∀ I : Subgroup S, GLAPComponent 3 (fixSubgroup α) I →
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 3 → IsChevSimple q (PSimple 3 I) →
      α ≠ 1 ∧ Claims1116c.SporDownCase s 3 (PSimple 3 I)

theorem isKGroup_spor_of_quot {X : Type} [Group X] (hX : CFSG.Open.IsKGroup X) {s : TauCeti.SporadicName}
    (f : X ⧸ Subgroup.center X ≃* (TauCeti.CFSGIndex.sporadic s).Group) :
    CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic s).Group :=
  (hX.quotient _).of_surjective f.toMonoidHom f.surjective

theorem type_splitK (hnl : Prop1116Design.InputAltNotLie)
    (hKD : ∀ r : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 r)
    (hSD : InputSporDownChev3K) {K : Type} [Group K] [Finite K]
    (hK : CFSG.LocalAnalysis.GLTheoremA.IsKHat K) (hKK : CFSG.Open.IsKGroup K)
    (hAlt : ¬ ∃ n : ℕ, IsAltType n (K ⧸ Subgroup.center K)) {x : MulAut K} (hx : orderOf x = 3)
    {L : Subgroup K} (hL : GLAPComponent 3 (Prop1310a5.fixedSub x) L) (hL5 : IsAltType 5 (barOf 3 L)) :
    IsLieChar (· = 2) K ∨ IsLieChar (· = 5) K ∨
      IsSporType .HS (K ⧸ Subgroup.center K) ∨ IsSporType .M23 (K ⧸ Subgroup.center K) := by
  have hq := hK.1
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hL' : GLAPComponent 3 (fixSubgroup x) L := by rwa [Inputs256b.fixedSub_eq] at hL
  obtain ⟨hJ', ⟨eJ⟩⟩ := Inputs1415.center_transfer Nat.prime_three x hL'
  obtain ⟨eA⟩ := Inputs256b.isAltType_pSimple hL5
  have eI : PSimple 3 (L.map (QuotientGroup.mk' (Subgroup.center K))) ≃* alternatingGroup (Fin 5) :=
    eJ.symm.trans eA
  obtain ⟨i, ⟨f⟩⟩ := hK.2
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply f.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn => exact absurd ⟨n, ⟨f⟩⟩ hAlt
  | lie idx =>
    have hchev : IsChevSimple idx.1.characteristic (K ⧸ Subgroup.center K) :=
      Or.inl ⟨TauCeti.CFSGIndex.lie idx, rfl, ⟨f⟩⟩
    have hI := hKD idx.1.characteristic (K ⧸ Subgroup.center K) inferInstance hnab hchev
      (centerQuotientHom K x) (Inputs1415.centerQuotientHom_pow_eq_one hx3) _ hJ'
    by_cases h2 : idx.1.characteristic = 2
    · exact Or.inl ⟨idx, ⟨f⟩, h2⟩
    · rcases Prop1116Design.alt_chev_cases hnl h2 le_rfl ⟨eI⟩ hI with ⟨-, h5⟩ | ⟨h6, -⟩
      · exact Or.inr (Or.inl ⟨idx, ⟨f⟩, h5⟩)
      · omega
  | sporadic s =>
    obtain ⟨-, h⟩ := hSD (K ⧸ Subgroup.center K) inferInstance hnab s
      ⟨f⟩ (isKGroup_spor_of_quot hKK f) (centerQuotientHom K x)
      (Inputs1415.centerQuotientHom_pow_eq_one hx3) _ hJ' 5 Nat.prime_five
      (by norm_num) (by norm_num) (Claims1116c.isChevSimple_five_of_A5 eI)
    rcases h with ⟨-, hs, -⟩ | ⟨-, -, h7⟩ | ⟨h35, -⟩ | ⟨h313, -⟩
    · rcases hs with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr ⟨f⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨f⟩))
    · exfalso
      have h168 := Prop1116Design.card_statedProj_two_seven h7
      rw [Nat.card_congr eI.toEquiv, Inputs256b.card_alt5] at h168
      omega
    · omega
    · omega

theorem good2319_of_pumpup_alt5K (hnl : Prop1116Design.InputAltNotLie)
    (hKD : ∀ r : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 r)
    (hSD : InputSporDownChev3K)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOff : ∀ s : TauCeti.SporadicName,
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.OffPair s (CFSG.Blueprint.NativeSporadic.Carrier s))
    {J : Type} [Group J] (hJ5 : IsAltType 5 J) (H : Type) [Group H] [Finite H]
    (hH : CFSG.LocalAnalysis.GLTheoremA.IsKHat H) (hHK : CFSG.Open.IsKGroup H)
    (hP : Prop1310a5b.IsPumpupOrSelf J H) : Prop1310a5b.Good2319 H := by
  obtain ⟨σ, hσ3, J₁, hJ₁, ⟨e⟩⟩ := hP
  obtain ⟨e5⟩ := hJ5
  have hq := hH.1
  haveI : IsSimpleGroup (H ⧸ Subgroup.center H) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian H hq
  have hJ₁' : GLAPComponent 3 (fixSubgroup σ) J₁ := by rwa [Inputs256b.fixedSub_eq] at hJ₁
  obtain ⟨hI, ⟨eJ⟩⟩ := Inputs1415.center_transfer Nat.prime_three σ hJ₁'
  obtain ⟨eA⟩ := Inputs256b.isAltType_pSimple (L := J₁) ⟨e.trans e5⟩
  have eI : PSimple 3 (J₁.map (QuotientGroup.mk' (Subgroup.center H))) ≃* alternatingGroup (Fin 5) :=
    eJ.symm.trans eA
  obtain ⟨i, ⟨f⟩⟩ := hH.2
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply f.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn => exact Or.inl ⟨n, ⟨f⟩⟩
  | lie idx =>
    by_cases h3 : idx.1.characteristic = 3
    · exfalso
      have hchev : IsChevSimple idx.1.characteristic (H ⧸ Subgroup.center H) :=
        Or.inl ⟨TauCeti.CFSGIndex.lie idx, rfl, ⟨f⟩⟩
      have hI3 := hKD idx.1.characteristic (H ⧸ Subgroup.center H) inferInstance hnab hchev
        (centerQuotientHom H σ) (Inputs1415.centerQuotientHom_pow_eq_one hσ3) _ hI
      rw [h3] at hI3
      rcases Prop1116Design.alt_chev_cases hnl (by norm_num) le_rfl ⟨eI⟩ hI3 with ⟨-, h⟩ | ⟨h, -⟩ <;>
        omega
    · exact Or.inr (Or.inl ⟨idx.1.characteristic, h3, idx, ⟨f⟩, rfl⟩)
  | sporadic s =>
    obtain ⟨-, h⟩ := hSD (H ⧸ Subgroup.center H) inferInstance hnab s
      ⟨f⟩ (isKGroup_spor_of_quot hHK f) (centerQuotientHom H σ)
      (Inputs1415.centerQuotientHom_pow_eq_one hσ3) _ hI 5 Nat.prime_five
      (by norm_num) (by norm_num) (Claims1116c.isChevSimple_five_of_A5 eI)
    rcases h with ⟨-, hs, -⟩ | ⟨-, -, h7⟩ | ⟨h35, -⟩ | ⟨h313, -⟩
    · refine Or.inr (Or.inr fun A _ => ?_)
      by_contra hA
      have h3' : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut H)) :=
        le_trans (by omega) (CFSG.SectionRank.pRank_mono (by norm_num) (le_top (a := A)))
      have hpair := Inputs256.onePair_of_three_le Nat.prime_three (by norm_num) hOut hbr hOff hq f h3'
      rcases hs with rfl | rfl <;> revert hpair <;> decide
    · exfalso
      have h168 := Prop1116Design.card_statedProj_two_seven h7
      rw [Nat.card_congr eI.toEquiv, Inputs256b.card_alt5] at h168
      omega
    · omega
    · omega

theorem concl_hsM23K (hnl : Prop1116Design.InputAltNotLie)
    (hKD : ∀ r : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 r)
    (hSD : InputSporDownChev3K)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOff : ∀ s : TauCeti.SporadicName,
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.OffPair s (CFSG.Blueprint.NativeSporadic.Carrier s))
    (hGen : Inputs256b.InputGen2324c) {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (hcore : GLAPPrimeCore 3 K = ⊥)
    (hs : IsSporType .HS (K ⧸ Subgroup.center K) ∨ IsSporType .M23 (K ⧸ Subgroup.center K))
    {x : MulAut K} (hx : orderOf x = 3) {L : Subgroup K} (hL : GLAPComponent 3 (Prop1310a5.fixedSub x) L)
    (hL5 : IsAltType 5 (barOf 3 L)) {y : K} (hyL : y ∈ L) (hy : orderOf y = 3) : Concl256K K x y L := by
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hLx : L ≤ fixSubgroup x := by
    rw [← Inputs256b.fixedSub_eq]
    exact hL.1
  refine ⟨Inputs256b.a5Comps, fun a _ _ J hJ => hJ.1, fun Y hY hLY => ?_, fun a _ _ J hJ => ?_, ?_⟩
  · rw [hGen K hq hcore hs x hx L hL hL5 y hyL hy] at hY
    exact Inputs256b.not_alt5_of_subnormal_top hq hcore hx1 hLx hL5 hY hLY
  · exact ⟨Or.inl ⟨5, Inputs256b.isAltType_pSimple hJ.2⟩, fun H _ _ hH hHK _ hP =>
      good2319_of_pumpup_alt5K hnl hKD hSD hOut hbr hOff hJ.2 H hH hHK hP⟩
  · exact le_iSup₂_of_le (f := fun (J : Subgroup K) (_ : J ∈ Inputs256b.a5Comps x) => J) L ⟨hL, hL5⟩ le_rfl

theorem good2319_of_pumpup_chev5K (hKD : ∀ r : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 r)
    (hSD : InputSporDownChev3K)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOff : ∀ s : TauCeti.SporadicName,
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.OffPair s (CFSG.Blueprint.NativeSporadic.Carrier s))
    (hcc : Claims1116.Input3_3_OddChar) {J : Type} [Group J]
    (hJ : IsChevSimple 5 (J ⧸ Subgroup.center J)) (H : Type) [Group H] [Finite H]
    (hH : CFSG.LocalAnalysis.GLTheoremA.IsKHat H) (hHK : CFSG.Open.IsKGroup H)
    (hP : Prop1310a5b.IsPumpupOrSelf J H) : Prop1310a5b.Good2319 H := by
  obtain ⟨σ, hσ3, J₁, hJ₁, ⟨e⟩⟩ := hP
  have hq := hH.1
  haveI : IsSimpleGroup (H ⧸ Subgroup.center H) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian H hq
  have hJ₁' : GLAPComponent 3 (fixSubgroup σ) J₁ := by rwa [Inputs256b.fixedSub_eq] at hJ₁
  obtain ⟨hI, ⟨eJ⟩⟩ := Inputs1415.center_transfer Nat.prime_three σ hJ₁'
  have eZ : PSimple 3 J₁ ≃* J ⧸ Subgroup.center J :=
    QuotientGroup.congr (Subgroup.center (barOf 3 J₁)) (Subgroup.center J) e (Subgroup.map_center_eq e)
  have hX : IsChevSimple 5 (PSimple 3 (J₁.map (QuotientGroup.mk' (Subgroup.center H)))) :=
    CFSG.LocalAnalysis.GLTheoremA.chev_isChevSimple_of_mulEquiv (eJ.symm.trans eZ) hJ
  obtain ⟨i, ⟨f⟩⟩ := hH.2
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply f.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn => exact Or.inl ⟨n, ⟨f⟩⟩
  | lie idx =>
    by_cases h3 : idx.1.characteristic = 3
    · exfalso
      have hchev : IsChevSimple idx.1.characteristic (H ⧸ Subgroup.center H) :=
        Or.inl ⟨TauCeti.CFSGIndex.lie idx, rfl, ⟨f⟩⟩
      have hI3 := hKD idx.1.characteristic (H ⧸ Subgroup.center H) inferInstance hnab hchev
        (centerQuotientHom H σ) (Inputs1415.centerQuotientHom_pow_eq_one hσ3) _ hI
      rw [h3] at hI3
      rcases hcc _ 3 5 hI3 hX (by norm_num) with h | h <;> omega
    · exact Or.inr (Or.inl ⟨idx.1.characteristic, h3, idx, ⟨f⟩, rfl⟩)
  | sporadic s =>
    obtain ⟨-, h⟩ := hSD (H ⧸ Subgroup.center H) inferInstance hnab s
      ⟨f⟩ (isKGroup_spor_of_quot hHK f) (centerQuotientHom H σ)
      (Inputs1415.centerQuotientHom_pow_eq_one hσ3) _ hI 5 Nat.prime_five
      (by norm_num) (by norm_num) hX
    rcases h with ⟨-, hs, -⟩ | ⟨-, -, h7⟩ | ⟨h35, -⟩ | ⟨h313, -⟩
    · refine Or.inr (Or.inr fun A _ => ?_)
      by_contra hA
      have h3' : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut H)) :=
        le_trans (by omega) (CFSG.SectionRank.pRank_mono (by norm_num) (le_top (a := A)))
      have hpair := Inputs256.onePair_of_three_le Nat.prime_three (by norm_num) hOut hbr hOff hq f h3'
      rcases hs with rfl | rfl <;> revert hpair <;> decide
    · exfalso
      rcases hcc _ 7 5 (Inputs256b.isChevSimple_seven_of_isLpType h7) hX (by norm_num) with h | h <;> omega
    · omega
    · omega

theorem concl_chev5K (hKD : ∀ r : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 r)
    (hSD : InputSporDownChev3K)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOff : ∀ s : TauCeti.SporadicName,
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.OffPair s (CFSG.Blueprint.NativeSporadic.Carrier s))
    (hcc : Claims1116.Input3_3_OddChar) (hGen5 : Inputs256b.InputGen2311Five) {K : Type} [Group K] [Finite K]
    (hK : CFSG.LocalAnalysis.GLTheoremA.IsKHat K) (hcore : GLAPPrimeCore 3 K = ⊥)
    (h5 : IsLieChar (· = 5) K) {x : MulAut K} (hx : orderOf x = 3) {L : Subgroup K}
    (hL : GLAPComponent 3 (Prop1310a5.fixedSub x) L) (hL5 : IsAltType 5 (barOf 3 L)) {y : K} (hyL : y ∈ L)
    (hy : orderOf y = 3) : Concl256K K x y L := by
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hLx : L ≤ fixSubgroup x := by
    rw [← Inputs256b.fixedSub_eq]
    exact hL.1
  obtain ⟨eL⟩ := Inputs256b.isAltType_pSimple hL5
  refine ⟨Inputs256b.chev5Comps, fun a _ _ J hJ => hJ.1, fun Y hY hLY => ?_, fun a _ _ J hJ => ?_, ?_⟩
  · rw [hGen5 K hK hcore h5 x hx L hL hL5 y hyL hy] at hY
    exact Inputs256b.not_alt5_of_subnormal_top hK.1 hcore hx1 hLx hL5 hY hLY
  · exact ⟨Inputs256b.isAltOrChev_of_chev5 (J := barOf 3 J) hJ.2, fun H _ _ hH hHK _ hP =>
      good2319_of_pumpup_chev5K hKD hSD hOut hbr hOff hcc (J := barOf 3 J) hJ.2 H hH hHK hP⟩
  · exact le_iSup₂_of_le (f := fun (J : Subgroup K) (_ : J ∈ Inputs256b.chev5Comps x) => J) L
      ⟨hL, Claims1116c.isChevSimple_five_of_A5 eL⟩ le_rfl

theorem concl_of_weakK (hnl : Prop1116Design.InputAltNotLie)
    (hKD : ∀ r : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 r)
    (hSD : InputSporDownChev3K)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOff : ∀ s : TauCeti.SporadicName,
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.OffPair s (CFSG.Blueprint.NativeSporadic.Carrier s))
    {K : Type} [Group K] {x : MulAut K} {y : K} {L : Subgroup K} (h : Inputs256b.Concl256W K x y L) :
    Concl256K K x y L := by
  obtain ⟨S, h0, h1, h2, h3⟩ := h
  refine ⟨S, h0, h1, fun a ha ha1 J hJ => ?_, h3⟩
  rcases h2 a ha ha1 J hJ with h5 | h
  · exact ⟨Or.inl ⟨5, Lemma1315b.isAltType_center_quot le_rfl h5⟩, fun H _ _ hH hHK _ hP =>
      good2319_of_pumpup_alt5K hnl hKD hSD hOut hbr hOff h5 H hH hHK hP⟩
  · exact ⟨h.1, fun H _ _ hH _ hc hP => h.2 H hH hc hP⟩

theorem input25_6A5NonAlt_of_factsK (hnl : Prop1116Design.InputAltNotLie)
    (hKD : ∀ r : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 r)
    (hSD : InputSporDownChev3K)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOff : ∀ s : TauCeti.SporadicName,
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.OffPair s (CFSG.Blueprint.NativeSporadic.Carrier s))
    (hcc : Claims1116.Input3_3_OddChar) (hGen : Inputs256b.InputGen2324c)
    (hGen5 : Inputs256b.InputGen2311Five) (h2 : Inputs256b.Input25_6A5Chev2) : Input25_6A5NonAltK := by
  intro K _ _ hK hKK hcore hnotPi hAlt x hx L hL hL5 y hyL hy
  rcases type_splitK hnl hKD hSD hK hKK hAlt hx hL hL5 with h | h | h | h
  · exact concl_of_weakK hnl hKD hSD hOut hbr hOff (h2 K hK hcore hnotPi hAlt h x hx L hL hL5 y hyL hy)
  · exact concl_chev5K hKD hSD hOut hbr hOff hcc hGen5 hK hcore h hx hL hL5 hyL hy
  · exact concl_hsM23K hnl hKD hSD hOut hbr hOff hGen hK.1 hcore (Or.inl h) hx hL hL5 hyL hy
  · exact concl_hsM23K hnl hKD hSD hOut hbr hOff hGen hK.1 hcore (Or.inr h) hx hL hL5 hyL hy

end A5

section A5Consumer

variable {G : Type} [Group G] [Finite G]

theorem comp_le_M'K (hI183 : Prop115.Input18_3Gen) (hI182 : Lemma1313.Input18_3Two)
    (hDiag : Lemma1313Z.Input18_3DiagZ)
    {m : ℕ} (hS : GLStanding G m 3) {M : Subgroup G} {d u : G}
    (hdord : orderOf d = 3) (huord : orderOf u = 3) (hdu : d * u = u * d)
    (hM : ∀ Kc : Subgroup G, GLAPComponent 3 (Cg u) Kc → Prop1310a5b.Good2319 (barOf 3 Kc) → Kc ≤ M)
    {K0 : Subgroup G} (hK0 : GLAPComponent 3 (Cg2 d u) K0)
    (hgood : Prop1310a5b.IsAltOrChev (barOf 3 K0) ∧ ∀ (H : Type) [Group H] [Finite H],
      CFSG.LocalAnalysis.GLTheoremA.IsKHat H → CFSG.Open.IsKGroup H → GLAPPrimeCore 3 H = ⊥ →
        Prop1310a5b.IsPumpupOrSelf (barOf 3 K0) H → Prop1310a5b.Good2319 H) : K0 ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hu1 : u ≠ 1 := by
    rintro rfl
    simp at huord
  have hKG : CFSG.Open.IsKGroup ↥(Cg u) := Prop1310a5b.isKGroup_centralizer_of_standing hS hu1
  have hK0hull : K0 ≤ ⨆ g ∈ GLAPLayer 3 (Cg u), GLBConj g K0 :=
    le_iSup₂_of_le (f := fun g (_ : g ∈ GLAPLayer 3 (Cg u)) => GLBConj g K0) (1 : G) (one_mem _)
      (le_of_eq (gLBConj_one K0).symm)
  have hI1 := hI183 3 hp (by norm_num) G hS.simple hS.nonabelian hS.kProper d u hdord huord hdu K0 hK0
  have hI2 := hI182 3 hp (by norm_num) G hS.simple hS.nonabelian hS.kProper d u hdord huord hdu K0 hK0
  rcases hI1 with ⟨Kc, hKc, hKcEq, hdKc⟩ | ⟨Lf, hLf, hinj, hcyc, hsup⟩
  ·
    have hK0Kc : K0 ≤ Kc := hKcEq ▸ hK0hull
    have hdN : d ∈ Subgroup.normalizer (Kc : Set G) := mem_normalizer_iff_gLBConj_eq.2 hdKc
    have hd3 : d ^ 3 = 1 := hdord ▸ pow_orderOf_eq_one d
    have hK02 : GLAPComponent 3 (Kc ⊓ Cg d) K0 := by
      rw [hKcEq] at hI2
      exact hI2
    have hbar := Prop115b.barX_glaPComponent_of_le hp (inf_le_left : Kc ⊓ Cg d ≤ Kc) hK02
    have hfix : Prop1310a5.fixedSub (barAut 3 Kc ⟨d, hdN⟩) = barX 3 Kc (Kc ⊓ Cg d) := by
      have h := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.fixedSub_barAut_eq hd3 hdN
      rw [← h]
      exact Subgroup.ext fun _ => Iff.rfl
    have hσ3 : (barAut 3 Kc ⟨d, hdN⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (Kc : Set G))) ^ 3 = 1 := Subtype.ext hd3
      rw [this, map_one]
    have hKhat := Prop1310a5b.isKHat_barOf_of_comp hKG hKc
    have hKKc : CFSG.Open.IsKGroup (barOf 3 Kc) := (hKG.of_le hKc.1).quotient _
    have hcoreK : GLAPPrimeCore 3 (barOf 3 Kc) = ⊥ := Lemma1311.glaPPrimeCore_quot_eq_bot 3 ↥Kc
    have hgoodKc : Prop1310a5b.Good2319 (barOf 3 Kc) := by
      refine hgood.2 (barOf 3 Kc) hKhat hKKc hcoreK ⟨barAut 3 Kc ⟨d, hdN⟩, hσ3, barX 3 Kc K0, ?_, ?_⟩
      · rw [hfix]
        exact hbar
      · exact ⟨(Prop115.barOfIso (p := 3) hK0Kc).symm⟩
    exact hK0Kc.trans (hM Kc hKc hgoodKc)
  ·
    have hLfM : ∀ i, Lf i ≤ M := by
      intro i
      obtain ⟨eZ⟩ := hDiag 3 hp (by norm_num) G hS.simple hS.nonabelian hS.kProper d u hdord huord hdu
        K0 hK0 Lf hLf hinj hcyc hsup i
      have hLg : Prop1310a5b.Good2319 (barOf 3 (Lf i)) :=
        Prop1310a5b.good2319_of_isAltOrChev (Prop1310a5b.isAltOrChev_of_quotCenter eZ hgood.1)
      exact hM (Lf i) (hLf i) hLg
    exact hK0hull.trans (hsup ▸ iSup_le hLfM)

variable {m : ℕ} {B M L0 L L0b : Subgroup G} {d b u0 : G}

theorem tfam_le_MK (c : Claims1310.Cfg' G m B M L0 L L0b d b u0) (hI183 : Prop115.Input18_3Gen)
    (hI182 : Lemma1313.Input18_3Two) (hDiag : Lemma1313Z.Input18_3DiagZ)
    (S : MulAut (barOf 3 L) → Set (Subgroup (barOf 3 L)))
    (hS2 : ∀ a ∈ Prop1310a5b.Agrp c.xOf c.yOf, a ≠ 1 → ∀ J ∈ S a, Prop1310a5b.IsAltOrChev (barOf 3 J) ∧
      ∀ (H : Type) [Group H] [Finite H], CFSG.LocalAnalysis.GLTheoremA.IsKHat H → CFSG.Open.IsKGroup H →
        GLAPPrimeCore 3 H = ⊥ → Prop1310a5b.IsPumpupOrSelf (barOf 3 J) H → Prop1310a5b.Good2319 H)
    {K0 : Subgroup G} (hK0 : K0 ∈ c.Tfam S) : K0 ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu, hne, hK0c, hmem⟩ := hK0
  have huB : u ∈ B := c.hU1B hu
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hne (map_one (barAut 3 L))
  have huord : orderOf u = 3 := orderOf_eq_prime (c.hBel.2 u huB) hu1
  have hdu : d * u = u * d := c.hU1d u hu
  have hDeq : Cg2 d u = Cg d ⊓ Cg u := by
    ext x
    simp [Cg2, Cg, Subgroup.mem_centralizer_iff]
  have hsn : CFSG.Open.IsSubnormal (L ⊓ Cg u) (Cg2 d u) := by
    rw [hDeq]
    exact isSubnormal_inf c.hLc.2.1 (Cg u)
  have hK0' : GLAPComponent 3 (Cg2 d u) K0 :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.glaPComponent_up Nat.prime_three hK0c
      (by rw [hDeq]; exact inf_le_inf_right _ c.hLc.1) (isSubnormal_trans' hK0c.2.1 hsn)
  obtain ⟨hAC, hP⟩ := hS2 _ (c.barAut_mem_A u hu) hne _ hmem
  have hiso : barOf 3 K0 ≃* barOf 3 (barX 3 L K0) :=
    Prop115.barOfIso (p := 3) (hK0c.1.trans inf_le_left)
  refine comp_le_M'K hI183 hI182 hDiag c.standing c.hdord huord hdu (c.hM u hu hu1) hK0'
    ⟨Prop1310a5b.isAltOrChev_of_equiv hiso.symm hAC, ?_⟩
  intro H _ _ hH hHK hcore hpump
  refine hP H hH hHK hcore ?_
  obtain ⟨σ, hσ, J₁, hJ₁, ⟨e⟩⟩ := hpump
  exact ⟨σ, hσ, J₁, hJ₁, ⟨e.trans hiso⟩⟩

theorem false_of_inputsK (c : Claims1310.Cfg' G m B M L0 L L0b d b u0) (hI25 : Input25_6A5K)
    (hI183 : Prop115.Input18_3Gen) (hI182 : Lemma1313.Input18_3Two)
    (hDiag : Lemma1313Z.Input18_3DiagZ) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKL : CFSG.Open.IsKGroup (barOf 3 L) :=
    ((Prop1310a5b.isKGroup_centralizer_of_standing c.standing c.hdne).of_le c.hLc.1).quotient _
  obtain ⟨S, hS0, hS1, hS2, hS3⟩ := hI25 (barOf 3 L) c.hKhat hKL
    (Lemma1311.glaPPrimeCore_quot_eq_bot 3 ↥L) c.hnotPi c.xOf c.xorder (barX 3 L L0b) c.hL'comp
    c.hL'5 c.yOf c.hyL' c.yorder
  have hxS : barX 3 L L0b ∈ S c.xOf :=
    Prop1310a5b.mem_of_le_iSup_comp (X := Prop1310a5.fixedSub c.xOf) (S := S c.xOf)
      (hS0 _ c.hxA c.xne) c.hL'comp hS3
  have hL0bT : L0b ∈ c.Tfam S := ⟨b, c.bU1, c.xne, c.hL0bc, hxS⟩
  have hJM : c.Jstar S ≤ M := iSup₂_le fun K0 hK0 => tfam_le_MK c hI183 hI182 hDiag S hS2 hK0
  have hJL : c.Jstar S ≤ L := iSup₂_le fun K0 hK0 => c.tfam_le_L hK0
  have hL0bJ : L0b ≤ c.Jstar S := le_iSup₂_of_le L0b hL0bT le_rfl
  have hJT : c.Jstar S ≤ M ⊓ Cg d := le_inf hJM (hJL.trans c.hLc.1)
  set Y1 : Subgroup G := c.Jstar S ⊓ L0 with hY1
  have hY1sn : CFSG.Open.IsSubnormal Y1 (c.Jstar S) := by
    have h := isSubnormal_inf c.hL0M.2.1 (c.Jstar S)
    rw [inf_eq_right.2 hJT] at h
    have e : Y1 = L0 ⊓ c.Jstar S := inf_comm _ _
    rw [e]
    exact h
  have hKs : Prop1310a5b.Kstar (Prop1310a5b.Agrp c.xOf c.yOf) S = barX 3 L (c.Jstar S) := c.Ks_eq S hS0
  have hYsn : CFSG.Open.IsSubnormal (barX 3 L Y1) (Prop1310a5b.Kstar (Prop1310a5b.Agrp c.xOf c.yOf) S) := by
    rw [hKs]
    exact Prop1310a5b.isSubnormal_barX_of hY1sn
  have hL0bY1 : L0b ≤ Y1 := le_inf hL0bJ c.hL0bL0
  have hL'Y : barX 3 L L0b ≤ barX 3 L Y1 := CFSG.LocalAnalysis.GLTheoremB.barX_mono 3 hL0bY1
  have hY1L : Y1 ≤ L := inf_le_left.trans hJL
  have hbar : barX 3 L0 L0b = ⊤ := by
    have h := Lemma1313.barX_le_glaPLayer_inf_cent (p := 3) (M := L0) (L0 := L0) (b := b) le_rfl le_rfl
      c.hbord c.hbL0 c.hcomm c.hq0
    rw [barX_self] at h
    rw [c.hL0b]
    exact top_le_iff.1 h
  have hcov : ∀ x ∈ L0, ∃ y ∈ Y1, ∃ n ∈ GLAPPrimeCoreOf 3 L0, x = y * n := by
    intro x hx
    obtain ⟨k, hk, hkn⟩ :=
      (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barX_eq_top_iff 3 c.hL0bL0).1 hbar x hx
    exact ⟨k, hL0bY1 hk, k⁻¹ * x, hkn, by group⟩
  obtain ⟨e1⟩ := Prop1310a5b.barOf_equiv_of_cover (Y := Y1) (L0 := L0) inf_le_right hcov c.hq0
  have h5Y : IsAltType 5 (barOf 3 (barX 3 L Y1)) := by
    obtain ⟨f⟩ := c.hL05
    exact ⟨(Prop115.barOfIso (p := 3) hY1L).symm.trans (e1.trans f)⟩
  exact hS1 (barX 3 L Y1) hYsn hL'Y h5Y

end A5Consumer

theorem prop1310_a5_of_MK (h1312 : Lemma1312Statement) (h1313 : Lemma1313Statement)
    (hI25 : Input25_6A5K) (hI183 : Prop115.Input18_3Gen)
    (hI182 : Lemma1313.Input18_3Two) (hDiag : Lemma1313Z.Input18_3DiagZ)
    (hM : Claims1310.Rank3CuM) : Prop1310_a5Statement := by
  intro G _ _ m p B M E A D T R L0 d h h139b
  have h139b' := h139b
  obtain ⟨hp3, hall⟩ := h139b
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS : GLStanding G m 3 := h.standing
  obtain ⟨U, hU, -⟩ := h1312 h
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU.2.2.2
  have hb1' : b ≠ 1 := fun e => hb1 (Subtype.ext e)
  obtain ⟨⟨u0, hu0⟩, hu01⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU.2.2.1
  have hu01' : u0 ≠ 1 := fun e => hu01 (Subtype.ext e)
  have hu0U : u0 ∈ U := (Subgroup.mem_inf.1 hu0).1
  have hu0L0 : u0 ∈ L0 := (Subgroup.mem_inf.1 hu0).2
  have hbU : b ∈ U := (Subgroup.mem_inf.1 hb).2
  obtain ⟨hbord, hbM, hbC, hbL0, hcomm, hL0M, hquasi⟩ := Lemma1313.setting_facts h hU hb hb1'
  obtain ⟨-, ⟨hLc, hL0bc, hisoL⟩, -, hLpi⟩ := h1313 h hU hb hb1'
  have hUB : U ≤ B := hU.1.1
  have hUel : IsElemAbelian 3 U := hU.1.2.1
  have hBel : IsElemAbelian 3 B := h.bOne.1.1
  have hU1U : Subgroup.closure {u0, b} ≤ U := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hu0U
    · exact hbU
  have hMm : ∀ u ∈ Subgroup.closure {u0, b}, u ≠ 1 → ∀ Kc : Subgroup G, GLAPComponent 3 (Cg u) Kc →
      Prop1310a5b.Good2319 (barOf 3 Kc) → Kc ≤ M :=
    fun u hu hu1 => hM h h139b' hU u (hU1U hu) hu1
  have hdD : d ∈ D := h.hd.1
  have hdord : orderOf d = 3 := orderOf_eq_prime (h.hD.2.1.2 d hdD) h.hd.2
  have hdb : d * b = b * d := Subgroup.mem_centralizer_iff.1 hbC d (Set.mem_singleton d)
  have hdu0 : d * u0 = u0 * d :=
    Subgroup.mem_centralizer_iff.1 (hU.2.1 hu0U) d (Set.mem_singleton d)
  have hbu0 : b * u0 = u0 * b := elemAbelian_comm hUel hbU hu0U
  obtain ⟨S0, hS0, -, hEq⟩ := Lemma1311.pComp_piLayer_summand Nat.prime_three h.hL0
  have hL0N : GLAPComponent 3 (Istar 3 M D ⊓ Cg d) L0 := by
    rw [hEq]
    exact hS0
  have hNT : Istar 3 M D ⊓ Cg d ≤ M ⊓ Cg d := inf_le_inf_right _ (istar_le_M 3 M D)
  have hTN : M ⊓ Cg d ≤ Subgroup.normalizer ((Istar 3 M D ⊓ Cg d : Subgroup G) : Set G) := by
    intro t ht
    obtain ⟨htM, htC⟩ := Subgroup.mem_inf.1 ht
    have hdt : d * t = t * d := Subgroup.mem_centralizer_iff.1 htC d (Set.mem_singleton d)
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [← mem_gLBConj, Lemma1313.gLBConj_istar_inf_centralizer htM hdt]
  have hL0T : GLAPComponent 3 (M ⊓ Cg d) L0 :=
    Lemma1311.glaPComponent_of_normal Nat.prime_three hNT hTN hL0N
  obtain ⟨L', hL'⟩ := Prop1310a5b.exists_pComp_istar h
  have hL'5 : IsAltType 5 (barOf 3 L') := hall L' hL'
  obtain ⟨e0⟩ := hisoL L' hL'
  obtain ⟨eL0b⟩ := Lemma1313.barOf_L0b_iso h hU hb hb1'
  have hL0b5 : IsAltType 5 (barOf 3 (GLAPLayer 3 (L0 ⊓ Cg b))) := by
    obtain ⟨f⟩ := hL'5
    exact ⟨e0.trans f⟩
  have hL05 : IsAltType 5 (barOf 3 L0) := by
    obtain ⟨f⟩ := hL0b5
    exact ⟨eL0b.symm.trans f⟩
  have hnotPi : ¬ IsPiGroup 3 (barOf 3 (⨆ g ∈ GLAPLayer 3 (Cg d), GLBConj g (GLAPLayer 3 (L0 ⊓ Cg b)))) :=
    fun hPi => hLpi (Lemma1313.le_piOf_of_comp' hLc hPi)
  have c : Claims1310.Cfg' G m B M L0 (⨆ g ∈ GLAPLayer 3 (Cg d), GLBConj g (GLAPLayer 3 (L0 ⊓ Cg b)))
      (GLAPLayer 3 (L0 ⊓ Cg b)) d b u0 :=
    { standing := hS
      hBel := hBel
      hM := hMm
      hdord := hdord
      hbB := hUB hbU
      hb1 := hb1'
      hdb := hdb
      hu0B := hUB hu0U
      hu01 := hu01'
      hdu0 := hdu0
      hbu0 := hbu0
      hu0L0 := hu0L0
      hbL0 := hbL0
      hcomm := hcomm
      hq0 := hquasi
      hL0M := hL0T
      hL05 := hL05
      hL0b := rfl
      hL := rfl
      hLc := hLc
      hL0bc := hL0bc
      hL0b5 := hL0b5
      hnotPi := hnotPi }
  exact false_of_inputsK c hI25 hI183 hI182 hDiag

theorem prop1310_a5_of_resK (h1312 : Lemma1312Statement) (h1313 : Lemma1313Statement)
    (hI25 : Input25_6A5K) (hI183 : Prop115.Input18_3Gen)
    (hI182 : Lemma1313.Input18_3Two) (hDiag : Lemma1313Z.Input18_3DiagZ)
    (hI2319 : Lemma1315b.Input23_19) (h112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2)
    (hres : Claims1310.Rank3CuRes) : Prop1310_a5Statement :=
  prop1310_a5_of_MK h1312 h1313 hI25 hI183 hI182 hDiag (Claims1310.rank3CuM_of_res hI2319 h112 hres)

section Holds

set_option linter.unusedSectionVars false

theorem inputSporDownChev_of_rowsK
    (hrow : ∀ (s : TauCeti.SporadicName) (p : ℕ), p.Prime → p ≠ 2 →
      p ^ 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s →
      CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic s).Group → Claims1116c.SporDownRow s p) :
    InputSporDownChevK := by
  intro S _ _ hS hnc p hp hp2 s hs hK α hα I hI q hq hq2 hqp hchev
  haveI := hS
  haveI : Fact p.Prime := ⟨hp⟩
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [Claims1116b.fixSubgroup_one_eq_top] at hI
    obtain ⟨f⟩ := CFSG.LocalAnalysis.GLTheoremA.chevQ_pSimple_top_equiv hp hnc hI
    exact Claims1116c.not_isChevSimple_of_isSporType (Claims1116.isSporType_congr f.symm hs) hq hq2 hchev
  refine ⟨hα1, ?_⟩
  obtain ⟨x, rfl, hxp⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow hp hp2
    (Claims1116b.center_eq_bot_of_simple hnc)
    (CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds S hS hnc s hs) α hα
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hα1 (map_one _)
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  rw [CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj] at hI
  have hcard : Nat.card S = CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s :=
    (Nat.card_congr hs.some.toEquiv).trans
      (CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds s)
  by_cases h2 : p ^ 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s
  · exact hrow s p hp hp2 h2 hK S hS hs x hxo I hI q hq hq2 hqp hchev
  · exact (CFSG.HardMathSupport.Solomon.Coordinator.no_glaPComponent_of_exact hp hxo
      (by rw [hcard]; exact h2) hI).elim

theorem sporDownRowK
    (hM11 : SporTables3.MElevenNoL223) (s : TauCeti.SporadicName) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hdvd : p ^ 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s)
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic s).Group) : Claims1116c.SporDownRow s p := by
  have hR := SporTables3.sporDownResidualK_of_mElevenDown (SporTables3.mElevenDown_of_noL223 hM11)
  have hdvd' : p ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic s).Group := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds s]
    exact hdvd
  rcases CFSG.HardMathSupport.Solomon.Coordinator.sporadicP2Table_holds s p hp hp2 hdvd' with
    h1 | h1
  · rcases h1 with ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, rfl⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
      exacts [Claims1116c.sporDownRow_J3_three, Claims1116c.sporDownRow_McL_three,
        Claims1116c.sporDownRow_Suz_three, Claims1116c.sporDownRow_ON_three,
        Claims1116c.sporDownRow_Co3_three, Claims1116c.sporDownRow_Co2_three,
        Claims1116d.sporDownRow_Co1_three, Claims1116c.sporDownRow_Fi22_three,
        Claims1116c.sporDownRow_Fi23_three, Claims1116c.sporDownRow_Fi24Prime_three,
        Claims1116c.sporDownRow_HN_three, Claims1116c.sporDownRow_Ly_three,
        Claims1116c.sporDownRow_Th_three, SporTables2.sporDownRow_B_three_of_kGroup hK,
        SporTables2.sporDownRow_M_three_of_kGroup hK]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl
      exacts [Claims1116c.sporDownRow_Co1_five, Claims1116c.sporDownRow_HN_five,
        Claims1116c.sporDownRow_Ly_five, SporTables2.sporDownRow_B_five_of_kGroup hK,
        SporTables2.sporDownRow_M_five_of_kGroup hK]
    · exact Claims1116c.sporDownRow_M_seven
  · rcases h1 with ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, rfl⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [Claims1116c.sporDownRow_M11_three, Claims1116c.sporDownRow_M12_three,
        Claims1116c.sporDownRow_M22_three, Claims1116c.sporDownRow_M23_three,
        Claims1116d.sporDownRow_M24_three, Claims1116d.sporDownRow_J2_three,
        Claims1116c.sporDownRow_J4_three, Claims1116c.sporDownRow_HS_three,
        Claims1116d.sporDownRow_Ru_three, Claims1116c.sporDownRow_He_three]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [Claims1116c.sporDownRow_J2_five, Claims1116c.sporDownRow_HS_five,
        Claims1116c.sporDownRow_McL_five, Claims1116c.sporDownRow_Suz_five,
        Claims1116c.sporDownRow_He_five, Claims1116c.sporDownRow_Ru_five,
        Claims1116c.sporDownRow_Co2_five, Claims1116c.sporDownRow_Co3_five,
        Claims1116c.sporDownRow_Fi22_five, SporTables2.sporDownRow_Fi23_five hR.Fi23_five,
        SporTables2.sporDownRow_Fi24_five hR.Fi24Prime_five, Claims1116c.sporDownRow_Th_five]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [Claims1116c.sporDownRow_He_seven, Claims1116c.sporDownRow_ON_seven,
        Claims1116d.sporDownRow_Co1_seven, Claims1116d.sporDownRow_Fi24_seven,
        Claims1116c.sporDownRow_Th_seven, SporTables2.sporDownRow_B_seven hR.B_seven]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      exacts [Claims1116c.sporDownRow_J4_eleven, SporTables2.sporDownRow_M_eleven hR.M_eleven]
    · exact SporTables2.sporDownRow_M_thirteen_of hR.M_thirteen_A

theorem inputSporDownChevK_holds
    (hM11 : SporTables3.MElevenNoL223) : InputSporDownChevK :=
  inputSporDownChev_of_rowsK (sporDownRowK hM11)

theorem inputSporDownChev3_of_rowsK
    (hB : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group → Claims1116c.SporDownRow .B 3)
    (hM : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group → Claims1116c.SporDownRow .M 3) :
    InputSporDownChev3K := by
  intro S _ _ hS hnc s hs hK α hα I hI q hq hq2 hq3 hchev
  haveI := hS
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [Claims1116b.fixSubgroup_one_eq_top] at hI
    obtain ⟨f⟩ := CFSG.LocalAnalysis.GLTheoremA.chevQ_pSimple_top_equiv Nat.prime_three hnc hI
    exact Claims1116c.not_isChevSimple_of_isSporType (Claims1116.isSporType_congr f.symm hs) hq hq2 hchev
  refine ⟨hα1, ?_⟩
  obtain ⟨x, rfl, hxp⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow Nat.prime_three
    (by norm_num) (Claims1116b.center_eq_bot_of_simple hnc)
    (CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds S hS hnc s hs) α hα
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hα1 (map_one _)
  have hxo : orderOf x = 3 := orderOf_eq_prime hxp hx1
  rw [CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj] at hI
  have hcard : Nat.card S = CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s :=
    (Nat.card_congr hs.some.toEquiv).trans
      (CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds s)
  by_cases h2 : 3 ^ 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s
  · have hrow : Claims1116c.SporDownRow s 3 := by
      have hdvd' : 3 ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic s).Group := by
        rw [CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds s]
        exact h2
      rcases CFSG.HardMathSupport.Solomon.Coordinator.sporadicP2Table_holds s 3 Nat.prime_three
          (by norm_num) hdvd' with h1 | h1
      · rcases h1 with ⟨-, hs'⟩ | ⟨h35, -⟩ | ⟨h37, -⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
          rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl
          exacts [Claims1116c.sporDownRow_J3_three, Claims1116c.sporDownRow_McL_three,
            Claims1116c.sporDownRow_Suz_three, Claims1116c.sporDownRow_ON_three,
            Claims1116c.sporDownRow_Co3_three, Claims1116c.sporDownRow_Co2_three,
            Claims1116d.sporDownRow_Co1_three, Claims1116c.sporDownRow_Fi22_three,
            Claims1116c.sporDownRow_Fi23_three, Claims1116c.sporDownRow_Fi24Prime_three,
            Claims1116c.sporDownRow_HN_three, Claims1116c.sporDownRow_Ly_three,
            Claims1116c.sporDownRow_Th_three, hB hK, hM hK]
        · omega
        · omega
      · rcases h1 with ⟨-, hs'⟩ | ⟨h35, -⟩ | ⟨h37, -⟩ | ⟨h311, -⟩ | ⟨h313, -⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
          rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          exacts [Claims1116c.sporDownRow_M11_three, Claims1116c.sporDownRow_M12_three,
            Claims1116c.sporDownRow_M22_three, Claims1116c.sporDownRow_M23_three,
            Claims1116d.sporDownRow_M24_three, Claims1116d.sporDownRow_J2_three,
            Claims1116c.sporDownRow_J4_three, Claims1116c.sporDownRow_HS_three,
            Claims1116d.sporDownRow_Ru_three, Claims1116c.sporDownRow_He_three]
        all_goals omega
    exact hrow S hS hs x hxo I hI q hq hq2 hq3 hchev
  · exact (CFSG.HardMathSupport.Solomon.Coordinator.no_glaPComponent_of_exact Nat.prime_three hxo
      (by rw [hcard]; exact h2) hI).elim

theorem input25_6A5NonAlt_of_residualsK
    (hSD : InputSporDownChev3K) (hGen : Inputs256b.InputGen2324c)
    (hGen5 : Inputs256b.InputGen2311Five) (h2 : Inputs256b.Input25_6A5Chev2) : Input25_6A5NonAltK :=
  input25_6A5NonAlt_of_factsK AltFacts4.inputAltNotLie_holds
    (fun r => PumpDefChar.kdChevDownQ_odd Nat.prime_three (by norm_num) r) hSD
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    (CFSG.HardMathSupport.Timmesfeld.Tables.Census.offPair_carrier
      CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicBMData_holds)
    CrossCharOdd.input3_3_OddChar_holds hGen hGen5 h2

theorem input25_6A5NonAlt_of_rowsK
    (hB : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group → Claims1116c.SporDownRow .B 3)
    (hM : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group → Claims1116c.SporDownRow .M 3)
    (hGen : Inputs256b.InputGen2324c) (hGen5 : Inputs256b.InputGen2311Five)
    (h2 : Inputs256b.Input25_6A5Chev2) : Input25_6A5NonAltK :=
  input25_6A5NonAlt_of_residualsK (inputSporDownChev3_of_rowsK hB hM) hGen hGen5 h2

end Holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporK

end
