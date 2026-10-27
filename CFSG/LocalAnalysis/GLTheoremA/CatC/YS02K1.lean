module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSpor
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLie

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
  (fixSubgroup mem_fixSubgroup glaPComponent_map_fixSubgroup)
open CFSG.ComponentClassification.PerfectAutomorphisms
  (centerQuotientHom onCenterQuotient_apply_mk)

@[expose] def KDLevelK (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    CFSG.Open.IsKGroup S → DownLe p (kLevel p S) S

@[expose] def KDLevelTwoK (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    catalogIs S (k2 p) → CFSG.Open.IsKGroup S → DownLe p 2 S

@[expose] def KDLevelThreeK : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    catalogIs S (k3 3) → CFSG.Open.IsKGroup S → DownLe 3 3 S

@[expose] def KDLevelFiniteSporK (p : ℕ) : Prop :=
  ∀ s : TauCeti.SporadicName,
    CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic s).Group → KDSporRow s p

@[expose] def KDLevelFiniteK (p : ℕ) : Prop :=
  ∀ i : TauCeti.CFSGIndex, CFSG.Open.IsKGroup i.Group →
    (p = 3 → ∀ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), i = .lie d →
      d.1 ≠ .A 1 q ∧ d.1 ≠ .A 2 q ∧ d.1 ≠ .twistedA 2 q) →
    (∀ n h, i ≠ .alternating n h) →
    (k2 p i → DownLe p 2 i.Group) ∧ (k3 p i → DownLe p 3 i.Group)

theorem kdLevelFiniteK_of_parts {p : ℕ} (hL : KDLevelFiniteLie p) (hS : KDLevelFiniteSporK p) :
    KDLevelFiniteK p := by
  intro i hK hp3 halt
  cases i with
  | cyclic r hr => exact ⟨fun h => (show False from h).elim, fun h => (show False from h).elim⟩
  | alternating n hn => exact (halt n hn rfl).elim
  | lie d => exact hL d (fun h3 q => hp3 h3 d q rfl)
  | sporadic s => exact hS s hK

theorem isKGroup_carrier_of_sporadic
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (s : TauCeti.SporadicName)
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic s).Group) :
    CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier s) :=
  hK.of_surjective (hbr s).some.symm.toMonoidHom (hbr s).some.symm.surjective

section KCentral

variable {A B : Type} [Group A] [Group B] [Finite A] {p : ℕ}

private theorem i1412K_map_glaPPrimeCore_le (hp : p.Prime) (f : A →* B)
    (hf : Function.Surjective f) : (GLAPPrimeCore p A).map f ≤ GLAPPrimeCore p B := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite B := Finite.of_surjective f hf
  exact le_sSup ⟨Subgroup.Normal.map inferInstance f hf,
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ f) CFSG.pPrimeCore_coprime_card⟩

private noncomputable def i1412K_PQuotMap (hp : p.Prime) (π : A →* B) (J : Subgroup A) :
    PQuot p J →* PQuot p (J.map π) :=
  QuotientGroup.map _ _ (π.subgroupMap J) (by
    rw [← Subgroup.map_le_iff_le_comap]
    exact i1412K_map_glaPPrimeCore_le hp _ (π.subgroupMap_surjective J))

private theorem i1412K_PQuotMap_surjective (hp : p.Prime) (π : A →* B) (J : Subgroup A) :
    Function.Surjective (i1412K_PQuotMap hp π J) := by
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨x, rfl⟩ := π.subgroupMap_surjective J y
  exact ⟨QuotientGroup.mk x, rfl⟩

private noncomputable def i1412K_PSimpleMap (hp : p.Prime) (π : A →* B) (J : Subgroup A) :
    PSimple p J →* PSimple p (J.map π) :=
  QuotientGroup.map _ _ (i1412K_PQuotMap hp π J) (by
    rw [← Subgroup.map_le_iff_le_comap]
    exact Subgroup.map_center_le_center (i1412K_PQuotMap_surjective hp π J))

private theorem i1412K_PSimpleMap_surjective (hp : p.Prime) (π : A →* B) (J : Subgroup A) :
    Function.Surjective (i1412K_PSimpleMap hp π J) := by
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨x, rfl⟩ := i1412K_PQuotMap_surjective hp π J y
  exact ⟨QuotientGroup.mk x, rfl⟩

private theorem i1412K_nonempty_pSimple_equiv_map [Finite B] (hp : p.Prime) (π : A →* B)
    {X : Subgroup A} {Y : Subgroup B} {J : Subgroup A} (hJ : GLAPComponent p X J)
    (hJπ : GLAPComponent p Y (J.map π)) :
    Nonempty (PSimple p J ≃* PSimple p (J.map π)) := by
  haveI : IsSimpleGroup (PSimple p J) := (isQuasisimple_pQuot_of_glaPComponent hp hJ).2
  haveI : IsSimpleGroup (PSimple p (J.map π)) := (isQuasisimple_pQuot_of_glaPComponent hp hJπ).2
  have hinj : Function.Injective (i1412K_PSimpleMap hp π J) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (i1412K_PSimpleMap hp π J).ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_pair_ne (PSimple p (J.map π))
      obtain ⟨a', rfl⟩ := i1412K_PSimpleMap_surjective hp π J a
      obtain ⟨b', rfl⟩ := i1412K_PSimpleMap_surjective hp π J b
      apply hab
      have h1 : i1412K_PSimpleMap hp π J a' = 1 := by
        rw [← MonoidHom.mem_ker, h]
        trivial
      have h2 : i1412K_PSimpleMap hp π J b' = 1 := by
        rw [← MonoidHom.mem_ker, h]
        trivial
      rw [h1, h2]
  exact ⟨MulEquiv.ofBijective _ ⟨hinj, i1412K_PSimpleMap_surjective hp π J⟩⟩

private theorem i1412K_exists_conjAut {Q : Type} [Group Q] {K : Subgroup Q} {y : Q}
    (hyN : y ∈ Subgroup.normalizer (K : Set Q)) {n : ℕ} (hy : y ^ n = 1) :
    ∃ β : MulAut ↥K, β ^ n = 1 ∧
      fixSubgroup β = (K ⊓ Subgroup.centralizer ({y} : Set Q)).subgroupOf K := by
  obtain ⟨β, hβdef⟩ : ∃ β : MulAut ↥K, β = Subgroup.normalizerMonoidHom K ⟨y, hyN⟩ :=
    ⟨_, rfl⟩
  have hβapp : ∀ k : ↥K, ((β k : ↥K) : Q) = y * (k : Q) * y⁻¹ := by
    intro k
    rw [hβdef]
    rfl
  refine ⟨β, ?_, ?_⟩
  · have h3 : (⟨y, hyN⟩ : Subgroup.normalizer (K : Set Q)) ^ n = 1 := Subtype.ext hy
    rw [hβdef, ← map_pow, h3, map_one]
  · ext k
    rw [mem_fixSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hk
      have h1 : ((β k : ↥K) : Q) = (k : Q) := congrArg Subtype.val hk
      rw [hβapp] at h1
      exact ⟨k.2, (mul_inv_eq_iff_eq_mul.1 h1).symm⟩
    · rintro ⟨-, hk⟩
      apply Subtype.ext
      rw [hβapp]
      exact mul_inv_eq_iff_eq_mul.2 hk.symm

private theorem i1412K_kLevel_le {p : ℕ} (hp : p.Prime) (h : KDLevelK p) {Y : Type} [Group Y]
    [Finite Y] (hq : CFSG.Open.IsQuasisimple Y) (hK : CFSG.Open.IsKGroup (Y ⧸ Subgroup.center Y))
    {β : MulAut Y} (hβ : β ^ p = 1) {J : Subgroup Y} (hJ : GLAPComponent p (fixSubgroup β) J) :
    kLevel p (PSimple p J) ≤ kLevel p (Y ⧸ Subgroup.center Y) := by
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  set π := QuotientGroup.mk' (Subgroup.center Y) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center Y := (QuotientGroup.ker_mk' _).le
  have hαp : centerQuotientHom Y β ^ p = 1 := by
    rw [← map_pow, hβ, map_one]
  have hαβ : ∀ k, π (β k) = centerQuotientHom Y β (π k) := fun k =>
    (onCenterQuotient_apply_mk β k).symm
  have hJ' := glaPComponent_map_fixSubgroup π hker β (centerQuotientHom Y β) hαβ hπs hp hJ
  have hnonab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hq
  have hle := h (Y ⧸ Subgroup.center Y) ‹_› hnonab hK (centerQuotientHom Y β) hαp (J.map π) hJ'
  obtain ⟨f⟩ := i1412K_nonempty_pSimple_equiv_map hp π hJ hJ'
  rwa [← kLevel_congr p f] at hle

end KCentral

theorem i1412UsedAt_of_kdLevelK {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : KDLevelK p) : I1412UsedAt G p := by
  intro X K y hX hK hyp hyN J hJ
  have hy : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hyp
  obtain ⟨Q, _, _, K', y', ⟨eK⟩, hnorm, hpow, -, hcomp⟩ := exists_pQuot_transfer hp hy hyN
  obtain ⟨J', hJ', ⟨eJ⟩⟩ := hcomp J hJ
  have hq : CFSG.Open.IsQuasisimple (PQuot p K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  have hq' : CFSG.Open.IsQuasisimple ↥K' :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eK.symm hq
  have eS : (↥K' ⧸ Subgroup.center ↥K') ≃* PSimple p K :=
    QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)
  have hPQ : CFSG.Open.IsKGroup (PQuot p K) := (hX.of_le hK.1).quotient _
  have hKK : CFSG.Open.IsKGroup (PSimple p K) := hPQ.quotient _
  have hcat' : CFSG.Open.IsKGroup (↥K' ⧸ Subgroup.center ↥K') :=
    hKK.of_surjective eS.symm.toMonoidHom eS.symm.surjective
  obtain ⟨β, hβp, hβfix⟩ := i1412K_exists_conjAut hnorm (hpow p hyp)
  have hJ₁ : GLAPComponent p (fixSubgroup β) (J'.subgroupOf K') := by
    rw [hβfix]
    exact glaPComponent_subgroupOf hp inf_le_left hJ'
  have hle := i1412K_kLevel_le hp h hq' hcat' hβp hJ₁
  obtain ⟨f₁⟩ := nonempty_pQuot_equiv_subgroupOf p (hJ'.1.trans inf_le_left)
  have g : PQuot p (J'.subgroupOf K') ≃* PQuot p J := f₁.trans eJ.symm
  have fJ : PSimple p (J'.subgroupOf K') ≃* PSimple p J :=
    QuotientGroup.congr _ _ g (Subgroup.map_center_eq g)
  rwa [kLevel_congr p fJ, kLevel_congr p eS] at hle

end CFSG.LocalAnalysis.GLTheoremA
