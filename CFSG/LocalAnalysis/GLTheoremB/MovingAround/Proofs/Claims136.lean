module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma136b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma136c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12a2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop126
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input223
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma912

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims136

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut localDeltaIn)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns (mem_gLAPPrimeCoreOf_iff)
open scoped commutatorElement

theorem barX_pPrimePCore {G : Type} [Group G] (p : ℕ) (X : Subgroup G) :
    barX p X (pPrimePCore p X) = CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X) := by
  unfold barX pPrimePCore
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

theorem centralizerFStarFact_holds : Lemma136c.CentralizerFStarFact := by
  intro G _ _ X Y hYX hY2 _ hcomm hK
  have hp : Nat.Prime 3 := Nat.prime_three
  have hcore : GLAPPrimeCore 3 (↥X ⧸ GLAPPrimeCore 3 ↥X) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hS2 : IsPGroup 2 ↥(barX 3 X Y) := MovingAround.isPGroup_barX hY2
  have hScop : Nat.Coprime 3 (Nat.card ↥(barX 3 X Y)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hS2
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have h1 : barX 3 X Y ≤ Subgroup.centralizer
      (CFSG.Open.pCore 3 (↥X ⧸ GLAPPrimeCore 3 ↥X) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    have := barX_le_centralizer (p := 3) (C := X) (S := Y) (T := pPrimePCore 3 X)
      (fun s hs t ht _ _ => hcomm s hs t ht)
    rwa [barX_pPrimePCore] at this
  have h2 : ∀ K' : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), IsComponentOf K' ⊤ →
      barX 3 X Y ≤ Subgroup.centralizer (K' : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    intro K' hK'
    obtain ⟨K, hKc, rfl⟩ := exists_glaPComponent_barX_eq X hK'
    refine barX_le_centralizer fun s hs t ht _ _ => ?_
    have hmem : ⁅t, s⁆ ∈ ⁅K, Y⁆ := Subgroup.commutator_mem_commutator ht hs
    have := (GLAPPrimeCoreOf 3 X).inv_mem (hK K hKc hmem)
    simpa [commutatorElement_def, mul_assoc] using this
  have hbot := eq_bot_of_centralizes_pCore_components hp hcore hScop h1 h2
  intro y hy
  have hyX := hYX hy
  have hmk : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨y, hyX⟩ : ↥X) = 1 := by
    have : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨y, hyX⟩ : ↥X) ∈ barX 3 X Y :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hy)
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  exact (mem_gLAPPrimeCoreOf_iff 3 X y).2 ⟨hyX, (QuotientGroup.eq_one_iff _).1 hmk⟩

section Delta

variable {G : Type} [Group G] [Finite G]

theorem localDeltaTwoIn_le {X D : Subgroup G} {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) :
    localDeltaTwoIn X D ≤ X := by
  intro x hx
  unfold localDeltaTwoIn at hx
  have h := (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx d) hd) hd1)
  exact ((CFSG.LieType.BorelTits.pCoreOf_le 2 _) h).1

theorem commutator_le_of_barX_le_centralizer {p : ℕ} {X K S : Subgroup G} (hKX : K ≤ X)
    (hSX : S ≤ X)
    (h : barX p X S ≤ Subgroup.centralizer (barX p X K : Set (↥X ⧸ GLAPPrimeCore p ↥X))) :
    ⁅K, S⁆ ≤ GLAPPrimeCoreOf p X := by
  rw [Subgroup.commutator_le]
  intro k hk s hs
  have hkX := hKX hk
  have hsX := hSX hs
  have hsb : QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨s, hsX⟩ : ↥X) ∈ barX p X S :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hs)
  have hkb : QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨k, hkX⟩ : ↥X) ∈ barX p X K :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hk)
  have hc := Subgroup.mem_centralizer_iff.1 (h hsb) _ hkb
  have hmem : (⟨k, hkX⟩ : ↥X) * ⟨s, hsX⟩ * (⟨k, hkX⟩ : ↥X)⁻¹ * (⟨s, hsX⟩ : ↥X)⁻¹ ∈
      GLAPPrimeCore p ↥X := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (GLAPPrimeCore p ↥X)
      ((⟨k, hkX⟩ : ↥X) * ⟨s, hsX⟩ * (⟨k, hkX⟩ : ↥X)⁻¹ * (⟨s, hsX⟩ : ↥X)⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  have e : ⁅k, s⁆ = (((⟨k, hkX⟩ : ↥X) * ⟨s, hsX⟩ * (⟨k, hkX⟩ : ↥X)⁻¹ * (⟨s, hsX⟩ : ↥X)⁻¹ : ↥X) : G) := by
    simp [commutatorElement_def]
  rw [e]
  exact (mem_gLAPPrimeCoreOf_iff p X _).2 ⟨Subtype.prop _, hmem⟩

theorem centBar_le_inf (p : ℕ) (D K : Subgroup G) : centBar p D K ≤ D ⊓ centBar p ⊤ K := by
  intro x hx
  unfold centBar at hx ⊢
  exact ⟨hx.2, hx.1, Subgroup.mem_top x⟩

end Delta

theorem input19_1_O2_of_input19_1_two (hI : Lemma129.Input19_1_two) : Lemma136c.Input19_1_O2 := by
  intro G _ _ _ hKp p hp hp2 k hk X D hX hD
  obtain ⟨⟨h1, h2⟩, h3⟩ := hI G hKp p hp hp2 X hX k D hk hD
  have hDne : D ≠ ⊥ := by
    intro hD0
    have hc := hD.2.2
    rw [hD0, Subgroup.card_bot] at hc
    have : p ^ k ≠ 1 := (Nat.one_lt_pow (by omega) hp.one_lt).ne'
    exact this hc.symm
  obtain ⟨d, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  have hΔX : localDeltaTwoIn X D ≤ X :=
    localDeltaTwoIn_le (d := (d : G)) d.2 (fun h => hd1 (Subtype.ext h))
  have hΔeq : Lemma129.deltaTwo X D = localDeltaTwoIn X D := rfl
  rw [hΔeq] at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · intro K hK x hx
    have hxX := hΔX hx
    exact Lemma136.l136_mem_normalizer_of_bar hK ⟨x, hxX⟩
      (h1 K hK (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)))
  · intro x hx y hy
    have hxX := hΔX hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
    have hxb : QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨x, hxX⟩ : ↥X) ∈
        barX p X (localDeltaTwoIn X D) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
    have hc := Subgroup.mem_centralizer_iff.1 (h2 hxb) _ hy'
    have hmem : (⟨x, hxX⟩ : ↥X) * y' * (⟨x, hxX⟩ : ↥X)⁻¹ * y'⁻¹ ∈ GLAPPrimeCore p ↥X := by
      rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' (GLAPPrimeCore p ↥X)
        ((⟨x, hxX⟩ : ↥X) * y' * (⟨x, hxX⟩ : ↥X)⁻¹ * y'⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
      group
    exact (mem_gLAPPrimeCoreOf_iff p X _).2 ⟨_, hmem⟩
  · intro K hK hnot
    have hnc : ¬ barX p X (localDeltaTwoIn X D) ≤
        Subgroup.centralizer (barX p X K : Set (↥X ⧸ GLAPPrimeCore p ↥X)) :=
      fun hc => hnot (commutator_le_of_barX_le_centralizer hK.1 hΔX hc)
    obtain ⟨hDN, hDc, hnb, -⟩ := h3 K hK hnc
    exact ⟨hDN, eq_bot_iff.2 ((centBar_le_inf p D K).trans hDc.le), hnb⟩

@[expose] def Input19_16Three : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsKGroup K → CFSG.Open.IsQuasisimple K →
    GLAPPrimeCore 3 K = ⊥ → ∀ (k : ℕ), 2 ≤ k → ∀ B : Subgroup (MulAut K), IsEkIn 3 k ⊤ B →
      IsLocallyOTwoBalanced 3 k B ∨ Lemma136c.Alt19_16 3 k K B

theorem input19_16Three_of_input19_16 (hI : Lemma136c.Input19_16) : Input19_16Three :=
  fun K _ _ _ hq hO k hk B hB => hI K hq 3 Nat.prime_three (by norm_num) hO k hk B hB

theorem alt_of_component {G : Type} [Group G] [Finite G] (hI : Input19_16Three) {k : ℕ} (hk : 2 ≤ k)
    {X K B : Subgroup G} (hKG : CFSG.Open.IsKGroup (barOf 3 K)) (hK : GLAPComponent 3 X K)
    (hB : IsEkIn 3 k X B) (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hcent : centBar 3 B K = ⊥)
    (hnb : ¬ IsCompLocallyOTwoBalanced 3 k B K) :
    Lemma136c.Alt19_16 3 k (barOf 3 K) (autBar 3 B K) := by
  haveI : Finite (barOf 3 K) := by unfold barOf; infer_instance
  have hq : CFSG.Open.IsQuasisimple (barOf 3 K) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.isQuasisimple_quot_of_component Nat.prime_three hK
  have hO : GLAPPrimeCore 3 (barOf 3 K) = ⊥ := glaPPrimeCore_quotient_eq_bot Nat.prime_three
  rcases hI (barOf 3 K) hKG hq hO k hk (autBar 3 B K)
      (Lemma136c.l136c_isEkIn_autBar hB hBK hcent) with h | h
  · exact absurd h hnb
  · exact h

theorem iiHard_of_inputs' (hI191 : Lemma129.Input19_1_two) (hI1916 : Input19_16Three)
    (hRed : Lemma136c.IIHardReduction) (hCase : Lemma136c.IIHardCases) : Lemma136.IIHardInput := by
  have hF := centralizerFStarFact_holds
  have hI191' := input19_1_O2_of_input19_1_two hI191
  unfold Lemma136c.IIHardReduction at hRed
  unfold Lemma136c.IIHardCases at hCase
  unfold Lemma136c.CentralizerFStarFact at hF
  intro G _ _ m B M E A D T L h hN d hd hd1 hfix
  haveI : IsSimpleGroup G := h.standing.simple
  obtain ⟨b, B1, hPD, hsetup⟩ := hRed G m h hN hd hd1 hfix
  have hs := hsetup
  obtain ⟨-, ⟨r, hr, hEk⟩, hS1Δ, hS1P, hS1C, hred⟩ := hsetup
  have hX : Cg d ≠ ⊤ := Lemma136c.l136c_centralizer_ne_top h.standing.nonabelian hd1
  have hI := hI191' G h.standing.kProper 3 Nat.prime_three (by norm_num) r (by omega) (Cg d)
    (Lemma136c.bStarOf B L D b) hX hEk
  have hS1O : Lemma136c.s1Of B L D d b B1 ≤ GLAPPrimeCoreOf 3 (Cg d) := by
    by_contra hne
    obtain ⟨K, hK, hnot⟩ : ∃ K : Subgroup G, GLAPComponent 3 (Cg d) K ∧
        ¬ ⁅K, Lemma136c.s1Of B L D d b B1⁆ ≤ GLAPPrimeCoreOf 3 (Cg d) := by
      by_contra hall
      push Not at hall
      exact hne (hF G (Cg d) (Lemma136c.s1Of B L D d b B1) hS1C hS1P
        (fun K hK => hS1Δ.trans (hI.1 K hK))
        (fun y hy z hz => hI.2.1 y (hS1Δ hy) z hz) hall)
    have hnotΔ : ¬ ⁅K, localDeltaTwoIn (Cg d) (Lemma136c.bStarOf B L D b)⁆ ≤
        GLAPPrimeCoreOf 3 (Cg d) :=
      fun hle => hnot ((Subgroup.commutator_mono le_rfl hS1Δ).trans hle)
    obtain ⟨hBsN, hcent, hnb⟩ := hI.2.2 K hK hnotΔ
    have hKtop : K ≠ ⊤ := fun htop => hX (top_le_iff.1 (htop ▸ hK.1))
    have hKG : CFSG.Open.IsKGroup (barOf 3 K) :=
      (CFSG.Open.IsKProper.isKGroup h.standing.kProper K hKtop).quotient (GLAPPrimeCore 3 ↥K)
    have halt := alt_of_component hI1916 hr hKG hK hEk hBsN hcent hnb
    exact hCase G m h hN hd hd1 hfix b B1 hPD hs r hr hEk K hK hnot hBsN hcent halt
  exact hred.trans (sup_le hS1O le_rfl)

section P1GLift

variable {G : Type} [Group G] [Finite G]

theorem isSubnormal_sSup {X : Subgroup G} (S : Set (Subgroup G))
    (hS : ∀ K ∈ S, K ≤ X ∧ IsSubnormal K X) : IsSubnormal (sSup S) X := by
  have hle : sSup S ≤ X := sSup_le fun K hK => (hS K hK).1
  rw [CFSG.Open.IsSubnormal.iff_subgroupOf hle]
  set 𝒮 : Set (Subgroup ↥X) := (fun K : Subgroup G => K.subgroupOf X) '' S with h𝒮
  have h1 : ∀ A ∈ 𝒮, A.IsSubnormal := by
    rintro _ ⟨K, hK, rfl⟩
    exact (CFSG.Open.IsSubnormal.iff_subgroupOf (hS K hK).1).1 (hS K hK).2
  have h2 := (CFSG.GroupTheory.subnormal_subgroups_generated_join 𝒮 h1).1
  have h3 : (sSup S).subgroupOf X = Subgroup.closure (⋃ A ∈ 𝒮, (A : Set ↥X)) := by
    have hc : Subgroup.closure (⋃ A ∈ 𝒮, (A : Set ↥X)) = sSup 𝒮 := by
      refine le_antisymm ((Subgroup.closure_le _).2 (Set.iUnion₂_subset fun A hA => ?_)) ?_
      · exact (le_sSup hA : A ≤ sSup 𝒮)
      · exact sSup_le fun A hA x hx => Subgroup.subset_closure (Set.mem_biUnion hA hx)
    rw [hc]
    refine le_antisymm ?_ (sSup_le ?_)
    · have h4 : sSup S ≤ (sSup 𝒮).map X.subtype := by
        refine sSup_le fun K hK => ?_
        rw [← Subgroup.map_subgroupOf_eq_of_le (hS K hK).1]
        exact Subgroup.map_mono (le_sSup ⟨K, hK, rfl⟩)
      have := Subgroup.comap_mono (f := X.subtype) h4
      rwa [Subgroup.comap_map_eq_self_of_injective X.subtype_injective] at this
    · rintro _ ⟨K, hK, rfl⟩
      exact Subgroup.comap_mono (le_sSup hK)
  rwa [h3]

theorem centralizer_pair (b d : G) :
    Subgroup.centralizer ({b, d} : Set G) =
      Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

theorem glaPComponent_conj_of_mem {p : ℕ} {M L : Subgroup G} (hL : GLAPComponent p M L) {g : G}
    (hg : g ∈ M) : GLAPComponent p M (GLBConj g L) := by
  have := glaPComponent_gLBConj hL g
  rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)] at this

theorem exists_glaPComponent_lift {p : ℕ} (hp : p.Prime) {M H : Subgroup G} (hHM : H ≤ M)
    {K : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)} (hK : GLAPComponent p (barX p M H) K) :
    ∃ J : Subgroup G, GLAPComponent p H J ∧ barX p M J = K := by
  have : Fact p.Prime := ⟨hp⟩
  have hker : Nat.Coprime p (Nat.card ↥(H.subgroupOf M ⊓
      (QuotientGroup.mk' (GLAPPrimeCore p ↥M)).ker)) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      CFSG.pPrimeCore_coprime_card
  obtain ⟨J₀, hJ₀, hJ₀K⟩ := exists_glaPComponent_map_eq hp
    (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) hker hK
  have hker' : Nat.Coprime p (Nat.card ↥(H.subgroupOf M ⊓ M.subtype.ker)) := by
    rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  refine ⟨J₀.map M.subtype, ?_, ?_⟩
  · have h1 := glaPComponent_map hp M.subtype hker' hJ₀
    rwa [Subgroup.map_subgroupOf_eq_of_le hHM] at h1
  · show ((J₀.map M.subtype).subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) = K
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact hJ₀K

theorem isSimpleGroup_of_alt7 {Y : Type*} [Group Y] (e : Y ≃* alternatingGroup (Fin 7)) :
    IsSimpleGroup Y := by
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  exact e.isSimpleGroup

theorem card_of_alt7 {Y : Type*} [Group Y] (e : Y ≃* alternatingGroup (Fin 7)) :
    Nat.card Y = 2520 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem glaPPrimeCore_eq_bot_of_alt7 {Y : Type*} [Group Y] [Finite Y]
    (e : Y ≃* alternatingGroup (Fin 7)) : GLAPPrimeCore 3 Y = ⊥ := by
  haveI := isSimpleGroup_of_alt7 e
  refine (CFSG.pPrimeCore_eq_bot_iff).2 ?_
  intro K _ hcop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
  · exact h
  · exfalso
    rw [h, Subgroup.card_top, card_of_alt7 e] at hcop
    norm_num at hcop

theorem glaPComponent_self_of_alt7 {Q : Type*} [Group Q] [Finite Q] {Y : Subgroup Q}
    (e : ↥Y ≃* alternatingGroup (Fin 7)) : GLAPComponent 3 Y Y := by
  haveI := isSimpleGroup_of_alt7 e
  have hO : GLAPPrimeCore 3 ↥Y = ⊥ := glaPPrimeCore_eq_bot_of_alt7 e
  have htop : (Y.subgroupOf Y).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y)) = ⊤ := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have eQ : (↥Y ⧸ GLAPPrimeCore 3 ↥Y) ≃* alternatingGroup (Fin 7) :=
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans e
  refine ⟨le_rfl, IsSubnormal.refl Y, ?_, ?_⟩
  · rw [htop]
    exact ⟨le_rfl, IsSubnormal.refl _,
      Lemma912.alt7_isQuasisimple.of_mulEquiv (Subgroup.topEquiv.trans eQ)⟩
  · intro J hJ hJsn heq
    rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hJsn inferInstance with h0 | h0
    · subst h0
      rw [htop, Subgroup.bot_subgroupOf, Subgroup.map_bot] at heq
      haveI : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
      haveI : Nontrivial ↥(alternatingGroup (Fin 7)) := IsSimpleGroup.toNontrivial
      haveI : Nontrivial (↥Y ⧸ GLAPPrimeCore 3 ↥Y) := eQ.toEquiv.nontrivial
      exact bot_ne_top heq
    · exact hJ.ne h0

theorem glaPPrimeCoreOf_le_of_barX_alt7 {M H : Subgroup G} (hHM : H ≤ M)
    (e : ↥(barX 3 M H) ≃* alternatingGroup (Fin 7)) : GLAPPrimeCoreOf 3 H ≤ GLAPPrimeCoreOf 3 M := by
  haveI := isSimpleGroup_of_alt7 e
  have hNH : GLAPPrimeCoreOf 3 H ≤ H := Subgroup.map_subtype_le _
  have hNbar : barX 3 M (GLAPPrimeCoreOf 3 H) ≤ barX 3 M H := barX_mono_of_le 3 hNH
  have hnorm : barX 3 M H ≤ Subgroup.normalizer
      ((barX 3 M (GLAPPrimeCoreOf 3 H) : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) :=
    Lemma136.l136_bar_normalizes fun x hx q hq =>
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 H hx) q).1 hq
  have hn : ((barX 3 M (GLAPPrimeCoreOf 3 H)).subgroupOf (barX 3 M H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNbar).2 hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((barX 3 M (GLAPPrimeCoreOf 3 H)).subgroupOf (barX 3 M H)) with h0 | h0
  · intro x hx
    have hxM := hHM (hNH hx)
    have hmk : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨x, hxM⟩ : ↥M) ∈
        barX 3 M (GLAPPrimeCoreOf 3 H) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
    have hmk' : (⟨_, hNbar hmk⟩ : ↥(barX 3 M H)) ∈
        (barX 3 M (GLAPPrimeCoreOf 3 H)).subgroupOf (barX 3 M H) :=
      Subgroup.mem_subgroupOf.2 hmk
    rw [h0] at hmk'
    have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨x, hxM⟩ : ↥M) = 1 :=
      congrArg Subtype.val (Subgroup.mem_bot.1 hmk')
    exact (mem_gLAPPrimeCoreOf_iff 3 M x).2 ⟨hxM, (QuotientGroup.eq_one_iff _).1 h1⟩
  · exfalso
    have heq : barX 3 M H ≤ barX 3 M (GLAPPrimeCoreOf 3 H) := fun x hx => by
      have : (⟨x, hx⟩ : ↥(barX 3 M H)) ∈
          (barX 3 M (GLAPPrimeCoreOf 3 H)).subgroupOf (barX 3 M H) := by
        rw [h0]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 this
    have h2 : Nat.card ↥(barX 3 M (GLAPPrimeCoreOf 3 H)) ∣ Nat.card ↥(GLAPPrimeCoreOf 3 H) := by
      have := Subgroup.card_map_dvd ((GLAPPrimeCoreOf 3 H).subgroupOf M)
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M))
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hNH.trans hHM)).toEquiv] at this
    have h3 : 3 ∣ Nat.card ↥(barX 3 M H) := by rw [card_of_alt7 e]; norm_num
    have h4 : Nat.card ↥(barX 3 M H) ∣ Nat.card ↥(barX 3 M (GLAPPrimeCoreOf 3 H)) :=
      Subgroup.card_dvd_of_le heq
    exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three H (h3.trans (h4.trans h2))

theorem core_le_of_comp_inf {M L' C J : Subgroup G} (hL' : GLAPComponent 3 M L')
    (hO2 : GLAPPrimeCoreOf 3 L' ≤ pCoreOf 2 L')
    (e : ↥(barX 3 M (L' ⊓ C)) ≃* alternatingGroup (Fin 7)) (hJ : GLAPComponent 3 (L' ⊓ C) J) :
    GLAPPrimeCoreOf 3 J ≤ pCoreOf 2 J := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have h1 : GLAPPrimeCoreOf 3 J ≤ GLAPPrimeCoreOf 3 (L' ⊓ C) :=
    glaPPrimeCoreOf_le_of_isSubnormal hp hJ.2.1
  have h2 : GLAPPrimeCoreOf 3 (L' ⊓ C) ≤ GLAPPrimeCoreOf 3 M :=
    glaPPrimeCoreOf_le_of_barX_alt7 (inf_le_left.trans hL'.1) e
  have h3 : GLAPPrimeCoreOf 3 (L' ⊓ C) ≤ L' := (Subgroup.map_subtype_le _).trans inf_le_left
  have h4 : L' ⊓ GLAPPrimeCoreOf 3 M = GLAPPrimeCoreOf 3 L' :=
    glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hL'.2.1
  have h5 : GLAPPrimeCoreOf 3 J ≤ pCoreOf 2 L' := by
    exact h1.trans ((le_inf h3 h2).trans (h4.le.trans hO2))
  have h2g : IsPGroup 2 ↥(GLAPPrimeCoreOf 3 J) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L').to_le h5
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Subgroup.map_subtype_le _)
    (le_normalizer_glaPPrimeCoreOf 3 J) h2g

theorem twoPrimeComp_of_glaPComponent' {X Js : Subgroup G} (hJs : GLAPComponent 3 X Js)
    (hcore : GLAPPrimeCoreOf 3 Js ≤ pCoreOf 2 Js) :
    IsTwoPrimeComp X Js ∧ CFSG.pCore 2 ↥Js = GLAPPrimeCore 3 ↥Js := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp3 : Nat.Prime 3 := by norm_num
  have hJX : Js ≤ X := hJs.1
  have hsn : IsSubnormal Js X := hJs.2.1
  have hcoreEq : CFSG.pCore 2 ↥Js = GLAPPrimeCore 3 ↥Js := by
    apply le_antisymm
    · have hcop : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥Js)) := by
        obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1
          (CFSG.pCore_isPGroup (p := 2) (G := ↥Js))
        rw [hn]
        exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp3 Nat.prime_two).2 (by norm_num))
      unfold GLAPPrimeCore CFSG.pPrimeCore
      exact le_sSup ⟨inferInstance, hcop⟩
    · intro x hx
      have hxG : (x : G) ∈ GLAPPrimeCoreOf 3 Js := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hcore hxG)
      have : y = x := Subtype.ext hyx
      rwa [← this]
  let f : ↥Js →* ↥X ⧸ CFSG.pCore 2 ↥X :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.inclusion hJX)
  have hrange : f.range = (Js.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hJX x, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.1 hy⟩, rfl⟩
  have hker : f.ker = CFSG.pCore 2 ↥Js := by
    apply le_antisymm
    ·
      have hT2 : IsPGroup 2 ↥f.ker := by
        intro t
        have ht : Subgroup.inclusion hJX t.1 ∈ CFSG.pCore 2 ↥X := by
          rw [← QuotientGroup.eq_one_iff]
          exact t.2
        have hPX : IsPGroup 2 ↥(CFSG.pCore 2 ↥X) := CFSG.pCore_isPGroup (p := 2) (G := ↥X)
        obtain ⟨k, hk⟩ := hPX ⟨_, ht⟩
        have hk1 : (Subgroup.inclusion hJX t.1) ^ (2 ^ k) = 1 := by
          have := congrArg Subtype.val hk
          simpa using this
        have hk2 : t.1 ^ (2 ^ k) = 1 := by
          apply Subgroup.inclusion_injective hJX
          rw [map_pow, map_one]
          exact hk1
        exact ⟨k, Subtype.ext (by simpa using hk2)⟩
      exact le_sSup ⟨inferInstance, hT2⟩
    ·
      intro x hx
      have hsnN : IsSubnormal (pCoreOf 2 Js) X :=
        isSubnormal_trans' (Sec12a2.isSubnormal_of_normal
          (CFSG.LieType.BorelTits.pCoreOf_le 2 Js)
          ((Subgroup.normal_subgroupOf_iff_le_normalizer
            (CFSG.LieType.BorelTits.pCoreOf_le 2 Js)).2
              (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Js))) hsn
      have hle := Sec12a2.le_pCoreOf_of_isSubnormal hsnN
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Js)
      have hxG : (x : G) ∈ pCoreOf 2 Js := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hle hxG)
      have hyx' : y = Subgroup.inclusion hJX x := Subtype.ext hyx
      show f x = 1
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      rwa [← hyx']
  have hqs : CFSG.Open.IsQuasisimple (↥Js ⧸ CFSG.pCore 2 ↥Js) := by
    have h0 := l119_isQuasisimple_barOf (p := 3) hp3 hJs
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq hcoreEq.symm) h0
  have hq' : CFSG.Open.IsQuasisimple
      ↥((Js.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) := by
    let e1 : (↥Js ⧸ f.ker) ≃* ↥f.range := QuotientGroup.quotientKerEquivRange f
    let e2 : ↥f.range ≃*
        ↥((Js.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) :=
      MulEquiv.subgroupCongr hrange
    let e3 : ↥Js ⧸ CFSG.pCore 2 ↥Js ≃* ↥Js ⧸ f.ker :=
      QuotientGroup.quotientMulEquivOfEq hker.symm
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      ((e3.trans e1).trans e2) hqs
  have hsn' : IsSubnormal ((Js.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) ⊤ := by
    have h1 := (glaPComponent_top hJs).2.1
    have h2 := isSubnormal_map' (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) h1
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  exact ⟨⟨hJX, hsn, glaPComponent_perfect hJs, le_top, hsn', hq'⟩, hcoreEq⟩

theorem le_alphaStarOf {M L' : Subgroup G} (hL' : GLAPComponent 3 M L')
    (hO2 : GLAPPrimeCoreOf 3 L' ≤ pCoreOf 2 L')
    (e : ↥(barX 3 M L') ≃* alternatingGroup (Fin 7)) : L' ≤ alphaStarOf 3 M := by
  have heq := (twoPrimeComp_of_glaPComponent' hL' hO2).2
  have hA7 : Nonempty ((↥L' ⧸ CFSG.pCore 2 ↥L') ≃* alternatingGroup (Fin 7)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans
      ((quotEquivBarX Nat.prime_three hL'.1 hL'.2.1).trans e)⟩
  exact le_sup_of_le_right
    (le_iSup₂_of_le L' ⟨rfl, hL'.1, hL'.2.1, glaPComponent_perfect hL', hA7⟩ le_rfl)

theorem isSubnormal_of_comp_inf_centralizer (h912 : Lemma912Statement) {m : ℕ}
    {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L) {b : G} (hbB : b ∈ B)
    (hb1 : b ≠ 1) {L' : Subgroup G} (hL' : GLAPComponent 3 M L')
    (hO2 : GLAPPrimeCoreOf 3 L' ≤ pCoreOf 2 L')
    (e : ↥(barX 3 M L') ≃* alternatingGroup (Fin 7))
    (hbar : barX 3 M (L' ⊓ Cg b) = barX 3 M L') {J : Subgroup G}
    (hJ : GLAPComponent 3 (L' ⊓ Cg b) J) : J ≤ Cg b ∧ IsSubnormal J (Cg b) := by
  have e' : ↥(barX 3 M (L' ⊓ Cg b)) ≃* alternatingGroup (Fin 7) :=
    (MulEquiv.subgroupCongr hbar).trans e
  have hcoreJ := core_le_of_comp_inf hL' hO2 e' hJ
  have hTP1 : IsTwoPrimeComp (L' ⊓ Cg b) J := (twoPrimeComp_of_glaPComponent' hJ hcoreJ).1
  have hL'α : L' ≤ alphaStarOf 3 M := le_alphaStarOf hL' hO2 e
  have hαM : alphaStarOf 3 M ≤ M := Lemma912.alphaStarOf_le 3 M
  have hL'αsn : IsSubnormal L' (alphaStarOf 3 M) := isSubnormal_of_le_of_le hL'.2.1 hL'α hαM
  have hsn : IsSubnormal (L' ⊓ Cg b) (alphaStarOf 3 M ⊓ Cg b) := isSubnormal_inf hL'αsn (Cg b)
  have hJsn : IsSubnormal J (alphaStarOf 3 M ⊓ Cg b) := isSubnormal_trans' hJ.2.1 hsn
  have hTP2 : IsTwoPrimeComp (alphaStarOf 3 M ⊓ Cg b) J :=
    isTwoPrimeComp_of_le hTP1 (inf_le_inf_right _ hL'α) hJsn
  have hTP3 := h912 G m 3 h.standing B M h.bOne h.pre rfl b hbB hb1 J hTP2
  exact ⟨hTP3.1, hTP3.2.1⟩

theorem glaPLayer_conj (g : G) (X : Subgroup G) :
    GLAPLayer 3 (GLBConj g X) = GLBConj g (GLAPLayer 3 X) := by
  refine gLBConj_eq_of_forall_ge (F := GLAPLayer 3) (fun g H => ?_) g X
  unfold GLAPLayer
  refine (Subgroup.map_le_iff_le_comap).2 (sSup_le fun J hJ => ?_)
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (glaPComponent_gLBConj hJ g)

theorem gLBConj_inf (g : G) (X Y : Subgroup G) :
    GLBConj g (X ⊓ Y) = GLBConj g X ⊓ GLBConj g Y := by
  ext z
  simp only [mem_gLBConj, Subgroup.mem_inf]

theorem gLBConj_iSup₂ (y : G) (D : Subgroup G) (F : G → Subgroup G) :
    GLBConj y (⨆ g ∈ D, F g) = ⨆ g ∈ D, GLBConj y (F g) := by
  unfold GLBConj
  rw [Subgroup.map_iSup]
  congr 1
  ext1 g
  rw [Subgroup.map_iSup]

theorem p1GLift_of_inputs (h912 : Lemma912Statement) (hO2 : Cex134_O2Statement)
    (hP95 : Prop95) (h111 : Prop111Statement) (h121 : Prop121_of_cexStatement)
    (hcomp : Sec13_compStatement) : Lemma136b.P1GLift := by
  intro G _ _ m B M E A D T L h b hbB hb1 hbc d hdD _ _ K hK
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hLc, -⟩ := hcomp h.toSec13 h.hL
  have hLM : L ≤ M := hLc.1
  have hDA : D ≤ A := h.hD.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hDM : D ≤ M := hDA.trans hAM
  obtain ⟨-, e, -⟩ := Lemma136.l136_gamma hP95 h111 h121 hcomp h
  have hOL : GLAPPrimeCoreOf 3 L ≤ pCoreOf 2 L := hO2 h rfl
  have hb1' : (b : G) ≠ 1 := fun h1 => hb1 (by rw [show b = 1 from Subtype.ext h1, map_one])
  have hbP : (b : G) ∈ A ⊔ B := Subgroup.mem_sup_right hbB
  have hdP : (d : G) ∈ A ⊔ B := Subgroup.mem_sup_left (hDA hdD)
  have hb3 : IsPGroup 3 ↥(Subgroup.zpowers (b : G)) := h.hAB.to_le ((Subgroup.zpowers_le).2 hbP)
  have hd3 : IsPGroup 3 ↥(Subgroup.zpowers (d : G)) := h.hAB.to_le ((Subgroup.zpowers_le).2 hdP)
  have hdbar : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) d ∈ barX 3 M D :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hdD)
  have hbd : (b : G) * d = d * b :=
    Lemma136b.commute_of_bar b.2 d.2 h.hAB hbP hdP (hbc _ (Subgroup.mem_sup_left hdbar))
  have hcompg : ∀ g ∈ D, GLAPComponent 3 M (GLBConj g L) := fun g hg =>
    glaPComponent_conj_of_mem hLc (hDM hg)
  have hOg : ∀ g ∈ D, GLAPPrimeCoreOf 3 (GLBConj g L) ≤ pCoreOf 2 (GLBConj g L) := fun g _ => by
    rw [glaPPrimeCoreOf_gLBConj, pCoreOf_gLBConj]
    exact gLBConj_mono g hOL
  have heg : ∀ g ∈ D, Nonempty (↥(barX 3 M (GLBConj g L)) ≃* alternatingGroup (Fin 7)) :=
    fun g hg => ⟨(MulEquiv.subgroupCongr (l119_barX_gLBConj (hDM hg) hLM)).trans
      ((conjEquiv _ (barX 3 M L)).symm.trans e)⟩
  have hLgL : ∀ g ∈ D, GLBConj g L ≤ Lstarsub D L := fun g hg =>
    le_iSup₂_of_le (f := fun d' (_ : d' ∈ D) => GLBConj d' L) g hg le_rfl
  have hLsM : Lstarsub D L ≤ M := iSup₂_le fun g hg => (hcompg g hg).1
  have hbcg : ∀ g ∈ D, ∀ y ∈ barX 3 M (GLBConj g L),
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) b * y = y * QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) b :=
    fun g hg y hy => hbc y (Subgroup.mem_sup_right (barX_mono_of_le 3 (hLgL g hg) hy))
  have hbN : ∀ g ∈ D, (b : G) ∈ Subgroup.normalizer ((GLBConj g L : Subgroup G) : Set G) :=
    fun g hg => Lemma136.l136_mem_normalizer_of_bar (hcompg g hg) b
      (Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.2 fun y hy => (hbcg g hg y hy).symm))
  have hbarg : ∀ g ∈ D, barX 3 M (GLBConj g L ⊓ Cg (b : G)) = barX 3 M (GLBConj g L) := by
    intro g hg
    rw [barX_inf_centralizer hp b.2 (hcompg g hg).1 (hbN g hg) hb3]
    exact inf_eq_left.2 fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hbcg g hg y hy).symm
  have hPsn : ∀ g ∈ D, GLAPLayer 3 (GLBConj g L ⊓ Cg (b : G)) ≤ Cg (b : G) ∧
      IsSubnormal (GLAPLayer 3 (GLBConj g L ⊓ Cg (b : G))) (Cg (b : G)) := by
    intro g hg
    obtain ⟨eg⟩ := heg g hg
    have hsub : ∀ J ∈ {J : Subgroup G | GLAPComponent 3 (GLBConj g L ⊓ Cg (b : G)) J},
        J ≤ Cg (b : G) ∧ IsSubnormal J (Cg (b : G)) := fun J hJ =>
      isSubnormal_of_comp_inf_centralizer h912 h hbB hb1' (hcompg g hg) (hOg g hg) eg
        (hbarg g hg) hJ
    unfold GLAPLayer
    exact ⟨sSup_le fun J hJ => (hsub J hJ).1, isSubnormal_sSup _ hsub⟩
  have hPle : ∀ g ∈ D, GLAPLayer 3 (GLBConj g L ⊓ Cg (b : G)) ≤ GLBConj g L ⊓ Cg (b : G) := by
    intro g _
    unfold GLAPLayer
    exact sSup_le fun J hJ => hJ.1
  set L0 : Subgroup G := ⨆ g ∈ D, GLAPLayer 3 (GLBConj g L ⊓ Cg (b : G)) with hL0
  have hL0sn : IsSubnormal L0 (Cg (b : G)) := by
    have hL0eq : L0 = sSup ((fun g => GLAPLayer 3 (GLBConj g L ⊓ Cg (b : G))) '' (D : Set G)) := by
      rw [sSup_image]
      rfl
    rw [hL0eq]
    refine isSubnormal_sSup _ ?_
    rintro _ ⟨g, hg, rfl⟩
    exact hPsn g hg
  have hL0L : L0 ≤ Lstarsub D L :=
    iSup₂_le fun g hg => (hPle g hg).trans (inf_le_left.trans (hLgL g hg))
  have hL0M : L0 ≤ M := hL0L.trans hLsM
  have hbarP : ∀ g ∈ D, barX 3 M (GLBConj g L) ≤
      barX 3 M (GLAPLayer 3 (GLBConj g L ⊓ Cg (b : G))) := by
    intro g hg
    obtain ⟨eg⟩ := heg g hg
    have hself := glaPComponent_self_of_alt7 ((MulEquiv.subgroupCongr (hbarg g hg)).trans eg)
    obtain ⟨J, hJ, hJK⟩ := exists_glaPComponent_lift hp (inf_le_left.trans (hcompg g hg).1) hself
    rw [← hbarg g hg, ← hJK]
    refine barX_mono_of_le 3 ?_
    unfold GLAPLayer
    exact le_sSup hJ
  have hbarL0 : barX 3 M L0 = barX 3 M (Lstarsub D L) := by
    refine le_antisymm (barX_mono_of_le 3 hL0L) ?_
    rw [Lemma136.l136_lstar_eq_iSup]
    refine (barX_iSup_le_iSup (fun g : ↥D => GLBConj (g : G) L) fun g => (hcompg g g.2).1).trans
      (iSup_le fun g => (hbarP g g.2).trans (barX_mono_of_le 3 ?_))
    exact le_iSup₂_of_le (f := fun g' (_ : g' ∈ D) => GLAPLayer 3 (GLBConj g' L ⊓ Cg (b : G)))
      (g : G) g.2 le_rfl
  have hdC : (d : G) ∈ Cg (b : G) := Subgroup.mem_centralizer_singleton_iff.2 hbd.symm
  have hconj : ∀ y ∈ D, y ∈ Cg (b : G) → GLBConj y L0 ≤ L0 := by
    intro y hyD hyC
    rw [hL0, gLBConj_iSup₂]
    refine iSup₂_le fun g hg => ?_
    rw [← glaPLayer_conj, gLBConj_inf, gLBConj_gLBConj,
      gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hyC)]
    exact le_iSup₂_of_le (f := fun g' (_ : g' ∈ D) => GLAPLayer 3 (GLBConj g' L ⊓ Cg (b : G)))
      (g * y) (D.mul_mem hg hyD) le_rfl
  have hdN : (d : G) ∈ Subgroup.normalizer (L0 : Set G) :=
    Lemma135.mem_normalizer_of_gLBConj_le (hconj _ hdD hdC)
      (hconj _ (D.inv_mem hdD) ((Cg (b : G)).inv_mem hdC))
  have hbar0 : barX 3 M (L0 ⊓ Cg (d : G)) = barX 3 M (Lstarsub D L) ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) d} : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
    rw [barX_inf_centralizer hp d.2 hL0M hdN hd3, hbarL0]
  rw [← hbar0] at hK
  obtain ⟨J, hJ, hJK⟩ := exists_glaPComponent_lift hp (inf_le_left.trans hL0M) hK
  refine ⟨J, (hJ.1.trans inf_le_left).trans hL0L, ?_, hJK⟩
  rw [centralizer_pair]
  exact Prop126.glaPComponent_up hp hJ (isSubnormal_inf hL0sn (Cg (d : G)))

end P1GLift

section S7Klein

open Equiv Equiv.Perm
open CFSG.LocalAnalysis.GLTheoremB.S7 (S Alt7 a x y V permOfAut permOfAut_spec permOfAut_injective
  x_mem y_mem x_mem_V y_mem_V V_le_Alt7 V_le_centralizer isPGroup_V mem_normalizer_V_of_comm
  conj_x_of_comm_a conj_y_of_comm_a)

@[expose] def a33 : S := c[0, 1, 2] * c[3, 4, 5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem s7_two_elem_comm_a : ∀ c : S, c * a = a * c → Equiv.Perm.sign c = 1 → c ^ 16 = 1 →
    c = 1 ∨ c = x ∨ c = y ∨ c = x * y := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem s7_two_elem_comm_a33 : ∀ c : S, c * a33 = a33 * c → Equiv.Perm.sign c = 1 → c ^ 16 = 1 →
    c = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem s7_comm_V : ∀ c : S, c * a = a * c → c ^ 3 = 1 → c ≠ 1 → c ≠ a → c ≠ a * a →
    (x = c * x * c⁻¹ * x⁻¹ ∨ x = c * y * c⁻¹ * y⁻¹ ∨
        x = (c * x * c⁻¹ * x⁻¹) * (c * y * c⁻¹ * y⁻¹)) ∧
      (y = c * x * c⁻¹ * x⁻¹ ∨ y = c * y * c⁻¹ * y⁻¹ ∨
        y = (c * x * c⁻¹ * x⁻¹) * (c * y * c⁻¹ * y⁻¹)) := by
  decide +kernel

theorem permOfAut_conj {X : Type*} [Group X] (e : X ≃* ↥Alt7) (τ : S) (φ : MulAut X) :
    permOfAut (e.trans (CFSG.LocalAnalysis.GLTheoremB.S7.conjEquiv τ)) φ =
      τ * permOfAut e φ * τ⁻¹ := by
  apply CFSG.LocalAnalysis.GLTheoremB.S7.conjEquiv.injective
  have h1 : CFSG.LocalAnalysis.GLTheoremB.S7.conjEquiv (permOfAut e φ) = MulAut.congr e φ := by
    simp [permOfAut]
  have h2 : CFSG.LocalAnalysis.GLTheoremB.S7.conjEquiv
      (permOfAut (e.trans (CFSG.LocalAnalysis.GLTheoremB.S7.conjEquiv τ)) φ) =
      MulAut.congr (e.trans (CFSG.LocalAnalysis.GLTheoremB.S7.conjEquiv τ)) φ := by
    simp [permOfAut]
  rw [h2, map_mul, map_mul, map_inv, h1]
  ext z
  simp [MulAut.congr_apply]

theorem permOfAut_conj_self {X : Type*} [Group X] (e : X ≃* ↥Alt7) (k : X) :
    permOfAut e (MulAut.conj k) = (e k : S) := by
  apply CFSG.LocalAnalysis.GLTheoremB.S7.conjEquiv.injective
  have h1 : CFSG.LocalAnalysis.GLTheoremB.S7.conjEquiv (permOfAut e (MulAut.conj k)) =
      MulAut.congr e (MulAut.conj k) := by simp [permOfAut]
  rw [h1]
  ext z
  simp [CFSG.LocalAnalysis.GLTheoremB.S7.conjEquiv, MulAut.congr_apply, MulAut.conjNormal_apply]

theorem cycleType_a : a.cycleType = Multiset.replicate 1 3 := by
  have h : a = swap (0 : Fin 7) 2 * swap 0 1 := by decide
  have h3 : a.IsThreeCycle := by
    rw [h]
    exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  exact h3

theorem cycleType_a33 : a33.cycleType = Multiset.replicate 2 3 := by
  have hd : Equiv.Perm.Disjoint (c[0, 1, 2] : S) c[3, 4, 5] := by
    unfold Equiv.Perm.Disjoint
    decide
  have h1 : (c[0, 1, 2] : S).IsThreeCycle := by
    have h : (c[0, 1, 2] : S) = swap (0 : Fin 7) 2 * swap 0 1 := by decide
    rw [h]
    exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  have h2 : (c[3, 4, 5] : S).IsThreeCycle := by
    have h : (c[3, 4, 5] : S) = swap (3 : Fin 7) 5 * swap 3 4 := by decide
    rw [h]
    exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  unfold a33
  rw [Equiv.Perm.Disjoint.cycleType_mul hd, h1, h2]
  rfl

theorem exists_conj_a_or_a33 {π : S} (h3 : π ^ 3 = 1) (h1 : π ≠ 1) :
    ∃ τ : S, τ * π * τ⁻¹ = a ∨ τ * π * τ⁻¹ = a33 := by
  have hdvd : orderOf π ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hall : ∀ c ∈ π.cycleType, c = 3 := by
    intro c hc
    have h1' : c ∣ orderOf π := by
      rw [← Equiv.Perm.lcm_cycleType]
      exact Multiset.dvd_lcm hc
    have h2 : c ∣ 3 := h1'.trans hdvd
    have h3' : 2 ≤ c := Equiv.Perm.two_le_of_mem_cycleType hc
    have : c ≤ 3 := Nat.le_of_dvd (by norm_num) h2
    interval_cases c
    · exact absurd h2 (by norm_num)
    · rfl
  have hne : π.cycleType ≠ 0 := fun h => h1 (Equiv.Perm.cycleType_eq_zero.1 h)
  have hsum : π.cycleType.sum ≤ 7 := by
    rw [Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  have hrep : π.cycleType = Multiset.replicate (Multiset.card π.cycleType) 3 :=
    Multiset.eq_replicate.2 ⟨rfl, hall⟩
  set k := Multiset.card π.cycleType with hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact absurd (Multiset.card_eq_zero.1 h) hne
    · exact h
  have hk2 : k ≤ 2 := by
    rw [hrep, Multiset.sum_replicate] at hsum
    simp at hsum
    omega
  interval_cases k
  · have hc : IsConj π a := (Equiv.Perm.isConj_iff_cycleType_eq).2 (by rw [hrep, cycleType_a])
    obtain ⟨τ, hτ⟩ := isConj_iff.1 hc
    exact ⟨τ, Or.inl hτ⟩
  · have hc : IsConj π a33 :=
      (Equiv.Perm.isConj_iff_cycleType_eq).2 (by rw [hrep, cycleType_a33])
    obtain ⟨τ, hτ⟩ := isConj_iff.1 hc
    exact ⟨τ, Or.inr hτ⟩

theorem pow_sixteen_of_two_power {g : S} {n : ℕ} (h : g ^ (2 ^ n) = 1) : g ^ 16 = 1 := by
  have h1 : orderOf g ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have h2 : orderOf g ∣ 5040 := by
    have := orderOf_dvd_natCard g
    rwa [CFSG.LocalAnalysis.GLTheoremB.S7.card_S] at this
  rw [hj] at h2
  have hj4 : j ≤ 4 := by
    by_contra hcon
    have : 2 ^ 5 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    have := this.trans h2
    norm_num at this
  apply orderOf_dvd_iff_pow_eq_one.1
  rw [hj]
  exact (pow_dvd_pow 2 hj4).trans (by norm_num)

theorem exists_klein {X : Type} [Group X] [Finite X] (e : X ≃* ↥Alt7) (σ : MulAut X)
    (hσ3 : σ ^ 3 = 1) (hO : pCoreOf 2 (fixSub σ) ≠ ⊥) :
    σ ≠ 1 ∧ ∃ W : Subgroup X, W ≤ fixSub σ ∧ IsPGroup 2 ↥W ∧
      (∀ k ∈ fixSub σ, k ∈ Subgroup.normalizer (W : Set X)) ∧
      (∀ k ∈ fixSub σ, ∀ n : ℕ, k ^ (2 ^ n) = 1 → k ∈ W) ∧
      (∀ c ∈ fixSub σ, c ^ 3 = 1 → MulAut.conj c ∉ Subgroup.zpowers σ →
        W ≤ ⁅Subgroup.zpowers c, W⁆) := by
  obtain ⟨k0, hk0, hk01⟩ : ∃ k ∈ pCoreOf 2 (fixSub σ), k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hO (eq_bot_iff.2 fun k hk => Subgroup.mem_bot.2 (hcon k hk))
  have hk0fix : k0 ∈ fixSub σ := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hk0
  obtain ⟨n0, hn0⟩ : ∃ n : ℕ, k0 ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (fixSub σ) ⟨k0, hk0⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hπ3 : permOfAut e σ ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
  by_cases hπ1 : permOfAut e σ = 1
  · exfalso
    have hσ1 : σ = 1 := permOfAut_injective e (by rw [hπ1, map_one])
    have hfix : fixSub σ = ⊤ := by
      rw [hσ1]
      ext k
      simp [mem_fixSub]
    haveI := isSimpleGroup_of_alt7 e
    haveI hN : (pCoreOf 2 (fixSub σ)).Normal := by
      constructor
      intro n hn g
      have hg : g ∈ fixSub σ := by rw [hfix]; exact Subgroup.mem_top g
      exact (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hg) n).1 hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCoreOf 2 (fixSub σ)) with h0 | h0
    · exact hO h0
    · have h2 : IsPGroup 2 ↥(⊤ : Subgroup X) := h0 ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
      obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 h2
      rw [Subgroup.card_top, card_of_alt7 e] at hj
      have h3 : (3 : ℕ) ∣ 2 ^ j := hj ▸ (by norm_num : (3 : ℕ) ∣ 2520)
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  obtain ⟨τ, hτ | hτ⟩ := exists_conj_a_or_a33 hπ3 hπ1
  · set e' : X ≃* ↥Alt7 := e.trans (CFSG.LocalAnalysis.GLTheoremB.S7.conjEquiv τ) with he'
    have hπ' : permOfAut e' σ = a := by rw [he', permOfAut_conj, hτ]
    have hcomm : ∀ k ∈ fixSub σ, (e' k : S) * a = a * (e' k : S) := by
      intro k hk
      have h1 := permOfAut_spec e' σ k
      rw [mem_fixSub.1 hk, hπ'] at h1
      calc (e' k : S) * a = (a * (e' k : S) * a⁻¹) * a := by rw [← h1]
        _ = a * (e' k : S) := by group
    have hmemW : ∀ v : X, v ∈ (V.subgroupOf Alt7).map e'.symm.toMonoidHom ↔
        ((e' v : ↥Alt7) : S) ∈ V := by
      intro v
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf]
    have hcoe : ∀ u v : X, ((e' (u * v) : ↥Alt7) : S) = (e' u : S) * (e' v : S) := by
      intro u v
      rw [map_mul, Subgroup.coe_mul]
    have hcoei : ∀ u : X, ((e' u⁻¹ : ↥Alt7) : S) = (e' u : S)⁻¹ := by
      intro u
      rw [map_inv, Subgroup.coe_inv]
    refine ⟨fun h1 => absurd (by rw [← hπ', h1, map_one]) (show a ≠ 1 by decide),
      (V.subgroupOf Alt7).map e'.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      have hwV : (w : S) ∈ V := Subgroup.mem_subgroupOf.1 hw
      have hwa : (w : S) * a = a * (w : S) :=
        Subgroup.mem_centralizer_singleton_iff.1 (V_le_centralizer hwV)
      show σ (e'.symm w) = e'.symm w
      have h1 := permOfAut_spec e' σ (e'.symm w)
      rw [hπ', MulEquiv.apply_symm_apply] at h1
      have h2 : e' (σ (e'.symm w)) = w := by
        apply Subtype.ext
        rw [h1]
        calc a * (w : S) * a⁻¹ = ((w : S) * a) * a⁻¹ := by rw [hwa]
          _ = (w : S) := by group
      calc σ (e'.symm w) = e'.symm (e' (σ (e'.symm w))) := (e'.symm_apply_apply _).symm
        _ = e'.symm w := by rw [h2]
    · exact (isPGroup_V.of_equiv (Subgroup.subgroupOfEquivOfLe V_le_Alt7).symm).map _
    · intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro v
      rw [hmemW, hmemW, hcoe, hcoe, hcoei]
      exact Subgroup.mem_normalizer_iff.1 (mem_normalizer_V_of_comm (hcomm k hk)) _
    · intro k hk n hn
      rw [hmemW]
      have hsign : Equiv.Perm.sign (e' k : S) = 1 := Equiv.Perm.mem_alternatingGroup.1 (e' k).2
      have hpow : (e' k : S) ^ (2 ^ n) = 1 := by
        rw [← Subgroup.coe_pow, ← map_pow, hn, map_one, Subgroup.coe_one]
      rcases s7_two_elem_comm_a _ (hcomm k hk) hsign (pow_sixteen_of_two_power hpow) with
        h | h | h | h <;> rw [h]
      · exact V.one_mem
      · exact x_mem_V
      · exact y_mem_V
      · exact V.mul_mem x_mem_V y_mem_V
    · intro c hc hc3 hcσ
      have hπc : permOfAut e' (MulAut.conj c) = (e' c : S) := permOfAut_conj_self e' c
      have hpc3 : (e' c : S) ^ 3 = 1 := by
        rw [← Subgroup.coe_pow, ← map_pow, hc3, map_one, Subgroup.coe_one]
      have hne : ∀ j : ℕ, (e' c : S) ≠ a ^ j := by
        intro j hj
        apply hcσ
        have : MulAut.conj c = σ ^ j := permOfAut_injective e' (by rw [hπc, map_pow, hπ', hj])
        rw [this]
        exact Subgroup.npow_mem_zpowers σ j
      have h1 : (e' c : S) ≠ 1 := by simpa using hne 0
      have h2 : (e' c : S) ≠ a := by simpa using hne 1
      have h3 : (e' c : S) ≠ a * a := by simpa [pow_two] using hne 2
      obtain ⟨hxx, hyy⟩ := s7_comm_V _ (hcomm c hc) hpc3 h1 h2 h3
      set W := (V.subgroupOf Alt7).map e'.symm.toMonoidHom with hW
      set C := ⁅Subgroup.zpowers c, W⁆ with hC
      set x' : X := e'.symm ⟨x, x_mem⟩ with hx'
      set y' : X := e'.symm ⟨y, y_mem⟩ with hy'
      have hex : (e' x' : S) = x := by rw [hx', MulEquiv.apply_symm_apply]
      have hey : (e' y' : S) = y := by rw [hy', MulEquiv.apply_symm_apply]
      have hx'W : x' ∈ W := (hmemW x').2 (hex ▸ x_mem_V)
      have hy'W : y' ∈ W := (hmemW y').2 (hey ▸ y_mem_V)
      have hu : c * x' * c⁻¹ * x'⁻¹ ∈ C := by
        have := Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers c) hx'W
        rwa [commutatorElement_def] at this
      have hw : c * y' * c⁻¹ * y'⁻¹ ∈ C := by
        have := Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers c) hy'W
        rwa [commutatorElement_def] at this
      have hinj : ∀ u v : X, (e' u : S) = (e' v : S) → u = v := fun u v h =>
        e'.injective (Subtype.ext h)
      have hxC : x' ∈ C := by
        rcases hxx with h | h | h
        · have : x' = c * x' * c⁻¹ * x'⁻¹ := hinj _ _ (by
            rw [hcoe, hcoe, hcoe, hcoei, hcoei, hex]; exact h)
          rw [this]; exact hu
        · have : x' = c * y' * c⁻¹ * y'⁻¹ := hinj _ _ (by
            rw [hcoe, hcoe, hcoe, hcoei, hcoei, hex, hey]; exact h)
          rw [this]; exact hw
        · have : x' = (c * x' * c⁻¹ * x'⁻¹) * (c * y' * c⁻¹ * y'⁻¹) := hinj _ _ (by
            rw [hcoe, hcoe, hcoe, hcoe, hcoei, hcoei, hcoe, hcoe, hcoe, hcoei, hcoei, hex, hey]
            exact h)
          rw [this]; exact C.mul_mem hu hw
      have hyC : y' ∈ C := by
        rcases hyy with h | h | h
        · have : y' = c * x' * c⁻¹ * x'⁻¹ := hinj _ _ (by
            rw [hcoe, hcoe, hcoe, hcoei, hcoei, hex, hey]; exact h)
          rw [this]; exact hu
        · have : y' = c * y' * c⁻¹ * y'⁻¹ := hinj _ _ (by
            rw [hcoe, hcoe, hcoe, hcoei, hcoei, hey]; exact h)
          rw [this]; exact hw
        · have : y' = (c * x' * c⁻¹ * x'⁻¹) * (c * y' * c⁻¹ * y'⁻¹) := hinj _ _ (by
            rw [hcoe, hcoe, hcoe, hcoe, hcoei, hcoei, hcoe, hcoe, hcoe, hcoei, hcoei, hex, hey]
            exact h)
          rw [this]; exact C.mul_mem hu hw
      have hVC : V ≤ (C.map e'.toMonoidHom).map Alt7.subtype := by
        refine sup_le ((Subgroup.zpowers_le).2 ?_) ((Subgroup.zpowers_le).2 ?_)
        · exact ⟨⟨x, x_mem⟩, ⟨x', hxC, MulEquiv.apply_symm_apply e' _⟩, rfl⟩
        · exact ⟨⟨y, y_mem⟩, ⟨y', hyC, MulEquiv.apply_symm_apply e' _⟩, rfl⟩
      intro v hv
      obtain ⟨z, ⟨u, hu', hzu⟩, hz⟩ := hVC ((hmemW v).1 hv)
      have : u = v := hinj _ _ (by
        have h1 : (e' u : S) = (z : S) := by rw [← hzu]; rfl
        rw [h1]
        exact hz)
      rw [← this]
      exact hu'
  · exfalso
    set e' : X ≃* ↥Alt7 := e.trans (CFSG.LocalAnalysis.GLTheoremB.S7.conjEquiv τ) with he'
    have hπ' : permOfAut e' σ = a33 := by rw [he', permOfAut_conj, hτ]
    have h1 := permOfAut_spec e' σ k0
    rw [mem_fixSub.1 hk0fix, hπ'] at h1
    have hcomm : (e' k0 : S) * a33 = a33 * (e' k0 : S) := by
      calc (e' k0 : S) * a33 = (a33 * (e' k0 : S) * a33⁻¹) * a33 := by rw [← h1]
        _ = a33 * (e' k0 : S) := by group
    have hsign : Equiv.Perm.sign (e' k0 : S) = 1 := Equiv.Perm.mem_alternatingGroup.1 (e' k0).2
    have hpow : (e' k0 : S) ^ (2 ^ n0) = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, hn0, map_one, Subgroup.coe_one]
    have h2 := s7_two_elem_comm_a33 _ hcomm hsign (pow_sixteen_of_two_power hpow)
    apply hk01
    apply e'.injective
    rw [map_one]
    exact Subtype.ext h2

end S7Klein

section IIHardTools

variable {G : Type} [Group G] [Finite G]

theorem barAut_eq_conj {L : Subgroup G} {l : G} (hl : l ∈ L)
    (hlN : l ∈ Subgroup.normalizer (L : Set G)) :
    barAut 3 L ⟨l, hlN⟩ = MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : barOf 3 L) := by
  ext w
  induction w using QuotientGroup.induction_on with
  | H x =>
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
    show (QuotientGroup.mk (L.normalizerMonoidHom ⟨l, hlN⟩ x) : barOf 3 L) = _
    rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl

theorem eq_one_of_mem_core_of_isPGroup {L P : Subgroup G} (hP : IsPGroup 3 ↥P) {x : G}
    (hxP : x ∈ P) (hxO : x ∈ GLAPPrimeCoreOf 3 L) : x = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨x, hxP⟩
  have hk' : orderOf x = 3 ^ k := (Subgroup.orderOf_coe (⟨x, hxP⟩ : ↥P)).trans hk
  have hdvd : orderOf x ∣ Nat.card ↥(GLAPPrimeCoreOf 3 L) := by
    have h1 := orderOf_dvd_natCard (⟨x, hxO⟩ : ↥(GLAPPrimeCoreOf 3 L))
    rwa [Subgroup.orderOf_mk] at h1
  have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCoreOf 3 L)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      (not_dvd_card_glaPPrimeCoreOf Nat.prime_three L)
  rw [hk'] at hdvd
  have h1 : 3 ^ k = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hcop) hdvd
  exact orderOf_eq_one_iff.1 (hk'.trans h1)

theorem eq_one_of_barAut_eq_one {L P : Subgroup G} (e : barOf 3 L ≃* alternatingGroup (Fin 7))
    (hP : IsPGroup 3 ↥P) {x : G} (hxL : x ∈ L) (hxP : x ∈ P)
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (h1 : barAut 3 L ⟨x, hxN⟩ = 1) : x = 1 := by
  rw [barAut_eq_conj hxL hxN] at h1
  have hcen : (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : barOf 3 L) = 1 := by
    have hz : e (QuotientGroup.mk (⟨x, hxL⟩ : ↥L)) ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨k, rfl⟩ := e.surjective g
      have := congrArg (fun φ : MulAut (barOf 3 L) => φ k) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [← map_mul, ← map_mul]
      congr 1
      calc k * QuotientGroup.mk ⟨x, hxL⟩ =
          (QuotientGroup.mk ⟨x, hxL⟩ * k * (QuotientGroup.mk ⟨x, hxL⟩)⁻¹) *
            QuotientGroup.mk ⟨x, hxL⟩ := by rw [this]
        _ = QuotientGroup.mk ⟨x, hxL⟩ * k := by group
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hz
    exact e.injective (hz.trans (map_one e).symm)
  have hO : (⟨x, hxL⟩ : ↥L) ∈ GLAPPrimeCore 3 ↥L := (QuotientGroup.eq_one_iff _).1 hcen
  exact eq_one_of_mem_core_of_isPGroup hP hxP ((mem_gLAPPrimeCoreOf_iff 3 L x).2 ⟨hxL, hO⟩)

theorem exists_lift_of_fix {L : Subgroup G} {g : G} (hgN : g ∈ Subgroup.normalizer (L : Set G))
    (hg3 : g ^ 3 = 1) (f : barOf 3 L) (hf : barAut 3 L ⟨g, hgN⟩ f = f) :
    ∃ y : ↥L, (y : G) ∈ Cg g ∧ (QuotientGroup.mk y : barOf 3 L) = f := by
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective f
  have hfz : (QuotientGroup.mk (L.normalizerMonoidHom ⟨g, hgN⟩ z) : barOf 3 L) =
      QuotientGroup.mk z := by
    rw [← CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
    exact hf
  have hzmem : (z : ↥L)⁻¹ * L.normalizerMonoidHom ⟨g, hgN⟩ z ∈ GLAPPrimeCore 3 ↥L :=
    QuotientGroup.eq.1 hfz.symm
  have hx : (z : G)⁻¹ * (g * (z : G) * g⁻¹) ∈ GLAPPrimeCoreOf 3 L :=
    (mem_gLAPPrimeCoreOf_iff 3 L _).2 ⟨((z : ↥L)⁻¹ * L.normalizerMonoidHom ⟨g, hgN⟩ z).2, hzmem⟩
  have hcopQ : ¬ 3 ∣ Nat.card ↥(GLAPPrimeCoreOf 3 L) :=
    not_dvd_card_glaPPrimeCoreOf Nat.prime_three L
  have hQn : ∀ q ∈ GLAPPrimeCoreOf 3 L, g * q * g⁻¹ ∈ GLAPPrimeCoreOf 3 L := fun q hq =>
    conj_mem_glaPPrimeCoreOf 3 hgN hq
  obtain ⟨q, hqQ, hfixq⟩ := exists_fixed_mem_coset g hg3 (GLAPPrimeCoreOf 3 L) hcopQ hQn (z : G) hx
  obtain ⟨hqL, hqcore⟩ := (mem_gLAPPrimeCoreOf_iff 3 L q).1 hqQ
  have hmk1 : (QuotientGroup.mk (⟨q, hqL⟩ : ↥L) : barOf 3 L) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hqcore
  have hwL : (z : G) * q ∈ L := Subgroup.mul_mem _ z.2 hqL
  refine ⟨⟨(z : G) * q, hwL⟩, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact mul_inv_eq_iff_eq_mul.1 hfixq
  · have hy_eq : (⟨(z : G) * q, hwL⟩ : ↥L) = z * ⟨q, hqL⟩ := Subtype.ext rfl
    rw [hy_eq, QuotientGroup.mk_mul, hmk1, mul_one]

theorem mem_pCoreOf_of_image {L H : Subgroup G} (hHL : H ≤ L)
    (hO : GLAPPrimeCoreOf 3 L ≤ pCoreOf 2 L) {W : Subgroup (barOf 3 L)} (hW2 : IsPGroup 2 ↥W)
    (hWn : ∀ z (hz : z ∈ H), (QuotientGroup.mk (⟨z, hHL hz⟩ : ↥L) : barOf 3 L) ∈
      Subgroup.normalizer (W : Set (barOf 3 L)))
    {y : G} (hyH : y ∈ H) (hyW : (QuotientGroup.mk (⟨y, hHL hyH⟩ : ↥L) : barOf 3 L) ∈ W) :
    y ∈ pCoreOf 2 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup G := H ⊓ (W.comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))).map L.subtype
    with hQ
  have hmemQ : ∀ z : G, z ∈ Q ↔ ∃ hz : z ∈ H,
      (QuotientGroup.mk (⟨z, hHL hz⟩ : ↥L) : barOf 3 L) ∈ W := by
    intro z
    constructor
    · rintro ⟨hzH, ⟨z', hz', rfl⟩⟩
      exact ⟨hzH, hz'⟩
    · rintro ⟨hzH, hzW⟩
      exact ⟨hzH, ⟨⟨z, hHL hzH⟩, hzW, rfl⟩⟩
  have hQH : Q ≤ H := inf_le_left
  have hQ2 : IsPGroup 2 ↥Q := by
    intro q
    obtain ⟨hqH, hqW⟩ := (hmemQ q).1 q.2
    obtain ⟨n, hn⟩ := hW2 ⟨_, hqW⟩
    have hn' : (QuotientGroup.mk (⟨(q : G), hHL hqH⟩ : ↥L) : barOf 3 L) ^ (2 ^ n) = 1 :=
      congrArg Subtype.val hn
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hn'
    have hcore : (q : G) ^ (2 ^ n) ∈ GLAPPrimeCoreOf 3 L :=
      (mem_gLAPPrimeCoreOf_iff 3 L _).2 ⟨_, hn'⟩
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨_, hO hcore⟩
    refine ⟨n + m, Subtype.ext ?_⟩
    have hm' : ((q : G) ^ (2 ^ n)) ^ (2 ^ m) = 1 := congrArg Subtype.val hm
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_add, pow_mul]
    exact hm'
  have hQn : H ≤ Subgroup.normalizer (Q : Set G) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro q
    rw [hmemQ, hmemQ]
    constructor
    · rintro ⟨hqH, hqW⟩
      have hzq : z * q * z⁻¹ ∈ H := H.mul_mem (H.mul_mem hz hqH) (H.inv_mem hz)
      refine ⟨hzq, ?_⟩
      have h1 := (Subgroup.mem_normalizer_iff.1 (hWn z hz) _).1 hqW
      have e1 : (QuotientGroup.mk (⟨z * q * z⁻¹, hHL hzq⟩ : ↥L) : barOf 3 L) =
          QuotientGroup.mk (⟨z, hHL hz⟩ : ↥L) * QuotientGroup.mk (⟨q, hHL hqH⟩ : ↥L) *
            (QuotientGroup.mk (⟨z, hHL hz⟩ : ↥L))⁻¹ := by
        rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        rfl
      rw [e1]
      exact h1
    · rintro ⟨hzq, hzqW⟩
      have hqH : q ∈ H := by
        have := H.mul_mem (H.mul_mem (H.inv_mem hz) hzq) hz
        simpa [mul_assoc] using this
      refine ⟨hqH, ?_⟩
      have e1 : (QuotientGroup.mk (⟨z * q * z⁻¹, hHL hzq⟩ : ↥L) : barOf 3 L) =
          QuotientGroup.mk (⟨z, hHL hz⟩ : ↥L) * QuotientGroup.mk (⟨q, hHL hqH⟩ : ↥L) *
            (QuotientGroup.mk (⟨z, hHL hz⟩ : ↥L))⁻¹ := by
        rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        rfl
      rw [e1] at hzqW
      exact (Subgroup.mem_normalizer_iff.1 (hWn z hz) _).2 hzqW
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQH hQn hQ2
    ((hmemQ y).2 ⟨hyH, hyW⟩)

theorem mk_mem_fixSub_of_comm {L : Subgroup G} {g : G} (hgN : g ∈ Subgroup.normalizer (L : Set G))
    {z : G} (hzL : z ∈ L) (hz : g * z = z * g) :
    (QuotientGroup.mk (⟨z, hzL⟩ : ↥L) : barOf 3 L) ∈ fixSub (barAut 3 L ⟨g, hgN⟩) := by
  rw [mem_fixSub, CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
  congr 1
  apply Subtype.ext
  show g * z * g⁻¹ = z
  rw [hz, mul_inv_cancel_right]

theorem T_facts : CFSG.LocalAnalysis.GLTheoremB.S7.T ≤ alternatingGroup (Fin 7) ∧
    IsElemAbelian 3 CFSG.LocalAnalysis.GLTheoremB.S7.T ∧
    Nat.card ↥CFSG.LocalAnalysis.GLTheoremB.S7.T = 9 := by
  set a := CFSG.LocalAnalysis.GLTheoremB.S7.a
  set b := CFSG.LocalAnalysis.GLTheoremB.S7.b
  have ha : a ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have hb : b ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have hab : Commute a b := CFSG.LocalAnalysis.GLTheoremB.S7.a_mul_b
  have hcomm : ∀ i j : ℤ, Commute (a ^ i) (b ^ j) := fun i j => hab.zpow_zpow i j
  have hc : Subgroup.zpowers a ≤ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup _) : Set _) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ((hcomm i j).eq).symm
  refine ⟨sup_le ((Subgroup.zpowers_le).2 ha) ((Subgroup.zpowers_le).2 hb), ⟨⟨⟨fun u v => ?_⟩⟩,
    fun z hz => ?_⟩, CFSG.LocalAnalysis.GLTheoremB.S7.card_T⟩
  · obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, hu⟩ := exists_mul_of_mem_sup hc u.2
    obtain ⟨_, ⟨k, rfl⟩, _, ⟨l, rfl⟩, hv⟩ := exists_mul_of_mem_sup hc v.2
    apply Subtype.ext
    show (u : Equiv.Perm (Fin 7)) * v = v * u
    rw [hu, hv]
    exact (Commute.mul_right (Commute.mul_left (Commute.zpow_zpow_self a i k) (hcomm k j).symm)
      (Commute.mul_left (hcomm i l) (Commute.zpow_zpow_self b j l))).eq
  · obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩ := exists_mul_of_mem_sup hc hz
    rw [(hcomm i j).mul_pow]
    have h1 : (a ^ i) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        CFSG.LocalAnalysis.GLTheoremB.S7.a_pow_three, one_zpow]
    have h2 : (b ^ j) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        CFSG.LocalAnalysis.GLTheoremB.S7.b_pow_three, one_zpow]
    rw [h1, h2, one_mul]

theorem two_le_pRank_of_alt7 {L : Subgroup G} (e : barOf 3 L ≃* alternatingGroup (Fin 7)) :
    2 ≤ CFSG.Open.pRank 3 L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hTA, hTel, hTc⟩ := T_facts
  set T' : Subgroup (barOf 3 L) :=
    (CFSG.LocalAnalysis.GLTheoremB.S7.T.subgroupOf (alternatingGroup (Fin 7))).map
      e.symm.toMonoidHom with hT'
  have hT'el : IsElemAbelian 3 T' :=
    CFSG.SectionRank.isElemAbelian_map (CFSG.Open.IsElemAbelian.subgroupOf hTel _) _
  have hT'c : Nat.card ↥T' = 9 := by
    rw [hT', Subgroup.card_map_of_injective e.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA).toEquiv, hTc]
  obtain ⟨S0, hS0el, -, hS0c⟩ := exists_elemAbelian_lift (GLAPPrimeCore 3 ↥L)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card) hT'el
  have hel : IsElemAbelian 3 (S0.map L.subtype) := CFSG.SectionRank.isElemAbelian_map hS0el _
  have hc : Nat.card ↥(S0.map L.subtype) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hS0c, hT'c]
    norm_num
  exact CFSG.SectionRank.le_pRank (by norm_num) (Subgroup.map_subtype_le _) hel hc

theorem exists_bd_complement {L B P : Subgroup G} (eL : barOf 3 L ≃* alternatingGroup (Fin 7))
    (hBel : IsElemAbelian 3 B) (hP : IsPGroup 3 ↥P) (hBP : B ≤ P) {d : G} (hdP : d ∈ P)
    (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hσd : barAut 3 L ⟨d, hdN⟩ ≠ 1)
    (h9 : 9 ≤ Nat.card ↥(B ⊓ L)) :
    ∃ b ∈ B ⊓ L, ∃ c ∈ B ⊓ L,
      (∀ hb : b ∈ Subgroup.normalizer (L : Set G), barAut 3 L ⟨b, hb⟩ = barAut 3 L ⟨d, hdN⟩) ∧
      c ∉ Subgroup.zpowers b ∧ Subgroup.zpowers c ⊓ Subgroup.zpowers b = ⊥ ∧
      Subgroup.zpowers c ⊔ Subgroup.zpowers b = B ⊓ L ∧ (∀ y ∈ B ⊓ L, y * d = d * y) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer (L : Set G) with hNdef
  set ρ : ↥N →* Equiv.Perm (Fin 7) :=
    (CFSG.LocalAnalysis.GLTheoremB.S7.permOfAut eL).comp (barAut 3 L) with hρ
  have hBLN : B ⊓ L ≤ N := inf_le_right.trans Subgroup.le_normalizer
  have hBLP : B ⊓ L ⊔ Subgroup.zpowers d ≤ N := sup_le hBLN ((Subgroup.zpowers_le).2 hdN)
  have hρ1 : ∀ y : ↥N, ρ y = 1 → barAut 3 L y = 1 := fun y h1 =>
    CFSG.LocalAnalysis.GLTheoremB.S7.permOfAut_injective eL (by rw [map_one]; exact h1)
  have hinj : ∀ y : ↥N, (y : G) ∈ B ⊓ L → ρ y = 1 → (y : G) = 1 := fun y hy h1 =>
    eq_one_of_barAut_eq_one eL hP hy.2 (hBP hy.1) y.2 (hρ1 y h1)
  have hinj' : Function.Injective (ρ.comp ((B ⊓ L).subgroupOf N).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have := hinj (y : ↥N) (Subgroup.mem_subgroupOf.1 y.2) hy
    exact Subgroup.mem_bot.2 (Subtype.ext (Subtype.ext this))
  have hcardBL : Nat.card ↥(((B ⊓ L).subgroupOf N).map ρ) = Nat.card ↥(B ⊓ L) := by
    have hrange : (ρ.comp ((B ⊓ L).subgroupOf N).subtype).range = ((B ⊓ L).subgroupOf N).map ρ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBLN).toEquiv]
  have hP'3 : IsPGroup 3 ↥((B ⊓ L ⊔ Subgroup.zpowers d).subgroupOf N) := by
    have : IsPGroup 3 ↥(B ⊓ L ⊔ Subgroup.zpowers d) :=
      hP.to_le (sup_le (inf_le_left.trans hBP) ((Subgroup.zpowers_le).2 hdP))
    exact this.of_equiv (Subgroup.subgroupOfEquivOfLe hBLP).symm
  have hle9 : Nat.card ↥(((B ⊓ L ⊔ Subgroup.zpowers d).subgroupOf N).map ρ) ≤ 9 :=
    CFSG.LocalAnalysis.GLTheoremB.S7.card_le_nine (hP'3.map ρ)
  have hBLP' : ((B ⊓ L).subgroupOf N).map ρ ≤ ((B ⊓ L ⊔ Subgroup.zpowers d).subgroupOf N).map ρ :=
    Subgroup.map_mono (Subgroup.comap_mono le_sup_left)
  have hcard9 : Nat.card ↥(B ⊓ L) = 9 := by
    have := Subgroup.card_le_of_le hBLP'
    omega
  have heq : ((B ⊓ L).subgroupOf N).map ρ = ((B ⊓ L ⊔ Subgroup.zpowers d).subgroupOf N).map ρ :=
    Subgroup.eq_of_le_of_card_ge hBLP' (by omega)
  have hdP' : (⟨d, hdN⟩ : ↥N) ∈ (B ⊓ L ⊔ Subgroup.zpowers d).subgroupOf N :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
  have hdIm : ρ ⟨d, hdN⟩ ∈ ((B ⊓ L).subgroupOf N).map ρ := heq ▸ Subgroup.mem_map_of_mem ρ hdP'
  obtain ⟨y, hy, hyd⟩ := hdIm
  have hbBL : (y : G) ∈ B ⊓ L := Subgroup.mem_subgroupOf.1 hy
  have hσb : barAut 3 L y = barAut 3 L ⟨d, hdN⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.S7.permOfAut_injective eL hyd
  have hcommIm : ∀ u ∈ ((B ⊓ L).subgroupOf N).map ρ, ∀ v ∈ ((B ⊓ L).subgroupOf N).map ρ,
      u * v = v * u := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hu' := Subgroup.mem_subgroupOf.1 hu
    have hv' := Subgroup.mem_subgroupOf.1 hv
    show (u : G) * (v : G) = (v : G) * (u : G)
    exact congrArg Subtype.val (hBel.1.is_comm.comm ⟨(u : G), hu'.1⟩ ⟨(v : G), hv'.1⟩)
  have hcd : ∀ z ∈ B ⊓ L, z * d = d * z := by
    intro z hz
    set z' : ↥N := ⟨z, hBLN hz⟩ with hz'
    have h1 : ρ z' * ρ ⟨d, hdN⟩ = ρ ⟨d, hdN⟩ * ρ z' :=
      hcommIm _ (Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.2 hz)) _ ⟨y, hy, hyd⟩
    have h2 : ρ (z' * ⟨d, hdN⟩ * z'⁻¹ * (⟨d, hdN⟩ : ↥N)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [h1]
      group
    have hcL : z * d * z⁻¹ * d⁻¹ ∈ L := by
      have h3 : d * z⁻¹ * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hdN _).1 (L.inv_mem hz.2)
      have : z * d * z⁻¹ * d⁻¹ = z * (d * z⁻¹ * d⁻¹) := by group
      rw [this]
      exact L.mul_mem hz.2 h3
    have hcP : z * d * z⁻¹ * d⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem (hBP hz.1) hdP) (P.inv_mem (hBP hz.1))) (P.inv_mem hdP)
    have h4 := eq_one_of_barAut_eq_one eL hP hcL hcP
      (z' * ⟨d, hdN⟩ * z'⁻¹ * (⟨d, hdN⟩ : ↥N)⁻¹).2 (hρ1 _ h2)
    calc z * d = (z * d * z⁻¹ * d⁻¹) * (d * z) := by group
      _ = d * z := by rw [h4, one_mul]
  have hb3 : (y : G) ^ 3 = 1 := hBel.2 _ hbBL.1
  have hb1 : (y : G) ≠ 1 := by
    intro h1
    apply hσd
    rw [← hσb]
    have : y = 1 := Subtype.ext h1
    rw [this, map_one]
  have hob : orderOf (y : G) = 3 := orderOf_eq_prime hb3 hb1
  obtain ⟨c, hcBL, hcb⟩ : ∃ c ∈ B ⊓ L, c ∉ Subgroup.zpowers (y : G) := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show B ⊓ L ≤ Subgroup.zpowers (y : G) from hcon)
    rw [Nat.card_zpowers, hob] at h1
    omega
  have hc3 : c ^ 3 = 1 := hBel.2 c hcBL.1
  have hc1 : c ≠ 1 := fun h => hcb (h ▸ Subgroup.one_mem _)
  have hoc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hinf : Subgroup.zpowers c ⊓ Subgroup.zpowers (y : G) = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers c ⊓ Subgroup.zpowers (y : G)) ∣ 3 := by
      rw [← hoc, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      apply hcb
      have h4 : Subgroup.zpowers c ⊓ Subgroup.zpowers (y : G) = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hoc])
      have h5 : Subgroup.zpowers c ≤ Subgroup.zpowers (y : G) := h4 ▸ inf_le_right
      exact h5 (Subgroup.mem_zpowers c)
  have hsup : Subgroup.zpowers c ⊔ Subgroup.zpowers (y : G) = B ⊓ L := by
    have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers (y : G) ≤ B ⊓ L :=
      sup_le ((Subgroup.zpowers_le).2 hcBL) ((Subgroup.zpowers_le).2 hbBL)
    have hlt : Subgroup.zpowers (y : G) < Subgroup.zpowers c ⊔ Subgroup.zpowers (y : G) :=
      lt_of_le_of_ne le_sup_right fun h => hcb (h ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
    have h1 := card_lt_of_lt' hlt
    rw [Nat.card_zpowers, hob] at h1
    have h2 : Nat.card ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers (y : G)) ∣ 9 :=
      hcard9 ▸ Subgroup.card_dvd_of_le hle
    have h3 : Nat.card ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers (y : G)) = 9 := by
      have h4 : Nat.card ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers (y : G)) ∈ Nat.divisors 9 :=
        Nat.mem_divisors.2 ⟨h2, by norm_num⟩
      have hd9 : Nat.divisors 9 = {1, 3, 9} := by decide
      rw [hd9] at h4
      simp only [Finset.mem_insert, Finset.mem_singleton] at h4
      omega
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h3, hcard9])
  exact ⟨(y : G), hbBL, c, hcBL, fun _ => hσb, hcb, hinf, hsup, hcd⟩

theorem card_eq_pow_pRank3 {E : Subgroup G} (hE : IsElemAbelian 3 E) :
    Nat.card ↥E = 3 ^ CFSG.Open.pRank 3 E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 ↥E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g.1 g.2)⟩
  obtain ⟨m, hm⟩ := hEp.exists_card_eq
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.pRank_eq_of_card Nat.prime_three hE hm, hm]

theorem mem_fixSub_of_mem_zpowers {X : Type} [Group X] {σ τ : MulAut X}
    (hτ : τ ∈ Subgroup.zpowers σ) {f : X} (hf : f ∈ fixSub σ) : f ∈ fixSub τ := by
  have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (MulAut X) f :=
    (Subgroup.zpowers_le).2 (show σ • f = f from hf)
  exact (show τ • f = f from hle hτ)

theorem fixSub_eq_of_mem_zpowers {X : Type} [Group X] {σ τ : MulAut X} (hσ3 : σ ^ 3 = 1)
    (hσ1 : σ ≠ 1) (hτ : τ ∈ Subgroup.zpowers σ) (hτ1 : τ ≠ 1) : fixSub τ = fixSub σ := by
  have hoσ : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hστ : σ ∈ Subgroup.zpowers τ := by
    obtain ⟨i, rfl⟩ := hτ
    have hmod : σ ^ (i % 3) = σ ^ i := by
      have := zpow_mod_orderOf σ i
      rwa [hoσ, Nat.cast_ofNat] at this
    rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with h0 | h1 | h2
    · exfalso
      apply hτ1
      show σ ^ i = 1
      rw [← hmod, h0, zpow_zero]
    · have : σ ^ i = σ := by rw [← hmod, h1, zpow_one]
      show σ ∈ Subgroup.zpowers (σ ^ i)
      rw [this]
      exact Subgroup.mem_zpowers σ
    · have h4 : (σ ^ i) ^ (2 : ℤ) = σ := by
        rw [← hmod, h2, ← zpow_mul]
        have := zpow_mod_orderOf σ ((2 : ℤ) * 2)
        rw [hoσ, Nat.cast_ofNat] at this
        rw [← this]
        norm_num
      show σ ∈ Subgroup.zpowers (σ ^ i)
      have h5 := Subgroup.zpow_mem_zpowers (σ ^ i) 2
      rwa [h4] at h5
  ext f
  exact ⟨fun hf => mem_fixSub_of_mem_zpowers hστ hf, fun hf => mem_fixSub_of_mem_zpowers hτ hf⟩

end IIHardTools

theorem iiHardReduction_of_inputs (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement) (hO2 : Cex134_O2Statement)
    (h121c : Prop121_corStatement) (h133 : Lemma133Statement) (h135 : Lemma135_iStatement)
    (h91 : Lemma91ii) (h912 : Lemma912Statement) : Lemma136c.IIHardReduction := by
  intro G _ _ m B M E A D T L h hN d hd hd1 hfix
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLc, -⟩ := hcomp h.toSec13 h.hL
  have hLM : L ≤ M := hLc.1
  have hLsn : IsSubnormal L M := hLc.2.1
  have hDA : D ≤ A := h.hD.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hDM : D ≤ M := hDA.trans hAM
  have hdA : d ∈ A := hDA hd
  have hdM : d ∈ M := hDM hd
  have hBM : B ≤ M := h.uniq.le
  have hBel : IsElemAbelian 3 B := h.uniq.elemAbelian
  have hP3 : IsPGroup 3 ↥(A ⊔ B) := h.hAB
  have hBP : B ≤ A ⊔ B := le_sup_right
  have hdP : d ∈ A ⊔ B := Subgroup.mem_sup_left hdA
  obtain ⟨-, eM, -⟩ := Lemma136.l136_gamma hP95 h111 h121 hcomp h
  set eL : barOf 3 L ≃* alternatingGroup (Fin 7) := (quotEquivBarX hp hLM hLsn).trans eM with heL
  have hOL : GLAPPrimeCoreOf 3 L ≤ pCoreOf 2 L := hO2 h rfl
  have hLI : GLAPComponent 3 (Istar 3 M D) L :=
    glaPComponent_of_le hp hLc ((h.hL.1).trans (Lemma135.iof_le_istar' 3 M D))
      (istar_le_M 3 M D)
  obtain ⟨-, hBN, -, -, hrkBL⟩ := (h133 h.toSec13).2 L hLI
  have h9 : 9 ≤ Nat.card ↥(B ⊓ L) := by
    rw [card_eq_pow_pRank3 (CFSG.Open.IsElemAbelian.mono hBel inf_le_left), hrkBL]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 L := Nat.pow_le_pow_right (by norm_num) (two_le_pRank_of_alt7 eL)
  have hd3 : d ^ 3 = 1 := h.hD.2.1.2 d hd
  have hσ3 : barAut 3 L ⟨d, hN hd⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨d, hN hd⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 := Subtype.ext (by simp [hd3])
    rw [this, map_one]
  obtain ⟨hσd1, W, hWfix, hW2, hWn, hW2elt, hWcomm⟩ := exists_klein eL _ hσ3 hfix
  obtain ⟨b, hbBL, c, hcBL, hσb, hcb, hinf, hsup, hBLd⟩ :=
    exists_bd_complement eL hBel hP3 hBP hdP (hN hd) hσd1 h9
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hbBL.2
  have hbd : b * d = d * b := hBLd b hbBL
  have hb1 : b ≠ 1 := by
    intro h1
    apply hσd1
    rw [← hσb hbN]
    have : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G))) = 1 := Subtype.ext h1
    rw [this, map_one]
  have hCDd : Subgroup.centralizer (D : Set G) ≤ Cg d :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hd)
  have hbCd : b ∈ Cg d := Subgroup.mem_centralizer_singleton_iff.2 hbd
  have hBsB : Lemma136c.bStarOf B L D b ≤ B :=
    sup_le ((Subgroup.zpowers_le).2 hbBL.1) (inf_le_left.trans inf_le_right)
  have hBsCd : Lemma136c.bStarOf B L D b ≤ Cg d :=
    sup_le ((Subgroup.zpowers_le).2 hbCd) (inf_le_right.trans hCDd)
  have hBsel : IsElemAbelian 3 (Lemma136c.bStarOf B L D b) := CFSG.Open.IsElemAbelian.mono hBel hBsB
  have hBsN : Lemma136c.bStarOf B L D b ≤ Subgroup.normalizer (L : Set G) := hBsB.trans hBN
  have hBs3 : IsPGroup 3 ↥(Lemma136c.bStarOf B L D b) := hP3.to_le (hBsB.trans hBP)
  have hBsσ : ∀ x (hx : x ∈ Lemma136c.bStarOf B L D b),
      barAut 3 L ⟨x, hBsN hx⟩ ∈ Subgroup.zpowers (barAut 3 L ⟨d, hN hd⟩) := by
    have hle : Lemma136c.bStarOf B L D b ≤
        ((Subgroup.zpowers (barAut 3 L ⟨d, hN hd⟩)).comap (barAut 3 L)).map
          (Subgroup.normalizer (L : Set G)).subtype := by
      refine sup_le ((Subgroup.zpowers_le).2 ⟨⟨b, hbN⟩, ?_, rfl⟩) fun v hv =>
        ⟨⟨v, hBN hv.1.2⟩, ?_, rfl⟩
      · show barAut 3 L ⟨b, hbN⟩ ∈ Subgroup.zpowers (barAut 3 L ⟨d, hN hd⟩)
        rw [hσb hbN]
        exact Subgroup.mem_zpowers _
      · show barAut 3 L ⟨v, _⟩ ∈ Subgroup.zpowers (barAut 3 L ⟨d, hN hd⟩)
        have hvc : v ∈ centBar 3 ⊤ L := ⟨hv.1.1, Subgroup.mem_top v⟩
        rw [(Lemma129.mem_centBar_top_iff _).1 hvc]
        exact Subgroup.one_mem _
    intro x hx
    obtain ⟨x', hx', hxx'⟩ := hle hx
    have : x' = ⟨x, hBsN hx⟩ := Subtype.ext hxx'
    rw [← this]
    exact hx'
  have hne := h135 h
  obtain ⟨y, hy, hy1⟩ : ∃ y ∈ barX 3 M B ⊓ Subgroup.centralizer
      ((barX 3 M D ⊔ barX 3 M (Lstarsub D L) : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M)), y ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hne ((Subgroup.eq_bot_iff_forall _).2 hc)
  obtain ⟨hyB, hyC⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨c', hc'B, rfl⟩ := (mem_barX_iff 3 _).1 hyB
  have hc'C : ∀ z ∈ barX 3 M D ⊔ barX 3 M (Lstarsub D L),
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) c' * z = z * QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) c' :=
    fun z hz => ((Subgroup.mem_centralizer_iff.1 hyC) z hz).symm
  have hc'D : (c' : G) ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hgbar : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨g, hDM hg⟩ : ↥M) ∈ barX 3 M D :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hg)
    exact (Lemma136b.commute_of_bar c'.2 (hDM hg) hP3 (hBP hc'B) (Subgroup.mem_sup_left (hDA hg))
      (hc'C _ (Subgroup.mem_sup_left hgbar))).symm
  have hc'N : (c' : G) ∈ Subgroup.normalizer (L : Set G) := hBN hc'B
  have hc'cent : (c' : G) ∈ centBar 3 ⊤ L :=
    Lemma136.l136_centBar_of_centralizes hp hLsn c'.2 hc'N fun q hq =>
      hc'C q (Subgroup.mem_sup_right (barX_mono_of_le 3 Lemma136.l136_le_lstar hq))
  have hc'Bs : (c' : G) ∈ Lemma136c.bStarOf B L D b :=
    Subgroup.mem_sup_right ⟨⟨hc'cent.1, hc'B⟩, hc'D⟩
  have hc'1 : (c' : G) ≠ 1 := fun h1 => hy1 (by rw [show c' = 1 from Subtype.ext h1, map_one])
  have hc'b : (c' : G) ∉ Subgroup.zpowers b := by
    rintro ⟨i, hi⟩
    have h1 : barAut 3 L ⟨c', hc'N⟩ = 1 := (Lemma129.mem_centBar_top_iff hc'N).1 hc'cent
    have hbiBL : b ^ i ∈ B ⊓ L := (B ⊓ L).zpow_mem hbBL i
    have h2 : barAut 3 L ⟨b ^ i, Subgroup.le_normalizer hbiBL.2⟩ = 1 := by
      have : (⟨b ^ i, Subgroup.le_normalizer hbiBL.2⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          ⟨c', hc'N⟩ := Subtype.ext hi
      rw [this]
      exact h1
    have h3 := eq_one_of_barAut_eq_one eL hP3 hbiBL.2 (hBP hbiBL.1) _ h2
    exact hc'1 (hi ▸ h3)
  have hr : 2 ≤ CFSG.Open.pRank 3 (Lemma136c.bStarOf B L D b) := by
    have hcard := card_eq_pow_pRank3 hBsel
    have hlt : Subgroup.zpowers b < Lemma136c.bStarOf B L D b :=
      lt_of_le_of_ne le_sup_left fun h => hc'b (h ▸ hc'Bs)
    have h1 := card_lt_of_lt' hlt
    rw [Nat.card_zpowers, orderOf_eq_prime (hBel.2 b hbBL.1) hb1, hcard] at h1
    by_contra hcon
    push Not at hcon
    have : 3 ^ CFSG.Open.pRank 3 (Lemma136c.bStarOf B L D b) ≤ 3 ^ 1 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hEk : IsEkIn 3 (CFSG.Open.pRank 3 (Lemma136c.bStarOf B L D b)) (Cg d)
      (Lemma136c.bStarOf B L D b) := ⟨hBsCd, hBsel, card_eq_pow_pRank3 hBsel⟩
  have hmkfix : ∀ z (hz : z ∈ L ⊓ Cg d),
      (QuotientGroup.mk (⟨z, hz.1⟩ : ↥L) : barOf 3 L) ∈ fixSub (barAut 3 L ⟨d, hN hd⟩) :=
    fun z hz => mk_mem_fixSub_of_comm (hN hd) hz.1
      (Subgroup.mem_centralizer_singleton_iff.1 hz.2).symm
  have hO2char : ∀ z, z ∈ pCoreOf 2 (L ⊓ Cg d) ↔
      ∃ hz : z ∈ L ⊓ Cg d, (QuotientGroup.mk (⟨z, hz.1⟩ : ↥L) : barOf 3 L) ∈ W := by
    intro z
    constructor
    · intro hz
      have hzLC : z ∈ L ⊓ Cg d := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hz
      refine ⟨hzLC, ?_⟩
      obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊓ Cg d) ⟨z, hz⟩
      have hn' : z ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
      refine hW2elt _ (hmkfix z hzLC) n ?_
      rw [← QuotientGroup.mk_pow]
      have : (⟨z, hzLC.1⟩ : ↥L) ^ (2 ^ n) = 1 := Subtype.ext (by simpa using hn')
      rw [this, QuotientGroup.mk_one]
    · rintro ⟨hz, hzW⟩
      exact mem_pCoreOf_of_image inf_le_left hOL hW2 (fun z' hz' => hWn _ (hmkfix z' hz')) hz hzW
  have hSΔ : Subgroup.centralizer (Lemma136c.bStarOf B L D b : Set G) ⊓ pCoreOf 2 (L ⊓ Cg d) ≤
      localDeltaTwoIn (Cg d) (Lemma136c.bStarOf B L D b) := by
    intro s hs
    obtain ⟨hsBs, hsO⟩ := hs
    obtain ⟨⟨hsL, hsd⟩, hsW⟩ := (hO2char s).1 hsO
    unfold localDeltaTwoIn
    simp only [Subgroup.mem_iInf]
    intro x hx hx1
    have hxB : x ∈ B := hBsB hx
    have hxN : x ∈ Subgroup.normalizer (L : Set G) := hBsN hx
    have hxs : s ∈ Cg x := Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 hsBs) x hx).symm
    have hxd : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.1 (hBsCd hx)
    have hdx : d ∈ Cg x := Subgroup.mem_centralizer_singleton_iff.2 hxd.symm
    have hx3 : IsPGroup 3 ↥(Subgroup.zpowers x) := hP3.to_le ((Subgroup.zpowers_le).2 (hBP hxB))
    have h91x : pCoreOf 2 (M ⊓ Cg x) ≤ pCoreOf 2 (Cg x) :=
      h91 G m 3 h.standing B M h.bOne h.pre x hxB hx1
    have hdxC : Cg d ⊓ pCoreOf 2 (Cg x) ≤ pCoreOf 2 (Cg d ⊓ Cg x) :=
      Lemma129.inf_pCoreOf_two_le (Cg d) (Cg x)
    by_cases hσx : barAut 3 L ⟨x, hxN⟩ = 1
    ·
      have hxM : x ∈ M := hBM hxB
      have hxcent : x ∈ centBar 3 ⊤ L := (Lemma129.mem_centBar_top_iff hxN).2 hσx
      have hxbar := Lemma136.l136_centralizes_barX_of_centBar hp hLM hLsn hxM hxcent
      have hbarx : barX 3 M (L ⊓ Cg x) = barX 3 M L := by
        rw [barX_inf_centralizer hp hxM hLM hxN hx3]
        exact inf_eq_left.2 fun q hq => Subgroup.mem_centralizer_singleton_iff.2 (hxbar q hq).symm
      have hPxsn : GLAPLayer 3 (L ⊓ Cg x) ≤ Cg x ∧ IsSubnormal (GLAPLayer 3 (L ⊓ Cg x)) (Cg x) := by
        have hsub : ∀ J ∈ {J : Subgroup G | GLAPComponent 3 (L ⊓ Cg x) J},
            J ≤ Cg x ∧ IsSubnormal J (Cg x) := fun J hJ =>
          isSubnormal_of_comp_inf_centralizer h912 h hxB hx1 hLc hOL eM hbarx hJ
        unfold GLAPLayer
        exact ⟨sSup_le fun J hJ => (hsub J hJ).1, isSubnormal_sSup _ hsub⟩
      have hPxle : GLAPLayer 3 (L ⊓ Cg x) ≤ L ⊓ Cg x := by
        unfold GLAPLayer
        exact sSup_le fun J hJ => hJ.1
      have hbarPx : barX 3 M L ≤ barX 3 M (GLAPLayer 3 (L ⊓ Cg x)) := by
        have hself := glaPComponent_self_of_alt7 ((MulEquiv.subgroupCongr hbarx).trans eM)
        obtain ⟨J, hJ, hJK⟩ := exists_glaPComponent_lift hp (inf_le_left.trans hLM) hself
        rw [← hbarx, ← hJK]
        refine barX_mono_of_le 3 ?_
        unfold GLAPLayer
        exact le_sSup hJ
      have hdPx : d ∈ Subgroup.normalizer ((GLAPLayer 3 (L ⊓ Cg x) : Subgroup G) : Set G) := by
        rw [mem_normalizer_iff_gLBConj_eq, ← glaPLayer_conj, gLBConj_inf,
          gLBConj_eq_of_mem_normalizer (hN hd),
          gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hdx)]
      have hd3' : IsPGroup 3 ↥(Subgroup.zpowers d) := hP3.to_le ((Subgroup.zpowers_le).2 hdP)
      have hbarPxd := barX_inf_centralizer hp hdM (hPxle.trans (inf_le_left.trans hLM)) hdPx hd3'
      have hsM : s ∈ M := hLM hsL
      have hsbar : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨s, hsM⟩ : ↥M) ∈
          barX 3 M (GLAPLayer 3 (L ⊓ Cg x) ⊓ Cg d) := by
        rw [hbarPxd]
        refine Subgroup.mem_inf.2
          ⟨hbarPx (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hsL)), ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hsd)
      obtain ⟨j, hj, hjs⟩ := (mem_barX_iff 3 _).1 hsbar
      have hjL : (j : G) ∈ L := (hPxle hj.1).1
      have hjx : (j : G) ∈ Cg x := (hPxle hj.1).2
      have hjd : (j : G) ∈ Cg d := hj.2
      have hn : (j : G)⁻¹ * s ∈ GLAPPrimeCoreOf 3 M := by
        have := QuotientGroup.eq.1 hjs
        exact (mem_gLAPPrimeCoreOf_iff 3 M _).2 ⟨_, this⟩
      have hnL : (j : G)⁻¹ * s ∈ L := L.mul_mem (L.inv_mem hjL) hsL
      have hnO : (j : G)⁻¹ * s ∈ GLAPPrimeCoreOf 3 L := by
        rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hLsn]
        exact ⟨hnL, hn⟩
      have hnO2 : (j : G)⁻¹ * s ∈ pCoreOf 2 M := pCoreOf_le_of_isSubnormal 2 hLsn (hOL hnO)
      have hnx : (j : G)⁻¹ * s ∈ Cg x := (Cg x).mul_mem ((Cg x).inv_mem hjx) hxs
      have hnd : (j : G)⁻¹ * s ∈ Cg d := (Cg d).mul_mem ((Cg d).inv_mem hjd) hsd
      have hnΔ : (j : G)⁻¹ * s ∈ pCoreOf 2 (Cg d ⊓ Cg x) := by
        have h1 : (j : G)⁻¹ * s ∈ pCoreOf 2 (Cg x ⊓ M) :=
          Lemma129.inf_pCoreOf_two_le (Cg x) M ⟨hnx, hnO2⟩
        rw [inf_comm] at h1
        exact hdxC ⟨hnd, h91x h1⟩
      have hjW : (QuotientGroup.mk (⟨(j : G), hjL⟩ : ↥L) : barOf 3 L) ∈ W := by
        have : (QuotientGroup.mk (⟨(j : G), hjL⟩ : ↥L) : barOf 3 L) = QuotientGroup.mk ⟨s, hsL⟩ := by
          rw [QuotientGroup.eq]
          obtain ⟨_, h1⟩ := (mem_gLAPPrimeCoreOf_iff 3 L _).1 hnO
          exact h1
        rw [this]
        exact hsW
      have hHL : GLAPLayer 3 (L ⊓ Cg x) ⊓ Cg d ≤ L := inf_le_left.trans (hPxle.trans inf_le_left)
      have hjO2 : (j : G) ∈ pCoreOf 2 (GLAPLayer 3 (L ⊓ Cg x) ⊓ Cg d) :=
        mem_pCoreOf_of_image hHL hOL hW2
          (fun z hz => hWn _ (hmkfix z ⟨hHL hz, hz.2⟩)) hj hjW
      have hPxdsn : IsSubnormal (GLAPLayer 3 (L ⊓ Cg x) ⊓ Cg d) (Cg x ⊓ Cg d) :=
        isSubnormal_inf hPxsn.2 (Cg d)
      have hjΔ : (j : G) ∈ pCoreOf 2 (Cg d ⊓ Cg x) := by
        rw [inf_comm]
        exact pCoreOf_le_of_isSubnormal 2 hPxdsn hjO2
      have : s = (j : G) * ((j : G)⁻¹ * s) := by group
      rw [this]
      exact Subgroup.mul_mem _ hjΔ hnΔ
    ·
      have hfixx := fixSub_eq_of_mem_zpowers hσ3 hσd1 (hBsσ x hx) hσx
      have h1 : s ∈ pCoreOf 2 (L ⊓ Cg x) :=
        mem_pCoreOf_of_image inf_le_left hOL hW2 (fun z hz => by
          have := mk_mem_fixSub_of_comm hxN hz.1
            (Subgroup.mem_centralizer_singleton_iff.1 hz.2).symm
          rw [hfixx] at this
          exact hWn _ this) ⟨hsL, hxs⟩ hsW
      have h2 : pCoreOf 2 (L ⊓ Cg x) ≤ pCoreOf 2 (M ⊓ Cg x) :=
        pCoreOf_le_of_isSubnormal 2 (isSubnormal_inf hLsn (Cg x))
      exact hdxC ⟨hsd, h91x (h2 h1)⟩
  have hcL : c ∈ L := hcBL.2
  have hcd : c * d = d * c := hBLd c hcBL
  have hcN : c ∈ Subgroup.normalizer
      ((Subgroup.centralizer (Lemma136c.bStarOf B L D b : Set G) ⊓ pCoreOf 2 (L ⊓ Cg d) :
        Subgroup G) : Set G) := by
    have hcC : c ∈ Subgroup.centralizer (Lemma136c.bStarOf B L D b : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact congrArg Subtype.val (hBel.1.is_comm.comm ⟨z, hBsB hz⟩ ⟨c, hcBL.1⟩)
    have hcLd : c ∈ L ⊓ Cg d := ⟨hcL, Subgroup.mem_centralizer_singleton_iff.2 hcd⟩
    exact mem_normalizer_inf (Subgroup.le_normalizer hcC)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hcLd)
  have hS1S : Lemma136c.s1Of B L D d b (Subgroup.zpowers c) ≤
      Subgroup.centralizer (Lemma136c.bStarOf B L D b : Set G) ⊓ pCoreOf 2 (L ⊓ Cg d) := by
    show ⁅Subgroup.zpowers c, _⁆ ≤ _
    rw [Subgroup.commutator_le]
    intro u hu v hv
    have huN := (Subgroup.zpowers_le.2 hcN) hu
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 huN v).1 hv) (Subgroup.inv_mem _ hv)
  have hW_S : ∀ f ∈ W, ∃ s ∈ Subgroup.centralizer (Lemma136c.bStarOf B L D b : Set G) ⊓
      pCoreOf 2 (L ⊓ Cg d), ∃ hsL : s ∈ L, (QuotientGroup.mk (⟨s, hsL⟩ : ↥L) : barOf 3 L) = f := by
    intro f hf
    obtain ⟨w, hwd, hwf⟩ := exists_lift_of_fix (hN hd) hd3 f (hWfix hf)
    have hV0p : ¬ 3 ∣ Nat.card ↥(GLAPPrimeCoreOf 3 L ⊓ Cg d) := fun h3 =>
      not_dvd_card_glaPPrimeCoreOf hp L (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hOLN : ∀ u ∈ Subgroup.normalizer (L : Set G),
        u ∈ Subgroup.normalizer ((GLAPPrimeCoreOf 3 L : Subgroup G) : Set G) := fun u hu => by
      rw [mem_normalizer_iff_gLBConj_eq, ← glaPPrimeCoreOf_gLBConj, gLBConj_eq_of_mem_normalizer hu]
    have hBsV0 : Lemma136c.bStarOf B L D b ≤
        Subgroup.normalizer ((GLAPPrimeCoreOf 3 L ⊓ Cg d : Subgroup G) : Set G) := fun u hu =>
      mem_normalizer_inf (hOLN u (hBsN hu)) (Subgroup.le_normalizer (hBsCd hu))
    have hwV0 : (w : G) ∈ Subgroup.normalizer ((GLAPPrimeCoreOf 3 L ⊓ Cg d : Subgroup G) : Set G) :=
      mem_normalizer_inf (hOLN _ (Subgroup.le_normalizer w.2)) (Subgroup.le_normalizer hwd)
    have hcomm' : ∀ u ∈ Lemma136c.bStarOf B L D b,
        u * (w : G) * u⁻¹ * (w : G)⁻¹ ∈ GLAPPrimeCoreOf 3 L ⊓ Cg d := by
      intro u hu
      have huN := hBsN hu
      have hfu : barAut 3 L ⟨u, huN⟩ f = f := mem_fixSub_of_mem_zpowers (hBsσ u hu) (hWfix hf)
      rw [← hwf, CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk] at hfu
      have hwL : u * (w : G) * u⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 huN _).1 w.2
      have heq : L.normalizerMonoidHom ⟨u, huN⟩ w = ⟨u * (w : G) * u⁻¹, hwL⟩ := Subtype.ext rfl
      rw [heq, QuotientGroup.eq_iff_div_mem] at hfu
      refine ⟨(mem_gLAPPrimeCoreOf_iff 3 L _).2 ⟨L.mul_mem hwL (L.inv_mem w.2), ?_⟩, ?_⟩
      · rw [div_eq_mul_inv] at hfu
        exact hfu
      · exact (Cg d).mul_mem ((Cg d).mul_mem ((Cg d).mul_mem (hBsCd hu) hwd)
          ((Cg d).inv_mem (hBsCd hu))) ((Cg d).inv_mem hwd)
    obtain ⟨v, hvV0, hvfix⟩ := exists_fixed_in_coset' (p := 3) hBs3 hV0p hBsV0 hwV0 hcomm'
    obtain ⟨hvL, hvO⟩ := (mem_gLAPPrimeCoreOf_iff 3 L v).1 hvV0.1
    have hsL : (w : G) * v ∈ L := L.mul_mem w.2 hvL
    have hsd : (w : G) * v ∈ Cg d := (Cg d).mul_mem hwd hvV0.2
    have hsf : (QuotientGroup.mk (⟨(w : G) * v, hsL⟩ : ↥L) : barOf 3 L) = f := by
      have e1 : (⟨(w : G) * v, hsL⟩ : ↥L) = w * ⟨v, hvL⟩ := Subtype.ext rfl
      rw [e1, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hvO, mul_one, hwf]
    refine ⟨(w : G) * v, Subgroup.mem_inf.2 ⟨?_, (hO2char _).2 ⟨⟨hsL, hsd⟩, ?_⟩⟩, hsL, hsf⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have := hvfix u hu
      calc u * ((w : G) * v) = (u * ((w : G) * v) * u⁻¹) * u := by group
        _ = ((w : G) * v) * u := by rw [this]
    · rw [hsf]
      exact hf
  have hcfix : (QuotientGroup.mk (⟨c, hcL⟩ : ↥L) : barOf 3 L) ∈ fixSub (barAut 3 L ⟨d, hN hd⟩) :=
    hmkfix c ⟨hcL, Subgroup.mem_centralizer_singleton_iff.2 hcd⟩
  have hc3 : (QuotientGroup.mk (⟨c, hcL⟩ : ↥L) : barOf 3 L) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨c, hcL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hBel.2 c hcBL.1)
    rw [this, QuotientGroup.mk_one]
  have hcσ : MulAut.conj (QuotientGroup.mk (⟨c, hcL⟩ : ↥L) : barOf 3 L) ∉
      Subgroup.zpowers (barAut 3 L ⟨d, hN hd⟩) := by
    rw [← barAut_eq_conj hcL (Subgroup.le_normalizer hcL)]
    rintro ⟨i, hi⟩
    apply hcb
    set cN : ↥(Subgroup.normalizer (L : Set G)) := ⟨c, Subgroup.le_normalizer hcL⟩
    set bN : ↥(Subgroup.normalizer (L : Set G)) := ⟨b, hbN⟩
    have hi' : barAut 3 L ⟨d, hN hd⟩ ^ i = barAut 3 L cN := hi
    have h1 : barAut 3 L (cN * (bN ^ i)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow, hσb hbN, hi', mul_inv_cancel]
    have hmemL : ((cN * (bN ^ i)⁻¹ : ↥(Subgroup.normalizer (L : Set G))) : G) ∈ L := by
      show c * (b ^ i)⁻¹ ∈ L
      exact L.mul_mem hcL (L.inv_mem (L.zpow_mem hbBL.2 i))
    have hmemP : ((cN * (bN ^ i)⁻¹ : ↥(Subgroup.normalizer (L : Set G))) : G) ∈ A ⊔ B := by
      show c * (b ^ i)⁻¹ ∈ A ⊔ B
      exact (A ⊔ B).mul_mem (hBP hcBL.1) ((A ⊔ B).inv_mem ((A ⊔ B).zpow_mem (hBP hbBL.1) i))
    have h2 := eq_one_of_barAut_eq_one eL hP3 hmemL hmemP _ h1
    have h3 : c * (b ^ i)⁻¹ = 1 := h2
    exact ⟨i, (mul_inv_eq_one.1 h3).symm⟩
  have hSL : Subgroup.centralizer (Lemma136c.bStarOf B L D b : Set G) ⊓ pCoreOf 2 (L ⊓ Cg d) ≤ L :=
    inf_le_right.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
  have hWS1 : W ≤ barX 3 L (Lemma136c.s1Of B L D d b (Subgroup.zpowers c)) := by
    refine (hWcomm _ hcfix hc3 hcσ).trans ?_
    show _ ≤ barX 3 L ⁅Subgroup.zpowers c, _⁆
    rw [barX_commutator 3 ((Subgroup.zpowers_le).2 hcL) hSL]
    refine Subgroup.commutator_mono ((Subgroup.zpowers_le).2 ?_) ?_
    · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers c))
    · intro f hf
      obtain ⟨s, hsS, hsL, hsf⟩ := hW_S f hf
      exact ⟨⟨s, hsL⟩, Subgroup.mem_subgroupOf.2 hsS, hsf⟩
  have hstep7 : pCoreOf 2 (L ⊓ Cg d) ≤ Lemma136c.s1Of B L D d b (Subgroup.zpowers c) ⊔
      GLAPPrimeCoreOf 3 (Cg d) := by
    intro z hz
    obtain ⟨⟨hzL, hzd⟩, hzW⟩ := (hO2char z).1 hz
    obtain ⟨s', hs', hs'z⟩ := hWS1 hzW
    have hs'S1 : (s' : G) ∈ Lemma136c.s1Of B L D d b (Subgroup.zpowers c) :=
      Subgroup.mem_subgroupOf.1 hs'
    have hn : (s' : G)⁻¹ * z ∈ GLAPPrimeCoreOf 3 L := by
      have := QuotientGroup.eq.1 hs'z
      exact (mem_gLAPPrimeCoreOf_iff 3 L _).2 ⟨_, this⟩
    have hs'd : (s' : G) ∈ Cg d :=
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _) (hS1S hs'S1).2).2
    have hnd : (s' : G)⁻¹ * z ∈ Cg d := (Cg d).mul_mem ((Cg d).inv_mem hs'd) hzd
    have hnO : (s' : G)⁻¹ * z ∈ GLAPPrimeCoreOf 3 (Cg d) := by
      have h1 : (s' : G)⁻¹ * z ∈ pCoreOf 2 M := pCoreOf_le_of_isSubnormal 2 hLsn (hOL hn)
      have h2 := h121c h.toSec11 hdA hd1 ⟨h1, hnd⟩
      exact pCoreOf_two_le_glaPPrimeCoreOf hp (by norm_num) _ h2
    have : z = (s' : G) * ((s' : G)⁻¹ * z) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hs'S1 hnO
  refine ⟨b, Subgroup.zpowers c, ⟨hbBL, hσb, (Subgroup.zpowers_le).2 hcBL, hinf, hsup⟩,
    ⟨le_inf hBsB hBsCd, ⟨_, hr, hEk⟩, hS1S.trans hSΔ, ?_, ?_, hstep7⟩⟩
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊓ Cg d)).to_le (hS1S.trans inf_le_right)
  · exact hS1S.trans (inf_le_right.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right))

@[expose] def IIHardCaseAlt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    (hN : D ≤ Subgroup.normalizer (L : Set G)) {d : G} (hd : d ∈ D) (hd1 : d ≠ 1),
    pCoreOf 2 (fixSub (barAut 3 L ⟨d, hN hd⟩)) ≠ ⊥ →
    ∀ (b : G) (B1 : Subgroup G), Lemma136c.IIHardPrinted B L D hN hd b B1 →
    Lemma136c.IIHardSetupData B L D d (Lemma136c.bStarOf B L D b) (Lemma136c.s1Of B L D d b B1) →
    ∀ (r : ℕ), 2 ≤ r → IsEkIn 3 r (Cg d) (Lemma136c.bStarOf B L D b) →
    ∀ (K : Subgroup G), GLAPComponent 3 (Cg d) K →
      ¬ ⁅K, Lemma136c.s1Of B L D d b B1⁆ ≤ GLAPPrimeCoreOf 3 (Cg d) →
      Lemma136c.bStarOf B L D b ≤ Subgroup.normalizer (K : Set G) →
      centBar 3 (Lemma136c.bStarOf B L D b) K = ⊥ →
      ¬ ∃ m' r' : ℕ, Lemma136c.Alt19_16a 3 r (barOf 3 K) (autBar 3 (Lemma136c.bStarOf B L D b) K) m' r'

@[expose] def IIHardCaseLie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    (hN : D ≤ Subgroup.normalizer (L : Set G)) {d : G} (hd : d ∈ D) (hd1 : d ≠ 1),
    pCoreOf 2 (fixSub (barAut 3 L ⟨d, hN hd⟩)) ≠ ⊥ →
    ∀ (b : G) (B1 : Subgroup G), Lemma136c.IIHardPrinted B L D hN hd b B1 →
    Lemma136c.IIHardSetupData B L D d (Lemma136c.bStarOf B L D b) (Lemma136c.s1Of B L D d b B1) →
    ∀ (r : ℕ), 2 ≤ r → IsEkIn 3 r (Cg d) (Lemma136c.bStarOf B L D b) →
    ∀ (K : Subgroup G), GLAPComponent 3 (Cg d) K →
      ¬ ⁅K, Lemma136c.s1Of B L D d b B1⁆ ≤ GLAPPrimeCoreOf 3 (Cg d) →
      Lemma136c.bStarOf B L D b ≤ Subgroup.normalizer (K : Set G) →
      centBar 3 (Lemma136c.bStarOf B L D b) K = ⊥ →
      ¬ Lemma136c.Alt19_16c 3 r (barOf 3 K) (autBar 3 (Lemma136c.bStarOf B L D b) K)

theorem iiHardCases_of_cases (hAlt : IIHardCaseAlt) (hLie : IIHardCaseLie) : Lemma136c.IIHardCases := by
  intro G _ _ m B M E A D T L h hN d hd hd1 hfix b B1 hP hS r hr hEk K hK hnot hBsN hcent halt
  rcases halt with ⟨m', r', ha⟩ | hb | hc
  · exact hAlt G m h hN hd hd1 hfix b B1 hP hS r hr hEk K hK hnot hBsN hcent ⟨m', r', ha⟩
  · exact absurd hb.1 (by norm_num)
  · exact hLie G m h hN hd hd1 hfix b B1 hP hS r hr hEk K hK hnot hBsN hcent hc

theorem iiHardInput_of_inputs (hI191 : Lemma129.Input19_1_two) (hI1916 : Input19_16Three)
    (hP95 : Prop95) (h111 : Prop111Statement) (h121 : Prop121_of_cexStatement)
    (hcomp : Sec13_compStatement) (hO2 : Cex134_O2Statement) (h121c : Prop121_corStatement)
    (h133 : Lemma133Statement) (h135 : Lemma135_iStatement) (h91 : Lemma91ii)
    (h912 : Lemma912Statement) (hAlt : IIHardCaseAlt) (hLie : IIHardCaseLie) :
    Lemma136.IIHardInput :=
  iiHard_of_inputs' hI191 hI1916
    (iiHardReduction_of_inputs hP95 h111 h121 hcomp hO2 h121c h133 h135 h91 h912)
    (iiHardCases_of_cases hAlt hLie)

theorem p1BarInput_of_inputs' (h135 : Lemma135_iStatement) (h912 : Lemma912Statement)
    (hO2 : Cex134_O2Statement) (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement) (hCore : Lemma136b.P1GCore) :
    Lemma136.P1BarInput :=
  Lemma136b.p1BarInput_of_inputs h135 (p1GLift_of_inputs h912 hO2 hP95 h111 h121 hcomp) hCore

theorem lemma136_of_inputs' (hI191 : Lemma129.Input19_1_two) (hI1916 : Input19_16Three)
    (hP95 : Prop95) (h111 : Prop111Statement) (h121 : Prop121_of_cexStatement)
    (hcomp : Sec13_compStatement) (hO2 : Cex134_O2Statement) (h121c : Prop121_corStatement)
    (h133 : Lemma133Statement) (h135 : Lemma135_iStatement) (h91 : Lemma91ii)
    (h912 : Lemma912Statement) (hCore : Lemma136b.P1GCore) (hAlt : IIHardCaseAlt)
    (hLie : IIHardCaseLie) : Lemma136Statement :=
  lemma136_of_inputs hP95 h111 h121 hcomp input22_3_2_holds
    (p1BarInput_of_inputs' h135 h912 hO2 hP95 h111 h121 hcomp hCore) hO2 h121c
    (iiHardInput_of_inputs hI191 hI1916 hP95 h111 h121 hcomp hO2 h121c h133 h135 h91 h912 hAlt hLie)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims136

end
