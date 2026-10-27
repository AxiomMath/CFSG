module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenFiveSetting
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34SylowStructure
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ChainNine
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneSetup
import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
import CFSG.GroupTheory.NormalizerInfCentralizer
import CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.GroupTheory.CentralizerSup
import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VSylow
public import CFSG.Quasithin.Background.A3Structure318Star

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M H E Q J : Subgroup G}

private theorem center_le_of_normal_ne_bot {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] (hH : IsPGroup p H) {N : Subgroup H} [N.Normal] (hN : N ≠ ⊥)
    (hZ : Nat.card ↥(Subgroup.center H) = p) : Subgroup.center H ≤ N := by
  have hne : N ⊓ Subgroup.center H ≠ ⊥ :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter.inf_center_ne_bot
      hH N hN
  have hdvd : Nat.card ↥(N ⊓ Subgroup.center H) ∣ p := by
    simpa [hZ] using Subgroup.card_dvd_of_le
      (inf_le_right : N ⊓ Subgroup.center H ≤ Subgroup.center H)
  have hcard : Nat.card ↥(N ⊓ Subgroup.center H) = p := by
    rcases (Nat.dvd_prime Fact.out).mp hdvd with h1 | hp
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hne
    · exact hp
  have heq : N ⊓ Subgroup.center H = Subgroup.center H :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcard, hZ])
  exact heq.ge.trans inf_le_left

private theorem centralizer_ne_top (h : S14Choice G M H E Q J) {A₀ : Subgroup G}
    (hA0card : Nat.card A₀ = 3) : Subgroup.centralizer (A₀ : Set G) ≠ ⊤ := by
  haveI : IsSimpleGroup G := h.cstar.simple
  intro htop
  have hA0ne : A₀ ≠ ⊥ := by
    intro hbot
    rw [hbot] at hA0card
    simp at hA0card
  have hA0center : A₀ ≤ Subgroup.center G := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (A₀ : Set G) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg x hx).symm
  have hZne : Subgroup.center G ≠ ⊥ := by
    intro hbot
    exact hA0ne (le_bot_iff.mp (hbot ▸ hA0center))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hbot | htop'
  · exact hZne hbot
  · have hcomm : IsMulCommutative G := Subgroup.center_eq_top_iff.mp htop'
    obtain ⟨a, b, hab⟩ := h.cstar.nonab
    exact hab (hcomm.is_comm.comm a b)

private theorem centralizer_not_le (h : S14Choice G M H E Q J) (hpre : PreambleTypes M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) {A₀ : Subgroup G} (hA0Q : A₀ ≤ Q)
    (hA0card : Nat.card A₀ = 3) (hA0J : ⁅A₀, J⁆ ≤ CFSG.Open.pCoreOf 2 J) :
    ¬ Subgroup.centralizer (A₀ : Set G) ≤ M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := Subgroup.centralizer (A₀ : Set G) with hCdef
  set D : Subgroup G := (CFSG.pPrimeCore 3 ↥J).map J.subtype with hDdef
  have hDcop : ¬ 3 ∣ Nat.card D := by
    rw [show Nat.card D = Nat.card (CFSG.pPrimeCore 3 ↥J) from
      Subgroup.card_map_of_injective J.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hED : E ≤ Subgroup.normalizer (D : Set G) := by
    intro e he
    rw [hDdef]
    exact CFSG.ABGLocalTools.mem_normalizer_map_subtype_of_characteristic
      (M := J) (C := CFSG.pPrimeCore 3 ↥J) (h.Q_le_normalizer_J hpre hU (h.E_le_Q he))
  have hDM : D ≤ M := h.hypCGen.invariant_coprime_le_M hDcop hED
  have hoTwo : CFSG.Open.pCoreOf 2 J ≤ D := by
    rw [hDdef, CFSG.openPCoreOf_eq_map_pCore]
    exact Subgroup.map_mono
      (CFSG.Quasithin.A318.pCore_two_le_pPrimeCore (p := 3) (by norm_num))
  have hA0D : ⁅A₀, J⁆ ≤ D := hA0J.trans hoTwo
  have hA0p : IsPGroup 3 A₀ :=
    IsPGroup.of_card (n := 1) (by rw [hA0card]; norm_num)
  have hDJ : D ≤ J := Subgroup.map_subtype_le _
  have hJN : J ≤ Subgroup.normalizer (D : Set G) := by
    intro j hj
    rw [hDdef]
    exact CFSG.ABGLocalTools.mem_normalizer_map_subtype_of_characteristic
      (M := J) (C := CFSG.pPrimeCore 3 ↥J) (Subgroup.le_normalizer hj)
  have hA0ND : A₀ ≤ Subgroup.normalizer (D : Set G) := by
    intro a ha
    rw [hDdef]
    exact CFSG.ABGLocalTools.mem_normalizer_map_subtype_of_characteristic
      (M := J) (C := CFSG.pPrimeCore 3 ↥J) (h.Q_le_normalizer_J hpre hU (hA0Q ha))
  have hcover : ∀ x ∈ J, ∃ y ∈ J ⊓ C, ∃ d ∈ D, x = y * d := by
    intro x hx
    obtain ⟨d, hdD, hxdJ, hxdC⟩ :=
      exists_coset_translate_centralizer (J := J) (B := A₀) (D := D)
        hA0p hDJ hJN hA0ND hDcop hA0D (x := ⟨x, hx⟩)
    exact ⟨(x : G) * d, ⟨hxdJ, hxdC⟩, d⁻¹, D.inv_mem hdD, by group⟩
  intro hCM
  apply h.not_le_M hL
  intro x hx
  obtain ⟨y, hy, d, hd, rfl⟩ := hcover x hx
  exact M.mul_mem (hCM hy.2) (hDM hd)

private theorem centralizer_ne_top_and_not_le (h : S14Choice G M H E Q J)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    {A₀ : Subgroup G} (hA0Q : A₀ ≤ Q) (hA0card : Nat.card A₀ = 3)
    (hA0J : ⁅A₀, J⁆ ≤ CFSG.Open.pCoreOf 2 J) :
    Subgroup.centralizer (A₀ : Set G) ≠ ⊤ ∧
      ¬ Subgroup.centralizer (A₀ : Set G) ≤ M :=
  ⟨centralizer_ne_top h hA0card, centralizer_not_le h hpre hU hL hA0Q hA0card hA0J⟩

private theorem inf_J_le_centralizer (h : S14Choice G M H E Q J) (hU : NineNineOneAt M)
    {A₀ : Subgroup G} (hA0Q : A₀ ≤ Q)
    (hA0J : ⁅A₀, J⁆ ≤ CFSG.Open.pCoreOf 2 J) :
    Q ⊓ J ≤ Subgroup.centralizer (A₀ : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO2p : IsPGroup 2 (CFSG.Open.pCoreOf 2 J) := by
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥J)).map J.subtype
  have hQ3 : IsPGroup 3 Q := h.sylow.isPGroup
  have hdisj : CFSG.Open.pCoreOf 2 J ⊓ Q = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ hO2p hQ3)
  have hle1 : ⁅A₀, Q ⊓ J⁆ ≤ CFSG.Open.pCoreOf 2 J :=
    (Subgroup.commutator_mono le_rfl inf_le_right).trans hA0J
  have hle2 : ⁅A₀, Q ⊓ J⁆ ≤ Q :=
    (Subgroup.commutator_mono hA0Q inf_le_left).trans (Subgroup.commutator_le_self Q)
  have hbot : ⁅A₀, Q ⊓ J⁆ = ⊥ := by
    rw [eq_bot_iff, ← hdisj]
    exact le_inf hle1 hle2
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Q ⊓ J) (H₂ := A₀)).mp
    (by rwa [Subgroup.commutator_comm])

private theorem center_inf_J_eq_center
    (h : S14Choice G M H E Q J) (hA : TypeA M H) (hpre : PreambleTypes M)
    (hU : NineNineOneAt M) (h142 : FourteenTwoCaseOneAt M) :
    (Subgroup.center ↥(Q ⊓ J)).map (Q ⊓ J).subtype =
      (Subgroup.center ↥Q).map Q.subtype := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Subgroup G := Q ⊓ J
  obtain ⟨hScard, -, -, hZScardMap⟩ :=
    IsKComp.sylow_three_structure (M := M) (N := H) h.isKComp
      (Or.inl (h.isSL34Star_of_typeA hpre hU hA)) (h.isSylowOf_inf_J hpre hU)
  have hna : ∃ a b : ↥S, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    haveI : IsMulCommutative ↥S := ⟨⟨fun a b => hcon a b⟩⟩
    have htop : Subgroup.center ↥S = ⊤ := Subgroup.center_eq_top
    have h27 : Nat.card ↥(Subgroup.center ↥S) = 27 := by
      rw [htop]
      simpa [S] using hScard
    have h3 : Nat.card ↥(Subgroup.center ↥S) = 3 := by
      rw [← Subgroup.card_map_of_injective S.subtype_injective]
      exact hZScardMap
    omega
  have hcomm := CFSG.HardMathSupport.Solomon.Coordinator.i112v_commutator_eq_center
    (R := ↥S) hScard hna
  have hZSeq : (Subgroup.center ↥S).map S.subtype = ⁅S, S⁆ := by
    rw [← hcomm, _root_.commutator_def, Subgroup.map_commutator]
    congr 1
    · simpa [MonoidHom.range_eq_map] using (S.range_subtype : S.subtype.range = S)
    · simpa [MonoidHom.range_eq_map] using (S.range_subtype : S.subtype.range = S)
  have h142Q := h142 H E Q J h hA
  have hle : (Subgroup.center ↥S).map S.subtype ≤
      (Subgroup.center ↥Q).map Q.subtype := by
    rw [hZSeq]
    calc ⁅S, S⁆ ≤ ⁅Q, Q⁆ := Subgroup.commutator_mono inf_le_left inf_le_left
      _ = (Subgroup.center ↥Q).map Q.subtype := h142Q.1.2.2.1
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hZScardMap, h142Q.1.2.2.2]

private theorem center_not_le_centralizer {p : ℕ} (hpp : p.Prime) {A₀ C P F : Subgroup G}
    (hA0Q : A₀ ≤ Q) (hPC : P ≤ C) (hZQleC : (Subgroup.center ↥Q).map Q.subtype ≤ C)
    (hcent : C ⊓ Subgroup.centralizer (F : Set G) ≤
      (CFSG.pPrimeCore p ↥C).map C.subtype)
    (hPp : IsPGroup p P)
    (hZnorm : (Subgroup.center ↥Q).map Q.subtype ≤ Subgroup.normalizer (P : Set G))
    (hZcomm : ⁅(Subgroup.center ↥Q).map Q.subtype, P⁆ ≠ ⊥) :
    ¬ (Subgroup.center ↥Q).map Q.subtype ≤ Subgroup.centralizer (F : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hpp⟩
  let Z : Subgroup G := (Subgroup.center ↥Q).map Q.subtype
  let O : Subgroup G := (CFSG.pPrimeCore p ↥C).map C.subtype
  intro hZle
  have hZleO : Z ≤ O := (le_inf hZQleC hZle).trans hcent
  have hOnorm : C ≤ Subgroup.normalizer (O : Set G) := by
    intro c hc
    exact CFSG.ABGLocalTools.mem_normalizer_map_subtype_of_characteristic
      (M := C) (C := CFSG.pPrimeCore p ↥C) (Subgroup.le_normalizer hc)
  have hOcop : ¬ p ∣ Nat.card O := by
    rw [show Nat.card O = Nat.card (CFSG.pPrimeCore p ↥C) from
      Subgroup.card_map_of_injective C.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd hpp).mp CFSG.pPrimeCore_coprime_card
  have hPinfO : P ⊓ O = ⊥ := by
    by_contra hne
    have hP'p : IsPGroup p ↥(P ⊓ O) := hPp.to_le inf_le_left
    have hpdvd : p ∣ Nat.card ↥(P ⊓ O) := by
      rcases hP'p.card_eq_or_dvd with h1 | hd
      · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hne
      · exact hd
    exact hOcop (hpdvd.trans (Subgroup.card_dvd_of_le
      (inf_le_right : P ⊓ O ≤ O)))
  have hZP : ⁅Z, P⁆ ≤ P :=
    (Subgroup.le_normalizer_iff_commutator_le_right).mp hZnorm
  have hOP : ⁅O, P⁆ ≤ O :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp (hPC.trans hOnorm)
  have hZPO : ⁅Z, P⁆ ≤ P ⊓ O :=
    le_inf hZP ((Subgroup.commutator_mono hZleO le_rfl).trans hOP)
  have hbot : ⁅Z, P⁆ = ⊥ := by
    rw [eq_bot_iff, ← hPinfO]
    exact hZPO
  exact hZcomm (by simpa [Z] using hbot)

private theorem inf_centralizer_eq_bot_of_center_eq {S Z F : Subgroup G}
    (hSp : IsPGroup 3 ↥S) (hZcard : Nat.card ↥(Subgroup.center ↥S) = 3)
    (hSF : S ≤ Subgroup.normalizer (F : Set G))
    (hZeq : (Subgroup.center ↥S).map S.subtype = Z)
    (hZnot : ¬ Z ≤ Subgroup.centralizer (F : Set G)) :
    S ⊓ Subgroup.centralizer (F : Set G) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  have hNnorm : ((S ⊓ Subgroup.centralizer (F : Set G)).subgroupOf S).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer
      (show S ⊓ Subgroup.centralizer (F : Set G) ≤ S from inf_le_left)]
    intro s hs
    exact CFSG.GroupTheory.mem_normalizer_inf_centralizer (L := F) (Q := S)
      (hSF hs) (Subgroup.le_normalizer hs)
  have hNne : (S ⊓ Subgroup.centralizer (F : Set G)).subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hne
    have hmap := congrArg (Subgroup.map S.subtype) hbot
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left,
      Subgroup.map_bot] at hmap
    exact hmap
  have hZle : Subgroup.center ↥S ≤
      (S ⊓ Subgroup.centralizer (F : Set G)).subgroupOf S :=
    center_le_of_normal_ne_bot hSp hNne hZcard
  have hZle' : (Subgroup.center ↥S).map S.subtype ≤
      S ⊓ Subgroup.centralizer (F : Set G) := by
    have hmap := Subgroup.map_mono hZle (f := S.subtype)
    have h1 : ((S ⊓ Subgroup.centralizer (F : Set G)).subgroupOf S).map S.subtype =
        S ⊓ Subgroup.centralizer (F : Set G) := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
    rw [h1] at hmap
    exact hmap
  exact hZnot (hZeq ▸ (hZle'.trans inf_le_right))

private theorem branch_one_inf_centralizer_eq_bot {F : Subgroup G}
    (hEea : IsElemAbelian 3 E) (hEM : E ≤ M)
    (hEF : E ≤ Subgroup.normalizer (F : Set G)) (hKM : ¬ F ≤ M)
    (hgamma : CFSG.Open.rankThreeGamma 1 3 E ≤ M) :
    E ⊓ Subgroup.centralizer (F : Set G) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  obtain ⟨e, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have heE : (e : G) ∈ E := e.2.1
  have heC : (e : G) ∈ Subgroup.centralizer (F : Set G) := e.2.2
  have he3 : (e : G) ^ 3 = 1 := hEea.2 (e : G) heE
  have heGne : (e : G) ≠ 1 := fun h => he1 (Subtype.ext h)
  have heord : orderOf (e : G) = 3 := orderOf_eq_prime he3 heGne
  have hzelem : IsElemAbelian 3 (Subgroup.zpowers (e : G)) :=
    CFSG.Open.isElemAbelian_zpowers he3
  have hzcard : Nat.card ↥(Subgroup.zpowers (e : G)) = 3 ^ 1 := by
    rw [Nat.card_zpowers, heord]
    norm_num
  have hzle : Subgroup.zpowers (e : G) ≤ E := Subgroup.zpowers_le.mpr heE
  have hpR : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers (e : G)) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl hzelem hzcard
  have hN : Subgroup.normalizer (Subgroup.zpowers (e : G) : Set G) ≤ M :=
    (CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff 1 3 E M).mp hgamma
      (Subgroup.zpowers (e : G)) hzle hpR
  have hFcent : F ≤ Subgroup.centralizer (Subgroup.zpowers (e : G) : Set G) := by
    rw [CFSG.centralizer_zpowers_eq_centralizer_singleton]
    intro f hf
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp heC f hf)
  exact hKM (hFcent.trans
    ((Subgroup.centralizer_le_normalizer (Subgroup.zpowers (e : G) : Set G)).trans hN))

private theorem false_of_branch_one {p : ℕ} {F : Subgroup G}
    (hEea : IsElemAbelian 3 E) (hEcard : Nat.card E = 9) (hEM : E ≤ M)
    (hEF : E ≤ Subgroup.normalizer (F : Set G))
    (hK : CFSG.IsQuasisimple ↥F)
    (hlist : CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup p
      (↥F ⧸ Subgroup.center ↥F))
    (hKM : ¬ F ≤ M)
    (hPsyl : ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P F ∧
      ∀ U : Subgroup G, U ≤ P → U ≠ ⊥ → F ⊓ Subgroup.normalizer (U : Set G) ≤ F ⊓ M)
    (hgamma : CFSG.Open.rankThreeGamma 1 3 E ≤ M)
    (hpp : p.Prime) (hp5 : 5 ≤ p) (hK9 : KFactNineFourAutM) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYne : F ⊓ M ≠ F := by
    intro heq
    exact hKM (heq ▸ inf_le_right)
  have hEY : E ≤ Subgroup.normalizer (F ⊓ M : Set G) :=
    (le_inf hEF (hEM.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hdisj : E ⊓ Subgroup.centralizer (F : Set G) = ⊥ :=
    branch_one_inf_centralizer_eq_bot hEea hEM hEF hKM hgamma
  obtain ⟨r, hrE, hr1, hr⟩ := (hK9 p hpp hp5 G F (F ⊓ M) E hK hlist inf_le_left
    hYne hPsyl hEF hEY hdisj hEea.2 (by omega)).2
  have hr3 : r ^ 3 = 1 := hEea.2 r hrE
  have hro : orderOf r = 3 := orderOf_eq_prime hr3 hr1
  have hzelem : IsElemAbelian 3 (Subgroup.zpowers r) :=
    CFSG.Open.isElemAbelian_zpowers hr3
  have hzcard : Nat.card ↥(Subgroup.zpowers r) = 3 ^ 1 := by
    rw [Nat.card_zpowers, hro]
    norm_num
  have hzle : Subgroup.zpowers r ≤ E := Subgroup.zpowers_le.mpr hrE
  have hpR : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers r) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl hzelem hzcard
  have hN : Subgroup.normalizer (Subgroup.zpowers r : Set G) ≤ M :=
    (CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff 1 3 E M).mp hgamma
      (Subgroup.zpowers r) hzle hpR
  have hcle : F ⊓ Subgroup.centralizer ({r} : Set G) ≤ F ⊓ M := by
    have hle : Subgroup.centralizer ({r} : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers r : Set G) := by
      rw [← CFSG.centralizer_zpowers_eq_centralizer_singleton r]
      exact Subgroup.centralizer_le_normalizer (Subgroup.zpowers r : Set G)
    exact le_inf inf_le_left (inf_le_right.trans (hle.trans hN))
  exact hr hcle

private theorem false_of_branch_two
    {p : ℕ} (h : S14Choice G M H E Q J) (hA : TypeA M H) (hpre : PreambleTypes M)
    (hU : NineNineOneAt M) (h142 : FourteenTwoCaseOneAt M) {A₀ C F P : Subgroup G}
    (hA0Q : A₀ ≤ Q) (hSleC : Q ⊓ J ≤ C)
    (hZQleC : (Subgroup.center ↥Q).map Q.subtype ≤ C)
    (hK : CFSG.IsQuasisimple ↥F)
    (hlist : CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup p
      (↥F ⧸ Subgroup.center ↥F))
    (hKM : ¬ F ≤ M) (hKnorm : C ⊓ M ≤ Subgroup.normalizer (F : Set G))
    (hcent : C ⊓ Subgroup.centralizer (F : Set G) ≤
      (CFSG.pPrimeCore p ↥C).map C.subtype)
    (hPsyl : ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P F ∧
      ∀ U : Subgroup G, U ≤ P → U ≠ ⊥ → F ⊓ Subgroup.normalizer (U : Set G) ≤ F ⊓ M)
    (hPC : P ≤ C) (hPp : IsPGroup p P)
    (hZnorm : (Subgroup.center ↥Q).map Q.subtype ≤ Subgroup.normalizer (P : Set G))
    (hZcomm : ⁅(Subgroup.center ↥Q).map Q.subtype, P⁆ ≠ ⊥)
    (hpp : p.Prime) (hp5 : 5 ≤ p) (hK9 : KFactNineFourAutM) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Subgroup G := Q ⊓ J
  have hSM : S ≤ M := inf_le_left.trans (h.Q_le_M hU)
  obtain ⟨hScard, hSexp, -, hZScardMap⟩ :=
    IsKComp.sylow_three_structure (M := M) (N := H) h.isKComp
      (Or.inl (h.isSL34Star_of_typeA hpre hU hA)) (h.isSylowOf_inf_J hpre hU)
  have hScardS : Nat.card ↥S = 27 := by simpa [S] using hScard
  have hSp : IsPGroup 3 ↥S := IsPGroup.of_card (n := 3) (by rw [hScardS]; norm_num)
  have hZScard : Nat.card ↥(Subgroup.center ↥S) = 3 := by
    rw [← Subgroup.card_map_of_injective S.subtype_injective]
    exact hZScardMap
  have hZeq := center_inf_J_eq_center h hA hpre hU h142
  have hSF : S ≤ Subgroup.normalizer (F : Set G) :=
    (le_inf hSleC hSM).trans hKnorm
  have hSY : S ≤ Subgroup.normalizer (F ⊓ M : Set G) :=
    (le_inf hSF (hSM.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hZnot : ¬ (Subgroup.center ↥Q).map Q.subtype ≤
      Subgroup.centralizer (F : Set G) :=
    center_not_le_centralizer hpp hA0Q hPC hZQleC hcent hPp hZnorm hZcomm
  have hSdisj : S ⊓ Subgroup.centralizer (F : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_center_eq hSp hZScard hSF hZeq hZnot
  have hYne : F ⊓ M ≠ F := by
    intro heq
    exact hKM (heq ▸ inf_le_right)
  have hres := hK9 p hpp hp5 G F (F ⊓ M) S hK hlist inf_le_left hYne hPsyl
    hSF hSY hSdisj hSexp (by omega)
  exact absurd hres.1 (by omega)

theorem fourteenFiveCaseOneAt_of
    (hpre : PreambleTypes M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (h142 : FourteenTwoCaseOneAt M) (h1 : NineFourTwoSigmaGen)
    (h2 : NineTwelveOneSigmaStrong) (h1441 : FourteenFourOneCaseOneAt M)
    (hK9 : KFactNineFourAutM) : FourteenFiveCaseOneAt M := by
  intro H E Q J h hA p hp A₀ hA0Q hA0card h2C hA0J hbranch
  classical
  obtain ⟨hCtop, hCM⟩ :=
    centralizer_ne_top_and_not_le h hpre hU hL hA0Q hA0card hA0J
  have hset := h.caseOne_setting_centralizer hA h1441 h1 h2 hp hCtop hCM h2C
  obtain ⟨hp5, hK, hlist, hKM, hKnorm, hPsyl, hcent⟩ := hset
  let C : Subgroup G := Subgroup.centralizer (A₀ : Set G)
  let F : Subgroup G := kSub p M C
  have hpp : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  haveI : Fact p.Prime := ⟨hpp⟩
  rcases hbranch with hA0E | ⟨P, hPM, hPp, hZnorm, hZcomm⟩
  · have hEC : E ≤ C := by
      refine (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := E) (H₂ := A₀)).mp ?_
      rwa [Subgroup.commutator_comm]
    have hEF : E ≤ Subgroup.normalizer (F : Set G) :=
      (le_inf hEC h.hypCGen.E_le_M).trans hKnorm
    exact (false_of_branch_one (p := p) (F := F) h.elem h.card h.hypCGen.E_le_M
      hEF hK hlist hKM hPsyl h.hypCGen.gamma hpp hp5 hK9).elim
  · have hSleC : Q ⊓ J ≤ C :=
      inf_J_le_centralizer (A₀ := A₀) h hU hA0Q hA0J
    have hZQleC : (Subgroup.center ↥Q).map Q.subtype ≤ C := by
      intro z hz
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hz
      change (q : G) ∈ Subgroup.centralizer (A₀ : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hq ⟨a, hA0Q ha⟩)
    have hPC : P ≤ C := hPM.trans inf_le_right
    exact (false_of_branch_two h hA hpre hU h142 hA0Q hSleC hZQleC hK hlist hKM
      hKnorm hcent hPsyl hPC hPp hZnorm hZcomm hpp hp5 hK9).elim

theorem fourteenFiveCaseOneGen_of
    (h142 : FourteenTwoCaseOneGen) (h1210 : TwelveTenThree) (h1211 : TwelveElevenGen)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (h96 : NineSixMoreoverGen) (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen)
    (h1 : NineFourTwoSigmaGen) (h2 : NineTwelveOneSigmaStrong)
    (h1441 : FourteenFourOneCaseOneGen) (hK9 : KFactNineFourAutM) :
    FourteenFiveCaseOneGen := by
  intro G _ _ M H E Q J h hA
  have hU : NineNineOneAt M := nineNineOneAt_of_twelveEleven h991 h1211
  have hpre : PreambleTypes M :=
    preambleTypes_of h1211 h.cstar h.maxLocal h.sigma_nonempty
      (preambleFiveTypes_of h1210 h97 h96 h.cstar h.maxLocal h.sigma_nonempty hU)
  have hL : PLayerNotLeAt M := pLayerNotLeAt_of h1211 h1210 h97 hU
  exact fourteenFiveCaseOneAt_of hpre hU hL (h142 G M) h1 h2 (h1441 G M) hK9
    H E Q J h hA

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
