module

public import CFSG.LocalAnalysis.RankThreeTheoremC.K1NoBMDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConfigU3
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt
import CFSG.LocalAnalysis.RankThreeTheoremC.D1BetaRank3
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfigAt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem not_d1CzSP_of_config3 {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hcfg : D1ComponentConfig3 p P M H R Rbar) (z : G) : ¬ D1CzSP p z := by
  have hp : p.Prime := hcfg.ext.prime
  have h1 : Open.pRank p (Subgroup.centralizer ({z} : Set G)) ≤ Open.pRank p (⊤ : Subgroup G) :=
    pRank_mono p hp le_top
  have h2 := pRank_sylow_eq_globalRank p hp P
  have h3 := hcfg.pRank_eq_three
  intro h
  unfold D1CzSP at h
  omega

theorem d1CaseTwoNoSP_of_config3 {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hcfg : D1ComponentConfig3 p P M H R Rbar) : D1CaseTwoNoSP p M H R :=
  fun _ _ _ z _ _ _ _ => not_d1CzSP_of_config3 hcfg (z : G)

@[expose] def D1CaseTwoNoCentral (p : ℕ) (P : Sylow p G) (M H R : Subgroup G) : Prop :=
  ∀ z : H, D1CaseTwoCand p M H R z →
    ¬ ∃ m ∈ M, (P : Subgroup G).map (MulAut.conj m).toMonoidHom ≤
      Subgroup.centralizer ({(z : G)} : Set G)

structure D1CaseTwoData3 (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)) : Prop where
  cfg : D1ComponentConfig3 p P M H R Rbar
  cyclic : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
    IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
      Subgroup (H ⧸ primeComplementCore (G := H) p))
  noCentral : D1CaseTwoNoCentral p P M H R

theorem D1CaseTwoData3.rank {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} (hd : D1CaseTwoData3 p P M H R Rbar) :
    Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = 3 :=
  hd.cfg.pRank_rbar_eq_three

@[expose] def D1CaseTwoCentral3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p))) →
    ∀ z : H, D1CaseTwoCand p M H R z →
      (∃ m ∈ M, (P : Subgroup G).map (MulAut.conj m).toMonoidHom ≤
        Subgroup.centralizer ({(z : G)} : Set G)) → False

theorem d1CaseTwoCentral3_of_caseTwo3 (h : D1CaseTwo3 G) : D1CaseTwoCentral3 G :=
  fun p P M H R Rbar hcfg hcyc _ _ _ => h p P M H R Rbar hcfg hcyc

theorem d1CaseTwo3_of_data3 (hcen : D1CaseTwoCentral3 G)
    (h : ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
      (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)),
      D1CaseTwoData3 p P M H R Rbar → False) : D1CaseTwo3 G := by
  intro p P M H R Rbar hcfg hcyc
  by_cases hz : ∃ z : H, D1CaseTwoCand p M H R z ∧ ∃ m ∈ M,
      (P : Subgroup G).map (MulAut.conj m).toMonoidHom ≤
        Subgroup.centralizer ({(z : G)} : Set G)
  · obtain ⟨z, hzc, hzm⟩ := hz
    exact hcen p P M H R Rbar hcfg hcyc z hzc hzm
  · exact h p P M H R Rbar ⟨hcfg, hcyc, fun z hzc hzm => hz ⟨z, hzc, hzm⟩⟩

omit [Finite G] in
theorem central_of_eq_sylow {p : ℕ} {P : Sylow p G} {M R : Subgroup G} {z : G}
    (hRz : R ≤ Subgroup.centralizer ({z} : Set G)) (hRP : R = (P : Subgroup G))
    (hM : (1 : G) ∈ M) :
    ∃ m ∈ M, (P : Subgroup G).map (MulAut.conj m).toMonoidHom ≤
      Subgroup.centralizer ({z} : Set G) := by
  refine ⟨1, hM, ?_⟩
  have h1 : (P : Subgroup G).map (MulAut.conj (1 : G)).toMonoidHom = P := by
    ext x; simp
  rw [h1, ← hRP]
  exact hRz

omit [Finite G] in
theorem hnTQ_of_not_central {p : ℕ} {P : Sylow p G} {M R : Subgroup G} {z : G}
    (hnc : ¬ ∃ m ∈ M, (P : Subgroup G).map (MulAut.conj m).toMonoidHom ≤
        Subgroup.centralizer ({z} : Set G)) :
    ∀ m ∈ M, ∀ T : Sylow p (Subgroup.centralizer ({z} : Set G)),
      R ≤ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype →
      (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ≤
        (P : Subgroup G).map (MulAut.conj m).toMonoidHom →
      (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ≠
        (P : Subgroup G).map (MulAut.conj m).toMonoidHom := by
  intro m hm T _ _ heq
  exact hnc ⟨m, hm, heq ▸ Subgroup.map_subtype_le _⟩

theorem D1ComponentConfig3.pRank_inf_le_three {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hcfg : D1ComponentConfig3 p P M H R Rbar) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    Open.pRank q (H ⊓ M) ≤ 3 :=
  (pRank_mono q hq inf_le_right).trans
    ((local_pRank_le_evenRank q hq hq2 M hcfg.loc.isCoreMaxLocal.1.1).trans hcfg.glob.rank.le)

theorem D1CaseTwoData3.ne_sylow {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} (hd : D1CaseTwoData3 p P M H R Rbar)
    {z : H} (hz : D1CaseTwoCand p M H R z) : R ≠ (P : Subgroup G) := by
  intro h
  obtain ⟨-, -, -, -, -, hRz, -⟩ := id hz
  exact hd.noCentral z hz (central_of_eq_sylow hRz h M.one_mem)

theorem _root_.CFSG.AGLEmbedding.ReducedNongeneration.pRank_mulAut_le_two_of_isCyclic3
    {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}
    (h : ReducedNongeneration p X R X₀) (hX : CatalogSimpleSections X) (hOut : KFactOutCyclic)
    {L : Subgroup X} (hL : IsComponentOf L ⊤)
    (hcyc : IsCyclic ((R : Subgroup X) ⊓ L : Subgroup X)) :
    Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ 2 := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨hsimple, hnonab, hcat, T, -, hTcyc⟩ := h.isSimpleGroup_of_isCyclic hX hL hcyc
  exact pRank_mulAut_le_two_of_isCyclic_sylow h.prime (h.center_eq_bot_of_isCyclic hL hcyc) T
    hTcyc (hOut L hsimple hnonab hcat p h.prime h.ne_two T hTcyc)

theorem _root_.CFSG.AGLEmbedding.ReducedNongeneration.cycAutRankLeTwo_of_kFactOutCyclic
    {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}
    (h : ReducedNongeneration p X R X₀) (hX : CatalogSimpleSections X) (hOut : KFactOutCyclic) :
    CycAutRankLeTwo p X R :=
  fun _ hL hcyc => h.pRank_mulAut_le_two_of_isCyclic3 hX hOut hL hcyc

theorem D1CaseTwoData3.toAt {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} (hd : D1CaseTwoData3 p P M H R Rbar) :
    D1CaseTwoDataAt p P M H R Rbar :=
  ⟨hd.cfg.toU, hd.cyclic, hd.rank, fun _ hz _ => hd.ne_sylow hz⟩

theorem kFactCycAut_of_kFactOutCyclic (hOut : KFactOutCyclic) : KFactCycAut :=
  fun _ _ _ _ _ _ h hX => h.cycAutRankLeTwo_of_kFactOutCyclic hX hOut

@[expose] def KFactCaseTwoInvNoBM : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → NotBM K → ∀ p : ℕ, (p = 3 ∨ p = 5) → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      Open.pRank p (⊤ : Subgroup K) ≤ 2 →
      ∀ (A : Subgroup K) (L : Type) [Group L], IsCaseTwoGroup p L →
        ∀ f : A →* L, ¬ Function.Surjective f

structure D1CaseTwoInv3 (G : Type) [Group G] [Finite G] : Prop where
  inv : KFactCaseTwoInvNoBM
  noSec : NoExcludedSection3 G

theorem D1CaseTwoInv3.notBM (h : D1CaseTwoInv3 G) {H : Subgroup G} {N : Subgroup H} [N.Normal]
    {K : Subgroup (H ⧸ N)} (hq : Open.IsQuasisimple K) (hZ : Subgroup.center K = ⊥) :
    NotBM ↥K :=
  have h1 : NotSecExcl3 ↥K := notSecExcl3_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
    (h.noSec H N K hq)
  ⟨h1 .B (by simp [sectionExcludedNames3]), h1 .M (by simp [sectionExcludedNames3])⟩

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoInv3.toIn (h : D1CaseTwoInv3 G) : KFactCaseTwoInvIn G :=
  fun _ _ _ K hq hZ hs hn hc p hp T hT hΓ hr A L _ hL f =>
    h.inv K hs hn hc (h.notBM hq hZ) p hp T hT hΓ hr A L hL f

theorem D1ComponentConfig3.centralizer_not_le (hcfg : D1ComponentConfig3 p P M H R Rbar)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hLX : ¬ L ≤ d1X0 p M H) {z : G}
    (hzH : z ∈ H) (hzp : orderOf z = p)
    (hzL : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩ ∈
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p))) :
    ¬ Subgroup.centralizer ({z} : Set G) ≤ M :=
  hcfg.toU.centralizer_not_le hLX hzH hzp hzL

theorem D1ComponentConfig3.b0_of_shape3 (hcfg : D1ComponentConfig3 p P M H R Rbar) {z : G}
    (hzp : orderOf z = p) (hzR : z ∈ R) (hRz : R ≤ Subgroup.centralizer ({z} : Set G))
    (hCM : ¬ Subgroup.centralizer ({z} : Set G) ≤ M)
    (hshape : D1CzShape p P M R z)
    (hnTQ : ∀ m ∈ M, ∀ T : Sylow p (Subgroup.centralizer ({z} : Set G)),
      R ≤ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype →
      (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ≤
        (P : Subgroup G).map (MulAut.conj m).toMonoidHom →
      (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ≠
        (P : Subgroup G).map (MulAut.conj m).toMonoidHom) :
    D1CzB0 p R z ∧ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≠ ⊥ ∧ D1CzEven p z :=
  hcfg.toU.b0_of_shape hzp hzR hRz hCM hshape hnTQ

end CFSG.LocalAnalysis.RankThreeTheoremC
