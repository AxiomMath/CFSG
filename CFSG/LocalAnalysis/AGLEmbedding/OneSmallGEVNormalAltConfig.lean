module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltDefs
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitorReduced
import CFSG.LocalAnalysis.AGLEmbedding.OneLiePerfect
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszAux
import CFSG.LocalAnalysis.AGLEmbedding.UPrimeComponents

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

structure D1SmallAltConfig (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (z : G) : Prop where
  data : D1OneSmallData p P M H R Rbar K
  elt : D1SmallCZElt p H R K z
  ia : D1SmallIa p H K
  b0 : D1CzB0 p R z
  cz_le : Subgroup.centralizer ({z} : Set G) ≤ H
  normal : ∀ hzH : z ∈ H,
    (Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩)).Normal
  prime57 : p = 5 ∨ p = 7
  alt : IsAltTwoP p K
  not_fi22 : ¬ (p = 5 ∧ IsFi22 K)
  phase : D1PhaseThree p P M H R
  dec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i
  exp : ∀ r ∈ R, r ^ p = 1
  rbar_le : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
    K ⊔ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
  out : Group.IsSolvable (Outer K)
  uprime : KFactUPrime p K

namespace D1SmallAltConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem prime (hc : D1SmallAltConfig p P M H R Rbar K z) : p.Prime := hc.data.cfg.red.prime

theorem five_le (hc : D1SmallAltConfig p P M H R Rbar K z) : 5 ≤ p := by
  rcases hc.prime57 with h | h <;> omega

theorem mem_M (hc : D1SmallAltConfig p P M H R Rbar K z) : z ∈ M :=
  hc.phase.le_M hc.elt.1

theorem le_centralizer (hc : D1SmallAltConfig p P M H R Rbar K z) :
    R ≤ Subgroup.centralizer ({z} : Set G) :=
  hc.data.le_centralizer_czElt hc.elt

theorem twoCore_le_primeCore (hc : D1SmallAltConfig p P M H R Rbar K z) :
    pCoreOf 2 M ≤ GLBPrimeCore p H :=
  (hc.phase.twoCore_M_le hc.phase.twoCore_inf).trans (pCoreOf_le_glbPrimeCore Nat.prime_two
    ((Nat.coprime_primes hc.prime Nat.prime_two).mpr hc.data.cfg.red.ne_two) H)

theorem normal_K (hc : D1SmallAltConfig p P M H R Rbar K z) : K.Normal :=
  hc.data.cfg.red.normal_of_rankOne hc.data.comp hc.data.noncyclic

theorem not_le_d1X0 (hc : D1SmallAltConfig p P M H R Rbar K z) : ¬ K ≤ d1X0 p M H := by
  obtain ⟨zb, hzR, hzK, hzp, hzc⟩ := hc.data.z
  exact (hc.data.cfg.red.rankOne_principle hc.data.comp hc.data.noncyclic hzR hzK hzp hzc).2

theorem centralizer_le_d1X0 (hc : D1SmallAltConfig p P M H R Rbar K z) :
    Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ≤ d1X0 p M H := by
  obtain ⟨zb, hzR, hzK, hzp, hzc⟩ := hc.data.z
  exact hc.data.cfg.red.centralizer_le_of_rankOne hc.data.noncyclic hzR hzK hzp hzc

theorem inf_centralizer_eq_bot (hc : D1SmallAltConfig p P M H R Rbar K z) :
    K ⊓ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun c hc' => ?_
  have hcen : (⟨c, hc'.1⟩ : K) ∈ Subgroup.center K :=
    Subgroup.mem_center_iff.mpr fun k =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hc'.2 k k.2)
  rw [hc.data.center, Subgroup.mem_bot] at hcen
  exact congrArg Subtype.val hcen

theorem perfect_le (hc : D1SmallAltConfig p P M H R Rbar K z)
    {J : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hJ : ⁅J, J⁆ = J) : J ≤ K := by
  have := hc.normal_K
  set C := Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
  have hJKC : J ≤ K ⊔ C :=
    le_sup_centralizer_of_isPerfect (Subgroup.isPerfect_iff.mpr hJ) hc.out
  set ρ := QuotientGroup.mk' K
  set ψ := ρ.comp C.subtype
  have hψ : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).mpr fun c hc1 => ?_
    have hcK : (c : H ⧸ primeComplementCore (G := H) p) ∈ K := (QuotientGroup.eq_one_iff _).mp hc1
    have hmem : (c : H ⧸ primeComplementCore (G := H) p) ∈ K ⊓ C := ⟨hcK, c.2⟩
    rw [hc.inf_centralizer_eq_bot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  set J' := (J.map ρ).comap ψ
  have hJ'map : J'.map ψ = J.map ρ := by
    refine le_antisymm (Subgroup.map_comap_le _ _) ?_
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨k, hk, c, hcC, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hJKC hj)
    have hk1 : ρ k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    have hρ : ρ c = ρ (k * c) := by rw [map_mul, hk1, one_mul]
    exact ⟨⟨c, hcC⟩, show ρ c ∈ J.map ρ by rw [hρ]; exact ⟨_, hj, rfl⟩, hρ⟩
  have hJ'p : ⁅J', J'⁆ = J' := by
    apply Subgroup.map_injective hψ
    rw [Subgroup.map_commutator, hJ'map, ← Subgroup.map_commutator, hJ]
  have hbot := hc.data.cfg.red.eq_bot_of_le_centralizer_of_perfect hc.data.comp hc.not_le_d1X0
    hc.ia (Subgroup.map_subtype_le J') (by rw [← Subgroup.map_commutator, hJ'p])
  have hJ'b : J' = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp hbot
  have hρJ : J.map ρ = ⊥ := by rw [← hJ'map, hJ'b, Subgroup.map_bot]
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hρJ

theorem inf_d1X0_eq (hc : D1SmallAltConfig p P M H R Rbar K z) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) :
    K ⊓ d1X0 p M H = (GLBCore p 1 (T₁ : Subgroup K)).map K.subtype := by
  obtain ⟨zb, hzR, hzK, hzp, hzc⟩ := hc.data.z
  obtain ⟨hN, hKX₀⟩ :=
    hc.data.cfg.red.rankOne_principle hc.data.comp hc.data.noncyclic hzR hzK hzp hzc
  have hne := hc.data.cfg.red.glbCore_ne_top_of_rankOne hN hKX₀ hT₁
  have hΓX : (GLBCore p 1 (T₁ : Subgroup K)).map K.subtype ≤ d1X0 p M H :=
    glbCore_map_le_of_normalizer_le hc.prime hT₁ hN
  have hcomap : (d1X0 p M H).comap K.subtype = GLBCore p 1 (T₁ : Subgroup K) := by
    rcases (hc.uprime T₁ hne).1 ((d1X0 p M H).comap K.subtype)
      (Subgroup.map_le_iff_le_comap.mp hΓX) with h | h
    · exact h
    · exact absurd (fun k hk => (Subgroup.mem_comap.mp (h.ge (Subgroup.mem_top ⟨k, hk⟩)) :)) hKX₀
  rw [← hcomap, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]

theorem exists_injective_of_perfect (hc : D1SmallAltConfig p P M H R Rbar K z)
    (hΓ : KFactAltTwoPGamma) {J : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hJX : J ≤ d1X0 p M H) (hJ : ⁅J, J⁆ = J) :
    ∃ f : ↥J →* alternatingGroup (Fin p) × alternatingGroup (Fin p), Function.Injective f := by
  obtain ⟨T₁, hT₁, -⟩ := hc.data.exists_sylow
  have hJK : J ≤ K ⊓ d1X0 p M H := le_inf (hc.perfect_le hJ) hJX
  rw [hc.inf_d1X0_eq hT₁] at hJK
  set Γ := GLBCore p 1 (T₁ : Subgroup K)
  set ι : ↥Γ →* H ⧸ primeComplementCore (G := H) p := K.subtype.comp Γ.subtype
  have hι : Function.Injective ι := K.subtype_injective.comp Γ.subtype_injective
  set V := J.comap ι
  have hVmap : V.map ι = J := by
    refine le_antisymm (Subgroup.map_comap_le _ _) fun j hj => ?_
    obtain ⟨k, hk, rfl⟩ := hJK hj
    exact ⟨⟨k, hk⟩, show ι ⟨k, hk⟩ ∈ J from hj, rfl⟩
  have hVp : ⁅V, V⁆ = V :=
    Subgroup.map_injective hι (by rw [Subgroup.map_commutator, hVmap, hJ])
  obtain ⟨f, hf⟩ := (hΓ (↥K) p hc.prime hc.five_le hc.alt T₁).2 V hVp
  let e : ↥V ≃* ↥J := (V.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hVmap)
  exact ⟨f.comp e.symm.toMonoidHom, hf.comp e.symm.injective⟩

end D1SmallAltConfig

end CFSG.AGLEmbedding
