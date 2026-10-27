module

public import CFSG.LocalAnalysis.AGLEmbedding.D1CompCore
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMData
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMDataAux2
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G]

structure D1OneLieU3Data (p : ℕ) [Fact p.Prime] (n : ℕ) (P : Sylow p G)
    (M H R X Z Np : Subgroup G) : Prop where
  ph3 : D1PhaseThree p P M H R
  ind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q
  two_le : 2 ≤ n
  le_R : X ≤ R
  center_eq : Z = X ⊓ Subgroup.centralizer (X : Set G)
  card_eq : Nat.card X = p ^ (3 * n)
  card_center : Nat.card Z = p ^ n
  commutator_eq : ⁅X, X⁆ = Z
  pow_eq_one : ∀ x ∈ X, x ^ p = 1
  pRank_le : Open.pRank p (H ⊓ M) ≤ 2 * n + 1
  perfect_le : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ Np
  plus_cyclic : ∀ A : Subgroup G, A ≤ Np → IsPGroup p A → IsCyclic A
  comm_plus : ∀ x ∈ X, ∀ c ∈ Np, x * c * x⁻¹ * c⁻¹ ∈ GLBPrimeCore p H
  comm_core : ⁅GLBPrimeCore p H, X⁆ ≤ pCoreOf 2 H
  core_eq : GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H
  le_pCore : Z ≤ pCorePreimage p M
  inf_pCore : X ⊓ pCorePreimage p M ≤ Z
  comm_pCore : ∀ x ∈ X, ∀ y ∈ R ⊓ pCorePreimage p M, x * y = y * x
  ppd : ∃ (r : ℕ) (t : G), r.Prime ∧ 2 * n < r ∧ r ≠ p ∧ ¬ r ∣ p - 1 ∧ t ∈ H ⊓ M ∧
    t ∈ Subgroup.normalizer (X : Set G) ∧ IsPGroup r (Subgroup.zpowers t) ∧
    (∀ z ∈ Z, t * z * t⁻¹ = z) ∧ (∀ x ∈ X, t ^ r * x * (t ^ r)⁻¹ = x) ∧
    (∃ x ∈ X, t * x * t⁻¹ * x⁻¹ ∉ Z) ∧
    ∀ V : Subgroup G, Z ≤ V → V ≤ X → t ∈ Subgroup.normalizer (V : Set G) → V = Z ∨ V = X

end Data

section Transport

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P : Sylow p G}
  {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1CompCore.unitary_sylow (hd : D1CompCore p P M H R Rbar K) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) {n : ℕ}
    (hTcard : Nat.card (T₁ : Subgroup K) = p ^ (3 * n))
    (hTcomm : ⁅(T₁ : Subgroup K), (T₁ : Subgroup K)⁆ =
      (T₁ : Subgroup K) ⊓ Subgroup.centralizer ((T₁ : Subgroup K) : Set K))
    (hTpow : ∀ u ∈ (T₁ : Subgroup K), u ^ p = 1) :
    d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) =
        d1LiftX p H R K ⊓ Subgroup.centralizer (d1LiftX p H R K : Set G) ∧
      ⁅d1LiftX p H R K, d1LiftX p H R K⁆ =
        d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) ∧
      Nat.card (d1LiftX p H R K) = p ^ (3 * n) ∧ ∀ u ∈ d1LiftX p H R K, u ^ p = 1 := by
  have hp : p.Prime := Fact.out
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set T : Subgroup (H ⧸ primeComplementCore (G := H) p) :=
    (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K with hTdef
  set U := d1LiftX p H R K with hUdef
  set Z := d1LiftX p H R (centerOf T) with hZdef
  have hUH : U ≤ H := d1LiftX_le_H p H R K
  have hUR : U ≤ R := d1LiftX_le p H R K
  have hUp : IsPGroup p U := hd.esc.isPGroup.to_le hUR
  have hUmap : (U.subgroupOf H).map π = T := hd.map_d1LiftX_eq_inf
  have hUN : U ⊓ GLBPrimeCore p H = ⊥ := inf_eq_bot_of_isPGroup hp hUp (glbPrimeCore_coprime p H)
  have hinj : ∀ {A B : Subgroup G}, A ≤ U → B ≤ U →
      (A.subgroupOf H).map π ≤ (B.subgroupOf H).map π → A ≤ B :=
    fun hAU hBU hAB => le_of_map_mk_le_of_isPGroup hUH hUp hAU hBU hAB
  have hZX : Z ≤ U := Subgroup.map_mono (inf_le_inf_left _ (Subgroup.comap_mono
    ((inf_le_left : centerOf _ ≤ _).trans inf_le_right)))
  have hZmap : (Z.subgroupOf H).map π = centerOf T := hd.map_d1LiftX_centerOf
  have hZT : centerOf T =
      ((T₁ : Subgroup K) ⊓ Subgroup.centralizer ((T₁ : Subgroup K) : Set K)).map K.subtype := by
    rw [← hT₁]
    exact (map_subtype_centerOf _).symm
  have hCU : ((U ⊓ Subgroup.centralizer (U : Set G)).subgroupOf H).map π = centerOf T := by
    rw [map_inf_centralizer_eq hUH hUp, hUmap]
    rfl
  have hZC : Z = U ⊓ Subgroup.centralizer (U : Set G) :=
    le_antisymm (hinj hZX inf_le_left (by rw [hZmap, hCU]))
      (hinj inf_le_left hZX (by rw [hZmap, hCU]))
  have hcomm : ⁅U, U⁆ = Z := by
    have hmap : ((⁅U, U⁆ : Subgroup G).subgroupOf H).map π = (Z.subgroupOf H).map π := by
      rw [hZmap, hZT, ← hTcomm, Subgroup.map_commutator, hT₁, ← hUmap,
        ← Subgroup.map_commutator]
      congr 1
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUH,
        Subgroup.map_subgroupOf_eq_of_le ((Subgroup.commutator_le_self U).trans hUH)]
    exact le_antisymm (hinj (Subgroup.commutator_le_self U) hZX hmap.le)
      (hinj hZX (Subgroup.commutator_le_self U) hmap.ge)
  have hcardU : Nat.card U = p ^ (3 * n) := by
    have h1 : Nat.card ((U.subgroupOf H).map π) = Nat.card (U.subgroupOf H) :=
      card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hUp.comap_subtype
    rw [hUmap, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv, ← hT₁,
      Subgroup.card_map_of_injective K.subtype_injective, hTcard] at h1
    exact h1.symm
  have hpowU : ∀ u ∈ U, u ^ p = 1 := by
    intro u hu
    have hπu : π ⟨u, hUH hu⟩ ∈ (U.subgroupOf H).map π :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu)
    rw [hUmap, ← hT₁] at hπu
    obtain ⟨v, hv, hvu⟩ := hπu
    have h1 : π ⟨u, hUH hu⟩ ^ p = 1 := by rw [← hvu, ← map_pow, hTpow v hv, map_one]
    have h2 : ((⟨u, hUH hu⟩ ^ p : H) : G) ∈ GLBPrimeCore p H := by
      rw [mem_glbPrimeCore_iff_mk_eq_one, map_pow, h1]
    have h3 : ((⟨u, hUH hu⟩ ^ p : H) : G) ∈ U ⊓ GLBPrimeCore p H :=
      ⟨by simpa using U.pow_mem hu p, h2⟩
    rw [hUN, Subgroup.mem_bot] at h3
    simpa using h3
  exact ⟨hZC, hcomm, hcardU, hpowU⟩

theorem D1OneLieData.unitary_sylow (hd : D1OneLieData p P M H R Rbar K) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) {n : ℕ}
    (hTcard : Nat.card (T₁ : Subgroup K) = p ^ (3 * n))
    (hTcomm : ⁅(T₁ : Subgroup K), (T₁ : Subgroup K)⁆ =
      (T₁ : Subgroup K) ⊓ Subgroup.centralizer ((T₁ : Subgroup K) : Set K))
    (hTpow : ∀ u ∈ (T₁ : Subgroup K), u ^ p = 1) :
    d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) =
        d1LiftX p H R K ⊓ Subgroup.centralizer (d1LiftX p H R K : Set G) ∧
      ⁅d1LiftX p H R K, d1LiftX p H R K⁆ =
        d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) ∧
      Nat.card (d1LiftX p H R K) = p ^ (3 * n) ∧ ∀ u ∈ d1LiftX p H R K, u ^ p = 1 :=
  hd.toCore.unitary_sylow hT₁ hTcard hTcomm hTpow

end Transport

end CFSG.AGLEmbedding
