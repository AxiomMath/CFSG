module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreePieces
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbBlock

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Abstract

variable {Y : Type*} [Group Y]

theorem not_mem_centralizer_of_perfect {zb : Y}
    (hZ : ∀ W : Subgroup Y, ⁅W, W⁆ = W → W ≤ Subgroup.centralizer ({zb} : Set Y) → W = ⊥)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) : zb ∉ Subgroup.centralizer (L : Set Y) := by
  intro hc
  apply ne_bot_of_component hL
  refine hZ L (Subgroup.isPerfect_iff.mp ⟨hL.2.2.1⟩) fun x hx => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hc x hx

end Abstract

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

omit [Finite G] in
theorem mk_not_mem_barM_of_commute {X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hXp : ∀ x ∈ X, x ^ p = 1) {z : G} (hzM : z ∈ M) (hzp : z ^ p = 1) (hzX : z ∉ X)
    (hXz : X ≤ Subgroup.centralizer ({z} : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∉ barM M X := by
  rintro ⟨⟨x, hxM⟩, hxX, hxz⟩
  have hx : x ∈ X := Subgroup.mem_subgroupOf.mp hxX
  have hxz' : z * x = x * z := Subgroup.mem_centralizer_iff.mp (hXz hx) z
    (Set.mem_singleton z)
  have hmem : (⟨x, hxM⟩ : M)⁻¹ * ⟨z, hzM⟩ ∈ CFSG.pCore 2 ↥M := by
    rw [← QuotientGroup.eq]
    exact hxz
  have h2 : IsPGroup 2 (CFSG.pCore 2 ↥M) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := h2 ⟨_, hmem⟩
  have hk1 := congrArg (fun y : CFSG.pCore 2 ↥M => ((y : ↥M) : G)) hk
  have hk' : (x⁻¹ * z) ^ 2 ^ k = 1 := by simpa using hk1
  have hp' : (x⁻¹ * z) ^ p = 1 := by
    have hc : Commute x⁻¹ z := Commute.inv_left (show Commute x z from hxz'.symm)
    rw [hc.mul_pow, inv_pow, hXp x hx, inv_one, one_mul, hzp]
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have h1 : x⁻¹ * z = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hk', hp'⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have : z = x := by
    have := congrArg (fun y => x * y) h1
    simpa using this
  exact hzX (this ▸ hx)

theorem D1PhaseThree.exists_inner_mem_barM (h3 : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : D1NoXBlock)
    (hSch : KFactCatalogSchreier) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hDp : ⁅D, D⁆ = D) (hDK : D ≤ barM M (H ⊓ M))
    (hDL : D ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {zb : ↥M ⧸ CFSG.pCore 2 ↥M} (hzD : zb ∈ D) :
    ∃ j ∈ barM M L ⊓ barM M (H ⊓ M), zb * j⁻¹ ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  set S := pCoreOf 2 H with hS
  have hLbC : IsComponentOf (barM M L) ⊤ := hL.component
  have hMtop : M ≠ ⊤ := fun hM => h3.not_le (hM ▸ le_top)
  have hcat : CatalogSimpleSections (↥M ⧸ CFSG.pCore 2 ↥M) :=
    (catalogSimpleSections_of_isKProper h3.glob.kProper M hMtop).quotient _
  have hNSH : Subgroup.normalizer (S : Set G) = H := h3.normalizer_twoCore_H
  have hDS : D ≤ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    hDK.trans (barM_le_normalizer_barM (inf_le_left.trans hNSH.ge))
  set Cb := Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  set Pb := barM M (Subgroup.normalizer (S : Set G) ⊓ L) with hPb
  have hOut := isSolvable_outer_of_component hSch hLbC (hcat.isCatalogGroup_center_quotient hLbC)
  have hzPC : zb ∈ Pb ⊔ Cb :=
    h3.mem_sup_barM_of_mem_sup h84 h86 hD2 hL
      (perfect_le_sup_centralizer_of_outer hOut hDp hDL hzD) (hDS hzD)
  have hPL : Pb ≤ barM M L := barM_mono inf_le_right
  have hLC : barM M L ≤ Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun l hl =>
    mem_normalizer_centralizer (Subgroup.le_normalizer hl)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Pb Cb
    (hPL.trans hLC)] at hzPC
  obtain ⟨j, hjP, c, hc, hjc⟩ := hzPC
  have hjB : j ∈ barM M (H ⊓ M) :=
    (barM_mono (by rw [hNSH]; exact inf_le_inf_left H hL.le)) hjP
  refine ⟨j, ⟨hPL hjP, hjB⟩, ?_⟩
  rw [← hjc]
  have : j * c * j⁻¹ ∈ Cb := (Subgroup.mem_normalizer_iff.mp (hLC (hPL hjP)) c).mp hc
  simpa [mul_assoc] using this

theorem D1OneSmallData.commutator_mem_primeCore_of_mem_d1PlusCore
    (hd : D1OneSmallData p P M H R Rbar K) {x : G} (hx : x ∈ d1LiftX p H R K) {c : G}
    (hc : c ∈ d1PlusCore p H K) : x * c * x⁻¹ * c⁻¹ ∈ GLBPrimeCore p H := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  obtain ⟨c', hc'C, rfl⟩ := hc
  have hxH := d1LiftX_le_H p H R K hx
  have hxK : π ⟨x, hxH⟩ ∈ K := by
    have h1 : π ⟨x, hxH⟩ ∈ ((d1LiftX p H R K).subgroupOf H).map π :=
      ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hd.cfg.map_d1LiftX_eq_inf] at h1
    exact h1.2
  have hcomm' := Subgroup.mem_centralizer_iff.mp hc'C _ hxK
  refine (mem_glbPrimeCore_iff_mk_eq_one (⟨x, hxH⟩ * c' * (⟨x, hxH⟩ : H)⁻¹ * c'⁻¹)).mpr ?_
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  exact hcomm'

end CFSG.AGLEmbedding
