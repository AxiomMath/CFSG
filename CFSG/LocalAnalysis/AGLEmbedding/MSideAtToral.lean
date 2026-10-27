module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorBarM
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtFixed
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeToral

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1MSideAt

variable {M S R : Subgroup G}

theorem false_of_toral_three (h : D1MSideAt M S) (hRM : R ≤ M)
    (hNR : Subgroup.normalizer (R : Set G) ≤ M)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK : CitedBlockToralThree)
    (hperf : ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y, Y⁆ = Y →
      Nat.Coprime 3 (Nat.card Y))
    {z : G} (hzR : z ∈ R) (hzo : orderOf z = 3)
    (hCz : M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (S : Set G))
    (hsyl : ∃ S : Sylow 3 ↥(M ⊓ Subgroup.centralizer ({z} : Set G)),
      (S : Subgroup _).map (M ⊓ Subgroup.centralizer ({z} : Set G)).subtype = R)
    {T : Subgroup G} (hzT : z ∉ T) (hRz : ∀ r ∈ R, z * r = r * z) (hexp : ∀ r ∈ R, r ^ 3 = 1)
    (hfus : ∀ r ∈ R, r ∉ T → r ∈ fusionSet R z)
    (hinv : ∀ t ∈ T, t ≠ 1 → ∃ n ∈ M, n * z * n⁻¹ = z ∧ n * t * n⁻¹ = t⁻¹)
    (hE : ∃ E : Subgroup G, E ≤ R ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3) : False := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hzM : z ∈ M := hRM hzR
  set zb := mk ⟨z, hzM⟩ with hzb
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hz : IsPGroup 3 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  have hzb3 : zb ^ 3 = 1 := by
    rw [hzb, ← map_pow]
    have : (⟨z, hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [this, map_one]
  have hblk : ∀ L : Subgroup G, IsWeakSBlock M S L →
      (zb ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M L →
        E ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → IsElemAbelian 3 E →
        Nat.card E ≠ 3 ^ 3) := fun L hL =>
    hK G M S L h.isKGroup h.hyp hL (h.nineThree h93 hL)
      (h.nineThree_not_one h85 hD2 hL).1 (h.not_isSylowTwoOf_inf h85 hD2 hL) hperf zb
      (mem_normalizer_barM hzM (h.mem_normalizer_block_of_cube hp hp2 h84 h86 hD2 hzM hz hz3
        hCz hL)) hzb3 (h.not_mem_centralizer_block hp hp2 hzM hz hCz hL)
      (fun l hl hl' => h.fixed_le_barM_normalizer_inf hp hp2 hzM hz hCz l hl hl')
  obtain ⟨L₀, hL₀⟩ := h.exists_weakSBlock h84 hD2
  obtain ⟨L₁, hL₁, r, hrR, hrM, hrL, hrc⟩ :=
    exists_rep_mem_R_at hzM hz3 hCz hsyl hL₀ (hblk L₀ hL₀).1
  have hzC₁ := h.not_mem_centralizer_block hp hp2 hzM hz hCz hL₁
  have hr1 : r ≠ 1 := by
    rintro rfl
    apply hzC₁
    have e : (mk ⟨1, hrM⟩)⁻¹ * zb = zb := by
      have : (⟨1, hrM⟩ : M) = 1 := rfl
      rw [this, map_one, inv_one, one_mul]
    rwa [e] at hrc
  have hrT : r ∉ T := by
    intro hrT
    obtain ⟨n, hnM, hnz, hnr⟩ := hinv r hrT hr1
    exact h.false_of_rep_inv hp hp2 hzM hz hCz hL₁ hrM (hexp r hrR) hrL hrc hnM hnz hnr
  obtain ⟨-, n, hnN, hrn⟩ := hfus r hrR hrT
  have hnM : n ∈ M := hNR hnN
  have hnzo : orderOf (n * z * n⁻¹) = 3 := by
    rw [← hzo]; exact orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective z
  have hzr : n * z * n⁻¹ ∈ Subgroup.zpowers r :=
    mem_zpowers_of_mem_zpowers_of_prime hp hnzo hrn hr1
  have hnzM : n * z * n⁻¹ ∈ M := M.mul_mem (M.mul_mem hnM hzM) (M.inv_mem hnM)
  have hnzL : mk ⟨n * z * n⁻¹, hnzM⟩ ∈ barM M L₁ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzr
    have : (⟨n * z * n⁻¹, hnzM⟩ : M) = (⟨r, hrM⟩ : M) ^ k := Subtype.ext (by simpa using hk.symm)
    rw [this, map_zpow]
    exact Subgroup.zpow_mem _ hrL k
  set A := barM M (L₁.map (MulAut.conj n⁻¹).toMonoidHom) with hA
  have hAc : IsComponentOf A ⊤ := (hL₁.toIsTwoPrimeComponent.map_conj (M.inv_mem hnM)).component
  have hzA : zb ∈ A := by
    rw [hA, barM_map_conj (M.inv_mem hnM) L₁]
    refine ⟨mk ⟨n * z * n⁻¹, hnzM⟩, hnzL, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hzb]
    congr 1
    exact Subtype.ext (by simp [mul_assoc])
  have hzL₁ : zb ∈ barM M L₁ := (h.barM_eq_of_mem_component hp hp2 hzM hz hCz hAc hzA hL₁) ▸ hzA
  have hRL := h.barM_le_of_fusion hp hp2 hzR hzM hz hCz hNR hL₁ hzL₁ hzT hRz hexp hfus
  obtain ⟨E, hER, hEel, hEcard⟩ := hE
  refine (hblk L₁ hL₁).2 (barM M E) ((barM_mono hER).trans hRL) ?_
    (isElemAbelian_barM hEel) ?_
  · rintro _ ⟨⟨e, heM⟩, he, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hzb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hRz e (hER (Subgroup.mem_subgroupOf.mp he))).symm
  · rw [card_barM_of_isPGroup hp hp2 (hER.trans hRM)
      (IsPGroup.of_card (n := 3) hEcard), hEcard]

end D1MSideAt

end CFSG.AGLEmbedding
