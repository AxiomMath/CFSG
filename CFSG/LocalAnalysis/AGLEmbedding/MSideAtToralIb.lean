module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeDefs
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbBasic
import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorBarM
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtFixed
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeToral

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ}

namespace D1MSideAt

variable {M S R : Subgroup G}

theorem barM_cover (h : D1MSideAt M S) {V : Subgroup G}
    (hVHM : V ≤ M ⊓ Subgroup.normalizer (S : Set G)) (hVp : ⁅V, V⁆ = V) {L : Subgroup G}
    (hVL : V ≤ Subgroup.normalizer (L : Set G)) :
    ⁅barM M V, barM M V⁆ = barM M V ∧
      barM M V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      barM M V ≤ Subgroup.normalizer (barM M (S ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hVM : V ≤ M := hVHM.trans inf_le_left
  have hVL' : barM M V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨v, hv, rfl⟩
    exact mem_normalizer_barM v.2 (hVL (Subgroup.mem_subgroupOf.mp hv))
  have hVS : barM M V ≤
      Subgroup.normalizer (barM M (S) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨v, hv, rfl⟩
    have hvHM := hVHM (Subgroup.mem_subgroupOf.mp hv)
    have hvN : (v : G) ∈ Subgroup.normalizer (S : Set G) := hvHM.2
    exact mem_normalizer_barM v.2 hvN
  have hinf := barM_inf_eq (L := L) h.twoCore_M_le
  refine ⟨commutator_barM_eq_self hVM hVp, hVL', ?_⟩
  rw [hinf]
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxS, hxL⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hVS hv) x).mp hxS,
      (Subgroup.mem_normalizer_iff.mp (hVL' hv) x).mp hxL⟩
  · rintro ⟨hxS, hxL⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hVS hv) x).mpr hxS,
      (Subgroup.mem_normalizer_iff.mp (hVL' hv) x).mpr hxL⟩

theorem zbar_mem_sup_of_cover (h : D1MSideAt M S) (hMtop : M ≠ ⊤)
    (hSch : KFactCatalogSchreier) {V : Subgroup G}
    (hVHM : V ≤ M ⊓ Subgroup.normalizer (S : Set G)) (hVp : ⁅V, V⁆ = V)
    {z : G} (hzV : z ∈ V) (hzM : z ∈ M) {L : Subgroup G} (hL : IsWeakSBlock M (S) L)
    (hVL : V ≤ Subgroup.normalizer (L : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
      barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨hVp', hVL', -⟩ := h.barM_cover hVHM hVp hVL
  have hcat : IsCatalogGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
    ((catalogSimpleSections_of_isKProper h.glob.kProper M hMtop).quotient
      _).isCatalogGroup_center_quotient hL.component
  have hzV' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈ barM M V :=
    ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.mpr hzV, rfl⟩
  exact perfect_le_sup_centralizer_of_outer
    (isSolvable_outer_of_component hSch hL.component hcat) hVp' hVL' hzV'

theorem false_of_toral_three_ib (h : D1MSideAt M S) (hMtop : M ≠ ⊤) (hRM : R ≤ M)
    (hNR : Subgroup.normalizer (R : Set G) ≤ M)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hSch : KFactCatalogSchreier)
    (hK : CitedBlockToralThreeIb)
    (hperf : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      V ≤ barM M (M ⊓ Subgroup.normalizer (S : Set G)) → ⁅V, V⁆ = V → ¬ 3 ^ 2 ∣ Nat.card V)
    {z : G} (hzR : z ∈ R) (hzo : orderOf z = 3)
    (hCz : M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (S : Set G))
    (hcov : ∃ V : Subgroup G, V ≤ M ⊓ Subgroup.normalizer (S : Set G) ∧ ⁅V, V⁆ = V ∧ z ∈ V ∧
      ∀ L : Subgroup G, IsWeakSBlock M (S) L → V ≤ Subgroup.normalizer (L : Set G))
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
  obtain ⟨V, hVHM, hVp, hzV, hVN⟩ := hcov
  have hPL : ∀ L : Subgroup G, IsWeakSBlock M S L → IbPerfectSections 3 (blockPL M S L) := by
    intro L hL W hW hWp
    refine hperf W (hW.trans (barM_mono ?_)) hWp
    exact fun x hx => ⟨hL.le hx.2, hx.1⟩
  have hblkA : ∀ L : Subgroup G, IsWeakSBlock M S L →
      zb ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun L hL => h.zbar_mem_sup_of_cover hMtop hSch hVHM hVp hzV hzM hL (hVN L hL)
  have hblkB : ∀ L : Subgroup G, IsWeakSBlock M S L → zb ∈ barM M L →
      ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M L →
        E ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → IsElemAbelian 3 E →
        Nat.card E ≠ 3 ^ 3 := by
    intro L hL hzL
    obtain ⟨hVp', hVL', hVSL⟩ := h.barM_cover hVHM hVp (hVN L hL)
    exact hK G M S L h.isKGroup h.hyp hL (h.nineThree h93 hL)
      (h.nineThree_not_one h85 hD2 hL).1 (h.not_isSylowTwoOf_inf h85 hD2 hL) (hPL L hL) zb hzL
      hzb3 (h.not_mem_centralizer_block hp hp2 hzM hz hCz hL)
      ⟨barM M V, hVp', hVL', hVSL, ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.mpr hzV, rfl⟩⟩
      (fun l hl hl' => h.fixed_le_barM_normalizer_inf hp hp2 hzM hz hCz l hl hl')
  obtain ⟨L₀, hL₀⟩ := h.exists_weakSBlock h84 hD2
  obtain ⟨L₁, hL₁, r, hrR, hrM, hrL, hrc⟩ :=
    exists_rep_mem_R_at hzM hz3 hCz hsyl hL₀ (hblkA L₀ hL₀)
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
  refine hblkB L₁ hL₁ hzL₁ (barM M E) ((barM_mono hER).trans hRL) ?_
    (isElemAbelian_barM hEel) ?_
  · rintro _ ⟨⟨e, heM⟩, he, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hzb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hRz e (hER (Subgroup.mem_subgroupOf.mp he))).symm
  · rw [card_barM_of_isPGroup hp hp2 (hER.trans hRM)
      (IsPGroup.of_card (n := 3) hEcard), hEcard]

end D1MSideAt

end CFSG.AGLEmbedding
