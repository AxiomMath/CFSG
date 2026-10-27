module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.CompletionThreeCross
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.CompletionThreeRange
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.D5Completion
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PhanD4
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureRecovery
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Extension

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan
open CFSG.GroupTheory CFSG.ClassicalGroups.Unitary CFSG.GorensteinWalter

open QuadraticMap

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

private noncomputable def pureUnivMulEquiv :
    DΩ E 3 ≃* normPureBlock E 4 Finset.univ :=
  (MonoidHom.ofInjective (stdEmb_injective E)).trans
    (MulEquiv.subgroupCongr (range_stdEmb E))

private theorem pureUnivMulEquiv_apply (x : DΩ E 3) :
    ((pureUnivMulEquiv E x : normPureBlock E 4 Finset.univ) : normOmega E 4) = stdEmb E x :=
  rfl

private theorem map_subgroupOf_pureBlock_eq_map_comap {G : Type*} [Group G]
    (φ₀ : DΩ E 3 →* G) (T : Finset (Fin 4)) :
    ((normPureBlock E 4 T).subgroupOf (normPureBlock E 4 Finset.univ)).map
        (φ₀.comp (pureUnivMulEquiv E).symm.toMonoidHom) =
      ((normPureBlock E 4 T).comap (stdEmb E)).map φ₀ := by
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(pureUnivMulEquiv E).symm y, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    rw [← pureUnivMulEquiv_apply E ((pureUnivMulEquiv E).symm y),
      MulEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨x, hx, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨⟨stdEmb E x, by
        rw [← range_stdEmb E]
        exact MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩, hx, ?_⟩
    refine congrArg φ₀ ?_
    show (pureUnivMulEquiv E).symm ⟨stdEmb E x, _⟩ = x
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [pureUnivMulEquiv_apply]

private theorem mem_normPureBlock_three_of_cast_mem {x : normOmega E 3}
    (hx : normOmegaCast E (by norm_num : 3 ≤ 4) x ∈ normPureBlock E 4 Finset.univ) :
    x ∈ normPureBlock E 3 Finset.univ := by
  rw [normPureBlock_univ_three_eq_normAnchorFixing, mem_normAnchorFixing_iff]
  intro w
  have h4 := (mem_normAnchorFixing_iff E).mp
    (normPureBlock_le_normAnchorFixing E 4 Finset.univ hx) w
  have h4' := congrArg (castRestr (F := F) (K := K) (by norm_num : 3 ≤ 4)) h4
  rw [normOmegaCast_apply, castEquiv_apply, castRestr_castLin] at h4'
  have hzero : castRestr (F := F) (K := K) (by norm_num : 3 ≤ 4)
      ((w, (0 : Fin 4 → K))) = (w, (0 : Fin 3 → K)) := rfl
  rw [hzero] at h4'
  exact h4'

private theorem hagree_of_pureD4 {G : Type*} [Group G]
    (φ₀ : DΩ E 3 →* G) (a3 : normOmega E 3 →* G)
    (h3 : φ₀.comp (qnExtΩ E (Fin.succEmb 3)) =
      a3.comp (pureEmb E (Function.Embedding.refl (Fin 3)))) :
    ∀ (x : normOmega E 3)
      (hx : normOmegaCast E (by norm_num : 3 ≤ 4) x ∈ normPureBlock E 4 Finset.univ),
      (φ₀.comp (pureUnivMulEquiv E).symm.toMonoidHom) ⟨_, hx⟩ = a3 x := by
  intro x hx
  have hx3 : x ∈ normPureBlock E 3 Finset.univ :=
    mem_normPureBlock_three_of_cast_mem E hx
  have hrange : normPureBlock E 3 Finset.univ =
      (pureEmb E (Function.Embedding.refl (Fin 3))).range := by
    rw [range_pureEmb, Finset.map_refl]
  rw [hrange] at hx3
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hx3
  have hstd : pureUnivMulEquiv E (qnExtΩ E (Fin.succEmb 3) z) =
      (⟨normOmegaCast E (by norm_num : 3 ≤ 4) x, hx⟩ : normPureBlock E 4 Finset.univ) := by
    apply Subtype.ext
    rw [pureUnivMulEquiv_apply]
    have h3z : stdEmb E (qnExtΩ E (Fin.succEmb 3) z) =
        normOmegaCast E (by norm_num : 3 ≤ 4)
          (pureEmb E (Function.Embedding.refl (Fin 3)) z) := by
      have := congrArg (fun g : orthDerived (Qn E 3) →* normOmega E 4 => g z)
        (stdEmb_comp_qnExtΩ_succ E)
      simpa using this
    rw [h3z, hz]
  have hsymm : (pureUnivMulEquiv E).symm
      (⟨normOmegaCast E (by norm_num : 3 ≤ 4) x, hx⟩ : normPureBlock E 4 Finset.univ) =
      qnExtΩ E (Fin.succEmb 3) z := by
    rw [← hstd, MulEquiv.symm_apply_apply]
  calc
    (φ₀.comp (pureUnivMulEquiv E).symm.toMonoidHom)
        (⟨normOmegaCast E (by norm_num : 3 ≤ 4) x, hx⟩ :
          normPureBlock E 4 Finset.univ)
        = φ₀ ((pureUnivMulEquiv E).symm
            ⟨normOmegaCast E (by norm_num : 3 ≤ 4) x, hx⟩) := rfl
    _ = φ₀ (qnExtΩ E (Fin.succEmb 3) z) := by rw [hsymm]
    _ = (φ₀.comp (qnExtΩ E (Fin.succEmb 3))) z := rfl
    _ = ((a3).comp (pureEmb E (Function.Embedding.refl (Fin 3)))) z := by rw [h3]
    _ = a3 (pureEmb E (Function.Embedding.refl (Fin 3)) z) := rfl
    _ = a3 x := by rw [hz]

private theorem h23_of_recovery {G : Type*} [Group G]
    (φ₀ : DΩ E 3 →* G) (a0 : normOmega E 3 →* G)
    (hrec23 : ((normPureBlock E 4 {2, 3}).comap (stdEmb E)).map φ₀ =
      ((normPureBlock E 4 {2, 3}).comap
        (normDel E (by norm_num : 2 ≤ 3) 0)).map a0)
    (y : normPureBlock E 4 Finset.univ)
    (hy : (y : normOmega E 4) ∈ normPureBlock E 4 {2, 3}) :
    (φ₀.comp (pureUnivMulEquiv E).symm.toMonoidHom) y ∈
      (normPureBlock E 3 {1, 2}).map a0 := by
  have hmap := map_subgroupOf_pureBlock_eq_map_comap (E := E) φ₀ ({2, 3} : Finset (Fin 4))
  have hone : (φ₀.comp (pureUnivMulEquiv E).symm.toMonoidHom) y ∈
      ((normPureBlock E 4 {2, 3}).subgroupOf
          (normPureBlock E 4 Finset.univ)).map
        (φ₀.comp (pureUnivMulEquiv E).symm.toMonoidHom) :=
    Subgroup.mem_map.mpr ⟨⟨y, y.2⟩, hy, rfl⟩
  rw [hmap, hrec23] at hone
  have hS : (({1, 2} : Finset (Fin 3)).map (0 : Fin 4).succAboveEmb) = {2, 3} := by decide
  rw [← hS, comap_normPureBlock_normDel E (by norm_num : 2 ≤ 3) (0 : Fin 4)
    ({1, 2} : Finset (Fin 3))] at hone
  exact hone

private theorem comp_eq_of_eq_on_blocks {G : Type*} [Group G]
    (Ψ : normOmega E 4 →* G) (a3 : normOmega E 3 →* G)
    (φ : normPureBlock E 4 Finset.univ →* G)
    (hΨφ : ∀ y : normPureBlock E 4 Finset.univ, Ψ y = φ y)
    (hΨa : ∀ x ∈ normBlock E 3 {0, 1},
      Ψ (normOmegaCast E (by norm_num : 3 ≤ 4) x) = a3 x)
    (hagree : ∀ (x : normOmega E 3)
      (hx : normOmegaCast E (by norm_num : 3 ≤ 4) x ∈ normPureBlock E 4 Finset.univ),
      φ ⟨_, hx⟩ = a3 x)
    (hq : 2 < Nat.card F) :
    Ψ.comp (normOmegaCast E (by norm_num : 3 ≤ 4)) = a3 := by
  let L := MonoidHom.eqLocus (Ψ.comp (normOmegaCast E (by norm_num : 3 ≤ 4))) a3
  have hB : normBlock E 3 {0, 1} ≤ L := fun x hx => hΨa x hx
  have hP : normPureBlock E 3 Finset.univ ≤ L := by
    intro x hx
    change (Ψ.comp (normOmegaCast E (by norm_num : 3 ≤ 4))) x = a3 x
    have hx4 : normOmegaCast E (by norm_num : 3 ≤ 4) x ∈
        normPureBlock E 4 Finset.univ := by
      have h1 : normOmegaCast E (by norm_num : 3 ≤ 4) x ∈
          normPureBlock E 4 (Finset.univ.map (Fin.castLEEmb (by norm_num : 3 ≤ 4))) := by
        rw [← map_normPureBlock_normOmegaCast E (by norm_num : 3 ≤ 4) Finset.univ]
        exact Subgroup.mem_map_of_mem _ hx
      exact normPureBlock_mono E 4 (Finset.subset_univ _) h1
    rw [MonoidHom.comp_apply, hΨφ ⟨_, hx4⟩]
    exact hagree x hx4
  have htop : normBlock E 3 {0, 1} ⊔ normPureBlock E 3 Finset.univ = ⊤ := by
    have htriple := normBlock_pair_sup_normPureBlock_triple E hq (le_refl 3)
      (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
      (show (1 : Fin 3) ≠ 2 by decide)
    rw [show ({0, 1, 2} : Finset (Fin 3)) = Finset.univ by decide,
      normBlock_univ] at htriple
    exact htriple
  have hL : L = ⊤ := top_unique (htop ▸ sup_le hB hP)
  ext x
  have hx : x ∈ L := by rw [hL]; exact Subgroup.mem_top x
  simpa [L, MonoidHom.mem_eqLocusM] using hx

private theorem h03_of_recovery {G : Type*} [Group G]
    (φ₀ : DΩ E 3 →* G) (a1 : normOmega E 3 →* G)
    (φ : normPureBlock E 4 Finset.univ →* G) (Ψ : normOmega E 4 →* G)
    (hφ0 : φ = φ₀.comp (pureUnivMulEquiv E).symm.toMonoidHom)
    (hΨφ : ∀ y : normPureBlock E 4 Finset.univ, Ψ y = φ y)
    (hrec03 : ((normPureBlock E 4 {0, 3}).comap (stdEmb E)).map φ₀ =
      ((normPureBlock E 4 {0, 3}).comap
        (normDel E (by norm_num : 2 ≤ 3) 1)).map a1) :
    (normPureBlock E 4 {0, 3}).map Ψ = (normPureBlock E 3 {0, 2}).map a1 := by
  have hHK : normPureBlock E 4 {0, 3} ≤ normPureBlock E 4 Finset.univ :=
    normPureBlock_mono E 4 (Finset.subset_univ _)
  have hmap : (normPureBlock E 4 {0, 3}).map Ψ =
      ((normPureBlock E 4 {0, 3}).subgroupOf
        (normPureBlock E 4 Finset.univ)).map φ := by
    have hφ : φ = Ψ.comp (normPureBlock E 4 Finset.univ).subtype :=
      MonoidHom.ext fun y => (hΨφ y).symm
    rw [hφ, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hHK]
  rw [hmap, hφ0, map_subgroupOf_pureBlock_eq_map_comap (E := E) φ₀ {0, 3}, hrec03]
  have hS : (({0, 2} : Finset (Fin 3)).map (1 : Fin 4).succAboveEmb) = {0, 3} := by decide
  rw [← hS, comap_normPureBlock_normDel E (by norm_num : 2 ≤ 3) (1 : Fin 4)
    ({0, 2} : Finset (Fin 3))]

theorem exists_normOmega_hom_of_rangeCoherent_three (hq : 4 ≤ Nat.card F)
    (hK : Nat.card K = (2 ^ f) ^ 2) {G : Type} [Group G] (a : Fin 4 → (normOmega E 3 →* G))
    (ha : ∀ i, Function.Injective (a i)) (R : Finset (Fin 4) → Subgroup G)
    (hR : ∀ (i : Fin 4) (S : Finset (Fin 3)), S.Nonempty → S.card ≤ 2 →
      (normBlock E 3 S).map (a i) = R (S.image i.succAbove)) :
    ∃ Ψ : normOmega E 4 →* G, Function.Injective Ψ ∧
      Ψ.comp (normOmegaCast E (by norm_num : 3 ≤ 4)) = a 3 ∧
      Ψ.range = ⨆ i, (a i).range := by
  classical
  have hF : Nat.card F = 2 ^ f :=
    card_base_eq_two_pow E (unitaryFieldDataOfCard hK)
  have hq' : 4 ≤ 2 ^ f := hF ▸ hq
  have h2 : 2 < Nat.card F := by omega
  obtain ⟨φ₀, hφ₀, h3, h0⟩ := exists_pureD4_hom E hq' hK ha hR
  have hrec := pureD4_recovery E hq' hK ha hR hφ₀ h3 h0
  let φ : normPureBlock E 4 Finset.univ →* G :=
    φ₀.comp (pureUnivMulEquiv E).symm.toMonoidHom
  have hagree : ∀ (x : normOmega E 3)
      (hx : normOmegaCast E (by norm_num : 3 ≤ 4) x ∈ normPureBlock E 4 Finset.univ),
      φ ⟨_, hx⟩ = a 3 x := fun x hx => hagree_of_pureD4 E φ₀ (a 3) h3 x hx
  have hrec23 := hrec {2, 3} (by decide) (by decide) 0 (by decide)
  have hrec03 := hrec {0, 3} (by decide) (by decide) 1 (by decide)
  have h23 : ∀ y : normPureBlock E 4 Finset.univ,
      (y : normOmega E 4) ∈ normPureBlock E 4 {2, 3} →
      φ y ∈ (normPureBlock E 3 {1, 2}).map (a 0) :=
    fun y hy => h23_of_recovery E φ₀ (a 0) hrec23 y hy
  obtain ⟨Ψ, hΨφ, hΨa, -⟩ :=
    exists_d5Completion (E := E) hq φ (a 3) hagree
      (commute_crossAnchor_crossPure (E := E) hq ha hR hagree h23)
  have hΨ3 : Ψ.comp (normOmegaCast E (by norm_num : 3 ≤ 4)) = a 3 :=
    comp_eq_of_eq_on_blocks E Ψ (a 3) φ hΨφ hΨa hagree h2
  have hΨinj : Function.Injective Ψ :=
    injective_normOmega_hom E (m := 3) (by norm_num) (a 3) (ha 3) Ψ
      (fun x => DFunLike.congr_fun hΨ3 x)
  have h03 : (normPureBlock E 4 {0, 3}).map Ψ =
      (normPureBlock E 3 {0, 2}).map (a 1) :=
    h03_of_recovery E φ₀ (a 1) φ Ψ rfl hΨφ hrec03
  exact ⟨Ψ, hΨinj, hΨ3, range_eq_iSup_of_comp_normOmegaCast E hq ha hR hΨ3 h03⟩

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
