module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackage
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackageCore
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackageFactors
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackageAtoms
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackageIndec
import CFSG.GroupTheory.SubgroupOfQuotientMapConj
import CFSG.GroupTheory.DirectProductKrullSchmidt
import CFSG.LocalAnalysis.GLTheoremB.Prop95L97Sigma3Dec

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.Quasithin CFSG.SignalizerFunctorTheorem.McBride
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Sigma3

variable {G : Type} [Group G] {L U P D : Subgroup G} {ℳ : Set (Subgroup G)}

private lemma isIndecomposable_map_subgroupOf_sup [Finite G] {M : Subgroup G}
    (hU : IsSylowOf 2 U L) (hBP : L ⊓ normalizer (U : Set G) < P) (hPL : P ≤ L)
    (h : IsGomiLeviPackage L U P ℳ) (hD : IsGomiLeviCore P D) {X : Subgroup G} (hPX : P ≤ X)
    (hXD : X ≤ normalizer (D : Set G)) {Γ : Type} [Group Γ] {ψ : ↥X →* Γ}
    (hker : ψ.ker = D.subgroupOf X) (hM : M ∈ ℳ) :
    IsIndecomposableGroup ↥(((D ⊔ M).subgroupOf X).map ψ) := by
  have hDMX : D ⊔ M ≤ X :=
    sup_le (hD.le.trans hPX) ((h.le_parabolic M hM).trans hPX)
  have hN : (D.subgroupOf (D ⊔ M)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hDMX.trans hXD)
  have h₁ := (letI inst : (D.subgroupOf (D ⊔ M)).Normal := hN
    nonempty_mulEquiv_map_subgroupOf (X := X) (D := D) (ψ := ψ) hker hDMX)
  obtain ⟨e₁⟩ := h₁
  have h₂ := (letI inst : (D.subgroupOf (D ⊔ M)).Normal := hN
    h.nonempty_mulEquiv_quotient hD hM)
  obtain ⟨e₂⟩ := h₂
  exact Sigma3Dec.isIndecomposableGroup_of_mulEquiv (e₁.trans e₂)
    (h.isIndecomposableGroup hU hBP hPL hM)

private lemma center_map_subgroupOf_sup_eq_bot [Finite G] {M : Subgroup G}
    (h : IsGomiLeviPackage L U P ℳ) (hD : IsGomiLeviCore P D) {X : Subgroup G} (hPX : P ≤ X)
    (hXD : X ≤ normalizer (D : Set G)) {Γ : Type} [Group Γ] {ψ : ↥X →* Γ}
    (hker : ψ.ker = D.subgroupOf X) (hM : M ∈ ℳ) :
    center ↥(((D ⊔ M).subgroupOf X).map ψ) = ⊥ := by
  have hDMX : D ⊔ M ≤ X :=
    sup_le (hD.le.trans hPX) ((h.le_parabolic M hM).trans hPX)
  have hN : (D.subgroupOf (D ⊔ M)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hDMX.trans hXD)
  have h₁ := (letI inst : (D.subgroupOf (D ⊔ M)).Normal := hN
    nonempty_mulEquiv_map_subgroupOf (X := X) (D := D) (ψ := ψ) hker hDMX)
  obtain ⟨e₁⟩ := h₁
  have h₂ := (letI inst : (D.subgroupOf (D ⊔ M)).Normal := hN
    h.nonempty_mulEquiv_quotient hD hM)
  obtain ⟨e₂⟩ := h₂
  refine Sigma3Dec.center_eq_bot_of_mulEquiv (e₁.trans e₂) fun y hy => ?_
  have hy' : y ∈ center (↥M ⧸ center ↥M) := Subgroup.mem_center_iff.mpr fun z => (hy z).symm
  rw [h.center_quotient_center_eq_bot hM] at hy'
  exact Subgroup.mem_bot.mp hy'

private lemma isDirectProduct_leviFactors [Finite G] (h : IsGomiLeviPackage L U P ℳ)
    (hD : IsGomiLeviCore P D) {X : Subgroup G} (hPX : P ≤ X) {Γ : Type} [Group Γ]
    {ψ : ↥X →* Γ} (hker : ψ.ker = D.subgroupOf X) :
    IsDirectProduct ((fun K : Subgroup G => (K.subgroupOf X).map ψ) ''
      ((fun M => D ⊔ M) '' ℳ))
      (((sSup ((fun M => D ⊔ M) '' ℳ)).subgroupOf X).map ψ) := by
  let 𝒦 : Set (Subgroup G) := (fun M => D ⊔ M) '' ℳ
  change IsDirectProduct ((fun K : Subgroup G => (K.subgroupOf X).map ψ) '' 𝒦)
    (((sSup 𝒦).subgroupOf X).map ψ)
  refine isDirectProduct_image hker ?_ ?_ ?_
  · rintro K ⟨M, hM, rfl⟩
    exact ⟨le_sup_left, sup_le (hD.le.trans hPX) ((h.le_parabolic M hM).trans hPX)⟩
  · rintro K₁ ⟨M₁, hM₁, rfl⟩ K₂ ⟨M₂, hM₂, rfl⟩ hne
    exact h.commutator_le_of_ne hD hM₁ hM₂ hne
  · rintro K ⟨M, hM, rfl⟩
    exact h.inf_sSup_le hD hM

private lemma map_conj_pElementSubgroup (g : G) (hg : g ∈ normalizer (P : Set G)) :
    (pElementSubgroup 2 P).map (MulAut.conj g).toMonoidHom = pElementSubgroup 2 P := by
  let s : Set G := {x : G | x ∈ P ∧ ∃ k : ℕ, orderOf x = 2 ^ k}
  have hP : P.map (MulAut.conj g).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hg' : g⁻¹ ∈ normalizer (P : Set G) := (normalizer (P : Set G)).inv_mem hg
  have hP' : P.map (MulAut.conj g⁻¹).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg'
  have hsub : (MulAut.conj g) '' s ⊆ s := by
    rintro x ⟨y, ⟨hyP, k, hk⟩, rfl⟩
    exact ⟨hP ▸ Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hyP, k, by
      rw [MulEquiv.orderOf_eq]; exact hk⟩
  have hsub' : (MulAut.conj g⁻¹) '' s ⊆ s := by
    rintro x ⟨y, ⟨hyP, k, hk⟩, rfl⟩
    exact ⟨hP' ▸ Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hyP, k, by
      rw [MulEquiv.orderOf_eq]; exact hk⟩
  have hset : (MulAut.conj g) '' s = s :=
    Set.Subset.antisymm hsub fun x hx =>
      ⟨(MulAut.conj g⁻¹) x, hsub' ⟨x, hx, rfl⟩, by
        simp only [MulAut.conj_apply]; group⟩
  unfold pElementSubgroup
  change (Subgroup.closure s).map (MulAut.conj g).toMonoidHom = Subgroup.closure s
  rw [MonoidHom.map_closure]
  change Subgroup.closure ((MulAut.conj g) '' s) = Subgroup.closure s
  rw [hset]

private lemma mem_normalizer_map_subgroupOf [Finite G] {M : Subgroup G}
    (hU : IsSylowOf 2 U L) (hBP : L ⊓ normalizer (U : Set G) < P) (hPL : P ≤ L)
    (h : IsGomiLeviPackage L U P ℳ) (hD : IsGomiLeviCore P D) {X : Subgroup G}
    {Γ : Type} [Group Γ] {ψ : ↥X →* Γ} {g : G} (hgX : g ∈ X)
    (hg : g ∈ normalizer (P : Set G)) (hM : M ∈ ℳ) :
    ψ ⟨g, hgX⟩ ∈
      normalizer (((sSup ((fun M => D ⊔ M) '' ℳ)).subgroupOf X).map ψ : Set Γ) := by
  let 𝒦 : Set (Subgroup G) := (fun M => D ⊔ M) '' ℳ
  change ψ ⟨g, hgX⟩ ∈ normalizer (((sSup 𝒦).subgroupOf X).map ψ : Set Γ)
  have hconjD : D.map (MulAut.conj g).toMonoidHom = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hD.normalizer_le hg)
  have hconjO := map_conj_pElementSubgroup g hg
  have hsup : sSup 𝒦 = D ⊔ pElementSubgroup 2 P := by
    have h1 : sSup 𝒦 = D ⊔ sSup ℳ := by
      change sSup ((fun M => D ⊔ M) '' ℳ) = D ⊔ sSup ℳ
      rw [sSup_image,
        ← sup_biSup (p := fun M => M ∈ ℳ) (f := fun M _ => M) (a := D) ⟨M, hM⟩,
        ← sSup_eq_iSup (s := ℳ)]
    rw [h1, ← h.sup_sSup_eq_pElementSubgroup hU hBP hPL, ← sup_assoc,
      sup_eq_left.mpr hD.pCoreOf_le]
  have hconjsup : (sSup 𝒦).map (MulAut.conj g).toMonoidHom = sSup 𝒦 := by
    rw [hsup, Subgroup.map_sup, hconjD, hconjO]
  have hNconj : (((sSup 𝒦).subgroupOf X).map ψ).map
      (MulAut.conj (ψ ⟨g, hgX⟩)).toMonoidHom = ((sSup 𝒦).subgroupOf X).map ψ := by
    rw [← map_subgroupOf_map_conj (x := ⟨g, hgX⟩) (K := sSup 𝒦)]
    rw [show ((⟨g, hgX⟩ : ↥X) : G) = g from rfl, hconjsup]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hNconj

private lemma map_conj_mem_of_map_subgroupOf_mem [Finite G] {M : Subgroup G}
    (h : IsGomiLeviPackage L U P ℳ) (hD : IsGomiLeviCore P D) {X : Subgroup G} (hPX : P ≤ X)
    {Γ : Type} [Group Γ] {ψ : ↥X →* Γ} (hker : ψ.ker = D.subgroupOf X) {g : G}
    (hPconj : P.map (MulAut.conj g).toMonoidHom = P)
    (hconjD : D.map (MulAut.conj g).toMonoidHom = D) (hM : M ∈ ℳ)
    (hmem : (((D ⊔ M).map (MulAut.conj g).toMonoidHom).subgroupOf X).map ψ ∈
      (fun K : Subgroup G => (K.subgroupOf X).map ψ) '' ((fun M => D ⊔ M) '' ℳ)) :
    (D ⊔ M).map (MulAut.conj g).toMonoidHom ∈ (fun M => D ⊔ M) '' ℳ := by
  obtain ⟨K₀, hK₀, hEq⟩ := hmem
  obtain ⟨M₀, hM₀, hK₀eq⟩ := hK₀
  have hDMleP : D ⊔ M ≤ P := sup_le hD.le (h.le_parabolic M hM)
  have hKtX : (D ⊔ M).map (MulAut.conj g).toMonoidHom ≤ X := by
    calc (D ⊔ M).map (MulAut.conj g).toMonoidHom
        ≤ P.map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hDMleP
      _ = P := hPconj
      _ ≤ X := hPX
  have hDKt : D ≤ (D ⊔ M).map (MulAut.conj g).toMonoidHom := by
    calc D = D.map (MulAut.conj g).toMonoidHom := hconjD.symm
      _ ≤ (D ⊔ M).map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) le_sup_left
  have hK₀X : K₀ ≤ X := by
    rw [← hK₀eq]
    exact sup_le (hD.le.trans hPX) ((h.le_parabolic M₀ hM₀).trans hPX)
  have hDK₀ : D ≤ K₀ := by
    rw [← hK₀eq]
    exact le_sup_left
  have hfinal : K₀ = (D ⊔ M).map (MulAut.conj g).toMonoidHom :=
    (map_subgroupOf_inj hker hK₀X hKtX hDK₀ hDKt).mp hEq
  rw [← hfinal]
  exact ⟨M₀, hM₀, hK₀eq⟩

theorem IsGomiLeviPackage.map_conj_mem [Finite G] (hU : IsSylowOf 2 U L)
    (hBP : L ⊓ normalizer (U : Set G) < P) (hPL : P ≤ L) (h : IsGomiLeviPackage L U P ℳ)
    (hD : IsGomiLeviCore P D) {g : G} (hg : g ∈ normalizer (P : Set G)) {K : Subgroup G}
    (hK : K ∈ (fun M => D ⊔ M) '' ℳ) :
    K.map (MulAut.conj g).toMonoidHom ∈ (fun M => D ⊔ M) '' ℳ := by
  let X : Subgroup G := normalizer (P : Set G)
  have hPX : P ≤ X := Subgroup.le_normalizer
  have hXD : X ≤ normalizer (D : Set G) := hD.normalizer_le
  have hN : (D.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXD
  let ψ := (letI inst : (D.subgroupOf X).Normal := hN
    QuotientGroup.mk' (D.subgroupOf X))
  have hker : ψ.ker = D.subgroupOf X := (letI inst : (D.subgroupOf X).Normal := hN
    QuotientGroup.ker_mk' (D.subgroupOf X))
  obtain ⟨M, hM, rfl⟩ := hK
  have hPconj : P.map (MulAut.conj g).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hconjD : D.map (MulAut.conj g).toMonoidHom = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hD.normalizer_le hg)
  have hDP := isDirectProduct_leviFactors h hD hPX hker
  have hind : ∀ A ∈ (fun K : Subgroup G => (K.subgroupOf X).map ψ) ''
      ((fun M => D ⊔ M) '' ℳ), IsIndecomposableGroup ↥A := by
    rintro A ⟨K, hK, rfl⟩
    obtain ⟨M', hM', rfl⟩ := hK
    exact isIndecomposable_map_subgroupOf_sup hU hBP hPL h hD hPX hXD hker hM'
  have hZ : ∀ A ∈ (fun K : Subgroup G => (K.subgroupOf X).map ψ) ''
      ((fun M => D ⊔ M) '' ℳ), center ↥A = ⊥ := by
    rintro A ⟨K, hK, rfl⟩
    obtain ⟨M', hM', rfl⟩ := hK
    exact center_map_subgroupOf_sup_eq_bot h hD hPX hXD hker hM'
  have hg' := mem_normalizer_map_subgroupOf (ψ := ψ) hU hBP hPL h hD hg hg hM
  have hA0 : ((D ⊔ M).subgroupOf X).map ψ ∈
      (fun K : Subgroup G => (K.subgroupOf X).map ψ) '' ((fun M => D ⊔ M) '' ℳ) :=
    ⟨D ⊔ M, ⟨M, hM, rfl⟩, rfl⟩
  have hmem := IsDirectProduct.map_conj_mem hDP hind hZ hg' hA0
  rw [← map_subgroupOf_map_conj (x := ⟨g, hg⟩) (K := D ⊔ M)] at hmem
  change (((D ⊔ M).map (MulAut.conj g).toMonoidHom).subgroupOf X).map ψ ∈
    (fun K : Subgroup G => (K.subgroupOf X).map ψ) '' ((fun M => D ⊔ M) '' ℳ) at hmem
  exact map_conj_mem_of_map_subgroupOf_mem h hD hPX hker hPconj hconjD hM hmem

end CFSG.GroupTheory
