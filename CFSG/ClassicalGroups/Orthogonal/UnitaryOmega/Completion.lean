module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Chamber
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Charts
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockGeneration
import all CFSG.LieType.CurtisTits.TitsGeometry

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open QuadraticMap
open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.SeitzReduction.UnitaryPilot CFSG.Permutation.ProperSupportMaps
open CFSG.LieType.CurtisTits
open CFSG.ClassicalGroups.Orthogonal.FramedPlanes

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

@[expose] noncomputable def normFamily {m : ℕ} (hm : 2 ≤ m)
    {H : Type} [Group H] (t : Equiv.Perm (Fin (m + 1)) →* H) (κ : normOmega E m →* H)
    (ω : K) (hω : polar (normQuad E) 1 ω = 1) (J : Set (Fin (m + 1))) (hJ : J.Nonempty) :
    parabolic ↥(normOmega E (m + 1)) (normChamber E ω hω (m + 1)) J →* H :=
  (properSupportPhi (hB := normBlock_mono E (m + 1)) (a := deletionChart E m κ)
      (t := t) (map_normBlock_normPerm E (by omega : 3 ≤ m + 1))
      (Finset.univ.erase hJ.some)
      (fun he => (Finset.erase_eq_self.mp he) (Finset.mem_univ _))).comp
    (Subgroup.inclusion (parabolic_normChamber_le_erase E ω hω (by omega) hJ.some_mem))

private theorem normOmegaCast_mem_deletionBlock {m : ℕ} (a : normOmega E m) :
    normOmegaCast E (Nat.le_succ m) a ∈ normBlock E (m + 1) (deletionSet (Fin.last m)) := by
  rw [show deletionSet (Fin.last m) = Finset.univ.erase (Fin.last m) from rfl,
    ← range_normOmegaCast_succ E m]
  exact MonoidHom.mem_range.mpr ⟨a, rfl⟩

private theorem deletionChart_hBmap {m : ℕ} (hm : 2 ≤ m) :
    ∀ (σ : Equiv.Perm (Fin (m + 1))) (S : Finset (Fin (m + 1))),
      (normBlock E (m + 1) S).map
        (MulAut.conj (normPerm E (by omega : 3 ≤ m + 1) σ)).toMonoidHom =
        normBlock E (m + 1) (S.image σ) :=
  fun σ S => map_normBlock_normPerm E (by omega) σ S

private theorem deletionChart_hgen {m : ℕ} :
    ∀ (S : Finset (Fin (m + 1))), S ⊆ deletionSet (Fin.last m) → 2 ≤ S.card →
      normBlock E (m + 1) S =
        ⨆ P : PairBelow S, normBlock E (m + 1) (P : Finset (Fin (m + 1))) :=
  fun S _ hS => normBlock_eq_iSup_pairs E (m + 1) S hS

private theorem properSupportPhi_inclusion_transport {m : ℕ}
    (hm : 4 ≤ m) {H : Type} [Group H] (t : Equiv.Perm (Fin (m + 1)) →* H)
    (κ : normOmega E m →* H)
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) =
      κ.comp (normPerm E (by omega : 3 ≤ m)))
    (hT2 : ∀ y ∈ (anchorBlock E (by omega : 2 ≤ m)).map κ,
      t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)) * y *
        (t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)))⁻¹ ∈
        (anchorBlock E (by omega : 2 ≤ m)).map κ)
    {R S : Finset (Fin (m + 1))} (hR : R ≠ Finset.univ) (hS : S ≠ Finset.univ)
    (hRS : R ⊆ S) (x : normBlock E (m + 1) S) (y : normBlock E (m + 1) R)
    (hxy : (y : normOmega E (m + 1)) = (x : normOmega E (m + 1))) :
    properSupportPhi (hB := normBlock_mono E (m + 1)) (a := deletionChart E m κ)
        (t := t) (map_normBlock_normPerm E (by omega : 3 ≤ m + 1))
        S hS x =
      properSupportPhi (hB := normBlock_mono E (m + 1)) (a := deletionChart E m κ)
        (t := t) (map_normBlock_normPerm E (by omega : 3 ≤ m + 1))
        R hR y := by
  classical
  have hBmap := deletionChart_hBmap (E := E) (by omega : 2 ≤ m)
  have hgen := deletionChart_hgen (E := E) (m := m)
  have hpair := deletionChart_pairCovariance E hm t κ hT1 hT2
  have hI : 4 ≤ Fintype.card (Fin (m + 1)) := by
    rw [Fintype.card_fin]
    omega
  have hstep := DFunLike.congr_fun
    (properSupportPhi_comp_inclusion (hB := normBlock_mono E (m + 1))
      (a := deletionChart E m κ) (t := t) hBmap hgen hpair hI
      R S hR hS hRS) y
  simp only [MonoidHom.comp_apply] at hstep
  have harg : Subgroup.inclusion (normBlock_mono E (m + 1) hRS) y = x := Subtype.ext hxy
  rw [harg] at hstep
  exact hstep

private theorem properSupportPhi_erase_eq {m : ℕ} (hm : 4 ≤ m)
    {H : Type} [Group H] (t : Equiv.Perm (Fin (m + 1)) →* H) (κ : normOmega E m →* H)
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) =
      κ.comp (normPerm E (by omega : 3 ≤ m)))
    (hT2 : ∀ y ∈ (anchorBlock E (by omega : 2 ≤ m)).map κ,
      t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)) * y *
        (t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)))⁻¹ ∈
        (anchorBlock E (by omega : 2 ≤ m)).map κ)
    (ω : K) (hω : polar (normQuad E) 1 ω = 1) {J : Set (Fin (m + 1))}
    {i j : Fin (m + 1)} (hi : i ∈ J) (hj : j ∈ J)
    (x : parabolic ↥(normOmega E (m + 1)) (normChamber E ω hω (m + 1)) J) :
    properSupportPhi (hB := normBlock_mono E (m + 1)) (a := deletionChart E m κ)
        (t := t) (map_normBlock_normPerm E (by omega : 3 ≤ m + 1))
        (Finset.univ.erase i) (fun he => (Finset.erase_eq_self.mp he) (Finset.mem_univ _))
        (Subgroup.inclusion (parabolic_normChamber_le_erase E ω hω (by omega) hi) x) =
      properSupportPhi (hB := normBlock_mono E (m + 1)) (a := deletionChart E m κ)
        (t := t) (map_normBlock_normPerm E (by omega : 3 ≤ m + 1))
        (Finset.univ.erase j) (fun he => (Finset.erase_eq_self.mp he) (Finset.mem_univ _))
        (Subgroup.inclusion (parabolic_normChamber_le_erase E ω hω (by omega) hj) x) := by
  classical
  let R : Finset (Fin (m + 1)) := (Finset.univ.erase i).erase j
  have hR_Ui : R ⊆ Finset.univ.erase i := Finset.erase_subset j _
  have hR_Uj : R ⊆ Finset.univ.erase j := by
    intro a ha
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ha).1, Finset.mem_univ a⟩
  have hiR : i ∉ R := fun h => (Finset.mem_erase.mp (hR_Ui h)).1 rfl
  have hRne : R ≠ Finset.univ := fun hR => hiR (hR ▸ Finset.mem_univ i)
  have hUi : (Finset.univ.erase i) ≠ Finset.univ :=
    fun he => (Finset.erase_eq_self.mp he) (Finset.mem_univ i)
  have hUj : (Finset.univ.erase j) ≠ Finset.univ :=
    fun he => (Finset.erase_eq_self.mp he) (Finset.mem_univ j)
  have hxR : (x : normOmega E (m + 1)) ∈ normBlock E (m + 1) R :=
    parabolic_normChamber_le_erase_erase E ω hω (by omega : 4 ≤ m + 1) hi hj x.2
  have h1 := properSupportPhi_inclusion_transport E hm t κ hT1 hT2 hRne hUi hR_Ui
    (Subgroup.inclusion (parabolic_normChamber_le_erase E ω hω (by omega) hi) x)
    ⟨(x : normOmega E (m + 1)), hxR⟩ rfl
  have h2 := properSupportPhi_inclusion_transport E hm t κ hT1 hT2 hRne hUj hR_Uj
    (Subgroup.inclusion (parabolic_normChamber_le_erase E ω hω (by omega) hj) x)
    ⟨(x : normOmega E (m + 1)), hxR⟩ rfl
  exact h1.trans h2.symm

theorem normFamily_apply_of_mem {m : ℕ} (hm : 4 ≤ m)
    {H : Type} [Group H] (t : Equiv.Perm (Fin (m + 1)) →* H) (κ : normOmega E m →* H)
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) =
      κ.comp (normPerm E (by omega : 3 ≤ m)))
    (hT2 : ∀ y ∈ (anchorBlock E (by omega : 2 ≤ m)).map κ,
      t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)) * y *
        (t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)))⁻¹ ∈
        (anchorBlock E (by omega : 2 ≤ m)).map κ)
    (ω : K) (hω : polar (normQuad E) 1 ω = 1) {J : Set (Fin (m + 1))} (hJ : J.Nonempty)
    {j : Fin (m + 1)} (hj : j ∈ J)
    (x : parabolic ↥(normOmega E (m + 1)) (normChamber E ω hω (m + 1)) J) :
    normFamily E (by omega) t κ ω hω J hJ x =
      properSupportPhi (hB := normBlock_mono E (m + 1)) (a := deletionChart E m κ)
        (t := t) (map_normBlock_normPerm E (by omega : 3 ≤ m + 1))
        (Finset.univ.erase j) (fun he => (Finset.erase_eq_self.mp he) (Finset.mem_univ _))
        (Subgroup.inclusion (parabolic_normChamber_le_erase E ω hω (by omega) hj) x) := by
  rw [normFamily, MonoidHom.comp_apply]
  exact properSupportPhi_erase_eq E hm t κ hT1 hT2 ω hω hJ.some_mem hj x

theorem isCompatibleFamily_normFamily {m : ℕ} (hm : 4 ≤ m)
    {H : Type} [Group H] (t : Equiv.Perm (Fin (m + 1)) →* H) (κ : normOmega E m →* H)
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) =
      κ.comp (normPerm E (by omega : 3 ≤ m)))
    (hT2 : ∀ y ∈ (anchorBlock E (by omega : 2 ≤ m)).map κ,
      t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)) * y *
        (t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)))⁻¹ ∈
        (anchorBlock E (by omega : 2 ≤ m)).map κ)
    (ω : K) (hω : polar (normQuad E) 1 ω = 1) :
    IsCompatibleFamily ↥(normOmega E (m + 1)) (normChamber E ω hω (m + 1))
      (normFamily E (by omega) t κ ω hω) := by
  unfold IsCompatibleFamily
  intro J K hJ hK hJK a haK haJ
  have hjJ : hJ.some ∈ J := hJ.some_mem
  have hjK : hJ.some ∈ K := hJK hjJ
  have h1 := normFamily_apply_of_mem E hm t κ hT1 hT2 ω hω hK hjK ⟨a, haK⟩
  have h2 := normFamily_apply_of_mem E hm t κ hT1 hT2 ω hω hJ hjJ ⟨a, haJ⟩
  rw [h1, h2]
  exact congrArg
    (properSupportPhi (hB := normBlock_mono E (m + 1)) (a := deletionChart E m κ)
      (t := t) (map_normBlock_normPerm E (by omega : 3 ≤ m + 1))
      (Finset.univ.erase hJ.some)
      (fun he => (Finset.erase_eq_self.mp he) (Finset.mem_univ _)))
    (Subtype.ext rfl)

theorem exists_hom_normFamily {m : ℕ} (hm : 4 ≤ m)
    {H : Type} [Group H] (t : Equiv.Perm (Fin (m + 1)) →* H) (κ : normOmega E m →* H)
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) =
      κ.comp (normPerm E (by omega : 3 ≤ m)))
    (hT2 : ∀ y ∈ (anchorBlock E (by omega : 2 ≤ m)).map κ,
      t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)) * y *
        (t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)))⁻¹ ∈
        (anchorBlock E (by omega : 2 ≤ m)).map κ)
    (ω : K) (hω : polar (normQuad E) 1 ω = 1) :
    ∃ Ψ : normOmega E (m + 1) →* H, ∀ (J : Set (Fin (m + 1))) (hJ : J.Nonempty)
      (a : parabolic ↥(normOmega E (m + 1)) (normChamber E ω hω (m + 1)) J),
        Ψ a = normFamily E (by omega) t κ ω hω J hJ a := by
  have hm2 : 2 ≤ m := by omega
  have hn2 : 2 ≤ m + 1 := by omega
  have hn5 : 5 ≤ m + 1 := by omega
  obtain ⟨Ψ, hΨ, -⟩ := existsUnique_hom
    (I := Fin (m + 1))
    (X := FrameVert (normHypForm E (m + 1)) (normQuad E ω) (m + 1))
    (typ := FrameVert.typ)
    (Γ := frameGraph (normHypForm E (m + 1)) (normQuad E ω) (m + 1))
    (G := ↥(normOmega E (m + 1)))
    (hFtyp := normChamber_typ E ω hω)
    (htyp := typ_smul)
    (htyp_adj := fun {_ _} h => (frameGraph_adj_iff.mp h).1)
    (hadj := fun g {_ _} h => frameGraph_adj_smul g h)
    (hFadj := fun i j hij => normChamber_adj E ω hω hij)
    (hflag := flagTransitive_normChamber E ω hω hn2)
    (hgen := iSup_stabilizer_normChamber E ω hω hn5)
    (htri := triangulable_normFrameGraph E ω hn5)
    (φ := normFamily E hm2 t κ ω hω)
    (hφ := isCompatibleFamily_normFamily E hm t κ hT1 hT2 ω hω)
  exact ⟨Ψ, hΨ⟩

private theorem normOmegaCast_mem_parabolic_last {m : ℕ} (hm : 4 ≤ m)
    (ω : K) (hω : polar (normQuad E) 1 ω = 1) (a : normOmega E m) :
    normOmegaCast E (Nat.le_succ m) a ∈
      parabolic ↥(normOmega E (m + 1)) (normChamber E ω hω (m + 1))
        ({Fin.last m} : Set (Fin (m + 1))) := by
  have hS_card : 2 ≤ (Finset.univ.erase (Fin.last m) : Finset (Fin (m + 1))).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have hcompl : (((Finset.univ.erase (Fin.last m) : Finset (Fin (m + 1)))ᶜ :
      Finset (Fin (m + 1))) : Set (Fin (m + 1))) = {Fin.last m} := by
    rw [Finset.compl_erase]
    simp
  have h := parabolic_normChamber_compl (E := E) (ω := ω) (hω := hω)
    (S := Finset.univ.erase (Fin.last m)) hS_card
  rw [hcompl] at h
  rw [h]
  exact normOmegaCast_mem_deletionBlock E a

private theorem properSupportPhi_eq_deletionChart {m : ℕ}
    (hm : 4 ≤ m) {H : Type} [Group H] (t : Equiv.Perm (Fin (m + 1)) →* H)
    (κ : normOmega E m →* H)
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) =
      κ.comp (normPerm E (by omega : 3 ≤ m)))
    (hT2 : ∀ y ∈ (anchorBlock E (by omega : 2 ≤ m)).map κ,
      t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)) * y *
        (t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)))⁻¹ ∈
        (anchorBlock E (by omega : 2 ≤ m)).map κ)
    {S : Finset (Fin (m + 1))} (hS : S ≠ Finset.univ)
    (hSD : S ⊆ deletionSet (Fin.last m)) (x : normBlock E (m + 1) S) :
    properSupportPhi (hB := normBlock_mono E (m + 1)) (a := deletionChart E m κ)
        (t := t) (map_normBlock_normPerm E (by omega : 3 ≤ m + 1))
        S hS x =
      deletionChart E m κ (Subgroup.inclusion (normBlock_mono E (m + 1) hSD) x) := by
  classical
  have hBmap := deletionChart_hBmap (E := E) (by omega : 2 ≤ m)
  have hgen := deletionChart_hgen (E := E) (m := m)
  have hpair := deletionChart_pairCovariance E hm t κ hT1 hT2
  have hI : 4 ≤ Fintype.card (Fin (m + 1)) := by
    rw [Fintype.card_fin]
    omega
  exact properSupportPhi_apply_of_subset (hB := normBlock_mono E (m + 1))
    (a := deletionChart E m κ) (t := t) hBmap hgen hpair hI S hS hSD x

private theorem normFamily_apply_normOmegaCast {m : ℕ} (hm : 4 ≤ m)
    {H : Type} [Group H] (t : Equiv.Perm (Fin (m + 1)) →* H) (κ : normOmega E m →* H)
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) =
      κ.comp (normPerm E (by omega : 3 ≤ m)))
    (hT2 : ∀ y ∈ (anchorBlock E (by omega : 2 ≤ m)).map κ,
      t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)) * y *
        (t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)))⁻¹ ∈
        (anchorBlock E (by omega : 2 ≤ m)).map κ)
    (ω : K) (hω : polar (normQuad E) 1 ω = 1) (Ψ : normOmega E (m + 1) →* H)
    (hΨ : ∀ (J : Set (Fin (m + 1))) (hJ : J.Nonempty)
      (a : parabolic ↥(normOmega E (m + 1)) (normChamber E ω hω (m + 1)) J),
        Ψ a = normFamily E (by omega) t κ ω hω J hJ a)
    (a : normOmega E m) :
    Ψ (normOmegaCast E (Nat.le_succ m) a) = κ a := by
  have hmem := normOmegaCast_mem_deletionBlock E a
  have hpar := normOmegaCast_mem_parabolic_last E hm ω hω a
  have hS_ne : (Finset.univ.erase (Fin.last m) : Finset (Fin (m + 1))) ≠ Finset.univ :=
    fun he => (Finset.erase_eq_self.mp he) (Finset.mem_univ (Fin.last m))
  have h1 := hΨ ({Fin.last m} : Set (Fin (m + 1))) (Set.singleton_nonempty _)
    ⟨normOmegaCast E (Nat.le_succ m) a, hpar⟩
  have h2 := normFamily_apply_of_mem E hm t κ hT1 hT2 ω hω
    (Set.singleton_nonempty (Fin.last m)) (Set.mem_singleton (Fin.last m))
    ⟨normOmegaCast E (Nat.le_succ m) a, hpar⟩
  rw [h1, h2]
  have h3 := properSupportPhi_eq_deletionChart E hm t κ hT1 hT2 hS_ne (fun _ hx => hx)
    (Subgroup.inclusion (parabolic_normChamber_le_erase E ω hω (by omega)
      (Set.mem_singleton (Fin.last m))) ⟨normOmegaCast E (Nat.le_succ m) a, hpar⟩)
  rw [h3]
  have hx : Subgroup.inclusion (normBlock_mono E (m + 1) (fun _ hx => hx))
      (Subgroup.inclusion (parabolic_normChamber_le_erase E ω hω (by omega)
        (Set.mem_singleton (Fin.last m))) ⟨normOmegaCast E (Nat.le_succ m) a, hpar⟩) =
      ⟨normOmegaCast E (Nat.le_succ m) a, hmem⟩ := Subtype.ext rfl
  rw [hx]
  exact deletionChart_apply E m κ a hmem

private theorem properSupportPhi_eq_permSUHom {m : ℕ}
    (hm : 4 ≤ m) {H : Type} [Group H] (t : Equiv.Perm (Fin (m + 1)) →* H)
    (κ : normOmega E m →* H)
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) =
      κ.comp (normPerm E (by omega : 3 ≤ m)))
    (hT2 : ∀ y ∈ (anchorBlock E (by omega : 2 ≤ m)).map κ,
      t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)) * y *
        (t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)))⁻¹ ∈
        (anchorBlock E (by omega : 2 ≤ m)).map κ)
    {S : Finset (Fin (m + 1))} (hS : S ≠ Finset.univ)
    {τ : Equiv.Perm (Fin (m + 1))} (hfix : ∀ x, x ∉ S → τ x = x)
    (hmem : (normPerm E (by omega : 3 ≤ m + 1) τ : normOmega E (m + 1)) ∈
      normBlock E (m + 1) S) :
    properSupportPhi (hB := normBlock_mono E (m + 1)) (a := deletionChart E m κ)
        (t := t) (map_normBlock_normPerm E (by omega : 3 ≤ m + 1))
        S hS ⟨normPerm E (by omega : 3 ≤ m + 1) τ, hmem⟩ =
      t τ := by
  classical
  have hBmap := deletionChart_hBmap (E := E) (by omega : 2 ≤ m)
  have hgen := deletionChart_hgen (E := E) (m := m)
  have hpair := deletionChart_pairCovariance E hm t κ hT1 hT2
  have hI : 4 ≤ Fintype.card (Fin (m + 1)) := by
    rw [Fintype.card_fin]
    omega
  have hcommon := deletionChart_common E (by omega) t κ hT1
  exact properSupportPhi_apply_common (hB := normBlock_mono E (m + 1))
    (a := deletionChart E m κ) (t := t) hBmap hgen hpair hI
    S hS τ hfix hmem hcommon

private theorem normFamily_apply_normPerm_of_fixed {m : ℕ}
    (hm : 4 ≤ m) {H : Type} [Group H] (t : Equiv.Perm (Fin (m + 1)) →* H)
    (κ : normOmega E m →* H)
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) =
      κ.comp (normPerm E (by omega : 3 ≤ m)))
    (hT2 : ∀ y ∈ (anchorBlock E (by omega : 2 ≤ m)).map κ,
      t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)) * y *
        (t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)))⁻¹ ∈
        (anchorBlock E (by omega : 2 ≤ m)).map κ)
    (ω : K) (hω : polar (normQuad E) 1 ω = 1) (Ψ : normOmega E (m + 1) →* H)
    (hΨ : ∀ (J : Set (Fin (m + 1))) (hJ : J.Nonempty)
      (a : parabolic ↥(normOmega E (m + 1)) (normChamber E ω hω (m + 1)) J),
        Ψ a = normFamily E (by omega) t κ ω hω J hJ a)
    (τ : Equiv.Perm (Fin (m + 1))) {j : Fin (m + 1)} (hτj : τ j = j) :
    Ψ (normPerm E (by omega : 3 ≤ m + 1) τ) = t τ := by
  have hn3 : 3 ≤ m + 1 := by omega
  have hpar : normPerm E hn3 τ ∈
      parabolic ↥(normOmega E (m + 1)) (normChamber E ω hω (m + 1))
        ({j} : Set (Fin (m + 1))) :=
    normPerm_mem_parabolic_singleton E ω hω hn3 hτj
  have hmemS : (normPerm E hn3 τ : normOmega E (m + 1)) ∈
      normBlock E (m + 1) (Finset.univ.erase j) :=
    parabolic_normChamber_le_erase E ω hω hn3 (Set.mem_singleton j) hpar
  have hSne : (Finset.univ.erase j : Finset (Fin (m + 1))) ≠ Finset.univ :=
    fun he => (Finset.erase_eq_self.mp he) (Finset.mem_univ j)
  have hfixj : ∀ x : Fin (m + 1),
      x ∉ (Finset.univ.erase j : Finset (Fin (m + 1))) → τ x = x := by
    intro x hx
    have hxj : x = j := by
      by_contra hne
      exact hx (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ x⟩)
    rw [hxj]
    exact hτj
  have h1 := hΨ ({j} : Set (Fin (m + 1))) (Set.singleton_nonempty j) ⟨_, hpar⟩
  have h2 := normFamily_apply_of_mem E hm t κ hT1 hT2 ω hω
    (Set.singleton_nonempty j) (Set.mem_singleton j) ⟨_, hpar⟩
  have harg : Subgroup.inclusion (parabolic_normChamber_le_erase E ω hω hn3
      (Set.mem_singleton j)) ⟨_, hpar⟩ = ⟨normPerm E hn3 τ, hmemS⟩ := Subtype.ext rfl
  rw [h1, h2, harg]
  exact properSupportPhi_eq_permSUHom E hm t κ hT1 hT2 hSne hfixj hmemS

private theorem normFamily_apply_normPerm_of_isSwap {m : ℕ}
    (hm : 4 ≤ m) {H : Type} [Group H] (t : Equiv.Perm (Fin (m + 1)) →* H)
    (κ : normOmega E m →* H)
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) =
      κ.comp (normPerm E (by omega : 3 ≤ m)))
    (hT2 : ∀ y ∈ (anchorBlock E (by omega : 2 ≤ m)).map κ,
      t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)) * y *
        (t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)))⁻¹ ∈
        (anchorBlock E (by omega : 2 ≤ m)).map κ)
    (ω : K) (hω : polar (normQuad E) 1 ω = 1) (Ψ : normOmega E (m + 1) →* H)
    (hΨ : ∀ (J : Set (Fin (m + 1))) (hJ : J.Nonempty)
      (a : parabolic ↥(normOmega E (m + 1)) (normChamber E ω hω (m + 1)) J),
        Ψ a = normFamily E (by omega) t κ ω hω J hJ a)
    (τ : Equiv.Perm (Fin (m + 1))) (hτ : τ.IsSwap) :
    Ψ (normPerm E (by omega : 3 ≤ m + 1) τ) = t τ := by
  have hsupp : τ.support.card = 2 := Equiv.Perm.card_support_eq_two.mpr hτ
  have hcard : τ.support.card < (Finset.univ : Finset (Fin (m + 1))).card := by
    rw [hsupp, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hfixx : τ x = x := by
    by_contra h
    exact hx (Equiv.Perm.mem_support.mpr h)
  exact normFamily_apply_normPerm_of_fixed E hm t κ hT1 hT2 ω hω Ψ hΨ τ hfixx

theorem exists_hom_normOmegaCast_normPerm {m : ℕ} (hm : 4 ≤ m)
    {H : Type} [Group H] (t : Equiv.Perm (Fin (m + 1)) →* H) (κ : normOmega E m →* H)
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) =
      κ.comp (normPerm E (by omega : 3 ≤ m)))
    (hT2 : ∀ y ∈ (anchorBlock E (by omega : 2 ≤ m)).map κ,
      t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)) * y *
        (t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)))⁻¹ ∈
        (anchorBlock E (by omega : 2 ≤ m)).map κ) :
    ∃ Ψ : normOmega E (m + 1) →* H,
      (∀ a, Ψ (normOmegaCast E (Nat.le_succ m) a) = κ a) ∧
        ∀ σ, Ψ (normPerm E (by omega : 3 ≤ m + 1) σ) = t σ := by
  obtain ⟨ω, hω⟩ := exists_polar_normQuad_one_eq_one E
  obtain ⟨Ψ, hΨ⟩ := exists_hom_normFamily E hm t κ hT1 hT2 ω hω
  have hn3 : 3 ≤ m + 1 := by omega
  refine ⟨Ψ, ?_, ?_⟩
  · exact normFamily_apply_normOmegaCast E hm t κ hT1 hT2 ω hω Ψ hΨ
  · intro σ
    have hcomp : Ψ.comp (normPerm E hn3) = t := by
      refine MonoidHom.eq_of_eqOn_dense (Equiv.Perm.closure_isSwap (α := Fin (m + 1))) ?_
      intro τ hτ
      exact normFamily_apply_normPerm_of_isSwap E hm t κ hT1 hT2 ω hω Ψ hΨ τ hτ
    exact DFunLike.congr_fun hcomp σ

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
