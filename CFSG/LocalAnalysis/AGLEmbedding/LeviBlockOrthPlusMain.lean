module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusFamData
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusCover
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSection
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenFivesAt
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniData
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitMaximalFamilyOrbits

public section

namespace CFSG.AGLEmbedding

open Matrix QuadraticMap CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin
open scoped Pointwise

namespace LeviBlock

variable {r : ℕ} {K : Type} [Field K]

theorem flag_top_inf_Xstar (hr : 0 < r) :
    flag r K r ⊓ Xstar r K hr = flag r K (r - 1) := by
  ext v
  rw [Submodule.mem_inf, mem_flag, mem_flag, mem_Xstar]
  constructor
  · rintro ⟨⟨h1, -⟩, h3, -⟩
    refine ⟨h1, fun j hj => ?_⟩
    rw [show j = ⟨r - 1, by omega⟩ from Fin.ext (by have := j.isLt; simp; omega)]
    exact h3
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun j hj => absurd j.isLt (by omega)⟩, h2 _ le_rfl, fun k _ => h1 k⟩

theorem smul_Xstar_of_smul_flag [Finite K] (hr : 3 ≤ r)
    {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hgE : g ∈ orthElementaryGroup (quadPlus r K)) (hg : g • flag r K (r - 1) = flag r K (r - 1)) :
    g • Xstar r K (by omega) = Xstar r K (by omega) := by
  have hgO := orthElementaryGroup_le _ hgE
  rcases eq_flag_or_eq_Xstar (by omega) (map_mem_singularSubspaces hgO
      (Xstar_mem_singularSubspaces (by omega)))
      (by rw [← hg]; exact Submodule.map_mono le_sup_left) with h | h
  · exfalso
    apply map_flag_top_ne_Xstar hr (inv_mem hgE)
    have h' : g • Xstar r K (by omega) = flag r K r := h
    change (g⁻¹ • flag r K r) = _
    rw [← h', smul_smul, inv_mul_cancel, one_smul]
  · exact h

@[expose] noncomputable def plusNodeDims (I : Set (Fin r)) : Finset ℕ := by
  classical exact (Finset.univ.filter (· ∈ I)).image fun i => i.val + 1

theorem mem_plusNodeDims {I : Set (Fin r)} {d : ℕ} :
    d ∈ plusNodeDims I ↔ ∃ i ∈ I, i.val + 1 = d := by
  classical
  simp [plusNodeDims]

theorem plusNodeStab_eq_plusFlagStab [Finite K] (hr : 3 ≤ r) {I : Set (Fin r)}
    (hI : (⟨r - 2, by omega⟩ : Fin r) ∈ I → (⟨r - 1, by omega⟩ : Fin r) ∈ I) :
    plusNodeStab K hr I = plusFlagStab K r (plusNodeDims I) := by
  ext g
  rw [mem_plusNodeStab, mem_plusFlagStab]
  refine and_congr_right fun hgE => ⟨fun h d hd => ?_, fun h i hi => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := mem_plusNodeDims.1 hd
    have hiV := h i hi
    unfold plusNodeSpace at hiV
    split_ifs at hiV with h1 h2
    · exact hiV
    ·
      have hX := h _ (hI (by rwa [show i = ⟨r - 2, by omega⟩ from Fin.ext h2] at hi))
      simp only [plusNodeSpace, show ¬ r - 1 + 1 ≤ r - 2 by omega, show r - 1 ≠ r - 2 by omega,
        ite_false] at hX
      rw [show i.val + 1 = r - 1 by omega, ← flag_top_inf_Xstar (by omega)]
      change Submodule.map _ (flag r K r ⊓ Xstar r K _) = _
      rw [Submodule.map_inf _ (show Function.Injective
        (DistribSMul.toLinearMap K (Fin r ⊕ Fin r → K) g) from g.injective)]
      exact congrArg₂ (· ⊓ ·) hX hiV
    · rw [show i.val + 1 = r by have := i.isLt; omega]
      exact hiV
  · have hd := h (i.val + 1) (mem_plusNodeDims.2 ⟨i, hi, rfl⟩)
    unfold plusNodeSpace
    split_ifs with h1 h2
    · exact hd
    · rw [show i.val + 1 = r - 1 by omega] at hd
      exact smul_Xstar_of_smul_flag hr hgE hd
    · rwa [show i.val + 1 = r by have := i.isLt; omega] at hd

theorem plusNodeDims_props (hr : 3 ≤ r) {I : Set (Fin r)}
    (hI : (⟨r - 2, by omega⟩ : Fin r) ∈ I → (⟨r - 1, by omega⟩ : Fin r) ∈ I) :
    (∀ d ∈ plusNodeDims I, 1 ≤ d ∧ d ≤ r) ∧ (r - 1 ∈ plusNodeDims I → r ∈ plusNodeDims I) := by
  refine ⟨fun d hd => ?_, fun hd => ?_⟩
  · obtain ⟨i, -, rfl⟩ := mem_plusNodeDims.1 hd
    exact ⟨by omega, i.isLt⟩
  · obtain ⟨i, hi, hie⟩ := mem_plusNodeDims.1 hd
    exact mem_plusNodeDims.2 ⟨_, hI (by
      rwa [show i = ⟨r - 2, by omega⟩ from Fin.ext (show i.val = r - 2 by omega)] at hi),
      by simp only; omega⟩

theorem exists_hasLeviBlocks_of_idxD (hZ : OddCenterRest) {Y : Type} [Group Y] [Finite Y]
    {L P : Subgroup Y} (hCP : CompParab L P) (hD : IsLieOf IdxD (↥L ⧸ Subgroup.center ↥L)) :
    ∃ (r : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (ρ : ↥(orthElementaryGroup (quadPlus r K)) ≃* ↥L), 4 ≤ r ∧
      HasLeviBlocks ↥((P.subgroupOf L).comap ρ.toMonoidHom) (plusBlockOrders (Nat.card K)) ∧
      borel r K ≤ ((P.subgroupOf L).comap ρ.toMonoidHom).map
        (orthElementaryGroup (quadPlus r K)).subtype := by
  obtain ⟨r, K, _, _, _, hr, ⟨φ⟩⟩ := exists_mulEquiv_plusElementary_of_idxD hZ hCP.comp hCP.odd hD
  obtain ⟨ψ, I, -, hI, hψ⟩ := exists_plusNodeStab_of_compParab hr hCP φ
  have hcomap : (P.subgroupOf L).comap ψ.symm.toMonoidHom = (P.subgroupOf L).map ψ.toMonoidHom := by
    rw [Subgroup.comap_equiv_eq_map_symm', MulEquiv.symm_symm]
  rw [plusNodeStab_eq_plusFlagStab (by omega) hI] at hψ
  obtain ⟨hD1, hD2⟩ := plusNodeDims_props (by omega) hI
  refine ⟨r, K, inferInstance, inferInstance, inferInstance, ψ.symm, hr, ?_, ?_⟩
  · rw [hcomap]
    refine HasLeviBlocks.of_mulEquiv (((P.subgroupOf L).map ψ.toMonoidHom).equivMapOfInjective _
      (Subgroup.subtype_injective _) |>.trans (MulEquiv.subgroupCongr hψ)) ?_
    exact hasLeviBlocks_plusFlagStab (by omega) hD1 hD2
  · rw [hcomap, hψ]
    intro b hb
    refine mem_plusFlagStab.2 ⟨borel_le hb, fun d hd => ?_⟩
    exact MulAction.mem_stabilizer_iff.1 (borel_le_stabilizer_flag (hD1 d hd).1 (hD1 d hd).2 hb)

theorem four_le_pRank_of_borel_le {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    [Finite K] [CharP K 2] (hK : Nat.card K = 4) (hr : 4 ≤ r)
    (ρ : ↥(orthElementaryGroup (quadPlus r K)) ≃* ↥L)
    (hB : borel r K ≤ ((P.subgroupOf L).comap ρ.toMonoidHom).map
      (orthElementaryGroup (quadPlus r K)).subtype) : 4 ≤ CFSG.Open.pRank 3 P := by
  have hE : ∀ a : Fin r → Kˣ, torusElt r K a ∈ orthElementaryGroup (quadPlus r K) := fun a =>
    maxStab_le_orthElementaryGroup (by omega) (mem_posBorel.1 (torusElt_mem_posBorel a)).1
  let τ : (Fin r → Kˣ) →* ↥(orthElementaryGroup (quadPlus r K)) :=
    (torusElt r K).codRestrict _ hE
  set φ : (Fin r → Kˣ) →* Y := L.subtype.comp (ρ.toMonoidHom.comp τ) with hφ
  have hinj : Function.Injective φ := by
    intro a b h
    have h1 : ρ (τ a) = ρ (τ b) := Subtype.ext h
    exact torusElt_injective (congrArg Subtype.val (ρ.injective h1))
  have hrange : φ.range ≤ P := by
    rintro _ ⟨a, rfl⟩
    have hb : torusElt r K a ∈ borel r K := torus_le_borel ⟨hE a, a, rfl⟩
    obtain ⟨y, hy, hya⟩ := hB hb
    have : y = τ a := Subtype.ext hya
    rw [this] at hy
    exact Subgroup.mem_subgroupOf.1 hy
  have hunits : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have h := CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num)
    (fun a b => mul_comm a b) (fun a => funext fun j => by
      rw [Pi.pow_apply, Pi.one_apply, ← hunits]; exact pow_card_eq_one')
    (k := r) (by rw [Nat.card_fun, hunits, Nat.card_fin]) φ hinj hrange
  omega

end LeviBlock

open LeviBlock

theorem kFactCompParabSU38On_idxD (hZ : OddCenterRest) : KFactCompParabSU38On (IsLieOf IdxD) := by
  intro Y _ _ L P hCP hD
  obtain ⟨r, K, _, _, _, ρ, -, hQ, -⟩ := exists_hasLeviBlocks_of_idxD hZ hCP hD
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact su38At_of_levi hCP.parab.1 ⟨_, inferInstance, Finite.of_equiv _ ρ.symm.toEquiv,
    ρ.toMonoidHom, _, ρ.surjective, hQ,
    u38_not_mem_plusBlockOrders (f := n) (by rw [Nat.card_eq_fintype_card, hn])⟩

theorem kFactCompParabLeviU42On_idxD (hZ : OddCenterRest) :
    KFactCompParabLeviU42On (IsLieOf IdxD) := by
  intro Y _ _ L P hCP hD
  obtain ⟨r, K, _, _, _, ρ, -, hQ, -⟩ := exists_hasLeviBlocks_of_idxD hZ hCP hD
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact leviU42At_of_levi hCP.parab.1 ⟨_, inferInstance, Finite.of_equiv _ ρ.symm.toEquiv,
    ρ.toMonoidHom, _, ρ.surjective, hQ,
    u42_not_mem_plusBlockOrders (f := n) (by rw [Nat.card_eq_fintype_card, hn])⟩

theorem kFactCompParabThreeFivesOn_idxD (hZ : OddCenterRest) :
    KFactCompParabThreeFivesOn (IsLieOf IdxD) := by
  intro Y _ _ L P hCP hD
  obtain ⟨r, K, _, _, _, ρ, hr, hQ, hB⟩ := exists_hasLeviBlocks_of_idxD hZ hCP hD
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  by_cases h4 : Nat.card K = 4
  · intro O J _ _ _ _ _ _
    exact four_le_pRank_of_borel_le h4 hr ρ hB
  · obtain ⟨k, G, _, _, S, β, hker, hpi, hcomm, hS, h𝒯⟩ := hQ
    have hno : ∀ j, ¬ (CFSG.Open.IsQuasisimple (S j) ∧
        Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60) := fun j ⟨hq, h60⟩ =>
      h4 (eq_four_of_sixty_mem_plusBlockOrders hK (h60 ▸ h𝒯 j hq))
    refine fivesAt_of_levi hCP.parab.1 ρ.toMonoidHom ρ.surjective β hker hpi hcomm hS
      (fun j hq h60 => absurd ⟨hq, h60⟩ (hno j)) ?_
    have : IsEmpty {j // CFSG.Open.IsQuasisimple (S j) ∧
        Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60} := ⟨fun j => hno j.1 j.2⟩
    rw [Nat.card_of_isEmpty]
    omega

end CFSG.AGLEmbedding
