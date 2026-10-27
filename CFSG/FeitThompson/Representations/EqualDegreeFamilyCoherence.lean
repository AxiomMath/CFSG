module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
import CFSG.FeitThompson.Representations.InnerProductOneDifferencesSharedEndpoint
import CFSG.FeitThompson.Representations.DegreeZeroVirtualCharactersNormTwo
import CFSG.FeitThompson.Representations.IrreducibleCharactersOrthonormalBasis
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped RealInnerProductSpace

section Orthonormal

theorem apply_eq_finsuppSum_smul {ι M X : Type*} [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis ι ℤ M) (φ : M →ₗ[ℤ] (X → ℂ)) (x : M) :
    φ x = (b.repr x).sum fun i n => (n : ℂ) • φ (b i) := by
  conv_lhs => rw [← b.linearCombination_repr x]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    Int.cast_smul_eq_zsmul]

theorem cfInner_finsuppSum_finsuppSum {X ι : Type*} [Fintype X] (v : ι → X → ℂ)
    (h1 : ∀ i, cfInner (v i) (v i) = 1) (h0 : ∀ i j, i ≠ j → cfInner (v i) (v j) = 0)
    (a c : ι →₀ ℤ) :
    cfInner (a.sum fun i n => (n : ℂ) • v i) (c.sum fun i n => (n : ℂ) • v i)
      = ∑ i ∈ a.support, (a i : ℂ) * (c i : ℂ) := by
  classical
  rw [Finsupp.sum, Finsupp.sum, cfInner_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cfInner_smul_left, cfInner_sum_right]
  have key : ∀ j ∈ c.support, cfInner (v i) ((c j : ℂ) • v j) = if j = i then (c i : ℂ) else 0 := by
    intro j _
    rw [cfInner_smul_right]
    by_cases h : j = i
    · subst h; rw [h1]; simp
    · rw [h0 i j (Ne.symm h)]; simp [h]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' c.support i (fun _ => (c i : ℂ))]
  by_cases hic : i ∈ c.support
  · rw [if_pos hic]
  · rw [if_neg hic]
    have hci : c i = 0 := Finsupp.notMem_support_iff.mp hic
    simp [hci]

theorem cfInner_apply_apply_eq {ι M L X : Type*} [AddCommGroup M] [Module ℤ M]
    [Fintype L] [Fintype X] (b : Module.Basis ι ℤ M) (u : ι → L → ℂ) (V : ι → X → ℂ)
    (ψ : M →ₗ[ℤ] (L → ℂ)) (hψ : ∀ i, ψ (b i) = u i)
    (φ : M →ₗ[ℤ] (X → ℂ)) (hφ : ∀ i, φ (b i) = V i)
    (hu1 : ∀ i, cfInner (u i) (u i) = 1) (hu0 : ∀ i j, i ≠ j → cfInner (u i) (u j) = 0)
    (hV1 : ∀ i, cfInner (V i) (V i) = 1) (hV0 : ∀ i j, i ≠ j → cfInner (V i) (V j) = 0)
    (f g : M) : cfInner (φ f) (φ g) = cfInner (ψ f) (ψ g) := by
  rw [apply_eq_finsuppSum_smul b φ f, apply_eq_finsuppSum_smul b φ g,
    apply_eq_finsuppSum_smul b ψ f, apply_eq_finsuppSum_smul b ψ g]
  simp only [hφ, hψ]
  rw [cfInner_finsuppSum_finsuppSum V hV1 hV0, cfInner_finsuppSum_finsuppSum u hu1 hu0]

end Orthonormal

section Free

variable {L : Type*} [Group L] [Finite L] {S : Set (L → ℂ)}

theorem linearIndependent_of_subset_Irr (hS : S ⊆ Irr L) :
    LinearIndependent ℤ (fun χ : S => (χ : L → ℂ)) := by
  classical
  have : Fintype L := Fintype.ofFinite L
  rw [linearIndependent_iff']
  intro t g hg j hj
  have key := congrArg (fun f => cfInner f ((j : L → ℂ))) hg
  simp only [cfInner_sum_left, cfInner_zsmul_left, cfInner_zero_left] at key
  have hij : ∀ i : S, cfInner ((i : L → ℂ)) ((j : L → ℂ)) = if i = j then 1 else 0 := by
    intro i
    rw [cfInner_eq_ite_of_mem_Irr (hS i.2) (hS j.2)]
    congr 1
    simp [Subtype.ext_iff]
  simp only [hij] at key
  rw [Finset.sum_congr rfl (fun i _ => by rw [mul_ite, mul_one, mul_zero] :
    ∀ i ∈ t, (g i : ℂ) * (if i = j then 1 else 0) = if i = j then (g i : ℂ) else 0),
    Finset.sum_ite_eq' t j (fun i => (g i : ℂ)), if_pos hj] at key
  exact_mod_cast key

noncomputable def spanBasis (hS : S ⊆ Irr L) : Module.Basis S ℤ (Submodule.span ℤ S) :=
  (Module.Basis.span (linearIndependent_of_subset_Irr hS)).map
    (LinearEquiv.ofEq _ _ (by rw [Subtype.range_coe]))

@[simp] theorem spanBasis_apply (hS : S ⊆ Irr L) (χ : S) :
    (spanBasis hS χ : L → ℂ) = (χ : L → ℂ) := by
  simp [spanBasis, Module.Basis.span_apply]

theorem spanBasis_repr_self (hS : S ⊆ Irr L) (χ : S) :
    (spanBasis hS).repr (spanBasis hS χ) = Finsupp.single χ 1 := by
  rw [Module.Basis.repr_self]

theorem finrank_span_of_subset_Irr (hS : S ⊆ Irr L) :
    Module.finrank ℤ (Submodule.span ℤ S) = S.ncard := by
  rw [Module.finrank_eq_nat_card_basis (spanBasis hS), Nat.card_coe_set_eq]

end Free

section Transfer

variable {L G : Type*} [Group L] [Group G] {χ₀ : L → ℂ}

theorem cfInner_sub_sub_of_mem_Irr [Fintype L] {χ ψ : L → ℂ} (hχ : χ ∈ Irr L) (hψ : ψ ∈ Irr L)
    (hχ₀ : χ₀ ∈ Irr L) (h : χ ≠ ψ) (h1 : χ ≠ χ₀) (h2 : ψ ≠ χ₀) :
    cfInner (χ - χ₀) (ψ - χ₀) = 1 := by
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
    cfInner_eq_zero_of_mem_Irr hχ hψ h, cfInner_eq_zero_of_mem_Irr hχ hχ₀ h1,
    cfInner_eq_zero_of_mem_Irr hχ₀ hψ (Ne.symm h2), cfInner_self_of_mem_Irr hχ₀]
  ring

theorem ofReal_inner_single_sub_single_eq_cfInner [Fintype G] [DecidableEq (Irr G)]
    [Fintype (Irr G)] (a b c e : Irr G) :
    ((⟪(EuclideanSpace.single a (1 : ℝ) - EuclideanSpace.single b 1 : EuclideanSpace ℝ (Irr G)),
        EuclideanSpace.single c 1 - EuclideanSpace.single e 1⟫ : ℝ) : ℂ)
      = cfInner ((a : G → ℂ) - (b : G → ℂ)) ((c : G → ℂ) - (e : G → ℂ)) := by
  rw [inner_single_sub_single, cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
    cfInner_coe_Irr, cfInner_coe_Irr, cfInner_coe_Irr, cfInner_coe_Irr]
  split_ifs <;> push_cast <;> ring

theorem sub_eq_zsmul_sub_of_single_sub_single_eq_zsmul [DecidableEq (Irr G)] {a b c e : Irr G}
    {n : ℤ} (hn : n = 1 ∨ n = -1) (hab : a ≠ b)
    (h : (EuclideanSpace.single a (1 : ℝ) - EuclideanSpace.single b 1 : EuclideanSpace ℝ (Irr G))
      = (n : ℝ) • (EuclideanSpace.single c 1 - EuclideanSpace.single e 1)) :
    ((a : G → ℂ) - (b : G → ℂ)) = n • ((c : G → ℂ) - (e : G → ℂ)) := by
  rcases hn with rfl | rfl
  · rw [Int.cast_one, one_smul] at h
    obtain ⟨rfl, rfl⟩ := eq_and_eq_of_single_sub_single_eq hab h
    rw [one_smul]
  · rw [show ((-1 : ℤ) : ℝ) = -1 by norm_num, neg_one_smul, neg_sub] at h
    obtain ⟨rfl, rfl⟩ := eq_and_eq_of_single_sub_single_eq hab h
    rw [neg_smul, one_smul, neg_sub]

end Transfer

variable {L G : Type*} [Group L] [Group G] [Fintype L] [Fintype G]
  {S : Set (L → ℂ)} {χ₀ : L → ℂ} {d : ℂ}

theorem isCoherent_of_injOn_signed_map (hSfin : S.Finite) (hS : S ⊆ Irr L)
    (hχ₀ : χ₀ ∈ S) (hdeg : ∀ χ ∈ S, χ 1 = d)
    (τ : charSpanZero S →+ virtualChars G)
    (w : (L → ℂ) → G → ℂ) (hw : ∀ χ ∈ S, w χ ∈ Irr G)
    (hwinj : ∀ χ ∈ S, ∀ ψ ∈ S, w χ = w ψ → χ = ψ)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hτw : ∀ χ ∈ S, χ ≠ χ₀ → ∀ h : χ - χ₀ ∈ charSpanZero S,
      (τ ⟨χ - χ₀, h⟩ : G → ℂ) = ε • (w χ - w χ₀)) :
    IsCoherent S τ := by
  classical
  set b := spanBasis hS with hb
  set φ : Submodule.span ℤ S →ₗ[ℤ] virtualChars G :=
    b.constr ℤ (fun χ : S => ε • (⟨w χ, Irr_subset_virtualChars (hw χ χ.2)⟩ : virtualChars G))
    with hφ
  have hφb : ∀ χ : S, ((φ (b χ) : virtualChars G) : G → ℂ) = ε • w χ := by
    intro χ
    rw [hφ, Module.Basis.constr_basis]
    rfl
  refine IsCoherentWith.isCoherent (ν := φ.toAddMonoidHom) ⟨?_, ?_⟩
  ·
    intro f g
    have hεsq : (ε : ℂ) * (starRingEnd ℂ) (ε : ℂ) = 1 := by
      rcases hε with h | h <;> subst h <;> norm_num
    refine cfInner_apply_apply_eq b (fun χ : S => (χ : L → ℂ)) (fun χ : S => ε • w χ)
      (Submodule.subtype _) (fun χ => by simp [hb])
      ((virtualChars G).subtype.comp φ) (fun χ => hφb χ) ?_ ?_ ?_ ?_ f g
    · intro χ; exact cfInner_self_of_mem_Irr (hS χ.2)
    · intro χ ψ h
      exact cfInner_eq_zero_of_mem_Irr (hS χ.2) (hS ψ.2) (fun he => h (Subtype.ext he))
    · intro χ
      rw [← Int.cast_smul_eq_zsmul ℂ, cfInner_smul_left, cfInner_smul_right,
        cfInner_self_of_mem_Irr (hw χ χ.2), mul_one]
      simpa [mul_comm] using hεsq
    · intro χ ψ h
      rw [← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ, cfInner_smul_left,
        cfInner_smul_right, cfInner_eq_zero_of_mem_Irr (hw χ χ.2) (hw ψ ψ.2)
          (fun he => h (Subtype.ext (hwinj χ χ.2 ψ ψ.2 he)))]
      ring
  ·
    have key : (φ.toAddMonoidHom.comp
        (Submodule.inclusion (charSpanZero_le S)).toAddMonoidHom).toIntLinearMap
        = τ.toIntLinearMap := by
      refine Module.Basis.ext (charSpanZeroBasis hSfin hS hχ₀ hdeg) fun χ => ?_
      have hχS : (χ : L → ℂ) ∈ S := χ.2.1
      have hχne : (χ : L → ℂ) ≠ χ₀ := χ.2.2
      have hcoe : ((charSpanZeroBasis hSfin hS hχ₀ hdeg χ : charSpanZero S) : L → ℂ)
          = (χ : L → ℂ) - χ₀ := charSpanZeroBasis_apply hSfin hS hχ₀ hdeg χ
      have hmem : (χ : L → ℂ) - χ₀ ∈ charSpanZero S :=
        hcoe ▸ (charSpanZeroBasis hSfin hS hχ₀ hdeg χ).2
      have hτeq : τ (charSpanZeroBasis hSfin hS hχ₀ hdeg χ)
          = τ ⟨(χ : L → ℂ) - χ₀, hmem⟩ := congrArg τ (Subtype.ext hcoe)
      have hsplit : (Submodule.inclusion (charSpanZero_le S))
          (charSpanZeroBasis hSfin hS hχ₀ hdeg χ)
          = b ⟨(χ : L → ℂ), hχS⟩ - b ⟨χ₀, hχ₀⟩ :=
        Subtype.ext (by simp [hcoe, hb])
      change φ ((Submodule.inclusion (charSpanZero_le S))
        (charSpanZeroBasis hSfin hS hχ₀ hdeg χ)) = τ (charSpanZeroBasis hSfin hS hχ₀ hdeg χ)
      rw [hsplit, map_sub, hτeq]
      refine Subtype.ext ?_
      rw [Submodule.coe_sub, hφb, hφb, hτw _ hχS hχne hmem, smul_sub]
    intro f
    exact congrArg (fun (m : charSpanZero S →ₗ[ℤ] virtualChars G) => m f) key

theorem isCoherent_of_forall_apply_one_eq (hSfin : S.Finite) (hS : S ⊆ Irr L)
    (hdeg : ∀ χ ∈ S, χ 1 = d) (τ : charSpanZero S →+ virtualChars G)
    (hτiso : ∀ f g : charSpanZero S,
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτ1 : ∀ f : charSpanZero S, (τ f : G → ℂ) 1 = 0) :
    IsCoherent S τ := by
  classical
  have : Fintype (Irr G) := Fintype.ofFinite _
  rcases Set.eq_empty_or_nonempty S with rfl | ⟨χ₀, hχ₀⟩
  · exact isCoherent_empty τ
  by_cases hsingle : S = {χ₀}
  · refine isCoherent_of_injOn_signed_map hSfin hS hχ₀ hdeg τ (fun _ => (1 : G → ℂ))
      (fun _ _ => one_mem_Irr) (fun χ hχ ψ hψ _ => ?_) (ε := 1) (Or.inl rfl) (fun χ hχ hne => ?_)
    · rw [hsingle] at hχ hψ; rw [hχ, hψ]
    · rw [hsingle] at hχ; exact absurd hχ hne
  obtain ⟨χ₁, hχ₁S, hχ₁ne⟩ : ∃ χ ∈ S, χ ≠ χ₀ := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hsingle (Set.eq_singleton_iff_unique_mem.2 ⟨hχ₀, fun x hx => hcon x hx⟩)
  set Tf : Finset (L → ℂ) := hSfin.toFinset.erase χ₀ with hTf
  have hmemTf : ∀ χ : L → ℂ, χ ∈ Tf ↔ χ ∈ S ∧ χ ≠ χ₀ := by
    intro χ
    simp [hTf, Set.Finite.mem_toFinset, and_comm]
  have hχ₀nTf : χ₀ ∉ Tf := by simp [hTf]
  have hnotTf : ∀ χ ∈ S, χ ∉ Tf → χ = χ₀ := by
    intro χ hχS hχ
    by_contra hcon
    exact hχ ((hmemTf χ).2 ⟨hχS, hcon⟩)
  set r : (L → ℂ) → G → ℂ := fun χ =>
    if h : χ - χ₀ ∈ charSpanZero S then (τ ⟨χ - χ₀, h⟩ : G → ℂ) else 0 with hrdef
  have hrval : ∀ (χ : L → ℂ) (h : χ - χ₀ ∈ charSpanZero S), r χ = (τ ⟨χ - χ₀, h⟩ : G → ℂ) :=
    fun χ h => dif_pos h
  have hmemz : ∀ χ ∈ Tf, χ - χ₀ ∈ charSpanZero S :=
    fun χ hχ => sub_mem_charSpanZero hdeg ((hmemTf χ).1 hχ).1 hχ₀
  have hrinner : ∀ χ ∈ Tf, ∀ ψ ∈ Tf, cfInner (r χ) (r ψ) = cfInner (χ - χ₀) (ψ - χ₀) := by
    intro χ hχ ψ hψ
    rw [hrval χ (hmemz χ hχ), hrval ψ (hmemz ψ hψ), hτiso]
  have hr2 : ∀ χ ∈ Tf, cfInner (r χ) (r χ) = 2 := by
    intro χ hχ
    obtain ⟨hχS, hχne⟩ := (hmemTf χ).1 hχ
    rw [hrinner χ hχ χ hχ, cfInner_self_sub_of_mem_Irr (hS hχS) (hS hχ₀) hχne]
  have hrone : ∀ χ ∈ Tf, ∀ ψ ∈ Tf, χ ≠ ψ → cfInner (r χ) (r ψ) = 1 := by
    intro χ hχ ψ hψ hne
    obtain ⟨hχS, hχne⟩ := (hmemTf χ).1 hχ
    obtain ⟨hψS, hψne⟩ := (hmemTf ψ).1 hψ
    rw [hrinner χ hχ ψ hψ, cfInner_sub_sub_of_mem_Irr (hS hχS) (hS hψS) (hS hχ₀) hne hχne hψne]
  have hr1 : ∀ χ ∈ Tf, r χ 1 = 0 := by
    intro χ hχ
    rw [hrval χ (hmemz χ hχ)]
    exact hτ1 _
  have hrspan : ∀ χ ∈ Tf, r χ ∈ Submodule.span ℤ (Irr G) := by
    intro χ hχ
    rw [hrval χ (hmemz χ hχ)]
    exact coe_mem_span_Irr _
  have hdecomp : ∀ χ : Tf, ∃ p : Irr G × Irr G, p.1 ≠ p.2 ∧
      r (χ : L → ℂ) = (p.1 : G → ℂ) - (p.2 : G → ℂ) := by
    intro χ
    obtain ⟨η, hη, θ, hθ, hne, -, heq⟩ :=
      exists_sub_Irr_of_cfInner_self_eq_two (hrspan _ χ.2) (hr2 _ χ.2) (hr1 _ χ.2)
    exact ⟨(⟨η, hη⟩, ⟨θ, hθ⟩), fun h => hne (congrArg Subtype.val h), heq⟩
  choose p hp1 hp2 using hdecomp
  set vec : Tf → EuclideanSpace ℝ (Irr G) := fun χ =>
    EuclideanSpace.single (p χ).1 (1 : ℝ) - EuclideanSpace.single (p χ).2 1 with hvec
  have hvecinner : ∀ χ ψ : Tf,
      ((⟪vec χ, vec ψ⟫ : ℝ) : ℂ) = cfInner (r (χ : L → ℂ)) (r (ψ : L → ℂ)) := by
    intro χ ψ
    rw [hvec, ofReal_inner_single_sub_single_eq_cfInner, hp2, hp2]
  have hvecinj : Function.Injective vec := by
    intro χ ψ h
    by_contra hne
    have hne' : (χ : L → ℂ) ≠ (ψ : L → ℂ) := fun he => hne (Subtype.ext he)
    have h1 : ((⟪vec χ, vec ψ⟫ : ℝ) : ℂ) = 1 := by
      rw [hvecinner, hrone _ χ.2 _ ψ.2 hne']
    rw [h, hvecinner, hr2 _ ψ.2] at h1
    norm_num at h1
  set R : Finset (EuclideanSpace ℝ (Irr G)) := Finset.image vec Finset.univ with hR
  have hmemR : ∀ χ : Tf, vec χ ∈ R := fun χ => Finset.mem_image_of_mem vec (Finset.mem_univ χ)
  have hform : ∀ x ∈ R, ∃ a b : Irr G, a ≠ b ∧
      x = EuclideanSpace.single a (1 : ℝ) - EuclideanSpace.single b 1 := by
    rintro x hx
    obtain ⟨χ, -, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨(p χ).1, (p χ).2, hp1 χ, rfl⟩
  have hinner : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → ⟪x, y⟫ = (1 : ℝ) := by
    rintro x hx y hy hxy
    obtain ⟨χ, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨ψ, -, rfl⟩ := Finset.mem_image.1 hy
    have hne : (χ : L → ℂ) ≠ (ψ : L → ℂ) := fun he => hxy (congrArg vec (Subtype.ext he))
    have hkey := hvecinner χ ψ
    rw [hrone _ χ.2 _ ψ.2 hne] at hkey
    exact_mod_cast hkey
  have hRne : R.Nonempty := ⟨vec ⟨χ₁, (hmemTf χ₁).2 ⟨hχ₁S, hχ₁ne⟩⟩, hmemR _⟩
  obtain ⟨ε, hε, j₀, jj, hjinj, hjne, hjeq⟩ :=
    exists_common_endpoint_of_pairwise_inner_eq_one R hform hinner hRne
  set εZ : ℤ := if ε = 1 then 1 else -1 with hεZ
  have hεZeq : ((εZ : ℝ)) = ε := by
    rcases hε with h | h
    · rw [hεZ, if_pos h, h]; norm_num
    · rw [hεZ, if_neg (by rw [h]; norm_num), h]; norm_num
  have hεZsign : εZ = 1 ∨ εZ = -1 := by
    rcases hε with h | h
    · exact Or.inl (by rw [hεZ, if_pos h])
    · exact Or.inr (by rw [hεZ, if_neg (by rw [h]; norm_num)])
  set w : (L → ℂ) → G → ℂ := fun χ =>
    if h : χ ∈ Tf then ((jj ⟨vec ⟨χ, h⟩, hmemR ⟨χ, h⟩⟩ : Irr G) : G → ℂ) else ((j₀ : Irr G) : G → ℂ)
    with hw
  have hwTf : ∀ (χ : L → ℂ) (h : χ ∈ Tf),
      w χ = ((jj ⟨vec ⟨χ, h⟩, hmemR ⟨χ, h⟩⟩ : Irr G) : G → ℂ) := fun χ h => dif_pos h
  have hwχ₀ : w χ₀ = ((j₀ : Irr G) : G → ℂ) := dif_neg hχ₀nTf
  refine isCoherent_of_injOn_signed_map hSfin hS hχ₀ hdeg τ w ?_ ?_ hεZsign ?_
  · intro χ _
    by_cases hχ : χ ∈ Tf
    · rw [hwTf χ hχ]; exact Subtype.coe_prop _
    · rw [show w χ = ((j₀ : Irr G) : G → ℂ) from dif_neg hχ]; exact Subtype.coe_prop _
  · intro χ hχS ψ hψS hwe
    by_cases hχ : χ ∈ Tf
    · by_cases hψ : ψ ∈ Tf
      · rw [hwTf χ hχ, hwTf ψ hψ] at hwe
        exact congrArg Subtype.val
          (hvecinj (congrArg Subtype.val (hjinj (Subtype.ext hwe))))
      · rw [hwTf χ hχ, hnotTf ψ hψS hψ, hwχ₀] at hwe
        exact absurd (Subtype.ext hwe) (hjne _)
    · by_cases hψ : ψ ∈ Tf
      · rw [hnotTf χ hχS hχ, hwχ₀, hwTf ψ hψ] at hwe
        exact absurd (Subtype.ext hwe.symm) (hjne _)
      · rw [hnotTf χ hχS hχ, hnotTf ψ hψS hψ]
  · intro χ hχS hχne h
    have hχ : χ ∈ Tf := (hmemTf χ).2 ⟨hχS, hχne⟩
    have hjq := hjeq ⟨vec ⟨χ, hχ⟩, hmemR ⟨χ, hχ⟩⟩
    rw [← hεZeq] at hjq
    have hkey := sub_eq_zsmul_sub_of_single_sub_single_eq_zsmul (G := G) hεZsign (hp1 ⟨χ, hχ⟩) hjq
    calc (τ ⟨χ - χ₀, h⟩ : G → ℂ) = r χ := (hrval χ h).symm
      _ = ((p ⟨χ, hχ⟩).1 : G → ℂ) - ((p ⟨χ, hχ⟩).2 : G → ℂ) := hp2 ⟨χ, hχ⟩
      _ = εZ • (((jj ⟨vec ⟨χ, hχ⟩, hmemR ⟨χ, hχ⟩⟩ : Irr G) : G → ℂ) - ((j₀ : Irr G) : G → ℂ)) :=
          hkey
      _ = εZ • (w χ - w χ₀) := by rw [hwTf χ hχ, hwχ₀]

end CFSG.FeitThompson
