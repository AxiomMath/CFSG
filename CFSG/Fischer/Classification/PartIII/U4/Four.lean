module

public import CFSG.Fischer.Classification.PartIII.U4.Sections
public import CFSG.Fischer.Classification.PartIII.U4.Link
public import CFSG.Fischer.Classification.PartIII.R3.Main
public import CFSG.Fischer.Classification.SRG.Pair

public section

namespace CFSG.Fischer.Classification.LocalU4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
  CFSG.Fischer.Classification.Unitary CFSG.Fischer.Classification.Beta
  CFSG.Fischer.Classification.LocalU CFSG.Fischer.Classification.LocalR3

theorem not_isSquare_192 :
    ¬ IsSquare ((((12 : ℕ) : ℤ) - (6 : ℕ)) ^ 2 + 4 * (((45 : ℕ) : ℤ) - (6 : ℕ))) := by
  rintro ⟨r, hr⟩
  norm_num at hr
  have h1 : r ≤ 14 := by nlinarith
  have h2 : -14 ≤ r := by nlinarith
  interval_cases r <;> omega

theorem classicalConclusion_of_localPG_four {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hnab : NonabelianCommutator G) {d : G} (hd : d ∈ D) (φ : LocalQuotient D d ≃* PG 4)
    (hφ : φ '' LocalImages D d = DG 4) : ClassicalConclusion G D := by
  have hH' := hH
  obtain ⟨hP, hZ, hS⟩ := hH'
  have hna : ∃ a b : commutator G, a * b ≠ b * a := hnab
  have hPG : Pair (PG 4) (DG 4) := pair_DG le_rfl
  obtain ⟨x, hx, hxd⟩ : ∃ x ∈ D, x * d ≠ d * x := by
    by_contra! h
    have hdZ : d ∈ Subgroup.center G := (Pair.mem_center_iff hP).2 h
    rw [hZ, Subgroup.mem_bot] at hdZ
    exact Pair.ne_one hP hd hdZ
  obtain ⟨f₀, hf₀⟩ := Pair.muSet_nonempty hP (Pair.connected_of_nonabelian hP hS hna) hd hx hxd
  have hι := isChart_of_localQuotientEquiv hP (Pair.starImage_injective_of_simple hP hZ hS hd)
    φ hφ
  set ι : G → PG 4 := φ ∘ lqMap D d with hιdef
  set M := ι '' muSet D d x with hMdef
  have hF : MuSections (DG 4) := muSections_DG (n := 2) le_rfl
  have hMD : M ⊆ DG 4 := hι.image_subset (muSet_subset_localClass d x)
  have hτ : ∀ a ∈ M, ∀ b ∈ M, a * b * a ∈ M := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact mul_mul_mem_image_muSet hP φ ha hb
  have hTF : ∀ g ∈ M, TwinFree (LocalClass (DG 4) g) (M ∩ LocalClass (DG 4) g) := by
    rintro _ ⟨f, hf, rfl⟩
    exact twinFree_inter hP hZ hS hd φ hφ hF hx hxd hf
  have hMT : ∀ g ∈ M, MeetsTwins (LocalClass (DG 4) g) (M ∩ LocalClass (DG 4) g) := by
    rintro _ ⟨f, hf, rfl⟩
    exact meetsTwins_inter hP hZ hS hd φ hφ hF hx hxd hf
  have hg₀ : ι f₀ ∈ M := ⟨f₀, hf₀, rfl⟩
  have hτS : ∀ a ∈ M ∩ LocalClass (DG 4) (ι f₀), ∀ b ∈ M ∩ LocalClass (DG 4) (ι f₀),
      a * b * a ∈ M ∩ LocalClass (DG 4) (ι f₀) := fun a ha b hb =>
    ⟨hτ a ha.1 b hb.1, Pair.mul_mul_mem_localClass_of_mem hPG ha.2 hb.2⟩
  obtain ⟨q₀, hq₀, hq₀g₀, hS₀⟩ := exists_eq_muSet_of_section (hMD hg₀) Set.inter_subset_right
    hτS (hTF _ hg₀) (hMT _ hg₀)
  have hinv : FlagInv (ι f₀) (M ∩ LocalClass (DG 4) (ι f₀)) M := fun h hh hhS =>
    image_conj_eq_of_fix hP hZ hS hd φ hφ hPG (tripleProperty_DG (n := 2) le_rfl)
      (fun p hp => localClass_DG_nonempty (by norm_num) hp) hx hxd hf₀ h hh hhS
  obtain ⟨c, hc | hc⟩ := exists_conj_eq_M6_or_M18 hMD hτ hTF hMT hg₀ hq₀ hq₀g₀ hS₀ hinv
  ·
    exfalso
    have hM6 : M.ncard = 6 := by
      rw [← Set.ncard_image_of_injective M (conj_injective c), hc, ncard_M6]
    have hμ : (muSet D d x).ncard = 6 := by
      rw [← (hι.injOn.mono (muSet_subset_localClass d x)).ncard_image]
      exact hM6
    have hk : (LocalClass D d).ncard = 45 := by
      rw [← hι.injOn.ncard_image, hι.image_eq, ncard_DG_four]
    have hℓ : (LocalClass D d ∩ LocalClass D f₀).ncard = 12 := by
      have e : LocalClass D d ∩ LocalClass D f₀ = LocalClass (LocalClass D d) f₀ := by
        ext s
        simp only [Set.mem_inter_iff, mem_localClass]
        tauto
      rw [e, ← (hι.injOn.mono (localClass_subset _ _)).ncard_image,
        hι.image_localClass hf₀.1, ncard_localClass_DG_four (hMD hg₀)]
    obtain ⟨-, h2⟩ := Pair.even_and_conference_of_not_isSquare hH hnab hd hf₀.1 hx hxd hk hℓ
      hμ not_isSquare_192
    have hv : (0 : ℤ) ≤ D.ncard := Nat.cast_nonneg _
    push_cast at h2
    linarith
  ·
    obtain ⟨Ξ, hΞpt, hΞD⟩ := exists_mulEquiv_PG_four_R3_I5
    have hfun : (⇑(MulAut.conj c) : PG 4 → PG 4) = fun s => c * s * c⁻¹ :=
      funext fun s => MulAut.conj_apply c s
    set φ' : LocalQuotient D d ≃* R3 I5Form := (φ.trans (MulAut.conj c)).trans Ξ with hφ'def
    have hφ' : φ' '' LocalImages D d = D3 I5Form := by
      rw [hφ'def, MulEquiv.coe_trans, MulEquiv.coe_trans, Set.image_comp, Set.image_comp, hφ,
        Pair.image_conj hPG, hΞD]
    have hμ' : φ' '' (starImage D d '' {p | (p : G) ∈ muSet D d x}) = sPt I5Form zStar := by
      have e1 : φ' '' (lqMap D d '' muSet D d x) = Ξ '' ((fun s => c * s * c⁻¹) '' M) := by
        rw [hMdef, hιdef, Set.image_comp, hφ'def, MulEquiv.coe_trans, MulEquiv.coe_trans,
          Set.image_comp, Set.image_comp, hfun]
      rw [← lqMap_image (muSet_subset_localClass d x), e1, hc, image_M18_eq_sPt hΞpt]
    exact classicalConclusion_of_localR3_of_muSet hH hnab hd le_rfl isF3Form_I5Form φ' hφ' hx
      hxd zStar_ne_zero I5Form_zStar hμ'

end CFSG.Fischer.Classification.LocalU4

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification.Unitary
  CFSG.Fischer.Classification.LocalU4

theorem classicalConclusion_of_localU2_four {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hnab : NonabelianCommutator G) {d : G} (hd : d ∈ D) (φ : LocalQuotient D d ≃* Unitary.U2 4)
    (hφ : φ '' LocalImages D d = Unitary.DU 4) : ClassicalConclusion G D := by
  refine classicalConclusion_of_localPG_four hH hnab hd (φ.trans (u2Equiv 4)) ?_
  rw [MulEquiv.coe_trans, Set.image_comp, hφ, image_DU]

theorem classicalConclusion_of_localR3_five_of_ncard {G : Type} [Group G] {D : Set G}
    (hH : Hyp G D) (hnab : NonabelianCommutator G) {d : G} (hd : d ∈ D)
    {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)} (hf : IsF3Form f)
    (h45 : (D3 f).ncard = 45) (φ : LocalQuotient D d ≃* R3 f) (hφ : φ '' LocalImages D d = D3 f) :
    ClassicalConclusion G D := by
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_U2_four_of_ncard hf h45
  refine classicalConclusion_of_localU2_four hH hnab hd (φ.trans ψ) ?_
  rw [MulEquiv.coe_trans, Set.image_comp, hφ, hψ]

end CFSG.Fischer.Classification
