module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralDihGen
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsRank
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSqClass
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralModelKlein

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral.Model

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.AutL2Facts

variable {F : Type} [Field F] [Finite F]

variable (F) in
abbrev inlL : PGL2 F →* PGammaL2 F := SemidirectProduct.inl

theorem gen3_model (hodd : IsOddPrimePower (Nat.card F)) {R' : Subgroup (PGammaL2 F)}
    (hR' : IsPGroup 2 R') :
    ∃ s : Finset (PGammaL2 F), s.card ≤ 3 ∧ closure (s : Set (PGammaL2 F)) = R' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup (PGL2 F) := R'.comap (inlL F)
  have hV : IsPGroup 2 V := hR'.comap_of_injective _ SemidirectProduct.inl_injective
  obtain ⟨P₁, hVP⟩ := hV.exists_le_sylow
  obtain ⟨m, -, ⟨e⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F hodd P₁
  obtain ⟨s₀, hs₀, hcl₀⟩ := DihGen.exists_closure_eq_of_equiv e V hVP
  have := isCyclic_ringAut F
  obtain ⟨τ₀, hτ₀⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top (R'.map (fieldProj F))).mp inferInstance
  obtain ⟨g, hgR, hgτ⟩ : τ₀ ∈ R'.map (fieldProj F) := hτ₀ ▸ mem_zpowers τ₀
  refine ⟨insert g (s₀.image (inlL F)), (Finset.card_insert_le _ _).trans
    (by have := Finset.card_image_le (s := s₀) (f := inlL F); omega), ?_⟩
  apply le_antisymm
  · rw [closure_le]
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image,
      Finset.mem_coe] at hx
    rcases hx with rfl | ⟨v, hv, rfl⟩
    · exact hgR
    · have : v ∈ V := by rw [← hcl₀]; exact subset_closure hv
      exact this
  · intro x hx
    have hgc : g ∈ closure ((insert g (s₀.image (inlL F)) : Finset _) :
        Set (PGammaL2 F)) := subset_closure (by simp)
    have hlin : ∀ v ∈ V, inlL F v ∈
        closure ((insert g (s₀.image (inlL F)) : Finset _) : Set (PGammaL2 F)) := by
      intro v hv
      rw [← hcl₀] at hv
      have h1 := Subgroup.mem_map_of_mem (inlL F) hv
      rw [MonoidHom.map_closure] at h1
      refine closure_mono ?_ h1
      intro y hy
      obtain ⟨v', hv', rfl⟩ := hy
      simp only [Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image,
        Finset.mem_coe]
      exact Or.inr ⟨v', hv', rfl⟩
    obtain ⟨n, hn⟩ : x.right ∈ zpowers τ₀ := by rw [hτ₀]; exact ⟨x, hx, rfl⟩
    set y := x * g ^ (-n)
    have hy1 : y.right = 1 := by
      change (fieldProj F) (x * g ^ (-n)) = 1
      rw [map_mul, map_zpow]
      change x.right * (fieldProj F g) ^ (-n) = 1
      rw [show fieldProj F g = τ₀ from hgτ, ← hn, zpow_neg, mul_inv_cancel]
    have hyR : y ∈ R' := mul_mem hx (zpow_mem hgR _)
    have hyV : y.left ∈ V := by
      change inlL F y.left ∈ R'
      rw [← eq_inl_of_right hy1]
      exact hyR
    have hx' : x = inlL F y.left * g ^ n := by
      rw [← eq_inl_of_right hy1]
      simp [y]
    rw [hx']
    exact mul_mem (hlin _ hyV) (zpow_mem hgc _)

theorem card_le_two_mul {H : Subgroup (PGammaL2 F)} (hH1 : ∀ x ∈ H, x.right = 1) :
    Nat.card H ≤ 2 * Nat.card ↥(H ⊓ pGammaL2PSLRange F) := by
  classical
  by_cases hex : ∃ x₀ ∈ H, x₀ ∉ pGammaL2PSLRange F
  · obtain ⟨x₀, hx₀H, hx₀L⟩ := hex
    have hsq₀ : ¬ SqLeft x₀ := fun h => hx₀L ((mem_pslRange_iff x₀).mpr ⟨hH1 x₀ hx₀H, h⟩)
    let φ : ↥H → ↥(H ⊓ pGammaL2PSLRange F) × Bool := fun x =>
      if hx : (x : PGammaL2 F) ∈ pGammaL2PSLRange F then (⟨x, mem_inf.mpr ⟨x.2, hx⟩⟩, false)
      else (⟨x * x₀⁻¹, mem_inf.mpr ⟨mul_mem x.2 (inv_mem hx₀H), by
        have hsq : ¬ SqLeft (x : PGammaL2 F) := fun h =>
          hx ((mem_pslRange_iff _).mpr ⟨hH1 x x.2, h⟩)
        refine (mem_pslRange_iff _).mpr ⟨?_, ?_⟩
        · change (fieldProj F) ((x : PGammaL2 F) * x₀⁻¹) = 1
          rw [map_mul, map_inv]
          change (x : PGammaL2 F).right * (x₀.right)⁻¹ = 1
          rw [hH1 x x.2, hH1 x₀ hx₀H, inv_one, mul_one]
        · rw [sqLeft_mul, sqLeft_inv]
          tauto⟩⟩, true)
    have hφ : Function.Injective φ := by
      intro a b hab
      simp only [φ] at hab
      by_cases ha : (a : PGammaL2 F) ∈ pGammaL2PSLRange F <;>
        by_cases hb : (b : PGammaL2 F) ∈ pGammaL2PSLRange F <;>
        simp only [ha, hb, dite_true, dite_false, Prod.mk.injEq, Subtype.mk.injEq] at hab
      · exact Subtype.ext hab.1
      · exact absurd hab.2 (by decide)
      · exact absurd hab.2 (by decide)
      · exact Subtype.ext (mul_right_cancel hab.1)
    have := Nat.card_le_card_of_injective φ hφ
    rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
      mul_comm] at this
  · push Not at hex
    have : H ⊓ pGammaL2PSLRange F = H := inf_of_le_left fun x hx => hex x hx
    rw [this]
    omega

theorem card_inf_psl_le (T : Sylow 2 (PSL2 F)) {H : Subgroup (PGammaL2 F)} (hH : IsPGroup 2 H) :
    Nat.card ↥(H ⊓ pGammaL2PSLRange F) ≤ Nat.card ((T : Subgroup (PSL2 F)).map (incl F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := (H ⊓ pGammaL2PSLRange F).comap (incl F)
  have hK : IsPGroup 2 K := (hH.to_le inf_le_left).comap_of_injective _ (incl_injective F)
  obtain ⟨S, hS⟩ := hK.exists_le_sylow
  have hmap : K.map (incl F) = H ⊓ pGammaL2PSLRange F :=
    map_comap_eq_self inf_le_right
  rw [← hmap, card_map_of_injective (incl_injective F), card_map_of_injective (incl_injective F),
    Sylow.card_eq_multiplicity T, ← Sylow.card_eq_multiplicity S]
  exact card_le_of_le hS

theorem tbar_dihedral (hodd : IsOddPrimePower (Nat.card F)) (T : Sylow 2 (PSL2 F))
    {Tb : Subgroup (PGammaL2 F)} (hTb2 : IsPGroup 2 Tb) (hTb1 : ∀ x ∈ Tb, x.right = 1)
    (hDT : (T : Subgroup (PSL2 F)).map (incl F) ≤ Tb)
    (hne : Tb ≠ (T : Subgroup (PSL2 F)).map (incl F)) :
    ∃ m : ℕ, Nonempty (↥Tb ≃* DihedralGroup m) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D₀ := (T : Subgroup (PSL2 F)).map (incl F)
  set V : Subgroup (PGL2 F) := Tb.comap (inlL F)
  have hTbV : V.map (inlL F) = Tb :=
    map_comap_eq_self fun x hx => ⟨x.left, (eq_inl_of_right (hTb1 x hx)).symm⟩
  have hV : IsPGroup 2 V := hTb2.comap_of_injective _ SemidirectProduct.inl_injective
  obtain ⟨P₁, hVP⟩ := hV.exists_le_sylow
  set W := (P₁ : Subgroup (PGL2 F)).map (inlL F)
  have hW2 : IsPGroup 2 W := P₁.isPGroup'.map _
  have hW1 : ∀ x ∈ W, x.right = 1 := by
    rintro _ ⟨v, -, rfl⟩
    rfl
  have hTbW : Tb ≤ W := hTbV ▸ map_mono hVP
  have hD : Nat.card D₀ ∣ Nat.card Tb := card_dvd_of_le hDT
  have hDne : Nat.card D₀ ≠ Nat.card Tb := fun h =>
    hne (eq_of_le_of_card_ge hDT h.symm.le).symm
  have hTbge : 2 * Nat.card D₀ ≤ Nat.card Tb := by
    obtain ⟨c, hc⟩ := hD
    have hc2 : 2 ≤ c := by
      rcases Nat.lt_or_ge c 2 with h | h
      · interval_cases c
        · rw [mul_zero] at hc
          exact absurd hc Nat.card_pos.ne'
        · rw [mul_one] at hc
          exact absurd hc.symm hDne
      · exact h
    rw [hc, mul_comm]
    exact Nat.mul_le_mul_left _ hc2
  have hWle : Nat.card W ≤ 2 * Nat.card D₀ :=
    (card_le_two_mul hW1).trans (Nat.mul_le_mul_left 2 (card_inf_psl_le T hW2))
  have hTbW' : Tb = W := eq_of_le_of_card_ge hTbW (hWle.trans hTbge)
  obtain ⟨m, -, ⟨e⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F hodd P₁
  exact ⟨2 ^ m, ⟨(MulEquiv.subgroupCongr hTbW').trans
    (((P₁ : Subgroup (PGL2 F)).equivMapOfInjective _ SemidirectProduct.inl_injective).symm.trans
      e)⟩⟩

end CFSG.ComponentClassification.HSDihedral.Model
