module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFComp
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace L34FF

omit [Finite G] in
theorem isElemAbelian_two_map_hom {G' : Type*} [Group G'] {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (f : G →* G') : IsElemAbelian 2 (A.map f) := CFSG.Open.IsElemAbelian.map hA _

omit [Finite G] in
theorem normalizer_le_normalizer_thompsonJ_of_le {V V₁ : Subgroup G} (hV₁V : V₁ ≤ V)
    (hA : ∀ A : Subgroup G, IsMaxElemAbelian V A → A ≤ V₁) :
    Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (thompsonJ V : Set G) := by
  refine le_normalizer_of_forall_map_conj_le fun g hg => ?_
  rw [thompsonJ, Subgroup.map_iSup]
  refine iSup_le fun A => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hAm => ?_
  have hgA : IsMaxElemAbelian V (A.map (MulAut.conj g).toMonoidHom) := by
    refine ⟨?_, isElemAbelian_two_map_hom hAm.2.1 _, fun B hB hBe => ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact hV₁V ((Subgroup.mem_normalizer_iff.mp hg a).mp (hA A hAm ha))
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hAm.2.2 B hB hBe
  exact le_iSup₂_of_le (f := fun (B : Subgroup G) (_ : IsMaxElemAbelian V B) => B) _ hgA le_rfl

end L34FF

variable {P : Sylow 3 G} {M H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem L34FF.Core.cover_thompsonJ (hd : L34FF.Core H R Rbar K)
    {D₀ V : Subgroup G} (hD₀H : D₀ ≤ H) (hOD : GLBPrimeCore 3 H ≤ D₀) (hV : IsSylowTwoOf V D₀)
    (hα : ∀ A : Subgroup G, IsMaxElemAbelian V A → ∀ a ∈ A, ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ ∈
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3))) :
    ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (thompsonJ V : Set G), ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set L := L34FF.threeComp H R K with hLdef
  set Y := L34FF.threeCompCore H R K with hYdef
  have hVH : V ≤ H := hV.1.trans hD₀H
  have hYD₀ : Y ≤ D₀ := inf_le_right.trans hOD
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) := L34FF.le_normalizer_threeCompCore
  have hYH : Y ≤ H := L34FF.threeCompCore_le.trans L34FF.threeComp_le
  set V₁ := V ⊓ ((Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3))).comap
    π).map H.subtype with hV₁
  have hV₁V : V₁ ≤ V := inf_le_left
  have hV₁Y : V₁ ≤ Subgroup.normalizer (Y : Set G) := (hV₁V.trans hVH).trans hHY
  have hYV₁ : Y ⊓ V₁ = Y ⊓ V := by
    refine le_antisymm (inf_le_inf_left _ inf_le_left) fun y hy => ⟨hy.1, hy.2, ?_⟩
    refine ⟨⟨y, hYH hy.1⟩, ?_, rfl⟩
    have h1 : π ⟨y, hYH hy.1⟩ = 1 := (mk'_primeComplementCore_eq_one_iff 3 _).mpr hy.1.2
    show π ⟨y, hYH hy.1⟩ ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3))
    rw [h1]
    exact Subgroup.one_mem _
  have hsylY : IsSylowTwoOf (V ⊓ Y) Y :=
    L34FF.isSylowTwoOf_inf_of_le_of_normalizes hV hYD₀ (hVH.trans hHY)
  have hsylQ : IsSylowTwoOf V₁ (Y ⊔ V₁) := by
    refine ⟨le_sup_right, hV.2.1.to_le hV₁V, ?_⟩
    change ¬ 2 ∣ V₁.relIndex (Y ⊔ V₁)
    rw [L34FF.relIndex_right_sup hV₁Y, hYV₁, inf_comm]
    exact hsylY.2.2
  intro k hk
  have hk' : k ∈ (L.subgroupOf H).map π := by rw [hd.map_threeComp]; exact hk
  obtain ⟨⟨l, hlH⟩, hl, rfl⟩ := hk'
  have hlL : l ∈ L := hl
  have hcomm : ∀ v ∈ V₁, l * v * l⁻¹ * v⁻¹ ∈ Y := by
    rintro v ⟨-, ⟨⟨v', hvH⟩, hvC, hvv⟩⟩
    obtain rfl : v = v' := hvv.symm
    refine ⟨?_, ?_⟩
    · have h1 : v * l⁻¹ * v⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp
        (L34FF.le_normalizer_threeComp hvH) _).mp (L.inv_mem hlL)
      have e : l * v * l⁻¹ * v⁻¹ = l * (v * l⁻¹ * v⁻¹) := by group
      show l * v * l⁻¹ * v⁻¹ ∈ L
      rw [e]
      exact L.mul_mem hlL h1
    · have hmem : l * v * l⁻¹ * v⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem (H.mul_mem hlH hvH) (H.inv_mem hlH)) (H.inv_mem hvH)
      refine (mk'_primeComplementCore_eq_one_iff 3 ⟨_, hmem⟩).mp ?_
      have e : (⟨l * v * l⁻¹ * v⁻¹, hmem⟩ : H) =
          ⟨l, hlH⟩ * ⟨v, hvH⟩ * (⟨l, hlH⟩ : H)⁻¹ * (⟨v, hvH⟩ : H)⁻¹ := rfl
      have hlK : π ⟨l, hlH⟩ ∈ K := by
        rw [← hd.map_threeComp]
        exact ⟨⟨l, hlH⟩, hl, rfl⟩
      have hc : π ⟨l, hlH⟩ * π ⟨v, hvH⟩ = π ⟨v, hvH⟩ * π ⟨l, hlH⟩ :=
        Subgroup.mem_centralizer_iff.mp hvC _ hlK
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hc, mul_inv_cancel_right,
        mul_inv_cancel]
  have hlQ : ∀ x ∈ Y ⊔ V₁, l * x * l⁻¹ ∈ Y ⊔ V₁ := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left Y V₁ hV₁Y] at hx
    obtain ⟨y, hy, v, hv, rfl⟩ := hx
    have e : l * (y * v) * l⁻¹ = (l * y * l⁻¹) * ((l * v * l⁻¹ * v⁻¹) * v) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp
      (hHY hlH) y).mp hy)) (Subgroup.mul_mem _ (Subgroup.mem_sup_left (hcomm v hv))
        (Subgroup.mem_sup_right hv))
  have hsyl' : IsSylowTwoOf (V₁.map (MulAut.conj l).toMonoidHom) (Y ⊔ V₁) := by
    refine isSylowTwoOf_of_card_eq ?_ ((hV.2.1.to_le hV₁V).map _) ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact hlQ v (Subgroup.mem_sup_right hv)
    · rw [Subgroup.card_map_of_injective (MulAut.conj l).injective, hsylQ.card_eq]
  obtain ⟨h, hhQ, hh⟩ := hsylQ.exists_conj hsyl'
  have hnN : h⁻¹ * l ∈ Subgroup.normalizer (V₁ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 : l * x * l⁻¹ ∈ V₁.map (MulAut.conj l).toMonoidHom := ⟨x, hx, rfl⟩
      rw [hh] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      have hyx' : h * y * h⁻¹ = l * x * l⁻¹ := hyx
      have e : h⁻¹ * l * x * (h⁻¹ * l)⁻¹ = y := by
        calc h⁻¹ * l * x * (h⁻¹ * l)⁻¹ = h⁻¹ * (l * x * l⁻¹) * h := by group
          _ = y := by rw [← hyx']; group
      rw [e]
      exact hy
    · intro hx
      have h1 : h * (h⁻¹ * l * x * (h⁻¹ * l)⁻¹) * h⁻¹ ∈ V₁.map (MulAut.conj h).toMonoidHom :=
        ⟨_, hx, rfl⟩
      rw [← hh] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      have hyx' : l * y * l⁻¹ = h * (h⁻¹ * l * x * (h⁻¹ * l)⁻¹) * h⁻¹ := hyx
      have e : y = x := by
        have : l * y * l⁻¹ = l * x * l⁻¹ := by rw [hyx']; group
        simpa using this
      rw [← e]
      exact hy
  have hJ := L34FF.normalizer_le_normalizer_thompsonJ_of_le hV₁V fun A hA a ha =>
    ⟨hA.1 ha, ⟨⟨a, (hα A hA a ha).1⟩, (hα A hA a ha).2, rfl⟩⟩
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left Y V₁ hV₁Y] at hhQ
  obtain ⟨y, hy, v, hv, rfl⟩ := hhQ
  have hyH : y ∈ H := hYH hy
  have haH : y⁻¹ * l ∈ H := H.mul_mem (H.inv_mem hyH) hlH
  have ha : y⁻¹ * l = v * ((y * v)⁻¹ * l) := by group
  refine ⟨y⁻¹ * l, ⟨haH, ?_⟩, haH, ?_⟩
  · rw [ha]
    exact Subgroup.mul_mem _ (hJ (Subgroup.le_normalizer hv)) (hJ hnN)
  · have e : (⟨y⁻¹ * l, haH⟩ : H) = (⟨y, hyH⟩ : H)⁻¹ * ⟨l, hlH⟩ := rfl
    rw [e, map_mul, map_inv, (mk'_primeComplementCore_eq_one_iff 3 ⟨y, hyH⟩).mpr hy.2, inv_one,
      one_mul]

theorem D1OneSmallData.cover_thompsonJ (hd : D1OneSmallData 3 P M H R Rbar K)
    {V : Subgroup G} (hV : IsSylowTwoOf V (GLBPrimeCore 3 (H ⊓ M)))
    (hα : ∀ A : Subgroup G, IsMaxElemAbelian V A → ∀ a ∈ A, ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ ∈
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3))) :
    ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (thompsonJ V : Set G), ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k :=
  hd.toL34FFCore.cover_thompsonJ ((glbPrimeCore_le 3 _).trans inf_le_left)
    hd.glbPrimeCore_le_inf hV hα

end CFSG.AGLEmbedding
