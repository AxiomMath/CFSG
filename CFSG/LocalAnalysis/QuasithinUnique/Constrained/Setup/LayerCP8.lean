module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerCP7

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.ABGLocalTools CFSG.LocalCores CFSG.Quasithin.B6
open scoped commutatorElement

structure CentralProductTransfer (p : ℕ) {H : Type*} [Group H] (T M : Subgroup H) {ι : Type*}
    (L : ι → Subgroup H) (i₀ : ι) : Prop where
  center_le : (Subgroup.center ↥(⨆ i, L i : Subgroup H)).map (⨆ i, L i : Subgroup H).subtype ≤ M
  normL_eq : normL (L i₀) = (⨆ i, L i : Subgroup H) ⊔ normT T (L i₀)
  sylow_normL : IsSylowOf p (normT T (L i₀)) (normL (L i₀))
  sylow_locL : IsSylowOf p (normT T (L i₀)) (locL T (L i₀))
  ker_eq : (L i₀).normalizerMonoidHom.ker = (centL (L i₀)).subgroupOf (normL (L i₀))
  range_eq_locL : actImg (L i₀) (normL (L i₀)) = actImg (L i₀) (locL T (L i₀))
  range_eq_inn_mul :
    actImg (L i₀) (normL (L i₀)) = innGroup (L i₀) ⊔ actImg (L i₀) (normT T (L i₀))
  inn_eq : actImg (L i₀) (L i₀) = innGroup (L i₀)
  inn_equiv : Nonempty (innGroup (L i₀) ≃* ↥(L i₀) ⧸ Subgroup.center ↥(L i₀))
  inn_le : innGroup (L i₀) ≤ actImg (L i₀) (normL (L i₀))
  inn_normal : ((innGroup (L i₀)).subgroupOf (actImg (L i₀) (normL (L i₀)))).Normal
  centralizer_inn : actImg (L i₀) (normL (L i₀)) ⊓
    Subgroup.centralizer (innGroup (L i₀) : Set (MulAut ↥(L i₀))) = ⊥
  opCore : ∀ Y : Subgroup (MulAut ↥(L i₀)), Y ≤ actImg (L i₀) (normL (L i₀)) →
    (Y.subgroupOf (actImg (L i₀) (normL (L i₀)))).Normal → IsPGroup p ↥Y → Y = ⊥
  sylow_S : IsSylowOf p (actImg (L i₀) (normT T (L i₀))) (actImg (L i₀) (normL (L i₀)))
  S_ne_bot : actImg (L i₀) (normT T (L i₀)) ≠ ⊥
  S_not_normal :
    ¬ ((actImg (L i₀) (normT T (L i₀))).subgroupOf (actImg (L i₀) (normL (L i₀)))).Normal
  P_max : actImg (L i₀) (normT T (L i₀)) ≤ actImg (L i₀) (maxL T M (L i₀)) ∧
    actImg (L i₀) (maxL T M (L i₀)) < actImg (L i₀) (normL (L i₀)) ∧
    ∀ Y : Subgroup (MulAut ↥(L i₀)), Y ≤ actImg (L i₀) (normL (L i₀)) →
      actImg (L i₀) (normT T (L i₀)) ≤ Y → Y < actImg (L i₀) (normL (L i₀)) →
        Y ≤ actImg (L i₀) (maxL T M (L i₀))
  P_inf_inn : actImg (L i₀) (maxL T M (L i₀)) ⊓ innGroup (L i₀) = actImg (L i₀) (M ⊓ L i₀)
  P_preimage : (actImg (L i₀) (maxL T M (L i₀))).comap (L i₀).normalizerMonoidHom =
    (centL (L i₀) ⊔ maxL T M (L i₀)).subgroupOf (normL (L i₀))
  T_not_normal : ¬ ((normT T (L i₀)).subgroupOf (locL T (L i₀))).Normal
  X_max : normT T (L i₀) ≤ maxL T M (L i₀) ∧ maxL T M (L i₀) < locL T (L i₀) ∧
    ∀ Y : Subgroup H, Y ≤ locL T (L i₀) → normT T (L i₀) ≤ Y → Y < locL T (L i₀) →
      Y ≤ maxL T M (L i₀)

theorem central_product_transfer {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    {T M : Subgroup H} (hT : IsSylowOf p T ⊤) (hTM : T ≤ M) (hMH : M < ⊤)
    (hmax : ∀ Y : Subgroup H, T ≤ Y → Y < ⊤ → Y ≤ M) {ι : Type*} [Finite ι]
    (L : ι → Subgroup H) (hinj : Function.Injective L)
    (hqs : ∀ i, CFSG.IsQuasisimple ↥(L i)) (hcomm : ∀ i j, i ≠ j → ⁅L i, L j⁆ = ⊥)
    (hKn : (⨆ i, L i : Subgroup H).Normal) (hKT : (⨆ i, L i : Subgroup H) ⊔ T = ⊤)
    (hperm : ∀ t ∈ T, ∀ i, ∃ j, conjSub t (L i) = L j)
    (htrans : ∀ i j, ∃ t ∈ T, conjSub t (L i) = L j) (i₀ : ι) {E : Subgroup H}
    (hEp : IsPGroup p ↥E) (hEn : E ≤ Subgroup.normalizer (L i₀ : Set H)) (hEc : ⁅L i₀, E⁆ ≠ ⊥) :
    CentralProductTransfer p T M L i₀ := by
  have : Nonempty ι := ⟨i₀⟩
  have hS : CPSetting p T M L :=
    ⟨hp, hT, hTM, hMH, hmax, hinj, hqs, hcomm, hKn, hKT, hperm, htrans⟩
  refine ⟨?_, hS.normL_eq i₀, hS.sylow_TL i₀, hS.sylow_HL i₀, Subgroup.normalizerMonoidHom_ker _,
    hS.actImg_normL_eq_locL i₀, hS.actImg_normL i₀, actImg_self _, innGroup_equiv _,
    innGroup_le_actImg _, innGroup_normal_in_actImg _, hS.centralizer_inn i₀,
    fun Y hY hn hpg => hS.opCore i₀ hY hn hpg, hS.sylow_actImg i₀,
    hS.actImg_normT_ne_bot i₀ hEp hEn hEc, hS.actImg_normT_not_normal i₀ hEp hEn hEc,
    ⟨actImg_mono normT_le_maxL, hS.actImg_maxL_lt i₀,
      fun Y _ hSY hlt => hS.le_actImg_maxL i₀ hSY hlt⟩, hS.actImg_maxL_inf_inn i₀,
    comap_actImg_maxL T M (L i₀), hS.normT_not_normal_locL i₀ hEp hEn hEc,
    ⟨normT_le_maxL, hS.maxL_lt_locL i₀, fun Y hYH hTY hlt => hS.maxL_unique i₀ hYH hTY hlt⟩⟩
  rw [center_map_eq]
  exact hS.center_le_M

end CFSG.QuasithinUnique.Setup.Layer
