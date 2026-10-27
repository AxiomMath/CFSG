module

public import CFSG.LocalAnalysis.EvenBN.U5.LinTwin39dData
public import CFSG.LocalAnalysis.EvenBN.U5.LinTwin39dKey

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped commutatorElement

namespace LinCase

theorem lin39d_map_conj_eq {G : Type*} [Group G] {R : Subgroup G} {t : G} (ht : t * t = 1)
    (hR : ∀ y ∈ R, t * y * t⁻¹ ∈ R) : R.map (MulAut.conj t).toMonoidHom = R := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hR y hy
  · intro hz
    refine ⟨t * z * t⁻¹, hR z hz, ?_⟩
    show t * (t * z * t⁻¹) * t⁻¹ = z
    rw [hti]
    calc t * (t * z * t) * t = (t * t) * z * (t * t) := by group
      _ = z := by rw [ht]; group

end LinCase

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem lin_sec39d (hl : d.LinCtx) (k8 : d.Know8) (S : Subgroup G) (hS : IsSylowOf 2 S d.L₂)
    (hP : d.P ≤ S) (ha : d.Sec39a S) (hb : d.Sec39b) (hc : d.Sec39c S) : d.Sec39d S := by
  refine ⟨?_, sec39d_D_char hc⟩
  have hd := hl.hyp
  have hGMS := hl.gms
  obtain ⟨hML₂, hVL, -, -, -⟩ := k8.s8
  have hSL₂ : S ≤ d.L₂ := hS.le
  have hS2 : IsPGroup 2 S := hS.isPGroup
  have hq : 2 ≤ 2 ^ f := le_trans (by norm_num) hd.four_le
  obtain ⟨-, -, hN3, -, -, -, hEab, hcardE⟩ := hd.sec3_6 hGMS
  have hES : d.E ≤ S := ha.S_eq ▸ le_sup_left
  have hVL' : ∀ v ∈ d.V, ∀ x ∈ d.L₂, v * x = x * v := fun v hv x hx =>
    (mem_centralizer_iff.1 (mem_inf.1 (hVL hv)).2 x hx).symm
  have hVS : ∀ v ∈ d.V, ∀ s ∈ S, v * s = s * v := fun v hv s hs => hVL' v hv s (hSL₂ hs)
  have hEn : ∀ s ∈ S, ∀ e ∈ d.E, s * e * s⁻¹ ∈ d.E := fun s hs e he =>
    (mem_normalizer_iff.1 (d.L₂_le_normalizer_E (hSL₂ hs)) e).1 he
  have htB : d.t ∈ d.B₂ := mem_sup_left (mem_zpowers d.t)
  have htE : d.t ∈ normalizer (d.E : Set G) :=
    hN3 (le_normalizer ((le_sup_right : d.B₂ ≤ d.V ⊔ d.B₂) htB))
  have htS : d.t ∈ normalizer (S : Set G) := by
    rw [ha.S_eq]
    exact Common.mem_normalizer_sup htE hd.t_mem_normalizer_D
  have htE' : ∀ e ∈ d.E, d.t * e * d.t⁻¹ ∈ d.E := fun e he => (mem_normalizer_iff.1 htE e).1 he
  have htV : ∀ v ∈ d.V, d.t * v * d.t⁻¹ ∈ d.V := by
    intro v hv
    have hvS : v ∈ S := hES (d.V_le_E hv)
    have h1 : d.t * v * d.t⁻¹ ∈ S := (mem_normalizer_iff.1 htS v).1 hvS
    rw [← hc.1]
    refine mem_inf.2 ⟨h1, mem_centralizer_iff.2 fun s hs => ?_⟩
    have hs' : d.t⁻¹ * s * d.t ∈ S := by
      refine (mem_normalizer_iff.1 htS (d.t⁻¹ * s * d.t)).2 ?_
      rw [show d.t * (d.t⁻¹ * s * d.t) * d.t⁻¹ = s by group]
      exact hs
    have hc' := hVS v hv _ hs'
    calc s * (d.t * v * d.t⁻¹) = d.t * ((d.t⁻¹ * s * d.t) * v) * d.t⁻¹ := by group
      _ = d.t * (v * (d.t⁻¹ * s * d.t)) * d.t⁻¹ := by rw [← hc']
      _ = (d.t * v * d.t⁻¹) * s := by group
  have htM : d.t ∈ normalizer (d.M₂ : Set G) := sec39d_t_mem_normalizer_M₂ hd
  have hle : S ⊓ centralizer (d.I₂ : Set G) ≤ S ⊓ d.M₂ := le_inf inf_le_left ha.sylow₂.le
  have hRS : S ⊓ d.M₂ = S ⊓ centralizer (d.I₂ : Set G) :=
    ha.sylow₂.eq_of_le hle inf_le_right (hS2.to_le inf_le_left)
  have hRle : S ⊓ centralizer (d.I₂ : Set G) ≤ d.M₂ := ha.sylow₂.le
  have hRn : S ⊓ centralizer (d.I₂ : Set G) ≤ normalizer (d.E : Set G) :=
    inf_le_left.trans (hSL₂.trans d.L₂_le_normalizer_E)
  have hRt : ∀ y ∈ S ⊓ centralizer (d.I₂ : Set G), d.t * y * d.t⁻¹ ∈
      S ⊓ centralizer (d.I₂ : Set G) := by
    intro y hy
    rw [← hRS] at hy ⊢
    exact mem_inf.2 ⟨(mem_normalizer_iff.1 htS y).1 (mem_inf.1 hy).1,
      (mem_normalizer_iff.1 htM y).1 (mem_inf.1 hy).2⟩
  have htR : (S ⊓ centralizer (d.I₂ : Set G)).map (MulAut.conj d.t).toMonoidHom =
      S ⊓ centralizer (d.I₂ : Set G) := LinCase.lin39d_map_conj_eq hd.t_mul_t hRt
  have hdec : ∀ s ∈ S, ∃ e ∈ d.E, ∃ y ∈ S ⊓ centralizer (d.I₂ : Set G), s = e * y := fun s hs =>
    exists_mul_of_mem_sup_of_le_normalizer (A := d.E) (B := S ⊓ centralizer (d.I₂ : Set G))
      hRn (by rw [← ha.S_eq₂]; exact hs)
  have hER : ∀ x ∈ d.E, x ∈ S ⊓ centralizer (d.I₂ : Set G) → x = 1 := fun x hx hxR => by
    have : x ∈ d.E ⊓ (S ⊓ centralizer (d.I₂ : Set G)) := mem_inf.2 ⟨hx, hxR⟩
    rw [ha.E_inf₂] at this
    exact (mem_bot).1 this
  obtain ⟨R₁, R₂, hrad⟩ := lin_exists_radicals_of_isSylowOf_M₂ hl ha.sylow₂
  have hswap := lin_swap_radicals hl ha.sylow₂ hrad htR
  have hW : ∀ u ∈ d.E, (∀ s ∈ S, ⁅u, s⁆ ∈ d.V) → u ∈ d.W := by
    intro u hu hcomm
    rw [← hc.2.1]
    refine ⟨⟨u, hES hu⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    rw [Subgroup.upperCentralSeries_one]
    exact (sec39d_mem_V_iff hc.1 _).1 (hcomm (y : G) y.2)
  have hcardW : Nat.card d.W < ((2 ^ f) ^ 10) := by
    rw [hd.card_W hGMS]
    exact Nat.pow_lt_pow_right hq (by norm_num)
  have hH4 : ∀ y ∈ S ⊓ centralizer (d.I₂ : Set G), y ≠ 1 → y * y = 1 →
      Nat.card (sec39dECent d.V d.E (fun v hv e he => hVS v hv e (hES he)) y) ≤ (2 ^ f) ^ 10 :=
    fun y hy hy1 hy2 => lin_card_ECent_le_invol hl k8 hVL' (hRle hy) hy1 hy2
  have key := LinCase.lin39d_key_abstract (2 ^ f) hq S d.E d.V (S ⊓ centralizer (d.I₂ : Set G))
    R₁ R₂ d.W d.t hd.t_mul_t hVS d.V_le_E hES hEn hEab.2 hcardE inf_le_left hdec hER htE' htV
    hrad hswap hH4 hW hcardW
  exact sec39d_E_char S hc.1 hES hcardE hEab
    (fun X hVX hXS hX hcardX => key X hVX hXS hX.1 hX.2 hcardX)

end Data

end CFSG.LocalAnalysis.EvenBN.U5
