module

public import CFSG.LocalAnalysis.EvenBN.U5.LinSec42E
public import CFSG.LocalAnalysis.EvenBN.U5.LinTorus
public import CFSG.LocalAnalysis.EvenBN.U5.LinOddFactors
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3TwelveCommon

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups

namespace LinCase

section Generic

variable {G : Type*} [Group G]

theorem mem_normalizer_of_characteristic [Finite G] {S D : Subgroup G} (hDS : D ≤ S)
    (hD : (D.subgroupOf S).Characteristic) {g : G} (hg : g ∈ normalizer (S : Set G)) :
    g ∈ normalizer (D : Set G) := by
  refine mem_normalizer_fintype fun x hx => ?_
  set α : MulAut S := S.normalizerMonoidHom ⟨g, hg⟩ with hα
  have hchar : (D.subgroupOf S).comap α.toMonoidHom = D.subgroupOf S := hD.fixed α
  have hx' : (⟨x, hDS hx⟩ : S) ∈ D.subgroupOf S := hx
  have h1 : (⟨x, hDS hx⟩ : S) ∈ (D.subgroupOf S).comap α.toMonoidHom := by rw [hchar]; exact hx'
  have h2 : α ⟨x, hDS hx⟩ ∈ D.subgroupOf S := h1
  have : ((α ⟨x, hDS hx⟩ : S) : G) = g * x * g⁻¹ := by simp [hα]
  rw [← this]
  exact h2

theorem decomp_F_mul_center {E R₀ D F S : Subgroup G} (hSR : S = E ⊔ R₀) (hER : E ⊓ R₀ = ⊥)
    (hSD : S = E ⊔ D) (hRN : R₀ ≤ normalizer (E : Set G)) (hDN : D ≤ normalizer (E : Set G))
    (hFc : ∀ f ∈ F, ∀ x ∈ D, f * x = x * f) (hFS : F ≤ S)
    (hSN : S ≤ normalizer (E : Set G)) :
    ∀ f ∈ F, ∃ e ∈ E, ∃ r ∈ R₀ ⊓ centralizer (R₀ : Set G), f = e * r := by
  intro f hf
  have hfS : f ∈ S := hFS hf
  obtain ⟨e, he, r, hr, hfe⟩ :=
    Common.exists_mul_of_le_normalizer hRN f (by rw [← hSR]; exact hfS)
  have hcomm : ∀ s ∈ S, f * s * f⁻¹ * s⁻¹ ∈ E := by
    intro s hs
    obtain ⟨e', he', d', hd', hsed⟩ :=
      Common.exists_mul_of_le_normalizer hDN s (by rw [← hSD]; exact hs)
    have hfd : f * d' = d' * f := hFc f hf d' hd'
    have h1 : f * s * f⁻¹ * s⁻¹ = (f * e' * f⁻¹) * e'⁻¹ := by
      rw [hsed]
      calc f * (e' * d') * f⁻¹ * (e' * d')⁻¹ = (f * e' * f⁻¹) * (f * d' * f⁻¹) * d'⁻¹ * e'⁻¹ := by
            group
        _ = (f * e' * f⁻¹) * (d' * f * f⁻¹) * d'⁻¹ * e'⁻¹ := by rw [hfd]
        _ = (f * e' * f⁻¹) * e'⁻¹ := by group
    rw [h1]
    exact mul_mem ((mem_normalizer_iff.1 (hSN hfS) e').1 he') (inv_mem he')
  refine ⟨e, he, r, ⟨hr, mem_centralizer_iff.2 fun c hc => ?_⟩, hfe⟩
  have hcS : c ∈ S := by rw [hSR]; exact mem_sup_right hc
  have h1 := hcomm c hcS
  set a : G := r * c * r⁻¹ * c⁻¹ with ha
  have haR : a ∈ R₀ := mul_mem (mul_mem (mul_mem hr hc) (inv_mem hr)) (inv_mem hc)
  have h2 : f * c * f⁻¹ * c⁻¹ = e * a * (c * e⁻¹ * c⁻¹) := by
    rw [hfe, ha]; group
  have hce : c * e⁻¹ * c⁻¹ ∈ E := (mem_normalizer_iff.1 (hRN hc) e⁻¹).1 (inv_mem he)
  have haE : a ∈ E := by
    have h3 : e * a * (c * e⁻¹ * c⁻¹) ∈ E := h2 ▸ h1
    have := mul_mem (mul_mem (inv_mem he) h3) (inv_mem hce)
    have e4 : e⁻¹ * (e * a * (c * e⁻¹ * c⁻¹)) * (c * e⁻¹ * c⁻¹)⁻¹ = a := by group
    rwa [e4] at this
  have ha1 : a = 1 := by
    have : a ∈ E ⊓ R₀ := Subgroup.mem_inf.2 ⟨haE, haR⟩
    rwa [hER, mem_bot] at this
  have : r * c * r⁻¹ = c := by
    have h5 : r * c * r⁻¹ * c⁻¹ = 1 := ha1
    calc r * c * r⁻¹ = (r * c * r⁻¹ * c⁻¹) * c := by group
      _ = c := by rw [h5, one_mul]
  have h6 : r * c = c * r := by
    calc r * c = (r * c * r⁻¹) * r := by group
      _ = c * r := by rw [this]
  exact h6.symm

theorem le_or_decomp_of_transitive {E F U₀ J Z : Subgroup G} (hFEZ : ∀ f ∈ F, ∃ e ∈ E, ∃ r ∈ Z, f = e * r)
    (hU₀F : U₀ ≤ F) (hJE : J ≤ normalizer (E : Set G))
    (hJU : J ≤ normalizer (U₀ : Set G))
    (htr : ∀ x ∈ Z, x ≠ 1 → ∀ y ∈ Z, y ≠ 1 → ∃ j ∈ J, j * x * j⁻¹ = y) :
    U₀ ≤ E ∨ ∀ f ∈ F, ∃ w ∈ F ⊓ E, ∃ z ∈ U₀, f = w * z := by
  by_cases hU : U₀ ≤ E
  · exact Or.inl hU
  right
  obtain ⟨u, hu, huE⟩ : ∃ u ∈ U₀, u ∉ E := by
    by_contra hcon
    push Not at hcon
    exact hU hcon
  obtain ⟨e₀, he₀, r₀, hr₀, hu₀⟩ := hFEZ u (hU₀F hu)
  have hr₀1 : r₀ ≠ 1 := by
    rintro rfl
    exact huE (by rw [hu₀, mul_one]; exact he₀)
  intro f hf
  obtain ⟨e, he, r, hr, hfe⟩ := hFEZ f hf
  by_cases hr1 : r = 1
  · subst hr1
    exact ⟨f, Subgroup.mem_inf.2 ⟨hf, by rw [hfe, mul_one]; exact he⟩, 1, one_mem _, by simp⟩
  obtain ⟨j, hj, hjr⟩ := htr r₀ hr₀ hr₀1 r hr hr1
  have hjuU : j * u * j⁻¹ ∈ U₀ := (mem_normalizer_iff.1 (hJU hj) u).1 hu
  have hje : j * e₀ * j⁻¹ ∈ E := (mem_normalizer_iff.1 (hJE hj) e₀).1 he₀
  have hjz : j * u * j⁻¹ = (j * e₀ * j⁻¹) * r := by
    rw [hu₀, ← hjr]; group
  set z : G := j * u * j⁻¹ with hz
  have hzr : z = (j * e₀ * j⁻¹) * r := hjz
  refine ⟨f * z⁻¹, Subgroup.mem_inf.2 ⟨mul_mem hf (inv_mem (hU₀F hjuU)), ?_⟩, z, hjuU, by group⟩
  have : f * z⁻¹ = e * (j * e₀ * j⁻¹)⁻¹ := by
    rw [hfe, hzr]; group
  rw [this]
  exact mul_mem he (inv_mem hje)

theorem comm_mem_V_of_decomp {S F V W D P Q U₀ U₁ : Subgroup G}
    (hVc : ∀ v ∈ V, ∀ s ∈ S, v * s = s * v)
    (hW : ∀ w ∈ W, ∀ s ∈ S, w * s * w⁻¹ * s⁻¹ ∈ V)
    (hDF : ∀ f ∈ F, ∀ x ∈ D, f * x = x * f)
    (hP : ∀ p ∈ P, ∀ z ∈ U₀, p * z = z * p) (hQ : ∀ q ∈ Q, ∀ z ∈ U₁, q * z = z * q)
    (hPS : P ≤ S) (hQS : Q ≤ S) (hDS : D ≤ S) (hSle : S ≤ D ⊔ (P ⊔ Q))
    (hF0 : ∀ f ∈ F, ∃ w ∈ W, ∃ z ∈ U₀, f = w * z)
    (hF1 : ∀ f ∈ F, ∃ w ∈ W, ∃ z ∈ U₁, f = w * z) :
    ∀ s ∈ S, ∀ f ∈ F, s * f * s⁻¹ * f⁻¹ ∈ V := by
  let T : Subgroup G :=
    { carrier := {s | s ∈ S ∧ ∀ f ∈ F, s * f * s⁻¹ * f⁻¹ ∈ V}
      one_mem' := ⟨one_mem _, fun f _ => by simpa using one_mem V⟩
      mul_mem' := by
        rintro a b ⟨ha, hac⟩ ⟨hb, hbc⟩
        refine ⟨mul_mem ha hb, fun f hf => ?_⟩
        have hv := hbc f hf
        have hcomm : a * (b * f * b⁻¹ * f⁻¹) * a⁻¹ = b * f * b⁻¹ * f⁻¹ := by
          have := hVc _ hv a ha
          calc a * (b * f * b⁻¹ * f⁻¹) * a⁻¹ = ((b * f * b⁻¹ * f⁻¹) * a) * a⁻¹ := by rw [this]
            _ = b * f * b⁻¹ * f⁻¹ := by group
        have e : a * b * f * (a * b)⁻¹ * f⁻¹ =
            (a * (b * f * b⁻¹ * f⁻¹) * a⁻¹) * (a * f * a⁻¹ * f⁻¹) := by group
        show a * b * f * (a * b)⁻¹ * f⁻¹ ∈ V
        rw [e, hcomm]
        exact mul_mem hv (hac f hf)
      inv_mem' := by
        rintro a ⟨ha, hac⟩
        refine ⟨inv_mem ha, fun f hf => ?_⟩
        have hvi : (a * f * a⁻¹ * f⁻¹)⁻¹ ∈ V := inv_mem (hac f hf)
        have hcomm := hVc _ hvi a ha
        show a⁻¹ * f * a⁻¹⁻¹ * f⁻¹ ∈ V
        have e : a⁻¹ * f * a⁻¹⁻¹ * f⁻¹ = a⁻¹ * ((a * f * a⁻¹ * f⁻¹)⁻¹ * a) := by group
        rw [e, hcomm]
        have e2 : a⁻¹ * (a * (a * f * a⁻¹ * f⁻¹)⁻¹) = (a * f * a⁻¹ * f⁻¹)⁻¹ := by group
        rw [e2]
        exact hvi }
  have hDT : D ≤ T := fun x hx => ⟨hDS hx, fun f hf => by
    have h1 := hDF f hf x hx
    have e : x * f * x⁻¹ * f⁻¹ = 1 := by rw [← h1]; group
    rw [e]; exact one_mem V⟩
  have hPT : P ≤ T := fun p hp => ⟨hPS hp, fun f hf => by
    obtain ⟨w, hw, z, hz, rfl⟩ := hF0 f hf
    have hpz := hP p hp z hz
    have hpz' : p * z * p⁻¹ = z := by rw [hpz]; group
    have e : p * (w * z) * p⁻¹ * (w * z)⁻¹ = (w * p * w⁻¹ * p⁻¹)⁻¹ := by
      calc p * (w * z) * p⁻¹ * (w * z)⁻¹ = (p * w * p⁻¹) * (p * z * p⁻¹) * z⁻¹ * w⁻¹ := by group
        _ = (p * w * p⁻¹) * z * z⁻¹ * w⁻¹ := by rw [hpz']
        _ = (w * p * w⁻¹ * p⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem (hW w hw p (hPS hp))⟩
  have hQT : Q ≤ T := fun q hq => ⟨hQS hq, fun f hf => by
    obtain ⟨w, hw, z, hz, rfl⟩ := hF1 f hf
    have hqz := hQ q hq z hz
    have hqz' : q * z * q⁻¹ = z := by rw [hqz]; group
    have e : q * (w * z) * q⁻¹ * (w * z)⁻¹ = (w * q * w⁻¹ * q⁻¹)⁻¹ := by
      calc q * (w * z) * q⁻¹ * (w * z)⁻¹ = (q * w * q⁻¹) * (q * z * q⁻¹) * z⁻¹ * w⁻¹ := by group
        _ = (q * w * q⁻¹) * z * z⁻¹ * w⁻¹ := by rw [hqz']
        _ = (w * q * w⁻¹ * q⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem (hW w hw q (hQS hq))⟩
  have hST : S ≤ T := hSle.trans (sup_le hDT (sup_le hPT hQT))
  exact fun s hs f hf => (hST hs).2 f hf

end Generic

end LinCase

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

namespace CaseBData

section A0

variable (hl : d.LinCtx) (k : d.Know12) (c : d.CaseBData)
include hl k c

theorem lin_isSimpleGroup_Y : IsSimpleGroup (Common.prodFactorTwo c.ψ) := by
  have hp := hl.toCaseHyp
  haveI : IsSimpleGroup SL(2, c.k) := GMSK.sl2_isSimpleGroup
    (s313a_two_eq_zero hp k c.S_syl c.P_le_S c.card_k)
    (s313a_four_le_card hp k c.S_syl c.P_le_S c.card_k)
  exact (Common.prodFactorTwoEquiv c.ψ).isSimpleGroup

theorem lin_exists_mul_ne_Y : ∃ x y : Common.prodFactorTwo c.ψ, x * y ≠ y * x := by
  obtain ⟨x, y, hxy⟩ := GMSK.sl2_exists_mul_ne (K := c.k)
  exact ⟨(Common.prodFactorTwoEquiv c.ψ).symm x, (Common.prodFactorTwoEquiv c.ψ).symm y,
    fun e => hxy (by simpa using congrArg (Common.prodFactorTwoEquiv c.ψ) e)⟩

theorem lin_D_sup_X_ne : d.D ⊔ c.X ≠ d.D ⊔ c.Y := by
  intro heq
  have hp := hl.toCaseHyp
  have hDM : d.D ⊓ d.M₁ = ⊥ := sec312_D_inf_M₁ k.toKnow11.toKnow10
  have hYN : c.Y ≤ normalizer (d.D : Set G) := (lin_Y_le_L₁ hl k c).trans (lin_L₁_le_normalizer_D hl k c)
  have hXY : c.X ≤ c.Y := by
    intro x hx
    have hx' : x ∈ d.D ⊔ c.Y := heq ▸ (mem_sup_right hx : x ∈ d.D ⊔ c.X)
    obtain ⟨d', hd', y, hy, hxd⟩ := Common.exists_mul_of_le_normalizer hYN x hx'
    have hdM : d' ∈ d.M₁ := by
      have : d' = x * y⁻¹ := by rw [hxd]; group
      rw [this]
      exact mul_mem (c.X_le_M₁ hx) (inv_mem (c.Y_le_M₁ hy))
    have hd1 : d' = 1 := by
      have : d' ∈ d.D ⊓ d.M₁ := Subgroup.mem_inf.2 ⟨hd', hdM⟩
      rwa [hDM, mem_bot] at this
    rw [hxd, hd1, one_mul]
    exact hy
  obtain ⟨a, b, hab⟩ := s313a_exists_mul_ne_X hp k c.S_syl c.P_le_S c.ψ
  have ha : (a : G) ∈ c.X ⊓ c.Y := Subgroup.mem_inf.2 ⟨a.2, hXY a.2⟩
  have hb : (b : G) ∈ c.X ⊓ c.Y := Subgroup.mem_inf.2 ⟨b.2, hXY b.2⟩
  rw [c.X_inf_Y, mem_bot] at ha hb
  exact hab (Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ha, hb]))

theorem lin_F_split
    (hX : 2 ^ (2 * (2 * f)) <
      Nat.card (d.F ⊓ centralizer ((c.X ⊓ c.S : Subgroup G) : Set G) : Subgroup G)) :
    c.F₁ ⊔ c.F₂ = d.F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := hl.toCaseHyp
  have hf := hl.hyp.two_le
  obtain ⟨P', hP', hPP⟩ := exists_isSylowOf_ne c.card_k_eq (by omega) c.φX (c.X ⊓ c.S)
  obtain ⟨Q', hQ', hQQ⟩ := exists_isSylowOf_ne c.card_k_eq (by omega) c.φY (c.Y ⊓ c.S)
  have hFcard : Nat.card d.F = 2 ^ (4 * (2 * f)) := by
    rw [hl.hyp.card_F hl.gms]
    ring
  have hY : 2 ^ (2 * (2 * f)) <
      Nat.card (d.F ⊓ centralizer ((c.Y ⊓ c.S : Subgroup G) : Set G) : Subgroup G) := by
    exact lt_of_lt_of_eq hX (s313a_card_F_Y_eq hp k c.S_syl c.P_le_S c.ψ c.card_k).symm
  obtain ⟨-, -, hsup, -, -, -⟩ := sl2_pair_module_large c.card_k_eq (by omega) (by omega)
    (hl.hyp.isElementaryAbelian_F hl.gms) hFcard c.φX c.φY
    ((lin_X_le_L₁ hl k c).trans (lin_L₁_le_normalizer_F hl k c))
    ((lin_Y_le_L₁ hl k c).trans (lin_L₁_le_normalizer_F hl k c))
    (fun x hx y hy => (mem_centralizer_iff.1 (c.X_le_centralizer_Y hx) y hy).symm)
    (s313a_F_inf_centralizer_X_inf_centralizer_Y hp k c.S_syl c.P_le_S c.ψ)
    (s313a_isSylowOf_X_inf_S hp k c.S_syl c.P_le_S c.ψ) hP' hPP
    (s313a_isSylowOf_Y_inf_S hp k c.S_syl c.P_le_S c.ψ) hQ' hQQ hX hY
  exact hsup

theorem lin_card_centerIn_Uc_le :
    Nat.card (CFSG.centerIn (d.Uc c.S c.X)) ≤ (2 ^ f) ^ 4 := by
  by_contra hlt
  push Not at hlt
  have hp := hl.toCaseHyp
  have hd := hl.hyp
  have hS := c.S_syl
  have hP := c.P_le_S
  obtain ⟨hSeq, -, hDchar⟩ := k.s9_1 c.S hS hP
  obtain ⟨hVc, hWc, -, -, -⟩ := k.s9_2 c.S hS hP
  have ha := k.s9a c.S hS hP
  have hC₂ : c.S ⊓ centralizer (d.I₂ : Set G) = c.S ⊓ d.M₂ := (k.s10_2 c.S hS hP).2.1.1
  have hR₀ : IsSylowOf 2 (c.S ⊓ d.M₂) d.M₂ := (k.s10_2 c.S hS hP).2.1.2
  have hSR : c.S = d.E ⊔ (c.S ⊓ d.M₂) := by rw [← hC₂]; exact ha.S_eq₂
  have hER : d.E ⊓ (c.S ⊓ d.M₂) = ⊥ := by rw [← hC₂]; exact ha.E_inf₂
  have hL₂ : d.L₂ = d.E ⊔ d.M₂ := k.s8.1
  have hME : d.M₂ ≤ normalizer (d.E : Set G) :=
    ((hL₂ ▸ le_sup_right : d.M₂ ≤ d.L₂)).trans d.L₂_le_normalizer_E
  have hES : d.E ≤ c.S := hSeq ▸ le_sup_left
  have hDS : d.D ≤ c.S := hSeq ▸ le_sup_right
  have hSN : c.S ≤ normalizer (d.E : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hES).1 (lin_E_normal_S hl k c)
  have hDN : d.D ≤ normalizer (d.E : Set G) := hDS.trans hSN
  have hR₀N : c.S ⊓ d.M₂ ≤ normalizer (d.E : Set G) := inf_le_right.trans hME
  have hFS : d.F ≤ c.S := (lin_F_le_D hl k c).trans hDS
  have hdec := LinCase.decomp_F_mul_center hSR hER hSeq hR₀N hDN
    (fun f hf x hx => mem_centralizer_iff.1 (lin_D_le_centralizer_F hl k c hx) f hf) hFS hSN
  obtain ⟨J, hJM, hJN, hJodd, hJtr⟩ := lin_exists_odd_torus hl hR₀
  have hJE : ∀ j ∈ J, j ∈ normalizer (d.E : Set G) := fun j hj => hME (hJM hj)
  have hJS : ∀ j ∈ J, j ∈ normalizer (c.S : Set G) := fun j hj => by
    rw [hSR]; exact Common.mem_normalizer_sup (hJE j hj) (hJN hj)
  have hJD : ∀ j ∈ J, j ∈ normalizer (d.D : Set G) := fun j hj =>
    LinCase.mem_normalizer_of_characteristic hDS hDchar (hJS j hj)
  have hJL : ∀ j ∈ J, j ∈ normalizer (d.L₁ : Set G) := fun j hj =>
    d.normalizer_D_le_normalizer_L₁ (hJD j hj)
  have hJodd' : ∀ j ∈ J, Odd (orderOf j) := fun j hj =>
    Odd.of_dvd_nat hJodd (Subgroup.orderOf_dvd_natCard J hj)
  have hLeq : d.L₁ = d.D ⊔ (c.X ⊔ c.Y) := by rw [c.X_sup_Y]; exact lin_L₁_eq hl k c
  have hDXY : d.D ⊓ (c.X ⊔ c.Y) = ⊥ := by
    rw [c.X_sup_Y]; exact sec312_D_inf_M₁ k.toKnow11.toKnow10
  have hjX : ∀ j ∈ J, j ∈ normalizer ((d.D ⊔ c.X : Subgroup G) : Set G) := fun j hj =>
    LinCase.normalizer_sup_of_odd (lin_D_le_L₁ hl k c) (lin_L₁_le_normalizer_D hl k c)
      (lin_X_le_L₁ hl k c) (lin_Y_le_L₁ hl k c) hLeq hDXY c.X_le_centralizer_Y c.X_inf_Y
      (s313a_isSimpleGroup_X hp k hS hP c.ψ c.card_k) (s313a_exists_mul_ne_X hp k hS hP c.ψ)
      (lin_isSimpleGroup_Y hl k c) (lin_exists_mul_ne_Y hl k c) (lin_D_sup_X_ne hl k c)
      (hJL j hj) (hJD j hj) (hJodd' j hj)
  have hKe : d.D ⊔ d.Kc c.X = d.D ⊔ c.X :=
    le_antisymm (sup_le le_sup_left (s313a_Kc_le_D_sup_X hp k hS hP c.ψ))
      (sup_le_sup_left (s313a_X_le_Kc hp k hS hP c.ψ) _)
  have hUc : d.Uc c.S c.X = c.S ⊓ (d.D ⊔ c.X) := by
    unfold Data.Uc; rw [hKe]
  have hJU : ∀ j ∈ J, j ∈ normalizer ((d.Uc c.S c.X : Subgroup G) : Set G) := fun j hj => by
    rw [hUc]; exact Common.mem_normalizer_inf (hJS j hj) (hjX j hj)
  have hJU₀ : ∀ j ∈ J, j ∈ normalizer ((CFSG.centerIn (d.Uc c.S c.X) : Subgroup G) : Set G) :=
    fun j hj => normalizer_le_normalizer_centerIn _ (hJU j hj)
  have hU₀ : CFSG.centerIn (d.Uc c.S c.X) =
      d.F ⊓ centralizer ((c.X ⊓ c.S : Subgroup G) : Set G) :=
    s313a_centerIn_Uc hp k hS hP c.ψ c.card_k
  have hU₀F : CFSG.centerIn (d.Uc c.S c.X) ≤ d.F := hU₀ ▸ inf_le_left
  have hFE : d.F ⊓ d.E = d.W := lin_F_inf_E hl k c
  have hcardF : Nat.card d.F = (2 ^ f) ^ 8 := lin_card_F hl k c
  have hcardW : Nat.card d.W = (2 ^ f) ^ 6 := hd.card_W hl.gms
  have hFW_not : ¬ d.F ≤ d.W := by
    intro hFW
    have h1 := Subgroup.card_le_of_le hFW
    rw [hcardF, hcardW] at h1
    have h2 : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := hd.two_le; omega)
    have h3 : (2 ^ f) ^ 6 < (2 ^ f) ^ 8 := Nat.pow_lt_pow_right h2 (by norm_num)
    omega
  have hX : 2 ^ (2 * (2 * f)) <
      Nat.card (d.F ⊓ centralizer ((c.X ⊓ c.S : Subgroup G) : Set G) : Subgroup G) := by
    rw [← hU₀, show 2 ^ (2 * (2 * f)) = (2 ^ f) ^ 4 by ring]
    exact hlt
  have hsplit := lin_F_split hl k c hX
  have htS : d.t ∈ normalizer (c.S : Set G) := s313a_t_mem_normalizer_S hp k hS hP
  have htW : d.t ∈ normalizer (d.W : Set G) := s313a_mem_normalizer_W hp k hS hP htS
  have htF : d.t ∈ normalizer (d.F : Set G) := hd.t_mem_normalizer_F
  rcases LinCase.le_or_decomp_of_transitive (E := d.E) (F := d.F)
      (U₀ := CFSG.centerIn (d.Uc c.S c.X)) (J := J) (Z := (c.S ⊓ d.M₂) ⊓ centralizer ((c.S ⊓ d.M₂ : Subgroup G) : Set G))
      hdec hU₀F (fun j hj => hJE j hj) (fun j hj => hJU₀ j hj) hJtr with hle | hall
  ·
    refine hFW_not ?_
    have hU₀W : CFSG.centerIn (d.Uc c.S c.X) ≤ d.W := by
      rw [← hFE]; exact le_inf hU₀F hle
    have hF₁ : c.F₁ ≤ d.W := by
      refine le_trans ?_ hU₀W
      rw [hU₀]
      exact inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2 inf_le_left))
    have hF₂ : c.F₂ ≤ d.W := by
      have h1 : c.F₂ ≤ d.F ⊓ centralizer ((c.Y ⊓ c.S : Subgroup G) : Set G) :=
        inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2 inf_le_left))
      have h2 : d.F ⊓ centralizer ((c.Y ⊓ c.S : Subgroup G) : Set G) =
          (CFSG.centerIn (d.Uc c.S c.X)).map (MulAut.conj d.t).toMonoidHom := by
        have h3 : ((c.X ⊓ c.S).map (MulAut.conj d.t).toMonoidHom : Subgroup G) = c.Y ⊓ c.S :=
          s313a_map_conj_t_X_inf_S hp k hS hP c.ψ c.card_k
        rw [← h3, Prelim.inf_centralizer_map_conj htF, hU₀]
      refine h1.trans ?_
      rw [h2]
      calc (CFSG.centerIn (d.Uc c.S c.X)).map (MulAut.conj d.t).toMonoidHom
          ≤ d.W.map (MulAut.conj d.t).toMonoidHom := map_mono hU₀W
        _ = d.W := map_conj_eq_of_mem_normalizer htW
    rw [← hsplit]
    exact sup_le hF₁ hF₂
  ·
    refine hFW_not ?_
    have hF0 : ∀ f ∈ d.F, ∃ w ∈ d.W, ∃ z ∈ CFSG.centerIn (d.Uc c.S c.X), f = w * z := by
      intro f hf
      obtain ⟨w, hw, z, hz, hfe⟩ := hall f hf
      exact ⟨w, hFE ▸ hw, z, hz, hfe⟩
    have h3 : ((c.X ⊓ c.S).map (MulAut.conj d.t).toMonoidHom : Subgroup G) = c.Y ⊓ c.S :=
      s313a_map_conj_t_X_inf_S hp k hS hP c.ψ c.card_k
    have hU₁ : d.F ⊓ centralizer ((c.Y ⊓ c.S : Subgroup G) : Set G) =
        (CFSG.centerIn (d.Uc c.S c.X)).map (MulAut.conj d.t).toMonoidHom := by
      rw [← h3, Prelim.inf_centralizer_map_conj htF, hU₀]
    have hF1 : ∀ f ∈ d.F, ∃ w ∈ d.W, ∃ z ∈ d.F ⊓ centralizer ((c.Y ⊓ c.S : Subgroup G) : Set G),
        f = w * z := by
      intro f hf
      have hf' : d.t⁻¹ * f * d.t ∈ d.F := by
        have := (mem_normalizer_iff.1 (inv_mem htF) f).1 hf
        rwa [inv_inv] at this
      obtain ⟨w, hw, z, hz, hfe⟩ := hF0 _ hf'
      refine ⟨d.t * w * d.t⁻¹, (mem_normalizer_iff.1 htW w).1 hw, d.t * z * d.t⁻¹, ?_, ?_⟩
      · rw [hU₁]; exact ⟨z, hz, rfl⟩
      · calc f = d.t * (d.t⁻¹ * f * d.t) * d.t⁻¹ := by group
          _ = d.t * (w * z) * d.t⁻¹ := by rw [hfe]
          _ = (d.t * w * d.t⁻¹) * (d.t * z * d.t⁻¹) := by group
    have hVc' : ∀ v ∈ d.V, ∀ s ∈ c.S, v * s = s * v := fun v hv s hs =>
      (mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hVc ▸ hv : v ∈ CFSG.centerIn c.S)).2 s hs).symm
    have hW' : ∀ w ∈ d.W, ∀ s ∈ c.S, w * s * w⁻¹ * s⁻¹ ∈ d.V := by
      intro w hw s hs
      rw [← hWc] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      rw [SetLike.mem_coe, show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff] at hw'
      have h1 := hw' ⟨s, hs⟩
      rw [Subgroup.upperCentralSeries_one] at h1
      rw [← hVc]
      refine ⟨?_, mem_centralizer_iff.2 fun g hg => ?_⟩
      · exact (w' * ⟨s, hs⟩ * w'⁻¹ * ⟨s, hs⟩⁻¹).2
      · have h2 := Subgroup.mem_center_iff.1 h1 ⟨g, hg⟩
        have h3 := congrArg Subtype.val h2
        simp only [commutatorElement_def, Subgroup.coe_mul, InvMemClass.coe_inv] at h3
        exact h3
    have hcomm := LinCase.comm_mem_V_of_decomp (S := c.S) (F := d.F) (V := d.V) (W := d.W)
      (D := d.D) (P := c.X ⊓ c.S) (Q := c.Y ⊓ c.S)
      (U₀ := CFSG.centerIn (d.Uc c.S c.X))
      (U₁ := d.F ⊓ centralizer ((c.Y ⊓ c.S : Subgroup G) : Set G)) hVc' hW'
      (fun f hf x hx => mem_centralizer_iff.1 (lin_D_le_centralizer_F hl k c hx) f hf)
      (fun p hp z hz => by
        rw [hU₀] at hz
        exact mem_centralizer_iff.1 hz.2 p hp)
      (fun q hq z hz => mem_centralizer_iff.1 hz.2 q hq)
      inf_le_right inf_le_right hDS
      (by
        have e : c.S ⊓ d.M₁ = (c.X ⊓ c.S) ⊔ (c.Y ⊓ c.S) := s313a_S_inf_M₁_eq hp k hS hP c.ψ
        have e2 : c.S = d.D ⊔ (c.S ⊓ d.M₁) := s313a_S_eq_D_sup hp k hS hP
        rw [← e]; exact e2.le)
      hF0 hF1
    intro f hf
    rw [← hWc]
    refine ⟨⟨f, hFS hf⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
    have hv : f * (y : G) * f⁻¹ * (y : G)⁻¹ ∈ d.V := by
      have h1 := hcomm (y : G) y.2 f hf
      have e : f * (y : G) * f⁻¹ * (y : G)⁻¹ = ((y : G) * f * (y : G)⁻¹ * f⁻¹)⁻¹ := by group
      rw [e]; exact inv_mem h1
    intro g
    have h2 := mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hVc ▸ hv : _ ∈ CFSG.centerIn c.S)).2
      (g : G) g.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact h2

end A0

end CaseBData


end Data

end CFSG.LocalAnalysis.EvenBN.U5
