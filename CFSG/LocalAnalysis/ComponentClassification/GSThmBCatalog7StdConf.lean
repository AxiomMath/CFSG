module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecTransport

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7Std

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

structure StdConf (H : Type) [Group H] [Finite H] where
  a : H
  b : H
  J : Subgroup H
  K : Subgroup H
  p : ℕ
  f : ℕ
  prime : p.Prime
  ne_two : p ≠ 2
  one_le : 1 ≤ f
  five_le : 5 ≤ p ^ f
  simple : IsSimpleGroup ↥(generalizedFitting H)
  centralizer_eq_bot : centralizer (generalizedFitting H : Set H) = ⊥
  orderOf_a : orderOf a = 2
  orderOf_b : orderOf b = 2
  mul_comm_ab : a * b = b * a
  K_le_G : K ≤ generalizedFitting H
  J_le_G : J ≤ generalizedFitting H
  K_le : K ≤ centralizer ({b} : Set H)
  isPComponent_K : IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set H)))
  layer : ∀ M : Subgroup H, M ≤ centralizer ({b} : Set H) →
    IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set H))) → M = K
  sylow : ∀ T : Subgroup H, IsPGroup 2 T →
    T ≤ centralizer ({b} : Set H) ⊓ coreActionKernel K → Nat.card T ≤ 2
  J_le : J ≤ centralizer ({a} : Set H)
  isPComponent_J : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set H)))
  b_mem_kernel : b ∈ coreActionKernel J
  conjugate_K : conjugate K a = K
  type_J : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f
  type_K : Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 p (2 * f)

variable {H : Type} [Group H] [Finite H]

theorem StdConf.ofHyp59 (h : Hyp59 H) (hB : Nat.card h.B = 2) (hKa : conjugate h.K h.a = h.K)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (hJL : Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p f)
    (hKL : Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSL 2 p (2 * f)) :
    ∃ c : StdConf H, c.J = h.J ∧ c.K = h.K ∧ c.a = h.a ∧ c.p = p ∧ c.f = f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb, hBb⟩ := exists_eq_zpowers_of_card_two hB
  have hWb : normalizer (h.B : Set H) = centralizer ({b} : Set H) := by
    rw [hBb]
    exact UnbalancedCorr.normalizer_zpowers_eq_centralizer hb
  obtain ⟨hF, hsimple, hC, hcomp, huniq⟩ := h.generalizedFitting_simple
  have hLG : pLayer H 2 = generalizedFitting H := by
    rw [ClassicalInvolution.LBalanceProof.pLayer_eq_layer_of_pPrimeCore_eq_bot h.oddCore_eq_bot,
      hF]
    exact le_antisymm (sSup_le fun L hL => (huniq L hL).le) (le_sSup hcomp)
  have hJG : h.J ≤ generalizedFitting H := hF ▸ B5a.le_conjClosure _ _
  have hVG : h.V ≤ generalizedFitting H := hLG ▸ B5a.V_le_pLayer h.toHyp52
  have hbB : b ∈ h.B := hBb ▸ mem_zpowers b
  have hbS : b ∈ h.S := (h.B_le hbB).1
  have hab : h.a * b = b * h.a :=
    (mem_centralizer_singleton_iff.mp (mem_inf.mp (h.S_le hbS)).1).symm
  obtain ⟨hKW, hKpc⟩ := h.isPComponent_K
  rw [hWb] at hKW hKpc
  have hlayer : layerIn (centralizer ({b} : Set H)) = h.K := by
    rw [← hWb, ← h.layer_eq_K, hKa, sup_idem]
  have hV : h.V = h.K := by
    change layerIn (normalizer (h.B : Set H)) = _
    rw [hWb, hlayer]
  refine ⟨{
    a := h.a
    b := b
    J := h.J
    K := h.K
    p := p
    f := f
    prime := hp
    ne_two := hp2
    one_le := hf
    five_le := h5
    simple := hsimple
    centralizer_eq_bot := by rw [hF]; exact hC
    orderOf_a := h.orderOf_a
    orderOf_b := hb
    mul_comm_ab := hab
    K_le_G := hV ▸ hVG
    J_le_G := hJG
    K_le := hKW
    isPComponent_K := hKpc
    layer := fun M hMW hMpc => by
      have hMle : M ≤ h.K ⊔ h.K := by
        rw [sup_idem, ← hlayer]
        have h1 : M.subgroupOf (centralizer ({b} : Set H)) ≤
            pLayer ↥(centralizer ({b} : Set H)) 2 := le_sSup hMpc
        have h2 := map_mono (f := (centralizer ({b} : Set H)).subtype) h1
        rwa [map_subgroupOf_eq_of_le hMW] at h2
      exact (GSLit.eq_or_eq_of_le_sup hMW hMpc hKW hKpc hKW hKpc hMle).elim id id
    sylow := fun T hT hTle => by
      have hY := h.B_sylow_kernel
      have hBY := h.B_le_kernel
      rw [hWb, hlayer] at hY hBY
      exact hB ▸ Sp4Rec.Config.card_le_of_sylow hBY hY hT hTle
    J_le := h.J_le
    isPComponent_J := h.isPComponent_J
    b_mem_kernel := h.toHyp52.B_le_coreActionKernel hbB
    conjugate_K := hKa
    type_J := hJL
    type_K := hKL }, rfl, rfl, rfl, rfl, rfl⟩

namespace StdConf

variable (c : StdConf H)

theorem b_ne_one : c.b ≠ 1 := by
  intro h
  have := c.orderOf_b
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

end StdConf

theorem exists_fixed_pComponent (hC : centralizer (generalizedFitting H : Set H) = ⊥) {x : H}
    (hx : orderOf x = 2) {L : Subgroup H} (hLx : L ≤ centralizer ({x} : Set H))
    (hLG : L ≤ generalizedFitting H)
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set H)))) {M : Type*} [Group M]
    [Finite M] (θ : ↥(generalizedFitting H) ≃* M) :
    ∃ α : MulAut M, α ^ 2 = 1 ∧ α ≠ 1 ∧ ∃ L' : Subgroup M,
      L' ≤ fixedSubgroup α ∧ IsPComponent 2 (L'.subgroupOf (fixedSubgroup α)) ∧
      Nonempty (L' ≃* L) := by
  classical
  have hGn : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  set α : MulAut M := MulAut.congr θ (MulAut.conjNormal x) with hα
  have hfix : fixedSubgroup α =
      ((centralizer ({x} : Set H)).subgroupOf (generalizedFitting H)).map θ.toMonoidHom := by
    ext y
    obtain ⟨g, rfl⟩ := θ.surjective y
    rw [mem_map_equiv]
    simp only [MulEquiv.symm_apply_apply, mem_subgroupOf, mem_centralizer_singleton_iff]
    change α (θ g) = θ g ↔ _
    have hαg : α (θ g) = θ (MulAut.conjNormal x g) := by
      simp [hα, MulAut.congr_apply]
    rw [hαg, EmbeddingLike.apply_eq_iff_eq]
    constructor
    · intro h
      have h1 : x * (g : H) * x⁻¹ = g := congrArg Subtype.val h
      calc (g : H) * x = x * g * x⁻¹ * x := by rw [h1]
        _ = x * g := by group
    · intro h
      apply Subtype.ext
      change x * (g : H) * x⁻¹ = g
      rw [← h]
      group
  have hLG' : L.subgroupOf (generalizedFitting H) ≤
      (centralizer ({x} : Set H)).subgroupOf (generalizedFitting H) :=
    fun y hy => mem_subgroupOf.mpr (hLx (mem_subgroupOf.mp hy))
  refine ⟨α, ?_, ?_, (L.subgroupOf (generalizedFitting H)).map θ.toMonoidHom, ?_, ?_, ?_⟩
  · rw [hα, ← map_pow, ← map_pow, ← hx, pow_orderOf_eq_one, map_one, map_one]
  ·
    intro h1
    have h2 : MulAut.conjNormal x = (1 : MulAut (generalizedFitting H)) := by
      have := congrArg (MulAut.congr θ).symm h1
      rwa [hα, MulEquiv.symm_apply_apply, map_one] at this
    have hxC : x ∈ centralizer (generalizedFitting H : Set H) := by
      rw [mem_centralizer_iff]
      intro w hw
      have h3 := congrArg (fun φ : MulAut (generalizedFitting H) => ((φ ⟨w, hw⟩ : _) : H)) h2
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
      calc w * x = x * w * x⁻¹ * x := by rw [h3]
        _ = x * w := by group
    rw [hC, mem_bot] at hxC
    rw [hxC, orderOf_one] at hx
    exact absurd hx (by norm_num)
  · rw [hfix]; exact map_mono hLG'
  · rw [hfix]
    exact (Sp4Rec.isPComponent_subgroupOf_map_iff θ hLG').mp
      (Sp4Rec.isPComponent_subgroupOf_restrict hLx hLG hL)
  · exact ⟨((L.subgroupOf (generalizedFitting H)).equivMapOfInjective _ θ.injective).symm.trans
      (subgroupOfEquivOfLe hLG)⟩

end Catalog7Std

end CFSG.ComponentClassification.GSThmB
