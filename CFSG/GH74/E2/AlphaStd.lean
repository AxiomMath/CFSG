module

public import CFSG.GH74.E2.BlackBoxesStd
public import CFSG.GH74.AS16.E2.Local3Models

public section

namespace CFSG.GH74.E2

open Subgroup

theorem false_of_isCompIn_conj_centralizer (hI : NoCaseI) {G : Type} [Group G] [Finite G]
    (hH : Hyp G) {K : Subgroup G} (hq : IsQuasisimple ↥K) (hZ : center ↥K = ⊥)
    (hE : ∃ E : Subgroup G, E ≤ K ∧ ElemAb 3 E ∧ Nat.card E = 9)
    (h3 : ∀ v ∈ K, orderOf v = 2 → ∃ c ∈ K, orderOf c = 3 ∧ c * v = v * c) (g : G)
    (hg : GLS.IsCompIn (centralizer (K : Set G)) (CFSG.conjugate K g)) : False := by
  obtain ⟨E, hEK, hE, hE9⟩ := hE
  obtain ⟨v, hvK, hv2⟩ := AS16.exists_involution_of_isQuasisimple hq
  obtain ⟨c, hcK, hc3, hcv⟩ := h3 v hvK hv2
  have hmem : ∀ x ∈ K, g⁻¹ * x * g ∈ centralizer (K : Set G) := by
    intro x hx
    apply hg.1
    rw [AS16.mem_conjugate_iff']
    have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [this]
    exact hx
  have hord : ∀ x : G, orderOf (g⁻¹ * x * g) = orderOf x := fun x => by
    have := (MulAut.conj g⁻¹).orderOf_eq x
    simpa [MulAut.conj_apply] using this
  have hy2 : orderOf (g⁻¹ * v * g) = 2 := by rw [hord, hv2]
  have hc'3 : orderOf (g⁻¹ * c * g) = 3 := by rw [hord, hc3]
  have hyc : (g⁻¹ * v * g) * (g⁻¹ * c * g) = (g⁻¹ * c * g) * (g⁻¹ * v * g) := by
    calc (g⁻¹ * v * g) * (g⁻¹ * c * g) = g⁻¹ * (v * c) * g := by group
      _ = g⁻¹ * (c * v) * g := by rw [hcv]
      _ = (g⁻¹ * c * g) * (g⁻¹ * v * g) := by group
  have hyC : ∀ k ∈ K, (g⁻¹ * v * g) * k = k * (g⁻¹ * v * g) := fun k hk =>
    (mem_centralizer_iff.1 (hmem v hvK) k hk).symm
  have hc'C : ∀ k ∈ K, (g⁻¹ * c * g) * k = k * (g⁻¹ * c * g) := fun k hk =>
    (mem_centralizer_iff.1 (hmem c hcK) k hk).symm
  have hc'nE : g⁻¹ * c * g ∉ E := by
    intro hcE
    have hcK' : g⁻¹ * c * g ∈ K := hEK hcE
    have hz : (⟨g⁻¹ * c * g, hcK'⟩ : ↥K) ∈ center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (hc'C k k.2).symm
    rw [hZ, Subgroup.mem_bot] at hz
    have h1 : g⁻¹ * c * g = 1 := congrArg Subtype.val hz
    have : orderOf (g⁻¹ * c * g) = 1 := by rw [h1, orderOf_one]
    omega
  have hc'3' : (g⁻¹ * c * g) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (g⁻¹ * c * g)
    rwa [hc'3] at this
  have hc'1 : g⁻¹ * c * g ≠ 1 := by
    intro h1
    have : orderOf (g⁻¹ * c * g) = 1 := by rw [h1, orderOf_one]
    omega
  obtain ⟨A, hAc, hA3, hAcard, hAr⟩ := AS16.E2.exists_elemAb27 hE.1 hE.2 hE9 hc'3' hc'1
    (fun e he => hc'C e (hEK he)) hc'nE
  have hAy := hAr (g⁻¹ * v * g) (fun e he => hyC e (hEK he)) hyc
  exact hI G hH (g⁻¹ * v * g) A ⟨hy2, hAy, ⟨hAc, hA3⟩, hAcard⟩

theorem false_of_L33_rank_two
    (hComp : ComponentList) (hP : PumpUpData) (hD3 : K0Data3)
    (hI : NoCaseI) (hAS : AschbacherStandardL33) {G : Type} [Group G] [Finite G] (hH : Hyp G)
    {t : G} (ht : orderOf t = 2) {K : Subgroup G} (hK : IsCompCen t K) (hsh : ShapeL33 ↥K)
    {u v : G} (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u ≠ v) (hcomm : u * v = v * u)
    (huK : ∀ k ∈ K, u * k = k * u) (hvK : ∀ k ∈ K, v * k = k * v) : False := by
  have hcard : Nat.card ↥K = 5616 := by
    rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) hsh]
    decide
  have hterm := isTerminalPair_of_card hComp hP hH ht hK (by omega) (by omega)
  have hq := isCompCen_quasisimple hK
  have hZ : center ↥K = ⊥ := hD3.center_bot ↥K (Or.inr (Or.inr (Or.inr (Or.inl hsh))))
  have hSub := AS16.E2.Local3Sub.of_table (AS16.E2.local3Data_L33 ↥K hsh)
    (hD3.inner3 ↥K (Or.inr (Or.inl hsh)))
  have htC : t ∈ centralizer (K : Set G) :=
    mem_centralizer_iff.2 fun k hk => (mem_Cen.1 (hK.1 hk)).symm
  have hstd : CFSG.IsStandardSubgroup K :=
    AS16.isStandardSubgroup_of_terminal hq ht htC (fun y hy hy2 => hterm.2.2.2 y hy2 hy)
      (fun g hg => false_of_isCompIn_conj_centralizer hI hH hq hZ hSub.elemAb9 hSub.exists3 g hg)
  exact hAS G hH.simple hH.nonabelian hH.kgh K hstd hsh
    ⟨u, v, hu, hv, huv, hcomm, mem_centralizer_iff.2 fun k hk => (huK k hk).symm,
      mem_centralizer_iff.2 fun k hk => (hvK k hk).symm⟩

theorem noCaseIIAlphaL33_of_standard
    (hComp : ComponentList) (hP : PumpUpData) (hD3 : K0Data3)
    (hI : NoCaseI) (hAS : AschbacherStandardL33) : NoCaseIIAlphaL33 := by
  intro G _ _ hH t t' a A B K hc hK hsh _ _ ht'K
  exact false_of_L33_rank_two hComp hP hD3 hI hAS hH hc.order_t hK hsh hc.order_t hc.order_t'
    hc.ne hc.comm (fun k hk => mem_Cen.1 (hK.1 hk)) ht'K

end CFSG.GH74.E2
