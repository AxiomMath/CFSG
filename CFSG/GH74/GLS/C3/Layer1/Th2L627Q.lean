module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.BkIv10
public import CFSG.GH74.GLS.C3.Layer1.Th2Tstar
public import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk102L

public section

namespace CFSG.GH74.GLS.Th2.L625

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.IVK.Proofs2

theorem mem_innDiagSub_of_card_five {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]
    (hF : L2Field F) (e : K ≃* L2 F) (h5 : Nat.card F = 5) (x : MulAut K) : x ∈ innDiagSub e := by
  obtain ⟨-, ⟨ε⟩, hn⟩ := ivk_1_2e F hF K e
  have h1 : Nat.card (F ≃+* F) = 1 := by
    rw [← Nat.card_congr ε.toEquiv]
    exact hn 5 1 (by norm_num) (by rw [h5]; norm_num)
  have hsub : Subsingleton (F ≃+* F) := (Nat.card_eq_one_iff_unique.1 h1).1
  exact (mem_innDiagSub_iff e x).2 (Subsingleton.elim _ _)

theorem card_centralizer_eq_mul_CxK
    {G : Type} [Group G] [Finite G] {v w : G} {H : Subgroup G}
    (hlu : IsLocallyUnbalancing v w H) (hH5 : HasL2Model (kBar H) (fun q => q = 5))
    (hnorm : ∀ c ∈ centralizer ({v} : Set G), ∀ k ∈ H, c * k * c⁻¹ ∈ H) :
    Nat.card ↥(centralizer ({v} : Set G)) = Nat.card ↥(CxK v H) * 120 := by
  set C : Subgroup G := centralizer ({v} : Set G) with hC
  let ψ : ↥C →* MulAut (kBar H) := Back.actHom hnorm
  have hker : ψ.ker = (CxK v H).subgroupOf C := Back.actHom_ker hnorm
  have hHC : H ≤ C := hlu.1.2.1
  have hwC : w ∈ C := hlu.2.2.1
  have hfive : IsFM9 5 := Th2Tstar.isFM9_five
  obtain ⟨F, _, _, e, hF, hFq⟩ := exists_l2Field_of_hasL2Model hfive hH5
  have hD : ∀ a : MulAut (kBar H), a ∈ innDiagSub e :=
    mem_innDiagSub_of_card_five hF e hFq
  obtain ⟨hnotInn, -⟩ := Bk.ivk10_bridge b_ivk_10_2L hlu hfive hH5
  have hnotInn' : Back.actHom (Bk.hLn_normalizer H) ⟨w, hlu.2.2.2.1⟩ ∉ innAut (kBar H) := hnotInn
  have hInn : innAut (kBar H) ≤ ψ.range := by
    rintro _ ⟨xb, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective xb
    exact ⟨⟨(l : G), hHC l.2⟩, Back.actHom_of_mem hnorm l.2 (hHC l.2)⟩
  have hsup : innDiagSub e ≤ ψ.range := by
    rw [← innAut_sup_zpowers_eq e hF (hD _) hnotInn']
    exact sup_le hInn (Subgroup.zpowers_le.2 ⟨⟨w, hwC⟩, rfl⟩)
  have hrange : ψ.range = ⊤ := eq_top_iff.2 fun a _ => hsup (hD a)
  have hMul : Nat.card (MulAut (kBar H)) = 120 := by
    rw [card_mulAut_eq e, card_innDiagSub_q e hF, hFq,
      (ivk_1_2e F hF (kBar H) e).2.2 5 1 (by norm_num) (by rw [hFq]; norm_num)]
    norm_num
  have hCxC : CxK v H ≤ C := inf_le_left
  have hcard := Subgroup.card_ker_mul_card_range ψ
  rw [hker, hrange, Subgroup.card_top, hMul,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCxC).toEquiv] at hcard
  exact hcard.symm

theorem twoPartCard_centralizer_eq_eight_mul
    {G : Type} [Group G] [Finite G] {v w : G} {H : Subgroup G}
    (hlu : IsLocallyUnbalancing v w H) (hH5 : HasL2Model (kBar H) (fun q => q = 5))
    (hnorm : ∀ c ∈ centralizer ({v} : Set G), ∀ k ∈ H, c * k * c⁻¹ ∈ H) :
    twoPartCard (centralizer ({v} : Set G)) = 8 * twoPartCard (CxK v H) := by
  have hcard := card_centralizer_eq_mul_CxK hlu hH5 hnorm
  have hpos : Nat.card ↥(CxK v H) ≠ 0 := Nat.card_pos.ne'
  have h120 : (Nat.factorization 120) 2 = 3 := by decide +kernel
  unfold twoPartCard
  rw [hcard, Nat.factorization_mul hpos (by norm_num), Finsupp.add_apply, h120, pow_add]
  ring

end CFSG.GH74.GLS.Th2.L625
