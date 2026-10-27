module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralLiftStructure
public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs
public import CFSG.LargeExtraspecial.S5Lay
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.Open CFSG.ComponentClassification

section Act

variable {X : Type*} [Group X]

noncomputable def barAct (E : Subgroup X) [E.Normal] : X →* MulAut (E ⧸ center E) :=
  (PerfectAutomorphisms.centerQuotientHom E).comp MulAut.conjNormal

theorem barAct_mk (E : Subgroup X) [E.Normal] (x : X) (e : E) :
    barAct E x (QuotientGroup.mk e) = QuotientGroup.mk (MulAut.conjNormal x e) :=
  PerfectAutomorphisms.onCenterQuotient_apply_mk _ e

theorem commute_of_barAct_eq_one {E : Subgroup X} [E.Normal] [Group.IsPerfect E] {x : X}
    (hx : barAct E x = 1) : ∀ e ∈ E, x * e = e * x := by
  have h1 : (MulAut.conjNormal x : MulAut E) = 1 :=
    PerfectAutomorphisms.centerQuotientHom_injective E (by rw [map_one]; exact hx)
  intro e he
  have h2 := congrArg (fun σ : MulAut E => ((σ ⟨e, he⟩ : E) : X)) h1
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
  calc x * e = x * e * x⁻¹ * x := by group
    _ = e * x := by rw [h2]

theorem barAct_of_mem (E : Subgroup X) [E.Normal] (e : E) :
    barAct E (e : X) = MulAut.conj (QuotientGroup.mk e : E ⧸ center E) := by
  ext y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [barAct_mk, MulAut.conj_apply]
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  congr 1

end Act

section Gold

variable {X : Type} [Group X]

theorem goldschmidtSimpleType_of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : goldschmidtSimpleType L) : goldschmidtSimpleType L' := by
  rcases h with ⟨f, hf, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩ | ⟨f, hf, ⟨φ⟩⟩ | ⟨p, f, hp, h1, h2, h3, h4, ⟨φ⟩⟩ |
    ⟨m, hm, hc⟩ | ⟨⟨φ⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans φ⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans φ⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans φ⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, h1, h2, h3, h4, ⟨e.symm.trans φ⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨m, hm, (Nat.card_congr e.toEquiv).symm.trans hc⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.symm.trans φ⟩))))

theorem isComponentOf_top_of_normal {E : Subgroup X} [hEn : E.Normal]
    (hE : CFSG.Open.IsQuasisimple E) :
    CFSG.Open.IsComponentOf E ⊤ :=
  ⟨le_top, CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf le_top
    (Subgroup.normal_subgroupOf), hE⟩

theorem le_of_not_commute {E K : Subgroup X} [E.Normal] [hK : K.Normal]
    (hE : CFSG.Open.IsQuasisimple E) {t : X} (htK : t ∈ K) (hnc : ¬ ∀ e ∈ E, e * t = t * e) :
    E ≤ K := by
  have : Group.IsPerfect E := ⟨hE.1⟩
  have hN : ((E ⊓ K).subgroupOf E).Normal := Subgroup.normal_subgroupOf
  rcases Quasisimple.normal_le_center_or_eq_top hE
      ((E ⊓ K).subgroupOf E) with h | h
  · exfalso
    apply hnc
    intro e he
    have h1 := commute_of_barAct_eq_one (E := E) (x := t) ?_ e he
    · exact h1.symm
    ext y
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    rw [barAct_mk, MulAut.one_apply, QuotientGroup.eq]
    apply h
    rw [mem_subgroupOf]
    simp only [coe_mul, coe_inv, MulAut.conjNormal_apply]
    refine ⟨?_, ?_⟩
    · exact E.mul_mem (E.inv_mem (‹E.Normal›.conj_mem _ e.2 t)) e.2
    · have h2 : (t * (e : X) * t⁻¹)⁻¹ * e = t * ((e : X)⁻¹ * t⁻¹ * (e : X)⁻¹⁻¹) := by group
      rw [h2]
      exact mul_mem htK (hK.conj_mem _ (inv_mem htK) _)
  · intro e he
    have : (⟨e, he⟩ : E) ∈ (E ⊓ K).subgroupOf E := by rw [h]; trivial
    exact (mem_subgroupOf.mp this).2

theorem goldschmidtSimpleType_of_le [Finite X] {E K : Subgroup X} [E.Normal]
    (hE : CFSG.Open.IsQuasisimple E) (hEK : E ≤ K)
    (hG : ∀ J : Subgroup (K ⧸ goldschmidtOddCore K), CFSG.Open.IsComponentOf J ⊤ →
      goldschmidtSimpleType (J ⧸ center J)) :
    goldschmidtSimpleType (E ⧸ center E) := by
  have hc := LocalComponents.of_overgroup (isComponentOf_top_of_normal hE) hEK
  set EK := E.subgroupOf K with hEKdef
  set π := QuotientGroup.mk' (goldschmidtOddCore K) with hπ
  have hnk : ¬ EK ≤ π.ker := by
    intro hle
    rw [QuotientGroup.ker_mk'] at hle
    have h2 := CFSG.LargeExtraspecial.S5.two_dvd_card_of_isQuasisimple hc.2.2
    have hodd : Odd (Nat.card (goldschmidtOddCore K)) :=
      CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd (G := K)
    have hd := Subgroup.card_dvd_of_le hle
    have : 2 ∣ Nat.card (goldschmidtOddCore K) := h2.trans hd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  have hJ := LocalComponents.image hc π (QuotientGroup.mk'_surjective _) hnk
  have hGT := hG _ hJ
  have : Group.IsPerfect EK := ⟨hc.2.2.1⟩
  have : Group.IsPerfect E := ⟨hE.1⟩
  let ψ : EK →* EK.map π := π.subgroupMap EK
  have hψ : Function.Surjective ψ := π.subgroupMap_surjective EK
  have hker : ψ.ker ≤ center EK := by
    rcases Quasisimple.normal_le_center_or_eq_top hc.2.2 ψ.ker with h | h
    · exact h
    · exfalso
      apply hnk
      intro x hx
      have : (⟨x, hx⟩ : EK) ∈ ψ.ker := by rw [h]; trivial
      rw [MonoidHom.mem_ker] at this ⊢
      exact congrArg Subtype.val this
  let e1 := CFSG.ShultStronglyClosedTI.centralLiftCenterQuotientEquiv ψ hψ hker
  let φ : E ≃* EK := (subgroupOfEquivOfLe hEK).symm
  have hφker : φ.toMonoidHom.ker ≤ center E := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have : x = 1 := φ.injective (by rw [map_one]; exact hx)
    rw [this]
    exact one_mem _
  let e0 := CFSG.ShultStronglyClosedTI.centralLiftCenterQuotientEquiv φ.toMonoidHom
    φ.surjective hφker
  exact goldschmidtSimpleType_of_mulEquiv (e0.trans e1).symm hGT

end Gold

end CFSG.LargeExtraspecial.S11
