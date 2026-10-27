module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AB1B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AE16L
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenRank
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathInvol

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem pt_elem_of_le {E D : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) (hDE : D ≤ E) :
    CFSG.Open.IsElemAbelian 2 D := by
  haveI : IsMulCommutative E := hE.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hE.2 x (hDE hx)⟩
  have hab : (a : G) * b = b * a :=
    congrArg Subtype.val (mul_comm' (⟨(a : G), hDE a.2⟩ : E) ⟨(b : G), hDE b.2⟩)
  exact Subtype.ext hab

theorem pt_conj_x₁ (hw : WreathRel x₁ x₂ lam) (a b : ℕ) :
    (x₁ ^ a * x₂ ^ b * lam) * x₁ * (x₁ ^ a * x₂ ^ b * lam)⁻¹ = x₂ := by
  have hc : Commute x₁ x₂ := hw.comm
  calc (x₁ ^ a * x₂ ^ b * lam) * x₁ * (x₁ ^ a * x₂ ^ b * lam)⁻¹
      = x₁ ^ a * x₂ ^ b * (lam * x₁ * lam⁻¹) * (x₂ ^ b)⁻¹ * (x₁ ^ a)⁻¹ := by group
    _ = x₁ ^ a * x₂ ^ b * x₂ * (x₂ ^ b)⁻¹ * (x₁ ^ a)⁻¹ := by rw [hw.conj_x₁]
    _ = x₁ ^ a * x₂ * (x₁ ^ a)⁻¹ := by group
    _ = x₂ := by rw [(hc.pow_left a).eq, mul_inv_cancel_right]

theorem pt_sq_x₂_inv_x₁ (hw : WreathRel x₁ x₂ lam) : (x₂ * x₁⁻¹) ^ 2 = (x₁ * x₂) ^ 2 := by
  have hc12 : Commute x₁ x₂ := hw.comm
  have hc : Commute x₂ x₁⁻¹ := hc12.symm.inv_right
  have hcz : Commute (x₁ ^ 2) ((x₁ * x₂) ^ 2) :=
    (((Commute.refl x₁).mul_right hc12).pow_pow 2 2)
  rw [hc.mul_pow, hw.x₂_sq, inv_pow, hcz.eq, mul_inv_cancel_right]

section Cert


theorem pt_m2 (h : Ctx0 t L S x₁ x₂ lam rho) :
    ∀ E : Subgroup G, E ≤ twoCore t ⊔ wreathGrp x₁ x₂ lam →
      CFSG.Open.IsElemAbelian 2 E → Nat.card ↥E ≤ 8 := by
  intro E hE hEe
  by_cases hET : E ≤ wreathGrp x₁ x₂ lam
  · have := card_le_four_of_elemAbelian_wreathGrp h.wreath hET hEe
    omega
  · obtain ⟨a, haE, haT⟩ := SetLike.not_le_iff_exists.mp hET
    have hD : CFSG.Open.IsElemAbelian 2 (E ⊓ wreathGrp x₁ x₂ lam) :=
      pt_elem_of_le hEe inf_le_left
    have hD4 : Nat.card ↥(E ⊓ wreathGrp x₁ x₂ lam) ≤ 4 :=
      card_le_four_of_elemAbelian_wreathGrp h.wreath inf_le_right hD
    have hsq : ∀ n ∈ E, n * n = 1 := fun n hn => by
      rw [← pow_two]
      exact hEe.2 n hn
    have ha := (pt_invol h a (hE haE) (hsq a haE)).resolve_left haT
    have hmem : ∀ n ∈ E, n ∈ E ⊓ wreathGrp x₁ x₂ lam ∨
        a⁻¹ * n ∈ E ⊓ wreathGrp x₁ x₂ lam := by
      intro n hnE
      by_cases hnT : n ∈ wreathGrp x₁ x₂ lam
      · exact Or.inl ⟨hnE, hnT⟩
      · right
        have hn := (pt_invol h n (hE hnE) (hsq n hnE)).resolve_left hnT
        refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ haE) hnE, ?_⟩
        have e : a⁻¹ * n = (t * a)⁻¹ * (t * n) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hn
    have hidx : (E ⊓ wreathGrp x₁ x₂ lam).relIndex E ≤ 2 :=
      relIndex_le_two_of_forall inf_le_left a haE hmem
    have hmul := Subgroup.relIndex_mul_card (H := E ⊓ wreathGrp x₁ x₂ lam) (K := E)
    rw [inf_eq_left.mpr (inf_le_left : E ⊓ wreathGrp x₁ x₂ lam ≤ E)] at hmul
    calc Nat.card ↥E
        = (E ⊓ wreathGrp x₁ x₂ lam).relIndex E * Nat.card ↥(E ⊓ wreathGrp x₁ x₂ lam) :=
          hmul.symm
      _ ≤ 2 * 4 := Nat.mul_le_mul hidx hD4
      _ = 8 := by norm_num

theorem pt_rank (h : Ctx0 t L S x₁ x₂ lam rho) :
    RankLE (twoCore t ⊔ wreathGrp x₁ x₂ lam) 4 := by
  haveI := h.hyp.isCyclic
  have hcomm12 : ∀ u ∈ zpowers x₁, ∀ v ∈ zpowers x₂, u * v = v * u := by
    intro u hu v hv
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hc : Commute x₁ x₂ := h.wreath.comm
    exact (hc.zpow_zpow m n).eq
  have hB : RankLE (baseGrp x₁ x₂) 2 := by
    have := RankLE.sup hcomm12 (RankLE.of_isCyclic (K := zpowers x₁))
      (RankLE.of_isCyclic (K := zpowers x₂))
    rw [← (h.wreath.baseGrp_eq).2.1] at this
    exact this
  have hW : RankLE (ctxW t x₁ x₂) 3 := RankLE.sup (pt_comm_base h) RankLE.of_isCyclic hB
  exact RankLE.of_relIndex_two (pt_W_le t x₁ x₂ lam) (pt_relIndex_W h) hW

theorem pt_normal_elem_le (h : Ctx0 t L S x₁ x₂ lam rho) {E : Subgroup G}
    (hEn : NormalIn E (twoCore t ⊔ wreathGrp x₁ x₂ lam)) (hEe : CFSG.Open.IsElemAbelian 2 E) :
    E ≤ ctxE t x₁ x₂ := by
  intro e he
  have heS := hEn.1 he
  have hee : e * e = 1 := by
    rw [← pow_two]
    exact hEe.2 e he
  have ht2 : t * t = 1 := t_mul_self h.hyp
  have hx₁ : x₁ ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
  have hx₁PT : x₁ ∈ twoCore t ⊔ wreathGrp x₁ x₂ lam := Subgroup.mem_sup_right hx₁
  have hFA : fourGrp x₁ x₂ ≤ ctxE t x₁ x₂ := by
    rw [pt_ctxE_eq_sup]
    exact le_sup_right
  have htA : t ∈ ctxE t x₁ x₂ := by
    rw [pt_ctxE_eq_sup]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have htL : ∀ g ∈ L, t * g = g * t := fun g hg =>
    (mem_invCent_iff.mp (L_le_invCent h.hyp hg)).symm
  have key : ∀ u ∈ wreathGrp x₁ x₂ lam, u * u = 1 → (u = e ∨ u = t * e) →
      u ∈ fourGrp x₁ x₂ := by
    intro u hu huu hue
    by_cases hu1 : u = 1
    · rw [hu1]
      exact Subgroup.one_mem _
    rcases h.wreath.involution_cases hu huu hu1 with h1 | h1 | h1 | ⟨a, ha⟩
    · rw [h1]
      exact Subgroup.subset_closure (by simp)
    · rw [h1, h.wreath.x₂_sq]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · rw [h1]
      exact Subgroup.subset_closure (by simp)
    · exfalso
      have he' : x₁ * e * x₁⁻¹ ∈ E := hEn.2 x₁ hx₁PT e he
      have hc : e * (x₁ * e * x₁⁻¹) ∈ E := Subgroup.mul_mem _ he he'
      have hkey : e * (x₁ * e * x₁⁻¹) = u * (x₁ * u * x₁⁻¹) := by
        rcases hue with hue | hue
        · rw [hue]
        · have heu : e = t * u := by rw [hue, ← mul_assoc, ht2, one_mul]
          have htu : Commute t u := htL u (pt_wreath_le_L h hu)
          have htx : Commute t x₁ := htL x₁ (pt_wreath_le_L h hx₁)
          have hcom : t * (u * x₁) = (u * x₁) * t := (htu.mul_right htx).eq
          rw [heu]
          calc t * u * (x₁ * (t * u) * x₁⁻¹) = t * ((u * x₁) * t) * u * x₁⁻¹ := by group
            _ = t * (t * (u * x₁)) * u * x₁⁻¹ := by rw [← hcom]
            _ = (t * t) * (u * x₁ * u * x₁⁻¹) := by group
            _ = u * (x₁ * u * x₁⁻¹) := by rw [ht2, one_mul]; group
      have hconj : u * x₁ * u⁻¹ = x₂ := by
        rw [ha]
        exact pt_conj_x₁ h.wreath _ _
      have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
      have hx₂x₁ : x₂ * x₁⁻¹ ∈ E := by
        have h3 : u * (x₁ * u * x₁⁻¹) = x₂ * x₁⁻¹ := by
          calc u * (x₁ * u * x₁⁻¹) = (u * x₁ * u) * x₁⁻¹ := by group
            _ = (u * x₁ * u⁻¹) * x₁⁻¹ := by rw [huinv]
            _ = x₂ * x₁⁻¹ := by rw [hconj]
        rw [← h3, ← hkey]
        exact hc
      have hsq2 : (x₂ * x₁⁻¹) ^ 2 = 1 := hEe.2 _ hx₂x₁
      exact h.wreath.sq_x₁x₂_ne_one ((pt_sq_x₂_inv_x₁ h.wreath).symm.trans hsq2)
  rcases pt_invol h e heS hee with heT | hteT
  · exact hFA (key e heT hee (Or.inl rfl))
  · have hPT : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ invCent t :=
      sup_le (twoCore_le_invCent t) ((pt_wreath_le_L h).trans (L_le_invCent h.hyp))
    have hte : t * e = e * t := (mem_invCent_iff.mp (hPT heS)).symm
    have htee : (t * e) * (t * e) = 1 := by
      calc t * e * (t * e) = t * (e * t) * e := by group
        _ = t * (t * e) * e := by rw [← hte]
        _ = (t * t) * (e * e) := by group
        _ = 1 := by rw [ht2, hee, one_mul]
    have hu := key (t * e) hteT htee (Or.inr rfl)
    have hdecomp : e = t * (t * e) := by rw [← mul_assoc, ht2, one_mul]
    rw [hdecomp]
    exact Subgroup.mul_mem _ htA (hFA hu)

end Cert

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
