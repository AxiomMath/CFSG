module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedParts
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBBasic
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B6Four

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec39b_V_not_le_centralizer_t (hd : d.Hyp) : ¬ d.V ≤ centralizer ({d.t} : Set G) := by
  intro hVt
  have hVt' : d.V ≤ d.Zp := by
    intro v hv
    rw [← hd.V_inf_centralizer_t]
    exact ⟨hv, hVt hv⟩
  have h1 := Subgroup.card_le_of_le hVt'
  rw [hd.card_V, d.card_Zp] at h1
  have h4 := hd.four_le
  nlinarith

theorem sec39b_t_not_mem_D (hd : d.Hyp) (hV : d.V ≤ CFSG.centerIn d.L₂) (hDL : d.D ≤ d.L₂) :
    d.t ∉ d.D := by
  intro htD
  apply sec39b_V_not_le_centralizer_t hd
  intro v hv
  rw [mem_centralizer_singleton_iff]
  have := mem_centralizer_iff.1 (hV hv).2 d.t (hDL htD)
  exact this.symm

theorem sec39b_F_le_centralizer_D (hd : d.Hyp) (hV : d.V ≤ CFSG.centerIn d.L₂)
    (hDL : d.D ≤ d.L₂) : d.F ≤ centralizer (d.D : Set G) := by
  refine Data.F_le fun n hn v hv => mem_centralizer_iff.2 fun y hy => ?_
  have hy' : n⁻¹ * y * n ∈ d.D := by
    have := (mem_normalizer_iff.1 (inv_mem (hd.N₁_le_normalizer_D hn)) y).1 hy
    simpa using this
  have hc := mem_centralizer_iff.1 (hV hv).2 _ (hDL hy')
  calc y * (n * v * n⁻¹) = n * ((n⁻¹ * y * n) * v) * n⁻¹ := by group
    _ = n * (v * (n⁻¹ * y * n)) * n⁻¹ := by rw [hc]
    _ = n * v * n⁻¹ * y := by group

theorem sec39b_mem_D_or (hd : d.Hyp) (hB₆ : d.B₆ = d.D ⊔ zpowers d.t) {x : G} (hx : x ∈ d.B₆) :
    x ∈ d.D ∨ ∃ a ∈ d.D, x = a * d.t := by
  rw [hB₆] at hx
  have hle : zpowers d.t ≤ normalizer (d.D : Set G) := by
    rw [zpowers_le]
    exact hd.t_mem_normalizer_D
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hle hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
  rcases zpow_eq_one_or_eq_of_mul_self hd.t_mul_t k with h1 | h1
  · left
    rw [h1, mul_one]
    exact ha
  · right
    exact ⟨a, ha, by rw [h1]⟩

theorem sec39b_F_le_D (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hB₆ : d.B₆ = d.D ⊔ zpowers d.t) (hFc : d.F ≤ centralizer (d.D : Set G)) : d.F ≤ d.D := by
  intro x hx
  have hxB : x ∈ d.B₆ := hd.FB₃_le_B₆ hGMS (mem_sup_left hx)
  rcases sec39b_mem_D_or hd hB₆ hxB with h1 | ⟨a, ha, hxa⟩
  · exact h1
  · exfalso
    apply hd.t_not_mem_centralizer_F hGMS
    rw [mem_centralizer_iff]
    intro y hy
    have hFab := hd.F_comm hGMS
    have h2 : y * a⁻¹ = a⁻¹ * y := (mem_centralizer_iff.1 (hFc hy) _ (inv_mem ha)).symm
    have h3 : d.t = a⁻¹ * x := by rw [hxa]; group
    rw [h3]
    calc y * (a⁻¹ * x) = (y * a⁻¹) * x := by group
      _ = (a⁻¹ * y) * x := by rw [h2]
      _ = a⁻¹ * (y * x) := by group
      _ = a⁻¹ * (x * y) := by rw [hFab y hy x hx]
      _ = (a⁻¹ * x) * y := by group

theorem sec39b_A₃_le_D (hd : d.Hyp) {S : Subgroup G} (hP : d.P ≤ S) (ha : d.Sec39a S)
    (hFD : d.F ≤ d.D) : d.A₃ ≤ d.D := by
  obtain ⟨_, _, _, _, _, _, _, hA₃, _, _, _, _⟩ := d.sec2_1_two hd.two_le
  have h2 : d.P ⊓ centralizer (d.I₂ : Set G) ≤ d.D := fun x hx => by
    have : x ∈ S ⊓ centralizer (d.I₂ : Set G) := ⟨hP hx.1, hx.2⟩
    rw [← ha.cD₂] at this
    exact this.1
  have h5 : d.P ⊓ centralizer (d.I₅ : Set G) ≤ d.D := fun x hx => by
    have : x ∈ S ⊓ centralizer (d.I₅ : Set G) := ⟨hP hx.1, hx.2⟩
    rw [← ha.cD₅] at this
    exact this.1
  intro x hx
  rw [hA₃] at hx
  exact (sup_le (sup_le (hd.A₁_le_F.trans hFD) h2) h5) hx

theorem sec39b_mem_A₁_of_comm (hd : d.Hyp) {y a : G} (hy : y ∈ d.F) (ha : a ∈ d.A₃)
    (h : ∀ b ∈ d.A₃, b * (y * a) = (y * a) * b) : a ∈ d.A₁ := by
  have hyc : ∀ b ∈ d.A₃, b * y = y * b := fun b hb =>
    mem_centralizer_iff.1 (hd.F_le_centralizer_A₃ hy) b hb
  rw [← d.sec2_2_three.2.2.1]
  refine ⟨ha, mem_centralizer_iff.2 fun b hb => ?_⟩
  have h2 : y * (b * a) = y * (a * b) := by
    calc y * (b * a) = (y * b) * a := by group
      _ = (b * y) * a := by rw [hyc b hb]
      _ = b * (y * a) := by group
      _ = (y * a) * b := h b hb
      _ = y * (a * b) := by group
  exact mul_left_cancel h2

theorem sec39b_centralizer_A₃_le_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hB₆ : d.B₆ = d.D ⊔ zpowers d.t) (htD : d.t ∉ d.D) (hFD : d.F ≤ d.D) (hA₃D : d.A₃ ≤ d.D)
    {w : G} (hwD : w ∈ d.D) (hw : ∀ b ∈ d.A₃, b * w = w * b) : w ∈ d.F := by
  have hwB : w ∈ d.B₆ := by
    rw [hB₆]
    exact mem_sup_left hwD
  have hcr := hd.cr_mem_FA₃ hGMS (d.B₆_le_normalizer hwB)
  obtain ⟨c, hc⟩ : ∃ c, c = w⁻¹ * d.t * w * d.t := ⟨_, rfl⟩
  rw [← hc] at hcr
  have hct : ∀ b ∈ d.A₃, b * c = c * b := by
    intro b hb
    have hbw : Commute b w := hw b hb
    have hbt : Commute b d.t := hd.comm_t (d.A₃_le_P.trans d.P_le_L hb)
    rw [hc]
    exact ((((hbw.inv_right.mul_right hbt).mul_right hbw).mul_right hbt)).eq
  obtain ⟨y, hy, a, ha, hya⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer (hd.A₃_le_normalizer_F hGMS) hcr
  have haZ : a ∈ d.A₁ :=
    sec39b_mem_A₁_of_comm hd hy ha fun b hb => hya ▸ hct b hb
  have hcF : c ∈ d.F := hya ▸ mul_mem hy (hd.A₁_le_F haZ)
  have ht' : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right hd.t_mul_t
  have hst : (w * d.t)⁻¹ * (d.t * w) ∈ d.F := by
    have e : (w * d.t)⁻¹ * (d.t * w) = d.t * c * d.t⁻¹ := by
      rw [hc]
      calc (w * d.t)⁻¹ * (d.t * w) = d.t⁻¹ * w⁻¹ * d.t * w := by group
        _ = d.t * w⁻¹ * d.t * w := by rw [ht']
        _ = d.t * (w⁻¹ * d.t * w * d.t) * d.t⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 hd.t_mem_normalizer_F c).1 hcF
  obtain ⟨y', hy', a', ha', hw' | hw'⟩ := hd.exists_of_mem_FB₃ (hd.mem_FB₃_of_mem_B₆ hGMS hwB hst)
  · have : a' ∈ d.A₁ := sec39b_mem_A₁_of_comm hd hy' ha' fun b hb => hw' ▸ hw b hb
    rw [hw']
    exact mul_mem hy' (hd.A₁_le_F this)
  · exfalso
    apply htD
    have e : d.t = y'⁻¹ * w * a'⁻¹ := by rw [hw']; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hFD hy')) hwD) (inv_mem (hA₃D ha'))

theorem sec39b_sq_comm_A₃ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hB₆ : d.B₆ = d.D ⊔ zpowers d.t) (hFc : d.F ≤ centralizer (d.D : Set G)) {s : G}
    (hsD : s ∈ d.D) : ∀ b ∈ d.A₃, b * (s * s) = (s * s) * b := by
  intro b hb
  have hsB : s ∈ d.B₆ := by
    rw [hB₆]
    exact mem_sup_left hsD
  have hf := hd.commutator_B₆_FA₃_mem_F hGMS hsB (mem_sup_right hb)
  obtain ⟨f₁, hf₁⟩ : ∃ f₁, f₁ = s * b * s⁻¹ * b⁻¹ := ⟨_, rfl⟩
  rw [← hf₁] at hf
  haveI := hd.isElementaryAbelian_F hGMS
  have hsq : f₁ * f₁ = 1 := by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := d.F) f₁ hf
    simpa [pow_two] using this
  have hsc : s * f₁ = f₁ * s := mem_centralizer_iff.1 (hFc hf) s hsD
  have e1 : s * b = f₁ * b * s := by
    rw [hf₁]
    group
  calc b * (s * s) = (f₁ * f₁) * b * (s * s) := by rw [hsq, one_mul]
    _ = f₁ * (f₁ * b * s) * s := by group
    _ = f₁ * (s * b) * s := by rw [← e1]
    _ = (f₁ * s) * b * s := by group
    _ = (s * f₁) * b * s := by rw [hsc]
    _ = s * (f₁ * b * s) := by group
    _ = s * (s * b) := by rw [← e1]
    _ = (s * s) * b := by group

theorem sec39b_of_hyp (hp : d.CaseHyp) (k8 : d.Know8) (S : Subgroup G)
    (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) (ha : d.Sec39a S) : d.Sec39b := by
  have hGMS := hp.gms
  have hd := hp.hyp
  have hDS : d.D ≤ S := by
    rw [ha.S_eq]
    exact le_sup_right
  have hDL : d.D ≤ d.L₂ := hDS.trans hS.le
  have hV : d.V ≤ CFSG.centerIn d.L₂ := k8.s8.2.1
  have hB₆ := ha.B₆_eq
  have hFc := sec39b_F_le_centralizer_D hd hV hDL
  have htD := sec39b_t_not_mem_D hd hV hDL
  have hFD := sec39b_F_le_D hGMS hd hB₆ hFc
  have hA₃D := sec39b_A₃_le_D hd hP ha hFD
  have hC : ∀ w ∈ d.D, (∀ b ∈ d.A₃, b * w = w * b) → w ∈ d.F := fun w hwD hw =>
    sec39b_centralizer_A₃_le_F hGMS hd hB₆ htD hFD hA₃D hwD hw
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · rintro z ⟨hzD, hzc⟩
    exact hC z hzD fun b hb => mem_centralizer_iff.1 hzc b (hA₃D hb)
  · intro x hx
    exact ⟨hFD hx, hFc hx⟩
  · intro x hx
    exact hC (x * x) (mul_mem hx hx) (sec39b_sq_comm_A₃ hGMS hd hB₆ hFc hx)

end Data

namespace CaseBParts

theorem sec39b : Sec39bStatement :=
  fun _ _ _ _ _ _ _ _ hp k8 S hS hP ha => Data.sec39b_of_hyp hp k8 S hS hP ha

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
