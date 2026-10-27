module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootAd

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable (h : Setup G)

theorem le_of_le_sup_zpowers_t {Y W' : Subgroup G} (hY2 : IsPGroup 2 Y)
    (htW : h.t ∈ normalizer (W' : Set G)) (hHY : h.H ≤ normalizer (Y : Set G))
    (hHW : h.H ≤ normalizer (W' : Set G))
    (hC : ∀ w ∈ W', w ∈ centralizer (h.H : Set G) → w = 1) (hnt : h.t ∉ Y)
    (hle : Y ≤ W' ⊔ zpowers h.t) : Y ≤ W' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWN : W' ⊔ zpowers h.t ≤ normalizer (W' : Set G) :=
    sup_le le_normalizer (zpowers_le.2 htW)
  intro y hy
  obtain ⟨w, hw, hyw | hyw⟩ := exists_eq_or_eq_mul_of_mem_sup h.t_mul_t htW (hle hy)
  · rw [hyw]
    exact hw
  exfalso
  let : MulDistribMulAction h.H Y := Subgroup.conjMulDistribMulActionOfLeNormalizer h.H Y hHY
  set N : Subgroup Y := (Y ⊓ W').subgroupOf Y with hNdef
  have hYN : Y ≤ normalizer ((Y ⊓ W' : Subgroup G) : Set G) := fun z hz =>
    mem_normalizer_inf (le_normalizer hz) (hWN (hle hz))
  have : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYN
  have hNinv : CFSG.IsInvariant h.H Y N :=
    CFSG.SolvableHall.isInvariant_of_forall_smul_mem fun b z hz => by
      rw [mem_subgroupOf] at hz ⊢
      exact (mem_normalizer_iff.1 (mem_normalizer_inf (hHY b.2) (hHW b.2)) z).1 hz
  have hN2 : IsPGroup 2 N :=
    (hY2.to_le (inf_le_left : Y ⊓ W' ≤ Y)).of_equiv (subgroupOfEquivOfLe inf_le_left).symm
  have hNsolv : Group.IsSolvable N := by
    have := hN2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card h.H) (Nat.card N) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hN2
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 h.odd_card_H)
  have hbt : ∀ b ∈ h.H, b * h.t = h.t * b := fun b hb => h.mul_t_comm (h.H_le_L hb)
  have hcoset : ∀ b : h.H, (⟨y, hy⟩ : Y)⁻¹ * (b • (⟨y, hy⟩ : Y)) ∈ N := by
    intro b
    have hsmul : ((b • (⟨y, hy⟩ : Y) : Y) : G) = (b : G) * y * (b : G)⁻¹ := rfl
    rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hsmul]
    refine mem_inf.2 ⟨mul_mem (inv_mem hy) ((mem_normalizer_iff.1 (hHY b.2) y).1 hy), ?_⟩
    have hbw : (b : G) * w * (b : G)⁻¹ ∈ W' := (mem_normalizer_iff.1 (hHW b.2) w).1 hw
    have e : y⁻¹ * ((b : G) * y * (b : G)⁻¹) =
        h.t⁻¹ * (w⁻¹ * ((b : G) * w * (b : G)⁻¹)) * h.t⁻¹⁻¹ := by
      rw [hyw, inv_inv]
      have hbt' := hbt b b.2
      calc (w * h.t)⁻¹ * ((b : G) * (w * h.t) * (b : G)⁻¹) =
          h.t⁻¹ * w⁻¹ * ((b : G) * w * (b : G)⁻¹) * ((b : G) * h.t * (b : G)⁻¹) := by group
        _ = h.t⁻¹ * (w⁻¹ * ((b : G) * w * (b : G)⁻¹)) * h.t := by
          rw [hbt', mul_inv_cancel_right]
          group
    rw [e]
    exact (mem_normalizer_iff.1 (inv_mem htW) _).1 (mul_mem (inv_mem hw) hbw)
  obtain ⟨c, hc, hcN⟩ := CFSG.SolvableHall.exists_fixed_of_coset_fixed N hNinv hNsolv hcop
    ⟨y, hy⟩ hcoset
  have hcfix : ∀ b ∈ h.H, b * (c : G) * b⁻¹ = c := fun b hb => congrArg Subtype.val (hc ⟨b, hb⟩)
  have hcn : (c : G)⁻¹ * y ∈ W' := by
    have := (mem_subgroupOf.1 hcN).2
    simpa using this
  have hct : (c : G) * h.t⁻¹ ∈ W' := by
    have e : (c : G) * h.t⁻¹ = w * (h.t * ((c : G)⁻¹ * y)⁻¹ * h.t⁻¹) := by
      rw [hyw]
      group
    rw [e]
    exact mul_mem hw ((mem_normalizer_iff.1 htW _).1 (inv_mem hcn))
  have hctH : (c : G) * h.t⁻¹ ∈ centralizer (h.H : Set G) := mem_centralizer_iff.2 fun b hb => by
    have h1 := hcfix b hb
    have h2 : b * h.t⁻¹ = h.t⁻¹ * b := by
      calc b * h.t⁻¹ = h.t⁻¹ * (h.t * b) * h.t⁻¹ := by group
        _ = h.t⁻¹ * (b * h.t) * h.t⁻¹ := by rw [hbt b hb]
        _ = h.t⁻¹ * b := by group
    calc b * ((c : G) * h.t⁻¹) = b * (c : G) * b⁻¹ * (b * h.t⁻¹) := by group
      _ = (c : G) * (h.t⁻¹ * b) := by rw [h1, h2]
      _ = (c : G) * h.t⁻¹ * b := by group
  have h1 := hC _ hct hctH
  have hct' : (c : G) = h.t := by
    calc (c : G) = (c : G) * h.t⁻¹ * h.t := by group
      _ = h.t := by rw [h1, one_mul]
  exact hnt (hct' ▸ c.2)

end Setup

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

theorem _root_.CFSG.LocalAnalysis.EvenBN.TwoF4.Setup.t_mem_J (h : Setup G) : h.t ∈ h.J :=
  h.P_sup_Tsyl_le_J_Kp.1 (mem_sup_right h.t_mem_Tsyl)

theorem A_inf_CH5_le_W : d.A ⊓ h.CH .i5 ≤ d.W := by
  have hY2 : IsPGroup 2 (d.A ⊓ h.CH .i5 : Subgroup G) := d.isPGroup_A.to_le inf_le_left
  have htY : h.t ∈ normalizer ((d.A ⊓ h.CH .i5 : Subgroup G) : Set G) :=
    mem_normalizer_inf (d.J_le_normalizer_A h.t_mem_J) (le_normalizer (h.t_mem_CH .i5))
  have hHCH : h.H ≤ normalizer (h.CH .i5 : Set G) := fun b hb =>
    le_normalizer (mem_centralizer_iff.2 fun c hc => h.H_comm (h.Ht_le_H .i5 hc) hb)
  have hHY : h.H ≤ normalizer ((d.A ⊓ h.CH .i5 : Subgroup G) : Set G) := fun b hb =>
    mem_normalizer_inf (d.J_le_normalizer_A (h.H_le_J hb)) (hHCH hb)
  have hV5Y : h.V .i5 ≤ d.A ⊓ h.CH .i5 :=
    le_inf ((h.V_le_R (by decide)).trans d.R_le_A) (h.V_le_centralizer_Ht rfl)
  have hYt2 : IsPGroup 2 ((d.A ⊓ h.CH .i5) ⊔ zpowers h.t : Subgroup G) :=
    hY2.to_sup_of_normal_left' h.isPGroup_zpowers_t (zpowers_le.2 htY)
  have hle := d.le_W_sup _ (sup_le inf_le_right (zpowers_le.2 (h.t_mem_CH .i5))) hYt2
    (sup_le_sup_right hV5Y _)
  exact h.le_of_le_sup_zpowers_t hY2 d.bender.mem_normalizer hHY d.H_le_normalizer_W
    (fun w hw hwH => d.eq_one_of_mem_W_of_mem_centralizer_H hw hwH)
    (fun ht => d.t_not_mem_A ht.1) (le_sup_left.trans hle)

theorem mem_W12_of_mem_A1_of_mem_V5_sup_W12 {z : G} (hzA : z ∈ d.A1)
    (hz : z ∈ h.V .i5 ⊔ d.W12) : z ∈ d.W12 := by
  obtain ⟨v, hv, z', hz', rfl⟩ := exists_mul_of_mem_sup_zIn d.bender.le hz
  have hvA : v ∈ d.A1 := by
    have e : v = v * z' * z'⁻¹ := by group
    rw [e]
    exact mul_mem hzA (inv_mem (d.W12_le_A1 hz'))
  have hvR := d.mem_R₁_of_mem_A1 hvA
    (commutatorElement_eq_one_iff_mul_comm.2 (h.mul_t_comm (h.pull_le_L _ hv)))
  have hv12 : v ∈ h.V .i12 := h.mem_V_of_mem_R₁_of_mem_CH (i := .i5) rfl (by decide)
    hvR (h.V_le_centralizer_Ht rfl hv)
  exact mul_mem (d.V12_le_W12 hv12) hz'

theorem comm_t_mem_A1_of_mem_RA1 {q : G} (hq : q ∈ d.RA1) : ⁅q, h.t⁆ ∈ d.A1 := by
  obtain ⟨r, hr, a, ha, rfl⟩ := d.exists_mul_of_mem_RA1 hq
  rw [commutatorElement_mul_left_eq,
    commutatorElement_eq_one_iff_mul_comm.2 (h.mul_t_comm (h.R_le_L hr)), mul_one]
  exact (mem_normalizer_iff.1 (d.R_le_normalizer_A1 hr) _).1 (d.R₁_le_A1 ha.2.2)

theorem exists_A_CH_comm_t {i : Idx} {u : G} (hu : u ∈ h.R) (huH : u ∈ h.CH i) :
    ∃ c ∈ d.A, c ∈ h.CH i ∧ ⁅c, h.t⁆⁻¹ * u ∈ d.A1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, hα⟩ := d.exists_A_comm_t hu
  have hHJ : ∀ b ∈ h.Ht i, b ∈ h.J := fun b hb => h.H_le_J (h.Ht_le_H i hb)
  have hHA : h.Ht i ≤ normalizer (d.A : Set G) := fun b hb => d.J_le_normalizer_A (hHJ b hb)
  let : MulDistribMulAction (h.Ht i) d.A :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (h.Ht i) d.A hHA
  set N : Subgroup d.A := d.RA1.subgroupOf d.A with hNdef
  have hAN : d.A ≤ normalizer (d.RA1 : Set G) := fun z hz =>
    mem_normalizer_of_conj_mem (fun q hq => d.conj_A_mem_RA1 hz hq) fun q hq => by
      have := d.conj_A_mem_RA1 (inv_mem hz) hq
      rwa [inv_inv] at this
  have : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  have hNinv : CFSG.IsInvariant (h.Ht i) d.A N :=
    CFSG.SolvableHall.isInvariant_of_forall_smul_mem fun b z hz => by
      rw [mem_subgroupOf] at hz ⊢
      exact (mem_normalizer_iff.1 (d.J_le_normalizer_RA1 (hHJ b b.2)) z).1 hz
  have hN2 : IsPGroup 2 N := d.isPGroup_RA1.of_equiv (subgroupOfEquivOfLe d.RA1_le_A).symm
  have hNsolv : Group.IsSolvable N := by
    have := hN2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card (h.Ht i)) (Nat.card N) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hN2
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 (h.odd_card_Ht i))
  set κ := ⁅x, h.t⁆ with hκ
  set α := κ⁻¹ * u with hαdef
  have hκu : κ = u * α⁻¹ := by rw [hαdef]; group
  have hκR : κ ∈ d.RA1 := hx.2.2.2.2
  have hcoset : ∀ b : h.Ht i, (⟨x, hx⟩ : d.A)⁻¹ * (b • (⟨x, hx⟩ : d.A)) ∈ N := by
    intro b
    have hsmul : ((b • (⟨x, hx⟩ : d.A) : d.A) : G) = (b : G) * x * (b : G)⁻¹ := rfl
    rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hsmul]
    have hbJ := hHJ b b.2
    have hy : (b : G) * x * (b : G)⁻¹ ∈ d.A := d.conj_J_mem_A hbJ hx
    refine d.mem_RA1_of_comm_mem_A1 (mul_mem (inv_mem hx) hy) ?_
    have hbt : (b : G) * h.t = h.t * b := mem_centralizer_singleton_iff.1 (mem_inf.1 hbJ).1
    have hbu : (b : G) * u * (b : G)⁻¹ = u := by
      rw [mem_centralizer_iff.1 huH b b.2, mul_inv_cancel_right]
    set ε := ⁅x⁻¹ * ((b : G) * x * (b : G)⁻¹), h.t⁆ *
      (⁅x⁻¹, h.t⁆ * ⁅(b : G) * x * (b : G)⁻¹, h.t⁆)⁻¹ with hε
    have hεA : ε ∈ d.A1 := d.comm_t_mul_mem (inv_mem hx) hy
    set δ := ⁅x * x⁻¹, h.t⁆ * (κ * ⁅x⁻¹, h.t⁆)⁻¹ with hδ
    have hδA : δ ∈ d.A1 := d.comm_t_mul_mem hx (inv_mem hx)
    have e1 : ⁅x⁻¹, h.t⁆ = κ⁻¹ * δ⁻¹ := by
      rw [hδ, mul_inv_cancel, commutatorElement_one_left, one_mul]
      group
    have e2 : ⁅(b : G) * x * (b : G)⁻¹, h.t⁆ = (b : G) * κ * (b : G)⁻¹ := by
      have hbt' : (b : G) * h.t * (b : G)⁻¹ = h.t := by rw [hbt, mul_inv_cancel_right]
      rw [hκ]
      simp only [commutatorElement_def]
      conv_lhs => rw [← hbt']
      group
    have e3 : ⁅x⁻¹ * ((b : G) * x * (b : G)⁻¹), h.t⁆ =
        ε * (α * (u⁻¹ * δ⁻¹ * u)) * ((b : G) * α⁻¹ * (b : G)⁻¹) := by
      have e4 : ⁅x⁻¹ * ((b : G) * x * (b : G)⁻¹), h.t⁆ =
          ε * (⁅x⁻¹, h.t⁆ * ⁅(b : G) * x * (b : G)⁻¹, h.t⁆) := by rw [hε]; group
      rw [e4, e1, e2, hκu]
      calc ε * ((u * α⁻¹)⁻¹ * δ⁻¹ * ((b : G) * (u * α⁻¹) * (b : G)⁻¹)) =
          ε * (α * u⁻¹ * δ⁻¹ * ((b : G) * u * (b : G)⁻¹) * ((b : G) * α⁻¹ * (b : G)⁻¹)) := by
            group
        _ = _ := by rw [hbu]; group
    rw [e3]
    have huN : u⁻¹ ∈ normalizer (d.A1 : Set G) := d.R_le_normalizer_A1 (inv_mem hu)
    refine mul_mem (mul_mem hεA (mul_mem hα ?_))
      ((mem_normalizer_iff.1 (d.J_le_normalizer_A1 hbJ) _).1 (inv_mem hα))
    have := (mem_normalizer_iff.1 huN _).1 (inv_mem hδA)
    simpa [mul_assoc] using this
  obtain ⟨c, hc, hcN⟩ := CFSG.SolvableHall.exists_fixed_of_coset_fixed N hNinv hNsolv hcop
    ⟨x, hx⟩ hcoset
  have hcH : (c : G) ∈ h.CH i := mem_centralizer_iff.2 fun b hb => by
    have := congrArg Subtype.val (hc ⟨b, hb⟩)
    have hsmul : (((⟨b, hb⟩ : h.Ht i) • c : d.A) : G) = b * (c : G) * b⁻¹ := rfl
    rw [hsmul] at this
    calc b * (c : G) = b * c * b⁻¹ * b := by group
      _ = c * b := by rw [this]
  refine ⟨c, c.2, hcH, ?_⟩
  have hq : (c : G)⁻¹ * x ∈ d.RA1 := by
    have := mem_subgroupOf.1 hcN
    simpa using this
  set q := (c : G)⁻¹ * x with hqdef
  have hcx : (c : G) = x * q⁻¹ := by rw [hqdef]; group
  have hθ : x * ⁅q⁻¹, h.t⁆ * x⁻¹ ∈ d.A1 :=
    (mem_normalizer_iff.1 hx.1 _).1 (d.comm_t_mem_A1_of_mem_RA1 (inv_mem hq))
  have e : ⁅(c : G), h.t⁆⁻¹ * u =
      (κ⁻¹ * (x * ⁅q⁻¹, h.t⁆ * x⁻¹)⁻¹ * κ⁻¹⁻¹) * α := by
    rw [hcx, commutatorElement_mul_left_eq, hαdef, hκ]
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mul_mem ((mem_normalizer_iff.1 (d.RA1_le_A (inv_mem hκR)).1 _).1 (inv_mem hθ)) hα

theorem W_le_A : d.W ≤ d.A := by
  intro w hw
  obtain ⟨u, hu, z, hz, hwt⟩ := exists_mul_of_mem_sup_zIn d.bender.le (d.comm_t_mem_V5_sup_W12 hw)
  obtain ⟨c, hcA, hcH, hc⟩ := d.exists_A_CH_comm_t (i := .i5) (h.V_le_R (by decide) hu)
    (h.V_le_centralizer_Ht rfl hu)
  have hcW : c ∈ d.W := d.A_inf_CH5_le_W (mem_inf.2 ⟨hcA, hcH⟩)
  have hc' : u⁻¹ * ⁅c, h.t⁆ ∈ d.W12 := by
    refine d.mem_W12_of_mem_A1_of_mem_V5_sup_W12 ?_
      (mul_mem (mem_sup_left (inv_mem hu)) (d.comm_t_mem_V5_sup_W12 hcW))
    have := inv_mem hc
    simpa using this
  set z' := u⁻¹ * ⁅c, h.t⁆ with hz'
  have hct : ⁅c, h.t⁆ = u * z' := by rw [hz']; group
  have hW12 : ⁅c⁻¹ * w, h.t⁆ ∈ d.W12 := by
    have e : ⁅c⁻¹ * w, h.t⁆ = c⁻¹ * (u * (z * z'⁻¹) * u⁻¹) * c⁻¹⁻¹ := by
      have e1 : ⁅c⁻¹ * w, h.t⁆ = c⁻¹ * (⁅w, h.t⁆ * ⁅c, h.t⁆⁻¹) * c⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e1, hwt, hct]
      group
    rw [e]
    have hu12 : u * (z * z'⁻¹) * u⁻¹ ∈ d.W12 :=
      (mem_normalizer_iff.1 (le_normalizer_zIn d.W (d.bender.le hu)) _).1
        (mul_mem hz (inv_mem hc'))
    exact (mem_normalizer_iff.1 (le_normalizer_zIn d.W (inv_mem hcW)) _).1 hu12
  have hw' : c⁻¹ * w ∈ h.V .i5 ⊔ d.W12 := by
    have h1 := d.bender.mem_of_comm (c⁻¹ * w)⁻¹ (inv_mem (mul_mem (inv_mem hcW) hw)) (by
      have e : (c⁻¹ * w)⁻¹⁻¹ * (h.t⁻¹ * (c⁻¹ * w)⁻¹ * h.t) = ⁅c⁻¹ * w, h.t⁆ := by
        rw [inv_inv, commutatorElement_def, h.t_inv]
        group
      rw [e]
      exact hW12)
    have := inv_mem h1
    rwa [inv_inv] at this
  have hle : h.V .i5 ⊔ d.W12 ≤ d.A :=
    sup_le ((h.V_le_R (by decide)).trans d.R_le_A) (d.W12_le_A1.trans d.A1_le_A)
  have e : w = c * (c⁻¹ * w) := by group
  rw [e]
  exact mul_mem hcA (hle hw')

theorem mem_W6_iff {y : G} : y ∈ d.W6 ↔ h.s * y * h.s⁻¹ ∈ d.W := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h.s_inv]
    rw [show h.s * (h.s * z * h.s) * h.s = (h.s * h.s) * z * (h.s * h.s) by group,
      h.r_mul_self_s_mul_self.2, one_mul, mul_one]
    exact hz
  · intro hy
    refine ⟨h.s * y * h.s⁻¹, hy, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h.s_inv,
      show h.s * (h.s * y * h.s) * h.s = (h.s * h.s) * y * (h.s * h.s) by group,
      h.r_mul_self_s_mul_self.2, one_mul, mul_one]

theorem t_mem_normalizer_W6 : h.t ∈ normalizer (d.W6 : Set G) := by
  have key : ∀ y ∈ d.W6, h.t * y * h.t⁻¹ ∈ d.W6 := by
    intro y hy
    rw [d.mem_W6_iff] at hy ⊢
    have e : h.s * (h.t * y * h.t⁻¹) * h.s⁻¹ = h.t * (h.s * y * h.s⁻¹) * h.t⁻¹ := by
      have h1 := h.s_comm_t
      calc h.s * (h.t * y * h.t⁻¹) * h.s⁻¹ = (h.s * h.t) * y * (h.s * h.t)⁻¹ := by group
        _ = (h.t * h.s) * y * (h.t * h.s)⁻¹ := by rw [h1]
        _ = h.t * (h.s * y * h.s⁻¹) * h.t⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 d.bender.mem_normalizer _).1 hy
  refine mem_normalizer_of_conj_mem key fun y hy => ?_
  have := key y hy
  rw [h.t_inv] at this ⊢
  exact this

theorem H_le_normalizer_W6 : h.H ≤ normalizer (d.W6 : Set G) := by
  have key : ∀ {b : G}, b ∈ h.H → ∀ y ∈ d.W6, b * y * b⁻¹ ∈ d.W6 := by
    intro b hb y hy
    rw [d.mem_W6_iff] at hy ⊢
    have hbs : h.s * b * h.s⁻¹ ∈ h.H := (mem_normalizer_iff.1 h.s_mem_normalizer_H b).1 hb
    have e : h.s * (b * y * b⁻¹) * h.s⁻¹ =
        (h.s * b * h.s⁻¹) * (h.s * y * h.s⁻¹) * (h.s * b * h.s⁻¹)⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 (d.H_le_normalizer_W hbs) _).1 hy
  intro b hb
  refine mem_normalizer_of_conj_mem (key hb) fun y hy => ?_
  have := key (inv_mem hb) y hy
  rwa [inv_inv] at this

theorem eq_one_of_mem_W6_of_mem_centralizer_H {y : G} (hy : y ∈ d.W6)
    (hyH : y ∈ centralizer (h.H : Set G)) : y = 1 := by
  have hyH' : h.s * y * h.s⁻¹ ∈ centralizer (h.H : Set G) := by
    have := mem_normalizer_centralizer (A := h.H) (g := h.s) h.s_mem_normalizer_H
    exact (mem_normalizer_iff.1 this y).1 hyH
  have h1 := d.eq_one_of_mem_W_of_mem_centralizer_H (d.mem_W6_iff.1 hy) hyH'
  have e : y = h.s⁻¹ * (h.s * y * h.s⁻¹) * h.s := by group
  rw [e, h1, mul_one, inv_mul_cancel]

theorem comm_W6_mem_W11 {x y : G} (hx : x ∈ d.W6) (hy : y ∈ d.W6) : ⁅x, y⁆ ∈ d.W11 := by
  rw [d.mem_W11_iff]
  have := d.comm_W_mem_W12 (d.mem_W6_iff.1 hx) (d.mem_W6_iff.1 hy)
  have e : h.s * ⁅x, y⁆ * h.s⁻¹ = ⁅h.s * x * h.s⁻¹, h.s * y * h.s⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact this

theorem W6_mul_self_mem_W11 {x : G} (hx : x ∈ d.W6) : x * x ∈ d.W11 := by
  rw [d.mem_W11_iff]
  have := d.bender.mul_self_mem _ (d.mem_W6_iff.1 hx)
  have e : h.s * (x * x) * h.s⁻¹ = (h.s * x * h.s⁻¹) * (h.s * x * h.s⁻¹) := by group
  rw [e]
  exact this

theorem le_W6_sup (S : Subgroup G) (hS : S ≤ h.CH .i6) (hS2 : IsPGroup 2 S)
    (hVS : h.V .i6 ⊔ zpowers h.t ≤ S) : S ≤ d.W6 ⊔ zpowers h.t := by
  set S' := S.map (MulAut.conj h.s).toMonoidHom with hS'
  have hS'C : S' ≤ h.CH .i5 := by
    rintro _ ⟨z, hz, rfl⟩
    exact h.conj_s_mem_CH (i := .i6) (by decide) (hS hz)
  have hS'2 : IsPGroup 2 S' := hS2.map _
  have hVS' : h.V .i5 ⊔ zpowers h.t ≤ S' := by
    refine sup_le (fun v hv => ?_) (zpowers_le.2 ⟨h.t, hVS (mem_sup_right (mem_zpowers _)), ?_⟩)
    · refine ⟨h.s * v * h.s⁻¹, hVS (mem_sup_left (h.conj_s_mem_V (i := .i5) (by decide) hv)), ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h.s_inv,
        show h.s * (h.s * v * h.s) * h.s = (h.s * h.s) * v * (h.s * h.s) by group,
        h.r_mul_self_s_mul_self.2, one_mul, mul_one]
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h.s_conj_t']
  have hle := d.le_W_sup S' hS'C hS'2 hVS'
  intro y hy
  have hy' : h.s * y * h.s⁻¹ ∈ d.W ⊔ zpowers h.t := hle ⟨y, hy, rfl⟩
  obtain ⟨w, hw, e | e⟩ := exists_eq_or_eq_mul_of_mem_sup h.t_mul_t d.bender.mem_normalizer hy'
  · have hy6 : y ∈ d.W6 := d.mem_W6_iff.2 (e ▸ hw)
    exact mem_sup_left hy6
  · have e' : y = h.s⁻¹ * w * h.s * h.t := by
      calc y = h.s⁻¹ * (h.s * y * h.s⁻¹) * h.s := by group
        _ = h.s⁻¹ * (w * h.t) * h.s := by rw [e]
        _ = h.s⁻¹ * w * h.s * (h.s⁻¹ * h.t * h.s) := by group
        _ = h.s⁻¹ * w * h.s * h.t := by rw [h.s_conj_t]
    have hw6 : h.s⁻¹ * w * h.s ∈ d.W6 := by
      rw [d.mem_W6_iff]
      have e2 : h.s * (h.s⁻¹ * w * h.s) * h.s⁻¹ = w := by group
      rw [e2]
      exact hw
    rw [e']
    exact mul_mem (mem_sup_left hw6) (mem_sup_right (mem_zpowers _))

theorem A_inf_CH6_le_W6 : d.A ⊓ h.CH .i6 ≤ d.W6 := by
  have hY2 : IsPGroup 2 (d.A ⊓ h.CH .i6 : Subgroup G) := d.isPGroup_A.to_le inf_le_left
  have htY : h.t ∈ normalizer ((d.A ⊓ h.CH .i6 : Subgroup G) : Set G) :=
    mem_normalizer_inf (d.J_le_normalizer_A h.t_mem_J) (le_normalizer (h.t_mem_CH .i6))
  have hHCH : h.H ≤ normalizer (h.CH .i6 : Set G) := fun b hb =>
    le_normalizer (mem_centralizer_iff.2 fun c hc => h.H_comm (h.Ht_le_H .i6 hc) hb)
  have hHY : h.H ≤ normalizer ((d.A ⊓ h.CH .i6 : Subgroup G) : Set G) := fun b hb =>
    mem_normalizer_inf (d.J_le_normalizer_A (h.H_le_J hb)) (hHCH hb)
  have hV6Y : h.V .i6 ≤ d.A ⊓ h.CH .i6 :=
    le_inf ((h.V_le_R (by decide)).trans d.R_le_A) (h.V_le_centralizer_Ht rfl)
  have hYt2 : IsPGroup 2 ((d.A ⊓ h.CH .i6) ⊔ zpowers h.t : Subgroup G) :=
    hY2.to_sup_of_normal_left' h.isPGroup_zpowers_t (zpowers_le.2 htY)
  have hle := d.le_W6_sup _ (sup_le inf_le_right (zpowers_le.2 (h.t_mem_CH .i6))) hYt2
    (sup_le_sup_right hV6Y _)
  exact h.le_of_le_sup_zpowers_t hY2 d.t_mem_normalizer_W6 hHY d.H_le_normalizer_W6
    (fun w hw hwH => d.eq_one_of_mem_W6_of_mem_centralizer_H hw hwH)
    (fun ht => d.t_not_mem_A ht.1) (le_sup_left.trans hle)

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4
