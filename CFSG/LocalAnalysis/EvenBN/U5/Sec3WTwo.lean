module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3W
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3FThree

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open CFSG.EvenSmallLie.UnitarySix.YamadaD (crossed_eq_one_iff crossed_conj card_eq_of_crossed_onto)

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.P_le_normalizer_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.P ≤ normalizer (d.F : Set G) := fun _ hp =>
  hd.normalizer_B₁_le_normalizer_F hGMS (hd.T_le_normalizer_B₁ (hd.P_le hp))

theorem Hyp.I_le_normalizer_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.I ≤ normalizer (d.F : Set G) := fun _ hi =>
  hd.normalizer_B₁_le_normalizer_F hGMS (hd.I_le_normalizer_B₁ hi).1

theorem Hyp.isPGroup_F (hd : d.Hyp) : IsPGroup 2 d.F := d.isPGroup_B₅.to_le hd.F_le_B₅

theorem Hyp.exists_mul_of_mem_FP (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {x : G} (hx : x ∈ d.F ⊔ d.P) : ∃ a ∈ d.F, ∃ p ∈ d.P, x = a * p :=
  exists_mul_of_mem_sup_of_le_normalizer (hd.P_le_normalizer_F hGMS) hx

theorem Hyp.F_inf_P (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.F ⊓ d.P = d.A₁ := by
  refine le_antisymm (fun x hx => ?_) (le_inf hd.A₁_le_F d.A₁_le_P)
  rw [← hd.F_inf_centralizer_t hGMS]
  exact ⟨hx.1, hd.L_le_centralizer (d.P_le_L hx.2)⟩

theorem Hyp.cr_F_mem (hd : d.Hyp) {x : G} (hx : x ∈ d.F) : x⁻¹ * d.t * x * d.t ∈ d.A₁ :=
  hd.cosetData_B₁.crossed_mem x (hd.F_le_normalizer_B₁ hx)

theorem Hyp.cr_F_mul (hd : d.Hyp) {x y : G} (hx : x ∈ d.F) (hy : y ∈ d.F) :
    (x * y)⁻¹ * d.t * (x * y) * d.t = (x⁻¹ * d.t * x * d.t) * (y⁻¹ * d.t * y * d.t) :=
  hd.cosetData_B₁.crossed_mul_of_mem ⟨hd.F_le_normalizer_B₁ hx, hd.F_le_centralizer_A₁ hx⟩
    ⟨hd.F_le_normalizer_B₁ hy, hd.F_le_centralizer_A₁ hy⟩

theorem Hyp.cr_F_inv (hd : d.Hyp) {x : G} (hx : x ∈ d.F) :
    x⁻¹⁻¹ * d.t * x⁻¹ * d.t = (x⁻¹ * d.t * x * d.t)⁻¹ :=
  hd.cosetData_B₁.crossed_inv_of_mem ⟨hd.F_le_normalizer_B₁ hx, hd.F_le_centralizer_A₁ hx⟩

theorem Hyp.cr_F_eq_one_iff (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {x : G}
    (hx : x ∈ d.F) : x⁻¹ * d.t * x * d.t = 1 ↔ x ∈ d.A₁ := by
  rw [crossed_eq_one_iff hd.t_mul_t, ← hd.F_inf_centralizer_t hGMS, mem_inf,
    mem_centralizer_singleton_iff]
  exact ⟨fun e => ⟨hx, e⟩, fun e => e.2⟩

theorem Hyp.inv_mul_mem_A₁_of_cr_eq (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {x y : G} (hx : x ∈ d.F) (hy : y ∈ d.F)
    (e : x⁻¹ * d.t * x * d.t = y⁻¹ * d.t * y * d.t) : x⁻¹ * y ∈ d.A₁ := by
  refine (hd.cr_F_eq_one_iff hGMS (mul_mem (inv_mem hx) hy)).1 ?_
  rw [hd.cr_F_mul (inv_mem hx) hy, hd.cr_F_inv hx, e, inv_mul_cancel]

omit [Finite G] in
theorem cr_conj (d : Data G h) {c x : G} (hc : c ∈ centralizer ({d.t} : Set G)) :
    (c * x * c⁻¹)⁻¹ * d.t * (c * x * c⁻¹) * d.t = c * (x⁻¹ * d.t * x * d.t) * c⁻¹ :=
  crossed_conj (mem_centralizer_singleton_iff.1 hc)

theorem Hyp.mem_A₃_of_mem_P_of_comm (hd : d.Hyp) {p : G} (hp : p ∈ d.P)
    (hc : p ∈ centralizer (d.A₁ : Set G)) : p ∈ d.A₃ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpt : p ∈ centralizer ({d.t} : Set G) := hd.L_le_centralizer (d.P_le_L hp)
  have hpB : p ∈ centralizer (d.B₁ : Set G) :=
    mem_centralizer_sup (mem_centralizer_zpowers hpt) hc
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 d.isPGroup_P) ⟨p, hp⟩
  have hpk : p ^ 2 ^ k = 1 := by
    rw [← orderOf_coe] at hk
    simp only at hk
    rw [← hk, pow_orderOf_eq_one]
  obtain ⟨a, ha, hpa | hpa⟩ := hd.exists_of_mem_B₃ (hd.mem_B₃_of_pow hpB hpk)
  · rw [hpa]
    exact ha
  · exfalso
    refine hd.t_not_mem_L ?_
    have := mul_mem (d.P_le_L hp) (inv_mem (d.P_le_L (d.A₃_le_P ha)))
    rwa [hpa, mul_inv_cancel_right] at this

omit [Finite G] in
theorem V_le_FP (d : Data G h) : d.V ≤ d.F ⊔ d.P := d.V_le_F.trans le_sup_left

theorem Hyp.centerIn_FP (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    CFSG.centerIn (d.F ⊔ d.P) = d.V := by
  have hFc := hd.F_comm hGMS
  have hVP : d.V ≤ centralizer (d.P : Set G) := hd.V_le_CB₄I₃.trans hd.CB₄I₃_le_centralizer_P
  have hZP : CFSG.centerIn d.P = d.Zp := d.sec2_2_three.2.2.2.2
  refine le_antisymm (fun x hx => ?_) (le_inf d.V_le_FP fun v hv => ?_)
  · obtain ⟨hxFP, hxc⟩ := hx
    obtain ⟨a, ha, p, hp, rfl⟩ := hd.exists_mul_of_mem_FP hGMS hxFP
    have hpF : ∀ y ∈ d.F, y * p = p * y := by
      intro y hy
      have e1 := mem_centralizer_iff.1 hxc y (mem_sup_left hy)
      have e2 := hFc y hy a ha
      have : a * (y * p) = a * (p * y) := by
        calc a * (y * p) = y * (a * p) := by rw [← mul_assoc, ← e2, mul_assoc]
          _ = a * p * y := e1
          _ = a * (p * y) := by group
      exact mul_left_cancel this
    have hpA₃ : p ∈ d.A₃ := hd.mem_A₃_of_mem_P_of_comm hp
      (mem_centralizer_iff.2 fun y hy => hpF y (hd.A₁_le_F hy))
    have hpA₁ : p ∈ d.A₁ := by
      rw [← d.sec2_2_three.2.2.1]
      refine ⟨hpA₃, mem_centralizer_iff.2 fun y hy => ?_⟩
      have e1 := mem_centralizer_iff.1 hxc y (mem_sup_right (d.A₃_le_P hy))
      have e2 : y * a = a * y := mem_centralizer_iff.1 (hd.F_le_centralizer_A₃ ha) y hy
      have : a * (y * p) = a * (p * y) := by
        calc a * (y * p) = y * a * p := by rw [← mul_assoc, e2]
          _ = a * p * y := by rw [mul_assoc]; exact e1
          _ = a * (p * y) := by group
      exact mul_left_cancel this
    have hxF : a * p ∈ d.F := mul_mem ha (hd.A₁_le_F hpA₁)
    have hxP : ∀ y ∈ d.P, y * (a * p) = (a * p) * y := fun y hy =>
      mem_centralizer_iff.1 hxc y (mem_sup_right hy)
    have hcr : (a * p)⁻¹ * d.t * (a * p) * d.t ∈ d.Zp := by
      rw [← hZP]
      refine ⟨d.A₁_le_P (hd.cr_F_mem hxF), mem_centralizer_iff.2 fun y hy => ?_⟩
      have hyC : y ∈ centralizer ({d.t} : Set G) := hd.L_le_centralizer (d.P_le_L hy)
      have e := d.cr_conj (x := a * p) hyC
      rw [show y * (a * p) * y⁻¹ = a * p by rw [hxP y hy, mul_inv_cancel_right]] at e
      calc y * ((a * p)⁻¹ * d.t * (a * p) * d.t)
          = y * ((a * p)⁻¹ * d.t * (a * p) * d.t) * y⁻¹ * y := by group
        _ = (a * p)⁻¹ * d.t * (a * p) * d.t * y := by rw [← e]
    obtain ⟨v, hv, hvt⟩ := hd.exists_V_cr_eq hcr
    have hva : v⁻¹ * (a * p) ∈ d.A₁ :=
      hd.inv_mul_mem_A₁_of_cr_eq hGMS (d.V_le_F hv) hxF hvt
    have hvaZ : v⁻¹ * (a * p) ∈ d.Zp := by
      rw [← hZP]
      refine ⟨d.A₁_le_P hva, mem_centralizer_iff.2 fun y hy => ?_⟩
      have e1 := mem_centralizer_iff.1 (hVP hv) y hy
      calc y * (v⁻¹ * (a * p)) = v⁻¹ * (v * y * v⁻¹) * (a * p) := by group
        _ = v⁻¹ * y * (a * p) := by rw [← e1]; group
        _ = v⁻¹ * (a * p) * y := by rw [mul_assoc, hxP y hy, ← mul_assoc]
    have := mul_mem hv (hd.Zp_le_V hvaZ)
    rwa [mul_inv_cancel_left] at this
  · have hle : d.F ⊔ d.P ≤ centralizer (d.V : Set G) :=
      sup_le (fun a ha => mem_centralizer_iff.2 fun w hw => hFc w (d.V_le_F hw) a ha)
        (fun p hp => mem_centralizer_iff.2 fun w hw => (mem_centralizer_iff.1 (hVP hw) p hp).symm)
    exact mem_centralizer_iff.2 fun y hy => (mem_centralizer_iff.1 (hle hy) v hv).symm

omit [Finite G] in
theorem odd_card_I₄ (d : Data G h) : Odd (Nat.card d.I₄) :=
  Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le d.I₄_le_I)

theorem Hyp.FP_inf_centralizer_I₄ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    (d.F ⊔ d.P) ⊓ centralizer (d.I₄ : Set G) = d.F ⊓ centralizer (d.I₄ : Set G) := by
  refine le_antisymm (fun x hx => ?_) (inf_le_inf_right _ le_sup_left)
  obtain ⟨hxFP, hxc⟩ := hx
  obtain ⟨i, hi, hgen, -⟩ := d.exists_I₄_generic hd.two_le
  obtain ⟨a, ha, p, hp, rfl⟩ := hd.exists_mul_of_mem_FP hGMS hxFP
  have hiI := d.I₄_le_I hi
  have hia : i * a * i⁻¹ ∈ d.F := (mem_normalizer_iff.1 (hd.I_le_normalizer_F hGMS hiI) a).1 ha
  have hip : i * p * i⁻¹ ∈ d.P := (mem_normalizer_iff.1 (d.I_le_normalizer_P hiI) p).1 hp
  have hfix : i * (a * p) * i⁻¹ = a * p := by
    rw [mem_centralizer_iff.1 hxc i hi, mul_inv_cancel_right]
  have e : i * p * i⁻¹ * p⁻¹ = (i * a * i⁻¹)⁻¹ * a := by
    have : (i * a * i⁻¹) * (i * p * i⁻¹) = a * p := by rw [← hfix]; group
    calc i * p * i⁻¹ * p⁻¹ = (i * a * i⁻¹)⁻¹ * ((i * a * i⁻¹) * (i * p * i⁻¹)) * p⁻¹ := by
          group
      _ = (i * a * i⁻¹)⁻¹ * a := by rw [this]; group
  have hmem : i * p * i⁻¹ * p⁻¹ ∈ d.A₁ := by
    rw [← hd.F_inf_P hGMS]
    exact Subgroup.mem_inf.2 ⟨e ▸ mul_mem (inv_mem hia) ha, mul_mem hip (inv_mem hp)⟩
  exact ⟨mul_mem ha (hd.A₁_le_F (hgen p hp hmem)), hxc⟩

theorem Hyp.W_eq (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.W = d.V ⊔ (d.F ⊓ centralizer (d.I₄ : Set G)) := by
  rw [Data.W, hd.FP_inf_centralizer_I₄ hGMS]

theorem Hyp.C₄_le_A₁ (hd : d.Hyp) : d.P ⊓ centralizer (d.I₄ : Set G) ≤ d.A₁ :=
  (le_sup_right.trans hd.Z₂p_eq.1.ge).trans d.Z₂p_le_A₁

theorem Hyp.A₁_inf_centralizer_I₄ (hd : d.Hyp) :
    d.A₁ ⊓ centralizer (d.I₄ : Set G) = d.P ⊓ centralizer (d.I₄ : Set G) :=
  le_antisymm (inf_le_inf_right _ d.A₁_le_P) (le_inf hd.C₄_le_A₁ inf_le_right)

theorem Hyp.cr_mem_centralizer_I₄ (hd : d.Hyp) {x : G} (hx : x ∈ centralizer (d.I₄ : Set G)) :
    x⁻¹ * d.t * x * d.t ∈ centralizer (d.I₄ : Set G) := by
  refine mem_centralizer_iff.2 fun i hi => ?_
  have hiC : i ∈ centralizer ({d.t} : Set G) := hd.L_le_centralizer (d.pull_le_L _ hi)
  have e := d.cr_conj (x := x) hiC
  rw [show i * x * i⁻¹ = x by rw [mem_centralizer_iff.1 hx i hi, mul_inv_cancel_right]] at e
  calc i * (x⁻¹ * d.t * x * d.t) = i * (x⁻¹ * d.t * x * d.t) * i⁻¹ * i := by group
    _ = x⁻¹ * d.t * x * d.t * i := by rw [← e]

theorem Hyp.cr_F_I₄_mem (hd : d.Hyp) {x : G} (hx : x ∈ d.F ⊓ centralizer (d.I₄ : Set G)) :
    x⁻¹ * d.t * x * d.t ∈ d.P ⊓ centralizer (d.I₄ : Set G) :=
  ⟨d.A₁_le_P (hd.cr_F_mem hx.1), hd.cr_mem_centralizer_I₄ hx.2⟩

theorem Hyp.exists_F_I₄_cr_eq (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {a : G}
    (ha : a ∈ d.P ⊓ centralizer (d.I₄ : Set G)) :
    ∃ c ∈ d.F ⊓ centralizer (d.I₄ : Set G), c⁻¹ * d.t * c * d.t = a := by
  obtain ⟨x, hx, hxa⟩ := hd.exists_F_cr_eq (hd.C₄_le_A₁ ha)
  have hFc := hd.F_comm hGMS
  have hsolv : Group.IsSolvable d.F :=
    Group.isSolvable_of_comm fun u w => Subtype.ext (hFc u u.2 w w.2)
  have hI₄F : d.I₄ ≤ normalizer (d.F : Set G) := d.I₄_le_I.trans (hd.I_le_normalizer_F hGMS)
  have hI₄A : d.I₄ ≤ normalizer (d.A₁ : Set G) := d.I₄_le_I.trans d.I_le_normalizer_A₁
  have hFA : d.F ≤ normalizer (d.A₁ : Set G) := fun u hu =>
    Subgroup.centralizer_le_normalizer _ (hd.F_le_centralizer_A₁ hu)
  obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime hd.A₁_le_F hFA
    hI₄F hI₄A hsolv (coprime_card_of_odd d.odd_card_I₄ hd.isPGroup_F) hx fun s hs => by
      have hsC : s ∈ centralizer ({d.t} : Set G) := hd.L_le_centralizer (d.pull_le_L _ hs)
      have hsx : s * x * s⁻¹ ∈ d.F := (mem_normalizer_iff.1 (hI₄F hs) x).1 hx
      refine hd.inv_mul_mem_A₁_of_cr_eq hGMS hx hsx ?_
      rw [d.cr_conj hsC, hxa, mem_centralizer_iff.1 ha.2 s hs, mul_inv_cancel_right]
  refine ⟨c, hc, ?_⟩
  have hnF := hd.A₁_le_F hn
  have hn1 : n⁻¹ * d.t * n * d.t = 1 := (hd.cr_F_eq_one_iff hGMS hnF).2 hn
  rw [← hxa, hd.cr_F_mul hc.1 hnF, hn1, mul_one]

theorem Hyp.F_I₄_inf_centralizer_t (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    (d.F ⊓ centralizer (d.I₄ : Set G)) ⊓ centralizer ({d.t} : Set G) =
      d.P ⊓ centralizer (d.I₄ : Set G) := by
  rw [inf_right_comm, hd.F_inf_centralizer_t hGMS, hd.A₁_inf_centralizer_I₄]

theorem Hyp.card_F_I₄ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    Nat.card (d.F ⊓ centralizer (d.I₄ : Set G) : Subgroup G) = (2 ^ f) ^ 4 := by
  have hYB : d.F ⊓ centralizer (d.I₄ : Set G) ≤
      centralizer ((d.P ⊓ centralizer (d.I₄ : Set G) : Subgroup G) : Set G) :=
    inf_le_left.trans (hd.F_le_centralizer_A₁.trans (centralizer_le hd.C₄_le_A₁))
  rw [card_eq_of_crossed_onto hd.t_mul_t hYB (fun _ hy => hd.cr_F_I₄_mem hy)
    (fun _ hb => hd.exists_F_I₄_cr_eq hGMS hb), hd.F_I₄_inf_centralizer_t hGMS, hd.card_C₄]
  ring

theorem Hyp.V_inf_F_I₄ (hd : d.Hyp) : d.V ⊓ (d.F ⊓ centralizer (d.I₄ : Set G)) = ⊥ := by
  refine eq_bot_iff.2 fun v hv => ?_
  obtain ⟨hvV, -, hvc⟩ := hv
  have hvB : v ∈ d.B₄ := (hd.V_le_CB₄I₃.trans d.CB₄I₃_le) hvV
  have hcr : v⁻¹ * d.t * v * d.t = 1 := by
    rw [← mem_bot, ← hd.Z₂p_eq.2]
    exact ⟨hd.cr_mem hvB, d.Zp_le_P (hd.cr_mem hvB), hd.cr_mem_centralizer_I₄ hvc⟩
  have hvZ : v ∈ d.Zp := by
    rw [← hd.V_inf_centralizer_t]
    exact ⟨hvV, mem_centralizer_singleton_iff.2 ((crossed_eq_one_iff hd.t_mul_t).1 hcr)⟩
  rw [← hd.Z₂p_eq.2]
  exact ⟨hvZ, d.Zp_le_P hvZ, hvc⟩

theorem Hyp.W_le_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) : d.W ≤ d.F := by
  rw [hd.W_eq hGMS]
  exact sup_le d.V_le_F inf_le_left

theorem Hyp.card_W (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    Nat.card d.W = (2 ^ f) ^ 6 := by
  have hFc := hd.F_comm hGMS
  have hN : d.F ⊓ centralizer (d.I₄ : Set G) ≤ normalizer (d.V : Set G) := fun c hc =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun v hv =>
      hFc v (d.V_le_F hv) c hc.1)
  have h1 := Common.card_sup_mul_card_inf_eq hN
  rw [hd.V_inf_F_I₄, card_bot, mul_one, hd.card_V, hd.card_F_I₄ hGMS] at h1
  rw [hd.W_eq hGMS, h1]
  ring

end Data

end CFSG.LocalAnalysis.EvenBN.U5
