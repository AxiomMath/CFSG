module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootAh
public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootB4e

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

theorem B2_le_centralizer_B4 : d.B2 ≤ centralizer (d.B4 : Set G) := by
  rw [← d.sec3_8_three.1]
  exact inf_le_left

theorem comm_comm_t_mem_B2 {x y : G} (hx : x ∈ d.B4) (hy : y ∈ d.B4) :
    ⁅⁅x, y⁆, h.t⁆ ∈ d.B2 := by
  have hcent : ∀ {b g : G}, b ∈ d.B2 → g ∈ d.B4 → g * b = b * g := fun {b g} hb hg =>
    mem_centralizer_iff.1 (d.B2_le_centralizer_B4 hb) g hg
  set a := ⁅x, h.t⁆⁻¹ with ha
  set b := ⁅y, h.t⁆⁻¹ with hb
  have haQ : a ∈ d.Q4 := inv_mem hx.2.2.2.2
  have hbQ : b ∈ d.Q4 := inv_mem hy.2.2.2.2
  have haB := d.Q4_le_B4 haQ
  have hbB := d.Q4_le_B4 hbQ
  set z := ⁅x, y⁆ with hz
  have hzB : z ∈ d.B4 := by
    rw [hz, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have htx : h.t * x * h.t⁻¹ = a * x := by rw [ha, commutatorElement_def]; group
  have hty : h.t * y * h.t⁻¹ = b * y := by rw [hb, commutatorElement_def]; group
  have htz : h.t * z * h.t⁻¹ = ⁅a * x, b * y⁆ := by
    rw [hz, conjugate_commutatorElement, htx, hty]
  set β₀ := ⁅x, b⁆ with hβ₀
  set β₁ := ⁅a, b * y⁆ with hβ₁
  set β₂ := ⁅a * b, z⁆ with hβ₂
  have h0 : β₀ ∈ d.B2 := d.comm_B4_Q4_mem hx hbQ
  have h1 : β₁ ∈ d.B2 := by
    rw [hβ₁, ← commutatorElement_inv]
    exact inv_mem (d.comm_B4_Q4_mem (mul_mem hbB hy) haQ)
  have h2 : β₂ ∈ d.B2 := by
    rw [hβ₂, ← commutatorElement_inv]
    exact inv_mem (d.comm_B4_Q4_mem hzB (mul_mem haQ hbQ))
  have e1 : ⁅a * x, b * y⁆ = a * β₀ * (b * z * b⁻¹) * a⁻¹ * β₁ := by
    rw [hβ₀, hβ₁, hz]
    simp only [commutatorElement_def]
    group
  have e2 : a * β₀ = β₀ * a := hcent h0 haB
  have e3 : ⁅a * x, b * y⁆ = β₀ * (β₂ * z) * β₁ := by
    rw [e1, e2, hβ₂]
    simp only [commutatorElement_def]
    group
  have e4 : ⁅z, h.t⁆ = z * (h.t * z * h.t⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  have e5 : z * β₁⁻¹ = β₁⁻¹ * z := hcent (inv_mem h1) hzB
  have e6 : z * (β₀ * (β₂ * z) * β₁)⁻¹ = β₁⁻¹ * β₂⁻¹ * β₀⁻¹ := by
    calc z * (β₀ * (β₂ * z) * β₁)⁻¹ = (z * β₁⁻¹) * z⁻¹ * β₂⁻¹ * β₀⁻¹ := by group
      _ = β₁⁻¹ * β₂⁻¹ * β₀⁻¹ := by rw [e5]; group
  rw [e4, htz, e3, e6]
  exact mul_mem (mul_mem (inv_mem h1) (inv_mem h2)) (inv_mem h0)

theorem comm_t_mem_R₁_of_mem_A1 {z : G} (hz : ⁅z, h.t⁆ ∈ d.A1) : ⁅z, h.t⁆ ∈ h.R₁ := by
  have ht : h.t⁻¹ = h.t := h.t_inv
  have htt : h.t * ⁅z, h.t⁆ * h.t⁻¹ = ⁅z, h.t⁆⁻¹ := by
    calc h.t * ⁅z, h.t⁆ * h.t⁻¹ = h.t * z * h.t * z⁻¹ * (h.t⁻¹ * h.t⁻¹) := by
          rw [commutatorElement_def]; group
      _ = h.t * z * h.t * z⁻¹ := by rw [ht, h.t_mul_t, mul_one]
      _ = ⁅z, h.t⁆⁻¹ := by
          rw [commutatorElement_def]
          simp only [mul_inv_rev, inv_inv, ht, mul_assoc]
  refine d.mem_R₁_of_mem_A1 hz ?_
  rw [commutatorElement_eq_one_iff_mul_comm]
  have h1 : h.t * ⁅z, h.t⁆ * h.t⁻¹ = ⁅z, h.t⁆ := by
    rw [htt]
    exact inv_eq_of_mul_eq_one_left (d.A1_mul_self hz)
  calc ⁅z, h.t⁆ * h.t = h.t * ⁅z, h.t⁆ * h.t⁻¹ * h.t := by rw [h1]
    _ = h.t * ⁅z, h.t⁆ := by group

theorem comm_B4_A1_mem_A1 {x y : G} (hx : x ∈ d.B4) (hy : y ∈ d.A1) : ⁅x, y⁆ ∈ d.A1 := by
  have hyB := d.A1_le_B4 hy
  have hxW : x ∈ centralizer (d.W12 : Set G) := mem_centralizer_iff.2 fun w hw =>
    (mem_centralizer_iff.1 (d.B2_le_centralizer_B4 (d.W12_le_B1.trans
      (le_sup_right : d.B1 ≤ d.B2) hw)) x hx).symm
  refine ⟨mem_centralizer_iff.2 fun v hv => ?_, ?_, ?_⟩
  · have hvS : v ∈ h.S₄ := (sup_le (h.V_le_S₄ (by decide)) h.R₁_le_S₄_V12_le_S₁.1) hv
    have hβ : ⁅x⁻¹, v⁆ ∈ d.A1 := d.B2_le_A1 ((inv_mem hx).2.2.1 v hvS)
    have h1 : x⁻¹ * v * x = ⁅x⁻¹, v⁆ * v := by simp only [commutatorElement_def]; group
    have hyv : v * y = y * v := mem_centralizer_iff.1 hy.1 v hv
    have hyβ : y * ⁅x⁻¹, v⁆ = ⁅x⁻¹, v⁆ * y := d.A1_comm hy hβ
    have hyv' : y * (x⁻¹ * v * x) = (x⁻¹ * v * x) * y := by
      rw [h1, ← mul_assoc, hyβ, mul_assoc, ← hyv, mul_assoc]
    have hvy : v * y⁻¹ = y⁻¹ * v := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, hyv, inv_mul_cancel_left]
    calc v * ⁅x, y⁆ = x * (x⁻¹ * v * x) * y * x⁻¹ * y⁻¹ := by
          rw [commutatorElement_def]; group
      _ = x * (y * (x⁻¹ * v * x)) * x⁻¹ * y⁻¹ := by rw [mul_assoc x, ← hyv', ← mul_assoc]
      _ = x * y * x⁻¹ * (v * y⁻¹) := by group
      _ = ⁅x, y⁆ * v := by rw [hvy, commutatorElement_def]; group
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hxW hy.2.1) (inv_mem hxW)) (inv_mem hy.2.1)
  · exact d.comm_t_mem_R₁_of_mem_A1 (d.B2_le_A1 (d.comm_comm_t_mem_B2 hx hyB))

theorem B4_le_normalizer_A1 : d.B4 ≤ normalizer (d.A1 : Set G) := fun x hx =>
  mem_normalizer_of_conj_mem (fun y hy => by
      rw [show x * y * x⁻¹ = ⁅x, y⁆ * y by simp only [commutatorElement_def]; group]
      exact mul_mem (d.comm_B4_A1_mem_A1 hx hy) hy)
    fun y hy => by
      rw [show x⁻¹ * y * x = ⁅x⁻¹, y⁆ * y by simp only [commutatorElement_def]; group]
      exact mul_mem (d.comm_B4_A1_mem_A1 (inv_mem hx) hy) hy

theorem B4_le_centralizer_W12 : d.B4 ≤ centralizer (d.W12 : Set G) := fun x hx =>
  mem_centralizer_iff.2 fun _ hw => (mem_centralizer_iff.1 (d.B2_le_centralizer_B4
    (d.W12_le_B1.trans (le_sup_right : d.B1 ≤ d.B2) hw)) x hx).symm

@[expose] def D : Subgroup G where
  carrier := {x | x ∈ normalizer (d.A1 : Set G) ∧ x ∈ centralizer (d.W12 : Set G) ∧
    ∀ a ∈ d.A1, ⁅x, a⁆ ∈ d.W12}
  mul_mem' := fun {x y} hx hy => by
    refine ⟨mul_mem hx.1 hy.1, mul_mem hx.2.1 hy.2.1, fun a ha => ?_⟩
    rw [commutatorElement_mul_left_eq, ← mem_centralizer_iff.1 hx.2.1 _ (hy.2.2 a ha),
      mul_inv_cancel_right]
    exact mul_mem (hy.2.2 a ha) (hx.2.2 a ha)
  one_mem' := ⟨one_mem _, one_mem _, fun a _ => by
    rw [commutatorElement_one_left]; exact one_mem _⟩
  inv_mem' := fun {x} hx => by
    have e : ∀ y : G, ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x⁻¹⁻¹ := fun y => by
      simp only [commutatorElement_def]
      group
    refine ⟨inv_mem hx.1, inv_mem hx.2.1, fun a ha => ?_⟩
    rw [e, ← mem_centralizer_iff.1 (inv_mem hx.2.1) _ (inv_mem (hx.2.2 a ha)),
      mul_inv_cancel_right]
    exact inv_mem (hx.2.2 a ha)

theorem A_le_D : d.A ≤ d.D := fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.2.1⟩

theorem mem_normalizer_D {g : G} (hgA : g ∈ normalizer (d.A1 : Set G))
    (hgW : g ∈ normalizer (d.W12 : Set G)) : g ∈ normalizer (d.D : Set G) := by
  have key : ∀ {g : G}, g ∈ normalizer (d.A1 : Set G) → g ∈ normalizer (d.W12 : Set G) →
      ∀ x ∈ d.D, g * x * g⁻¹ ∈ d.D := by
    intro g hgA hgW x hx
    have e : ∀ y : G, ⁅g * x * g⁻¹, y⁆ = g * ⁅x, g⁻¹ * y * g⁻¹⁻¹⁆ * g⁻¹ := fun y => by
      simp only [commutatorElement_def]
      group
    refine ⟨mul_mem (mul_mem hgA hx.1) (inv_mem hgA),
      (mem_normalizer_iff.1 (mem_normalizer_centralizer hgW) x).1 hx.2.1, fun a ha => ?_⟩
    rw [e]
    exact (mem_normalizer_iff.1 hgW _).1 (hx.2.2 _ ((mem_normalizer_iff.1 (inv_mem hgA) a).1 ha))
  refine mem_normalizer_of_conj_mem (key hgA hgW) fun x hx => ?_
  have := key (inv_mem hgA) (inv_mem hgW) x hx
  rwa [inv_inv] at this

theorem J_le_normalizer_D : h.J ≤ normalizer (d.D : Set G) := fun _ hj =>
  d.mem_normalizer_D (d.J_le_normalizer_A1 hj) (d.J_le_normalizer_W12 hj)

theorem B4_le_normalizer_D : d.B4 ≤ normalizer (d.D : Set G) := fun _ hx =>
  d.mem_normalizer_D (d.B4_le_normalizer_A1 hx)
    (Subgroup.centralizer_le_normalizer _ (d.B4_le_centralizer_W12 hx))

theorem t_not_mem_D : h.t ∉ d.D := fun ht => d.t_not_mem_centralizer_W12 ht.2.1

theorem eq_one_of_mem_N1_of_comm_mem_W12 {r m : G} (hr : r ∈ h.R) (hm : m ∈ h.N .i1)
    (hrm : ∀ y ∈ h.R₁, ⁅r * m, y⁆ ∈ d.W12) : m = 1 := by
  refine h.eq_one_of_mem_N1_of_comm_mem_V12 hm fun y hy => ?_
  have hry : ⁅r, y⁆ ∈ h.V .i12 := by
    rw [← h.commutator_R_R₁]
    exact commutator_mem_commutator hr hy
  have hmy : ⁅m, y⁆ ∈ d.W12 := by
    have e : ⁅m, y⁆ = r⁻¹ * (⁅r * m, y⁆ * ⁅r, y⁆⁻¹) * r := by
      rw [commutatorElement_mul_left_eq]
      group
    have hz : ⁅r * m, y⁆ * ⁅r, y⁆⁻¹ ∈ d.W12 :=
      mul_mem (hrm y hy) (inv_mem (d.V12_le_W12 hry))
    rw [e, mem_centralizer_iff.1 (d.W12_le_centralizer_R hz) r⁻¹ (inv_mem hr),
      inv_mul_cancel_right]
    exact hz
  have hmyL : ⁅m, y⁆ ∈ h.L := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (h.N_le_L _ hm) (h.pull_le_L _ hy))
      (inv_mem (h.N_le_L _ hm))) (inv_mem (h.pull_le_L _ hy))
  exact d.mem_V12_of_commute hmy (h.mul_t_comm hmyL)

theorem mem_R_of_mem_D_of_commute {x : G} (hx : x ∈ d.D) (hxt : x * h.t = h.t * x) :
    x ∈ h.R := by
  have hxE : x ∈ h.CE := mem_inf.2 ⟨mem_centralizer_singleton_iff.2 hxt,
    centralizer_le (SetLike.coe_subset_coe.2 d.V12_le_W12) hx.2.1⟩
  obtain ⟨r, hr, m, hm, hxm | hxm⟩ := h.exists_of_mem_CE hxE
  · have hm1 : m = 1 := d.eq_one_of_mem_N1_of_comm_mem_W12 hr hm fun y hy => by
      rw [← hxm]
      exact hx.2.2 y (d.R₁_le_A1 hy)
    rw [hxm, hm1, mul_one]
    exact hr
  · have hm1 : m = 1 := d.eq_one_of_mem_N1_of_comm_mem_W12 hr hm fun y hy => by
      have e : ⁅r * m, y⁆ = ⁅x, y⁆ := by
        rw [hxm, commutatorElement_mul_left_eq (r * m) h.t y,
          commutatorElement_eq_one_iff_mul_comm.2 (h.mul_t_comm (h.pull_le_L _ hy)).symm]
        group
      rw [e]
      exact hx.2.2 y (d.R₁_le_A1 hy)
    rw [hm1, mul_one] at hxm
    refine absurd ?_ d.t_not_mem_D
    have e : h.t = r⁻¹ * x := by rw [hxm]; group
    rw [e]
    exact mul_mem (inv_mem (d.A_le_D (d.R_le_A hr))) hx

theorem _root_.CFSG.LocalAnalysis.EvenBN.TwoF4.Setup.exists_eq_or_eq_mul_t (h : Setup G)
    {M : Subgroup G} (htM : h.t ∈ normalizer (M : Set G)) {x : G}
    (hx : x ∈ M ⊔ zpowers h.t) : ∃ m ∈ M, x = m ∨ x = m * h.t := by
  have hle : zpowers h.t ≤ normalizer (M : Set G) := zpowers_le.2 htM
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left M (zpowers h.t) hle,
    Set.mem_mul] at hx
  obtain ⟨m, hm, c, hc, rfl⟩ := hx
  rcases eq_one_or_eq_of_mem_zpowers h.t_mul_t hc with rfl | rfl
  · exact ⟨m, hm, Or.inl (mul_one m)⟩
  · exact ⟨m, hm, Or.inr rfl⟩

theorem _root_.CFSG.LocalAnalysis.EvenBN.TwoF4.mem_normalizer_of_mem_normalizer_subgroupOf
    {X : Type*} [Group X] {H M : Subgroup X} (hHM : H ≤ M) {m : M}
    (hm : m ∈ normalizer ((H.subgroupOf M : Subgroup M) : Set M)) :
    (m : X) ∈ normalizer (H : Set X) := by
  rw [mem_normalizer_iff] at hm ⊢
  intro x
  constructor
  · intro hx
    have := (hm ⟨x, hHM hx⟩).1 (mem_subgroupOf.2 hx)
    rw [mem_subgroupOf] at this
    simpa using this
  · intro hx
    have hxM : x ∈ M := by
      have h1 : (m : X) * x * (m : X)⁻¹ ∈ M := hHM hx
      have e : x = (m : X)⁻¹ * ((m : X) * x * (m : X)⁻¹) * m := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem m.2) h1) m.2
    have := (hm ⟨x, hxM⟩).2 (mem_subgroupOf.2 (by simpa using hx))
    exact mem_subgroupOf.1 this

theorem eq_A_of_le_D {B : Subgroup G} (hBD : B ≤ d.D) (hB2 : IsPGroup 2 B) (hAB : d.A ≤ B)
    (htB : h.t ∈ normalizer (B : Set G)) : B = d.A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (fun b hb => ?_) hAB
  by_contra hbA
  have htA : h.t ∈ normalizer (d.A : Set G) := d.J_le_normalizer_A h.t_mem_J
  have htD : ∀ {x : G}, x ∈ B → x ≠ h.t := fun hx hxt => d.t_not_mem_D (hxt ▸ hBD hx)
  set M : Subgroup G := B ⊔ zpowers h.t with hMdef
  set H : Subgroup G := d.A ⊔ zpowers h.t with hHdef
  have hM2 : IsPGroup 2 M := hB2.to_sup_of_normal_left' h.isPGroup_zpowers_t (zpowers_le.2 htB)
  have hHM : H ≤ M := sup_le_sup_right hAB _
  have htH : h.t ∈ H := mem_sup_right (mem_zpowers _)
  have hHB : ∀ {x : G}, x ∈ H → x ∈ B → x ∈ d.A := by
    intro x hxH hxB
    obtain ⟨a, ha, rfl | rfl⟩ := h.exists_eq_or_eq_mul_t htA hxH
    · exact ha
    · exfalso
      have e : h.t = a⁻¹ * (a * h.t) := by group
      exact htD (e ▸ mul_mem (inv_mem (hAB ha)) hxB) rfl
  have hlt : H.subgroupOf M < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hbA (hHB ?_ hb)
    have : (⟨b, mem_sup_left hb⟩ : M) ∈ H.subgroupOf M := htop ▸ mem_top _
    exact mem_subgroupOf.1 this
  have : Group.IsNilpotent M := hM2.isNilpotent
  have hgrow := Group.normalizerCondition_of_isNilpotent _ hlt
  obtain ⟨⟨m, hmM⟩, hmN, hmH⟩ := IsConcreteLE.exists_of_lt hgrow
  rw [mem_subgroupOf] at hmH
  change m ∉ H at hmH
  have hmN' : m ∈ normalizer (H : Set G) := mem_normalizer_of_mem_normalizer_subgroupOf hHM hmN
  have htN : h.t ∈ normalizer (H : Set G) := le_normalizer htH
  obtain ⟨n, hnB, hnH, hnN⟩ : ∃ n ∈ B, n ∉ H ∧ n ∈ normalizer (H : Set G) := by
    obtain ⟨n, hn, hmn | hmn⟩ := h.exists_eq_or_eq_mul_t htB hmM
    · rw [hmn] at hmH hmN'
      exact ⟨n, hn, hmH, hmN'⟩
    · rw [hmn] at hmH hmN'
      refine ⟨n, hn, fun hnH => hmH (mul_mem hnH htH), ?_⟩
      have := mul_mem hmN' (inv_mem htN)
      rwa [mul_inv_cancel_right] at this
  have hnA : n ∈ normalizer (d.A : Set G) := by
    refine mem_normalizer_of_conj_mem (fun a ha => hHB ((mem_normalizer_iff.1 hnN a).1
      (mem_sup_left ha)) (mul_mem (mul_mem hnB (hAB ha)) (inv_mem hnB))) fun a ha => ?_
    refine hHB ?_ (mul_mem (mul_mem (inv_mem hnB) (hAB ha)) hnB)
    have := (mem_normalizer_iff.1 (inv_mem hnN) a).1 (mem_sup_left ha)
    rwa [inv_inv] at this
  have hnt : h.t⁻¹ * n⁻¹ * h.t * n ∈ d.A := by
    obtain ⟨a, ha, hc | hc⟩ := h.exists_eq_or_eq_mul_t htA ((mem_normalizer_iff.1 hnN h.t).1 htH)
    · exfalso
      have e : h.t = n⁻¹ * a * n := by rw [← hc]; group
      exact htD (e ▸ mul_mem (mul_mem (inv_mem hnB) (hAB ha)) hnB) rfl
    · have h1 : n * h.t⁻¹ * n⁻¹ = h.t⁻¹ * a⁻¹ := by
        have := congrArg (·⁻¹) hc
        simpa [mul_assoc] using this
      have e : h.t⁻¹ * n⁻¹ * h.t * n = n⁻¹ * (h.t⁻¹ * a⁻¹ * h.t) * n := by
        calc h.t⁻¹ * n⁻¹ * h.t * n = n⁻¹ * (n * h.t⁻¹ * n⁻¹) * h.t * n := by group
          _ = n⁻¹ * (h.t⁻¹ * a⁻¹) * h.t * n := by rw [h1]
          _ = _ := by group
      rw [e]
      have h2 : h.t⁻¹ * a⁻¹ * h.t ∈ d.A := by
        have := (mem_normalizer_iff.1 (inv_mem htA) a⁻¹).1 (inv_mem ha)
        rwa [inv_inv] at this
      have := (mem_normalizer_iff.1 (inv_mem hnA) _).1 h2
      rwa [inv_inv] at this
  have hnsec : n ∈ sectionCentralizer (zpowers h.t ⊔ d.A) d.A :=
    (mem_sectionCentralizer_zpowers_sup_iff htA).2 ⟨hnA, hnt⟩
  rw [d.miyamoto_1_3_A.2] at hnsec
  have hnsec' : n ∈ ((d.A ⊔ (normalizer (d.A : Set G) ⊓ centralizer ({h.t} : Set G)) :
      Subgroup G) : Set G) := hnsec
  rw [coe_mul_of_right_le_normalizer_left d.A _ inf_le_left, Set.mem_mul] at hnsec'
  obtain ⟨a, ha, c, hc, hac⟩ := hnsec'
  have hcB : c ∈ B := by
    have e : c = a⁻¹ * n := by rw [← hac]; group
    rw [e]
    exact mul_mem (inv_mem (hAB ha)) hnB
  have hcR : c ∈ h.R :=
    d.mem_R_of_mem_D_of_commute (hBD hcB) (mem_centralizer_singleton_iff.1 hc.2)
  exact hnH (mem_sup_left (hac ▸ mul_mem ha (d.R_le_A hcR)))

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4
