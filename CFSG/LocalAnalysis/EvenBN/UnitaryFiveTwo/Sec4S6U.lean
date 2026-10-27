module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6T
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6S
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6SplitG
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6PGrp
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S3E

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

section Basic



variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

include h hKU in
theorem Data.v_eq_w₁_mul :
    d.v = ((Data.w₁ h hKU hf : ↥K₀) : G) * (d.t * ((Data.w₁ h hKU hf : ↥K₀) : G) * d.t) := by
  rw [← Data.theta_apply h hf, Data.theta_w₁ h hKU hf]

include h hKU in
theorem Data.w₁_sq :
    ((Data.w₁ h hKU hf : ↥K₀) : G) * ((Data.w₁ h hKU hf : ↥K₀) : G) = 1 := by
  have hv : d.v * d.v = 1 := by
    show d.ι vSU * d.ι vSU = 1
    rw [← map_mul]
    have : vSU * vSU = 1 := by
      have := mul_inv_cancel vSU
      rwa [vSU_inv] at this
    rw [this, map_one]
  have h1 : Data.theta h hf (Data.w₁ h hKU hf * Data.w₁ h hKU hf) = Data.theta h hf 1 := by
    rw [map_mul, Data.theta_w₁ h hKU hf, map_one, hv]
  have := Data.theta_injective h hf h1
  exact congrArg Subtype.val this

include h hKU in
theorem Data.v_inv_conj_K₀ {u : G} (hu : u ∈ K₀) :
    d.v⁻¹ * u * d.v =
      ((Data.w₁ h hKU hf : ↥K₀) : G) * u * ((Data.w₁ h hKU hf : ↥K₀) : G)⁻¹ := by
  have hv := Data.v_eq_w₁_mul h hKU hf
  have hsq := Data.w₁_sq h hKU hf
  have hw₁0 : ((Data.w₁ h hKU hf : ↥K₀) : G) ∈ K₀ := (Data.w₁ h hKU hf).2
  generalize ((Data.w₁ h hKU hf : ↥K₀) : G) = w₁ at hv hsq hw₁0 ⊢
  have hw₂ : d.t * w₁ * d.t ∈ d.tc K₀ := (h.mem_tc).2 (by rw [h.t_conj_conj]; exact hw₁0)
  have hX : w₁ * u * w₁⁻¹ ∈ K₀ := K₀.mul_mem (K₀.mul_mem hw₁0 hu) (K₀.inv_mem hw₁0)
  have hc : (d.t * w₁ * d.t) * (w₁ * u * w₁⁻¹) = (w₁ * u * w₁⁻¹) * (d.t * w₁ * d.t) :=
    (hf.comm_elem _ hX _ hw₂).symm
  have hinv : w₁⁻¹ = w₁ := inv_eq_of_mul_eq_one_right hsq
  rw [hv]
  calc (w₁ * (d.t * w₁ * d.t))⁻¹ * u * (w₁ * (d.t * w₁ * d.t))
      = (d.t * w₁ * d.t)⁻¹ * (w₁⁻¹ * u * w₁) * (d.t * w₁ * d.t) := by group
    _ = (d.t * w₁ * d.t)⁻¹ * (w₁ * u * w₁⁻¹) * (d.t * w₁ * d.t) := by rw [hinv]
    _ = (d.t * w₁ * d.t)⁻¹ * ((w₁ * u * w₁⁻¹) * (d.t * w₁ * d.t)) := by group
    _ = (d.t * w₁ * d.t)⁻¹ * ((d.t * w₁ * d.t) * (w₁ * u * w₁⁻¹)) := by rw [hc]
    _ = w₁ * u * w₁⁻¹ := by group

include h hKU in
theorem Data.v_inv_conj_tc {u : G} (hu : u ∈ d.tc K₀) :
    d.v⁻¹ * u * d.v =
      (d.t * ((Data.w₁ h hKU hf : ↥K₀) : G) * d.t) * u *
        (d.t * ((Data.w₁ h hKU hf : ↥K₀) : G) * d.t)⁻¹ := by
  have hv := Data.v_eq_w₁_mul h hKU hf
  have hsq := Data.w₁_sq h hKU hf
  have hw₁0 : ((Data.w₁ h hKU hf : ↥K₀) : G) ∈ K₀ := (Data.w₁ h hKU hf).2
  generalize ((Data.w₁ h hKU hf : ↥K₀) : G) = w₁ at hv hsq hw₁0 ⊢
  have hw₂sq : (d.t * w₁ * d.t) * (d.t * w₁ * d.t) = 1 := by
    calc (d.t * w₁ * d.t) * (d.t * w₁ * d.t) = d.t * (w₁ * (d.t * d.t) * w₁) * d.t := by group
      _ = 1 := by rw [h.t_mul_t, mul_one, hsq, mul_one, h.t_mul_t]
  have hinv₂ : (d.t * w₁ * d.t)⁻¹ = d.t * w₁ * d.t := inv_eq_of_mul_eq_one_right hw₂sq
  have hc : w₁ * u = u * w₁ := hf.comm_elem w₁ hw₁0 u hu
  rw [hv]
  calc (w₁ * (d.t * w₁ * d.t))⁻¹ * u * (w₁ * (d.t * w₁ * d.t))
      = (d.t * w₁ * d.t)⁻¹ * (w₁⁻¹ * u * w₁) * (d.t * w₁ * d.t) := by group
    _ = (d.t * w₁ * d.t)⁻¹ * u * (d.t * w₁ * d.t) := by
      rw [show w₁⁻¹ * u * w₁ = u by rw [mul_assoc, ← hc]; group]
    _ = (d.t * w₁ * d.t) * u * (d.t * w₁ * d.t)⁻¹ := by rw [hinv₂]

end Basic

instance Data.normal_Y_D₂ (d : Data G) : (d.Y.subgroupOf d.D₂).Normal :=
  ⟨fun n hn g => by
    have hn' : (n : G) ∈ d.Y := hn
    have e : (g : G) * (n : G) * (g : G)⁻¹ = n := by
      rw [← (Data.Hyp.mem_D₂_iff.1 g.2).2 _ hn']
      group
    exact Subgroup.mem_subgroupOf.2 (by
      show (g : G) * (n : G) * (g : G)⁻¹ ∈ d.Y
      rw [e]
      exact hn')⟩

section Main


variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

include h hKU in
theorem Data.Hyp.hfix : ∀ x ∈ d.D₂, (∀ g ∈ Data.Lam₁ h hKU hf, g * x * g⁻¹ * x⁻¹ ∈ d.Y) →
    (∀ g ∈ d.tc (Data.Lam₁ h hKU hf), g * x * g⁻¹ * x⁻¹ ∈ d.Y) → x ∈ d.Y := by
  intro x hx h₁ h₂
  refine h.fixed_D₂_Y hx (fun k hk => ?_)
  have hk3 : k ∈ d.K₃ := Data.K₂_le_K₃ hk
  obtain ⟨g', hg'⟩ := Data.exists_theta_eq h hKU hf hk3
  have hgΛ : (g' : G) ∈ Data.Lam₁ h hKU hf :=
    (Data.theta_mem_K₂_iff h hKU hf g').2 (by rw [hg']; exact hk)
  have hk' : k = (g' : G) * (d.t * (g' : G) * d.t) := by rw [← hg', Data.theta_apply]
  generalize (g' : G) = g at hgΛ hk'
  have hg2 : d.t * g * d.t ∈ d.tc (Data.Lam₁ h hKU hf) :=
    (h.mem_tc).2 (by rw [h.t_conj_conj]; exact hgΛ)
  have c₁ := h₁ g hgΛ
  have c₂ := h₂ _ hg2
  have e : x⁻¹ * (k * x * k⁻¹) =
      x⁻¹ * ((g * ((d.t * g * d.t) * x * (d.t * g * d.t)⁻¹ * x⁻¹) * g⁻¹) *
        (g * x * g⁻¹ * x⁻¹)) * x := by
    rw [hk']
    group
  rw [e]
  have y₁ : g * ((d.t * g * d.t) * x * (d.t * g * d.t)⁻¹ * x⁻¹) * g⁻¹ ∈ d.Y :=
    h.Lam₁_conj_mem_Y hKU hf hgΛ c₂
  have hz := d.Y.mul_mem y₁ c₁
  have hcomm := Data.Hyp.D₂_comm_Y' hx hz
  rw [mul_assoc, ← hcomm]
  simpa using hz

include h hKU in
theorem Data.Hyp.V₃_cen_MY : ∀ x ∈ d.V₃, ∀ q ∈ d.M ⊔ d.Y, q * x * q⁻¹ * x⁻¹ ∈ d.Y := by
  have hK := h.comm_M_V₂_mem_W hKU
  have hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G) := fun m hm => h.M_le_normalizer_Y hKU hm
  have step1 : ∀ m ∈ d.M, d.V₃ ≤ centModSub d.Y m := by
    intro m hm
    rw [h.V₃_eq hK]
    refine sup_le (fun x hx => ?_) (fun y hy => ?_)
    · obtain ⟨hx3, hx2⟩ := Subgroup.mem_inf.1 hx
      have hx1 : x ∈ d.D₁ ⊓ d.D₂ := by rwa [← h.D₃_inf_D₂_eq]
      have hxN : x ∈ normalizer (d.Y : Set G) := mem_normalizer_fintype fun y hy => by
        have e : x * y = y * x := (Data.Hyp.D₂_comm_Y' hx2 hy).symm.symm
        rw [e, mul_inv_cancel_right]
        exact hy
      refine ⟨hxN, d.W_le_Y ?_⟩
      exact h.D₁_commutator_mem_W hK (Subgroup.mem_inf.1 hx1).1 (Subgroup.mem_inf.1 hm).1
    · refine ⟨d.Y.le_normalizer hy, ?_⟩
      have := (mem_normalizer_iff.1 (hKY m hm) y⁻¹).1 (inv_mem hy)
      rw [show y * m * y⁻¹ * m⁻¹ = y * (m * y⁻¹ * m⁻¹) by group]
      exact d.Y.mul_mem hy this
  have hMc : d.M ≤ cenMod d.Y d.V₃ := fun m hm => by
    refine ⟨hKY m hm, fun x hx => ?_⟩
    have := (step1 m hm hx).2
    have hinv := d.Y.inv_mem this
    rwa [show (x * m * x⁻¹ * m⁻¹)⁻¹ = m * x * m⁻¹ * x⁻¹ by group] at hinv
  have hYc : d.Y ≤ cenMod d.Y d.V₃ := fun y hy => by
    refine ⟨d.Y.le_normalizer hy, fun x hx => ?_⟩
    have hx2 : x ∈ d.D₂ := h.V₃_le_D₂ hK hx
    have e : x * y = y * x := (Data.Hyp.D₂_comm_Y' hx2 hy).symm.symm
    rw [show y * x * y⁻¹ * x⁻¹ = y * (x * y⁻¹ * x⁻¹) by group]
    have e' : x * y⁻¹ = y⁻¹ * x := (Data.Hyp.D₂_comm_Y' hx2 (inv_mem hy)).symm.symm
    rw [e']
    simpa using d.Y.one_mem
  have hMYc : d.M ⊔ d.Y ≤ cenMod d.Y d.V₃ := sup_le hMc hYc
  intro x hx q hq
  exact (hMYc hq).2 x hx

section Norm

variable (hD : d.D₁ ≤ normalizer (d.D₂ : Set G))

include h hKU hD in
theorem Data.Hyp.MY_le_normDY : d.M ⊔ d.Y ≤ ModSplit.normDY d.D₂ d.Y := by
  refine sup_le (fun m hm => ?_) (fun y hy => ?_)
  · exact Subgroup.mem_inf.2 ⟨hD (Subgroup.mem_inf.1 hm).1, h.M_le_normalizer_Y hKU hm⟩
  · exact Subgroup.mem_inf.2 ⟨d.D₂.le_normalizer (h.Y_le_D₂ hy), d.Y.le_normalizer hy⟩

include h hKU hD in
theorem Data.Hyp.U₁_le_normDY : Data.U₁ h hf ≤ ModSplit.normDY d.D₂ d.Y :=
  (h.U₁_le_M_sup_Y hKU hf).trans (h.MY_le_normDY hKU hD)

include h hKU hD in
theorem Data.Hyp.tcU₁_le_normDY : d.tc (Data.U₁ h hf) ≤ ModSplit.normDY d.D₂ d.Y :=
  (h.tcU₁_le_M_sup_Y hKU hf).trans (h.MY_le_normDY hKU hD)

include h in
theorem Data.Hyp.v_mem_normalizer_D₂ : d.v ∈ normalizer (d.D₂ : Set G) :=
  mem_normalizer_fintype fun y hy => h.conj_mem_D₂ h.v_mem_XC₀ hy

include h in
theorem Data.Hyp.t_mem_normalizer_D₂ : d.t ∈ normalizer (d.D₂ : Set G) :=
  mem_normalizer_fintype fun y hy => h.conj_mem_D₂ h.t_mem_XC₀ hy

include h hKU hD in
theorem Data.Hyp.Lam₁_le_normalizer_D₂ : Data.Lam₁ h hKU hf ≤ normalizer (d.D₂ : Set G) := by
  refine sup_le ((h.U₁_le_normDY hKU hf hD).trans inf_le_left) ?_
  rintro _ ⟨u, hu, rfl⟩
  have hu' : u ∈ normalizer (d.D₂ : Set G) := (h.U₁_le_normDY hKU hf hD hu).1
  have e := Data.v_inv_conj_K₀ h hKU hf (Data.U₁_le_K₀ h hf hu)
  show ((Data.w₁ h hKU hf : ↥K₀) : G) * u * ((Data.w₁ h hKU hf : ↥K₀) : G)⁻¹ ∈ _
  rw [← e]
  exact mul_mem (mul_mem (inv_mem h.v_mem_normalizer_D₂) hu') h.v_mem_normalizer_D₂

include h hKU hD in
theorem Data.Hyp.tcLam₁_le_normalizer_D₂ :
    d.tc (Data.Lam₁ h hKU hf) ≤ normalizer (d.D₂ : Set G) := by
  intro x hx
  have hx' : d.t * x * d.t ∈ normalizer (d.D₂ : Set G) :=
    h.Lam₁_le_normalizer_D₂ hKU hf hD ((h.mem_tc).1 hx)
  rw [← h.t_conj_conj x]
  exact mul_mem (mul_mem h.t_mem_normalizer_D₂ hx') h.t_mem_normalizer_D₂

end Norm

section Split

variable (hD : d.D₁ ≤ normalizer (d.D₂ : Set G))

include h in
theorem Data.Hyp.t_conj_mul' (x y : G) : (d.t * x * d.t) * (d.t * y * d.t) = d.t * (x * y) * d.t := by
  calc (d.t * x * d.t) * (d.t * y * d.t) = d.t * x * (d.t * d.t) * y * d.t := by group
    _ = d.t * (x * y) * d.t := by rw [h.t_mul_t]; group

include h in
theorem Data.Hyp.t_conj_inv' (x : G) : (d.t * x * d.t)⁻¹ = d.t * x⁻¹ * d.t := by
  rw [mul_inv_rev, mul_inv_rev, h.t_inv]
  group

include h hKU hD in
theorem Data.Hyp.liftFixG_U_eq_V₃ :
    ModSplit.liftFixG d.D₂ d.Y (Data.U₁ h hf ⊔ d.tc (Data.U₁ h hf)) = d.V₃ := by
  have hK := h.comm_M_V₂_mem_W hKU
  set S : Subgroup G := Data.U₁ h hf ⊔ d.tc (Data.U₁ h hf) with hSdef
  have hS : S ≤ ModSplit.normDY d.D₂ d.Y :=
    sup_le (h.U₁_le_normDY hKU hf hD) (h.tcU₁_le_normDY hKU hf hD)
  have hSMY : S ≤ d.M ⊔ d.Y := sup_le (h.U₁_le_M_sup_Y hKU hf) (h.tcU₁_le_M_sup_Y hKU hf)
  have hge : d.V₃ ≤ ModSplit.liftFixG d.D₂ d.Y S := fun x hx => by
    rw [ModSplit.mem_liftFixG_iff _ _ hS]
    exact ⟨h.V₃_le_D₂ hK hx, fun g hg => h.V₃_cen_MY hKU x hx g (hSMY hg)⟩
  refine le_antisymm (fun x hx => ?_) hge
  have hxmem := (ModSplit.mem_liftFixG_iff _ _ hS).1 hx
  have hxD := hxmem.1
  have hN : d.V₃.map (MulAut.conj d.v).toMonoidHom ≤ normalizer (d.V₃ : Set G) :=
    (h.conj_V₃_le_D₂ hK).trans h.D₂_le_normalizer_V₃
  have hxsup : x ∈ d.V₃.map (MulAut.conj d.v).toMonoidHom ⊔ d.V₃ := by
    rw [sup_comm, ← h.D₂_eq_V₃_sup hK]
    exact hxD
  obtain ⟨b, hb, a, ha, hxba⟩ := PGrp.exists_mul_of_mem_sup_of_le_normalizer hN hxsup
  have hbL : b ∈ ModSplit.liftFixG d.D₂ d.Y S := by
    have : b = x * a⁻¹ := by rw [hxba]; group
    rw [this]
    exact (ModSplit.liftFixG d.D₂ d.Y S).mul_mem hx
      ((ModSplit.liftFixG d.D₂ d.Y S).inv_mem (hge ha))
  have hbfix := ((ModSplit.mem_liftFixG_iff _ _ hS).1 hbL).2
  have hb₀ : d.v⁻¹ * b * d.v ∈ d.V₃ := (mem_map_conj_iff _ _ _).1 hb
  obtain ⟨b₀, hb₀def⟩ : ∃ b₀ : G, b₀ = d.v⁻¹ * b * d.v := ⟨_, rfl⟩
  rw [← hb₀def] at hb₀
  have hvY : d.v ∈ normalizer (d.Y : Set G) := h.NHA₂_le_normalizer_Y h.v_mem_NHA₂
  have hCbS : S ≤ centModSub d.Y b₀ := fun g hg =>
    ⟨(hS hg).2, h.V₃_cen_MY hKU b₀ hb₀ g (hSMY hg)⟩
  have hCbSv : S.map (MulAut.conj d.v⁻¹).toMonoidHom ≤ centModSub d.Y b₀ := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨?_, ?_⟩
    · show d.v⁻¹ * s * d.v⁻¹⁻¹ ∈ normalizer (d.Y : Set G)
      exact mul_mem (mul_mem (inv_mem hvY) (hS hs).2) (inv_mem (inv_mem hvY))
    · show (d.v⁻¹ * s * d.v⁻¹⁻¹) * b₀ * (d.v⁻¹ * s * d.v⁻¹⁻¹)⁻¹ * b₀⁻¹ ∈ d.Y
      have e : (d.v⁻¹ * s * d.v⁻¹⁻¹) * b₀ * (d.v⁻¹ * s * d.v⁻¹⁻¹)⁻¹ * b₀⁻¹ =
          d.v⁻¹ * (s * b * s⁻¹ * b⁻¹) * d.v⁻¹⁻¹ := by
        rw [hb₀def]
        group
      rw [e]
      exact (mem_normalizer_iff.1 (inv_mem hvY) _).1 (hbfix s hs)
  have hΛ₁ : Data.Lam₁ h hKU hf ≤ centModSub d.Y b₀ := by
    refine sup_le (le_sup_left.trans hCbS) ?_
    rintro _ ⟨u, hu, rfl⟩
    have hu0 : u ∈ K₀ := Data.U₁_le_K₀ h hf hu
    have e := Data.v_inv_conj_K₀ h hKU hf hu0
    apply hCbSv
    refine ⟨u, mem_sup_left hu, ?_⟩
    show d.v⁻¹ * u * d.v⁻¹⁻¹ = ((Data.w₁ h hKU hf : ↥K₀) : G) * u *
      ((Data.w₁ h hKU hf : ↥K₀) : G)⁻¹
    rw [inv_inv]
    exact e
  have hΛ₂ : d.tc (Data.Lam₁ h hKU hf) ≤ centModSub d.Y b₀ := by
    rw [Data.Lam₁, h.tc_sup]
    refine sup_le (le_sup_right.trans hCbS) ?_
    intro y hy
    obtain ⟨u, hu, e⟩ := Subgroup.mem_map.1 ((h.mem_tc).1 hy)
    have hu0 : u ∈ K₀ := Data.U₁_le_K₀ h hf hu
    have hu' : d.t * u * d.t ∈ d.tc (Data.U₁ h hf) :=
      (h.mem_tc).2 (by rw [h.t_conj_conj]; exact hu)
    have hu'tc : d.t * u * d.t ∈ d.tc K₀ := (h.mem_tc).2 (by rw [h.t_conj_conj]; exact hu0)
    have hv := Data.v_inv_conj_tc h hKU hf hu'tc
    apply hCbSv
    refine ⟨d.t * u * d.t, mem_sup_right hu', ?_⟩
    show d.v⁻¹ * (d.t * u * d.t) * d.v⁻¹⁻¹ = y
    rw [inv_inv, hv]
    have e' : ((Data.w₁ h hKU hf : ↥K₀) : G) * u * ((Data.w₁ h hKU hf : ↥K₀) : G)⁻¹ =
        d.t * y * d.t := e
    calc (d.t * ((Data.w₁ h hKU hf : ↥K₀) : G) * d.t) * (d.t * u * d.t) *
          (d.t * ((Data.w₁ h hKU hf : ↥K₀) : G) * d.t)⁻¹
        = d.t * (((Data.w₁ h hKU hf : ↥K₀) : G) * u * ((Data.w₁ h hKU hf : ↥K₀) : G)⁻¹) * d.t := by
          rw [h.t_conj_inv', h.t_conj_mul', h.t_conj_mul']
      _ = y := by rw [e', h.t_conj_conj]
  have hb₀Y : b₀ ∈ d.Y := h.hfix hKU hf b₀ (h.V₃_le_D₂ hK hb₀) (fun g hg => (hΛ₁ hg).2)
    (fun g hg => (hΛ₂ hg).2)
  have hbY : b ∈ d.Y := by
    have : b = d.v * b₀ * d.v⁻¹ := by rw [hb₀def]; group
    rw [this]
    exact (mem_normalizer_iff.1 hvY b₀).1 hb₀Y
  rw [hxba]
  exact d.V₃.mul_mem (h.Y_le_V₃ hbY) ha

include h hKU hD in
theorem Data.Hyp.splitting_D₂ :
    Nat.card (ModSplit.liftFixG d.D₂ d.Y (Data.Lam₁ h hKU hf)) = 2 ^ 12 ∧
      Nat.card (ModSplit.liftFixG d.D₂ d.Y (d.tc (Data.Lam₁ h hKU hf))) = 2 ^ 12 ∧
      ModSplit.liftFixG d.D₂ d.Y (Data.Lam₁ h hKU hf) ⊔
        ModSplit.liftFixG d.D₂ d.Y (d.tc (Data.Lam₁ h hKU hf)) = d.D₂ ∧
      ModSplit.liftFixG d.D₂ d.Y (Data.Lam₁ h hKU hf) ⊓
        ModSplit.liftFixG d.D₂ d.Y (d.tc (Data.Lam₁ h hKU hf)) = d.Y := by
  have hK := h.comm_M_V₂_mem_W hKU
  have hw₁0 : ((Data.w₁ h hKU hf : ↥K₀) : G) ∈ K₀ := (Data.w₁ h hKU hf).2
  have htY : d.t ∈ normalizer (d.Y : Set G) := mem_normalizer_fintype fun y hy => by
    have := h.t_conj_mem_Y hy
    rw [h.t_inv]
    exact this
  have hΓ₁ : Data.Lam₁ h hKU hf ≤ ModSplit.normDY d.D₂ d.Y :=
    le_inf (h.Lam₁_le_normalizer_D₂ hKU hf hD) (h.Lam₁_le_normalizer_Y hKU hf)
  have hΓ₂ : d.tc (Data.Lam₁ h hKU hf) ≤ ModSplit.normDY d.D₂ d.Y :=
    le_inf (h.tcLam₁_le_normalizer_D₂ hKU hf hD) (h.tcLam₁_le_normalizer_Y hKU hf)
  have hp₁ : IsPGroup 2 ↥(Data.U₁ h hf) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hX₂ : IsPGroup 2 ↥d.X₂ := IsPGroup.of_card (n := 2) (by rw [Data.Hyp.card_X₂ (d := d)]; norm_num)
    exact (hX₂.comap_of_injective (Data.theta h hf) (Data.theta_injective h hf)).map K₀.subtype
  have hp₂ : IsPGroup 2 ↥(d.tc (Data.U₁ h hf)) := hp₁.map (MulAut.conj d.t).toMonoidHom
  have e₂ : ↥(d.tc (Data.Lam₁ h hKU hf)) ≃* Matrix.SpecialLinearGroup (Fin 2) CFSG.Fischer.F4 :=
    (Subgroup.equivMapOfInjective (Data.Lam₁ h hKU hf) (MulAut.conj d.t).toMonoidHom
      (MulAut.conj d.t).injective).symm.trans (Data.lamEquiv h hKU hf)
  have hLU : ModSplit.liftFixG d.D₂ d.Y (Data.U₁ h hf ⊔ d.tc (Data.U₁ h hf)) = d.V₃ :=
    h.liftFixG_U_eq_V₃ hKU hf hD
  refine ModSplit.splittingG d.D₂ d.Y h.Y_le_D₂ (fun x hx y hy => h.D₂_commutator_mem_Y hK hx hy)
    h.card_D₂ h.card_Y (k := CFSG.Fischer.F4) (by rw [Nat.card_eq_fintype_card, CFSG.Fischer.F4.card])
    d.t ⟨h.t_mem_normalizer_D₂, htY⟩ h.t_mul_t
    (Data.Lam₁ h hKU hf) (d.tc (Data.Lam₁ h hKU hf)) (Data.U₁ h hf) (d.tc (Data.U₁ h hf))
    ((Data.w₁ h hKU hf : ↥K₀) : G) (d.t * ((Data.w₁ h hKU hf : ↥K₀) : G) * d.t)
    hΓ₁ hΓ₂ e₂ (Data.lamEquiv h hKU hf) rfl
    (fun a ha b hb => hf.comm_elem a (Data.Lam₁_le_K₀ h hKU hf ha) b
      (h.tc_mono (Data.Lam₁_le_K₀ h hKU hf) hb))
    le_sup_left (h.tc_mono le_sup_left) (Data.w₁_mem_Lam₁ h hKU hf)
    ((h.mem_tc).2 (by rw [h.t_conj_conj]; exact Data.w₁_mem_Lam₁ h hKU hf))
    hp₁ hp₂ le_rfl ?_ (h.hfix hKU hf) ?_ ?_
  ·
    rw [Data.Lam₁, h.tc_sup]
    refine sup_le le_sup_left ?_
    intro y hy
    obtain ⟨u, hu, e⟩ := Subgroup.mem_map.1 ((h.mem_tc).1 hy)
    have hu' : d.t * u * d.t ∈ d.tc (Data.U₁ h hf) :=
      (h.mem_tc).2 (by rw [h.t_conj_conj]; exact hu)
    refine mem_sup_right ⟨d.t * u * d.t, hu', ?_⟩
    show (d.t * ((Data.w₁ h hKU hf : ↥K₀) : G) * d.t) * (d.t * u * d.t) *
      (d.t * ((Data.w₁ h hKU hf : ↥K₀) : G) * d.t)⁻¹ = y
    have e' : ((Data.w₁ h hKU hf : ↥K₀) : G) * u * ((Data.w₁ h hKU hf : ↥K₀) : G)⁻¹ =
        d.t * y * d.t := e
    calc (d.t * ((Data.w₁ h hKU hf : ↥K₀) : G) * d.t) * (d.t * u * d.t) *
          (d.t * ((Data.w₁ h hKU hf : ↥K₀) : G) * d.t)⁻¹
        = d.t * (((Data.w₁ h hKU hf : ↥K₀) : G) * u * ((Data.w₁ h hKU hf : ↥K₀) : G)⁻¹) * d.t := by
          rw [h.t_conj_inv', h.t_conj_mul', h.t_conj_mul']
      _ = y := by rw [e', h.t_conj_conj]
  · rw [hLU, h.card_V₃ hK]
  · rw [hLU, ← Data.v_eq_w₁_mul h hKU hf]
    exact h.V₃_inf_conj_V₃ hK

end Split

end Main

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
