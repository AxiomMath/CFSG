module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7NR
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7Lev
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6KProd

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

@[expose] def Data.tc (d : Data G) (X : Subgroup G) : Subgroup G :=
  X.map (MulAut.conj d.t).toMonoidHom

theorem Data.Hyp.mem_tc (h : d.Hyp) {X : Subgroup G} {x : G} :
    x ∈ d.tc X ↔ d.t * x * d.t ∈ X := by
  have htt := h.t_mul_t
  have hti := h.t_inv
  constructor
  · rintro ⟨a, ha, rfl⟩
    show d.t * (d.t * a * d.t⁻¹) * d.t ∈ X
    rw [hti]
    have : d.t * (d.t * a * d.t) * d.t = a := by
      calc d.t * (d.t * a * d.t) * d.t = (d.t * d.t) * a * (d.t * d.t) := by group
        _ = a := by rw [htt]; group
    rw [this]
    exact ha
  · intro hx
    refine ⟨d.t * x * d.t, hx, ?_⟩
    show d.t * (d.t * x * d.t) * d.t⁻¹ = x
    rw [hti]
    calc d.t * (d.t * x * d.t) * d.t = (d.t * d.t) * x * (d.t * d.t) := by group
      _ = x := by rw [htt]; group

theorem Data.Hyp.tc_tc (h : d.Hyp) (X : Subgroup G) : d.tc (d.tc X) = X := by
  ext x
  rw [h.mem_tc, h.mem_tc]
  have htt := h.t_mul_t
  have : d.t * (d.t * x * d.t) * d.t = x := by
    calc d.t * (d.t * x * d.t) * d.t = (d.t * d.t) * x * (d.t * d.t) := by group
      _ = x := by rw [htt]; group
  rw [this]

theorem Data.card_tc (d : Data G) (X : Subgroup G) : Nat.card (d.tc X) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj d.t).injective

theorem Data.Hyp.tc_mono (h : d.Hyp) {X Y : Subgroup G} (hXY : X ≤ Y) : d.tc X ≤ d.tc Y := by
  intro x hx
  rw [h.mem_tc] at hx ⊢
  exact hXY hx

theorem Data.Hyp.tc_inf (h : d.Hyp) (X Y : Subgroup G) : d.tc (X ⊓ Y) = d.tc X ⊓ d.tc Y :=
  Subgroup.map_inf X Y _ (MulAut.conj d.t).injective

theorem Data.Hyp.tc_sup (h : d.Hyp) (X Y : Subgroup G) : d.tc (X ⊔ Y) = d.tc X ⊔ d.tc Y :=
  Subgroup.map_sup X Y _

theorem Data.IsUnitaryFactor.comm_elem (hf : d.IsUnitaryFactor K₀) :
    ∀ a ∈ K₀, ∀ b ∈ d.tc K₀, a * b = b * a := fun a ha b hb =>
  (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hf.comm ha) b hb).symm

theorem Data.IsUnitaryFactor.inf_tc (hf : d.IsUnitaryFactor K₀) : K₀ ⊓ d.tc K₀ = ⊥ := hf.inf

theorem Data.IsUnitaryFactor.K_eq_tc (hf : d.IsUnitaryFactor K₀) : d.K = K₀ ⊔ d.tc K₀ := hf.K_eq

theorem Data.IsUnitaryFactor.le_K (hf : d.IsUnitaryFactor K₀) : K₀ ≤ d.K := by
  rw [hf.K_eq]; exact le_sup_left

theorem Data.IsUnitaryFactor.tc_le_K (hf : d.IsUnitaryFactor K₀) : d.tc K₀ ≤ d.K := by
  rw [hf.K_eq]; exact le_sup_right

theorem Data.IsUnitaryFactor.comm_inv0 (h : d.Hyp) (hf : d.IsUnitaryFactor K₀) :
    ⁅K₀, K₀.map (MulAut.conj d.t⁻¹).toMonoidHom⁆ = ⊥ := by
  rw [h.t_inv]
  exact hf.comm

@[expose] noncomputable def Data.theta (h : d.Hyp) (hf : d.IsUnitaryFactor K₀) : ↥K₀ →* G :=
  Common.diagonalHom K₀ d.t (hf.comm_inv0 h)

theorem Data.theta_apply (h : d.Hyp) (hf : d.IsUnitaryFactor K₀) (k : ↥K₀) :
    Data.theta h hf k = (k : G) * (d.t * (k : G) * d.t) := by
  rw [Data.theta, Common.diagonalHom_apply_of_mul_self (hf.comm_inv0 h) h.t_mul_t]

theorem Data.IsUnitaryFactor.unique (hf : d.IsUnitaryFactor K₀) {a a' b b' : G} (ha : a ∈ K₀)
    (ha' : a' ∈ K₀) (hb : b ∈ d.tc K₀) (hb' : b' ∈ d.tc K₀) (e : a * b = a' * b') :
    a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [e]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ K₀ ⊓ d.tc K₀ :=
    ⟨K₀.mul_mem (K₀.inv_mem ha') ha, h1 ▸ (d.tc K₀).mul_mem hb' ((d.tc K₀).inv_mem hb)⟩
  rw [hf.inf_tc, Subgroup.mem_bot] at h2
  have h3 : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  refine ⟨h3, ?_⟩
  rw [h3] at e
  exact mul_left_cancel e

theorem Data.theta_injective (h : d.Hyp) (hf : d.IsUnitaryFactor K₀) :
    Function.Injective (Data.theta h hf) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have h1 := (Common.diagonalHom_eq_one_iff (hf.comm_inv0 h) k).1 hk
  rw [h.t_inv] at h1
  have hk' : (k : G) ∈ d.tc K₀ := (h.mem_tc).2 (by rw [h1]; exact inv_mem k.2)
  have hk0 : (k : G) ∈ K₀ ⊓ d.tc K₀ := ⟨k.2, hk'⟩
  rw [hf.inf_tc, Subgroup.mem_bot] at hk0
  exact Subtype.ext hk0

theorem Data.Hyp.t_conj_conj (h : d.Hyp) (x : G) : d.t * (d.t * x * d.t) * d.t = x := by
  have htt := h.t_mul_t
  calc d.t * (d.t * x * d.t) * d.t = (d.t * d.t) * x * (d.t * d.t) := by group
    _ = x := by rw [htt]; group

theorem Data.theta_mem_K₃ (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)
    (k : ↥K₀) : Data.theta h hf k ∈ d.K₃ := by
  rw [← hKU.centralizer_eq]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Data.theta_apply]
    refine mul_mem (hf.le_K k.2) (hf.tc_le_K ?_)
    rw [h.mem_tc, h.t_conj_conj]
    exact k.2
  · exact Common.range_diagonalHom_le (hf.comm_inv0 h) h.t_mul_t ⟨k, rfl⟩

theorem Data.theta_mem_L (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)
    (k : ↥K₀) : Data.theta h hf k ∈ d.L :=
  d.pull_le_L K₃sub (Data.theta_mem_K₃ h hKU hf k)

theorem Data.exists_theta_eq (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)
    {x : G} (hx : x ∈ d.K₃) : ∃ k : ↥K₀, Data.theta h hf k = x := by
  have hxKH : x ∈ d.K ⊓ d.H := by rw [hKU.centralizer_eq]; exact hx
  obtain ⟨hxK, hxH⟩ := Subgroup.mem_inf.1 hxKH
  have hxK' : x ∈ K₀ ⊔ d.tc K₀ := by rw [← hf.K_eq_tc]; exact hxK
  set X : ↥(K₀ ⊔ d.tc K₀) := ⟨x, hxK'⟩
  set a := KProd.projA K₀ (d.tc K₀) hf.comm_elem hf.inf_tc X
  set b := KProd.projB K₀ (d.tc K₀) hf.comm_elem hf.inf_tc X
  have hxab : x = (a : G) * (b : G) :=
    KProd.exists_eq_mul K₀ (d.tc K₀) hf.comm_elem hf.inf_tc X
  have hb' : d.t * (b : G) * d.t ∈ K₀ := (h.mem_tc).1 b.2
  have ha' : d.t * (a : G) * d.t ∈ d.tc K₀ := (h.mem_tc).2 (by rw [h.t_conj_conj]; exact a.2)
  have hxt : d.t * x * d.t = x := by
    have : d.t * x = x * d.t := (mem_centralizer_singleton_iff.1 hxH).symm
    rw [this, mul_assoc, h.t_mul_t, mul_one]
  have htt := h.t_mul_t
  have hx2 : x = (d.t * (b : G) * d.t) * (d.t * (a : G) * d.t) := by
    have hcomm := hf.comm_elem _ hb' _ ha'
    rw [hcomm]
    have e : (d.t * (a : G) * d.t) * (d.t * (b : G) * d.t) = d.t * ((a : G) * b) * d.t := by
      calc (d.t * (a : G) * d.t) * (d.t * (b : G) * d.t)
          = d.t * a * (d.t * d.t) * b * d.t := by group
        _ = d.t * ((a : G) * b) * d.t := by rw [htt]; group
    rw [e, ← hxab, hxt]
  obtain ⟨e1, e2⟩ := hf.unique a.2 hb' b.2 ha' (hxab.symm.trans hx2)
  refine ⟨a, ?_⟩
  rw [Data.theta_apply]
  calc (a : G) * (d.t * (a : G) * d.t) = (a : G) * (b : G) := by rw [← e2]
    _ = x := hxab.symm

theorem Data.card_le_of_elemAb_L (d : Data G) {E : Subgroup G} (hEL : E ≤ d.L)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 16 := by
  set E' : Subgroup SU52 := E.comap d.ι with hE'
  have hmap : E'.map d.ι = E := Subgroup.map_comap_eq_self (d.range_ι ▸ hEL)
  have hcard : Nat.card E = Nat.card E' :=
    calc Nat.card E = Nat.card (E'.map d.ι) := by rw [hmap]
      _ = Nat.card E' := Subgroup.card_map_of_injective d.ι_injective
  have hc' : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := fun x hx y hy => by
    apply d.ι_injective
    rw [map_mul, map_mul]
    exact hc _ hx _ hy
  have hs' : ∀ x ∈ E', x * x = 1 := fun x hx => by
    apply d.ι_injective
    rw [map_mul, map_one]
    exact hs _ hx
  rw [hcard]
  exact (card_le_of_elemAb_SU52 hc' hs').1

theorem Data.card_le_of_elemAb_K₀ (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)
    {E : Subgroup G} (hEK : E ≤ K₀) (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hs : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 16 := by
  set E' : Subgroup ↥K₀ := E.subgroupOf K₀ with hE'
  have hE'card : Nat.card E' = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  set E2 : Subgroup G := E'.map (Data.theta h hf) with hE2
  have hE2card : Nat.card E2 = Nat.card E' :=
    Subgroup.card_map_of_injective (Data.theta_injective h hf)
  have hE2L : E2 ≤ d.L := by
    rintro _ ⟨k, -, rfl⟩
    exact Data.theta_mem_L h hKU hf k
  have hE2c : ∀ x ∈ E2, ∀ y ∈ E2, x * y = y * x := by
    rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc _ (Subgroup.mem_subgroupOf.1 hk) _ (Subgroup.mem_subgroupOf.1 hl))
  have hE2s : ∀ x ∈ E2, x * x = 1 := by
    rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul]
    have : k * k = 1 := Subtype.ext (hs _ (Subgroup.mem_subgroupOf.1 hk))
    rw [this, map_one]
  have := d.card_le_of_elemAb_L hE2L hE2c hE2s
  omega

section YStructure

theorem Data.Hyp.card_Y (h : d.Hyp) : Nat.card d.Y = 2 ^ 8 := h.sec4_6.2.2.2.2.1

theorem Data.Hyp.tc_Y (h : d.Hyp) : d.tc d.Y = d.Y := by
  ext x
  rw [h.mem_tc]
  constructor
  · intro hx
    have := h.t_conj_mem_Y hx
    rwa [h.t_conj_conj] at this
  · intro hx
    exact h.t_conj_mem_Y hx

theorem Data.Hyp.K₃_le_K (hKU : d.KUnitary) : d.K₃ ≤ d.K := by
  rw [← hKU.centralizer_eq]
  exact inf_le_left

theorem Data.Hyp.Y_le_K' (h : d.Hyp) (hKU : d.KUnitary) : d.Y ≤ d.K :=
  h.Y_le_K (Data.Hyp.K₃_le_K hKU) (Data.Lev_le_zpowers_sup_K₃ d)

theorem Data.Hyp.card_Y_inf_tc_ge (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀) :
    16 ≤ Nat.card ↥(d.Y ⊓ d.tc K₀) := by
  have hY : d.Y ≤ K₀ ⊔ d.tc K₀ := by
    rw [← hf.K_eq_tc]; exact h.Y_le_K' hKU
  set φ : ↥d.Y →* ↥K₀ :=
    (KProd.projA K₀ (d.tc K₀) hf.comm_elem hf.inf_tc).comp (Subgroup.inclusion hY) with hφ
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [Nat.card_congr (show ↥d.Y ≃ ↥d.Y from Equiv.refl _), h.card_Y] at hcard
  have hrange : Nat.card φ.range ≤ 16 := by
    set E1 : Subgroup G := φ.range.map K₀.subtype with hE1
    have hE1card : Nat.card E1 = Nat.card φ.range :=
      Subgroup.card_map_of_injective K₀.subtype_injective
    have hE1K : E1 ≤ K₀ := by
      rintro _ ⟨a, -, rfl⟩
      exact a.2
    have hE1c : ∀ x ∈ E1, ∀ y ∈ E1, x * y = y * x := by
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩ _ ⟨_, ⟨b, rfl⟩, rfl⟩
      have hab : a * b = b * a := Subtype.ext (h.Y_comm a.2 b.2)
      have h2 := congrArg φ hab
      rw [map_mul, map_mul] at h2
      simpa using congrArg Subtype.val h2
    have hE1s : ∀ x ∈ E1, x * x = 1 := by
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      show ((φ a : ↥K₀) : G) * (φ a : ↥K₀) = 1
      rw [← Subgroup.coe_mul, ← map_mul]
      have : a * a = 1 := Subtype.ext (h.Y_sq a.2)
      rw [this, map_one]
      rfl
    rw [← hE1card]
    exact Data.card_le_of_elemAb_K₀ h hKU hf hE1K hE1c hE1s
  have hker : Nat.card φ.ker ≤ Nat.card ↥(d.Y ⊓ d.tc K₀) := by
    have hle : φ.ker.map d.Y.subtype ≤ d.Y ⊓ d.tc K₀ := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have := (KProd.projA_eq_one_iff K₀ (d.tc K₀) hf.comm_elem hf.inf_tc
        (Subgroup.inclusion hY y)).1 hy
      exact this
    calc Nat.card φ.ker = Nat.card (φ.ker.map d.Y.subtype) :=
          (Subgroup.card_map_of_injective d.Y.subtype_injective).symm
      _ ≤ Nat.card ↥(d.Y ⊓ d.tc K₀) := Subgroup.card_le_of_le hle
  nlinarith

theorem Data.Hyp.tc_I (h : d.Hyp) : d.tc (d.Y ⊓ K₀) = d.Y ⊓ d.tc K₀ := by
  rw [h.tc_inf, h.tc_Y]

theorem Data.Hyp.card_Y_inf_K₀ (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀) :
    Nat.card ↥(d.Y ⊓ K₀) = 16 := by
  have hge : 16 ≤ Nat.card ↥(d.Y ⊓ K₀) := by
    have := h.card_Y_inf_tc_ge hKU hf
    rw [← h.tc_I, Data.card_tc] at this
    exact this
  have hle : Nat.card ↥(d.Y ⊓ K₀) ≤ 16 :=
    Data.card_le_of_elemAb_K₀ h hKU hf inf_le_right
      (fun x hx y hy => h.Y_comm hx.1 hy.1) (fun x hx => h.Y_sq hx.1)
  omega

theorem Data.Hyp.I_comm (h : d.Hyp) (hf : d.IsUnitaryFactor K₀) :
    ∀ a ∈ d.Y ⊓ K₀, ∀ b ∈ d.tc (d.Y ⊓ K₀), a * b = b * a := by
  intro a ha b hb
  rw [h.tc_I] at hb
  exact hf.comm_elem a ha.2 b hb.2

theorem Data.Hyp.I_inf (h : d.Hyp) (hf : d.IsUnitaryFactor K₀) :
    (d.Y ⊓ K₀) ⊓ d.tc (d.Y ⊓ K₀) = ⊥ := by
  rw [eq_bot_iff, ← hf.inf_tc]
  refine inf_le_inf inf_le_right ?_
  rw [h.tc_I]
  exact inf_le_right

theorem Data.Hyp.Y_eq_I_sup (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀) :
    d.Y = (d.Y ⊓ K₀) ⊔ d.tc (d.Y ⊓ K₀) := by
  have hcomm := h.I_comm hf
  have hinf := h.I_inf hf
  have hle : (d.Y ⊓ K₀) ⊔ d.tc (d.Y ⊓ K₀) ≤ d.Y := by
    refine sup_le inf_le_left ?_
    rw [h.tc_I]
    exact inf_le_left
  have hcard : Nat.card ↥((d.Y ⊓ K₀) ⊔ d.tc (d.Y ⊓ K₀)) = 2 ^ 8 := by
    rw [← Nat.card_congr (KProd.prodEquivSup _ _ hcomm hinf).toEquiv, Nat.card_prod,
      Data.card_tc, h.card_Y_inf_K₀ hKU hf]
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h.card_Y])).symm

theorem Data.Hyp.exists_mul_of_mem_Y (h : d.Hyp) (hKU : d.KUnitary)
    (hf : d.IsUnitaryFactor K₀) {y : G} (hy : y ∈ d.Y) :
    ∃ a ∈ d.Y ⊓ K₀, ∃ b ∈ d.Y ⊓ d.tc K₀, y = a * b := by
  have hy' : y ∈ (d.Y ⊓ K₀) ⊔ d.tc (d.Y ⊓ K₀) := by
    rw [← h.Y_eq_I_sup hKU hf]; exact hy
  have hcomm := h.I_comm hf
  have hinf := h.I_inf hf
  set Y' : ↥((d.Y ⊓ K₀) ⊔ d.tc (d.Y ⊓ K₀)) := ⟨y, hy'⟩
  have hB : ((KProd.projB _ _ hcomm hinf Y' : ↥(d.tc (d.Y ⊓ K₀))) : G) ∈ d.Y ⊓ d.tc K₀ := by
    have h2 := (KProd.projB _ _ hcomm hinf Y').2
    exact (h.tc_I (K₀ := K₀)) ▸ h2
  exact ⟨(KProd.projA _ _ hcomm hinf Y' : G), (KProd.projA _ _ hcomm hinf Y').2,
    (KProd.projB _ _ hcomm hinf Y' : G), hB, KProd.exists_eq_mul _ _ hcomm hinf Y'⟩

end YStructure

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
