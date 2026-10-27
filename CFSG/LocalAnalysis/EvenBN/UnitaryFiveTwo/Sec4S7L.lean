module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7K
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7J

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

theorem map_commutator_mk_subtype {G N : Type*} [Group G] [Group N] {H : Subgroup G}
    (φ : ↥H →* N) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    φ ⟨x * y * x⁻¹ * y⁻¹, H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)⟩ =
      φ ⟨x, hx⟩ * φ ⟨y, hy⟩ * (φ ⟨x, hx⟩)⁻¹ * (φ ⟨y, hy⟩)⁻¹ := by
  have e : (⟨x * y * x⁻¹ * y⁻¹,
      H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)⟩ : ↥H) =
      ⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]

theorem commutator_prod_eq {G : Type*} [Group G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {c n c' m : G} (hc : c ∈ A) (hn : n ∈ A)
    (hc' : c' ∈ B) (hm : m ∈ B) :
    (c * c')⁻¹ * (n * m) * (c * c') * (n * m)⁻¹ =
      (c⁻¹ * n * c * n⁻¹) * (c'⁻¹ * m * c' * m⁻¹) := by
  have e := CFSG.GroupTheory.commutatorElement_mul_of_commute hcomm (A.inv_mem hc) hn
    (B.inv_mem hc') hm
  have h1 : (c * c')⁻¹ = c⁻¹ * c'⁻¹ := by
    rw [mul_inv_rev]
    exact (hcomm c⁻¹ (A.inv_mem hc) c'⁻¹ (B.inv_mem hc')).symm
  have hinv : (c⁻¹ * c'⁻¹)⁻¹ = c * c' := by
    rw [mul_inv_rev, inv_inv, inv_inv]
    exact (hcomm c hc c' hc').symm
  calc (c * c')⁻¹ * (n * m) * (c * c') * (n * m)⁻¹
      = ⁅c⁻¹ * c'⁻¹, n * m⁆ := by rw [commutatorElement_def, hinv, h1]
    _ = ⁅c⁻¹, n⁆ * ⁅c'⁻¹, m⁆ := e
    _ = (c⁻¹ * n * c * n⁻¹) * (c'⁻¹ * m * c' * m⁻¹) := by
      simp only [commutatorElement_def, inv_inv]

section Struct

variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

theorem Data.Hyp.A₁_comm_mem_ZX₄ {a a' : G} (ha : a ∈ d.A₁) (ha' : a' ∈ d.A₁) :
    a * a' * a⁻¹ * a'⁻¹ ∈ d.ZX₄ := by
  obtain ⟨α, hα, rfl⟩ := ha
  obtain ⟨β, hβ, rfl⟩ := ha'
  have := commutator_mem_ZX₄sub_of_A₁ (α := β) (β := α⁻¹) hβ (inv_mem hα)
  rw [inv_inv] at this
  exact ⟨_, this, by simp only [map_mul, map_inv]⟩

theorem Data.Hyp.mem_A₁_of_comm_mod_ZX₄ {s : G} (hs : s ∈ d.S)
    (hc : ∀ a ∈ d.A₁, s * a * s⁻¹ * a⁻¹ ∈ d.ZX₄) : s ∈ d.A₁ := by
  obtain ⟨σ, hσ, rfl⟩ := hs
  refine ⟨σ, mem_A₁sub_of_comm_mod_ZX₄sub hσ fun α hα => ?_, rfl⟩
  obtain ⟨ζ, hζ, hζe⟩ := hc (d.ι α) ⟨α, hα, rfl⟩
  have : ζ = σ * α * σ⁻¹ * α⁻¹ := d.ι_injective (by rw [hζe]; simp only [map_mul, map_inv])
  rwa [← this]

theorem Data.Hyp.t_conj_comm_of_comm (h : d.Hyp) {x y : G} (e : x * y = y * x) :
    (d.t * x * d.t) * (d.t * y * d.t) = (d.t * y * d.t) * (d.t * x * d.t) := by
  rw [h.t_conj_mul', h.t_conj_mul', e]

include h hKU in
theorem Data.Hyp.P_le_centralizer_W_u : d.P ≤ centralizer (d.W : Set G) :=
  h.P_le_centralizer_W (h.comm_M_V₂_mem_W hKU) (fun m hm => h.M_le_normalizer_Y hKU hm)

include h hKU in
theorem Data.Hyp.W_comm_P {w p : G} (hw : w ∈ d.W) (hp : p ∈ d.P) : w * p = p * w :=
  mem_centralizer_iff.1 (h.P_le_centralizer_W_u hKU hp) w hw

include h hKU in
theorem Data.Hyp.eq_of_delta_apply_eq {n n' : G} (hn : n ∈ Data.Nn h hKU hf)
    (hn' : n' ∈ Data.Nn h hKU hf) (e : n * (d.t * n * d.t) = n' * (d.t * n' * d.t)) : n = n' :=
  congrArg Subtype.val (h.delta_injective hKU hf
    (show Data.delta h hKU hf ⟨n, hn⟩ = Data.delta h hKU hf ⟨n', hn'⟩ from e))

include h hKU in
theorem Data.Hyp.comm_iff_delta_comm {n n' : G} (hn : n ∈ Data.Nn h hKU hf)
    (hn' : n' ∈ Data.Nn h hKU hf) :
    n * n' = n' * n ↔
      (n * (d.t * n * d.t)) * (n' * (d.t * n' * d.t)) =
        (n' * (d.t * n' * d.t)) * (n * (d.t * n * d.t)) := by
  have key : ∀ β γ : ↥(Data.Nn h hKU hf), β * γ = γ * β ↔
      Data.delta h hKU hf β * Data.delta h hKU hf γ =
        Data.delta h hKU hf γ * Data.delta h hKU hf β := by
    intro β γ
    rw [← map_mul, ← map_mul]
    exact ⟨fun e => by rw [e], fun e => h.delta_injective hKU hf e⟩
  have := key ⟨n, hn⟩ ⟨n', hn'⟩
  exact ⟨fun e => this.1 (Subtype.ext e), fun e => congrArg Subtype.val (this.2 e)⟩

include h hKU in
theorem Data.Hyp.delta_commutator_apply {n n' : G} (hn : n ∈ Data.Nn h hKU hf)
    (hn' : n' ∈ Data.Nn h hKU hf) :
    (n * n' * n⁻¹ * n'⁻¹) * (d.t * (n * n' * n⁻¹ * n'⁻¹) * d.t) =
      (n * (d.t * n * d.t)) * (n' * (d.t * n' * d.t)) * (n * (d.t * n * d.t))⁻¹ *
        (n' * (d.t * n' * d.t))⁻¹ :=
  map_commutator_mk_subtype (Data.delta h hKU hf) hn hn'

include h hKU in
theorem Data.Hyp.S_le_range_delta : d.S ≤ (Data.delta h hKU hf).range := fun s hs => by
  obtain ⟨q, hq, rfl⟩ := h.exists_mem_Q_delta_eq hKU hf hs
  exact ⟨⟨q, hq.2⟩, rfl⟩

include h hKU in
theorem Data.Hyp.B₁_le_Q : Data.B₁ h hKU hf ≤ d.P ⊓ Data.Nn h hKU hf := by
  intro b hb
  obtain ⟨hbN, hbA⟩ := (h.mem_B₁_iff hKU hf).1 hb
  obtain ⟨q, hq, hqb⟩ := h.exists_mem_Q_delta_eq hKU hf (d.A₁_le_S hbA)
  have : b = q := h.eq_of_delta_apply_eq hKU hf hbN hq.2 hqb
  rw [this]
  exact hq

include h hKU in
theorem Data.Hyp.exists_mem_B₁_delta_eq {a : G} (ha : a ∈ d.A₁) :
    ∃ b ∈ Data.B₁ h hKU hf, a = b * (d.t * b * d.t) := by
  obtain ⟨q, hq, hqa⟩ := h.exists_mem_Q_delta_eq hKU hf (d.A₁_le_S ha)
  refine ⟨q, (h.mem_B₁_iff hKU hf).2 ⟨hq.2, ?_⟩, hqa⟩
  rw [← hqa]
  exact ha

include h hKU in
theorem Data.Hyp.card_comap_delta {M : Subgroup G} (hM : M ≤ d.S) :
    Nat.card ((M.comap (Data.delta h hKU hf)).map (Data.Nn h hKU hf).subtype) = Nat.card M := by
  have h1 : Nat.card ↥(M.comap (Data.delta h hKU hf)) =
      Nat.card ↥((M.comap (Data.delta h hKU hf)).map (Data.delta h hKU hf)) :=
    (Subgroup.card_map_of_injective (h.delta_injective hKU hf)).symm
  rw [Subgroup.map_comap_eq, inf_eq_right.2 (hM.trans (h.S_le_range_delta hKU hf))] at h1
  rw [Subgroup.card_map_of_injective (Data.Nn h hKU hf).subtype_injective]
  exact h1

include h hKU in
theorem Data.Hyp.card_B₁ : Nat.card (Data.B₁ h hKU hf) = 2 ^ 7 := by
  have := h.card_comap_delta hKU hf (d.A₁_le_S)
  rw [d.card_A₁] at this
  exact this

include h hKU in
theorem Data.Hyp.card_ZQ : Nat.card (Data.ZQ h hKU hf) = 2 := by
  have := h.card_comap_delta hKU hf (Data.Hyp.ZX₄_le_A₁.trans d.A₁_le_S)
  rw [Data.ZX₄, d.card_pull, card_ZX₄sub] at this
  exact this

include h hKU in
theorem Data.Hyp.ZQ_central {z q : G} (hz : z ∈ Data.ZQ h hKU hf)
    (hq : q ∈ d.P ⊓ Data.Nn h hKU hf) : q * z = z * q := by
  obtain ⟨hzN, hzZ⟩ := (h.mem_ZQ_iff hKU hf).1 hz
  have hqS : q * (d.t * q * d.t) ∈ d.S := h.delta_mem_S_of_mem_Q hKU hf hq
  rw [h.comm_iff_delta_comm hKU hf hq.2 hzN]
  exact Data.Hyp.ZX₄_comm_S hzZ hqS

include h hKU in
theorem Data.Hyp.mem_ZQ_of_central {q : G} (hq : q ∈ d.P ⊓ Data.Nn h hKU hf)
    (hc : ∀ q' ∈ d.P ⊓ Data.Nn h hKU hf, q * q' = q' * q) : q ∈ Data.ZQ h hKU hf := by
  refine (h.mem_ZQ_iff hKU hf).2 ⟨hq.2, Data.Hyp.mem_ZX₄_of_central_S
    (h.delta_mem_S_of_mem_Q hKU hf hq) fun s' hs' => ?_⟩
  obtain ⟨q', hq', rfl⟩ := h.exists_mem_Q_delta_eq hKU hf hs'
  exact (h.comm_iff_delta_comm hKU hf hq.2 hq'.2).1 (hc q' hq')

include h hKU in
theorem Data.Hyp.comm_B₁_tcB₁ : ∀ x ∈ Data.B₁ h hKU hf, ∀ y ∈ d.tc (Data.B₁ h hKU hf),
    x * y = y * x := fun _ hx _ hy =>
  h.comm_Nn_tcNn hKU hf (h.B₁_le_Nn hKU hf hx) (h.tc_mono (h.B₁_le_Nn hKU hf) hy)

include h hKU in
theorem Data.Hyp.B₁_commutator_mem_ZQ {b c : G} (hb : b ∈ Data.B₁ h hKU hf)
    (hc : c ∈ Data.B₁ h hKU hf) : b * c * b⁻¹ * c⁻¹ ∈ Data.ZQ h hKU hf := by
  obtain ⟨hbN, hbA⟩ := (h.mem_B₁_iff hKU hf).1 hb
  obtain ⟨hcN, hcA⟩ := (h.mem_B₁_iff hKU hf).1 hc
  refine (h.mem_ZQ_iff hKU hf).2 ⟨mul_mem (mul_mem (mul_mem hbN hcN) (inv_mem hbN)) (inv_mem hcN),
    ?_⟩
  rw [h.delta_commutator_apply hKU hf hbN hcN]
  exact Data.Hyp.A₁_comm_mem_ZX₄ hbA hcA

include h hKU in
theorem Data.Hyp.mem_ZQ_of_central_B₁ {b : G} (hb : b ∈ Data.B₁ h hKU hf)
    (hc : ∀ c ∈ Data.B₁ h hKU hf, b * c = c * b) : b ∈ Data.ZQ h hKU hf := by
  obtain ⟨hbN, hbA⟩ := (h.mem_B₁_iff hKU hf).1 hb
  refine (h.mem_ZQ_iff hKU hf).2 ⟨hbN, Data.Hyp.mem_ZX₄_of_central hbA fun a' ha' => ?_⟩
  obtain ⟨c, hcB, rfl⟩ := h.exists_mem_B₁_delta_eq hKU hf ha'
  exact (h.comm_iff_delta_comm hKU hf hbN (h.B₁_le_Nn hKU hf hcB)).1 (hc c hcB)

include h hKU in
theorem Data.Hyp.B₁_inf_tcB₁ : Data.B₁ h hKU hf ⊓ d.tc (Data.B₁ h hKU hf) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ Data.Nn h hKU hf ⊓ d.tc (Data.Nn h hKU hf) :=
    ⟨h.B₁_le_Nn hKU hf hx.1, h.tc_mono (h.B₁_le_Nn hKU hf) hx.2⟩
  rwa [h.Nn_inf_tcNn hKU hf] at this

include h hKU in
theorem Data.Hyp.W_eq_ZQ_sup : d.W = Data.ZQ h hKU hf ⊔ d.tc (Data.ZQ h hKU hf) := by
  have hZN := h.ZQ_le_Nn hKU hf
  have hcomm : ∀ a ∈ Data.ZQ h hKU hf, ∀ b ∈ d.tc (Data.ZQ h hKU hf), a * b = b * a :=
    fun a ha b hb => h.comm_Nn_tcNn hKU hf (hZN ha) (h.tc_mono hZN hb)
  have hinf : Data.ZQ h hKU hf ⊓ d.tc (Data.ZQ h hKU hf) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ Data.Nn h hKU hf ⊓ d.tc (Data.Nn h hKU hf) := ⟨hZN hx.1, h.tc_mono hZN hx.2⟩
    rwa [h.Nn_inf_tcNn hKU hf] at this
  have hcard : Nat.card ↥(Data.ZQ h hKU hf ⊔ d.tc (Data.ZQ h hKU hf)) = 4 := by
    rw [← Nat.card_congr (KProd.prodEquivSup _ _ hcomm hinf).toEquiv, Nat.card_prod,
      Data.card_tc, h.card_ZQ hKU hf]
  refine Subgroup.eq_of_le_of_card_ge (fun w hw => ?_) (by rw [hcard, h.sec4_9_W.1])
  have hwP : w ∈ d.P := h.W_le_P hw
  obtain ⟨q, hq, q', hq', hwqq⟩ := h.exists_Q_mul_Qt hKU hf hwP
  have hqq : ∀ q'' ∈ d.P ⊓ Data.Nn h hKU hf, q * q'' = q'' * q := by
    intro q'' hq''
    have e1 : w * q'' = q'' * w := h.W_comm_P hKU hw hq''.1
    have e2 : q'' * q' = q' * q'' := h.comm_Nn_tcNn hKU hf hq''.2 hq'.2
    rw [hwqq] at e1
    have : (q * q'') * q' = (q'' * q) * q' := by
      calc (q * q'') * q' = q * (q'' * q') := by group
        _ = q * (q' * q'') := by rw [e2]
        _ = q * q' * q'' := by group
        _ = q'' * (q * q') := e1
        _ = (q'' * q) * q' := by group
    exact mul_right_cancel this
  have hq'q' : ∀ y ∈ d.P ⊓ d.tc (Data.Nn h hKU hf), q' * y = y * q' := by
    intro y hy
    have e1 : w * y = y * w := h.W_comm_P hKU hw hy.1
    have e2 : q * y = y * q := h.comm_Nn_tcNn hKU hf hq.2 hy.2
    rw [hwqq] at e1
    have : q * (q' * y) = q * (y * q') := by
      calc q * (q' * y) = q * q' * y := by group
        _ = y * (q * q') := e1
        _ = (y * q) * q' := by group
        _ = (q * y) * q' := by rw [e2]
        _ = q * (y * q') := by group
    exact mul_left_cancel this
  have hqZ : q ∈ Data.ZQ h hKU hf := h.mem_ZQ_of_central hKU hf hq hqq
  have htq' : d.t * q' * d.t ∈ d.P ⊓ Data.Nn h hKU hf :=
    ⟨h.t_conj_mem_P hq'.1, (h.mem_tc).1 hq'.2⟩
  have htq'Z : d.t * q' * d.t ∈ Data.ZQ h hKU hf := by
    refine h.mem_ZQ_of_central hKU hf htq' fun q'' hq'' => ?_
    have htq'' : d.t * q'' * d.t ∈ d.P ⊓ d.tc (Data.Nn h hKU hf) :=
      ⟨h.t_conj_mem_P hq''.1, (h.mem_tc).2 (by rw [h.t_conj_conj]; exact hq''.2)⟩
    have := h.t_conj_comm_of_comm (hq'q' _ htq'')
    rwa [h.t_conj_conj] at this
  have hq'Z : q' ∈ d.tc (Data.ZQ h hKU hf) := (h.mem_tc).2 htq'Z
  rw [hwqq]
  exact mul_mem (mem_sup_left hqZ) (mem_sup_right hq'Z)

include h hKU in
theorem Data.Hyp.mem_B₁_of_mem_D₁ {n m : G} (hx : n * m ∈ d.D₁)
    (hn : n ∈ d.P ⊓ Data.Nn h hKU hf) (hm : m ∈ d.P ⊓ d.tc (Data.Nn h hKU hf)) :
    n ∈ Data.B₁ h hKU hf := by
  have hcZ : ∀ c ∈ Data.B₁ h hKU hf, c⁻¹ * n * c * n⁻¹ ∈ Data.ZQ h hKU hf := by
    intro c hc
    obtain ⟨hcN, hcA⟩ := (h.mem_B₁_iff hKU hf).1 hc
    have hc' : d.t * c * d.t ∈ d.tc (Data.Nn h hKU hf) := h.t_conj_mem_tcNn hKU hf hcN
    have hW := ((Data.Hyp.mem_UA₁_iff.1 (Subgroup.mem_inf.1 hx).1).2 _ hcA).1
    rw [commutator_prod_eq (fun a ha b hb => h.comm_Nn_tcNn hKU hf ha hb) hcN hn.2 hc' hm.2,
      h.W_eq_ZQ_sup hKU hf] at hW
    obtain ⟨z, hz, z', hz', hzz⟩ := KProd.exists_mul_of_mem_sup_of_comm (fun a ha b hb =>
      h.comm_Nn_tcNn hKU hf (h.ZQ_le_Nn hKU hf ha) (h.tc_mono (h.ZQ_le_Nn hKU hf) hb)) hW
    obtain ⟨e1, -⟩ := eq_of_mul_eq_mul_of_inf_eq_bot (h.Nn_inf_tcNn hKU hf)
      (mul_mem (mul_mem (mul_mem (inv_mem hcN) hn.2) hcN) (inv_mem hn.2))
      (h.ZQ_le_Nn hKU hf hz)
      (mul_mem (mul_mem (mul_mem (inv_mem hc') hm.2) hc') (inv_mem hm.2))
      (h.tc_mono (h.ZQ_le_Nn hKU hf) hz') hzz
    rw [e1]
    exact hz
  have hnS : n * (d.t * n * d.t) ∈ d.S := h.delta_mem_S_of_mem_Q hKU hf hn
  refine (h.mem_B₁_iff hKU hf).2 ⟨hn.2, Data.Hyp.mem_A₁_of_comm_mod_ZX₄ hnS fun a ha => ?_⟩
  obtain ⟨c, hcB, rfl⟩ := h.exists_mem_B₁_delta_eq hKU hf ha
  have hcN := h.B₁_le_Nn hKU hf hcB
  have hz := hcZ c hcB
  have hz' : n * c * n⁻¹ * c⁻¹ ∈ Data.ZQ h hKU hf := by
    have e : n * c * n⁻¹ * c⁻¹ = c * (c⁻¹ * n * c * n⁻¹) * c⁻¹ := by group
    have hcen : c * (c⁻¹ * n * c * n⁻¹) = (c⁻¹ * n * c * n⁻¹) * c :=
      h.ZQ_central hKU hf hz (h.B₁_le_Q hKU hf hcB)
    rw [e, hcen, mul_inv_cancel_right]
    exact hz
  have hZ := ((h.mem_ZQ_iff hKU hf).1 hz').2
  rw [h.delta_commutator_apply hKU hf hn.2 hcN] at hZ
  exact hZ

include h hKU in
theorem Data.Hyp.D₁_eq_B₁_sup_tc : d.D₁ = Data.B₁ h hKU hf ⊔ d.tc (Data.B₁ h hKU hf) := by
  have hle : d.D₁ ≤ Data.B₁ h hKU hf ⊔ d.tc (Data.B₁ h hKU hf) := by
    intro x hx
    obtain ⟨n, hn, m, hm, rfl⟩ := h.exists_Q_mul_Qt hKU hf (Data.Hyp.D₁_le_P (d := d) hx)
    have hnB : n ∈ Data.B₁ h hKU hf := h.mem_B₁_of_mem_D₁ hKU hf hx hn hm
    have hx' : (d.t * m * d.t) * (d.t * n * d.t) ∈ d.D₁ := by
      have h1 := h.t_conj_mem_D₁ hx
      rw [← h.t_conj_mul'] at h1
      rwa [← h.comm_Nn_tcNn hKU hf ((h.mem_tc).1 hm.2) (h.t_conj_mem_tcNn hKU hf hn.2)] at h1
    have htmB : d.t * m * d.t ∈ Data.B₁ h hKU hf :=
      h.mem_B₁_of_mem_D₁ hKU hf hx' ⟨h.t_conj_mem_P hm.1, (h.mem_tc).1 hm.2⟩
        ⟨h.t_conj_mem_P hn.1, h.t_conj_mem_tcNn hKU hf hn.2⟩
    exact mul_mem (mem_sup_left hnB) (mem_sup_right ((h.mem_tc).2 htmB))
  have hcard : Nat.card ↥(Data.B₁ h hKU hf ⊔ d.tc (Data.B₁ h hKU hf)) = 2 ^ 14 := by
    rw [← Nat.card_congr (KProd.prodEquivSup _ _ (h.comm_B₁_tcB₁ hKU hf)
      (h.B₁_inf_tcB₁ hKU hf)).toEquiv, Nat.card_prod, Data.card_tc, h.card_B₁ hKU hf]
    norm_num
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h.card_D₁])

include h hKU in
theorem Data.Hyp.tcB₁_le_D₁ : d.tc (Data.B₁ h hKU hf) ≤ d.D₁ := by
  rw [h.D₁_eq_B₁_sup_tc hKU hf]
  exact le_sup_right

include h hKU in
theorem Data.Hyp.B₁_le_D₁ : Data.B₁ h hKU hf ≤ d.D₁ := by
  rw [h.D₁_eq_B₁_sup_tc hKU hf]
  exact le_sup_left

include h hKU in
theorem Data.Hyp.mem_B₁_sup_W_iff {x : G} (hx : x ∈ d.D₁) :
    (∀ y ∈ d.D₁, x * y * x⁻¹ * y⁻¹ ∈ Data.ZQ h hKU hf) ↔ x ∈ Data.B₁ h hKU hf ⊔ d.W := by
  have hD := h.D₁_eq_B₁_sup_tc hKU hf
  constructor
  · intro hcomm
    have hx' : x ∈ Data.B₁ h hKU hf ⊔ d.tc (Data.B₁ h hKU hf) := by
      rw [← hD]
      exact hx
    obtain ⟨b, hb, c', hc', rfl⟩ :=
      KProd.exists_mul_of_mem_sup_of_comm (h.comm_B₁_tcB₁ hKU hf) hx'
    have hc'N : c' ∈ d.tc (Data.Nn h hKU hf) := h.tc_mono (h.B₁_le_Nn hKU hf) hc'
    have hcen : ∀ y ∈ d.tc (Data.B₁ h hKU hf), c' * y = y * c' := by
      intro y hy
      have hyN : y ∈ d.tc (Data.Nn h hKU hf) := h.tc_mono (h.B₁_le_Nn hKU hf) hy
      have h1 := hcomm y (h.tcB₁_le_D₁ hKU hf hy)
      have hu : b * (c' * y * c'⁻¹) = (c' * y * c'⁻¹) * b :=
        h.comm_B₁_tcB₁ hKU hf b hb _ (mul_mem (mul_mem hc' hy) (inv_mem hc'))
      have e : b * c' * y * (b * c')⁻¹ * y⁻¹ = c' * y * c'⁻¹ * y⁻¹ := by
        calc b * c' * y * (b * c')⁻¹ * y⁻¹ = (b * (c' * y * c'⁻¹)) * b⁻¹ * y⁻¹ := by group
          _ = ((c' * y * c'⁻¹) * b) * b⁻¹ * y⁻¹ := by rw [hu]
          _ = c' * y * c'⁻¹ * y⁻¹ := by group
      rw [e] at h1
      have h2 : c' * y * c'⁻¹ * y⁻¹ ∈ Data.Nn h hKU hf ⊓ d.tc (Data.Nn h hKU hf) :=
        Subgroup.mem_inf.2 ⟨h.ZQ_le_Nn hKU hf h1,
          mul_mem (mul_mem (mul_mem hc'N hyN) (inv_mem hc'N)) (inv_mem hyN)⟩
      rw [h.Nn_inf_tcNn hKU hf, Subgroup.mem_bot] at h2
      exact (commutatorElement_eq_one_iff_mul_comm (g₁ := c') (g₂ := y)).1 h2
    have htcB : d.t * c' * d.t ∈ Data.B₁ h hKU hf := (h.mem_tc).1 hc'
    have htcZ : d.t * c' * d.t ∈ Data.ZQ h hKU hf := by
      refine h.mem_ZQ_of_central_B₁ hKU hf htcB fun c hc => ?_
      have htc : d.t * c * d.t ∈ d.tc (Data.B₁ h hKU hf) :=
        (h.mem_tc).2 (by rw [h.t_conj_conj]; exact hc)
      have := h.t_conj_comm_of_comm (hcen _ htc)
      rwa [h.t_conj_conj] at this
    have hc'W : c' ∈ d.W := by
      rw [h.W_eq_ZQ_sup hKU hf]
      exact mem_sup_right ((h.mem_tc).2 htcZ)
    exact mul_mem (mem_sup_left hb) (mem_sup_right hc'W)
  · intro hxBW y hy
    obtain ⟨b, hb, w, hw, rfl⟩ := KProd.exists_mul_of_mem_sup_of_comm
      (fun a ha w hw => (h.W_comm_P hKU hw (h.B₁_le_Q hKU hf ha).1).symm) hxBW
    have hy' : y ∈ Data.B₁ h hKU hf ⊔ d.tc (Data.B₁ h hKU hf) := by
      rw [← hD]
      exact hy
    obtain ⟨b', hb', c', hc', rfl⟩ :=
      KProd.exists_mul_of_mem_sup_of_comm (h.comm_B₁_tcB₁ hKU hf) hy'
    have hwy : w * (b' * c') = (b' * c') * w :=
      h.W_comm_P hKU hw (Data.Hyp.D₁_le_P (d := d) hy)
    have hcb : c' * b⁻¹ * c'⁻¹ = b⁻¹ := by
      have := h.comm_B₁_tcB₁ hKU hf b⁻¹ (inv_mem hb) c' hc'
      rw [← this, mul_inv_cancel_right]
    have e : b * w * (b' * c') * (b * w)⁻¹ * (b' * c')⁻¹ = b * b' * b⁻¹ * b'⁻¹ := by
      calc b * w * (b' * c') * (b * w)⁻¹ * (b' * c')⁻¹
          = b * (w * (b' * c') * w⁻¹) * b⁻¹ * (b' * c')⁻¹ := by group
        _ = b * (b' * c') * b⁻¹ * (b' * c')⁻¹ := by rw [hwy, mul_inv_cancel_right]
        _ = b * b' * (c' * b⁻¹ * c'⁻¹) * b'⁻¹ := by group
        _ = b * b' * b⁻¹ * b'⁻¹ := by rw [hcb]
    rw [e]
    exact h.B₁_commutator_mem_ZQ hKU hf hb hb'

end Struct

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
