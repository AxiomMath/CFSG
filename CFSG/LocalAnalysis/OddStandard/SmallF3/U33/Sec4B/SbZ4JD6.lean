module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD5
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1Orbit

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

theorem exists_comm_subgroup {G₀ : Subgroup H} (hG₀ : ∀ m ∈ G₀, ∀ v ∈ V, m * v * m⁻¹ = v)
    (σ : H) :
    ∃ D : Subgroup H, (∀ m, m ∈ D ↔ m ∈ G₀ ∧ m * σ * m⁻¹ * σ⁻¹ ∈ V) ∧
      Nat.card D ≤ Nat.card ↥(G₀ ⊓ centralizer ({σ} : Set H)) * 4 := by
  classical
  let D : Subgroup H :=
    { carrier := {m | m ∈ G₀ ∧ m * σ * m⁻¹ * σ⁻¹ ∈ V}
      one_mem' :=
        ⟨G₀.one_mem, by rw [show (1 : H) * σ * 1⁻¹ * σ⁻¹ = 1 by group]; exact V.one_mem⟩
      mul_mem' := by
        rintro a b ⟨haG, haV⟩ ⟨hbG, hbV⟩
        refine ⟨G₀.mul_mem haG hbG, ?_⟩
        rw [show (a * b) * σ * (a * b)⁻¹ * σ⁻¹ =
              (a * (b * σ * b⁻¹ * σ⁻¹) * a⁻¹) * (a * σ * a⁻¹ * σ⁻¹) by group,
            hG₀ a haG (b * σ * b⁻¹ * σ⁻¹) hbV]
        exact V.mul_mem hbV haV
      inv_mem' := by
        rintro a ⟨haG, haV⟩
        refine ⟨G₀.inv_mem haG, ?_⟩
        rw [show a⁻¹ * σ * (a⁻¹)⁻¹ * σ⁻¹ =
              a⁻¹ * (a * σ * a⁻¹ * σ⁻¹)⁻¹ * (a⁻¹)⁻¹ by group,
            hG₀ a⁻¹ (G₀.inv_mem haG) (a * σ * a⁻¹ * σ⁻¹)⁻¹ (V.inv_mem haV)]
        exact V.inv_mem haV }
  have hDmem : ∀ m, m ∈ D ↔ m ∈ G₀ ∧ m * σ * m⁻¹ * σ⁻¹ ∈ V := fun m => Iff.rfl
  refine ⟨D, hDmem, ?_⟩
  have hbound := CFSG.SeitzReduction.RankOne.card_le_card_centralizer_mul_card_of_comm_mem
    (H := D) (A := V) (x := σ) (fun w hw => (hDmem w).mp hw |>.2)
  let f : ↥((centralizer ({σ} : Set H)).subgroupOf D) → ↥(G₀ ⊓ centralizer ({σ} : Set H)) :=
    fun k => ⟨(k.1 : H), ((hDmem (k.1 : H)).mp k.1.2).1, (Subgroup.mem_subgroupOf).mp k.2⟩
  have hinj : Nat.card ↥((centralizer ({σ} : Set H)).subgroupOf D) ≤
      Nat.card ↥(G₀ ⊓ centralizer ({σ} : Set H)) := by
    refine Nat.card_le_card_of_injective f ?_
    intro k k' hkk'
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : ↥(G₀ ⊓ centralizer ({σ} : Set H)) => (u : H)) hkk'
  calc Nat.card D
      ≤ Nat.card ↥((centralizer ({σ} : Set H)).subgroupOf D) * Nat.card V := hbound
    _ ≤ Nat.card ↥(G₀ ⊓ centralizer ({σ} : Set H)) * 4 := by
        rw [h.card_V]
        exact Nat.mul_le_mul_right 4 hinj

theorem comm_t_mem_V {q : H} (hq : q ∈ Q) : q * t * q⁻¹ * t⁻¹ ∈ V := by
  have hVY : V ≤ Y := by rw [h.Y_eq]; exact le_sup_left
  have hVQ : V ≤ Q := fun x hx => h.Y_le_Q (hVY hx)
  have hG₀ : ∀ m ∈ Q, ∀ v ∈ V, m * v * m⁻¹ = v := by
    intro m hm v hv
    rw [h.Q_comm m hm v (hVQ hv)]
    group
  obtain ⟨D, hDmem, _⟩ := h.exists_comm_subgroup hG₀ t
  have hyV : y ∈ V := by rw [h.V_eq]; exact Subgroup.subset_closure (by simp)
  have hzV : z ∈ V := by rw [h.V_eq]; exact Subgroup.subset_closure (by simp)
  have hkey : ∀ u w : H, u ∈ Q → w ∈ V → t * u * t⁻¹ = u * w → u * t * u⁻¹ * t⁻¹ ∈ V := by
    intro u w hu hw htu
    have htu' : t * u⁻¹ * t⁻¹ = (u * w)⁻¹ := by rw [← htu]; group
    have he : u * t * u⁻¹ * t⁻¹ = w⁻¹ := by
      calc u * t * u⁻¹ * t⁻¹ = u * (t * u⁻¹ * t⁻¹) := by group
        _ = u * (u * w)⁻¹ := by rw [htu']
        _ = w⁻¹ := by
              rw [mul_inv_rev, h.Q_comm w⁻¹ (hVQ (V.inv_mem hw)) u⁻¹ (Q.inv_mem hu)]
              group
    rw [he]
    exact V.inv_mem hw
  have hBD : B ≤ D := by
    intro b hb
    refine (hDmem b).mpr ⟨h.B_le_Q hb, ?_⟩
    rw [show b * t * b⁻¹ * t⁻¹ = 1 by rw [← h.B_cent_t b hb]; group]
    exact V.one_mem
  have hV'D : V' ≤ D := by
    rw [h.V'_eq, Subgroup.closure_le]
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with e | e
    · rw [e]
      exact (hDmem v₁).mpr ⟨h.Y_le_Q h.v₁_mem, hkey v₁ y (h.Y_le_Q h.v₁_mem) hyV h.t_v₁⟩
    · rw [e]
      exact (hDmem v₂).mpr
        ⟨h.Y_le_Q h.v₂_mem, hkey v₂ (y * z) (h.Y_le_Q h.v₂_mem) (V.mul_mem hyV hzV) h.t_v₂⟩
  have hQD : Q ≤ D := by rw [h.Q_eq]; exact sup_le hBD hV'D
  exact ((hDmem q).mp (hQD hq)).2

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem Mc_cent_tau (hb : ZJBound t) {m : H} (hm : m ∈ Mc) (hc : τ * m = m * τ) : m ∈ Y := by
  have hG₀V : ∀ x ∈ Mc ⊓ centralizer ({τ} : Set H), ∀ v ∈ V, x * v * x⁻¹ = v :=
    fun x hx v hv => h.Mh_cent_V hMh (h.Mc_le_Mh hMh hMc hx.1) hv
  obtain ⟨D, hDmem, hDcard⟩ := h.exists_comm_subgroup hG₀V t
  have hG₀D : Mc ⊓ centralizer ({τ} : Set H) ≤ D := by
    intro k hk
    obtain ⟨hkMc, hkτ⟩ := hk
    have hkMh : k ∈ Mh := h.Mc_le_Mh hMh hMc hkMc
    have hkc : k * τ = τ * k := (Subgroup.mem_centralizer_singleton_iff).mp hkτ
    have hcQ : k * t * k⁻¹ * t⁻¹ ∈ Q := h.Mh_comm_t hMh hkMh
    have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
    have hleft : t * (k * t * k⁻¹ * t⁻¹) * t⁻¹ = t * k * t * k⁻¹ := by
      calc t * (k * t * k⁻¹ * t⁻¹) * t⁻¹
          = t * k * t * k⁻¹ * (t⁻¹ * t⁻¹) := by group
        _ = t * k * t * k⁻¹ := by
              rw [show t⁻¹ * t⁻¹ = 1 by rw [ht_inv, h.t_sq], mul_one]
    have hright : (k * t * k⁻¹ * t⁻¹)⁻¹ = t * k * t * k⁻¹ := by
      rw [show (k * t * k⁻¹ * t⁻¹)⁻¹ = t * k * t⁻¹ * k⁻¹ by group, ht_inv]
    have hc_t_inv : t * (k * t * k⁻¹ * t⁻¹) * t⁻¹ = (k * t * k⁻¹ * t⁻¹)⁻¹ := by
      rw [hleft, hright]
    have hc_fixed : τ * (k * t * k⁻¹ * t⁻¹) * τ⁻¹ = k * t * k⁻¹ * t⁻¹ := by
      have h1 : τ * k * τ⁻¹ = k := by rw [hkc.symm]; group
      have h2 : τ * t * τ⁻¹ = t := by rw [h.t_tau.symm]; group
      have h1' : τ * k⁻¹ * τ⁻¹ = k⁻¹ := by
        rw [show τ * k⁻¹ * τ⁻¹ = (τ * k * τ⁻¹)⁻¹ by group, h1]
      have h2' : τ * t⁻¹ * τ⁻¹ = t⁻¹ := by
        rw [show τ * t⁻¹ * τ⁻¹ = (τ * t * τ⁻¹)⁻¹ by group, h2]
      rw [show τ * (k * t * k⁻¹ * t⁻¹) * τ⁻¹ =
            (τ * k * τ⁻¹) * (τ * t * τ⁻¹) * (τ * k⁻¹ * τ⁻¹) * (τ * t⁻¹ * τ⁻¹) by group,
          h1, h2, h1', h2']
    have hc_inv : τ * (k * t * k⁻¹ * t⁻¹) * τ⁻¹ = (k * t * k⁻¹ * t⁻¹)⁻¹ :=
      h.tau_inv _ hcQ
    have hcc : (k * t * k⁻¹ * t⁻¹) * (k * t * k⁻¹ * t⁻¹) = 1 := by
      have heq : k * t * k⁻¹ * t⁻¹ = (k * t * k⁻¹ * t⁻¹)⁻¹ := hc_fixed.symm.trans hc_inv
      exact (congrArg (fun u => (k * t * k⁻¹ * t⁻¹) * u) heq).trans (mul_inv_cancel _)
    have hcY : k * t * k⁻¹ * t⁻¹ ∈ Y := h.Y_mem _ hcQ hcc
    have hc_inv_eq : (k * t * k⁻¹ * t⁻¹)⁻¹ = k * t * k⁻¹ * t⁻¹ :=
      inv_eq_of_mul_eq_one_right hcc
    have hc_cent_t : t * (k * t * k⁻¹ * t⁻¹) = (k * t * k⁻¹ * t⁻¹) * t := by
      calc t * (k * t * k⁻¹ * t⁻¹) = (t * (k * t * k⁻¹ * t⁻¹) * t⁻¹) * t := by group
        _ = (k * t * k⁻¹ * t⁻¹) * t := by rw [hc_t_inv, hc_inv_eq]
    exact (hDmem k).mpr ⟨⟨hkMc, hkτ⟩, h.Y_cent_t _ hcY hc_cent_t⟩
  have hcardG₀ : Nat.card ↥(Mc ⊓ centralizer ({τ} : Set H)) ≤ 16 := by
    have h1 : Nat.card ↥(Mc ⊓ centralizer ({τ} : Set H)) ≤
        Nat.card ↥((Mc ⊓ centralizer ({τ} : Set H)) ⊓ centralizer ({t} : Set H)) * 4 :=
      le_trans (Subgroup.card_le_of_le hG₀D) hDcard
    have h2 : (Mc ⊓ centralizer ({τ} : Set H)) ⊓ centralizer ({t} : Set H) ≤ V := by
      intro x hx
      obtain ⟨⟨hxMc, hxτ⟩, hxt⟩ := hx
      have hxt' : x * t = t * x := (Subgroup.mem_centralizer_singleton_iff).mp hxt
      have hxB : x ∈ B := h.Mc_cent_t hMh hMc hb hxMc hxt'.symm
      have hxQ : x ∈ Q := h.B_le_Q hxB
      have hxτ' : x * τ = τ * x := (Subgroup.mem_centralizer_singleton_iff).mp hxτ
      have h1τ : τ * x * τ⁻¹ = x⁻¹ := h.tau_inv x hxQ
      have h2τ : τ * x * τ⁻¹ = x := by rw [← hxτ']; group
      have heq : x = x⁻¹ := h2τ.symm.trans h1τ
      have hx_sq : x * x = 1 :=
        (congrArg (fun u => x * u) heq).trans (mul_inv_cancel x)
      have hxY : x ∈ Y := h.Y_mem x hxQ hx_sq
      exact h.Y_cent_t x hxY hxt'.symm
    have h3 : Nat.card ↥((Mc ⊓ centralizer ({τ} : Set H)) ⊓ centralizer ({t} : Set H)) ≤ 4 :=
      calc Nat.card ↥((Mc ⊓ centralizer ({τ} : Set H)) ⊓ centralizer ({t} : Set H))
          ≤ Nat.card ↥V := Subgroup.card_le_of_le h2
        _ = 4 := h.card_V
    calc Nat.card ↥(Mc ⊓ centralizer ({τ} : Set H))
        ≤ Nat.card ↥((Mc ⊓ centralizer ({τ} : Set H)) ⊓ centralizer ({t} : Set H)) * 4 := h1
      _ ≤ 4 * 4 := Nat.mul_le_mul_right 4 h3
      _ = 16 := by norm_num
  have hQMc : Q ≤ Mc := h.Q_le_Mc hMh hMc
  have hYG₀ : Y ≤ Mc ⊓ centralizer ({τ} : Set H) := by
    intro u hu
    refine ⟨hQMc (h.Y_le_Q hu), ?_⟩
    refine (Subgroup.mem_centralizer_singleton_iff).mpr ?_
    have h1 : τ * u * τ⁻¹ = u⁻¹ := h.tau_inv u (h.Y_le_Q hu)
    have hu1 : u⁻¹ = u := inv_eq_of_mul_eq_one_right (h.Y_sq u hu)
    have h2 : τ * u * τ⁻¹ = u := by rw [h1, hu1]
    calc u * τ = (τ * u * τ⁻¹) * τ := by rw [h2]
      _ = τ * u := by group
  have hYeq : Y = Mc ⊓ centralizer ({τ} : Set H) :=
    Subgroup.eq_of_le_of_card_ge hYG₀ (by rw [h.card_Y]; exact hcardG₀)
  have hmG₀ : m ∈ Mc ⊓ centralizer ({τ} : Set H) :=
    ⟨hm, (Subgroup.mem_centralizer_singleton_iff).mpr hc.symm⟩
  exact hYeq.symm ▸ hmG₀

theorem Mc_comm_t_mem_V_iff (hb : ZJBound t) {m : H} (hm : m ∈ Mc) :
    m * t * m⁻¹ * t⁻¹ ∈ V ↔ m ∈ Q := by
  have hMcV : ∀ x ∈ Mc, ∀ v ∈ V, x * v * x⁻¹ = v :=
    fun x hx v hv => h.Mh_cent_V hMh (h.Mc_le_Mh hMh hMc hx) hv
  constructor
  · intro hmV
    obtain ⟨D, hDmem, hDcard⟩ := h.exists_comm_subgroup hMcV t
    have hQMc : Q ≤ Mc := h.Q_le_Mc hMh hMc
    have hQD : Q ≤ D := fun q hq => (hDmem q).mpr ⟨hQMc hq, h.comm_t_mem_V hq⟩
    have hcentB : Mc ⊓ centralizer ({t} : Set H) ≤ B := by
      intro x hx
      exact h.Mc_cent_t hMh hMc hb hx.1
        ((Subgroup.mem_centralizer_singleton_iff).mp hx.2).symm
    have hcard_cent : Nat.card ↥(Mc ⊓ centralizer ({t} : Set H)) ≤ 16 :=
      calc Nat.card ↥(Mc ⊓ centralizer ({t} : Set H)) ≤ Nat.card B :=
            Subgroup.card_le_of_le hcentB
        _ = 16 := h.card_B
    have hDcard64 : Nat.card D ≤ 64 := by
      calc Nat.card D ≤ Nat.card ↥(Mc ⊓ centralizer ({t} : Set H)) * 4 := hDcard
        _ ≤ 16 * 4 := Nat.mul_le_mul_right 4 hcard_cent
        _ = 64 := by norm_num
    have hQD_eq : Q = D :=
      Subgroup.eq_of_le_of_card_ge hQD (by rw [h.card_Q]; exact hDcard64)
    have hmD : m ∈ D := (hDmem m).mpr ⟨hm, hmV⟩
    exact hQD_eq.symm ▸ hmD
  · intro hmQ
    exact h.comm_t_mem_V hmQ

theorem Mc_comm_tau_mem_V_iff (hb : ZJBound t) {m : H} (hm : m ∈ Mc) :
    m * τ * m⁻¹ * τ⁻¹ ∈ V ↔ m ∈ Q := by
  have hMcV : ∀ x ∈ Mc, ∀ v ∈ V, x * v * x⁻¹ = v :=
    fun x hx v hv => h.Mh_cent_V hMh (h.Mc_le_Mh hMh hMc hx) hv
  have hQmem : ∀ q ∈ Q, q * τ * q⁻¹ * τ⁻¹ ∈ V := by
    intro q hq
    have h1 : τ * q⁻¹ * τ⁻¹ = q := by
      rw [show τ * q⁻¹ * τ⁻¹ = (τ * q * τ⁻¹)⁻¹ by group, h.tau_inv q hq]
      group
    have he : q * τ * q⁻¹ * τ⁻¹ = q ^ 2 := by
      rw [show q * τ * q⁻¹ * τ⁻¹ = q * (τ * q⁻¹ * τ⁻¹) by group, h1, pow_two]
    rw [he]
    exact h.sq_mem_V q hq
  constructor
  · intro hmV
    obtain ⟨D, hDmem, hDcard⟩ := h.exists_comm_subgroup hMcV τ
    have hQMc : Q ≤ Mc := h.Q_le_Mc hMh hMc
    have hQD : Q ≤ D := fun q hq => (hDmem q).mpr ⟨hQMc hq, hQmem q hq⟩
    have hcentY : Mc ⊓ centralizer ({τ} : Set H) ≤ Y := by
      intro x hx
      exact h.Mc_cent_tau hMh hMc hb hx.1
        ((Subgroup.mem_centralizer_singleton_iff).mp hx.2).symm
    have hcard_cent : Nat.card ↥(Mc ⊓ centralizer ({τ} : Set H)) ≤ 16 :=
      calc Nat.card ↥(Mc ⊓ centralizer ({τ} : Set H)) ≤ Nat.card Y :=
            Subgroup.card_le_of_le hcentY
        _ = 16 := h.card_Y
    have hDcard64 : Nat.card D ≤ 64 := by
      calc Nat.card D ≤ Nat.card ↥(Mc ⊓ centralizer ({τ} : Set H)) * 4 := hDcard
        _ ≤ 16 * 4 := Nat.mul_le_mul_right 4 hcard_cent
        _ = 64 := by norm_num
    have hQD_eq : Q = D :=
      Subgroup.eq_of_le_of_card_ge hQD (by rw [h.card_Q]; exact hDcard64)
    have hmD : m ∈ D := (hDmem m).mpr ⟨hm, hmV⟩
    exact hQD_eq.symm ▸ hmD
  · intro hmQ
    exact hQmem m hmQ

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
