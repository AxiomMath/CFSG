module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7M
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7Gen
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7Comm

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem conj_conj_eq_self {u : G} (hu : u * u = 1) (x : G) : u * (u * x * u) * u = x := by
  calc u * (u * x * u) * u = (u * u) * x * (u * u) := by group
    _ = x := by rw [hu]; group

theorem comm_of_conj_comm {u X Y : G} (hu : u * u = 1)
    (h : (u * X * u) * (u * Y * u) = (u * Y * u) * (u * X * u)) : X * Y = Y * X := by
  have := mul_conj_comm_of_comm hu h
  rwa [conj_conj_eq_self hu, conj_conj_eq_self hu] at this

theorem mem_map_conj_iff_of_invol {u : G} (hu : u * u = 1) {N : Subgroup G} {x : G} :
    x ∈ N.map (MulAut.conj u).toMonoidHom ↔ u * x * u ∈ N := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  constructor
  · rintro ⟨n, hn, rfl⟩
    show u * (u * n * u⁻¹) * u ∈ N
    rw [hu', conj_conj_eq_self hu]
    exact hn
  · intro hx
    refine ⟨u * x * u, hx, ?_⟩
    show u * (u * x * u) * u⁻¹ = x
    rw [hu', conj_conj_eq_self hu]

theorem sup_commute_sup {A A' B B' : Subgroup G}
    (h₁ : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (h₂ : ∀ x ∈ A, ∀ y ∈ B', x * y = y * x)
    (h₃ : ∀ x ∈ A', ∀ y ∈ B, x * y = y * x) (h₄ : ∀ x ∈ A', ∀ y ∈ B', x * y = y * x) :
    ∀ x ∈ A ⊔ A', ∀ y ∈ B ⊔ B', x * y = y * x := by
  have hA : ∀ x ∈ A, B ⊔ B' ≤ centralizer ({x} : Set G) := fun x hx =>
    sup_le (fun y hy => mem_centralizer_singleton_iff.2 (h₁ x hx y hy).symm)
      (fun y hy => mem_centralizer_singleton_iff.2 (h₂ x hx y hy).symm)
  have hA' : ∀ x ∈ A', B ⊔ B' ≤ centralizer ({x} : Set G) := fun x hx =>
    sup_le (fun y hy => mem_centralizer_singleton_iff.2 (h₃ x hx y hy).symm)
      (fun y hy => mem_centralizer_singleton_iff.2 (h₄ x hx y hy).symm)
  have hle : A ⊔ A' ≤ centralizer ((B ⊔ B' : Subgroup G) : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [mem_centralizer_iff]
      intro y hy
      exact mem_centralizer_singleton_iff.1 (hA x hx hy)
    · rw [mem_centralizer_iff]
      intro y hy
      exact mem_centralizer_singleton_iff.1 (hA' x hx hy)
  intro x hx y hy
  exact (mem_centralizer_iff.1 (hle hx) y hy).symm

end Generic

theorem K₃sub_le_gen : K₃sub ≤ A₂sub ⊔ K₂sub ⊔ zpowers uSU := by
  refine sup_le (sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_) ?_
  · exact ZX₁sub_le_X₁sub.trans (X₁sub_le_A₂sub.trans (le_sup_left.trans le_sup_left))
  · exact X₂sub_le_K₂sub.trans (le_sup_right.trans le_sup_left)
  · exact X₃sub_le_A₂sub.trans (le_sup_left.trans le_sup_left)
  · exact ZX₄sub_le_X₄sub.trans (X₄sub_le_A₂sub.trans (le_sup_left.trans le_sup_left))
  · exact le_sup_right
  · exact (le_sup_right : zpowers vSU ≤ K₂sub).trans (le_sup_right.trans le_sup_left)

theorem Ssub_le_gen : Ssub ≤ A₂sub ⊔ K₂sub := by
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · exact X₁sub_le_A₂sub.trans le_sup_left
  · exact X₂sub_le_K₂sub.trans le_sup_right
  · exact X₃sub_le_A₂sub.trans le_sup_left
  · exact X₄sub_le_A₂sub.trans le_sup_left

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

theorem Data.S_le_A₂_sup_K₂ (d : Data G) : d.S ≤ d.A₂ ⊔ d.K₂ := by
  have h1 := d.pull_mono Ssub_le_gen
  rwa [d.pull_sup] at h1

theorem Data.K₃_le_gen (d : Data G) : d.K₃ ≤ d.A₂ ⊔ d.K₂ ⊔ zpowers d.u := by
  have h1 := d.pull_mono K₃sub_le_gen
  have h2 : d.pull (A₂sub ⊔ K₂sub ⊔ zpowers uSU) = d.A₂ ⊔ d.K₂ ⊔ zpowers d.u := by
    rw [d.pull_sup, d.pull_sup]
    congr 1
    exact MonoidHom.map_zpowers d.ι uSU
  exact h2 ▸ h1

section Final

variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

@[expose] noncomputable def Data.Gg : Subgroup G :=
  Data.Nn h hKU hf ⊔ (Data.Nn h hKU hf).map (MulAut.conj d.u).toMonoidHom

include h hKU in
theorem Data.Hyp.Nn_le_Gg : Data.Nn h hKU hf ≤ Data.Gg h hKU hf := le_sup_left

include h hKU in
theorem Data.Hyp.comm_conj_u_tcNn
    (hBu : ∀ x ∈ Data.B₁ h hKU hf, d.u * x * d.u⁻¹ ∈ Data.B₁ h hKU hf) :
    ∀ x ∈ Data.Nn h hKU hf, ∀ y ∈ Data.Nn h hKU hf,
      (d.u * x * d.u) * (d.t * y * d.t) = (d.t * y * d.t) * (d.u * x * d.u) := by
  have hu1 : d.u⁻¹ = d.u := inv_eq_of_mul_eq_one_right (Data.u_mul_u d)
  have hv1 : d.v⁻¹ = d.v := inv_eq_of_mul_eq_one_right (Data.v_mul_v d)
  exact commute_conj_of_generation (Data.Nn h hKU hf) (Data.B₁ h hKU hf) d.u d.v d.t
    (Data.u_mul_u d) (Data.v_mul_v d) h.t_mul_t (h.t_comm_of_mem_L (Data.u_mem_L d)).symm
    (h.t_comm_of_mem_L (Data.v_mem_L d)).symm (Data.uv_pow_four d) (h.B₁_le_Nn hKU hf)
    (fun x hx => by
      have := hBu x hx
      rwa [hu1] at this)
    (fun x hx => by
      have := (mem_normalizer_iff.1 (h.v_mem_normalizer_Nn hKU hf) x).1 hx
      rwa [hv1] at this)
    (fun x hx y hy => h.comm_Nn_tcNn hKU hf hx (h.t_conj_mem_tcNn hKU hf hy))
    (h.Nn_eq_gen hKU hf hBu)

include h hKU in
theorem Data.Hyp.comm_Gg_tcGg
    (hBu : ∀ x ∈ Data.B₁ h hKU hf, d.u * x * d.u⁻¹ ∈ Data.B₁ h hKU hf) :
    ∀ x ∈ Data.Gg h hKU hf, ∀ y ∈ d.tc (Data.Gg h hKU hf), x * y = y * x := by
  have hc := h.comm_conj_u_tcNn hKU hf hBu
  have huu := Data.u_mul_u d
  have htt := h.t_mul_t
  have htu : d.t * d.u = d.u * d.t := (h.t_comm_of_mem_L (Data.u_mem_L d)).symm
  have htut : d.t * d.u * d.t = d.u := by rw [htu, mul_assoc, htt, mul_one]
  have e1 : ∀ y : G, d.t * (d.u * (d.t * y * d.t) * d.u) * d.t = d.u * y * d.u := by
    intro y
    calc d.t * (d.u * (d.t * y * d.t) * d.u) * d.t
        = (d.t * d.u * d.t) * y * (d.t * d.u * d.t) := by group
      _ = d.u * y * d.u := by rw [htut]
  rw [Data.Gg, h.tc_sup]
  refine sup_commute_sup (fun x hx y hy => h.comm_Nn_tcNn hKU hf hx hy) ?_ ?_ ?_
  ·
    intro x hx y hy
    have hy' : d.u * (d.t * y * d.t) * d.u ∈ Data.Nn h hKU hf :=
      (mem_map_conj_iff_of_invol huu).1 ((h.mem_tc).1 hy)
    have := hc x hx _ hy'
    rw [e1] at this
    exact comm_of_conj_comm huu this
  ·
    intro x hx y hy
    have hx' : d.u * x * d.u ∈ Data.Nn h hKU hf := (mem_map_conj_iff_of_invol huu).1 hx
    have hy' : d.t * y * d.t ∈ Data.Nn h hKU hf := (h.mem_tc).1 hy
    have := hc _ hx' _ hy'
    rwa [conj_conj_eq_self huu, h.t_conj_conj] at this
  ·
    intro x hx y hy
    have hx' : d.u * x * d.u ∈ Data.Nn h hKU hf := (mem_map_conj_iff_of_invol huu).1 hx
    have hy' : d.u * (d.t * y * d.t) * d.u ∈ Data.Nn h hKU hf :=
      (mem_map_conj_iff_of_invol huu).1 ((h.mem_tc).1 hy)
    have := h.comm_Nn_tcNn hKU hf hx' (h.t_conj_mem_tcNn hKU hf hy')
    rw [e1] at this
    exact comm_of_conj_comm huu this

include h hKU in
theorem Data.Hyp.u_mem_normalizer_Gg : d.u ∈ normalizer (Data.Gg h hKU hf : Set G) := by
  have huu := Data.u_mul_u d
  have hu' : d.u⁻¹ = d.u := inv_eq_of_mul_eq_one_right huu
  refine mem_normalizer_fintype fun y hy => ?_
  have hle : Data.Gg h hKU hf ≤ (Data.Gg h hKU hf).comap (MulAut.conj d.u).toMonoidHom := by
    refine sup_le ?_ ?_
    · intro n hn
      exact Subgroup.mem_sup_right ⟨n, hn, rfl⟩
    · rintro _ ⟨n, hn, rfl⟩
      rw [Subgroup.mem_comap]
      have e : (MulAut.conj d.u).toMonoidHom ((MulAut.conj d.u).toMonoidHom n) = n := by
        show d.u * (d.u * n * d.u⁻¹) * d.u⁻¹ = n
        rw [hu']
        exact conj_conj_eq_self huu n
      rw [e]
      exact Subgroup.mem_sup_left hn
  exact hle hy

include h hKU in
theorem Data.Hyp.delta_mem_normalizer_Gg
    (hBu : ∀ x ∈ Data.B₁ h hKU hf, d.u * x * d.u⁻¹ ∈ Data.B₁ h hKU hf)
    (n : ↥(Data.Nn h hKU hf)) :
    Data.delta h hKU hf n ∈ normalizer (Data.Gg h hKU hf : Set G) := by
  have hcomm := h.comm_Gg_tcGg hKU hf hBu
  have hn : (n : G) ∈ normalizer (Data.Gg h hKU hf : Set G) :=
    le_normalizer (h.Nn_le_Gg hKU hf n.2)
  have htn : d.t * (n : G) * d.t ∈ normalizer (Data.Gg h hKU hf : Set G) := by
    refine mem_normalizer_of_forall_comm fun x hx => ?_
    exact hcomm x hx _ (h.tc_mono (h.Nn_le_Gg hKU hf) (h.t_conj_mem_tcNn hKU hf n.2))
  rw [h.delta_eq_mul hKU hf]
  exact mul_mem hn htn

include h hKU in
theorem Data.Hyp.A₂_sup_K₂_le_normalizer_Gg
    (hBu : ∀ x ∈ Data.B₁ h hKU hf, d.u * x * d.u⁻¹ ∈ Data.B₁ h hKU hf) :
    d.A₂ ⊔ d.K₂ ≤ normalizer (Data.Gg h hKU hf : Set G) := by
  intro x hx
  rw [← h.range_delta_eq_A₂_sup_K₂ hKU hf] at hx
  obtain ⟨n, rfl⟩ := hx
  exact h.delta_mem_normalizer_Gg hKU hf hBu n

include h hKU in
theorem Data.Hyp.S_le_normalizer_Gg
    (hBu : ∀ x ∈ Data.B₁ h hKU hf, d.u * x * d.u⁻¹ ∈ Data.B₁ h hKU hf) :
    d.S ≤ normalizer (Data.Gg h hKU hf : Set G) :=
  (Data.S_le_A₂_sup_K₂ d).trans (h.A₂_sup_K₂_le_normalizer_Gg hKU hf hBu)

include h hKU in
theorem Data.Hyp.K₃_le_normalizer_Gg
    (hBu : ∀ x ∈ Data.B₁ h hKU hf, d.u * x * d.u⁻¹ ∈ Data.B₁ h hKU hf) :
    d.K₃ ≤ normalizer (Data.Gg h hKU hf : Set G) :=
  (Data.K₃_le_gen d).trans (sup_le (h.A₂_sup_K₂_le_normalizer_Gg hKU hf hBu)
    (zpowers_le.2 (h.u_mem_normalizer_Gg hKU hf)))

include h hKU in
theorem Data.Hyp.L_le_normalizer_Gg
    (hBu : ∀ x ∈ Data.B₁ h hKU hf, d.u * x * d.u⁻¹ ∈ Data.B₁ h hKU hf) :
    d.L ≤ normalizer (Data.Gg h hKU hf : Set G) :=
  h.L_le_of_S_K₃_u hKU hf (h.S_le_normalizer_Gg hKU hf hBu) (h.K₃_le_normalizer_Gg hKU hf hBu)
    (h.u_mem_normalizer_Gg hKU hf)

include h hKU in
theorem Data.Hyp.K₀_le_Gg
    (hBu : ∀ x ∈ Data.B₁ h hKU hf, d.u * x * d.u⁻¹ ∈ Data.B₁ h hKU hf) :
    K₀ ≤ Data.Gg h hKU hf := by
  haveI := hf.isSimpleGroup
  have hK₃N := h.K₃_le_normalizer_Gg hKU hf hBu
  set Hs : Subgroup ↥K₀ := (Data.Gg h hKU hf).subgroupOf K₀ with hHs
  haveI : Hs.Normal := ⟨fun n hn g => by
    have hn' : (n : G) ∈ Data.Gg h hKU hf := Subgroup.mem_subgroupOf.1 hn
    set tg : G := d.t * (g : G) * d.t with htgdef
    have htg : tg ∈ d.tc K₀ := (h.mem_tc).2 (by rw [htgdef, h.t_conj_conj]; exact g.2)
    have hθ : (g : G) * tg ∈ d.K₃ := by
      have := Data.theta_mem_K₃ h hKU hf g
      rwa [Data.theta_apply] at this
    have h1 := (mem_normalizer_iff.1 (hK₃N hθ) (n : G)).1 hn'
    have e : (g : G) * tg * (n : G) * ((g : G) * tg)⁻¹ = (g : G) * (n : G) * (g : G)⁻¹ := by
      have hc : tg * (n : G) = (n : G) * tg := (hf.comm_elem (n : G) n.2 tg htg).symm
      calc (g : G) * tg * (n : G) * ((g : G) * tg)⁻¹
          = (g : G) * (tg * (n : G)) * tg⁻¹ * (g : G)⁻¹ := by group
        _ = (g : G) * ((n : G) * tg) * tg⁻¹ * (g : G)⁻¹ := by rw [hc]
        _ = (g : G) * (n : G) * (g : G)⁻¹ := by group
    rw [e] at h1
    exact Subgroup.mem_subgroupOf.2 h1⟩
  have hI : d.Y ⊓ K₀ ≠ ⊥ := by
    intro hb
    have := h.card_Y_inf_K₀ hKU hf
    rw [hb, Subgroup.card_bot] at this
    omega
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hI
  have hy1' : y ≠ 1 := fun e => hy1 (Subtype.ext e)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Hs with hb | ht
  · exfalso
    have hyHs : (⟨y, hy.2⟩ : ↥K₀) ∈ Hs :=
      Subgroup.mem_subgroupOf.2 (h.Nn_le_Gg hKU hf (h.I₀_le_Nn hKU hf hy))
    rw [hb, Subgroup.mem_bot] at hyHs
    exact hy1' (congrArg Subtype.val hyHs)
  · intro k hk
    have : (⟨k, hk⟩ : ↥K₀) ∈ Hs := ht ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this

include h hKU in
theorem Data.Hyp.nclL_le_Gg
    (hBu : ∀ x ∈ Data.B₁ h hKU hf, d.u * x * d.u⁻¹ ∈ Data.B₁ h hKU hf) :
    d.nclL K₀ ≤ Data.Gg h hKU hf := by
  refine Data.nclL_le fun l hl => ?_
  rintro _ ⟨k, hk, rfl⟩
  show l * k * l⁻¹ ∈ Data.Gg h hKU hf
  exact (mem_normalizer_iff.1 (h.L_le_normalizer_Gg hKU hf hBu hl) k).1
    (h.K₀_le_Gg hKU hf hBu hk)

include h hKU in
theorem Data.Hyp.commutation_of_hBu
    (hBu : ∀ x ∈ Data.B₁ h hKU hf, d.u * x * d.u⁻¹ ∈ Data.B₁ h hKU hf) :
    ⁅d.nclL K₀, (d.nclL K₀).map (MulAut.conj d.t).toMonoidHom⁆ = ⊥ := by
  have hA := h.nclL_le_Gg hKU hf hBu
  have hcomm := h.comm_Gg_tcGg hKU hf hBu
  refine eq_bot_iff.2 (Subgroup.commutator_le.2 fun x hx y hy => ?_)
  exact Subgroup.mem_bot.2 (commutatorElement_eq_one_iff_mul_comm.2
    (hcomm x (hA hx) y (Subgroup.map_mono hA hy)))

end Final

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
