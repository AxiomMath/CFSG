module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.SettingTwo
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckAut
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckA2
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3Fusion

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem η_ι (g : SU52) : d.η ⟨d.ι g, d.ι_mem g⟩ = g := by
  change d.η (d.η.symm g) = g
  exact MulEquiv.apply_symm_apply _ _

omit [Finite G] in
theorem ι_η' {l : G} (hl : l ∈ d.L) : d.ι (d.η ⟨l, hl⟩) = l := by
  rw [Data.ι_η]

omit [Finite G] in
theorem comm_of_mem_centralizer {c l : G} (hc : c ∈ centralizer (d.L : Set G)) (hl : l ∈ d.L) :
    l * c = c * l :=
  mem_centralizer_iff.1 hc l hl

theorem act_ι (h : d.Hyp) (n : SU52) :
    h.act ⟨d.ι n, h.L_le_H (d.ι_mem n)⟩ = MulAut.conj n := by
  rw [h.act_of_mem (d.ι_mem n), η_ι]

omit [Finite G] in
theorem ι_conj (g g' : SU52) : d.ι g * d.ι g' * (d.ι g)⁻¹ = d.ι (g * g' * g⁻¹) := by
  rw [map_mul, map_mul, map_inv]

theorem conj_t_mul_self (h : d.Hyp) (k : G) : k * d.t * k⁻¹ * (k * d.t * k⁻¹) = 1 := by
  calc k * d.t * k⁻¹ * (k * d.t * k⁻¹) = k * (d.t * d.t) * k⁻¹ := by group
    _ = 1 := by rw [h.t_mul_t, mul_one, mul_inv_cancel]

theorem conj_t_ne_one (h : d.Hyp) (k : G) : k * d.t * k⁻¹ ≠ 1 := fun e =>
  h.t_ne_one (by
    calc d.t = k⁻¹ * (k * d.t * k⁻¹) * k := by group
      _ = 1 := by rw [e]; group)

theorem exists_conj_mem_withT_F_of_inner (h : d.Hyp) {s k : G}
    (hs : s = k * d.t * k⁻¹) (hsH : s ∈ d.H) (hst : s ≠ d.t) (hσ : h.fieldFactor ⟨s, hsH⟩ = 1) :
    ∃ g : G, g⁻¹ * d.t * g ∈ d.withT d.F ∧ g⁻¹ * d.t * g ≠ d.t := by
  obtain ⟨l, hl, c, hc, hlc⟩ := (h.fieldFactor_eq_one_iff _).1 hσ
  change s = l * c at hlc
  have hcC : c ∈ centralizer (d.L : Set G) := (Subgroup.mem_inf.1 hc).1
  have hs2 : s * s = 1 := by rw [hs]; exact h.conj_t_mul_self k
  have hcl : l * c = c * l := comm_of_mem_centralizer hcC hl
  have hll : l * l = 1 := by
    have e : l * l = (c * c)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc l * l * (c * c) = l * c * (l * c) := by
            rw [show l * c * (l * c) = l * (c * l) * c by group, ← hcl]; group
        _ = 1 := by rw [← hlc, hs2]
    have hmem : l * l ∈ d.L ⊓ centralizer (d.L : Set G) :=
      Subgroup.mem_inf.2 ⟨mul_mem hl hl, by rw [e]; exact inv_mem (mul_mem hcC hcC)⟩
    rw [h.inf_centralizer_eq_bot, mem_bot] at hmem
    exact hmem
  have hcc : c * c = 1 := by
    have : l * c * (l * c) = 1 := by rw [← hlc, hs2]
    rw [show l * c * (l * c) = (l * l) * (c * c) by
      rw [show l * c * (l * c) = l * (c * l) * c by group, ← hcl]; group, hll, one_mul] at this
    exact this
  have hc' := h.eq_one_or_eq_t_of_mem_kernel hc hcc
  have hl1 : l ≠ 1 := by
    rintro rfl
    rw [one_mul] at hlc
    rcases hc' with rfl | rfl
    · exact h.conj_t_ne_one k (hs ▸ hlc)
    · exact hst hlc
  set σ := d.η ⟨l, hl⟩ with hσdef
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← map_mul]
    rw [show (⟨l, hl⟩ : d.L) * ⟨l, hl⟩ = 1 from Subtype.ext hll, map_one]
  have hσ1 : σ ≠ 1 := fun e => hl1 (by
    rw [← ι_η' hl, ← hσdef, e, map_one])
  obtain ⟨n, hn⟩ := exists_conj_mem_Fsub hσ2
  have hf1 : n * σ * n⁻¹ ≠ 1 := fun e => hσ1 (by
    calc σ = n⁻¹ * (n * σ * n⁻¹) * n := by group
      _ = 1 := by rw [e]; group)
  set m := d.ι n with hm
  have hml : m * l * m⁻¹ = d.ι (n * σ * n⁻¹) := by
    rw [hm, ← ι_conj, hσdef, ι_η']
  have hmc : m * c * m⁻¹ = c := by
    rw [mul_inv_eq_iff_eq_mul]
    exact comm_of_mem_centralizer hcC (d.ι_mem n)
  refine ⟨k⁻¹ * m⁻¹, ?_, ?_⟩
  · have e : (k⁻¹ * m⁻¹)⁻¹ * d.t * (k⁻¹ * m⁻¹) = d.ι (n * σ * n⁻¹) * c := by
      calc (k⁻¹ * m⁻¹)⁻¹ * d.t * (k⁻¹ * m⁻¹) = m * (k * d.t * k⁻¹) * m⁻¹ := by group
        _ = m * l * m⁻¹ * (m * c * m⁻¹) := by rw [← hs, hlc]; group
        _ = d.ι (n * σ * n⁻¹) * c := by rw [hml, hmc]
    rw [e]
    refine mul_mem (mem_sup_left (d.ι_mem_pull_iff.2 hn)) (mem_sup_right ?_)
    rcases hc' with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  · intro e
    have e' : d.ι (n * σ * n⁻¹) * c = d.t := by
      rw [← e]
      calc d.ι (n * σ * n⁻¹) * c = m * l * m⁻¹ * (m * c * m⁻¹) := by rw [hml, hmc]
        _ = m * (l * c) * m⁻¹ := by group
        _ = (k⁻¹ * m⁻¹)⁻¹ * d.t * (k⁻¹ * m⁻¹) := by rw [← hlc, hs]; group
    rcases hc' with rfl | rfl
    · rw [mul_one] at e'
      exact h.t_not_mem_L (e' ▸ d.ι_mem _)
    · have : d.ι (n * σ * n⁻¹) = 1 := by simpa using e'
      exact hf1 (d.ι_injective (this.trans (map_one d.ι).symm))

theorem cSU_ne_one : cSU ≠ 1 := fun e => by
  have h := congrFun (congrFun (congrArg mat e) 3) 0
  rw [mat_cSU, mat_one] at h
  revert h
  simp [Certificates.U52Yamada.cA5, x₃Mat, x₄Mat, Matrix.mul_apply, Fin.sum_univ_five]

theorem exists_conj_eq_t_mul_of_outer
    (h : d.Hyp) {s k : G} (hs : s = k * d.t * k⁻¹)
    (hsH : s ∈ d.H) (hσ : h.fieldFactor ⟨s, hsH⟩ ≠ 1) :
    ∃ g : G, ∃ y ∈ d.L, y ≠ 1 ∧ g * d.t * g⁻¹ = d.t * y := by
  set α := h.act ⟨s, hsH⟩ with hα
  have hαo : UnitaryFiveTwo.fieldFactor α ≠ 1 := hσ
  have hα2 : α * α = 1 := by
    rw [hα, ← map_mul]
    rw [show (⟨s, hsH⟩ : d.H) * ⟨s, hsH⟩ = 1 from Subtype.ext (by
      change s * s = 1
      rw [hs]; exact h.conj_t_mul_self k), map_one]
  obtain ⟨n, hn⟩ := exists_conj_eq_fld hαo hα2
  set m := d.ι n with hm
  have hmH : m ∈ d.H := h.L_le_H (d.ι_mem n)
  set s₁ := m * s * m⁻¹ with hs₁
  have hs₁H : s₁ ∈ d.H := mul_mem (mul_mem hmH hsH) (inv_mem hmH)
  have hact : h.act ⟨s₁, hs₁H⟩ = fld := by
    have e : (⟨s₁, hs₁H⟩ : d.H) = ⟨m, hmH⟩ * ⟨s, hsH⟩ * (⟨m, hmH⟩)⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv, act_ι, ← hα, hn]
  have hconj : ∀ g : SU52, s₁ * d.ι g * s₁⁻¹ = d.ι (fld g) := fun g => by
    rw [← hact, h.ι_act_apply]
  have hs₁2 : s₁⁻¹ = s₁ := by
    rw [inv_eq_iff_mul_eq_one, hs₁, hs]
    calc m * (k * d.t * k⁻¹) * m⁻¹ * (m * (k * d.t * k⁻¹) * m⁻¹) =
        (m * k) * d.t * (m * k)⁻¹ * ((m * k) * d.t * (m * k)⁻¹) := by group
      _ = 1 := h.conj_t_mul_self _
  set l := d.ι yωSU with hl
  have hls : l⁻¹ * s₁ * l = s₁ * d.ι cSU := by
    have e1 : s₁⁻¹ * l⁻¹ * s₁ = d.ι ((fld yωSU)⁻¹) := by
      calc s₁⁻¹ * l⁻¹ * s₁ = s₁ * d.ι yωSU⁻¹ * s₁⁻¹ := by
            rw [hs₁2, hl, map_inv]
        _ = d.ι (fld yωSU⁻¹) := hconj _
        _ = d.ι ((fld yωSU)⁻¹) := by rw [map_inv fld]
    calc l⁻¹ * s₁ * l = s₁ * (s₁⁻¹ * l⁻¹ * s₁) * l := by group
      _ = s₁ * (d.ι ((fld yωSU)⁻¹) * d.ι yωSU) := by rw [e1, hl]; group
      _ = s₁ * d.ι cSU := by rw [← map_mul, fld_yω_inv_mul]
  set k₁ := m * k with hk₁
  have hs₁k : s₁ = k₁ * d.t * k₁⁻¹ := by rw [hs₁, hs, hk₁]; group
  set ψ : SU52 →* G := (MulAut.conj k₁⁻¹).toMonoidHom.comp d.ι with hψ
  have hψ_apply : ∀ g, ψ g = k₁⁻¹ * d.ι g * k₁ := fun g => by
    simp [hψ]
  have hQperf : ⁅P0sub.map ψ, P0sub.map ψ⁆ = P0sub.map ψ := by
    rw [← map_commutator, commutator_P0sub]
  have hQH : P0sub.map ψ ≤ d.H := by
    rintro _ ⟨p, hp, rfl⟩
    rw [hψ_apply]
    have hpf : fld p = p := P0sub_le_CfldSub hp
    have hcomm : d.ι p * s₁ = s₁ * d.ι p := by
      have := hconj p
      rw [hpf, mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    refine mem_centralizer_singleton_iff.2 ?_
    rw [hs₁k] at hcomm
    calc k₁⁻¹ * d.ι p * k₁ * d.t = k₁⁻¹ * (d.ι p * (k₁ * d.t * k₁⁻¹)) * k₁ := by group
      _ = k₁⁻¹ * ((k₁ * d.t * k₁⁻¹) * d.ι p) * k₁ := by rw [hcomm]
      _ = d.t * (k₁⁻¹ * d.ι p * k₁) := by group
  have hQL := h.perfect_le hQperf hQH
  have hcP : cSU ∈ P0sub := subset_closure (Set.mem_insert _ _)
  refine ⟨k₁⁻¹ * l⁻¹ * k₁, ψ cSU, hQL ⟨cSU, hcP, rfl⟩, ?_, ?_⟩
  · rw [hψ_apply]
    intro e
    have : d.ι cSU = 1 := by
      calc d.ι cSU = k₁ * (k₁⁻¹ * d.ι cSU * k₁) * k₁⁻¹ := by group
        _ = 1 := by rw [e]; group
    exact cSU_ne_one (d.ι_injective (this.trans (map_one d.ι).symm))
  · rw [hψ_apply]
    calc k₁⁻¹ * l⁻¹ * k₁ * d.t * (k₁⁻¹ * l⁻¹ * k₁)⁻¹ = k₁⁻¹ * (l⁻¹ * s₁ * l) * k₁ := by
          rw [hs₁k]; group
      _ = k₁⁻¹ * s₁ * k₁ * (k₁⁻¹ * d.ι cSU * k₁) := by rw [hls]; group
      _ = d.t * (k₁⁻¹ * d.ι cSU * k₁) := by rw [hs₁k]; group

theorem exists_conj_mem_withT_F_ne
    (h : d.Hyp) :
    ∃ g : G, g⁻¹ * d.t * g ∈ d.withT d.F ∧ g⁻¹ * d.t * g ≠ d.t := by
  have := h.simple
  obtain ⟨k, hkc, hkt⟩ := U5.exists_conj_ne_commute h.nonab h.t_ne_one h.t_mul_t
  have hsH : k * d.t * k⁻¹ ∈ d.H := mem_centralizer_singleton_iff.2 hkc
  by_cases hσ : h.fieldFactor ⟨k * d.t * k⁻¹, hsH⟩ = 1
  · exact h.exists_conj_mem_withT_F_of_inner rfl hsH hkt hσ
  · obtain ⟨g, y, hyL, hy1, hgy⟩ := h.exists_conj_eq_t_mul_of_outer rfl hsH hσ
    have hyt : d.t * y = y * d.t := (comm_of_mem_centralizer h.t_mem hyL).symm
    have htyH : d.t * y ∈ d.H := mul_mem h.t_mem_H (h.L_le_H hyL)
    refine h.exists_conj_mem_withT_F_of_inner hgy.symm htyH ?_ ?_
    · intro e
      exact hy1 (by simpa using e)
    · refine (h.fieldFactor_eq_one_iff _).2 ⟨y, hyL, d.t, h.t_mem_kernel, ?_⟩
      exact hyt

theorem inf_kernel_eq_bot (h : d.Hyp) {X : Subgroup G} (hX : X ≤ d.L) :
    X ⊓ (centralizer (d.L : Set G) ⊓ d.H) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxX, hxT⟩ := Subgroup.mem_inf.1 hx
  have : x ∈ d.L ⊓ centralizer (d.L : Set G) :=
    Subgroup.mem_inf.2 ⟨hX hxX, (Subgroup.mem_inf.1 hxT).1⟩
  rwa [h.inf_centralizer_eq_bot] at this

omit [Finite G] in
theorem comm_kernel {X : Subgroup G} (hX : X ≤ d.L) :
    ∀ x ∈ X, ∀ c ∈ centralizer (d.L : Set G) ⊓ d.H, x * c = c * x :=
  fun _ hx _ hc => comm_of_mem_centralizer (Subgroup.mem_inf.1 hc).1 (hX hx)

theorem card_sup_kernel (h : d.Hyp) {X : Subgroup G} (hX : X ≤ d.L) :
    Nat.card (X ⊔ (centralizer (d.L : Set G) ⊓ d.H) : Subgroup G) =
      Nat.card X * Nat.card (centralizer (d.L : Set G) ⊓ d.H : Subgroup G) := by
  obtain ⟨hc, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X
    (centralizer (d.L : Set G) ⊓ d.H) (comm_kernel hX)
  rwa [h.inf_kernel_eq_bot hX, card_bot, mul_one] at hc

omit [Finite G] in
theorem mem_sup_kernel_iff [Finite G] {X : Subgroup G} (hX : X ≤ d.L) {y : G} :
    y ∈ X ⊔ (centralizer (d.L : Set G) ⊓ d.H) ↔
      ∃ x ∈ X, ∃ c ∈ centralizer (d.L : Set G) ⊓ d.H, y = x * c := by
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X
    (centralizer (d.L : Set G) ⊓ d.H) (comm_kernel hX)).2
  have e : y ∈ X ⊔ (centralizer (d.L : Set G) ⊓ d.H) ↔
      y ∈ ((X ⊔ (centralizer (d.L : Set G) ⊓ d.H) : Subgroup G) : Set G) := Iff.rfl
  rw [e, hset]
  constructor
  · rintro ⟨x, hx, c, hc, rfl⟩
    exact ⟨x, hx, c, hc, rfl⟩
  · rintro ⟨x, hx, c, hc, rfl⟩
    exact ⟨x, hx, c, hc, rfl⟩

omit [Finite G] in
theorem kernel_le_H : centralizer (d.L : Set G) ⊓ d.H ≤ d.H := inf_le_right

theorem isPGroup_ST (h : d.Hyp) :
    IsPGroup 2 (d.S ⊔ (centralizer (d.L : Set G) ⊓ d.H) : Subgroup G) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h.kernel.2.1
  refine IsPGroup.of_card (n := 10 + k) ?_
  rw [h.card_sup_kernel (X := d.S) (d.pull_le_L _), d.card_S, hk, pow_add]

theorem ST_le_H (h : d.Hyp) : d.S ⊔ (centralizer (d.L : Set G) ⊓ d.H) ≤ d.H :=
  sup_le ((d.pull_le_L _).trans h.L_le_H) kernel_le_H

theorem exists_sylow_Q (h : d.Hyp) : ∃ Q : Subgroup G, IsSylowOf 2 Q d.H ∧
    d.S ⊔ (centralizer (d.L : Set G) ⊓ d.H) ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := (h.isPGroup_ST.comap_subtype (K := d.H)).exists_le_sylow
  refine ⟨(P : Subgroup d.H).map d.H.subtype, ⟨P, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, h.ST_le_H hx⟩, hP hx, rfl⟩

theorem Q_inf_L (_h : d.Hyp) {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hSQ : d.S ≤ Q) :
    Q ⊓ d.L = d.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := (Q ⊓ d.L).comap d.ι with hE
  have hEp : IsPGroup 2 E := (hQ.to_le inf_le_left).comap_of_injective d.ι d.ι_injective
  have hmap : d.pull E = Q ⊓ d.L := by
    rw [Data.pull, hE, map_comap_eq, d.range_ι]
    exact inf_eq_right.2 inf_le_right
  obtain ⟨g, hg⟩ := exists_conj_le_Ssub hEp
  have hc := Subgroup.card_map_of_injective (K := E) (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective
  have hcard : Nat.card (Q ⊓ d.L : Subgroup G) ≤ Nat.card d.S := by
    rw [← hmap, d.card_pull, d.card_S, ← card_Ssub, ← hc]
    exact Subgroup.card_le_of_le hg
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hSQ (d.pull_le_L _)) hcard).symm

theorem mem_ST_of_inner (h : d.Hyp) {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hSTQ : d.S ⊔ (centralizer (d.L : Set G) ⊓ d.H) ≤ Q) {e : G} (heQ : e ∈ Q) (heH : e ∈ d.H)
    (he : h.fieldFactor ⟨e, heH⟩ = 1) : e ∈ d.S ⊔ (centralizer (d.L : Set G) ⊓ d.H) := by
  obtain ⟨l, hl, c, hc, hlc⟩ := (h.fieldFactor_eq_one_iff _).1 he
  change e = l * c at hlc
  have hlQ : l ∈ Q := by
    have : l = e * c⁻¹ := by rw [hlc]; group
    rw [this]
    exact mul_mem heQ (inv_mem (hSTQ (mem_sup_right hc)))
  have hlS : l ∈ d.S := by
    rw [← h.Q_inf_L hQ (le_sup_left.trans hSTQ)]
    exact ⟨hlQ, hl⟩
  rw [hlc]
  exact mul_mem (mem_sup_left hlS) (mem_sup_right hc)

theorem withT_F_comm_A₂T (h : d.Hyp) {z b : G} (hz : z ∈ d.withT d.F)
    (hb : b ∈ d.A₂ ⊔ (centralizer (d.L : Set G) ⊓ d.H)) : z * b = b * z := by
  obtain ⟨a, ha, k, rfl⟩ := h.exists_eq_mul_of_mem_withT_F hz
  obtain ⟨x, hx, c, hc, rfl⟩ := (mem_sup_kernel_iff (d.pull_le_L _)).1 hb
  have hcC := (Subgroup.mem_inf.1 hc).1
  have hcH := (Subgroup.mem_inf.1 hc).2
  have h1 : a * x = x * a := by
    obtain ⟨σ, hσ, rfl⟩ := ha
    obtain ⟨τ, hτ, rfl⟩ := hx
    rw [← map_mul, ← map_mul, Fsub_comm_A₂ hτ hσ]
  have h2 : a * c = c * a := (comm_of_mem_centralizer hcC (h.F_le_L ha))
  have h3 : d.t ^ k * x = x * d.t ^ k :=
    (Commute.zpow_left (comm_of_mem_centralizer h.t_mem (d.pull_le_L _ hx)).symm k).eq
  have h4 : d.t ^ k * c = c * d.t ^ k :=
    (Commute.zpow_left (mem_centralizer_singleton_iff.1 hcH).symm k).eq
  calc a * d.t ^ k * (x * c) = a * (d.t ^ k * x) * c := by group
    _ = a * x * (d.t ^ k * c) := by rw [h3]; group
    _ = x * a * (c * d.t ^ k) := by rw [h1, h4]
    _ = x * (a * c) * d.t ^ k := by group
    _ = x * c * (a * d.t ^ k) := by rw [h2]; group

theorem withT_F_le_A₂T (h : d.Hyp) :
    d.withT d.F ≤ d.A₂ ⊔ (centralizer (d.L : Set G) ⊓ d.H) :=
  sup_le (d.F_le_A₂.trans le_sup_left) (zpowers_le.2 (mem_sup_right h.t_mem_kernel))

theorem mem_A₂T_of_comm_F (h : d.Hyp) {Q : Subgroup G} (hQH : Q ≤ d.H) (hQ : IsPGroup 2 Q)
    (hSTQ : d.S ⊔ (centralizer (d.L : Set G) ⊓ d.H) ≤ Q) {q : G} (hq : q ∈ Q)
    (hqF : ∀ z ∈ d.F, q * z = z * q) : q ∈ d.A₂ ⊔ (centralizer (d.L : Set G) ⊓ d.H) := by
  have hqH := hQH hq
  have hfix : ∀ y ∈ Fsub, h.act ⟨q, hqH⟩ y = y := fun y hy => d.ι_injective (by
    rw [h.ι_act_apply]
    change q * d.ι y * q⁻¹ = d.ι y
    rw [hqF _ (d.ι_mem_pull_iff.2 hy), mul_inv_cancel_right])
  have hσ : h.fieldFactor ⟨q, hqH⟩ = 1 := fieldFactor_eq_one_of_fix_Fsub hfix
  obtain ⟨s, hs, c, hc, rfl⟩ :=
    (mem_sup_kernel_iff (d.pull_le_L _)).1 (h.mem_ST_of_inner hQ hSTQ hq hqH hσ)
  obtain ⟨σ, hσS, rfl⟩ := hs
  have hσF : ∀ z ∈ Fsub, σ * z = z * σ := fun z hz => d.ι_injective (by
    have hcz : d.ι z * c = c * d.ι z := comm_of_mem_centralizer (Subgroup.mem_inf.1 hc).1
      (d.ι_mem z)
    have e := hqF _ (d.ι_mem_pull_iff.2 hz)
    rw [map_mul, map_mul]
    calc d.ι σ * d.ι z = d.ι σ * c * d.ι z * c⁻¹ := by rw [mul_assoc _ c, ← hcz]; group
      _ = d.ι z * (d.ι σ * c) * c⁻¹ := by rw [e]
      _ = d.ι z * d.ι σ := by group)
  exact mul_mem (mem_sup_left (d.ι_mem_pull_iff.2 (mem_A₂sub_of_comm_Fsub hσS hσF)))
    (mem_sup_right hc)

theorem card_A₂T (h : d.Hyp) :
    Nat.card (d.A₂ ⊔ (centralizer (d.L : Set G) ⊓ d.H) : Subgroup G) =
      2 ^ 8 * Nat.card (centralizer (d.L : Set G) ⊓ d.H : Subgroup G) := by
  rw [h.card_sup_kernel (X := d.A₂) (d.pull_le_L _), d.card_A₂]

theorem eq_withT_F_of_inner (h : d.Hyp) {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQH : Q ≤ d.H)
    (hSTQ : d.S ⊔ (centralizer (d.L : Set G) ⊓ d.H) ≤ Q) {E : Subgroup G} (hEQ : E ≤ Q)
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEs : ∀ x ∈ E, x * x = 1)
    (hEcard : Nat.card E = 2 ^ 5) (hin : ∀ e (he : e ∈ E), h.fieldFactor ⟨e, hQH (hEQ he)⟩ = 1) :
    E = d.withT d.F := by
  set D : Subgroup (MulAut SU52) := (E.subgroupOf d.H).map h.act with hD
  set E₁ : Subgroup SU52 := D.comap MulAut.conj with hE₁
  have hdec : ∀ e ∈ E, ∃ σ ∈ Ssub, ∃ c ∈ centralizer (d.L : Set G) ⊓ d.H, e = d.ι σ * c := by
    intro e he
    obtain ⟨s, hs, c, hc, rfl⟩ :=
      (mem_sup_kernel_iff (d.pull_le_L _)).1 (h.mem_ST_of_inner hQ hSTQ (hEQ he) _ (hin e he))
    obtain ⟨σ, hσ, rfl⟩ := hs
    exact ⟨σ, hσ, c, hc, rfl⟩
  have hact_mul : ∀ (σ : SU52) (c : G) (hc : c ∈ centralizer (d.L : Set G) ⊓ d.H)
      (hH : d.ι σ * c ∈ d.H), h.act ⟨d.ι σ * c, hH⟩ = MulAut.conj σ := by
    intro σ c hc hH
    have e : (⟨d.ι σ * c, hH⟩ : d.H) = ⟨d.ι σ, h.L_le_H (d.ι_mem σ)⟩ * ⟨c, hc.2⟩ :=
      Subtype.ext rfl
    rw [e, map_mul, act_ι, (h.act_eq_one_iff _).2 hc.1, mul_one]
  have hDinn : ∀ α ∈ D, ∃ σ ∈ Ssub, α = MulAut.conj σ := by
    rintro _ ⟨⟨e, heH⟩, he, rfl⟩
    obtain ⟨σ, hσ, c, hc, rfl⟩ := hdec e he
    exact ⟨σ, hσ, hact_mul σ c hc heH⟩
  have hE₁S : E₁ ≤ Ssub := by
    intro σ hσ
    obtain ⟨τ, hτ, e⟩ := hDinn _ hσ
    rw [conj_inj.1 e]
    exact hτ
  have hE₁c : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := by
    intro x hx y hy
    obtain ⟨⟨a, haH⟩, ha, hax⟩ := hx
    obtain ⟨⟨b, hbH⟩, hb, hby⟩ := hy
    refine conj_injective ?_
    rw [map_mul, map_mul, ← hax, ← hby, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (hEc a ha b hb))
  have hE₁s : ∀ x ∈ E₁, x * x = 1 := by
    intro x hx
    obtain ⟨⟨a, haH⟩, ha, hax⟩ := hx
    refine conj_injective ?_
    rw [map_mul, ← hax, ← map_mul, map_one]
    rw [show (⟨a, haH⟩ : d.H) * ⟨a, haH⟩ = 1 from Subtype.ext (hEs a ha), map_one]
  have hcardE₁ : Nat.card E₁ = Nat.card D := by
    have hmap : E₁.map MulAut.conj = D := by
      ext α
      constructor
      · rintro ⟨σ, hσ, rfl⟩
        exact hσ
      · intro hα
        obtain ⟨σ, -, rfl⟩ := hDinn α hα
        exact ⟨σ, hα, rfl⟩
    rw [← hmap, Subgroup.card_map_of_injective conj_injective]
  have hcardD : 2 ^ 4 ≤ Nat.card D := by
    set f : E →* MulAut SU52 := h.act.comp (inclusion (hEQ.trans hQH)) with hf
    have hrange : f.range = D := by
      ext α
      constructor
      · rintro ⟨⟨e, he⟩, rfl⟩
        exact ⟨⟨e, hQH (hEQ he)⟩, he, rfl⟩
      · rintro ⟨⟨e, heH⟩, he, rfl⟩
        exact ⟨⟨e, he⟩, rfl⟩
    have hker : Nat.card f.ker ≤ 2 := by
      have hmem : ∀ x : f.ker, ((x : E) : G) ∈ zpowers d.t := by
        intro x
        have hx : h.act ⟨(x : E), hQH (hEQ (x : E).2)⟩ = 1 := x.2
        rw [act_eq_one_iff] at hx
        rcases h.eq_one_or_eq_t_of_mem_kernel ⟨hx, hQH (hEQ (x : E).2)⟩ (hEs _ (x : E).2) with
          e | e
        · rw [e]; exact one_mem _
        · rw [e]; exact mem_zpowers _
      calc Nat.card f.ker ≤ Nat.card (zpowers d.t) :=
            Nat.card_le_card_of_injective (fun x => (⟨((x : E) : G), hmem x⟩ : zpowers d.t))
              fun x y e => Subtype.ext (Subtype.ext (congrArg (fun z : zpowers d.t => (z : G)) e))
        _ = 2 := h.card_zpowers_t
    have hcard := Subgroup.card_ker_mul_card_range f
    rw [hEcard, hrange] at hcard
    have : 2 ^ 5 ≤ 2 * Nat.card D := hcard ▸ Nat.mul_le_mul_right _ hker
    omega
  have hE₁F : E₁ = Fsub := eq_Fsub_of_elemAb_Ssub hE₁S hE₁c hE₁s (by rw [hcardE₁]; exact hcardD)
  have hle : E ≤ d.withT d.F := by
    intro e he
    obtain ⟨σ, -, c, hc, rfl⟩ := hdec e he
    have hσE₁ : σ ∈ E₁ := Subgroup.mem_comap.2
      (Subgroup.mem_map.2 ⟨⟨d.ι σ * c, hQH (hEQ he)⟩, he, hact_mul σ c hc _⟩)
    rw [hE₁F] at hσE₁
    have hσ2 : d.ι σ * d.ι σ = 1 := by rw [← map_mul, Fsub_sq hσE₁, map_one]
    have hcσ : d.ι σ * c = c * d.ι σ := comm_of_mem_centralizer hc.1 (d.ι_mem σ)
    have hcc : c * c = 1 := by
      have e2 := hEs _ he
      calc c * c = d.ι σ * d.ι σ * (c * c) := by rw [hσ2, one_mul]
        _ = d.ι σ * c * (d.ι σ * c) := by rw [show d.ι σ * c * (d.ι σ * c) =
              d.ι σ * (c * d.ι σ) * c by group, ← hcσ]; group
        _ = 1 := e2
    refine mul_mem (mem_sup_left (d.ι_mem_pull_iff.2 hσE₁)) (mem_sup_right ?_)
    rcases h.eq_one_or_eq_t_of_mem_kernel hc hcc with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_withT_F, hEcard])

theorem weakly_closed_A₂T (h : d.Hyp) {Q : Subgroup G}
    (hQ : IsSylowOf 2 Q d.H) (hSTQ : d.S ⊔ (centralizer (d.L : Set G) ⊓ d.H) ≤ Q) (x : G)
    (hx : ∀ r ∈ d.A₂ ⊔ (centralizer (d.L : Set G) ⊓ d.H), x⁻¹ * r * x ∈ Q) :
    ∀ r ∈ d.A₂ ⊔ (centralizer (d.L : Set G) ⊓ d.H), x⁻¹ * r * x ∈
      d.A₂ ⊔ (centralizer (d.L : Set G) ⊓ d.H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQH : Q ≤ d.H := hQ.le
  have hQp : IsPGroup 2 Q := hQ.isPGroup
  set B₀ := d.A₂ ⊔ (centralizer (d.L : Set G) ⊓ d.H) with hB₀
  set B := B₀.map (MulAut.conj x⁻¹).toMonoidHom with hB
  set E := (d.withT d.F).map (MulAut.conj x⁻¹).toMonoidHom with hE
  have hBQ : B ≤ Q := by
    rintro _ ⟨r, hr, rfl⟩
    simpa [MulAut.conj_apply] using hx r hr
  have hEB : E ≤ B := Subgroup.map_mono h.withT_F_le_A₂T
  have hEQ : E ≤ Q := hEB.trans hBQ
  have hconj_comm : ∀ a ∈ d.withT d.F, ∀ b ∈ B₀, (x⁻¹ * a * x) * (x⁻¹ * b * x) =
      (x⁻¹ * b * x) * (x⁻¹ * a * x) := fun a ha b hb => by
    rw [show (x⁻¹ * a * x) * (x⁻¹ * b * x) = x⁻¹ * (a * b) * x by group,
      h.withT_F_comm_A₂T ha hb]
    group
  have hEc : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simpa [MulAut.conj_apply] using hconj_comm a ha b (h.withT_F_le_A₂T hb)
  have hEs : ∀ u ∈ E, u * u = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have ha2 : a * a = 1 := by
      have := (h.isElemAbelian_withT_F).2 a ha
      rwa [sq] at this
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc x⁻¹ * a * x * (x⁻¹ * a * x) = x⁻¹ * (a * a) * x := by group
      _ = 1 := by rw [ha2]; group
  have hEcard : Nat.card E = 2 ^ 5 := by
    rw [hE, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, h.card_withT_F]
  by_cases hin : ∀ e (he : e ∈ E), h.fieldFactor ⟨e, hQH (hEQ he)⟩ = 1
  ·
    have hEF := h.eq_withT_F_of_inner hQp hQH hSTQ hEQ hEc hEs hEcard hin
    intro r hr
    have hrB : x⁻¹ * r * x ∈ B := ⟨r, hr, by simp⟩
    refine h.mem_A₂T_of_comm_F hQH hQp hSTQ (hBQ hrB) fun z hz => ?_
    have hzE : z ∈ E := hEF ▸ mem_sup_left hz
    obtain ⟨a, ha, rfl⟩ := hzE
    simpa [MulAut.conj_apply] using (hconj_comm a ha r hr).symm
  ·
    exfalso
    push Not at hin
    obtain ⟨e, he, heo⟩ := hin
    set D : Subgroup (MulAut SU52) := (B.subgroupOf d.H).map h.act with hD
    have hDp : IsPGroup 2 D := ((hQp.to_le hBQ).comap_subtype).map _
    have heD : h.act ⟨e, hQH (hEQ he)⟩ ∈ D := ⟨⟨e, hQH (hEQ he)⟩, hEB he, rfl⟩
    have he2 : h.act ⟨e, hQH (hEQ he)⟩ * h.act ⟨e, hQH (hEQ he)⟩ = 1 := by
      rw [← map_mul, show (⟨e, hQH (hEQ he)⟩ : d.H) * ⟨e, hQH (hEQ he)⟩ = 1 from
        Subtype.ext (hEs e he), map_one]
    have hcD : ∀ y ∈ D, y * h.act ⟨e, hQH (hEQ he)⟩ = h.act ⟨e, hQH (hEQ he)⟩ * y := by
      rintro _ ⟨⟨b, hbH⟩, hb, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      refine Subtype.ext ?_
      change b * e = e * b
      obtain ⟨r, hr, rfl⟩ := hb
      obtain ⟨a, ha, rfl⟩ := he
      simpa [MulAut.conj_apply] using hconj_comm a ha r hr |>.symm
    have hle := card_le_of_centralize_outer hDp heD heo he2 hcD
    set f : B →* MulAut SU52 := h.act.comp (inclusion (hBQ.trans hQH)) with hf
    have hrange : f.range = D := by
      ext α
      constructor
      · rintro ⟨⟨b, hb⟩, rfl⟩
        exact ⟨⟨b, hQH (hBQ hb)⟩, hb, rfl⟩
      · rintro ⟨⟨b, hbH⟩, hb, rfl⟩
        exact ⟨⟨b, hb⟩, rfl⟩
    have hker : Nat.card f.ker ≤ Nat.card (centralizer (d.L : Set G) ⊓ d.H : Subgroup G) := by
      refine Nat.card_le_card_of_injective (fun y => (⟨((y : B) : G), ?_⟩ :
        (centralizer (d.L : Set G) ⊓ d.H : Subgroup G))) fun y z e => ?_
      · have hy : h.act ⟨(y : B), hQH (hBQ (y : B).2)⟩ = 1 := y.2
        exact ⟨(act_eq_one_iff _ _).1 hy, hQH (hBQ (y : B).2)⟩
      · exact Subtype.ext (Subtype.ext (congrArg (fun w : (centralizer (d.L : Set G) ⊓ d.H :
          Subgroup G) => (w : G)) e))
    have hBcard : Nat.card B = 2 ^ 8 * Nat.card (centralizer (d.L : Set G) ⊓ d.H : Subgroup G) := by
      rw [hB, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, h.card_A₂T]
    have hcard := Subgroup.card_ker_mul_card_range f
    rw [hrange, hBcard] at hcard
    have hT0 : 0 < Nat.card (centralizer (d.L : Set G) ⊓ d.H : Subgroup G) := Nat.card_pos
    have : 2 ^ 8 * Nat.card (centralizer (d.L : Set G) ⊓ d.H : Subgroup G) ≤
        Nat.card (centralizer (d.L : Set G) ⊓ d.H : Subgroup G) * 2 ^ 5 :=
      hcard ▸ Nat.mul_le_mul hker hle
    nlinarith

theorem exists_normalizer_A₂T_conj_eq (h : d.Hyp) {g : G}
    (hg : g⁻¹ * d.t * g ∈ d.withT d.F) :
    ∃ n ∈ normalizer ((d.A₂ ⊔ (centralizer (d.L : Set G) ⊓ d.H) : Subgroup G) : Set G),
      n⁻¹ * d.t * n = g⁻¹ * d.t * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ, hSTQ⟩ := h.exists_sylow_Q
  have hA₂TQ : d.A₂ ⊔ (centralizer (d.L : Set G) ⊓ d.H) ≤ Q :=
    sup_le ((d.pull_mono A₂sub_le_Ssub).trans (le_sup_left.trans hSTQ)) (le_sup_right.trans hSTQ)
  exact U5.exists_normalizer_conj_eq_of_weakly_closed_in (x := d.t) hQ hA₂TQ
    (fun c hc => h.weakly_closed_A₂T hQ hSTQ c hc)
    (fun r hr => (h.withT_F_comm_A₂T hg hr).symm)

omit [Finite G] in
theorem conj_central_of_mem_normalizer {B : Subgroup G} {n z : G}
    (hn : n ∈ normalizer (B : Set G)) (hz : ∀ b ∈ B, z * b = b * z) :
    ∀ b ∈ B, n⁻¹ * z * n * b = b * (n⁻¹ * z * n) := by
  intro b hb
  have hb' : n * b * n⁻¹ ∈ B := (mem_normalizer_iff.1 hn b).1 hb
  have := hz _ hb'
  calc n⁻¹ * z * n * b = n⁻¹ * (z * (n * b * n⁻¹)) * n := by group
    _ = n⁻¹ * ((n * b * n⁻¹) * z) * n := by rw [this]
    _ = b * (n⁻¹ * z * n) := by group

theorem normalizer_le_H_of_two_lt (h : d.Hyp)
    (hT : 2 < Nat.card (centralizer (d.L : Set G) ⊓ d.H : Subgroup G)) :
    normalizer ((d.A₂ ⊔ (centralizer (d.L : Set G) ⊓ d.H) : Subgroup G) : Set G) ≤ d.H := by
  obtain ⟨hcyc, hp, huniq, -⟩ := h.kernel
  set T := (centralizer (d.L : Set G) ⊓ d.H : Subgroup G) with hTdef
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
  have hk2 : 2 ≤ k := by
    by_contra hlt
    interval_cases k <;> simp_all
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := T)
  have hoτ : orderOf τ = 2 ^ k := by rw [orderOf_eq_card_of_forall_mem_zpowers hτ, hk]
  set τ' : T := τ ^ 2 ^ (k - 2) with hτ'
  have ht : ((τ' ^ 2 : T) : G) = d.t := by
    refine huniq _ (τ' ^ 2).2 ?_
    rw [Subgroup.orderOf_coe, hτ', ← pow_mul, ← pow_succ]
    have e : k - 2 + 1 = k - 1 := by omega
    rw [e, orderOf_pow_of_dvd (by positivity) (by rw [hoτ]; exact pow_dvd_pow 2 (by omega)), hoτ]
    rw [show 2 ^ k = 2 ^ (k - 1) * 2 by rw [← pow_succ]; congr 1; omega,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hcen : ∀ b ∈ d.A₂ ⊔ T, (τ' : G) * b = b * τ' := by
    intro b hb
    obtain ⟨a, ha, c, hc, rfl⟩ := (mem_sup_kernel_iff (d.pull_le_L _)).1 hb
    have h1 : (τ' : G) * a = a * τ' :=
      (comm_of_mem_centralizer (Subgroup.mem_inf.1 τ'.2).1 (d.pull_le_L _ ha)).symm
    have h2 : (τ' : G) * c = c * τ' := by
      have := hcyc.isMulCommutative.is_comm.comm τ' ⟨c, hc⟩
      exact congrArg Subtype.val this
    calc (τ' : G) * (a * c) = a * (τ' * c) := by rw [← mul_assoc, h1, mul_assoc]
      _ = a * c * τ' := by rw [h2, mul_assoc]
  intro n hn
  set w := n⁻¹ * (τ' : G) * n with hw
  have hwB : w ∈ d.A₂ ⊔ T := by
    have := (mem_normalizer_iff.1 (inv_mem hn) (τ' : G)).1 (mem_sup_right τ'.2)
    simpa [hw] using this
  have hwc := conj_central_of_mem_normalizer hn hcen
  obtain ⟨a, ha, c, hc, hac⟩ := (mem_sup_kernel_iff (d.pull_le_L _)).1 hwB
  have hcomm_ac : a * c = c * a := comm_of_mem_centralizer (Subgroup.mem_inf.1 hc).1
    (d.pull_le_L _ ha)
  have ha_cen : ∀ b ∈ d.A₂, a * b = b * a := by
    intro b hb
    have hcb : c * b = b * c :=
      (comm_of_mem_centralizer (Subgroup.mem_inf.1 hc).1 (d.pull_le_L _ hb)).symm
    have e := hwc b (mem_sup_left hb)
    rw [← hw, hac] at e
    calc a * b = a * b * c * c⁻¹ := by group
      _ = a * (c * b) * c⁻¹ := by rw [hcb]; group
      _ = b * (a * c) * c⁻¹ := by rw [← mul_assoc, e]
      _ = b * a := by group
  obtain ⟨α, hα, rfl⟩ := ha
  have hαF : α ∈ Fsub := mem_Fsub_of_central hα fun β hβ => d.ι_injective (by
    rw [map_mul, map_mul]
    exact (ha_cen _ (d.ι_mem_pull_iff.2 hβ)).symm)
  have ha2 : d.ι α * d.ι α = 1 := by rw [← map_mul, Fsub_sq hαF, map_one]
  have hnt : n⁻¹ * d.t * n = c * c := by
    rw [← ht]
    calc n⁻¹ * ((τ' ^ 2 : T) : G) * n = w * w := by
          rw [hw, Subgroup.coe_pow, sq]; group
      _ = d.ι α * d.ι α * (c * c) := by
          rw [hac, show d.ι α * c * (d.ι α * c) = d.ι α * (c * d.ι α) * c by group,
            ← hcomm_ac]; group
      _ = c * c := by rw [ha2, one_mul]
  have hcc : c * c ∈ T := mul_mem hc hc
  have ho : orderOf (n⁻¹ * d.t * n) = 2 := by
    rw [show n⁻¹ * d.t * n = n⁻¹ * d.t * n⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
      MulEquiv.orderOf_eq, h.t_two]
  have hnt' : n⁻¹ * d.t * n = d.t := huniq _ (hnt ▸ hcc) ho
  refine mem_centralizer_singleton_iff.2 ?_
  calc n * d.t = n * (n⁻¹ * d.t * n) := by rw [hnt']
    _ = d.t * n := by group

theorem centralizer_inf_H_eq
    (h : d.Hyp) :
    centralizer (d.L : Set G) ⊓ d.H = zpowers d.t := by
  have ht : zpowers d.t ≤ centralizer (d.L : Set G) ⊓ d.H := zpowers_le.2 h.t_mem_kernel
  by_contra hne
  have hT2 : 2 < Nat.card (centralizer (d.L : Set G) ⊓ d.H : Subgroup G) := by
    have h2 : 2 ∣ Nat.card (centralizer (d.L : Set G) ⊓ d.H : Subgroup G) :=
      h.card_zpowers_t ▸ Subgroup.card_dvd_of_le ht
    have hne2 : Nat.card (centralizer (d.L : Set G) ⊓ d.H : Subgroup G) ≠ 2 := fun e =>
      hne (Subgroup.eq_of_le_of_card_ge ht (by rw [e, h.card_zpowers_t])).symm
    have hpos : 0 < Nat.card (centralizer (d.L : Set G) ⊓ d.H : Subgroup G) := Nat.card_pos
    obtain ⟨m, hm⟩ := h2
    omega
  obtain ⟨g, hgF, hgt⟩ := h.exists_conj_mem_withT_F_ne
  obtain ⟨n, hn, hng⟩ := h.exists_normalizer_A₂T_conj_eq hgF
  have hnH := mem_centralizer_singleton_iff.1 (h.normalizer_le_H_of_two_lt hT2 hn)
  apply hgt
  rw [← hng]
  calc n⁻¹ * d.t * n = n⁻¹ * (n * d.t) := by rw [mul_assoc, hnH]
    _ = d.t := by group

theorem isSylowOf_zpowers_t
    (h : d.Hyp) :
    IsSylowOf 2 (zpowers d.t) (centralizer (d.L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tc : centralizer (d.L : Set G) := ⟨d.t, h.t_mem⟩ with htc
  have hz : IsPGroup 2 (zpowers tc) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ← orderOf_coe, pow_one]; exact h.t_two)
  obtain ⟨P, hPt⟩ := hz.exists_le_sylow
  have htP : tc ∈ P := hPt (mem_zpowers _)
  have hPc := h.isCyclic_sylow P
  refine ⟨P, le_antisymm ?_ ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [← h.centralizer_inf_H_eq]
    refine ⟨y.2, mem_centralizer_singleton_iff.2 ?_⟩
    have := hPc.isMulCommutative.is_comm.comm ⟨y, hy⟩ ⟨tc, htP⟩
    exact congrArg (fun z : (P : Subgroup (centralizer (d.L : Set G))) => ((z : _) : G)) this
  · rw [zpowers_le]
    exact ⟨tc, htP, rfl⟩

theorem index_L_dvd_four
    (h : d.Hyp) : d.L.relIndex d.H ∣ 4 := by
  have hK : d.L ≤ d.L ⊔ (centralizer (d.L : Set G) ⊓ d.H) := le_sup_left
  have hKH : d.L ⊔ (centralizer (d.L : Set G) ⊓ d.H) ≤ d.H := sup_le h.L_le_H kernel_le_H
  have h1 := Subgroup.relIndex_mul_relIndex d.L _ d.H hK hKH
  have h2 : d.L.relIndex (d.L ⊔ (centralizer (d.L : Set G) ⊓ d.H)) = 2 := by
    have hc : Nat.card (d.L ⊔ (centralizer (d.L : Set G) ⊓ d.H) : Subgroup G) =
        2 * Nat.card d.L := by
      rw [h.card_sup_kernel le_rfl, h.centralizer_inf_H_eq, h.card_zpowers_t, mul_comm]
    have e := Subgroup.relIndex_mul_card d.L (d.L ⊔ (centralizer (d.L : Set G) ⊓ d.H))
    rw [inf_eq_left.2 hK, hc] at e
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos e
  have h3 := h.index_le_two
  rw [← h1, h2]
  have h4 : (d.L ⊔ (centralizer (d.L : Set G) ⊓ d.H)).relIndex d.H ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  change (d.L ⊔ (centralizer (d.L : Set G) ⊓ d.H)).relIndex d.H ≤ 2 at h3
  interval_cases hr : (d.L ⊔ (centralizer (d.L : Set G) ⊓ d.H)).relIndex d.H
  · exact absurd rfl h4
  · norm_num
  · norm_num

theorem commutator_mem_L
    (h : d.Hyp) {x y : G} (hx : x ∈ d.H) (hy : y ∈ d.H) :
    ⁅x, y⁆ ∈ d.L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.normal_subgroupOf
  set N := d.L.subgroupOf d.H with hN
  have hcard : Nat.card (d.H ⧸ N) ∣ 4 := by
    rw [← Subgroup.index_eq_card]
    exact h.index_L_dvd_four
  have hcomm : ∀ a b : d.H ⧸ N, a * b = b * a := by
    have h4 : Nat.card (d.H ⧸ N) ∈ ({1, 2, 4} : Finset ℕ) := by
      have := Nat.le_of_dvd (by norm_num) hcard
      interval_cases e : Nat.card (d.H ⧸ N) <;> simp_all
    simp only [Finset.mem_insert, Finset.mem_singleton] at h4
    rcases h4 with h1 | h2 | h4
    · intro a b
      have : Subsingleton (d.H ⧸ N) := (Nat.card_eq_one_iff_unique.1 h1).1
      exact Subsingleton.elim _ _
    · have := isCyclic_of_prime_card (p := 2) h2
      exact fun a b => this.isMulCommutative.is_comm.comm a b
    · exact fun a b => (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
        (by rw [h4]; norm_num)).is_comm.comm a b
  have e : QuotientGroup.mk' N ⁅(⟨x, hx⟩ : d.H), ⟨y, hy⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, mem_subgroupOf] at e
  exact e

theorem conj_t_not_mem_L
    (h : d.Hyp) (g : G) : g⁻¹ * d.t * g ∉ d.L := by
  intro hx
  set x := g⁻¹ * d.t * g with hxdef
  set σ := d.η ⟨x, hx⟩ with hσ
  have hx2 : x * x = 1 := by
    rw [hxdef, show g⁻¹ * d.t * g * (g⁻¹ * d.t * g) = g⁻¹ * (d.t * d.t) * g by group, h.t_mul_t]
    group
  have hσ2 : σ * σ = 1 := by
    rw [hσ, ← map_mul, show (⟨x, hx⟩ : d.L) * ⟨x, hx⟩ = 1 from Subtype.ext hx2, map_one]
  have hσ1 : σ ≠ 1 := fun e => by
    have : x = 1 := by rw [← ι_η' hx, ← hσ, e, map_one]
    rw [hxdef] at this
    exact h.conj_t_ne_one g⁻¹ (by rw [inv_inv]; exact this)
  obtain ⟨a, b, ha, hb, hab⟩ := exists_commutator_eq_of_sq hσ2 hσ1
  have hιx : d.ι σ = x := ι_η' hx
  have hcomm : ∀ c : SU52, c * σ = σ * c → g * d.ι c * g⁻¹ ∈ d.H := by
    intro c hc
    refine mem_centralizer_singleton_iff.2 ?_
    have e : d.ι c * x = x * d.ι c := by rw [← hιx, ← map_mul, hc, map_mul]
    rw [hxdef] at e
    calc g * d.ι c * g⁻¹ * d.t = g * (d.ι c * (g⁻¹ * d.t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * d.t * g) * d.ι c) * g⁻¹ := by rw [e]
      _ = d.t * (g * d.ι c * g⁻¹) := by group
  have ht : d.t = ⁅g * d.ι a * g⁻¹, g * d.ι b * g⁻¹⁆ := by
    rw [commutatorElement_def]
    have e : d.ι a * d.ι b * (d.ι a)⁻¹ * (d.ι b)⁻¹ = x := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← commutatorElement_def, hab,
        hιx]
    calc d.t = g * x * g⁻¹ := by rw [hxdef]; group
      _ = g * (d.ι a * d.ι b * (d.ι a)⁻¹ * (d.ι b)⁻¹) * g⁻¹ := by rw [e]
      _ = _ := by group
  exact h.t_not_mem_L (ht ▸ h.commutator_mem_L (hcomm a ha) (hcomm b hb))

theorem A₂T_eq
    (h : d.Hyp) :
    d.A₂ ⊔ (centralizer (d.L : Set G) ⊓ d.H) = d.withT d.A₂ := by
  rw [h.centralizer_inf_H_eq]
  rfl

theorem mem_center_A₂t_iff
    (h : d.Hyp) {z : G} :
    (z ∈ d.withT d.A₂ ∧ ∀ p ∈ d.withT d.A₂, z * p = p * z) ↔ z ∈ d.withT d.F := by
  constructor
  · rintro ⟨hz, hzc⟩
    rw [← h.A₂T_eq] at hz hzc
    obtain ⟨a, ha, c, hc, rfl⟩ := (mem_sup_kernel_iff (d.pull_le_L _)).1 hz
    have ha_cen : ∀ b ∈ d.A₂, a * b = b * a := by
      intro b hb
      have hcb : c * b = b * c :=
        (comm_of_mem_centralizer (Subgroup.mem_inf.1 hc).1 (d.pull_le_L _ hb)).symm
      have e := hzc b (mem_sup_left hb)
      calc a * b = a * b * c * c⁻¹ := by group
        _ = a * (c * b) * c⁻¹ := by rw [hcb]; group
        _ = b * (a * c) * c⁻¹ := by rw [← mul_assoc, e]
        _ = b * a := by group
    obtain ⟨α, hα, rfl⟩ := ha
    have hαF : α ∈ Fsub := mem_Fsub_of_central hα fun β hβ => d.ι_injective (by
      rw [map_mul, map_mul]
      exact (ha_cen _ (d.ι_mem_pull_iff.2 hβ)).symm)
    rw [h.centralizer_inf_H_eq] at hc
    exact mul_mem (mem_sup_left (d.ι_mem_pull_iff.2 hαF)) (mem_sup_right hc)
  · intro hz
    have h1 := h.withT_F_le_A₂T hz
    rw [h.A₂T_eq] at h1
    refine ⟨h1, fun p hp => ?_⟩
    rw [← h.A₂T_eq] at hp
    exact h.withT_F_comm_A₂T hz hp

theorem normalizer_A₂t_le
    (h : d.Hyp) :
    normalizer ((d.withT d.A₂ : Subgroup G) : Set G) ≤
      normalizer ((d.withT d.F : Subgroup G) : Set G) := by
  intro n hn
  have key : ∀ m ∈ normalizer ((d.withT d.A₂ : Subgroup G) : Set G), ∀ z ∈ d.withT d.F,
      m * z * m⁻¹ ∈ d.withT d.F := by
    intro m hm z hz
    obtain ⟨hzA, hzc⟩ := (h.mem_center_A₂t_iff).2 hz
    refine (h.mem_center_A₂t_iff).1 ⟨(mem_normalizer_iff.1 hm z).1 hzA, ?_⟩
    have := conj_central_of_mem_normalizer (inv_mem hm) hzc
    simpa using this
  refine mem_normalizer_iff.2 fun z => ⟨key n hn z, fun hz => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ hz
  simpa [mul_assoc] using this

theorem exists_normalizer_conj_eq
    (h : d.Hyp) {g : G} (hg : g⁻¹ * d.t * g ∈ d.withT d.F) :
    ∃ n ∈ normalizer ((d.withT d.A₂ : Subgroup G) : Set G), n⁻¹ * d.t * n = g⁻¹ * d.t * g := by
  obtain ⟨n, hn, hng⟩ := h.exists_normalizer_A₂T_conj_eq hg
  rw [h.A₂T_eq] at hn
  exact ⟨n, hn, hng⟩

theorem conj_mem_F_mul_t
    (h : d.Hyp) {g : G} (hg : g⁻¹ * d.t * g ∈ d.withT d.F) :
    ∃ a ∈ d.F, g⁻¹ * d.t * g = a * d.t := by
  obtain ⟨a, ha, k, hk⟩ := h.exists_eq_mul_of_mem_withT_F hg
  have hk' : d.t ^ k = d.t ^ (k % 2) := by
    rw [← zpow_mod_orderOf, h.t_two]
    norm_cast
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [hk', h0, zpow_zero, mul_one] at hk
    exact absurd (hk ▸ h.F_le_L ha) (h.conj_t_not_mem_L g)
  · rw [hk', h1, zpow_one] at hk
    exact ⟨a, ha, hk⟩

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
