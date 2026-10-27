module

public import CFSG.GH74.GLS.Stage2.Final.L26.Pair

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L20

open Subgroup CFSG CFSG.LocalCores CFSG.GH74.GLS CFSG.GH74.GLS.Bg
open scoped commutatorElement


section Diag

variable {G : Type} [Group G] {K₁ K₂ : Subgroup G} {s : G}

@[expose] def diagHom (K₁ K₂ : Subgroup G) (s : G) (hs : ∀ a ∈ K₁, s * a * s⁻¹ ∈ K₂)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) : ↥K₁ →* G where
  toFun a := (a : G) * (s * a * s⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have h1 := hc b b.2 _ (hs a a.2)
    calc ((a * b : ↥K₁) : G) * (s * ((a * b : ↥K₁) : G) * s⁻¹)
        = (a : G) * (b * (s * a * s⁻¹)) * (s * b * s⁻¹) := by
          simp only [Subgroup.coe_mul]; group
      _ = (a : G) * ((s * a * s⁻¹) * b) * (s * b * s⁻¹) := by rw [h1]
      _ = ((a : G) * (s * a * s⁻¹)) * ((b : G) * (s * b * s⁻¹)) := by group

theorem diagHom_apply (hs : ∀ a ∈ K₁, s * a * s⁻¹ ∈ K₂) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (a : ↥K₁) : diagHom K₁ K₂ s hs hc a = (a : G) * (s * a * s⁻¹) := rfl

theorem diag_centralizes (hperf : ⁅K₁, K₁⁆ = K₁) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hs2 : s * s = 1) (hs₁ : ∀ a ∈ K₁, s * a * s⁻¹ ∈ K₂) (hs₂ : ∀ b ∈ K₂, s * b * s⁻¹ ∈ K₁)
    {I : Subgroup G} (hI : ∀ a ∈ K₁, a * (s * a * s⁻¹) ∈ I)
    {x : G} (hx₁ : ∀ a ∈ K₁, x * a * x⁻¹ ∈ K₁) (hx₂ : ∀ b ∈ K₂, x * b * x⁻¹ ∈ K₂)
    (hxI : ∀ i ∈ I, x * i = i * x) :
    (∀ a ∈ K₁, x * a = a * x) ∧ (∀ b ∈ K₂, x * b = b * x) := by
  have hζ : ∀ a ∈ K₁, a⁻¹ * (x * a * x⁻¹) ∈ K₂ := by
    intro a ha
    have h1 := hxI _ (hI a ha)
    have hb := hs₁ a ha
    have hb' := hx₂ _ hb
    have e : a⁻¹ * (x * a * x⁻¹) = (s * a * s⁻¹) * (x * (s * a * s⁻¹) * x⁻¹)⁻¹ := by
      have h2 : x * (a * (s * a * s⁻¹)) * x⁻¹ = a * (s * a * s⁻¹) := by
        rw [h1]; group
      have h3 : (x * a * x⁻¹) * (x * (s * a * s⁻¹) * x⁻¹) = a * (s * a * s⁻¹) := by
        rw [← h2]; group
      calc a⁻¹ * (x * a * x⁻¹)
          = a⁻¹ * ((x * a * x⁻¹) * (x * (s * a * s⁻¹) * x⁻¹)) * (x * (s * a * s⁻¹) * x⁻¹)⁻¹ := by group
        _ = a⁻¹ * (a * (s * a * s⁻¹)) * (x * (s * a * s⁻¹) * x⁻¹)⁻¹ := by rw [h3]
        _ = (s * a * s⁻¹) * (x * (s * a * s⁻¹) * x⁻¹)⁻¹ := by group
    rw [e]
    exact K₂.mul_mem hb (K₂.inv_mem hb')
  have hζc : ∀ a ∈ K₁, ∀ l ∈ K₁, (a⁻¹ * (x * a * x⁻¹)) * l = l * (a⁻¹ * (x * a * x⁻¹)) :=
    fun a ha l hl => (hc l hl _ (hζ a ha)).symm
  have hcomm : ∀ a ∈ K₁, ∀ b ∈ K₁, x * ⁅a, b⁆ * x⁻¹ = ⁅a, b⁆ := by
    intro a ha b hb
    have e1 : x * a * x⁻¹ = a * (a⁻¹ * (x * a * x⁻¹)) := by group
    have e2 : x * b * x⁻¹ = b * (b⁻¹ * (x * b * x⁻¹)) := by group
    set za := a⁻¹ * (x * a * x⁻¹) with hzadef
    set zb := b⁻¹ * (x * b * x⁻¹) with hzbdef
    have hza : ∀ l ∈ K₁, za * l = l * za := hζc a ha
    have hzb : ∀ l ∈ K₁, zb * l = l * zb := hζc b hb
    have hzaK : za ∈ K₁ := K₁.mul_mem (K₁.inv_mem ha) (hx₁ a ha)
    have hzbK : zb ∈ K₁ := K₁.mul_mem (K₁.inv_mem hb) (hx₁ b hb)
    have key : x * ⁅a, b⁆ * x⁻¹ = ⁅x * a * x⁻¹, x * b * x⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    have hpb : za * b = b * za := hza b hb
    have hpq : za * zb = zb * za := hza zb hzbK
    have hqa : zb * a = a * zb := hzb a ha
    rw [key, e1, e2]
    have hpa' : za * a⁻¹ = a⁻¹ * za := by
      have := hza a⁻¹ (K₁.inv_mem ha); exact this
    have hqa' : zb * a⁻¹ = a⁻¹ * zb := hzb a⁻¹ (K₁.inv_mem ha)
    have hqp' : zb * za⁻¹ = za⁻¹ * zb := by
      have := hzb za⁻¹ (K₁.inv_mem hzaK); exact this
    calc ⁅a * za, b * zb⁆ = a * (za * b) * zb * za⁻¹ * a⁻¹ * zb⁻¹ * b⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = a * (b * za) * zb * za⁻¹ * a⁻¹ * zb⁻¹ * b⁻¹ := by rw [hpb]
      _ = a * b * (za * zb * za⁻¹) * a⁻¹ * zb⁻¹ * b⁻¹ := by group
      _ = a * b * zb * a⁻¹ * zb⁻¹ * b⁻¹ := by
          have : za * zb * za⁻¹ = zb := by rw [hpq]; group
          rw [this]
      _ = a * b * (zb * a⁻¹ * zb⁻¹) * b⁻¹ := by group
      _ = a * b * a⁻¹ * b⁻¹ := by
          have : zb * a⁻¹ * zb⁻¹ = a⁻¹ := by rw [hqa']; group
          rw [this]
      _ = ⁅a, b⁆ := by simp only [commutatorElement_def]
  have hK₁ : ∀ a ∈ K₁, x * a = a * x := by
    have hle : ⁅K₁, K₁⁆ ≤ centralizer ({x} : Set G) := by
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hcomm a ha b hb
      calc ⁅a, b⁆ * x = (x * ⁅a, b⁆ * x⁻¹) * x := by rw [this]
        _ = x * ⁅a, b⁆ := by group
    intro a ha
    have ha' : a ∈ ⁅K₁, K₁⁆ := by rw [hperf]; exact ha
    have : a ∈ centralizer ({x} : Set G) := hle ha'
    exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm
  refine ⟨hK₁, fun b hb => ?_⟩
  have ha := hs₂ b hb
  have hba : s * (s * b * s⁻¹) * s⁻¹ = b := by
    have : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    calc s * (s * b * s⁻¹) * s⁻¹ = (s * s) * b * (s * s)⁻¹ := by group
      _ = b := by rw [hs2]; group
  have h1 := hxI _ (hI _ ha)
  rw [hba] at h1
  have h2 := hK₁ _ ha
  have e : (s * b * s⁻¹) * (x * b) = (s * b * s⁻¹) * (b * x) := by
    calc (s * b * s⁻¹) * (x * b) = ((s * b * s⁻¹) * x) * b := by group
      _ = (x * (s * b * s⁻¹)) * b := by rw [← h2]
      _ = x * ((s * b * s⁻¹) * b) := by group
      _ = ((s * b * s⁻¹) * b) * x := h1
      _ = (s * b * s⁻¹) * (b * x) := by group
  exact mul_left_cancel e



theorem commutator_mul_central {a b p q : G} (hpb : p * b = b * p)
    (hpq : p * q = q * p) (hqa : q * a = a * q) :
    ⁅a * p, b * q⁆ = ⁅a, b⁆ := by
  have hqa' : q * a⁻¹ = a⁻¹ * q := by
    calc q * a⁻¹ = a⁻¹ * (a * q) * a⁻¹ := by group
      _ = a⁻¹ * (q * a) * a⁻¹ := by rw [← hqa]
      _ = a⁻¹ * q := by group
  calc ⁅a * p, b * q⁆ = a * (p * b) * q * p⁻¹ * a⁻¹ * q⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = a * (b * p) * q * p⁻¹ * a⁻¹ * q⁻¹ * b⁻¹ := by rw [hpb]
    _ = a * b * (p * q * p⁻¹) * a⁻¹ * q⁻¹ * b⁻¹ := by group
    _ = a * b * q * a⁻¹ * q⁻¹ * b⁻¹ := by
        have : p * q * p⁻¹ = q := by rw [hpq]; group
        rw [this]
    _ = a * b * (q * a⁻¹ * q⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by
        have : q * a⁻¹ * q⁻¹ = a⁻¹ := by rw [hqa']; group
        rw [this]
    _ = ⁅a, b⁆ := by simp only [commutatorElement_def]


theorem exists_diag_of_fixed (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hs₁ : ∀ a ∈ K₁, s * a * s⁻¹ ∈ K₂) (hs₂ : ∀ b ∈ K₂, s * b * s⁻¹ ∈ K₁)
    {d : G} (hd : d ∈ K₁ ⊔ K₂) (hsd : s * d * s⁻¹ = d) :
    ∃ a ∈ K₁, ∃ ζ ∈ K₁ ⊓ K₂, d = a * (s * a * s⁻¹) * ζ := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := CFSG.GH74.GLS.Stage2.Final.L26.exists_mul_of_mem_sup_of_commute hc hd
  set u := s * k₂ * s⁻¹ with hu
  set v := s * k₁ * s⁻¹ with hv
  have huK : u ∈ K₁ := hs₂ k₂ hk₂
  have hvK : v ∈ K₂ := hs₁ k₁ hk₁
  have h1 : k₁ * k₂ = u * v := by
    calc k₁ * k₂ = s * (k₁ * k₂) * s⁻¹ := hsd.symm
      _ = v * u := by simp only [hu, hv]; group
      _ = u * v := (hc u huK v hvK).symm
  set ζ₀ := u⁻¹ * k₁ with hζ₀
  have hζ₀1 : ζ₀ ∈ K₁ := K₁.mul_mem (K₁.inv_mem huK) hk₁
  have hζ₀e : ζ₀ = v * k₂⁻¹ := by
    calc ζ₀ = u⁻¹ * (k₁ * k₂) * k₂⁻¹ := by simp only [hζ₀]; group
      _ = u⁻¹ * (u * v) * k₂⁻¹ := by rw [h1]
      _ = v * k₂⁻¹ := by group
  have hζ₀2 : ζ₀ ∈ K₂ := hζ₀e ▸ K₂.mul_mem hvK (K₂.inv_mem hk₂)
  refine ⟨k₁, hk₁, ζ₀⁻¹, (K₁ ⊓ K₂).inv_mem ⟨hζ₀1, hζ₀2⟩, ?_⟩
  have hk₂e : k₂ = ζ₀⁻¹ * v := by
    calc k₂ = (v * k₂⁻¹)⁻¹ * v := by group
      _ = ζ₀⁻¹ * v := by rw [← hζ₀e]
  have hcomm : ζ₀⁻¹ * v = v * ζ₀⁻¹ := hc _ (K₁.inv_mem hζ₀1) v hvK
  calc k₁ * k₂ = k₁ * (ζ₀⁻¹ * v) := by rw [← hk₂e]
    _ = k₁ * (v * ζ₀⁻¹) := by rw [hcomm]
    _ = k₁ * (s * k₁ * s⁻¹) * ζ₀⁻¹ := by simp only [hv]; group

theorem central_of_mem_inf (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) {ζ : G} (hζ : ζ ∈ K₁ ⊓ K₂)
    {w : G} (hw : w ∈ K₁ ⊔ K₂) : ζ * w = w * ζ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GH74.GLS.Stage2.Final.L26.exists_mul_of_mem_sup_of_commute hc hw
  have h1 : ζ * a = a * ζ := (hc a ha ζ hζ.2).symm
  have h2 : ζ * b = b * ζ := hc ζ hζ.1 b hb
  calc ζ * (a * b) = (ζ * a) * b := by group
    _ = (a * ζ) * b := by rw [h1]
    _ = a * (ζ * b) := by group
    _ = a * (b * ζ) := by rw [h2]
    _ = a * b * ζ := by group


theorem swap_swap (hs2 : s * s = 1) (a : G) : s * (s * a * s⁻¹) * s⁻¹ = a := by
  calc s * (s * a * s⁻¹) * s⁻¹ = (s * s) * a * (s * s)⁻¹ := by group
    _ = a := by rw [hs2]; group

theorem diagHom_mem (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hs2 : s * s = 1)
    (hs₁ : ∀ a ∈ K₁, s * a * s⁻¹ ∈ K₂) (a : ↥K₁) :
    diagHom K₁ K₂ s hs₁ hc a ∈ (K₁ ⊔ K₂) ⊓ centralizer ({s} : Set G) := by
  refine Subgroup.mem_inf.mpr ⟨(K₁ ⊔ K₂).mul_mem (Subgroup.mem_sup_left a.2) (Subgroup.mem_sup_right (hs₁ a a.2)), ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff, diagHom_apply]
  have h1 : s * ((a : G) * (s * a * s⁻¹)) * s⁻¹ = (a : G) * (s * a * s⁻¹) := by
    calc s * ((a : G) * (s * a * s⁻¹)) * s⁻¹ = (s * a * s⁻¹) * (s * (s * a * s⁻¹) * s⁻¹) := by group
      _ = (s * a * s⁻¹) * a := by rw [swap_swap hs2]
      _ = a * (s * a * s⁻¹) := (hc a a.2 _ (hs₁ a a.2)).symm
  calc (a : G) * (s * a * s⁻¹) * s = (s * ((a : G) * (s * a * s⁻¹)) * s⁻¹) * s := by rw [h1]
    _ = s * ((a : G) * (s * a * s⁻¹)) := by group

theorem diag_le_layer (hq : IsQuasisimple ↥K₁) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hs2 : s * s = 1)
    (hs₁ : ∀ a ∈ K₁, s * a * s⁻¹ ∈ K₂) (hs₂ : ∀ b ∈ K₂, s * b * s⁻¹ ∈ K₁) :
    (diagHom K₁ K₂ s hs₁ hc).range ≤ Em ((K₁ ⊔ K₂) ⊓ centralizer ({s} : Set G)) := by
  set D := (K₁ ⊔ K₂) ⊓ centralizer ({s} : Set G) with hD
  set δ := diagHom K₁ K₂ s hs₁ hc with hδ
  have hΔD : δ.range ≤ D := by
    rintro _ ⟨a, rfl⟩
    exact diagHom_mem hc hs2 hs₁ a
  have hnorm : (δ.range.subgroupOf D).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨a, ha⟩ := hn
    obtain ⟨a₀, ha₀, ζ, hζ, hd⟩ := exists_diag_of_fixed hc hs₁ hs₂ (Subgroup.mem_inf.mp g.2).1
      (by
        have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp g.2).2
        calc s * (g : G) * s⁻¹ = (g : G) * s * s⁻¹ := by rw [← this]
          _ = g := by group)
    set a₀' : ↥K₁ := ⟨a₀, ha₀⟩ with ha₀'
    have hnK : (n : G) ∈ K₁ ⊔ K₂ := (Subgroup.mem_inf.mp n.2).1
    have hζn : ζ * (n : G) = (n : G) * ζ := central_of_mem_inf hc hζ hnK
    have hd' : (g : G) = δ a₀' * ζ := hd
    refine ⟨a₀' * a * a₀'⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, ha]
    show δ a₀' * (n : G) * (δ a₀')⁻¹ = ((g * n * g⁻¹ : ↥D) : G)
    calc δ a₀' * (n : G) * (δ a₀')⁻¹ = δ a₀' * (ζ * n * ζ⁻¹) * (δ a₀')⁻¹ := by
          rw [hζn]; group
      _ = ((g * n * g⁻¹ : ↥D) : G) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hd']; group
  have hker : (δ.rangeRestrict).ker ≤ center ↥K₁ := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have h1 : δ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have h2 : (a : G) ∈ K₂ := by
      have : (a : G) = (s * a * s⁻¹)⁻¹ := by
        have h3 : (a : G) * (s * a * s⁻¹) = 1 := h1
        exact eq_inv_of_mul_eq_one_left h3
      rw [this]; exact K₂.inv_mem (hs₁ a a.2)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2 a h2)
  have hqΔ : IsQuasisimple ↥δ.range :=
    CFSG.LocalCores.isQuasisimple_of_surjective hq δ.rangeRestrict δ.rangeRestrict_surjective hker
  have hqΔ' : IsQuasisimple ↥(δ.range.subgroupOf D) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hΔD).symm hqΔ
  have hcomp : IsComponent (δ.range.subgroupOf D) := ⟨hqΔ', hnorm.isSubnormal⟩
  have hle : δ.range.subgroupOf D ≤ layer ↥D := component_le_layer hcomp
  have := Subgroup.map_mono (f := D.subtype) hle
  rw [Subgroup.map_subgroupOf_eq_of_le hΔD] at this
  exact this


theorem diagHom_mem_sup (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hs₁ : ∀ a ∈ K₁, s * a * s⁻¹ ∈ K₂)
    (a : ↥K₁) : diagHom K₁ K₂ s hs₁ hc a ∈ K₁ ⊔ K₂ :=
  (K₁ ⊔ K₂).mul_mem (Subgroup.mem_sup_left a.2) (Subgroup.mem_sup_right (hs₁ a a.2))

theorem perfect_le_diag (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hs₁ : ∀ a ∈ K₁, s * a * s⁻¹ ∈ K₂) (hs₂ : ∀ b ∈ K₂, s * b * s⁻¹ ∈ K₁)
    {P : Subgroup G} (hP : ⁅P, P⁆ = P) (hPK : P ≤ K₁ ⊔ K₂) (hPs : ∀ p ∈ P, s * p * s⁻¹ = p) :
    P ≤ (diagHom K₁ K₂ s hs₁ hc).range := by
  set δ := diagHom K₁ K₂ s hs₁ hc with hδ
  have hle : ⁅P, P⁆ ≤ δ.range := by
    refine Subgroup.commutator_le.mpr fun p hp p' hp' => ?_
    obtain ⟨a, ha, ζ, hζ, hpe⟩ := exists_diag_of_fixed hc hs₁ hs₂ (hPK hp) (hPs p hp)
    obtain ⟨a', ha', ζ', hζ', hpe'⟩ := exists_diag_of_fixed hc hs₁ hs₂ (hPK hp') (hPs p' hp')
    have hδa : δ ⟨a, ha⟩ ∈ K₁ ⊔ K₂ := (diagHom_mem_sup hc hs₁ ⟨a, ha⟩)
    have hδa' : δ ⟨a', ha'⟩ ∈ K₁ ⊔ K₂ := (diagHom_mem_sup hc hs₁ ⟨a', ha'⟩)
    have hζK : ζ ∈ K₁ ⊔ K₂ := Subgroup.mem_sup_left hζ.1
    have hζ'K : ζ' ∈ K₁ ⊔ K₂ := Subgroup.mem_sup_left hζ'.1
    have e1 : p = δ ⟨a, ha⟩ * ζ := hpe
    have e2 : p' = δ ⟨a', ha'⟩ * ζ' := hpe'
    rw [e1, e2, commutator_mul_central (central_of_mem_inf hc hζ hδa') (central_of_mem_inf hc hζ hζ'K)
      (central_of_mem_inf hc hζ' hδa)]
    exact ⟨⁅(⟨a, ha⟩ : ↥K₁), ⟨a', ha'⟩⁆, map_commutatorElement δ _ _⟩
  intro p hp
  have : p ∈ ⁅P, P⁆ := by rw [hP]; exact hp
  exact hle this

end Diag


end CFSG.GH74.GLS.Stage2.Final.Thm6.L20
