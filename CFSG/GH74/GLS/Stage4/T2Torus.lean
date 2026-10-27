module

public import CFSG.GH74.GLS.Stage4.T2SL2A
public import CFSG.GH74.GLS.Stage4.T2SL2B
public import CFSG.GH74.GLS.Stage4.RestSetup

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T2

open CFSG.GH74.GLS.Stage4.Hex Subgroup

section Torus

variable {G : Type} [Group G] {F₁ F₂ : Type} [Field F₁] [Field F₂]

@[expose] def sqExt (M : Subgroup G) (s : G) (hc : ∀ m ∈ M, s * m = m * s) (hs : s * s ∈ M) : Subgroup G where
  carrier := {x | x ∈ M ∨ ∃ m ∈ M, x = m * s}
  one_mem' := Or.inl M.one_mem
  mul_mem' := by
    rintro x y (hx | ⟨m, hm, rfl⟩) (hy | ⟨m', hm', rfl⟩)
    · exact Or.inl (M.mul_mem hx hy)
    · exact Or.inr ⟨x * m', M.mul_mem hx hm', by rw [mul_assoc]⟩
    · refine Or.inr ⟨m * y, M.mul_mem hm hy, ?_⟩
      calc m * s * y = m * (s * y) := by rw [mul_assoc]
        _ = m * (y * s) := by rw [hc y hy]
        _ = m * y * s := by rw [mul_assoc]
    · refine Or.inl ?_
      have : m * s * (m' * s) = (m * m') * (s * s) := by
        calc m * s * (m' * s) = m * (s * m') * s := by group
          _ = m * (m' * s) * s := by rw [hc m' hm']
          _ = (m * m') * (s * s) := by group
      rw [this]
      exact M.mul_mem (M.mul_mem hm hm') hs
  inv_mem' := by
    rintro x (hx | ⟨m, hm, rfl⟩)
    · exact Or.inl (M.inv_mem hx)
    · refine Or.inr ⟨m⁻¹ * (s * s)⁻¹, M.mul_mem (M.inv_mem hm) (M.inv_mem hs), ?_⟩
      have h1 : s⁻¹ * m⁻¹ = m⁻¹ * s⁻¹ := by
        have := hc m⁻¹ (M.inv_mem hm)
        calc s⁻¹ * m⁻¹ = s⁻¹ * (m⁻¹ * s) * s⁻¹ := by group
          _ = s⁻¹ * (s * m⁻¹) * s⁻¹ := by rw [this]
          _ = m⁻¹ * s⁻¹ := by group
      calc (m * s)⁻¹ = s⁻¹ * m⁻¹ := by group
        _ = m⁻¹ * s⁻¹ := h1
        _ = m⁻¹ * (s * s)⁻¹ * s := by group

theorem mem_sup_zpowers_iff_of_commute {M : Subgroup G} {s : G} (hc : ∀ m ∈ M, s * m = m * s)
    (hs : s * s ∈ M) {x : G} : x ∈ M ⊔ Subgroup.zpowers s ↔ x ∈ M ∨ ∃ m ∈ M, x = m * s := by
  constructor
  · intro hx
    have hle : M ⊔ Subgroup.zpowers s ≤ sqExt M s hc hs := by
      refine sup_le (fun m hm => Or.inl hm) ?_
      rw [Subgroup.zpowers_le]
      exact Or.inr ⟨1, M.one_mem, by rw [one_mul]⟩
    exact hle hx
  · rintro (hx | ⟨m, hm, rfl⟩)
    · exact Subgroup.mem_sup_left hx
    · exact Subgroup.mul_mem_sup hm (Subgroup.mem_zpowers s)

end Torus

section TorusData

variable {G : Type} [Group G] {F₁ F₂ : Type} [Field F₁] [Field F₂]

structure TorusData (φ₁ : SL2 F₁ →* G) (φ₂ : SL2 F₂ →* G) (s : G) (d₁ : F₁ˣ) (d₂ : F₂ˣ) : Prop where
  inj₁ : Function.Injective φ₁
  inj₂ : Function.Injective φ₂
  comm : ∀ a b, φ₁ a * φ₂ b = φ₂ b * φ₁ a
  zeq : φ₁ (negOne F₁) = φ₂ (negOne F₂)
  inter : ∀ g, g ∈ φ₁.range → g ∈ φ₂.range → g = 1 ∨ g = φ₁ (negOne F₁)
  act₁ : ∀ x, s * φ₁ x * s⁻¹ = φ₁ (slConj (diagGL 1 d₁) x)
  act₂ : ∀ x, s * φ₂ x * s⁻¹ = φ₂ (slConj (diagGL 1 d₂) x)
  ss : s * s = φ₁ (sl2D (-d₁⁻¹)) * φ₂ (sl2D (-d₂⁻¹))
  nsq₁ : ¬ IsSquare (d₁ : F₁)

@[expose] def Hm (φ₁ : SL2 F₁ →* G) (φ₂ : SL2 F₂ →* G) : Subgroup G :=
  (tSub F₁).map φ₁ ⊔ (tSub F₂).map φ₂

variable {φ₁ : SL2 F₁ →* G} {φ₂ : SL2 F₂ →* G} {s : G} {d₁ : F₁ˣ} {d₂ : F₂ˣ}

namespace TorusData

variable (h : TorusData φ₁ φ₂ s d₁ d₂)
include h

theorem comm' : ∀ x ∈ (tSub F₁).map φ₁, ∀ y ∈ (tSub F₂).map φ₂, x * y = y * x := by
  rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
  exact h.comm a b

theorem mem_Hm {x : G} :
    x ∈ Hm φ₁ φ₂ ↔ ∃ a ∈ tSub F₁, ∃ b ∈ tSub F₂, x = φ₁ a * φ₂ b := by
  rw [Hm, mem_sup_iff_of_comm h.comm']
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩

theorem Hm_comm : ∀ x ∈ Hm φ₁ φ₂, ∀ y ∈ Hm φ₁ φ₂, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (h.mem_Hm).1 hx
  obtain ⟨a', ha', b', hb', rfl⟩ := (h.mem_Hm).1 hy
  calc φ₁ a * φ₂ b * (φ₁ a' * φ₂ b') = φ₁ a * (φ₂ b * φ₁ a') * φ₂ b' := by group
    _ = φ₁ a * (φ₁ a' * φ₂ b) * φ₂ b' := by rw [← h.comm a' b]
    _ = φ₁ (a * a') * φ₂ (b * b') := by simp [map_mul, mul_assoc]
    _ = φ₁ (a' * a) * φ₂ (b' * b) := by rw [tSub_comm a ha a' ha', tSub_comm b hb b' hb']
    _ = φ₁ a' * φ₂ b' * (φ₁ a * φ₂ b) := by
        simp only [map_mul]
        calc φ₁ a' * φ₁ a * (φ₂ b' * φ₂ b) = φ₁ a' * (φ₁ a * φ₂ b') * φ₂ b := by group
          _ = φ₁ a' * (φ₂ b' * φ₁ a) * φ₂ b := by rw [h.comm a b']
          _ = _ := by group

theorem s_comm_Hm : ∀ m ∈ Hm φ₁ φ₂, s * m = m * s := by
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := (h.mem_Hm).1 hm
  have h1 : s * φ₁ a * s⁻¹ = φ₁ a := by rw [h.act₁, slConj_diag_tSub 1 d₁ a ha]
  have h2 : s * φ₂ b * s⁻¹ = φ₂ b := by rw [h.act₂, slConj_diag_tSub 1 d₂ b hb]
  have e1 : s * φ₁ a = φ₁ a * s := by
    have := congrArg (· * s) h1
    simpa [mul_assoc] using this
  have e2 : s * φ₂ b = φ₂ b * s := by
    have := congrArg (· * s) h2
    simpa [mul_assoc] using this
  calc s * (φ₁ a * φ₂ b) = (s * φ₁ a) * φ₂ b := by group
    _ = φ₁ a * (s * φ₂ b) := by rw [e1]; group
    _ = φ₁ a * (φ₂ b * s) := by rw [e2]
    _ = φ₁ a * φ₂ b * s := by group

theorem ss_mem : s * s ∈ Hm φ₁ φ₂ := by
  rw [h.mem_Hm]
  exact ⟨_, sl2D_mem_tSub _, _, sl2D_mem_tSub _, h.ss⟩

theorem mem_Hg {x : G} :
    x ∈ Hm φ₁ φ₂ ⊔ Subgroup.zpowers s ↔ x ∈ Hm φ₁ φ₂ ∨ ∃ m ∈ Hm φ₁ φ₂, x = m * s :=
  mem_sup_zpowers_iff_of_commute h.s_comm_Hm h.ss_mem

theorem Hg_comm : ∀ x ∈ Hm φ₁ φ₂ ⊔ Subgroup.zpowers s, ∀ y ∈ Hm φ₁ φ₂ ⊔ Subgroup.zpowers s,
    x * y = y * x := by
  intro x hx y hy
  have hsm := h.s_comm_Hm
  have hmc := h.Hm_comm
  rcases (h.mem_Hg).1 hx with hx | ⟨m, hm, rfl⟩ <;> rcases (h.mem_Hg).1 hy with hy | ⟨m', hm', rfl⟩
  · exact hmc x hx y hy
  · calc x * (m' * s) = (x * m') * s := by group
      _ = (m' * x) * s := by rw [hmc x hx m' hm']
      _ = m' * (x * s) := by group
      _ = m' * (s * x) := by rw [← hsm x hx]
      _ = m' * s * x := by group
  · calc m * s * y = m * (s * y) := by group
      _ = m * (y * s) := by rw [hsm y hy]
      _ = (m * y) * s := by group
      _ = (y * m) * s := by rw [hmc m hm y hy]
      _ = y * (m * s) := by group
  · have e1 : m * s * (m' * s) = (m * m') * (s * s) := by
      calc m * s * (m' * s) = m * (s * m') * s := by group
        _ = m * (m' * s) * s := by rw [hsm m' hm']
        _ = (m * m') * (s * s) := by group
    have e2 : m' * s * (m * s) = (m' * m) * (s * s) := by
      calc m' * s * (m * s) = m' * (s * m) * s := by group
        _ = m' * (m * s) * s := by rw [hsm m hm]
        _ = (m' * m) * (s * s) := by group
    rw [e1, e2, hmc m hm m' hm']

end TorusData

end TorusData

section TorusData2

variable {G : Type} [Group G] {F₁ F₂ : Type} [Field F₁] [Field F₂]
variable {φ₁ : SL2 F₁ →* G} {φ₂ : SL2 F₂ →* G} {s : G} {d₁ : F₁ˣ} {d₂ : F₂ˣ}

namespace TorusData

variable (h : TorusData φ₁ φ₂ s d₁ d₂)
include h

theorem range_comm : ∀ x ∈ φ₁.range, ∀ y ∈ φ₂.range, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact h.comm a b

omit h in
theorem Hm_le_K : Hm φ₁ φ₂ ≤ φ₁.range ⊔ φ₂.range :=
  sup_le_sup (Subgroup.map_le_range _ _) (Subgroup.map_le_range _ _)

theorem s_not_mem : s ∉ φ₁.range ⊔ φ₂.range := by
  intro hs
  obtain ⟨k₁, hk₁, k₂, hk₂, hsk⟩ := (mem_sup_iff_of_comm h.range_comm s).1 hs
  obtain ⟨a, rfl⟩ := hk₁
  obtain ⟨b, rfl⟩ := hk₂
  apply h.nsq₁
  apply isSquare_of_slConj_eq_inner d₁ a
  intro x
  apply h.inj₁
  rw [← h.act₁, hsk]
  have hc : φ₂ b * φ₁ x = φ₁ x * φ₂ b := (h.comm x b).symm
  calc φ₁ a * φ₂ b * φ₁ x * (φ₁ a * φ₂ b)⁻¹
      = φ₁ a * (φ₂ b * φ₁ x) * (φ₂ b)⁻¹ * (φ₁ a)⁻¹ := by group
    _ = φ₁ a * (φ₁ x * φ₂ b) * (φ₂ b)⁻¹ * (φ₁ a)⁻¹ := by rw [hc]
    _ = φ₁ (a * x * a⁻¹) := by simp [map_mul, map_inv, mul_assoc]

theorem Hg_inf_K₁ :
    (Hm φ₁ φ₂ ⊔ Subgroup.zpowers s) ⊓ φ₁.range = (tSub F₁).map φ₁ := by
  apply le_antisymm
  · rintro x ⟨hxH, y, rfl⟩
    rcases (h.mem_Hg).1 hxH with hx | ⟨m, hm, hxm⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := (h.mem_Hm).1 hx
      have hb1 : φ₂ b ∈ φ₁.range := ⟨a⁻¹ * y, by
        rw [map_mul, map_inv]
        have : φ₂ b = (φ₁ a)⁻¹ * φ₁ y := by rw [hab]; group
        rw [this]⟩
      rcases h.inter (φ₂ b) hb1 ⟨b, rfl⟩ with h1 | h1
      · refine ⟨a, ha, ?_⟩
        rw [hab, h1, mul_one]
      · refine ⟨a * negOne F₁, (tSub F₁).mul_mem ha negOne_mem_tSub, ?_⟩
        rw [map_mul, ← h1, hab]
    · exfalso
      apply h.s_not_mem
      have hsmem : s = m⁻¹ * φ₁ y := by rw [hxm]; group
      rw [hsmem]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Hm_le_K hm))
        (Subgroup.mem_sup_left ⟨y, rfl⟩)
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨?_, ⟨a, rfl⟩⟩
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨a, ha, rfl⟩)

theorem Hg_inf_K₂ :
    (Hm φ₁ φ₂ ⊔ Subgroup.zpowers s) ⊓ φ₂.range = (tSub F₂).map φ₂ := by
  apply le_antisymm
  · rintro x ⟨hxH, y, rfl⟩
    rcases (h.mem_Hg).1 hxH with hx | ⟨m, hm, hxm⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := (h.mem_Hm).1 hx
      have ha1 : φ₁ a ∈ φ₂.range := ⟨y * b⁻¹, by
        rw [map_mul, map_inv]
        have : φ₁ a = φ₂ y * (φ₂ b)⁻¹ := by
          have h' : φ₂ y = φ₁ a * φ₂ b := hab
          rw [h']; group
        rw [this]⟩
      rcases h.inter (φ₁ a) ⟨a, rfl⟩ ha1 with h1 | h1
      · refine ⟨b, hb, ?_⟩
        rw [hab, h1, one_mul]
      · refine ⟨negOne F₂ * b, (tSub F₂).mul_mem negOne_mem_tSub hb, ?_⟩
        rw [map_mul, ← h.zeq, ← h1, hab]
    · exfalso
      apply h.s_not_mem
      have hsmem : s = m⁻¹ * φ₂ y := by rw [hxm]; group
      rw [hsmem]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Hm_le_K hm))
        (Subgroup.mem_sup_right ⟨y, rfl⟩)
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨?_, ⟨a, rfl⟩⟩
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨a, ha, rfl⟩)

omit h in
theorem s_mem_Hg : s ∈ Hm φ₁ φ₂ ⊔ Subgroup.zpowers s := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)

theorem s_not_mem_Hm : s ∉ Hm φ₁ φ₂ := fun hs => h.s_not_mem (Hm_le_K hs)

theorem Hm_relIndex : (Hm φ₁ φ₂).relIndex (Hm φ₁ φ₂ ⊔ Subgroup.zpowers s) = 2 := by
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨s, s_mem_Hg⟩, ?_⟩
  rintro ⟨b, hb⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  rcases (h.mem_Hg).1 hb with hbm | ⟨m, hm, rfl⟩
  · right
    refine ⟨hbm, ?_⟩
    intro hbs
    exact h.s_not_mem_Hm (by
      have : s = b⁻¹ * (b * s) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hbm) hbs)
  · left
    have hbm : m * s ∉ Hm φ₁ φ₂ := by
      intro hh
      exact h.s_not_mem_Hm (by
        have : s = m⁻¹ * (m * s) := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) hh)
    refine ⟨?_, hbm⟩
    have : m * s * s = m * (s * s) := by group
    rw [this]
    exact Subgroup.mul_mem _ hm h.ss_mem

end TorusData

end TorusData2

section TorusData3

variable {G : Type} [Group G] {F₁ F₂ : Type} [Field F₁] [Field F₂]
variable {φ₁ : SL2 F₁ →* G} {φ₂ : SL2 F₂ →* G} {s : G} {d₁ : F₁ˣ} {d₂ : F₂ˣ}

namespace TorusData

variable (h : TorusData φ₁ φ₂ s d₁ d₂)
include h

theorem conj_Hm_map₁ (A : Subgroup (SL2 F₁)) (hT : ∀ t ∈ tSub F₁, ∀ x ∈ A, t * x * t⁻¹ ∈ A) :
    ∀ m ∈ Hm φ₁ φ₂, ∀ x ∈ A.map φ₁, m * x * m⁻¹ ∈ A.map φ₁ := by
  intro m hm x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (h.mem_Hm).1 hm
  obtain ⟨ξ, hξ, rfl⟩ := hx
  have hc : φ₂ b * φ₁ ξ = φ₁ ξ * φ₂ b := (h.comm ξ b).symm
  refine ⟨a * ξ * a⁻¹, hT a ha ξ hξ, ?_⟩
  calc φ₁ (a * ξ * a⁻¹) = φ₁ a * φ₁ ξ * (φ₁ a)⁻¹ := by simp [map_mul, map_inv]
    _ = φ₁ a * (φ₂ b * φ₁ ξ) * (φ₂ b)⁻¹ * (φ₁ a)⁻¹ := by
        rw [hc]; group
    _ = _ := by group

theorem conj_Hm_map₂ (A : Subgroup (SL2 F₂)) (hT : ∀ t ∈ tSub F₂, ∀ x ∈ A, t * x * t⁻¹ ∈ A) :
    ∀ m ∈ Hm φ₁ φ₂, ∀ x ∈ A.map φ₂, m * x * m⁻¹ ∈ A.map φ₂ := by
  intro m hm x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (h.mem_Hm).1 hm
  obtain ⟨ξ, hξ, rfl⟩ := hx
  have hc : φ₁ a * φ₂ (b * ξ * b⁻¹) = φ₂ (b * ξ * b⁻¹) * φ₁ a := h.comm a _
  refine ⟨b * ξ * b⁻¹, hT b hb ξ hξ, ?_⟩
  calc φ₂ (b * ξ * b⁻¹) = φ₁ a * φ₂ (b * ξ * b⁻¹) * (φ₁ a)⁻¹ := by rw [hc]; group
    _ = _ := by simp [map_mul, map_inv, mul_assoc]

theorem conj_s_map₁ (A : Subgroup (SL2 F₁)) (hD : ∀ x ∈ A, slConj (diagGL 1 d₁) x ∈ A) :
    ∀ x ∈ A.map φ₁, s * x * s⁻¹ ∈ A.map φ₁ := by
  rintro _ ⟨ξ, hξ, rfl⟩
  exact ⟨_, hD ξ hξ, (h.act₁ ξ).symm⟩

theorem conj_s_map₂ (A : Subgroup (SL2 F₂)) (hD : ∀ x ∈ A, slConj (diagGL 1 d₂) x ∈ A) :
    ∀ x ∈ A.map φ₂, s * x * s⁻¹ ∈ A.map φ₂ := by
  rintro _ ⟨ξ, hξ, rfl⟩
  exact ⟨_, hD ξ hξ, (h.act₂ ξ).symm⟩

theorem conj_Hg_map₁ (A : Subgroup (SL2 F₁)) (hT : ∀ t ∈ tSub F₁, ∀ x ∈ A, t * x * t⁻¹ ∈ A)
    (hD : ∀ x ∈ A, slConj (diagGL 1 d₁) x ∈ A) :
    ∀ g ∈ Hm φ₁ φ₂ ⊔ Subgroup.zpowers s, ∀ x ∈ A.map φ₁, g * x * g⁻¹ ∈ A.map φ₁ := by
  intro g hg x hx
  rcases (h.mem_Hg).1 hg with hg | ⟨m, hm, rfl⟩
  · exact h.conj_Hm_map₁ A hT g hg x hx
  · have h1 := h.conj_s_map₁ A hD x hx
    have h2 := h.conj_Hm_map₁ A hT m hm _ h1
    have : m * s * x * (m * s)⁻¹ = m * (s * x * s⁻¹) * m⁻¹ := by group
    rw [this]; exact h2

theorem conj_Hg_map₂ (A : Subgroup (SL2 F₂)) (hT : ∀ t ∈ tSub F₂, ∀ x ∈ A, t * x * t⁻¹ ∈ A)
    (hD : ∀ x ∈ A, slConj (diagGL 1 d₂) x ∈ A) :
    ∀ g ∈ Hm φ₁ φ₂ ⊔ Subgroup.zpowers s, ∀ x ∈ A.map φ₂, g * x * g⁻¹ ∈ A.map φ₂ := by
  intro g hg x hx
  rcases (h.mem_Hg).1 hg with hg | ⟨m, hm, rfl⟩
  · exact h.conj_Hm_map₂ A hT g hg x hx
  · have h1 := h.conj_s_map₂ A hD x hx
    have h2 := h.conj_Hm_map₂ A hT m hm _ h1
    have : m * s * x * (m * s)⁻¹ = m * (s * x * s⁻¹) * m⁻¹ := by group
    rw [this]; exact h2

end TorusData

end TorusData3

section TorusData4

variable {G : Type} [Group G] {F₁ F₂ : Type} [Field F₁] [Field F₂]
variable {φ₁ : SL2 F₁ →* G} {φ₂ : SL2 F₂ →* G} {s : G} {d₁ : F₁ˣ} {d₂ : F₂ˣ}

namespace TorusData

variable (h : TorusData φ₁ φ₂ s d₁ d₂)
include h

theorem w₁_conj_s : φ₁ (sl2W F₁) * s * (φ₁ (sl2W F₁))⁻¹ = φ₁ (sl2D d₁) * s := by
  have h1 := h.act₁ (sl2W F₁)⁻¹
  have h2 : φ₁ (sl2W F₁) * (s * (φ₁ (sl2W F₁))⁻¹ * s⁻¹) = φ₁ (sl2D d₁) := by
    rw [← map_inv, h1, ← map_mul, sl2W_mul_slConj_diagGL_one]
  calc φ₁ (sl2W F₁) * s * (φ₁ (sl2W F₁))⁻¹ =
      (φ₁ (sl2W F₁) * (s * (φ₁ (sl2W F₁))⁻¹ * s⁻¹)) * s := by group
    _ = φ₁ (sl2D d₁) * s := by rw [h2]

theorem w₂_conj_s : φ₂ (sl2W F₂) * s * (φ₂ (sl2W F₂))⁻¹ = φ₂ (sl2D d₂) * s := by
  have h1 := h.act₂ (sl2W F₂)⁻¹
  have h2 : φ₂ (sl2W F₂) * (s * (φ₂ (sl2W F₂))⁻¹ * s⁻¹) = φ₂ (sl2D d₂) := by
    rw [← map_inv, h1, ← map_mul, sl2W_mul_slConj_diagGL_one]
  calc φ₂ (sl2W F₂) * s * (φ₂ (sl2W F₂))⁻¹ =
      (φ₂ (sl2W F₂) * (s * (φ₂ (sl2W F₂))⁻¹ * s⁻¹)) * s := by group
    _ = φ₂ (sl2D d₂) * s := by rw [h2]

omit h in
theorem w₁_sq : φ₁ (sl2W F₁) * φ₁ (sl2W F₁) = φ₁ (negOne F₁) := by
  rw [← map_mul, sl2W_sq]

theorem w₂_sq : φ₂ (sl2W F₂) * φ₂ (sl2W F₂) = φ₁ (negOne F₁) := by
  rw [← map_mul, sl2W_sq, h.zeq]

theorem w₁_conj_Hm : ∀ m ∈ Hm φ₁ φ₂, φ₁ (sl2W F₁) * m * (φ₁ (sl2W F₁))⁻¹ ∈ Hm φ₁ φ₂ := by
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := (h.mem_Hm).1 hm
  rw [h.mem_Hm]
  refine ⟨(sl2W F₁) * a * (sl2W F₁)⁻¹, ?_, b, hb, ?_⟩
  · rw [sl2W_inv_tSub a ha]; exact (tSub F₁).inv_mem ha
  · have hc : φ₁ (sl2W F₁) * φ₂ b = φ₂ b * φ₁ (sl2W F₁) := h.comm _ b
    calc φ₁ (sl2W F₁) * (φ₁ a * φ₂ b) * (φ₁ (sl2W F₁))⁻¹
        = φ₁ (sl2W F₁) * φ₁ a * (φ₂ b * (φ₁ (sl2W F₁))⁻¹) := by group
      _ = φ₁ (sl2W F₁) * φ₁ a * ((φ₁ (sl2W F₁))⁻¹ * φ₂ b) := by
          have := (h.comm (sl2W F₁)⁻¹ b).symm
          rw [map_inv] at this
          rw [this]
      _ = φ₁ ((sl2W F₁) * a * (sl2W F₁)⁻¹) * φ₂ b := by simp [map_mul, map_inv, mul_assoc]

end TorusData

end TorusData4

section TorusData5

variable {G : Type} [Group G] {F₁ F₂ : Type} [Field F₁] [Field F₂]
variable {φ₁ : SL2 F₁ →* G} {φ₂ : SL2 F₂ →* G} {s : G} {d₁ : F₁ˣ} {d₂ : F₂ˣ}

namespace TorusData

variable (h : TorusData φ₁ φ₂ s d₁ d₂)
include h

omit h in
theorem z_comm_φ₁ (x : SL2 F₁) : φ₁ (negOne F₁) * φ₁ x = φ₁ x * φ₁ (negOne F₁) := by
  rw [← map_mul, ← map_mul, negOne_central]

theorem z_comm_φ₂ (x : SL2 F₂) : φ₁ (negOne F₁) * φ₂ x = φ₂ x * φ₁ (negOne F₁) := by
  rw [h.zeq, ← map_mul, ← map_mul, negOne_central]

omit h in
theorem z_mul_z : φ₁ (negOne F₁) * φ₁ (negOne F₁) = 1 := by
  rw [← map_mul, negOne_mul_self, map_one]

theorem ss_eq : s * s = (φ₁ (sl2D d₁))⁻¹ * (φ₂ (sl2D d₂))⁻¹ := by
  have e1 : (sl2D (-d₁⁻¹) : SL2 F₁) = negOne F₁ * (sl2D d₁)⁻¹ := by
    have : (sl2D (-d₁⁻¹) : SL2 F₁) = sl2D (-1) * sl2D d₁⁻¹ := by
      rw [sl2D_mul]; congr 1; simp
    rw [this, sl2D_neg_one]
    congr 1
    have h2 : (sl2D d₁⁻¹ : SL2 F₁) * sl2D d₁ = 1 := by rw [sl2D_mul, inv_mul_cancel, sl2D_one]
    exact eq_inv_of_mul_eq_one_left h2
  have e2 : (sl2D (-d₂⁻¹) : SL2 F₂) = negOne F₂ * (sl2D d₂)⁻¹ := by
    have : (sl2D (-d₂⁻¹) : SL2 F₂) = sl2D (-1) * sl2D d₂⁻¹ := by
      rw [sl2D_mul]; congr 1; simp
    rw [this, sl2D_neg_one]
    congr 1
    have h2 : (sl2D d₂⁻¹ : SL2 F₂) * sl2D d₂ = 1 := by rw [sl2D_mul, inv_mul_cancel, sl2D_one]
    exact eq_inv_of_mul_eq_one_left h2
  rw [h.ss, e1, e2, map_mul, map_mul, map_inv, map_inv, ← h.zeq]
  have hc : (φ₁ (sl2D d₁))⁻¹ * φ₁ (negOne F₁) = φ₁ (negOne F₁) * (φ₁ (sl2D d₁))⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, negOne_central]
  calc φ₁ (negOne F₁) * (φ₁ (sl2D d₁))⁻¹ * (φ₁ (negOne F₁) * (φ₂ (sl2D d₂))⁻¹)
      = φ₁ (negOne F₁) * ((φ₁ (sl2D d₁))⁻¹ * φ₁ (negOne F₁)) * (φ₂ (sl2D d₂))⁻¹ := by group
    _ = φ₁ (negOne F₁) * (φ₁ (negOne F₁) * (φ₁ (sl2D d₁))⁻¹) * (φ₂ (sl2D d₂))⁻¹ := by rw [hc]
    _ = (φ₁ (negOne F₁) * φ₁ (negOne F₁)) * (φ₁ (sl2D d₁))⁻¹ * (φ₂ (sl2D d₂))⁻¹ := by group
    _ = (φ₁ (sl2D d₁))⁻¹ * (φ₂ (sl2D d₂))⁻¹ := by rw [z_mul_z, one_mul]

end TorusData

end TorusData5

section TorusData6

variable {G : Type} [Group G] {F₁ F₂ : Type} [Field F₁] [Field F₂]
variable {φ₁ : SL2 F₁ →* G} {φ₂ : SL2 F₂ →* G} {s : G} {d₁ : F₁ˣ} {d₂ : F₂ˣ}

namespace TorusData

variable (h : TorusData φ₁ φ₂ s d₁ d₂)
include h

theorem w₂_conj_Hm : ∀ m ∈ Hm φ₁ φ₂, φ₂ (sl2W F₂) * m * (φ₂ (sl2W F₂))⁻¹ ∈ Hm φ₁ φ₂ := by
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := (h.mem_Hm).1 hm
  rw [h.mem_Hm]
  refine ⟨a, ha, (sl2W F₂) * b * (sl2W F₂)⁻¹, ?_, ?_⟩
  · rw [sl2W_inv_tSub b hb]; exact (tSub F₂).inv_mem hb
  · have hc : φ₂ (sl2W F₂) * φ₁ a = φ₁ a * φ₂ (sl2W F₂) := (h.comm a _).symm
    calc φ₂ (sl2W F₂) * (φ₁ a * φ₂ b) * (φ₂ (sl2W F₂))⁻¹
        = (φ₂ (sl2W F₂) * φ₁ a) * φ₂ b * (φ₂ (sl2W F₂))⁻¹ := by group
      _ = (φ₁ a * φ₂ (sl2W F₂)) * φ₂ b * (φ₂ (sl2W F₂))⁻¹ := by rw [hc]
      _ = φ₁ a * (φ₂ (sl2W F₂) * φ₂ b * (φ₂ (sl2W F₂))⁻¹) := by group
      _ = φ₁ a * φ₂ ((sl2W F₂) * b * (sl2W F₂)⁻¹) := by simp [map_mul, map_inv, mul_assoc]

theorem w₁_conj_Hg : ∀ g ∈ Hm φ₁ φ₂ ⊔ Subgroup.zpowers s,
    φ₁ (sl2W F₁) * g * (φ₁ (sl2W F₁))⁻¹ ∈ Hm φ₁ φ₂ ⊔ Subgroup.zpowers s := by
  intro g hg
  rcases (h.mem_Hg).1 hg with hg | ⟨m, hm, rfl⟩
  · exact (h.mem_Hg).2 (Or.inl (h.w₁_conj_Hm g hg))
  · have hm' : (φ₁ (sl2W F₁) * m * (φ₁ (sl2W F₁))⁻¹) * φ₁ (sl2D d₁) ∈ Hm φ₁ φ₂ :=
      Subgroup.mul_mem _ (h.w₁_conj_Hm m hm) (Subgroup.mem_sup_left ⟨_, sl2D_mem_tSub d₁, rfl⟩)
    refine (h.mem_Hg).2 (Or.inr ⟨_, hm', ?_⟩)
    have e : φ₁ (sl2W F₁) * (m * s) * (φ₁ (sl2W F₁))⁻¹ =
        (φ₁ (sl2W F₁) * m * (φ₁ (sl2W F₁))⁻¹) * (φ₁ (sl2W F₁) * s * (φ₁ (sl2W F₁))⁻¹) := by
      group
    rw [e, h.w₁_conj_s]
    group

theorem w₂_conj_Hg : ∀ g ∈ Hm φ₁ φ₂ ⊔ Subgroup.zpowers s,
    φ₂ (sl2W F₂) * g * (φ₂ (sl2W F₂))⁻¹ ∈ Hm φ₁ φ₂ ⊔ Subgroup.zpowers s := by
  intro g hg
  rcases (h.mem_Hg).1 hg with hg | ⟨m, hm, rfl⟩
  · exact (h.mem_Hg).2 (Or.inl (h.w₂_conj_Hm g hg))
  · have hm' : (φ₂ (sl2W F₂) * m * (φ₂ (sl2W F₂))⁻¹) * φ₂ (sl2D d₂) ∈ Hm φ₁ φ₂ :=
      Subgroup.mul_mem _ (h.w₂_conj_Hm m hm) (Subgroup.mem_sup_right ⟨_, sl2D_mem_tSub d₂, rfl⟩)
    refine (h.mem_Hg).2 (Or.inr ⟨_, hm', ?_⟩)
    have e : φ₂ (sl2W F₂) * (m * s) * (φ₂ (sl2W F₂))⁻¹ =
        (φ₂ (sl2W F₂) * m * (φ₂ (sl2W F₂))⁻¹) * (φ₂ (sl2W F₂) * s * (φ₂ (sl2W F₂))⁻¹) := by
      group
    rw [e, h.w₂_conj_s]
    group

theorem w₁_mem_normalizer [Finite G] :
    φ₁ (sl2W F₁) ∈ normalizer ((Hm φ₁ φ₂ ⊔ Subgroup.zpowers s : Subgroup G) : Set G) :=
  Subgroup.mem_normalizer_fintype (fun n hn => h.w₁_conj_Hg n hn)

theorem w₂_mem_normalizer [Finite G] :
    φ₂ (sl2W F₂) ∈ normalizer ((Hm φ₁ φ₂ ⊔ Subgroup.zpowers s : Subgroup G) : Set G) :=
  Subgroup.mem_normalizer_fintype (fun n hn => h.w₂_conj_Hg n hn)

theorem comm_conj₂ (a : SL2 F₁) (b : SL2 F₂) : φ₂ b * φ₁ a * (φ₂ b)⁻¹ = φ₁ a := by
  rw [← h.comm a b]; group

theorem comm_conj₁ (a : SL2 F₁) (b : SL2 F₂) : φ₁ a * φ₂ b * (φ₁ a)⁻¹ = φ₂ b := by
  rw [h.comm a b]; group

theorem w₀_conj_φ₁ (a : SL2 F₁) :
    (φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * φ₁ a * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂))⁻¹ =
      φ₁ ((sl2W F₁) * a * (sl2W F₁)⁻¹) := by
  have : (φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * φ₁ a * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂))⁻¹ =
      φ₁ (sl2W F₁) * (φ₂ (sl2W F₂) * φ₁ a * (φ₂ (sl2W F₂))⁻¹) * (φ₁ (sl2W F₁))⁻¹ := by group
  rw [this, h.comm_conj₂]
  simp [map_mul, map_inv, mul_assoc]

theorem w₀_conj_φ₂ (b : SL2 F₂) :
    (φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * φ₂ b * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂))⁻¹ =
      φ₂ ((sl2W F₂) * b * (sl2W F₂)⁻¹) := by
  have : (φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * φ₂ b * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂))⁻¹ =
      φ₁ (sl2W F₁) * (φ₂ (sl2W F₂) * φ₂ b * (φ₂ (sl2W F₂))⁻¹) * (φ₁ (sl2W F₁))⁻¹ := by group
  rw [this]
  have h2 : φ₂ (sl2W F₂) * φ₂ b * (φ₂ (sl2W F₂))⁻¹ = φ₂ ((sl2W F₂) * b * (sl2W F₂)⁻¹) := by
    simp [map_mul, map_inv, mul_assoc]
  rw [h2]
  have h3 := h.comm_conj₁ (sl2W F₁)⁻¹ ((sl2W F₂) * b * (sl2W F₂)⁻¹)
  have h4 : φ₁ (sl2W F₁) * φ₂ ((sl2W F₂) * b * (sl2W F₂)⁻¹) * (φ₁ (sl2W F₁))⁻¹ =
      φ₂ ((sl2W F₂) * b * (sl2W F₂)⁻¹) := h.comm_conj₁ (sl2W F₁) _
  rw [h4]

theorem w₀_conj_Hm : ∀ m ∈ Hm φ₁ φ₂,
    (φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * m * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂))⁻¹ = m⁻¹ := by
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := (h.mem_Hm).1 hm
  have e : (φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * (φ₁ a * φ₂ b) * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂))⁻¹ =
      ((φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * φ₁ a * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂))⁻¹) *
      ((φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * φ₂ b * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂))⁻¹) := by group
  rw [e, h.w₀_conj_φ₁, h.w₀_conj_φ₂, sl2W_inv_tSub a ha, sl2W_inv_tSub b hb]
  simp only [map_inv]
  rw [mul_inv_rev]
  have := h.comm a⁻¹ b⁻¹
  simp only [map_inv] at this
  exact this

theorem w₀_conj_s : (φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * s * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂))⁻¹ = s⁻¹ := by
  have e : (φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * s * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂))⁻¹ =
      φ₁ (sl2W F₁) * (φ₂ (sl2W F₂) * s * (φ₂ (sl2W F₂))⁻¹) * (φ₁ (sl2W F₁))⁻¹ := by group
  rw [e, h.w₂_conj_s]
  have e2 : φ₁ (sl2W F₁) * (φ₂ (sl2D d₂) * s) * (φ₁ (sl2W F₁))⁻¹ =
      (φ₁ (sl2W F₁) * φ₂ (sl2D d₂) * (φ₁ (sl2W F₁))⁻¹) * (φ₁ (sl2W F₁) * s * (φ₁ (sl2W F₁))⁻¹) := by
    group
  rw [e2, h.w₁_conj_s, h.comm_conj₁]
  have hs : s⁻¹ = (s * s)⁻¹ * s := by group
  rw [hs, h.ss_eq, mul_inv_rev, inv_inv, inv_inv]
  group

theorem w₀_conj_Hg : ∀ g ∈ Hm φ₁ φ₂ ⊔ Subgroup.zpowers s,
    (φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * g * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂))⁻¹ = g⁻¹ := by
  intro g hg
  rcases (h.mem_Hg).1 hg with hg | ⟨m, hm, rfl⟩
  · exact h.w₀_conj_Hm g hg
  · have e : (φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * (m * s) * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂))⁻¹ =
        ((φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * m * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂))⁻¹) *
        ((φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * s * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂))⁻¹) := by group
    rw [e, h.w₀_conj_Hm m hm, h.w₀_conj_s]
    have hc : s * m = m * s := h.s_comm_Hm m hm
    rw [← hc, mul_inv_rev]

theorem fpf₁ (g : G) (hg : g ∈ (Hm φ₁ φ₂ ⊔ Subgroup.zpowers s) ⊓ φ₁.range)
    (hgz : g ∉ Subgroup.zpowers (φ₁ (negOne F₁))) :
    ∀ x ∈ (uSub F₁).map φ₁, g * x * g⁻¹ = x → x = 1 := by
  rw [h.Hg_inf_K₁] at hg
  obtain ⟨a, ha, rfl⟩ := hg
  rintro _ ⟨ξ, hξ, rfl⟩ hfix
  have h1 : a ≠ 1 := by
    rintro rfl
    exact hgz (by rw [map_one]; exact Subgroup.one_mem _)
  have h2 : a ≠ negOne F₁ := by
    rintro rfl
    exact hgz (Subgroup.mem_zpowers _)
  have : a * ξ * a⁻¹ = ξ := by
    apply h.inj₁
    rw [map_mul, map_mul, map_inv]
    exact hfix
  rw [tSub_fpf_uSub a ha h1 h2 ξ hξ this, map_one]

theorem fpf₁' (g : G) (hg : g ∈ (Hm φ₁ φ₂ ⊔ Subgroup.zpowers s) ⊓ φ₁.range)
    (hgz : g ∉ Subgroup.zpowers (φ₁ (negOne F₁))) :
    ∀ x ∈ (lSub F₁).map φ₁, g * x * g⁻¹ = x → x = 1 := by
  rw [h.Hg_inf_K₁] at hg
  obtain ⟨a, ha, rfl⟩ := hg
  rintro _ ⟨ξ, hξ, rfl⟩ hfix
  have h1 : a ≠ 1 := by
    rintro rfl
    exact hgz (by rw [map_one]; exact Subgroup.one_mem _)
  have h2 : a ≠ negOne F₁ := by
    rintro rfl
    exact hgz (Subgroup.mem_zpowers _)
  have : a * ξ * a⁻¹ = ξ := by
    apply h.inj₁
    rw [map_mul, map_mul, map_inv]
    exact hfix
  rw [tSub_fpf_lSub a ha h1 h2 ξ hξ this, map_one]

theorem fpf₂ (g : G) (hg : g ∈ (Hm φ₁ φ₂ ⊔ Subgroup.zpowers s) ⊓ φ₂.range)
    (hgz : g ∉ Subgroup.zpowers (φ₁ (negOne F₁))) :
    ∀ x ∈ (uSub F₂).map φ₂, g * x * g⁻¹ = x → x = 1 := by
  rw [h.Hg_inf_K₂] at hg
  obtain ⟨a, ha, rfl⟩ := hg
  rintro _ ⟨ξ, hξ, rfl⟩ hfix
  have h1 : a ≠ 1 := by
    rintro rfl
    exact hgz (by rw [map_one]; exact Subgroup.one_mem _)
  have h2 : a ≠ negOne F₂ := by
    rintro rfl
    exact hgz (by rw [h.zeq]; exact Subgroup.mem_zpowers _)
  have : a * ξ * a⁻¹ = ξ := by
    apply h.inj₂
    rw [map_mul, map_mul, map_inv]
    exact hfix
  rw [tSub_fpf_uSub a ha h1 h2 ξ hξ this, map_one]

theorem fpf₂' (g : G) (hg : g ∈ (Hm φ₁ φ₂ ⊔ Subgroup.zpowers s) ⊓ φ₂.range)
    (hgz : g ∉ Subgroup.zpowers (φ₁ (negOne F₁))) :
    ∀ x ∈ (lSub F₂).map φ₂, g * x * g⁻¹ = x → x = 1 := by
  rw [h.Hg_inf_K₂] at hg
  obtain ⟨a, ha, rfl⟩ := hg
  rintro _ ⟨ξ, hξ, rfl⟩ hfix
  have h1 : a ≠ 1 := by
    rintro rfl
    exact hgz (by rw [map_one]; exact Subgroup.one_mem _)
  have h2 : a ≠ negOne F₂ := by
    rintro rfl
    exact hgz (by rw [h.zeq]; exact Subgroup.mem_zpowers _)
  have : a * ξ * a⁻¹ = ξ := by
    apply h.inj₂
    rw [map_mul, map_mul, map_inv]
    exact hfix
  rw [tSub_fpf_lSub a ha h1 h2 ξ hξ this, map_one]

end TorusData

end TorusData6

end CFSG.GH74.GLS.Stage4.Rest.T2
