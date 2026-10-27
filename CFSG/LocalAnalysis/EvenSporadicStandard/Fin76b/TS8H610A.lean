module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H69O
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma610A

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem mem_Zg {α : G} (hα : AlphaSpec S z t α) {u : G} :
    u ∈ (zpowers α ⊔ zpowers t : Subgroup G) ↔ u = 1 ∨ u = t ∨ u = α ∨ u = α * t := by
  have hc : zpowers t ≤ centralizer ((zpowers α : Subgroup G) : Set G) := by
    rw [zpowers_le]
    refine mem_centralizer_iff.2 fun a ha => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    exact (Commute.zpow_left (show Commute α t from h.t_comm_S α hα.mem) k).eq
  constructor
  · intro hu
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hc hu
    rcases mem_zpowers_sq_eq_one hα.sq ha with rfl | rfl <;>
      rcases mem_zpowers_sq_eq_one h.t_sq hb with rfl | rfl
    · left; simp
    · right; left; simp
    · right; right; left; simp
    · right; right; right; rfl
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact mem_sup_right (mem_zpowers _)
    · exact mem_sup_left (mem_zpowers _)
    · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))

theorem Zg_conj {α : G} (hα : AlphaSpec S z t α) {m : G}
    (hm : m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G)) {a : G}
    (ha : a ∈ (zpowers α ⊔ zpowers t : Subgroup G)) :
    m * a * m⁻¹ ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
  have hαm := h.alpha_orbit hα hm
  have htm := h.conj_t_of_M hm
  rcases (h.mem_Zg hα).1 ha with rfl | rfl | rfl | rfl
  · simp
  · rw [htm]; exact (h.mem_Zg hα).2 (Or.inr (Or.inl rfl))
  · rcases hαm with h1 | h1
    · rw [h1]; exact (h.mem_Zg hα).2 (Or.inr (Or.inr (Or.inl rfl)))
    · rw [h1]; exact (h.mem_Zg hα).2 (Or.inr (Or.inr (Or.inr rfl)))
  · have : m * (α * t) * m⁻¹ = (m * α * m⁻¹) * (m * t * m⁻¹) := by group
    rw [this, htm]
    rcases hαm with h1 | h1
    · rw [h1]; exact (h.mem_Zg hα).2 (Or.inr (Or.inr (Or.inr rfl)))
    · rw [h1, mul_assoc, h.t_sq, mul_one]
      exact (h.mem_Zg hα).2 (Or.inr (Or.inr (Or.inl rfl)))

theorem Theta_inv {α : G} (hα : AlphaSpec S z t α) {m : G}
    (hm : m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G)) {e : G} (he : e ∈ E2 E t) :
    ∃ a ∈ (zpowers α ⊔ zpowers t : Subgroup G), ∃ e' ∈ E2 E t, m * e * m⁻¹ = a * e' := by
  have hXeq := h.X_eq hα
  have hu : m * e * m⁻¹ ∈ S ⊔ E := (mem_normalizer_iff.1 hm e).1 (mem_sup_right he.1)
  have hu2 : m * e * m⁻¹ * (m * e * m⁻¹) = 1 := by
    calc m * e * m⁻¹ * (m * e * m⁻¹) = m * (e * e) * m⁻¹ := by group
      _ = 1 := by rw [he.2.1]; group
  have hu1 : m * e * m⁻¹ ≠ 1 := by
    intro h1
    apply he.2.2.1
    calc e = m⁻¹ * (m * e * m⁻¹) * m := by group
      _ = 1 := by rw [h1]; group
  have hut : m * e * m⁻¹ ≠ t := by
    intro h1
    apply he.2.2.2
    have := h.conj_t_of_M (inv_mem hm)
    calc e = m⁻¹ * (m * e * m⁻¹) * m := by group
      _ = m⁻¹ * t * m := by rw [h1]
      _ = t := by simpa using this
  have hnX : m * e * m⁻¹ ∉ XSet S E z := by
    intro hX
    apply h.E2_not_X he
    have := h.X_inv (inv_mem hm) hX
    have e1 : m⁻¹ * (m * e * m⁻¹) * m⁻¹⁻¹ = e := by group
    rwa [e1] at this
  have hnA : m * e * m⁻¹ ∉ blk α {1, t} := by
    rintro ⟨a, ha, hma⟩
    change α * a = m * e * m⁻¹ at hma
    have haZ : α * a ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
      rcases ha with ha | ha
      · rw [ha, mul_one]; exact (h.mem_Zg hα).2 (Or.inr (Or.inr (Or.inl rfl)))
      · rw [ha]; exact (h.mem_Zg hα).2 (Or.inr (Or.inr (Or.inr rfl)))
    have heZ : e ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
      have := h.Zg_conj hα (inv_mem hm) haZ
      have e1 : m⁻¹ * (α * a) * m⁻¹⁻¹ = e := by rw [hma]; group
      rwa [e1] at this
    have hαE : α ∈ E := by
      rcases (h.mem_Zg hα).1 heZ with h1 | h1 | h1 | h1
      · exact absurd h1 he.2.2.1
      · exact absurd h1 he.2.2.2
      · rw [← h1]; exact he.1
      · have : α = e * t := by rw [h1, mul_assoc, h.t_sq, mul_one]
        rw [this]; exact mul_mem he.1 h.t_mem_E
    rcases h.S_inf_E hα.mem hαE with h1 | h1
    · exact hα.ne_one h1
    · exact hα.ne_t h1
  rw [hXeq] at hnX
  rcases h.classify hα hu hu2 hu1 hut with h1 | h1 | h1 | h1 | h1 | h1
  · exact absurd (Or.inl (Or.inl h1)) hnX
  · exact absurd (Or.inl (Or.inr h1)) hnX
  · exact absurd h1 hnA
  · obtain ⟨e', he', hee'⟩ := h1
    exact ⟨α, (h.mem_Zg hα).2 (Or.inr (Or.inr (Or.inl rfl))), e', he', hee'.symm⟩
  · exact ⟨1, one_mem _, _, h1, (one_mul _).symm⟩
  · exact absurd (Or.inr h1) hnX

@[expose] noncomputable def Fsub {α : G} (hα : AlphaSpec S z t α) : Subgroup G where
  carrier := {m | m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G) ∧
    ∀ e ∈ E2 E t, ∃ a ∈ (zpowers α ⊔ zpowers t : Subgroup G), m * e * m⁻¹ = a * e}
  mul_mem' := by
    rintro m₁ m₂ ⟨hm₁, h₁⟩ ⟨hm₂, h₂⟩
    refine ⟨mul_mem hm₁ hm₂, fun e he => ?_⟩
    obtain ⟨a₁, ha₁, h1⟩ := h₁ e he
    obtain ⟨a₂, ha₂, h2⟩ := h₂ e he
    refine ⟨(m₁ * a₂ * m₁⁻¹) * a₁, mul_mem (h.Zg_conj hα hm₁ ha₂) ha₁, ?_⟩
    calc m₁ * m₂ * e * (m₁ * m₂)⁻¹ = m₁ * (m₂ * e * m₂⁻¹) * m₁⁻¹ := by group
      _ = m₁ * (a₂ * e) * m₁⁻¹ := by rw [h2]
      _ = (m₁ * a₂ * m₁⁻¹) * (m₁ * e * m₁⁻¹) := by group
      _ = (m₁ * a₂ * m₁⁻¹) * (a₁ * e) := by rw [h1]
      _ = (m₁ * a₂ * m₁⁻¹) * a₁ * e := by group
  one_mem' := ⟨one_mem _, fun e he => ⟨1, one_mem _, by simp⟩⟩
  inv_mem' := by
    rintro m ⟨hm, h1⟩
    refine ⟨inv_mem hm, fun e he => ?_⟩
    obtain ⟨a, ha, h2⟩ := h1 e he
    refine ⟨m⁻¹ * a⁻¹ * m⁻¹⁻¹, ?_, ?_⟩
    · have := h.Zg_conj hα (inv_mem hm) (inv_mem ha)
      exact this
    · calc m⁻¹ * e * m⁻¹⁻¹ = m⁻¹ * (a⁻¹ * (a * e)) * m⁻¹⁻¹ := by group
        _ = m⁻¹ * (a⁻¹ * (m * e * m⁻¹)) * m⁻¹⁻¹ := by rw [h2]
        _ = m⁻¹ * a⁻¹ * m⁻¹⁻¹ * e := by group

theorem Fsub_le_M {α : G} (hα : AlphaSpec S z t α) :
    Fsub h hα ≤ normalizer ((S ⊔ E : Subgroup G) : Set G) := fun _ hm => hm.1

theorem U_le_Fsub {α : G} (hα : AlphaSpec S z t α) : S ⊔ E ≤ Fsub h hα := by
  intro u hu
  refine ⟨le_normalizer hu, fun e he => ?_⟩
  obtain ⟨s, hs, e₁, he₁, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer h.E_le_cent_S hu
  have hZt : t ∈ (zpowers α ⊔ zpowers t : Subgroup G) := (h.mem_Zg hα).2 (Or.inr (Or.inl rfl))
  have h1 : s * e₁ * e * (s * e₁)⁻¹ = e₁ * e * e₁⁻¹ := by
    calc s * e₁ * e * (s * e₁)⁻¹ = s * (e₁ * e * e₁⁻¹) * s⁻¹ := by group
      _ = e₁ * e * e₁⁻¹ := by
        have hc := h.S_comm_E s hs (e₁ * e * e₁⁻¹) (mul_mem (mul_mem he₁ he.1) (inv_mem he₁))
        rw [hc]; group
  rw [h1]
  rcases h.E_comm e₁ he₁ e he.1 with h2 | h2
  · refine ⟨1, one_mem _, ?_⟩
    calc e₁ * e * e₁⁻¹ = (e₁ * e) * e₁⁻¹ := rfl
      _ = (e * e₁) * e₁⁻¹ := by rw [h2]
      _ = 1 * e := by group
  · refine ⟨t, hZt, ?_⟩
    calc e₁ * e * e₁⁻¹ = (t * (e * e₁)) * e₁⁻¹ := by rw [h2]
      _ = t * e := by group

theorem Fsub_normal {α : G} (hα : AlphaSpec S z t α) {g f : G}
    (hg : g ∈ normalizer ((S ⊔ E : Subgroup G) : Set G)) (hf : f ∈ Fsub h hα) :
    g * f * g⁻¹ ∈ Fsub h hα := by
  obtain ⟨hfM, hf⟩ := hf
  refine ⟨mul_mem (mul_mem hg hfM) (inv_mem hg), fun e he => ?_⟩
  obtain ⟨a₀, ha₀, e'', he'', h0⟩ := h.Theta_inv hα (inv_mem hg) he
  simp only [inv_inv] at h0
  obtain ⟨a₁, ha₁, h1⟩ := hf e'' he''
  have e1 : e = g * (a₀ * e'') * g⁻¹ := by
    calc e = g * (g⁻¹ * e * g) * g⁻¹ := by group
      _ = g * (a₀ * e'') * g⁻¹ := by rw [h0]
  have h2 : g * f * g⁻¹ * e * (g * f * g⁻¹)⁻¹ =
      (g * f * a₀ * f⁻¹ * g⁻¹) * (g * (f * e'' * f⁻¹) * g⁻¹) := by
    calc g * f * g⁻¹ * e * (g * f * g⁻¹)⁻¹ = g * f * (g⁻¹ * e * g) * f⁻¹ * g⁻¹ := by group
      _ = g * f * (a₀ * e'') * f⁻¹ * g⁻¹ := by rw [h0]
      _ = _ := by group
  rw [h1] at h2
  have hZ1 : g * f * a₀ * f⁻¹ * g⁻¹ ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
    have := h.Zg_conj hα hfM ha₀
    have := h.Zg_conj hα hg this
    simpa [mul_assoc] using this
  have hZ2 : g * a₁ * g⁻¹ ∈ (zpowers α ⊔ zpowers t : Subgroup G) := h.Zg_conj hα hg ha₁
  have h3 : g * (a₁ * e'') * g⁻¹ = (g * a₁ * g⁻¹) * (g * e'' * g⁻¹) := by group
  have h4 : g * e'' * g⁻¹ = (g * a₀⁻¹ * g⁻¹) * e := by
    calc g * e'' * g⁻¹ = g * (a₀⁻¹ * (a₀ * e'')) * g⁻¹ := by group
      _ = g * (a₀⁻¹ * (g⁻¹ * e * g)) * g⁻¹ := by rw [h0]
      _ = (g * a₀⁻¹ * g⁻¹) * e := by group
  refine ⟨(g * f * a₀ * f⁻¹ * g⁻¹) * (g * a₁ * g⁻¹) * (g * a₀⁻¹ * g⁻¹), ?_, ?_⟩
  · exact mul_mem (mul_mem hZ1 hZ2) (h.Zg_conj hα hg (inv_mem ha₀))
  · rw [h2, h3, h4]; group

theorem Blk5_card_le {α : G} (hα : AlphaSpec S z t α) : Nat.card ↥(Blk5 E α t) ≤ 5 := by
  classical
  have hZt : t ∈ (zpowers α ⊔ zpowers t : Subgroup G) := (h.mem_Zg hα).2 (Or.inr (Or.inl rfl))
  have hrep : ∀ B' : ↥(Blk5 E α t), ∃ e ∈ E2 E t,
      B'.1 = (fun a => a * e) '' ((zpowers α ⊔ zpowers t : Subgroup G) : Set G) := fun B' => B'.2
  choose r hr using hrep
  have hr1 : ∀ B', r B' ∈ E2 E t := fun B' => (hr B').1
  have hr2 : ∀ B', B'.1 = (fun a => a * r B') '' ((zpowers α ⊔ zpowers t : Subgroup G) : Set G) :=
    fun B' => (hr B').2
  let ψ : ↥(Blk5 E α t) × Fin 2 → ↥(E2 E t) := fun p =>
    if p.2 = 0 then ⟨r p.1, hr1 p.1⟩ else ⟨t * r p.1, by
      refine ⟨mul_mem h.t_mem_E (hr1 p.1).1, ?_, ?_, ?_⟩
      · have hc := h.t_comm_E (r p.1) (hr1 p.1).1
        calc t * r p.1 * (t * r p.1) = t * (r p.1 * t) * r p.1 := by group
          _ = t * (t * r p.1) * r p.1 := by rw [hc]
          _ = (t * t) * (r p.1 * r p.1) := by group
          _ = 1 := by rw [h.t_sq, (hr1 p.1).2.1, one_mul]
      · intro h1
        apply (hr1 p.1).2.2.2
        calc r p.1 = t * (t * r p.1) := by rw [← mul_assoc, h.t_sq, one_mul]
          _ = t * 1 := by rw [h1]
          _ = t := mul_one t
      · intro h1
        apply (hr1 p.1).2.2.1
        exact mul_left_cancel (h1.trans (mul_one t).symm)⟩
  have hinj : Function.Injective ψ := by
    rintro ⟨B₁, i₁⟩ ⟨B₂, i₂⟩ hψ
    have hmem : ∀ (B' : ↥(Blk5 E α t)) (i : Fin 2), (ψ (B', i) : G) ∈ B'.1 := by
      intro B' i
      rw [hr2 B']
      by_cases hi : i = 0
      · simp only [ψ, hi, ite_true]
        exact ⟨1, one_mem _, by simp⟩
      · simp only [ψ, hi, ite_false]
        exact ⟨t, hZt, rfl⟩
    have hB : B₁ = B₂ := by
      have h1 := hmem B₁ i₁
      have h2 := hmem B₂ i₂
      rw [hψ] at h1
      apply Subtype.ext
      rw [hr2 B₁, hr2 B₂]
      obtain ⟨a₁, ha₁, hx₁⟩ := (hr2 B₁ ▸ h1 : _ ∈ (fun a => a * r B₁) '' _)
      obtain ⟨a₂, ha₂, hx₂⟩ := (hr2 B₂ ▸ h2 : _ ∈ (fun a => a * r B₂) '' _)
      have hrel : r B₂ = (a₂⁻¹ * a₁) * r B₁ := by
        have : a₁ * r B₁ = a₂ * r B₂ := hx₁.trans hx₂.symm
        calc r B₂ = a₂⁻¹ * (a₂ * r B₂) := by group
          _ = a₂⁻¹ * (a₁ * r B₁) := by rw [this]
          _ = (a₂⁻¹ * a₁) * r B₁ := by group
      ext u
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨a * (a₂⁻¹ * a₁)⁻¹, mul_mem ha (inv_mem (mul_mem (inv_mem ha₂) ha₁)), ?_⟩
        show a * (a₂⁻¹ * a₁)⁻¹ * r B₂ = a * r B₁
        rw [hrel]; group
      · rintro ⟨a, ha, rfl⟩
        refine ⟨a * (a₂⁻¹ * a₁), mul_mem ha (mul_mem (inv_mem ha₂) ha₁), ?_⟩
        show a * (a₂⁻¹ * a₁) * r B₁ = a * r B₂
        rw [hrel]; group
    subst hB
    have hi : i₁ = i₂ := by
      by_contra hne
      have hv : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
      have hval : ∀ i : Fin 2, (ψ (B₁, i) : G) = if i = 0 then r B₁ else t * r B₁ := by
        intro i
        by_cases hi : i = 0 <;> simp [ψ, hi]
      have h12 := congrArg Subtype.val hψ
      rw [hval, hval] at h12
      rcases hv i₁ with rfl | rfl <;> rcases hv i₂ with rfl | rfl
      · exact hne rfl
      · simp at h12
        exact h.t_ne h12
      · simp at h12
        exact h.t_ne h12
      · exact hne rfl
    rw [hi]
  have hc := Nat.card_le_card_of_injective ψ hinj
  rw [Nat.card_prod, Nat.card_fin] at hc
  have h10 : Nat.card ↥(E2 E t) = 10 := by
    rw [Nat.card_coe_set_eq]; exact h.ef.card_two
  omega

@[expose] def cjSet {G : Type*} [Group G] (m : G) (B' : Set G) : Set G :=
  (fun u => m * u * m⁻¹) '' B'

omit h in
theorem cjSet_mul {G : Type*} [Group G] (m m' : G) (B' : Set G) :
    cjSet m (cjSet m' B') = cjSet (m * m') B' := by
  unfold cjSet
  rw [Set.image_image]
  congr 1
  ext u
  group

omit h in
theorem cjSet_one {G : Type*} [Group G] (B' : Set G) : cjSet 1 B' = B' := by
  unfold cjSet
  simp

omit h in
theorem mem_cjSet {G : Type*} [Group G] {m u : G} {B' : Set G} :
    u ∈ cjSet m B' ↔ m⁻¹ * u * m ∈ B' := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : m⁻¹ * (m * x * m⁻¹) * m = x := by group
    rwa [this]
  · intro h1
    exact ⟨m⁻¹ * u * m, h1, by group⟩

theorem cj_block {α : G} (hα : AlphaSpec S z t α) {m : G}
    (hm : m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G)) {B' : Set G}
    (hB' : B' ∈ Blk5 E α t) : cjSet m B' ∈ Blk5 E α t := by
  obtain ⟨e, he, rfl⟩ := hB'
  obtain ⟨a₀, ha₀, e', he', h0⟩ := h.Theta_inv hα hm he
  refine ⟨e', he', ?_⟩
  ext u
  constructor
  · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨(m * a * m⁻¹) * a₀, mul_mem (h.Zg_conj hα hm ha) ha₀, ?_⟩
    show (m * a * m⁻¹ * a₀) * e' = m * (a * e) * m⁻¹
    calc (m * a * m⁻¹ * a₀) * e' = (m * a * m⁻¹) * (a₀ * e') := by group
      _ = (m * a * m⁻¹) * (m * e * m⁻¹) := by rw [h0]
      _ = m * (a * e) * m⁻¹ := by group
  · rintro ⟨a', ha', rfl⟩
    apply (mem_cjSet).2
    refine ⟨m⁻¹ * (a' * a₀⁻¹) * m, ?_, ?_⟩
    · have := h.Zg_conj hα (inv_mem hm) (mul_mem ha' (inv_mem ha₀))
      simpa using this
    · show m⁻¹ * (a' * a₀⁻¹) * m * e = m⁻¹ * (a' * e') * m
      have he'' : e' = a₀⁻¹ * (m * e * m⁻¹) := by rw [h0]; group
      rw [he'']; group

@[expose] noncomputable def rhoM {α : G} (hα : AlphaSpec S z t α) :
    ↥(normalizer ((S ⊔ E : Subgroup G) : Set G)) →* Equiv.Perm ↥(Blk5 E α t) :=
  MonoidHom.mk' (fun m =>
    { toFun := fun B' => ⟨cjSet (m : G) B'.1, h.cj_block hα m.2 B'.2⟩
      invFun := fun B' => ⟨cjSet (m : G)⁻¹ B'.1, h.cj_block hα (inv_mem m.2) B'.2⟩
      left_inv := fun B' => Subtype.ext (by
        simp only; rw [cjSet_mul, inv_mul_cancel, cjSet_one])
      right_inv := fun B' => Subtype.ext (by
        simp only; rw [cjSet_mul, mul_inv_cancel, cjSet_one]) })
    (fun m m' => Equiv.ext fun B' => Subtype.ext (by
      simp only [Equiv.Perm.mul_apply, Equiv.coe_fn_mk]
      rw [cjSet_mul]
      rfl))

theorem ker_rhoM_le {α : G} (hα : AlphaSpec S z t α)
    {m : ↥(normalizer ((S ⊔ E : Subgroup G) : Set G))} (hm : m ∈ (rhoM h hα).ker) :
    (m : G) ∈ Fsub h hα := by
  refine ⟨m.2, fun e he => ?_⟩
  have hB : ((fun a => a * e) '' ((zpowers α ⊔ zpowers t : Subgroup G) : Set G)) ∈ Blk5 E α t :=
    ⟨e, he, rfl⟩
  have h1 := congrArg (fun p : Equiv.Perm ↥(Blk5 E α t) => (p ⟨_, hB⟩).1)
    (MonoidHom.mem_ker.1 hm)
  simp only [rhoM, MonoidHom.mk'_apply, Equiv.coe_fn_mk, Equiv.Perm.coe_one, id_eq] at h1
  have h2 : (m : G) * e * (m : G)⁻¹ ∈ cjSet (m : G)
      ((fun a => a * e) '' ((zpowers α ⊔ zpowers t : Subgroup G) : Set G)) :=
    ⟨e, ⟨1, one_mem _, by simp⟩, rfl⟩
  rw [h1] at h2
  obtain ⟨a, ha, hae⟩ := h2
  exact ⟨a, ha, hae.symm⟩

theorem card_M_le_F {α : G} (hα : AlphaSpec S z t α) :
    Nat.card ↥(normalizer ((S ⊔ E : Subgroup G) : Set G)) ≤ 120 * Nat.card ↥(Fsub h hα) := by
  set K := (rhoM h hα).ker with hK
  have h1 := Subgroup.card_mul_index K
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card ↥(rhoM h hα).range ≤ 120 := by
    calc Nat.card ↥(rhoM h hα).range ≤ Nat.card (Equiv.Perm ↥(Blk5 E α t)) :=
          Subgroup.card_le_card_group _
      _ = (Nat.card ↥(Blk5 E α t)).factorial := Nat.card_perm
      _ ≤ (5 : ℕ).factorial := Nat.factorial_le (h.Blk5_card_le hα)
      _ = 120 := by decide
  have h3 : Nat.card ↥K ≤ Nat.card ↥(Fsub h hα) := by
    refine Nat.card_le_card_of_injective
      (fun k => (⟨(k : G), h.ker_rhoM_le hα k.2⟩ : ↥(Fsub h hα))) ?_
    intro k k' hkk
    have h4 := congrArg (fun p : ↥(Fsub h hα) => (p : G)) hkk
    exact Subtype.ext (Subtype.ext h4)
  calc Nat.card ↥(normalizer ((S ⊔ E : Subgroup G) : Set G))
      = Nat.card ↥K * Nat.card ↥(rhoM h hα).range := h1.symm
    _ ≤ Nat.card ↥(Fsub h hα) * 120 := Nat.mul_le_mul h3 h2
    _ = 120 * Nat.card ↥(Fsub h hα) := by ring

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
