module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31SL2
public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.GH74.GLS.Stage2.Local (InducedPGL2)
open scoped commutatorElement

theorem l31_diag_proj_one {X : Type} [Group X] {L₁ L₂ : Subgroup X}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    {t : X} (h21 : ∀ b ∈ L₂, t * b * t⁻¹ ∈ L₁)
    {P : Subgroup X} (hP : P ≤ L₁ ⊔ L₂) (hPperf : Group.IsPerfect ↥P)
    (hPns : ¬ Group.IsSolvable ↥P) (hPt : ∀ p ∈ P, t * p = p * t) :
    ∃ X₁ : Subgroup X, X₁ ≤ L₁ ∧ ¬ Group.IsSolvable ↥X₁ ∧
      ∀ g : X, (∀ a ∈ L₁, g * a * g⁻¹ ∈ L₁) → (∀ b ∈ L₂, g * b * g⁻¹ ∈ L₂) →
        (∀ ζ ∈ L₁ ⊓ L₂, g * ζ = ζ * g) → (∀ p ∈ P, g * p = p * g) →
        ∀ x ∈ X₁, g * x = x * g := by
  have hdec : ∀ p ∈ P, ∃ x ∈ L₁, ∃ y ∈ L₂, x * y = p := fun p hp =>
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm (hP hp)
  let X₁ : Subgroup X :=
    { carrier := {x | x ∈ L₁ ∧ ∃ y ∈ L₂, x * y ∈ P}
      mul_mem' := by
        rintro x x' ⟨hx, y, hy, hxy⟩ ⟨hx', y', hy', hxy'⟩
        refine ⟨L₁.mul_mem hx hx', y * y', L₂.mul_mem hy hy', ?_⟩
        have : x * x' * (y * y') = x * y * (x' * y') := by
          calc x * x' * (y * y') = x * (x' * y) * y' := by group
            _ = x * (y * x') * y' := by rw [hcomm x' hx' y hy]
            _ = x * y * (x' * y') := by group
        rw [this]; exact P.mul_mem hxy hxy'
      one_mem' := ⟨L₁.one_mem, 1, L₂.one_mem, by simp⟩
      inv_mem' := by
        rintro x ⟨hx, y, hy, hxy⟩
        refine ⟨L₁.inv_mem hx, y⁻¹, L₂.inv_mem hy, ?_⟩
        have : x⁻¹ * y⁻¹ = (x * y)⁻¹ := by
          rw [mul_inv_rev, hcomm x⁻¹ (L₁.inv_mem hx) y⁻¹ (L₂.inv_mem hy)]
        rw [this]; exact P.inv_mem hxy }
  have hX₁L₁ : X₁ ≤ L₁ := fun x hx => hx.1
  refine ⟨X₁, hX₁L₁, ?_, ?_⟩
  ·
    intro hsolv
    apply hPns
    let ψ : ↥X₁ × ↥L₂ →* X := MonoidHom.noncommCoprod X₁.subtype L₂.subtype
      (fun a b => hcomm a (hX₁L₁ a.2) b b.2)
    let Q : Subgroup (↥X₁ × ↥L₂) := P.comap ψ
    let σ : ↥Q →* ↥X₁ := (MonoidHom.fst ↥X₁ ↥L₂).comp Q.subtype
    let ρ : ↥Q →* ↥P := ψ.subgroupComap P
    have hψ : ∀ a : ↥X₁, ∀ b : ↥L₂, ψ (a, b) = (a : X) * b := fun a b => rfl
    have hρ : Function.Surjective ρ := by
      intro p
      obtain ⟨x, hx, y, hy, hxy⟩ := hdec p p.2
      have hxP : x * y ∈ P := hxy ▸ p.2
      refine ⟨⟨(⟨x, hx, y, hy, hxP⟩, ⟨y, hy⟩), ?_⟩, ?_⟩
      · show ψ _ ∈ P
        rw [hψ]
        exact hxP
      · apply Subtype.ext
        show ψ _ = _
        rw [hψ]
        exact hxy
    have hkerL₁ : ∀ c : σ.ker, ((c.1.1.2 : ↥L₂) : X) ∈ L₁ := by
      intro c
      have hc1 : c.1.1.1 = 1 := c.2
      have hmem : ψ c.1.1 ∈ P := c.1.2
      have hψc : ψ c.1.1 = ((c.1.1.2 : ↥L₂) : X) := by
        have : c.1.1 = (1, c.1.1.2) := Prod.ext hc1 rfl
        rw [this, hψ]
        simp
      rw [hψc] at hmem
      have h1 := h21 _ c.1.1.2.2
      have h2 := hPt _ hmem
      have h3 : t * ((c.1.1.2 : ↥L₂) : X) * t⁻¹ = ((c.1.1.2 : ↥L₂) : X) := by
        rw [h2]; group
      rwa [h3] at h1
    have hker : ∀ a b : σ.ker, a * b = b * a := by
      intro a b
      apply Subtype.ext; apply Subtype.ext; apply Prod.ext
      · have ha : a.1.1.1 = 1 := a.2
        have hb : b.1.1.1 = 1 := b.2
        show a.1.1.1 * b.1.1.1 = b.1.1.1 * a.1.1.1
        rw [ha, hb]
      · apply Subtype.ext
        show ((a.1.1.2 : ↥L₂) : X) * ((b.1.1.2 : ↥L₂) : X) =
          ((b.1.1.2 : ↥L₂) : X) * ((a.1.1.2 : ↥L₂) : X)
        exact hcomm _ (hkerL₁ a) _ b.1.1.2.2
    have : Group.IsSolvable σ.ker := Group.isSolvable_of_comm hker
    have : Group.IsSolvable ↥Q :=
      Group.isSolvable_of_ker_le_range σ.ker.subtype σ (by simp)
    exact Group.isSolvable_of_surjective hρ
  ·
    intro g hgL₁ hgL₂ hgZ hgP
    have hcm : ∀ (H : Subgroup X) {a b : X}, a ∈ H → b ∈ H → ⁅a, b⁆ ∈ H := by
      intro H a b ha hb
      simp only [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    have huniq : ∀ {x y x' y' : X}, x ∈ L₁ → y ∈ L₂ → x' ∈ L₁ → y' ∈ L₂ → x * y = x' * y' →
        x'⁻¹ * x ∈ L₁ ⊓ L₂ := by
      intro x y x' y' hx hy hx' hy' h
      refine ⟨L₁.mul_mem (L₁.inv_mem hx') hx, ?_⟩
      have : x'⁻¹ * x = y' * y⁻¹ := by
        calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
          _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [h]
          _ = y' * y⁻¹ := by group
      rw [this]; exact L₂.mul_mem hy' (L₂.inv_mem hy)
    have hcommOf : ∀ {x y u v : X}, x ∈ L₁ → y ∈ L₂ → u ∈ L₁ → v ∈ L₂ → x * y = u * v →
        Commute g u → Commute g x := by
      intro x y u v hx hy hu hv h hgu
      have hz : u⁻¹ * x ∈ L₁ ⊓ L₂ := huniq hx hy hu hv h
      have hx' : x = u * (u⁻¹ * x) := by group
      rw [hx']
      exact hgu.mul_right (hgZ _ hz)
    let Y : Subgroup X :=
      { carrier := {p | p ∈ P ∧ ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = p → Commute g x}
        mul_mem' := by
          rintro p q ⟨hpP, hp⟩ ⟨hqP, hq⟩
          refine ⟨P.mul_mem hpP hqP, ?_⟩
          intro x hx y hy hxy
          obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := hdec p hpP
          obtain ⟨x₂, hx₂, y₂, hy₂, rfl⟩ := hdec q hqP
          have h12 : x₁ * y₁ * (x₂ * y₂) = (x₁ * x₂) * (y₁ * y₂) := by
            calc x₁ * y₁ * (x₂ * y₂) = x₁ * (y₁ * x₂) * y₂ := by group
              _ = x₁ * (x₂ * y₁) * y₂ := by rw [← hcomm x₂ hx₂ y₁ hy₁]
              _ = (x₁ * x₂) * (y₁ * y₂) := by group
          exact hcommOf hx hy (L₁.mul_mem hx₁ hx₂) (L₂.mul_mem hy₁ hy₂) (hxy.trans h12)
            ((hp x₁ hx₁ y₁ hy₁ rfl).mul_right (hq x₂ hx₂ y₂ hy₂ rfl))
        one_mem' := by
          refine ⟨P.one_mem, ?_⟩
          intro x hx y hy hxy
          exact hcommOf hx hy L₁.one_mem L₂.one_mem (hxy.trans (mul_one 1).symm)
            (Commute.one_right g)
        inv_mem' := by
          rintro p ⟨hpP, hp⟩
          refine ⟨P.inv_mem hpP, ?_⟩
          intro x hx y hy hxy
          obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := hdec p hpP
          have h1 : (x₁ * y₁)⁻¹ = x₁⁻¹ * y₁⁻¹ := by
            rw [mul_inv_rev, hcomm x₁⁻¹ (L₁.inv_mem hx₁) y₁⁻¹ (L₂.inv_mem hy₁)]
          exact hcommOf hx hy (L₁.inv_mem hx₁) (L₂.inv_mem hy₁) (hxy.trans h1)
            ((hp x₁ hx₁ y₁ hy₁ rfl).inv_right) }
    have hcomm_gen : ∀ x₁ ∈ L₁, ∀ y₁ ∈ L₂, x₁ * y₁ ∈ P →
        ∃ ε ∈ L₁ ⊓ L₂, g * x₁ * g⁻¹ = x₁ * ε := by
      intro x₁ hx₁ y₁ hy₁ hp
      have hg1 : g * x₁ * g⁻¹ ∈ L₁ := hgL₁ x₁ hx₁
      have hg2 : g * y₁ * g⁻¹ ∈ L₂ := hgL₂ y₁ hy₁
      have hgp : g * x₁ * g⁻¹ * (g * y₁ * g⁻¹) = x₁ * y₁ := by
        have h0 := hgP _ hp
        calc g * x₁ * g⁻¹ * (g * y₁ * g⁻¹) = g * (x₁ * y₁) * g⁻¹ := by group
          _ = x₁ * y₁ * g * g⁻¹ := by rw [h0]
          _ = x₁ * y₁ := by group
      exact ⟨x₁⁻¹ * (g * x₁ * g⁻¹), huniq hg1 hg2 hx₁ hy₁ hgp, by group⟩
    have hPY : P ≤ Y := by
      have hle : ⁅P, P⁆ ≤ Y := by
        rw [Subgroup.commutator_le]
        intro p hp q hq
        refine ⟨hcm P hp hq, ?_⟩
        intro x hx y hy hxy
        obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := hdec p hp
        obtain ⟨x₂, hx₂, y₂, hy₂, rfl⟩ := hdec q hq
        obtain ⟨ε₁, hε₁, hg₁⟩ := hcomm_gen x₁ hx₁ y₁ hy₁ hp
        obtain ⟨ε₂, hε₂, hg₂⟩ := hcomm_gen x₂ hx₂ y₂ hy₂ hq
        have hcom : ⁅x₁ * y₁, x₂ * y₂⁆ = ⁅x₁, x₂⁆ * ⁅y₁, y₂⁆ :=
          CFSG.GroupTheory.commutatorElement_mul_of_commute hcomm hx₁ hx₂ hy₁ hy₂
        have hgc : Commute g ⁅x₁, x₂⁆ := by
          have h1 : g * ⁅x₁, x₂⁆ * g⁻¹ = ⁅g * x₁ * g⁻¹, g * x₂ * g⁻¹⁆ := by
            simp only [commutatorElement_def]; group
          have h2 : ⁅g * x₁ * g⁻¹, g * x₂ * g⁻¹⁆ = ⁅x₁, x₂⁆ := by
            rw [hg₁, hg₂,
              CFSG.GroupTheory.commutatorElement_mul_of_commute hcomm hx₁ hx₂ hε₁.2 hε₂.2]
            have h3 : ⁅ε₁, ε₂⁆ = 1 :=
              commutatorElement_eq_one_iff_mul_comm.mpr (hcomm ε₁ hε₁.1 ε₂ hε₂.2)
            rw [h3, mul_one]
          have h4 : g * ⁅x₁, x₂⁆ * g⁻¹ = ⁅x₁, x₂⁆ := h1.trans h2
          show g * ⁅x₁, x₂⁆ = ⁅x₁, x₂⁆ * g
          calc g * ⁅x₁, x₂⁆ = g * ⁅x₁, x₂⁆ * g⁻¹ * g := by group
            _ = ⁅x₁, x₂⁆ * g := by rw [h4]
        exact hcommOf hx hy (hcm L₁ hx₁ hx₂) (hcm L₂ hy₁ hy₂) (hxy.trans hcom) hgc
      exact (Subgroup.isPerfect_iff.mp hPperf).ge.trans hle
    intro x hx
    obtain ⟨hxL, y, hy, hxy⟩ := hx
    exact (hPY hxy).2 x hxL y hy rfl

theorem l31_diag_proj {X : Type} [Group X] {L₁ L₂ : Subgroup X}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    {t : X} (h12 : ∀ a ∈ L₁, t * a * t⁻¹ ∈ L₂) (h21 : ∀ b ∈ L₂, t * b * t⁻¹ ∈ L₁)
    {P : Subgroup X} (hP : P ≤ L₁ ⊔ L₂) (hPperf : Group.IsPerfect ↥P)
    (hPns : ¬ Group.IsSolvable ↥P) (hPt : ∀ p ∈ P, t * p = p * t) :
    ∃ X₁ X₂ : Subgroup X, X₁ ≤ L₁ ∧ X₂ ≤ L₂ ∧ ¬ Group.IsSolvable ↥X₁ ∧
      ¬ Group.IsSolvable ↥X₂ ∧
      ∀ g : X, (∀ a ∈ L₁, g * a * g⁻¹ ∈ L₁) → (∀ b ∈ L₂, g * b * g⁻¹ ∈ L₂) →
        (∀ ζ ∈ L₁ ⊓ L₂, g * ζ = ζ * g) → (∀ p ∈ P, g * p = p * g) →
        (∀ x ∈ X₁, g * x = x * g) ∧ (∀ y ∈ X₂, g * y = y * g) := by
  obtain ⟨X₁, hX₁, hX₁ns, hX₁g⟩ := l31_diag_proj_one hcomm h21 hP hPperf hPns hPt
  obtain ⟨X₂, hX₂, hX₂ns, hX₂g⟩ := l31_diag_proj_one (L₁ := L₂) (L₂ := L₁)
    (fun a ha b hb => (hcomm b hb a ha).symm) h12 (hP.trans (sup_comm L₁ L₂).le)
    hPperf hPns hPt
  refine ⟨X₁, X₂, hX₁, hX₂, hX₁ns, hX₂ns, ?_⟩
  intro g hg₁ hg₂ hgZ hgP
  exact ⟨hX₁g g hg₁ hg₂ hgZ hgP, hX₂g g hg₂ hg₁ (by rwa [inf_comm]) hgP⟩

theorem l31_not_isSolvable_subgroupOf {L : Type} [Group L] {A B : Subgroup L} (h : A ≤ B)
    (hA : ¬ Group.IsSolvable ↥A) : ¬ Group.IsSolvable ↥(A.subgroupOf B) := fun _hs =>
  hA (Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe h).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe h).surjective)

theorem l31_centralizer_diag {X : Type} [Group X] {L₁ L₂ : Subgroup X}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hZ₁ : ∀ x ∈ L₁, (∀ y ∈ L₁, x * y = y * x) → x ∈ L₂)
    (hZ₂ : ∀ x ∈ L₂, (∀ y ∈ L₂, x * y = y * x) → x ∈ L₁)
    {F₁ F₂ : Type} [Field F₁] [Finite F₁] [Field F₂] [Finite F₂]
    (hF₁ : Odd (Nat.card F₁)) (hF₂ : Odd (Nat.card F₂))
    (e₁ : L₁ ≃* StatedSL 2 F₁) (e₂ : L₂ ≃* StatedSL 2 F₂)
    {t : X} (h12 : ∀ a ∈ L₁, t * a * t⁻¹ ∈ L₂) (h21 : ∀ b ∈ L₂, t * b * t⁻¹ ∈ L₁)
    {P : Subgroup X} (hP : P ≤ L₁ ⊔ L₂) (hPperf : Group.IsPerfect ↥P)
    (hPns : ¬ Group.IsSolvable ↥P) (hPt : ∀ p ∈ P, t * p = p * t) {c : X} (hc : c ∈ L₁ ⊔ L₂)
    (hcP : ∀ p ∈ P, c * p = p * c) :
    c ∈ L₁ ⊓ L₂ := by
  obtain ⟨X₁, X₂, hX₁, hX₂, hns₁, hns₂, key⟩ := l31_diag_proj hcomm h12 h21 hP hPperf hPns hPt
  obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hc
  have hbcomm : ∀ x ∈ L₁, b * x = x * b := fun x hx => (hcomm x hx b hb).symm
  have hacomm : ∀ y ∈ L₂, a * y = y * a := fun y hy => hcomm a ha y hy
  have hn₁ : ∀ x ∈ L₁, a * b * x * (a * b)⁻¹ ∈ L₁ := by
    intro x hx
    have : a * b * x * (a * b)⁻¹ = a * x * a⁻¹ := by
      calc a * b * x * (a * b)⁻¹ = a * (b * x) * b⁻¹ * a⁻¹ := by group
        _ = a * (x * b) * b⁻¹ * a⁻¹ := by rw [hbcomm x hx]
        _ = a * x * a⁻¹ := by group
    rw [this]; exact L₁.mul_mem (L₁.mul_mem ha hx) (L₁.inv_mem ha)
  have hn₂ : ∀ y ∈ L₂, a * b * y * (a * b)⁻¹ ∈ L₂ := by
    intro y hy
    have hw : b * y * b⁻¹ ∈ L₂ := L₂.mul_mem (L₂.mul_mem hb hy) (L₂.inv_mem hb)
    have : a * b * y * (a * b)⁻¹ = b * y * b⁻¹ := by
      have h := hacomm _ hw
      calc a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
        _ = (b * y * b⁻¹) * a * a⁻¹ := by rw [h]
        _ = b * y * b⁻¹ := by group
    rw [this]; exact hw
  have hnZ : ∀ ζ ∈ L₁ ⊓ L₂, a * b * ζ = ζ * (a * b) := by
    intro ζ hζ
    calc a * b * ζ = a * (b * ζ) := by group
      _ = a * (ζ * b) := by rw [hbcomm ζ hζ.1]
      _ = (a * ζ) * b := by group
      _ = (ζ * a) * b := by rw [hacomm ζ hζ.2]
      _ = ζ * (a * b) := by group
  obtain ⟨h1, h2⟩ := key (a * b) hn₁ hn₂ hnZ hcP
  have ha₁ : ∀ x ∈ X₁, a * x = x * a := by
    intro x hx
    have hxL : x ∈ L₁ := hX₁ hx
    have h := h1 x hx
    refine mul_right_cancel (b := b) ?_
    calc a * x * b = a * (x * b) := by group
      _ = a * (b * x) := by rw [hbcomm x hxL]
      _ = a * b * x := by group
      _ = x * (a * b) := h
      _ = x * a * b := by group
  have hb₂ : ∀ y ∈ X₂, b * y = y * b := by
    intro y hy
    have hyL : y ∈ L₂ := hX₂ hy
    have h := h2 y hy
    refine mul_left_cancel (a := a) ?_
    calc a * (b * y) = a * b * y := by group
      _ = y * (a * b) := h
      _ = (y * a) * b := by group
      _ = (a * y) * b := by rw [hacomm y hyL]
      _ = a * (y * b) := by group
  have haZ : (⟨a, ha⟩ : ↥L₁) ∈ Subgroup.center ↥L₁ :=
    centralizer_le_center_of_sl2 hF₁ e₁ (l31_not_isSolvable_subgroupOf hX₁ hns₁)
      (g := ⟨a, ha⟩) (fun x hx => Subtype.ext (ha₁ x hx))
  have hbZ : (⟨b, hb⟩ : ↥L₂) ∈ Subgroup.center ↥L₂ :=
    centralizer_le_center_of_sl2 hF₂ e₂ (l31_not_isSolvable_subgroupOf hX₂ hns₂)
      (g := ⟨b, hb⟩) (fun y hy => Subtype.ext (hb₂ y hy))
  have haL₂ : a ∈ L₂ := hZ₁ a ha fun y hy =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.mp haZ ⟨y, hy⟩)).symm
  have hbL₁ : b ∈ L₁ := hZ₂ b hb fun y hy =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.mp hbZ ⟨y, hy⟩)).symm
  exact ⟨L₁.mul_mem ha hbL₁, L₂.mul_mem haL₂ hb⟩

theorem l31_pgl_trivial {X : Type} [Group X] [Finite X] {L T : Subgroup X} {q : ℕ} (hq : Odd q)
    (hpgl : InducedPGL2 L T q) {X₁ : Subgroup X} (hX₁ : X₁ ≤ L)
    (hX₁ns : ¬ Group.IsSolvable ↥X₁) {g : X} (hgT : g ∈ T)
    (hg : ∀ x ∈ X₁, g * x = x * g) : g ∈ centralizer (L : Set X) := by
  obtain ⟨hnorm, F, hFfield, hFfin, hFq, ⟨e⟩⟩ := hpgl
  have hFq' : Nat.card F = q := hFq
  have hXN : X₁ ≤ L ⊔ T := hX₁.trans le_sup_left
  have hgN : g ∈ L ⊔ T := Subgroup.mem_sup_right hgT
  let K : Subgroup ↥(L ⊔ T) := (centralizer (L : Set X)).subgroupOf (L ⊔ T)
  let π : ↥(L ⊔ T) →* ↥(L ⊔ T) ⧸ K := QuotientGroup.mk' K
  let ξ : ↥X₁ →* ↥(L ⊔ T) ⧸ K := π.comp (Subgroup.inclusion hXN)
  have hker : ∀ a b : ξ.ker, a * b = b * a := by
    intro a b
    have ha : ((a.1 : ↥X₁) : X) ∈ centralizer (L : Set X) := by
      have h0 : ξ a.1 = 1 := a.2
      have h0' : Subgroup.inclusion hXN a.1 ∈ K :=
        (QuotientGroup.eq_one_iff (N := K) (Subgroup.inclusion hXN a.1)).mp h0
      exact h0'
    apply Subtype.ext; apply Subtype.ext
    show ((a.1 : ↥X₁) : X) * ((b.1 : ↥X₁) : X) = ((b.1 : ↥X₁) : X) * ((a.1 : ↥X₁) : X)
    exact (Subgroup.mem_centralizer_iff.mp ha _ (hX₁ b.1.2)).symm
  have hsolvKer : Group.IsSolvable ξ.ker := Group.isSolvable_of_comm hker
  have hsolvRange : ¬ Group.IsSolvable ↥ξ.range := by
    intro hsr
    apply hX₁ns
    exact Group.isSolvable_of_ker_le_range ξ.ker.subtype ξ.rangeRestrict
      (by simp [MonoidHom.ker_rangeRestrict])
  have hgY : ∀ y ∈ ξ.range, π ⟨g, hgN⟩ * y = y * π ⟨g, hgN⟩ := by
    rintro _ ⟨x, rfl⟩
    show π ⟨g, hgN⟩ * π (Subgroup.inclusion hXN x) = π (Subgroup.inclusion hXN x) * π ⟨g, hgN⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hg x x.2
  have h1 : π ⟨g, hgN⟩ = 1 :=
    centralizer_eq_one_of_pgl2 (by rwa [hFq']) e hsolvRange hgY
  have h2 : (⟨g, hgN⟩ : ↥(L ⊔ T)) ∈ K :=
    (QuotientGroup.eq_one_iff (N := K) (⟨g, hgN⟩ : ↥(L ⊔ T))).mp h1
  exact h2

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
