module

public import CFSG.ClassicalInvolution.Q3.Q3PPFundFix

public section

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.ComponentClassification CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.ClassicalInvolution.Balance

@[expose] def OutOne (X : Type) [Group X] : Prop :=
  ∀ a b : MulAut X, (∀ g : X, a ≠ MulAut.conj g) → (∀ g : X, b ≠ MulAut.conj g) →
    ∃ g : X, a = MulAut.conj g * b

theorem mulAut_mul_conj {X : Type} [Group X] (b : MulAut X) (m : X) :
    b * MulAut.conj m = MulAut.conj (b m) * b := by
  ext x
  simp [MulAut.conj_apply]

theorem conj_eq_one_iff_of_center_eq_bot {X : Type} [Group X] (hZ : Subgroup.center X = ⊥)
    (g : X) : MulAut.conj g = 1 ↔ g = 1 := by
  constructor
  · intro hg
    have hc : g ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro x
      have := congrArg (fun φ : MulAut X => φ x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * g = (g * x * g⁻¹) * g := by rw [this]
        _ = g * x := by group
    rw [hZ] at hc
    exact hc
  · rintro rfl
    exact map_one _

theorem OutOne.of_card_dvd_two {X : Type} [Group X]
    (h : Nat.card (OuterAutomorphisms.Outer X) ∣ 2) : OutOne X := by
  intro a b ha hb
  have hpos : 0 < Nat.card (OuterAutomorphisms.Outer X) := Nat.pos_of_dvd_of_pos h (by norm_num)
  have hfin : Finite (OuterAutomorphisms.Outer X) := Nat.finite_of_card_ne_zero hpos.ne'
  have hnot : ∀ c : MulAut X, (∀ g : X, c ≠ MulAut.conj g) →
      (c : OuterAutomorphisms.Outer X) ≠ 1 := by
    intro c hc h1
    obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff c).mp h1
    exact hc g hg.symm
  have h2 : Nat.card (OuterAutomorphisms.Outer X) = 2 := by
    have hnt : Nontrivial (OuterAutomorphisms.Outer X) := ⟨⟨(a : OuterAutomorphisms.Outer X), 1,
      hnot a ha⟩⟩
    have hge : 2 ≤ Nat.card (OuterAutomorphisms.Outer X) := by
      have := Finite.one_lt_card (α := OuterAutomorphisms.Outer X)
      omega
    exact le_antisymm (Nat.le_of_dvd (by norm_num) h) hge
  have hab : (a : OuterAutomorphisms.Outer X) = (b : OuterAutomorphisms.Outer X) := by
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : OuterAutomorphisms.Outer X)).mp h2
    rw [hy _ (hnot a ha), hy _ (hnot b hb)]
  obtain ⟨k, hk⟩ := (QuotientGroup.eq.mp hab)
  refine ⟨b (k⁻¹), ?_⟩
  rw [← mulAut_mul_conj, map_inv]
  have : MulAut.conj k = a⁻¹ * b := hk
  calc a = b * (a⁻¹ * b)⁻¹ := by group
    _ = b * (MulAut.conj k)⁻¹ := by rw [this]

theorem congr_conj {A B : Type} [Group A] [Group B] (e : A ≃* B) (a : A) :
    MulAut.congr e (MulAut.conj a) = MulAut.conj (e a) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem OutOne.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : OutOne A) :
    OutOne B := by
  intro a b ha hb
  have hp : ∀ c : MulAut B, (∀ g : B, c ≠ MulAut.conj g) →
      ∀ g : A, (MulAut.congr e).symm c ≠ MulAut.conj g := by
    intro c hc g hg
    apply hc (e g)
    rw [← congr_conj, ← hg, MulEquiv.apply_symm_apply]
  obtain ⟨g, hg⟩ := h _ _ (hp a ha) (hp b hb)
  refine ⟨e g, ?_⟩
  have h1 := congrArg (MulAut.congr e) hg
  rwa [MulEquiv.apply_symm_apply, map_mul, congr_conj, MulEquiv.apply_symm_apply] at h1

theorem eq_one_or_conj_of_invol {X : Type} [Group X] (hZ : Subgroup.center X = ⊥)
    (hout : OutOne X) {R : Subgroup X} {t : X} (ht : t * t = 1) (ht1 : t ≠ 1)
    (hC : ∀ g : X, (∀ r ∈ R, g * r = r * g) → g * g = 1 → g = 1 ∨ g = t)
    (γ : MulAut X) (hγR : ∀ r ∈ R, γ r = r) (hγ2 : γ * γ = MulAut.conj t)
    (hγC : ∀ g : X, (∀ r ∈ R, g * r = r * g) → γ g = g⁻¹)
    (ρ : MulAut X) (hρ2 : ρ * ρ = 1) (hρR : ∀ r ∈ R, ρ r = r) :
    ρ = 1 ∨ ρ = MulAut.conj t := by
  have hct1 : (MulAut.conj t : MulAut X) ≠ 1 := fun h =>
    ht1 ((conj_eq_one_iff_of_center_eq_bot hZ t).mp h)
  have hγγ : ∀ y, γ (γ y) = t * y * t⁻¹ := fun y => by
    have := congrArg (fun φ : MulAut X => φ y) hγ2
    simpa using this
  have hinn : ∀ g : X, (∀ r ∈ R, MulAut.conj g r = r) → MulAut.conj g * MulAut.conj g = 1 →
      MulAut.conj g = 1 ∨ MulAut.conj g = MulAut.conj t := by
    intro g hg hg2
    have hgC : ∀ r ∈ R, g * r = r * g := by
      intro r hr
      have := hg r hr
      simp only [MulAut.conj_apply] at this
      calc g * r = (g * r * g⁻¹) * g := by group
        _ = r * g := by rw [this]
    have hgg : g * g = 1 := by
      have : MulAut.conj (g * g) = 1 := by rw [map_mul]; exact hg2
      exact (conj_eq_one_iff_of_center_eq_bot hZ _).mp this
    rcases hC g hgC hgg with rfl | rfl
    · left
      exact map_one _
    · right
      rfl
  by_cases hρi : ∃ g, ρ = MulAut.conj g
  · obtain ⟨g, rfl⟩ := hρi
    exact hinn g hρR hρ2
  · push Not at hρi
    have hγn : ∀ g : X, γ ≠ MulAut.conj g := by
      intro g hg
      have hfix : ∀ r ∈ R, g * r = r * g := by
        intro r hr
        have := hγR r hr
        rw [hg] at this
        simp only [MulAut.conj_apply] at this
        calc g * r = (g * r * g⁻¹) * g := by group
          _ = r * g := by rw [this]
      have h1 := hγC g hfix
      rw [hg] at h1
      simp only [MulAut.conj_apply] at h1
      have hgg : g * g = 1 := by
        calc g * g = (g * g * g⁻¹) * g := by group
          _ = g⁻¹ * g := by rw [h1]
          _ = 1 := inv_mul_cancel g
      have h2 : γ * γ = 1 := by
        rw [hg, ← map_mul, hgg, map_one]
      rw [h2] at hγ2
      exact hct1 hγ2.symm
    obtain ⟨g, hg⟩ := hout ρ γ hρi hγn
    have hfix : ∀ r ∈ R, g * r = r * g := by
      intro r hr
      have h1 : ρ r = r := hρR r hr
      rw [hg] at h1
      simp only [MulAut.mul_apply, MulAut.conj_apply, hγR r hr] at h1
      calc g * r = (g * r * g⁻¹) * g := by group
        _ = r * g := by rw [h1]
    have hγg := hγC g hfix
    exfalso
    have hsq : ρ * ρ = MulAut.conj t := by
      rw [hg]
      ext x
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hγg, hγγ, inv_inv]
      group
    rw [hsq] at hρ2
    exact hct1 hρ2

theorem fixedSubgroup_conj_eq {X : Type} [Group X] (s : X) :
    fixedSubgroup (MulAut.conj s) = Subgroup.centralizer ({s} : Set X) := by
  ext x
  rw [mem_fixedSubgroup_iff, Subgroup.mem_centralizer_singleton_iff]
  change s * x * s⁻¹ = x ↔ x * s = s * x
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem fixedSubgroup_one_eq_top {X : Type} [Group X] : fixedSubgroup (1 : MulAut X) = ⊤ := by
  ext x
  simp [mem_fixedSubgroup_iff]

theorem fixedOddFreeFund_of_center_eq_bot {c : CompData} (hZ : Subgroup.center c.G = ⊥)
    (h : ∀ ρ : MulAut c.G, ρ * ρ = 1 → (∃ R ∈ c.fund, ∀ r ∈ R, ρ r = r) →
      oddCoreIn (fixedSubgroup ρ) = ⊥) : FixedOddFreeFund c := by
  intro ρ hρ2 ⟨R, hR, hρR⟩
  have hinj : Function.Injective (QuotientGroup.mk' (Subgroup.center c.G)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  let e : c.G ≃* (c.G ⧸ Subgroup.center c.G) :=
    MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center c.G))
      ⟨hinj, QuotientGroup.mk'_surjective _⟩
  have he : ∀ r : c.G, e r = (QuotientGroup.mk r : c.G ⧸ Subgroup.center c.G) := fun r => rfl
  set ρ' : MulAut c.G := (MulAut.congr e).symm ρ with hρ'
  have hρρ' : MulAut.congr e ρ' = ρ := (MulAut.congr e).apply_symm_apply ρ
  have hρe : ∀ x, e (ρ' x) = ρ (e x) := by
    intro x
    have := congrArg (fun φ : MulAut (c.G ⧸ Subgroup.center c.G) => φ (e x)) hρρ'
    simpa [MulAut.congr_apply] using this
  have h2 : ρ' * ρ' = 1 := by
    show (MulAut.congr e).symm ρ * (MulAut.congr e).symm ρ = 1
    rw [← map_mul, hρ2, map_one]
  have hfix : ∀ r ∈ R, ρ' r = r := by
    intro r hr
    apply e.injective
    rw [hρe, he, hρR r hr]
  have := oddCoreIn_fixed_congr_eq_bot' e ρ' (h ρ' h2 ⟨R, hR, hfix⟩)
  rwa [hρρ'] at this

theorem inv_classification_transport {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {fA : Set (Subgroup A)} {fB : Set (Subgroup B)}
    (hf : ∀ R ∈ fA, R.map e.toMonoidHom ∈ fB)
    (h : ∀ ρ : MulAut B, ρ * ρ = 1 → (∃ R ∈ fB, ∀ r ∈ R, ρ r = r) →
      ρ = 1 ∨ ∃ s : B, s * s = 1 ∧ s ≠ 1 ∧ ρ = MulAut.conj s) :
    ∀ ρ : MulAut A, ρ * ρ = 1 → (∃ R ∈ fA, ∀ r ∈ R, ρ r = r) →
      ρ = 1 ∨ ∃ s : A, s * s = 1 ∧ s ≠ 1 ∧ ρ = MulAut.conj s := by
  intro ρ hρ2 ⟨R, hR, hρR⟩
  have h2 : MulAut.congr e ρ * MulAut.congr e ρ = 1 := by
    rw [← map_mul, hρ2, map_one]
  have hfix : ∀ y ∈ R.map e.toMonoidHom, MulAut.congr e ρ y = y := by
    rintro _ ⟨r, hr, rfl⟩
    have h1 : MulAut.congr e ρ (e r) = e (ρ r) := by simp [MulAut.congr_apply]
    rw [MulEquiv.coe_toMonoidHom, h1, hρR r hr]
  have hback : MulAut.congr e.symm (MulAut.congr e ρ) = ρ := by
    ext x
    simp [MulAut.congr_apply]
  rcases h _ h2 ⟨R.map e.toMonoidHom, hf R hR, hfix⟩ with h1 | ⟨s, hs2, hs1, hs⟩
  · left
    rw [← hback, h1, map_one]
  · right
    refine ⟨e.symm s, ?_, ?_, ?_⟩
    · rw [← map_mul, hs2, map_one]
    · intro h3
      apply hs1
      have := congrArg e h3
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    · rw [← hback, hs, congr_conj]

theorem OutOne.of_center_eq_bot {G : Type} [Group G] (hZ : Subgroup.center G = ⊥)
    (h : OutOne (G ⧸ Subgroup.center G)) : OutOne G := by
  have hinj : Function.Injective (QuotientGroup.mk' (Subgroup.center G)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  exact OutOne.of_mulEquiv (MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center G))
    ⟨hinj, QuotientGroup.mk'_surjective _⟩).symm h

end CFSG.ClassicalInvolution.Q3.Q3PP
