module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Abs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

section Cover

variable {M : Type*} [Group M]

theorem F3S.of_cover {N : Subgroup M} {p : ℕ} {P : M → Prop} (reps : List M)
    (hcover : ∀ u, P u → orderOf u = 2 → ∃ r ∈ reps, ∃ d ∈ N, u = d * r * d⁻¹)
    (hreps : ∀ r ∈ reps, F3S N r p) : ∀ u, P u → orderOf u = 2 → F3S N u p := by
  intro u hu ho
  obtain ⟨r, hr, d, hd, rfl⟩ := hcover u hu ho
  exact (hreps r hr).conj hd

theorem F3.of_inner {N : Subgroup M} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcenter : Subgroup.center ↥N = ⊥) (hF : ∀ t ∈ N, orderOf t = 2 → F3S N t p)
    {α : MulAut ↥N} {g : ↥N} (hα : α = MulAut.conj g) (hα2 : α * α = 1) : F3 p α := by
  have hg2 : g * g = 1 := by
    have hc : g * g ∈ Subgroup.center ↥N := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun φ : MulAut ↥N => φ z) hα2
      simp only [MulAut.mul_apply, MulAut.one_apply, hα, MulAut.conj_apply] at hz
      calc z * (g * g) = g * (g * z * g⁻¹) * g⁻¹ * (g * g) := by rw [hz]
        _ = g * g * z := by group
    rw [hcenter, Subgroup.mem_bot] at hc
    exact hc
  have hαg : ∀ h : ↥N, ((α h : ↥N) : M) = (g : M) * h * (g : M)⁻¹ := fun h => by
    rw [hα]; rfl
  by_cases hg1 : g = 1
  · subst hg1
    exact F3.of_F3S α (u := 1) (fun h => by rw [hαg]; simp) (F3S.one_elt hp hp2)
  · have ho : orderOf (g : M) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [sq]; exact hg2) hg1
    exact F3.of_F3S α hαg (hF (g : M) g.2 ho)

theorem F3.of_outer (N : Subgroup M) [Finite N] (δ : M) (hδ : ∀ h ∈ N, δ * h * δ⁻¹ ∈ N)
    (hδ2 : δ * δ ∈ N) (hcenter : Subgroup.center ↥N = ⊥)
    (houter : ∀ g ∈ N, ¬∀ h ∈ N, δ * g * h = h * (δ * g))
    (hcard : Nat.card (MulAut ↥N) ≤ 2 * Nat.card ↥N) {p : ℕ}
    (hF : ∀ u, δ⁻¹ * u ∈ N → orderOf u = 2 → F3S N u p)
    (α : MulAut ↥N) (hα2 : α * α = 1) (hα : α ∉ inner ↥N) : F3 p α := by
  have hδ' := inv_conj_mem N hδ hδ2
  obtain ⟨g, hg, hαg⟩ := exists_eq_conj_of_outer N δ hδ hδ2 hcenter houter hcard α hα
  set u := g * δ with hu_def
  have hu : δ⁻¹ * u ∈ N := by
    simpa [u, mul_assoc] using hδ' g hg
  have hu2N : u * u ∈ N := by
    have : u * u = g * (δ * g * δ⁻¹) * (δ * δ) := by simp only [u]; group
    rw [this]
    exact N.mul_mem (N.mul_mem hg (hδ g hg)) hδ2
  have hu2 : u * u = 1 := by
    have hc : (⟨u * u, hu2N⟩ : ↥N) ∈ Subgroup.center ↥N := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun φ : MulAut ↥N => (φ z : M)) hα2
      simp only [MulAut.mul_apply, MulAut.one_apply] at hz
      rw [hαg, hαg] at hz
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (z : M) * (u * u) = u * (u * z * u⁻¹) * u⁻¹ * (u * u) := by rw [hz]
        _ = u * u * z := by group
    rw [hcenter, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hu1 : u ≠ 1 := by
    intro h1
    apply hα
    refine ⟨1, MulEquiv.ext fun z => Subtype.ext ?_⟩
    rw [hαg, h1]
    simp
  have ho : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  exact F3.of_F3S α hαg (hF u hu ho)

end Cover

section Assembly

variable {Y : Type} [Group Y]

theorem QuotCfg.false_of_F3_all {N : Type*} [Group N] [Finite N] (e : Y ≃* N) {ps : List ℕ}
    (hAll : ∀ β : MulAut N, β * β = 1 → ∀ p ∈ ps, F3 p β)
    (hps : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card N → p ∈ ps) {p : ℕ} {α : MulAut Y} {Xh : Subgroup Y}
    (h : QuotCfg p α Xh) : False := by
  have hY : Finite Y := Finite.of_equiv N e.symm.toEquiv
  have hcard : Nat.card Y = Nat.card N := Nat.card_congr e.toEquiv
  have hpmem : p ∈ ps := hps p h.prime h.odd (hcard ▸ h.dvd_card)
  set β : MulAut N := MulAut.congr e α with hβ
  have hαβ : ∀ y, e (α y) = β (e y) := fun y => by
    show e (α y) = e (α (e.symm (e y)))
    rw [MulEquiv.symm_apply_apply]
  have hβ2 : β * β = 1 := by
    refine MulEquiv.ext fun t => ?_
    have h1 := h.invol (e.symm t)
    have : β (β t) = e (α (α (e.symm t))) := by
      have h2 := hαβ (α (e.symm t))
      have h3 := hαβ (e.symm t)
      rw [MulEquiv.apply_symm_apply] at h3
      rw [← h3, ← h2]
    rw [MulAut.mul_apply, MulAut.one_apply, this, h1, MulEquiv.apply_symm_apply]
  exact h.false_of_F3 (F3.of_equiv e hαβ (hAll β hβ2 p hpmem))

theorem prime_mem_of_dvd {N : ℕ} {L : List ℕ} (hN : N ≠ 0) (hL : Nat.primeFactorsList N = L) {p : ℕ}
    (hp : p.Prime) (hd : p ∣ N) : p ∈ L :=
  hL ▸ (Nat.mem_primeFactorsList hN).2 ⟨hp, hd⟩

end Assembly

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
