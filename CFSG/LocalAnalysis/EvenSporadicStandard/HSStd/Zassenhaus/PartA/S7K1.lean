module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Data

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

set_option linter.unusedSectionVars false

open Subgroup Wreath Open
open scoped commutatorElement

section Abstract

variable {G : Type*} [Group G]

theorem s7_conj_mem_of_perfect {K O : Subgroup G} {y : G} (hperf : commutator ↥K = ⊤)
    (hOc : ∀ o : G, o ∈ O → ∀ o' : G, o' ∈ O → ⁅o, o'⁆ ∈ zpowers y) (hKO : ∀ k ∈ K, ∀ o ∈ O, k * o = o * k)
    (hinf : ∀ k ∈ K, k ∈ O → k = 1) {g : G}
    (h : ∀ k ∈ K, ∃ o ∈ O, ∃ k' ∈ K, g * k * g⁻¹ = o * k') :
    ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
  choose! o ho k' hk' heq using h
  have hmul : ∀ k ∈ K, ∀ l ∈ K, o (k * l) = o k * o l := by
    intro k hk l hl
    have h1 : g * (k * l) * g⁻¹ = (g * k * g⁻¹) * (g * l * g⁻¹) := by group
    rw [heq k hk, heq l hl, heq (k * l) (K.mul_mem hk hl)] at h1
    have h2 : o k * k' k * (o l * k' l) = (o k * o l) * (k' k * k' l) := by
      calc o k * k' k * (o l * k' l) = o k * (k' k * o l) * k' l := by group
        _ = o k * (o l * k' k) * k' l := by rw [hKO _ (hk' k hk) _ (ho l hl)]
        _ = _ := by group
    rw [h2] at h1
    have h3 : (o (k * l))⁻¹ * (o k * o l) = k' (k * l) * (k' k * k' l)⁻¹ := by
      have := h1
      calc (o (k * l))⁻¹ * (o k * o l)
          = (o (k * l))⁻¹ * (o (k * l) * k' (k * l)) * (k' k * k' l)⁻¹ := by
            rw [this]; group
        _ = _ := by group
    have h4 : (o (k * l))⁻¹ * (o k * o l) ∈ O :=
      O.mul_mem (O.inv_mem (ho _ (K.mul_mem hk hl))) (O.mul_mem (ho k hk) (ho l hl))
    have h5 : k' (k * l) * (k' k * k' l)⁻¹ ∈ K :=
      K.mul_mem (hk' _ (K.mul_mem hk hl)) (K.inv_mem (K.mul_mem (hk' k hk) (hk' l hl)))
    rw [← h3] at h5
    have h6 := hinf _ h5 h4
    rw [inv_mul_eq_one] at h6
    exact h6
  let ρ : ↥K →* G := MonoidHom.mk' (fun k => o (k : G)) (fun k l => hmul k k.2 l l.2)
  have hS : ∀ k : ↥K, ρ k ∈ zpowers y := by
    have hle : commutator ↥K ≤ (zpowers y).comap ρ := by
      rw [_root_.commutator_def, commutator_le]
      intro a _ b _
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact hOc _ (ho a a.2) _ (ho b b.2)
    intro k
    have hk : k ∈ commutator ↥K := by rw [hperf]; trivial
    exact hle hk
  have hρ : ∀ k : ↥K, ρ k = 1 := by
    intro k
    have hk : k ∈ commutator ↥K := by rw [hperf]; trivial
    have : commutator ↥K ≤ ρ.ker := by
      rw [_root_.commutator_def, commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      obtain ⟨m, hm⟩ := mem_zpowers_iff.1 (hS a)
      obtain ⟨n, hn⟩ := mem_zpowers_iff.1 (hS b)
      rw [← hm, ← hn]
      exact ((Commute.refl y).zpow_zpow m n).eq
    exact this hk
  intro k hk
  have h1 : o k = 1 := hρ ⟨k, hk⟩
  rw [heq k hk, h1, one_mul]
  exact hk' k hk

end Abstract

section Facts

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E : Subgroup G} {z : G}
  (a : PA4 L t E z)

theorem s7_K₁_perfect : commutator ↥a.K₁ = ⊤ := by
  have hA : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have : Group.IsPerfect ↥a.K₁ :=
    Group.IsPerfect.ofSurjective (f := a.eK₁.symm.toMonoidHom) a.eK₁.symm.surjective
  exact (Group.isPerfect_def).1 this

theorem s7_phi_eq_one_iff {g : G} (hg : g ∈ Cen a.y) :
    S5.phi a ⟨g, hg⟩ = 1 ↔ g ∈ fusionOddCoreOf (Cen a.y) := by
  show a.ι (oMk (Cen a.y) ⟨g, hg⟩) = 1 ↔ _
  rw [map_eq_one_iff _ a.ι_inj]
  have h1 : oMk (Cen a.y) ⟨g, hg⟩ = 1 ↔ (⟨g, hg⟩ : ↥(Cen a.y)) ∈ fusionOddCore ↥(Cen a.y) :=
    QuotientGroup.eq_one_iff _
  rw [h1, fusionOddCoreOf_eq]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨h, hh, hgh⟩
    have : h = ⟨g, hg⟩ := Subtype.ext hgh
    rw [← this]
    exact hh

theorem s7_K₁_eq_one_of_mem_O {g : G} (hg : g ∈ a.K₁) (hO : g ∈ fusionOddCoreOf (Cen a.y)) :
    g = 1 := by
  have hm : g ∈ fusionOddCoreOf (Cen a.y) ⊓ (a.K₁ ⊔ conjSub t a.K₁) := ⟨hO, mem_sup_left hg⟩
  rw [a.O_inf] at hm
  exact Subgroup.mem_bot.1 hm

theorem s7_K₁_inj {k l : G} (hk : k ∈ a.K₁) (hl : l ∈ a.K₁)
    (h : S5.phi a ⟨k, a.K₁_le hk⟩ = S5.phi a ⟨l, a.K₁_le hl⟩) : k = l := by
  have h1 : S5.phi a ⟨k⁻¹ * l, a.K₁_le (a.K₁.mul_mem (a.K₁.inv_mem hk) hl)⟩ = 1 := by
    have : (⟨k⁻¹ * l, a.K₁_le (a.K₁.mul_mem (a.K₁.inv_mem hk) hl)⟩ : ↥(Cen a.y)) =
        ⟨k, a.K₁_le hk⟩⁻¹ * ⟨l, a.K₁_le hl⟩ := rfl
    rw [this, map_mul, map_inv, h, inv_mul_cancel]
  have h2 := (s7_phi_eq_one_iff a _).1 h1
  have h3 := s7_K₁_eq_one_of_mem_O a (a.K₁.mul_mem (a.K₁.inv_mem hk) hl) h2
  exact inv_mul_eq_one.1 h3

theorem s7_conj_mem_K₁ {g : G} (hg : g ∈ Cen a.y) {s s' : Equiv.Perm (Fin 5)}
    (hs : S5.phi a ⟨g, hg⟩ = base s s') {k : G} (hk : k ∈ a.K₁) : g * k * g⁻¹ ∈ a.K₁ := by
  refine s7_conj_mem_of_perfect (K := a.K₁) (O := fusionOddCoreOf (Cen a.y)) (y := a.y)
    (s7_K₁_perfect a) a.O_comm
    (fun k hk o ho => (mem_centralizer_iff.1 (a.K₁_O hk) o ho).symm)
    (fun k hk ho => s7_K₁_eq_one_of_mem_O a hk ho) ?_ k hk
  intro k hk
  obtain ⟨σ, hσ⟩ := a.K₁_ι k hk
  have hσ' : S5.phi a ⟨k, a.K₁_le hk⟩ = base (σ : Equiv.Perm (Fin 5)) 1 := hσ
  have hmem : s * (σ : Equiv.Perm (Fin 5)) * s⁻¹ ∈ alternatingGroup (Fin 5) :=
    (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem _ σ.2 s
  obtain ⟨k', hk'K, hk'⟩ := a.K₁_onto ⟨s * (σ : Equiv.Perm (Fin 5)) * s⁻¹, hmem⟩
  have hk'' : S5.phi a ⟨k', a.K₁_le hk'K⟩ = base (s * (σ : Equiv.Perm (Fin 5)) * s⁻¹) 1 := hk'
  have hc : g * k * g⁻¹ * k'⁻¹ ∈ Cen a.y :=
    mul_mem (mul_mem (mul_mem hg (a.K₁_le hk)) (inv_mem hg)) (inv_mem (a.K₁_le hk'K))
  refine ⟨g * k * g⁻¹ * k'⁻¹, ?_, k', hk'K, by group⟩
  rw [← s7_phi_eq_one_iff a hc]
  have h1 : (⟨g * k * g⁻¹ * k'⁻¹, hc⟩ : ↥(Cen a.y)) =
      ⟨g, hg⟩ * ⟨k, a.K₁_le hk⟩ * ⟨g, hg⟩⁻¹ * ⟨k', a.K₁_le hk'K⟩⁻¹ := rfl
  rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv, hs, hσ', hk'', conj_base_base, base_inv,
    base_mul_base]
  have e1 : s * (σ : Equiv.Perm (Fin 5)) * s⁻¹ * (s * (σ : Equiv.Perm (Fin 5)) * s⁻¹)⁻¹ = 1 :=
    mul_inv_cancel _
  have e2 : s' * 1 * s'⁻¹ * (1 : Equiv.Perm (Fin 5))⁻¹ = 1 := by group
  rw [e1, e2, base_one]

theorem s7_comm_of_phi {g : G} (hg : g ∈ Cen a.y) {s s' : Equiv.Perm (Fin 5)}
    (hs : S5.phi a ⟨g, hg⟩ = base s s') {k : G} (hk : k ∈ a.K₁) {ρ : Equiv.Perm (Fin 5)}
    (hρ : S5.phi a ⟨k, a.K₁_le hk⟩ = base ρ 1) (hc : ρ * s = s * ρ) : g * k = k * g := by
  have hmem : g * k * g⁻¹ ∈ a.K₁ := s7_conj_mem_K₁ a hg hs hk
  have h1 : S5.phi a ⟨g * k * g⁻¹, a.K₁_le hmem⟩ = S5.phi a ⟨k, a.K₁_le hk⟩ := by
    have e : (⟨g * k * g⁻¹, a.K₁_le hmem⟩ : ↥(Cen a.y)) =
        ⟨g, hg⟩ * ⟨k, a.K₁_le hk⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hs, hρ, conj_base_base]
    have e1 : s * ρ * s⁻¹ = ρ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hc.symm
    have e2 : s' * 1 * s'⁻¹ = (1 : Equiv.Perm (Fin 5)) := by group
    rw [e1, e2]
  have h2 := s7_K₁_inj a hmem hk h1
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2

end Facts

section Perm

open Equiv

theorem s7_exists_wj_check : ∀ a b : Fin 5, a ≠ b → ∃ w j : Perm (Fin 5), Perm.sign w = 1 ∧
    Perm.sign j = 1 ∧ w ^ 3 = 1 ∧ w ≠ 1 ∧ j * j = 1 ∧ j ≠ 1 ∧ w * swap a b = swap a b * w ∧
    j * swap a b = swap a b * j ∧ j * w * j⁻¹ = w⁻¹ := by
  decide +kernel

end Perm

section Elements

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

@[expose] noncomputable def PA4.s7_phiK (a : PA4 L t E z) :
    ↥a.K₁ →* Wr2 (Equiv.Perm (Fin 5)) :=
  (S5.phi a).comp (Subgroup.inclusion a.K₁_le)

theorem PA4.s7_phiK_injective (a : PA4 L t E z) : Function.Injective a.s7_phiK := fun k l h =>
  Subtype.ext (s7_K₁_inj a k.2 l.2 h)

theorem PA5.s7_exists_ck (hb : PAB G L t E W z) (a : PA5 L t E z) :
    ∃ c k : G, c ∈ a.K₁ ∧ k ∈ a.K₁ ∧ c * (c * c) = 1 ∧ c ≠ 1 ∧ k * k = 1 ∧ k ≠ 1 ∧
      k * c * k⁻¹ = c⁻¹ ∧ c * a.ub = a.ub * c ∧ k * a.ub = a.ub * k ∧
      (a.dcase = DCase.d8 → c * a.u₁ = a.u₁ * c ∧ k * a.u₁ = a.u₁ * k) := by
  obtain ⟨σ, ⟨p, q, hpq, rfl⟩, hι⟩ := a.ub_base
  obtain ⟨wt, jt, hsw, hsj, hw3, hw1, hj2, hj1, hwσ, hjσ, hjw⟩ := s7_exists_wj_check p q hpq
  obtain ⟨c, hcK, hc⟩ := a.K₁_onto ⟨wt, Equiv.Perm.mem_alternatingGroup.2 hsw⟩
  obtain ⟨k, hkK, hk⟩ := a.K₁_onto ⟨jt, Equiv.Perm.mem_alternatingGroup.2 hsj⟩
  have hc' : S5.phi a.toPA4 ⟨c, a.K₁_le hcK⟩ = base wt 1 := hc
  have hk' : S5.phi a.toPA4 ⟨k, a.K₁_le hkK⟩ = base jt 1 := hk
  have hub : S5.phi a.toPA4 ⟨a.ub, a.ub_cy⟩ = base (Equiv.swap p q) (Equiv.swap p q) := hι
  have hcK' : a.toPA4.s7_phiK ⟨c, hcK⟩ = base wt 1 := hc
  have hkK' : a.toPA4.s7_phiK ⟨k, hkK⟩ = base jt 1 := hk
  have hw3' : wt * (wt * wt) = 1 := by rw [← pow_three]; exact hw3
  refine ⟨c, k, hcK, hkK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (⟨c, hcK⟩ : ↥a.K₁) * ((⟨c, hcK⟩ : ↥a.K₁) * ⟨c, hcK⟩) = 1 := by
      apply a.toPA4.s7_phiK_injective
      rw [map_mul, map_mul, map_one, hcK', base_mul_base, base_mul_base]
      simp only [hw3', mul_one, base_one]
    exact congrArg Subtype.val this
  · intro h
    have h1 : (⟨c, hcK⟩ : ↥a.K₁) = 1 := Subtype.ext h
    have h2 := congrArg a.toPA4.s7_phiK h1
    rw [map_one, hcK'] at h2
    exact hw1 (base_injective.1 (h2.trans base_one.symm)).1
  · have : (⟨k, hkK⟩ : ↥a.K₁) * ⟨k, hkK⟩ = 1 := by
      apply a.toPA4.s7_phiK_injective
      rw [map_mul, map_one, hkK', base_mul_base]
      simp only [hj2, mul_one, base_one]
    exact congrArg Subtype.val this
  · intro h
    have h1 : (⟨k, hkK⟩ : ↥a.K₁) = 1 := Subtype.ext h
    have h2 := congrArg a.toPA4.s7_phiK h1
    rw [map_one, hkK'] at h2
    exact hj1 (base_injective.1 (h2.trans base_one.symm)).1
  · have : (⟨k, hkK⟩ : ↥a.K₁) * ⟨c, hcK⟩ * (⟨k, hkK⟩ : ↥a.K₁)⁻¹ = (⟨c, hcK⟩ : ↥a.K₁)⁻¹ := by
      apply a.toPA4.s7_phiK_injective
      rw [map_mul, map_mul, map_inv, map_inv, hkK', hcK', conj_base_base, base_inv, hjw]
      simp
    exact congrArg Subtype.val this
  · exact (s7_comm_of_phi a.toPA4 a.ub_cy hub hcK hc' hwσ).symm
  · exact (s7_comm_of_phi a.toPA4 a.ub_cy hub hkK hk' hjσ).symm
  · intro hd
    obtain ⟨hsq, hcm, ht1, -, -⟩ := a.s7_d8_facts hb hd
    obtain ⟨-, -, hu₁J, -, -, -, -⟩ := a.d8_props hd
    have hu₁cy : a.u₁ ∈ Cen a.y := S5.cent_J_le_Cen_y a.toPA0 hu₁J
    have hform := S5.u₁_form hb a.toPA4 a.ub_cases a.ub_cy ⟨p, q, hpq, rfl⟩ hι hu₁cy hsq hcm
      hu₁J ht1
    rcases hform with h | h
    · exact ⟨(s7_comm_of_phi a.toPA4 hu₁cy h hcK hc' hwσ).symm,
        (s7_comm_of_phi a.toPA4 hu₁cy h hkK hk' hjσ).symm⟩
    · exact ⟨(s7_comm_of_phi a.toPA4 hu₁cy h hcK hc' (by simp)).symm,
        (s7_comm_of_phi a.toPA4 hu₁cy h hkK hk' (by simp)).symm⟩

end Elements

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
