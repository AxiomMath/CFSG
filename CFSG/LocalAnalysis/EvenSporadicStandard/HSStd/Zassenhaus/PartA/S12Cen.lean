module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S12Swap

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath Open CFSG.EvenSporadicStandard.HSStd.Zassenhaus

section Abstract

variable {G : Type*} [Group G]

theorem conj_mem_of_perfect {K O : Subgroup G} (hperf : commutator ↥K = ⊤)
    (hOab : ∀ o ∈ O, ∀ o' ∈ O, o * o' = o' * o) (hKO : ∀ k ∈ K, ∀ o ∈ O, k * o = o * k)
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
  have hρ : ∀ k : ↥K, ρ k = 1 := by
    intro k
    have hk : k ∈ commutator ↥K := by rw [hperf]; trivial
    have : commutator ↥K ≤ ρ.ker := by
      rw [_root_.commutator_def, commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hOab _ (ho a a.2) _ (ho b b.2)
    exact this hk
  intro k hk
  have h1 : o k = 1 := hρ ⟨k, hk⟩
  rw [heq k hk, h1, one_mul]
  exact hk' k hk

theorem comm_sup_zpowers {x y : G} (h : x * y = y * x) :
    ∀ a ∈ zpowers x ⊔ zpowers y, ∀ b ∈ zpowers x ⊔ zpowers y, a * b = b * a := by
  have hxy : Commute x y := h
  have hx : zpowers x ⊔ zpowers y ≤ centralizer ((zpowers x : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · rw [zpowers_le, mem_centralizer_iff]
      intro g hg
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
      exact ((Commute.refl x).zpow_left n).eq
    · rw [zpowers_le, mem_centralizer_iff]
      intro g hg
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
      exact (hxy.zpow_left n).symm.eq.symm
  have hy : zpowers x ⊔ zpowers y ≤ centralizer ((zpowers y : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · rw [zpowers_le, mem_centralizer_iff]
      intro g hg
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
      exact (hxy.symm.zpow_left n).symm.eq.symm
    · rw [zpowers_le, mem_centralizer_iff]
      intro g hg
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
      exact ((Commute.refl y).zpow_left n).eq
  have h1 : zpowers x ≤ centralizer ((zpowers x ⊔ zpowers y : Subgroup G) : Set G) :=
    le_centralizer_iff.1 hx
  have h2 : zpowers y ≤ centralizer ((zpowers x ⊔ zpowers y : Subgroup G) : Set G) :=
    le_centralizer_iff.1 hy
  intro a ha b hb
  exact ((mem_centralizer_iff.1 (sup_le h1 h2 ha)) b hb).symm

end Abstract


section Facts

variable {G : Type} [Group G] {L : Subgroup G} {t : G} {E : Subgroup G} {z : G}
  (a : PA11 L t E z)

theorem PA11.phi_eq_one_iff {g : G} (hg : g ∈ Cen a.y) :
    a.phi ⟨g, hg⟩ = 1 ↔ g ∈ fusionOddCoreOf (Cen a.y) := by
  rw [PA11.phi_apply, map_eq_one_iff _ a.ι_inj]
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

theorem PA11.K₁_eq_one_of_mem_O {g : G} (hg : g ∈ a.K₁) (hO : g ∈ fusionOddCoreOf (Cen a.y)) :
    g = 1 := by
  have hm : g ∈ fusionOddCoreOf (Cen a.y) ⊓ (a.K₁ ⊔ conjSub t a.K₁) := ⟨hO, mem_sup_left hg⟩
  rw [a.O_inf] at hm
  exact Subgroup.mem_bot.1 hm

theorem PA11.K₁_inj {k l : G} (hk : k ∈ a.K₁) (hl : l ∈ a.K₁)
    (h : a.phi ⟨k, a.K₁_le hk⟩ = a.phi ⟨l, a.K₁_le hl⟩) : k = l := by
  have h1 : a.phi ⟨k⁻¹ * l, a.K₁_le (a.K₁.mul_mem (a.K₁.inv_mem hk) hl)⟩ = 1 := by
    have : (⟨k⁻¹ * l, a.K₁_le (a.K₁.mul_mem (a.K₁.inv_mem hk) hl)⟩ : ↥(Cen a.y)) =
        ⟨k, a.K₁_le hk⟩⁻¹ * ⟨l, a.K₁_le hl⟩ := rfl
    rw [this, map_mul, map_inv, h, inv_mul_cancel]
  have h2 := (a.phi_eq_one_iff _).1 h1
  have h3 := a.K₁_eq_one_of_mem_O (a.K₁.mul_mem (a.K₁.inv_mem hk) hl) h2
  exact inv_mul_eq_one.1 h3

theorem PA11.K₁_perfect : commutator ↥a.K₁ = ⊤ := by
  have hA : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have : Group.IsPerfect ↥a.K₁ :=
    Group.IsPerfect.ofSurjective (f := a.eK₁.symm.toMonoidHom) a.eK₁.symm.surjective
  exact (Group.isPerfect_def).1 this

theorem PA11.O_abel : ∀ o ∈ fusionOddCoreOf (Cen a.y), ∀ o' ∈ fusionOddCoreOf (Cen a.y),
    o * o' = o' * o := by
  rw [a.O_eq]
  exact comm_sup_zpowers (a.L₁_comm a.x a.x_mem a.x a.x_mem).eq

theorem PA11.K₁_comm_O {k o : G} (hk : k ∈ a.K₁) (ho : o ∈ fusionOddCoreOf (Cen a.y)) :
    k * o = o * k :=
  (mem_centralizer_iff.1 (a.K₁_O hk) o ho).symm

theorem PA11.xt_mem_O : t * a.x * t⁻¹ ∈ fusionOddCoreOf (Cen a.y) := by
  rw [a.O_eq]
  exact mem_sup_right (mem_zpowers _)

theorem PA11.conj_mem_K₁ {g : G} (hg : g ∈ Cen a.y) {s s' : Equiv.Perm (Fin 5)}
    (hs : a.phi ⟨g, hg⟩ = base s s') {k : G} (hk : k ∈ a.K₁) : g * k * g⁻¹ ∈ a.K₁ := by
  refine conj_mem_of_perfect (K := a.K₁) (O := fusionOddCoreOf (Cen a.y)) a.K₁_perfect
    a.O_abel (fun k hk o ho => a.K₁_comm_O hk ho) (fun k hk ho => a.K₁_eq_one_of_mem_O hk ho)
    ?_ k hk
  intro k hk
  obtain ⟨σ, hσ⟩ := a.K₁_ι k hk
  have hσ' : a.phi ⟨k, a.K₁_le hk⟩ = base (σ : Equiv.Perm (Fin 5)) 1 := hσ
  have hmem : s * (σ : Equiv.Perm (Fin 5)) * s⁻¹ ∈ alternatingGroup (Fin 5) :=
    (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem _ σ.2 s
  obtain ⟨k', hk'K, hk'⟩ := a.K₁_onto ⟨s * (σ : Equiv.Perm (Fin 5)) * s⁻¹, hmem⟩
  have hk'' : a.phi ⟨k', a.K₁_le hk'K⟩ = base (s * (σ : Equiv.Perm (Fin 5)) * s⁻¹) 1 := hk'
  have hc : g * k * g⁻¹ * k'⁻¹ ∈ Cen a.y :=
    mul_mem (mul_mem (mul_mem hg (a.K₁_le hk)) (inv_mem hg)) (inv_mem (a.K₁_le hk'K))
  refine ⟨g * k * g⁻¹ * k'⁻¹, ?_, k', hk'K, by group⟩
  rw [← a.phi_eq_one_iff hc]
  have h1 : (⟨g * k * g⁻¹ * k'⁻¹, hc⟩ : ↥(Cen a.y)) =
      ⟨g, hg⟩ * ⟨k, a.K₁_le hk⟩ * ⟨g, hg⟩⁻¹ * ⟨k', a.K₁_le hk'K⟩⁻¹ := rfl
  rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv, hs, hσ', hk'', conj_base_base, base_inv,
    base_mul_base]
  have e1 : s * (σ : Equiv.Perm (Fin 5)) * s⁻¹ * (s * (σ : Equiv.Perm (Fin 5)) * s⁻¹)⁻¹ = 1 :=
    mul_inv_cancel _
  have e2 : s' * 1 * s'⁻¹ * (1 : Equiv.Perm (Fin 5))⁻¹ = 1 := by group
  rw [e1, e2, base_one]

end Facts

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
