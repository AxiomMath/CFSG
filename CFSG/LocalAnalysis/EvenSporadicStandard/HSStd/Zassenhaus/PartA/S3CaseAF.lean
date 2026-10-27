module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3CaseAE
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3CaseAN

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Equiv Subgroup CFSG.Open

variable {D : Type} [Group D] [Finite D] {t : D} {K : Subgroup D}

theorem s3a_swap_contra (h : DShape D t K) (ψ : ↥K ≃* Perm (Fin 5))
    (j j' : ↥(alternatingGroup (Fin 5)) →* D) (hj : Function.Injective j)
    (hcomm : ∀ a b, j a * j' b = j' b * j a)
    (hn : ∀ a, ∃ c, t * j a * t⁻¹ = j c)
    (hex : ∀ a, ∃ b, s3a_iota ψ a = j' b) : False :=
  s3a_contra_range h ψ j hj s3a_A5_noncomm (fun b hb => s3a_A5_comm_exists b hb) hn
    (fun b a => by
      obtain ⟨b', hb'⟩ := hex a
      rw [hb']
      exact hcomm b b')

theorem s3a_not_preserved (h : DShape D t K) (ψ : ↥K ≃* Perm (Fin 5)) (E : Subgroup D) [E.Normal]
    (e : ↥E ≃* ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)))
    (hp : (∀ a, ∃ c, t * s3a_j₁ E e a * t⁻¹ = s3a_j₁ E e c) ∧
      ∀ b, ∃ c, t * s3a_j₂ E e b * t⁻¹ = s3a_j₂ E e c) : False := by
  have hsimple := s3a_A5_simple
  have hmemC : ∀ x : D, t * x = x * t → x ∈ centralizer ({t} : Set D) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hx
  let M : Subgroup D := E ⊓ centralizer ({t} : Set D)
  have hMC : M ≤ centralizer ({t} : Set D) := inf_le_right
  have hM : ∀ c ∈ centralizer ({t} : Set D), ∀ m ∈ M, c * m * c⁻¹ ∈ M := by
    intro c hc m hm
    refine ⟨Normal.conj_mem inferInstance m hm.1 c, ?_⟩
    exact (centralizer ({t} : Set D)).mul_mem
      ((centralizer ({t} : Set D)).mul_mem hc hm.2) ((centralizer ({t} : Set D)).inv_mem hc)
  rcases s3a_normal_dichotomy h ψ M hMC hM with hall | hι
  · obtain ⟨b₁, hb₁, hc₁⟩ := s3a_fixed_exists h.t_sq (s3a_j₁ E e) (s3a_j₁_injective E e)
      s3a_A5_noncomm hp.1
    obtain ⟨b₂, hb₂, hc₂⟩ := s3a_fixed_exists h.t_sq (s3a_j₂ E e) (s3a_j₂_injective E e)
      s3a_A5_noncomm hp.2
    have e1 : s3a_j₁ E e b₁ = t := by
      rcases hall _ ⟨s3a_j₁_mem E e b₁, hmemC _ hc₁⟩ with e' | e'
      · exact absurd (s3a_j₁_injective E e (by rw [e', map_one])) hb₁
      · exact e'
    have e2 : s3a_j₂ E e b₂ = t := by
      rcases hall _ ⟨s3a_j₂_mem E e b₂, hmemC _ hc₂⟩ with e' | e'
      · exact absurd (s3a_j₂_injective E e (by rw [e', map_one])) hb₂
      · exact e'
    exact hb₁ (s3a_j₁_ne_j₂ E e b₁ b₂ (e1.trans e2.symm))
  · let g : ↥(alternatingGroup (Fin 5)) →* ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) :=
      e.toMonoidHom.comp ((s3a_iota ψ).codRestrict E (fun a => (hι a).1))
    have hgfE : ∀ a, s3a_fE E e (g a) = s3a_iota ψ a := by
      intro a
      simp [g, s3a_fE_apply]
    have hτ₁ : ∀ a c, t * s3a_j₁ E e a * t⁻¹ = s3a_j₁ E e c →
        s3a_tau E e t (a, 1) = (c, 1) := by
      intro a c hac
      apply s3a_fE_injective E e
      rw [s3a_tau_spec]
      exact hac
    have hτ₂ : ∀ a c, t * s3a_j₂ E e a * t⁻¹ = s3a_j₂ E e c →
        s3a_tau E e t (1, a) = (1, c) := by
      intro a c hac
      apply s3a_fE_injective E e
      rw [s3a_tau_spec]
      exact hac
    have hfix : ∀ a, s3a_tau E e t (g a) = g a := by
      intro a
      apply s3a_fE_injective E e
      rw [s3a_tau_spec, hgfE]
      have : t * s3a_iota ψ a = s3a_iota ψ a * t :=
        (mem_centralizer_iff.1 (hι a).2) t rfl
      rw [this, mul_inv_cancel_right]
    have h₁ : ∀ a, (s3a_tau E e t (a, 1)).2 = 1 := by
      intro a
      obtain ⟨c, hc⟩ := hp.1 a
      rw [hτ₁ a c hc]
    have h₂ : ∀ b, (s3a_tau E e t (1, b)).1 = 1 := by
      intro b
      obtain ⟨c, hc⟩ := hp.2 b
      rw [hτ₂ b c hc]
    rcases s3a_pure_swap (s3a_tau E e t) h₁ h₂ g hfix with hid | hg1 | hg2
    · refine s3a_E_not_comm h ψ E e (fun x hx => ?_)
      obtain ⟨y, rfl⟩ := s3a_fE_surj E e hx
      have := s3a_tau_spec E e t y
      rw [hid y] at this
      exact mul_inv_eq_iff_eq_mul.1 this.symm
    · refine s3a_swap_contra h ψ (s3a_j₁ E e) (s3a_j₂ E e) (s3a_j₁_injective E e)
        (s3a_j_comm E e) hp.1 (fun a => ⟨(g a).2, ?_⟩)
      rw [← hgfE, s3a_j₂_apply, ← hg1 a]
    · refine s3a_swap_contra h ψ (s3a_j₂ E e) (s3a_j₁ E e) (s3a_j₂_injective E e)
        (fun a b => (s3a_j_comm E e b a).symm) hp.2 (fun a => ⟨(g a).1, ?_⟩)
      rw [← hgfE, s3a_j₁_apply, ← hg2 a]

theorem s3a_faithful (h : DShape D t K) (ψ : ↥K ≃* Perm (Fin 5)) (hz : fusionZStar D = ⊥)
    (E : Subgroup D) [E.Normal]
    (e : ↥E ≃* ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5))) {d : D}
    (hd : ∀ x ∈ E, d * x = x * d) : d = 1 := by
  have hsimple := s3a_A5_simple
  have hmemC : ∀ x : D, t * x = x * t → x ∈ centralizer ({t} : Set D) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hx
  have hRn : (centralizer (E : Set D)).Normal := Subgroup.normal_centralizer
  let R : Subgroup D := centralizer (E : Set D)
  have htR : t ∉ R := by
    intro ht
    exact s3a_E_not_comm h ψ E e (fun x hx => ((mem_centralizer_iff.1 ht) x hx).symm)
  let M : Subgroup D := R ⊓ centralizer ({t} : Set D)
  have hMC : M ≤ centralizer ({t} : Set D) := inf_le_right
  have hM : ∀ c ∈ centralizer ({t} : Set D), ∀ m ∈ M, c * m * c⁻¹ ∈ M := by
    intro c hc m hm
    refine ⟨Normal.conj_mem hRn m hm.1 c, ?_⟩
    exact (centralizer ({t} : Set D)).mul_mem
      ((centralizer ({t} : Set D)).mul_mem hc hm.2) ((centralizer ({t} : Set D)).inv_mem hc)
  have hdR : d ∈ R := fun x hx => (hd x hx).symm
  have hR : R = ⊥ := by
    rcases s3a_normal_dichotomy h ψ M hMC hM with hall | hι
    · have hn : ∀ o ∈ R, t * o * t⁻¹ ∈ R := fun o ho => Normal.conj_mem hRn o ho t
      have hfix : ∀ o ∈ R, t * o = o * t → o = 1 := by
        intro o ho hoc
        rcases hall o ⟨ho, hmemC o hoc⟩ with e1 | e1
        · exact e1
        · exact absurd (e1 ▸ ho) htR
      have hinv := (inv_of_centralizer_eq_bot (O := R) h.t_sq hn hfix).1
      have hodd : Odd (Nat.card R) := by
        by_contra hev
        have h2 : 2 ∣ Nat.card R := by
          rcases Nat.even_or_odd (Nat.card R) with he | ho
          · exact even_iff_two_dvd.1 he
          · exact absurd ho hev
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
        have hu2 : (u : D) * u = 1 := by
          have : (u : D) ^ 2 = 1 := by
            have := pow_orderOf_eq_one u
            rw [hu] at this
            exact congrArg Subtype.val this
          rwa [pow_two] at this
        have hu1 : (u : D) ≠ 1 := by
          intro e1
          have : u = 1 := Subtype.ext e1
          rw [this, orderOf_one] at hu
          omega
        have h3 := hinv u u.2
        have h4 : (u : D)⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
        rw [h4] at h3
        exact hu1 (hfix u u.2 (by
          calc t * (u : D) = t * u * t⁻¹ * t := by group
            _ = u * t := by rw [h3]))
      exact s3a_normal_odd hz R hodd
    · exfalso
      obtain ⟨a₀, b₀, hab₀⟩ := s3a_A5_noncomm
      refine s3a_contra_range h ψ (s3a_fE E e) (s3a_fE_injective E e)
        ⟨(a₀, 1), (b₀, 1), fun hh => hab₀ (congrArg Prod.fst hh)⟩ s3a_prod_comm_exists ?_ ?_
      · intro b
        have hmem : t * s3a_fE E e b * t⁻¹ ∈ E :=
          Normal.conj_mem inferInstance _ (s3a_fE_mem E e b) t
        obtain ⟨c, hc⟩ := s3a_fE_surj E e hmem
        exact ⟨c, hc.symm⟩
      · intro b a
        exact (mem_centralizer_iff.1 (hι a).1) _ (s3a_fE_mem E e b)
  rw [hR] at hdR
  exact hdR

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
