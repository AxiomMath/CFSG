module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S11Refl

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath

set_option linter.unusedSectionVars false

section Reflect

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem S11_reflection (hb : PAB G L t E W z) (a : PA10 L t E z) {x : G} (hx : x ∈ a.L₁)
    (hx3 : orderOf x = 3) (hxy : a.y = x * (t * x * t⁻¹)) {X : Subgroup G}
    (h : S11XData a hx X) (hcard : Nat.card ↥(Cen a.y ⊓ Cen a.u) = 2592) :
    ∃ g : G, g ∈ Cen a.y ∧ g ∈ Cen a.u ∧ g * x = x * g ∧
      (∀ b ∈ conjSub t X, g * b = b * g) ∧ (∀ c ∈ X, g * c * g⁻¹ ∈ X) ∧
      (∀ c ∈ X, g * g * c = c * g * g) ∧ ∃ c ∈ X, g * c ≠ c * g := by
  have ht := hb.t_mul_t
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hy := S11_y_mem_Cen hb a
  have hπ := S11_pi_x_ord hb a hx hx3
  set y' : ↥(Cen a.u) := ⟨a.y, hy⟩ with hy'
  set ζ : MulAut (alternatingGroup (Fin 6)) := MulAut.conj (s11Pi a.L₁ (S11_e a) ⟨x, hx⟩) with hζ
  let K' : Subgroup ↥(Cen a.u) := centralizer ({y'} : Set ↥(Cen a.u))
  have hK' : Nat.card K' = 2592 := by
    have h2 : Nat.card K' = Nat.card ↥(Cen a.u ⊓ Cen a.y) := card_centralizer_subtype (Cen a.u) hy
    rw [h2, inf_comm]
    exact hcard
  let f : K' →* Wr2 (MulAut (alternatingGroup (Fin 6))) := (S11_rhoBar hb a).comp K'.subtype
  have hker : Nat.card f.ker ≤ 4 := by
    rw [← S11_card_ker hb a]
    refine Nat.card_le_card_of_injective
      (fun k : f.ker => (⟨(k.1 : ↥(Cen a.u)), k.2⟩ : (S11_rhoBar hb a).ker)) ?_
    intro k₁ k₂ hk
    have := congrArg (fun q : (S11_rhoBar hb a).ker => (q : ↥(Cen a.u))) hk
    exact Subtype.ext (Subtype.ext this)
  have hC0 := S11_card_C0 hb hx hx3 hxy
  have hrange : f.range ≤ centralizer ({S11_rhoBar hb a y'} :
      Set (Wr2 (MulAut (alternatingGroup (Fin 6))))) := by
    rintro _ ⟨k, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hk : (k : ↥(Cen a.u)) * y' = y' * k := mem_centralizer_singleton_iff.1 k.2
    show S11_rhoBar hb a k * S11_rhoBar hb a y' = S11_rhoBar hb a y' * S11_rhoBar hb a k
    rw [← map_mul, ← map_mul, hk]
  have hmul := Subgroup.card_ker_mul_card_range f
  have hr : Nat.card f.range = 648 := by
    have h1 : 2592 ≤ 4 * Nat.card f.range := by
      rw [← hK', ← hmul]
      exact Nat.mul_le_mul_right _ hker
    have h2 : Nat.card f.range ≤ 648 := hC0 ▸ Subgroup.card_le_of_le hrange
    omega
  have hreq : f.range = centralizer ({S11_rhoBar hb a y'} :
      Set (Wr2 (MulAut (alternatingGroup (Fin 6))))) :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [hr, hC0])
  obtain ⟨r, hr2⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(centralizer ({ζ} : Set (MulAut (alternatingGroup (Fin 6)))))) 2
    (by rw [hζ, card_centralizer_conj_of_orderOf_eq_three hπ]; norm_num)
  set r₀ : MulAut (alternatingGroup (Fin 6)) := r.1 with hr₀
  have hr₀2 : orderOf r₀ = 2 := by rw [hr₀, Subgroup.orderOf_coe]; exact hr2
  have hr₀sq : r₀ * r₀ = 1 := by
    have := pow_orderOf_eq_one r₀
    rw [hr₀2, pow_two] at this
    exact this
  have hr₀c : r₀ * ζ = ζ * r₀ := mem_centralizer_singleton_iff.1 r.2
  have hmem : base r₀ 1 ∈ f.range := by
    rw [hreq, S11_rho_y hb a hx hxy, mem_centralizer_base_iff]
    exact ⟨hr₀c, by simp⟩
  obtain ⟨k, hk⟩ := hmem
  set g : G := ((k : ↥(Cen a.u)) : G) with hg
  have hgk : S11_rhoBar hb a k = base r₀ 1 := hk
  have hgy : g * a.y = a.y * g := by
    have hk2 : (k : ↥(Cen a.u)) * y' = y' * k := mem_centralizer_singleton_iff.1 k.2
    exact congrArg Subtype.val hk2
  obtain ⟨α, β, hαβ, hα, hβ⟩ := s11_map_eq_base (S11_f₀ a) (w := (S11_pd hb a).rho k)
    (b₁ := r₀) (b₂ := 1) hgk
  have hβ1 : β = 1 := S11_f₀_injective a (by rw [hβ, map_one])
  subst hβ1
  have hpd := S11_pd hb a
  have hn : g ∈ normalizer (a.L₁ : Set G) := by
    have h1 : hpd.rho k ∈ (baseSubgroup : Subgroup (Wr2 (MulAut ↥a.L₁))) := by
      rw [hαβ]; exact ⟨(α, 1), rfl⟩
    have h2 := (hpd.rho_mem_baseSubgroup_iff k).1 h1
    exact (mem_normalizer_iff_map_eq a.L₁ g).2 h2
  have hrho := hpd.rho_of_normalizes k hn
  rw [hαβ, base_injective] at hrho
  obtain ⟨hα', hβ'⟩ := hrho
  have hgXt0 : ∀ k' ∈ a.L₁, g * (t * k' * t⁻¹) = (t * k' * t⁻¹) * g := by
    intro k' hk'
    have h1 := (conjAutOf_eq_one_iff a.L₁ (hpd.tpt_mem_normalizer hn)).1 hβ'.symm k' hk'
    have h2 := commute_conj_iff g k' t
    rw [ht'] at h2 ⊢
    have := (h2.1 h1).eq
    exact this
  have hgx : g * x = x * g := by
    have hxt : t * x * t⁻¹ ∈ conjSub t a.L₁ := ⟨x, hx, rfl⟩
    have h1 := hgXt0 x hx
    have h2 : g * (x * (t * x * t⁻¹)) = (x * (t * x * t⁻¹)) * g := by rw [← hxy]; exact hgy
    have h3 : g * x * (t * x * t⁻¹) = x * g * (t * x * t⁻¹) := by
      calc g * x * (t * x * t⁻¹) = g * (x * (t * x * t⁻¹)) := mul_assoc _ _ _
        _ = (x * (t * x * t⁻¹)) * g := h2
        _ = x * ((t * x * t⁻¹) * g) := mul_assoc _ _ _
        _ = x * (g * (t * x * t⁻¹)) := by rw [h1]
        _ = x * g * (t * x * t⁻¹) := (mul_assoc _ _ _).symm
    exact mul_right_cancel h3
  have hact : ∀ l : ↥a.L₁, s11Pi a.L₁ (S11_e a) ⟨g * l * g⁻¹, (mem_normalizer_iff.1 hn l.1).1 l.2⟩ =
      r₀ (s11Pi a.L₁ (S11_e a) l) := by
    intro l
    have h1 := S11_f₀_apply a α l
    rw [hα] at h1
    have hl : (α l : G) = g * l * g⁻¹ := by rw [hα']; rfl
    rw [h1]
    congr 1
    exact Subtype.ext hl.symm
  have hsq : ∀ c ∈ X, g * g * c = c * g * g := by
    intro c hc
    have hker2 : (k : ↥(Cen a.u)) * k ∈ (S11_rhoBar hb a).ker := by
      rw [MonoidHom.mem_ker, map_mul, hgk, base_mul_base, hr₀sq, mul_one, base_one]
    rw [S11_rhoBar_ker] at hker2
    have h1 := ((hpd.rho_eq_one_iff _).1 (MonoidHom.mem_ker.1 hker2)).1 c (h.le_L₁ hc)
    have h2 : g * g * c = c * (g * g) := h1.eq
    rw [h2, mul_assoc]
  refine ⟨g, mem_Cen.2 hgy, (k : ↥(Cen a.u)).2, hgx, ?_, ?_, hsq, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact hgXt0 c (h.le_L₁ hc)
  · intro c hc
    have hcL := h.le_L₁ hc
    have hcx : c * x = x * c := mem_centralizer_singleton_iff.1 (h.le hc).2
    have hgL : g * c * g⁻¹ ∈ a.L₁ := (mem_normalizer_iff.1 hn c).1 hcL
    have hc' : g * c * g⁻¹ ∈ a.L₁ ⊓ centralizer ({x} : Set G) := by
      refine ⟨hgL, mem_centralizer_singleton_iff.2 ?_⟩
      have hxg : Commute g x := hgx
      exact (((hxg.mul_left (show Commute c x from hcx)).mul_left hxg.inv_left)).eq
    by_cases h1 : g * c * g⁻¹ = 1
    · rw [h1]; exact X.one_mem
    · have h3 : (g * c * g⁻¹) ^ 3 = 1 := by
        rw [conj_pow, h.cube c hc]; group
      exact h.three _ hc' (orderOf_eq_prime h3 h1)
  · by_contra hcon
    push Not at hcon
    have hfix : ∀ b ∈ centralizer ({s11Pi a.L₁ (S11_e a) ⟨x, hx⟩} :
        Set (alternatingGroup (Fin 6))), r₀ b = b := by
      intro b hb'
      obtain ⟨c, hcX, hcb⟩ := h.lift b hb'
      have hgc : g * c = c * g := hcon c hcX
      have h1 := hact c
      have h2 : (⟨g * c * g⁻¹, (mem_normalizer_iff.1 hn c.1).1 c.2⟩ : ↥a.L₁) = c :=
        Subtype.ext (show g * (c : G) * g⁻¹ = c by rw [hgc]; group)
      rw [h2, hcb] at h1
      exact h1.symm
    obtain ⟨b₀, hb₀, hr⟩ := mem_inner_of_fix_centralizer hπ r₀ hfix
    have h3 : r₀ ^ 3 = 1 := by
      rw [hr, ← map_pow, pow_three_of_mem_centralizer hπ b₀ hb₀, map_one]
    have h4 : r₀ ^ 3 = r₀ := by rw [pow_succ, pow_two, hr₀sq, one_mul]
    have h5 : r₀ = 1 := by rw [← h4, h3]
    rw [h5, orderOf_one] at hr₀2
    omega

end Reflect

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
