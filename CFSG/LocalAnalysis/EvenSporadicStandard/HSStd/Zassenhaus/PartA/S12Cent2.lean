module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S12Cent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S12Facts

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath Open CFSG.EvenSporadicStandard.HSStd.Zassenhaus

set_option linter.unusedSectionVars false

section U1t

variable {G : Type} [Group G] {L : Subgroup G} {t : G} {E : Subgroup G} {z : G}
  (a : PA11 L t E z)

theorem PA11.sign_swap_of_firstType (h : a.FirstType) :
    ∃ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = -1 ∧ σ * σ = 1 ∧ ∃ hc : a.u₁ ∈ Cen a.y,
      a.phi ⟨a.u₁, hc⟩ = base σ 1 := by
  obtain ⟨σ, ⟨p, q, hpq, rfl⟩, hc, hι⟩ := h
  exact ⟨_, Equiv.Perm.sign_swap hpq, Equiv.swap_mul_self p q, hc, hι⟩

theorem PA11.u₁t_mem (hc : a.u₁ ∈ Cen a.y) : t * a.u₁ * t⁻¹ ∈ Cen a.y :=
  mul_mem (mul_mem a.t_cy hc) (inv_mem a.t_cy)

theorem PA11.phi_u₁t {σ : Equiv.Perm (Fin 5)} (hc : a.u₁ ∈ Cen a.y)
    (hι : a.phi ⟨a.u₁, hc⟩ = base σ 1) (hmem : t * a.u₁ * t⁻¹ ∈ Cen a.y) :
    a.phi ⟨t * a.u₁ * t⁻¹, hmem⟩ = base 1 σ := by
  have h1 := a.phi_conj hc hmem
  rw [h1, hι, tau_mul_base, mul_assoc, tau_mul_tau, mul_one]

theorem PA11.u₁_K₁t (htt : t * t = 1) (h : a.FirstType) {b : G} (hb : b ∈ a.K₁) :
    a.u₁ * (t * b * t⁻¹) = (t * b * t⁻¹) * a.u₁ := by
  obtain ⟨σ, hsg, hsq, hc, hι⟩ := a.sign_swap_of_firstType h
  have hmem := a.u₁t_mem hc
  have h1 := a.comm_K₁_of hmem (a.phi_u₁t hc hι hmem) hb
  have h2 := (s12_conj_comm_iff t (t * a.u₁ * t⁻¹) b).2 h1
  rw [conj_conj_of_sq htt] at h2
  exact h2

end U1t

section Decomp

variable {G : Type} [Group G] {L : Subgroup G} {t : G} {E : Subgroup G} {z : G}
  (a : PA11 L t E z)

theorem PA11.mem_of_phi_base (_htt : t * t = 1) (h : a.FirstType) {Hs : Subgroup G}
    (hO : fusionOddCoreOf (Cen a.y) ≤ Hs) (hK : a.K₁ ≤ Hs) (hKt : conjSub t a.K₁ ≤ Hs)
    (hu : a.u₁ ∈ Hs) (hut : t * a.u₁ * t⁻¹ ∈ Hs) {g : G} (hg : g ∈ Cen a.y)
    {s s' : Equiv.Perm (Fin 5)} (hs : a.phi ⟨g, hg⟩ = base s s') : g ∈ Hs := by
  obtain ⟨σ, hsg, hsq, hc, hι⟩ := a.sign_swap_of_firstType h
  have hmem := a.u₁t_mem hc
  have hιt := a.phi_u₁t hc hι hmem
  have key : ∀ (g' : G) (hg' : g' ∈ Cen a.y) (p q : Equiv.Perm (Fin 5)),
      Equiv.Perm.sign p = 1 → Equiv.Perm.sign q = 1 → a.phi ⟨g', hg'⟩ = base p q → g' ∈ Hs := by
    intro g' hg' p q hp hq hpq
    have := a.P₁_eq ⟨hg', ⟨p, Equiv.Perm.mem_alternatingGroup.2 hp⟩,
      ⟨q, Equiv.Perm.mem_alternatingGroup.2 hq⟩, hpq⟩
    exact (sup_le (sup_le hO hK) hKt) this
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h1 | h1 <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign s') with h2 | h2
  · exact key g hg s s' h1 h2 hs
  ·
    have hg' : g * (t * a.u₁ * t⁻¹) ∈ Cen a.y := mul_mem hg hmem
    have := key _ hg' s (s' * σ) h1 (by rw [map_mul, h2, hsg]; decide) (by
      have e : (⟨g * (t * a.u₁ * t⁻¹), hg'⟩ : ↥(Cen a.y)) = ⟨g, hg⟩ * ⟨_, hmem⟩ := rfl
      rw [e, map_mul, hs, hιt, base_mul_base]; simp only [mul_one])
    have h3 := mul_mem this (inv_mem hut)
    rwa [mul_inv_cancel_right] at h3
  · have hg' : g * a.u₁ ∈ Cen a.y := mul_mem hg hc
    have := key _ hg' (s * σ) s' (by rw [map_mul, h1, hsg]; decide) h2 (by
      have e : (⟨g * a.u₁, hg'⟩ : ↥(Cen a.y)) = ⟨g, hg⟩ * ⟨_, hc⟩ := rfl
      rw [e, map_mul, hs, hι, base_mul_base]; simp only [mul_one])
    have h3 := mul_mem this (inv_mem hu)
    rwa [mul_inv_cancel_right] at h3
  · have hg' : g * a.u₁ * (t * a.u₁ * t⁻¹) ∈ Cen a.y := mul_mem (mul_mem hg hc) hmem
    have := key _ hg' (s * σ) (s' * σ) (by rw [map_mul, h1, hsg]; decide)
      (by rw [map_mul, h2, hsg]; decide) (by
      have e : (⟨g * a.u₁ * (t * a.u₁ * t⁻¹), hg'⟩ : ↥(Cen a.y)) =
          ⟨g, hg⟩ * ⟨_, hc⟩ * ⟨_, hmem⟩ := rfl
      rw [e, map_mul, map_mul, hs, hι, hιt, base_mul_base, base_mul_base]; simp only [mul_one])
    have h3 := mul_mem this (inv_mem hut)
    rw [mul_inv_cancel_right] at h3
    have h4 := mul_mem h3 (inv_mem hu)
    rwa [mul_inv_cancel_right] at h4

end Decomp


section S5

variable {G : Type} [Group G] {L : Subgroup G} {t : G} {E : Subgroup G} {z : G}
  (a : PA11 L t E z)

theorem mem_sup_zpowers_decomp {K : Subgroup G} {g : G} (hg2 : g * g = 1)
    (hn : g ∈ normalizer (K : Set G)) {h : G} (hh : h ∈ K ⊔ zpowers g) :
    h ∈ K ∨ ∃ k ∈ K, h = k * g := by
  have hzN : zpowers g ≤ normalizer (K : Set G) := zpowers_le.2 hn
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K _ hzN] at hh
  obtain ⟨k, hk, m, hm, rfl⟩ := Set.mem_mul.mp hh
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hm
  rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hg2, one_zpow, mul_one]
    exact hk
  · right
    exact ⟨k, hk, by rw [zpow_add_one, zpow_mul, zpow_two, hg2, one_zpow, one_mul]⟩

theorem PA11.u₁_S5 (h : a.FirstType) :
    Nonempty (↥(a.K₁ ⊔ zpowers a.u₁) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨σ, hsg, hsq, hc, hι⟩ := a.sign_swap_of_firstType h
  have hQle : a.K₁ ⊔ zpowers a.u₁ ≤ Cen a.y := sup_le a.K₁_le (zpowers_le.2 hc)
  let φQ : ↥(a.K₁ ⊔ zpowers a.u₁) →* Wr2 (Equiv.Perm (Fin 5)) :=
    a.phi.comp (Subgroup.inclusion hQle)
  let θ : Equiv.Perm (Fin 5) →* Wr2 (Equiv.Perm (Fin 5)) :=
    (SemidirectProduct.inl : (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5)) →*
      Wr2 (Equiv.Perm (Fin 5))).comp (MonoidHom.inl _ _)
  have hθ : ∀ s, θ s = base s 1 := fun s => rfl
  have hθinj : Function.Injective θ := by
    intro s s' hss
    rw [hθ, hθ] at hss
    exact (base_injective.1 hss).1
  have hrange : φQ.range = θ.range := by
    ext w
    constructor
    · rintro ⟨q, rfl⟩
      let Qc : Subgroup G := ((θ.range).comap a.phi).map (Cen a.y).subtype
      have hK : a.K₁ ≤ Qc := fun k hk => by
        obtain ⟨σ', hσ'⟩ := a.K₁_ι k hk
        exact ⟨⟨k, a.K₁_le hk⟩, ⟨σ', (hθ _).trans hσ'.symm⟩, rfl⟩
      have hu : zpowers a.u₁ ≤ Qc := by
        rw [zpowers_le]
        exact ⟨⟨a.u₁, hc⟩, ⟨σ, (hθ _).trans hι.symm⟩, rfl⟩
      obtain ⟨g, hg, hgq⟩ := sup_le hK hu q.2
      have : g = ⟨q, hQle q.2⟩ := Subtype.ext hgq
      rw [this] at hg
      exact hg
    · rintro ⟨s, rfl⟩
      rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h1 | h1
      · obtain ⟨k, hk⟩ := a.exists_phiK ⟨s, Equiv.Perm.mem_alternatingGroup.2 h1⟩
        exact ⟨⟨k, Subgroup.mem_sup_left k.2⟩, hk⟩
      · have h2 : Equiv.Perm.sign (s * σ) = 1 := by rw [map_mul, h1, hsg]; decide
        obtain ⟨k, hk⟩ := a.exists_phiK ⟨s * σ, Equiv.Perm.mem_alternatingGroup.2 h2⟩
        have hk' : a.phi ⟨k, a.K₁_le k.2⟩ = base (s * σ) 1 := hk
        refine ⟨⟨k * a.u₁, mul_mem (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right (mem_zpowers a.u₁))⟩, ?_⟩
        show a.phi ⟨k * a.u₁, _⟩ = θ s
        have e : (⟨(k : G) * a.u₁, mul_mem (a.K₁_le k.2) hc⟩ : ↥(Cen a.y)) =
            ⟨k, a.K₁_le k.2⟩ * ⟨a.u₁, hc⟩ := rfl
        rw [e, map_mul, hk', hι, base_mul_base, hθ, mul_assoc, hsq, mul_one, mul_one]
  have hφinj : Function.Injective φQ := by
    rw [injective_iff_map_eq_one]
    intro q hq1
    have hq1' : a.phi ⟨q, hQle q.2⟩ = 1 := hq1
    rcases mem_sup_zpowers_decomp (K := a.K₁) a.u₁_sq (a.u₁_norm h) q.2 with hk | ⟨k, hk, hkq⟩
    · have := a.K₁_inj (k := q) (l := 1) hk (one_mem _) (by rw [hq1']; exact (map_one a.phi).symm)
      exact Subtype.ext this
    · exfalso
      obtain ⟨ρ, hρ⟩ := a.K₁_ι k hk
      have hρ' : a.phi ⟨k, a.K₁_le hk⟩ = base (ρ : Equiv.Perm (Fin 5)) 1 := hρ
      have e : (⟨(q : G), hQle q.2⟩ : ↥(Cen a.y)) = ⟨k, a.K₁_le hk⟩ * ⟨a.u₁, hc⟩ :=
        Subtype.ext hkq
      rw [e, map_mul, hρ', hι, base_mul_base, mul_one, ← base_one] at hq1'
      have h3 := (base_injective.1 hq1').1
      have h4 := congrArg Equiv.Perm.sign h3
      rw [map_mul, Equiv.Perm.mem_alternatingGroup.1 ρ.2, hsg, map_one] at h4
      exact absurd h4 (by decide)
  exact ⟨(MonoidHom.ofInjective hφinj).trans
    ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective hθinj).symm)⟩

theorem PA11.cent_x_xt (htt : t * t = 1) (h : a.FirstType) :
    Cen a.x ⊓ Cen (t * a.x * t⁻¹) =
      (zpowers a.x ⊔ zpowers (t * a.x * t⁻¹)) ⊔ (a.K₁ ⊔ zpowers a.u₁) ⊔
        conjSub t (a.K₁ ⊔ zpowers a.u₁) := by
  set C₀ : Subgroup G := Cen a.x ⊓ Cen (t * a.x * t⁻¹) with hC₀
  have hO : fusionOddCoreOf (Cen a.y) ≤ C₀ := fun o ho =>
    Subgroup.mem_inf.2 ⟨mem_Cen.2 (a.O_abel o ho a.x a.x_O), mem_Cen.2 (a.O_abel o ho _ a.xt_mem_O)⟩
  have hK : a.K₁ ≤ C₀ := fun k hk =>
    Subgroup.mem_inf.2 ⟨mem_Cen.2 (a.K₁_comm_O hk a.x_O), mem_Cen.2 (a.K₁_comm_O hk a.xt_mem_O)⟩
  have hu1 : a.u₁ ∈ C₀ := by
    obtain ⟨hL, hLt⟩ := Subgroup.mem_inf.1 (a.u₁_CPE a.d8_case)
    exact Subgroup.mem_inf.2 ⟨mem_Cen.2 (mem_centralizer_iff.1 hL a.x a.x_mem).symm,
      mem_Cen.2 (mem_centralizer_iff.1 hLt _ (conj_mem_conjSub a.x_mem)).symm⟩
  have hstab : ∀ g ∈ C₀, t * g * t⁻¹ ∈ C₀ := by
    intro g hg
    obtain ⟨hgx, hgxt⟩ := Subgroup.mem_inf.1 hg
    have e1 := mem_Cen.1 hgx
    have e2 := mem_Cen.1 hgxt
    refine Subgroup.mem_inf.2 ⟨mem_Cen.2 ?_, mem_Cen.2 ?_⟩
    · have := (s12_conj_comm_iff t g (t * a.x * t⁻¹)).2 e2
      rwa [conj_conj_of_sq htt] at this
    · exact (s12_conj_comm_iff t g a.x).2 e1
  have hKt : conjSub t a.K₁ ≤ C₀ := by
    rintro _ ⟨k, hk, rfl⟩
    exact hstab k (hK hk)
  have hut : t * a.u₁ * t⁻¹ ∈ C₀ := hstab _ hu1
  have hQ : a.K₁ ⊔ zpowers a.u₁ ≤ C₀ := sup_le hK (zpowers_le.2 hu1)
  have hQt : conjSub t (a.K₁ ⊔ zpowers a.u₁) ≤ C₀ := by
    rintro _ ⟨q, hq, rfl⟩
    exact hstab q (hQ hq)
  apply le_antisymm
  · intro g hg
    obtain ⟨hgx, hgxt⟩ := Subgroup.mem_inf.1 hg
    have hgy : g ∈ Cen a.y := by
      rw [mem_Cen, a.x_y]
      have c1 : Commute g a.x := mem_Cen.1 hgx
      have c2 : Commute g (t * a.x * t⁻¹) := mem_Cen.1 hgxt
      exact (c1.mul_right c2).eq
    rcases eq_base_or_eq_base_mul_tau (a.phi ⟨g, hgy⟩) with ⟨s, s', hs⟩ | ⟨s, s', hs⟩
    · refine a.mem_of_phi_base htt h ?_ ?_ ?_ ?_ ?_ hgy hs
      · rw [a.O_eq]; exact le_sup_left.trans le_sup_left
      · exact le_sup_left.trans (le_sup_right.trans le_sup_left)
      · exact (conjSub_mono (le_sup_left : a.K₁ ≤ a.K₁ ⊔ zpowers a.u₁)).trans le_sup_right
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_sup_right (mem_zpowers _)))
      · exact Subgroup.mem_sup_right (conj_mem_conjSub (Subgroup.mem_sup_right (mem_zpowers _)))
    · exfalso
      have hc : g * t ∈ Cen a.y := mul_mem hgy a.t_cy
      have hphi : a.phi ⟨g * t, hc⟩ = base s s' := by
        have e : (⟨g * t, hc⟩ : ↥(Cen a.y)) = ⟨g, hgy⟩ * ⟨t, a.t_cy⟩ := rfl
        rw [e, map_mul, hs, a.phi_apply ⟨t, a.t_cy⟩, a.ι_t, mul_assoc, tau_mul_tau, mul_one]
      have hcC : g * t ∈ C₀ := a.mem_of_phi_base htt h hO hK hKt hu1 hut hc hphi
      have hcx := mem_Cen.1 (Subgroup.mem_inf.1 hcC).1
      have e2 := mem_Cen.1 hgxt
      have h1 : (t * a.x * t⁻¹) * g * t = a.x * g * t := by
        calc (t * a.x * t⁻¹) * g * t = g * (t * a.x * t⁻¹) * t := by rw [e2]
          _ = g * t * a.x := by group
          _ = a.x * (g * t) := hcx
          _ = a.x * g * t := by group
      have h2 := mul_right_cancel (mul_right_cancel h1)
      exact a.x_ne_xt h2.symm
  · exact sup_le (sup_le (by rw [← a.O_eq]; exact hO) hQ) hQt

end S5

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
