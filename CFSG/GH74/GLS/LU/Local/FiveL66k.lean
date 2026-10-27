module

public import CFSG.GH74.GLS.LU.Local.FiveL66g

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local.Five

section NoInv

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ : G} {Gs : Type} [Group Gs] {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ht : t ∈ Cz z} {hu : u ∈ Cz z} {ψ : ↥(Cz z) ≃* ↥(Cz z')}

omit [Finite G] in
theorem ModelPic.no_inv_G (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ)
    (b66 : Five66W z t u K₁ K₂ H w₁) {R : Subgroup G} (hR : R ≤ Cz z)
    (hRH : ∀ h ∈ H, cjL h R = R) (hRo : ∀ r ∈ R, ¬ 2 ∣ orderOf r ∧ ¬ 5 ∣ orderOf r) : R = ⊥ := by
  have hK₁le : K₁ ≤ Cz z := by rw [← pic.K₁_eq]; exact pull_le ψ K₁'
  have hw₁C : w₁ ∈ Cz z := hK₁le b66.w₁_mem
  obtain ⟨hT, -, -, -⟩ := pic.torus_of_five66W b66 hw₁C
  have hRo' : ∀ r' ∈ push ψ R, ¬ 2 ∣ orderOf r' ∧ ¬ 5 ∣ orderOf r' := by
    intro r' hr'
    obtain ⟨x, hxC, hxR, rfl⟩ := exists_pe_of_mem_push ψ hr'
    have h1 : orderOf (pe ψ x hxC) = orderOf x := orderOf_psi ψ hxC
    rw [h1]
    exact hRo x hxR
  have h := pic.facts.no_inv _ hT (push ψ R) (push_le ψ R) (push_hinv ψ hR hRH) hRo'
  have h2 := congrArg (pull ψ) h
  rwa [pull_push ψ hR, pull_bot] at h2

theorem ModelPic.inf_cent_eq_bot (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ)
    (b66 : Five66W z t u K₁ K₂ H w₁) (hNH : ∀ n ∈ NN z u, cjL n H = H) {Y : Subgroup G}
    (hYo : ∀ y ∈ Y, ¬ 2 ∣ orderOf y ∧ ¬ 5 ∣ orderOf y) (hYH : ∀ h ∈ H, cjL h Y = Y) {g s : G}
    (hg : g ∈ NN z u) (hgs : g * s * g⁻¹ = z) (hsH : ∀ h ∈ H, h * s = s * h) :
    Y ⊓ centralizer ({s} : Set G) = ⊥ := by
  have hRH : ∀ h ∈ H, cjL h (Y ⊓ centralizer ({s} : Set G)) = Y ⊓ centralizer ({s} : Set G) := by
    intro h hh
    have hc : h ∈ centralizer ({s} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hsH h hh)
    rw [cjL_inf, hYH h hh, cjL_eq_of_mem_normalizer (Subgroup.le_normalizer hc)]
  set Rs := Y ⊓ centralizer ({s} : Set G) with hRs
  have hle : cjL g Rs ≤ Cz z := by
    intro y hy
    have hy' : g⁻¹ * y * g ∈ Rs := mem_cjL.mp hy
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hy'.2
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc y * z = g * ((g⁻¹ * y * g) * s) * g⁻¹ := by rw [← hgs]; group
      _ = g * (s * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = z * y := by rw [← hgs]; group
  have hinv : ∀ h ∈ H, cjL h (cjL g Rs) = cjL g Rs := by
    intro h hh
    have h' : g⁻¹ * h * g ∈ H := by
      have := (hNH g hg)
      have h2 : h ∈ cjL g H := by rw [this]; exact hh
      exact mem_cjL.mp h2
    have e : h * g = g * (g⁻¹ * h * g) := by group
    rw [cjL_cjL, e, ← cjL_cjL, hRH _ h']
  have hord : ∀ y ∈ cjL g Rs, ¬ 2 ∣ orderOf y ∧ ¬ 5 ∣ orderOf y := by
    intro y hy
    have hy' : g⁻¹ * y * g ∈ Rs := mem_cjL.mp hy
    have hconj : IsConj y (g⁻¹ * y * g) := isConj_iff.mpr ⟨g⁻¹, by group⟩
    rw [orderOf_eq_of_isConj hconj]
    exact hYo _ hy'.1
  have hbot := pic.no_inv_G b66 hle hinv hord
  have h3 : cjL g Rs = cjL g ⊥ := hbot.trans (Subgroup.map_bot _).symm
  exact (cjL_inj g).mp h3

theorem ModelPic.no_inv_sub (c : FiveCtx G p f z S K₁ K₂ t u)
    (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ)
    (b66 : Five66W z t u K₁ K₂ H w₁) {x : G} (hxN : x ∈ NN z u) (hxz : x * z * x⁻¹ = u)
    (hxu : x * u * x⁻¹ = z * u) (hNH : ∀ n ∈ NN z u, cjL n H = H) :
    ∀ Y : Subgroup G, (∀ y ∈ Y, ¬ 2 ∣ orderOf y ∧ ¬ 5 ∣ orderOf y) →
      (∀ h ∈ H, cjL h Y = Y) → Y = ⊥ := by
  intro Y hYo hYH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z * z = 1 := c.hs.z_sq
  have hu2 : u * u = 1 := c.hs.u_sq
  have hzu : z * u = u * z := c.hs.zu_comm
  have hHz : ∀ h ∈ H, h * z = z * h := fun h hh => (b66.H_cent h hh).1
  have hHu : ∀ h ∈ H, h * u = u * h := fun h hh => (b66.H_cent h hh).2
  have hHzu : ∀ h ∈ H, h * (z * u) = (z * u) * h := by
    intro h hh
    calc h * (z * u) = (h * z) * u := by group
      _ = (z * h) * u := by rw [hHz h hh]
      _ = z * (h * u) := by group
      _ = z * (u * h) := by rw [hHu h hh]
      _ = (z * u) * h := by group
  have hxi : x⁻¹ ∈ NN z u := (NN z u).inv_mem hxN
  have hxuz : x⁻¹ * u * x⁻¹⁻¹ = z := by
    have : x⁻¹ * u * x = z := by rw [← hxz]; group
    simpa using this
  have hxzu : x⁻¹ * (z * u) * x⁻¹⁻¹ = u := by
    have : x⁻¹ * (z * u) * x = u := by rw [← hxu]; group
    simpa using this
  have hRz : Y ⊓ centralizer ({z} : Set G) = ⊥ := by
    refine pic.inf_cent_eq_bot b66 hNH hYo hYH (g := 1) (s := z) (NN z u).one_mem (by simp) hHz
  have hRu : Y ⊓ centralizer ({u} : Set G) = ⊥ :=
    pic.inf_cent_eq_bot b66 hNH hYo hYH (g := x⁻¹) (s := u) hxi hxuz hHu
  have hRzu : Y ⊓ centralizer ({z * u} : Set G) = ⊥ := by
    refine pic.inf_cent_eq_bot b66 hNH hYo hYH (g := x⁻¹ * x⁻¹) (s := z * u)
      ((NN z u).mul_mem hxi hxi) ?_ hHzu
    calc x⁻¹ * x⁻¹ * (z * u) * (x⁻¹ * x⁻¹)⁻¹ = x⁻¹ * (x⁻¹ * (z * u) * x⁻¹⁻¹) * x⁻¹⁻¹ := by
          simp only [mul_inv_rev, inv_inv, mul_assoc]
      _ = z := by rw [hxzu, hxuz]
  have hzY : z ∈ normalizer (Y : Set G) :=
    mem_normalizer_of_cjL_eq (hYH z b66.z_mem)
  have huY : u ∈ normalizer (Y : Set G) :=
    mem_normalizer_of_cjL_eq (hYH u b66.u_mem)
  have hodd : Odd (Nat.card ↥Y) := by
    by_contra hne
    have h2 : 2 ∣ Nat.card ↥Y := by
      rcases Nat.even_or_odd (Nat.card ↥Y) with h | h
      · exact even_iff_two_dvd.mp h
      · exact absurd h hne
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hi : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
    exact (hYo (y : G) y.2).1 (by rw [hi])
  have hu1 : u ≠ 1 := by
    intro h
    have := c.hs.u_ord
    rw [h, orderOf_one] at this
    omega
  have hBW := CFSG.Walter.J1.card_mul_card_sq_eq_mul hz2 hu2 c.z_ne_one hu1
    (fun h => c.hs.u_ne h.symm) hzu Y hzY huY hodd
  have h1 : Y ⊓ centralizer ({z} : Set G) ⊓ centralizer ({u} : Set G) = ⊥ := by
    rw [hRz, bot_inf_eq]
  rw [h1, hRz, hRu, hRzu] at hBW
  simp only [Subgroup.card_bot, one_pow, mul_one] at hBW
  exact Subgroup.eq_bot_of_card_eq _ hBW

end NoInv

end CFSG.GH74.GLS.LU.Local.Five
