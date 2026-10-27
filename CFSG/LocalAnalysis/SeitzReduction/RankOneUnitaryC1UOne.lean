module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1U
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiUOne

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem conj_R₂_mem_u3C1U (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) {x : G}
    (hx : x ∈ u3C1U L T R₂ t) {r : G} (hr : r ∈ R₂) :
    r⁻¹ * (x * r * x⁻¹) ∈ szA₁ (szT₁ L T) := by
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  refine hR.conj_mem_of_inv hinv (mem_inf.mp (hNR₁ hx.1)).2 (fun b hb => ?_) hr
  rw [← mem_centralizer_iff.mp hx.2.1 b hb, mul_inv_cancel_right]

omit [Finite G] in
theorem conj_szA₁_of_mem_u3C1U {R₂ : Subgroup G} {x : G} (hx : x ∈ u3C1U L T R₂ t) {b : G}
    (hb : b ∈ szA₁ (szT₁ L T)) : x * b * x⁻¹ = b := by
  rw [← mem_centralizer_iff.mp hx.2.1 b hb, mul_inv_cancel_right]

theorem mem_sup_of_mem_szR_of_comm {R₂ : Subgroup G} (hR : U3R2 G L (szT₁ L T) R₂ t f)
    (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) (hne : ∃ r ∈ R₂, r ^ 2 ≠ 1) {x : G}
    (hx : x ∈ szR (szT₁ L T) R₂ t) (hxC : ∀ r ∈ R₂, x * r * x⁻¹ = r) : x ∈ szT₁ L T ⊔ R₂ := by
  obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_of_mem_szR hR hx
  rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with hz1 | hz1
  · rw [hz1, mul_one]; exact hw
  · exfalso
    obtain ⟨r, hr, hrt⟩ := U3R2.exists_not_comm_t_of_inv hinv hne
    apply hrt
    have hwr : w * r * w⁻¹ = r := by
      rw [← hR.comm_of_mem_sup hr hw, mul_inv_cancel_right]
    have h1 := hxC r hr
    rw [hz1] at h1
    have h2 : w * (t * r * t⁻¹) * w⁻¹ = w * r * w⁻¹ := by
      calc w * (t * r * t⁻¹) * w⁻¹ = w * t * r * (w * t)⁻¹ := by group
        _ = r := h1
        _ = w * r * w⁻¹ := hwr.symm
    have h3 : t * r * t⁻¹ = r := mul_left_cancel (mul_right_cancel h2)
    calc t * r = t * r * t⁻¹ * t := by group
      _ = r * t := by rw [h3]

theorem exists_conj_t_eq_of_mem_szA (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) {y : G}
    (hy : y ∈ normalizer (szR (szT₁ L T) R₂ t : Set G)) (hyt : y * t * y⁻¹ ∈ szA L T t) :
    y * t * y⁻¹ * t⁻¹ ∈ szA₁ (szT₁ L T) := by
  obtain ⟨r, hr, hrt⟩ := h.exists_conj_t_eq_of_inv hS2 hR hinv hy
  rw [hrt] at hyt ⊢
  obtain ⟨a, ha, z, hz, haz⟩ := exists_mul_eq_of_mem_sup_zpowers
    (centralizer_le (szA₁_le _) h.mem_centralizer_szT₁) hyt
  rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with hz1 | hz1
  · exfalso
    rw [hz1, mul_one] at haz
    apply h.t_not_mem_sup_of_card_sylow hS2 hR
    have : t = r⁻¹ * a := by rw [haz]; group
    rw [this]
    exact mul_mem (mem_sup_right (inv_mem hr)) (mem_sup_left (szA₁_le _ ha))
  · rw [hz1] at haz
    rw [mul_inv_cancel_right, ← mul_right_cancel haz]
    exact ha

omit [Finite G] in
theorem conj_t_mem_self (x : G) {A₁ : Subgroup G} :
    x * t * x⁻¹ * ((x * t * x⁻¹ * t⁻¹) * t)⁻¹ ∈ A₁ := by
  rw [show x * t * x⁻¹ * ((x * t * x⁻¹ * t⁻¹) * t)⁻¹ = 1 by group]
  exact one_mem _

section Certificates


theorem conj_t_not_mem_u3C1U (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) {u : G}
    (hu : u ∈ u3C1U L T R₂ t) (huR : u ∉ szR (szT₁ L T) R₂ t) : u * t * u⁻¹ ∉ szA L T t := by
  intro hut
  have hb := h.exists_conj_t_eq_of_mem_szA hS2 hR hinv hu.1 hut
  have huA : u ∈ normalizer (szA L T t : Set G) :=
    mem_normalizer_szA_of_conj_t_mem (centralizer_le_normalizer _ hu.2.1) hb (by group)
  apply huR
  rw [← h.u3C1U_inf_normalizer_szA hS2 hR]
  exact mem_inf.mpr ⟨hu, huA⟩

theorem mem_szR_of_conj_t_mem_u3C1U (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {u : G} (hu : u ∈ u3C1U L T R₂ t)
    (hut : u * t * u⁻¹ * t⁻¹ ∈ szA₁ (szT₁ L T)) : u ∈ szR (szT₁ L T) R₂ t := by
  rw [← h.u3C1U_inf_normalizer_szA hS2 hR]
  have huA : u ∈ normalizer (szA L T t : Set G) :=
    mem_normalizer_szA_of_conj_t_mem (centralizer_le_normalizer _ hu.2.1) hut (by group)
  exact mem_inf.mpr ⟨hu, huA⟩

theorem comm_mem_sup_of_u3C1U (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hne : ∃ r ∈ R₂, r ^ 2 ≠ 1) {x y : G} (hx : x ∈ u3C1U L T R₂ t)
    (hy : y ∈ u3C1U L T R₂ t) : x * y * x⁻¹ * y⁻¹ ∈ szT₁ L T ⊔ R₂ := by
  set A₁ := szA₁ (szT₁ L T) with hA₁
  have hσ : ∀ z ∈ u3C1U L T R₂ t, z * t * z⁻¹ * t⁻¹ ∈ R₂ := fun z hz => by
    obtain ⟨r, hr, hrt⟩ := h.exists_conj_t_eq_of_inv hS2 hR hinv hz.1
    rw [hrt, mul_inv_cancel_right]; exact hr
  have hRt : ∀ z ∈ u3C1U L T R₂ t, ∀ s ∈ R₂, s⁻¹ * (z * s * z⁻¹) ∈ A₁ := fun z hz s hs =>
    h.conj_R₂_mem_u3C1U hS2 hR hinv hz hs
  have hAt : ∀ z ∈ u3C1U L T R₂ t, ∀ a ∈ A₁, z * a * z⁻¹ = a := fun z hz a ha =>
    conj_szA₁_of_mem_u3C1U hz ha
  set rx := x * t * x⁻¹ * t⁻¹ with hrx
  set ry := y * t * y⁻¹ * t⁻¹ with hry
  have hrxR := hσ x hx
  have hryR := hσ y hy
  have hxi := U3C1.inv_conj_t_mem hR.le hR.comm hrxR (fun s hs => hRt _ (inv_mem hx) s hs)
    (hAt x hx) (conj_t_mem_self x)
  have hyi := U3C1.inv_conj_t_mem hR.le hR.comm hryR (fun s hs => hRt _ (inv_mem hy) s hs)
    (hAt y hy) (conj_t_mem_self y)
  have h1 := U3C1.mul_conj_t_mem hR.le hR.comm (inv_mem hryR) (hRt _ (inv_mem hx))
    (hAt _ (inv_mem hx)) hxi hyi
  have h2 := U3C1.mul_conj_t_mem hR.le hR.comm (mul_mem (inv_mem hryR) (inv_mem hrxR))
    (hRt _ hy) (hAt _ hy) (conj_t_mem_self y) h1
  have h3 := U3C1.mul_conj_t_mem hR.le hR.comm (mul_mem (mul_mem (inv_mem hryR)
    (inv_mem hrxR)) hryR) (hRt _ hx) (hAt _ hx) (conj_t_mem_self x) h2
  have hone : ry⁻¹ * rx⁻¹ * ry * rx = 1 := by
    have hc : rx⁻¹ * ry = ry * rx⁻¹ := hR.comm _ (inv_mem hrxR) _ hryR
    calc ry⁻¹ * rx⁻¹ * ry * rx = ry⁻¹ * (rx⁻¹ * ry) * rx := by
          simp only [mul_assoc]
      _ = ry⁻¹ * (ry * rx⁻¹) * rx := by rw [hc]
      _ = 1 := by simp only [inv_mul_cancel_left, inv_mul_cancel]
  rw [hone, one_mul, show x * (y * (x⁻¹ * y⁻¹)) = x * y * x⁻¹ * y⁻¹ by group] at h3
  have hc : x * y * x⁻¹ * y⁻¹ ∈ u3C1U L T R₂ t :=
    mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hcR := h.mem_szR_of_conj_t_mem_u3C1U hS2 hR hc h3
  refine mem_sup_of_mem_szR_of_comm hR hinv hne hcR fun r hr => ?_
  have key : ∀ x' ∈ u3C1U L T R₂ t, ∀ y' ∈ u3C1U L T R₂ t,
      x' * y' * r * (x' * y')⁻¹ = y' * x' * r * (y' * x')⁻¹ := by
    intro x' hx' y' hy'
    obtain ⟨a, haA, ha'⟩ : ∃ a ∈ A₁, x' * r * x'⁻¹ = r * a := ⟨_, hRt x' hx' r hr, by group⟩
    obtain ⟨b, hbA, hb'⟩ : ∃ b ∈ A₁, y' * r * y'⁻¹ = r * b := ⟨_, hRt y' hy' r hr, by group⟩
    have e1 : x' * y' * r * (x' * y')⁻¹ = r * a * b := by
      calc x' * y' * r * (x' * y')⁻¹ = x' * (y' * r * y'⁻¹) * x'⁻¹ := by group
        _ = x' * (r * b) * x'⁻¹ := by rw [hb']
        _ = (x' * r * x'⁻¹) * (x' * b * x'⁻¹) := by group
        _ = r * a * b := by rw [ha', hAt x' hx' b hbA]
    have e2 : y' * x' * r * (y' * x')⁻¹ = r * b * a := by
      calc y' * x' * r * (y' * x')⁻¹ = y' * (x' * r * x'⁻¹) * y'⁻¹ := by group
        _ = y' * (r * a) * y'⁻¹ := by rw [ha']
        _ = (y' * r * y'⁻¹) * (y' * a * y'⁻¹) := by group
        _ = r * b * a := by rw [hb', hAt y' hy' a haA]
    rw [e1, e2, mul_assoc, mul_assoc, hR.comm a (hR.le haA) b (hR.le hbA)]
  have h4 := key x⁻¹ (inv_mem hx) y⁻¹ (inv_mem hy)
  calc x * y * x⁻¹ * y⁻¹ * r * (x * y * x⁻¹ * y⁻¹)⁻¹ =
      x * y * (x⁻¹ * y⁻¹ * r * (x⁻¹ * y⁻¹)⁻¹) * (x * y)⁻¹ := by group
    _ = x * y * (y⁻¹ * x⁻¹ * r * (y⁻¹ * x⁻¹)⁻¹) * (x * y)⁻¹ := by rw [h4]
    _ = r := by group

theorem sq_mem_sup_of_u3C1U (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hne : ∃ r ∈ R₂, r ^ 2 ≠ 1) {x : G} (hx : x ∈ u3C1U L T R₂ t) :
    x ^ 2 ∈ szT₁ L T ⊔ R₂ := by
  have hσ : x * t * x⁻¹ * t⁻¹ ∈ R₂ := by
    obtain ⟨r, hr, hrt⟩ := h.exists_conj_t_eq_of_inv hS2 hR hinv hx.1
    rw [hrt, mul_inv_cancel_right]; exact hr
  have h1 := U3C1.mul_conj_t_mem hR.le hR.comm hσ
    (fun s hs => h.conj_R₂_mem_u3C1U hS2 hR hinv hx hs)
    (fun a ha => conj_szA₁_of_mem_u3C1U hx ha) (conj_t_mem_self x) (conj_t_mem_self x)
  have hsqA : (x * t * x⁻¹ * t⁻¹) * (x * t * x⁻¹ * t⁻¹) ∈ szA₁ (szT₁ L T) := by
    rw [← sq]; exact hR.sq_mem _ hσ
  have h2 : x ^ 2 * t * (x ^ 2)⁻¹ * t⁻¹ ∈ szA₁ (szT₁ L T) := by
    have e : x ^ 2 * t * (x ^ 2)⁻¹ * t⁻¹ =
        (x * x * t * (x * x)⁻¹ * ((x * t * x⁻¹ * t⁻¹) * (x * t * x⁻¹ * t⁻¹) * t)⁻¹) *
          ((x * t * x⁻¹ * t⁻¹) * (x * t * x⁻¹ * t⁻¹)) := by rw [sq]; group
    rw [e]
    exact mul_mem h1 hsqA
  have hxR := h.mem_szR_of_conj_t_mem_u3C1U hS2 hR (pow_mem hx 2) h2
  refine mem_sup_of_mem_szR_of_comm hR hinv hne hxR fun r hr => ?_
  set a := r⁻¹ * (x * r * x⁻¹) with ha
  have haA : a ∈ szA₁ (szT₁ L T) := h.conj_R₂_mem_u3C1U hS2 hR hinv hx hr
  have e1 : x * r * x⁻¹ = r * a := by rw [ha]; group
  calc x ^ 2 * r * (x ^ 2)⁻¹ = x * (x * r * x⁻¹) * x⁻¹ := by rw [sq]; group
    _ = r * a * (x * a * x⁻¹) := by rw [e1, show x * (r * a) * x⁻¹ = x * r * x⁻¹ * (x * a * x⁻¹)
          by group, e1]
    _ = r * a ^ 2 := by rw [conj_szA₁_of_mem_u3C1U hx haA, sq, mul_assoc]
    _ = r := by rw [hR.sq_A₁ a haA, mul_one]

theorem exists_u3C1U₁ (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hne : ∃ r ∈ R₂, r ^ 2 ≠ 1) {d : G} (hdY : d ∈ normalizer (szR (szT₁ L T) R₂ t : Set G))
    (hdodd : Odd (orderOf d)) (hdt : d * t = t * d)
    (hdfix : ∀ r ∈ R₂, r⁻¹ * (d⁻¹ * r * d) ∈ szA₁ (szT₁ L T) → r ∈ szA₁ (szT₁ L T)) :
    ∃ U₁ : Subgroup G, szT₁ L T ⊔ R₂ ≤ U₁ ∧ U₁ ≤ u3C1U L T R₂ t ∧
      u3C1U L T R₂ t ≤ normalizer (U₁ : Set G) ∧ t ∉ U₁ ∧
      U₁ ⊔ zpowers t = u3C1U L T R₂ t ∧ d ∈ normalizer (U₁ : Set G) ∧
      U₁ ⊓ szR (szT₁ L T) R₂ t = szT₁ L T ⊔ R₂ := by
  obtain ⟨hYT, hYA⟩ := h.normalizer_szR_le_normalizer_szT₁_of_inv hS2 hR hinv hne
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  have hR₁U := h.szR_le_u3C1U hS2 hR
  have hHU : szT₁ L T ⊔ R₂ ≤ u3C1U L T R₂ t := (sup_le_szR _ _ _).trans hR₁U
  have hUH : u3C1U L T R₂ t ≤ normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) :=
    fun x hx => (mem_inf.mp (hNR₁ hx.1)).1
  have htU : t ∈ u3C1U L T R₂ t := hR₁U (mem_szR_right _ _ _)
  have htH := h.t_not_mem_sup_of_card_sylow hS2 hR
  have hdtd : d * t * d⁻¹ = t := by rw [hdt, mul_inv_cancel_right]
  have hσ : ∀ z ∈ u3C1U L T R₂ t, z * t * z⁻¹ * t⁻¹ ∈ R₂ := fun z hz => by
    obtain ⟨r, hr, hrt⟩ := h.exists_conj_t_eq_of_inv hS2 hR hinv hz.1
    rw [hrt, mul_inv_cancel_right]; exact hr
  have hfix : ∀ w ∈ u3C1U L T R₂ t, w⁻¹ * (d⁻¹ * w * d) ∈ szT₁ L T ⊔ R₂ →
      w ∈ szT₁ L T ⊔ R₂ ∨ t⁻¹ * w ∈ szT₁ L T ⊔ R₂ := by
    intro w hw hwd
    have hzR₁ : w⁻¹ * (d⁻¹ * w * d) ∈ szR (szT₁ L T) R₂ t := sup_le_szR _ _ _ hwd
    have hzU := hR₁U hzR₁
    have hzA : w⁻¹ * (d⁻¹ * w * d) ∈ normalizer (szA L T t : Set G) := by
      rw [← h.u3C1U_inf_normalizer_szA hS2 hR] at hzR₁; exact (mem_inf.mp hzR₁).2
    have hσz := h.exists_conj_t_eq_of_mem_szA hS2 hR hinv hzU.1
      ((mem_normalizer_iff.mp hzA t).mp (mem_sup_right (mem_zpowers t)))
    have h1 := U3C1.mul_conj_t_mem hR.le hR.comm (hR.le hσz)
      (fun s hs => h.conj_R₂_mem_u3C1U hS2 hR hinv hw hs) (fun a ha => conj_szA₁_of_mem_u3C1U hw ha)
      (conj_t_mem_self w) (conj_t_mem_self (w⁻¹ * (d⁻¹ * w * d)))
    set r := w * t * w⁻¹ * t⁻¹ with hr
    set c := w⁻¹ * (d⁻¹ * w * d) * t * (w⁻¹ * (d⁻¹ * w * d))⁻¹ * t⁻¹ with hc
    have hrR : r ∈ R₂ := hσ w hw
    have e : w * (w⁻¹ * (d⁻¹ * w * d)) * t * (w * (w⁻¹ * (d⁻¹ * w * d)))⁻¹ * (c * r * t)⁻¹ =
        (d⁻¹ * r * d) * (c * r)⁻¹ := by
      have e1 : w * (w⁻¹ * (d⁻¹ * w * d)) = d⁻¹ * w * d := by group
      rw [e1]
      calc d⁻¹ * w * d * t * (d⁻¹ * w * d)⁻¹ * (c * r * t)⁻¹ =
          d⁻¹ * w * (d * t * d⁻¹) * w⁻¹ * d * t⁻¹ * (c * r)⁻¹ := by group
        _ = d⁻¹ * (w * t * w⁻¹ * t⁻¹) * (t * d * t⁻¹) * (c * r)⁻¹ := by rw [hdtd]; group
        _ = (d⁻¹ * r * d) * (c * r)⁻¹ := by
            rw [← hr, show t * d * t⁻¹ = d by rw [← hdt, mul_inv_cancel_right]]
    rw [e] at h1
    have hdr : d⁻¹ * r * d ∈ R₂ := (mem_normalizer_iff''.mp (hNR₁ hdY).2 r).mp hrR
    have hrA : r ∈ szA₁ (szT₁ L T) := by
      refine hdfix r hrR ?_
      have e2 : r⁻¹ * (d⁻¹ * r * d) = (d⁻¹ * r * d) * (c * r)⁻¹ * c := by
        rw [hR.comm _ (inv_mem hrR) _ hdr]; group
      rw [e2]
      exact mul_mem h1 hσz
    have hwR := h.mem_szR_of_conj_t_mem_u3C1U hS2 hR hw hrA
    obtain ⟨w', hw', z', hz', rfl⟩ := exists_mul_of_mem_szR hR hwR
    rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz' with hz1 | hz1
    · left; rw [hz1, mul_one]; exact hw'
    · right
      rw [hz1, show t⁻¹ * (w' * t) = t⁻¹ * w' * t⁻¹⁻¹ by group]
      exact (mem_normalizer_iff.mp (inv_mem hR.t_mem_normalizer_sup) w').mp hw'
  obtain ⟨U₁, hHU₁, hU₁U, hUU₁, htU₁, hsupU₁, hdU₁⟩ := exists_complement_of_coprime hHU hUH
    (fun x hx y hy => h.comm_mem_sup_of_u3C1U hS2 hR hinv hne hx hy)
    (fun x hx => h.sq_mem_sup_of_u3C1U hS2 hR hinv hne hx)
    (le_normalizer_u3C1U hYT hYA hdY) (hNR₁ hdY).1 hdodd htU htH hdt hfix
  refine ⟨U₁, hHU₁, hU₁U, hUU₁, htU₁, hsupU₁, hdU₁, le_antisymm (fun x hx => ?_)
    (le_inf hHU₁ (sup_le_szR _ _ _))⟩
  obtain ⟨hxU₁, hxR⟩ := mem_inf.mp hx
  obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_of_mem_szR hR hxR
  rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with hz1 | hz1
  · rw [hz1, mul_one]; exact hw
  · exfalso
    apply htU₁
    rw [hz1] at hxU₁
    have := mul_mem (inv_mem (hHU₁ hw)) hxU₁
    rwa [inv_mul_cancel_left] at this

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
