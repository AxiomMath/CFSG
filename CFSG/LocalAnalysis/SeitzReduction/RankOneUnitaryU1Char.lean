module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineTwoFree

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.Blueprint CFSG.GH74.Uniqueness.Bender

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem comm_mem_mul_of_comm_mem {G : Type*} [Group G] {T₁ A₁ : Subgroup G} {a b : G}
    (haA : a ∈ normalizer (A₁ : Set G))
    (ha : ∀ y ∈ T₁, a * y * a⁻¹ * y⁻¹ ∈ A₁) (hb : ∀ y ∈ T₁, b * y * b⁻¹ * y⁻¹ ∈ A₁) :
    ∀ y ∈ T₁, (a * b) * y * (a * b)⁻¹ * y⁻¹ ∈ A₁ := by
  intro y hy
  have e : (a * b) * y * (a * b)⁻¹ * y⁻¹ =
      (a * (b * y * b⁻¹ * y⁻¹) * a⁻¹) * (a * y * a⁻¹ * y⁻¹) := by group
  rw [e]
  exact mul_mem ((mem_normalizer_iff.mp haA _).mp (hb y hy)) (ha y hy)

theorem comm_mem_inv_of_comm_mem {G : Type*} [Group G] {T₁ A₁ : Subgroup G} {a : G}
    (haT : a ∈ normalizer (T₁ : Set G)) (ha : ∀ y ∈ T₁, a * y * a⁻¹ * y⁻¹ ∈ A₁) :
    ∀ y ∈ T₁, a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ ∈ A₁ := by
  intro y hy
  have hy' : a⁻¹ * y * a ∈ T₁ := (mem_normalizer_iff''.mp haT y).mp hy
  have e : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = (a * (a⁻¹ * y * a) * a⁻¹ * (a⁻¹ * y * a)⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem (ha _ hy')

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem mem_sup_of_forall_comm_mem_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {v₀ : G} (hv₀T : v₀ ∈ T) (hv₀2 : v₀ ^ 2 = 1) (hv₀S : v₀ ∉ szT₁ L T ⊔ zpowers t) {s : G}
    (hsT : s ∈ T) (hs : ∀ y ∈ szT₁ L T, s * y * s⁻¹ * y⁻¹ ∈ szA₁ (szT₁ L T)) :
    s ∈ szT₁ L T ⊔ zpowers t := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, hA₁comm, -⟩ := h.facts_of_card_sylow hS2
  have hTA : ∀ x ∈ T, x ∈ normalizer (szA₁ (szT₁ L T) : Set G) := fun x hx =>
    normalizer_le_normalizer_inf_centralizer (szT₁ L T) (hTN₁ hx)
  have hT₁tT : szT₁ L T ⊔ zpowers t ≤ T := by
    obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
    exact sup_le (szT₁_le_left L T) (zpowers_le.mpr htT)
  have hN : ∀ m ∈ szT₁ L T ⊔ zpowers t, ∀ y ∈ szT₁ L T, m * y * m⁻¹ * y⁻¹ ∈ szA₁ (szT₁ L T) := by
    intro m hm
    obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hm
    refine comm_mem_mul_of_comm_mem (hTA w (szT₁_le_left L T hw)) (fun y hy => ?_)
      (fun y hy => ?_)
    · rw [hA₁comm]
      exact commutator_mem_commutator hw hy
    · rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
      · rw [hz1]; simp
      · rw [hz1, ← mem_centralizer_iff.mp h.mem_centralizer_szT₁ y hy]
        simp
  by_contra hsS
  obtain ⟨k, hk⟩ := h.isPGroup ⟨s, hsT⟩
  have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨n, hn, hn2⟩ := exists_pow_not_mem_sq_mem_of_two_pow hk' hsS
  have hpow : ∀ j : ℕ, ∀ y ∈ szT₁ L T, s ^ j * y * (s ^ j)⁻¹ * y⁻¹ ∈ szA₁ (szT₁ L T) := by
    intro j
    induction j with
    | zero => intro y _; simp
    | succ j ih =>
      rw [pow_succ]
      exact comm_mem_mul_of_comm_mem (hTA _ (pow_mem hsT j)) ih hs
  have hv₀2' : v₀ ^ 2 ∈ szT₁ L T ⊔ zpowers t := by rw [hv₀2]; exact one_mem _
  have hm := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 (pow_mem hsT n) hv₀T hn2 hv₀2' hn hv₀S
  have hmT : s ^ n * v₀⁻¹ ∈ T := hT₁tT hm
  have hminv := comm_mem_inv_of_comm_mem (hTN₁ hmT) (hN _ hm)
  have hv₀ := comm_mem_mul_of_comm_mem (hTA _ (inv_mem hmT)) hminv (hpow n)
  obtain ⟨y, hy, hyv⟩ := h.exists_comm_not_mem_of_outer_of_card_sylow hS2 hv₀T hv₀2 hv₀S
  have e : (s ^ n * v₀⁻¹)⁻¹ * s ^ n = v₀ := by group
  rw [e] at hv₀
  have h1 := hv₀ y hy
  have h2 : y * v₀ * y⁻¹ * v₀⁻¹ = (v₀ * y * v₀⁻¹ * y⁻¹)⁻¹ := by group
  exact hyv (by rw [h2]; exact inv_mem h1)

end U3Start

namespace U3U1Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}

theorem comm_t_mem_of_mem_sup (hR : U3R2 G L (szT₁ L T) R₂ t f) {y : G}
    (hy : y ∈ szT₁ L T ⊔ R₂) : y * t * y⁻¹ * t⁻¹ ∈ R₂ := by
  obtain ⟨w, hw, r, hr, rfl⟩ := hR.mem_sup_iff.mp hy
  have hrt : r * t * r⁻¹ * t⁻¹ ∈ R₂ := by
    simpa [mul_assoc] using mul_mem hr (hR.tN _ (inv_mem hr))
  have e : (w * r) * t * (w * r)⁻¹ * t⁻¹ =
      (w * (r * t * r⁻¹ * t⁻¹) * w⁻¹) * (w * t * w⁻¹ * t⁻¹) := by group
  rw [e, hR.commT₁ _ hw _ hrt, mul_inv_cancel_right, show w * t * w⁻¹ * t⁻¹ = 1 by
    rw [hR.t_comm w hw]; group, mul_one]
  exact hrt

theorem mem_of_forall_comm (hU : U3U1Data G L f t T R₂ U₁) (hR : U3R2 G L (szT₁ L T) R₂ t f)
    {x : G} (hx : x ∈ U₁) (hxT : ∀ y ∈ szT₁ L T, x * y = y * x) : x ∈ R₂ := by
  have htt : t * t = 1 := by rw [← sq, hR.t_sq]
  have htN : t ∈ normalizer (U₁ : Set G) :=
    hU.normalizer_le (Subgroup.le_normalizer (mem_szR_right _ _ _))
  have htM : ∀ y ∈ U₁, t * y * t⁻¹ ∈ U₁ := fun y hy => (mem_normalizer_iff.mp htN y).mp hy
  have hM2 : ∀ y ∈ U₁, y * y ∈ R₂ := fun y hy => by rw [← sq]; exact hU.sq_mem y hy
  have hH : ∀ c ∈ szT₁ L T ⊔ R₂, (∀ y ∈ szT₁ L T, c * y = y * c) → c ∈ R₂ := by
    intro c hc hcT
    obtain ⟨w, hw, r, hr, rfl⟩ := hR.mem_sup_iff.mp hc
    have hwZ : w ∈ szA₁ (szT₁ L T) := by
      refine mem_inf.mpr ⟨hw, mem_centralizer_iff.mpr fun y hy => ?_⟩
      have h1 := hcT y hy
      have h2 : r * y = y * r := (hR.commT₁ y hy r hr).symm
      have h3 : w * y * r = y * w * r := by
        calc w * y * r = w * (r * y) := by rw [h2]; group
          _ = w * r * y := by group
          _ = y * (w * r) := h1
          _ = y * w * r := by group
      exact (mul_right_cancel h3).symm
    exact mul_mem (hR.le hwZ) hr
  have hc : x * t * x⁻¹ * t⁻¹ ∈ szT₁ L T ⊔ R₂ :=
    hU.mem_sup_of_comm_mem hR htt (layers_comm_mem htM hx) (layers_comm_comm_mem htt htM hM2 hx)
  have hcT : ∀ y ∈ szT₁ L T, (x * t * x⁻¹ * t⁻¹) * y = y * (x * t * x⁻¹ * t⁻¹) := by
    intro y hy
    have h1 := hxT y hy
    have h2 : t * y = y * t := (hR.t_comm y hy).symm
    have h3 : x⁻¹ * y = y * x⁻¹ := by
      calc x⁻¹ * y = x⁻¹ * (y * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * y) * x⁻¹ := by rw [h1]
        _ = y * x⁻¹ := by group
    have h4 : t⁻¹ * y = y * t⁻¹ := by
      calc t⁻¹ * y = t⁻¹ * (y * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * y) * t⁻¹ := by rw [h2]
        _ = y * t⁻¹ := by group
    calc (x * t * x⁻¹ * t⁻¹) * y = x * t * x⁻¹ * (t⁻¹ * y) := by group
      _ = x * t * x⁻¹ * (y * t⁻¹) := by rw [h4]
      _ = x * t * (x⁻¹ * y) * t⁻¹ := by group
      _ = x * t * (y * x⁻¹) * t⁻¹ := by rw [h3]
      _ = x * (t * y) * x⁻¹ * t⁻¹ := by group
      _ = x * (y * t) * x⁻¹ * t⁻¹ := by rw [h2]
      _ = (x * y) * t * x⁻¹ * t⁻¹ := by group
      _ = (y * x) * t * x⁻¹ * t⁻¹ := by rw [h1]
      _ = y * (x * t * x⁻¹ * t⁻¹) := by group
  exact hH x (hU.mem_sup_of_comm_mem hR htt hx (hH _ hc hcT)) hxT

section Certificates


theorem exists_eq_of_comm_mem_of_card_sylow (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {v₀ : G} (hv₀T : v₀ ∈ T) (hv₀2 : v₀ ^ 2 = 1)
    (hv₀S : v₀ ∉ szT₁ L T ⊔ zpowers t) {x : G} (hx : x ∈ U₁ ⊔ T)
    (hxT : ∀ y ∈ szT₁ L T, x * y * x⁻¹ * y⁻¹ ∈ R₂) : ∃ u ∈ U₁, x = u ∨ x = u * t := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  have hTU := hU.le_normalizer h hS2 hR
  obtain ⟨u, hu, s, hs, rfl⟩ := exists_mul_eq_of_mem_sup_of_le_normalizer hTU hx
  have hsT : ∀ y ∈ szT₁ L T, s * y * s⁻¹ * y⁻¹ ∈ szA₁ (szT₁ L T) := by
    intro y hy
    have hsy : s * y * s⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp (hTN₁ hs) y).mp hy
    rw [← hR.inf]
    refine mem_inf.mpr ⟨mul_mem hsy (inv_mem hy), ?_⟩
    have h1 := hxT y hy
    have h2 := hU.comm_mem u hu _ (hU.le (mem_sup_left hsy))
    have e : s * y * s⁻¹ * y⁻¹ = (u * (s * y * s⁻¹) * u⁻¹ * (s * y * s⁻¹)⁻¹)⁻¹ *
        ((u * s) * y * (u * s)⁻¹ * y⁻¹) := by group
    rw [e]
    exact mul_mem (inv_mem h2) h1
  have hsS := h.mem_sup_of_forall_comm_mem_of_card_sylow hS2 hv₀T hv₀2 hv₀S hs hsT
  obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hsS
  refine ⟨u * y, mul_mem hu (hU.le (mem_sup_left hy)), ?_⟩
  rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
  · left; rw [← hyz, hz1]; group
  · right; rw [← hyz, hz1]; group

theorem exists_comm_not_mem_sup_of_card_sylow (hU : U3U1Data G L f t T R₂ U₁)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {v₀ : G} (hv₀T : v₀ ∈ T) (hv₀2 : v₀ ^ 2 = 1)
    (hv₀S : v₀ ∉ szT₁ L T ⊔ zpowers t) :
    ∃ z ∈ U₁, z * v₀ * z⁻¹ * v₀⁻¹ ∉ szT₁ L T ⊔ R₂ := by
  obtain ⟨htT, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, -, -, hNR, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hTA : T ≤ normalizer (szA L T t : Set G) :=
    Subgroup.le_normalizer.trans (h.normalizer_le_normalizer_szA_of_card_sylow hS2)
  have hvR : v₀ ∈ normalizer (R₂ : Set G) := hNR (hTA hv₀T)
  have hvU : v₀ ∈ normalizer (U₁ : Set G) := hU.le_normalizer h hS2 hR hv₀T
  have htU : t ∈ normalizer (U₁ : Set G) := hU.le_normalizer h hS2 hR htT
  have hvt : v₀ * t = t * v₀ := mem_centralizer_singleton_iff.mp (h.le hv₀T)
  by_contra hall
  push Not at hall
  obtain ⟨y, hy, hyv⟩ := h.exists_comm_not_mem_of_outer_of_card_sylow hS2 hv₀T hv₀2 hv₀S
  apply hyv
  obtain ⟨z, hz, hzy⟩ := hU.exists_inv_comm_mul_mem hR (mem_sup_left (T := R₂) hy)
  have hτz : z * t * z⁻¹ * t⁻¹ ∈ U₁ :=
    layers_comm_mem (fun x hx => (mem_normalizer_iff.mp htU x).mp hx) hz
  set m := (z * t * z⁻¹ * t⁻¹)⁻¹ * y with hm
  have hym : y = (z * t * z⁻¹ * t⁻¹) * m := by rw [hm]; group
  have hνm : m * v₀ * m⁻¹ * v₀⁻¹ ∈ R₂ := by
    simpa [mul_assoc] using mul_mem hzy ((mem_normalizer_iff.mp hvR _).mp (inv_mem hzy))
  have hsw := layers_comm_swap_mem (M := U₁) (N := R₂) hvt.symm
    (fun x hx => (mem_normalizer_iff.mp htU x).mp hx)
    (fun x hx => (mem_normalizer_iff.mp hvU x).mp hx) hU.comm_mem hz
  have hτν : (z * v₀ * z⁻¹ * v₀⁻¹) * t * (z * v₀ * z⁻¹ * v₀⁻¹)⁻¹ * t⁻¹ ∈ R₂ :=
    comm_t_mem_of_mem_sup hR (hall z hz)
  have hcen : (z * t * z⁻¹ * t⁻¹) * (m * v₀ * m⁻¹ * v₀⁻¹) * (z * t * z⁻¹ * t⁻¹)⁻¹ =
      m * v₀ * m⁻¹ * v₀⁻¹ := by
    rw [← mem_centralizer_iff.mp (hU.le_centralizer hτz) _ hνm, mul_inv_cancel_right]
  have hyR : y * v₀ * y⁻¹ * v₀⁻¹ ∈ R₂ := by
    have e : y * v₀ * y⁻¹ * v₀⁻¹ =
        ((z * t * z⁻¹ * t⁻¹) * (m * v₀ * m⁻¹ * v₀⁻¹) * (z * t * z⁻¹ * t⁻¹)⁻¹) *
          ((z * v₀ * z⁻¹ * v₀⁻¹) * t * (z * v₀ * z⁻¹ * v₀⁻¹)⁻¹ * t⁻¹) *
          (((z * t * z⁻¹ * t⁻¹) * v₀ * (z * t * z⁻¹ * t⁻¹)⁻¹ * v₀⁻¹)⁻¹ *
            ((z * v₀ * z⁻¹ * v₀⁻¹) * t * (z * v₀ * z⁻¹ * v₀⁻¹)⁻¹ * t⁻¹))⁻¹ := by
      rw [hym]; group
    rw [e, hcen]
    exact mul_mem (mul_mem hνm hτν) (inv_mem hsw)
  have hyT : y * v₀ * y⁻¹ * v₀⁻¹ ∈ szT₁ L T := by
    have := mul_mem hy ((mem_normalizer_iff.mp (hTN₁ hv₀T) _).mp (inv_mem hy))
    simpa [mul_assoc] using this
  rw [← hR.inf]
  exact mem_inf.mpr ⟨hyT, hyR⟩

theorem mem_iff_forall_comm_of_card_sylow (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {v₀ : G} (hv₀T : v₀ ∈ T) (hv₀2 : v₀ ^ 2 = 1)
    (hv₀S : v₀ ∉ szT₁ L T ⊔ zpowers t) {x : G} :
    x ∈ R₂ ↔ x ∈ U₁ ⊔ T ∧
      ∀ a ∈ U₁ ⊔ T, ∀ b ∈ U₁ ⊔ T, x * (a * b * a⁻¹ * b⁻¹) = (a * b * a⁻¹ * b⁻¹) * x := by
  have hcomm : ∀ a ∈ U₁ ⊔ T, ∀ b ∈ U₁ ⊔ T, a * b * a⁻¹ * b⁻¹ ∈ U₁ := fun a ha b hb => by
    have := hU.commutator_le h hS2 hR (commutator_mem_commutator ha hb)
    rwa [commutatorElement_def] at this
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  constructor
  · intro hx
    refine ⟨mem_sup_left (hU.le (mem_sup_right hx)), fun a ha b hb => ?_⟩
    exact (mem_centralizer_iff.mp (hU.le_centralizer (hcomm a ha b hb)) x hx)
  · rintro ⟨hx, hxc⟩
    have hxR : ∀ r ∈ R₂, x * r = r * x := by
      have hle : ⁅U₁, U₁⁆ ≤ centralizer ({x} : Set G) := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [mem_centralizer_singleton_iff, commutatorElement_def]
        exact (hxc a (mem_sup_left ha) b (mem_sup_left hb)).symm
      intro r hr
      rw [← hU.commutator_eq] at hr
      exact (mem_centralizer_singleton_iff.mp (hle hr)).symm
    have hxT : ∀ y ∈ szT₁ L T, x * y = y * x := by
      intro y hy
      obtain ⟨z, hz, hzy⟩ := hU.exists_inv_comm_mul_mem hR (mem_sup_left (T := R₂) hy)
      have e : y = (z * t * z⁻¹ * t⁻¹) * ((z * t * z⁻¹ * t⁻¹)⁻¹ * y) := by group
      have h1 := hxc z (mem_sup_left hz) t (mem_sup_right htT)
      have h2 := hxR _ hzy
      rw [e]
      calc x * ((z * t * z⁻¹ * t⁻¹) * ((z * t * z⁻¹ * t⁻¹)⁻¹ * y)) =
          (x * (z * t * z⁻¹ * t⁻¹)) * ((z * t * z⁻¹ * t⁻¹)⁻¹ * y) := by group
        _ = ((z * t * z⁻¹ * t⁻¹) * x) * ((z * t * z⁻¹ * t⁻¹)⁻¹ * y) := by rw [h1]
        _ = (z * t * z⁻¹ * t⁻¹) * (x * ((z * t * z⁻¹ * t⁻¹)⁻¹ * y)) := by group
        _ = (z * t * z⁻¹ * t⁻¹) * (((z * t * z⁻¹ * t⁻¹)⁻¹ * y) * x) := by rw [h2]
        _ = _ := by group
    obtain ⟨u, hu, rfl | rfl⟩ := hU.exists_eq_of_comm_mem_of_card_sylow h hS2 hR hv₀T hv₀2 hv₀S
      hx (fun y hy => by rw [hxT y hy, mul_inv_cancel_right, mul_inv_cancel]; exact one_mem _)
    · exact hU.mem_of_forall_comm hR hu hxT
    · exfalso
      have huT : ∀ y ∈ szT₁ L T, u * y = y * u := by
        intro y hy
        have h1 := hxT y hy
        have h2 : t * y = y * t := (hR.t_comm y hy).symm
        calc u * y = (u * t) * y * t⁻¹ := by rw [mul_assoc u t y, h2]; group
          _ = y * (u * t) * t⁻¹ := by rw [h1]
          _ = y * u := by group
      have huR := hU.mem_of_forall_comm hR hu huT
      apply h.t_not_mem_centralizer_of_card_sylow hS2 hR
      refine mem_centralizer_iff.mpr fun r hr => ?_
      have h2 : u * r = r * u := hR.comm u huR r hr
      have h3 : u * (t * r) = u * (r * t) := by
        calc u * (t * r) = (u * t) * r := by group
          _ = r * (u * t) := hxR r hr
          _ = (r * u) * t := by group
          _ = (u * r) * t := by rw [h2]
          _ = u * (r * t) := by group
      exact (mul_left_cancel h3).symm

theorem mem_iff_forall_comm_mem_of_card_sylow (hU : U3U1Data G L f t T R₂ U₁)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {v₀ : G} (hv₀T : v₀ ∈ T) (hv₀2 : v₀ ^ 2 = 1)
    (hv₀S : v₀ ∉ szT₁ L T ⊔ zpowers t) {x : G} :
    x ∈ U₁ ↔ x ∈ U₁ ⊔ T ∧ ∀ a ∈ U₁ ⊔ T, ∀ b ∈ U₁ ⊔ T,
      x * (a * b * a⁻¹ * b⁻¹) * x⁻¹ * (a * b * a⁻¹ * b⁻¹)⁻¹ ∈ R₂ := by
  have hcomm : ∀ a ∈ U₁ ⊔ T, ∀ b ∈ U₁ ⊔ T, a * b * a⁻¹ * b⁻¹ ∈ U₁ := fun a ha b hb => by
    have := hU.commutator_le h hS2 hR (commutator_mem_commutator ha hb)
    rwa [commutatorElement_def] at this
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, -, -, hNR, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hTA : T ≤ normalizer (szA L T t : Set G) :=
    Subgroup.le_normalizer.trans (h.normalizer_le_normalizer_szA_of_card_sylow hS2)
  have hÛR : U₁ ⊔ T ≤ normalizer (R₂ : Set G) :=
    sup_le (hU.le_centralizer.trans (centralizer_le_normalizer _)) (fun s hs => hNR (hTA hs))
  have htt : t * t = 1 := by rw [← sq, hR.t_sq]
  constructor
  · intro hx
    exact ⟨mem_sup_left hx, fun a ha b hb => hU.comm_mem x hx _ (hcomm a ha b hb)⟩
  · rintro ⟨hx, hxc⟩
    have hxT : ∀ y ∈ szT₁ L T, x * y * x⁻¹ * y⁻¹ ∈ R₂ := by
      intro y hy
      obtain ⟨z, hz, hzy⟩ := hU.exists_inv_comm_mul_mem hR (mem_sup_left (T := R₂) hy)
      have hτz : z * t * z⁻¹ * t⁻¹ ∈ U₁ := hcomm z (mem_sup_left hz) t (mem_sup_right htT)
      have h1 := hxc z (mem_sup_left hz) t (mem_sup_right htT)
      have hxm : x * ((z * t * z⁻¹ * t⁻¹)⁻¹ * y) * x⁻¹ * ((z * t * z⁻¹ * t⁻¹)⁻¹ * y)⁻¹ ∈ R₂ :=
        mul_mem ((mem_normalizer_iff.mp (hÛR hx) _).mp hzy) (inv_mem hzy)
      have hcen : (z * t * z⁻¹ * t⁻¹) *
          (x * ((z * t * z⁻¹ * t⁻¹)⁻¹ * y) * x⁻¹ * ((z * t * z⁻¹ * t⁻¹)⁻¹ * y)⁻¹) *
          (z * t * z⁻¹ * t⁻¹)⁻¹ =
          x * ((z * t * z⁻¹ * t⁻¹)⁻¹ * y) * x⁻¹ * ((z * t * z⁻¹ * t⁻¹)⁻¹ * y)⁻¹ := by
        rw [← mem_centralizer_iff.mp (hU.le_centralizer hτz) _ hxm, mul_inv_cancel_right]
      have e : x * y * x⁻¹ * y⁻¹ =
          (x * (z * t * z⁻¹ * t⁻¹) * x⁻¹ * (z * t * z⁻¹ * t⁻¹)⁻¹) *
          ((z * t * z⁻¹ * t⁻¹) *
            (x * ((z * t * z⁻¹ * t⁻¹)⁻¹ * y) * x⁻¹ * ((z * t * z⁻¹ * t⁻¹)⁻¹ * y)⁻¹) *
            (z * t * z⁻¹ * t⁻¹)⁻¹) := by group
      rw [e, hcen]
      exact mul_mem h1 hxm
    obtain ⟨u, hu, rfl | rfl⟩ :=
      hU.exists_eq_of_comm_mem_of_card_sylow h hS2 hR hv₀T hv₀2 hv₀S hx hxT
    · exact hu
    · exfalso
      obtain ⟨z₀, hz₀, hz₀v⟩ := hU.exists_comm_not_mem_sup_of_card_sylow h hS2 hR hv₀T hv₀2 hv₀S
      have hv₀U : v₀ ∈ U₁ ⊔ T := mem_sup_right hv₀T
      have hc := hcomm z₀ (mem_sup_left hz₀) v₀ hv₀U
      have h1 := hxc z₀ (mem_sup_left hz₀) v₀ hv₀U
      have htc : t * (z₀ * v₀ * z₀⁻¹ * v₀⁻¹) * t⁻¹ ∈ U₁ := by
        have htN : t ∈ normalizer (U₁ : Set G) :=
          hU.normalizer_le (Subgroup.le_normalizer (mem_szR_right _ _ _))
        exact (mem_normalizer_iff.mp htN _).mp hc
      have h2 := hU.comm_mem u hu _ htc
      apply hz₀v
      refine hU.mem_sup_of_comm_mem hR htt hc ?_
      have e : (z₀ * v₀ * z₀⁻¹ * v₀⁻¹) * t * (z₀ * v₀ * z₀⁻¹ * v₀⁻¹)⁻¹ * t⁻¹ =
          ((u * (t * (z₀ * v₀ * z₀⁻¹ * v₀⁻¹) * t⁻¹) * u⁻¹ *
            (t * (z₀ * v₀ * z₀⁻¹ * v₀⁻¹) * t⁻¹)⁻¹)⁻¹ *
          ((u * t) * (z₀ * v₀ * z₀⁻¹ * v₀⁻¹) * (u * t)⁻¹ * (z₀ * v₀ * z₀⁻¹ * v₀⁻¹)⁻¹))⁻¹ := by
        group
      rw [e]
      exact inv_mem (mul_mem (inv_mem h2) h1)

theorem normalizer_sup_le_of_card_sylow (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {v₀ : G} (hv₀T : v₀ ∈ T) (hv₀2 : v₀ ^ 2 = 1)
    (hv₀S : v₀ ∉ szT₁ L T ⊔ zpowers t) :
    normalizer ((U₁ ⊔ T : Subgroup G) : Set G) ≤
      normalizer (R₂ : Set G) ⊓ normalizer (U₁ : Set G) := by
  have hR₂ := fun {x : G} => hU.mem_iff_forall_comm_of_card_sylow h hS2 hR hv₀T hv₀2 hv₀S (x := x)
  have hU₁ := fun {x : G} =>
    hU.mem_iff_forall_comm_mem_of_card_sylow h hS2 hR hv₀T hv₀2 hv₀S (x := x)
  have hconj : ∀ g ∈ normalizer ((U₁ ⊔ T : Subgroup G) : Set G), ∀ a ∈ U₁ ⊔ T,
      g⁻¹ * a * g ∈ U₁ ⊔ T := fun g hg a ha => (mem_normalizer_iff''.mp hg a).mp ha
  have key₁ : ∀ g ∈ normalizer ((U₁ ⊔ T : Subgroup G) : Set G), ∀ x ∈ R₂, g * x * g⁻¹ ∈ R₂ := by
    intro g hg x hx
    obtain ⟨hxS, hxc⟩ := hR₂.mp hx
    refine hR₂.mpr ⟨(mem_normalizer_iff.mp hg x).mp hxS, fun a ha b hb => ?_⟩
    have h1 := hxc _ (hconj g hg a ha) _ (hconj g hg b hb)
    calc g * x * g⁻¹ * (a * b * a⁻¹ * b⁻¹) =
        g * (x * ((g⁻¹ * a * g) * (g⁻¹ * b * g) * (g⁻¹ * a * g)⁻¹ * (g⁻¹ * b * g)⁻¹)) * g⁻¹ := by
          group
      _ = g * (((g⁻¹ * a * g) * (g⁻¹ * b * g) * (g⁻¹ * a * g)⁻¹ * (g⁻¹ * b * g)⁻¹) * x) * g⁻¹ := by
          rw [h1]
      _ = (a * b * a⁻¹ * b⁻¹) * (g * x * g⁻¹) := by group
  have key₂ : ∀ g ∈ normalizer ((U₁ ⊔ T : Subgroup G) : Set G), ∀ x ∈ U₁, g * x * g⁻¹ ∈ U₁ := by
    intro g hg x hx
    obtain ⟨hxS, hxc⟩ := hU₁.mp hx
    refine hU₁.mpr ⟨(mem_normalizer_iff.mp hg x).mp hxS, fun a ha b hb => ?_⟩
    have h1 := key₁ g hg _ (hxc _ (hconj g hg a ha) _ (hconj g hg b hb))
    have e : g * x * g⁻¹ * (a * b * a⁻¹ * b⁻¹) * (g * x * g⁻¹)⁻¹ * (a * b * a⁻¹ * b⁻¹)⁻¹ =
        g * (x * ((g⁻¹ * a * g) * (g⁻¹ * b * g) * (g⁻¹ * a * g)⁻¹ * (g⁻¹ * b * g)⁻¹) * x⁻¹ *
          ((g⁻¹ * a * g) * (g⁻¹ * b * g) * (g⁻¹ * a * g)⁻¹ * (g⁻¹ * b * g)⁻¹)⁻¹) * g⁻¹ := by
      group
    rw [e]
    exact h1
  intro g hg
  refine mem_inf.mpr ⟨mem_normalizer_iff.mpr fun x => ⟨key₁ g hg x, fun hx => ?_⟩,
    mem_normalizer_iff.mpr fun x => ⟨key₂ g hg x, fun hx => ?_⟩⟩
  · have := key₁ g⁻¹ (inv_mem hg) _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
  · have := key₂ g⁻¹ (inv_mem hg) _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

end Certificates

end U3U1Data

end CFSG.SeitzReduction.RankOne
