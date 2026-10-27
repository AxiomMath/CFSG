module

public import CFSG.GH74.Uniqueness.Bender.Aut
public import CFSG.GH74.Uniqueness.SU.SU8Setup

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.Bender CFSG.GH74.Uniqueness.SU.SU8.Setup
open scoped commutatorElement Pointwise

namespace LocA

theorem exists_ne_one_of_ne_bot {G : Type*} [Group G] {H : Subgroup G} (h : H ≠ ⊥) :
    ∃ w ∈ H, w ≠ 1 := by
  by_contra hcon
  exact h ((Subgroup.eq_bot_iff_forall _).2 fun w hw => by_contra fun h' => hcon ⟨w, hw, h'⟩)

theorem conj_mul_of_mem_centralizer {Hh : Type*} [Group Hh] {K : Subgroup Hh} {x a c : Hh}
    (hx : x ∈ K) (hc : c ∈ centralizer (K : Set Hh)) :
    x * (a * c) * x⁻¹ = (x * a * x⁻¹) * c := by
  have h1 : x * c = c * x := Subgroup.mem_centralizer_iff.mp hc x hx
  calc x * (a * c) * x⁻¹ = x * a * (c * x⁻¹) := by group
    _ = x * a * (x⁻¹ * c) := by
        congr 1
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← h1]; group
    _ = (x * a * x⁻¹) * c := by group

variable {Hh : Type*} [Group Hh] [Finite Hh]

structure LocHyp (K Ah : Subgroup Hh) (n i e : ℕ) : Prop where
  two_le : 2 ≤ n
  center_bot : center ↥K = ⊥
  core : ∀ Q : Sylow 2 ↥K, ∃ t, BenderCore (2 ^ n) i e (Q : Subgroup ↥K) t
  exp : ∀ a ∈ Ah, a * a = 1
  comm : ∀ a ∈ Ah, ∀ b ∈ Ah, a * b = b * a
  omega : ∃ P : Sylow 2 ↥K, ∀ g : ↥K, g ∈ (P : Subgroup ↥K) → g * g = 1 → (g : Hh) ∈ Ah
  split : ∀ a ∈ Ah, ∃ k ∈ K, ∃ c ∈ centralizer (K : Set Hh), a = k * c

structure LocOut (K Ah Y : Subgroup Hh) (n : ℕ) : Prop where
  le : Y ≤ K
  norm : Y ≤ normalizer (Ah : Set Hh)
  cyclic : IsCyclic ↥Y
  odd : Odd (Nat.card ↥Y)
  card_Z : Nat.card ↥(Ah ⊓ K) = 2 ^ n
  card_Y : Nat.card ↥Y + 1 = 2 ^ n
  trans : ∀ u ∈ Ah ⊓ K, u ≠ 1 → ∀ v ∈ Ah ⊓ K, v ≠ 1 → ∃ y ∈ Y, y * u * y⁻¹ = v
  free : ∀ y ∈ Y, y ≠ 1 → ∀ u ∈ Ah ⊓ K, u ≠ 1 → y * u * y⁻¹ ≠ u
  action : ∀ m ∈ K, m ∈ normalizer (Ah : Set Hh) →
    ∃ y ∈ Y, ∀ a ∈ Ah, m * a * m⁻¹ = y * a * y⁻¹
  split : ∀ a ∈ Ah, ∃ u ∈ Ah ⊓ K, ∃ c ∈ Ah ⊓ centralizer (K : Set Hh), a = u * c

section

variable {K Ah : Subgroup Hh} {n i e : ℕ}

omit [Finite Hh] in
theorem LocHyp.eq_one_of_mem_centralizer (h : LocHyp K Ah n i e) {x : Hh} (hx : x ∈ K)
    (hxc : x ∈ centralizer (K : Set Hh)) : x = 1 := by
  have : (⟨x, hx⟩ : ↥K) ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := Subgroup.mem_centralizer_iff.mp hxc (y : Hh) y.2
    exact Subtype.ext this
  rw [h.center_bot, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

omit [Finite Hh] in
theorem LocHyp.two_pow_ge (h : LocHyp K Ah n i e) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le

omit [Finite Hh] in
theorem LocHyp.rootCenter_ne_bot (h : LocHyp K Ah n i e) {P : Sylow 2 ↥K} {t : ↥K}
    (hc : BenderCore (2 ^ n) i e (P : Subgroup ↥K) t) : rootCenter (P : Subgroup ↥K) ≠ ⊥ := by
  intro hbot
  have h1 := hc.card_center
  rw [hbot, Subgroup.card_bot] at h1
  have := h.two_pow_ge
  omega

structure LocChoice (h : LocHyp K Ah n i e) where
  P : Sylow 2 ↥K
  hP : ∀ g : ↥K, g ∈ (P : Subgroup ↥K) → g * g = 1 → (g : Hh) ∈ Ah
  t : ↥K
  hc : BenderCore (2 ^ n) i e (P : Subgroup ↥K) t

omit [Finite Hh] in
theorem LocHyp.exists_choice (h : LocHyp K Ah n i e) : Nonempty (LocChoice h) := by
  obtain ⟨P, hP⟩ := h.omega
  obtain ⟨t, hc⟩ := h.core P
  exact ⟨⟨P, hP, t, hc⟩⟩

variable {h : LocHyp K Ah n i e}

omit [Finite Hh] in
theorem LocChoice.mem_Ah (ch : LocChoice h) {u : ↥K}
    (hu : u ∈ rootCenter (ch.P : Subgroup ↥K)) : (u : Hh) ∈ Ah :=
  ch.hP u (rootCenter_le _ hu) (ch.hc.center_sq u hu)

theorem LocChoice.inf_eq (ch : LocChoice h) :
    (Ah ⊓ K).subgroupOf K = rootCenter (ch.P : Subgroup ↥K) := by
  have hZE : rootCenter (ch.P : Subgroup ↥K) ≤ (Ah ⊓ K).subgroupOf K := fun u hu =>
    Subgroup.mem_subgroupOf.mpr ⟨ch.mem_Ah hu, u.2⟩
  apply le_antisymm _ hZE
  have hE2 : IsPGroup 2 ((Ah ⊓ K).subgroupOf K) := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have := h.exp (x : Hh) (Subgroup.mem_subgroupOf.mp x.2).1
    simpa [sq] using this
  obtain ⟨Q, hQ⟩ := hE2.exists_le_sylow
  obtain ⟨tQ, hcQ⟩ := h.core Q
  have hEQ : (Ah ⊓ K).subgroupOf K ≤ rootCenter (Q : Subgroup ↥K) := by
    refine hcQ.elemAbelian_le_rootCenter hQ (fun x hx => ?_)
    have := h.exp (x : Hh) (Subgroup.mem_subgroupOf.mp hx).1
    exact Subtype.ext this
  have hPQ : Q = ch.P := ch.hc.sylow_eq_of_ne_bot (Q₁ := Q) (h.rootCenter_ne_bot ch.hc)
    (rootCenter_le _) (hZE.trans hQ)
  rw [hPQ] at hEQ
  exact hEQ

theorem LocChoice.mem_rootCenter_of_mem (ch : LocChoice h) {x : ↥K} (hx : (x : Hh) ∈ Ah) :
    x ∈ rootCenter (ch.P : Subgroup ↥K) := by
  rw [← ch.inf_eq]
  exact Subgroup.mem_subgroupOf.mpr ⟨hx, x.2⟩

theorem LocChoice.decomp (ch : LocChoice h) {a : Hh} (ha : a ∈ Ah) :
    ∃ u : ↥K, u ∈ rootCenter (ch.P : Subgroup ↥K) ∧
      ∃ c ∈ Ah ⊓ centralizer (K : Set Hh), a = (u : Hh) * c := by
  obtain ⟨k, hk, c, hc', rfl⟩ := h.split a ha
  have hkc : ∀ x ∈ K, x * c = c * x := fun x hx => Subgroup.mem_centralizer_iff.mp hc' x hx
  have hkk : k * k = 1 := by
    have h1 := h.exp (k * c) ha
    have h2 : (k * k) * (c * c) = 1 := by
      calc (k * k) * (c * c) = k * (k * c) * c := by group
        _ = k * (c * k) * c := by rw [hkc k hk]
        _ = (k * c) * (k * c) := by group
        _ = 1 := h1
    have h3 : k * k = (c * c)⁻¹ := eq_inv_of_mul_eq_one_left h2
    apply h.eq_one_of_mem_centralizer (K.mul_mem hk hk)
    rw [h3]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hc' hc')
  have hkK : (⟨k, hk⟩ : ↥K) * ⟨k, hk⟩ = 1 := Subtype.ext hkk
  have hcomm_u : ∀ u ∈ rootCenter (ch.P : Subgroup ↥K), k * (u : Hh) = (u : Hh) * k := by
    intro u hu
    have h1 := h.comm (k * c) ha (u : Hh) (ch.mem_Ah hu)
    have h2 : (u : Hh) * c = c * u := hkc u u.2
    have h3 : (k * (u : Hh)) * c = ((u : Hh) * k) * c := by
      calc (k * (u : Hh)) * c = k * ((u : Hh) * c) := by group
        _ = k * (c * u) := by rw [h2]
        _ = (k * c) * u := by group
        _ = u * (k * c) := h1
        _ = ((u : Hh) * k) * c := by group
    exact mul_right_cancel h3
  have hkr : (⟨k, hk⟩ : ↥K) ∈ rootCenter (ch.P : Subgroup ↥K) := by
    by_cases hk1 : (⟨k, hk⟩ : ↥K) = 1
    · rw [hk1]; exact (rootCenter _).one_mem
    · obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_ne_bot (h.rootCenter_ne_bot ch.hc)
      have hu2 : orderOf u = 2 := (ch.hc.involution_iff.mpr ⟨hu, hu1⟩).2
      have huB : u ∈ borel (ch.P : Subgroup ↥K) := le_borel _ (rootCenter_le _ hu)
      have hconj : (⟨k, hk⟩ : ↥K)⁻¹ * u * ⟨k, hk⟩ = u := by
        have h1 : (⟨k, hk⟩ : ↥K) * u = u * ⟨k, hk⟩ := Subtype.ext (hcomm_u u hu)
        have h2 : (⟨k, hk⟩ : ↥K)⁻¹ = ⟨k, hk⟩ := inv_eq_of_mul_eq_one_right hkK
        rw [h2, h1]
        calc u * ⟨k, hk⟩ * ⟨k, hk⟩ = u * (⟨k, hk⟩ * ⟨k, hk⟩) := by group
          _ = u := by rw [hkK, mul_one]
      have hkB := ch.hc.mem_borel_of_conj huB hu2 (by rw [hconj]; exact huB)
      have hord : orderOf (⟨k, hk⟩ : ↥K) = 2 := by
        apply orderOf_eq_prime _ hk1
        rw [sq]; exact hkK
      exact (ch.hc.involution_iff.mp ⟨hkB, hord⟩).1
  refine ⟨⟨k, hk⟩, hkr, (k : Hh)⁻¹ * (k * c), ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact Ah.mul_mem (Ah.inv_mem (ch.mem_Ah hkr)) ha
    · simpa using hc'
  · simp

def LocChoice.Y (ch : LocChoice h) : Subgroup Hh :=
  (⁅cartan (ch.P : Subgroup ↥K) ch.t, Subgroup.zpowers ch.t⁆).map K.subtype

omit [Finite Hh] in
theorem LocChoice.Y_le (ch : LocChoice h) : ch.Y ≤ K := Subgroup.map_subtype_le _

omit [Finite Hh] in
theorem LocChoice.mem_Y_iff (ch : LocChoice h) {y : Hh} :
    y ∈ ch.Y ↔ ∃ d : ↥K, d ∈ ⁅cartan (ch.P : Subgroup ↥K) ch.t, Subgroup.zpowers ch.t⁆ ∧
      (d : Hh) = y := by
  unfold LocChoice.Y
  simp [Subgroup.mem_map]

theorem LocChoice.Y_cyclic (ch : LocChoice h) : IsCyclic ↥ch.Y := by
  have : IsCyclic ↥⁅cartan (ch.P : Subgroup ↥K) ch.t, Subgroup.zpowers ch.t⁆ :=
    ch.hc.isCyclic_commutator
  exact isCyclic_of_surjective
    (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).toMonoidHom
    (MulEquiv.surjective _)

theorem LocChoice.Y_card (ch : LocChoice h) : Nat.card ↥ch.Y = 2 ^ n - 1 := by
  unfold LocChoice.Y
  rw [Subgroup.card_map_of_injective K.subtype_injective]
  exact ch.hc.card_commutator_cartan

theorem LocChoice.Y_odd (ch : LocChoice h) : Odd (Nat.card ↥ch.Y) := by
  rw [ch.Y_card]
  have h4 := h.two_pow_ge
  obtain ⟨m, hm⟩ : Even (2 ^ n) := (Nat.even_pow.mpr ⟨even_two, by have := h.two_le; omega⟩)
  exact ⟨m - 1, by omega⟩

theorem LocChoice.card_Z (ch : LocChoice h) : Nat.card ↥(Ah ⊓ K) = 2 ^ n := by
  have h1 : Nat.card ↥(Ah ⊓ K) = Nat.card ↥((Ah ⊓ K).subgroupOf K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Ah ⊓ K ≤ K)).toEquiv.symm
  rw [h1, ch.inf_eq]
  exact ch.hc.card_center

theorem LocChoice.Y_card_add_one (ch : LocChoice h) :
    Nat.card ↥ch.Y + 1 = Nat.card ↥(Ah ⊓ K) := by
  rw [ch.card_Z, ch.Y_card]
  have := h.two_pow_ge
  omega

theorem LocChoice.Y_conj_mem (ch : LocChoice h) {y : Hh} (hy : y ∈ ch.Y) {a : Hh} (ha : a ∈ Ah) :
    y * a * y⁻¹ ∈ Ah := by
  obtain ⟨d, hd, rfl⟩ := ch.mem_Y_iff.mp hy
  obtain ⟨u, hu, c, hcA, rfl⟩ := ch.decomp ha
  have hdB : d ∈ borel (ch.P : Subgroup ↥K) :=
    cartan_le_borel _ _ (ch.hc.commutator_cartan_le hd)
  have h1 : d * u * d⁻¹ ∈ rootCenter (ch.P : Subgroup ↥K) := conj_mem_rootCenter hdB hu
  have hdc : (d : Hh) * c = c * d := Subgroup.mem_centralizer_iff.mp hcA.2 d d.2
  have hdc' : c * (d : Hh)⁻¹ = (d : Hh)⁻¹ * c := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hdc]; group
  have : (d : Hh) * ((u : Hh) * c) * (d : Hh)⁻¹ = ((d * u * d⁻¹ : ↥K) : Hh) * c := by
    calc (d : Hh) * ((u : Hh) * c) * (d : Hh)⁻¹ = (d : Hh) * u * (c * (d : Hh)⁻¹) := by group
      _ = (d : Hh) * u * ((d : Hh)⁻¹ * c) := by rw [hdc']
      _ = ((d * u * d⁻¹ : ↥K) : Hh) * c := by simp [mul_assoc]
  rw [this]
  exact Ah.mul_mem (ch.mem_Ah h1) hcA.1

theorem LocChoice.Y_le_normalizer (ch : LocChoice h) : ch.Y ≤ normalizer (Ah : Set Hh) := by
  intro y hy
  exact mem_normalizer_of_conj_le (fun a ha => ch.Y_conj_mem hy ha)

theorem LocChoice.Y_trans (ch : LocChoice h) {u v : Hh} (hu : u ∈ Ah ⊓ K) (hu1 : u ≠ 1)
    (hv : v ∈ Ah ⊓ K) (hv1 : v ≠ 1) : ∃ y ∈ ch.Y, y * u * y⁻¹ = v := by
  obtain ⟨hu_A, hu_K⟩ := Subgroup.mem_inf.mp hu
  obtain ⟨hv_A, hv_K⟩ := Subgroup.mem_inf.mp hv
  have huR := ch.mem_rootCenter_of_mem (x := ⟨u, hu_K⟩) hu_A
  have hvR := ch.mem_rootCenter_of_mem (x := ⟨v, hv_K⟩) hv_A
  have huK1 : (⟨u, hu_K⟩ : ↥K) ≠ 1 := fun h' => hu1 (congrArg Subtype.val h')
  have hvK1 : (⟨v, hv_K⟩ : ↥K) ≠ 1 := fun h' => hv1 (congrArg Subtype.val h')
  obtain ⟨d, ⟨hd, hvd⟩, -⟩ := ch.hc.existsUnique_commutator_conj huR huK1 hvR hvK1
  refine ⟨((d⁻¹ : ↥K) : Hh), ch.mem_Y_iff.mpr ⟨d⁻¹, Subgroup.inv_mem _ hd, rfl⟩, ?_⟩
  have := congrArg Subtype.val hvd
  simpa using this.symm

theorem LocChoice.Y_free (ch : LocChoice h) {y : Hh} (hy : y ∈ ch.Y) (hy1 : y ≠ 1) {u : Hh}
    (hu : u ∈ Ah ⊓ K) (hu1 : u ≠ 1) : y * u * y⁻¹ ≠ u := by
  intro hfix
  obtain ⟨d, hd, rfl⟩ := ch.mem_Y_iff.mp hy
  obtain ⟨hu_A, hu_K⟩ := Subgroup.mem_inf.mp hu
  have huR := ch.mem_rootCenter_of_mem (x := ⟨u, hu_K⟩) hu_A
  have huK1 : (⟨u, hu_K⟩ : ↥K) ≠ 1 := fun h' => hu1 (congrArg Subtype.val h')
  obtain ⟨x, -, hx⟩ := ch.hc.existsUnique_commutator_conj huR huK1 huR huK1
  have h1 : (1 : ↥K) ∈ ⁅cartan (ch.P : Subgroup ↥K) ch.t, Subgroup.zpowers ch.t⁆ ∧
      (⟨u, hu_K⟩ : ↥K) = 1⁻¹ * ⟨u, hu_K⟩ * 1 := ⟨Subgroup.one_mem _, by simp⟩
  have h2 : d ∈ ⁅cartan (ch.P : Subgroup ↥K) ch.t, Subgroup.zpowers ch.t⁆ ∧
      (⟨u, hu_K⟩ : ↥K) = d⁻¹ * ⟨u, hu_K⟩ * d := by
    refine ⟨hd, Subtype.ext ?_⟩
    have : (d : Hh) * u * (d : Hh)⁻¹ = u := hfix
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc u = (d : Hh)⁻¹ * ((d : Hh) * u * (d : Hh)⁻¹) * d := by group
      _ = (d : Hh)⁻¹ * u * d := by rw [this]
  have h3 := (hx 1 h1).trans (hx d h2).symm
  exact hy1 (by have := congrArg Subtype.val h3; simpa using this.symm)

theorem LocChoice.exists_Y_action (ch : LocChoice h) {m : Hh} (hm : m ∈ K)
    (hmN : m ∈ normalizer (Ah : Set Hh)) :
    ∃ y ∈ ch.Y, ∀ a ∈ Ah, m * a * m⁻¹ = y * a * y⁻¹ := by
  set mK : ↥K := ⟨m, hm⟩ with hmK
  have hnorm : ∀ v ∈ rootCenter (ch.P : Subgroup ↥K),
      mK * v * mK⁻¹ ∈ borel (ch.P : Subgroup ↥K) := by
    intro v hv
    have hvA := ch.mem_Ah hv
    have h1 : m * (v : Hh) * m⁻¹ ∈ Ah := (Subgroup.mem_normalizer_iff.mp hmN _).mp hvA
    have hmem : mK * v * mK⁻¹ ∈ rootCenter (ch.P : Subgroup ↥K) :=
      ch.mem_rootCenter_of_mem (x := mK * v * mK⁻¹) (by simpa [hmK] using h1)
    exact le_borel _ (rootCenter_le _ hmem)
  have hV2 : IsPGroup 2 (rootCenter (ch.P : Subgroup ↥K)) := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa [sq] using ch.hc.center_sq x x.2
  have hmB : mK ∈ borel (ch.P : Subgroup ↥K) :=
    IsStronglyEmbedded.mem_of_conj_mem ch.hc.strong (V := rootCenter (ch.P : Subgroup ↥K))
      (fun v hv => le_borel _ (rootCenter_le _ hv)) hnorm hV2 (h.rootCenter_ne_bot ch.hc)
  have hsup : mK ∈ (ch.P : Subgroup ↥K) ⊔ cartan (ch.P : Subgroup ↥K) ch.t := by
    rw [ch.hc.sup_eq]; exact hmB
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (ch.P : Subgroup ↥K)
    (cartan (ch.P : Subgroup ↥K) ch.t) (cartan_le_borel _ _)
  have hmem : mK ∈ ((ch.P : Subgroup ↥K) : Set ↥K) *
      (cartan (ch.P : Subgroup ↥K) ch.t : Set ↥K) := by
    rw [← hmul]; exact hsup
  obtain ⟨p, hp, d, hd, hpd⟩ := Set.mem_mul.mp hmem
  have hdsup : d ∈ ⁅cartan (ch.P : Subgroup ↥K) ch.t, Subgroup.zpowers ch.t⁆ ⊔
      fixCartan (ch.P : Subgroup ↥K) ch.t := ch.hc.cartan_eq_sup ▸ hd
  obtain ⟨y0, hy0, f, hf, rfl⟩ :=
    exists_mul_of_mem_sup_of_commute ch.hc.comm_commutator_fixCartan hdsup
  refine ⟨(y0 : Hh), ch.mem_Y_iff.mpr ⟨y0, hy0, rfl⟩, fun a ha => ?_⟩
  obtain ⟨u, hu, c, hcA, rfl⟩ := ch.decomp ha
  have hcK := hcA.2
  have hy0B : y0 ∈ borel (ch.P : Subgroup ↥K) :=
    cartan_le_borel _ _ (ch.hc.commutator_cartan_le hy0)
  have hw : y0 * u * y0⁻¹ ∈ rootCenter (ch.P : Subgroup ↥K) := conj_mem_rootCenter hy0B hu
  have hfc : f ∈ centralizer (rootCenter (ch.P : Subgroup ↥K) : Set ↥K) := by
    rw [ch.hc.centralizer_rootCenter_eq]
    exact Subgroup.mem_sup_right hf
  have hfu : f * u * f⁻¹ = u := by
    have := Subgroup.mem_centralizer_iff.mp hfc u hu
    rw [mul_inv_eq_iff_eq_mul]; exact this.symm
  have hact : mK * u * mK⁻¹ = y0 * u * y0⁻¹ := by
    have h1 : mK = p * (y0 * f) := hpd.symm
    rw [h1]
    calc p * (y0 * f) * u * (p * (y0 * f))⁻¹ = p * (y0 * (f * u * f⁻¹) * y0⁻¹) * p⁻¹ := by group
      _ = p * (y0 * u * y0⁻¹) * p⁻¹ := by rw [hfu]
      _ = y0 * u * y0⁻¹ := by
        have h2 := (mem_rootCenter_iff.mp hw).2 p hp
        rw [h2]; group
  have e1 := conj_mul_of_mem_centralizer (a := (u : Hh)) hm hcK
  have e2 := conj_mul_of_mem_centralizer (a := (u : Hh)) (y0 : ↥K).2 hcK
  have e3 : m * (u : Hh) * m⁻¹ = ((mK * u * mK⁻¹ : ↥K) : Hh) := by simp [hmK]
  have e4 : (y0 : Hh) * (u : Hh) * (y0 : Hh)⁻¹ = ((y0 * u * y0⁻¹ : ↥K) : Hh) := by simp
  rw [e1, e2, e3, e4, hact]

theorem LocHyp.exists_out (h : LocHyp K Ah n i e) : ∃ Y : Subgroup Hh, LocOut K Ah Y n := by
  obtain ⟨ch⟩ := h.exists_choice
  refine ⟨ch.Y, ⟨ch.Y_le, ch.Y_le_normalizer, ch.Y_cyclic, ch.Y_odd, ch.card_Z, ?_,
    fun u hu hu1 v hv hv1 => ch.Y_trans hu hu1 hv hv1,
    fun y hy hy1 u hu hu1 => ch.Y_free hy hy1 hu hu1,
    fun m hm hmN => ch.exists_Y_action hm hmN, ?_⟩⟩
  · rw [← ch.card_Z]; exact ch.Y_card_add_one
  · intro a ha
    obtain ⟨u, hu, c, hc, rfl⟩ := ch.decomp ha
    exact ⟨(u : Hh), ⟨ch.mem_Ah hu, u.2⟩, c, hc, rfl⟩

theorem LocHyp.of_benderType
    (hK : BenderType ↥K n i e) (hexp : ∀ a ∈ Ah, a * a = 1)
    (hcomm : ∀ a ∈ Ah, ∀ b ∈ Ah, a * b = b * a)
    (homega : ∃ P : Sylow 2 ↥K, ∀ g : ↥K, g ∈ (P : Subgroup ↥K) → g * g = 1 → (g : Hh) ∈ Ah)
    (hsplit : ∀ a ∈ Ah, ∃ k ∈ K, ∃ c ∈ centralizer (K : Set Hh), a = k * c) :
    LocHyp K Ah n i e :=
  { two_le := hK.two_le.2
    center_bot := hK.center_eq_bot
    core := fun Q => hK.exists_benderCore Q
    exp := hexp
    comm := hcomm
    omega := homega
    split := hsplit }

end

end LocA

end CFSG.GH74.Uniqueness.SU.SU8
