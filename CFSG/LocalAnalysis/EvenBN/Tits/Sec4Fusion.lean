module

public import CFSG.LocalAnalysis.EvenBN.Tits.Model.Short

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped commutatorElement

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem θ_lift (d : Data G) {a : Equiv.Perm (Fin 1755)} (ha : a ∈ titsD) :
    ((d.θ ⟨d.lift a, d.lift_mem a⟩ : titsD) : Equiv.Perm (Fin 1755)) = a := by
  have e : (⟨d.lift a, d.lift_mem a⟩ : d.L) = d.θ.symm ⟨a, ha⟩ := Subtype.ext (d.lift_eq ha)
  rw [e, MulEquiv.apply_symm_apply]

omit [Finite G] in
theorem lift_mul (d : Data G) {a b : Equiv.Perm (Fin 1755)} (ha : a ∈ titsD) (hb : b ∈ titsD) :
    d.lift (a * b) = d.lift a * d.lift b := by
  have e : (⟨a * b, mul_mem ha hb⟩ : titsD) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
  rw [d.lift_eq ha, d.lift_eq hb, d.lift_eq (mul_mem ha hb), e, map_mul, coe_mul]

omit [Finite G] in
theorem lift_one (d : Data G) : d.lift 1 = 1 := by
  have e : (⟨1, one_mem _⟩ : titsD) = 1 := rfl
  rw [d.lift_eq (one_mem _), e, map_one, OneMemClass.coe_one]

omit [Finite G] in
theorem lift_inj (d : Data G) {a b : Equiv.Perm (Fin 1755)} (ha : a ∈ titsD) (hb : b ∈ titsD)
    (h : d.lift a = d.lift b) : a = b := by
  have e : (⟨d.lift a, d.lift_mem a⟩ : d.L) = ⟨d.lift b, d.lift_mem b⟩ := Subtype.ext h
  calc a = ((d.θ ⟨d.lift a, d.lift_mem a⟩ : titsD) : Equiv.Perm (Fin 1755)) :=
        (d.θ_lift ha).symm
    _ = ((d.θ ⟨d.lift b, d.lift_mem b⟩ : titsD) : Equiv.Perm (Fin 1755)) := by rw [e]
    _ = b := d.θ_lift hb

omit [Finite G] in
theorem lift_comm (d : Data G) {a b : Equiv.Perm (Fin 1755)} (ha : a ∈ titsD) (hb : b ∈ titsD)
    (h : a * b = b * a) : d.lift a * d.lift b = d.lift b * d.lift a := by
  rw [← d.lift_mul ha hb, ← d.lift_mul hb ha, h]

omit [Finite G] in
theorem lift_titsZ (d : Data G) : d.lift titsZ = d.z :=
  rfl

omit [Finite G] in
theorem lift_titsTInv (d : Data G) : d.lift titsTInv = d.v :=
  rfl

theorem Hyp.conj_lift_eq (hd : d.Hyp) {x : G} (hx : x ∈ centralizer ({d.t} : Set G))
    {a b : Equiv.Perm (Fin 1755)} (ha : a ∈ titsD) (hb : b ∈ titsD)
    (h : (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) * a = b * d.ρ ⟨x, hx⟩) :
    x * d.lift a * x⁻¹ = d.lift b := by
  have h1 := hd.θ_conj ⟨x, hx⟩ ⟨d.lift a, d.lift_mem a⟩
  rw [d.θ_lift ha] at h1
  have h2 : ((d.θ ⟨x * d.lift a * x⁻¹, hd.conj_mem ⟨x, hx⟩ (d.lift_mem a)⟩ : titsD) :
      Equiv.Perm (Fin 1755)) = ((d.θ ⟨d.lift b, d.lift_mem b⟩ : titsD) :
        Equiv.Perm (Fin 1755)) := by
    rw [h1, d.θ_lift hb, h, mul_inv_cancel_right]
  exact congrArg Subtype.val (d.θ_val_injective h2)

theorem Hyp.commute_lift_iff (hd : d.Hyp) {x : G} (hx : x ∈ centralizer ({d.t} : Set G))
    {a : Equiv.Perm (Fin 1755)} (ha : a ∈ titsD) :
    x * d.lift a = d.lift a * x ↔
      (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) * a = a * d.ρ ⟨x, hx⟩ := by
  constructor
  · intro h
    have h2 : ((d.θ ⟨x * d.lift a * x⁻¹, hd.conj_mem ⟨x, hx⟩ (d.lift_mem a)⟩ : titsD) :
        Equiv.Perm (Fin 1755)) = a := by
      have e : (⟨x * d.lift a * x⁻¹, hd.conj_mem ⟨x, hx⟩ (d.lift_mem a)⟩ : d.L) =
          ⟨d.lift a, d.lift_mem a⟩ :=
        Subtype.ext (show x * d.lift a * x⁻¹ = d.lift a by rw [h, mul_inv_cancel_right])
      rw [e, d.θ_lift ha]
    have h1 := hd.θ_conj ⟨x, hx⟩ ⟨d.lift a, d.lift_mem a⟩
    rw [d.θ_lift ha] at h1
    have h3 : (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) * a *
        (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755))⁻¹ = a := h1.symm.trans h2
    calc (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) * a =
        (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) * a * (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755))⁻¹ *
          d.ρ ⟨x, hx⟩ := by group
      _ = a * d.ρ ⟨x, hx⟩ := by rw [h3]
  · intro h
    have e := hd.conj_lift_eq hx ha ha h
    calc x * d.lift a = x * d.lift a * x⁻¹ * x := by group
      _ = d.lift a * x := by rw [e]

theorem Hyp.ρ_lift
    (hd : d.Hyp) {a : Equiv.Perm (Fin 1755)} (ha : a ∈ titsD) :
    (d.ρ ⟨d.lift a, hd.L_le (d.lift_mem a)⟩ : Equiv.Perm (Fin 1755)) = a := by
  rw [hd.ρ_eq_θ ⟨d.lift a, d.lift_mem a⟩, d.θ_lift ha]

theorem Hyp.eq_lift_or
    (hd : d.Hyp) {x : G} (hx : x ∈ centralizer ({d.t} : Set G))
    (hρ : (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) ∈ titsD) :
    x = d.lift (d.ρ ⟨x, hx⟩) ∨ x = d.t * d.lift (d.ρ ⟨x, hx⟩) := by
  have hk : x * (d.lift (d.ρ ⟨x, hx⟩))⁻¹ ∈
      centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) := by
    refine mem_inf.2 ⟨?_, mul_mem hx (inv_mem (hd.L_le (d.lift_mem _)))⟩
    have h1 : d.ρ (⟨x, hx⟩ * (⟨d.lift (d.ρ ⟨x, hx⟩), hd.L_le (d.lift_mem _)⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hd.ρ_lift hρ, mul_inv_cancel, OneMemClass.coe_one]
    exact (hd.ρ_eq_one_iff _).1 h1
  rw [Model.kernel_eq_zpowers_of_hyp hd, Model.mem_zpowers_of_orderOf_two hd.t_two] at hk
  rcases hk with h | h
  · left
    rw [mul_inv_eq_one] at h
    exact h
  · right
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h

theorem Hyp.exists_pow_eq_one
    (hd : d.Hyp) {x : G} (hx : x ∈ centralizer ({d.t} : Set G)) {n : ℕ}
    (h : (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) ^ 2 ^ n = 1) : ∃ m : ℕ, x ^ 2 ^ m = 1 := by
  have h1 : d.ρ (⟨x, hx⟩ ^ 2 ^ n) = 1 := by
    rw [map_pow]
    exact Subtype.ext (by rw [Subgroup.coe_pow, h, OneMemClass.coe_one])
  have hk : x ^ 2 ^ n ∈ centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) :=
    ⟨(hd.ρ_eq_one_iff _).1 h1, pow_mem hx _⟩
  obtain ⟨k, hk'⟩ := hd.isCyclic_kernel.2 ⟨_, hk⟩
  refine ⟨n + k, ?_⟩
  have e := congrArg Subtype.val hk'
  rw [Subgroup.coe_pow, OneMemClass.coe_one, ← pow_mul, ← pow_add] at e
  exact e

@[expose] noncomputable def u₁ (d : Data G) : G := d.lift Model.hatU₁

@[expose] noncomputable def u₂ (d : Data G) : G := d.lift Model.hatU₂

@[expose] noncomputable def U₁₁ (d : Data G) : Subgroup G := closure {d.u₁, d.u₂}

omit [Finite G] in
theorem U₁₁_facts
    (d : Data G) :
    d.u₁ * d.u₁ = 1 ∧ d.u₂ * d.u₂ = 1 ∧ d.u₁ * d.u₂ = d.u₂ * d.u₁ ∧ d.u₁ ≠ 1 ∧ d.u₂ ≠ 1 ∧
      d.u₁ ≠ d.u₂ ∧ ∀ u, u ∈ d.U₁₁ ↔ u = 1 ∨ u = d.u₁ ∨ u = d.u₂ ∨ u = d.u₁ * d.u₂ := by
  obtain ⟨h1, h2, h12, hne1, hne2, hne, -⟩ := Model.struct_facts
  obtain ⟨h1D, h2D, -⟩ := Model.hat_mem
  have s1 : d.u₁ * d.u₁ = 1 := by
    rw [u₁, ← d.lift_mul h1D h1D, h1, d.lift_one]
  have s2 : d.u₂ * d.u₂ = 1 := by
    rw [u₂, ← d.lift_mul h2D h2D, h2, d.lift_one]
  have c12 : d.u₁ * d.u₂ = d.u₂ * d.u₁ := d.lift_comm h1D h2D h12
  refine ⟨s1, s2, c12, fun e => hne1 (d.lift_inj h1D (one_mem _) (e.trans d.lift_one.symm)),
    fun e => hne2 (d.lift_inj h2D (one_mem _) (e.trans d.lift_one.symm)),
    fun e => hne (d.lift_inj h1D h2D e), fun u => mem_closure_pair_iff s1 s2 c12⟩

omit [Finite G] in
theorem long_of_mem_U₁₁
    (d : Data G) {u : G} (hu : u ∈ d.U₁₁)
    (hu1 : u ≠ 1) : ∃ m ∈ d.L, u = m * d.z * m⁻¹ := by
  obtain ⟨h1D, h2D, -⟩ := Model.hat_mem
  have key : ∀ a, (a = Model.hatU₁ ∨ a = Model.hatU₂ ∨ a = Model.hatU₁ * Model.hatU₂) →
      ∃ m ∈ d.L, d.lift a = m * d.z * m⁻¹ := by
    intro a ha
    obtain ⟨e, he, hez⟩ := Model.long_of_mem_hatU ha
    refine ⟨d.lift e, d.lift_mem e, ?_⟩
    have hinv : (d.lift e)⁻¹ = d.lift e⁻¹ := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← d.lift_mul (inv_mem he) he, inv_mul_cancel,
        d.lift_one]
    rw [← hez, d.lift_mul (mul_mem he titsZ_mem_titsD) (inv_mem he),
      d.lift_mul he titsZ_mem_titsD, d.lift_titsZ, hinv]
  rcases (d.U₁₁_facts.2.2.2.2.2.2 u).1 hu with h | h | h | h
  · exact absurd h hu1
  · exact h ▸ key _ (Or.inl rfl)
  · exact h ▸ key _ (Or.inr (Or.inl rfl))
  · rw [h, u₁, u₂, ← d.lift_mul h1D h2D]
    exact key _ (Or.inr (Or.inr rfl))

omit [Finite G] in
theorem short_of_mem_U₁₁
    (d : Data G) {u : G} (hu : u ∈ d.U₁₁)
    (hu1 : u ≠ 1) : u * d.v = d.v * u ∧ ∃ m ∈ d.L, u * d.v = m * d.v * m⁻¹ := by
  obtain ⟨-, -, -, -, -, -, h1t, h2t, -⟩ := Model.struct_facts
  obtain ⟨h1D, h2D, -⟩ := Model.hat_mem
  have key : ∀ a, (a = Model.hatU₁ ∨ a = Model.hatU₂ ∨ a = Model.hatU₁ * Model.hatU₂) →
      a ∈ titsD → a * titsTInv = titsTInv * a →
      d.lift a * d.v = d.v * d.lift a ∧ ∃ m ∈ d.L, d.lift a * d.v = m * d.v * m⁻¹ := by
    intro a ha haD hat
    obtain ⟨f, hf, hft⟩ := Model.short_of_mem_hatU ha
    have hT := titsTInv_mem_titsD
    refine ⟨by rw [← d.lift_titsTInv]; exact d.lift_comm haD hT hat, d.lift f, d.lift_mem f, ?_⟩
    have hinv : (d.lift f)⁻¹ = d.lift f⁻¹ := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← d.lift_mul (inv_mem hf) hf, inv_mul_cancel,
        d.lift_one]
    rw [← d.lift_titsTInv, ← d.lift_mul haD hT, ← hft, d.lift_mul (mul_mem hf hT) (inv_mem hf),
      d.lift_mul hf hT, hinv]
  have h3t : Model.hatU₁ * Model.hatU₂ * titsTInv = titsTInv * (Model.hatU₁ * Model.hatU₂) := by
    rw [mul_assoc, h2t, ← mul_assoc, h1t, mul_assoc]
  rcases (d.U₁₁_facts.2.2.2.2.2.2 u).1 hu with h | h | h | h
  · exact absurd h hu1
  · exact h ▸ key _ (Or.inl rfl) h1D h1t
  · exact h ▸ key _ (Or.inr (Or.inl rfl)) h2D h2t
  · rw [h, u₁, u₂, ← d.lift_mul h1D h2D]
    exact key _ (Or.inr (Or.inr rfl)) (mul_mem h1D h2D) h3t

theorem Hyp.zOTwoComm_eq
    (hd : d.Hyp) :
    zOTwoComm (centralizer ({d.t} : Set G) ⊓ centralizer ({d.v} : Set G)) = d.U₁₁ := by
  obtain ⟨h1, h2, h12, -, -, -, h1t, h2t, hyt, hy1, hy2, -, -, -, -, hq⟩ := Model.struct_facts
  obtain ⟨h1D, h2D, hyD, -, hqD⟩ := Model.hat_mem
  obtain ⟨s1, s2, c12, ne1, ne2, ne12, hmem⟩ := d.U₁₁_facts
  have hT := titsTInv_mem_titsD
  set Q := centralizer ({d.t} : Set G) ⊓ centralizer ({d.v} : Set G) with hQ
  have memQ : ∀ {a : Equiv.Perm (Fin 1755)}, a ∈ titsD → a * titsTInv = titsTInv * a →
      d.lift a ∈ Q := by
    intro a ha hat
    refine ⟨hd.L_le (d.lift_mem a), mem_centralizer_singleton_iff.2 ?_⟩
    rw [← d.lift_titsTInv]
    exact d.lift_comm ha hT hat
  have hρ : ∀ x (hx : x ∈ Q), (d.ρ ⟨x, hx.1⟩ : Equiv.Perm (Fin 1755)) ∈ titsA ∧
      (d.ρ ⟨x, hx.1⟩ : Equiv.Perm (Fin 1755)) * titsTInv =
        titsTInv * d.ρ ⟨x, hx.1⟩ := by
    intro x hx
    refine ⟨(d.ρ ⟨x, hx.1⟩).2, (hd.commute_lift_iff hx.1 hT).1 ?_⟩
    rw [d.lift_titsTInv]
    exact mem_centralizer_singleton_iff.1 hx.2
  have hu₁ : d.u₁ = d.lift Model.hatU₁ := rfl
  have hu₂ : d.u₂ = d.lift Model.hatU₂ := rfl
  have hu₃ : d.u₁ * d.u₂ = d.lift (Model.hatU₁ * Model.hatU₂) := (d.lift_mul h1D h2D).symm
  have mU : ∀ a, (a = Model.hatU₁ ∨ a = Model.hatU₂ ∨ a = Model.hatU₁ * Model.hatU₂) →
      d.lift a ∈ closure ({d.u₁, d.u₂} : Set G) := by
    rintro a (rfl | rfl | rfl)
    · exact (hmem _).2 (Or.inr (Or.inl rfl))
    · exact (hmem _).2 (Or.inr (Or.inr (Or.inl rfl)))
    · exact (hmem _).2 (Or.inr (Or.inr (Or.inr hu₃.symm)))
  refine zOTwoComm_eq_closure s1 s2 c12 ne1 ne2 ne12 (memQ h1D h1t) (memQ h2D h2t)
    (y := d.lift Model.hatY) (memQ hyD hyt) ?_ ?_ (fun x hx => ?_) (fun x hx hx1 hx2 => ?_)
    (R := (fun w => d.lift (Model.nElt w)) '' {w | w ∈ Certificates.TitsAschbacherSecFour.qWords})
    ?_ ?_ (fun x hx hxR => ?_)
  · rw [hu₁, hu₂]
    exact hd.conj_lift_eq (hd.L_le (d.lift_mem _)) h1D h2D (by
      rw [hd.ρ_lift hyD, ← hy1, inv_mul_cancel_right])
  · rw [hu₃, hu₂]
    exact hd.conj_lift_eq (hd.L_le (d.lift_mem _)) h2D (mul_mem h1D h2D) (by
      rw [hd.ρ_lift hyD, ← hy2, inv_mul_cancel_right])
  · obtain ⟨r, hr, hok⟩ := Model.exists_cOK (hρ x hx).1 (hρ x hx).2
    obtain ⟨k1, k2, -, -⟩ := Model.cOK_sound hr hok
    have conjU : ∀ a b, (a = Model.hatU₁ ∨ a = Model.hatU₂ ∨ a = Model.hatU₁ * Model.hatU₂) →
        b ∈ titsD → (d.ρ ⟨x, hx.1⟩ : Equiv.Perm (Fin 1755)) * b *
          (d.ρ ⟨x, hx.1⟩ : Equiv.Perm (Fin 1755))⁻¹ = a →
        x * d.lift b * x⁻¹ ∈ closure ({d.u₁, d.u₂} : Set G) := by
      intro a b ha hb hab
      have haD : a ∈ titsD := by
        rcases ha with rfl | rfl | rfl
        exacts [h1D, h2D, mul_mem h1D h2D]
      rw [hd.conj_lift_eq hx.1 hb haD (by rw [← hab, inv_mul_cancel_right])]
      exact mU a ha
    refine ⟨?_, ?_⟩
    · rw [hu₁]
      rcases k1 with h | h | h
      · exact conjU _ _ (Or.inl rfl) h1D h
      · exact conjU _ _ (Or.inr (Or.inl rfl)) h1D h
      · exact conjU _ _ (Or.inr (Or.inr rfl)) h1D h
    · rw [hu₂]
      rcases k2 with h | h | h
      · exact conjU _ _ (Or.inl rfl) h2D h
      · exact conjU _ _ (Or.inr (Or.inl rfl)) h2D h
      · exact conjU _ _ (Or.inr (Or.inr rfl)) h2D h
  · obtain ⟨r, hr, hok⟩ := Model.exists_cOK (hρ x hx).1 (hρ x hx).2
    have e := (Model.cOK_sound hr hok).2.2.2 ((hd.commute_lift_iff hx.1 h1D).1 hx1)
      ((hd.commute_lift_iff hx.1 h2D).1 hx2)
    exact hd.exists_pow_eq_one hx.1 e
  · rintro _ ⟨w, hw, rfl⟩
    exact memQ (hqD w hw) (hq w hw).1
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨d.lift_comm (hqD w hw) h1D (hq w hw).2.1, d.lift_comm (hqD w hw) h2D (hq w hw).2.2⟩
  · obtain ⟨r, hr, hok⟩ := Model.exists_cOK (hρ x hx).1 (hρ x hx).2
    obtain ⟨e, u, he, hu, hxe⟩ := (Model.cOK_sound hr hok).2.2.1 fun w hw =>
      (hd.commute_lift_iff hx.1 (hqD w hw)).1 (hxR _ ⟨w, hw, rfl⟩)
    have heD : e ∈ titsD := by
      rcases he with rfl | rfl
      exacts [one_mem _, hT]
    have huD : u ∈ titsD := by
      rcases hu with rfl | rfl | rfl | rfl
      exacts [one_mem _, h1D, h2D, mul_mem h1D h2D]
    have hxD : (d.ρ ⟨x, hx.1⟩ : Equiv.Perm (Fin 1755)) ∈ titsD := hxe ▸ mul_mem heD huD
    have hlift : d.lift (d.ρ ⟨x, hx.1⟩) = d.lift e * d.lift u := by
      rw [hxe, d.lift_mul heD huD]
    have hcen : ∀ c, (c = 1 ∨ c = d.t ∨ c = d.lift e ∨ c = d.t * d.lift e) →
        ∀ q ∈ Q, c * q = q * c := by
      have he' : ∀ q ∈ Q, d.lift e * q = q * d.lift e := by
        intro q hq
        rcases he with rfl | rfl
        · rw [d.lift_one, one_mul, mul_one]
        · rw [d.lift_titsTInv]
          exact (mem_centralizer_singleton_iff.1 hq.2).symm
      have ht' : ∀ q ∈ Q, d.t * q = q * d.t :=
        fun q hq => (mem_centralizer_singleton_iff.1 hq.1).symm
      rintro c (rfl | rfl | rfl | rfl) q hq
      · rw [one_mul, mul_one]
      · exact ht' q hq
      · exact he' q hq
      · rw [mul_assoc, he' q hq, ← mul_assoc, ht' q hq, mul_assoc]
    have huU : d.lift u ∈ closure ({d.u₁, d.u₂} : Set G) := by
      rcases hu with rfl | h | h | h
      · rw [d.lift_one]
        exact one_mem _
      all_goals exact mU u (by rw [h]; first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) |
        exact Or.inr (Or.inr rfl))
    rcases hd.eq_lift_or hx.1 hxD with h | h
    · exact ⟨d.lift e, d.lift u, hcen _ (Or.inr (Or.inr (Or.inl rfl))), huU,
        by rw [h, hlift]⟩
    · exact ⟨d.t * d.lift e, d.lift u, hcen _ (Or.inr (Or.inr (Or.inr rfl))), huU,
        by rw [h, hlift, mul_assoc]⟩

theorem Hyp.exists_conj_ne_mem (hd : d.Hyp) :
    ∃ g : G, g * d.t * g⁻¹ ∈ centralizer ({d.t} : Set G) ∧ g * d.t * g⁻¹ ≠ d.t := by
  by_contra hcon
  push Not at hcon
  have : Fintype G := Fintype.ofFinite G
  have ht2 : d.t * d.t = 1 := by rw [← sq, ← hd.t_two, pow_orderOf_eq_one]
  obtain ⟨N, hN, hNodd, hNt⟩ := CFSG.ZStar.glauberman_zStar G d.t hd.t_ne_one ht2
    fun g hg => hcon g (mem_centralizer_singleton_iff.2 hg)
  have := hd.std.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | htop
  · apply hd.t_not_mem_center
    rw [mem_center_iff]
    intro g
    have h1 := hNt g
    rw [hb, mem_bot, mul_inv_eq_one] at h1
    calc g * d.t = g * d.t * g⁻¹ * g := by group
      _ = d.t * g := by rw [h1]
  · rw [htop, card_top] at hNodd
    exact Nat.not_even_iff_odd.2 hNodd hd.setting.even_card

theorem Hyp.exists_conj_eq_t_mul_z_of_conj_eq_t_mul_v
    (hd : d.Hyp) {h : G} (hh : h * d.t * h⁻¹ = d.t * d.v) :
    ∃ g : G, g * d.t * g⁻¹ = d.t * d.z := by
  obtain ⟨-, -, -, -, -, -, -, -, hyt, -, -, hy3, hy1', -, -, -⟩ := Model.struct_facts
  obtain ⟨-, -, hyD, -, -⟩ := Model.hat_mem
  obtain ⟨-, s2, -, -, -, ne12, hmem⟩ := d.U₁₁_facts
  have hT := titsTInv_mem_titsD
  have ht2 : d.t * d.t = 1 := by rw [← sq, ← hd.t_two, pow_orderOf_eq_one]
  have hv2 : d.v * d.v = 1 := by
    rw [← d.lift_titsTInv, ← d.lift_mul hT hT, titsTInv_mul_self, d.lift_one]
  have hv1 : d.v ≠ 1 := fun e => titsTInv_ne_one (d.lift_inj hT (one_mem _)
    ((d.lift_titsTInv).trans (e.trans d.lift_one.symm)))
  have hcL : ∀ l ∈ d.L, l * d.t = d.t * l := fun l hl => mem_centralizer_iff.1 hd.t_mem l hl
  have htv : d.v * d.t = d.t * d.v := hcL _ d.v_mem
  obtain ⟨s, hs⟩ : ∃ s, s = d.t * d.v := ⟨_, rfl⟩
  rw [← hs] at hh
  have hsv : d.v * s = s * d.v := by rw [hs, ← mul_assoc, htv, mul_assoc]
  have hsv' : s * d.v = d.t := by rw [hs, mul_assoc, hv2, mul_one]
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, v₀ = h⁻¹ * d.v * h := ⟨_, rfl⟩
  have htconj : d.t = h⁻¹ * s * h := by rw [← hh]; group
  have hv₀C : v₀ ∈ centralizer ({d.t} : Set G) := by
    rw [mem_centralizer_singleton_iff, hv₀, htconj]
    calc h⁻¹ * d.v * h * (h⁻¹ * s * h) = h⁻¹ * (d.v * s) * h := by group
      _ = h⁻¹ * (s * d.v) * h := by rw [hsv]
      _ = h⁻¹ * s * h * (h⁻¹ * d.v * h) := by group
  have hv₀2 : v₀ ^ 2 = 1 := by
    rw [hv₀, sq]
    calc h⁻¹ * d.v * h * (h⁻¹ * d.v * h) = h⁻¹ * (d.v * d.v) * h := by group
      _ = 1 := by rw [hv2]; group
  have hv₀L : v₀ ∈ d.L := by
    rcases hd.involution_mem hv₀C hv₀2 with h1 | h1
    · exact h1
    · exfalso
      have e : d.t * v₀ = h⁻¹ * d.t * h⁻¹⁻¹ := by
        rw [inv_inv, hv₀]
        nth_rewrite 1 [htconj]
        calc h⁻¹ * s * h * (h⁻¹ * d.v * h) = h⁻¹ * (s * d.v) * h := by group
          _ = h⁻¹ * d.t * h := by rw [hsv']
      exact hd.conj_t_not_mem h⁻¹ (e ▸ h1)
  have hv₀1 : v₀ ≠ 1 := fun e => hv1 (by
    calc d.v = h * v₀ * h⁻¹ := by rw [hv₀]; group
      _ = 1 := by rw [e]; group)
  obtain ⟨m, hm, hx⟩ := involution_L_conj d hv₀L (orderOf_eq_prime hv₀2 hv₀1)
  obtain ⟨k, hk⟩ : ∃ k, k = h * m := ⟨_, rfl⟩
  have hkt : k * d.t * k⁻¹ = s := by
    rw [hk, mul_inv_rev]
    calc h * m * d.t * (m⁻¹ * h⁻¹) = h * (m * d.t) * m⁻¹ * h⁻¹ := by group
      _ = s := by rw [hcL m hm, ← hh]; group
  have hkx : ∀ x, v₀ = m * x * m⁻¹ → k * x * k⁻¹ = d.v := by
    intro x hx
    rw [hk]
    calc h * m * x * (h * m)⁻¹ = h * (m * x * m⁻¹) * h⁻¹ := by group
      _ = d.v := by rw [← hx, hv₀]; group
  rcases hx with hx | hx
  ·
    exfalso
    have hkz := hkx _ hx
    obtain ⟨y, hy⟩ : ∃ y, y = d.lift Model.hatY := ⟨_, rfl⟩
    have hyt' : y * d.t = d.t * y := by rw [hy]; exact hcL _ (d.lift_mem _)
    have hyv : y * d.v = d.v * y := by
      rw [hy, ← d.lift_titsTInv]
      exact d.lift_comm hyD hT hyt
    have hy3' : y ^ 3 = 1 := by
      rw [hy, pow_three', ← d.lift_mul hyD hyD, ← d.lift_mul (mul_mem hyD hyD) hyD, ← pow_three',
        hy3, d.lift_one]
    have hy1 : y ≠ 1 := fun e => hy1' (d.lift_inj hyD (one_mem _)
      ((hy.symm.trans e).trans d.lift_one.symm))
    obtain ⟨w, hw⟩ : ∃ w, w = k⁻¹ * y * k := ⟨_, rfl⟩
    have hwt : w * d.t = d.t * w := by
      have e1 : d.t = k⁻¹ * s * k := by rw [← hkt]; group
      have e2 : y * s = s * y := by rw [hs, ← mul_assoc, hyt', mul_assoc, hyv, mul_assoc]
      rw [hw, e1]
      calc k⁻¹ * y * k * (k⁻¹ * s * k) = k⁻¹ * (y * s) * k := by group
        _ = k⁻¹ * (s * y) * k := by rw [e2]
        _ = k⁻¹ * s * k * (k⁻¹ * y * k) := by group
    have hwz : w * d.z = d.z * w := by
      have e1 : d.z = k⁻¹ * d.v * k := by rw [← hkz]; group
      rw [hw, e1]
      calc k⁻¹ * y * k * (k⁻¹ * d.v * k) = k⁻¹ * (y * d.v) * k := by group
        _ = k⁻¹ * (d.v * y) * k := by rw [hyv]
        _ = k⁻¹ * d.v * k * (k⁻¹ * y * k) := by group
    have hwC : w ∈ centralizer ({d.t} : Set G) := mem_centralizer_singleton_iff.2 hwt
    have hw3 : w ^ 3 = 1 := by
      have e : w ^ 3 = k⁻¹ * y ^ 3 * k := by rw [pow_three', pow_three', hw]; group
      rw [e, hy3', mul_one, inv_mul_cancel]
    have hw1 : w ≠ 1 := fun e => hy1 (by
      calc y = k * w * k⁻¹ := by rw [hw]; group
        _ = 1 := by rw [e]; group)
    have hρz : (d.ρ ⟨w, hwC⟩ : Equiv.Perm (Fin 1755)) * titsZ = titsZ * d.ρ ⟨w, hwC⟩ :=
      (hd.commute_lift_iff hwC titsZ_mem_titsD).1 (by rw [d.lift_titsZ]; exact hwz)
    have hρ3 : (d.ρ ⟨w, hwC⟩ : Equiv.Perm (Fin 1755)) ^ 3 = 1 := by
      have e : (⟨w, hwC⟩ : centralizer ({d.t} : Set G)) ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, hw3, OneMemClass.coe_one])
      rw [← Subgroup.coe_pow, ← map_pow, e, map_one, OneMemClass.coe_one]
    have hρ1 : (d.ρ ⟨w, hwC⟩ : Equiv.Perm (Fin 1755)) ≠ 1 := by
      intro e
      have hker : w ∈ centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) :=
        ⟨(hd.ρ_eq_one_iff _).1 (Subtype.ext e), hwC⟩
      rw [Model.kernel_eq_zpowers_of_hyp hd, Model.mem_zpowers_of_orderOf_two hd.t_two] at hker
      rcases hker with e' | e'
      · exact hw1 e'
      · rw [e', pow_three', ht2, one_mul] at hw3
        exact hd.t_ne_one hw3
    have hmem' : (d.ρ ⟨w, hwC⟩ : Equiv.Perm (Fin 1755)) ∈ titsA ⊓ centralizer {titsZ} :=
      ⟨(d.ρ ⟨w, hwC⟩).2, mem_centralizer_singleton_iff.2 hρz⟩
    have hdvd := orderOf_dvd_natCard (⟨_, hmem'⟩ : ↥(titsA ⊓ centralizer {titsZ}))
    rw [Subgroup.orderOf_mk, orderOf_eq_prime hρ3 hρ1, Model.centralizer_titsZ_eq,
      Model.card_twoF4H] at hdvd
    exact absurd hdvd (by norm_num)
  ·
    have hkv := hkx _ hx
    have hkv' : k⁻¹ * d.v * k = d.v := by
      calc k⁻¹ * d.v * k = k⁻¹ * (k * d.v * k⁻¹) * k := by rw [hkv]
        _ = d.v := by group
    have hA : ∀ x : G, x ∈ centralizer ({d.t} : Set G) ⊓ centralizer ({d.v} : Set G) ↔
        x * s = s * x ∧ x * d.v = d.v * x := by
      intro x
      rw [mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rw [hs, ← mul_assoc, h1, mul_assoc, h2, mul_assoc]
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rw [← hsv', ← mul_assoc, h1, mul_assoc, h2, mul_assoc]
    have hc : ∀ a x : G, (k * x * k⁻¹) * (k * a * k⁻¹) = (k * a * k⁻¹) * (k * x * k⁻¹) ↔
        x * a = a * x := by
      intro a x
      have e1 : (k * x * k⁻¹) * (k * a * k⁻¹) = k * (x * a) * k⁻¹ := by group
      have e2 : (k * a * k⁻¹) * (k * x * k⁻¹) = k * (a * x) * k⁻¹ := by group
      rw [e1, e2]
      exact ⟨fun h => mul_left_cancel (mul_right_cancel h), fun h => by rw [h]⟩
    have hkQ : k ∈ normalizer
        ((centralizer ({d.t} : Set G) ⊓ centralizer ({d.v} : Set G) : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro x
      rw [hA (k * x * k⁻¹), ← hkt]
      nth_rewrite 2 [← hkv]
      nth_rewrite 3 [← hkv]
      rw [hc, hc, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    obtain ⟨u, hu⟩ : ∃ u, u = d.u₁ * d.u₂ := ⟨_, rfl⟩
    have huU : u ∈ d.U₁₁ := (hmem _).2 (Or.inr (Or.inr (Or.inr hu)))
    have hu1 : u ≠ 1 := fun e => ne12 ((eq_inv_of_mul_eq_one_left (hu.symm.trans e)).trans
      (inv_eq_of_mul_eq_one_right s2))
    have hw : k⁻¹ * u * k ∈ d.U₁₁ := by
      have h1 := conj_mem_zOTwoComm (inv_mem hkQ) (hd.zOTwoComm_eq ▸ huU)
      rw [inv_inv] at h1
      exact hd.zOTwoComm_eq ▸ h1
    have hw1 : k⁻¹ * u * k ≠ 1 := fun e => hu1 (by
      calc u = k * (k⁻¹ * u * k) * k⁻¹ := by group
        _ = 1 := by rw [e]; group)
    obtain ⟨-, m₂, hm₂, hwv⟩ := d.short_of_mem_U₁₁ hw hw1
    obtain ⟨huv, -⟩ := d.short_of_mem_U₁₁ huU hu1
    obtain ⟨m₁, hm₁, huz⟩ := d.long_of_mem_U₁₁ huU hu1
    have e1 : u * d.v = k * m₂ * d.v * (k * m₂)⁻¹ := by
      calc u * d.v = k * ((k⁻¹ * u * k) * (k⁻¹ * d.v * k)) * k⁻¹ := by group
        _ = k * ((k⁻¹ * u * k) * d.v) * k⁻¹ := by rw [hkv']
        _ = k * (m₂ * d.v * m₂⁻¹) * k⁻¹ := by rw [hwv]
        _ = k * m₂ * d.v * (k * m₂)⁻¹ := by group
    have e2 : k * m₂ * d.t * (k * m₂)⁻¹ = s := by
      calc k * m₂ * d.t * (k * m₂)⁻¹ = k * (m₂ * d.t) * m₂⁻¹ * k⁻¹ := by group
        _ = s := by rw [hcL m₂ hm₂, ← hkt]; group
    have e3 : d.t * u = k * m₂ * h * d.t * (k * m₂ * h)⁻¹ := by
      calc d.t * u = d.t * d.v * (d.v * u) := by
            rw [mul_assoc, ← mul_assoc d.v, hv2, one_mul]
        _ = s * (u * d.v) := by rw [hs, huv]
        _ = k * m₂ * d.t * (k * m₂)⁻¹ * (k * m₂ * d.v * (k * m₂)⁻¹) := by rw [e2, e1]
        _ = k * m₂ * (d.t * d.v) * (k * m₂)⁻¹ := by group
        _ = k * m₂ * (h * d.t * h⁻¹) * (k * m₂)⁻¹ := by rw [← hs, hh]
        _ = k * m₂ * h * d.t * (k * m₂ * h)⁻¹ := by group
    refine ⟨m₁⁻¹ * (k * m₂ * h), ?_⟩
    have e4 : d.t * d.z = m₁⁻¹ * (d.t * u) * m₁ := by
      rw [huz]
      calc d.t * d.z = m₁⁻¹ * (m₁ * d.t) * d.z := by group
        _ = m₁⁻¹ * (d.t * m₁) * d.z := by rw [hcL m₁ hm₁]
        _ = m₁⁻¹ * (d.t * (m₁ * d.z * m₁⁻¹)) * m₁ := by group
    rw [e4, e3]
    group

theorem Hyp.exists_conj_eq_t_mul_z
    (hd : d.Hyp) : ∃ g : G, g * d.t * g⁻¹ = d.t * d.z := by
  obtain ⟨g, hgC, hgne⟩ := hd.exists_conj_ne_mem
  rcases hd.conj_t_cases hgC with h | ⟨m, -, h | h⟩
  · exact absurd h hgne
  · refine ⟨m⁻¹ * g, ?_⟩
    calc m⁻¹ * g * d.t * (m⁻¹ * g)⁻¹ = m⁻¹ * (g * d.t * g⁻¹) * m := by group
      _ = d.t * d.z := by rw [h]; group
  · refine hd.exists_conj_eq_t_mul_z_of_conj_eq_t_mul_v (h := m⁻¹ * g) ?_
    calc m⁻¹ * g * d.t * (m⁻¹ * g)⁻¹ = m⁻¹ * (g * d.t * g⁻¹) * m := by group
      _ = d.t * d.v := by rw [h]; group

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
