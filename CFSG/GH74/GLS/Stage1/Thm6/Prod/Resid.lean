module

public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section Lift

variable {X Y : Type*} [Group X] [Group Y] [Finite X]

theorem exists_lift_coprime (f : X →* Y) {p : ℕ} (hp : p.Prime) (x₀ : X)
    (hy : Nat.Coprime (orderOf (f x₀)) p) :
    ∃ x : X, Nat.Coprime (orderOf x) p ∧ f x = f x₀ := by
  have hn : orderOf x₀ ≠ 0 := (orderOf_pos x₀).ne'
  obtain ⟨a, m, hmp, hnm⟩ : ∃ a m : ℕ, Nat.Coprime p m ∧ p ^ a * m = orderOf x₀ :=
    ⟨_, _, Nat.coprime_ordCompl hp hn, Nat.ordProj_mul_ordCompl_eq_self _ _⟩
  have hcop2 : Nat.Coprime (orderOf (f x₀)) (p ^ a) := Nat.Coprime.pow_right _ hy
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop2 1 0
  refine ⟨x₀ ^ k, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := Nat.modEq_zero_iff_dvd.1 hk2
    have h1 : (x₀ ^ k) ^ m = 1 := by
      have : k * m = orderOf x₀ * c := by rw [hc, ← hnm]; ring
      rw [← pow_mul, this, pow_mul, pow_orderOf_eq_one, one_pow]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1) hmp.symm
  · rw [map_pow, (pow_eq_pow_iff_modEq (x := f x₀) (n := k) (m := 1)).2 hk1, pow_one]

theorem exists_lift_pElement (f : X →* Y) {p : ℕ} (hp : p.Prime) (x₀ : X) {j : ℕ}
    (hy : f x₀ ^ (p ^ j) = 1) :
    ∃ (x : X) (i : ℕ), x ^ (p ^ i) = 1 ∧ f x = f x₀ := by
  have hn : orderOf x₀ ≠ 0 := (orderOf_pos x₀).ne'
  obtain ⟨a, m, hmp, hnm⟩ : ∃ a m : ℕ, Nat.Coprime p m ∧ p ^ a * m = orderOf x₀ :=
    ⟨_, _, Nat.coprime_ordCompl hp hn, Nat.ordProj_mul_ordCompl_eq_self _ _⟩
  obtain ⟨b, hb, hdb⟩ : ∃ b ≤ j, orderOf (f x₀) = p ^ b :=
    (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hy)
  have hcop2 : Nat.Coprime (orderOf (f x₀)) m := by
    rw [hdb]; exact Nat.Coprime.pow_left _ hmp
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop2 1 0
  refine ⟨x₀ ^ k, a, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := Nat.modEq_zero_iff_dvd.1 hk2
    have : k * p ^ a = orderOf x₀ * c := by rw [hc, ← hnm]; ring
    rw [← pow_mul, this, pow_mul, pow_orderOf_eq_one, one_pow]
  · rw [map_pow, (pow_eq_pow_iff_modEq (x := f x₀) (n := k) (m := 1)).2 hk1, pow_one]

theorem map_oResidual (f : X →* Y) (hf : Function.Surjective f) {p : ℕ} (hp : p.Prime) :
    (oResidual p X).map f = oResidual p Y := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    apply Subgroup.subset_closure
    exact Nat.Coprime.coprime_dvd_left (orderOf_map_dvd f x) hx
  · refine (Subgroup.closure_le _).2 ?_
    intro y hy
    obtain ⟨x₀, rfl⟩ := hf y
    obtain ⟨x, hx, hfx⟩ := exists_lift_coprime f hp x₀ hy
    exact ⟨x, Subgroup.subset_closure hx, hfx⟩

theorem map_oPrimeResidual (f : X →* Y) (hf : Function.Surjective f) {p : ℕ} (hp : p.Prime) :
    (oPrimeResidual p X).map f = oPrimeResidual p Y := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨k, hk⟩
    apply Subgroup.subset_closure
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨k, hk⟩
    obtain ⟨x₀, rfl⟩ := hf y
    obtain ⟨x, i, hx, hfx⟩ := exists_lift_pElement f hp x₀ hk
    exact ⟨x, Subgroup.subset_closure ⟨i, hx⟩, hfx⟩

theorem map_oPrimePResidual (f : X →* Y) (hf : Function.Surjective f) {p : ℕ} (hp : p.Prime) :
    (oPrimePResidual p X).map f = oPrimePResidual p Y := by
  have hmem : ∀ x ∈ oPrimeResidual p X, f x ∈ oPrimeResidual p Y := by
    intro x hx
    rw [← map_oPrimeResidual f hf hp]
    exact ⟨x, hx, rfl⟩
  let f' : ↥(oPrimeResidual p X) →* ↥(oPrimeResidual p Y) :=
    ((f.comp (oPrimeResidual p X).subtype).codRestrict (oPrimeResidual p Y)
      (fun x => hmem x.1 x.2))
  have hf' : Function.Surjective f' := by
    rintro ⟨y, hy⟩
    rw [← map_oPrimeResidual f hf hp] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hcomm : f.comp (oPrimeResidual p X).subtype =
      (oPrimeResidual p Y).subtype.comp f' := by
    ext x; rfl
  unfold oPrimePResidual
  rw [Subgroup.map_map, hcomm, ← Subgroup.map_map, map_oResidual f' hf' hp]

theorem oPrimePResidual_eq_oResidual {p : ℕ} (hp : p.Prime) (h : oPrimeResidual p X = ⊤) :
    oPrimePResidual p X = oResidual p X := by
  have e : ∀ K : Subgroup X, K = ⊤ → (oResidual p ↥K).map K.subtype = oResidual p X := by
    intro K hK
    subst hK
    exact map_oResidual (⊤ : Subgroup X).subtype (fun x => ⟨⟨x, trivial⟩, rfl⟩) hp
  exact e _ h

end Lift

section Misc

variable {Γ : Type*} [Group Γ]

theorem oResidual_normal (p : ℕ) (Y : Type*) [Group Y] : (oResidual p Y).Normal := by
  constructor
  intro n hn g
  unfold oResidual at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    have h1 : orderOf ((MulAut.conj g).toMonoidHom x) = orderOf x :=
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    have h2 : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := rfl
    rw [h2] at h1
    show Nat.Coprime (orderOf (g * x * g⁻¹)) p
    rw [h1]
    exact hx
  | one => simp
  | mul a b _ _ iha ihb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ iha ihb
  | inv a _ iha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ iha

theorem oResidual_le_of_isPGroup_quotient {Y : Type*} [Group Y] {N : Subgroup Y} [N.Normal]
    (h : IsPGroup 2 (Y ⧸ N)) : oResidual 2 Y ≤ N := by
  refine (Subgroup.closure_le N).mpr ?_
  intro y hy
  have hy' : Nat.Coprime (orderOf y) 2 := hy
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp h (QuotientGroup.mk y)
  have hd : orderOf (QuotientGroup.mk y : Y ⧸ N) ∣ orderOf y :=
    orderOf_map_dvd (QuotientGroup.mk' N) y
  rw [hk] at hd
  have hcop : Nat.Coprime (2 ^ k) (orderOf y) := (Nat.Coprime.pow_left k (hy'.symm))
  have h1 : 2 ^ k = 1 := Nat.Coprime.eq_one_of_dvd hcop hd
  have hone : orderOf (QuotientGroup.mk y : Y ⧸ N) = 1 := by rw [hk, h1]
  exact (QuotientGroup.eq_one_iff y).mp (orderOf_eq_one_iff.mp hone)

theorem oPrimeResidual_normal (p : ℕ) (Y : Type*) [Group Y] : (oPrimeResidual p Y).Normal := by
  constructor
  intro n hn g
  unfold oPrimeResidual at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    obtain ⟨k, hk⟩ := hx
    refine ⟨k, ?_⟩
    have : (g * x * g⁻¹) ^ (p ^ k) = g * x ^ (p ^ k) * g⁻¹ := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply]; exact (map_pow (MulAut.conj g) x _).symm
    rw [this, hk]; group
  | one => simp
  | mul a b _ _ iha ihb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ iha ihb
  | inv a _ iha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ iha

theorem perm3_normal_top (N : Subgroup (Equiv.Perm (Fin 3))) [N.Normal]
    (h : ∃ g ∈ N, g ≠ 1 ∧ g * g = 1) : N = ⊤ := by
  obtain ⟨g, hg, hg1, hg2⟩ := h
  have key : ∀ g σ : Equiv.Perm (Fin 3), g ≠ 1 → g * g = 1 →
      ∃ c₁ c₂ : Equiv.Perm (Fin 3), σ = 1 ∨ σ = c₁ * g * c₁⁻¹ ∨
        σ = (c₁ * g * c₁⁻¹) * (c₂ * g * c₂⁻¹) := by decide +kernel
  rw [eq_top_iff]
  intro σ _
  obtain ⟨c₁, c₂, h | h | h⟩ := key g σ hg1 hg2
  · rw [h]; exact N.one_mem
  · rw [h]; exact Normal.conj_mem inferInstance g hg c₁
  · rw [h]; exact N.mul_mem (Normal.conj_mem inferInstance g hg c₁) (Normal.conj_mem inferInstance g hg c₂)

theorem two_elt_mem_of_map_mem {C : Type*} [Group C] (N L : Subgroup C) [N.Normal] [L.Normal]
    (hN : Nat.Coprime 2 (Nat.card N)) {s : C} {k : ℕ} (hs : s ^ (2 ^ k) = 1)
    (h : QuotientGroup.mk' N s ∈ L.map (QuotientGroup.mk' N)) : s ∈ L := by
  obtain ⟨l, hl, hls⟩ := h
  have hn : l⁻¹ * s ∈ N := by
    have : QuotientGroup.mk' N (l⁻¹ * s) = 1 := by
      rw [map_mul, map_inv, hls, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 this
  have hs' : s = l * (l⁻¹ * s) := by group
  have hq : QuotientGroup.mk' L s = QuotientGroup.mk' L (l⁻¹ * s) := by
    conv_lhs => rw [hs']
    have hl1 : QuotientGroup.mk' L l = 1 := (QuotientGroup.eq_one_iff l).2 hl
    rw [map_mul, hl1, one_mul]
  have h2 : orderOf (QuotientGroup.mk' L s) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hs, map_one])
  have h3 : orderOf (QuotientGroup.mk' L s) ∣ Nat.card N := by
    rw [hq]
    exact (orderOf_map_dvd _ _).trans (by
      have := Subgroup.orderOf_dvd_natCard N hn
      simpa [Subgroup.orderOf_coe] using this)
  have hcop : Nat.Coprime (2 ^ k) (Nat.card N) := Nat.Coprime.pow_left _ hN
  have h1 : orderOf (QuotientGroup.mk' L s) = 1 :=
    Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h2 h3)
  exact (QuotientGroup.eq_one_iff s).1 (orderOf_eq_one_iff.1 h1)

theorem exists_gen_card_three {X : Subgroup Γ} (h : Nat.card X = 3) :
    ∃ x₀ ∈ X, X = zpowers x₀ ∧ x₀ ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcyc : IsCyclic ↥X := isCyclic_of_prime_card (p := 3) h
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  refine ⟨g, g.2, ?_, ?_⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := hg ⟨x, hx⟩
      exact ⟨n, congrArg Subtype.val hn⟩
    · rw [zpowers_le]; exact g.2
  · have := pow_card_eq_one' (G := ↥X) (x := g)
    rw [h] at this
    simpa using congrArg Subtype.val this

theorem commutator_central_mul {G : Type*} [Group G] {u v a b : G} (hu : ∀ g, u * g = g * u)
    (hv : ∀ g, v * g = g * v) : ⁅u * a, v * b⁆ = ⁅a, b⁆ := by
  have hu' : ∀ g, u * g * u⁻¹ = g := fun g => by
    rw [hu g, mul_assoc, mul_inv_cancel, mul_one]
  have hv' : ∀ g, v * g * v⁻¹ = g := fun g => by
    rw [hv g, mul_assoc, mul_inv_cancel, mul_one]
  have e1 : ⁅u * a, v * b⁆ = u * (a * v * b * a⁻¹) * u⁻¹ * (b⁻¹ * v⁻¹) := by
    simp only [commutatorElement_def, mul_inv_rev]; group
  rw [e1, hu']
  have e2 : a * v * b * a⁻¹ * (b⁻¹ * v⁻¹) = a * (v * (b * a⁻¹ * b⁻¹) * v⁻¹) := by group
  rw [e2, hv']
  simp [commutatorElement_def, mul_assoc]

theorem exists_fixed_coset {Γ : Type*} [Group Γ] (Q : Subgroup Γ) [Finite Γ] (x₀ r : Γ)
    (hx : x₀ ^ 3 = 1) (hQx : ∀ q ∈ Q, x₀ * q * x₀⁻¹ ∈ Q) (hc : r⁻¹ * x₀ * r * x₀⁻¹ ∈ Q)
    (h3 : ¬ 3 ∣ Nat.card Q) : ∃ q ∈ Q, x₀ * (r * q) = (r * q) * x₀ := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  let F : Q → Q := fun q => ⟨(r⁻¹ * x₀ * r * x₀⁻¹) * (x₀ * q * x₀⁻¹), Q.mul_mem hc (hQx q q.2)⟩
  have hF : ∀ q : Q, ((F q : Q) : Γ) = r⁻¹ * x₀ * r * q * x₀⁻¹ := by
    intro q; simp only [F]; group
  have hx3 : x₀ * x₀ * x₀ = 1 := by simpa [pow_succ, mul_assoc] using hx
  have hf3 : ∀ q : Q, F (F (F q)) = q := by
    intro q
    apply Subtype.ext
    rw [hF, hF, hF]
    calc r⁻¹ * x₀ * r * (r⁻¹ * x₀ * r * (r⁻¹ * x₀ * r * (q : Γ) * x₀⁻¹) * x₀⁻¹) * x₀⁻¹
        = r⁻¹ * (x₀ * x₀ * x₀) * r * q * (x₀ * x₀ * x₀)⁻¹ := by group
      _ = q := by rw [hx3]; group
  let f : Function.End Q := F
  have hfp : f ^ 3 ^ 1 = 1 := by
    funext q
    show F^[3] q = q
    simpa [Function.iterate_succ] using hf3 q
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (α := Q) (f := f) hfp
  by_cases hne : Nonempty f.fixedPoints
  · obtain ⟨⟨q, hq⟩⟩ := hne
    refine ⟨q, q.2, ?_⟩
    have h1 : (F q : Γ) = q := by rw [show F q = q from hq]
    rw [hF] at h1
    have h2 : x₀ * (r * q) = (r * q) * x₀ := by
      calc x₀ * (r * q) = r * (r⁻¹ * x₀ * r * q * x₀⁻¹) * x₀ := by group
        _ = r * q * x₀ := by rw [h1]
    exact h2
  · exfalso
    have hempty : IsEmpty f.fixedPoints := not_nonempty_iff.1 hne
    have hz : Fintype.card f.fixedPoints = 0 := by
      rw [← Nat.card_eq_fintype_card]; exact Nat.card_of_isEmpty
    rw [hz] at hmod
    apply h3
    have : 3 ∣ Fintype.card Q := (Nat.modEq_zero_iff_dvd).1 hmod
    simpa [Nat.card_eq_fintype_card] using this


theorem oPrimePResidual_normal {p : ℕ} (hp : p.Prime) (X : Type*) [Group X] [Finite X] :
    (oPrimePResidual p X).Normal := by
  have hY : (oPrimeResidual p X).Normal := oPrimeResidual_normal p X
  constructor
  rintro _ ⟨y, hy, rfl⟩ g
  let α : MulAut ↥(oPrimeResidual p X) := MulAut.conjNormal g
  refine ⟨α y, ?_, by simp [α, MulAut.conjNormal_apply]⟩
  have : α y ∈ (oResidual p ↥(oPrimeResidual p X)).map α.toMonoidHom := ⟨y, hy, rfl⟩
  rwa [map_oResidual α.toMonoidHom α.surjective hp] at this

end Misc

end CFSG.GH74.GLS.Stage1.Thm6.Prod
