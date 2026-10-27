module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem not_mem_closure_odd_of_comm {D N : Subgroup X} (_hND : N ≤ D)
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b * a⁻¹ * b⁻¹ ∈ N) {x : X} (hxD : x ∈ D) (hx : x * x = 1)
    (hxN : x ∉ N) : x ∉ closure {y : X | y ∈ D ∧ Odd (orderOf y)} := by
  classical
  set N' : Subgroup ↥D := N.subgroupOf D with hN'
  have hN'n : N'.Normal := by
    refine ⟨fun n hn d => ?_⟩
    rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : (d : X) * n * (d : X)⁻¹ * (n : X)⁻¹ ∈ N := hcomm d d.2 n n.2
    have h2 : (d : X) * n * (d : X)⁻¹ = ((d : X) * n * (d : X)⁻¹ * (n : X)⁻¹) * n := by group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h2]
    exact N.mul_mem h1 hn
  let φ : ↥D →* ↥D ⧸ N' := QuotientGroup.mk' N'
  have hφc : ∀ a b : ↥D, Commute (φ a) (φ b) := by
    intro a b
    show φ a * φ b = φ b * φ a
    rw [← map_mul, ← map_mul]
    refine QuotientGroup.eq.mpr ?_
    rw [hN', Subgroup.mem_subgroupOf]
    have := hcomm (b : X)⁻¹ (D.inv_mem b.2) (a : X)⁻¹ (D.inv_mem a.2)
    simpa [mul_assoc] using this
  let T : Subgroup ↥D :=
    { carrier := {g | ∃ m : ℕ, Odd m ∧ φ g ^ m = 1}
      one_mem' := ⟨1, odd_one, by simp⟩
      mul_mem' := by
        rintro a b ⟨m, hm, ha⟩ ⟨k, hk, hb⟩
        refine ⟨m * k, hm.mul hk, ?_⟩
        rw [map_mul, (hφc a b).mul_pow, pow_mul, ha, one_pow, mul_comm m k, pow_mul, hb, one_pow,
          one_mul]
      inv_mem' := by
        rintro a ⟨m, hm, ha⟩
        exact ⟨m, hm, by rw [map_inv, inv_pow, ha, inv_one]⟩ }
  intro hmem
  have hle : closure {y : X | y ∈ D ∧ Odd (orderOf y)} ≤ T.map D.subtype := by
    rw [closure_le]
    rintro y ⟨hyD, hyodd⟩
    refine ⟨⟨y, hyD⟩, ⟨orderOf y, hyodd, ?_⟩, rfl⟩
    rw [← map_pow]
    have : (⟨y, hyD⟩ : ↥D) ^ orderOf y = 1 := Subtype.ext (by simp)
    rw [this, map_one]
  obtain ⟨g, ⟨m, hm, hgm⟩, hgx⟩ := hle hmem
  have hg : g = ⟨x, hxD⟩ := Subtype.ext hgx
  subst hg
  have hsq : (⟨x, hxD⟩ : ↥D) * ⟨x, hxD⟩ = 1 := Subtype.ext hx
  obtain ⟨k, rfl⟩ := hm
  have hpow : (⟨x, hxD⟩ : ↥D) ^ (2 * k + 1) = ⟨x, hxD⟩ := by
    rw [pow_succ, pow_mul, pow_two, hsq, one_pow, one_mul]
  rw [← map_pow, hpow] at hgm
  have : (⟨x, hxD⟩ : ↥D) ∈ N' := (QuotientGroup.eq_one_iff _).mp hgm
  exact hxN (by rw [hN', Subgroup.mem_subgroupOf] at this; exact this)

omit [Finite X] in
theorem exists_proj_of_normal_complement {M N₁ D : Subgroup X} (hDM : D ≤ M)
    (hN₁ : ∀ g ∈ M, ∀ x ∈ N₁, g * x * g⁻¹ ∈ N₁) (hsup : ∀ g ∈ M, ∃ a ∈ N₁, ∃ d ∈ D, g = a * d)
    (hinf : N₁ ⊓ D = ⊥) :
    ∃ π : ↥M →* ↥D, (∀ d : ↥D, π ⟨(d : X), hDM d.2⟩ = d) ∧
      ∀ m : ↥M, (m : X) * ((π m : ↥D) : X)⁻¹ ∈ N₁ := by
  classical
  have hex : ∀ m : ↥M, ∃ d : ↥D, (m : X) * ((d : ↥D) : X)⁻¹ ∈ N₁ := by
    intro m
    obtain ⟨v, hv, d, hd, hmd⟩ := hsup m m.2
    refine ⟨⟨d, hd⟩, ?_⟩
    have : (m : X) * d⁻¹ = v := by rw [hmd]; group
    simpa [this] using hv
  have huniq : ∀ (m : ↥M) (d d' : ↥D), (m : X) * ((d : ↥D) : X)⁻¹ ∈ N₁ →
      (m : X) * ((d' : ↥D) : X)⁻¹ ∈ N₁ → d = d' := by
    intro m d d' h h'
    have h1 : ((d' : X) * (d : X)⁻¹) ∈ N₁ := by
      have := N₁.mul_mem (N₁.inv_mem h') h
      have e : ((m : X) * (d' : X)⁻¹)⁻¹ * ((m : X) * (d : X)⁻¹) = (d' : X) * (d : X)⁻¹ := by group
      rwa [e] at this
    have h2 : ((d' : X) * (d : X)⁻¹) ∈ D := D.mul_mem d'.2 (D.inv_mem d.2)
    have h3 : ((d' : X) * (d : X)⁻¹) ∈ N₁ ⊓ D := ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot] at h3
    exact Subtype.ext (mul_inv_eq_one.mp h3).symm
  let f : ↥M → ↥D := fun m => Classical.choose (hex m)
  have hf : ∀ m : ↥M, (m : X) * ((f m : ↥D) : X)⁻¹ ∈ N₁ := fun m => Classical.choose_spec (hex m)
  refine ⟨
    { toFun := f
      map_one' := by
        refine huniq 1 _ 1 (hf 1) ?_
        simp
      map_mul' := by
        intro m m'
        refine huniq (m * m') _ _ (hf (m * m')) ?_
        have e : ((m * m' : ↥M) : X) * (((f m * f m' : ↥D) : ↥D) : X)⁻¹ =
            ((m : X) * ((m' : X) * ((f m' : ↥D) : X)⁻¹) * (m : X)⁻¹) *
              ((m : X) * ((f m : ↥D) : X)⁻¹) := by
          simp only [Subgroup.coe_mul, mul_inv_rev]
          group
        rw [e]
        exact N₁.mul_mem (hN₁ (m : X) m.2 _ (hf m')) (hf m) }, ?_, hf⟩
  intro d
  refine huniq _ _ d (hf _) ?_
  simp

omit [Finite X] in
theorem not_mem_closure_odd_of_complement {M N₁ D : Subgroup X} (hDM : D ≤ M) (_hN₁M : N₁ ≤ M)
    (hN₁ : ∀ g ∈ M, ∀ x ∈ N₁, g * x * g⁻¹ ∈ N₁) (hsup : ∀ g ∈ M, ∃ a ∈ N₁, ∃ d ∈ D, g = a * d)
    (hinf : N₁ ⊓ D = ⊥) {x : X} (hxD : x ∈ D)
    (hx : x ∉ closure {y : X | y ∈ D ∧ Odd (orderOf y)}) :
    x ∉ closure {y : X | y ∈ M ∧ Odd (orderOf y)} := by
  obtain ⟨π, hπD, -⟩ := exists_proj_of_normal_complement hDM hN₁ hsup hinf
  let T : Subgroup ↥M := (closure {y : X | y ∈ D ∧ Odd (orderOf y)}).comap (D.subtype.comp π)
  intro hmem
  have hle : closure {y : X | y ∈ M ∧ Odd (orderOf y)} ≤ T.map M.subtype := by
    rw [closure_le]
    rintro y ⟨hyM, hyodd⟩
    refine ⟨⟨y, hyM⟩, ?_, rfl⟩
    show ((π ⟨y, hyM⟩ : ↥D) : X) ∈ closure {y : X | y ∈ D ∧ Odd (orderOf y)}
    refine subset_closure ⟨(π ⟨y, hyM⟩).2, ?_⟩
    have h1 : orderOf (π ⟨y, hyM⟩) ∣ orderOf y := by
      have := orderOf_map_dvd π (⟨y, hyM⟩ : ↥M)
      rwa [Subgroup.orderOf_mk y hyM] at this
    have h2 : orderOf ((π ⟨y, hyM⟩ : ↥D) : X) = orderOf (π ⟨y, hyM⟩) := Subgroup.orderOf_coe _
    rw [h2]
    exact Odd.of_dvd_nat hyodd h1
  obtain ⟨g, hgT, hgx⟩ := hle hmem
  have hg : g = ⟨x, hDM hxD⟩ := Subtype.ext hgx
  subst hg
  have : ((π ⟨x, hDM hxD⟩ : ↥D) : X) ∈ closure {y : X | y ∈ D ∧ Odd (orderOf y)} := hgT
  rw [hπD ⟨x, hxD⟩] at this
  exact hx this

theorem exists_normal_sylow_two {C : Subgroup X}
    (hB : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup X, P ≤ C → IsPGroup p P →
      ¬ p ∣ P.relIndex C → normalizer (P : Set X) ⊓ C ≤ centralizer (P : Set X)) :
    ∃ S : Subgroup X, S ≤ C ∧ IsPGroup 2 S ∧ (∀ g ∈ C, IsPGroup 2 (zpowers g) → g ∈ S) ∧
      ∀ g ∈ C, ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
  classical
  have hK : ∀ p : {p : ℕ // p.Prime ∧ p ≠ 2}, ∃ K : Subgroup ↥C, K.Normal ∧
      ¬ (p : ℕ) ∣ Nat.card K ∧ ∀ g : ↥C, (∃ a : ℕ, orderOf g = 2 ^ a) → g ∈ K := by
    rintro ⟨p, hp, hp2⟩
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨P⟩ : Nonempty (Sylow p ↥C) := inferInstance
    set Pm : Subgroup X := (P : Subgroup ↥C).map C.subtype with hPm
    have hPmC : Pm ≤ C := Subgroup.map_subtype_le _
    have hPmp : IsPGroup p Pm :=
      P.isPGroup'.of_surjective (C.subtype.subgroupMap (P : Subgroup ↥C))
        (C.subtype.subgroupMap_surjective _)
    have hidx : ¬ p ∣ Pm.relIndex C := by
      have : Pm.relIndex C = (P : Subgroup ↥C).index := by
        rw [Subgroup.relIndex, hPm]
        rw [show ((P : Subgroup ↥C).map C.subtype).subgroupOf C = (P : Subgroup ↥C) from
          Subgroup.comap_map_eq_self_of_injective C.subtype_injective _]
      rw [this]
      exact P.not_dvd_index
    have hnorm := hB p hp hp2 Pm hPmC hPmp hidx
    have hP : normalizer (P : Set ↥C) ≤ centralizer (P : Set ↥C) := by
      intro g hg
      have hg' : g ∈ normalizer ((P : Subgroup ↥C) : Set ↥C) := hg
      have hgn : (g : X) ∈ normalizer (Pm : Set X) := by
        rw [Subgroup.mem_normalizer_iff] at hg' ⊢
        intro y
        constructor
        · rintro ⟨h, hh, rfl⟩
          exact ⟨g * h * g⁻¹, (hg' h).mp hh, by simp⟩
        · rintro ⟨h, hh, hgy⟩
          refine ⟨g⁻¹ * h * g, ?_, ?_⟩
          · refine (hg' (g⁻¹ * h * g)).mpr ?_
            have e : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
            rw [e]
            exact hh
          · have hgy' : (h : X) = g * y * (g : X)⁻¹ := hgy
            show (g : X)⁻¹ * h * g = y
            rw [hgy']
            group
      have hgc := hnorm ⟨hgn, g.2⟩
      change g ∈ centralizer ((P : Subgroup ↥C) : Set ↥C)
      rw [Subgroup.mem_centralizer_iff] at hgc ⊢
      intro h hh
      exact Subtype.ext (hgc h ⟨h, hh, rfl⟩)
    obtain ⟨K, hKn, hKp, hKidx, -⟩ := CFSG.GroupTheory.burnside_normal_complement P hP
    refine ⟨K, hKn, hKp, fun g ⟨a, ha⟩ => ?_⟩
    have hq : IsPGroup p (↥C ⧸ K) := by
      obtain ⟨n, hn⟩ := P.2.exists_card_eq
      refine IsPGroup.of_card (n := n) ?_
      rw [← Subgroup.index_eq_card, hKidx, hn]
    obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.mp hq) (QuotientGroup.mk g)
    have hdvd : orderOf (QuotientGroup.mk g : ↥C ⧸ K) ∣ orderOf g :=
      orderOf_map_dvd (QuotientGroup.mk' K) g
    rw [hb, ha] at hdvd
    have hb0 : p ^ b = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)) hdvd
    have hone : (QuotientGroup.mk g : ↥C ⧸ K) = 1 := by
      rw [← orderOf_eq_one_iff, hb, hb0]
    exact (QuotientGroup.eq_one_iff g).mp hone
  choose K hKn hKp hK2 using hK
  have hSn : (⨅ p, K p).Normal := Subgroup.normal_iInf_normal hKn
  set S' : Subgroup ↥C := ⨅ p, K p with hS'
  have hS'2 : IsPGroup 2 ↥S' := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card S' = 2 ^ k :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := ↥S')).ne' (fun {q} hq hqd => by
        by_contra hq2
        exact hKp ⟨q, hq, hq2⟩ (hqd.trans (Subgroup.card_dvd_of_le (iInf_le K ⟨q, hq, hq2⟩))))⟩
    exact IsPGroup.of_card hk
  refine ⟨S'.map C.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · exact hS'2.of_surjective (C.subtype.subgroupMap S') (C.subtype.subgroupMap_surjective S')
  · intro g hg hg2
    obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.mp hg2 ⟨g, mem_zpowers g⟩
    have ha' : orderOf (⟨g, hg⟩ : ↥C) = 2 ^ a := by
      rw [Subgroup.orderOf_mk]
      rwa [Subgroup.orderOf_mk] at ha
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, hS', Subgroup.mem_iInf]
    exact fun p => hK2 p ⟨g, hg⟩ ⟨a, ha'⟩
  · rintro g hg _ ⟨s, hs, rfl⟩
    exact ⟨⟨g, hg⟩ * s * ⟨g, hg⟩⁻¹, hSn.conj_mem s hs ⟨g, hg⟩, by simp⟩

theorem exists_commute_mem_coset {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : X}
    (hx : IsPGroup p (zpowers x)) {N : Subgroup X} (hN : IsPGroup 2 N)
    (hxN : ∀ m ∈ N, x * m * x⁻¹ ∈ N) {v : X} (hv : v⁻¹ * (x * v * x⁻¹) ∈ N) :
    ∃ c : X, v⁻¹ * c ∈ N ∧ x * c = c * x := by
  have : Fact p.Prime := ⟨hp⟩
  have hcop : ¬ p ∣ Nat.card N := by
    obtain ⟨n, hn⟩ := hN.exists_card_eq
    rw [hn]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hstep : ∀ y : X, v⁻¹ * y ∈ N → v⁻¹ * (x * y * x⁻¹) ∈ N := by
    intro y hy
    have e : v⁻¹ * (x * y * x⁻¹) = (v⁻¹ * (x * v * x⁻¹)) * (x * (v⁻¹ * y) * x⁻¹) := by group
    rw [e]
    exact N.mul_mem hv (hxN _ hy)
  have hpow : ∀ k : ℕ, ∀ y : X, v⁻¹ * y ∈ N → v⁻¹ * (x ^ k * y * (x ^ k)⁻¹) ∈ N := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      have := hstep _ (ih y hy)
      have e : x * (x ^ k * y * (x ^ k)⁻¹) * x⁻¹ = x ^ (k + 1) * y * (x ^ (k + 1))⁻¹ := by
        rw [pow_succ']
        group
      rwa [e] at this
  let α : ↥(zpowers x) →* MulAut X := MulAut.conj.comp (zpowers x).subtype
  have hα : ∀ (a : ↥(zpowers x)) (y : X), α a y = (a : X) * y * (a : X)⁻¹ := fun a y => rfl
  have hinv : ∀ a : ↥(zpowers x), ∀ y : X, v⁻¹ * y ∈ N → v⁻¹ * α a y ∈ N := by
    intro a y hy
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp
      ((mem_powers_iff_mem_zpowers (x := x) (y := (a : X))).mpr a.2)
    rw [hα, ← hk]
    exact hpow k y hy
  obtain ⟨c, hc, hfix⟩ :=
    (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed p hx α N hcop v).2 hinv
  refine ⟨c, hc, ?_⟩
  have h' : x * c * x⁻¹ = c := (hα ⟨x, mem_zpowers x⟩ c).symm.trans (hfix ⟨x, mem_zpowers x⟩)
  calc x * c = x * c * x⁻¹ * x := by group
    _ = c * x := by rw [h']

theorem card_subtype_ne_eq_sub_one {α : Type*} [Finite α] (b : α) :
    Nat.card {a : α // a ≠ b} = Nat.card α - 1 := by
  classical
  have := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]

theorem ncard_conj_TI {H U : Subgroup X}
    (hTI : ∀ g ∈ H, ∀ a ∈ U, a ≠ 1 → g * a * g⁻¹ ∈ U → g ∈ normalizer (U : Set X)) :
    {y : X | ∃ g ∈ H, ∃ a ∈ U, a ≠ 1 ∧ y = g * a * g⁻¹}.ncard =
      ((H ⊓ normalizer (U : Set X)).subgroupOf H).index * (Nat.card U - 1) := by
  classical
  set NH : Subgroup ↥H := (H ⊓ normalizer (U : Set X)).subgroupOf H with hNH
  have hmemNH : ∀ g : ↥H, g ∈ NH ↔ (g : X) ∈ normalizer (U : Set X) := by
    intro g
    rw [hNH, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
  let Y : Set X := {y : X | ∃ g ∈ H, ∃ a ∈ U, a ≠ 1 ∧ y = g * a * g⁻¹}
  let Φ : (↥H ⧸ NH) × {a : ↥U // a ≠ 1} → Y := fun q =>
    ⟨((q.1.out : ↥H) : X) * ((q.2.1 : ↥U) : X) * ((q.1.out : ↥H) : X)⁻¹,
      (q.1.out : ↥H), (q.1.out : ↥H).2, (q.2.1 : ↥U), q.2.1.2,
      fun h => q.2.2 (Subtype.ext h), rfl⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨q, a, ha⟩ ⟨q', a', ha'⟩ h
      have h1 : ((q.out : ↥H) : X) * (a : X) * ((q.out : ↥H) : X)⁻¹ =
          ((q'.out : ↥H) : X) * (a' : X) * ((q'.out : ↥H) : X)⁻¹ := congrArg Subtype.val h
      have h2 : (((q'.out : ↥H)⁻¹ * q.out : ↥H) : X) * (a : X) *
          (((q'.out : ↥H)⁻¹ * q.out : ↥H) : X)⁻¹ = (a' : X) := by
        have : (((q'.out : ↥H)⁻¹ * q.out : ↥H) : X) * (a : X) *
            (((q'.out : ↥H)⁻¹ * q.out : ↥H) : X)⁻¹ =
            ((q'.out : ↥H) : X)⁻¹ * (((q.out : ↥H) : X) * (a : X) * ((q.out : ↥H) : X)⁻¹) *
              ((q'.out : ↥H) : X) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
          group
        rw [this, h1]
        group
      have h3 : (((q'.out : ↥H)⁻¹ * q.out : ↥H) : X) ∈ normalizer (U : Set X) :=
        hTI _ (((q'.out : ↥H)⁻¹ * q.out : ↥H)).2 (a : X) a.2 (fun h => ha (Subtype.ext h))
          (h2 ▸ a'.2)
      have h4 : ((q'.out : ↥H)⁻¹ * q.out : ↥H) ∈ NH := (hmemNH _).mpr h3
      have h5 : q' = q := by
        rw [← QuotientGroup.out_eq' q', ← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.mpr h4
      subst h5
      have : (a : X) = (a' : X) := by
        have := h1
        simpa using this
      have : a = a' := Subtype.ext this
      subst this
      rfl
    · rintro ⟨y, g, hg, a, ha, ha1, rfl⟩
      let q : ↥H ⧸ NH := QuotientGroup.mk ⟨g, hg⟩
      have hq : (q.out : ↥H)⁻¹ * ⟨g, hg⟩ ∈ NH := by
        have : (QuotientGroup.mk (q.out : ↥H) : ↥H ⧸ NH) = QuotientGroup.mk ⟨g, hg⟩ :=
          QuotientGroup.out_eq' q
        exact QuotientGroup.eq.mp this
      have hm := (hmemNH _).mp hq
      set m : X := (((q.out : ↥H)⁻¹ * ⟨g, hg⟩ : ↥H) : X) with hm_def
      have hmU : m * a * m⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hm a).mp ha
      have hm1 : m * a * m⁻¹ ≠ 1 := by
        intro h
        apply ha1
        have := congrArg (fun z => m⁻¹ * z * m) h
        simpa [mul_assoc] using this
      refine ⟨(q, ⟨⟨m * a * m⁻¹, hmU⟩, fun h => hm1 (congrArg Subtype.val h)⟩), ?_⟩
      apply Subtype.ext
      show ((q.out : ↥H) : X) * (m * a * m⁻¹) * ((q.out : ↥H) : X)⁻¹ = g * a * g⁻¹
      have hg' : g = ((q.out : ↥H) : X) * m := by
        rw [hm_def]
        simp
      rw [hg']
      group
  have hcard : Nat.card Y = Nat.card ((↥H ⧸ NH) × {a : ↥U // a ≠ 1}) :=
    (Nat.card_congr (Equiv.ofBijective Φ hΦ)).symm
  rw [← Nat.card_coe_set_eq]
  change Nat.card Y = _
  rw [hcard, Nat.card_prod, card_subtype_ne_eq_sub_one, ← Subgroup.index_eq_card]

theorem exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] {P H : Subgroup X}
    (hP : IsPGroup p P) (hHP : H ≤ P) (hne : H ≠ P) :
    ∃ g ∈ P, g ∉ H ∧ g ∈ normalizer (H : Set X) := by
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have hnc : NormalizerCondition ↥P := Group.normalizerCondition_of_isNilpotent
  have hlt : H.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hne (le_antisymm hHP htop)
  obtain ⟨g, hg1, hg2⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
  refine ⟨g.1, g.2, hg2, ?_⟩
  have h2 : g ∈ (normalizer (H : Set X)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq hHP]
    exact hg1
  exact h2

omit [Finite X] in
theorem card_sup_of_normal {N D : Subgroup X} (hN : ∀ d ∈ D, ∀ x ∈ N, d * x * d⁻¹ ∈ N)
    (hinf : N ⊓ D = ⊥) : Nat.card ↥(N ⊔ D) = Nat.card N * Nat.card D := by
  have hDN : D ≤ normalizer (N : Set X) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hN d hd x hx, fun hx => ?_⟩
    have := hN d⁻¹ (D.inv_mem hd) _ hx
    simpa [mul_assoc] using this
  have hmul : ((D ⊔ N : Subgroup X) : Set X) = (D : Set X) * (N : Set X) :=
    Subgroup.coe_mul_of_left_le_normalizer_right D N hDN
  let f : D × N → ↥(N ⊔ D) := fun q =>
    ⟨(q.1 : X) * q.2, by rw [sup_comm, ← SetLike.mem_coe, hmul]; exact Set.mul_mem_mul q.1.2 q.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨d, hd⟩, ⟨n, hn⟩⟩ ⟨⟨d', hd'⟩, ⟨n', hn'⟩⟩ h
      have h' : d * n = d' * n' := congrArg Subtype.val h
      have h1 : d'⁻¹ * d ∈ N ⊓ D := by
        refine ⟨?_, D.mul_mem (D.inv_mem hd') hd⟩
        have e : d'⁻¹ * d = n' * n⁻¹ := by
          have : d = d' * n' * n⁻¹ := by rw [← h']; group
          rw [this]; group
        rw [e]
        exact N.mul_mem hn' (N.inv_mem hn)
      rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at h1
      subst h1
      have : n = n' := mul_left_cancel h'
      subst this
      rfl
    · rintro ⟨y, hy⟩
      rw [sup_comm, ← SetLike.mem_coe, hmul] at hy
      obtain ⟨d, hd, n, hn, rfl⟩ := hy
      exact ⟨(⟨d, hd⟩, ⟨n, hn⟩), rfl⟩
  have := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod] at this
  rw [← this, mul_comm]

end CFSG.GH74.Uniqueness
