module

public import CFSG.GH74.Uniqueness.Section14Defs
public import CFSG.GH74.Uniqueness.Section5Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X]

theorem weak149_exists_centralizer_mod {M V : Subgroup X}
    (hVn : ∀ g ∈ M, ∀ v ∈ V, g * v * g⁻¹ ∈ V) (v : X) :
    ∃ C : Subgroup X, ∀ h, h ∈ C ↔ h ∈ M ∧ h * v * h⁻¹ * v⁻¹ ∈ V := by
  refine ⟨{ carrier := {h | h ∈ M ∧ h * v * h⁻¹ * v⁻¹ ∈ V}
            one_mem' := ⟨M.one_mem, by simp⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, fun h => Iff.rfl⟩
  · rintro h₁ h₂ ⟨h₁M, h₁V⟩ ⟨h₂M, h₂V⟩
    refine ⟨M.mul_mem h₁M h₂M, ?_⟩
    have e : h₁ * h₂ * v * (h₁ * h₂)⁻¹ * v⁻¹ =
        h₁ * (h₂ * v * h₂⁻¹ * v⁻¹) * h₁⁻¹ * (h₁ * v * h₁⁻¹ * v⁻¹) := by group
    rw [e]
    exact V.mul_mem (hVn h₁ h₁M _ h₂V) h₁V
  · rintro h ⟨hM, hV⟩
    refine ⟨M.inv_mem hM, ?_⟩
    have e : h⁻¹ * v * h⁻¹⁻¹ * v⁻¹ = h⁻¹ * (h * v * h⁻¹ * v⁻¹)⁻¹ * h⁻¹⁻¹ := by group
    rw [e]
    exact hVn h⁻¹ (M.inv_mem hM) _ (V.inv_mem hV)

variable [Finite X]

theorem weak149_reduction {M V S : Subgroup X} {u : X}
    (hVn : ∀ g ∈ M, ∀ v ∈ V, g * v * g⁻¹ ∈ V) (hS : ABGLocalTools.IsSylowOf 2 S M)
    (hSab : ∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ V) (huS : u ∈ S)
    (hN : ∀ g ∈ M, g ∈ normalizer (S : Set X) → g * u * g⁻¹ * u⁻¹ ∈ V) :
    ∀ g ∈ M, g * u * g⁻¹ ∈ S → g * u * g⁻¹ * u⁻¹ ∈ V := by
  intro g hgM hv
  obtain ⟨C, hC⟩ := weak149_exists_centralizer_mod hVn (g * u * g⁻¹)
  have hSC : S ≤ C := fun s hs => (hC s).2 ⟨hS.le hs, hSab s hs _ hv⟩
  have hCM : C ≤ M := fun h hh => ((hC h).1 hh).1
  have hconj : S ≤ conjugate C g := by
    intro x hx
    rw [mem_conjugate_iff, hC]
    refine ⟨M.mul_mem (M.mul_mem hgM (hS.le hx)) (M.inv_mem hgM), ?_⟩
    have e : g * x * g⁻¹ * (g * u * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * u * g⁻¹)⁻¹ =
        g * (x * u * x⁻¹ * u⁻¹) * g⁻¹ := by group
    rw [e]
    exact hVn g hgM _ (hSab x hx u huS)
  obtain ⟨e, heC, hen⟩ :=
    exists_mul_mem_normalizer_of_isSylowOf Nat.prime_two (hS.of_le hSC hCM) hconj
  have h1 := hN (e * g) (M.mul_mem (hCM heC) hgM) hen
  have h2 := ((hC e).1 heC).2
  have e2 : g * u * g⁻¹ * u⁻¹ = (e * (g * u * g⁻¹) * e⁻¹ * (g * u * g⁻¹)⁻¹)⁻¹ *
      (e * g * u * (e * g)⁻¹ * u⁻¹) := by group
  rw [e2]
  exact V.mul_mem (V.inv_mem h2) h1

omit [Finite X] in
theorem weak149_exists_action {N S V : Subgroup X} [(V.subgroupOf S).Normal]
    (hNS : N ≤ normalizer (S : Set X)) (hNV : N ≤ normalizer (V : Set X))
    (hSV : S ≤ normalizer (V : Set X)) :
    ∃ ρ : N →* MulAut (S ⧸ V.subgroupOf S), ∀ (n : N) (s : S),
      ρ n (s : S ⧸ V.subgroupOf S) = (s : S ⧸ V.subgroupOf S) ↔
        (n : X) * s * (n : X)⁻¹ * (s : X)⁻¹ ∈ V := by
  refine ⟨ABGLocalTools.chiefAction hNS hNV, fun n s => ?_⟩
  rw [ABGLocalTools.chiefAction_mk, QuotientGroup.eq, mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, ABGLocalTools.chiefConj_apply_coe]
  have hs : ∀ v, v ∈ V ↔ (s : X) * v * (s : X)⁻¹ ∈ V := mem_normalizer_iff.1 (hSV s.2)
  have hs' : ∀ v, v ∈ V ↔ (s : X)⁻¹ * v * (s : X)⁻¹⁻¹ ∈ V :=
    mem_normalizer_iff.1 (hSV (S.inv_mem s.2))
  constructor
  · intro h
    have h1 := V.inv_mem ((hs _).1 h)
    have e : (n : X) * s * (n : X)⁻¹ * (s : X)⁻¹ =
        ((s : X) * (((n : X) * s * (n : X)⁻¹)⁻¹ * s) * (s : X)⁻¹)⁻¹ := by group
    rw [e]
    exact h1
  · intro h
    have h1 := (hs' _).1 (V.inv_mem h)
    have e : ((n : X) * s * (n : X)⁻¹)⁻¹ * s =
        (s : X)⁻¹ * ((n : X) * s * (n : X)⁻¹ * (s : X)⁻¹)⁻¹ * (s : X)⁻¹⁻¹ := by group
    rw [e]
    exact h1

omit [Finite X] in
theorem weak149_eq_one_of_mem {S K : Subgroup X} (hS : IsPGroup 2 S) (hK : Odd (Nat.card K))
    {k : X} (hkK : k ∈ K) (hkS : k ∈ S) : k = 1 := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.1 hS ⟨k, hkS⟩
  have h1 : orderOf k = 2 ^ m := by simpa using hm
  have h2 : orderOf k ∣ Nat.card K := by simpa using orderOf_dvd_natCard (⟨k, hkK⟩ : K)
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simpa using h1
  · exfalso
    have : 2 ∣ Nat.card K := (dvd_pow_self 2 hm0.ne').trans (h1 ▸ h2)
    exact (Nat.not_even_iff_odd.2 hK) (even_iff_two_dvd.2 this)

theorem weak149_core {M V S K : Subgroup X} {u : X} {n : ℕ} (hF : Frob149Stmt)
    (hVn : ∀ g ∈ M, ∀ v ∈ V, g * v * g⁻¹ ∈ V) (hVS : V ≤ S)
    (hS : ABGLocalTools.IsSylowOf 2 S M)
    (hSab : ∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ V ∧ x * x ∈ V)
    (hn : 3 ≤ n) (hcard : Nat.card S = 2 ^ (2 * n + 1) * Nat.card V) (huS : u ∈ S) (huV : u ∉ V)
    (hKM : K ≤ M) (hKS : K ≤ normalizer (S : Set X)) (hKcard : Nat.card K = 2 ^ n - 1)
    (hKu : ∀ k ∈ K, k * u = u * k)
    (h1 : ∀ g ∈ M, g ∈ normalizer (S : Set X) → (∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ V) → g ∈ S)
    (h2 : ∀ y ∈ K, (orderOf y).Prime → ∀ s ∈ S, s * y * s⁻¹ * y⁻¹ ∈ V → s ∈ V ∨ s * u⁻¹ ∈ V)
    (h3 : ∀ y ∈ K, (orderOf y).Prime → ∀ g ∈ M, g ∈ normalizer (S : Set X) →
      g * y * g⁻¹ * y⁻¹ ∈ S → ∃ s ∈ S, s * g ∈ normalizer (K : Set X))
    (h4 : ∀ g ∈ M, g ∈ normalizer (S : Set X) → (∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ S) →
      ∃ k ∈ K, ∃ s ∈ S, g = k * s)
    (h5 : n = 3 → ∀ p a : ℕ, p.Prime → p ≠ 2 → 0 < a → p ^ a ∣ Nat.card M → p ^ a % 7 ≠ 1) :
    ∀ g ∈ M, g ∈ normalizer (S : Set X) → g * u * g⁻¹ * u⁻¹ ∈ V := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : Subgroup X, N = M ⊓ normalizer (S : Set X) := ⟨_, rfl⟩
  have hmemN : ∀ g : X, g ∈ N ↔ g ∈ M ∧ g ∈ normalizer (S : Set X) := fun g => by
    rw [hN, mem_inf]
  have hNM : N ≤ M := fun g hg => ((hmemN g).1 hg).1
  have hNS : N ≤ normalizer (S : Set X) := fun g hg => ((hmemN g).1 hg).2
  have hSM : S ≤ M := hS.le
  have hSN : S ≤ N := fun s hs => (hmemN s).2 ⟨hSM hs, Subgroup.le_normalizer hs⟩
  have hKN : K ≤ N := fun k hk => (hmemN k).2 ⟨hKM hk, hKS hk⟩
  have hMV : ∀ g ∈ M, g ∈ normalizer (V : Set X) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro v
    refine ⟨fun hv => hVn g hg v hv, fun hv => ?_⟩
    have h := hVn g⁻¹ (M.inv_mem hg) _ hv
    have e : g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v := by group
    rwa [e] at h
  have hNV : N ≤ normalizer (V : Set X) := fun g hg => hMV g (hNM hg)
  have hSV : S ≤ normalizer (V : Set X) := fun s hs => hMV s (hSM hs)
  have hVnorm : (V.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hVS).2 hSV
  have hSnorm : (S.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hSN).2 hNS
  obtain ⟨ρ₀, hA⟩ := weak149_exists_action hNS hNV hSV
  have hker : S.subgroupOf N ≤ ρ₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    ext w
    induction w using QuotientGroup.induction_on with
    | H s =>
      rw [MulAut.one_apply]
      exact (hA x s).2 (hSab _ (mem_subgroupOf.1 hx) s s.2).1
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (N ⧸ S.subgroupOf N) →* MulAut (S ⧸ V.subgroupOf S),
      ∀ x : N, ρ (x : N ⧸ S.subgroupOf N) = ρ₀ x :=
    ⟨QuotientGroup.lift _ ρ₀ hker, fun x => QuotientGroup.lift_mk _ hker x⟩
  have hSylN : ABGLocalTools.IsSylowOf 2 S N := hS.of_le hSN hNM
  have hodd : Odd (Nat.card (N ⧸ S.subgroupOf N)) := by
    have h := (ABGLocalTools.isSylowOf_iff.1 hSylN).2.2
    rw [Nat.odd_iff]
    have e : Nat.card (N ⧸ S.subgroupOf N) = S.relIndex N := (Subgroup.index_eq_card _).symm
    rw [e]
    omega
  have hsq : ∀ w : S ⧸ V.subgroupOf S, w * w = 1 := by
    intro w
    induction w using QuotientGroup.induction_on with
    | H s =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact (hSab s s.2 s s.2).2
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    induction g using QuotientGroup.induction_on with
    | H x =>
      rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
      rw [hρ] at hg
      refine h1 x (hNM x.2) (hNS x.2) fun s hs => (hA x ⟨s, hs⟩).1 ?_
      rw [hg, MulAut.one_apply]
  have hW : Nat.card (S ⧸ V.subgroupOf S) = 2 ^ (2 * n + 1) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf S)
    have hV : Nat.card (V.subgroupOf S) = Nat.card V :=
      Nat.card_congr (subgroupOfEquivOfLe hVS).toEquiv
    rw [hV, hcard] at h
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h).symm
  obtain ⟨φ, hφ⟩ : ∃ φ : K →* (N ⧸ S.subgroupOf N),
      ∀ k : K, φ k = ((⟨k, hKN k.2⟩ : N) : N ⧸ S.subgroupOf N) :=
    ⟨(QuotientGroup.mk' (S.subgroupOf N)).comp (inclusion hKN), fun _ => rfl⟩
  have hKodd : Odd (Nat.card K) := by
    rw [hKcard]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    rw [hφ, QuotientGroup.eq_one_iff, mem_subgroupOf] at hk
    exact Subtype.ext (weak149_eq_one_of_mem hS.isPGroup hKodd k.2 hk)
  have hK'card : Nat.card φ.range = 2 ^ n - 1 := by
    rw [← hKcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
  have hord : ∀ k : K, orderOf (φ k) = orderOf (k : X) := fun k => by
    rw [Subgroup.orderOf_coe, orderOf_injective φ hφinj k]
  have hū : ((⟨u, huS⟩ : S) : S ⧸ V.subgroupOf S) ≠ 1 := fun h =>
    huV (mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h))
  have hfix : ∀ y ∈ φ.range, ρ y ((⟨u, huS⟩ : S) : S ⧸ V.subgroupOf S) =
      ((⟨u, huS⟩ : S) : S ⧸ V.subgroupOf S) := by
    rintro _ ⟨k, rfl⟩
    rw [hφ, hρ]
    refine (hA _ ⟨u, huS⟩).2 ?_
    show (k : X) * u * (k : X)⁻¹ * u⁻¹ ∈ V
    have e : (k : X) * u * (k : X)⁻¹ * u⁻¹ = 1 := by
      rw [hKu k k.2]
      group
    rw [e]
    exact V.one_mem
  have hprime : ∀ y ∈ φ.range, (orderOf y).Prime → ∀ w : S ⧸ V.subgroupOf S, ρ y w = w →
      w = 1 ∨ w = ((⟨u, huS⟩ : S) : S ⧸ V.subgroupOf S) := by
    rintro _ ⟨k, rfl⟩ hpr w hw
    induction w using QuotientGroup.induction_on with
    | H s =>
      rw [hord] at hpr
      rw [hφ, hρ] at hw
      have hc := V.inv_mem ((hA _ s).1 hw)
      have e : (s : X) * (k : X) * (s : X)⁻¹ * (k : X)⁻¹ =
          ((k : X) * s * (k : X)⁻¹ * (s : X)⁻¹)⁻¹ := by group
      have hc' : (s : X) * (k : X) * (s : X)⁻¹ * (k : X)⁻¹ ∈ V := by
        rw [e]
        exact hc
      rcases h2 k k.2 hpr s s.2 hc' with hv | hv
      · left
        rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
        exact hv
      · right
        rw [QuotientGroup.eq, mem_subgroupOf]
        show (s : X)⁻¹ * u ∈ V
        have hu' := (mem_normalizer_iff.1 (hSV (S.inv_mem huS)) ((s : X) * u⁻¹)).1 hv
        have e2 : (s : X)⁻¹ * u = (u⁻¹ * ((s : X) * u⁻¹) * u⁻¹⁻¹)⁻¹ := by group
        rw [e2]
        exact V.inv_mem hu'
  have hcomm : ∀ x y : N, (x : N ⧸ S.subgroupOf N) * y = y * x →
      (x : X) * y * (x : X)⁻¹ * (y : X)⁻¹ ∈ S := by
    intro x y hxy
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf] at hxy
    have hxy' : ((x : X) * y)⁻¹ * ((y : X) * x) ∈ S := hxy
    have e : (x : X) * y * (x : X)⁻¹ * (y : X)⁻¹ =
        ((x : X) * y) * (((x : X) * y)⁻¹ * ((y : X) * x))⁻¹ * ((x : X) * y)⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 (hNS (N.mul_mem x.2 y.2)) _).1 (S.inv_mem hxy')
  have hconj : ∀ x : N, (x : X) ∈ normalizer (K : Set X) →
      (x : N ⧸ S.subgroupOf N) ∈ normalizer (φ.range : Set (N ⧸ S.subgroupOf N)) := by
    have key : ∀ x : N, (x : X) ∈ normalizer (K : Set X) → ∀ y ∈ φ.range,
        (x : N ⧸ S.subgroupOf N) * y * (x : N ⧸ S.subgroupOf N)⁻¹ ∈ φ.range := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := hy
      refine ⟨⟨(x : X) * k * (x : X)⁻¹, (mem_normalizer_iff.1 hx k).1 k.2⟩, ?_⟩
      rw [hφ, hφ, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    refine ⟨fun hy => key x hx y hy, fun hy => ?_⟩
    have hx' : ((x⁻¹ : N) : X) ∈ normalizer (K : Set X) := by
      rw [Subgroup.coe_inv]
      exact (normalizer (K : Set X)).inv_mem hx
    have h := key x⁻¹ hx' _ hy
    have e : ((x⁻¹ : N) : N ⧸ S.subgroupOf N) * ((x : N ⧸ S.subgroupOf N) * y *
        (x : N ⧸ S.subgroupOf N)⁻¹) * ((x⁻¹ : N) : N ⧸ S.subgroupOf N)⁻¹ = y := by
      rw [QuotientGroup.mk_inv]
      group
    rwa [e] at h
  have hnormK : ∀ y ∈ φ.range, (orderOf y).Prime →
      centralizer ({y} : Set (N ⧸ S.subgroupOf N)) ≤
        normalizer (φ.range : Set (N ⧸ S.subgroupOf N)) := by
    rintro _ ⟨k, rfl⟩ hpr g' hg'
    induction g' using QuotientGroup.induction_on with
    | H g =>
      rw [hord] at hpr
      have hcg := mem_centralizer_singleton_iff.1 hg'
      rw [hφ] at hcg
      obtain ⟨s, hs, hsg⟩ := h3 k k.2 hpr g (hNM g.2) (hNS g.2) (hcomm g ⟨k, hKN k.2⟩ hcg)
      have hsN : s ∈ N := hSN hs
      have hmk : ((⟨s, hsN⟩ * g : N) : N ⧸ S.subgroupOf N) = g := by
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (⟨s, hsN⟩ : N)).2 (mem_subgroupOf.2 hs),
          one_mul]
      rw [← hmk]
      exact hconj _ hsg
  have hcentK : centralizer (φ.range : Set (N ⧸ S.subgroupOf N)) ≤ φ.range := by
    intro g' hg'
    induction g' using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨k₀, hk₀, s, hs, hgks⟩ := h4 g (hNM g.2) (hNS g.2) fun k hk => by
        have hc := mem_centralizer_iff.1 hg' (φ ⟨k, hk⟩) ⟨⟨k, hk⟩, rfl⟩
        rw [hφ] at hc
        exact hcomm g ⟨k, hKN hk⟩ hc.symm
      refine ⟨⟨k₀, hk₀⟩, ?_⟩
      rw [hφ]
      have hsN : s ∈ N := hSN hs
      have hmk : (g : N ⧸ S.subgroupOf N) = ((⟨k₀, hKN hk₀⟩ : N) : N ⧸ S.subgroupOf N) *
          ((⟨s, hsN⟩ : N) : N ⧸ S.subgroupOf N) := by
        rw [← QuotientGroup.mk_mul]
        exact congrArg _ (Subtype.ext hgks)
      rw [hmk, (QuotientGroup.eq_one_iff (⟨s, hsN⟩ : N)).2 (mem_subgroupOf.2 hs), mul_one]
  have hGN : Nat.card (N ⧸ S.subgroupOf N) ∣ Nat.card N :=
    ⟨Nat.card (S.subgroupOf N), Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩
  have h5' : n = 3 → ∀ p a : ℕ, p.Prime → 0 < a → p ^ a ∣ Nat.card (N ⧸ S.subgroupOf N) →
      p ^ a % 7 ≠ 1 := by
    intro hn3 p a hp ha hdvd
    have hp2 : p ≠ 2 := by
      rintro rfl
      have h2d : 2 ∣ Nat.card (N ⧸ S.subgroupOf N) := (dvd_pow_self 2 ha.ne').trans hdvd
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2d)
    exact h5 hn3 p a hp hp2 ha (hdvd.trans (hGN.trans (Subgroup.card_dvd_of_le hNM)))
  have key := hF ρ φ.range ((⟨u, huS⟩ : S) : S ⧸ V.subgroupOf S) n hodd hsq hinj hn hW hK'card
    hū hfix hprime hnormK hcentK h5'
  intro g hgM hgS
  have hgN : g ∈ N := (hmemN g).2 ⟨hgM, hgS⟩
  have hg := key ((⟨g, hgN⟩ : N) : N ⧸ S.subgroupOf N)
  rw [hρ] at hg
  exact (hA ⟨g, hgN⟩ ⟨u, huS⟩).1 hg

theorem weak149 (hF : Frob149Stmt) : Weak149Stmt := by
  intro X _ _ M V S K u n _ hVn hVS hS hSab hn hcard huS huV hKM hKS hKcard hKu h1 h2 h3 h4 h5
  exact weak149_reduction hVn hS (fun x hx y hy => (hSab x hx y hy).1) huS
    (weak149_core hF hVn hVS hS hSab hn hcard huS huV hKM hKS hKcard hKu h1 h2 h3 h4 h5)

end CFSG.GH74.Uniqueness
