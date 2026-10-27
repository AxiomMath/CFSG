module

public import CFSG.GH74.Generic.S45.LAltPerm
public import CFSG.GH74.Generic.S45.LAltLift
public import CFSG.GH74.Generic.S45.LAltCover

public section

namespace CFSG.GH74.Generic.S45.LAlt

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.PerfectAutomorphisms
open scoped commutatorElement

section Setup

variable {K : Type} [Group K] {n : ℕ}

@[expose] noncomputable def projAlt (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    K →* alternatingGroup (Fin n) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))

theorem projAlt_surjective (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    Function.Surjective (projAlt e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem ker_projAlt (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    (projAlt e).ker = Subgroup.center K := by
  rw [projAlt, MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

theorem exists_induced (hKp : Group.IsPerfect K) (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (y : MulAut K) (hy : orderOf y = 2) :
    ∃ yb : MulAut (alternatingGroup (Fin n)),
      (∀ k : K, projAlt e (y k) = yb (projAlt e k)) ∧ yb ≠ 1 ∧ yb * yb = 1 := by
  have : Group.IsPerfect K := hKp
  refine ⟨MulAut.congr e (centerQuotientHom K y), fun k => ?_, ?_, ?_⟩
  · show e (QuotientGroup.mk' (Subgroup.center K) (y k)) =
      (MulAut.congr e (centerQuotientHom K y)) (e (QuotientGroup.mk' (Subgroup.center K) k))
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    congr 1
  · intro h
    have h1 : centerQuotientHom K y = 1 :=
      (MulAut.congr e).injective (h.trans (map_one (MulAut.congr e)).symm)
    have h2 : y = 1 := onCenterQuotient_eq_one_imp y h1
    rw [h2, orderOf_one] at hy
    omega
  · have hyy : y * y = 1 := by
      have := pow_orderOf_eq_one y
      rw [hy, pow_two] at this
      exact this
    rw [← map_mul, ← map_mul, hyy, map_one, map_one]

theorem inj_restrict {A : Type} [Group A] (π : K →* A) (hker : π.ker = Subgroup.center K)
    {L : Subgroup K} (hLs : IsSimpleGroup ↥L) (hLnab : ∃ a b : ↥L, a * b ≠ b * a) :
    Function.Injective (π.comp L.subtype) := by
  intro a b hab
  have hπab : π a = π b := hab
  have hc : (a : K)⁻¹ * b ∈ Subgroup.center K := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hπab, inv_mul_cancel]
  have hmem : a⁻¹ * b ∈ (Subgroup.center K).subgroupOf L := by
    rw [Subgroup.mem_subgroupOf]
    exact hc
  rcases hLs.eq_bot_or_eq_top_of_normal ((Subgroup.center K).subgroupOf L) with h | h
  · rw [h, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem
  · exfalso
    obtain ⟨u, v, huv⟩ := hLnab
    have hu : (u : K) ∈ Subgroup.center K := by
      have : u ∈ (Subgroup.center K).subgroupOf L := h ▸ Subgroup.mem_top u
      exact this
    exact huv (Subtype.ext ((Subgroup.mem_center_iff.mp hu) v).symm)

end Setup

theorem isPerfect_of_simple_nonab {F : Type} [Group F] (hs : IsSimpleGroup F)
    (hnab : ∃ a b : F, a * b ≠ b * a) : Group.IsPerfect F := by
  refine ⟨?_⟩
  rcases hs.eq_bot_or_eq_top_of_normal (commutator F) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (((commutator_eq_bot_iff F).1 h).is_comm.comm a b)
  · exact h

theorem simple_dichotomy {G : Type*} [Group G] {Lb : Subgroup G} (hs : IsSimpleGroup ↥Lb) :
    ∀ N : Subgroup G, N ≤ Lb → (∀ g ∈ Lb, ∀ h ∈ N, g * h * g⁻¹ ∈ N) → N = ⊥ ∨ N = Lb := by
  intro N hNle hNn
  have hnorm : (N.subgroupOf Lb).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNn g g.2 n hn
  rcases hs.eq_bot_or_eq_top_of_normal (N.subgroupOf Lb) with h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact disjoint_self.1 (h.mono_right hNle)
  · right
    rw [Subgroup.subgroupOf_eq_top] at h
    exact le_antisymm hNle h

theorem sq_eq_one_of_card_le_two {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 2) (g : G) :
    g ^ 2 = 1 := by
  have hcard := pow_card_eq_one' (G := G) (x := g)
  have hpos : 0 < Nat.card G := Nat.card_pos
  interval_cases hc : Nat.card G
  · have : g = 1 := by simpa using hcard
    rw [this, one_pow]
  · exact hcard

theorem no_order_four_alt5 (g : Perm (Fin 5)) (hg : g ∈ alternatingGroup (Fin 5)) :
    orderOf g ≠ 4 := by
  have key : ∀ g : Perm (Fin 5), Perm.sign g = 1 → g ^ 4 = 1 → g ^ 2 = 1 := by
    decide +kernel
  intro h4
  have h1 : g ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one g
  have h2 := key g (Perm.mem_alternatingGroup.1 hg) h1
  have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [h4] at this
  omega

theorem alt_core {K : Type} [Group K] [Finite K] (hKp : Group.IsPerfect K) {n : ℕ}
    (hn : n = 5 ∨ 7 ≤ n) (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (hz2 : IsPGroup 2 (Subgroup.center K)) (y : MulAut K) (hy : orderOf y = 2)
    (L : Subgroup K) (hLfix : ∀ l ∈ L, y l = l) (hLs : IsSimpleGroup ↥L)
    (hLnab : ∃ a b : ↥L, a * b ≠ b * a) (hLinv : ∃ v ∈ L, orderOf v = 2)
    (hno4 : ∀ m : K, y m = m → ¬ 4 ∣ orderOf m) : False := by
  classical
  have : Group.IsPerfect K := hKp
  obtain ⟨yb, hπy, hyb1, hyb2⟩ := exists_induced hKp e y hy
  obtain ⟨σ, hσ2, hσ1, hσyb⟩ := exists_sigma hn yb hyb1 hyb2
  have hπsurj := projAlt_surjective e
  have hπker := ker_projAlt e
  set π := projAlt e with hπdef
  have hπσ : ∀ k : K, ((π (y k) : alternatingGroup (Fin n)) : Perm (Fin n)) =
      σ * (π k : Perm (Fin n)) * σ⁻¹ := fun k => by rw [hπy, hσyb]
  let ψ : K →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp π
  have hψk : ∀ k, ψ k = (π k : Perm (Fin n)) := fun k => rfl
  have hψσ : ∀ k, ψ (y k) = σ * ψ k * σ⁻¹ := fun k => hπσ k
  have hψker : ψ.ker = Subgroup.center K := by
    rw [← hπker]
    exact MonoidHom.ker_comp_of_injective π (alternatingGroup (Fin n)).subtype
      (alternatingGroup (Fin n)).subtype_injective
  have hLinj : Function.Injective (π.comp L.subtype) := inj_restrict π hπker hLs hLnab
  have hφ : Function.Injective (ψ.comp L.subtype) := fun a b hab =>
    hLinj (Subtype.ext hab)
  let Lb : Subgroup (Perm (Fin n)) := L.map ψ
  have hLbc : Lb ≤ centAlt σ := by
    rintro _ ⟨l, hl, rfl⟩
    rw [mem_centAlt]
    refine ⟨(π l).2, ?_⟩
    have h1 := hψσ l
    rw [hLfix l hl] at h1
    calc ψ l * σ = (σ * ψ l * σ⁻¹) * σ := by rw [← h1]
      _ = σ * ψ l := by group
  have hLperf : ⁅L, L⁆ = L :=
    Subgroup.isPerfect_iff.1 (isPerfect_of_simple_nonab hLs hLnab)
  have hLbperf : ⁅Lb, Lb⁆ = Lb := by
    rw [← Subgroup.map_commutator, hLperf]
  let eL : ↥L ≃* ↥Lb :=
    MulEquiv.ofBijective (ψ.subgroupMap L)
      ⟨fun a b hab => hφ (by
        have h1 := Subtype.ext_iff.1 hab
        exact h1), ψ.subgroupMap_surjective L⟩
  have hLbs : IsSimpleGroup ↥Lb := (MulEquiv.isSimpleGroup_congr eL).1 hLs
  have hLbd := simple_dichotomy hLbs
  obtain ⟨v, hvL, hv2⟩ := hLinv
  have hv₀mem : ψ v ∈ Lb := ⟨v, hvL, rfl⟩
  have hv₀ord : orderOf (ψ v) = 2 := by
    have h1 := orderOf_injective (ψ.comp L.subtype) hφ ⟨v, hvL⟩
    rw [Subgroup.orderOf_mk] at h1
    rw [← hv2]
    exact h1
  obtain ⟨⟨g, hg, hord4⟩, X, hXle, hXperf, g', hg'X, hg'⟩ :=
    badCent_of_simple hσ2 hσ1 hLbc hLbperf hLbd hv₀mem hv₀ord
  rcases hn with rfl | hn7
  · exact no_order_four_alt5 g (mem_centAlt.1 hg).1 hord4
  by_cases hZ : Subgroup.center K = ⊥
  ·
    have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 (by rw [hπker]; exact hZ)
    obtain ⟨hgA, hgσ⟩ := mem_centAlt.1 hg
    obtain ⟨k, hk⟩ := hπsurj ⟨g, hgA⟩
    have hyk : y k = k := by
      apply hinj
      apply Subtype.ext
      rw [hπσ k, hk]
      show σ * g * σ⁻¹ = g
      rw [← hgσ]
      group
    have h4 : 4 ∣ orderOf k := by
      have h1 : orderOf (π k) = orderOf k := orderOf_injective π hinj k
      rw [← h1, hk, Subgroup.orderOf_mk, hord4]
    exact hno4 k hyk h4
  ·
    have hne : π.ker ≠ ⊥ := by rw [hπker]; exact hZ
    have hK2 : IsPGroup 2 π.ker := by rw [hπker]; exact hz2
    have hXr : X ≤ ψ.range := by
      intro x hx
      obtain ⟨hxA, -⟩ := mem_centAlt.1 (hXle hx)
      obtain ⟨k, hk⟩ := hπsurj ⟨x, hxA⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have hy' : ∀ k : K, ψ k ∈ X → ψ (y k) = ψ k := by
      intro k hk
      obtain ⟨-, hcomm⟩ := mem_centAlt.1 (hXle hk)
      rw [hψσ k, ← hcomm]
      group
    obtain ⟨D, hDX, hDsurj, hDfix⟩ :=
      exists_fixed_perfect_lift y ψ hψker.le X hXr hXperf hy'
    obtain ⟨k, hkD, hk⟩ := hDsurj g' hg'X
    have hyk : y k = k := hDfix k hkD
    rcases hg' with hord | ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hgeq⟩
    · have h4 : 4 ∣ orderOf k := by
        have h1 := orderOf_map_dvd ψ k
        rw [hk, hord] at h1
        exact h1
      exact hno4 k hyk h4
    · have hx : ((π k : alternatingGroup (Fin n)) : Perm (Fin n)) = swap a b * swap c d := by
        rw [← hgeq, ← hk]
        rfl
      have hsq := sq_ne_one_of_lift_swap_mul_swap (by omega) π hπsurj hπker.le hK2 hne
        hab hac had hbc hbd hcd hx
      have hker2 : Nat.card π.ker ≤ 2 :=
        CFSG.LocalAnalysis.ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two
          (by omega) π hπsurj hπker.le hK2
      have hnd : [a, b, c, d].Nodup := by
        simp [hab, hac, had, hbc, hbd, hcd]
      have hswsq : (swap a b * swap c d) ^ 2 = 1 := by
        have hc := (Equiv.Perm.disjoint_swap_swap hnd).commute
        rw [hc.mul_pow, pow_two, pow_two, Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]
      have hk2ker : k ^ 2 ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_pow]
        apply Subtype.ext
        rw [Subgroup.coe_pow, hx, hswsq]
        rfl
      have hk4 : (k ^ 2) ^ 2 = 1 :=
        congrArg Subtype.val (sq_eq_one_of_card_le_two hker2 (⟨k ^ 2, hk2ker⟩ : π.ker))
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hord : orderOf k = 4 := by
        have h1 : ¬ k ^ 2 ^ 1 = 1 := by simpa using hsq
        have h2 : k ^ 2 ^ (1 + 1) = 1 := by
          rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul]
          exact hk4
        simpa using orderOf_eq_prime_pow h1 h2
      exact hno4 k hyk (by rw [hord])

end CFSG.GH74.Generic.S45.LAlt
