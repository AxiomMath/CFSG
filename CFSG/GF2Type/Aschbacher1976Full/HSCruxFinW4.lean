module

public import CFSG.GF2Type.Aschbacher1976Full.HSCruxFinW3
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.FinW

section Generic

variable {G : Type*} [Group G]

theorem sq_ne_one {a : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) : a ^ 2 ≠ 1 := by
  intro h
  apply ha1
  have h' : a ^ 3 = a * a ^ 2 := pow_succ' a 2
  rw [h, mul_one] at h'
  exact h'.symm.trans ha3

theorem sq_notMem {c : G} {H : Subgroup G} (hc3 : c ^ 3 = 1) (hcz : c ∉ H) : c ^ 2 ∉ H := by
  intro h
  apply hcz
  have h4 : (c ^ 2) ^ 2 = c := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hc3, one_mul]
  rw [← h4]
  exact Subgroup.pow_mem _ h 2

theorem exists_gen_pair (key : G → ℕ) (N : Subgroup G) [Finite N] (hN : Nat.card N = 9)
    (hp3 : ∀ n ∈ N, n ^ 3 = 1) :
    ∃ a ∈ N, ∃ c ∈ N, a ≠ 1 ∧ c ∉ Subgroup.zpowers a ∧
      (∀ n ∈ N, n ≠ 1 → key a ≤ key n) ∧ (∀ n ∈ N, n ∉ Subgroup.zpowers a → key c ≤ key n) := by
  have hfinS : ∀ P : G → Prop, {n | n ∈ N ∧ P n}.Finite := fun P =>
    (Set.toFinite (N : Set G)).subset (fun n hn => hn.1)
  obtain ⟨n0, hn0, hn01⟩ : ∃ n ∈ N, n ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have := (Subgroup.eq_bot_iff_card N).1 ((Subgroup.eq_bot_iff_forall N).2 hcon)
    omega
  obtain ⟨a, ⟨haN, ha1⟩, hamin⟩ :=
    Set.exists_min_image {n | n ∈ N ∧ n ≠ 1} key (hfinS _) ⟨n0, hn0, hn01⟩
  obtain ⟨n1, hn1N, hn1z⟩ : ∃ n ∈ N, n ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have heq : Subgroup.zpowers a = N :=
      le_antisymm (Subgroup.zpowers_le.2 haN) (fun n hn => hcon n hn)
    have hcard : Nat.card N = orderOf a := by rw [← heq, Nat.card_zpowers]
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hp3 a haN))
    omega
  obtain ⟨c, ⟨hcN, hcz⟩, hcmin⟩ :=
    Set.exists_min_image {n | n ∈ N ∧ n ∉ Subgroup.zpowers a} key (hfinS _) ⟨n1, hn1N, hn1z⟩
  exact ⟨a, haN, c, hcN, ha1, hcz, fun n hn hn1 => hamin n ⟨hn, hn1⟩,
    fun n hn hnz => hcmin n ⟨hn, hnz⟩⟩

theorem prod_surj (N : Subgroup G) [Finite N] (hN : Nat.card N = 9) {a c : G} (ha : a ∈ N)
    (hc : c ∈ N)
    (hinj : ∀ p < 9, ∀ p' < 9, a ^ (p / 3) * c ^ (p % 3) = a ^ (p' / 3) * c ^ (p' % 3) → p = p') :
    ∀ n ∈ N, ∃ p < 9, n = a ^ (p / 3) * c ^ (p % 3) := by
  let f : Fin 9 → N := fun p => ⟨a ^ ((p : ℕ) / 3) * c ^ ((p : ℕ) % 3),
    N.mul_mem (N.pow_mem ha _) (N.pow_mem hc _)⟩
  have hf : Function.Injective f := fun p p' h =>
    Fin.ext (hinj p p.2 p' p'.2 (congrArg Subtype.val h))
  have hbij := hf.bijective_of_nat_card_le (by simp [hN])
  intro n hn
  obtain ⟨p, hp⟩ := hbij.2 ⟨n, hn⟩
  exact ⟨p, p.2, (congrArg Subtype.val hp).symm⟩

end Generic

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def FreeVec (N : Subgroup (V ≃ₗ[ZMod 2] V)) (x : V) : Prop :=
  ∀ n ∈ N, n ≠ 1 → n x ≠ x

open Classical in
@[expose] noncomputable def qOf (N : Subgroup (V ≃ₗ[ZMod 2] V)) (x : V) : ZMod 2 :=
  if x = 0 ∨ FreeVec N x then 0 else 1

theorem conj_inv_mem {N : Subgroup (V ≃ₗ[ZMod 2] V)} [Finite N] {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ n ∈ N, g * n * g⁻¹ ∈ N) : ∀ n ∈ N, g⁻¹ * n * g ∈ N := by
  have hinj : Function.Injective (fun m : N => (⟨g * m * g⁻¹, hg m m.2⟩ : N)) := by
    intro m m' h
    have h' : g * (m : V ≃ₗ[ZMod 2] V) * g⁻¹ = g * (m' : V ≃ₗ[ZMod 2] V) * g⁻¹ :=
      congrArg Subtype.val h
    exact Subtype.ext (by simpa using h')
  intro n hn
  obtain ⟨m, hm⟩ := Finite.surjective_of_injective hinj ⟨n, hn⟩
  have h1 : g * (m : V ≃ₗ[ZMod 2] V) * g⁻¹ = n := congrArg Subtype.val hm
  have h2 : g⁻¹ * n * g = m := by rw [← h1]; group
  rw [h2]
  exact m.2

theorem freeVec_map {N : Subgroup (V ≃ₗ[ZMod 2] V)} [Finite N] {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ n ∈ N, g * n * g⁻¹ ∈ N) {x : V} (hx : FreeVec N x) : FreeVec N (g x) := by
  intro n hn hn1 hfix
  have hm : g⁻¹ * n * g ∈ N := conj_inv_mem hg n hn
  have hm1 : g⁻¹ * n * g ≠ 1 := by
    intro h
    apply hn1
    have h' : g * (g⁻¹ * n * g) * g⁻¹ = g * 1 * g⁻¹ := by rw [h]
    simpa [mul_assoc] using h'
  apply hx _ hm hm1
  simp only [LinearEquiv.mul_apply]
  rw [hfix]
  exact g.symm_apply_apply x

theorem qOf_map {N : Subgroup (V ≃ₗ[ZMod 2] V)} [Finite N] {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ n ∈ N, g * n * g⁻¹ ∈ N) (x : V) : qOf N (g x) = qOf N x := by
  have hg' : ∀ n ∈ N, g⁻¹ * n * g⁻¹⁻¹ ∈ N := by
    intro n hn
    simpa using conj_inv_mem hg n hn
  have h0 : g x = 0 ↔ x = 0 :=
    ⟨fun h => g.injective (h.trans (map_zero g).symm), fun h => by rw [h, map_zero]⟩
  have hf : FreeVec N (g x) ↔ FreeVec N x := by
    refine ⟨fun h => ?_, freeVec_map hg⟩
    have := freeVec_map hg' h
    simpa using this
  unfold qOf
  by_cases hx : x = 0 ∨ FreeVec N x
  · rw [if_pos (hx.imp h0.2 hf.2), if_pos hx]
  · rw [if_neg (fun h => hx (h.imp h0.1 hf.1)), if_neg hx]

theorem getD_range_map (f : ℕ → ℕ) {z : ℕ} (hz : z < 16) :
    ((List.range 16).map f).getD z 0 = f z := by
  simp [List.getD_eq_getElem?_getD, hz]

section Core

variable (bs : Module.Basis (Fin 2 ⊕ Fin 2) (ZMod 2) V) (β : LinearMap.BilinForm (ZMod 2) V)
  (h1 : ∀ i j, β (bs (.inl i)) (bs (.inl j)) = 0) (h2 : ∀ i j, β (bs (.inr i)) (bs (.inr j)) = 0)
  (h3 : ∀ i j, β (bs (.inl i)) (bs (.inr j)) = if i = j then 1 else 0) (halt : β.IsAlt)
  (N : Subgroup (V ≃ₗ[ZMod 2] V)) (hN : Nat.card N = 9)
  (hiso : ∀ g ∈ N, ∀ x y : V, β (g x) (g y) = β x y)

include h1 h2 h3 halt hN hiso

theorem pow_three_eq_one : ∀ n ∈ N, n ^ 3 = 1 := by
  intro n hn
  haveI := finite_aut bs
  have h9 : n ^ 9 = 1 := by
    have h := pow_card_eq_one' (G := N) (x := ⟨n, hn⟩)
    rw [hN] at h
    exact congrArg Subtype.val h
  have hx : ∀ x < 16, apN (tupOf bs n) 9 x = x := by
    intro x hx
    obtain ⟨y, rfl⟩ := cc_surj bs hx
    rw [← cc_pow, h9]
    rfl
  have h3' := exp_three _ (tupOf_mem_L bs β h1 h2 h3 halt n (hiso n hn)) hx
  refine LinearEquiv.ext fun y => cc_inj bs ?_
  rw [cc_pow]
  exact h3' _ (cc_lt bs y)

theorem qOf_quad (x y : V) : qOf N (x + y) = qOf N x + qOf N y + β x y := by
  haveI := finite_aut bs
  have hp3 := pow_three_eq_one bs β h1 h2 h3 halt N hN hiso
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, haN, c, hcN, ha1, hcz, hamin, hcmin⟩ :=
    exists_gen_pair (fun g => keyT (tupOf bs g)) N hN hp3
  have hcomm : a * c = c * a :=
    congrArg Subtype.val ((IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := N) (p := 3)
      (by rw [hN]; norm_num)).is_comm.comm ⟨a, haN⟩ ⟨c, hcN⟩)
  have ha3 := hp3 a haN
  have hc3 := hp3 c hcN
  have hc1 : c ≠ 1 := fun h => hcz (h ▸ Subgroup.one_mem _)
  have hpair : PairHyp (tupOf bs a) (tupOf bs c) :=
    pairHyp_tupOf bs a c (fun h => hcz (h ▸ Subgroup.mem_zpowers a))
      (fun h => hcz (h ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 2)) hcomm
      (hamin (a ^ 2) (N.pow_mem haN 2) (sq_ne_one ha3 ha1))
      (hcmin (c ^ 2) (N.pow_mem hcN 2) (sq_notMem hc3 hcz)) (hamin c hcN hc1)
  obtain ⟨hdist, hquad⟩ := pairs_ok _ (tupOf_mem_L3 bs β h1 h2 h3 halt a (hiso a haN) ha3 ha1) _
    (tupOf_mem_L3 bs β h1 h2 h3 halt c (hiso c hcN) hc3 hc1) hpair
  have hprod := prod_surj N hN haN hcN fun p hp p' hp' h => by
    by_contra hne
    obtain ⟨w, hw, hd⟩ := hdist p hp p' hp' hne
    obtain ⟨z, rfl⟩ := cc_surj bs hw
    exact hd (by rw [← cc_prod, ← cc_prod, h])
  have hfree : ∀ z : V, FreeVec N z ↔ FreeC (tupOf bs a) (tupOf bs c) (cc bs z) := by
    intro z
    constructor
    · intro hz p hp hp0 hfix
      have hn : a ^ (p / 3) * c ^ (p % 3) ∈ N := N.mul_mem (N.pow_mem haN _) (N.pow_mem hcN _)
      have hn1 : a ^ (p / 3) * c ^ (p % 3) ≠ 1 := by
        intro h1'
        obtain ⟨w, hw, hd⟩ := hdist p hp 0 (by norm_num) hp0
        obtain ⟨u, rfl⟩ := cc_surj bs hw
        apply hd
        rw [← cc_prod, h1']
        rfl
      refine hz _ hn hn1 (cc_inj bs ?_)
      rw [cc_prod]
      exact hfix
    · intro hz n hn hn1 hfix
      obtain ⟨p, hp, rfl⟩ := hprod n hn
      have hp0 : p ≠ 0 := by
        rintro rfl
        exact hn1 (by simp)
      exact hz p hp hp0 (by rw [← cc_prod, hfix])
  have hq := hquad (cc bs x) (cc_lt bs x) (cc bs y) (cc_lt bs y)
  rw [← cc_add, getD_range_map _ (cc_lt bs _), getD_range_map _ (cc_lt bs _),
    getD_range_map _ (cc_lt bs _), bf_cc bs β h1 h2 h3 halt] at hq
  have hQ : ∀ z : V, ((Qc (tupOf bs a) (tupOf bs c) (cc bs z) : ℕ) : ZMod 2) = qOf N z := by
    intro z
    unfold qOf Qc
    by_cases hz : z = 0 ∨ FreeVec N z
    · have h' : cc bs z = 0 ∨ FreeC (tupOf bs a) (tupOf bs c) (cc bs z) :=
        hz.imp (fun h => (cc_eq_zero_iff bs).2 h) (fun h => (hfree z).1 h)
      rw [if_pos h', if_pos hz]
      simp
    · have h' : ¬ (cc bs z = 0 ∨ FreeC (tupOf bs a) (tupOf bs c) (cc bs z)) := fun h =>
        hz (h.imp (fun h => (cc_eq_zero_iff bs).1 h) (fun h => (hfree z).2 h))
      rw [if_neg h', if_neg hz]
      simp
  have hq' := congrArg (fun m : ℕ => (m : ZMod 2)) hq
  simp only [Nat.cast_add, ZMod.natCast_mod, ZMod.natCast_zmod_val] at hq'
  rwa [hQ, hQ, hQ] at hq'

theorem finW_core :
    ∃ q : V → ZMod 2, q 0 = 0 ∧ (∀ x y : V, q (x + y) = q x + q y + β x y) ∧
      (∀ g : V ≃ₗ[ZMod 2] V, (∀ x y : V, β (g x) (g y) = β x y) → (∀ n ∈ N, g * n * g⁻¹ ∈ N) →
        ∀ x : V, q (g x) = q x) ∧
      ∀ v : V, v ≠ 0 → (∀ n ∈ N, n ≠ 1 → n v ≠ v) → q v = 0 := by
  haveI := finite_aut bs
  refine ⟨qOf N, ?_, qOf_quad bs β h1 h2 h3 halt N hN hiso, fun g _ hg x => qOf_map hg x, ?_⟩
  · unfold qOf
    rw [if_pos (Or.inl rfl)]
  · intro v _ hv
    unfold qOf
    rw [if_pos (Or.inr (show FreeVec N v from hv))]

end Core

end CFSG.GF2Type.Aschbacher1976Full.HS.FinW
