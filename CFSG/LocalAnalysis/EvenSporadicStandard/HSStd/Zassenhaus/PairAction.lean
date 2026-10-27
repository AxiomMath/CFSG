module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.Wreath

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup Wreath

variable {G : Type*} [Group G]

@[expose] def conjAutOf (K : Subgroup G) {g : G} (hg : g ∈ normalizer (K : Set G)) :
    MulAut ↥K :=
  K.normalizerMonoidHom ⟨g, hg⟩

theorem conjAutOf_apply (K : Subgroup G) {g : G} (hg : g ∈ normalizer (K : Set G)) (k : ↥K) :
    ((conjAutOf K hg k : ↥K) : G) = g * k * g⁻¹ :=
  rfl

theorem conjAutOf_mul (K : Subgroup G) {g h : G} (hg : g ∈ normalizer (K : Set G))
    (hh : h ∈ normalizer (K : Set G)) :
    conjAutOf K (mul_mem hg hh) = conjAutOf K hg * conjAutOf K hh :=
  map_mul K.normalizerMonoidHom ⟨g, hg⟩ ⟨h, hh⟩

theorem conjAutOf_one (K : Subgroup G) (h1 : (1 : G) ∈ normalizer (K : Set G)) :
    conjAutOf K h1 = 1 :=
  map_one K.normalizerMonoidHom

theorem conjAutOf_congr (K : Subgroup G) {g g' : G} (e : g = g')
    (hg : g ∈ normalizer (K : Set G)) (hg' : g' ∈ normalizer (K : Set G)) :
    conjAutOf K hg = conjAutOf K hg' := by
  subst e; rfl

theorem conjAutOf_eq_one_iff (K : Subgroup G) {g : G} (hg : g ∈ normalizer (K : Set G)) :
    conjAutOf K hg = 1 ↔ ∀ k ∈ K, Commute g k := by
  constructor
  · intro h k hk
    have := congrArg (fun f : MulAut ↥K => ((f ⟨k, hk⟩ : ↥K) : G)) h
    simp only [conjAutOf_apply, MulAut.one_apply] at this
    exact mul_inv_eq_iff_eq_mul.1 this
  · intro h
    ext k
    rw [conjAutOf_apply, MulAut.one_apply]
    exact mul_inv_eq_iff_eq_mul.2 (h k k.2).eq

theorem map_conj_map_conj (K : Subgroup G) (g h : G) :
    (K.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      K.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one (K : Subgroup G) : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext x
  simp [Subgroup.mem_map]

theorem mem_normalizer_iff_map_eq (K : Subgroup G) (g : G) :
    g ∈ normalizer (K : Set G) ↔ K.map (MulAut.conj g).toMonoidHom = K :=
  mem_normalizer_iff_map_conj_eq

theorem map_conj_inj {K L : Subgroup G} (g : G) :
    K.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj g).toMonoidHom ↔ K = L :=
  (Subgroup.map_injective (MulEquiv.injective (MulAut.conj g))).eq_iff

open Classical in
@[expose] noncomputable def conjAutTotal (K : Subgroup G) (g : G) : MulAut ↥K :=
  if hg : g ∈ normalizer (K : Set G) then conjAutOf K hg else 1

theorem conjAutTotal_of_mem (K : Subgroup G) {g : G} (hg : g ∈ normalizer (K : Set G)) :
    conjAutTotal K g = conjAutOf K hg := by
  simp [conjAutTotal, hg]

theorem conjAutTotal_mul (K : Subgroup G) {g h : G} (hg : g ∈ normalizer (K : Set G))
    (hh : h ∈ normalizer (K : Set G)) :
    conjAutTotal K (g * h) = conjAutTotal K g * conjAutTotal K h := by
  rw [conjAutTotal_of_mem K hg, conjAutTotal_of_mem K hh,
    conjAutTotal_of_mem K (mul_mem hg hh), conjAutOf_mul]

theorem conjAutTotal_one (K : Subgroup G) : conjAutTotal K (1 : G) = 1 := by
  rw [conjAutTotal_of_mem K (one_mem _), conjAutOf_one]

theorem base_mul_tau_mul_base {A : Type*} [Group A] (a b c d : A) :
    base a b * tau * base c d = base (a * d) (b * c) * tau := by
  rw [mul_assoc, tau_mul_base, ← mul_assoc, base_mul_base]

theorem base_mul_tau_mul_base_mul_tau {A : Type*} [Group A] (a b c d : A) :
    (base a b * tau) * (base c d * tau) = base (a * d) (b * c) := by
  rw [← mul_assoc, base_mul_tau_mul_base, mul_assoc, tau_mul_tau, mul_one]

theorem mem_normalizer_of_forall_commute (K : Subgroup G) {g : G} (hc : ∀ k ∈ K, Commute g k) :
    g ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rwa [(hc x hx).mul_inv_cancel]
  · intro hx
    have h1 := (hc _ hx).eq
    have e : g * x * g⁻¹ = x := mul_left_cancel (a := g) (by rw [h1]; simp [mul_assoc])
    rwa [e] at hx

theorem conjAutOf_of_mem (K : Subgroup G) {k : G} (hk : k ∈ K)
    (hg : k ∈ normalizer (K : Set G)) : conjAutOf K hg = MulAut.conj (⟨k, hk⟩ : ↥K) := by
  ext x
  rfl

theorem commute_conj_iff (p k c : G) : Commute (c * p * c⁻¹) k ↔ Commute p (c⁻¹ * k * c) := by
  constructor
  · intro hc
    have hc' := hc.eq
    show p * (c⁻¹ * k * c) = c⁻¹ * k * c * p
    calc p * (c⁻¹ * k * c) = c⁻¹ * (c * p * c⁻¹ * k) * c := by group
      _ = c⁻¹ * (k * (c * p * c⁻¹)) * c := by rw [hc']
      _ = c⁻¹ * k * c * p := by group
  · intro hc
    have hc' := hc.eq
    show c * p * c⁻¹ * k = k * (c * p * c⁻¹)
    calc c * p * c⁻¹ * k = c * (p * (c⁻¹ * k * c)) * c⁻¹ := by group
      _ = c * (c⁻¹ * k * c * p) * c⁻¹ := by rw [hc']
      _ = k * (c * p * c⁻¹) := by group

structure PairData (P K : Subgroup G) (t : G) : Prop where
  t_mem : t ∈ P
  t_sq : t * t = 1
  K_le : K ≤ P
  ne : K.map (MulAut.conj t).toMonoidHom ≠ K
  comm : ∀ a ∈ K, ∀ b ∈ K, Commute a (t * b * t⁻¹)
  perm : ∀ p ∈ P, K.map (MulAut.conj p).toMonoidHom = K ∨
    K.map (MulAut.conj p).toMonoidHom = K.map (MulAut.conj t).toMonoidHom

namespace PairData

variable {P K : Subgroup G} {t : G} (h : PairData P K t)

include h

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq

theorem map_conj_conj_of_normalizes {p : G} (hpP : p ∈ P) (hp : p ∈ normalizer (K : Set G)) :
    (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj p).toMonoidHom =
      K.map (MulAut.conj t).toMonoidHom := by
  rw [map_conj_map_conj]
  rcases h.perm (p * t) (mul_mem hpP h.t_mem) with h1 | h1
  · exfalso
    apply h.ne
    apply (map_conj_inj p).1
    rw [map_conj_map_conj, h1]
    exact ((mem_normalizer_iff_map_eq K p).1 hp).symm
  · exact h1

theorem map_conj_conj_of_swaps {p : G} (hpP : p ∈ P)
    (hp : K.map (MulAut.conj p).toMonoidHom = K.map (MulAut.conj t).toMonoidHom) :
    (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj p).toMonoidHom = K := by
  rw [map_conj_map_conj]
  rcases h.perm (p * t) (mul_mem hpP h.t_mem) with h1 | h1
  · exact h1
  · exfalso
    apply h.ne
    apply (map_conj_inj p).1
    rw [map_conj_map_conj, h1, hp]

theorem map_conj_eq_of_not_mem_normalizer {p : G} (hpP : p ∈ P)
    (hp : p ∉ normalizer (K : Set G)) :
    K.map (MulAut.conj p).toMonoidHom = K.map (MulAut.conj t).toMonoidHom := by
  rcases h.perm p hpP with h1 | h1
  · exact absurd ((mem_normalizer_iff_map_eq K p).2 h1) hp
  · exact h1

theorem tpt_mem_normalizer {p : ↥P} (hp : (p : G) ∈ normalizer (K : Set G)) :
    t * p * t ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff_map_eq, mul_assoc, ← map_conj_map_conj K t ((p : G) * t),
    ← map_conj_map_conj K p t, h.map_conj_conj_of_normalizes p.2 hp, map_conj_map_conj,
    h.t_sq, map_conj_one]

theorem pt_mem_normalizer {p : ↥P}
    (hp : K.map (MulAut.conj (p : G)).toMonoidHom = K.map (MulAut.conj t).toMonoidHom) :
    (p : G) * t ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff_map_eq, ← map_conj_map_conj K p t]
  exact h.map_conj_conj_of_swaps p.2 hp

theorem tp_mem_normalizer {p : ↥P}
    (hp : K.map (MulAut.conj (p : G)).toMonoidHom = K.map (MulAut.conj t).toMonoidHom) :
    t * (p : G) ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff_map_eq, ← map_conj_map_conj K t p, hp, map_conj_map_conj,
    h.t_sq, map_conj_one]

theorem not_mem_normalizer_of_swaps {p : G}
    (hp : K.map (MulAut.conj p).toMonoidHom = K.map (MulAut.conj t).toMonoidHom) :
    p ∉ normalizer (K : Set G) := fun hn =>
  h.ne (hp.symm.trans ((mem_normalizer_iff_map_eq K p).1 hn))

theorem t_mul_mul_t (p q : G) : t * (p * q) * t = (t * p * t) * (t * q * t) := by
  calc t * (p * q) * t = t * p * (t * t) * q * t := by rw [h.t_sq]; simp [mul_assoc]
    _ = (t * p * t) * (t * q * t) := by simp [mul_assoc]

theorem t_mul_mul_eq (p q : G) : t * (p * q) = (t * p * t) * (t * q) := by
  calc t * (p * q) = t * p * (t * t) * q := by rw [h.t_sq]; simp [mul_assoc]
    _ = (t * p * t) * (t * q) := by simp [mul_assoc]

theorem mul_t_eq (p q : G) : p * q * t = (p * t) * (t * q * t) := by
  calc p * q * t = p * (t * t) * q * t := by rw [h.t_sq]; simp [mul_assoc]
    _ = (p * t) * (t * q * t) := by simp [mul_assoc]

theorem mul_eq_mul_t (p q : G) : p * q = (p * t) * (t * q) := by
  calc p * q = p * (t * t) * q := by rw [h.t_sq]; simp
    _ = (p * t) * (t * q) := by simp [mul_assoc]

omit h in
theorem not_mem_normalizer_mul_left {p q : G} (hp : p ∈ normalizer (K : Set G))
    (hq : q ∉ normalizer (K : Set G)) : p * q ∉ normalizer (K : Set G) := by
  intro hpq
  apply hq
  simpa using mul_mem (inv_mem hp) hpq

omit h in
theorem not_mem_normalizer_mul_right {p q : G} (hq : q ∈ normalizer (K : Set G))
    (hp : p ∉ normalizer (K : Set G)) : p * q ∉ normalizer (K : Set G) := by
  intro hpq
  apply hp
  simpa using mul_mem hpq (inv_mem hq)

theorem mul_mem_normalizer_of_swaps {p q : ↥P}
    (hp : K.map (MulAut.conj (p : G)).toMonoidHom = K.map (MulAut.conj t).toMonoidHom)
    (hq : K.map (MulAut.conj (q : G)).toMonoidHom = K.map (MulAut.conj t).toMonoidHom) :
    (p : G) * q ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff_map_eq, ← map_conj_map_conj K p q, hq]
  exact h.map_conj_conj_of_swaps p.2 hp

open Classical in
@[expose] noncomputable def rhoFun (_h : PairData P K t) (p : ↥P) : Wr2 (MulAut ↥K) :=
  if (p : G) ∈ normalizer (K : Set G) then
    base (conjAutTotal K p) (conjAutTotal K (t * p * t))
  else base (conjAutTotal K (p * t)) (conjAutTotal K (t * p)) * tau

theorem rhoFun_of_normalizes (p : ↥P) (hp : (p : G) ∈ normalizer (K : Set G)) :
    h.rhoFun p = base (conjAutTotal K p) (conjAutTotal K (t * p * t)) := by
  simp [rhoFun, hp]

theorem rhoFun_of_not_normalizes (p : ↥P) (hp : (p : G) ∉ normalizer (K : Set G)) :
    h.rhoFun p = base (conjAutTotal K (p * t)) (conjAutTotal K (t * p)) * tau := by
  simp [rhoFun, hp]

@[expose] noncomputable def rho (h : PairData P K t) : ↥P →* Wr2 (MulAut ↥K) where
  toFun := h.rhoFun
  map_one' := by
    have h1 : ((1 : ↥P) : G) ∈ normalizer (K : Set G) := one_mem _
    rw [h.rhoFun_of_normalizes 1 h1]
    simp [conjAutTotal_one, base_one, h.t_sq]
  map_mul' p q := by
    by_cases hp : (p : G) ∈ normalizer (K : Set G) <;>
      by_cases hq : (q : G) ∈ normalizer (K : Set G)
    · have hpq : ((p * q : ↥P) : G) ∈ normalizer (K : Set G) := mul_mem hp hq
      rw [h.rhoFun_of_normalizes _ hpq, h.rhoFun_of_normalizes p hp,
        h.rhoFun_of_normalizes q hq, base_mul_base]
      have e : t * ((p * q : ↥P) : G) * t = (t * p * t) * (t * q * t) := h.t_mul_mul_t p q
      rw [e, conjAutTotal_mul K (h.tpt_mem_normalizer hp) (h.tpt_mem_normalizer hq)]
      rw [Subgroup.coe_mul, conjAutTotal_mul K hp hq]
    · have hqs := h.map_conj_eq_of_not_mem_normalizer q.2 hq
      have hpq : ((p * q : ↥P) : G) ∉ normalizer (K : Set G) :=
        not_mem_normalizer_mul_left hp hq
      rw [h.rhoFun_of_not_normalizes _ hpq, h.rhoFun_of_normalizes p hp,
        h.rhoFun_of_not_normalizes q hq, ← mul_assoc, base_mul_base]
      have e1 : ((p * q : ↥P) : G) * t = p * (q * t) := mul_assoc _ _ _
      have e2 : t * ((p * q : ↥P) : G) = (t * p * t) * (t * q) := h.t_mul_mul_eq p q
      rw [e1, e2, conjAutTotal_mul K hp (h.pt_mem_normalizer hqs),
        conjAutTotal_mul K (h.tpt_mem_normalizer hp) (h.tp_mem_normalizer hqs)]
    · have hps := h.map_conj_eq_of_not_mem_normalizer p.2 hp
      have hpq : ((p * q : ↥P) : G) ∉ normalizer (K : Set G) :=
        not_mem_normalizer_mul_right hq hp
      rw [h.rhoFun_of_not_normalizes _ hpq, h.rhoFun_of_not_normalizes p hp,
        h.rhoFun_of_normalizes q hq, base_mul_tau_mul_base]
      have e1 : ((p * q : ↥P) : G) * t = (p * t) * (t * q * t) := h.mul_t_eq p q
      have e2 : t * ((p * q : ↥P) : G) = (t * p) * q := by
        simp [mul_assoc]
      rw [e1, e2, conjAutTotal_mul K (h.pt_mem_normalizer hps) (h.tpt_mem_normalizer hq),
        conjAutTotal_mul K (h.tp_mem_normalizer hps) hq]
    · have hps := h.map_conj_eq_of_not_mem_normalizer p.2 hp
      have hqs := h.map_conj_eq_of_not_mem_normalizer q.2 hq
      have hpq : ((p * q : ↥P) : G) ∈ normalizer (K : Set G) :=
        h.mul_mem_normalizer_of_swaps hps hqs
      rw [h.rhoFun_of_normalizes _ hpq, h.rhoFun_of_not_normalizes p hp,
        h.rhoFun_of_not_normalizes q hq, base_mul_tau_mul_base_mul_tau]
      have e1 : ((p * q : ↥P) : G) = (p * t) * (t * q) := h.mul_eq_mul_t p q
      have e2 : t * ((p * q : ↥P) : G) * t = (t * p) * (q * t) := by
        simp [mul_assoc]
      rw [e2, conjAutTotal_mul K (h.tp_mem_normalizer hps) (h.pt_mem_normalizer hqs)]
      conv_lhs => rw [e1, conjAutTotal_mul K (h.pt_mem_normalizer hps) (h.tp_mem_normalizer hqs)]

theorem rho_apply (p : ↥P) : h.rho p = h.rhoFun p := rfl

theorem rho_of_normalizes (p : ↥P) (hp : (p : G) ∈ normalizer (K : Set G)) :
    h.rho p = base (conjAutOf K hp) (conjAutOf K (h.tpt_mem_normalizer hp)) := by
  rw [rho_apply, h.rhoFun_of_normalizes p hp, conjAutTotal_of_mem K hp,
    conjAutTotal_of_mem K (h.tpt_mem_normalizer hp)]

theorem rho_of_swaps (p : ↥P)
    (hp : K.map (MulAut.conj (p : G)).toMonoidHom = K.map (MulAut.conj t).toMonoidHom) :
    h.rho p = base (conjAutOf K (h.pt_mem_normalizer hp)) (conjAutOf K (h.tp_mem_normalizer hp))
      * tau := by
  rw [rho_apply, h.rhoFun_of_not_normalizes p (h.not_mem_normalizer_of_swaps hp),
    conjAutTotal_of_mem K (h.pt_mem_normalizer hp),
    conjAutTotal_of_mem K (h.tp_mem_normalizer hp)]

theorem rho_t : h.rho ⟨t, h.t_mem⟩ = tau := by
  have hs : K.map (MulAut.conj ((⟨t, h.t_mem⟩ : ↥P) : G)).toMonoidHom =
      K.map (MulAut.conj t).toMonoidHom := rfl
  rw [rho_apply, h.rhoFun_of_not_normalizes _ (h.not_mem_normalizer_of_swaps hs)]
  show base (conjAutTotal K (t * t)) (conjAutTotal K (t * t)) * tau = tau
  rw [h.t_sq, conjAutTotal_one, base_one, one_mul]

theorem rho_eq_one_iff (p : ↥P) :
    h.rho p = 1 ↔ (∀ k ∈ K, Commute (p : G) k) ∧ ∀ k ∈ K, Commute (p : G) (t * k * t⁻¹) := by
  by_cases hp : (p : G) ∈ normalizer (K : Set G)
  · rw [rho_apply, h.rhoFun_of_normalizes p hp, ← base_one, base_injective,
      conjAutTotal_of_mem K hp, conjAutTotal_of_mem K (h.tpt_mem_normalizer hp),
      conjAutOf_eq_one_iff, conjAutOf_eq_one_iff]
    refine and_congr Iff.rfl (forall₂_congr fun k hk => ?_)
    have := commute_conj_iff (p : G) k t
    simp only [h.t_inv] at this
    rw [h.t_inv]
    exact this
  · rw [rho_apply, h.rhoFun_of_not_normalizes p hp]
    refine iff_of_false (fun heq => base_ne_base_mul_tau 1 1 _ _ (base_one.trans heq.symm))
      (fun hc => hp (mem_normalizer_of_forall_commute K hc.1))

theorem rho_mem_baseSubgroup_iff (p : ↥P) :
    h.rho p ∈ baseSubgroup ↔ K.map (MulAut.conj (p : G)).toMonoidHom = K := by
  by_cases hp : (p : G) ∈ normalizer (K : Set G)
  · rw [rho_apply, h.rhoFun_of_normalizes p hp, mem_baseSubgroup_iff, swapChar_base]
    exact iff_of_true rfl ((mem_normalizer_iff_map_eq K _).1 hp)
  · rw [rho_apply, h.rhoFun_of_not_normalizes p hp, mem_baseSubgroup_iff, map_mul,
      swapChar_base, one_mul, swapChar_tau]
    exact iff_of_false (by decide) (fun hm => hp ((mem_normalizer_iff_map_eq K _).2 hm))

theorem rho_of_commute_t_of_normalizes (p : ↥P) (hp : (p : G) ∈ normalizer (K : Set G))
    (htp : Commute (p : G) t) : h.rho p = base (conjAutOf K hp) (conjAutOf K hp) := by
  rw [h.rho_of_normalizes p hp]
  have e : t * (p : G) * t = p := by
    calc t * (p : G) * t = (p * t) * t := by rw [htp.eq]
      _ = p := by rw [mul_assoc, h.t_sq, mul_one]
  rw [conjAutOf_congr K e (h.tpt_mem_normalizer hp) hp]

theorem rho_of_commute_t_of_swaps (p : ↥P)
    (hp : K.map (MulAut.conj (p : G)).toMonoidHom = K.map (MulAut.conj t).toMonoidHom)
    (htp : Commute (p : G) t) :
    ∃ a : MulAut ↥K, h.rho p = base a a * tau ∧
      ∀ k : ↥K, ((a k : ↥K) : G) = p * t * k * ((p : G) * t)⁻¹ := by
  refine ⟨conjAutOf K (h.pt_mem_normalizer hp), ?_, fun k => conjAutOf_apply K _ k⟩
  rw [h.rho_of_swaps p hp, conjAutOf_congr K htp.eq.symm (h.tp_mem_normalizer hp)
    (h.pt_mem_normalizer hp)]

theorem rho_of_mem (k : G) (hk : k ∈ K) :
    h.rho ⟨k, h.K_le hk⟩ = base (MulAut.conj (⟨k, hk⟩ : ↥K)) 1 := by
  have hn : k ∈ normalizer (K : Set G) := le_normalizer hk
  rw [h.rho_of_normalizes ⟨k, h.K_le hk⟩ hn]
  congr 1
  · exact conjAutOf_of_mem K hk hn
  · refine (conjAutOf_eq_one_iff K _).2 fun x hx => ?_
    have := (h.comm x hx k hk).symm
    rwa [h.t_inv] at this

theorem rho_of_mem_conj (k : G) (hk : k ∈ K) :
    h.rho ⟨t * k * t⁻¹, mul_mem (mul_mem h.t_mem (h.K_le hk)) (inv_mem h.t_mem)⟩ =
      base 1 (MulAut.conj (⟨k, hk⟩ : ↥K)) := by
  have hc : ∀ x ∈ K, Commute (t * k * t⁻¹) x := fun x hx => (h.comm x hx k hk).symm
  have hn : t * k * t⁻¹ ∈ normalizer (K : Set G) := mem_normalizer_of_forall_commute K hc
  rw [h.rho_of_normalizes _ hn]
  congr 1
  · exact (conjAutOf_eq_one_iff K hn).2 hc
  · have e : t * (t * k * t⁻¹) * t = k := by
      rw [h.t_inv]
      calc t * (t * k * t) * t = (t * t) * k * (t * t) := by simp [mul_assoc]
        _ = k := by rw [h.t_sq]; simp
    rw [conjAutOf_congr K e _ (le_normalizer hk)]
    exact conjAutOf_of_mem K hk _

theorem ker_rho : h.rho.ker =
    (centralizer (K : Set G) ⊓
      centralizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)).subgroupOf P := by
  ext p
  rw [MonoidHom.mem_ker, h.rho_eq_one_iff, mem_subgroupOf, mem_inf, mem_centralizer_iff,
    mem_centralizer_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k hk => (h1 k hk).eq.symm, ?_⟩
    rintro x ⟨k, hk, rfl⟩
    exact (h2 k hk).eq.symm
  · rintro ⟨h1, h2⟩
    refine ⟨fun k hk => (h1 k hk).symm, fun k hk => (h2 _ ⟨k, hk, rfl⟩).symm⟩

end PairData

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
