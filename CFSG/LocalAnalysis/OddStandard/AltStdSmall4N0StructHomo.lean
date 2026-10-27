module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4N0StructT
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBBasis

public section

namespace CFSG.OddStandard.AltStdSmall4.N0

open Subgroup Equiv Equiv.Perm AltStdCycTwo

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}

theorem nonempty_z4cube {T : Subgroup G} (hT : Nat.card T = 64)
    (hab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) {a b d : G} (ha : a ∈ T) (hb : b ∈ T) (hd : d ∈ T)
    (ha4 : a ^ 4 = 1) (hb4 : b ^ 4 = 1) (hd4 : d ^ 4 = 1)
    (hinj : ∀ i j k : ℕ, i < 4 → j < 4 → k < 4 → a ^ i * b ^ j * d ^ k = 1 →
      i = 0 ∧ j = 0 ∧ k = 0) :
    Nonempty (T ≃* Multiplicative (Fin 3 → ZMod 4)) := by
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  letI : CommGroup T :=
    { (inferInstance : Group T) with
      mul_comm := fun x y => Subtype.ext (hab x x.2 y y.2) }
  set A : T := ⟨a, ha⟩
  set B : T := ⟨b, hb⟩
  set D : T := ⟨d, hd⟩
  have hpow : ∀ {X : T}, X ^ 4 = 1 → ∀ p q : ZMod 4, X ^ (p + q).val = X ^ p.val * X ^ q.val := by
    intro X hX p q
    rw [ZMod.val_add, ← pow_add]
    conv_rhs => rw [← Nat.mod_add_div (p.val + q.val) 4, pow_add, pow_mul, hX, one_pow, mul_one]
  have hA4 : A ^ 4 = 1 := Subtype.ext (by simpa using ha4)
  have hB4 : B ^ 4 = 1 := Subtype.ext (by simpa using hb4)
  have hD4 : D ^ 4 = 1 := Subtype.ext (by simpa using hd4)
  let φ : Multiplicative (Fin 3 → ZMod 4) →* T :=
    { toFun := fun v => A ^ (v.toAdd 0).val * B ^ (v.toAdd 1).val * D ^ (v.toAdd 2).val
      map_one' := by simp
      map_mul' := by
        intro v w
        simp only [toAdd_mul, Pi.add_apply]
        rw [hpow hA4, hpow hB4, hpow hD4, mul_mul_mul_comm (A ^ _) (A ^ _), mul_mul_mul_comm] }
  have hinjφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hv' : a ^ (v.toAdd 0).val * b ^ (v.toAdd 1).val * d ^ (v.toAdd 2).val = 1 := by
      have := congrArg Subtype.val hv
      simpa [φ, A, B, D] using this
    obtain ⟨h0, h1, h2⟩ := hinj _ _ _ (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) hv'
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact (ZMod.val_eq_zero _).1 h0
    · exact (ZMod.val_eq_zero _).1 h1
    · exact (ZMod.val_eq_zero _).1 h2
  have hcard : Nat.card (Multiplicative (Fin 3 → ZMod 4)) = 64 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  have hbij : Function.Bijective φ := hinjφ.bijective_of_nat_card_le (by rw [hT, hcard])
  exact ⟨(MulEquiv.ofBijective φ hbij).symm⟩

section Setup

variable [Finite G] {Q : Subgroup G} {θ : L ≃* alternatingGroup (Fin n)} {z : G}
  (hn : 8 ≤ n) (c : Config G L Q n θ z)
  (hF : ∃ g ∈ N0 θ hn z, g * z * g⁻¹ = z * w θ hn)

include c hF

theorem card_of_bz {X : Subgroup G} (hX : X ≤ D0 θ hn z)
    (htr : ∀ j, ∃ x ∈ X, bz z x = eps θ hn j) :
    Nat.card X = Nat.card (X ⊓ centralizer ({z} : Set G) : Subgroup G) * 8 := by
  have hmem : ∀ x : X, bz z (x : G) ∈ E θ hn :=
    fun x => bz_mem_E hn c (Subgroup.mem_inf.1 (hX x.2)).1
  let β : X →* E θ hn := MonoidHom.mk' (fun x => ⟨bz z x, hmem x⟩) (by
    intro a b
    apply Subtype.ext
    exact bz_mul hn c (hX a.2) (hX b.2))
  have hker : β.ker = (X ⊓ centralizer ({z} : Set G)).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨x.2, ((bz_eq_one_iff _).1 (congrArg Subtype.val h))⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext ((bz_eq_one_iff _).2 h)
  have hrange : β.range = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    obtain ⟨j, rfl⟩ := (mem_E_iff θ hn y).1 hy
    obtain ⟨x, hx, hxj⟩ := htr j
    exact ⟨⟨x, hx⟩, Subtype.ext hxj⟩
  have h1 := Subgroup.card_ker_mul_card_range β
  rw [hker, hrange, Subgroup.card_top, card_E,
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
  exact h1.symm

variable {P O : Subgroup G} {s : G} (hS : SetupData θ hn z P O s) {T : Subgroup G}
  (hT : TData θ hn z P T s)

include hS hT

theorem TData.inf_cent : (T ⊓ centralizer ({z} : Set G) : Subgroup G) = E θ hn := by
  ext x
  rw [Subgroup.mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hx, hxz⟩
    exact hT.cent x hx hxz
  · intro hx
    obtain ⟨i, rfl⟩ := (mem_E_iff θ hn x).1 hx
    exact ⟨hT.E_le (eps_mem_E θ hn i), eps_comm_z hn c i⟩

theorem TData.card_eq : Nat.card T = 64 := by
  rw [card_of_bz hn c hF (hT.le_D0 hn c hF hS) hT.trans, hT.inf_cent hn c hF hS, card_E]

theorem TData.sq_mem_E {t : G} (ht : t ∈ T) : t * t ∈ E θ hn := by
  apply hT.cent _ (mul_mem ht ht)
  rw [← bz_eq_one_iff, bz_mul hn c (hT.le_D0 hn c hF hS ht) (hT.le_D0 hn c hF hS ht)]
  obtain ⟨i, hi⟩ := (mem_E_iff θ hn _).1 (bz_mem_E hn c (P_le_N0 hn c hS (hT.le_P ht)))
  rw [hi, eps_mul_self]

theorem bz_pow {x : G} (hx : x ∈ D0 θ hn z) (k : ℕ) : bz z (x ^ k) = bz z x ^ k := by
  induction k with
  | zero => simp [bz]
  | succ k ih => rw [pow_succ, bz_mul hn c (pow_mem hx k) hx, ih, pow_succ]

omit c hF hS hT in
theorem eps_pow (x : Fin 8) (k : ℕ) :
    eps θ hn x ^ k = eps θ hn (if k % 2 = 1 then x else 0) := by
  induction k with
  | zero => simp [eps_zero]
  | succ k ih =>
    rw [pow_succ, ih, eps_mul]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have h' : (k + 1) % 2 = 1 := by omega
      rw [if_neg (by omega), if_pos h']
      exact (by decide : ∀ y : Fin 8, (0 : Fin 8) ^^^ y = y) x
    · have h' : (k + 1) % 2 = 0 := by omega
      rw [if_pos h, if_neg (by omega)]
      exact (by decide : ∀ y : Fin 8, y ^^^ y = 0) x

theorem TData.homo : Nonempty (T ≃* Multiplicative (Fin 6 → ZMod 2)) ∨
    Nonempty (T ≃* Multiplicative (Fin 3 → ZMod 4)) := by
  obtain ⟨t₀, ht₀, hgen⟩ := hT.exists_gens hn c hF hS
  set tk : ℕ → G := fun k => s ^ k * t₀ * (s ^ k)⁻¹ with htk
  have htkT : ∀ k, tk k ∈ T := fun k => (hgen k).1
  have hbk : ∀ k, bz z (tk k) = eps θ hn ((mPerm ^ k) 1) := fun k => (hgen k).2
  have hm : ∀ k : Fin 8, (mPerm ^ (k : ℕ)) 1 = ![1, 2, 4, 3, 6, 7, 5, 1] k := by decide
  have hb0 : bz z (tk 0) = eps θ hn 1 := by rw [hbk]; exact congrArg _ (hm 0)
  have hb1 : bz z (tk 1) = eps θ hn 2 := by rw [hbk]; exact congrArg _ (hm 1)
  have hb2 : bz z (tk 2) = eps θ hn 4 := by rw [hbk]; exact congrArg _ (hm 2)
  have hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    hT.comm hn c hF hS hx hy
  obtain ⟨a₀, ha₀⟩ := (mem_E_iff θ hn _).1 (hT.sq_mem_E hn c hF hS (htkT 0))
  have hsq : ∀ k, tk k * tk k = eps θ hn ((mPerm ^ k) a₀) := by
    intro k
    rw [← s_pow_conj_eps hn c hS k, ← ha₀]
    simp only [htk]
    group
  have hT64 := hT.card_eq hn c hF hS
  by_cases ha : a₀ = 0
  ·
    left
    have hgenT := forall_of_gen hn c (hT.le_D0 hn c hF hS) (fun x hx => hT.E_le hx)
      (fun x hx y hy h => hT.inv_mul_mem_E hn c hF hS hx hy h) (htkT 0) (htkT 1) (htkT 2)
      hb0 hb1 hb2
    have h2 : ∀ t ∈ T, t * t = 1 := by
      refine hgenT (fun t => t * t = 1) (fun e he => ?_) (fun x hx y hy h1 h2 => ?_) ?_ ?_ ?_
        (by simp)
      · obtain ⟨i, rfl⟩ := (mem_E_iff θ hn e).1 he
        exact eps_mul_self θ hn i
      · show x * y * (x * y) = 1
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hcomm y hy x hx]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [h1, h2, one_mul]
      all_goals
        show tk _ * tk _ = 1
        rw [hsq, ha]
        rw [show ∀ k : ℕ, (mPerm ^ k) (0 : Fin 8) = 0 from fun k => by
          induction k with
          | zero => rfl
          | succ k ih => rw [pow_succ', Perm.mul_apply, ih]; rfl]
        exact eps_zero θ hn
    obtain ⟨bs⟩ := CFSG.SeitzReduction.LinearPilot.exists_elemBasis (m := 6)
      (by rw [hT64]; norm_num) h2
    exact ⟨bs.mulEquiv.symm⟩
  ·
    right
    have h4 : ∀ k, tk k ^ 4 = 1 := by
      intro k
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, hsq, eps_mul_self]
    have hsq' : ∀ k, tk k ^ 2 = eps θ hn ((mPerm ^ k) a₀) := fun k => by rw [sq, hsq]
    refine nonempty_z4cube hT64 hcomm (htkT 0) (htkT 1) (htkT 2) (h4 0) (h4 1) (h4 2) ?_
    intro i j k hi hj hk h1
    have hD : ∀ k, tk k ∈ D0 θ hn z := fun k => hT.le_D0 hn c hF hS (htkT k)
    have hbz : bz z (tk 0 ^ i * tk 1 ^ j * tk 2 ^ k) = 1 := by rw [h1]; simp [bz]
    rw [bz_mul hn c (mul_mem (pow_mem (hD 0) i) (pow_mem (hD 1) j)) (pow_mem (hD 2) k),
      bz_mul hn c (pow_mem (hD 0) i) (pow_mem (hD 1) j), bz_pow hn c hF hS hT (hD 0),
      bz_pow hn c hF hS hT (hD 1), bz_pow hn c hF hS hT (hD 2), hb0, hb1, hb2, eps_pow,
      eps_pow, eps_pow, eps_mul, eps_mul, eps_eq_one_iff] at hbz
    have hpar : ∀ p q r : Fin 2, (((if p.val = 1 then (1 : Fin 8) else 0) ^^^
        (if q.val = 1 then 2 else 0)) ^^^ (if r.val = 1 then 4 else 0)) = 0 →
          p.val = 0 ∧ q.val = 0 ∧ r.val = 0 := by decide
    obtain ⟨hi2, hj2, hk2⟩ := hpar ⟨i % 2, Nat.mod_lt _ (by norm_num)⟩
      ⟨j % 2, Nat.mod_lt _ (by norm_num)⟩ ⟨k % 2, Nat.mod_lt _ (by norm_num)⟩ hbz
    simp only at hi2 hj2 hk2
    have hi' : i = 2 * (i / 2) := by omega
    have hj' : j = 2 * (j / 2) := by omega
    have hk' : k = 2 * (k / 2) := by omega
    rw [hi', hj', hk', pow_mul, pow_mul, pow_mul, hsq', hsq', hsq', eps_pow, eps_pow, eps_pow,
      eps_mul, eps_mul, eps_eq_one_iff] at h1
    have hm2 : (mPerm ^ 2) a₀ = mPerm (mPerm a₀) := by rw [sq, Perm.mul_apply]
    rw [pow_zero, Perm.one_apply, pow_one, hm2] at h1
    have hsoc : ∀ a : Fin 8, a ≠ 0 → ∀ p q r : Fin 2,
        (((if p.val % 2 = 1 then a else 0) ^^^ (if q.val % 2 = 1 then mPerm a else 0)) ^^^
          (if r.val % 2 = 1 then mPerm (mPerm a) else 0)) = 0 →
            p.val = 0 ∧ q.val = 0 ∧ r.val = 0 := by decide
    obtain ⟨h0, h1', h2'⟩ := hsoc a₀ ha ⟨i / 2, by omega⟩ ⟨j / 2, by omega⟩ ⟨k / 2, by omega⟩ h1
    simp only at h0 h1' h2'
    omega

end Setup

end CFSG.OddStandard.AltStdSmall4.N0
