module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7Struct
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7Class

public section

namespace CFSG.QuasithinUnique.L246A7

open Equiv CFSG.Open
open scoped commutatorElement

local notation "S₇" => Equiv.Perm (Fin 7)
local notation "A₇" => alternatingGroup (Fin 7)

section UAlgebra

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem mem_U_of_cube (hL : IsShort2 L) {p y : G} (hp : p ∈ blockQ L) (hy : y ∈ L)
    (hy3 : y ^ 3 = 1) (h : (p * y) ^ 3 = 1) : p ∈ blockU L := by
  have hy2 : y ^ 2 ∈ L := L.pow_mem hy 2
  have hu1 : y * p * y⁻¹ * p⁻¹ ∈ blockU L := C1.commutator_mem_blockU' hy hp
  have hu2 : y ^ 2 * p * (y ^ 2)⁻¹ * p⁻¹ ∈ blockU L := C1.commutator_mem_blockU' hy2 hp
  set u₁ := y * p * y⁻¹ * p⁻¹ with hu₁
  set u₂ := y ^ 2 * p * (y ^ 2)⁻¹ * p⁻¹ with hu₂
  have e : (p * y) ^ 3 = p * (u₁ * p) * (u₂ * p) * y ^ 3 := by
    have hpy : (p * y) ^ 3 = (p * y) * (p * y) * (p * y) := by simp [pow_succ]
    have hy3' : y ^ 3 = y * y * y := by simp [pow_succ]
    have hy2' : y ^ 2 = y * y := by simp [pow_succ]
    rw [hu₁, hu₂, hpy, hy3', hy2']
    group
  rw [hy3, mul_one] at e
  have hc1 : u₁ * p = p * u₁ := C1.blockU_comm hL u₁ hu1 p hp
  have hc2 : u₂ * p = p * u₂ := C1.blockU_comm hL u₂ hu2 p hp
  have key : p * (u₁ * p) * (u₂ * p) = p ^ 3 * (u₁ * u₂) := by
    calc p * (u₁ * p) * (u₂ * p) = p * (p * u₁) * (u₂ * p) := by rw [hc1]
      _ = p * p * (u₁ * (u₂ * p)) := by group
      _ = p * p * (u₁ * (p * u₂)) := by rw [hc2]
      _ = p * p * ((u₁ * p) * u₂) := by group
      _ = p * p * ((p * u₁) * u₂) := by rw [hc1]
      _ = p ^ 3 * (u₁ * u₂) := by
        have hp3' : p ^ 3 = p * p * p := by simp [pow_succ]
        rw [hp3']
        group
  have h3 : p ^ 3 * (u₁ * u₂) = 1 := by rw [← key, ← e, h]
  have hp3 : p ^ 3 ∈ blockU L := by
    have : p ^ 3 = (u₁ * u₂)⁻¹ := eq_inv_of_mul_eq_one_left h3
    rw [this]
    exact (blockU L).inv_mem ((blockU L).mul_mem hu1 hu2)
  obtain ⟨k, hk⟩ := (C1.blockQ_isPGroup L) ⟨p, hp⟩
  have hk' : p ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hord : orderOf p ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime 3 (orderOf p) :=
    Nat.Coprime.coprime_dvd_right hord (Nat.Coprime.pow_right k (by norm_num))
  have hbez := Nat.gcd_eq_gcd_ab 3 (orderOf p)
  rw [hcop.gcd_eq_one] at hbez
  have hpn : p ^ (orderOf p : ℤ) = 1 := by
    rw [zpow_natCast, pow_orderOf_eq_one]
  have : p = (p ^ (3 : ℤ)) ^ (Nat.gcdA 3 (orderOf p)) := by
    calc p = p ^ (1 : ℤ) := (zpow_one p).symm
      _ = p ^ ((3 : ℤ) * Nat.gcdA 3 (orderOf p) + (orderOf p : ℤ) * Nat.gcdB 3 (orderOf p)) := by
        congr 1
      _ = (p ^ (3 : ℤ)) ^ (Nat.gcdA 3 (orderOf p)) := by
        rw [zpow_add, zpow_mul p 3, zpow_mul p (orderOf p : ℤ), hpn, one_zpow, mul_one]
  rw [this]
  refine (blockU L).zpow_mem ?_ _
  simpa using hp3

theorem orderOf_ccA : orderOf ccA = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
  · apply Subtype.ext
    exact cc_pow_three
  · intro h
    exact cc_ne_one (congrArg Subtype.val h)

theorem exists_y (D : Alt7Data L) : ∃ y ∈ L, y ^ 3 = 1 ∧ rho D y = cc := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Lc : Subgroup ↥L := (Subgroup.zpowers ccA).comap D.α
  have h3 : 3 ∣ Nat.card Lc := by
    let f : ↥Lc →* ↥(Subgroup.zpowers ccA) :=
      (D.α.comp Lc.subtype).codRestrict (Subgroup.zpowers ccA) (fun x => x.2)
    have hf : Function.Surjective f := by
      rintro ⟨b, hb⟩
      obtain ⟨ℓ, hℓ⟩ := D.hα b
      exact ⟨⟨ℓ, by rw [Subgroup.mem_comap, hℓ]; exact hb⟩, Subtype.ext hℓ⟩
    have := Subgroup.card_dvd_of_surjective hf
    rwa [Nat.card_zpowers, orderOf_ccA] at this
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Lc) 3 h3
  set ℓ : ↥L := (x : ↥L) with hℓdef
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hℓ3 : ℓ ^ 3 = 1 := by
    have := congrArg (fun z : ↥Lc => (z : ↥L)) hx3
    simpa using this
  have hℓord : orderOf ℓ = 3 := by
    have := Subgroup.orderOf_coe x
    rw [hx] at this
    exact this
  have hα1 : D.α ℓ ≠ 1 := by
    intro h1
    have hker : ℓ ∈ D.α.ker := h1
    rw [D.hker] at hker
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨ℓ, hker⟩
    have hk' : ℓ ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hd : orderOf ℓ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    rw [hℓord] at hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  have hαmem : D.α ℓ ∈ Subgroup.zpowers ccA := x.2
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hαmem
  have hm3 : ccA ^ m = ccA ^ (m % 3) := by
    rw [← zpow_mod_orderOf, orderOf_ccA]
    norm_num
  have hcases : D.α ℓ = ccA ∨ D.α ℓ = ccA⁻¹ := by
    have hmod : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · exfalso
      apply hα1
      rw [← hm, hm3, h0]
      simp
    · left
      rw [← hm, hm3, h1]
      simp
    · right
      rw [← hm, hm3, h2]
      have : ccA ^ (3 : ℤ) = 1 := by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
        apply Subtype.ext
        exact cc_pow_three
      calc ccA ^ (2 : ℤ) = ccA ^ (3 : ℤ) * ccA⁻¹ := by group
        _ = ccA⁻¹ := by rw [this, one_mul]
  rcases hcases with h | h
  · refine ⟨(ℓ : G), ℓ.2, ?_, ?_⟩
    · have := congrArg (fun z : ↥L => (z : G)) hℓ3
      simpa using this
    · rw [rho_of_mem D ℓ.2]
      show ((D.α ℓ : A₇) : S₇) = cc
      rw [h]
      rfl
  · refine ⟨((ℓ⁻¹ : ↥L) : G), (ℓ⁻¹).2, ?_, ?_⟩
    · have := congrArg (fun z : ↥L => ((z⁻¹ : ↥L) : G)) hℓ3
      simp only [inv_pow, Subgroup.coe_inv, Subgroup.coe_one, inv_one] at this ⊢
      have h' : ((ℓ : G) ^ 3) = 1 := by
        have := congrArg (fun z : ↥L => (z : G)) hℓ3
        simpa using this
      rw [h', inv_one]
    · rw [rho_of_mem D (ℓ⁻¹).2]
      show ((D.α ℓ⁻¹ : A₇) : S₇) = cc
      rw [map_inv, h, inv_inv]
      rfl

structure Cfg7 (D : Alt7Data L) (T : Subgroup G) : Prop where
  hshort : IsShort2 L
  hTN : T ≤ Subgroup.normalizer (L : Set G)
  hT2 : IsPGroup 2 T
  hstd : StdLabel D T

variable {D : Alt7Data L} {T : Subgroup G}

theorem exists_p (C : Cfg7 D T) {y : G} (hyL : y ∈ L) (hy3 : y ^ 3 = 1) (hρy : rho D y = cc)
    {t : G} (htT : t ∈ T) :
    ∃ p ∈ blockU L, (p * y) ^ 3 = 1 ∧ (t * y * t⁻¹ = p * y ∨ t * y * t⁻¹ = (p * y)⁻¹) := by
  have htN : t ∈ Subgroup.normalizer (L : Set G) := C.hTN htT
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hyL
  have hy'L : t * y * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 htN y).1 hyL
  have hy'N : t * y * t⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hy'L
  have hy'3 : (t * y * t⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3]; simp
  have hρ' : rho D (t * y * t⁻¹) = rho D t * cc * (rho D t)⁻¹ := by
    rw [rho_mul D (Subgroup.mul_mem _ htN hyN) (Subgroup.inv_mem _ htN), rho_mul D htN hyN,
      rho_inv D htN, hρy]
  rcases rho_T_conj_cc D C.hTN C.hstd htT with h | h
  · have hρ1 : rho D (t * y * t⁻¹) = cc := by rw [hρ', h]
    set p := t * y * t⁻¹ * y⁻¹ with hp
    have hpL : p ∈ L := L.mul_mem hy'L (L.inv_mem hyL)
    have hpρ : rho D p = 1 := by
      rw [hp, rho_mul D hy'N (Subgroup.inv_mem _ hyN), rho_inv D hyN, hρ1, hρy]
      simp
    have hpQ : p ∈ blockQ L := (mem_blockQ_iff_rho D hpL).2 hpρ
    have hpy : p * y = t * y * t⁻¹ := by simp [hp]
    have hcube : (p * y) ^ 3 = 1 := by rw [hpy]; exact hy'3
    exact ⟨p, mem_U_of_cube C.hshort hpQ hyL hy3 hcube, hcube, Or.inl hpy.symm⟩
  · have hρ1 : rho D (t * y * t⁻¹)⁻¹ = cc := by
      rw [rho_inv D hy'N, hρ', h]
      simp
    have hy''L : (t * y * t⁻¹)⁻¹ ∈ L := L.inv_mem hy'L
    have hy''N : (t * y * t⁻¹)⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hy''L
    set p := (t * y * t⁻¹)⁻¹ * y⁻¹ with hp
    have hpL : p ∈ L := L.mul_mem hy''L (L.inv_mem hyL)
    have hpρ : rho D p = 1 := by
      rw [hp, rho_mul D hy''N (Subgroup.inv_mem _ hyN), rho_inv D hyN, hρ1, hρy]
      simp
    have hpQ : p ∈ blockQ L := (mem_blockQ_iff_rho D hpL).2 hpρ
    have hpy : p * y = (t * y * t⁻¹)⁻¹ := by simp [hp]
    have hcube : (p * y) ^ 3 = 1 := by rw [hpy, inv_pow, hy'3, inv_one]
    refine ⟨p, mem_U_of_cube C.hshort hpQ hyL hy3 hcube, hcube, Or.inr ?_⟩
    rw [hpy, inv_inv]

end UAlgebra

section Act

open scoped IsMulCommutative

variable {G : Type} [Group G] {L : Subgroup G}

theorem normalizer_le_normalizer_blockU :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (blockU L : Set G) :=
  fun _ hg => C1.mem_normalizer_blockU hg

@[expose] def actN (L : Subgroup G) :
    ↥(Subgroup.normalizer (L : Set G)) →* MulAut ↥(blockU L) :=
  (blockU L).normalizerMonoidHom.comp (Subgroup.inclusion normalizer_le_normalizer_blockU)

theorem actN_coe (g : ↥(Subgroup.normalizer (L : Set G))) (u : ↥(blockU L)) :
    ((actN L g u : ↥(blockU L)) : G) = (g : G) * (u : G) * (g : G)⁻¹ := rfl

theorem isMulCommutative_blockU (hL : IsShort2 L) : IsMulCommutative ↥(blockU L) :=
  IsMulCommutative.of_comm fun a b => Subtype.ext
    (C1.blockU_comm hL a.1 a.2 b.1 (C1.blockU_le_blockQ hL b.2))

theorem blockU_le_L (hL : IsShort2 L) : blockU L ≤ L :=
  (C1.blockU_le_blockQ hL).trans (C1.blockQ_le L)

theorem actN_eq_one_of_mem (hL : IsShort2 L) {p : G} (hp : p ∈ blockU L)
    (hpN : p ∈ Subgroup.normalizer (L : Set G)) : actN L ⟨p, hpN⟩ = 1 := by
  ext u
  show (p : G) * (u : G) * (p : G)⁻¹ = (u : G)
  have h := C1.blockU_comm hL (u : G) u.2 p (C1.blockU_le_blockQ hL hp)
  rw [← h]
  group

@[expose] def normFn (φ : MulAut ↥(blockU L)) (u : ↥(blockU L)) : ↥(blockU L) :=
  u * φ u * φ (φ u)

theorem normFn_mul (hL : IsShort2 L) (φ : MulAut ↥(blockU L)) (a b : ↥(blockU L)) :
    normFn φ (a * b) = normFn φ a * normFn φ b := by
  have := isMulCommutative_blockU hL
  simp only [normFn, map_mul]
  ac_rfl

@[expose] def normHom (hL : IsShort2 L) (φ : MulAut ↥(blockU L)) : ↥(blockU L) →* ↥(blockU L) :=
  MonoidHom.mk' (normFn φ) (normFn_mul hL φ)

theorem normHom_apply (hL : IsShort2 L) (φ : MulAut ↥(blockU L)) (u : ↥(blockU L)) :
    normHom hL φ u = u * φ u * φ (φ u) := rfl

theorem normHom_conj (hL : IsShort2 L) {φ : MulAut ↥(blockU L)} (hφ3 : φ ^ 3 = 1)
    {τ : MulAut ↥(blockU L)} (hτ : τ * φ * τ⁻¹ = φ ∨ τ * φ * τ⁻¹ = φ⁻¹) (u : ↥(blockU L)) :
    normHom hL φ (τ u) = τ (normHom hL φ u) := by
  have := isMulCommutative_blockU hL
  have h3 : φ * φ * φ = 1 := by
    have h := hφ3
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two] at h
    exact h
  have hinv : φ⁻¹ = φ * φ := (eq_inv_of_mul_eq_one_left h3).symm
  have hcube : ∀ x : ↥(blockU L), φ (φ (φ x)) = x := fun x => by
    have := congrArg (fun m : MulAut ↥(blockU L) => m x) h3
    simpa using this
  have hφ : ∀ w : ↥(blockU L), τ (φ w) = (τ * φ * τ⁻¹) (τ w) := by
    intro w
    simp
  have hA : τ (φ u) = (τ * φ * τ⁻¹) (τ u) := hφ u
  have hB : τ (φ (φ u)) = (τ * φ * τ⁻¹) ((τ * φ * τ⁻¹) (τ u)) := by
    rw [hφ (φ u), hA]
  rw [normHom_apply, normHom_apply, map_mul, map_mul, hA, hB]
  rcases hτ with h | h
  · rw [h]
  · rw [h, hinv]
    simp only [MulAut.mul_apply, hcube]
    ac_rfl

theorem phi_cube {y : G} (hyN : y ∈ Subgroup.normalizer (L : Set G)) (hy3 : y ^ 3 = 1) :
    (actN L ⟨y, hyN⟩) ^ 3 = 1 := by
  rw [← map_pow]
  have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 := Subtype.ext hy3
  rw [this, map_one]

@[expose] def Vsub (hL : IsShort2 L) (φ : MulAut ↥(blockU L)) : Subgroup G :=
  (normHom hL φ).ker.map (blockU L).subtype

theorem mem_Vsub {hL : IsShort2 L} {φ : MulAut ↥(blockU L)} {g : G} :
    g ∈ Vsub hL φ ↔ ∃ u : ↥(blockU L), normHom hL φ u = 1 ∧ (u : G) = g := by
  simp [Vsub, Subgroup.mem_map, MonoidHom.mem_ker]

theorem Vsub_le_U (hL : IsShort2 L) (φ : MulAut ↥(blockU L)) : Vsub hL φ ≤ blockU L := by
  intro g hg
  obtain ⟨u, -, rfl⟩ := mem_Vsub.1 hg
  exact u.2

theorem Vsub_comm (hL : IsShort2 L) (φ : MulAut ↥(blockU L)) :
    ∀ a ∈ Vsub hL φ, ∀ b ∈ Vsub hL φ, a * b = b * a := fun a ha b hb =>
  C1.blockU_comm hL a (Vsub_le_U hL φ ha) b (C1.blockU_le_blockQ hL (Vsub_le_U hL φ hb))

theorem mem_Vsub_of_conj (hL : IsShort2 L) {φ : MulAut ↥(blockU L)} (hφ3 : φ ^ 3 = 1)
    {τ : MulAut ↥(blockU L)} (hτ : τ * φ * τ⁻¹ = φ ∨ τ * φ * τ⁻¹ = φ⁻¹) {u : ↥(blockU L)}
    (hu : (u : G) ∈ Vsub hL φ) : ((τ u : ↥(blockU L)) : G) ∈ Vsub hL φ := by
  obtain ⟨u', h1, h2⟩ := mem_Vsub.1 hu
  have : u' = u := Subtype.ext h2
  subst this
  refine mem_Vsub.2 ⟨τ u', ?_, rfl⟩
  rw [normHom_conj hL hφ3 hτ, h1, map_one]

theorem fpf_Vsub (hL : IsShort2 L) {φ : MulAut ↥(blockU L)} {v : ↥(blockU L)}
    (hv : (v : G) ∈ Vsub hL φ) (hfix : φ v = v) : v = 1 := by
  obtain ⟨u, h1, h2⟩ := mem_Vsub.1 hv
  have : u = v := Subtype.ext h2
  subst this
  rw [normHom_apply, hfix, hfix] at h1
  have hsq : u ^ 2 = 1 := Subtype.ext (by simpa using C1.blockU_sq hL u u.2)
  calc u = u * u * u * (u * u)⁻¹ := by group
    _ = u * u * u * (u ^ 2)⁻¹ := by rw [pow_two]
    _ = 1 := by rw [hsq]; simpa using h1

end Act


section Assembly

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {D : Alt7Data L} {T : Subgroup G}

omit [Finite G] in
theorem Alt7Data.vec_mul (D : Alt7Data L) (a b : ↥(blockU L)) :
    D.vec (a * b) = D.vec a + D.vec b := by
  funext i
  simp [Alt7Data.vec, map_mul]

omit [Finite G] in
theorem Alt7Data.vec_one (D : Alt7Data L) : D.vec 1 = 0 := by
  funext i
  simp [Alt7Data.vec]

theorem card_Vsub_le (hL : IsShort2 L) (D : Alt7Data L) {y : G} (hyL : y ∈ L)
    (hρy : rho D y = cc) :
    Nat.card (Vsub hL (actN L ⟨y, Subgroup.le_normalizer hyL⟩)) ≤ 4 := by
  set hyN : y ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hyL with hyN_def
  set φ : MulAut ↥(blockU L) := actN L ⟨y, hyN⟩ with hφ
  have hvec1 : ∀ u : ↥(blockU L), D.vec (φ u) = pact cc (D.vec u) := by
    intro u
    have h := D.vec_conj ⟨y, hyL⟩ u (φ u) rfl
    rw [h]
    congr 1
    have := rho_of_mem D hyL
    rw [hρy] at this
    exact this.symm
  have hvec2 : ∀ u : ↥(blockU L), D.vec (φ (φ u)) = pact (cc * cc) (D.vec u) := by
    intro u
    rw [hvec1, hvec1, pact_mul]
  have hsupp : ∀ u : ↥(blockU L), (u : G) ∈ Vsub hL φ → ∀ i : Fin 7, i.val < 4 → D.vec u i = 0 := by
    intro u hu i hi
    obtain ⟨u', h1, h2⟩ := mem_Vsub.1 hu
    have : u' = u := Subtype.ext h2
    subst this
    rw [normHom_apply] at h1
    have h3 := congrArg D.vec h1
    rw [D.vec_mul, D.vec_mul, hvec1, hvec2, Alt7Data.vec_one] at h3
    exact support_of_norm h3 i hi
  have heven : ∀ u : ↥(blockU L), ∑ i, D.vec u i = 0 := fun u =>
    (Multiplicative.toAdd (D.β u)).2
  let F : ↥(Vsub hL φ) → ZMod 2 × ZMod 2 := fun v =>
    (D.vec ⟨v.1, Vsub_le_U hL φ v.2⟩ 4, D.vec ⟨v.1, Vsub_le_U hL φ v.2⟩ 5)
  have hF : Function.Injective F := by
    intro v v' h
    obtain ⟨h4, h5⟩ := Prod.mk.inj h
    set u : ↥(blockU L) := ⟨v.1, Vsub_le_U hL φ v.2⟩ with hu
    set u' : ↥(blockU L) := ⟨v'.1, Vsub_le_U hL φ v'.2⟩ with hu'
    have hvec : D.vec u = D.vec u' :=
      eq_of_support (heven u) (heven u') (hsupp u v.2) (hsupp u' v'.2) h4 h5
    have hβ : D.β u = D.β u' := by
      apply Multiplicative.toAdd.injective
      exact Subtype.ext hvec
    have hker : u⁻¹ * u' ∈ D.β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hβ, inv_mul_cancel]
    rw [D.hβker, Subgroup.mem_subgroupOf] at hker
    have hZ : ((u⁻¹ * u' : ↥(blockU L)) : G) ∈ Subgroup.centralizer (L : Set G) := hker.2
    have hfix : φ (u⁻¹ * u') = u⁻¹ * u' := by
      apply Subtype.ext
      show y * ((u⁻¹ * u' : ↥(blockU L)) : G) * y⁻¹ = ((u⁻¹ * u' : ↥(blockU L)) : G)
      have := Subgroup.mem_centralizer_iff.1 hZ y hyL
      rw [this]
      group
    have hmemV : ((u⁻¹ * u' : ↥(blockU L)) : G) ∈ Vsub hL φ := by
      have h1 : (u : G) ∈ Vsub hL φ := v.2
      have h2 : (u' : G) ∈ Vsub hL φ := v'.2
      have := (Vsub hL φ).mul_mem ((Vsub hL φ).inv_mem h1) h2
      simpa using this
    have h1 := fpf_Vsub hL hmemV hfix
    have hu_eq : u = u' := inv_mul_eq_one.1 h1
    apply Subtype.ext
    exact congrArg (fun w : ↥(blockU L) => (w : G)) hu_eq
  have hcard := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_zmod] at hcard
  omega

theorem exists_p_V (C : Cfg7 D T) {y : G} (hyL : y ∈ L) (hy3 : y ^ 3 = 1) (hρy : rho D y = cc)
    {t : G} (htT : t ∈ T) :
    ∃ p ∈ Vsub C.hshort (actN L ⟨y, Subgroup.le_normalizer hyL⟩),
      (t * y * t⁻¹ = p * y ∨ t * y * t⁻¹ = (p * y)⁻¹) ∧
      (actN L ⟨t, C.hTN htT⟩ * actN L ⟨y, Subgroup.le_normalizer hyL⟩ *
          (actN L ⟨t, C.hTN htT⟩)⁻¹ = actN L ⟨y, Subgroup.le_normalizer hyL⟩ ∨
        actN L ⟨t, C.hTN htT⟩ * actN L ⟨y, Subgroup.le_normalizer hyL⟩ *
          (actN L ⟨t, C.hTN htT⟩)⁻¹ = (actN L ⟨y, Subgroup.le_normalizer hyL⟩)⁻¹) := by
  obtain ⟨p, hpU, hcube, hcase⟩ := exists_p C hyL hy3 hρy htT
  have htN : t ∈ Subgroup.normalizer (L : Set G) := C.hTN htT
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hyL
  have hpN : p ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.le_normalizer (blockU_le_L C.hshort hpU)
  set φ : MulAut ↥(blockU L) := actN L ⟨y, hyN⟩ with hφ
  set τ : MulAut ↥(blockU L) := actN L ⟨t, htN⟩ with hτ
  have hp1 : actN L ⟨p, hpN⟩ = 1 := actN_eq_one_of_mem C.hshort hpU hpN
  have hpV : p ∈ Vsub C.hshort φ := by
    refine mem_Vsub.2 ⟨⟨p, hpU⟩, ?_, rfl⟩
    apply Subtype.ext
    show p * (y * p * y⁻¹) * (y * (y * p * y⁻¹) * y⁻¹) = 1
    have e : (p * y) ^ 3 = p * (y * p * y⁻¹) * (y * (y * p * y⁻¹) * y⁻¹) * y ^ 3 := by
      have hpy : (p * y) ^ 3 = (p * y) * (p * y) * (p * y) := by simp [pow_succ]
      have hy3' : y ^ 3 = y * y * y := by simp [pow_succ]
      rw [hpy, hy3']
      group
    rw [hy3, mul_one] at e
    rw [← e]
    exact hcube
  have hy'N : t * y * t⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ htN hyN) (Subgroup.inv_mem _ htN)
  have hconj : actN L ⟨t * y * t⁻¹, hy'N⟩ = τ * φ * τ⁻¹ := by
    have : (⟨t * y * t⁻¹, hy'N⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨t, htN⟩ * ⟨y, hyN⟩ * ⟨t, htN⟩⁻¹ := Subtype.ext (by simp)
    rw [this, map_mul, map_mul, map_inv]
  have hpy : actN L ⟨p * y, Subgroup.mul_mem _ hpN hyN⟩ = φ := by
    have : (⟨p * y, Subgroup.mul_mem _ hpN hyN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨p, hpN⟩ * ⟨y, hyN⟩ := rfl
    rw [this, map_mul, hp1, one_mul]
  refine ⟨p, hpV, hcase, ?_⟩
  rcases hcase with h | h
  · left
    rw [← hconj, ← hpy]
    congr 1
    exact Subtype.ext h
  · right
    have h' : (⟨t * y * t⁻¹, hy'N⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨p * y, Subgroup.mul_mem _ hpN hyN⟩⁻¹ := Subtype.ext h
    rw [← hconj, h', map_inv, hpy]

theorem a4Act (C : Cfg7 D T) {y : G} (hyL : y ∈ L) (hy3 : y ^ 3 = 1) (hρy : rho D y = cc) :
    A4Act T (Vsub C.hshort (actN L ⟨y, Subgroup.le_normalizer hyL⟩)) y := by
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hyL
  set φ : MulAut ↥(blockU L) := actN L ⟨y, hyN⟩ with hφ
  have hφ3 : φ ^ 3 = 1 := phi_cube hyN hy3
  have hVU : ∀ v ∈ Vsub C.hshort φ, v ∈ blockU L := fun v hv => Vsub_le_U C.hshort φ hv
  refine ⟨C.hT2, hy3, Vsub_comm C.hshort φ, card_Vsub_le C.hshort D hyL hρy, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have := mem_Vsub_of_conj C.hshort hφ3 (τ := φ) (Or.inl (by simp))
      (u := ⟨v, hVU v hv⟩) hv
    exact this
  · intro v hv hfix
    have h1 := fpf_Vsub C.hshort (φ := φ) (v := ⟨v, hVU v hv⟩) hv (Subtype.ext hfix)
    exact congrArg (fun w : ↥(blockU L) => (w : G)) h1
  · intro t htT v hv
    obtain ⟨p, -, -, hτ⟩ := exists_p_V C hyL hy3 hρy htT
    exact mem_Vsub_of_conj C.hshort hφ3 hτ (u := ⟨v, hVU v hv⟩) hv
  · intro t htT
    obtain ⟨p, hpV, hcase, -⟩ := exists_p_V C hyL hy3 hρy htT
    rcases hcase with h | h
    · exact ⟨p, hpV, Or.inl h⟩
    ·
      have hy2 : y * y = y⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        have : y ^ 3 = y * y * y := by simp [pow_succ]
        rw [← this]
        exact hy3
      have hmem : y⁻¹ * p⁻¹ * y ∈ Vsub C.hshort φ := by
        have hp' : p⁻¹ ∈ Vsub C.hshort φ := (Vsub C.hshort φ).inv_mem hpV
        have h1 := mem_Vsub_of_conj C.hshort hφ3 (τ := φ) (Or.inl (by simp))
          (u := ⟨p⁻¹, hVU _ hp'⟩) hp'
        have h2 := mem_Vsub_of_conj C.hshort hφ3 (τ := φ) (Or.inl (by simp))
          (u := ⟨y * p⁻¹ * y⁻¹, hVU _ h1⟩) h1
        have e : y * (y * p⁻¹ * y⁻¹) * y⁻¹ = y⁻¹ * p⁻¹ * y := by
          calc y * (y * p⁻¹ * y⁻¹) * y⁻¹ = (y * y) * p⁻¹ * (y * y)⁻¹ := by group
            _ = y⁻¹ * p⁻¹ * (y⁻¹)⁻¹ := by rw [hy2]
            _ = y⁻¹ * p⁻¹ * y := by rw [inv_inv]
        rw [← e]
        exact h2
      refine ⟨y⁻¹ * p⁻¹ * y, hmem, Or.inr ?_⟩
      rw [h]
      group

theorem zmod2_neg (x : ZMod 2) : -x = x := by
  revert x
  decide

omit [Finite G] in
theorem Alt7Data.vec_inv (D : Alt7Data L) (u : ↥(blockU L)) : D.vec u⁻¹ = D.vec u := by
  funext i
  simp only [Alt7Data.vec, map_inv, toAdd_inv, AddSubgroup.coe_neg, Pi.neg_apply]
  exact zmod2_neg _

theorem exists_commutator_vec (D : Alt7Data L) {a : G} (haL : a ∈ L) (u : ↥(blockU L)) :
    ∃ u' : ↥(blockU L), (u' : G) = ⁅(u : G), a⁆ ∧
      D.vec u' = D.vec u + pact (rho D a) (D.vec u) := by
  set au : ↥(blockU L) := actN L ⟨a, Subgroup.le_normalizer haL⟩ u with hau
  refine ⟨u * au⁻¹, ?_, ?_⟩
  · show (u : G) * ((a * (u : G) * a⁻¹)⁻¹) = ⁅(u : G), a⁆
    simp [commutatorElement_def, mul_assoc]
  · rw [D.vec_mul, D.vec_inv]
    have h := D.vec_conj ⟨a, haL⟩ u au rfl
    rw [h, rho_of_mem D haL]

theorem commutator_ne_bot (C : Cfg7 D T) (hQT : blockQ L ≤ T) : ⁅⁅T, T⁆, T⁆ ≠ ⊥ := by
  obtain ⟨a, ha, hρa⟩ := C.hstd.2 g1 g1_mem
  obtain ⟨w, hw⟩ := D.hβ (Multiplicative.ofAdd (⟨w0, w0_mem⟩ : evenWeight 7))
  have hvw : D.vec w = w0 := by
    have : Multiplicative.toAdd (D.β w) = (⟨w0, w0_mem⟩ : evenWeight 7) := by rw [hw]; rfl
    exact congrArg Subtype.val this
  have hwT : (w : G) ∈ T := hQT (C1.blockU_le_blockQ C.hshort w.2)
  obtain ⟨c₁, hc₁, hv₁⟩ := exists_commutator_vec D ha.2 w
  obtain ⟨c₂, hc₂, hv₂⟩ := exists_commutator_vec D ha.2 c₁
  have hne : (c₂ : G) ≠ 1 := by
    intro h1
    have h2 : c₂ = 1 := Subtype.ext h1
    have h3 : D.vec c₂ = 0 := by rw [h2, Alt7Data.vec_one]
    rw [hv₂, hv₁, hvw, hρa] at h3
    exact w0_twice_ne (congrFun h3 0)
  have hmem : (c₂ : G) ∈ ⁅⁅T, T⁆, T⁆ := by
    rw [hc₂, hc₁]
    exact Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator hwT ha.1) ha.1
  intro h
  rw [h] at hmem
  exact hne (Subgroup.mem_bot.1 hmem)

omit [Finite G] in
theorem commutator_characteristic (T : Subgroup G) :
    ((⁅⁅T, T⁆, T⁆ : Subgroup G).subgroupOf T).Characteristic := by
  have hTop : (⊤ : Subgroup ↥T).map T.subtype = T := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have heq : (⁅⁅T, T⁆, T⁆ : Subgroup G) = Subgroup.map T.subtype
      ⁅⁅(⊤ : Subgroup ↥T), (⊤ : Subgroup ↥T)⁆, (⊤ : Subgroup ↥T)⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hTop]
  rw [heq]
  have : (Subgroup.map T.subtype
      ⁅⁅(⊤ : Subgroup ↥T), (⊤ : Subgroup ↥T)⁆, (⊤ : Subgroup ↥T)⁆).subgroupOf T =
      ⁅⁅(⊤ : Subgroup ↥T), (⊤ : Subgroup ↥T)⁆, (⊤ : Subgroup ↥T)⁆ :=
    Subgroup.comap_map_eq_self_of_injective T.subtype_injective _
  rw [this]
  infer_instance

theorem exists_y_central (C : Cfg7 D T) :
    ∃ y ∈ L, rho D y = cc ∧ y ∈ Subgroup.centralizer ((⁅⁅T, T⁆, T⁆ : Subgroup G) : Set G) := by
  obtain ⟨y, hyL, hy3, hρy⟩ := exists_y D
  have hA := a4Act C hyL hy3 hρy
  have hcl := hA.class_two
  refine ⟨y, hyL, hρy, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  exact (Subgroup.mem_centralizer_iff.1 (hcl hc) y hA.y_mem_Y).symm

end Assembly

end CFSG.QuasithinUnique.L246A7
