module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4Perm
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4HbarOrder
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoSplit

public section

namespace CFSG.OddStandard.AltStdSmall4

open Subgroup Equiv AltStdCycTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {T : Subgroup G}

section Basic

omit [Finite G] in
theorem mem_E_of_mem_eBar (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n)
    {e : alternatingGroup (Fin n)} (he : e ∈ eBar hn) : ((θ.symm e : L) : G) ∈ E θ hn :=
  ⟨θ.symm e, ⟨e, he, rfl⟩, rfl⟩

omit [Finite G] in
theorem card_E (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) : Nat.card (E θ hn) = 8 := by
  unfold E
  rw [card_map_of_injective L.subtype_injective,
    card_map_of_injective (f := θ.symm.toMonoidHom) θ.symm.injective, card_eBar]

private theorem z_sq (c : Config G L Q n θ z) : z ^ 2 = 1 := by
  rw [← c.ot.cyc.order]
  exact pow_orderOf_eq_one z

private theorem z_mul_self (c : Config G L Q n θ z) : z * z = 1 := by
  rw [← sq]
  exact z_sq c

private theorem z_inv (c : Config G L Q n θ z) : z⁻¹ = z :=
  inv_eq_of_mul_eq_one_right (z_mul_self c)

omit [Finite G] in
private theorem comm_of_elem (helem : ∀ x ∈ T, x ^ 2 = 1) {a b : G} (ha : a ∈ T) (hb : b ∈ T) :
    a * b = b * a := by
  have e1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact helem a ha)
  have e2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact helem b hb)
  have e3 : (a * b)⁻¹ = a * b :=
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact helem _ (mul_mem ha hb))
  calc a * b = (a * b)⁻¹ := e3.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [e1, e2]

omit [Finite G] in
private theorem le_centralizer_of_elem (helem : ∀ x ∈ T, x ^ 2 = 1) :
    T ≤ centralizer (T : Set G) :=
  fun a ha => mem_centralizer_iff.2 fun b hb => comm_of_elem helem hb ha

private theorem conj_z_mem {hn : 8 ≤ n} (h0 : N0Data θ hn z T) {x : G} (hx : x ∈ T) :
    z * x * z⁻¹ ∈ T :=
  (mem_normalizer_iff.1 h0.norm x).1 hx

omit [Finite G] in
private theorem conj_mem_centralizer {g x : G} (hg : g ∈ normalizer (T : Set G))
    (hx : x ∈ centralizer (T : Set G)) : g * x * g⁻¹ ∈ centralizer (T : Set G) := by
  rw [mem_centralizer_iff]
  intro t ht
  have ht' : g⁻¹ * t * g ∈ T := by
    have := (mem_normalizer_iff.1 (inv_mem hg) t).1 ht
    simpa using this
  have hxt := mem_centralizer_iff.1 hx _ ht'
  calc t * (g * x * g⁻¹) = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by rw [hxt]
    _ = g * x * g⁻¹ * t := by group

private theorem z_not_mem_centralizer {hn : 8 ≤ n} (h0 : N0Data θ hn z T) :
    z ∉ centralizer (T : Set G) := by
  intro hz
  have hle : T ≤ T ⊓ centralizer ({z} : Set G) := fun t ht =>
    ⟨ht, mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hz t ht)⟩
  rw [h0.cent] at hle
  have := Subgroup.card_le_of_le hle
  rw [h0.card_eq, card_E] at this
  omega

end Basic

section Inv

theorem inv_of_n0Data (c : Config G L Q n θ z) (h0 : N0Data θ c.hn8 z T)
    (helem : ∀ x ∈ T, x ^ 2 = 1) :
    ∀ y ∈ T, (y * z) ^ 2 = 1 → ∃ x ∈ T, x * z * x⁻¹ = y * z := by
  have hzz : z * z = 1 := z_mul_self c
  have hzinv : z⁻¹ = z := z_inv c
  let f : T →* T :=
    { toFun := fun x => ⟨x * (z * x * z⁻¹)⁻¹, mul_mem x.2 (inv_mem (conj_z_mem h0 x.2))⟩
      map_one' := by
        apply Subtype.ext
        show (1 : G) * (z * 1 * z⁻¹)⁻¹ = 1
        group
      map_mul' := fun a b => by
        apply Subtype.ext
        show (a : G) * b * (z * (a * b) * z⁻¹)⁻¹ =
          (a : G) * (z * a * z⁻¹)⁻¹ * ((b : G) * (z * b * z⁻¹)⁻¹)
        have hc := comm_of_elem helem (inv_mem (conj_z_mem h0 a.2))
          (mul_mem b.2 (inv_mem (conj_z_mem h0 b.2)))
        calc (a : G) * b * (z * (a * b) * z⁻¹)⁻¹
            = a * ((b * (z * b * z⁻¹)⁻¹) * (z * a * z⁻¹)⁻¹) := by group
          _ = a * ((z * a * z⁻¹)⁻¹ * (b * (z * b * z⁻¹)⁻¹)) := by rw [hc]
          _ = a * (z * a * z⁻¹)⁻¹ * (b * (z * b * z⁻¹)⁻¹) := by group }
  have hfx : ∀ x : T, ((f x : T) : G) = x * (z * x * z⁻¹)⁻¹ := fun _ => rfl
  have hker : ∀ x : T, f x = 1 ↔ (x : G) ∈ E θ c.hn8 := by
    intro x
    rw [← h0.cent]
    constructor
    · intro hx
      have h1 : (x : G) * (z * x * z⁻¹)⁻¹ = 1 := (hfx x).symm.trans (congrArg Subtype.val hx)
      have h2 : (x : G) = z * x * z⁻¹ := mul_inv_eq_one.1 h1
      refine ⟨x.2, mem_centralizer_singleton_iff.2 ?_⟩
      calc (x : G) * z = (z * x * z⁻¹) * z := by rw [← h2]
        _ = z * x := by group
    · intro hx
      have hxz : (x : G) * z = z * x :=
        mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).2
      have h1 : z * (x : G) * z⁻¹ = x := by rw [← hxz]; group
      apply Subtype.ext
      rw [hfx, h1, mul_inv_cancel, Subgroup.coe_one]
  have hcardker : Nat.card f.ker = 8 := by
    have : f.ker = (E θ c.hn8).subgroupOf T := by
      ext x
      rw [MonoidHom.mem_ker, hker, mem_subgroupOf]
    rw [this, Nat.card_congr (subgroupOfEquivOfLe h0.E_le).toEquiv, card_E]
  have hcardrange : Nat.card f.range = 8 := by
    have := Subgroup.card_ker_mul_card_range f
    rw [hcardker, h0.card_eq] at this
    omega
  have hle : f.range ≤ (E θ c.hn8).subgroupOf T := by
    rintro _ ⟨x, rfl⟩
    rw [mem_subgroupOf, ← h0.cent]
    refine ⟨(f x).2, mem_centralizer_singleton_iff.2 ?_⟩
    rw [hfx]
    have hu2 := helem _ (f x).2
    rw [hfx] at hu2
    have hzx : z * (z * (x : G) * z⁻¹) * z⁻¹ = x := by
      rw [show z * (z * (x : G) * z⁻¹) * z⁻¹ = (z * z) * x * (z * z)⁻¹ by group, hzz, one_mul,
        inv_one, mul_one]
    have h1 : z * ((x : G) * (z * x * z⁻¹)⁻¹) * z⁻¹ = ((x : G) * (z * x * z⁻¹)⁻¹)⁻¹ := by
      calc z * ((x : G) * (z * x * z⁻¹)⁻¹) * z⁻¹
          = (z * x * z⁻¹) * (z * (z * (x : G) * z⁻¹) * z⁻¹)⁻¹ := by group
        _ = (z * x * z⁻¹) * (x : G)⁻¹ := by rw [hzx]
        _ = ((x : G) * (z * x * z⁻¹)⁻¹)⁻¹ := by group
    have h2 : ((x : G) * (z * x * z⁻¹)⁻¹)⁻¹ = (x : G) * (z * x * z⁻¹)⁻¹ :=
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hu2)
    calc (x : G) * (z * x * z⁻¹)⁻¹ * z
        = (z * ((x : G) * (z * x * z⁻¹)⁻¹) * z⁻¹) * z := by rw [h1, h2]
      _ = z * ((x : G) * (z * x * z⁻¹)⁻¹) := by group
  have hrange : f.range = (E θ c.hn8).subgroupOf T :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by
      rw [hcardrange, Nat.card_congr (subgroupOfEquivOfLe h0.E_le).toEquiv, card_E]))
  intro y hyT hy2
  have hyE : y ∈ E θ c.hn8 := by
    rw [← h0.cent]
    refine ⟨hyT, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : y * z * (y * z) = 1 := by rw [← sq]; exact hy2
    have hy1 : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact helem y hyT)
    have e1 : y * z = (y * z)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    rw [e1, mul_inv_rev, hzinv, hy1]
  obtain ⟨x, hx⟩ : (⟨y, hyT⟩ : T) ∈ f.range := by
    rw [hrange, mem_subgroupOf]
    exact hyE
  refine ⟨x, x.2, ?_⟩
  have h1 : (x : G) * (z * x * z⁻¹)⁻¹ = y := (hfx x).symm.trans (congrArg Subtype.val hx)
  calc (x : G) * z * (x : G)⁻¹ = ((x : G) * (z * x * z⁻¹)⁻¹) * z := by group
    _ = y * z := by rw [h1]

end Inv

section Cent

private theorem rho_conj_eq (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) {x : G}
    (hx : x ∈ normalizer (L : Set G)) (a b : L) (hab : (b : G) = x * a * x⁻¹) :
    AltStdBal.rho θ hn ⟨x, hx⟩ * (θ a : Perm (Fin n)) * (AltStdBal.rho θ hn ⟨x, hx⟩)⁻¹ =
      (θ b : Perm (Fin n)) := by
  have h1 := AltStdBal.rho_conj θ hn ⟨x, hx⟩ (θ a)
  have h2 : (⟨x * ((θ.symm (θ a) : L) : G) * x⁻¹,
      (mem_normalizer_iff.mp hx _).mp (θ.symm (θ a)).2⟩ : L) = b := by
    apply Subtype.ext
    simp [hab]
  rw [h2] at h1
  exact h1

theorem mem_E_of_two_pow (c : Config G L Q n θ z) (h0 : N0Data θ c.hn8 z T)
    (helem : ∀ x ∈ T, x ^ 2 = 1) {x : G} (hxT : x ∈ centralizer (T : Set G))
    (hxz : x ∈ centralizer ({z} : Set G)) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x ∈ E θ c.hn8 := by
  have hS := c.ot.std
  have d := c.ot.cyc
  have hxN : x ∈ normalizer (L : Set G) := cent_le_normalizer hS d hxz
  have hcomm : ∀ e ∈ eBar c.hn8, AltStdBal.rho θ c.hn8 ⟨x, hxN⟩ * (e : Perm (Fin n)) =
      e * AltStdBal.rho θ c.hn8 ⟨x, hxN⟩ := by
    intro e he
    have hlT : ((θ.symm e : L) : G) ∈ T := h0.E_le (mem_E_of_mem_eBar θ c.hn8 he)
    have h1 := rho_conj_eq θ c.hn8 hxN (θ.symm e) (θ.symm e) (by
      have := mem_centralizer_iff.1 hxT _ hlT
      rw [← this]
      group)
    rw [MulEquiv.apply_symm_apply] at h1
    calc AltStdBal.rho θ c.hn8 ⟨x, hxN⟩ * (e : Perm (Fin n))
        = (AltStdBal.rho θ c.hn8 ⟨x, hxN⟩ * (e : Perm (Fin n)) *
            (AltStdBal.rho θ c.hn8 ⟨x, hxN⟩)⁻¹) * AltStdBal.rho θ c.hn8 ⟨x, hxN⟩ := by group
      _ = e * AltStdBal.rho θ c.hn8 ⟨x, hxN⟩ := by rw [h1]
  have hk' : AltStdBal.rho θ c.hn8 ⟨x, hxN⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨x, hxN⟩ : normalizer (L : Set G)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hev : n ≤ 9 ∨ AltStdBal.rho θ c.hn8 ⟨x, hxN⟩ ∈ alternatingGroup (Fin n) := by
    rcases c.shape with hsh | ⟨h9, -⟩
    · exact Or.inr ((mem_evenAct_iff θ c.hn8 hxN).1 (sup_le_evenAct θ c.hn8 (hsh hxz)))
    · exact Or.inl h9
  obtain ⟨e, he, hσe⟩ := exists_eBar_eq_of_comm c.hn8 c.small hcomm hk' hev
  have hlE : ((θ.symm e : L) : G) ∈ E θ c.hn8 := mem_E_of_mem_eBar θ c.hn8 he
  have hlT : ((θ.symm e : L) : G) ∈ T := h0.E_le hlE
  have hlN : ((θ.symm e : L) : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer (θ.symm e).2
  have hρl : AltStdBal.rho θ c.hn8 ⟨_, hlN⟩ = AltStdBal.rho θ c.hn8 ⟨x, hxN⟩ := by
    rw [AltStdBal.rho_of_mem θ c.hn8 (θ.symm e) hlN, MulEquiv.apply_symm_apply, hσe]
  have hyN : x * ((θ.symm e : L) : G)⁻¹ ∈ normalizer (L : Set G) := mul_mem hxN (inv_mem hlN)
  have hyK : x * ((θ.symm e : L) : G)⁻¹ ∈ centralizer (L : Set G) := by
    refine (AltStdBal.rho_eq_one_iff θ c.hn8 ⟨_, hyN⟩).1 ?_
    have : (⟨x * ((θ.symm e : L) : G)⁻¹, hyN⟩ : normalizer (L : Set G)) =
        ⟨x, hxN⟩ * ⟨_, hlN⟩⁻¹ := rfl
    rw [this, map_mul, map_inv, hρl, mul_inv_cancel]
  have hyC : x * ((θ.symm e : L) : G)⁻¹ ∈ centralizer ({z} : Set G) :=
    mul_mem hxz (inv_mem (le_cent_single hS d (θ.symm e).2))
  have hxl : Commute x ((θ.symm e : L) : G)⁻¹ :=
    (Commute.inv_right (mem_centralizer_iff.1 hxT _ hlT).symm)
  have hy2 : (x * ((θ.symm e : L) : G)⁻¹) ^ 2 ^ (k + 1) = 1 := by
    rw [hxl.mul_pow]
    have h1 : x ^ 2 ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hk, one_pow]
    have h2 : (((θ.symm e : L) : G)⁻¹) ^ 2 ^ (k + 1) = 1 := by
      rw [pow_succ', pow_mul, inv_pow, helem _ hlT, inv_one, one_pow]
    rw [h1, h2, one_mul]
  have hyz := mem_zpowers_of_two_pow d c.ot.card ⟨hyK, hyC⟩ hy2
  have hQz : zpowers z = Q := Subgroup.eq_of_le_of_card_ge (zpowers_le.2 d.mem)
    (by rw [c.ot.card, Nat.card_zpowers, d.order])
  rw [hQz] at hyz
  rcases AltStdBal.eq_one_or_eq_of_card_eq_two d c.ot.card hyz with h1 | h1
  · have : x = ((θ.symm e : L) : G) := mul_inv_eq_one.1 h1
    rw [this]
    exact hlE
  · exfalso
    apply z_not_mem_centralizer h0
    rw [← h1]
    exact mul_mem hxT (inv_mem (le_centralizer_of_elem helem hlT))

omit [Finite G] in
private theorem mem_sup_zpowers_iff' {X : Subgroup G} {u : G} (hu : u ^ 2 = 1)
    (hX : ∀ p ∈ X, u * p * u⁻¹ ∈ X) {x : G} : x ∈ X ⊔ zpowers u ↔ x ∈ X ∨ x * u ∈ X := by
  have huu : u * u = 1 := by rw [← sq, hu]
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hN : zpowers u ≤ normalizer (X : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro p
    refine ⟨hX p, fun hp => ?_⟩
    have := hX _ hp
    rwa [show u * (u * p * u⁻¹) * u⁻¹ = (u * u) * p * (u * u)⁻¹ by group, huu, one_mul, inv_one,
      mul_one] at this
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left X (zpowers u) hN
  have hz : ∀ b ∈ zpowers u, b = 1 ∨ b = u := by
    intro b hb
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
    rcases Int.emod_two_eq_zero_or_one j with hj | hj
    · left
      obtain ⟨m, hjm⟩ := Int.dvd_of_emod_eq_zero hj
      rw [hjm, zpow_mul, show u ^ (2 : ℤ) = 1 by rw [zpow_two, huu], one_zpow]
    · right
      have : j = 2 * (j / 2) + 1 := by omega
      rw [this, zpow_add, zpow_mul, show u ^ (2 : ℤ) = 1 by rw [zpow_two, huu], one_zpow,
        one_mul, zpow_one]
  constructor
  · intro hx
    have hx' : x ∈ (X : Set G) * (zpowers u : Set G) := by rw [← hm]; exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx'
    rcases hz b hb with h | h
    · left
      rw [h, mul_one]
      exact ha
    · right
      rw [h, mul_assoc, huu, mul_one]
      exact ha
  · rintro (hx | hx)
    · exact mem_sup_left hx
    · have : x = (x * u) * u := by rw [mul_assoc, huu, mul_one]
      rw [this]
      exact mul_mem (mem_sup_left hx) (mem_sup_right (mem_zpowers u))

private theorem card_sup_zpowers' {X : Subgroup G} {u : G} (hu : u ^ 2 = 1)
    (hX : ∀ p ∈ X, u * p * u⁻¹ ∈ X) (huX : u ∉ X) :
    Nat.card ↥(X ⊔ zpowers u) = 2 * Nat.card X := by
  have huu : u * u = 1 := by rw [← sq, hu]
  have hdisj : Disjoint (X : Set G) ((fun x => x * u) '' (X : Set G)) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨y, hy, rfl⟩
    have : u = y⁻¹ * (y * u) := by group
    exact huX (this ▸ X.mul_mem (X.inv_mem hy) hx)
  have hunion : ((X ⊔ zpowers u : Subgroup G) : Set G) =
      (X : Set G) ∪ (fun x => x * u) '' (X : Set G) := by
    ext x
    rw [SetLike.mem_coe, mem_sup_zpowers_iff' hu hX, Set.mem_union, SetLike.mem_coe]
    refine or_congr Iff.rfl ⟨fun h => ⟨x * u, h, by
      show x * u * u = x
      rw [mul_assoc, huu, mul_one]⟩, ?_⟩
    rintro ⟨y, hy, rfl⟩
    show y * u * u ∈ X
    rw [mul_assoc, huu, mul_one]
    exact hy
  have hinj : Set.InjOn (fun x => x * u) (X : Set G) := fun x _ y _ h => mul_right_cancel h
  have h1 : Nat.card ↥(X ⊔ zpowers u) = ((X ⊔ zpowers u : Subgroup G) : Set G).ncard :=
    Nat.card_coe_set_eq _
  have h2 : Nat.card ↥X = (X : Set G).ncard := Nat.card_coe_set_eq _
  rw [h1, hunion, Set.ncard_union_eq hdisj, hinj.ncard_image, h2]
  ring

theorem not_two_dvd_index (c : Config G L Q n θ z) (h0 : N0Data θ c.hn8 z T)
    (helem : ∀ x ∈ T, x ^ 2 = 1) :
    ¬ 2 ∣ (T.subgroupOf (centralizer (T : Set G))).index := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z ^ 2 = 1 := z_sq c
  have hzz : z * z = 1 := z_mul_self c
  have hTC : T ≤ centralizer (T : Set G) := le_centralizer_of_elem helem
  have hzC : z ∉ centralizer (T : Set G) := z_not_mem_centralizer h0
  have hzT : z ∉ T := fun h => hzC (hTC h)
  have hnT : ∀ t ∈ T, z * t * z⁻¹ ∈ T := fun t ht => conj_z_mem h0 ht
  have hnC : ∀ x ∈ centralizer (T : Set G), z * x * z⁻¹ ∈ centralizer (T : Set G) :=
    fun x hx => conj_mem_centralizer h0.norm hx
  have hcardR : Nat.card ↥(T ⊔ zpowers z) = 128 := by
    rw [card_sup_zpowers' hz2 hnT hzT, h0.card_eq] <;> norm_num
  have hcardD : Nat.card ↥(centralizer (T : Set G) ⊔ zpowers z) =
      2 * Nat.card (centralizer (T : Set G)) := card_sup_zpowers' hz2 hnC hzC
  have hRD : T ⊔ zpowers z ≤ centralizer (T : Set G) ⊔ zpowers z := sup_le_sup_right hTC _
  have hCidx : Nat.card (centralizer (T : Set G)) =
      64 * (T.subgroupOf (centralizer (T : Set G))).index := by
    rw [← (T.subgroupOf (centralizer (T : Set G))).card_mul_index,
      Nat.card_congr (subgroupOfEquivOfLe hTC).toEquiv, h0.card_eq]
  intro h2
  obtain ⟨m, hm⟩ := h2
  have hdvd : 2 ^ (7 + 1) ∣ Nat.card ↥(centralizer (T : Set G) ⊔ zpowers z) :=
    ⟨m, by rw [hcardD, hCidx, hm]; ring⟩
  have hR' : Nat.card ((T ⊔ zpowers z).subgroupOf (centralizer (T : Set G) ⊔ zpowers z)) =
      2 ^ 7 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRD).toEquiv, hcardR] <;> norm_num
  obtain ⟨K', hK'card, hRK'⟩ := Sylow.exists_subgroup_card_pow_succ hdvd hR'
  have hKcard : Nat.card (K'.map (centralizer (T : Set G) ⊔ zpowers z).subtype) = 256 := by
    rw [card_map_of_injective (Subgroup.subtype_injective _), hK'card] <;> norm_num
  have hRK : T ⊔ zpowers z ≤ K'.map (centralizer (T : Set G) ⊔ zpowers z).subtype :=
    fun r hr => ⟨⟨r, hRD hr⟩, hRK' (by rw [mem_subgroupOf]; exact hr), rfl⟩
  have hKD : K'.map (centralizer (T : Set G) ⊔ zpowers z).subtype ≤
      centralizer (T : Set G) ⊔ zpowers z := map_subtype_le K'
  set K := K'.map (centralizer (T : Set G) ⊔ zpowers z).subtype with hK
  have hzK : z ∈ K := hRK (mem_sup_right (mem_zpowers z))
  have hRn : ((T ⊔ zpowers z).subgroupOf K).Normal := by
    apply Subgroup.normal_of_index_eq_two
    have := ((T ⊔ zpowers z).subgroupOf K).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hRK).toEquiv, hcardR, hKcard] at this
    omega
  obtain ⟨x, hxK, hxR⟩ : ∃ x ∈ K, x ∉ T ⊔ zpowers z := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show K ≤ T ⊔ zpowers z from hcon)
    rw [hKcard, hcardR] at this
    omega
  obtain ⟨y, hyC, hyK, hyR⟩ : ∃ y ∈ centralizer (T : Set G), y ∈ K ∧ y ∉ T ⊔ zpowers z := by
    rcases (mem_sup_zpowers_iff' hz2 hnC).1 (hKD hxK) with hx | hx
    · exact ⟨x, hx, hxK, hxR⟩
    · refine ⟨x * z, hx, mul_mem hxK hzK, fun h => hxR ?_⟩
      have : x = x * z * z := by rw [mul_assoc, hzz, mul_one]
      rw [this]
      exact mul_mem h (mem_sup_right (mem_zpowers z))
  have hyzy : y * z * y⁻¹ ∈ T ⊔ zpowers z := by
    have := hRn.conj_mem ⟨z, hzK⟩ (by rw [mem_subgroupOf]; exact mem_sup_right (mem_zpowers z))
      ⟨y, hyK⟩
    rw [mem_subgroupOf] at this
    simpa using this
  rcases (mem_sup_zpowers_iff' hz2 hnT).1 hyzy with h1 | h1
  · apply hzC
    have : z = y⁻¹ * (y * z * y⁻¹) * y := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hyC) (hTC h1)) hyC
  · have hyz : y * z * y⁻¹ * z * z = y * z * y⁻¹ := by rw [mul_assoc _ z z, hzz, mul_one]
    have hsq : (y * z * y⁻¹ * z * z) ^ 2 = 1 := by
      rw [hyz, sq, show y * z * y⁻¹ * (y * z * y⁻¹) = y * (z * z) * y⁻¹ by group, hzz, mul_one,
        mul_inv_cancel]
    obtain ⟨s, hsT, hs⟩ := inv_of_n0Data c h0 helem _ h1 hsq
    rw [hyz] at hs
    have hw : s⁻¹ * y ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc s⁻¹ * y * z = s⁻¹ * (y * z * y⁻¹) * y := by group
        _ = s⁻¹ * (s * z * s⁻¹) * y := by rw [hs]
        _ = z * (s⁻¹ * y) := by group
    have hwC : s⁻¹ * y ∈ centralizer (T : Set G) := mul_mem (inv_mem (hTC hsT)) hyC
    have hwK : s⁻¹ * y ∈ K := mul_mem (inv_mem (hRK (mem_sup_left hsT))) hyK
    have hwpow : (s⁻¹ * y) ^ 2 ^ 8 = 1 := by
      have h3 := orderOf_dvd_natCard (⟨s⁻¹ * y, hwK⟩ : K)
      rw [Subgroup.orderOf_mk, hKcard] at h3
      exact orderOf_dvd_iff_pow_eq_one.1 (by rw [show (2 : ℕ) ^ 8 = 256 by norm_num]; exact h3)
    have hwE := mem_E_of_two_pow c h0 helem hwC hw hwpow
    apply hyR
    have : y = s * (s⁻¹ * y) := by group
    rw [this]
    exact mem_sup_left (mul_mem hsT (h0.E_le hwE))

theorem centralizer_eq_sup (c : Config G L Q n θ z) (h0 : N0Data θ c.hn8 z T)
    (helem : ∀ x ∈ T, x ^ 2 = 1) :
    centralizer (T : Set G) = T ⊔ AltStdSec.oddCoreOf (normalizer (T : Set G)) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (T : Set G) with hCdef
  set H := normalizer (T : Set G) with hHdef
  have hTC : T ≤ C := le_centralizer_of_elem helem
  have hCH : C ≤ H := Subgroup.centralizer_le_normalizer (T : Set G)
  have hinfO : T ⊓ AltStdSec.oddCoreOf H = ⊥ :=
    inf_eq_bot_of_coprime
      (by rw [h0.card_eq]; exact Nat.Coprime.pow_left 6 (coprime_card_oddCoreOf _))
  have hOC : AltStdSec.oddCoreOf H ≤ C := by
    rintro _ ⟨o, ho, rfl⟩
    show ((o : H) : G) ∈ C
    rw [mem_centralizer_iff]
    intro t ht
    have htH : t ∈ H := Subgroup.le_normalizer ht
    have h1 : (o : G) * t * (o : G)⁻¹ * t⁻¹ ∈ T :=
      mul_mem ((mem_normalizer_iff.1 o.2 t).1 ht) (inv_mem ht)
    have h2 : (o : G) * t * (o : G)⁻¹ * t⁻¹ ∈ AltStdSec.oddCoreOf H := by
      have hc : (⟨t, htH⟩ : H) * o⁻¹ * (⟨t, htH⟩ : H)⁻¹ ∈ CFSG.oddCore ↥H :=
        (inferInstance : (CFSG.oddCore ↥H).Normal).conj_mem _ (inv_mem ho) _
      refine ⟨o * ((⟨t, htH⟩ : H) * o⁻¹ * (⟨t, htH⟩ : H)⁻¹), mul_mem ho hc, ?_⟩
      show (o : G) * (t * (o : G)⁻¹ * t⁻¹) = (o : G) * t * (o : G)⁻¹ * t⁻¹
      group
    have h3 : (o : G) * t * (o : G)⁻¹ * t⁻¹ = 1 := by
      have : (o : G) * t * (o : G)⁻¹ * t⁻¹ ∈ T ⊓ AltStdSec.oddCoreOf H := ⟨h1, h2⟩
      rwa [hinfO, mem_bot] at this
    calc t * (o : G) = ((o : G) * t * (o : G)⁻¹ * t⁻¹)⁻¹ * ((o : G) * t) := by group
      _ = (o : G) * t := by rw [h3, inv_one, one_mul]
  apply le_antisymm
  ·
    have hidx := not_two_dvd_index c h0 helem
    have hTp : IsPGroup 2 (T.subgroupOf C) := IsPGroup.of_card (n := 6) (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hTC).toEquiv, h0.card_eq] <;> norm_num)
    let P : Sylow 2 ↥C := hTp.toSylow hidx
    have hPeq : (P : Subgroup ↥C) = T.subgroupOf C := IsPGroup.toSylow_coe hTp hidx
    have hP' : normalizer ((P : Subgroup ↥C) : Set ↥C) ≤
        centralizer ((P : Subgroup ↥C) : Set ↥C) := by
      intro g _
      rw [mem_centralizer_iff]
      intro q hq
      rw [SetLike.mem_coe, hPeq, mem_subgroupOf] at hq
      exact Subtype.ext (mem_centralizer_iff.1 g.2 q hq)
    have hcompl := MonoidHom.ker_transferSylow_isComplement' P hP'
    have hKodd0 := MonoidHom.not_dvd_card_ker_transferSylow P hP'
    have hKnormal := MonoidHom.normal_ker (MonoidHom.transferSylow P hP')
    obtain ⟨K, hK⟩ : ∃ K : Subgroup ↥C, K = (MonoidHom.transferSylow P hP').ker := ⟨_, rfl⟩
    rw [← hK] at hcompl hKodd0 hKnormal
    have hPmap : (P : Subgroup ↥C).map C.subtype = T := by
      rw [hPeq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTC]
    have hOodd : Odd (Nat.card (K.map C.subtype)) := by
      rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hKodd0)
    have hOC' : ∀ x ∈ C, ∀ o ∈ K.map C.subtype, x * o * x⁻¹ ∈ K.map C.subtype := by
      rintro x hx _ ⟨o, ho, rfl⟩
      exact ⟨⟨x, hx⟩ * o * ⟨x, hx⟩⁻¹, hKnormal.conj_mem o ho ⟨x, hx⟩, rfl⟩
    have hsup : K.map C.subtype ⊔ T = C := by
      rw [← hPmap, ← Subgroup.map_sup, hcompl.sup_eq_top, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have hinf : K.map C.subtype ⊓ T = ⊥ := by
      rw [← hPmap, ← Subgroup.map_inf_eq _ _ _ C.subtype_injective, hcompl.disjoint.eq_bot,
        Subgroup.map_bot]
    have hodd : ∀ x ∈ C, Odd (orderOf x) → x ∈ K.map C.subtype := by
      intro x hx hxo
      have hTN : T ≤ normalizer ((K.map C.subtype : Subgroup G) : Set G) :=
        fun t ht => mem_normalizer_iff.mpr fun o => ⟨fun ho => hOC' t (hTC ht) o ho, fun ho => by
          have := hOC' t⁻¹ (inv_mem (hTC ht)) _ ho
          simpa [mul_assoc] using this⟩
      rw [← hsup, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTN,
        Set.mem_mul] at hx
      obtain ⟨o, ho, t, ht, rfl⟩ := hx
      have hoC : o ∈ C := map_subtype_le _ ho
      have hcomm : Commute o t := (mem_centralizer_iff.mp hoC t ht).symm
      have hpow : (o * t) ^ orderOf (o * t) = 1 := pow_orderOf_eq_one _
      rw [hcomm.mul_pow] at hpow
      have htm : t ^ orderOf (o * t) ∈ K.map C.subtype ⊓ T := by
        refine ⟨?_, pow_mem ht _⟩
        rw [eq_inv_of_mul_eq_one_right hpow]
        exact (K.map C.subtype).inv_mem ((K.map C.subtype).pow_mem ho _)
      rw [hinf, mem_bot] at htm
      obtain ⟨j, hj⟩ := hxo
      rw [hj, pow_succ, pow_mul, helem t ht, one_pow, one_mul] at htm
      rw [htm, mul_one]
      exact ho
    have hOH : K.map C.subtype ≤ AltStdSec.oddCoreOf H := by
      have hOleH : K.map C.subtype ≤ H := (map_subtype_le K).trans hCH
      have hnorm : ((K.map C.subtype).subgroupOf H).Normal := by
        refine ⟨fun a ha h => ?_⟩
        rw [mem_subgroupOf] at ha ⊢
        have haC : (a : G) ∈ C := map_subtype_le K ha
        refine hodd _ (conj_mem_centralizer h.2 haC) ?_
        have h1 : orderOf (a : G) ∣ Nat.card (K.map C.subtype) := by
          have := orderOf_dvd_natCard (⟨a, ha⟩ : K.map C.subtype)
          rwa [Subgroup.orderOf_mk] at this
        have h2 : orderOf ((h : G) * a * (h : G)⁻¹) = orderOf (a : G) := by
          rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
        show Odd (orderOf ((h : G) * a * (h : G)⁻¹))
        rw [h2]
        exact Odd.of_dvd_nat hOodd h1
      have hcard : Odd (Nat.card ((K.map C.subtype).subgroupOf H)) := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hOleH).toEquiv]
        exact hOodd
      have hle : (K.map C.subtype).subgroupOf H ≤ CFSG.oddCore ↥H := le_sSup ⟨hnorm, hcard⟩
      intro x hx
      exact ⟨⟨x, hOleH hx⟩, hle (by rw [mem_subgroupOf]; exact hx), rfl⟩
    calc C = K.map C.subtype ⊔ T := hsup.symm
      _ ≤ AltStdSec.oddCoreOf H ⊔ T := sup_le_sup_right hOH T
      _ = T ⊔ AltStdSec.oddCoreOf H := sup_comm _ _
  · exact sup_le hTC hOC

end Cent

theorem sec4HSetup_holds : Sec4HSetup := by
  intro G _ _ L Q n θ z c T h0 helem
  exact ⟨h0, helem, centralizer_eq_sup c h0 helem, inv_of_n0Data c h0 helem⟩

end CFSG.OddStandard.AltStdSmall4
