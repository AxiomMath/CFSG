module

public import CFSG.GH74.GLS.Stage4.RestSetup

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS
open scoped commutatorElement

section General

variable {G : Type} [Group G]

theorem t2C_oPrimeResidualOf_eq_closure (p : ℕ) (K : Subgroup G) :
    oPrimeResidualOf p K = Subgroup.closure {x | x ∈ K ∧ ∃ k : ℕ, x ^ p ^ k = 1} := by
  rw [oPrimeResidualOf, oPrimeResidual, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨k, hk⟩, rfl⟩
    exact ⟨y.2, k, by rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hk, Subgroup.coe_one]⟩
  · rintro ⟨hx, k, hk⟩
    exact ⟨⟨x, hx⟩, ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, hk])⟩, rfl⟩

theorem t2C_oPrimeResidualOf_conj (p : ℕ) {X : Subgroup G} {c : G} (hc : c ∈ X) {x : G}
    (hx : x ∈ oPrimeResidualOf p X) : c * x * c⁻¹ ∈ oPrimeResidualOf p X := by
  rw [t2C_oPrimeResidualOf_eq_closure] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨hyX, k, hk⟩ := hy
    refine Subgroup.subset_closure ⟨?_, k, ?_⟩
    · exact X.mul_mem (X.mul_mem hc hyX) (X.inv_mem hc)
    · rw [conj_pow, hk, mul_one, mul_inv_cancel]
  | one => simp
  | mul y y' _ _ h1 h2 =>
    have e : c * (y * y') * c⁻¹ = (c * y * c⁻¹) * (c * y' * c⁻¹) := by group
    rw [e]; exact Subgroup.mul_mem _ h1 h2
  | inv y _ h1 =>
    have e : c * y⁻¹ * c⁻¹ = (c * y * c⁻¹)⁻¹ := by group
    rw [e]; exact Subgroup.inv_mem _ h1

theorem t2C_odd_mem_of_index_two {N M : Subgroup G} (hidx : N.relIndex M = 2)
    {x : G} (hx : x ∈ M) (hodd : Odd (orderOf x)) : x ∈ N := by
  have hsq : x * x ∈ N := by
    have := Subgroup.mul_self_mem_of_index_two hidx ⟨x, hx⟩
    rwa [Subgroup.mem_subgroupOf] at this
  obtain ⟨k, hk⟩ := hodd
  have h1 : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have h2 : x = (x * x) ^ (k + 1) := by
    have : (x * x) ^ (k + 1) = x ^ (2 * k + 1) * x := by
      rw [← pow_two, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ]
    rw [this, h1, one_mul]
  rw [h2]
  exact Subgroup.pow_mem _ hsq _

theorem t2C_exists_odd_normal {X : Type} [Group X] [Finite X] (Z : Subgroup X) (hZ : IsPGroup 2 ↥Z)
    (hZidx : ¬ 2 ∣ Z.index) (hZc : ∀ a ∈ Z, ∀ x : X, a * x = x * a) :
    ∃ M : Subgroup X, M.Normal ∧ Odd (Nat.card ↥M) ∧ (∀ x : X, Odd (orderOf x) → x ∈ M) ∧
      M ⊓ Z = ⊥ ∧ M ⊔ Z = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 X := hZ.toSylow hZidx
  have hPZ : (P : Subgroup X) = Z := IsPGroup.toSylow_coe hZ hZidx
  have hP : Subgroup.normalizer ((P : Subgroup X) : Set X) ≤ Subgroup.centralizer ((P : Subgroup X) : Set X) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ Z := by rw [← hPZ]; exact hh
    exact hZc h hh' g
  let φ := MonoidHom.transferSylow P hP
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hP
  refine ⟨φ.ker, MonoidHom.normal_ker φ, ?_, ?_, ?_, ?_⟩
  · have this : ¬ 2 ∣ Nat.card ↥φ.ker := MonoidHom.not_dvd_card_ker_transferSylow P hP
    exact Nat.odd_iff.2 (by omega)
  · intro x hx
    rw [MonoidHom.mem_ker]
    obtain ⟨k, hk⟩ := (P.isPGroup' (φ x))
    have h1 : orderOf (φ x) ∣ orderOf x := orderOf_map_dvd φ x
    have h2 : orderOf (φ x) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    have hi0 : i = 0 := by
      by_contra hne
      have h2o : 2 ∣ orderOf (φ x) := by
        rw [hio]; exact dvd_pow_self 2 hne
      have := hx
      obtain ⟨j, hj⟩ := hx
      have h3 : 2 ∣ orderOf x := h2o.trans h1
      omega
    rw [hi0, pow_zero] at hio
    exact orderOf_eq_one_iff.1 hio
  · rw [← hPZ]; exact hcompl.disjoint.eq_bot
  · rw [← hPZ]; exact hcompl.sup_eq_top

end General

section Comp

variable {G : Type} [Group G] [Finite G]

structure T2Comp (z : G) (K₁ K₂ : Subgroup G) : Prop where
  zz : z * z = 1
  z_ne : z ≠ 1
  z₁ : z ∈ K₁
  z₂ : z ∈ K₂
  zc₁ : ∀ x ∈ K₁, x * z = z * x
  zc₂ : ∀ x ∈ K₂, x * z = z * x
  comm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x
  inter : K₁ ⊓ K₂ ≤ Subgroup.zpowers z
  Z₁ : ∀ k ∈ K₁, (∀ k' ∈ K₁, k * k' = k' * k) → k ∈ Subgroup.zpowers z
  Z₂ : ∀ k ∈ K₂, (∀ k' ∈ K₂, k * k' = k' * k) → k ∈ Subgroup.zpowers z
  Q₁ : ∀ N : Subgroup G, N ≤ K₁ → (∀ k ∈ K₁, ∀ n ∈ N, k * n * k⁻¹ ∈ N) →
    N ≤ Subgroup.zpowers z ∨ K₁ ≤ N
  nab₁ : ¬ K₁ ≤ Subgroup.zpowers z
  gen₁ : K₁ ≤ Subgroup.closure {x | x ∈ K₁ ∧ Odd (orderOf x)}
  gen₂ : K₂ ≤ Subgroup.closure {x | x ∈ K₂ ∧ Odd (orderOf x)}
  card : Nat.card ↥K₂ ≤ Nat.card ↥K₁

variable {z : G} {K₁ K₂ : Subgroup G}

omit [Finite G] in
theorem t2C_K₁_normal_K (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) :
    ∀ k ∈ K₁ ⊔ K₂, ∀ x ∈ K₁, k * x * k⁻¹ ∈ K₁ := by
  intro k hk x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hcomm k).1 hk
  have : a * b * x * (a * b)⁻¹ = a * x * a⁻¹ := by
    have hbx : b * x = x * b := (hcomm x hx b hb).symm
    calc a * b * x * (a * b)⁻¹ = a * (b * x) * b⁻¹ * a⁻¹ := by group
      _ = a * (x * b) * b⁻¹ * a⁻¹ := by rw [hbx]
      _ = a * x * a⁻¹ := by group
  rw [this]
  exact K₁.mul_mem (K₁.mul_mem ha hx) (K₁.inv_mem ha)

omit [Finite G] in
theorem t2C_K₂_normal_K (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) :
    ∀ k ∈ K₁ ⊔ K₂, ∀ x ∈ K₂, k * x * k⁻¹ ∈ K₂ := by
  intro k hk x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hcomm k).1 hk
  have : a * b * x * (a * b)⁻¹ = b * x * b⁻¹ := by
    have hax : a * x = x * a := hcomm a ha x hx
    calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      _ = (b * x * b⁻¹) * a * a⁻¹ := by
        rw [hcomm a ha (b * x * b⁻¹) (K₂.mul_mem (K₂.mul_mem hb hx) (K₂.inv_mem hb))]
      _ = b * x * b⁻¹ := by group
  rw [this]
  exact K₂.mul_mem (K₂.mul_mem hb hx) (K₂.inv_mem hb)

omit [Finite G] in
theorem t2C_zpowers_cases (hzz : z * z = 1) {g : G} (hg : g ∈ Subgroup.zpowers z) : g = 1 ∨ g = z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have key : z ^ n = (z * z) ^ (n / 2) * z ^ (n % 2) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod n 2]
    rw [zpow_add, zpow_mul, zpow_two]
  rw [key, hzz, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left; rw [h, zpow_zero]
  · right; rw [h, zpow_one]

omit [Finite G] in
theorem t2C_commute_odd (hz : z * z = 1) (hz1 : z ≠ 1) {l k : G} (hkz : k * z = z * k)
    (hc : l * k * l⁻¹ * k⁻¹ ∈ Subgroup.zpowers z) (hodd : Odd (orderOf k)) : l * k = k * l := by
  rcases t2C_zpowers_cases hz hc with h | h
  · have : l * k * l⁻¹ = k := by
      calc l * k * l⁻¹ = (l * k * l⁻¹ * k⁻¹) * k := by group
        _ = k := by rw [h, one_mul]
    calc l * k = (l * k * l⁻¹) * l := by group
      _ = k * l := by rw [this]
  · exfalso
    have h1 : l * k * l⁻¹ = z * k := by
      calc l * k * l⁻¹ = (l * k * l⁻¹ * k⁻¹) * k := by group
        _ = z * k := by rw [h]
    have hcomm : Commute z k := hkz.symm
    obtain ⟨j, hj⟩ := hodd
    have hkn : k ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one k
    have h2 : (l * k * l⁻¹) ^ (2 * j + 1) = 1 := by
      rw [conj_pow, hkn]; group
    rw [h1, hcomm.mul_pow, hkn, mul_one] at h2
    have h3 : z ^ (2 * j + 1) = z := by
      rw [pow_succ, pow_mul, pow_two, hz, one_pow, one_mul]
    exact hz1 (h3.symm.trans h2)

omit [Finite G] in
theorem t2C_conj_zpowers {m : G} (hmz : m * z = z * m) {g : G} (hg : g ∈ Subgroup.zpowers z) :
    m * g * m⁻¹ = g := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have : m * z * m⁻¹ = z := by rw [hmz]; group
  rw [← conj_zpow, this]

theorem t2C_conj_K₁ (hC : T2Comp z K₁ K₂) {m : G} (hmz : m * z = z * m)
    (hK : ∀ x ∈ K₁ ⊔ K₂, m * x * m⁻¹ ∈ K₁ ⊔ K₂) (hK' : ∀ x ∈ K₁ ⊔ K₂, m⁻¹ * x * m ∈ K₁ ⊔ K₂) :
    K₁.map (MulAut.conj m).toMonoidHom = K₁ ∨ K₁.map (MulAut.conj m).toMonoidHom = K₂ := by
  set L : Subgroup G := K₁.map (MulAut.conj m).toMonoidHom with hL
  have hLmem : ∀ y, y ∈ L ↔ ∃ x ∈ K₁, m * x * m⁻¹ = y := by
    intro y
    simp [hL, Subgroup.mem_map, MulAut.conj_apply]
  have hmz' : m⁻¹ * z = z * m⁻¹ := by
    have : m⁻¹ * (m * z) * m⁻¹ = m⁻¹ * (z * m) * m⁻¹ := by rw [hmz]
    have h2 : z * m⁻¹ = m⁻¹ * z := by simpa [mul_assoc] using this
    exact h2.symm
  have hLK : L ≤ K₁ ⊔ K₂ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hLmem y).1 hy
    exact hK x (Subgroup.mem_sup_left hx)
  have hKnorm₁ := t2C_K₁_normal_K hC.comm
  have hKnorm₂ := t2C_K₂_normal_K hC.comm
  have hLnorm : ∀ k ∈ K₁ ⊔ K₂, ∀ y ∈ L, k * y * k⁻¹ ∈ L := by
    intro k hk y hy
    obtain ⟨x, hx, rfl⟩ := (hLmem y).1 hy
    have hk' : m⁻¹ * k * m ∈ K₁ ⊔ K₂ := hK' k hk
    have h1 := hKnorm₁ _ hk' x hx
    rw [hLmem]
    refine ⟨_, h1, ?_⟩
    group
  have hcardL : Nat.card L = Nat.card K₁ :=
    Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj m))
  have hN₁ : ∀ k ∈ K₁, ∀ n ∈ K₁ ⊓ L, k * n * k⁻¹ ∈ K₁ ⊓ L := by
    intro k hk n hn
    exact ⟨K₁.mul_mem (K₁.mul_mem hk hn.1) (K₁.inv_mem hk),
      hLnorm k (Subgroup.mem_sup_left hk) n hn.2⟩
  rcases hC.Q₁ (K₁ ⊓ L) inf_le_left hN₁ with hNz | hKN
  swap
  · left
    have hKL : K₁ ≤ L := le_trans hKN inf_le_right
    exact (Subgroup.eq_of_le_of_card_ge hKL (by rw [hcardL])).symm
  set N₂' : Subgroup G := K₁ ⊓ K₂.map (MulAut.conj m⁻¹).toMonoidHom with hN₂'
  have hN₂'mem : ∀ y, y ∈ N₂' ↔ y ∈ K₁ ∧ m * y * m⁻¹ ∈ K₂ := by
    intro y
    simp only [hN₂', Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨hy, w, hw, hwy⟩
      refine ⟨hy, ?_⟩
      have : m * y * m⁻¹ = w := by rw [← hwy]; group
      rw [this]; exact hw
    · rintro ⟨hy, hy2⟩
      exact ⟨hy, _, hy2, by group⟩
  have hN₂'norm : ∀ k ∈ K₁, ∀ n ∈ N₂', k * n * k⁻¹ ∈ N₂' := by
    intro k hk n hn
    obtain ⟨hn1, hn2⟩ := (hN₂'mem n).1 hn
    rw [hN₂'mem]
    refine ⟨K₁.mul_mem (K₁.mul_mem hk hn1) (K₁.inv_mem hk), ?_⟩
    have hl : m * k * m⁻¹ ∈ K₁ ⊔ K₂ := hK k (Subgroup.mem_sup_left hk)
    have := hKnorm₂ _ hl _ hn2
    have e : m * (k * n * k⁻¹) * m⁻¹ = (m * k * m⁻¹) * (m * n * m⁻¹) * (m * k * m⁻¹)⁻¹ := by group
    rw [e]; exact this
  have hN₂'le : N₂' ≤ K₁ := inf_le_left
  rcases hC.Q₁ N₂' hN₂'le hN₂'norm with hz2 | hKN₂
  swap
  · right
    have hLK₂ : L ≤ K₂ := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := (hLmem y).1 hy
      exact ((hN₂'mem x).1 (hKN₂ hx)).2
    exact Subgroup.eq_of_le_of_card_ge hLK₂ (by rw [hcardL]; exact hC.card)
  exfalso
  have hLc₁ : ∀ l ∈ L, ∀ k ∈ K₁, l * k = k * l := by
    intro l hl
    have hlK : l ∈ K₁ ⊔ K₂ := hLK hl
    have hsub : K₁ ≤ Subgroup.centralizer ({l} : Set G) := by
      refine le_trans hC.gen₁ ?_
      rw [Subgroup.closure_le]
      rintro k ⟨hk, hodd⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      refine (t2C_commute_odd hC.zz hC.z_ne (hC.zc₁ k hk) ?_ hodd).symm
      refine hNz ⟨?_, ?_⟩
      · exact K₁.mul_mem (hKnorm₁ l hlK k hk) (K₁.inv_mem hk)
      · have e : l * k * l⁻¹ * k⁻¹ = l * (k * l⁻¹ * k⁻¹) := by group
        rw [e]
        exact L.mul_mem hl (hLnorm k (Subgroup.mem_sup_left hk) l⁻¹ (L.inv_mem hl))
    intro k hk
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hsub hk)).symm
  have hLc₂ : ∀ l ∈ L, ∀ k ∈ K₂, l * k = k * l := by
    intro l hl
    have hlK : l ∈ K₁ ⊔ K₂ := hLK hl
    have hN₂z : ∀ y ∈ L, y ∈ K₂ → y ∈ Subgroup.zpowers z := by
      intro y hy hy2
      obtain ⟨x, hx, rfl⟩ := (hLmem y).1 hy
      have hx2 : x ∈ N₂' := (hN₂'mem x).2 ⟨hx, hy2⟩
      have := hz2 hx2
      rw [t2C_conj_zpowers hmz this]; exact this
    have hsub : K₂ ≤ Subgroup.centralizer ({l} : Set G) := by
      refine le_trans hC.gen₂ ?_
      rw [Subgroup.closure_le]
      rintro k ⟨hk, hodd⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      refine (t2C_commute_odd hC.zz hC.z_ne (hC.zc₂ k hk) ?_ hodd).symm
      refine hN₂z _ ?_ ?_
      · have e : l * k * l⁻¹ * k⁻¹ = l * (k * l⁻¹ * k⁻¹) := by group
        rw [e]
        exact L.mul_mem hl (hLnorm k (Subgroup.mem_sup_right hk) l⁻¹ (L.inv_mem hl))
      · exact K₂.mul_mem (hKnorm₂ l hlK k hk) (K₂.inv_mem hk)
    intro k hk
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hsub hk)).symm
  have hLz : L ≤ Subgroup.zpowers z := by
    intro l hl
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_comm hC.comm l).1 (hLK hl)
    have ha1 : a ∈ Subgroup.zpowers z := by
      refine hC.Z₁ a ha (fun k hk => ?_)
      have h1 := hLc₁ l hl k hk
      rw [hab] at h1
      have h2 : b * k = k * b := (hC.comm k hk b hb).symm
      calc a * k = a * (k * b) * b⁻¹ := by group
        _ = a * (b * k) * b⁻¹ := by rw [h2]
        _ = (a * b) * k * b⁻¹ := by group
        _ = k * (a * b) * b⁻¹ := by rw [h1]
        _ = k * a := by group
    have hb1 : b ∈ Subgroup.zpowers z := by
      refine hC.Z₂ b hb (fun k hk => ?_)
      have h1 := hLc₂ l hl k hk
      rw [hab] at h1
      have h2 : a * k = k * a := hC.comm a ha k hk
      calc b * k = a⁻¹ * (a * b * k) := by group
        _ = a⁻¹ * (k * (a * b)) := by rw [h1]
        _ = a⁻¹ * (k * a) * b := by group
        _ = a⁻¹ * (a * k) * b := by rw [h2]
        _ = k * b := by group
    rw [hab]
    exact Subgroup.mul_mem _ ha1 hb1
  apply hC.nab₁
  intro x hx
  have hx' := hLz ((hLmem _).2 ⟨x, hx, rfl⟩)
  have h5 := t2C_conj_zpowers hmz' hx'
  rw [inv_inv] at h5
  have e : m⁻¹ * (m * x * m⁻¹) * m = x := by group
  rw [e] at h5
  rw [h5]
  exact hx'

end Comp

end CFSG.GH74.GLS.Stage4.Rest
