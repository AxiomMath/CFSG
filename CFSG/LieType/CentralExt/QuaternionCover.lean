module

public import CFSG.CharacterTheory.Semidihedral.CentralTransferSplitting
public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2

public section

namespace CFSG.LieType.CentralExt

open QuaternionGroup
open scoped commutatorElement

section Relations

variable {F : Type*} [Group F] {x y α : F}

theorem conj_zpow_of_conj_eq (hα : α ∈ Subgroup.center F) (hyx : y * x * y⁻¹ = x⁻¹ * α)
    (i : ℤ) : y * x ^ i * y⁻¹ = x ^ (-i) * α ^ i := by
  have hc : Commute x⁻¹ α := Subgroup.mem_center_iff.1 hα x⁻¹
  rw [← conj_zpow, hyx, hc.mul_zpow, inv_zpow']

theorem commutatorElement_mul_center {u v z w : F} (hz : z ∈ Subgroup.center F)
    (hw : w ∈ Subgroup.center F) : ⁅u * z, v * w⁆ = ⁅u, v⁆ := by
  have hz' : ∀ g, g * z = z * g := Subgroup.mem_center_iff.1 hz
  have hw' : ∀ g, g * w = w * g := Subgroup.mem_center_iff.1 hw
  simp only [commutatorElement_def]
  calc u * z * (v * w) * (u * z)⁻¹ * (v * w)⁻¹
      = u * (z * (v * w) * z⁻¹) * u⁻¹ * (v * w)⁻¹ := by group
    _ = u * v * (w * (u⁻¹ * w⁻¹)) * v⁻¹ := by rw [← hz', mul_inv_cancel_right]; group
    _ = u * v * u⁻¹ * v⁻¹ := by rw [← hw']; group

theorem commutatorElement_zpow_zpow (i k : ℤ) : ⁅x ^ i, x ^ k⁆ = 1 := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_zpow_mul_zpow (hα : α ∈ Subgroup.center F)
    (hyx : y * x * y⁻¹ = x⁻¹ * α) (i k : ℤ) : ⁅x ^ i, y * x ^ k⁆ = (x ^ 2 * α⁻¹) ^ i := by
  have hc : Commute (x ^ 2) α⁻¹ := Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hα) _
  have h1 : ⁅x ^ i, y * x ^ k⁆ = x ^ i * (y * x ^ (-i) * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [h1, conj_zpow_of_conj_eq hα hyx, hc.mul_zpow]
  group

theorem commutatorElement_mul_zpow_zpow (hα : α ∈ Subgroup.center F)
    (hyx : y * x * y⁻¹ = x⁻¹ * α) (i k : ℤ) : ⁅y * x ^ i, x ^ k⁆ = (x ^ 2 * α⁻¹) ^ (-k) := by
  rw [← commutatorElement_inv, commutatorElement_zpow_mul_zpow hα hyx, zpow_neg]

theorem commutatorElement_mul_zpow_mul_zpow (hα : α ∈ Subgroup.center F)
    (hyx : y * x * y⁻¹ = x⁻¹ * α) (i k : ℤ) :
    ⁅y * x ^ i, y * x ^ k⁆ = (x ^ 2 * α⁻¹) ^ (k - i) := by
  have hc : Commute (x ^ 2) α⁻¹ := Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hα) _
  have hcz : ∀ g, α ^ (k - i) * g = g * α ^ (k - i) := fun g =>
    (Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ hα (k - i)) g).symm
  have h1 : ⁅y * x ^ i, y * x ^ k⁆ = y * x ^ i * (y * x ^ (k - i) * y⁻¹) * x ^ (-k) * y⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [h1, conj_zpow_of_conj_eq hα hyx (k - i)]
  calc y * x ^ i * (x ^ (-(k - i)) * α ^ (k - i)) * x ^ (-k) * y⁻¹
      = y * x ^ i * x ^ (-(k - i)) * (α ^ (k - i) * (x ^ (-k) * y⁻¹)) := by group
    _ = y * x ^ i * x ^ (-(k - i)) * ((x ^ (-k) * y⁻¹) * α ^ (k - i)) := by rw [hcz]
    _ = y * x ^ (2 * i - 2 * k) * y⁻¹ * α ^ (k - i) := by group
    _ = (x ^ 2 * α⁻¹) ^ (k - i) := by
      rw [conj_zpow_of_conj_eq hα hyx, hc.mul_zpow]
      group

theorem commutator_le_zpowers (hα : α ∈ Subgroup.center F) (hyx : y * x * y⁻¹ = x⁻¹ * α)
    {T : Subgroup F}
    (hT : ∀ t ∈ T, ∃ i : ℤ, ∃ z ∈ Subgroup.center F, t = x ^ i * z ∨ t = y * x ^ i * z) :
    ⁅T, T⁆ ≤ Subgroup.zpowers (x ^ 2 * α⁻¹) := by
  rw [Subgroup.commutator_le]
  intro t₁ ht₁ t₂ ht₂
  obtain ⟨i, z, hz, h1 | h1⟩ := hT t₁ ht₁ <;> obtain ⟨k, w, hw, h2 | h2⟩ := hT t₂ ht₂ <;>
    rw [h1, h2, commutatorElement_mul_center hz hw]
  · rw [commutatorElement_zpow_zpow]
    exact Subgroup.one_mem _
  · rw [commutatorElement_zpow_mul_zpow hα hyx]
    exact Subgroup.zpow_mem_zpowers _ _
  · rw [commutatorElement_mul_zpow_zpow hα hyx]
    exact Subgroup.zpow_mem_zpowers _ _
  · rw [commutatorElement_mul_zpow_mul_zpow hα hyx]
    exact Subgroup.zpow_mem_zpowers _ _

theorem pow_two_mul_eq_one (hα : α ∈ Subgroup.center F) (hyx : y * x * y⁻¹ = x⁻¹ * α)
    {β : F} (hβ : β ∈ Subgroup.center F) {M : ℕ} (hy2 : y ^ 2 = x ^ (2 * M) * β) :
    (x ^ 2 * α⁻¹) ^ (2 * M) = 1 := by
  have hc : Commute (x ^ 2) α⁻¹ := Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hα) _
  have hαy : y⁻¹ * α⁻¹ = α⁻¹ * y⁻¹ := Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hα) _
  have hαx : (x ^ 2)⁻¹ * α = α * (x ^ 2)⁻¹ := Subgroup.mem_center_iff.1 hα _
  have hconj : y * (x ^ 2 * α⁻¹) * y⁻¹ = (x ^ 2 * α⁻¹)⁻¹ := by
    have h2 := conj_zpow_of_conj_eq hα hyx 2
    calc y * (x ^ 2 * α⁻¹) * y⁻¹ = y * x ^ 2 * (y⁻¹ * α⁻¹) := by rw [hαy]; group
      _ = y * x ^ (2 : ℤ) * y⁻¹ * α⁻¹ := by group
      _ = (x ^ 2)⁻¹ * α * α * α⁻¹ := by rw [h2]; group
      _ = (x ^ 2 * α⁻¹)⁻¹ := by rw [mul_inv_cancel_right, hαx]; group
  set d := (x ^ 2 * α⁻¹) ^ M with hd
  have hd1 : y * d * y⁻¹ = d⁻¹ := by rw [hd, ← conj_pow, hconj, inv_pow]
  have hw : β⁻¹ * α⁻¹ ^ M ∈ Subgroup.center F :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hβ) (Subgroup.pow_mem _ (Subgroup.inv_mem _ hα) M)
  have hd2 : d = y ^ 2 * (β⁻¹ * α⁻¹ ^ M) := by
    rw [hd, hc.mul_pow, ← pow_mul, hy2]
    group
  have hd3 : y * d * y⁻¹ = d := by
    rw [hd2]
    generalize β⁻¹ * α⁻¹ ^ M = w at hw ⊢
    calc y * (y ^ 2 * w) * y⁻¹ = y * y ^ 2 * (w * y⁻¹) := by group
      _ = y * y ^ 2 * (y⁻¹ * w) := by rw [← Subgroup.mem_center_iff.1 hw y⁻¹]
      _ = y ^ 2 * w := by group
  have hdd : d⁻¹ = d := hd1.symm.trans hd3
  rw [pow_mul', ← hd, sq]
  calc d * d = d * d⁻¹ := by rw [hdd]
    _ = 1 := mul_inv_cancel d

theorem zpowers_inf_ker_eq_bot {Q : Type*} [Group Q] (η : F →* Q) (hα : η α = 1) {N : ℕ}
    (hord : orderOf (η x) = 2 * N) (hc : (x ^ 2 * α⁻¹) ^ N = 1) :
    Subgroup.zpowers (x ^ 2 * α⁻¹) ⊓ η.ker = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz1
  have hz2 : η ((x ^ 2 * α⁻¹) ^ j) = 1 := hz2
  rw [map_zpow, map_mul, map_inv, hα, inv_one, mul_one, map_pow, ← zpow_natCast,
    ← zpow_mul] at hz2
  have h1 : ((2 * N : ℕ) : ℤ) ∣ (2 : ℕ) * j := hord ▸ orderOf_dvd_iff_zpow_eq_one.2 hz2
  have h2 : (N : ℤ) ∣ j := by
    push_cast at h1
    exact (mul_dvd_mul_iff_left two_ne_zero).1 h1
  have h3 : (orderOf (x ^ 2 * α⁻¹) : ℤ) ∣ j :=
    (Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one hc)).trans h2
  exact orderOf_dvd_iff_zpow_eq_one.1 h3

end Relations

section QuaternionCoordinates

variable {N : ℕ}

theorem quaternion_conj : (xa 0 : QuaternionGroup N) * a 1 * (xa 0)⁻¹ = (a 1)⁻¹ := by
  have h : (a 1 : QuaternionGroup N)⁻¹ = a (-1) := inv_eq_of_mul_eq_one_right (by simp)
  rw [h, mul_inv_eq_iff_eq_mul]
  simp

theorem quaternion_sq : (xa 0 : QuaternionGroup N) ^ 2 = a 1 ^ N := by
  rw [xa_sq, a_one_pow]

theorem quaternion_cases [NeZero N] (q : QuaternionGroup N) :
    ∃ i : ℕ, q = a 1 ^ i ∨ q = xa 0 * a 1 ^ i := by
  cases q with
  | a i => exact ⟨i.val, .inl (by rw [a_one_pow, ZMod.natCast_zmod_val])⟩
  | xa i => exact ⟨i.val, .inr (by rw [a_one_pow, ZMod.natCast_zmod_val, xa_mul_a, zero_add])⟩

end QuaternionCoordinates

section Transfer

variable {E : Type*} [Group E] [Finite E]

theorem mem_commutator_of_mem_center (hE : Subgroup.closure {x : E | Odd (orderOf x)} = ⊤)
    {T : Subgroup E} (hT : IsPGroup 2 T) (hodd : Odd T.index) {c : E}
    (hc : c ∈ Subgroup.center E) (hcT : c ∈ T) : c ∈ ⁅T, T⁆ := by
  have hA : IsPGroup 2 (Abelianization T) :=
    hT.of_surjective Abelianization.of (fun q => QuotientGroup.mk_surjective q)
  obtain ⟨V, hV⟩ := CFSG.Semidihedral.CentralTransferSplitting.exists_normalized_transfer 2 T hA
    (Nat.coprime_two_left.2 hodd) Abelianization.of
  have hV1 : ∀ g, V g = 1 := by
    have hle : Subgroup.closure {x : E | Odd (orderOf x)} ≤ V.ker := by
      rw [Subgroup.closure_le]
      intro g hg
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hA (V g)
      have hdvd : 2 ^ k ∣ orderOf g := hk ▸ orderOf_map_dvd V g
      have hk0 : k = 0 := by
        by_contra h
        exact (Nat.not_even_iff_odd.2 hg) (even_iff_two_dvd.2 ((dvd_pow_self 2 h).trans hdvd))
      rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
      exact hk
    rw [hE] at hle
    exact fun g => hle (Subgroup.mem_top g)
  have h1 : (⟨c, hcT⟩ : T) ∈ commutator T := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker, ← hV c hcT hc, hV1]
  rw [← Subgroup.map_subtype_commutator]
  exact ⟨_, h1, rfl⟩

end Transfer

section Cover

variable {E Q : Type*} [Group E] [Group Q] [Finite E]

theorem ker_eq_bot_of_sylow_quaternion
    (hE : Subgroup.closure {x : E | Odd (orderOf x)} = ⊤) (η : E →* Q)
    (hη : Function.Surjective η) (hcen : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    (S : Sylow 2 Q) {n : ℕ} (hn : 3 ≤ n)
    (φ : (S : Subgroup Q) ≃* QuaternionGroup (2 ^ (n - 2))) : η.ker = ⊥ := by
  have : Finite Q := Finite.of_surjective η hη
  set N := 2 ^ (n - 2) with hN
  set M := 2 ^ (n - 3) with hM
  have hNM : N = 2 * M := by
    rw [hN, hM, ← pow_succ']
    congr 1
    omega
  let ψ : QuaternionGroup N →* Q := (S : Subgroup Q).subtype.comp φ.symm.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp φ.symm.injective
  have hψq : ∀ (q : Q) (hq : q ∈ (S : Subgroup Q)), ψ (φ ⟨q, hq⟩) = q := fun q hq => by
    simp [ψ]
  set r := ψ (a 1) with hr
  set s := ψ (xa 0) with hs
  have hsr : s * r * s⁻¹ = r⁻¹ := by
    simpa only [map_mul, map_inv] using congrArg ψ (quaternion_conj (N := N))
  have hs2 : s ^ 2 = r ^ N := by
    simpa only [map_pow] using congrArg ψ (quaternion_sq (N := N))
  have hord : orderOf r = 2 * N := by rw [hr, orderOf_injective ψ hψ, orderOf_a_one]
  have hcases : ∀ q ∈ (S : Subgroup Q), ∃ i : ℕ, q = r ^ i ∨ q = s * r ^ i := by
    intro q hq
    obtain ⟨i, hi | hi⟩ := quaternion_cases (φ ⟨q, hq⟩)
    · exact ⟨i, .inl (by rw [← hψq q hq, hi, map_pow])⟩
    · exact ⟨i, .inr (by rw [← hψq q hq, hi, map_mul, map_pow])⟩
  obtain ⟨x, hx⟩ := hη r
  obtain ⟨y, hy⟩ := hη s
  set α := x * (y * x * y⁻¹) with hαdef
  have hαker : η α = 1 := by
    rw [hαdef, map_mul, map_mul, map_mul, map_inv, hx, hy, hsr, mul_inv_cancel]
  have hα : α ∈ Subgroup.center E := hcen hαker
  have hyx : y * x * y⁻¹ = x⁻¹ * α := by rw [hαdef, inv_mul_cancel_left]
  set β := (x ^ (2 * M))⁻¹ * y ^ 2 with hβdef
  have hβ : β ∈ Subgroup.center E := hcen (by
    rw [MonoidHom.mem_ker, hβdef, map_mul, map_inv, map_pow, map_pow, hx, hy, hs2, ← hNM,
      inv_mul_cancel])
  have hy2 : y ^ 2 = x ^ (2 * M) * β := by rw [hβdef, mul_inv_cancel_left]
  have hc0 : (x ^ 2 * α⁻¹) ^ N = 1 := hNM ▸ pow_two_mul_eq_one hα hyx hβ hy2
  set T := (S : Subgroup Q).comap η with hTdef
  have hT : ∀ t ∈ T, ∃ i : ℤ, ∃ z ∈ Subgroup.center E, t = x ^ i * z ∨ t = y * x ^ i * z := by
    intro t ht
    obtain ⟨i, hi | hi⟩ := hcases (η t) ht
    · refine ⟨i, (x ^ (i : ℤ))⁻¹ * t, hcen ?_, .inl (mul_inv_cancel_left _ _).symm⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hx, hi, zpow_natCast, inv_mul_cancel]
    · refine ⟨i, (y * x ^ (i : ℤ))⁻¹ * t, hcen ?_, .inr (mul_inv_cancel_left _ _).symm⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_zpow, hx, hy, hi, zpow_natCast,
        inv_mul_cancel]
  have hTc : ⁅T, T⁆ ≤ Subgroup.zpowers (x ^ 2 * α⁻¹) := commutator_le_zpowers hα hyx hT
  have hTp : IsPGroup 2 T := IsPGroup.comap_of_ker_isPGroup S.isPGroup' η h2
  have hTodd : Odd T.index := by
    rw [hTdef, Subgroup.index_comap_of_surjective _ hη]
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 S.not_dvd_index)
  have hker : η.ker ≤ Subgroup.zpowers (x ^ 2 * α⁻¹) ⊓ η.ker := fun c hc =>
    ⟨hTc (mem_commutator_of_mem_center hE hTp hTodd (hcen hc) (by
      rw [hTdef, Subgroup.mem_comap, (MonoidHom.mem_ker).1 hc]
      exact Subgroup.one_mem _)), hc⟩
  rw [zpowers_inf_ker_eq_bot η hαker (hx ▸ hord) hc0] at hker
  exact le_bot_iff.1 hker

theorem ker_eq_bot_of_exists_sylow_quaternion
    (hE : Subgroup.closure {x : E | Odd (orderOf x)} = ⊤) (η : E →* Q)
    (hη : Function.Surjective η) (hcen : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    (hS : ∃ S : Sylow 2 Q, ∃ n : ℕ, 3 ≤ n ∧
      Nonempty ((S : Subgroup Q) ≃* QuaternionGroup (2 ^ (n - 2)))) : η.ker = ⊥ := by
  obtain ⟨S, n, hn, ⟨φ⟩⟩ := hS
  exact ker_eq_bot_of_sylow_quaternion hE η hη hcen h2 S hn φ

theorem ker_eq_bot_of_mulEquiv_specialLinearGroup {K : Type*} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (hE : Subgroup.closure {x : E | Odd (orderOf x)} = ⊤) (η : E →* Q)
    (hη : Function.Surjective η) (hcen : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) K) : η.ker = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  have hodd : Odd (Nat.card K) := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.2 (FiniteField.odd_card_of_char_ne_two hK)
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) K)))
  obtain ⟨n, hn, ⟨φ⟩⟩ := CFSG.Semidihedral.OddFieldSL2.sylow_two_quaternion K hodd P
  have hrange : (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) ≤ e.toMonoidHom.range :=
    fun g _ => ⟨e.symm g, e.apply_symm_apply g⟩
  let S : Sylow 2 Q := P.comapOfInjective e.toMonoidHom e.injective hrange
  have hS : ∀ q : Q, q ∈ (S : Subgroup Q) ↔ e q ∈ (P : Subgroup _) := fun _ => Iff.rfl
  let ε : (S : Subgroup Q) ≃* (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) :=
    { toFun := fun q => ⟨e q, (hS q).1 q.2⟩
      invFun := fun g => ⟨e.symm g, (hS _).2 (by rw [e.apply_symm_apply]; exact g.2)⟩
      left_inv := fun q => Subtype.ext (e.symm_apply_apply q)
      right_inv := fun g => Subtype.ext (e.apply_symm_apply g)
      map_mul' := fun q₁ q₂ => Subtype.ext (map_mul e (q₁ : Q) (q₂ : Q)) }
  exact ker_eq_bot_of_sylow_quaternion hE η hη hcen h2 S hn (ε.trans φ)

end Cover

end CFSG.LieType.CentralExt
