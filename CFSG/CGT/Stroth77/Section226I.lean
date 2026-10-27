module

public import CFSG.CGT.Stroth77.Section224A
public import CFSG.CGT.Stroth77.Section310CharBA
public import CFSG.CGT.Stroth77.Section43Fus

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)
open CFSG.GroupTheory.HuppertProduct (mho mho_le pow_mem_mho)
open scoped commutatorElement

namespace Stroth226I

section Comm

variable {G : Type} [Group G] {B D : Subgroup G}

theorem commutator_mem_inf (hBD : B ≤ Subgroup.normalizer (D : Set G))
    (hDB : D ≤ Subgroup.normalizer (B : Set G)) {b d : G} (hb : b ∈ B) (hd : d ∈ D) :
    b * d * b⁻¹ * d⁻¹ ∈ B ⊓ D := by
  refine ⟨?_, ?_⟩
  · have h1 : d * b⁻¹ * d⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hDB hd) b⁻¹).mp (B.inv_mem hb)
    have h2 := B.mul_mem hb h1
    rwa [← mul_assoc, ← mul_assoc] at h2
  · have h1 : b * d * b⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hBD hb) d).mp hd
    exact D.mul_mem h1 (D.inv_mem hd)

variable (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
  (hBD : B ≤ Subgroup.normalizer (D : Set G)) (hDB : D ≤ Subgroup.normalizer (B : Set G))
include hB hBD hDB

theorem commutator_pow {b d : G} (hb : b ∈ B) (hd : d ∈ D) (k : ℕ) :
    b ^ k * d * (b ^ k)⁻¹ * d⁻¹ = (b * d * b⁻¹ * d⁻¹) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hck := commutator_mem_inf hBD hDB (B.pow_mem hb k) hd
    have hcomm : b * (b ^ k * d * (b ^ k)⁻¹ * d⁻¹) = (b ^ k * d * (b ^ k)⁻¹ * d⁻¹) * b :=
      hB b hb _ hck.1
    calc b ^ (k + 1) * d * (b ^ (k + 1))⁻¹ * d⁻¹
        = b * (b ^ k * d * (b ^ k)⁻¹ * d⁻¹) * b⁻¹ * (b * d * b⁻¹ * d⁻¹) := by
          rw [pow_succ']; group
      _ = (b ^ k * d * (b ^ k)⁻¹ * d⁻¹) * (b * d * b⁻¹ * d⁻¹) := by
          rw [hcomm]; group
      _ = (b * d * b⁻¹ * d⁻¹) ^ (k + 1) := by rw [ih, pow_succ]

include hD in
theorem commutator_mul_self_eq_one {b d : G} (hb : b ∈ B) (hb2 : b * b ∈ D) (hd : d ∈ D) :
    (b * d * b⁻¹ * d⁻¹) * (b * d * b⁻¹ * d⁻¹) = 1 := by
  have heBD := commutator_mem_inf hBD hDB hb hd
  have hbe : b * (b * d * b⁻¹ * d⁻¹) = (b * d * b⁻¹ * d⁻¹) * b := hB b hb _ heBD.1
  have hbbd : (b * b) * d = d * (b * b) := hD _ hb2 d hd
  have h1 : (b * b) * d * (b * b)⁻¹ =
      (b * d * b⁻¹ * d⁻¹) * (b * d * b⁻¹ * d⁻¹) * d := by
    calc (b * b) * d * (b * b)⁻¹
        = (b * (b * d * b⁻¹ * d⁻¹)) * b⁻¹ * (b * d * b⁻¹ * d⁻¹) * d := by group
      _ = (b * d * b⁻¹ * d⁻¹) * (b * d * b⁻¹ * d⁻¹) * d := by rw [hbe]; group
  have h2 : (b * b) * d * (b * b)⁻¹ = d := by rw [hbbd]; group
  have h3 := h1.symm.trans h2
  calc (b * d * b⁻¹ * d⁻¹) * (b * d * b⁻¹ * d⁻¹)
      = (b * d * b⁻¹ * d⁻¹) * (b * d * b⁻¹ * d⁻¹) * d * d⁻¹ := by group
    _ = 1 := by rw [h3]; group

include hD in
theorem mem_centralizer_mhoOne {b : G} (hb : b ∈ B) (hb2 : b * b ∈ D) :
    b ∈ Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) := by
  have key : ∀ d ∈ D, d ^ 2 * b = b * d ^ 2 := by
    intro d hd
    have he2 := commutator_mul_self_eq_one hB hD hBD hDB hb hb2 hd
    have heD := (commutator_mem_inf hBD hDB hb hd).2
    have hed : (b * d * b⁻¹ * d⁻¹) * d = d * (b * d * b⁻¹ * d⁻¹) := hD _ heD d hd
    have h1 : b * d ^ 2 * b⁻¹ = d ^ 2 := by
      rw [sq]
      calc b * (d * d) * b⁻¹
          = ((b * d * b⁻¹ * d⁻¹) * d) * ((b * d * b⁻¹ * d⁻¹) * d) := by group
        _ = ((b * d * b⁻¹ * d⁻¹) * (b * d * b⁻¹ * d⁻¹)) * (d * d) := by
            rw [mul_assoc (b * d * b⁻¹ * d⁻¹) d, ← mul_assoc d, ← hed]; group
        _ = d * d := by rw [he2, one_mul]
    calc d ^ 2 * b = (b * d ^ 2 * b⁻¹) * b := by rw [h1]
      _ = b * d ^ 2 := by group
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  change y ∈ Subgroup.closure {z | ∃ g ∈ D, z = g ^ 2} at hy
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨g, hg, rfl⟩ := hz
    exact key g hg
  | one => simp
  | mul x y _ _ hx hy =>
    calc x * y * b = x * (y * b) := by group
      _ = x * (b * y) := by rw [hy]
      _ = (x * b) * y := by group
      _ = (b * x) * y := by rw [hx]
      _ = b * (x * y) := by group
  | inv x _ hx =>
    calc x⁻¹ * b = x⁻¹ * (b * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * b) * x⁻¹ := by rw [hx]
      _ = b * x⁻¹ := by group

end Comm

section Count

variable {G : Type} [Group G] [Finite G]

theorem relIndex_le_two_pow {B₀ D : Subgroup G} (hB₀ : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x)
    (h2 : ∀ Q : Subgroup G, Q ≤ B₀ → (∀ q ∈ Q, q * q ∈ D) → D.relIndex Q ≤ 2) :
    ∀ (j : ℕ) (B : Subgroup G), B ≤ B₀ → (∀ b ∈ B, b ^ (2 ^ j) ∈ D) → D.relIndex B ≤ 2 ^ j := by
  intro j
  induction j with
  | zero =>
    intro B _ hj
    have hle : B ≤ D := fun b hb => by simpa using hj b hb
    rw [Subgroup.relIndex_eq_one.mpr hle]
    simp
  | succ j ih =>
    intro B hBB₀ hj
    have hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
      hB₀ x (hBB₀ hx) y (hBB₀ hy)
    have hB'B : CFSG.GroupTheory.HuppertProduct.mho B 2 ≤ B := mho_le B 2
    have hj' : ∀ b ∈ CFSG.GroupTheory.HuppertProduct.mho B 2, b ^ (2 ^ j) ∈ D := by
      intro b hb
      obtain ⟨c, hc, rfl⟩ := (mem_mho_iff_exists_pow_of_comm hB).mp hb
      rw [← pow_mul, ← pow_succ']
      exact hj c hc
    have ih' := ih (CFSG.GroupTheory.HuppertProduct.mho B 2) (hB'B.trans hBB₀) hj'
    let sq : ↥B →* G :=
      { toFun := fun x => (x : G) * x
        map_one' := by simp
        map_mul' := fun x y => by
          have h := hB x x.2 y y.2
          simp only [Subgroup.coe_mul]
          calc (x : G) * y * (x * y) = x * (y * x) * y := by group
            _ = x * (x * y) * y := by rw [h]
            _ = x * x * (y * y) := by group }
    have hrange : sq.range = CFSG.GroupTheory.HuppertProduct.mho B 2 := by
      ext z
      rw [MonoidHom.mem_range, mem_mho_iff_exists_pow_of_comm hB]
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.2, by simp [sq, pow_two]⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, by simp [sq, pow_two]⟩
    have hle : D.subgroupOf B ≤ D.comap sq := fun x hx => D.mul_mem hx hx
    have h1 : (D.comap sq).index = D.relIndex (CFSG.GroupTheory.HuppertProduct.mho B 2) := by
      rw [Subgroup.index_comap, hrange]
    have hQ : ∀ q ∈ (D.comap sq).map B.subtype, q * q ∈ D := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have hQsub : ((D.comap sq).map B.subtype).subgroupOf B = D.comap sq :=
      Subgroup.comap_map_eq_self_of_injective B.subtype_injective _
    have h3 : (D.subgroupOf B).relIndex (D.comap sq) = D.relIndex ((D.comap sq).map B.subtype) := by
      rw [← Subgroup.relIndex_subgroupOf (Subgroup.map_subtype_le (D.comap sq)), hQsub]
    calc D.relIndex B = (D.subgroupOf B).index := rfl
      _ = (D.subgroupOf B).relIndex (D.comap sq) * (D.comap sq).index :=
          (Subgroup.relIndex_mul_index hle).symm
      _ ≤ 2 * 2 ^ j :=
          Nat.mul_le_mul (h3 ▸ h2 _ ((Subgroup.map_subtype_le _).trans hBB₀) hQ) (h1 ▸ ih')
      _ = 2 ^ (j + 1) := by ring

theorem two_pow_mul_card_le {D : Subgroup G} (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {b : G}
    (hb : b ∈ Subgroup.normalizer (D : Set G)) {d₁ d₂ : G} (hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D) {j : ℕ}
    (h1 : (b⁻¹ * d₁ * b * d₁⁻¹) ^ (2 ^ j) ≠ 1)
    (h1' : (b⁻¹ * d₁ * b * d₁⁻¹) ^ (2 ^ (j + 1)) = 1)
    (h2 : ∀ k : ℤ, b⁻¹ * d₂ * b * d₂⁻¹ ≠ (b⁻¹ * d₁ * b * d₁⁻¹) ^ k) :
    2 ^ (j + 2) * Nat.card ↥(D ⊓ Subgroup.centralizer ({b} : Set G)) ≤ Nat.card D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := card_inf_centralizer_mul_card_range hD hb
  set φ := commHom hD hb with hφ
  have hz₁ : ((φ ⟨d₁, hd₁⟩ : ↥D) : G) = b⁻¹ * d₁ * b * d₁⁻¹ := coe_commHom hD hb _
  have hz₂ : ((φ ⟨d₂, hd₂⟩ : ↥D) : G) = b⁻¹ * d₂ * b * d₂⁻¹ := coe_commHom hD hb _
  have hord : orderOf (φ ⟨d₁, hd₁⟩) = 2 ^ (j + 1) := by
    apply orderOf_eq_prime_pow
    · intro h
      apply h1
      rw [← hz₁, ← Subgroup.coe_pow, h, Subgroup.coe_one]
    · apply Subtype.ext
      rw [Subgroup.coe_pow, hz₁, h1', Subgroup.coe_one]
  have hle : Subgroup.zpowers (φ ⟨d₁, hd₁⟩) ≤ φ.range :=
    (Subgroup.zpowers_le).mpr ⟨_, rfl⟩
  have hnot : φ ⟨d₂, hd₂⟩ ∉ Subgroup.zpowers (φ ⟨d₁, hd₁⟩) := by
    rintro ⟨k, hk⟩
    apply h2 k
    rw [← hz₂, ← hk, Subgroup.coe_zpow, hz₁]
  have hrel : (Subgroup.zpowers (φ ⟨d₁, hd₁⟩)).relIndex φ.range ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro h
    exact hnot (h ⟨_, rfl⟩)
  have hmul := Subgroup.relIndex_mul_card (Subgroup.zpowers (φ ⟨d₁, hd₁⟩)) φ.range
  rw [inf_of_le_left hle, Nat.card_zpowers, hord] at hmul
  have hrel0 : (Subgroup.zpowers (φ ⟨d₁, hd₁⟩)).relIndex φ.range ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact Nat.card_pos.ne' hmul.symm
  have hrange : 2 ^ (j + 2) ≤ Nat.card φ.range := by
    rw [← hmul, pow_succ, mul_comm]
    exact Nat.mul_le_mul_right _ (by omega)
  calc 2 ^ (j + 2) * Nat.card ↥(D ⊓ Subgroup.centralizer ({b} : Set G))
      ≤ Nat.card φ.range * Nat.card ↥(D ⊓ Subgroup.centralizer ({b} : Set G)) :=
        Nat.mul_le_mul_right _ hrange
    _ = Nat.card D := by rw [mul_comm]; exact hcard

end Count

section Shape

theorem two_pow_nsmul_eq_zero_iff {a i : ℕ} (hi : i ≤ a) (x : ZMod (2 ^ a)) :
    (2 ^ i : ℕ) • x = 0 ↔
      ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le a i)) (ZMod (2 ^ (a - i))) x = 0 := by
  have : NeZero (2 ^ a) := ⟨by positivity⟩
  have hsplit : 2 ^ a = 2 ^ i * 2 ^ (a - i) := by rw [← pow_add, Nat.add_sub_cancel' hi]
  have h1 : (2 ^ i : ℕ) • x = ((2 ^ i * x.val : ℕ) : ZMod (2 ^ a)) := by
    rw [nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_zmod_val]
  have h2 : ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le a i)) (ZMod (2 ^ (a - i))) x =
      ((x.val : ℕ) : ZMod (2 ^ (a - i))) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [h1, h2, ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff]
  have h3 := Nat.mul_dvd_mul_iff_left (a := 2 ^ i) (b := 2 ^ (a - i)) (c := x.val) (by positivity)
  rwa [← hsplit] at h3

noncomputable def torusRedPow (k : Fin 3 → ℕ) (i : ℕ) : Torus k →+ Torus (fun j => k j - i) where
  toFun v j := ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le (k j) i)) (ZMod (2 ^ (k j - i))) (v j)
  map_zero' := by funext j; exact map_zero _
  map_add' v w := by funext j; exact map_add _ _ _

theorem torusRedPow_surjective (k : Fin 3 → ℕ) (i : ℕ) : Function.Surjective (torusRedPow k i) := by
  intro w
  refine ⟨fun j => ((w j).val : ZMod (2 ^ k j)), ?_⟩
  funext j
  show ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le (k j) i)) (ZMod (2 ^ (k j - i)))
    (((w j).val : ℕ) : ZMod (2 ^ k j)) = w j
  rw [map_natCast, ZMod.natCast_zmod_val]

variable {G : Type} [Group G] [Finite G]

theorem nonempty_mho_two_pow_addEquiv {X : Subgroup G} {k : Fin 3 → ℕ} (e : Additive X ≃+ Torus k)
    {i : ℕ} (hi : ∀ j, i ≤ k j) :
    Nonempty (Additive ↥(CFSG.GroupTheory.HuppertProduct.mho X (2 ^ i)) ≃+ Torus (fun j => k j - i)) := by
  have hX := comm_of_torus e
  let ι : ↥(CFSG.GroupTheory.HuppertProduct.mho X (2 ^ i)) →* ↥X := Subgroup.inclusion (mho_le X _)
  let f : Additive ↥(CFSG.GroupTheory.HuppertProduct.mho X (2 ^ i)) →+ Torus k :=
    e.toAddMonoidHom.comp (MonoidHom.toAdditive ι)
  have hf : Function.Injective f :=
    e.injective.comp (Subgroup.inclusion_injective (mho_le X _))
  let nN : Torus k →+ Torus k :=
    { toFun := fun v => (2 ^ i : ℕ) • v
      map_zero' := smul_zero _
      map_add' := fun v w => smul_add _ v w }
  have hf_apply : ∀ y, f y = e (Additive.ofMul (ι (Additive.toMul y))) := fun _ => rfl
  have hnN : ∀ v, nN v = (2 ^ i : ℕ) • v := fun _ => rfl
  have hrange : f.range = nN.range := by
    ext v
    simp only [AddMonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨w, hw, hwz⟩ := (mem_mho_iff_exists_pow_of_comm hX).mp (Additive.toMul y).2
      refine ⟨e (Additive.ofMul (⟨w, hw⟩ : ↥X)), ?_⟩
      have h1 : ι (Additive.toMul y) = (⟨w, hw⟩ : ↥X) ^ (2 ^ i) := by
        apply Subtype.ext
        simp [ι, hwz]
      rw [hnN, hf_apply, h1, ofMul_pow, map_nsmul]
    · rintro ⟨v, rfl⟩
      set w : ↥X := Additive.toMul (e.symm v)
      refine ⟨Additive.ofMul ⟨(w : G) ^ (2 ^ i), pow_mem_mho w.2⟩, ?_⟩
      have h1 : ι ⟨(w : G) ^ (2 ^ i), pow_mem_mho w.2⟩ = w ^ (2 ^ i) := Subtype.ext (by simp [ι])
      rw [hnN, hf_apply, toMul_ofMul, h1, ofMul_pow, map_nsmul]
      simp [w]
  have hker : nN.ker = (torusRedPow k i).ker := by
    ext v
    simp only [AddMonoidHom.mem_ker]
    constructor
    · intro h
      funext j
      have hj : (2 ^ i : ℕ) • v j = 0 := by simpa [hnN] using congrFun h j
      exact (two_pow_nsmul_eq_zero_iff (hi j) (v j)).mp hj
    · intro h
      rw [hnN]
      funext j
      exact (two_pow_nsmul_eq_zero_iff (hi j) (v j)).mpr (congrFun h j)
  exact ⟨(AddMonoidHom.ofInjective hf).trans ((AddEquiv.addSubgroupCongr hrange).trans
    ((QuotientAddGroup.quotientKerEquivRange nN).symm.trans
      ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
        (QuotientAddGroup.quotientKerEquivOfSurjective _ (torusRedPow_surjective k i)))))⟩

def torusProdAddEquiv (a b c : ℕ) :
    Torus ![a, b, c] ≃+ ZMod (2 ^ a) × ZMod (2 ^ b) × ZMod (2 ^ c) where
  toFun v := (v 0, v 1, v 2)
  invFun p := Fin.cons (α := fun j => ZMod (2 ^ (![a, b, c] j))) p.1
    (Fin.cons (α := fun j : Fin 2 => ZMod (2 ^ (![a, b, c] j.succ))) p.2.1
      (Fin.cons (α := fun j : Fin 1 => ZMod (2 ^ (![a, b, c] j.succ.succ))) p.2.2 finZeroElim))
  left_inv v := by funext j; fin_cases j <;> rfl
  right_inv p := rfl
  map_add' v w := rfl

theorem nonempty_torus_sub_addEquiv_prod (τ : StrothTypeIndex) (i : ℕ) :
    Nonempty (Torus (fun j => τ.k j - i) ≃+
      (ZMod (2 ^ (τ.m - i)) × ZMod (2 ^ (τ.n - i)) × ZMod (2 ^ (τ.n - i)))) := by
  have h : ∀ j, 2 ^ (τ.k j - i) = 2 ^ (![τ.m - i, τ.n - i, τ.n - i] j) := by
    intro j
    rw [τ.k_eq]
    fin_cases j <;> rfl
  exact ⟨(AddEquiv.piCongrRight fun j => (ZMod.ringEquivCongr (h j)).toAddEquiv).trans
    (torusProdAddEquiv _ _ _)⟩

end Shape

section Frame

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pow_two_pow_eq_one_of_le {X : Subgroup G} {k : Fin 3 → ℕ} (e : Additive X ≃+ Torus k)
    {N : ℕ} (hk : ∀ j, k j ≤ N) {y : G} (hy : y ∈ X) : y ^ (2 ^ N) = 1 := by
  have h : (2 ^ N : ℕ) • e (Additive.ofMul (⟨y, hy⟩ : X)) = 0 := by
    funext j
    rw [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply]
    have h0 : ((2 ^ N : ℕ) : ZMod (2 ^ k j)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (pow_dvd_pow 2 (hk j))
    rw [h0, zero_mul]
  have h2 : (⟨y, hy⟩ : X) ^ (2 ^ N) = 1 := by
    apply Additive.ofMul.injective
    apply e.injective
    rw [ofMul_pow, map_nsmul, h, ofMul_one, map_zero]
  simpa using congrArg Subtype.val h2

omit [Finite G] in
theorem mem_zpowers_c_sup_mhoOne {D : Subgroup G} {τ : StrothTypeIndex}
    (dD : StrothWeakTypeData D τ) (hfam : τ.m + 2 = τ.n) {y : G} (hy : y ∈ D)
    (hy2 : y ^ (2 ^ τ.m) = 1) :
    y ∈ Subgroup.zpowers ((dD.c : D) : G) ⊔ mhoOne D := by
  set v : Torus τ.k := dD.e (Additive.ofMul (⟨y, hy⟩ : D)) with hv
  have hv0 : (2 ^ τ.m : ℕ) • v = 0 := by
    have h1 : (⟨y, hy⟩ : D) ^ (2 ^ τ.m) = 1 := Subtype.ext (by simpa using hy2)
    rw [hv, ← map_nsmul, ← ofMul_pow, h1, ofMul_one, map_zero]
  have hdiv : ∀ j : Fin 3, j ≠ 0 → 2 ∣ (v j).val := by
    intro j hj
    have hkj : τ.k j = τ.m + 2 := by
      rw [τ.k_eq]
      fin_cases j
      · exact absurd rfl hj
      · simpa using hfam.symm
      · simpa using hfam.symm
    have hj0 : (2 ^ τ.m : ℕ) • v j = 0 := by simpa using congrFun hv0 j
    have : NeZero (2 ^ τ.k j) := ⟨by positivity⟩
    rw [nsmul_eq_mul, ← ZMod.natCast_zmod_val (v j), ← Nat.cast_mul,
      ZMod.natCast_eq_zero_iff] at hj0
    have hj0' : 2 ^ τ.m * 2 ^ 2 ∣ 2 ^ τ.m * (v j).val := by
      rw [← pow_add, ← hkj]
      exact hj0
    have h4 : 2 ^ 2 ∣ (v j).val := Nat.dvd_of_mul_dvd_mul_left (by positivity) hj0'
    exact Nat.dvd_trans (by norm_num : 2 ∣ 2 ^ 2) h4
  set w : Torus τ.k := fun j => (((if j = 0 then 0 else (v j).val / 2 : ℕ)) : ZMod (2 ^ τ.k j))
    with hw
  have hvw : v = (v 0).val • (Torus.c : Torus τ.k) + 2 • w := by
    funext j
    have : NeZero (2 ^ τ.k j) := ⟨by positivity⟩
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    by_cases hj : j = 0
    · subst hj
      have hc0 : (Torus.c : Torus τ.k) 0 = 1 := by simp [gen]
      have hw0 : w 0 = 0 := by simp [w]
      rw [hc0, hw0, smul_zero, add_zero, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    · have hcj : (Torus.c : Torus τ.k) j = 0 := by simp [gen, hj]
      have hwj : w j = (((v j).val / 2 : ℕ) : ZMod (2 ^ τ.k j)) := by simp [w, hj]
      rw [hcj, smul_zero, zero_add, hwj, nsmul_eq_mul, ← Nat.cast_mul,
        Nat.mul_div_cancel' (hdiv j hj), ZMod.natCast_zmod_val]
  have hy' : (⟨y, hy⟩ : D) =
      dD.c ^ (v 0).val * (Additive.toMul (dD.e.symm w)) ^ 2 := by
    apply Additive.ofMul.injective
    apply dD.e.injective
    have h1 : dD.e (Additive.ofMul (dD.c ^ (v 0).val * (Additive.toMul (dD.e.symm w)) ^ 2)) =
        (v 0).val • (Torus.c : Torus τ.k) + 2 • w := by
      rw [ofMul_mul, ofMul_pow, ofMul_pow, map_add, map_nsmul, map_nsmul]
      simp only [StrothWeakTypeData.c, ofMul_toMul, AddEquiv.apply_symm_apply]
    rw [h1, ← hv]
    exact hvw
  have hyG : y = ((dD.c : D) : G) ^ (v 0).val * ((Additive.toMul (dD.e.symm w) : D) : G) ^ 2 := by
    simpa using congrArg Subtype.val hy'
  rw [hyG]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
    (Subgroup.mem_sup_right (pow_mem_mho (Additive.toMul (dD.e.symm w)).2))

theorem exists_eq_of_mem_commutator {D : Subgroup G} (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    {s : G} (hs : s ∈ Subgroup.normalizer (D : Set G)) (hss : s * s ∈ D) {z : G}
    (hz : z ∈ ⁅Subgroup.zpowers s, D⁆) : ∃ d ∈ D, s * d * s⁻¹ * d⁻¹ = z := by
  set φ := commHom hD (Subgroup.inv_mem _ hs)
  have hφ : ∀ d (hd : d ∈ D), ((φ ⟨d, hd⟩ : D) : G) = s * d * s⁻¹ * d⁻¹ := by
    intro d hd
    rw [coe_commHom, inv_inv]
  have hle : ⁅Subgroup.zpowers s, D⁆ ≤ φ.range.map D.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx d hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hs2 : s ^ (2 : ℤ) ∈ D := by rw [zpow_two]; exact hss
    have hsd : s * d * s⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hs d).mp hd
    rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
    · have ht : s ^ (2 * j) ∈ D := by rw [zpow_mul]; exact D.zpow_mem hs2 j
      have hc : s ^ (2 * j) * d = d * s ^ (2 * j) := hD _ ht d hd
      have : ⁅s ^ (2 * j), d⁆ = 1 := by
        rw [commutatorElement_def, hc]; group
      rw [this]
      exact Subgroup.one_mem _
    · have ht : s ^ (2 * j) ∈ D := by rw [zpow_mul]; exact D.zpow_mem hs2 j
      have hc : s ^ (2 * j) * (s * d * s⁻¹) = (s * d * s⁻¹) * s ^ (2 * j) := hD _ ht _ hsd
      have : ⁅s ^ (2 * j + 1), d⁆ = s * d * s⁻¹ * d⁻¹ := by
        rw [commutatorElement_def, zpow_add_one]
        calc s ^ (2 * j) * s * d * (s ^ (2 * j) * s)⁻¹ * d⁻¹
            = s ^ (2 * j) * (s * d * s⁻¹) * (s ^ (2 * j))⁻¹ * d⁻¹ := by group
          _ = (s * d * s⁻¹) * s ^ (2 * j) * (s ^ (2 * j))⁻¹ * d⁻¹ := by rw [hc]
          _ = s * d * s⁻¹ * d⁻¹ := by group
      rw [this]
      exact ⟨φ ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩, hφ d hd⟩
  obtain ⟨_, ⟨⟨d, hd⟩, rfl⟩, hzd⟩ := hle hz
  exact ⟨d, hd, (hφ d hd).symm.trans hzd⟩

theorem frame_commutator_rho_omega (F : StrothFrame G) :
    ((F.dA.a : F.A) : G) ^ 2 ∈ ⁅Subgroup.zpowers F.dA.ρ, omegaIn 1 F.A⁆ ∧
      ((F.dA.b : F.A) : G) ^ 2 ∈ ⁅Subgroup.zpowers F.dA.ρ, omegaIn 1 F.A⁆ ∧
      ((F.dA.a : F.A) : G) ^ 2 ≠ 1 ∧ ((F.dA.b : F.A) : G) ^ 2 ≠ 1 ∧
      ((F.dA.a : F.A) : G) ^ 2 ≠ ((F.dA.b : F.A) : G) ^ 2 ∧
      ((F.dA.a : F.A) : G) ^ 2 * ((F.dA.a : F.A) : G) ^ 2 = 1 := by
  set a₂ := ((F.dA.a : F.A) : G) ^ 2
  set b₂ := ((F.dA.b : F.A) : G) ^ 2
  set ρ := F.dA.ρ
  have hra : ρ⁻¹ * a₂ * ρ = b₂ := Stroth43Fus.t100_rho_a₁ F.dA le_rfl
  have hrb : ρ⁻¹ * b₂ * ρ = a₂ * b₂ := Stroth43Fus.t100_rho_b₁ F.dA le_rfl
  have hua : F.dA.u⁻¹ * a₂ * F.dA.u = b₂ := Stroth43Fus.t100_u_a₁ F.dA
  have ha1 : a₂ ≠ 1 := Stroth43Fus.t100_a₁_ne_one F.dA le_rfl
  have ha2 : a₂ * a₂ = 1 := Stroth43Fus.t100_a₁_mul_self F.dA le_rfl
  have hb2 : b₂ * b₂ = 1 := Stroth43Fus.t100_b₁_mul_self F.dA le_rfl
  have haA : a₂ ∈ omegaIn 1 F.A := mem_omegaIn_one_of_mul_self (F.A.pow_mem (F.dA.a).2 2) ha2
  have hbA : b₂ ∈ omegaIn 1 F.A := mem_omegaIn_one_of_mul_self (F.A.pow_mem (F.dA.b).2 2) hb2
  have hρ : ρ⁻¹ ∈ Subgroup.zpowers ρ := Subgroup.inv_mem _ (Subgroup.mem_zpowers ρ)
  have hcb : ⁅ρ⁻¹, b₂⁆ = a₂ := by
    rw [commutatorElement_def, inv_inv]
    calc ρ⁻¹ * b₂ * ρ * b₂⁻¹ = (ρ⁻¹ * b₂ * ρ) * b₂⁻¹ := rfl
      _ = a₂ := by rw [hrb]; group
  have hca : ⁅ρ⁻¹, a₂⁆ * a₂ = b₂ := by
    rw [commutatorElement_def, inv_inv]
    calc ρ⁻¹ * a₂ * ρ * a₂⁻¹ * a₂ = ρ⁻¹ * a₂ * ρ := by group
      _ = b₂ := hra
  have hmema : a₂ ∈ ⁅Subgroup.zpowers ρ, omegaIn 1 F.A⁆ :=
    hcb ▸ Subgroup.commutator_mem_commutator hρ hbA
  have hmemb : b₂ ∈ ⁅Subgroup.zpowers ρ, omegaIn 1 F.A⁆ :=
    hca ▸ Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator hρ haA) hmema
  have hb1 : b₂ ≠ 1 := by
    intro h
    apply ha1
    calc a₂ = F.dA.u * (F.dA.u⁻¹ * a₂ * F.dA.u) * F.dA.u⁻¹ := by group
      _ = 1 := by rw [hua, h]; group
  have hab : a₂ ≠ b₂ := by
    intro h
    apply hb1
    calc b₂ = ρ * (ρ⁻¹ * b₂ * ρ) * ρ⁻¹ := by group
      _ = 1 := by rw [hrb, ← h, ha2]; group
  exact ⟨hmema, hmemb, ha1, hb1, hab, ha2⟩

end Frame

end Stroth226I

open Stroth226I

theorem StrothFrame.IsD.false_of_le_R_of_le_normalizer_of_two_le
    (H2b : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
      {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 1 = τ.n →
      2 ≤ τ.m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ (k : ℕ), k ≤ τ.n - 1 → ∀ (B : Subgroup G),
        B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) →
        Nonempty (Additive ↥B ≃+ (ZMod (2 ^ k) × ZMod (2 ^ (k + 1)) × ZMod (2 ^ (k + 1)))) →
        B ≤ D)
    (H3two : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
      {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 2 = τ.n →
      2 ≤ τ.m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ (k : ℕ), k ≤ τ.n - 2 → ∀ (B : Subgroup G),
        B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) →
        Nonempty (Additive ↥B ≃+ (ZMod (2 ^ k) × ZMod (2 ^ (k + 2)) × ZMod (2 ^ (k + 2)))) →
        B ≤ Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G))
    (H3three : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
      {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 2 = τ.n →
      2 ≤ τ.m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
          Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) ≠ D →
      ∃ s ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
          Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
            Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) =
          D ⊔ Subgroup.zpowers s ∧
        s * s = (dD.c : G) ∧ ⁅Subgroup.zpowers s, D⁆ = ⁅Subgroup.zpowers dD.ρ, omegaIn 1 D⁆)
    {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex}
    {dD : StrothWeakTypeData D τ} (h : F.IsD D dD)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    (hfam : τ.m + 1 = τ.n ∨ τ.m + 2 = τ.n) (hm : 2 ≤ τ.m) {B : Subgroup G}
    (hBR : B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G))
    (hDB : D ≤ Subgroup.normalizer (B : Set G))
    (hne : B ≠ D) (hconj : ∃ g : G, B = D.map (MulAut.conj g).toMonoidHom) : False := by
  classical
  obtain ⟨g, hBg⟩ := hconj
  have hφg : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  let eDB : ↥D ≃* ↥B :=
    (Subgroup.equivMapOfInjective D _ hφg).trans (MulEquiv.subgroupCongr hBg.symm)
  let eB : Additive ↥B ≃+ Torus τ.k := (MulEquiv.toAdditive eDB.symm).trans dD.e
  have hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := comm_of_torus dD.e
  have hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := comm_of_torus eB
  have hcard : Nat.card B = Nat.card D := (Nat.card_congr eDB.toEquiv).symm
  have hBS : ∀ x ∈ B, x ∈ (F.S : Subgroup G) := fun x hx => (hBR hx).1.1
  have hBN : B ≤ Subgroup.normalizer (D : Set G) := fun x hx => (hBR hx).1.2
  have hBΩ : ∀ x ∈ B, x ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) :=
    fun x hx => (hBR hx).2
  have hBD : ¬ B ≤ D := fun hle => hne (Subgroup.eq_of_le_of_card_ge hle hcard.ge)
  have hmn : τ.m ≤ τ.n := by rcases hfam with h' | h' <;> omega
  have hn2m : τ.n - 2 ≤ τ.m := by rcases hfam with h' | h' <;> omega
  have hn3 : 3 ≤ τ.n := by rcases hfam with h' | h' <;> omega
  have hkn : ∀ j, τ.k j ≤ τ.n := by
    intro j; rw [τ.k_eq]; fin_cases j <;> simp [hmn]
  have hkm : ∀ j, τ.m ≤ τ.k j := by
    intro j; rw [τ.k_eq]; fin_cases j <;> simp [hmn]
  have hexp : ∀ b ∈ B, b ^ (2 ^ (τ.n - 1)) ∈ D := by
    intro b hb
    rw [← h.cent]
    refine ⟨(F.S : Subgroup G).pow_mem (hBS b hb) _, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro d hd
    have hbinv : b⁻¹ ∈ Subgroup.normalizer (D : Set G) := Subgroup.inv_mem _ (hBN hb)
    have hψ : ∀ x (hx : x ∈ D), ((commHom hD hbinv ⟨x, hx⟩ : D) : G) = b * x * b⁻¹ * x⁻¹ := by
      intro x hx
      rw [coe_commHom, inv_inv]
    have hdN : d ^ (2 ^ (τ.n - 1)) ∈ omegaIn 1 D := by
      rw [mem_omegaIn_iff_of_comm hD]
      refine ⟨D.pow_mem hd _, ?_⟩
      rw [← pow_mul, ← pow_add, Nat.sub_add_cancel (by omega)]
      exact pow_two_pow_eq_one_of_le dD.e hkn hd
    have h1 : b * d ^ (2 ^ (τ.n - 1)) * b⁻¹ * (d ^ (2 ^ (τ.n - 1)))⁻¹ = 1 := by
      have hc := Subgroup.mem_centralizer_iff.mp (hBΩ b hb) _ hdN
      rw [← hc]
      group
    have h2 : (b * d * b⁻¹ * d⁻¹) ^ (2 ^ (τ.n - 1)) = 1 := by
      rw [← hψ d hd, ← Subgroup.coe_pow, ← map_pow]
      have hpow : (⟨d, hd⟩ : D) ^ (2 ^ (τ.n - 1)) = ⟨d ^ (2 ^ (τ.n - 1)), D.pow_mem hd _⟩ := rfl
      rw [hpow, hψ, h1]
    have h3 := commutator_pow hB hBN hDB hb hd (2 ^ (τ.n - 1))
    rw [h2] at h3
    calc d * b ^ (2 ^ (τ.n - 1))
        = (b ^ (2 ^ (τ.n - 1)) * d * (b ^ (2 ^ (τ.n - 1)))⁻¹ * d⁻¹)⁻¹ *
            (b ^ (2 ^ (τ.n - 1)) * d) := by group
      _ = b ^ (2 ^ (τ.n - 1)) * d := by rw [h3]; group
  have hex : ∃ j, ∀ b ∈ B, b ^ (2 ^ j) ∈ D := ⟨τ.n - 1, hexp⟩
  have hj₀ := Nat.find_spec hex
  have hj₀le : Nat.find hex ≤ τ.n - 1 := Nat.find_min' hex hexp
  have hj₀pos : Nat.find hex ≠ 0 := by
    intro h0
    apply hBD
    intro b hb
    have hb' := hj₀ b hb
    rwa [h0, pow_zero, pow_one] at hb'
  obtain ⟨b₀, hb₀B, hb₀D⟩ : ∃ b₀ ∈ B, b₀ ^ (2 ^ (Nat.find hex - 1)) ∉ D := by
    have h' := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push Not at h'
    exact h'
  set i := Nat.find hex - 1 with hi_def
  have hi1 : ∀ b ∈ B, b ^ (2 ^ (i + 1)) ∈ D := by
    rw [show i + 1 = Nat.find hex by omega]
    exact hj₀
  have him : i ≤ τ.m := by omega
  have hB₁mem : ∀ x ∈ CFSG.GroupTheory.HuppertProduct.mho B (2 ^ i), x ∈ B ∧ x * x ∈ D := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := (mem_mho_iff_exists_pow_of_comm hB).mp hx
    refine ⟨B.pow_mem hb _, ?_⟩
    rw [← pow_two, ← pow_mul, ← pow_succ]
    exact hi1 b hb
  have hB₁K : CFSG.GroupTheory.HuppertProduct.mho B (2 ^ i) ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) := by
    intro x hx
    obtain ⟨hxB, hxx⟩ := hB₁mem x hx
    exact ⟨(hBR hxB).1, mem_centralizer_mhoOne hB hD hBN hDB hxB hxx⟩
  have hB₁D : ¬ CFSG.GroupTheory.HuppertProduct.mho B (2 ^ i) ≤ D := fun hle => hb₀D (hle (pow_mem_mho hb₀B))
  obtain ⟨e₁⟩ := nonempty_mho_two_pow_addEquiv eB (fun j => him.trans (hkm j))
  obtain ⟨e₂⟩ := nonempty_torus_sub_addEquiv_prod τ i
  have hshape : Nonempty (Additive ↥(CFSG.GroupTheory.HuppertProduct.mho B (2 ^ i)) ≃+
      (ZMod (2 ^ (τ.m - i)) × ZMod (2 ^ (τ.n - i)) × ZMod (2 ^ (τ.n - i)))) := ⟨e₁.trans e₂⟩
  rcases hfam with hfam1 | hfam2
  ·
    have e3 : τ.n - i = τ.m - i + 1 := by omega
    rw [e3] at hshape
    exact hB₁D (H2b h hfam1 hm hns (τ.m - i) (by omega) _ hB₁K hshape)
  ·
    have e3 : τ.n - i = τ.m - i + 2 := by omega
    rw [e3] at hshape
    have hB₁Ω := H3two h hfam2 hm hns (τ.m - i) (by omega) _ hB₁K hshape
    set R₂ := (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
      Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) with hR₂
    have hB₁R₂ : CFSG.GroupTheory.HuppertProduct.mho B (2 ^ i) ≤ R₂ := fun x hx => ⟨hB₁K hx, hB₁Ω hx⟩
    have hR₂ne : R₂ ≠ D := fun heq => hB₁D (heq ▸ hB₁R₂)
    obtain ⟨s, hsR₂, hR₂eq, hss, hW⟩ := H3three h hfam2 hm hns hR₂ne
    have hsN : s ∈ Subgroup.normalizer (D : Set G) := hsR₂.1.1.2
    have hsΩ : s ∈ Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) := hsR₂.2
    have hss' : s * s ∈ D := by rw [hss]; exact (dD.c).2
    have hxB : b₀ ^ (2 ^ i) ∈ B := B.pow_mem hb₀B _
    have hxs : b₀ ^ (2 ^ i) ∈ D ⊔ Subgroup.zpowers s := hR₂eq ▸ hB₁R₂ (pow_mem_mho hb₀B)
    have hd₀ : s⁻¹ * b₀ ^ (2 ^ i) ∈ D :=
      (mem_or_inv_mul_mem_of_mem_sup_zpowers hsN hss' hxs).resolve_left hb₀D
    have hxsd : b₀ ^ (2 ^ i) = s * (s⁻¹ * b₀ ^ (2 ^ i)) := by group
    have hT1 : ∀ b ∈ B, b * b ∈ D → b ∈ R₂ := by
      intro b hb hbb
      have hbC : b ∈ Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) :=
        mem_centralizer_mhoOne hB hD hBN hDB hb hbb
      refine ⟨⟨(hBR hb).1, hbC⟩, ?_⟩
      set d₀ := s⁻¹ * b₀ ^ (2 ^ i) with hd₀_def
      set e := b * d₀ * b⁻¹ * d₀⁻¹ with he_def
      have he2 : e * e = 1 := commutator_mul_self_eq_one hB hD hBN hDB hb hbb hd₀
      have heD : e ∈ D := (commutator_mem_inf hBN hDB hb hd₀).2
      have heΩ : e ∈ omegaIn (τ.n - 2) D := by
        rw [mem_omegaIn_iff_of_comm hD]
        refine ⟨heD, ?_⟩
        obtain ⟨t, ht⟩ : 2 ∣ 2 ^ (τ.n - 2) := dvd_pow_self 2 (by omega)
        rw [ht, pow_mul, sq, he2, one_pow]
      have hse : e * s = s * e := Subgroup.mem_centralizer_iff.mp hsΩ e heΩ
      have hbx : b * b₀ ^ (2 ^ i) = b₀ ^ (2 ^ i) * b := hB b hb _ hxB
      have hbs : b * s * b⁻¹ = s * e⁻¹ := by
        have hbd : b * d₀ * b⁻¹ = e * d₀ := by rw [he_def]; group
        calc b * s * b⁻¹ = (b * (s * d₀) * b⁻¹) * (b * d₀ * b⁻¹)⁻¹ := by group
          _ = (b * b₀ ^ (2 ^ i) * b⁻¹) * (e * d₀)⁻¹ := by rw [← hxsd, hbd]
          _ = b₀ ^ (2 ^ i) * (e * d₀)⁻¹ := by rw [hbx]; group
          _ = s * e⁻¹ := by
              rw [hxsd]
              group
      have hes : e⁻¹ * s = s * e⁻¹ := by
        calc e⁻¹ * s = e⁻¹ * (s * e) * e⁻¹ := by group
          _ = e⁻¹ * (e * s) * e⁻¹ := by rw [hse]
          _ = s * e⁻¹ := by group
      have hbc : b * (s * s) = (s * s) * b := by
        calc b * (s * s) = (b * s * b⁻¹) * (b * s * b⁻¹) * b := by group
          _ = s * e⁻¹ * (s * e⁻¹) * b := by rw [hbs]
          _ = s * (e⁻¹ * s) * e⁻¹ * b := by group
          _ = s * (s * e⁻¹) * e⁻¹ * b := by rw [hes]
          _ = s * s * (e * e)⁻¹ * b := by group
          _ = s * s * b := by rw [he2]; group
      have hcb : (dD.c : G) * b = b * (dD.c : G) := by rw [← hss]; exact hbc.symm
      have hle : Subgroup.zpowers ((dD.c : D) : G) ⊔ mhoOne D ≤
          Subgroup.centralizer ({b} : Set G) := by
        refine sup_le ?_ ?_
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact hcb
        · intro z hz
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp hbC z hz
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro y hy
      have hyD := (mem_omegaIn_iff_of_comm hD).mp hy
      have hy2 : y ^ (2 ^ τ.m) = 1 := by
        rw [show τ.m = τ.n - 2 by omega]
        exact hyD.2
      have hy' := hle (mem_zpowers_c_sup_mhoOne dD hfam2 hyD.1 hy2)
      exact Subgroup.mem_centralizer_singleton_iff.mp hy'
    have hup : D.relIndex B ≤ 2 ^ (i + 1) :=
      relIndex_le_two_pow hB (fun Q hQB hQ => relIndex_le_two_of_le_sup_zpowers hsN hss'
        (fun q hq => hR₂eq ▸ hT1 q (hQB hq) (hQ q hq))) (i + 1) B le_rfl hi1
    obtain ⟨hmema, hmemb, ha1, hb1, hab, ha2⟩ := frame_commutator_rho_omega F
    rw [← h.ρ_eq, ← h.omegaIn_one_eq, ← hW] at hmema hmemb
    obtain ⟨d₁, hd₁, hd₁eq⟩ := exists_eq_of_mem_commutator hD hsN hss' hmema
    obtain ⟨d₂, hd₂, hd₂eq⟩ := exists_eq_of_mem_commutator hD hsN hss' hmemb
    have hxd : ∀ d ∈ D, b₀ ^ (2 ^ i) * d * (b₀ ^ (2 ^ i))⁻¹ * d⁻¹ = s * d * s⁻¹ * d⁻¹ := by
      intro d hd
      have hc : (s⁻¹ * b₀ ^ (2 ^ i)) * d = d * (s⁻¹ * b₀ ^ (2 ^ i)) := hD _ hd₀ d hd
      calc b₀ ^ (2 ^ i) * d * (b₀ ^ (2 ^ i))⁻¹ * d⁻¹
          = s * ((s⁻¹ * b₀ ^ (2 ^ i)) * d) * (s⁻¹ * b₀ ^ (2 ^ i))⁻¹ * s⁻¹ * d⁻¹ := by group
        _ = s * d * s⁻¹ * d⁻¹ := by rw [hc]; group
    have hpow : ∀ d ∈ D, (b₀ * d * b₀⁻¹ * d⁻¹) ^ (2 ^ i) = s * d * s⁻¹ * d⁻¹ := by
      intro d hd
      rw [← commutator_pow hB hBN hDB hb₀B hd, hxd d hd]
    have hz1 := (hpow d₁ hd₁).trans hd₁eq
    have hz2 := (hpow d₂ hd₂).trans hd₂eq
    have hz1' : (b₀ * d₁ * b₀⁻¹ * d₁⁻¹) ^ (2 ^ (i + 1)) = 1 := by
      rw [pow_succ, pow_mul, hz1, sq, ha2]
    have hz2' : ∀ k : ℤ, b₀ * d₂ * b₀⁻¹ * d₂⁻¹ ≠ (b₀ * d₁ * b₀⁻¹ * d₁⁻¹) ^ k := by
      intro k hk
      have hcomm : ((b₀ * d₁ * b₀⁻¹ * d₁⁻¹) ^ k) ^ (2 ^ i) =
          ((b₀ * d₁ * b₀⁻¹ * d₁⁻¹) ^ (2 ^ i)) ^ k := by
        rw [← zpow_natCast, ← zpow_natCast (b₀ * d₁ * b₀⁻¹ * d₁⁻¹), ← zpow_mul, ← zpow_mul,
          mul_comm]
      have hbk : ((F.dA.b : F.A) : G) ^ 2 = (((F.dA.a : F.A) : G) ^ 2) ^ k := by
        rw [← hz2, hk, hcomm, hz1]
      rcases Int.even_or_odd' k with ⟨t, rfl | rfl⟩
      · apply hb1
        rw [hbk, zpow_mul, zpow_two, ha2, one_zpow]
      · apply hab
        rw [hbk, zpow_add_one, zpow_mul, zpow_two, ha2, one_zpow, one_mul]
    have hb₀inv : b₀⁻¹ ∈ Subgroup.normalizer (D : Set G) := Subgroup.inv_mem _ (hBN hb₀B)
    have hlow := two_pow_mul_card_le hD hb₀inv hd₁ hd₂ (j := i)
      (by rw [inv_inv, hz1]; exact ha1) (by rw [inv_inv]; exact hz1')
      (by simpa only [inv_inv] using hz2')
    have hPle : B ⊓ D ≤ D ⊓ Subgroup.centralizer ({b₀⁻¹} : Set G) := by
      intro y hy
      refine ⟨hy.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hyb := hB y hy.1 b₀ hb₀B
      calc y * b₀⁻¹ = b₀⁻¹ * (b₀ * y) * b₀⁻¹ := by group
        _ = b₀⁻¹ * (y * b₀) * b₀⁻¹ := by rw [hyb]
        _ = b₀⁻¹ * y := by group
    have hPcard := Subgroup.card_le_of_le hPle
    have hrel := Subgroup.relIndex_mul_card D B
    rw [inf_comm] at hrel
    have hpos : 0 < Nat.card ↥(B ⊓ D) := Nat.card_pos
    have h1 : 2 ^ (i + 2) * Nat.card ↥(B ⊓ D) ≤ 2 ^ (i + 1) * Nat.card ↥(B ⊓ D) := by
      calc 2 ^ (i + 2) * Nat.card ↥(B ⊓ D)
          ≤ 2 ^ (i + 2) * Nat.card ↥(D ⊓ Subgroup.centralizer ({b₀⁻¹} : Set G)) :=
            Nat.mul_le_mul_left _ hPcard
        _ ≤ Nat.card D := hlow
        _ = Nat.card B := hcard.symm
        _ = D.relIndex B * Nat.card ↥(B ⊓ D) := hrel.symm
        _ ≤ 2 ^ (i + 1) * Nat.card ↥(B ⊓ D) := Nat.mul_le_mul_right _ hup
    have h2 : 2 ^ (i + 2) ≤ 2 ^ (i + 1) := Nat.le_of_mul_le_mul_right h1 hpos
    have h3 : 2 ^ (i + 1) < 2 ^ (i + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

end CFSG.CGT.Stroth77
