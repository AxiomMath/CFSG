module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421MonoProof

abbrev V3 : Type := Fin 3 → ZMod 3

@[expose] def shiftV (x : V3) : V3 := fun b => x (b - 1)

theorem shiftV_neg (x : V3) : shiftV (-x) = -shiftV x := rfl

theorem shiftV_iter_neg (k : ℕ) (x : V3) : shiftV^[k] (-x) = -shiftV^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, shiftV_neg]

structure Mono81 (G : Type) [Group G] : Type where
  a : Multiplicative V3 →* G
  s : G
  a_inj : Function.Injective a
  s_pow : s ^ 3 = 1
  s_conj : ∀ x : V3, s * a (Multiplicative.ofAdd x) * s⁻¹ = a (Multiplicative.ofAdd (shiftV x))
  s_ne_a : ∀ x : V3, s ≠ a (Multiplicative.ofAdd x) ∧ s ^ 2 ≠ a (Multiplicative.ofAdd x)
  f : G
  f_s : ∃ x : V3, f⁻¹ * s * f = a (Multiplicative.ofAdd x)
  f_diag : ∀ c : ZMod 3, f⁻¹ * a (Multiplicative.ofAdd (fun _ => c)) * f =
    a (Multiplicative.ofAdd (fun _ => c))

variable {G : Type} [Group G] (D : Mono81 G)

@[expose] def Mono81.av (x : V3) : G := D.a (Multiplicative.ofAdd x)

theorem Mono81.av_add (x y : V3) : D.av (x + y) = D.av x * D.av y := by
  simp only [Mono81.av, ofAdd_add, map_mul]

theorem Mono81.av_zero : D.av 0 = 1 := by
  simp only [Mono81.av, ofAdd_zero, map_one]

theorem Mono81.av_neg (x : V3) : D.av (-x) = (D.av x)⁻¹ := by
  unfold Mono81.av
  rw [ofAdd_neg]
  exact map_inv D.a _

theorem Mono81.av_inj {x y : V3} (h : D.av x = D.av y) : x = y :=
  Multiplicative.ofAdd.injective (D.a_inj h)

theorem Mono81.av_comm (x y : V3) : D.av x * D.av y = D.av y * D.av x := by
  rw [← D.av_add, ← D.av_add, add_comm]

theorem Mono81.av_pow_three (x : V3) : D.av x ^ 3 = 1 := by
  have h : x + x + x = 0 := by
    funext b
    have h3 : ∀ y : ZMod 3, y + y + y = 0 := by decide
    simpa using h3 (x b)
  rw [pow_succ, pow_two, ← D.av_add, ← D.av_add, h, D.av_zero]

theorem Mono81.s_av (x : V3) : D.s * D.av x = D.av (shiftV x) * D.s := by
  have h := D.s_conj x
  have h' : D.s * D.av x * D.s⁻¹ * D.s = D.av (shiftV x) * D.s := by
    simpa [Mono81.av] using congrArg (· * D.s) h
  simpa [mul_assoc] using h'

theorem Mono81.s_pow_av (k : ℕ) (x : V3) : D.s ^ k * D.av x = D.av (shiftV^[k] x) * D.s ^ k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    calc D.s ^ (k + 1) * D.av x = D.s * (D.s ^ k * D.av x) := by rw [pow_succ', mul_assoc]
      _ = D.s * (D.av (shiftV^[k] x) * D.s ^ k) := by rw [ih]
      _ = (D.s * D.av (shiftV^[k] x)) * D.s ^ k := by rw [mul_assoc]
      _ = (D.av (shiftV (shiftV^[k] x)) * D.s) * D.s ^ k := by rw [D.s_av]
      _ = D.av (shiftV^[k + 1] x) * D.s ^ (k + 1) := by
        rw [Function.iterate_succ_apply', mul_assoc, pow_succ']

theorem Mono81.s_pow_mod (k : ℕ) : D.s ^ k = D.s ^ (k % 3) := pow_eq_pow_mod k D.s_pow

@[expose] def Mono81.R0 : Subgroup G where
  carrier := {g | ∃ (x : V3) (k : ℕ), g = D.av x * D.s ^ k}
  mul_mem' := by
    rintro _ _ ⟨x, k, rfl⟩ ⟨y, l, rfl⟩
    refine ⟨x + shiftV^[k] y, k + l, ?_⟩
    rw [D.av_add, mul_assoc, ← mul_assoc (D.s ^ k), D.s_pow_av, pow_add]
    simp only [mul_assoc]
  one_mem' := ⟨0, 0, by simp [D.av_zero]⟩
  inv_mem' := by
    rintro _ ⟨x, k, rfl⟩
    have hinv : (D.s ^ k)⁻¹ = D.s ^ (2 * k) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add]
      have h3 : k + 2 * k = 3 * k := by ring
      rw [h3, pow_mul, D.s_pow, one_pow]
    refine ⟨shiftV^[2 * k] (-x), 2 * k, ?_⟩
    rw [mul_inv_rev, hinv, ← D.av_neg, D.s_pow_av]

theorem Mono81.av_mem_R0 (x : V3) : D.av x ∈ D.R0 := ⟨x, 0, by simp⟩

@[expose] def Mono81.A0 : Subgroup G := D.a.range

theorem Mono81.mem_A0_iff {g : G} : g ∈ D.A0 ↔ ∃ x : V3, g = D.av x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Multiplicative.toAdd y, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨Multiplicative.ofAdd x, rfl⟩

theorem Mono81.av_mem_A0 (x : V3) : D.av x ∈ D.A0 := D.mem_A0_iff.mpr ⟨x, rfl⟩

theorem Mono81.card_A0 : Nat.card D.A0 = 27 := by
  show Nat.card D.a.range = 27
  rw [← Nat.card_congr (MonoidHom.ofInjective D.a_inj).toEquiv]
  simp [Nat.card_eq_fintype_card]

theorem Mono81.isElemAbelian_A0 : CFSG.Open.IsElemAbelian 3 D.A0 := by
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun g hg => ?_⟩
  · obtain ⟨x, hx⟩ := D.mem_A0_iff.mp u.2
    obtain ⟨y, hy⟩ := D.mem_A0_iff.mp v.2
    apply Subtype.ext
    show (u : G) * v = v * u
    rw [hx, hy, D.av_comm]
  · obtain ⟨x, rfl⟩ := D.mem_A0_iff.mp hg
    exact D.av_pow_three x

theorem Mono81.s_pow_mul_inv (k l : ℕ) : D.s ^ k * (D.s ^ l)⁻¹ = D.s ^ ((k + 2 * l) % 3) := by
  have hinv : (D.s ^ l)⁻¹ = D.s ^ (2 * l) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_add]
    have h3 : l + 2 * l = 3 * l := by ring
    rw [h3, pow_mul, D.s_pow, one_pow]
  rw [hinv, ← pow_add, D.s_pow_mod (k + 2 * l)]

theorem Mono81.normalForm_inj {x y : V3} {k l : Fin 3}
    (h : D.av x * D.s ^ (k : ℕ) = D.av y * D.s ^ (l : ℕ)) : x = y ∧ k = l := by
  have hk : D.s ^ (k : ℕ) = D.av (y - x) * D.s ^ (l : ℕ) := by
    have h3 : ∀ z : ZMod 3, -z + z = 0 := by decide
    have hneg : (-x + x : V3) = 0 := by
      funext b
      exact h3 (x b)
    have hxy : (-x + y : V3) = y - x := by
      funext b
      show -x b + y b = y b - x b
      exact neg_add_eq_sub _ _
    have h1 : D.s ^ (k : ℕ) = D.av (-x) * (D.av x * D.s ^ (k : ℕ)) := by
      rw [← mul_assoc, ← D.av_add, hneg, D.av_zero, one_mul]
    rw [h1, h, ← mul_assoc, ← D.av_add, hxy]
  have hkl : k = l := by
    by_contra hne
    have h2 : D.s ^ ((k : ℕ) + 2 * (l : ℕ)) = D.av (y - x) := by
      calc D.s ^ ((k : ℕ) + 2 * (l : ℕ)) = D.s ^ (k : ℕ) * (D.s ^ (l : ℕ))⁻¹ := by
            rw [D.s_pow_mul_inv, ← D.s_pow_mod]
        _ = D.av (y - x) := by rw [hk, mul_inv_cancel_right]
    have h3 : (k : ℕ) + 2 * (l : ℕ) = ((k : ℕ) + 2 * (l : ℕ)) % 3 ∨ True := Or.inr trivial
    rw [D.s_pow_mod] at h2
    have hcases : ((k : ℕ) + 2 * (l : ℕ)) % 3 = 0 ∨ ((k : ℕ) + 2 * (l : ℕ)) % 3 = 1 ∨
        ((k : ℕ) + 2 * (l : ℕ)) % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2'
    · apply hne
      apply Fin.ext
      omega
    · rw [h1, pow_one] at h2
      exact (D.s_ne_a (y - x)).1 h2
    · rw [h2'] at h2
      exact (D.s_ne_a (y - x)).2 h2
  subst hkl
  refine ⟨?_, rfl⟩
  have h1 : D.av x = D.av y := mul_right_cancel h
  exact D.av_inj h1

theorem Mono81.card_R0 : Nat.card D.R0 = 81 := by
  let φ : V3 × Fin 3 → D.R0 := fun p => ⟨D.av p.1 * D.s ^ (p.2 : ℕ), p.1, p.2, rfl⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨x, k⟩ ⟨y, l⟩ h
      have h' : D.av x * D.s ^ (k : ℕ) = D.av y * D.s ^ (l : ℕ) := congrArg Subtype.val h
      obtain ⟨hxy, hkl⟩ := D.normalForm_inj h'
      rw [hxy, hkl]
    · rintro ⟨g, x, k, rfl⟩
      refine ⟨(x, ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
      apply Subtype.ext
      show D.av x * D.s ^ (k % 3) = D.av x * D.s ^ k
      rw [← D.s_pow_mod]
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ)]
  simp [Nat.card_eq_fintype_card]

theorem Mono81.nf_mul (x y : V3) (k l : ℕ) :
    (D.av x * D.s ^ k) * (D.av y * D.s ^ l) = D.av (x + shiftV^[k] y) * D.s ^ (k + l) := by
  rw [D.av_add, mul_assoc, ← mul_assoc (D.s ^ k), D.s_pow_av, pow_add]
  simp only [mul_assoc]

theorem Mono81.nf_pow_three (x : V3) (k : ℕ) :
    (D.av x * D.s ^ k) ^ 3 = D.av (x + shiftV^[k] x + shiftV^[k + k] x) := by
  have h3 : D.s ^ (k + k + k) = 1 := by
    have : k + k + k = 3 * k := by ring
    rw [this, pow_mul, D.s_pow, one_pow]
  rw [pow_succ, pow_two, D.nf_mul, D.nf_mul, h3, mul_one]

theorem exists_sub_shift_one :
    ∀ x : V3, x 0 + x 1 + x 2 = 0 → ∃ w : V3, w + x - shiftV^[1] w = 0 := by
  decide

theorem exists_sub_shift_two :
    ∀ x : V3, x 0 + x 1 + x 2 = 0 → ∃ w : V3, w + x - shiftV^[2] w = 0 := by
  decide

theorem norm_shift_one : ∀ x : V3, x + shiftV^[1] x + shiftV^[1 + 1] x = fun _ => x 0 + x 1 + x 2 := by
  decide

theorem norm_shift_two : ∀ x : V3, x + shiftV^[2] x + shiftV^[2 + 2] x = fun _ => x 0 + x 1 + x 2 := by
  decide

theorem const_of_shift_one : ∀ v : V3, shiftV^[1] v = v → v = fun _ => v 0 := by decide

theorem const_of_shift_two : ∀ v : V3, shiftV^[2] v = v → v = fun _ => v 0 := by decide

theorem const_eq_zero_iff (c : ZMod 3) : ((fun _ => c : V3) = 0) ↔ c = 0 := by
  constructor
  · intro h
    exact congrFun h 0
  · rintro rfl
    rfl

theorem Mono81.eq_const_of_comm {v : V3} {l k : ℕ} (hk : k = 1 ∨ k = 2)
    (h : (D.av v * D.s ^ l) * D.s ^ k = D.s ^ k * (D.av v * D.s ^ l)) : v = fun _ => v 0 := by
  have h1 : D.av v * D.s ^ (l + k) = D.av (shiftV^[k] v) * D.s ^ (k + l) := by
    calc D.av v * D.s ^ (l + k) = (D.av v * D.s ^ l) * D.s ^ k := by rw [mul_assoc, pow_add]
      _ = D.s ^ k * (D.av v * D.s ^ l) := h
      _ = (D.s ^ k * D.av v) * D.s ^ l := by rw [mul_assoc]
      _ = (D.av (shiftV^[k] v) * D.s ^ k) * D.s ^ l := by rw [D.s_pow_av]
      _ = D.av (shiftV^[k] v) * D.s ^ (k + l) := by rw [mul_assoc, pow_add]
  rw [add_comm l k] at h1
  have h2 := D.av_inj (mul_right_cancel h1)
  rcases hk with rfl | rfl
  · exact const_of_shift_one v h2.symm
  · exact const_of_shift_two v h2.symm

theorem Mono81.f_conj_mem (c : ZMod 3) (l : ℕ) :
    D.f⁻¹ * (D.av (fun _ => c) * D.s ^ l) * D.f ∈ D.A0 := by
  obtain ⟨x₀, hx₀⟩ := D.f_s
  have h1 : D.f⁻¹ * (D.av (fun _ => c) * D.s ^ l) * D.f =
      (D.f⁻¹ * D.av (fun _ => c) * D.f) * (D.f⁻¹ * D.s * D.f) ^ l := by
    have := map_mul (MulAut.conj D.f⁻¹) (D.av (fun _ => c)) (D.s ^ l)
    rw [map_pow] at this
    simpa [MulAut.conj_apply, mul_assoc] using this
  have hd : D.f⁻¹ * D.av (fun _ => c) * D.f = D.av (fun _ => c) := D.f_diag c
  have hx₀' : D.f⁻¹ * D.s * D.f = D.av x₀ := hx₀
  rw [h1, hd, hx₀']
  exact D.A0.mul_mem (D.av_mem_A0 _) (D.A0.pow_mem (D.av_mem_A0 _) l)

theorem Mono81.exists_conj_le_A0 {E : Subgroup G} (hER : E ≤ D.R0)
    (hE : CFSG.Open.IsElemAbelian 3 E) :
    E ≤ D.A0 ∨ (Nat.card E ≤ 9 ∧ ∃ g : G, E.map (MulAut.conj g).toMonoidHom ≤ D.A0) := by
  by_cases hA : E ≤ D.A0
  · exact Or.inl hA
  right
  obtain ⟨y, hyE, hyA⟩ := Set.not_subset.mp hA
  obtain ⟨x, k, hy⟩ := hER hyE
  obtain ⟨k', hk'⟩ : ∃ k', k' = k % 3 := ⟨_, rfl⟩
  have hy' : y = D.av x * D.s ^ k' := by rw [hy, hk', D.s_pow_mod k]
  have hk1 : k' = 1 ∨ k' = 2 := by
    rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 by omega) with h | h | h
    · exfalso
      apply hyA
      rw [hy', h, pow_zero, mul_one]
      exact D.av_mem_A0 x
    · exact Or.inl h
    · exact Or.inr h
  have hnorm : x 0 + x 1 + x 2 = 0 := by
    have hy3 : y ^ 3 = 1 := hE.2 y hyE
    rw [hy', D.nf_pow_three] at hy3
    have hy3' : D.av (x + shiftV^[k'] x + shiftV^[k' + k'] x) = D.av 0 := by
      rw [hy3, D.av_zero]
    have h0 := D.av_inj hy3'
    rcases hk1 with h | h
    · rw [h, norm_shift_one] at h0
      exact (const_eq_zero_iff _).mp h0
    · rw [h, norm_shift_two] at h0
      exact (const_eq_zero_iff _).mp h0
  obtain ⟨w, hw⟩ : ∃ w : V3, w + x - shiftV^[k'] w = 0 := by
    rcases hk1 with h | h
    · rw [h]; exact exists_sub_shift_one x hnorm
    · rw [h]; exact exists_sub_shift_two x hnorm
  have hu : D.av w * y * (D.av w)⁻¹ = D.s ^ k' := by
    have h0 : w + x + shiftV^[k'] (-w) = 0 := by
      rw [shiftV_iter_neg]
      funext b
      have hb : w b + x b - shiftV^[k'] w b = 0 := congrFun hw b
      show w b + x b + -(shiftV^[k'] w b) = 0
      exact Eq.trans (sub_eq_add_neg _ _).symm hb
    calc D.av w * y * (D.av w)⁻¹ = D.av w * (D.av x * (D.s ^ k' * D.av (-w))) := by
          rw [hy', ← D.av_neg]
          simp only [mul_assoc]
      _ = D.av w * (D.av x * (D.av (shiftV^[k'] (-w)) * D.s ^ k')) := by rw [D.s_pow_av]
      _ = D.av (w + x + shiftV^[k'] (-w)) * D.s ^ k' := by
          rw [D.av_add, D.av_add]
          simp only [mul_assoc]
      _ = D.s ^ k' := by rw [h0, D.av_zero, one_mul]
  let E' : Subgroup G := E.map (MulAut.conj (D.av w)).toMonoidHom
  have hE'R : ∀ z ∈ E', ∃ (c : ZMod 3) (l : ℕ), z = D.av (fun _ => c) * D.s ^ l := by
    rintro _ ⟨z₀, hz₀, rfl⟩
    show ∃ (c : ZMod 3) (l : ℕ), (MulAut.conj (D.av w)) z₀ = D.av (fun _ => c) * D.s ^ l
    have hzR : (MulAut.conj (D.av w)) z₀ ∈ D.R0 := by
      have := D.R0.mul_mem (D.R0.mul_mem (D.av_mem_R0 w) (hER hz₀))
        (D.R0.inv_mem (D.av_mem_R0 w))
      simpa [MulAut.conj_apply] using this
    obtain ⟨v, l, hz⟩ := hzR
    refine ⟨v 0, l, ?_⟩
    have hcomm : z₀ * y = y * z₀ :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨z₀, hz₀⟩ ⟨y, hyE⟩)
    have hcomm' : (D.av v * D.s ^ l) * D.s ^ k' = D.s ^ k' * (D.av v * D.s ^ l) := by
      rw [← hz, ← hu]
      simp only [MulAut.conj_apply]
      calc D.av w * z₀ * (D.av w)⁻¹ * (D.av w * y * (D.av w)⁻¹)
          = D.av w * (z₀ * y) * (D.av w)⁻¹ := by group
        _ = D.av w * (y * z₀) * (D.av w)⁻¹ := by rw [hcomm]
        _ = D.av w * y * (D.av w)⁻¹ * (D.av w * z₀ * (D.av w)⁻¹) := by group
    have hv := D.eq_const_of_comm hk1 hcomm'
    rw [hz]
    conv_lhs => rw [hv]
  refine ⟨?_, D.f⁻¹ * D.av w, ?_⟩
  ·
    let φ : ZMod 3 × Fin 3 → G := fun p => D.av (fun _ => p.1) * D.s ^ (p.2 : ℕ)
    have hsub : ((E' : Subgroup G) : Set G) ⊆ Set.range φ := by
      intro z hz
      obtain ⟨c, l, rfl⟩ := hE'R z hz
      refine ⟨(c, ⟨l % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
      show D.av (fun _ => c) * D.s ^ (l % 3) = D.av (fun _ => c) * D.s ^ l
      rw [← D.s_pow_mod]
    have h1 : Nat.card E = Nat.card E' :=
      (Subgroup.card_map_of_injective (MulAut.conj (D.av w)).injective).symm
    have h2 : Nat.card E' ≤ Nat.card (Set.range φ) := Nat.card_mono (Set.toFinite _) hsub
    have h3 : Nat.card (Set.range φ) ≤ 9 := by
      have := Finite.card_range_le φ
      simpa [Nat.card_eq_fintype_card] using this
    omega
  ·
    rintro _ ⟨z₀, hz₀, rfl⟩
    have hz : (MulAut.conj (D.av w)) z₀ ∈ E' := ⟨z₀, hz₀, rfl⟩
    obtain ⟨c, l, hcl⟩ := hE'R _ hz
    have h1 : (MulAut.conj (D.f⁻¹ * D.av w)) z₀ =
        D.f⁻¹ * ((MulAut.conj (D.av w)) z₀) * D.f := by
      simp [MulAut.conj_apply, mul_assoc]
    show (MulAut.conj (D.f⁻¹ * D.av w)) z₀ ∈ D.A0
    rw [h1, hcl]
    exact D.f_conj_mem c l

section Finite

variable [Finite G]

noncomputable def Mono81.sylow {k : ℕ} (hk3 : ¬ 3 ∣ k) (hk : Nat.card G = 81 * k) : Sylow 3 G :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  (IsPGroup.of_card (n := 4) (by rw [D.card_R0]; norm_num) : IsPGroup 3 D.R0).toSylow (by
    have h := D.R0.card_mul_index
    rw [D.card_R0, hk] at h
    have : D.R0.index = k := Nat.eq_of_mul_eq_mul_left (by norm_num) h
    rw [this]
    exact hk3)

theorem Mono81.coe_sylow {k : ℕ} (hk3 : ¬ 3 ∣ k) (hk : Nat.card G = 81 * k) :
    (D.sylow hk3 hk : Subgroup G) = D.R0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact IsPGroup.toSylow_coe _ _

end Finite

end K421MonoProof

end CFSG.LocalAnalysis.RankThreeUC.S15
