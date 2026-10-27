module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57ModelBasic
public import CFSG.Quasithin.Background.JonesParshallG2Gen

public section

namespace CFSG.QuasithinUnique.Bridge.Alt57Model

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall Matrix
open CFSG.QuasithinUnique.Bridge

variable {K : Type} [Field K] [CharP K 2]

@[expose] def nullPts (K : Type) [Field K] : Set (quasithinZorn K) :=
  {x | x ≠ 0 ∧ cayleyTr x = 0 ∧ cayleyNorm x = 0}

theorem orbit_zU0_eq : MulAction.orbit ↥(cayleyGroup K) (zU0 K) = nullPts K := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    show cgE g (zU0 K) ≠ 0 ∧ cayleyTr (cgE g (zU0 K)) = 0 ∧ cayleyNorm (cgE g (zU0 K)) = 0
    refine ⟨?_, ?_, ?_⟩
    · intro h0
      have : zU0 K = 0 := by
        rw [← cg_inv_apply g (zU0 K), h0, map_zero]
      have h1 := congrArg Prod.fst (congrArg Prod.snd this)
      exact one_ne_zero (congrFun h1 0)
    · rw [cg_tr, zU0, cayleyTr_zmk, add_zero]
    · rw [cg_norm, zU0, cayleyNorm_zmk]
      ring
  · rintro ⟨hx, htr, hN⟩
    obtain ⟨r, hr, hre⟩ := exists_closure_apply_zU0 hx htr hN
    have hrC : r ∈ cayleyGroup K := (Subgroup.closure_le _).mpr gensG2_subset hr
    exact ⟨⟨r, hrC⟩, hre⟩

section Count

variable [Fintype K]

omit [CharP K 2] in
theorem mul_self_of_card_two (hK : Fintype.card K = 2) (a : K) : a * a = a := by
  have := FiniteField.pow_card a
  rwa [hK, sq] at this

theorem eq_of_null (hK : Fintype.card K = 2) {x : quasithinZorn K} (htr : cayleyTr x = 0)
    (hN : cayleyNorm x = 0) :
    x = (x.2.1 ⬝ᵥ x.2.2.1, x.2.1, x.2.2.1, x.2.1 ⬝ᵥ x.2.2.1) := by
  obtain ⟨r, u, v, s⟩ := x
  have hs : s = r := by
    have h : r + s = 0 := htr
    rw [eq_neg_of_add_eq_zero_right h, CharTwo.neg_eq]
  have hr : r = u ⬝ᵥ v := by
    have h : r * s + ∑ i, u i * v i = 0 := hN
    rw [hs] at h
    have h2 : r * r = u ⬝ᵥ v := by
      rw [eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq]
      rfl
    exact (mul_self_of_card_two hK r).symm.trans h2
  exact Prod.ext hr (Prod.ext rfl (Prod.ext rfl (hs.trans hr)))

theorem nullPts_ncard (hK : Fintype.card K = 2) : (nullPts K).ncard = 63 := by
  let Y : Set (quasithinZorn K) := {x | cayleyTr x = 0 ∧ cayleyNorm x = 0}
  have hYmem : ∀ p : (Fin 3 → K) × (Fin 3 → K),
      ((p.1 ⬝ᵥ p.2, p.1, p.2, p.1 ⬝ᵥ p.2) : quasithinZorn K) ∈ Y := by
    intro p
    refine ⟨?_, ?_⟩
    · show p.1 ⬝ᵥ p.2 + p.1 ⬝ᵥ p.2 = 0
      exact CharTwo.add_self_eq_zero _
    · show p.1 ⬝ᵥ p.2 * p.1 ⬝ᵥ p.2 + ∑ i, p.1 i * p.2 i = 0
      rw [mul_self_of_card_two hK]
      exact CharTwo.add_self_eq_zero _
  let e : Y ≃ (Fin 3 → K) × (Fin 3 → K) :=
    { toFun := fun x => (x.1.2.1, x.1.2.2.1)
      invFun := fun p => ⟨_, hYmem p⟩
      left_inv := fun x => Subtype.ext (eq_of_null hK x.2.1 x.2.2).symm
      right_inv := fun p => rfl }
  have hY : Y.ncard = 64 := by
    rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_prod, Nat.card_fun]
    have hK' : Nat.card K = 2 := by rw [Nat.card_eq_fintype_card]; exact hK
    rw [hK', Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
    norm_num
  have h0 : (0 : quasithinZorn K) ∈ Y := ⟨by simp [cayleyTr], by simp [cayleyNorm]⟩
  have hX : nullPts K = Y \ {0} := by
    ext x
    simp only [nullPts, Y, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    tauto
  rw [hX, Set.ncard_sdiff_singleton_of_mem h0, hY]

end Count

section Stab

abbrev S0 (K : Type) [Field K] : Subgroup (SL3 K) :=
  MulAction.stabilizer (SL3 K) (e0 : Fin 3 → K)

omit [CharP K 2] in
theorem mem_S0 {A : SL3 K} :
    A ∈ S0 K ↔ (A : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0] := Iff.rfl

omit [CharP K 2] in
theorem g2A_zE (A : SL3 K) : cgE (g2A A) (zE K) = zE K := by
  change gAFun (A : Matrix (Fin 3) (Fin 3) K) (zE K) = zE K
  rw [zE, gAFun_zmk]
  apply zmk_congr <;> simp

omit [CharP K 2] in
theorem g2A_zU0 {A : SL3 K} (hA : A ∈ S0 K) : cgE (g2A A) (zU0 K) = zU0 K := by
  change gAFun (A : Matrix (Fin 3) (Fin 3) K) (zU0 K) = zU0 K
  have hA' : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0] := hA
  have h0 := congrFun hA' 0
  have h1 := congrFun hA' 1
  have h2 := congrFun hA' 2
  simp [mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
  rw [zU0, gAFun_zmk]
  apply zmk_congr <;> simp [h0, h1, h2]

omit [CharP K 2] in
theorem g2A_injective : Function.Injective (g2A : SL3 K →* ↥(cayleyGroup K)) := by
  intro A B h
  have key : ∀ x : quasithinZorn K, gAFun (A : Matrix (Fin 3) (Fin 3) K) x =
      gAFun (B : Matrix (Fin 3) (Fin 3) K) x := fun x =>
    congrArg (fun g : ↥(cayleyGroup K) => ((g : quasithinZorn K ≃ₗ[K] quasithinZorn K)) x) h
  have e0' := key (zmk 0 1 0 0 0 0 0 0)
  have e1' := key (zmk 0 0 1 0 0 0 0 0)
  have e2' := key (zmk 0 0 0 1 0 0 0 0)
  rw [gAFun_zmk, gAFun_zmk] at e0' e1' e2'
  obtain ⟨-, a00, a10, a20, -, -, -, -⟩ := zmk_inj e0'
  obtain ⟨-, a01, a11, a21, -, -, -, -⟩ := zmk_inj e1'
  obtain ⟨-, a02, a12, a22, -, -, -, -⟩ := zmk_inj e2'
  simp only [mul_one, mul_zero, add_zero, zero_add] at a00 a10 a20 a01 a11 a21 a02 a12 a22
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

@[expose] noncomputable def stabElt (p : K × K × K × ↥(S0 K)) : ↥(cayleyGroup K) :=
  g2X ![p.1, 0, 0] * g2Y ![0, p.2.1, p.2.2.1] * g2A (p.2.2.2 : SL3 K)

theorem stabElt_zU0 (p : K × K × K × ↥(S0 K)) : cgE (stabElt p) (zU0 K) = zU0 K := by
  rw [stabElt, cg_mul_apply, g2A_zU0 p.2.2.2.2]
  exact uW_zU0 p.1 p.2.1 p.2.2.1

theorem stabElt_zE (p : K × K × K × ↥(S0 K)) :
    cgE (stabElt p) (zE K) = zmk 1 p.1 0 0 0 p.2.1 p.2.2.1 0 := by
  rw [stabElt, cg_mul_apply, g2A_zE]
  exact uW_zE p.1 p.2.1 p.2.2.1

theorem stabElt_injective : Function.Injective (stabElt (K := K)) := by
  intro p q h
  have hE := congrArg (fun g : ↥(cayleyGroup K) => cgE g (zE K)) h
  simp only [stabElt_zE] at hE
  obtain ⟨-, h1, -, -, -, h2, h3, -⟩ := zmk_inj hE
  have hA : g2A (p.2.2.2 : SL3 K) = g2A (q.2.2.2 : SL3 K) := by
    have h' := h
    rw [stabElt, stabElt, h1, h2, h3] at h'
    exact mul_left_cancel h'
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 (Subtype.ext (g2A_injective hA))))

theorem stab_card (hK : Nat.card K = 2) :
    Nat.card (MulAction.stabilizer ↥(cayleyGroup K) (zU0 K)) = 8 * Nat.card ↥(S0 K) := by
  let Φ : K × K × K × ↥(S0 K) → ↥(MulAction.stabilizer ↥(cayleyGroup K) (zU0 K)) :=
    fun p => ⟨stabElt p, MulAction.mem_stabilizer_iff.2 (stabElt_zU0 p)⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro p q h
      exact stabElt_injective (congrArg Subtype.val h)
    · rintro ⟨g, hg⟩
      have hg' : cgE g (zU0 K) = zU0 K := MulAction.mem_stabilizer_iff.1 hg
      obtain ⟨α, β, γ, A, hA, rfl⟩ := eq_uW_mul_g2A hg'
      exact ⟨(α, β, γ, ⟨A, hA⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective Φ hΦ), Nat.card_prod, Nat.card_prod, Nat.card_prod, hK]
  ring

end Stab

theorem not_five_dvd_card_cayley [Finite K] (hK : Nat.card K = 2) :
    ¬ 5 ∣ Nat.card ↥(cayleyGroup K) := by
  have : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥(cayleyGroup K) (zU0 K))
  rw [MulAction.index_stabilizer, orbit_zU0_eq, nullPts_ncard hKf, stab_card hK] at h1
  have hSL : Nat.card (SL3 K) = 168 := by
    rw [Matrix.card_SL_field 3]
    simp [Fin.prod_univ_three, hKf]
  have hS : Nat.card ↥(S0 K) ∣ 168 := by
    rw [← hSL]
    exact Subgroup.card_subgroup_dvd_card _
  intro h5
  rw [← h1] at h5
  have h5s : 5 ∣ Nat.card ↥(S0 K) := by omega
  have := h5s.trans hS
  omega

theorem noAlt57Image_cayley_two [Finite K] (hK : Nat.card K = 2) :
    NoAlt57Image ↥(cayleyGroup K) := by
  have : Finite ↥(cayleyGroup K) :=
    Finite.of_injective (fun g : ↥(cayleyGroup K) => fun x : quasithinZorn K =>
      (g : quasithinZorn K ≃ₗ[K] quasithinZorn K) x)
      fun g h hgh => Subtype.ext (LinearEquiv.ext (congrFun hgh))
  exact noAlt57Image_of_not_five_dvd (not_five_dvd_card_cayley hK)

end CFSG.QuasithinUnique.Bridge.Alt57Model
