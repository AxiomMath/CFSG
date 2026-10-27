module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1 Module

variable {F : Type} [Group F]

private lemma mul_comm_of_isE (hF : IsE 3 F) : ∀ a b : F, a * b = b * a := by
  haveI : IsMulCommutative (⊤ : Subgroup F) := hF.1.1
  intro a b
  exact congrArg Subtype.val
    (mul_comm' (M := (⊤ : Subgroup F)) ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩)

private def linearEquivToMulAut {F : Type} [CommGroup F] [Module (ZMod 2) (Additive F)]
    (E : Additive F ≃ₗ[ZMod 2] Additive F) : MulAut F where
  toFun x := (E (Additive.ofMul x)).toMul
  invFun x := (E.symm (Additive.ofMul x)).toMul
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by simp [ofMul_mul, toMul_add]

@[simp]
private lemma linearEquivToMulAut_apply {F : Type} [CommGroup F] [Module (ZMod 2) (Additive F)]
    (E : Additive F ≃ₗ[ZMod 2] Additive F) (x : F) :
    linearEquivToMulAut E x = (E (Additive.ofMul x)).toMul := rfl

private lemma exists_basis_pair {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    (hfin : Module.finrank (ZMod 2) A = 3) {a b : A} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) : ∃ B : Basis (Fin 3) (ZMod 2) A, B 0 = a ∧ B 1 = b := by
  have hli2 : LinearIndependent (ZMod 2) ![a, b] := by
    rw [LinearIndependent.pair_iff' ha]
    intro c
    have hc : c = 0 ∨ c = 1 := by
      have h : c.val = 0 ∨ c.val = 1 := by have := c.val_lt; omega
      rcases h with h | h
      · left; exact (ZMod.val_eq_zero c).mp h
      · right
        rw [← ZMod.natCast_zmod_val c, h]
        norm_num
    rcases hc with rfl | rfl
    · simpa using (Ne.symm hb)
    · simpa using hab
  have hproper : Submodule.span (ZMod 2) (Set.range ![a, b]) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have h1 : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) (Set.range ![a, b])) = 2 := by
      rw [finrank_span_eq_card hli2]; simp
    rw [htop] at h1
    have : Module.finrank (ZMod 2) A = 2 := by simpa using h1
    omega
  obtain ⟨c, -, hc⟩ := SetLike.exists_of_lt hproper
  have hli3 : LinearIndependent (ZMod 2) (Fin.snoc ![a, b] c) :=
    LinearIndependent.finSnoc hli2 hc
  have hcard : Fintype.card (Fin 3) = Module.finrank (ZMod 2) A := by simp [hfin]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli3 hcard, ?_, ?_⟩
  · simp
  · simp

private lemma add_self_eq_zero_zmod2 {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    (x : M) : x + x = 0 := by
  have h1 : x + x = (1 : ZMod 2) • x + (1 : ZMod 2) • x := by rw [one_smul]
  rw [h1, ← add_smul, show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]

private lemma alt_pair_zero {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (d : V → V → V)
    (hl : ∀ x y z : V, d (x + y) z = d x z + d y z)
    (hr : ∀ x y z : V, d x (y + z) = d x y + d x z)
    (halt : ∀ x : V, d x x = 0)
    (hσ : ∀ (E : V ≃ₗ[ZMod 2] V) (x y : V), d (E x) (E y) = E (d x y))
    (B : Basis (Fin 3) (ZMod 2) V) :
    d (B 0) (B 1) = 0 := by
  let T1 : V →ₗ[ZMod 2] V := B.constr (ZMod 2) ![B 0, B 1, B 2 + B 0]
  let T2 : V →ₗ[ZMod 2] V := B.constr (ZMod 2) ![B 0, B 1 + B 0, B 2]
  let T3 : V →ₗ[ZMod 2] V := B.constr (ZMod 2) ![B 1, B 0, B 2]
  have hT1_0 : T1 (B 0) = B 0 := by simp [T1, Basis.constr_basis]
  have hT1_1 : T1 (B 1) = B 1 := by simp [T1, Basis.constr_basis]
  have hT1_2 : T1 (B 2) = B 2 + B 0 := by simp [T1, Basis.constr_basis]
  have hT2_0 : T2 (B 0) = B 0 := by simp [T2, Basis.constr_basis]
  have hT2_1 : T2 (B 1) = B 1 + B 0 := by simp [T2, Basis.constr_basis]
  have hT2_2 : T2 (B 2) = B 2 := by simp [T2, Basis.constr_basis]
  have hT3_0 : T3 (B 0) = B 1 := by simp [T3, Basis.constr_basis]
  have hT3_1 : T3 (B 1) = B 0 := by simp [T3, Basis.constr_basis]
  have hT3_2 : T3 (B 2) = B 2 := by simp [T3, Basis.constr_basis]
  have hT1 : Function.Involutive T1 := by
    intro x
    have hcomp : T1.comp T1 = LinearMap.id := by
      apply B.ext
      intro i
      fin_cases i <;> simp [LinearMap.comp_apply, hT1_0, hT1_1, hT1_2, add_assoc,
        add_self_eq_zero_zmod2]
    exact congrFun (congrArg DFunLike.coe hcomp) x
  have hT2 : Function.Involutive T2 := by
    intro x
    have hcomp : T2.comp T2 = LinearMap.id := by
      apply B.ext
      intro i
      fin_cases i <;> simp [LinearMap.comp_apply, hT2_0, hT2_1, hT2_2, add_assoc,
        add_self_eq_zero_zmod2]
    exact congrFun (congrArg DFunLike.coe hcomp) x
  have hT3 : Function.Involutive T3 := by
    intro x
    have hcomp : T3.comp T3 = LinearMap.id := by
      apply B.ext
      intro i
      fin_cases i <;> simp [LinearMap.comp_apply, hT3_0, hT3_1, hT3_2]
    exact congrFun (congrArg DFunLike.coe hcomp) x
  have hsym : d (B 1) (B 0) = d (B 0) (B 1) := by
    have h2 : d (B 0) (B 1) + d (B 1) (B 0) = 0 := by
      have h := halt (B 0 + B 1)
      simpa only [hl, hr, halt, zero_add, add_zero] using h
    have h3 : d (B 1) (B 0) + d (B 1) (B 0) = 0 := add_self_eq_zero_zmod2 _
    exact (add_right_cancel_iff.mp (by rw [h2, h3])).symm
  let u : V := d (B 0) (B 1)
  have hu1 : u = T1 u := by
    have h := hσ (LinearEquiv.ofInvolutive T1 hT1) (B 0) (B 1)
    simp only [LinearEquiv.coe_ofInvolutive, hT1_0, hT1_1, u] at h
    exact h
  have hu2 : u = T2 u := by
    have h := hσ (LinearEquiv.ofInvolutive T2 hT2) (B 0) (B 1)
    simp only [LinearEquiv.coe_ofInvolutive, hT2_0, hT2_1, hr, halt, add_zero, u] at h
    exact h
  have hu3 : u = T3 u := by
    have h := hσ (LinearEquiv.ofInvolutive T3 hT3) (B 0) (B 1)
    simp only [LinearEquiv.coe_ofInvolutive, hT3_0, hT3_1, hsym, u] at h
    exact h
  have hcoord : (B.equivFun (T1 u)) 0 = (B.equivFun u) 0 + (B.equivFun u) 2 := by
    have hT1u : T1 u = ∑ i, (B.equivFun u) i • (![B 0, B 1, B 2 + B 0] : Fin 3 → V) i := by
      change B.constr (ZMod 2) ![B 0, B 1, B 2 + B 0] u =
        ∑ i, (B.equivFun u) i • (![B 0, B 1, B 2 + B 0] : Fin 3 → V) i
      rw [Basis.constr_apply_fintype]
    rw [hT1u]
    simp [Fin.sum_univ_three, Basis.equivFun_self, mul_add]
  have hc2 : (B.equivFun u) 2 = 0 := by
    have h0 : (B.equivFun u) 0 = (B.equivFun u) 0 + (B.equivFun u) 2 := by
      have h := congrFun (congrArg (fun w => B.equivFun w) hu1) 0
      rwa [hcoord] at h
    have h' : (B.equivFun u) 0 + 0 = (B.equivFun u) 0 + (B.equivFun u) 2 := by
      rw [add_zero]; exact h0
    exact (add_left_cancel_iff.mp h').symm
  have hcoord2 : (B.equivFun (T2 u)) 0 = (B.equivFun u) 0 + (B.equivFun u) 1 := by
    have hT2u : T2 u = ∑ i, (B.equivFun u) i • (![B 0, B 1 + B 0, B 2] : Fin 3 → V) i := by
      change B.constr (ZMod 2) ![B 0, B 1 + B 0, B 2] u =
        ∑ i, (B.equivFun u) i • (![B 0, B 1 + B 0, B 2] : Fin 3 → V) i
      rw [Basis.constr_apply_fintype]
    rw [hT2u]
    simp [Fin.sum_univ_three, Basis.equivFun_self, mul_add]
  have hc1 : (B.equivFun u) 1 = 0 := by
    have h0 : (B.equivFun u) 0 = (B.equivFun u) 0 + (B.equivFun u) 1 := by
      have h := congrFun (congrArg (fun w => B.equivFun w) hu2) 0
      rwa [hcoord2] at h
    have h' : (B.equivFun u) 0 + 0 = (B.equivFun u) 0 + (B.equivFun u) 1 := by
      rw [add_zero]; exact h0
    exact (add_left_cancel_iff.mp h').symm
  have hcoord3 : (B.equivFun (T3 u)) 0 = (B.equivFun u) 1 := by
    have hT3u : T3 u = ∑ i, (B.equivFun u) i • (![B 1, B 0, B 2] : Fin 3 → V) i := by
      change B.constr (ZMod 2) ![B 1, B 0, B 2] u =
        ∑ i, (B.equivFun u) i • (![B 1, B 0, B 2] : Fin 3 → V) i
      rw [Basis.constr_apply_fintype]
    rw [hT3u]
    simp [Fin.sum_univ_three, Basis.equivFun_self, mul_add]
  have hc0 : (B.equivFun u) 0 = 0 := by
    have h0 : (B.equivFun u) 0 = (B.equivFun u) 1 := by
      have h := congrFun (congrArg (fun w => B.equivFun w) hu3) 0
      rwa [hcoord3] at h
    rw [hc1] at h0
    exact h0
  have hu : B.equivFun u = 0 := by
    ext i; fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2
  have hbase : u = 0 := by
    have h := congrArg B.equivFun.symm hu
    simpa using h
  exact hbase

theorem gl_alt_zero (hF : IsE 3 F) (c : F → F → F)
    (hl : ∀ a a' b : F, c (a * a') b = c a b * c a' b)
    (hr : ∀ a b b' : F, c a (b * b') = c a b * c a b')
    (halt : ∀ a : F, c a a = 1)
    (hσ : ∀ (α : MulAut F) (a b : F), c (α a) (α b) = α (c a b)) :
    ∀ a b : F, c a b = 1 := by
  have h1r : ∀ b : F, c 1 b = 1 := by
    intro b
    have h : c 1 b * 1 = c 1 b * c 1 b := by rw [mul_one, ← hl 1 1 b, one_mul]
    exact (mul_left_cancel_iff.mp h).symm
  have h1l : ∀ a : F, c a 1 = 1 := by
    intro a
    have h : c a 1 * 1 = c a 1 * c a 1 := by rw [mul_one, ← hr a 1 1, one_mul]
    exact (mul_left_cancel_iff.mp h).symm
  intro a b
  by_cases ha : a = 1
  · rw [ha]; exact h1r b
  by_cases hb : b = 1
  · rw [hb]; exact h1l a
  by_cases hab : a = b
  · rw [hab]; exact halt b
  have hcomm := mul_comm_of_isE hF
  letI : CommGroup F := { ‹Group F› with mul_comm := hcomm }
  have h2 : ∀ x : F, x ^ 2 = 1 := fun x => hF.1.2 x trivial
  letI : Module (ZMod 2) (Additive F) :=
    AddCommGroup.zmodModule (n := 2) fun x => by
      rw [← toMul_eq_one, toMul_nsmul, h2]
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF.2]; norm_num)
  haveI : Fintype (Additive F) := Fintype.ofFinite (Additive F)
  have hcardV : Fintype.card (Additive F) = 8 := by
    rw [Fintype.card_eq_nat_card, ← Nat.card_congr Additive.ofMul, hF.2]
    norm_num
  have hfr := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive F)
  rw [hcardV, ZMod.card] at hfr
  have hfin : Module.finrank (ZMod 2) (Additive F) = 3 := by
    have h : (2 : ℕ) ^ Module.finrank (ZMod 2) (Additive F) = 2 ^ 3 := by
      rw [← hfr]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
  have ha0 : Additive.ofMul a ≠ 0 := fun h => ha (ofMul_eq_zero.mp h)
  have hb0 : Additive.ofMul b ≠ 0 := fun h => hb (ofMul_eq_zero.mp h)
  have hab0 : Additive.ofMul a ≠ Additive.ofMul b := fun h => hab (Additive.ofMul.injective h)
  obtain ⟨B, hB0, hB1⟩ := exists_basis_pair (A := Additive F) hfin ha0 hb0 hab0
  let d : Additive F → Additive F → Additive F := fun x y => Additive.ofMul (c x.toMul y.toMul)
  have hld : ∀ x y z : Additive F, d (x + y) z = d x z + d y z := by
    intro x y z
    change Additive.ofMul (c (x + y).toMul z.toMul) =
      Additive.ofMul (c x.toMul z.toMul) + Additive.ofMul (c y.toMul z.toMul)
    rw [toMul_add, hl, ofMul_mul]
  have hrd : ∀ x y z : Additive F, d x (y + z) = d x y + d x z := by
    intro x y z
    change Additive.ofMul (c x.toMul (y + z).toMul) =
      Additive.ofMul (c x.toMul y.toMul) + Additive.ofMul (c x.toMul z.toMul)
    rw [toMul_add, hr, ofMul_mul]
  have haltd : ∀ x : Additive F, d x x = 0 := by
    intro x
    change Additive.ofMul (c x.toMul x.toMul) = 0
    rw [halt x.toMul, ofMul_one]
  have hσd : ∀ (T : Additive F ≃ₗ[ZMod 2] Additive F) (x y : Additive F),
      d (T x) (T y) = T (d x y) := by
    intro T x y
    have h := hσ (linearEquivToMulAut T) x.toMul y.toMul
    rw [linearEquivToMulAut_apply, linearEquivToMulAut_apply, ofMul_toMul, ofMul_toMul] at h
    change Additive.ofMul (c (T x).toMul (T y).toMul) = T (Additive.ofMul (c x.toMul y.toMul))
    rw [h]
    simp
  have hpair := alt_pair_zero d hld hrd haltd hσd B
  rw [hB0, hB1] at hpair
  have hof : Additive.ofMul (c a b) = 0 := by
    change d (Additive.ofMul a) (Additive.ofMul b) = 0
    exact hpair
  exact ofMul_eq_zero.mp hof

end CFSG.OddStandard.HigherRank.YamadaG23
