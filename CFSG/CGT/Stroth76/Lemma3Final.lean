module

public import CFSG.CGT.Stroth76.Lemma3
public import CFSG.CGT.Stroth77.L4Sylow.Recognition
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitInputs

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77 CFSG.CGT.Stroth77.Arch76 CFSG.CGT.Stroth77.L4Sylow
  CFSG.OddStandard.HigherRank.YamadaG23

@[expose] def guvI : Cc8 → Cc8 := lin8 (1, 4, 4) (1, 1, 2) (1, 2, 1)

@[expose] def gtI : Cc8 → Cc8 := lin8 (1, 4, 0) (0, 7, 0) (1, 6, 7)

@[expose] def torus200ToCc (y : Torus (Type200.k 1)) : Cc8 := (y 0, y 1, y 2)

theorem torus200ToCc_add (y y' : Torus (Type200.k 1)) :
    torus200ToCc (y + y') = torus200ToCc y + torus200ToCc y' := rfl

theorem torus200ToCc_injective : Function.Injective torus200ToCc := by
  intro y y' h
  have h0 : y 0 = y' 0 := congrArg (fun p : Cc8 => p.1) h
  have h1 : y 1 = y' 1 := congrArg (fun p : Cc8 => p.2.1) h
  have h2 : y 2 = y' 2 := congrArg (fun p : Cc8 => p.2.2) h
  funext i
  fin_cases i
  exacts [h0, h1, h2]

theorem torus200ToCc_φuv : ∀ y : Torus (Type200.k 1),
    torus200ToCc ((Type200.action 1).φuv y) = guvI (torus200ToCc y) := by decide +kernel

theorem torus200ToCc_φt : ∀ y : Torus (Type200.k 1),
    torus200ToCc ((Type200.action 1).φt y) = gtI (torus200ToCc y) := by decide +kernel

theorem torus200ToCc_φu : ∀ y : Torus (Type200.k 1),
    torus200ToCc ((Type200.action 1).φu y) = gu8 (torus200ToCc y) := by decide +kernel

theorem guvI_surjective : Function.Surjective guvI := fun v => ⟨guvI v, by revert v; decide +kernel⟩
theorem gtI_surjective : Function.Surjective gtI := fun v => ⟨gtI v, by revert v; decide +kernel⟩
theorem gu8_surjective : Function.Surjective gu8 := fun v => ⟨gu8 v, by revert v; decide +kernel⟩

structure ShapeI {X : Type*} [Group X] (K : Config X) extends CBasis8 K where
  huv_a : K.uv⁻¹ * a * K.uv = K.w * a * b ^ 2
  huv_b : K.uv⁻¹ * b * K.uv = K.w * b * a ^ 2
  ht_a : K.t⁻¹ * a * K.t = a⁻¹
  ht_b : K.t⁻¹ * b * K.t = K.w * b⁻¹ * a⁻¹ ^ 2
  hu_a : K.u⁻¹ * a * K.u = b

namespace ShapeI

variable {X : Type*} [Group X] {K : Config X} (P : ShapeI K)

theorem conj_uv_ev8 (v : Cc8) : K.uv⁻¹ * P.ev8 v * K.uv = P.ev8 (guvI v) := by
  refine P.conj_ev8_of ?_ ?_ ?_ v
  · have h : K.uv⁻¹ * K.w * K.uv = P.ev8 (1, 0, 0) * (P.ev8 (0, 2, 0) * P.ev8 (0, 0, 2)) ^ 2 := by
      rw [K.huv_w, ← P.x_eq, ← P.y_eq, P.ev8_w]
    rw [h, ← P.ev8_add, pow_two, ← P.ev8_add, ← P.ev8_add]
    congr 1
  · rw [P.huv_a, ← P.ev8_w, ← P.ev8_a, ← P.ev8_b, ← P.ev8_nsmul, ← P.ev8_add, ← P.ev8_add]
    rfl
  · rw [P.huv_b, ← P.ev8_w, ← P.ev8_a, ← P.ev8_b, ← P.ev8_nsmul, ← P.ev8_add, ← P.ev8_add]
    rfl

theorem conj_t_ev8 (v : Cc8) : K.t⁻¹ * P.ev8 v * K.t = P.ev8 (gtI v) := by
  refine P.conj_ev8_of ?_ ?_ ?_ v
  · rw [K.ht_w, P.x_eq, ← P.ev8_w, ← P.ev8_nsmul, ← P.ev8_add]
    rfl
  · rw [P.ht_a, ← P.ev8_a, ← P.ev8_neg]
    rfl
  · rw [P.ht_b, ← P.ev8_w, ← P.ev8_a, ← P.ev8_b, ← P.ev8_neg, ← P.ev8_neg, ← P.ev8_nsmul,
      ← P.ev8_add, ← P.ev8_add]
    rfl

theorem hu_b : K.u⁻¹ * P.b * K.u = P.a := by
  rw [← P.hu_a, u_inv K]
  calc K.u * (K.u * P.a * K.u) * K.u = (K.u * K.u) * P.a * (K.u * K.u) := by group
    _ = P.a := by rw [u_mul_self K]; group

theorem conj_u_ev8 (v : Cc8) : K.u⁻¹ * P.ev8 v * K.u = P.ev8 (gu8 v) := by
  refine P.conj_ev8_of ?_ ?_ ?_ v
  · rw [K.hu_w, P.ev8_w]
  · rw [P.hu_a, P.ev8_b]
  · rw [P.hu_b, P.ev8_a]

theorem mem_normalizer_C_of_conj_ev8 {g : X} {f : Cc8 → Cc8}
    (hf : ∀ v, g⁻¹ * P.ev8 v * g = P.ev8 (f v)) (hsurj : Function.Surjective f) :
    g ∈ Subgroup.normalizer (P.C : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨v, rfl⟩ := P.exists_ev8 hh
    obtain ⟨v', rfl⟩ := hsurj v
    rw [← hf v', show g * (g⁻¹ * P.ev8 v' * g) * g⁻¹ = P.ev8 v' by group]
    exact P.ev8_mem v'
  · intro hh
    obtain ⟨v, hv⟩ := P.exists_ev8 hh
    rw [show h = g⁻¹ * (g * h * g⁻¹) * g by group, ← hv, hf]
    exact P.ev8_mem _

theorem uv_mem_normalizer : K.uv ∈ Subgroup.normalizer (P.C : Set X) :=
  P.mem_normalizer_C_of_conj_ev8 P.conj_uv_ev8 guvI_surjective
theorem t_mem_normalizer : K.t ∈ Subgroup.normalizer (P.C : Set X) :=
  P.mem_normalizer_C_of_conj_ev8 P.conj_t_ev8 gtI_surjective
theorem u_mem_normalizer : K.u ∈ Subgroup.normalizer (P.C : Set X) :=
  P.mem_normalizer_C_of_conj_ev8 P.conj_u_ev8 gu8_surjective

variable [Finite X]

@[expose] noncomputable def torusHomC : Torus (Type200.k 1) →+ Additive P.C :=
  AddMonoidHom.mk' (fun y => Additive.ofMul ⟨P.ev8 (torus200ToCc y), P.ev8_mem _⟩)
    (fun y y' => by
      apply Additive.toMul.injective
      apply Subtype.ext
      simp [torus200ToCc_add, P.ev8_add])

theorem coe_torusHomC (y : Torus (Type200.k 1)) :
    ((Additive.toMul (P.torusHomC y) : P.C) : X) = P.ev8 (torus200ToCc y) := rfl

theorem torusHomC_bijective : Function.Bijective P.torusHomC := by
  haveI : Finite (Additive P.C) := Finite.of_equiv _ Additive.ofMul
  refine Function.Injective.bijective_of_nat_card_le ?_ ?_
  · intro y y' h
    apply torus200ToCc_injective
    apply P.ev8_injective
    rw [← P.coe_torusHomC, ← P.coe_torusHomC, h]
  · rw [natCard_torus, Nat.card_congr Additive.toMul, P.hCcard]
    decide

@[expose] noncomputable def torusEquivC : Torus (Type200.k 1) ≃+ Additive P.C :=
  AddEquiv.ofBijective P.torusHomC P.torusHomC_bijective

theorem torusEquivC_symm_conjBy {g : X} (hg : g ∈ Subgroup.normalizer (P.C : Set X))
    {φ : Torus (Type200.k 1) →+ Torus (Type200.k 1)} {f : Cc8 → Cc8}
    (hf : ∀ v, g⁻¹ * P.ev8 v * g = P.ev8 (f v)) (hφ : ∀ y, torus200ToCc (φ y) = f (torus200ToCc y))
    (x : P.C) :
    P.torusEquivC.symm (Additive.ofMul (conjBy hg x)) =
      φ (P.torusEquivC.symm (Additive.ofMul x)) := by
  apply P.torusEquivC.injective
  rw [AddEquiv.apply_symm_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [toMul_ofMul]
  show _ = ((Additive.toMul (P.torusHomC (φ (P.torusEquivC.symm (Additive.ofMul x)))) : P.C) : X)
  rw [P.coe_torusHomC, hφ, ← hf]
  have hx : ((Additive.toMul (P.torusHomC (P.torusEquivC.symm (Additive.ofMul x))) : P.C) : X) =
      (x : X) := by
    show ((Additive.toMul (P.torusEquivC (P.torusEquivC.symm (Additive.ofMul x))) : P.C) : X) = _
    rw [AddEquiv.apply_symm_apply, toMul_ofMul]
  rw [P.coe_torusHomC] at hx
  simp [conjBy, hx]

@[expose] noncomputable def l4Frame : L4Frame P.C 1 where
  e := P.torusEquivC.symm
  uv := K.uv
  t := K.t
  u := K.u
  uv_mem := P.uv_mem_normalizer
  t_mem := P.t_mem_normalizer
  u_mem := P.u_mem_normalizer
  uv_conj := P.torusEquivC_symm_conjBy _ P.conj_uv_ev8 torus200ToCc_φuv
  t_conj := P.torusEquivC_symm_conjBy _ P.conj_t_ev8 torus200ToCc_φt
  u_conj := P.torusEquivC_symm_conjBy _ P.conj_u_ev8 torus200ToCc_φu
  uv_sq := uv_mul_self K
  t_sq := t_mul_self K
  u_sq := u_mul_self K
  uv_comm_u := K.huvu
  t_u := by
    have h := K.htu
    calc K.t * K.u = K.u * (K.u⁻¹ * K.t * K.u) := by group
      _ = K.u * K.uv * K.t := by rw [h]; group

end ShapeI

variable {G : Type} [Group G] [Finite G]

theorem arch76Lemma3 (K : Config G)
    (hfusE : ∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, e ≠ 1 →
      IsConj e ((K.x * K.y) ^ 2))
    (huw : IsConj K.u K.w) (hwu : IsConj (K.w * K.u) (K.x * K.y * K.uv))
    (hAnn1 : ¬ IsConj K.w ((K.x * K.y) ^ 2)) (S : Sylow 2 G) {C : Subgroup G}
    (hS : (S : Subgroup G) = C ⊔ Subgroup.closure {K.uv, K.t, K.u})
    (hCc : IsMulCommutative C) (hC : Nat.card C = 2 ^ 7)
    (hshape : (∃ a b : G, C = Subgroup.closure {K.w, a, b} ∧ a ^ 2 = K.x ∧ b ^ 2 = K.y ∧
        K.uv⁻¹ * a * K.uv = K.w * a * b ^ 2 ∧ K.uv⁻¹ * b * K.uv = K.w * b * a ^ 2 ∧
        K.t⁻¹ * a * K.t = a⁻¹ ∧ K.t⁻¹ * b * K.t = K.w * b⁻¹ * a⁻¹ ^ 2 ∧
        K.u⁻¹ * a * K.u = b) ∨
      (∃ a b : G, C = Subgroup.closure {K.w, a, b} ∧ a ^ 2 = K.x ∧ b ^ 2 = K.y ∧
        K.uv⁻¹ * a * K.uv = K.w * a ^ 5 * b ^ 2 ∧ K.uv⁻¹ * b * K.uv = K.w * b ^ 5 * a ^ 2 ∧
        K.t⁻¹ * a * K.t = a⁻¹ ∧ K.t⁻¹ * b * K.t = K.w * b ^ 3 * a⁻¹ ^ 2 ∧
        K.u⁻¹ * a * K.u = b))
    (hMason : ∀ {n : ℕ}, 3 ≤ n → ∀ P : Sylow 2 G, Nonempty (↥P ≃* L4Model n) → LitPSLU4S G) :
    LitPSLU4S G := by
  rcases hshape with ⟨a, b, hCab, ha, hb, h1, h2, h3, h4, h5⟩ | ⟨a, b, hCab, ha, hb, h1, h2, h3,
    h4, h5⟩
  · let P : ShapeI K := ⟨⟨C, a, b, hCab, hCc, hC, ha, hb⟩, h1, h2, h3, h4, h5⟩
    refine hMason (n := 1 + 2) (by norm_num) S ?_
    exact P.l4Frame.nonempty_mulEquiv_l4Model le_rfl hS.symm
  · let P : ShapeII K := ⟨⟨C, a, b, hCab, hCc, hC, ha, hb⟩, h1, h2, h3, h4, h5⟩
    exact (arch76Lemma3_not_shapeII K P hfusE huw hwu hAnn1 S hS).elim

end CFSG.CGT.Stroth76
