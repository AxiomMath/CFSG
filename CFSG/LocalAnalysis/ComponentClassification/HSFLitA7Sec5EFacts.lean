module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5EModel

public section

namespace CFSG.ComponentClassification.HSFLit.Sec5E

namespace T2M

theorem z_eq : z = x * x := by decide +kernel

theorem comm_cases : ∀ a b : T2M, a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = z := by
  decide +kernel

theorem sw2_E3 : ∀ e ∈ E3l, sw2 e = e := by decide +kernel

theorem mem_E3_of_sw2 : ∀ τ : T2M, τ * sw2 τ = 1 → τ ∈ E3l := by decide +kernel

theorem mem_Zl_of_central : ∀ a : T2M, (∀ b : T2M, a * b = b * a) → a ∈ Zl := by
  decide +kernel

theorem central_of_mem_Zl : ∀ a ∈ Zl, ∀ b : T2M, a * b = b * a := by decide +kernel

theorem sq_of_mem_Zl : ∀ a ∈ Zl, a * a = 1 := by decide +kernel

theorem conj_E2 : ∀ τ : T2M, ∀ e ∈ E2l, τ * e * τ⁻¹ ∈ E2l := by decide +kernel

theorem conj_E5 : ∀ τ : T2M, ∀ e ∈ E5l, τ * e * τ⁻¹ ∈ E5l := by decide +kernel

theorem sw2_E2 : ∀ e ∈ E2l, sw2 e ∈ E5l := by decide +kernel

theorem sw2_E5 : ∀ e ∈ E5l, sw2 e ∈ E2l := by decide +kernel

@[expose] def normD (ax ay aw bx by_ bw τ : T2M) : SigD :=
  ⟨homOf ax ay aw (t * k) (z * k) (τ * x * τ⁻¹), homOf ax ay aw (t * k) (z * k) (τ * y * τ⁻¹),
    homOf ax ay aw (t * k) (z * k) (τ * w * τ⁻¹), τ⁻¹ * bx * τ, τ⁻¹ * by_ * τ, τ⁻¹ * bw * τ⟩

@[expose] def ClB (ax ay aw : T2M) : Prop :=
  ∀ bx : T2M, homOf ax ay aw (t * k) (z * k) bx = x → ∀ by_ : T2M,
    homOf ax ay aw (t * k) (z * k) by_ = y → ∀ bw : T2M, homOf ax ay aw (t * k) (z * k) bw = w →
    ∃ τ : T2M, InT τ ∧ normD ax ay aw bx by_ bw τ ∈ repList

instance (ax ay aw : T2M) : Decidable (ClB ax ay aw) := by unfold ClB; infer_instance

@[expose] def ClW (ax ay : T2M) : Prop :=
  ∀ aw : T2M, aw * aw = 1 → aw * ax = ax * aw → aw * ay = ay * aw →
    aw * (z * k) = (z * k) * aw → aw * (t * k) * aw⁻¹ = t * k * z →
    (∀ g ∈ [x, y, w, t, k], homOf ax ay aw (t * k) (z * k) (homOf ax ay aw (t * k) (z * k) g) = g ∨
      homOf ax ay aw (t * k) (z * k) (homOf ax ay aw (t * k) (z * k) g) = g * z) →
    ClB ax ay aw

instance (ax ay : T2M) : Decidable (ClW ax ay) := by unfold ClW; infer_instance

@[expose] def ClY (ax : T2M) : Prop :=
  ∀ ay : T2M, InT ay → ay ∈ E2l → ay * ay = 1 →
    ay * ax * ay⁻¹ = ax⁻¹ → ay * (t * k) = (t * k) * ay → ay * (z * k) = (z * k) * ay → ClW ax ay

instance (ax : T2M) : Decidable (ClY ax) := by unfold ClY; infer_instance

theorem classify : ∀ ax : T2M, InT ax → ax * ax = z → ax * (t * k) = (t * k) * ax →
    ax * (z * k) = (z * k) * ax → ClY ax := by
  decide +kernel

namespace SigD

@[expose] def SigInvOk (p : SigD) : Prop := ∀ b : T2M, p.sig (p.sigInv b) = b

instance (p : SigD) : Decidable (SigInvOk p) := by unfold SigInvOk; infer_instance

theorem sigInvOk : ∀ p ∈ repList, SigInvOk p := by decide +kernel

@[expose] def InvCases (p : SigD) : Prop :=
  ∀ a : T2M, a * a = 1 → a ≠ 1 → a ∈ p.S16 ∨ a ∈ E3l ∨ a ∈ p.E3'l

instance (p : SigD) : Decidable (InvCases p) := by unfold InvCases; infer_instance

theorem involution_cases : ∀ p ∈ repList, InvCases p := by decide +kernel

@[expose] def RepsIn (p : SigD) : Prop := ∀ i : Fin 4, ∀ c ∈ Zl, p.reps i * c ∈ p.S16

instance (p : SigD) : Decidable (RepsIn p) := by unfold RepsIn; infer_instance

theorem reps_mem : ∀ p ∈ repList, RepsIn p := by decide +kernel

@[expose] def Match (i j : Fin 4) : Prop :=
  (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)

instance (i j : Fin 4) : Decidable (Match i j) := by unfold Match; infer_instance

@[expose] def RepsMatch (p : SigD) : Prop :=
  ∀ i j : Fin 4, (p.reps i * p.reps j * (p.reps i * p.reps j) ≠ 1 ↔ Match i j)

instance (p : SigD) : Decidable (RepsMatch p) := by unfold RepsMatch; infer_instance

theorem reps_match : ∀ p ∈ repList, RepsMatch p := by decide +kernel

@[expose] def RepsGen (p : SigD) : Prop :=
  ∀ a : T2M, Sec8.InSpan [p.reps 0, p.reps 1, p.reps 2, p.reps 3, z, k] a

instance (p : SigD) : Decidable (RepsGen p) := by unfold RepsGen; infer_instance

theorem reps_gen : ∀ p ∈ repList, RepsGen p := by decide +kernel

@[expose] def OrbitCases (p : SigD) : Prop :=
  ∀ a ∈ p.S16, ∀ b : T2M, a * b ∈ p.S16 → a * b = b * a → b * b = 1 → b ∉ Zl →
    (InE1 a ∧ InE1 b) ∨ (a ∈ E2l ∧ b ∈ E2l) ∨ (a ∈ E5l ∧ b ∈ E5l) ∨ (a ∈ p.E6l ∧ b ∈ p.E6l)

instance (p : SigD) : Decidable (OrbitCases p) := by unfold OrbitCases; infer_instance

theorem orbitCases : ∀ p ∈ repList, OrbitCases p := by decide +kernel

@[expose] def EAct (p : SigD) : Prop :=
  (∀ e : T2M, InE1 e → p.sig e ∈ E2l) ∧ (∀ e ∈ E2l, InE1 (p.sig e)) ∧
    (∀ e ∈ p.E6l, p.sig e ∈ E5l) ∧ (∀ e ∈ p.E6l, sw2 e ∈ p.E6l) ∧
    (∀ τ : T2M, ∀ e ∈ p.E6l, τ * e * τ⁻¹ ∈ p.E6l)

instance (p : SigD) : Decidable (EAct p) := by unfold EAct; infer_instance

theorem eAct : ∀ p ∈ repList, EAct p := by decide +kernel

@[expose] def EDistinct (p : SigD) : Prop :=
  (∃ e ∈ E2l, ¬ InE1 e) ∧ (∃ e ∈ E5l, ¬ InE1 e) ∧ (∃ e ∈ p.E6l, ¬ InE1 e) ∧
    (∃ e ∈ E5l, e ∉ E2l) ∧ (∃ e ∈ p.E6l, e ∉ E2l) ∧ (∃ e ∈ p.E6l, e ∉ E5l)

instance (p : SigD) : Decidable (EDistinct p) := by unfold EDistinct; infer_instance

theorem eDistinct : ∀ p ∈ repList, EDistinct p := by decide +kernel

@[expose] def Z4 (p : SigD) : Prop := ∀ τ c : T2M, InT (p.sig τ * c * τ) ↔ InT c

instance (p : SigD) : Decidable (Z4 p) := by unfold Z4; infer_instance

theorem z4 : ∀ p ∈ repList, Z4 p := by decide +kernel

@[expose] def InnerF (p : SigD) : Prop :=
  ∀ f : T2M, (∀ g ∈ [x, y, w, t, k], p.sf g = f * g * f⁻¹) → p ∈ repList' ∧ p.InN f

instance (p : SigD) : Decidable (InnerF p) := by unfold InnerF; infer_instance

theorem innerF : ∀ p ∈ repList, InnerF p := by decide +kernel

@[expose] def QInv (p : SigD) : Prop :=
  ∀ f : T2M, p.InN f → ∀ τ : T2M, τ * p.sq τ * f = 1 → p.InM0 τ

instance (p : SigD) : Decidable (QInv p) := by unfold QInv; infer_instance

theorem qInv : ∀ p ∈ repList', QInv p := by decide +kernel

@[expose] def WsOk (p : SigD) : Prop :=
  p.InN p.ws ∧ p.ws ∉ Zl ∧ (p.sig p.ws = p.ws ∨ p.sig p.ws = p.ws * z) ∧
    (∀ n : T2M, p.InN n → n ∈ Zl ∨ n * p.ws ∈ Zl) ∧ (∀ n : T2M, p.InN n → p.InN (p.sig n))

instance (p : SigD) : Decidable (WsOk p) := by unfold WsOk; infer_instance

theorem wsOk : ∀ p ∈ repList', WsOk p := by decide +kernel

@[expose] def ANorm (p : SigD) : Prop :=
  (∀ e ∈ E3l, e * (p.sw22 e)⁻¹ ∈ p.E3'l) ∧ (∀ a ∈ p.E3'l, sw2 a ∈ p.E3'l) ∧
    (∀ e ∈ E3l, ∀ a ∈ p.E3'l, e * a * e⁻¹ ∈ p.E3'l)

instance (p : SigD) : Decidable (ANorm p) := by unfold ANorm; infer_instance

theorem aNorm : ∀ p ∈ repList', ANorm p := by decide +kernel

@[expose] def M0Ok (p : SigD) : Prop :=
  (∀ s ∈ p.S16, s * p.ws ≠ p.ws * s) ∧
    (∀ m : T2M, p.InM0 m → ∃ e ∈ E3l, ∃ e' ∈ p.E3'l, m = e * e')

instance (p : SigD) : Decidable (M0Ok p) := by unfold M0Ok; infer_instance

theorem m0Ok : ∀ p ∈ repList', M0Ok p := by decide +kernel

end SigD

end T2M

end CFSG.ComponentClassification.HSFLit.Sec5E
