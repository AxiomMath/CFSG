module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAutInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsBridge
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction
import CFSG.CGT.PushingUpLit.CGT6M.FiveTransfer
import CFSG.CGT.T75P.SylowSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open CFSG.RankThree.PartOne.OutStructure Matrix
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.CGT.PushingUpLit.CGT6M (eq_of_map_eq_of_pow_eq_one)

section Semi

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def semiMap (A : GL ι K) (σ : K ≃+* K) : (ι → K) ≃+ (ι → K) :=
  ((Cls.glEquiv A⁻¹).toAddEquiv.trans (AddEquiv.piCongrRight fun _ : ι => σ.toAddEquiv)).trans
    (Cls.glEquiv A).toAddEquiv

theorem semiMap_apply (A : GL ι K) (σ : K ≃+* K) (v : ι → K) :
    semiMap A σ v =
      (A : Matrix ι ι K) *ᵥ fun i => σ ((((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) i) := by
  change Cls.glEquiv A (fun i => σ (Cls.glEquiv A⁻¹ v i)) = _
  rw [Cls.glEquiv_apply, Cls.glEquiv_apply]

@[expose] noncomputable def semiConj (A : GL ι K) (σ : K ≃+* K) : MulAut (GL ι K) :=
  (MulAut.conj A⁻¹).trans ((glFieldAut ι K σ).trans (MulAut.conj A))

theorem semiConj_apply (A : GL ι K) (σ : K ≃+* K) (g : GL ι K) :
    semiConj A σ g = A * glFieldAut ι K σ (A⁻¹ * g * A) * A⁻¹ := by
  simp [semiConj, MulAut.conj_apply]

theorem coe_glFieldAut (σ : K ≃+* K) (g : GL ι K) :
    ((glFieldAut ι K σ g : GL ι K) : Matrix ι ι K) = (g : Matrix ι ι K).map σ :=
  rfl

theorem map_mulVec_glFieldAut (σ : K ≃+* K) (g : GL ι K) (v : ι → K) :
    (fun i => σ (((g : Matrix ι ι K) *ᵥ v) i)) =
      ((glFieldAut ι K σ g : GL ι K) : Matrix ι ι K) *ᵥ fun i => σ (v i) := by
  funext i
  rw [coe_glFieldAut]
  exact RingHom.map_mulVec (σ : K →+* K) _ v i

theorem mulVec_mulVec_gl (X Y : GL ι K) (v : ι → K) :
    (X : Matrix ι ι K) *ᵥ ((Y : Matrix ι ι K) *ᵥ v) = ((X * Y : GL ι K) : Matrix ι ι K) *ᵥ v := by
  rw [Matrix.mulVec_mulVec, Units.val_mul]

theorem glEquiv_semiConj_apply (A : GL ι K) (σ : K ≃+* K) (g : GL ι K) (v : ι → K) :
    Cls.glEquiv (semiConj A σ g) (semiMap A σ v) = semiMap A σ (Cls.glEquiv g v) := by
  rw [Cls.glEquiv_apply, Cls.glEquiv_apply, semiMap_apply, semiMap_apply, mulVec_mulVec_gl]
  set N := A⁻¹ * g * A with hN
  have h1 : semiConj A σ g * A = A * glFieldAut ι K σ N := by
    rw [semiConj_apply, inv_mul_cancel_right]
  have h2 : N * A⁻¹ = A⁻¹ * g := by rw [hN]; group
  rw [h1, ← mulVec_mulVec_gl, ← map_mulVec_glFieldAut, mulVec_mulVec_gl, h2, ← mulVec_mulVec_gl]

theorem semiMap_smul (A : GL ι K) (σ : K ≃+* K) (c : K) (v : ι → K) :
    semiMap A σ (c • v) = σ c • semiMap A σ v := by
  rw [semiMap_apply, semiMap_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply, smul_eq_mul]

theorem semiMap_iterate (A : GL ι K) (σ : K ≃+* K) (n : ℕ) (v : ι → K) :
    (semiMap A σ)^[n] v =
      (A : Matrix ι ι K) *ᵥ fun i => (σ ^ n) ((((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) i) := by
  induction n generalizing v with
  | zero =>
    have h1 : (fun i => (σ ^ 0) ((((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) i)) =
        ((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v := rfl
    rw [Function.iterate_zero, id, h1, mulVec_mulVec_gl, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, semiMap_apply, Matrix.mulVec_mulVec,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, pow_succ']
    rfl

theorem semiMap_iterate_eq_self (A : GL ι K) {σ : K ≃+* K} {n : ℕ} (h : σ ^ n = 1)
    (v : ι → K) : (semiMap A σ)^[n] v = v := by
  rw [semiMap_iterate, h]
  have h1 : (fun i => (1 : K ≃+* K) ((((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) i)) =
      ((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v := rfl
  rw [h1, mulVec_mulVec_gl, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end Semi

theorem mem_of_pow_mem_of_coprime {G : Type*} [Group G] (I : Subgroup G) [I.Normal]
    {D : Subgroup G} {δ : G} {p : ℕ} (hδ : δ ∈ D) (hδp : δ ^ p ∈ I)
    (hcop : Nat.Coprime (I.relIndex D) p) : δ ∈ I := by
  have h1 := I.pow_relIndex_mem hδ
  have hg := Nat.gcd_eq_gcd_ab (I.relIndex D) p
  rw [hcop.gcd_eq_one, Nat.cast_one] at hg
  have hδ' : δ = (δ ^ I.relIndex D) ^ (Nat.gcdA (I.relIndex D) p) *
      (δ ^ p) ^ (Nat.gcdB (I.relIndex D) p) := by
    rw [← zpow_natCast δ (I.relIndex D), ← zpow_natCast δ p, ← _root_.zpow_mul, ← _root_.zpow_mul,
      ← _root_.zpow_add, ← hg, zpow_one]
  rw [hδ']
  exact I.mul_mem (I.zpow_mem h1 _) (I.zpow_mem hδp _)

theorem not_dvd_card_of_sq_eq_one {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : ∀ g : G, g ^ 2 = 1) : ¬ p ∣ Nat.card G := by
  intro hd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (h g)
  rw [hg] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem card_le_of_inner_split {Ω : Type*} [Group Ω] {p : ℕ} {B N : Subgroup Ω}
    (hB : IsElemAbelian p B) (hp : 0 < p)
    (hsplit : B ⊓ N = B ∨ ∃ b ∈ B, B = B ⊓ N ⊔ Subgroup.zpowers b ∧ Subgroup.zpowers b ⊓ N = ⊥) :
    Nat.card B ≤ Nat.card ↥(B ⊓ N) * p := by
  rcases hsplit with h | ⟨b, hb, hBb, hbN⟩
  · rw [h]
    exact Nat.le_mul_of_pos_right _ hp
  · have hcomm : ∀ x ∈ B ⊓ N, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
      intro x hx y hy
      exact hB.comm hx.1 (Subgroup.zpowers_le.2 hb hy)
    have hinf : B ⊓ N ⊓ Subgroup.zpowers b = ⊥ := by
      rw [eq_bot_iff, ← hbN, inf_comm]
      exact inf_le_inf_left _ inf_le_right
    have h1 := CFSG.CGT.T75P.card_sup_of_commute hcomm hinf
    rw [← hBb] at h1
    rw [h1]
    refine Nat.mul_le_mul_left _ ?_
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one (hB.2 b hb))

section Transport

variable {p : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω}
variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def coverProjEquiv {H : Subgroup (GL ι K)} (φ : ↥H →* Ω)
    (hφS : φ.range = S) (hφk : φ.ker = (StatedScalars ι K).subgroupOf H) : StatedProj H ≃* ↥S :=
  (QuotientGroup.quotientMulEquivOfEq hφk.symm).trans (coverEquiv φ hφS)

theorem inner_split' (hp : p.Prime) [S.Normal] {B : Subgroup Ω} (hB : IsElemAbelian p B)
    (hOut : OutPChain p ↥S) :
    B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = B ∨
      ∃ b ∈ B, b ∉ S ⊔ Subgroup.centralizer (S : Set Ω) ∧
        B = B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) ⊔ Subgroup.zpowers b ∧
        Subgroup.zpowers b ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = ⊥ := by
  rcases inner_split hp hB hOut with h | ⟨b, hb, hBb, hbN⟩
  · exact Or.inl h
  · by_cases hbS : b ∈ S ⊔ Subgroup.centralizer (S : Set Ω)
    · left
      have hb1 : b = 1 := by
        have : b ∈ Subgroup.zpowers b ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) :=
          ⟨Subgroup.mem_zpowers b, hbS⟩
        rwa [hbN, Subgroup.mem_bot] at this
      rw [hb1, Subgroup.zpowers_one_eq_bot, sup_bot_eq] at hBb
      exact hBb.symm
    · exact Or.inr ⟨b, hb, hbS, hBb, hbN⟩

private theorem eq_one_of_mem_centralizer (hZ : Subgroup.center ↥S = ⊥) {s : Ω} (hs : s ∈ S)
    (hc : s ∈ Subgroup.centralizer (S : Set Ω)) : s = 1 := by
  have h1 : (⟨s, hs⟩ : ↥S) ∈ Subgroup.center ↥S := Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext ((Subgroup.mem_centralizer_iff.1 hc) g g.2)
  rw [hZ, Subgroup.mem_bot] at h1
  exact congrArg Subtype.val h1

variable [S.Normal]

theorem transAut_eq_congr {X : Type*} [Group X] (e : X ≃* ↥S) (x : Ω) :
    transAut e x = MulAut.congr e.symm (MulAut.conjNormal x) :=
  rfl

theorem transAut_mem_inner_iff {X : Type*} [Group X] (e : X ≃* ↥S) (x : Ω) :
    transAut e x ∈ Inn X ↔ x ∈ S ⊔ Subgroup.centralizer (S : Set Ω) := by
  rw [← conjNormal_mem_inner_iff, transAut_eq_congr]
  have hmap := CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e.symm
  change _ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X ↔
    _ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥S
  rw [← hmap]
  constructor
  · rintro ⟨α, hα, hαx⟩
    have : α = MulAut.conjNormal x := (MulAut.congr e.symm).injective hαx
    exact this ▸ hα
  · intro h
    exact ⟨_, h, rfl⟩

theorem orderOf_transAut_eq {X : Type*} [Group X] (e : X ≃* ↥S) (hp : p.Prime) {b : Ω}
    (hbp : b ^ p = 1) (hbN : b ∉ S ⊔ Subgroup.centralizer (S : Set Ω)) :
    orderOf (transAut e b) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine orderOf_eq_prime ?_ fun h => hbN ((transAut_mem_inner_iff e b).1 (h ▸ one_mem _))
  rw [transAut_eq_congr, ← map_pow, ← map_pow, hbp, map_one, map_one]

theorem conj_lift_eq (hZ : Subgroup.center ↥S = ⊥) {H : Type*} [Group H] (φ : H →* Ω)
    (hφS : φ.range = S) {B B₁ : Subgroup Ω} (hB : IsElemAbelian p B) (hB₁ : B₁ ≤ B)
    (θ : ↥B₁ →* H) (hθ : ∀ x, (φ (θ x))⁻¹ * (x : Ω) ∈ Subgroup.centralizer (S : Set Ω))
    {b : Ω} (hb : b ∈ B) (x : ↥B₁) : b * φ (θ x) * b⁻¹ = φ (θ x) := by
  set s := φ (θ x) with hsdef
  have hs : s ∈ S := hφS ▸ ⟨θ x, rfl⟩
  have hbx : b * x = x * b := hB.comm hb (hB₁ x.2)
  have hbx' : b⁻¹ * x = x * b⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hbx, mul_inv_cancel_right]
  have hc : (b * s * b⁻¹)⁻¹ * x ∈ Subgroup.centralizer (S : Set Ω) := by
    have h1 : (b * s * b⁻¹)⁻¹ * x = b * (s⁻¹ * x) * b⁻¹ := by
      calc (b * s * b⁻¹)⁻¹ * x = b * s⁻¹ * (b⁻¹ * x) := by group
        _ = b * s⁻¹ * (x * b⁻¹) := by rw [hbx']
        _ = b * (s⁻¹ * x) * b⁻¹ := by group
    rw [h1]
    exact Subgroup.Normal.conj_mem inferInstance _ (hθ x) b
  have h2 : (b * s * b⁻¹)⁻¹ * s ∈ Subgroup.centralizer (S : Set Ω) := by
    have e : (b * s * b⁻¹)⁻¹ * s = ((b * s * b⁻¹)⁻¹ * x) * (s⁻¹ * x)⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ hc (Subgroup.inv_mem _ (hθ x))
  have h4 := eq_one_of_mem_centralizer hZ (S.mul_mem (S.inv_mem
    ((inferInstance : S.Normal).conj_mem s hs b)) hs) h2
  exact inv_mul_eq_one.1 h4

@[expose] def FieldAct (p : ℕ) {H : Subgroup (GL ι K)} (φ : ↥H →* Ω) (b : Ω) (A : GL ι K)
    (σ : K ≃+* K) : Prop :=
  orderOf σ = p ∧ Nat.card K = Nat.card (semilinearFixedSubfield σ) ^ p ∧
    ∀ k : ↥H, ∃ k' : ↥H, (k' : GL ι K) = semiConj A σ k ∧ φ k' = b * φ k * b⁻¹

@[expose] def FormRel {τ : K →+* K} (β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K) (A : GL ι K)
    (σ : K ≃+* K) : Prop :=
  ∃ c : Kˣ, ∀ u v, (c : K) * β (semiMap A σ u) (semiMap A σ v) = σ ((c : K) * β u v)

theorem semiConj_eq_of_fieldAct (hp : p.Prime) (hZ : Subgroup.center ↥S = ⊥)
    {H : Subgroup (GL ι K)} [Finite ↥H] (φ : ↥H →* Ω) (hφS : φ.range = S)
    (hker : φ.ker ≤ Subgroup.center ↥H) (hC : ¬ p ∣ Nat.card φ.ker) {B B₁ : Subgroup Ω}
    (hB : IsElemAbelian p B) (hB₁ : B₁ ≤ B) (θ : ↥B₁ →* ↥H)
    (hθ : ∀ x, (φ (θ x))⁻¹ * (x : Ω) ∈ Subgroup.centralizer (S : Set Ω))
    (hθp : ∀ x, θ x ^ p = 1) {b : Ω} (hb : b ∈ B) {A : GL ι K} {σ : K ≃+* K}
    (hact : FieldAct p φ b A σ) (x : ↥B₁) :
    semiConj A σ ((θ x : ↥H) : GL ι K) = θ x := by
  obtain ⟨k', hk', hφk'⟩ := hact.2.2 (θ x)
  have hk'p : k' ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hk', ← map_pow, ← Subgroup.coe_pow, hθp x, Subgroup.coe_one, map_one]
  have h1 : φ k' = φ (θ x) := by rw [hφk', conj_lift_eq hZ φ hφS hB hB₁ θ hθ hb x]
  rw [← hk', eq_of_map_eq_of_pow_eq_one hker hp hC hk'p (hθp x) h1]

end Transport

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
